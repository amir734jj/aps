#include <string.h>

#include <algorithm>
#include <iostream>
#include <numeric>
extern "C" {
#include <stdio.h>

#include "aps-ag.h"
}
#include <set>
#include <sstream>
#include <vector>

#include "dump.h"
#include "implement.h"

typedef struct synth_function_state {
  std::string fdecl_name;
  INSTANCE* source;
  PHY_GRAPH* source_phy_graph;
  std::vector<INSTANCE*> regular_dependencies;
  std::vector<AUG_GRAPH*> aug_graphs;
  bool is_phylum_instance;
  bool is_fiber_evaluation;
} SYNTH_FUNCTION_STATE;

#define LOCAL_VALUE_FLAG (1 << 28)

#ifdef APS2SCALA
#define DEREF "."
#else
#define DEREF "->"
#endif

static const string LOOP_VAR = "isInsideFixedPoint";
static const string PREV_LOOP_VAR = "prevIsInsideFixedPoint";
static const string EVAL_PREFIX = "eval_";
static const string EVAL_FIBER_PREFIX = "eval_Fiber_";

static bool get_env_bool(const char* name, bool default_val) {
  const char* val = getenv(name);
  if (val == NULL) return default_val;
  return string(val) != "0" && string(val) != "false";
}

static int get_env_int(const char* name, int default_val) {
  const char* val = getenv(name);
  if (val == NULL) return default_val;
  return atoi(val);
}

static const bool ENABLE_FIBER_HELPERS = get_env_bool("APS_FIBER_HELPERS", true);
static const int FIBER_DEP_BATCH_SIZE = get_env_int("APS_FIBER_BATCH_SIZE", 20);
static const int COND_HELPER_THRESHOLD = get_env_int("APS_COND_THRESHOLD", 10);

struct block_item_base;

struct HelperContext {
  string eval_name;
  string phylum_type;
  bool needs_fixed_point = false;
  string dep_formals;
  string dep_actuals;
  vector<string> pending_helpers;
  int helper_counter = 0;
  AUG_GRAPH* aug_graph = NULL;
  SYNTH_FUNCTION_STATE* current_state = NULL;
  std::vector<SYNTH_FUNCTION_STATE*> synth_states;
  vector<Block> blocks;
  block_item_base* scope_block = NULL;
  vector<block_item_base*> dumped_conditionals;
  vector<INSTANCE*> dumped_instances;
  bool fiber_convergence = false;
};

class CodeWriter {
  std::ostream& _os;
  std::ostringstream _buf;
  bool _has_code = false;
public:
  CodeWriter(std::ostream& os) : _os(os) {}
  ~CodeWriter() { flush(); }
  CodeWriter(const CodeWriter&) = delete;
  CodeWriter& operator=(const CodeWriter&) = delete;

  std::ostream& code() { _has_code = true; return _buf; }
  std::ostream& comment() { return _buf; }

  std::ostream& stream() {
    flush();
    return _os;
  }

  bool has_code() const { return _has_code; }

  void flush() {
    string s = _buf.str();
    if (!s.empty()) {
      _os << s;
      _buf.str("");
      _buf.clear();
    }
  }
};

class SynthImplBase : public SynthImplementation {
public:
  HelperContext ctx;
  virtual void dump_synth_instance(INSTANCE*, CodeWriter&) = 0;
  void dump_synth_instance(INSTANCE* in, ostream& os) {
    CodeWriter cw(os);
    dump_synth_instance(in, cw);
  }
};

static SynthImplBase* synth_impl_ptr;

#define KEY_BLOCK_ITEM_CONDITION 1
#define KEY_BLOCK_ITEM_INSTANCE 2

struct block_item_base {
  int key;
  INSTANCE* instance;
  struct block_item_base* prev;
};

typedef struct block_item_base BlockItem;

struct block_item_condition {
  int key; /* KEY_BLOCK_ITEM_CONDITION */
  INSTANCE* instance;
  BlockItem* prev;
  Declaration condition;
  BlockItem* next_positive;
  BlockItem* next_negative;
};

struct block_item_instance {
  int key; /* KEY_BLOCK_ITEM_INSTANCE */
  INSTANCE* instance;
  BlockItem* prev;
  BlockItem* next;
};

static void print_linearized_block(BlockItem* block, ostream& os) {
  if (block != NULL) {
    os << indent() << block->instance << "\n";
    if (block->key == KEY_BLOCK_ITEM_CONDITION) {
      struct block_item_condition* cond = (struct block_item_condition*)block;

      if (cond->prev != NULL && cond->prev->key != KEY_BLOCK_ITEM_CONDITION) {
        os << indent() << cond->prev->instance << "\n";
      }

      os << indent() << "IF\n";
      nesting_level++;
      print_linearized_block(cond->next_positive, os);
      nesting_level--;
      os << indent() << "ELSE\n";
      nesting_level++;
      print_linearized_block(cond->next_negative, os);
      nesting_level--;
    } else {
      print_linearized_block(((struct block_item_instance*)block)->next, os);
    }
  }
}

static vector<INSTANCE*> sort_instances(AUG_GRAPH* aug_graph) {
  vector<INSTANCE*> result;

  int n = aug_graph->instances.length;
  int i;
  for (i = 0; i < n; i++) {
    INSTANCE* instance = &aug_graph->instances.array[i];
    if (!if_rule_p(instance->fibered_attr.attr)) {
      result.push_back(instance);
    }
  }

  for (i = 0; i < n; i++) {
    INSTANCE* instance = &aug_graph->instances.array[i];
    if (if_rule_p(instance->fibered_attr.attr)) {
      result.push_back(instance);
    }
  }

  return result;
}

static int count_conditions(BlockItem* item) {
  if (item == NULL) return 0;
  if (item->key == KEY_BLOCK_ITEM_INSTANCE) {
    struct block_item_instance* bi = (struct block_item_instance*)item;
    return count_conditions(bi->next);
  } else if (item->key == KEY_BLOCK_ITEM_CONDITION) {
    struct block_item_condition* cond = (struct block_item_condition*)item;
    return 1 + count_conditions(cond->next_positive) + count_conditions(cond->next_negative);
  }
  return 0;
}

static BlockItem* linearize_block_helper(AUG_GRAPH* aug_graph,
                                         const vector<INSTANCE*>& sorted_instances,
                                         bool* scheduled,
                                         CONDITION* cond,
                                         BlockItem* prev,
                                         int remaining,
                                         INSTANCE* aug_graph_instance) {
  if (CONDITION_IS_IMPOSSIBLE(*cond)) {
    return NULL;
  }

  int j;
  int n = aug_graph->instances.length;

  for (auto it = sorted_instances.begin(); it != sorted_instances.end(); it++) {
    INSTANCE* instance = *it;
    int i = instance->index;

    if (scheduled[i]) {
      continue;
    }

    if (MERGED_CONDITION_IS_IMPOSSIBLE(*cond, instance_condition(instance))) {
      scheduled[i] = true;
      BlockItem* result = linearize_block_helper(aug_graph, sorted_instances, scheduled, cond, prev, remaining - 1, aug_graph_instance);
      scheduled[i] = false;
      return result;
    }

    if (aug_graph_instance != instance && !edgeset_kind(aug_graph->graph[instance->index * n + aug_graph_instance->index])) {
      scheduled[i] = true;
      BlockItem* result = linearize_block_helper(aug_graph, sorted_instances, scheduled, cond, prev, remaining - 1, aug_graph_instance);
      scheduled[i] = false;
      return result;
    }

    bool ready_to_schedule = true;
    for (j = 0; j < n && ready_to_schedule; j++) {
      INSTANCE* other_instance = &aug_graph->instances.array[j];

      if (scheduled[j]) {
        continue;
      }

      if (MERGED_CONDITION_IS_IMPOSSIBLE(instance_condition(instance), instance_condition(other_instance))) {
        continue;
      }

      if (!(edgeset_kind(aug_graph->graph[j * n + i]) & DEPENDENCY_MAYBE_DIRECT)) {
        continue;
      }

      ready_to_schedule = false;
      break;
    }

    if (!ready_to_schedule) {
      continue;
    }

    BlockItem* item_base;
    scheduled[i] = true;

    if (if_rule_p(instance->fibered_attr.attr)) {
      struct block_item_condition* item = (struct block_item_condition*)malloc(sizeof(struct block_item_condition));
      item_base = (BlockItem*)item;

      item->key = KEY_BLOCK_ITEM_CONDITION;
      item->instance = instance;
      item->condition = instance->fibered_attr.attr;
      item->prev = prev;

      int cmask = 1 << (if_rule_index(instance->fibered_attr.attr));
      cond->positive |= cmask;
      item->next_positive = linearize_block_helper(aug_graph, sorted_instances, scheduled, cond, item_base, remaining - 1, aug_graph_instance);
      cond->positive &= ~cmask;
      cond->negative |= cmask;
      item->next_negative = linearize_block_helper(aug_graph, sorted_instances, scheduled, cond, item_base, remaining - 1, aug_graph_instance);
      cond->negative &= ~cmask;
    } else {
      struct block_item_instance* item = (struct block_item_instance*)malloc(sizeof(struct block_item_instance));
      item_base = (BlockItem*)item;
      item->key = KEY_BLOCK_ITEM_INSTANCE;
      item->instance = instance;
      item->prev = prev;
      item->next = linearize_block_helper(aug_graph, sorted_instances, scheduled, cond, item_base, remaining - 1, aug_graph_instance);
    }

    scheduled[i] = false;

    return item_base;
  }

  if (remaining != 0) {
    fatal_error("failed to schedule some instances, remaining: %d", remaining);
  }

  return NULL;
}

static BlockItem* linearize_block(AUG_GRAPH* aug_graph, INSTANCE* aug_graph_instance) {
  int n = aug_graph->instances.length;
  bool* scheduled = (bool*)alloca(sizeof(bool) * n);
  memset(scheduled, 0, sizeof(bool) * n);

  CONDITION cond = {0, 0};
  vector<INSTANCE*> sorted_instances = sort_instances(aug_graph);

  return linearize_block_helper(aug_graph, sorted_instances, scheduled, &cond, NULL, n, aug_graph_instance);
}

static BlockItem* find_surrounding_block(BlockItem* block, INSTANCE* instance) {
  while (block != NULL) {
    if (block->key == KEY_BLOCK_ITEM_CONDITION) {
      return block;
    } else if (block->key == KEY_BLOCK_ITEM_INSTANCE) {
      if (block->instance == instance) {
        return block;
      } else {
        block = ((struct block_item_instance*)block)->next;
      }
    }
  }

  return NULL;
}

static enum instance_direction custom_instance_direction(INSTANCE* i) {
  enum instance_direction dir = fibered_attr_direction(&i->fibered_attr);
  if (i->node == NULL) {
    return dir;
  } else if (DECL_IS_LHS(i->node)) {
    return dir;
  } else if (DECL_IS_RHS(i->node)) {
    return dir;
  } else if (DECL_IS_LOCAL(i->node)) {
    return instance_local;
  } else {
    fatal_error("%d: unknown attributed node", tnode_line_number(i->node));
    return dir; /* keep CC happy */
  }
}

static bool instance_is_local(INSTANCE* instance) {
  if (instance->fibered_attr.fiber == NULL) {
    return custom_instance_direction(instance) == instance_local;
  } else {
    return fibered_attr_direction(&instance->fibered_attr) == instance_local;
  }
}

static bool instance_is_synthesized(INSTANCE* instance) {
  if (instance->fibered_attr.fiber == NULL) {
    return custom_instance_direction(instance) == instance_outward;
  } else {
    return fibered_attr_direction(&instance->fibered_attr) == instance_outward;
  }
}

static bool instance_is_inherited(INSTANCE* instance) {
  if (instance->fibered_attr.fiber == NULL) {
    return custom_instance_direction(instance) == instance_inward;
  } else {
    return fibered_attr_direction(&instance->fibered_attr) == instance_inward;
  }
}

static bool instance_is_pure_shared_info(INSTANCE* instance) {
  return instance->fibered_attr.fiber == NULL && ATTR_DECL_IS_SHARED_INFO(instance->fibered_attr.attr);
}

static std::vector<INSTANCE*> collect_phylum_graph_attr_dependencies(PHY_GRAPH* phylum_graph,
                                                                     INSTANCE* sink_instance) {
  std::vector<INSTANCE*> result;

  int i;
  int n = phylum_graph->instances.length;

  for (i = 0; i < n; i++) {
    INSTANCE* source_instance = &phylum_graph->instances.array[i];
    if (!instance_is_pure_shared_info(source_instance) && source_instance->index != sink_instance->index &&
        phylum_graph->mingraph[source_instance->index * n + sink_instance->index]) {
      result.push_back(source_instance);
    }
  }

  return result;
}

static bool is_function_decl_attribute(INSTANCE* instance) {
  if (instance->node != NULL && ABSTRACT_APS_tnode_phylum(instance->node) == KEYDeclaration) {
    switch (Declaration_KEY(instance->node)) {
      case KEYpragma_call: {
        Declaration fdecl = Declaration_info(instance->node)->proxy_fdecl;
        switch (Declaration_KEY(fdecl)) {
          case KEYfunction_decl:
            return true;
          default:
            break;
        }
        break;
      }
      default:
        break;
    }
  }

  return false;
}

static std::vector<INSTANCE*> collect_aug_graph_attr_dependencies(AUG_GRAPH* aug_graph,
                                                                  INSTANCE* sink_instance) {
  std::vector<INSTANCE*> result;

  int i;
  int n = aug_graph->instances.length;

  for (i = 0; i < n; i++) {
    INSTANCE* source_instance = &aug_graph->instances.array[i];
    if (!instance_is_pure_shared_info(source_instance) && source_instance->index != sink_instance->index &&
        !is_function_decl_attribute(source_instance) &&
        edgeset_kind(aug_graph->graph[source_instance->index * n + sink_instance->index])) {
      result.push_back(source_instance);
    }
  }

  return result;
}

static vector<AUG_GRAPH*> collect_lhs_aug_graphs(STATE* state, PHY_GRAPH* pgraph) {
  vector<AUG_GRAPH*> result;

  int i;
  int n = state->match_rules.length;
  for (i = 0; i < n; i++) {
    AUG_GRAPH* aug_graph = &state->aug_graphs[i];
    PHY_GRAPH* aug_graph_pgraph = Declaration_info(aug_graph->lhs_decl)->node_phy_graph;

    if (aug_graph_pgraph == pgraph) {
      switch (Declaration_KEY(aug_graph->lhs_decl)) {
        case KEYsome_function_decl:
          continue;
        default:
          break;
      }

      result.push_back(aug_graph);
    }
  }

  return result;
}

static bool find_instance(AUG_GRAPH* aug_graph,
                          Declaration node,
                          FIBERED_ATTRIBUTE& fiber_attr,
                          INSTANCE** instance_out) {
  int i;
  for (i = 0; i < aug_graph->instances.length; i++) {
    INSTANCE* instance = &aug_graph->instances.array[i];
    if (instance->node == node && instance->fibered_attr.attr == fiber_attr.attr) {
      if (fibered_attr_equal(&instance->fibered_attr, &fiber_attr)) {
        *instance_out = instance;
        return true;
      }
    }
  }

  return false;
}

static string attr_to_string(Declaration attr) {
  if (ATTR_DECL_IS_SHARED_INFO(attr)) {
    return "sharedinfo";
  } else {
    return decl_name(attr);
  }
}

static string fiber_to_string(FIBER fiber) {
  std::stringstream ss;

  while (fiber != NULL && fiber->field != NULL) {
    std::string field = decl_name(fiber->field);
    field.erase(std::remove(field.begin(), field.end(), '!'), field.end());

    ss << field;
    fiber = fiber->shorter;
    if (fiber->field != NULL) {
      ss << "_";
    }
  }

  return ss.str();
}

static string instance_to_string(INSTANCE* in, bool force_include_node_type = false, bool trim_node = false) {
  vector<string> result;

  Declaration node = in->node;
  if (force_include_node_type && node == NULL) {
    node = synth_impl_ptr->ctx.aug_graph->lhs_decl;
  }

  if (!trim_node && node != NULL) {
    if (Declaration_KEY(node) == KEYpragma_call) {
      result.push_back(symbol_name(pragma_call_name(node)));
    } else {
      result.push_back(decl_name(node));
    }
  }

  if (in->fibered_attr.attr != NULL) {
    result.push_back(attr_to_string(in->fibered_attr.attr));
  }

  if (in->fibered_attr.fiber != NULL) {
    result.push_back(fiber_to_string(in->fibered_attr.fiber));
  }

  return std::accumulate(std::next(result.begin()), result.end(), result[0],
                         [](std::string a, std::string b) { return a + "_" + b; });
}

static string instance_to_string_with_nodetype(Declaration polymorphic, INSTANCE* in) {
  Declaration attr = in->fibered_attr.attr;
  std::stringstream ss;

  if (Declaration_KEY(attr) == KEYvalue_decl && LOCAL_UNIQUE_PREFIX(attr) != 0) {
    ss << "a" << LOCAL_UNIQUE_PREFIX(attr) << "_";
  }

  ss << decl_name(polymorphic) << "_" << instance_to_string(in, false, false);

  return ss.str();
}

static string instance_to_attr(INSTANCE* in) {
  Declaration attr = in->fibered_attr.attr;
  Declaration field = in->fibered_attr.fiber != NULL ? in->fibered_attr.fiber->field : NULL;
  std::stringstream ss;

  if (Declaration_KEY(attr) == KEYvalue_decl && LOCAL_UNIQUE_PREFIX(attr) != 0) {
    ss << "a" << LOCAL_UNIQUE_PREFIX(attr);
  } else {
    ss << "a";
  }

  if (attr != NULL && !ATTR_DECL_IS_SHARED_INFO(attr)) {
    ss << "_" << decl_name(attr);
  }

  if (field != NULL) {
    std::string field_str = decl_name(field);
    field_str.erase(std::remove(field_str.begin(), field_str.end(), '!'), field_str.end());
    ss << "_" << field_str;
  }

  return ss.str();
}

static bool check_is_match_formal(void* node) {
  Declaration formal_decl = NULL;
  bool is_formal = check_surrounding_decl(node, KEYnormal_formal, &formal_decl);

  void* match = NULL;
  bool is_inside_match = check_surrounding_node(node, KEYMatch, &match);

  return is_formal && is_inside_match;
}

static bool should_skip_synth_dependency(INSTANCE* source_instance) {
  if (source_instance->fibered_attr.fiber != NULL) {
    return true;
  }
  if (if_rule_p(source_instance->fibered_attr.attr)) {
    return true;
  }
  if (check_is_match_formal(source_instance->fibered_attr.attr)) {
    return true;
  }
  return false;
}

static std::vector<SYNTH_FUNCTION_STATE*> build_synth_functions_state(STATE* s) {
  std::vector<SYNTH_FUNCTION_STATE*> synth_function_states;
  int i, j;
  int aug_graph_count = s->match_rules.length;

  for (i = 0; i < s->phyla.length; i++) {
    PHY_GRAPH* pg = &s->phy_graphs[i];
    if (Declaration_KEY(pg->phylum) != KEYphylum_decl) {
      continue;
    }

    for (j = 0; j < pg->instances.length; j++) {
      INSTANCE* in = &pg->instances.array[j];
      bool is_fiber = in->fibered_attr.fiber != NULL;
      bool is_shared_info = ATTR_DECL_IS_SHARED_INFO(in->fibered_attr.attr);

      if (!instance_is_synthesized(in)) {
        continue;
      }

      SYNTH_FUNCTION_STATE* state = new SYNTH_FUNCTION_STATE();
      state->fdecl_name = instance_to_string_with_nodetype(pg->phylum, in);
      state->source = in;
      state->is_phylum_instance = true;
      state->source_phy_graph = pg;
      state->is_fiber_evaluation = is_fiber || is_shared_info;

      if (state->is_fiber_evaluation && state->source->node != NULL) {
        printf("Warning: Synthesizing fiber evaluation for instance with attributed node, which is not supported yet. Instance: ");
        print_instance(in, stdout);
        printf("\n");
      }

      state->regular_dependencies = collect_phylum_graph_attr_dependencies(pg, in);
      state->aug_graphs = collect_lhs_aug_graphs(s, pg);

      synth_function_states.push_back(state);
    }
  }

  for (i = 0; i < aug_graph_count; i++) {
    AUG_GRAPH* aug_graph = &s->aug_graphs[i];

    switch (Declaration_KEY(aug_graph->lhs_decl)) {
      case KEYsome_function_decl:
        continue;
      default:
        break;
    }

    for (j = 0; j < aug_graph->instances.length; j++) {
      INSTANCE* instance = &aug_graph->instances.array[j];
      bool is_local = instance_direction(instance) == instance_local;
      bool is_fiber = instance->fibered_attr.fiber != NULL;
      bool is_shared_info = ATTR_DECL_IS_SHARED_INFO(instance->fibered_attr.attr);

      if (is_local && !is_fiber && !if_rule_p(instance->fibered_attr.attr)) {
        switch (Declaration_KEY(instance->fibered_attr.attr)) {
          case KEYformal:
            continue;
          default:
            break;
        }

        Declaration attr = instance->fibered_attr.attr;
        PHY_GRAPH* pg = Declaration_info(aug_graph->lhs_decl)->node_phy_graph;
        Declaration tdecl = canonical_type_decl(canonical_type(value_decl_type(attr)));

        SYNTH_FUNCTION_STATE* state = new SYNTH_FUNCTION_STATE();
        state->fdecl_name = instance_to_string_with_nodetype(tdecl, instance);
        state->source = instance;
        state->is_phylum_instance = false;
        state->source_phy_graph = pg;
        state->is_fiber_evaluation = is_fiber || is_shared_info;
        state->regular_dependencies = collect_aug_graph_attr_dependencies(aug_graph, instance);

        vector<AUG_GRAPH*> aug_graphs;
        aug_graphs.push_back(aug_graph);
        state->aug_graphs = aug_graphs;

        synth_function_states.push_back(state);
      }
    }
  }

  return synth_function_states;
}

static void destroy_synth_function_states(const vector<SYNTH_FUNCTION_STATE*>& states) {
  for (auto it = states.begin(); it != states.end(); it++) {
    delete (*it);
  }
}

static void dump_attribute_type(INSTANCE* in, ostream& os) {
  CanonicalType* ctype = canonical_type(infer_some_value_decl_type(in->fibered_attr.attr));
  switch (ctype->key) {
    case KEY_CANONICAL_USE: {
      os << "T_" << decl_name(canonical_type_decl(ctype));
      break;
    }
    case KEY_CANONICAL_FUNC: {
      struct Canonical_function_type* fdecl_ctype = (struct Canonical_function_type*)ctype;
      os << "T_" << decl_name(canonical_type_decl(fdecl_ctype->return_type));
      break;
    }
    default:
      break;
  }
}

static void emit_synth_dep_formals(SYNTH_FUNCTION_STATE* state, ostream& out) {
  for (auto it = state->regular_dependencies.begin(); it != state->regular_dependencies.end(); it++) {
    INSTANCE* dep_instance = *it;
    if (should_skip_synth_dependency(dep_instance)) continue;
    out << ",\n" << indent(nesting_level + 1) << "v_";
    if (!state->is_phylum_instance) {
      out << instance_to_string(dep_instance, false, false);
    } else {
      out << instance_to_string(dep_instance, false, true);
    }
    out << ": ";
    dump_attribute_type(dep_instance, out);
  }
}

static void emit_synth_dep_actuals(SYNTH_FUNCTION_STATE* state, ostream& out) {
  for (auto it = state->regular_dependencies.begin(); it != state->regular_dependencies.end(); it++) {
    INSTANCE* dep_instance = *it;
    if (should_skip_synth_dependency(dep_instance)) continue;
    out << ", v_";
    if (!state->is_phylum_instance) {
      out << instance_to_string(dep_instance, false, false);
    } else {
      out << instance_to_string(dep_instance, false, true);
    }
  }
}

class FiberDependencyDumper {
public:
  static void dump(AUG_GRAPH* aug_graph, INSTANCE* sink, ostream& os) {

    int i, j;
    int n = aug_graph->instances.length;

    vector<INSTANCE*> relevant_instances;

    for (i = 0; i < n; i++) {
      INSTANCE* in = &aug_graph->instances.array[i];
      if (in->node != NULL && Declaration_KEY(in->node) == KEYpragma_call) {
        continue;
      }

      if (in->index == sink->index) {
        continue;
      }

      if (edgeset_kind(aug_graph->graph[in->index * n + sink->index])) {
        if (in->fibered_attr.fiber != NULL) {
          if (instance_is_synthesized(in) || instance_is_local(in)) {
            relevant_instances.push_back(in);
          }
        }
      }
    }

    if (relevant_instances.empty()) {
      return;
    }

    bool* scheduled = (bool*)alloca(sizeof(bool) * n);
    memset(scheduled, 0, sizeof(bool) * n);

    SccGraph scc_graph;
    scc_graph_initialize(&scc_graph, static_cast<int>(relevant_instances.size()));

    for (auto it = relevant_instances.begin(); it != relevant_instances.end(); it++) {
      INSTANCE* in = *it;
      scc_graph_add_vertex(&scc_graph, in);
    }

    for (auto it1 = relevant_instances.begin(); it1 != relevant_instances.end(); it1++) {
      INSTANCE* in1 = *it1;
      for (auto it2 = relevant_instances.begin(); it2 != relevant_instances.end(); it2++) {
        INSTANCE* in2 = *it2;
        if (in1->index == in2->index) {
          continue;
        }

        if (edgeset_kind(aug_graph->graph[in1->index * n + in2->index])) {
          scc_graph_add_edge(&scc_graph, in1, in2);
        }
      }
    }

    SCC_COMPONENTS* components = scc_graph_components(&scc_graph);

    if (include_comments) {
      os << indent() << "/* Fiber dependency SCC components:\n";
      nesting_level++;
      for (i = 0; i < components->length; i++) {
        SCC_COMPONENT* component = components->array[i];
        os << indent() << "Component " << i << ":\n";
        nesting_level++;
        for (j = 0; j < component->length; j++) {
          INSTANCE* in = (INSTANCE*)component->array[j];
          os << indent() << in << "\n";
        }
        nesting_level--;
      }
      nesting_level--;
      os << indent() << "*/\n";
    }

    dump_scc_helper(aug_graph, components, scheduled, os);

    scc_graph_destroy(&scc_graph);
  }

private:
  static void dump_scc_helper(AUG_GRAPH* aug_graph, SCC_COMPONENTS* components, bool* scheduled, ostream& os) {
    int component_count = components->length;
    int i;
    for (i = 0; i < component_count; i++) {
      SCC_COMPONENT* component = find_next_ready_component(aug_graph, components, scheduled);

      dump_scc_helper_dump(aug_graph, component, scheduled, os);
    }

    for (i = 0; i < component_count; i++) {
      SCC_COMPONENT* component = components->array[i];
      if (!already_scheduled(aug_graph, component, scheduled)) {
        fatal_error("some instances were not scheduled");
      }
    }
  }

  static void dump_scc_helper_dump(AUG_GRAPH* aug_graph, SCC_COMPONENT* component, bool* scheduled, ostream& os) {
    int i;

    if (already_scheduled(aug_graph, component, scheduled)) {
      return;
    }

    int n = aug_graph->instances.length;
    if (component->length == 0) {
      return;
    }

    for (i = 0; i < component->length; i++) {
      INSTANCE* in = (INSTANCE*)component->array[i];

      if (scheduled[in->index]) {
        continue;
      }

      bool dependency_ready = true;
      for (int j = 0; j < component->length && dependency_ready; j++) {
        INSTANCE* dependency_instance = (INSTANCE*)component->array[j];
        if (dependency_instance == in) {
          continue;
        }

        if (!scheduled[dependency_instance->index] &&
            edgeset_kind(aug_graph->graph[dependency_instance->index * n + in->index]) & DEPENDENCY_MAYBE_DIRECT) {
          dependency_ready = false;
        }
      }

      if (!dependency_ready) {
        continue;
      }

      scheduled[in->index] = true;
      {
        std::ostringstream tmp;
        CodeWriter tmp_cw(tmp);
        synth_impl_ptr->dump_synth_instance(in, tmp_cw);
        tmp_cw.flush();
        synth_impl_ptr->ctx.dumped_conditionals.clear();
        synth_impl_ptr->ctx.dumped_instances.clear();
        if (tmp_cw.has_code()) {
          os << indent() << tmp.str() << "\n";
        }
      }

      dump_scc_helper_dump(aug_graph, component, scheduled, os);
    }
  }

  static bool already_scheduled(AUG_GRAPH* aug_graph, SCC_COMPONENT* component, bool* scheduled) {
    for (int i = 0; i < component->length; i++) {
      INSTANCE* in = (INSTANCE*)component->array[i];
      if (!scheduled[in->index]) {
        return false;
      }
    }
    return true;
  }

  static SCC_COMPONENT* find_next_ready_component(AUG_GRAPH* aug_graph,
                                            SCC_COMPONENTS* components,
                                            bool* scheduled) {

    int n = aug_graph->instances.length;

    for (int i = 0; i < components->length; i++) {
      SCC_COMPONENT* component = components->array[i];

      if (already_scheduled(aug_graph, component, scheduled)) {
        continue;
      }

      bool component_ready = true;
      for (int j = 0; j < component->length && component_ready; j++) {
        INSTANCE* in = (INSTANCE*)component->array[j];

        for (int k = 0; k < components->length && component_ready; k++) {
          SCC_COMPONENT* other_component = components->array[k];
          if (other_component == component) {
            continue;
          }

          if (already_scheduled(aug_graph, other_component, scheduled)) {
            continue;
          }

          for (int l = 0; l < other_component->length; l++) {
            INSTANCE* other_in = (INSTANCE*)other_component->array[l];
            if (edgeset_kind(aug_graph->graph[other_in->index * n + in->index])) {
              component_ready = false;
              break;
            }
          }
        }
      }

      if (component_ready) {
        return component;
      }
    }

    fatal_error("no more components to schedule");
    return NULL;
  }
};

#ifdef APS2SCALA
static void dump_synth_functions(STATE* s, ostream& os)
#else  /* APS2SCALA */
static void dump_synth_functions(STATE* s, output_streams& oss)
#endif /* APS2SCALA */
{
#ifdef APS2SCALA
  ostream& oss = os;
#else /* !APS2SCALA */
  ostream& hs = oss.hs;
  ostream& cpps = oss.cpps;
  ostream& os = inline_definitions ? hs : cpps;

#endif /* APS2SCALA */

  os << "\n";

  synth_impl_ptr->ctx.synth_states = build_synth_functions_state(s);
  bool needs_fixed_point = s->loop_required;

  for (auto state_it = synth_impl_ptr->ctx.synth_states.begin(); state_it != synth_impl_ptr->ctx.synth_states.end(); state_it++) {
    SYNTH_FUNCTION_STATE* synth_functions_state = *state_it;
    synth_impl_ptr->ctx.current_state = synth_functions_state;

    if (include_comments) {
      os << indent() << "// " << synth_functions_state->source << " ("
         << (synth_functions_state->is_phylum_instance ? "phylum" : "aug-graph") << ")\n";
    }
    if (synth_functions_state->is_fiber_evaluation) {
      os << indent() << "val evaluated_map_" << synth_functions_state->fdecl_name
            << " = scala.collection.mutable.Map[Int"
         << ", Boolean]()"
         << "\n\n";
    }

    synth_impl_ptr->ctx.pending_helpers.clear();
    synth_impl_ptr->ctx.helper_counter = 0;
    synth_impl_ptr->ctx.eval_name = synth_functions_state->fdecl_name;
    synth_impl_ptr->ctx.phylum_type = decl_name(synth_functions_state->source_phy_graph->phylum);
    synth_impl_ptr->ctx.needs_fixed_point = needs_fixed_point;

    os << indent() << "def " << EVAL_PREFIX << synth_functions_state->fdecl_name << "(";
    os << "node: T_" << decl_name(synth_functions_state->source_phy_graph->phylum);
    emit_synth_dep_formals(synth_functions_state, os);
    os << ")";

    if (needs_fixed_point) {
      os << "(implicit " << LOOP_VAR << ": Boolean, changed: AtomicBoolean)";
    }

    os << ": ";

    if (synth_functions_state->is_fiber_evaluation) {
      os << "Unit";
    } else {
      dump_attribute_type(synth_functions_state->source, os);
    }
    os << " = {\n";
    nesting_level++;

    if (needs_fixed_point) {
      os << indent() << "if (!" <<  LOOP_VAR << ") {\n";
      nesting_level++;
    }

    if (synth_functions_state->is_fiber_evaluation) {
      os << indent() << "evaluated_map_" << synth_functions_state->fdecl_name
        << ".getOrElse(node.nodeNumber, false) match {\n";
      os << indent(nesting_level + 1) << "case true => ";
      os << "return ()\n";
    } else {
      os << indent() << instance_to_attr(synth_functions_state->source)
        << ".checkNode(node).status match {\n";
      os << indent(nesting_level + 1) << "case Evaluation.ASSIGNED => ";
      if (include_comments) {
        os << "{\n";
        nesting_level++;
        os << indent(nesting_level + 1) << "Debug.out(\"cache hit for \" + node + \" with value \" + " << instance_to_attr(synth_functions_state->source) << ".get(node));\n";
        os << indent(nesting_level + 1);
      }

      os << "return " << instance_to_attr(synth_functions_state->source) << ".get(node)\n";

      if (include_comments) {
        nesting_level--;
        os << indent(nesting_level + 1) << "}\n";
      }
    }
      
    os << indent(nesting_level + 1) << "case _ => ()\n";
    os << indent() << "};\n";

    if (needs_fixed_point) {
      nesting_level--;
      os << indent() << "}\n";
    }

    // Define anchor as alias for node so that dump_Expression's
    // anchor-passing logic (for phylum constructors) works correctly.
    os << indent() << "val anchor = node;\n";

    if (synth_functions_state->is_fiber_evaluation) {
      os << indent() << "node match {\n";
    } else {
      os << indent() << "val result = node match {\n";
    }
    nesting_level++;

    int aug_graph_idx = 0;
    for (auto it = synth_functions_state->aug_graphs.begin(); it != synth_functions_state->aug_graphs.end(); it++, aug_graph_idx++) {
      AUG_GRAPH* aug_graph = *it;
      int n = aug_graph->instances.length;

      synth_impl_ptr->ctx.aug_graph = aug_graph;
      synth_impl_ptr->ctx.blocks.push_back(matcher_body(top_level_match_m(aug_graph->match_rule)));

      os << indent() << "case " << matcher_pat(top_level_match_m(aug_graph->match_rule)) << " => {\n";
      nesting_level++;

      INSTANCE* aug_graph_instance = NULL;
      if (synth_functions_state->is_phylum_instance) {
        if (!find_instance(aug_graph, aug_graph->lhs_decl, synth_functions_state->source->fibered_attr, &aug_graph_instance)) {
          fatal_error("something is wrong with instances in aug graph %s", aug_graph_name(aug_graph));
        }
      } else {
        aug_graph_instance = synth_functions_state->source;
      }

      synth_impl_ptr->ctx.scope_block = linearize_block(aug_graph, aug_graph_instance);

      if (include_comments) {
        os << indent() << "/* Linearized schedule:\n";
        nesting_level++;
        print_linearized_block(synth_impl_ptr->ctx.scope_block, os);
        nesting_level--;
        os << indent() << "*/\n";
      }

      int src_idx = synth_functions_state->source->index;
      string src_attr = instance_to_attr(synth_functions_state->source);

      bool declared_is_circular = instance_circular(aug_graph_instance);
      bool depends_on_itself = edgeset_kind(aug_graph->graph[src_idx * n + src_idx]) != 0;

      if (!declared_is_circular && depends_on_itself) {
        aps_warning(aug_graph_instance->node, "Instance %s depends on itself but is not declared circular", instance_to_string(aug_graph_instance).c_str());
      }

      bool dump_fixed_point_loop = declared_is_circular && !instance_is_pure_shared_info(synth_functions_state->source);
      string node_get = ATTR_DECL_IS_SHARED_INFO(synth_functions_state->source->fibered_attr.attr) ? "" : "node";
      string node_assign = ATTR_DECL_IS_SHARED_INFO(synth_functions_state->source->fibered_attr.attr) ? "" : "node, ";

      if (dump_fixed_point_loop) {
        os << indent() << "{\n";
        nesting_level++;
        os << indent() << "val " << PREV_LOOP_VAR << src_idx << " = " << LOOP_VAR << ";\n";
        os << indent() << "val prevChanged" << src_idx << " = changed;\n";
        os << indent() << "val newChanged" << src_idx << " = new AtomicBoolean(false);\n";
        if (include_comments) {
          os << indent() << "var iterCount" << src_idx << " = 0;\n";
        }
        os << indent() << "do {\n";
        nesting_level++;
        os << indent() << "newChanged" << src_idx << ".set(false);\n";
        if (synth_functions_state->is_fiber_evaluation) {
          synth_impl_ptr->ctx.fiber_convergence = true;
        }
        os << indent() << "implicit val " << LOOP_VAR << ": Boolean = true;\n";
        os << indent() << "implicit val changed: AtomicBoolean = newChanged" << src_idx << ";\n";
      }

      if (synth_functions_state->is_fiber_evaluation) {
        if (include_comments && !dump_fixed_point_loop) {
          os << "\n";
        }

        
        string eval_name = synth_functions_state->fdecl_name;
        string phylum_type = decl_name(synth_functions_state->source_phy_graph->phylum);

        {
          std::ostringstream dep_formals_os, dep_actuals_os;
          int saved = nesting_level;
          nesting_level = 1;
          emit_synth_dep_formals(synth_functions_state, dep_formals_os);
          emit_synth_dep_actuals(synth_functions_state, dep_actuals_os);
          nesting_level = saved;
          synth_impl_ptr->ctx.dep_formals = dep_formals_os.str();
          synth_impl_ptr->ctx.dep_actuals = dep_actuals_os.str();
        }

        {
          int n_dep = aug_graph->instances.length;
          vector<INSTANCE*> relevant_instances;
          for (int idx = 0; idx < n_dep; idx++) {
            INSTANCE* in = &aug_graph->instances.array[idx];
            if (in->node != NULL && Declaration_KEY(in->node) == KEYpragma_call) continue;
            if (in->index == aug_graph_instance->index) continue;
            if (edgeset_kind(aug_graph->graph[in->index * n_dep + aug_graph_instance->index])) {
              if (in->fibered_attr.fiber != NULL) {
                if (instance_is_synthesized(in) || instance_is_local(in)) {
                  relevant_instances.push_back(in);
                }
              }
            }
          }

          if (ENABLE_FIBER_HELPERS) {
            for (size_t batch_start = 0; batch_start < relevant_instances.size(); batch_start += FIBER_DEP_BATCH_SIZE) {
              size_t batch_end = std::min(batch_start + (size_t)FIBER_DEP_BATCH_SIZE, relevant_instances.size());
              string helper_name = EVAL_FIBER_PREFIX + eval_name + "_g" + std::to_string(aug_graph_idx) +
                  "_h" + std::to_string(batch_start) + "_" + std::to_string(batch_end - 1);

              std::ostringstream helper_os;
              int saved_nesting = nesting_level;
              nesting_level = 1;

              helper_os << indent() << "private def " << helper_name
                        << "(node: T_" << phylum_type;
              emit_synth_dep_formals(synth_functions_state, helper_os);
              helper_os << ")";
              if (needs_fixed_point) {
                helper_os << "(implicit " << LOOP_VAR << ": Boolean, changed: AtomicBoolean)";
              }
              helper_os << ": Unit = {\n";
              nesting_level++;
              helper_os << indent() << "val anchor = node;\n";
              helper_os << indent() << "node match {\n";
              nesting_level++;
              helper_os << indent() << "case " << matcher_pat(top_level_match_m(aug_graph->match_rule)) << " => {\n";
              nesting_level++;

              for (size_t bi = batch_start; bi < batch_end; bi++) {
                INSTANCE* dep_in = relevant_instances[bi];
                std::ostringstream tmp;
                CodeWriter tmp_cw(tmp);
                synth_impl_ptr->dump_synth_instance(dep_in, tmp_cw);
                tmp_cw.flush();
                synth_impl_ptr->ctx.dumped_conditionals.clear();
                synth_impl_ptr->ctx.dumped_instances.clear();
                if (tmp_cw.has_code()) {
                  helper_os << indent() << tmp.str() << "\n";
                }
              }

              nesting_level--;
              helper_os << indent() << "}\n";
              helper_os << indent() << "case _ => ()\n";
              nesting_level--;
              helper_os << indent() << "}\n";
              nesting_level--;
              helper_os << indent() << "}\n";

              nesting_level = saved_nesting;
              synth_impl_ptr->ctx.pending_helpers.push_back(helper_os.str());

              os << indent() << helper_name << "(node";
              emit_synth_dep_actuals(synth_functions_state, os);
              os << ");\n";
            }
          } else {
            for (auto dep_it = relevant_instances.begin(); dep_it != relevant_instances.end(); dep_it++) {
              INSTANCE* dep_in = *dep_it;
              std::ostringstream tmp;
              CodeWriter tmp_cw(tmp);
              synth_impl_ptr->dump_synth_instance(dep_in, tmp_cw);
              tmp_cw.flush();
              synth_impl_ptr->ctx.dumped_conditionals.clear();
              synth_impl_ptr->ctx.dumped_instances.clear();
              if (tmp_cw.has_code()) {
                os << indent() << tmp.str() << "\n";
              }
            }
          }
        }

        {
          std::ostringstream tmp;
          CodeWriter tmp_cw(tmp);
          synth_impl_ptr->dump_synth_instance(aug_graph_instance, tmp_cw);
          tmp_cw.flush();
          synth_impl_ptr->ctx.dumped_conditionals.clear();
          synth_impl_ptr->ctx.dumped_instances.clear();
          if (tmp_cw.has_code()) {
            os << indent() << tmp.str() << "\n";
          }
        }
      }

      if (!synth_functions_state->is_fiber_evaluation) {
        if (dump_fixed_point_loop) {
          os << indent() << src_attr << ".assign(" << node_assign;
          { CodeWriter cw(os); synth_impl_ptr->dump_synth_instance(aug_graph_instance, cw); }
          os << ", changed);\n";
        } else {
          os << indent();
          { CodeWriter cw(os); synth_impl_ptr->dump_synth_instance(aug_graph_instance, cw); }
          os << "\n";
        }
      }

      if (dump_fixed_point_loop) {
        synth_impl_ptr->ctx.fiber_convergence = false;
        if (include_comments) {
          os << indent() << "iterCount" << src_idx << " += 1;\n";
          os << indent() << "Debug.out(\"fixed-point " << synth_functions_state->fdecl_name
             << " node=\" + node + \" iteration=\" + iterCount" << src_idx << ");\n";
        }
        nesting_level--;
        os << indent() << "} while (newChanged" << src_idx << ".get && !" << PREV_LOOP_VAR << src_idx << ")\n";
        os << indent() << "prevChanged" << src_idx << ".compareAndSet(false, newChanged" << src_idx << ".get);\n";
        if (!synth_functions_state->is_fiber_evaluation) {
          os << indent() << src_attr << ".get(" << node_get << ")\n";
        }
        nesting_level--;
        os << indent() << "}\n";
      }

      synth_impl_ptr->ctx.blocks.clear();
      synth_impl_ptr->ctx.dumped_conditionals.clear();
      synth_impl_ptr->ctx.dumped_instances.clear();

      nesting_level--;
      os << indent() << "}\n";
    }

    os << indent() << "case _ => throw new RuntimeException(\"failed pattern matching: \" + node)\n";

    nesting_level--;
    os << indent() << "};\n";

    if (synth_functions_state->is_fiber_evaluation) {
        os << indent() << "evaluated_map_" << synth_functions_state->fdecl_name << ".update(node.nodeNumber, true);\n";
    } else {
      os << indent() << instance_to_attr(synth_functions_state->source) << ".assign(node, result);\n";
      os << indent() << instance_to_attr(synth_functions_state->source) << ".get(node);\n";
    }

    if (!synth_functions_state->is_fiber_evaluation) {
      os << indent() << "result\n";
    }

    nesting_level--;
    os << indent() << "}\n\n";

    for (auto& helper : synth_impl_ptr->ctx.pending_helpers) {
      os << helper << "\n";
    }
    synth_impl_ptr->ctx.pending_helpers.clear();
  }

  destroy_synth_function_states(synth_impl_ptr->ctx.synth_states);
  synth_impl_ptr->ctx.synth_states.clear();
}

class SynthImpl : public SynthImplBase {
 public:
  typedef Implementation::ModuleInfo Super;
  class ModuleInfo : public Super {
   public:
    ModuleInfo(Declaration mdecl) : Implementation::ModuleInfo(mdecl) {}

    void note_top_level_match(Declaration tlm, GEN_OUTPUT& oss) { Super::note_top_level_match(tlm, oss); }

    void note_local_attribute(Declaration ld, GEN_OUTPUT& oss) {
      Super::note_local_attribute(ld, oss);
      Declaration_info(ld)->decl_flags |= LOCAL_ATTRIBUTE_FLAG;
    }

    void note_attribute_decl(Declaration ad, GEN_OUTPUT& oss) {
      Declaration_info(ad)->decl_flags |= ATTRIBUTE_DECL_FLAG;
      Super::note_attribute_decl(ad, oss);
    }

    void note_var_value_decl(Declaration vd, GEN_OUTPUT& oss) { Super::note_var_value_decl(vd, oss); }

#ifdef APS2SCALA
    void implement(ostream& os){
#else  /* APS2SCALA */
    void implement(output_streams& oss) {
#endif /* APS2SCALA */
        STATE* s = (STATE*)Declaration_info(module_decl) -> analysis_state;

#ifdef APS2SCALA
    ostream& oss = os;
#else
      ostream& hs = oss.hs;
      ostream& cpps = oss.cpps;
      ostream& os = inline_definitions ? hs : cpps;
#endif /* APS2SCALA */

    dump_synth_functions(s, oss);

    bool needs_fixed_point = s->original_state_dependency != 0;

#ifdef APS2SCALA
    os << indent() << "override def finish() : Unit = {\n";
#else  /* APS2SCALA */
      hs << indent() << "void finish()";
      if (!inline_definitions) {
        hs << ";\n";
        cpps << "void " << oss.prefix << "finish()";
      }
      INDEFINITION;
      os << " {\n";
#endif /* APS2SCALA */
    ++nesting_level;

    PHY_GRAPH* start_phy_graph = summary_graph_for(s, s->start_phylum);

    if (needs_fixed_point) {
      os << indent() << "implicit val " << LOOP_VAR << ": Boolean = false;\n";
      os << indent() << "implicit val changed: AtomicBoolean = new AtomicBoolean(false);\n";
    }
    os << indent() << "for (root <- t_" << decl_name(s->start_phylum) << ".nodes) {\n";
    ++nesting_level;
    int i;
    for (i = 0; i < start_phy_graph->instances.length; i++) {
      INSTANCE* in = &start_phy_graph->instances.array[i];

      if (!instance_is_synthesized(in))
        continue;

      string eval_name = instance_to_string_with_nodetype(s->start_phylum, &start_phy_graph->instances.array[i]);
      os << indent() << EVAL_PREFIX << eval_name << "(root);\n";
    }
    --nesting_level;
    os << indent() << "}\n";

#ifdef APS2SCALA
    os << indent() << "super.finish();\n";
#endif /* ! APS2SCALA */
    --nesting_level;
    os << indent() << "};\n";

    clear_implementation_marks(module_decl);
  }
};

Super* get_module_info(Declaration m) {
  return new ModuleInfo(m);
}

void implement_function_body(Declaration f, ostream& os) {
  dynamic_impl->implement_function_body(f, os);
}

void implement_value_use(Declaration vd, ostream& os) {
  int flags = Declaration_info(vd)->decl_flags;
  if (flags & LOCAL_ATTRIBUTE_FLAG) {
    int instance_index = Declaration_info(vd)->instance_index;
    INSTANCE* instance = &synth_impl_ptr->ctx.aug_graph->instances.array[instance_index];

    Type ty = value_decl_type(vd);
    Declaration ctype_decl = canonical_type_decl(canonical_type(ty));
    string target_name = instance_to_string_with_nodetype(ctype_decl, instance);

    os << EVAL_PREFIX << target_name << "(\n";
    int saved_nesting = nesting_level;
    nesting_level = std::max(nesting_level + 2, 1);
    os << indent() << "node";

    for (auto state_it = synth_impl_ptr->ctx.synth_states.begin(); state_it != synth_impl_ptr->ctx.synth_states.end(); state_it++) {
      SYNTH_FUNCTION_STATE* synth_function_state = *state_it;
      if (synth_function_state->fdecl_name == target_name) {
        for (auto dep_it = synth_function_state->regular_dependencies.begin();
             dep_it != synth_function_state->regular_dependencies.end(); dep_it++) {
          INSTANCE* source_instance = *dep_it;
          if (should_skip_synth_dependency(source_instance)) {
            continue;
          }
          os << ",\n" << indent();
          { CodeWriter cw(os); synth_impl_ptr->dump_synth_instance(source_instance, cw); }
        }
        break;
      }
    }

    nesting_level = saved_nesting;
    os << "\n" << indent() << ")";
  } else if (flags & ATTRIBUTE_DECL_FLAG) {
    if (ATTR_DECL_IS_INH(vd)) {
      os << "v_" << decl_name(vd);
    } else {
      os << "a" << "_" << decl_name(vd) << DEREF << "get";
    }
  } else if (flags & LOCAL_VALUE_FLAG) {
    os << "v" << LOCAL_UNIQUE_PREFIX(vd) << "_" << decl_name(vd);
  } else {
    aps_error(vd, "internal_error: What is special about this?");
  }
}

static Expression default_init(Default def) {
  switch (Default_KEY(def)) {
    case KEYsimple:
      return simple_value(def);
    case KEYcomposite:
      return composite_initial(def);
    default:
      return 0;
  }
}

static vector<std::set<Expression> > make_instance_assignment() {
  int n = synth_impl_ptr->ctx.aug_graph->instances.length;

  vector<std::set<Expression> > from(n);

  for (int i = 0; i < n; ++i) {
    INSTANCE* in = &synth_impl_ptr->ctx.aug_graph->instances.array[i];
    Declaration ad = in->fibered_attr.attr;
    if (ad != 0 && in->fibered_attr.fiber == 0 && ABSTRACT_APS_tnode_phylum(ad) == KEYDeclaration) {
      switch (Declaration_KEY(ad)) {
        case KEYattribute_decl:
          from[in->index].insert(default_init(attribute_decl_default(ad)));
          break;
        case KEYvalue_decl:
          from[in->index].insert(default_init(value_decl_default(ad)));
          break;
        default:
          break;
      }
    }
  }

  for (auto it = synth_impl_ptr->ctx.blocks.begin(); it != synth_impl_ptr->ctx.blocks.end(); it++) {
    Block block = *it;
    bool is_outermost = (it == synth_impl_ptr->ctx.blocks.begin());
    vector<std::set<Expression> > array(from);

    int step = 1;
    while (step <= 2) {
      Declarations ds = block_body(block);
      for (Declaration d = first_Declaration(ds); d; d = DECL_NEXT(d)) {
        switch (Declaration_KEY(d)) {
          case KEYnormal_assign: {
            if (INSTANCE* in = Expression_info(assign_rhs(d))->value_for) {
              if (in->index >= n) {
                fatal_error("bad index [normal_assign] for instance");
              }
              array[in->index].clear();
              if (assign_rhs(d) == NULL) {
                printf("Warning: assignment to %s is empty\n", instance_to_string(in).c_str());
              }

              array[in->index].insert(assign_rhs(d));
            }
            break;
          }
          case KEYcollect_assign: {
            if (INSTANCE* in = Expression_info(assign_rhs(d))->value_for) {
              if (in->index >= n) {
                fatal_error("bad index [collection_assign] for instance");
              }

              if (step == 1 && is_outermost) {
                array[in->index].clear();
              } else if (step == 2) {
                array[in->index].insert(assign_rhs(d));
              }
            }
            break;
          }
          default:
            break;
        }
      }

      step++;
    }

    from = array;
  }

  return from;
}

void dump_assignment(INSTANCE* in, Expression rhs, CodeWriter& cw) {
  Declaration ad = in != NULL ? in->fibered_attr.attr : NULL;
  Symbol asym = ad ? def_name(declaration_def(ad)) : 0;
  bool node_is_syntax = in->node == synth_impl_ptr->ctx.aug_graph->lhs_decl;

  if (in->fibered_attr.fiber != NULL) {
    if (rhs == NULL) {
      if (include_comments) {
        cw.comment() << "// " << in << "\n";
      }
      return;
    }

    Declaration assign = (Declaration)tnode_parent(rhs);
    Expression lhs = assign_lhs(assign);
    Declaration field = 0;
    switch (Expression_KEY(lhs)) {
      case KEYvalue_use:
        field = USE_DECL(value_use_use(lhs));
#ifdef APS2SCALA
        cw.code() << "a_" << decl_name(field) << ".";
        if (debug)
          cw.code() << "assign";
        else
          cw.code() << "set";
        cw.code() << "(" << rhs;
        if (synth_impl_ptr->ctx.fiber_convergence) {
          cw.code() << ", changed";
        }
        cw.code() << ");\n";
#else  /* APS2SCALA */
          cw.code() << "v_" << decl_name(field) << "=";
          switch (Default_KEY(value_decl_default(field))) {
            case KEYcomposite:
              cw.code() << composite_combiner(value_decl_default(field));
              break;
            default:
              cw.code() << as_val(value_decl_type(field)) << "->v_combine";
              break;
          }
          cw.code() << "(v_" << decl_name(field) << "," << rhs << ");\n";
#endif /* APS2SCALA */
        break;
      case KEYfuncall:
        field = field_ref_p(lhs);
        if (field == 0)
          fatal_error("what sort of assignment lhs: %d", tnode_line_number(assign));
        cw.code() << "a_" << decl_name(field) << DEREF;
        if (debug)
          cw.code() << "assign";
        else
          cw.code() << "set";
        cw.code() << "(" << field_ref_object(lhs) << "," << rhs;
        if (synth_impl_ptr->ctx.fiber_convergence) {
          cw.code() << ", changed";
        }
        cw.code() << ");\n";
        break;
      default:
        fatal_error("what sort of assignment lhs: %d", tnode_line_number(assign));
    }
    return;
  }

  if (in->node == 0 && ad != NULL) {
    if (rhs) {
      if (Declaration_info(ad)->decl_flags & LOCAL_ATTRIBUTE_FLAG) {
        cw.code() << "a" << LOCAL_UNIQUE_PREFIX(ad) << "_" << asym << DEREF;
        if (debug)
          cw.code() << "assign";
        else
          cw.code() << "set";
        cw.code() << "(node," << rhs << ");\n";
      } else {
        int i = LOCAL_UNIQUE_PREFIX(ad);
        if (i == 0) {
#ifdef APS2SCALA
          if (!def_is_constant(value_decl_def(ad))) {
            if (include_comments) {
              cw.comment() << "// v_" << asym << " is assigned/initialized by default.\n";
            }
          } else {
            if (include_comments) {
              cw.comment() << "// v_" << asym << " is initialized in module.\n";
            }
          }
#else
            cw.code() << "v_" << asym << " = " << rhs << ";\n";
#endif
        } else {
          cw.code() << "v" << i << "_" << asym << " = " << rhs << "; // local\n";
        }
      }
    } else {
      if (Declaration_KEY(ad) == KEYvalue_decl && !direction_is_collection(value_decl_direction(ad))) {
        aps_warning(ad, "Local attribute %s is apparently undefined", decl_name(ad));
      }
      if (include_comments) {
        cw.comment() << "// " << in << " is ready now\n";
      }
    }
    return;
  } else if (node_is_syntax) {
    if (ATTR_DECL_IS_SHARED_INFO(ad)) {
      if (include_comments) {
        cw.comment() << "// shared info for " << decl_name(in->node) << " is ready.\n";
      }
    } else if (ATTR_DECL_IS_UP_DOWN(ad)) {
      if (include_comments) {
        cw.comment() << "// " << decl_name(in->node) << "." << decl_name(ad) << " implicit.\n";
      }
    } else if (rhs) {
      if (Declaration_KEY(in->node) == KEYfunction_decl) {
        if (direction_is_collection(value_decl_direction(ad))) {
          std::cout << "Not expecting collection here!\n";
          cw.code() << "v_" << asym << " = somehow_combine(v_" << asym << "," << rhs << ");\n";
        } else {
          int i = LOCAL_UNIQUE_PREFIX(ad);
          if (i == 0)
            cw.code() << "v_" << asym << " = " << rhs << "; // function\n";
          else
            cw.code() << "v" << i << "_" << asym << " = " << rhs << ";\n";
        }
      } else {
        cw.code() << "a_" << asym << DEREF;
        if (debug)
          cw.code() << "assign";
        else
          cw.code() << "set";
        cw.code() << "(v_" << decl_name(in->node) << "," << rhs << ");\n";
      }
    } else {
      aps_warning(in->node, "Attribute %s.%s is apparently undefined", decl_name(in->node),
                  symbol_name(asym));

      if (include_comments) {
        cw.comment() << "// " << in << " is ready.\n";
      }
    }
    return;
  } else if (Declaration_KEY(in->node) == KEYvalue_decl) {
    if (rhs) {
      cw.code() << "a_" << asym << DEREF;
      if (debug)
        cw.code() << "assign";
      else
        cw.code() << "set";
      cw.code() << "(v_" << decl_name(in->node) << "," << rhs << ");\n";
    } else {
      if (include_comments) {
        cw.comment() << "// " << in << " is ready now.\n";
      }
    }
    return;
  }
}

void dump_rhs_instance_helper(AUG_GRAPH* aug_graph, BlockItem* item, INSTANCE* instance, CodeWriter& cw) {
  if (item == NULL) {
    if (include_comments) {
      cw.comment() << "// " << instance << " is ready now.\n";
    }
    return;
  }

  if (item->key == KEY_BLOCK_ITEM_INSTANCE) {
    struct block_item_instance* bi = (struct block_item_instance*)item;

    if (bi->instance != instance && bi->next != NULL) {
      dump_rhs_instance_helper(aug_graph, bi->next, instance, cw);
      return;
    }

    vector<std::set<Expression> > all_assignments = make_instance_assignment();
    std::set<Expression> relevant_assignments = all_assignments[instance->index];
    bool any_assignment_dump = false;

    if (!relevant_assignments.empty()) {
      vector<Expression> valid_rhs;
      for (auto it = relevant_assignments.begin(); it != relevant_assignments.end(); it++) {
        if (*it != NULL) valid_rhs.push_back(*it);
      }

      if (!valid_rhs.empty()) {
        any_assignment_dump = true;

        if (instance->fibered_attr.fiber != NULL) {
          bool first = true;
          for (auto it = valid_rhs.begin(); it != valid_rhs.end(); it++) {
            if (!first) cw.code() << indent();
            first = false;
            dump_assignment(instance, *it, cw);
          }
        } else if (valid_rhs.size() == 1) {
          dump_Expression(valid_rhs[0], cw.stream());
        } else {
          Declaration attr = instance->fibered_attr.attr;
          if (!direction_is_collection(value_decl_direction(attr))) {
            fatal_error("Multiple RHS for non-collection attribute %s", decl_name(attr));
          }
          Type vt = value_decl_type(attr);
          for (size_t i = 0; i < valid_rhs.size() - 1; i++) {
            cw.code() << as_val(vt) << ".v_combine(";
          }
          dump_Expression(valid_rhs[0], cw.stream());
          for (size_t i = 1; i < valid_rhs.size(); i++) {
            cw.code() << ", ";
            dump_Expression(valid_rhs[i], cw.stream());
            cw.code() << ")";
          }
        }
      }

      if (!any_assignment_dump) {
        fatal_error("should have dumped an assignment here");
      }

      return;
    }

    if (instance->fibered_attr.fiber != NULL) {
      auto direction = fibered_attr_direction(&instance->fibered_attr);
      auto directionStr = "";
      switch (direction)
      {
      case instance_inward:
        directionStr = "instance_inward";
        break;
      case instance_outward:
        directionStr = "instance_outward";
        break;
      case instance_local:
        directionStr = "instance_local";
        break;
      default:
        break;
      }

      if (include_comments) {
        cw.comment() << "/* did not find any assignment for this fiber attribute " << instance << " -> " << directionStr << " <-" <<" */";
      }
      return;
    } else {
      print_instance(instance, stdout);
      printf(" is a non-fiber instance, but no assignment found in this block. %d\n", if_rule_p(instance->fibered_attr.attr));
      fatal_error("crashed since non-fiber instance is missing an assignment");
    }
  } else if (item->key == KEY_BLOCK_ITEM_CONDITION) {
    struct block_item_condition* cond = (struct block_item_condition*)item;
    bool visited_if_stmt = std::find(synth_impl_ptr->ctx.dumped_conditionals.begin(), synth_impl_ptr->ctx.dumped_conditionals.end(), item) != synth_impl_ptr->ctx.dumped_conditionals.end();
    synth_impl_ptr->ctx.dumped_conditionals.push_back(item);

    if (!visited_if_stmt && instance->fibered_attr.fiber != NULL &&
        !ctx.eval_name.empty() && !ctx.phylum_type.empty() &&
        count_conditions(item) > COND_HELPER_THRESHOLD) {
      string helper_name = EVAL_FIBER_PREFIX + ctx.eval_name + "_cond" + std::to_string(ctx.helper_counter++);

      std::ostringstream helper_os;
      int saved_nesting = nesting_level;
      nesting_level = 1;

      helper_os << indent() << "private def " << helper_name
                << "(node: T_" << ctx.phylum_type << ctx.dep_formals << ")";
      if (ctx.needs_fixed_point) {
        helper_os << "(implicit " << LOOP_VAR << ": Boolean, changed: AtomicBoolean)";
      }
      helper_os << ": Unit = {\n";
      nesting_level++;
      helper_os << indent() << "val anchor = node;\n";
      helper_os << indent() << "node match {\n";
      nesting_level++;
      helper_os << indent() << "case " << matcher_pat(top_level_match_m(synth_impl_ptr->ctx.aug_graph->match_rule)) << " => {\n";
      nesting_level++;

      vector<BlockItem*> saved_cond_items(synth_impl_ptr->ctx.dumped_conditionals);
      vector<INSTANCE*> saved_dumped(synth_impl_ptr->ctx.dumped_instances);

      CodeWriter helper_cw(helper_os);
      helper_os << indent();
      dump_rhs_instance_helper(aug_graph, item, instance, helper_cw);
      helper_cw.flush();
      helper_os << "\n";

      synth_impl_ptr->ctx.dumped_conditionals = saved_cond_items;
      synth_impl_ptr->ctx.dumped_instances = saved_dumped;

      nesting_level--;
      helper_os << indent() << "}\n";
      helper_os << indent() << "case _ => ()\n";
      nesting_level--;
      helper_os << indent() << "}\n";
      nesting_level--;
      helper_os << indent() << "}\n";

      nesting_level = saved_nesting;
      ctx.pending_helpers.push_back(helper_os.str());

      cw.code() << indent() << helper_name << "(node" << ctx.dep_actuals << ");\n";
      return;
    }

    switch (ABSTRACT_APS_tnode_phylum(cond->condition))
    {
    case KEYDeclaration:
    {
      Declaration if_stmt = (Declaration)cond->condition;
      if (Declaration_KEY(if_stmt) != KEYif_stmt) {
        fatal_error("expected if statement, got %s %d", decl_name(if_stmt), Declaration_info(if_stmt));
      }

      if (!edgeset_kind(synth_impl_ptr->ctx.aug_graph->graph[cond->instance->index * synth_impl_ptr->ctx.aug_graph->instances.length + instance->index])) {
        printf("\n");
        print_instance(cond->instance, stdout);
        printf(" does not affect ");
        print_instance(instance, stdout);
        printf("\n");
        fatal_error("crashed since instance not affected by condition");
      }

      if (!visited_if_stmt) {
        cw.code() << "if (";
        dump_Expression(if_stmt_cond(if_stmt), cw.stream());
        cw.code() << ") {\n";
        nesting_level++;
      }
      synth_impl_ptr->ctx.blocks.push_back(if_stmt_if_true(if_stmt));
      if (!visited_if_stmt) {
        cw.code() << indent();
      }
      
      vector<INSTANCE*> dumped_instanced_positive(synth_impl_ptr->ctx.dumped_instances);
      dump_rhs_instance_helper(aug_graph, cond->next_positive, instance, cw);
      synth_impl_ptr->ctx.dumped_instances = dumped_instanced_positive;

      if (!visited_if_stmt) {
        synth_impl_ptr->ctx.blocks.pop_back();
        cw.code() << "\n";
        nesting_level--;
        cw.code() << indent() << "} else {\n";
        nesting_level++;
      }
      synth_impl_ptr->ctx.blocks.push_back(if_stmt_if_false(if_stmt));
      if (!visited_if_stmt) {
        cw.code() << indent();
      }

      vector<INSTANCE*> dumped_instanced_negative(synth_impl_ptr->ctx.dumped_instances);
      dump_rhs_instance_helper(aug_graph, cond->next_negative, instance, cw);
      synth_impl_ptr->ctx.dumped_instances = dumped_instanced_negative;

      synth_impl_ptr->ctx.blocks.pop_back();
      if (!visited_if_stmt) {
        nesting_level--;
        cw.code() << "\n";
        cw.code() << indent() << "}";
      }
	    break;
    }
    case KEYMatch:
    {
      Match m = (Match)cond->condition;
      Pattern p = matcher_pat(m);
      Declaration header = Match_info(m)->header;
      if (m == first_Match(case_stmt_matchers(header))) {
        Expression e = case_stmt_expr(header);
#ifdef APS2SCALA
        cw.code() << "{\n";
        nesting_level++;
        cw.code() << indent() << "val node" << instance->index << " = " << e << ";\n";
#else  /* APS2SCALA */
        Type ty = infer_expr_type(e);
        cw.code() << indent() << ty << " node" << instance->index << " = " << e << ";\n";
#endif /* APS2SCALA */
      }
#ifdef APS2SCALA
      cw.code() << indent() << "node" << instance->index << " match {\n";
      nesting_level++;
      cw.code() << indent() << "case " << p << " => {\n";
#else  /* APS2SCALA */
      cw.code() << indent() << "if (";
      dump_Pattern_cond(p, "node" + std::to_string(instance->index), cw.stream());
      cw.code() << ") {\n";
#endif /* APS2SCALA */
      nesting_level += 1;
#ifndef APS2SCALA
      dump_Pattern_bindings(p, cw.stream());
#endif /* APS2SCALA */
      Block if_true;
      Block if_false;
      if_true = matcher_body(m);
      if (MATCH_NEXT(m)) {
        if_false = 0;  //? Why not the nxt match ?
      } else {
        if_false = case_stmt_default(header);
      }

      synth_impl_ptr->ctx.blocks.push_back(if_true);
      cw.code() << indent();
      dump_rhs_instance_helper(aug_graph, cond->next_positive, instance, cw);
      cw.code() << "\n";
      synth_impl_ptr->ctx.blocks.pop_back();

#ifdef APS2SCALA
      nesting_level--;
      cw.code() << indent() << "}\n";
      cw.code() << indent() << "case _ => {\n";
      nesting_level++;
#else  /* APS2SCALA */
      cw.code() << "} else {\n";
#endif /* APS2SCALA */
      synth_impl_ptr->ctx.blocks.push_back(if_false);
      cw.code() << indent();
      dump_rhs_instance_helper(aug_graph, cond->next_negative, instance, cw);
      cw.code() << "\n";
      synth_impl_ptr->ctx.blocks.pop_back();

      nesting_level--;
#ifdef APS2SCALA
      cw.code() << indent() << "}\n";
      nesting_level--;
      cw.code() << indent() << "}\n";
      if (m == first_Match(case_stmt_matchers(header))) {
        nesting_level--;
        cw.code() << indent() << "}";
      }
#else  /* APS2SCALA */
      cw.code() << indent() << "}\n";
#endif /* APS2SCALA */
      
      break;
    }
    default:
      fatal_error("unhandled if statement type");
      break;
    }
  }
}

bool try_dump_funcall(Expression e, ostream& o) override {
  Declaration attr = attr_ref_p(e);
  if (attr == nullptr) return false;
  Declaration node = USE_DECL(value_use_use(first_Actual(funcall_actuals(e))));
  FIBERED_ATTRIBUTE fiber_attr = {attr, NULL};
  INSTANCE* instance;
  if (find_instance(synth_impl_ptr->ctx.aug_graph, node, fiber_attr, &instance)) {
    CodeWriter cw(o);
    dump_synth_instance(instance, cw);
    return true;
  }
  fatal_error("failed to find instance");
  return false; // unreachable
}

void dump_synth_instance(INSTANCE* instance, CodeWriter& cw) override {
  bool already_dumped = false;
  if (std::find(synth_impl_ptr->ctx.dumped_instances.begin(), synth_impl_ptr->ctx.dumped_instances.end(), instance) != synth_impl_ptr->ctx.dumped_instances.end()) {
    already_dumped = true;
  } else {
    synth_impl_ptr->ctx.dumped_instances.push_back(instance);
  }

  AUG_GRAPH* aug_graph = synth_impl_ptr->ctx.aug_graph;
  BlockItem* block = find_surrounding_block(synth_impl_ptr->ctx.scope_block, instance);

  Declaration node = instance->node;
  bool is_parent_instance = synth_impl_ptr->ctx.aug_graph->lhs_decl == instance->node;

  bool is_synthesized = instance_is_synthesized(instance);
  bool is_inherited = instance_is_inherited(instance);
  bool is_circular = edgeset_kind(synth_impl_ptr->ctx.aug_graph->graph[instance->index * synth_impl_ptr->ctx.aug_graph->instances.length + instance->index]);
  bool is_match_formal = check_is_match_formal(instance->fibered_attr.attr);
  bool is_available = is_match_formal || is_inherited;

  if (is_circular && already_dumped && !is_available) {
    cw.comment() << "/* circular dependency detected for " << instance << ", dumping as attribute access */ ";

    cw.code() << instance_to_attr(instance) << ".get(";
    if (instance->node == NULL) {
      cw.code() << "node";
    } else {
      cw.code() << "v_" << decl_name(instance->node);
    }
  
    cw.code() << ")";
    return;
  } else if (is_match_formal) {
    cw.code() << "v_" << instance_to_string(instance, false, synth_impl_ptr->ctx.current_state->is_phylum_instance);
  } else if (is_inherited) {
    if (is_parent_instance) {
      cw.code() << "v_" << instance_to_string(instance, false, synth_impl_ptr->ctx.current_state->is_phylum_instance);
    } else {
      dump_rhs_instance_helper(aug_graph, block, instance, cw);
    }
  } else if (is_synthesized) {
    if (is_parent_instance) {
      dump_rhs_instance_helper(aug_graph, block, instance, cw);
    } else {
      for (auto it = synth_impl_ptr->ctx.synth_states.begin(); it != synth_impl_ptr->ctx.synth_states.end(); it++) {
        SYNTH_FUNCTION_STATE* synth_function_state = *it;
        if (fibered_attr_equal(&synth_function_state->source->fibered_attr, &instance->fibered_attr)) {
          cw.code() << EVAL_PREFIX << synth_function_state->fdecl_name << "(\n";
          int saved_nesting = nesting_level;
          nesting_level = std::max(nesting_level + 2, 2);
          cw.code() << indent() << "v_" << decl_name(node);

          const std::vector<INSTANCE*>& dependencies = synth_function_state->regular_dependencies;
          for (auto it = dependencies.begin(); it != dependencies.end(); it++) {
            INSTANCE* source_instance = *it;

            if (should_skip_synth_dependency(source_instance)) {
              continue;
            }

            for (int i = 0; i < synth_impl_ptr->ctx.aug_graph->instances.length; i++) {
              INSTANCE* in = &synth_impl_ptr->ctx.aug_graph->instances.array[i];
              if (in->node == node && fibered_attr_equal(&in->fibered_attr, &source_instance->fibered_attr)) {
                cw.code() << ",\n" << indent();
                dump_synth_instance(in, cw);
              }
            }
          }
          nesting_level = saved_nesting;

          cw.code() << "\n" << indent() << ")";
          return;
        }
      }

      printf("failed to find synth function for instance ");
      print_instance(instance, stdout);
      printf("\n");
      fatal_error("internal error: failed to find synth function for instance");
    }
  } else {
    dump_rhs_instance_helper(aug_graph, block, instance, cw);
  }
}
}
;

Implementation* synth_impl = synth_impl_ptr = new SynthImpl();
