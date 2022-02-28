#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include "jbb.h"
#include "jbb-alloc.h"
#include "aps-ag.h"

int oag_debug;

// <ph,ch> representing the parent inherited attributes
CHILD_PHASE parent_inherited_group = { -1, -1 };

struct total_order_state
{ 
  short max_parent_ph;
  CHILD_PHASE* instance_groups;
  int *schedule; /* one-d array, indexed by instance number */
  VECTOR(Declaration) children;
};

typedef struct total_order_state TOTAL_ORDER_STATE;

/**
 * Utility function that schedules a single phase
 * @param phy_graph phylum graph
 * @param ph phase its currently scheduling for
 * @param circular boolean indicating whether this phase is dedicated for circular
 * @return number of nodes scheduled successfully for this phase 
 */
static int schedule_phase(PHY_GRAPH * phy_graph, int phase, BOOL circular) {
  int done = 0;
  int n = phy_graph->instances.length;
  int i, j;

  /* find inherited instances for the phase. */
  for (i = 0; i < n; ++i) {
    INSTANCE * in = & phy_graph->instances.array[i];
    if (instance_direction(in) == instance_inward &&
      instance_circular(in) == circular &&
      phy_graph->summary_schedule[i] == 0) {
      for (j = 0; j < n; ++j) {
        if (phy_graph->summary_schedule[j] == 0 &&
          phy_graph->mingraph[j * n + i] != no_dependency)
          break;
      }
      if (j == n) {
        phy_graph->summary_schedule[i] = -phase;
        done++;
        for (j = 0; j < n; ++j) {
          /* force extra dependencies */
          int sch = phy_graph->summary_schedule[j];
          if (sch != 0 && sch != -phase)
            phy_graph->mingraph[j * n + i] = indirect_control_dependency;
        }
        if (oag_debug & TOTAL_ORDER) {
          printf("%d- ", phase);
          print_instance( in , stdout);
          printf("\n");
        }
      }
    }
  }

  /* now schedule synthesized attributes */
  for (i = 0; i < n; ++i) {
    INSTANCE * in = & phy_graph->instances.array[i];
    if (instance_direction(in) == instance_outward &&
      instance_circular(in) == circular &&
      phy_graph->summary_schedule[i] == 0) {
      for (j = 0; j < n; ++j) {
        if (phy_graph->summary_schedule[j] == 0 &&
          phy_graph->mingraph[j * n + i] != no_dependency)
          break;
      }
      if (j == n) {
        phy_graph->summary_schedule[i] = phase;
        done++;
        for (j = 0; j < n; ++j) {
          /* force extra dependencies */
          int sch = phy_graph->summary_schedule[j];
          if (sch != 0 && sch != phase)
            phy_graph->mingraph[j * n + i] = indirect_control_dependency;
        }
        if (oag_debug & TOTAL_ORDER) {
          printf("%d+ ", phase);
          print_instance( in , stdout);
          printf("\n");
        }
      }
    }
  }

  return done;
}

/**
 * Utility function that calculates ph (phase) for each attribute of a phylum
 */
void schedule_summary_dependency_graph(PHY_GRAPH* phy_graph) {
  int n = phy_graph->instances.length;
  int phase = 0;
  int done = 0;
  BOOL cont = true;

  if (oag_debug & TOTAL_ORDER) {
    printf("Scheduling order for %s\n",decl_name(phy_graph->phylum));
  }
  
  int i, j;
  for (i = 0; i < n; ++i)
    phy_graph->summary_schedule[i] = 0;

  size_t circular_phase_size = (n+1) * sizeof(BOOL);
  BOOL* circular_phase = (BOOL*)HALLOC(circular_phase_size);
  memset(circular_phase, false, circular_phase_size);

  // Hold on to the flag indicating whether phase is circular or not
  phy_graph->cyclic_flags = circular_phase;

  int count_non_circular = 0, count_circular = 0;
  do {
    phase++;

    // Schedule non-circular attributes in this phase
    count_non_circular = schedule_phase(phy_graph, phase, false);
    if (count_non_circular) {
      done += count_non_circular;
      circular_phase[phase] = false;
      continue;
    }

    // Schedule circular attributes in this phase
    count_circular = schedule_phase(phy_graph, phase, true);
    if (count_circular) {
      done += count_circular;
      circular_phase[phase] = true;
      continue;
    }

  } while (count_non_circular || count_circular);

  if (done < n) {
    if (cycle_debug & PRINT_CYCLE) {
      for (i = 0; i < n; ++i) {
        INSTANCE* in = & phy_graph->instances.array[i];
        int s = phy_graph->summary_schedule[i];
        print_instance( in , stdout);
        switch (instance_direction( in )) {
          case instance_local:
            printf(" (a local attribute!) ");
            break;
          case instance_inward:
            printf(" inherited ");
            break;
          case instance_outward:
            printf(" synthesized ");
            break;
          default:
            printf(" (garbage direction!) ");
            break;
        }
        if (s != 0) {
          if (s < 0) printf(": phase -%d\n", -s);
          else printf(":phase +%d\n", s);
        } else {
          printf(" depends on ");
          for (j = 0; j < n; ++j) {
            if (phy_graph->summary_schedule[j] == 0 &&
              phy_graph->mingraph[j * n + i] != no_dependency) {
              INSTANCE* in2 = & phy_graph->instances.array[j];
              print_instance(in2, stdout);
              if (phy_graph->mingraph[j * n + i] == fiber_dependency)
                printf("(?)");
              putc(' ', stdout);
            }
          }
          putc('\n', stdout);
        }
      }
    }

    fatal_error("Cycle detected when scheduling phase %d for %s",
		  phase,decl_name(phy_graph->phylum));
  }
}

CONDITION instance_condition(INSTANCE *in)
{
  Declaration ad = in->fibered_attr.attr;
  if (in->node != 0) {
    return Declaration_info(in->node)->decl_cond;
  }
  if (ad == 0) {
    /* attribute removed in cyclic fibering. */
    CONDITION c;
    c.positive = -1;
    c.negative = -1;
    return c;
  }
  switch (ABSTRACT_APS_tnode_phylum(ad)) {
  case KEYMatch:
    return Match_info((Match)ad)->match_cond;
  default:
    return Declaration_info(ad)->decl_cond;
  }
}

#define CONDITION_IS_IMPOSSIBLE(cond) ((cond).positive & (cond).negative)
#define MERGED_CONDITION_IS_IMPOSSIBLE(cond1, cond2) (((cond1).positive|(cond2).positive) & ((cond1).negative|(cond2).negative))
#define MAX(x, y) (((x) > (y)) ? (x) : (y))
#define IS_VISIT_MARKER(node) (node->cto_instance == NULL)

/**
 * Utility function to print indent with single space character
 * @param indent indent count
 * @param stream output stream
 */ 
static void print_indent(int count, FILE *stream)
{
  while (count-- > 0) fprintf(stream, " ");
}

/**
 * Utility function to print the static schedule
 * @param cto CTO node
 * @param indent current indent count
 * @param stream output stream
 */ 
static void print_total_order(CTO_NODE *cto, int indent, FILE *stream)
{
  if (cto == NULL) return;

  print_indent(indent, stream);
  if (cto->cto_instance == NULL)
  {
    fprintf(stream, "visit marker");
    if (cto->child_decl != NULL) fprintf(stream, " (%s) ", decl_name(cto->child_decl));
  }
  else
  {
    print_instance(cto->cto_instance, stream);
    if (ABSTRACT_APS_tnode_phylum(cto->cto_instance) == KEYDeclaration) printf(" %s ", instance_circular(cto->cto_instance) ? "circular": "non-circular");
  }
  fprintf(stream, " <%d,%d>", cto->child_phase.ph, cto->child_phase.ch);
  fprintf(stream, "\n");
  indent++;

  if (cto->cto_if_true != NULL)
  {
    print_indent(indent-1, stream);
    fprintf(stream, "(true)\n");
    print_total_order(cto->cto_if_true, indent, stdout);
    fprintf(stream, "\n");
    print_indent(indent-1, stream);
    fprintf(stream, "(false)\n");
  }

  print_total_order(cto->cto_next, indent, stdout);
}

/**
 * Utility function to print debug info before raising fatal error
 * @param prev CTO node
 * @param stream output stream
 */ 
static void print_schedule_error_debug(AUG_GRAPH *aug_graph, TOTAL_ORDER_STATE* state, CTO_NODE* prev, FILE *stream)
{
  fprintf(stderr, "Instances (%s):\n", decl_name(aug_graph->syntax_decl));

  int i;
  for (i = 0; i < aug_graph->instances.length; i++)
  {
    print_instance(&aug_graph->instances.array[i], stream);
    fprintf(stream, " <%d, %d> (%s)\n", state->instance_groups[i].ph, state->instance_groups[i].ch, state->schedule[i] ? "scheduled" : "not-scheduled");
  }

  fprintf(stderr, "\nNot scheduled instances (%s):\n", decl_name(aug_graph->syntax_decl));

  for (i = 0; i < aug_graph->instances.length; i++)
  {
    if (!state->schedule[i])
    {
      print_instance(&aug_graph->instances.array[i], stream);
      fprintf(stream, " <%d, %d>\n", state->instance_groups[i].ph, state->instance_groups[i].ch);
    }
  }

  fprintf(stream, "Schedule so far:\n");
  // For debugging purposes, traverse all the way back
  while (prev != NULL && prev->cto_prev != NULL) prev = prev->cto_prev;

  print_total_order(prev, 0, stream);
}

/**
 * Utility function to determine if instance group is local or not
 * @param group instance group <ph,ch>
 * @return boolean indicating if instance group is local
 */ 
static bool group_is_local(CHILD_PHASE* group)
{
  return group->ph == 0 && group->ch == 0;
}

/**
 * Utility function to determine if instance is local or not
 * @param aug_graph Augmented dependency graph
 * @param instance_groups array of <ph,ch>
 * @param i instance index to test
 * @return boolean indicating if instance is local
 */ 
static bool instance_is_local(AUG_GRAPH *aug_graph, TOTAL_ORDER_STATE* state, const int i)
{
  CHILD_PHASE* group = &state->instance_groups[i];
  return group_is_local(group);
}

/**
 * Utility function to check if two child phase are equal
 * @param group_key1 first child phase struct
 * @param group_key2 second child phase struct
 * @return boolean indicating if two child phase structs are equal
 */ 
static bool child_phases_are_equal(CHILD_PHASE* group_key1, CHILD_PHASE* group_key2)
{
  return group_key1->ph == group_key2->ph && group_key1->ch == group_key2->ch;
}

/**
 * Returns true if two attribute instances belong to the same group
 * @param aug_graph Augmented dependency graph
 * @param cond current condition
 * @param state state
 * @param i instance index to test
 * @return boolean indicating if two attributes are in the same group
 */ 
static bool instances_in_same_group(AUG_GRAPH *aug_graph, TOTAL_ORDER_STATE* state, const int i, const int j)
{
  CHILD_PHASE *group_key1 = &state->instance_groups[i];
  CHILD_PHASE *group_key2 = &state->instance_groups[j];

  // Both are locals
  if (instance_is_local(aug_graph, state, i) && instance_is_local(aug_graph, state, j))
  {
    return i == j;
  }
  // Anything else
  else
  {
    return child_phases_are_equal(group_key1, group_key2);
  }
}

/**
 * Given a geneirc instance index it returns boolean indicating if its ready to be scheduled or not
 * @param aug_graph Augmented dependency graph
 * @param cond current condition
 * @param state state
 * @param i group index
 * @param j instance index to test
 * @return boolean indicating whether instance is ready to be scheduled
 */
static bool instance_ready_to_go(AUG_GRAPH *aug_graph, TOTAL_ORDER_STATE* state, const CONDITION cond, const int i, const int j)
{
  int k;
  EDGESET edges;
  int n = aug_graph->instances.length;
  
  for (k = 0; k < n; k++)
  {
    // Already scheduled then ignore
    if (state->schedule[k] != 0) continue;

    // If from the same group then ignore
    if (instances_in_same_group(aug_graph, state, i, k)) continue;

    int index = k * n + j;  // k (source) >--> j (sink) edge

    /* Look at all dependencies from j to i */
    for (edges = aug_graph->graph[index]; edges != NULL; edges=edges->rest)
    {
      /* If the merge condition is impossible, ignore this edge */
      if (MERGED_CONDITION_IS_IMPOSSIBLE(cond, edges->cond)) continue;

      if (oag_debug & DEBUG_ORDER)
      {
        // Can't continue with scheduling if a dependency with a "possible" condition has not been scheduled yet
        printf("This edgeset was not ready to be scheduled because of:\n");
        print_edgeset(edges, stdout);
        printf("\n");
      }

      return false;
    }
  }

  return true;
}

/**
 * Given a generic instance index it returns boolean indicating if its ready to be scheduled or not
 * @param aug_graph Augmented dependency graph
 * @param cond current condition
 * @param state state
 * @param i instance index to test
 * @return boolean indicating whether group is ready to be scheduled
 */
static bool group_ready_to_go(AUG_GRAPH *aug_graph, TOTAL_ORDER_STATE* state, const CONDITION cond, const int i)
{
  if (oag_debug & DEBUG_ORDER)
  {
    printf("Checking group readyness of: ");
    print_instance(&aug_graph->instances.array[i], stdout);
    printf("\n");
  }

  int n = aug_graph->instances.length;
  CHILD_PHASE group = state->instance_groups[i];
  int j;

  for (j = 0; j < n; j++)
  {
    CHILD_PHASE current_group = state->instance_groups[j];

    // Instance in the same group but cannot be considered
    if (instances_in_same_group(aug_graph, state, i, j))
    {
      if (state->schedule[j] != 0) continue;  // already scheduled

      if (!instance_ready_to_go(aug_graph, state, cond, i, j))
      {
        return false;
      }
    }
  }

  return true;
}

/**
 * Simple function to check if there is more to schedule in the group of index
 * @param aug_graph Augmented dependency graph
 * @param state state
 * @param parent_group parent group key
 * @return boolean indicating if there is more in this group that needs to be scheduled
 */
static bool is_there_more_to_schedule_in_group(AUG_GRAPH *aug_graph, TOTAL_ORDER_STATE* state, CHILD_PHASE *parent_group)
{
  int n = aug_graph->instances.length;
  int i;
  for (i = 0; i < n; i++)
  {
    // Instance in the same group but cannot be considered
    CHILD_PHASE *group_key = &state->instance_groups[i];

    // Check if in the same group
    if (child_phases_are_equal(parent_group, group_key))
    {
      if (state->schedule[i] == 0) return true;
    }
  }

  return false;
}

/**
 * Simple function to check if there is more to schedule in the group of index
 * @param aug_graph Augmented dependency graph
 * @param state array of <ph,ch> indexed by INSTANCE index
 * @param parent_group parent group key
 * @param min_ch min value for ch
 * @return boolean indicating if there is more in this group that needs to be scheduled
 */
static BOOL find_child_attribute(AUG_GRAPH *aug_graph, CONDITION cond, TOTAL_ORDER_STATE* state, short phase, CHILD_PHASE** ret_group)
{
  if (oag_debug & DEBUG_ORDER)
  {
    printf("Testing whether there is any child attributes in phase %d ready to be scheduled.\n", abs(phase));
  }

  int n = aug_graph->instances.length;
  int i;
  int current_ph = SHRT_MAX;
  CHILD_PHASE* current_group =  NULL;

  for (i = 0; i < n; i++)
  {
    // Instance in the same group but cannot be considered
    CHILD_PHASE* group_key = &state->instance_groups[i];

    // Check if in the same group AND its phase is less than current phase
    // This is needed to make sure we always schedule inherited attributes (negative phase) first
    if (abs(phase) == abs(group_key->ph) && group_key->ph < current_ph && state->schedule[i] == 0)
    {
      if (!group_ready_to_go(aug_graph, state, cond, i))
      {
        if (oag_debug & DEBUG_ORDER)
        {
          printf("Attribute not ready: ");
          print_instance(&aug_graph->instances.array[i], stdout);
          printf(" <%d,%d> \n", group_key->ph, group_key->ch);
        }
        continue;
      }

      if (state->schedule[i] == 0)
      {
        current_group = group_key;
        current_ph = group_key->ph;
      }
    }
  }

  if (current_group != NULL)
  {
    if (oag_debug & DEBUG_ORDER)
    {
      printf("Child phase <%d,%d> is ready to be scheduled.\n", current_group->ph, current_group->ch);
    }

    *ret_group = current_group;
    return true;
  }

  return false;
}

// Signature of function
static CTO_NODE* schedule_visits(AUG_GRAPH *aug_graph, CTO_NODE* prev, CONDITION cond, TOTAL_ORDER_STATE* state, int remaining, CHILD_PHASE *group, short parent_ph);
static CTO_NODE* schedule_visits_group(AUG_GRAPH *aug_graph, CTO_NODE* prev, CONDITION cond, TOTAL_ORDER_STATE* state, int remaining, CHILD_PHASE *group, short parent_ph);

/**
 * Function that throws an error if locals are scheduled out of order
 * @param aug_graph Augmented dependency graph
 * @param instance_groups array of <ph,ch> indexed by INSTANCE index
 */
static void assert_locals_order(AUG_GRAPH *aug_graph, TOTAL_ORDER_STATE* state)
{
  int n = aug_graph->instances.length;
  int i, j;

  for (i = 0; i < n; i++)
  {
    if (instance_is_local(aug_graph, state, i) &&
        if_rule_p(aug_graph->instances.array[i].fibered_attr.attr) &&
        state->schedule[i])
    {
      for (j = 0; j < i; j++)
      {
        if (instance_is_local(aug_graph, state, j) &&
            if_rule_p(aug_graph->instances.array[j].fibered_attr.attr) &&
            !state->schedule[j])
        {
          fprintf(stderr, "Scheduled local:\n\t");
          print_instance(&aug_graph->instances.array[i], stderr);
          fprintf(stderr, "\nBefore scheduling:\n\t");
          print_instance(&aug_graph->instances.array[j], stderr);
          fprintf(stderr, "\n");

          print_schedule_error_debug(aug_graph, state, NULL, stderr);

          fatal_error("Scheduling local attribute instances in an out of order fashion.");
        }
      }
    }
  }
}

/**
 * Utility function to look ahead in the total order
 * @param current CTO_NODE node
 * @param ph phase
 * @param ch child number
 * @param immediate immediately followed by
 * @param visit_marker_only look for visit marker only
 * @param any boolean pointer to set to true if found any
 */
static void followed_by(CTO_NODE* current, short ph, short ch, bool immediate, bool visit_marker_only, bool* any)
{
  if (current == NULL) return;

  if (current->child_phase.ph == ph && current->child_phase.ch == ch)
  {
    if ((visit_marker_only && IS_VISIT_MARKER(current)) || !visit_marker_only)
    {
      *any = true;
    }
  }
  else if (immediate)
  {
    return;
  }

  if (group_is_local(&current->child_phase) && if_rule_p(current->cto_instance->fibered_attr.attr))
  {
    followed_by(current->cto_if_true, ph, ch, immediate, visit_marker_only, any);
  }

  followed_by(current->cto_next, ph, ch, immediate, visit_marker_only, any);
}

/**
 * Utility function used by assert_total_order to check sanity of total order
 *  - After visit marker <ph,-1> there should be no attribute belonging to <ph,-1> or <-ph,-1>
 *  - Immediately before visit marker <ph,ch> should be attribute belonging to <-ph,ch>
 *  - Or immediately after visit marker <ph,ch> should be attribute belonging to <ph,ch>
 * @param current CTO_NODE node
 * @param prev_group <ph,ch> group
 */
static void total_order_sanity_check(CTO_NODE* current, CHILD_PHASE* prev_group)
{
  if (current == NULL) return;

  CHILD_PHASE* current_group = &current->child_phase;

  if (IS_VISIT_MARKER(current))
  {
    if (current->child_phase.ch == -1)
    {
      // End of total order
      if (current->cto_next == NULL) return;

      // Should immediately followed by <ph+1,*>
      bool followed_by_parent_inherited = false;
      followed_by(current->cto_next, -current->child_phase.ph, -1, false, false, &followed_by_parent_inherited);

      bool followed_by_parent_synthesized = false;
      followed_by(current->cto_next, current->child_phase.ph, -1, false, false, &followed_by_parent_synthesized);

      if (followed_by_parent_inherited || followed_by_parent_synthesized)
      {
        fatal_error("After visit marker <%d,-1> the phase should be greater than current phase.", current->child_phase.ph);
      }
    }
    else
    {
      // Boolean indicating whether visit marker was followed by child synthesized attribute(s) <ph,ch>
      bool followed_by_child_synthesized = false;
      followed_by(current->cto_next, current->child_phase.ph, current->child_phase.ch, true, false, &followed_by_child_synthesized);

      // Boolean indicating whether visit marker was followed by child inherited attribute(s) <-ph,ch>
      bool preceded_by_child_inherited = prev_group->ph == -current_group->ph && prev_group->ch == current_group->ch;

      if (!(followed_by_child_synthesized || preceded_by_child_inherited))
      {
        fatal_error("After visit marker <ph,ch> the phase should be <ph,ch>.");
      }
    }
  }

  if (group_is_local(&current->child_phase))
  {
    // Do not change the current group if instance is local
    current_group = prev_group;

    if (if_rule_p(current->cto_instance->fibered_attr.attr))
    {
      total_order_sanity_check(current->cto_if_true, &current->child_phase);
    }
  }

  total_order_sanity_check(current->cto_next, current_group);
}

/**
 * Helper function to assert child visits are consecutive
 * @param current head of total order linked list
 * @param ph head of total order linked list
 * @param ch head of total order linked list
 */
static void child_visit_consecutive_check(CTO_NODE *current, short ph, short ch)
{
  if (current == NULL) return;

  if (IS_VISIT_MARKER(current) && current->child_phase.ch == ch)
  {
    if (current->child_phase.ph != ph)
    {
      fatal_error("Out of order child visits, expected visit(%d,%d) but received visit(%d,%d)", ph, ch, current->child_phase.ph, current->child_phase.ch);
    }

    // Done with this phase. Now check the next phase of this child
    child_visit_consecutive_check(current->cto_next, ph + 1, ch);
    return;
  }

  if (group_is_local(&current->child_phase) && if_rule_p(current->cto_instance->fibered_attr.attr))
  {
    child_visit_consecutive_check(current->cto_if_true, ph, ch);
  }

  child_visit_consecutive_check(current->cto_next, ph, ch);
}

/**
 * This function asserts that visits for a particular child are consecutive
 * @param aug_graph Augmented dependency graph
 * @param state state
 * @param head head of total order linked list
 */
static void child_visit_consecutive(AUG_GRAPH *aug_graph, TOTAL_ORDER_STATE* state, CTO_NODE *head)
{
  int i;
  for (i = 0; i < state->children.length; i++)
  {
    child_visit_consecutive_check(head, 1, i);
  }
}

/**
 * This function asserts that there is a visit call for each phase of child
 * @param aug_graph Augmented dependency graph
 * @param instance_groups array of <ph,ch> indexed by INSTANCE index
 * @param head head of total order linked list
 */
static void child_visit_completeness(AUG_GRAPH* aug_graph, TOTAL_ORDER_STATE* state, CTO_NODE* head)
{
  size_t max_phases_size = sizeof(short) * state->children.length;
  short* max_phases = (short*)alloca(max_phases_size);
  memset(max_phases, (int)0, max_phases_size);

  int i, j;
  for (i = 0; i < aug_graph->instances.length; i++)
  {
    CHILD_PHASE group = state->instance_groups[i];
    if (group.ch != -1 && !group_is_local(&group))
    {
      max_phases[group.ch] = MAX(abs(max_phases[group.ch]), group.ph);
    }
  }

  for (i = 0; i < state->children.length; i++)
  {
    short max_phase = (short) max_phases[i];
    for (j = 1; j <= max_phase; j++)
    {
      bool any = false;
      followed_by(head, j, i, false, true, &any);

      if (!any)
      {
        fatal_error("Missing child %d visit call for phase %d", i, j);
      }
    }
  }
}

/**
 * Function that throws an error if phases are out of order
 * @param aug_graph
 * @param head head of linkedlist
 * @param state current value of ph being investigated
 */
static void assert_total_order(AUG_GRAPH *aug_graph, TOTAL_ORDER_STATE* state, CTO_NODE *head)
{
  // Condition #1: completeness of child visit calls
  child_visit_completeness(aug_graph, state, head);

  // Condition #2: general sanity of total order using visit markers
  total_order_sanity_check(head, &parent_inherited_group);

  // Condition #3: consecutiveness of child visit calls
  child_visit_consecutive(aug_graph, state, head);
}

/**
 * Utility function to handle transitions between groups
 * @param aug_graph Augmented dependency graph
 * @param prev previous CTO node
 * @param cond current CONDITION
 * @param instance_groups array of <ph,ch> indexed by INSTANCE index
 * @param remaining count of remaining instances to schedule
 * @param group parent group key
 * @return head of linked list
 */
static CTO_NODE* schedule_transitions(AUG_GRAPH *aug_graph, CTO_NODE* prev, CONDITION cond, TOTAL_ORDER_STATE* state, int remaining, CHILD_PHASE *group, short parent_ph)
{
  // If we find ourselves scheduling a <-ph,ch>, we need to (after putting in all the
  // instances in that group), we need to schedule the visit of the child (add a CTO
  // node with a null instance but with <ph,ch) and then ALSO schedule immediately
  // all the syn attributes of that child's phase. (<+ph,ch> group, if any).
  if (group->ph < 0 && group->ch > -1)
  {
    // Visit marker
    CTO_NODE *cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
    cto_node->cto_prev = prev;
    cto_node->cto_instance = NULL;
    cto_node->child_phase.ph = -group->ph;
    cto_node->child_phase.ch = group->ch;
    cto_node->child_decl = state->children.array[group->ch];
    cto_node->cto_next = schedule_visits_group(aug_graph, cto_node, cond, state, remaining, &cto_node->child_phase, parent_ph);
    return cto_node;
  }

  // If we find ourselves scheduling a <+ph,-1>, this means that after we put all these ones in the schedule
  // (which we should do as a group NOW), this visit phase is over. And we should mark it with a <ph,-1> marker in the CTO.
  // if (group->ph > 0 && group->ph < state->max_parent_ph && group->ch == -1)
  // {
  //   // Visit marker
  //   CTO_NODE *cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
  //   cto_node->cto_prev = prev;
  //   cto_node->cto_instance = NULL;
  //   cto_node->child_phase.ph = group->ph;
  //   cto_node->child_phase.ch = -1;
  //   cto_node->cto_next = schedule_visits(aug_graph, prev, cond, state, remaining, group, parent_ph);
  //   return cto_node;
  // }

  // Fallback to normal scheduler
  return schedule_visits(aug_graph, prev, cond, state, remaining /* no change */, group, parent_ph);
}

/**
 * Utility function to handle visit end marker
 * @param aug_graph Augmented dependency graph
 * @param prev previous CTO node
 * @param instance_groups array of <ph,ch> indexed by INSTANCE index
 * @return head of linked list
 */
static CTO_NODE* schedule_visit_end(AUG_GRAPH *aug_graph, CTO_NODE* prev, TOTAL_ORDER_STATE* state)
{
  CTO_NODE* cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
  cto_node->cto_prev = prev;
  cto_node->cto_instance = NULL;
  cto_node->child_phase.ph = state->max_parent_ph;
  cto_node->child_phase.ch = -1;
  return cto_node;
}

/**
 * Recursive scheduling function
 * @param aug_graph Augmented dependency graph
 * @param prev previous CTO node
 * @param cond current CONDITION
 * @param state state
 * @param remaining count of remaining instances to schedule
 * @param group parent group key
 * @return head of linked list
 */
static CTO_NODE* schedule_visits_group(AUG_GRAPH *aug_graph, CTO_NODE* prev, CONDITION cond, TOTAL_ORDER_STATE* state, int remaining, CHILD_PHASE *group, short parent_ph)
{
  int i;
  int n = aug_graph->instances.length;
  int sane_remaining = 0;
  CTO_NODE* cto_node = prev;
  
  /* If nothing more to do, we are done. */
  if (remaining == 0)
  {
    return schedule_visit_end(aug_graph, prev, state);
  }

  /* Outer condition is impossible, its a dead-end branch */
  if (CONDITION_IS_IMPOSSIBLE(cond)) return NULL;

  for (i = 0; i < n; i++)
  {
    INSTANCE *instance = &aug_graph->instances.array[i];
    CHILD_PHASE *instance_group = &state->instance_groups[i];

    // Already scheduled then ignore
    if (state->schedule[i] != 0) continue;

    sane_remaining++;

    // Check if everything is in the same group, don't check for dependencies
    // Locals will never end-up in this function
    if (instance_group->ph == group->ph && instance_group->ch == group->ch)
    {
      cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
      cto_node->cto_prev = prev;
      cto_node->cto_instance = instance;
      cto_node->child_phase.ph = group->ph;
      cto_node->child_phase.ch = group->ch;

      state->schedule[i] = 1; // instance has been scheduled (and will not be considered for scheduling in the recursive call)

      assert_locals_order(aug_graph, state);

      if (if_rule_p(instance->fibered_attr.attr))
      {
        printf("scheduling <%d,%d>\n", group->ph, group->ch);

        int cmask = 1 << (if_rule_index(instance->fibered_attr.attr));
        cond.negative |= cmask;
        cto_node->cto_if_false = schedule_visits(aug_graph, cto_node, cond, state, remaining-1, group, parent_ph);
        cond.negative &= ~cmask;
        cond.positive |= cmask;
        cto_node->cto_if_true = schedule_visits(aug_graph, cto_node, cond, state, remaining-1, group, parent_ph);
        cond.positive &= ~cmask;
      }
      else
      {
        printf("scheduling <%d,%d>\n", group->ph, group->ch);

        cto_node->cto_next = schedule_visits_group(aug_graph, cto_node, cond, state, remaining-1, group, parent_ph);
      }

      state->schedule[i] = 0; // Release it

      return cto_node;
    }
  }

  // Group is finished
  if (!is_there_more_to_schedule_in_group(aug_graph, state, group))
  {
    return schedule_transitions(aug_graph, cto_node, cond, state, remaining, group, parent_ph);
  }

  fflush(stdout);
  if (sane_remaining != remaining)
  {
    fprintf(stderr,"remaining out of sync %d != %d\n", sane_remaining, remaining);
  }

  print_schedule_error_debug(aug_graph, state, prev, stderr);
  fatal_error("Cannot make conditional total order!");

  return NULL;
}

/**
 * Recursive scheduling function
 * @param aug_graph Augmented dependency graph
 * @param prev previous CTO node
 * @param cond current CONDITION
 * @param instance_groups array of <ph,ch> indexed by INSTANCE index
 * @param remaining count of remaining instances to schedule
 * @return head of linked list
 */
static CTO_NODE* schedule_visits(AUG_GRAPH *aug_graph, CTO_NODE* prev, CONDITION cond, TOTAL_ORDER_STATE* state, int remaining, CHILD_PHASE *prev_group, short parent_ph)
{
  int i;
  int n = aug_graph->instances.length;
  int sane_remaining = 0;
  CTO_NODE* cto_node = NULL;

  bool just_started = remaining == n;
  
  /* If nothing more to do, we are done. */
  if (remaining == 0)
  {
    return schedule_visit_end(aug_graph, prev, state);
  }

  /* Outer condition is impossible, its a dead-end branch */
  if (CONDITION_IS_IMPOSSIBLE(cond)) return NULL;

  for (i = 0; i < n; i++)
  {
    INSTANCE *instance = &aug_graph->instances.array[i];
    CHILD_PHASE *group = &state->instance_groups[i];

    // Already scheduled then ignore
    if (state->schedule[i] != 0) continue;

    sane_remaining++;

    // If edgeset condition is not impossible then go ahead with scheduling
    if (group_ready_to_go(aug_graph, state, cond, i))
    {
      // If it is local then continue scheduling
      if (instance_is_local(aug_graph, state, i))
      {
        cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
        cto_node->cto_prev = prev;
        cto_node->cto_instance = instance;
        cto_node->child_phase.ch = group->ch;
        cto_node->child_phase.ph = group->ph;

        state->schedule[i] = 1; // instance has been scheduled (and will not be considered for scheduling in the recursive call)

        assert_locals_order(aug_graph, state);

        printf("scheduling <%d,%d>\n", group->ph, group->ch);

        if (if_rule_p(instance->fibered_attr.attr))
        {
          int cmask = 1 << (if_rule_index(instance->fibered_attr.attr));
          cond.negative |= cmask;
          cto_node->cto_if_false = schedule_visits(aug_graph, cto_node, cond, state, remaining-1, prev_group, parent_ph);
          cond.negative &= ~cmask;
          cond.positive |= cmask;
          cto_node->cto_if_true = schedule_visits(aug_graph, cto_node, cond, state, remaining-1, prev_group, parent_ph);
          cond.positive &= ~cmask;
        }
        else
        {
          cto_node->cto_next = schedule_visits(aug_graph, cto_node, cond, state, remaining-1, prev_group, parent_ph);
        }

        state->schedule[i] = 0; // Release it

        return cto_node;
      }
      // Instance is not local then delegate it to group scheduler
      else
      {
        // If we are scheduling child synthesized attribute outside of group scheduler
        // it means child synthesized attribute did not immediately followed child inherited
        // attribute thus add a visit marker <ph,ch>
        if (group->ph > 0 && group->ch > -1)
        {
          cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
          cto_node->cto_prev = prev;
          cto_node->cto_instance = NULL;
          cto_node->child_phase.ph = group->ph;
          cto_node->child_phase.ch = group->ch;
          cto_node->child_decl = state->children.array[group->ch];
          cto_node->cto_next = schedule_visits_group(aug_graph, prev, cond, state, remaining, group, parent_ph);
          return cto_node;
        }

        // If parent phase is greater than current parent attribute phase then we
        // have reached the end of previous phase and so add a end of parent phase
        // visit marker <ph,-1>
        if (abs(group->ph) > parent_ph && group->ch == -1)
        {
          cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
          cto_node->cto_prev = prev;
          cto_node->cto_instance = NULL;
          cto_node->child_phase.ph = parent_ph;
          cto_node->child_phase.ch = -1;
          cto_node->cto_next = schedule_visits_group(aug_graph, prev, cond, state, remaining, group, parent_ph + 1);
          return cto_node;
        }

        return schedule_visits_group(aug_graph, prev, cond, state, remaining, group, parent_ph);
      }
    }
  }

  fflush(stdout);
  if (sane_remaining != remaining)
  {
    fprintf(stderr, "remaining out of sync %d != %d\n", sane_remaining, remaining);
  }

  print_schedule_error_debug(aug_graph, state, prev, stderr);
  fatal_error("Cannot make conditional total order!");

  return NULL;
}

/**
 * Utility function to get children of augmented dependency graph as array of declarations
 * @param aug_graph Augmented dependency graph
 */
static void set_aug_graph_children(AUG_GRAPH *aug_graph, TOTAL_ORDER_STATE* state)
{
  Declaration source = aug_graph->match_rule;
  Declaration* children_arr = NULL;
  int children_count = 0;

  switch (Declaration_KEY(source))
  {
  case KEYtop_level_match:
  {
    Declaration formal = top_level_match_first_rhs_decl(source);
    while (formal != NULL)
    {
      children_count++;
      formal = DECL_NEXT(formal);
    }

    int i = 0;
    children_arr = (Declaration*)HALLOC(sizeof(Declaration) * children_count);
    formal = top_level_match_first_rhs_decl(source);
    while (formal != NULL)
    {
      children_arr[i++] = formal;
      formal = DECL_NEXT(formal);
    }

    break;
  }
  case KEYsome_class_decl:
  {
    Declaration child = first_Declaration(block_body(some_class_decl_contents(source)));
    while (child != NULL)
    {
      if (Declaration_KEY(child) == KEYvalue_decl)
      {
        children_count++;
      }
      child = DECL_NEXT(child);
    }

    int i = 0;
    children_arr = (Declaration*)HALLOC(sizeof(Declaration) * children_count);
    child = first_Declaration(block_body(some_class_decl_contents(source)));
    while (child != NULL)
    {
      if (Declaration_KEY(child) == KEYvalue_decl)
      {
        children_arr[i++] = child;
      }
      child = DECL_NEXT(child);
    }

    break;
  }
  case KEYsome_function_decl:
  {
    Declaration formal = first_Declaration(function_type_formals(some_function_decl_type(source)));
    while (formal != NULL)
    {
      children_count++;
      formal = DECL_NEXT(formal);
    }

    int i = 0;
    children_arr = (Declaration*)HALLOC(sizeof(Declaration) * children_count);
    formal = first_Declaration(function_type_formals(some_function_decl_type(source)));
    while (formal != NULL)
    {
      children_arr[i++] = formal;
      formal = DECL_NEXT(formal);
    }
    
    break;
  }
  }

  state->children.array = children_arr;
  state->children.length = children_count;
}

/**
 * Return phase (synthesized) or -phase (inherited)
 * for fibered attribute, given the phylum's summary dependence graph.
 */
int attribute_schedule(PHY_GRAPH *phy_graph, FIBERED_ATTRIBUTE* key)
{
  int n = phy_graph->instances.length;
  for (int i=0; i < n; ++i) {
    FIBERED_ATTRIBUTE* fa = &(phy_graph->instances.array[i].fibered_attr);
    if (fa->attr == key->attr && fa->fiber == key->fiber)
      return phy_graph->summary_schedule[i];
  }
  fatal_error("Could not find summary schedule for instance");
  return 0;
}

void schedule_augmented_dependency_graph(AUG_GRAPH *aug_graph) {
  int n = aug_graph->instances.length;
  CONDITION cond;
  int i, j;

  (void)close_augmented_dependency_graph(aug_graph);

  /** Now schedule graph: we need to generate a conditional total order. */

  if (oag_debug & PROD_ORDER) {
    printf("Scheduling conditional total order for %s\n",
	   aug_graph_name(aug_graph));
  }
  if (oag_debug & DEBUG_ORDER) {
    for (int i=0; i < n; ++i) {
      INSTANCE *in = &(aug_graph->instances.array[i]);
      print_instance(in,stdout);
      printf(": ");
      Declaration ad = in->fibered_attr.attr;
      Declaration chdecl;
    
      int j = 0, ch = -1;
      for (chdecl = aug_graph->first_rhs_decl; chdecl != 0; chdecl=DECL_NEXT(chdecl)) {
	if (in->node == chdecl) ch = j;
	++j;
      }
      if (in->node == aug_graph->lhs_decl || ch >= 0) {
	PHY_GRAPH *npg = Declaration_info(in->node)->node_phy_graph;
	int ph = attribute_schedule(npg,&(in->fibered_attr));
	printf("<%d,%d>\n",ph,ch);
      } else {
	printf("local\n");
      }
    }
  }

  size_t instance_groups_size = n * sizeof(CHILD_PHASE);
  CHILD_PHASE* instance_groups = (CHILD_PHASE*) alloca(instance_groups_size);
  memset(instance_groups, (int)0, instance_groups_size);

  for (i = 0; i < n; i++)
  {
    INSTANCE *in = &(aug_graph->instances.array[i]);
    Declaration ad = in->fibered_attr.attr;
    Declaration chdecl;
  
    int j = 0, ch = -1;
    for (chdecl = aug_graph->first_rhs_decl; chdecl != 0; chdecl=DECL_NEXT(chdecl))
    {
      if (in->node == chdecl) ch = j;
      ++j;
    }

    if (in->node == aug_graph->lhs_decl || ch >= 0)
    {
      PHY_GRAPH *npg = Declaration_info(in->node)->node_phy_graph;
      int ph = attribute_schedule(npg,&(in->fibered_attr));
      instance_groups[i].ph = (short) ph;
      instance_groups[i].ch = (short) ch;
    }
  }

  TOTAL_ORDER_STATE* state = (TOTAL_ORDER_STATE *)alloca(sizeof(TOTAL_ORDER_STATE));
  state->instance_groups = instance_groups;
  state->max_parent_ph = 1;

  size_t schedule_size = n * sizeof(int);
  int* schedule = (int *)alloca(schedule_size);

  /* This means: not scheduled yet */
  memset(schedule, (int)0, schedule_size);
  state->schedule = schedule;

  for (i = 0; i < n; i++)
  {
    CHILD_PHASE group = instance_groups[i];

    if (group.ch == -1)
    {
      state->max_parent_ph = MAX(abs(group.ph), state->max_parent_ph);
    }
  }

  // if (oag_debug & DEBUG_ORDER)
  {
    printf("\nInstances %s:\n", decl_name(aug_graph->syntax_decl));
    for (i = 0; i < n; i++)
    {
      INSTANCE *in = &(aug_graph->instances.array[i]);
      CHILD_PHASE group = instance_groups[i];
      print_instance(in, stdout);
      printf(": ");
      
      if (!group.ph && !group.ch)
      {
        printf("local\n");
      }
      else
      {
        printf("<%d,%d>\n", group.ph, group.ch);
      }
    }
  }

  // Find children of augmented graph: this will be used as argument to visit calls
  set_aug_graph_children(aug_graph, state);

  cond.negative = 0;
  cond.positive = 0;
  printf("\nSchedule for %s:\n", decl_name(aug_graph->syntax_decl));

  // visit marker matrix
  // rows: child number
  // columns: phase number


  // It is safe to assume inherited attribute of parents have no dependencies and should be scheduled right away
  aug_graph->total_order = schedule_visits_group(aug_graph, NULL, cond, state, n, &parent_inherited_group, 1);

  if (aug_graph->total_order == NULL)
  {
    fatal_error("Failed to create total order.");
  }

  // if (oag_debug & DEBUG_ORDER)
  {
    printf("\nSchedule for %s:\n", decl_name(aug_graph->syntax_decl));
    print_total_order(aug_graph->total_order, 0, stdout);
  }

  // Ensure generated total order is valid
  // assert_total_order(aug_graph, state, aug_graph->total_order);
}

void compute_oag(Declaration module, STATE *s) {
  int j;
  for (j=0; j < s->phyla.length; ++j) {
    schedule_summary_dependency_graph(&s->phy_graphs[j]);

    /* now perform closure */
    {
      int saved_analysis_debug = analysis_debug;
      int j;

      if (oag_debug & TYPE_3_DEBUG) {
	analysis_debug |= TWO_EDGE_CYCLE;
      }

      if (analysis_debug & DNC_ITERATE) {
	printf("\n**** After OAG schedule for phylum %d:\n\n",j);
      }

      if (analysis_debug & ASSERT_CLOSED) {
	for (j=0; j < s->match_rules.length; ++j) {
	  printf("Checking rule %d\n",j);
	  assert_closed(&s->aug_graphs[j]);
	}
      }

      dnc_close(s);

      analysis_debug = saved_analysis_debug;
    }
    if (analysis_debug & DNC_ITERATE) {
      printf ("\n*** After closure after schedule OAG phylum %d\n\n",j);
      print_analysis_state(s,stdout);
      print_cycles(s,stdout);
    }
      
    if (analysis_state_cycle(s)) break;
  }

  if (!analysis_state_cycle(s)) {
    for (j=0; j < s->match_rules.length; ++j) {
      schedule_augmented_dependency_graph(&s->aug_graphs[j]);
    }
    schedule_augmented_dependency_graph(&s->global_dependencies);
  }

  if (analysis_debug & (DNC_ITERATE|DNC_FINAL)) {
    printf("*** FINAL OAG ANALYSIS STATE ***\n");
    print_analysis_state(s,stdout);
    print_cycles(s,stdout);
  }
}
