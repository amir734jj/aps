/* Testing DNC with fibering of conditional attribute grammars
 * written in APS syntax.  First we initialize the graphs for
 * every phylum and for every production.  Then we interate
 * computing summary graphs and then augmented depedency graphs
 * for productions until we reach a fixed point.
 */
#include <stdio.h>
#include "alloc.h"
#include "aps-ag.h"

int analysis_debug = 0;


/*** FUNCTIONS FOR INSTANCES */

BOOL fibered_attr_equal(FIBERED_ATTRIBUTE *fa1, FIBERED_ATTRIBUTE *fa2) {
  return fa1->attr == fa2->attr && fa1->fiber == fa2->fiber;
}

enum instance_direction fibered_attr_direction(FIBERED_ATTRIBUTE *fa) {
  if (ATTR_DECL_IS_SYN(fa->attr)) {
    if (fa->fiber_is_reverse) {
      return instance_inward;
    } else {
      return instance_outward;
    }
  } else if (ATTR_DECL_IS_INH(fa->attr)) {
    if (fa->fiber_is_reverse) {
      return instance_outward;
    } else {
      return instance_inward;
    }
  } else {
    return instance_local;
  }
}

enum instance_direction invert_direction(enum instance_direction dir) {
  switch (dir) {
  case instance_inward: return instance_outward;
  case instance_outward: return instance_inward;
  case instance_local: return instance_local;
  }
  fatal_error("control flow fell through invert_direction");
}

enum instance_direction instance_direction(INSTANCE *i) {
  enum instance_direction dir = fibered_attr_direction(&i->fibered_attr);
  if (i->node == NULL) {
    return dir;
  } else if (DECL_IS_LHS(i->node)) {
    return dir;
  } else if (DECL_IS_RHS(i->node)) {
    return invert_direction(dir);
  } else if (DECL_IS_LOCAL(i->node)) {
    return instance_local;
  } else {
    fatal_error("%d: unknown attributed node",tnode_line_number(i->node));
  }
}


/*** FUNCTIONS FOR EDGES ***/

DEPENDENCY dependency_join(DEPENDENCY k1, DEPENDENCY k2)
{
  return k1 | k2;
}

DEPENDENCY dependency_trans(DEPENDENCY k1, DEPENDENCY k2)
{
  // complicated because fiber trans non-fiber = non-fiber
  // but maybe-carrying trans non-carrying = non-carrying
  // and trans never gives direct.
  if (k1 == no_dependency || k2 == no_dependency) return no_dependency;
  return (((k1 & DEPENDENCY_NOT_JUST_FIBER)|
	   (k2 & DEPENDENCY_NOT_JUST_FIBER)) |
	  ((k1 & DEPENDENCY_MAYBE_CARRYING)&
	   (k2 & DEPENDENCY_MAYBE_CARRYING)) |
	  SOME_DEPENDENCY);
}

DEPENDENCY dependency_indirect(DEPENDENCY k)
{
  return k&~DEPENDENCY_MAYBE_DIRECT;
}

int worklist_length(AUG_GRAPH *aug_graph) {
  int i = 0;
  EDGESET e;
  for (e = aug_graph->worklist_head; e != NULL; e = e->next_in_edge_worklist) {
    if (e->next_in_edge_worklist == NULL && e != aug_graph->worklist_tail)
      fatal_error("Worklist structure corrupted");
    ++i;
  }
  return i;
}

void add_to_worklist(EDGESET node, AUG_GRAPH *aug_graph) {
  if (aug_graph != NULL && node->next_in_edge_worklist == NULL) {
    if (aug_graph->worklist_tail != node) {
      if (analysis_debug & WORKLIST_CHANGES) {
	printf("Worklist gets %d ",worklist_length(aug_graph)+1);
	print_edgeset(node,stdout);
      }
      if (aug_graph->worklist_tail == NULL) {
	if (aug_graph->worklist_head != NULL)
	  fatal_error("Worklist head is wrong!");
	aug_graph->worklist_head = node;
      } else {
	if (aug_graph->worklist_head == NULL)
	  fatal_error("Worklist head is NULL");
	aug_graph->worklist_tail->next_in_edge_worklist = node;
      }
      aug_graph->worklist_tail = node;
    }
  }
}

/** Remove an edgeset from the worklist if it is in it.
 * There are multiple cases: <ul>
 * <li> The element is at the head of the list.
 * <li> The element is at the tail of a list.
 * <li> The element is in the middle somewhere.
 * <li> The element is not in the worklist. </ul>
 */
void remove_from_worklist(EDGESET node, AUG_GRAPH *aug_graph) {
  if (node->next_in_edge_worklist != NULL) {
    /* hard work */
    EDGESET *ep = &aug_graph->worklist_head;
    while (*ep != node) {
      if (*ep == NULL) fatal_error("Not in worklist!");
      ep = &(*ep)->next_in_edge_worklist;
    }
    *ep = node->next_in_edge_worklist;
  } else if (node == aug_graph->worklist_tail) {
    if (node == aug_graph->worklist_head) {
      aug_graph->worklist_head = NULL;
      aug_graph->worklist_tail = NULL;
    } else {
      EDGESET e = aug_graph->worklist_head;
      while (e->next_in_edge_worklist != node) {
	if (e->next_in_edge_worklist == NULL)
	  fatal_error("Worklist in two pieces");
	e = e->next_in_edge_worklist;
      }
      e->next_in_edge_worklist = NULL;
      aug_graph->worklist_tail = e;
    }
  }
  node->kind = no_dependency;
}

static EDGESET edgeset_freelist = NULL;
EDGESET new_edgeset(INSTANCE *source,
		    INSTANCE *sink,
		    CONDITION *cond,
		    DEPENDENCY kind) {
  EDGESET new_edge;
  if (edgeset_freelist == NULL) {
    new_edge = (EDGESET)HALLOC(sizeof(struct edgeset));
  } else {
    new_edge = edgeset_freelist;
    edgeset_freelist = edgeset_freelist->rest;
    if (new_edge->kind != no_dependency)
      fatal_error("edgeset freelist corruption! (1)");
  }
  new_edge->rest = NULL;
  new_edge->source = source;
  new_edge->sink = sink;
  new_edge->cond = *cond;
  new_edge->kind = kind;
  new_edge->next_in_edge_worklist = NULL;
  if (analysis_debug & ADD_EDGE) {
    print_edgeset(new_edge,stdout);
  }
  return new_edge;
}

void free_edge(EDGESET old, AUG_GRAPH *aug_graph) {
  old->rest = edgeset_freelist;
  if (old->kind == no_dependency)
    fatal_error("edgeset freelist corruption! (2)");
  old->kind = no_dependency;
  remove_from_worklist(old,aug_graph);
  edgeset_freelist = old;
}

void free_edgeset(EDGESET es, AUG_GRAPH *aug_graph) {
  while (es != NULL) {
    EDGESET old = es;
    es = es->rest;
    /* printf("Freeing 0x%x\n",old); */
    free_edge(old,aug_graph);
  }
}

DEPENDENCY edgeset_kind(EDGESET es) {
  DEPENDENCY max=no_dependency;
  for (; es != NULL; es=es->rest) {
    max=dependency_join(max,es->kind);
  }
  return max;
}

DEPENDENCY edgeset_lowerbound(EDGESET es) {
  DEPENDENCY max=no_dependency;
  for (; es != NULL; es=es->rest) {
    if (es->cond.positive|es->cond.negative) continue;
    max=dependency_join(max,es->kind);
  }
  return max;
}

EDGESET add_edge(INSTANCE *source,
		 INSTANCE *sink,
		 CONDITION *cond,
		 DEPENDENCY kind,
		 EDGESET current,
		 AUG_GRAPH *aug_graph) {
  if (current == NULL) {
    EDGESET new_edge=new_edgeset(source,sink,cond,kind);
    add_to_worklist(new_edge,aug_graph);
    return new_edge;
  } else {
    enum CONDcompare comp = cond_compare(cond,&current->cond);
    if (current->source != source ||
	current->sink != sink) fatal_error("edgeset mixup");
    if (AT_MOST(kind,current->kind) &&
	(comp == CONDlt || comp == CONDeq)) {
      /* already entailed (or equal) */
      return current;
    } else if (AT_MOST(current->kind,kind) &&
	       (comp == CONDgt || comp == CONDeq)) {
      /* current entry is entailed, so remove */
      EDGESET rest = current->rest;
      free_edge(current,aug_graph);
      return add_edge(source,sink,cond,kind,rest,aug_graph);
    } else if (current->kind == kind && comp == CONDcomp) {
      /* edges are complements of each other */
      EDGESET rest = current->rest;
      CONDITION merged;
      unsigned common;
      merged.positive = cond->positive|current->cond.positive;
      merged.negative = cond->negative|current->cond.negative;
      common = merged.positive&merged.negative;
      if (common != 0 && !ONE_BIT(common))
	fatal_error("bad condition computation");
      merged.positive &= ~common;
      merged.negative &= ~common;
      rest = add_edge(source,sink,&merged,kind,rest,aug_graph);
      free_edge(current,aug_graph);
      return rest;
    } else {
      /* there is nothing to do */
      current->rest =
	add_edge(source,sink,cond,kind,current->rest,aug_graph);
      return current;
    }
  }
}

void add_edge_to_graph(INSTANCE *source,
		       INSTANCE *sink,
		       CONDITION *cond,
		       DEPENDENCY kind,
		       AUG_GRAPH *aug_graph) {
  int index = source->index*(aug_graph->instances.length)+sink->index;

  aug_graph->graph[index] =
    add_edge(source,sink,cond,kind,aug_graph->graph[index],aug_graph);
}

void add_transitive_edge_to_graph(INSTANCE *source,
				  INSTANCE *sink,
				  CONDITION *cond1,
				  CONDITION *cond2,
				  DEPENDENCY kind1,
				  DEPENDENCY kind2,
				  AUG_GRAPH *aug_graph) {
  CONDITION cond;
  DEPENDENCY kind=dependency_trans(kind1,kind2);
  cond.positive = cond1->positive|cond2->positive;
  cond.negative = cond1->negative|cond2->negative;
  if (cond.positive & cond.negative) return;
  add_edge_to_graph(source,sink,&cond,kind,aug_graph);
}
    

/*** AUXILIARY FUNCTIONS FOR IFS ***/

static void *count_if_rules(void *pint, void *node) {
  int *count = (int *)pint;
  Match m;
  if (ABSTRACT_APS_tnode_phylum(node) == KEYDeclaration) {
    Declaration decl = (Declaration)node;
    switch (Declaration_KEY(decl)) {
    case KEYmodule_decl: return NULL;
    case KEYif_stmt:
      Declaration_info(decl)->if_index = *count;
      ++*count;
      break;
    case KEYcase_stmt:
      for (m = first_Match(case_stmt_matchers(decl)); m; m=MATCH_NEXT(m)) {
	Match_info(m)->if_index = *count;
	++*count;
      }
      break;
    default: break;
    }
  }
  return pint;
}

static void *get_if_rules(void *varray, void *node) {
  void** array = (void**)varray;
  Match m;
  if (ABSTRACT_APS_tnode_phylum(node) == KEYDeclaration) {
    Declaration decl = (Declaration)node;
    switch (Declaration_KEY(decl)) {
    case KEYmodule_decl: return NULL;
    case KEYif_stmt:
      array[Declaration_info(decl)->if_index] = decl;
      break;
    case KEYcase_stmt:
      for (m = first_Match(case_stmt_matchers(decl)); m; m=MATCH_NEXT(m)) {
	array[Match_info(m)->if_index] = m;
      }
      break;
    default: break;
    }
  }
  return array;
}

/* link together all the conditions in a case */
static void *get_match_tests(void *vpexpr, void *node)
{
  Expression* pexpr = (Expression*)vpexpr;
  switch (ABSTRACT_APS_tnode_phylum(node)) {
  default:
    return NULL;
  case KEYMatch:
    traverse_Pattern(get_match_tests,vpexpr,matcher_pat((Match)node));
    Match_info((Match)node)->match_test = *pexpr;
    return NULL;
  case KEYMatches:
  case KEYPatternActuals:
    break;
  case KEYPattern:
    { Pattern pat = (Pattern)node;
      switch (Pattern_KEY(pat)) {
      case KEYcondition:
	{ Expression cond = condition_e(pat);
	  Expression expr = *pexpr;
	  Expression_info(cond)->next_expr = expr;
	  *pexpr = cond;
	}
	break;
      default:
	break;
      }
    }
  }
  return vpexpr;
}

static Expression if_rule_test(void* if_rule) {
  switch (ABSTRACT_APS_tnode_phylum(if_rule)) {
  case KEYDeclaration:
    return if_stmt_cond((Declaration)if_rule);
  case KEYMatch:
    return Match_info((Match)if_rule)->match_test;
  default:
    fatal_error("%d: unknown if_rule",tnode_line_number(if_rule));
  }
}

static CONDITION* if_rule_cond(void *if_rule) {
  switch (ABSTRACT_APS_tnode_phylum(if_rule)) {
  case KEYDeclaration:
    return &Declaration_info((Declaration)if_rule)->decl_cond;
  case KEYMatch:
    return &Match_info((Match)if_rule)->match_cond;
  default:
    fatal_error("%d: unknown if_rule",tnode_line_number(if_rule));
  }
}

int if_rule_index(void *if_rule) {
  switch (ABSTRACT_APS_tnode_phylum(if_rule)) {
  case KEYDeclaration:
    return Declaration_info((Declaration)if_rule)->if_index;
  case KEYMatch:
    return Match_info((Match)if_rule)->if_index;
  default:
    fatal_error("%d: unknown if_rule",tnode_line_number(if_rule));
    /*NOTREACHED*/
    return 0;
  }
}
 
int if_rule_p(void *if_rule) {
  switch (ABSTRACT_APS_tnode_phylum(if_rule)) {
  case KEYDeclaration:
    return Declaration_KEY(if_rule) == KEYif_stmt;
  case KEYMatch:
    return TRUE;
  default:
    return 0;
  }
}
 
static void *init_decl_cond(void *vcond, void *node) {
  CONDITION *cond = (CONDITION *)vcond;
  Declaration decl = (Declaration)node; /*but maybe not*/
  switch (ABSTRACT_APS_tnode_phylum(node)) {
  case KEYDeclaration:
    Declaration_info(decl)->decl_cond = *cond;
    switch (Declaration_KEY(decl)) {
    case KEYmodule_decl: return NULL;
    case KEYif_stmt:
      {
	Block if_true = if_stmt_if_true(decl);
	Block if_false = if_stmt_if_false(decl);
	int index = Declaration_info(decl)->if_index;
	CONDITION new_cond;
	new_cond.positive = cond->positive | (1 << index);
	new_cond.negative = cond->negative;
	traverse_Block(init_decl_cond,&new_cond,if_true);
	new_cond.positive = cond->positive;
	new_cond.negative = cond->negative | (1 << index);
	traverse_Block(init_decl_cond,&new_cond,if_false);
      }
      return NULL;
    case KEYcase_stmt:
      {
	Matches ms = case_stmt_matchers(decl);
	Expression testvar = case_stmt_expr(decl);
	CONDITION new_cond = *cond;
	Match m;

	Expression_info(testvar)->next_expr = 0;
	traverse_Matches(get_match_tests,&testvar,ms);
	for (m = first_Match(ms); m; m=MATCH_NEXT(m)) {
	  int index = Match_info(m)->if_index;
	  Match_info(m)->match_cond = new_cond;
	  new_cond.positive |= (1 << index); /* first set it */
	  traverse_Block(init_decl_cond,&new_cond,matcher_body(m));
	  new_cond.positive &= ~(1 << index); /* now clear it */
	  new_cond.negative |= (1 << index); /* set negative for rest */
	}
	traverse_Block(init_decl_cond,&new_cond,case_stmt_default(decl));
      }
      return NULL;
    default: break;
    }
  default:
    break;
  }
  return vcond;
}


/*** AUXILIARY FUNCTIONS FOR INSTANCES ***/

Declaration proc_call_p(Expression e) {
  Declaration decl = local_call_p(e);
  if (decl != NULL && Declaration_KEY(decl) == KEYprocedure_decl)
    return decl;
  else
    return NULL;
}

static void assign_instance(INSTANCE *array, int index,
			    Declaration attr, FIBER fiber, BOOL frev,
			    Declaration node) {
  if (attr == NULL) fatal_error("null instance!");
  if (array == NULL) return;
  array[index].fibered_attr.attr = attr;
  array[index].fibered_attr.fiber = fiber;
  array[index].fibered_attr.fiber_is_reverse = frev;
  array[index].node = node;
  array[index].index = index;
  if (analysis_debug & CREATE_INSTANCE) {
    printf("Created instance %d: ", index);
    print_instance(&array[index],stdout);
    printf("\n");
  }
}

static int assign_instances(INSTANCE *array, int index,
			    Declaration attr, Declaration node) {
  FIBERSET fiberset;
  assign_instance(array,index++,attr,NULL,FALSE,node);
  for (fiberset = fiberset_for(attr,FIBERSET_NORMAL_FINAL);
       fiberset != NULL;
       fiberset=fiberset->rest) {
    assign_instance(array,index++,attr,fiberset->fiber,FALSE,node);
  }
  for (fiberset = fiberset_for(attr,FIBERSET_REVERSE_FINAL);
       fiberset != NULL;
       fiberset=fiberset->rest) {
    assign_instance(array,index++,attr,fiberset->fiber,TRUE,node);
  }
  return index;
}

static Type infer_some_value_decl_type(Declaration d) {
  if (Declaration_KEY(d) == KEYnormal_formal) {
    return infer_formal_type(d);
  } else {
    return some_value_decl_type(d);
  }
}

/** Count and then assign instances.
 * Called in two cases: <ul>
 * <li> one to set instance indices and count instances
 * <li> assign instances to the array
 * </ul>
 */
static void *get_instances(void *vaug_graph, void *node) {
  AUG_GRAPH *aug_graph = (AUG_GRAPH *)vaug_graph;
  INSTANCE *array = aug_graph->instances.array;
  STATE *s = aug_graph->global_state;
  int index = -1;

  if (array == NULL) {
    index = aug_graph->instances.length;
  }
  
  if (ABSTRACT_APS_tnode_phylum(node) == KEYDeclaration) {
    Declaration decl = (Declaration)node;
    if (index == -1) index = Declaration_info(decl)->instance_index;
    switch (Declaration_KEY(decl)) {
    case KEYmodule_decl:
      /* we let the module_decl represent the instance of the
       * root phylum in the global dependency graph.
       */
      if (array == NULL) Declaration_info(decl)->instance_index = index;
      { Declaration sattr = phylum_shared_info_attribute(s->start_phylum,s);
	FIBERSET fiberset;
	assign_instance(array,index++,sattr,NULL,FALSE,decl);
	for (fiberset = fiberset_for(sattr,FIBERSET_NORMAL_FINAL);
	     fiberset != NULL;
	     fiberset=fiberset->rest) {
	  assign_instance(array,index++,sattr,fiberset->fiber,FALSE,decl);
	}
	for (fiberset = fiberset_for(sattr,FIBERSET_REVERSE_FINAL);
	     fiberset != NULL;
	     fiberset=fiberset->rest) {
	  assign_instance(array,index++,sattr,fiberset->fiber,TRUE,decl);
	}
      }
      break;
    case KEYsome_function_decl:
    case KEYtop_level_match:
      /* don't look inside (unless its what we're doing the analysis for) */
      if (aug_graph->match_rule != decl) return NULL;
      if (array == NULL) Declaration_info(decl)->instance_index = index;
      /* if it has attributes it is the parameters, shared_info and result
       * for a function_decl.
       */
      { ATTRSET attrset=attrset_for(s,decl);
	for (; attrset != NULL; attrset=attrset->rest) {
	  Declaration attr = attrset->attr;
	  FIBERSET fiberset;
	  assign_instance(array,index++,attr,NULL,FALSE,decl);
	  for (fiberset = fiberset_for(attr,FIBERSET_NORMAL_FINAL);
	       fiberset != NULL;
	       fiberset=fiberset->rest) {
	    assign_instance(array,index++,attr,fiberset->fiber,FALSE,decl);
	  }
	  for (fiberset = fiberset_for(attr,FIBERSET_REVERSE_FINAL);
	       fiberset != NULL;
	       fiberset=fiberset->rest) {
	    assign_instance(array,index++,attr,fiberset->fiber,TRUE,decl);
	  }
	}
      }
      break;
    case KEYformal: case KEYvalue_decl:
      if (array == NULL) Declaration_info(decl)->instance_index = index;
      { Type ty = infer_some_value_decl_type(decl);
      /*if (Type_KEY(ty) == KEYremote_type)
	ty = remote_type_nodetype(ty); */
	switch (Type_KEY(ty)) {
	default:
	  fprintf(stderr,"cannot handle type: ");
	  print_Type(ty,stderr);
	  fatal_error("\n%d:abort",tnode_line_number(ty));
	case KEYtype_use:
	  { Declaration tdecl = Use_info(type_use_use(ty))->use_decl;
	    if (tdecl == NULL) fatal_error("%d:type not bound",
					   tnode_line_number(ty));
	    /*printf("%d: finding instances for %s",tnode_line_number(decl),
	      decl_name(decl)); */
	    /* first direct fibers (but not for nodes & parameters) */
	    if (0 == (Declaration_info(decl)->decl_flags &
		      (ATTR_DECL_INH_FLAG|ATTR_DECL_SYN_FLAG|
		       DECL_LHS_FLAG|DECL_RHS_FLAG)))
	    { FIBERSET fiberset;
	      assign_instance(array,index++,decl,NULL,FALSE,NULL);
	       /* printf("%s, first option: ",decl_name(decl));
		 print_fiberset(fiberset_for(decl,FIBERSET_NORMAL_FINAL),
		 stdout);
		 printf("\n"); */
	      for (fiberset = fiberset_for(decl,FIBERSET_NORMAL_FINAL);
		   fiberset != NULL;
		   fiberset=fiberset->rest) {
		assign_instance(array,index++,decl,fiberset->fiber,FALSE,NULL);
	      }
	      /* printf(", ");
		 print_fiberset(fiberset_for(decl,FIBERSET_REVERSE_FINAL),stdout);
		 printf("\n"); */
	      for (fiberset = fiberset_for(decl,FIBERSET_REVERSE_FINAL);
		   fiberset != NULL;
		   fiberset=fiberset->rest) {
		assign_instance(array,index++,decl,fiberset->fiber,TRUE,NULL);
	      }
	    }
	    /* then fibers on attributes */
	    { ATTRSET attrset=attrset_for(s,tdecl);
	      /*printf(" Second option: ");
	        print_attrset(attrset,stdout);
	        printf("\n");*/
	      for (; attrset != NULL; attrset=attrset->rest) {
		Declaration attr = attrset->attr;
		FIBERSET fiberset;
		assign_instance(array,index++,attr,NULL,FALSE,decl);
		for (fiberset = fiberset_for(attr,FIBERSET_NORMAL_FINAL);
		     fiberset != NULL;
		     fiberset=fiberset->rest) {
		  assign_instance(array,index++,attr,fiberset->fiber,FALSE,decl);
		}
		for (fiberset = fiberset_for(attr,FIBERSET_REVERSE_FINAL);
		     fiberset != NULL;
		     fiberset=fiberset->rest) {
		  assign_instance(array,index++,attr,fiberset->fiber,TRUE,decl);
		}
	      }
	    }
	  }
	  break;
	}
      }
      break;
    case KEYassign:
      { Declaration pdecl = proc_call_p(assign_rhs(decl));
	if (pdecl != NULL) {
	  if (array == NULL) {
	    STATE *s = aug_graph->global_state;
	    int i;
	    Declaration_info(decl)->instance_index = index;
	    Declaration_info(decl)->decl_flags |= DECL_RHS_FLAG;
	    for (i=0; i < s->phyla.length; ++i) {
	      if (s->phyla.array[i] == pdecl) {
		Declaration_info(decl)->node_phy_graph = &s->phy_graphs[i];
		break;
	      }
	    }
	  }
	  /* assertion check */
	  if (index != Declaration_info(decl)->instance_index)
	    fatal_error("%d: instance index %d != %d",tnode_line_number(decl),
			Declaration_info(decl)->instance_index,index);
	  { ATTRSET attrset=attrset_for(s,pdecl);
	    for (; attrset != NULL; attrset=attrset->rest) {
	      Declaration attr = attrset->attr;
	      index = assign_instances(array,index,attr,decl);
	    }
	  }
	}
      }
      break;
    case KEYpragma_call:
    case KEYattribute_decl:
    case KEYphylum_decl:
    case KEYtype_decl:
    case KEYconstructor_decl:
      return NULL;
    case KEYif_stmt:
      /* don't mess with instance_index */
      break;
    default:
      if (array == NULL) Declaration_info(decl)->instance_index = index;
    }
  } else if (ABSTRACT_APS_tnode_phylum(node) == KEYExpression) {
    Expression e = (Expression)node;
    Declaration fdecl = NULL;
    switch (Expression_KEY(e)) {
    default:
      break;
    case KEYfuncall:
      if ((fdecl = local_call_p(e)) != NULL) {
	ATTRSET attrset=attrset_for(s,fdecl);
	Declaration proxy = Expression_info(e)->funcall_proxy;

	/* printf("%d: Found local function call of %s\n",
	 *      tnode_line_number(e),decl_name(fdecl));
	 */
	if (array == NULL) {
	  extern int aps_yylineno;
	  aps_yylineno = tnode_line_number(e);
	  proxy = pragma_call(def_name(function_decl_def(fdecl)),
			      nil_Expressions());
	  Expression_info(e)->funcall_proxy = proxy;
	  Declaration_info(proxy)->instance_index = index;
	  Declaration_info(proxy)->node_phy_graph = 
	    summary_graph_for(s,fdecl);
	  Declaration_info(proxy)->decl_flags |= DECL_RHS_FLAG;
	} else {
	  index =  Declaration_info(proxy)->instance_index;
	}

	for (; attrset != NULL; attrset=attrset->rest) {
	  Declaration attr = attrset->attr;
	  index = assign_instances(array,index,attr,proxy);
	}
      }
      break;
    }
  }
  if (array == NULL) aug_graph->instances.length = index;
  return vaug_graph;
}

static INSTANCE *get_instance_or_null(Declaration attr, FIBER fiber, BOOL frev,
				      Declaration node, AUG_GRAPH *aug_graph)
{
  int i;
  INSTANCE *array = aug_graph->instances.array;
  int n = aug_graph->instances.length;
  int start = Declaration_info((node==NULL)?attr:node)->instance_index;

  if (fiber == base_fiber) fiber = NULL;

  for (i=start; i < n; ++i) {
    if (array[i].fibered_attr.attr == attr &&
	array[i].fibered_attr.fiber == fiber &&
	array[i].fibered_attr.fiber_is_reverse == frev &&
	array[i].node == node) return &array[i];
  }
  return NULL;
}

INSTANCE *get_instance(Declaration attr, FIBER fiber, BOOL frev,
		       Declaration node, AUG_GRAPH *aug_graph)
{
  INSTANCE *instance = get_instance_or_null(attr,fiber,frev,node,aug_graph);
  if (instance != NULL) return instance;
  { INSTANCE in;
    int i;
    INSTANCE *array = aug_graph->instances.array;
    int n = aug_graph->instances.length;
    int start = Declaration_info((node==NULL)?attr:node)->instance_index;
    
    in.fibered_attr.attr = attr;
    in.fibered_attr.fiber = fiber;
    in.fibered_attr.fiber_is_reverse = frev;
    in.node = node;

    fputs("Looking for ",stderr);
    print_instance(&in,stderr);
    fputc('\n',stderr);
    for (i=0; i < n; ++i) {
      print_instance(&array[i],stderr);
      if (i < start) fputs(" (ignored)",stderr);
      fputc('\n',stderr);
    }
  }
  fatal_error("Could not get instance");
  return NULL;
}

static INSTANCE *get_summary_instance_or_null(Declaration attr, FIBER fiber, 
					      BOOL frev, PHY_GRAPH* phy_graph)
{
  int i;
  INSTANCE *array = phy_graph->instances.array;
  int n = phy_graph->instances.length;
  int start = Declaration_info(attr)->instance_index;

  if (fiber == base_fiber) fiber = NULL;

  for (i=start; i < n; ++i) {
    if (array[i].fibered_attr.attr == attr &&
	array[i].fibered_attr.fiber == fiber &&
	array[i].fibered_attr.fiber_is_reverse == frev &&
	array[i].node == NULL) return &array[i];
  }
  return NULL;
}

INSTANCE *get_summary_instance(Declaration attr, FIBER fiber, BOOL frev,
			       PHY_GRAPH *phy_graph)
{
  INSTANCE *instance =
    get_summary_instance_or_null(attr,fiber,frev,phy_graph);
  if (instance != NULL) return instance;
  { INSTANCE in;
    int i;
    INSTANCE *array = phy_graph->instances.array;
    int n = phy_graph->instances.length;
    int start = Declaration_info(attr)->instance_index;
    
    in.fibered_attr.attr = attr;
    in.fibered_attr.fiber = fiber;
    in.fibered_attr.fiber_is_reverse = frev;
    in.node = NULL;

    fputs("Looking for summary ",stderr);
    print_instance(&in,stderr);
    fputc('\n',stderr);
    for (i=0; i < n; ++i) {
      print_instance(&array[i],stderr);
      if (i < start) fputs(" (ignored)",stderr);
      fputc('\n',stderr);
    }
  }
  fatal_error("Could not get instance");
  return NULL;
}

/** Connect the source to the sink and all their appropriate fibers.
 * Reverse fibers connect in the opposite direction.
 */
void add_edges_to_graph(INSTANCE *source,
			INSTANCE *sink,
			CONDITION *cond,
			DEPENDENCY kind,
			AUG_GRAPH *aug_graph) {
  INSTANCE *array = aug_graph->instances.array;
  int start1 = source - array;
  int mid1;
  int max1 = aug_graph->instances.length;
  int start2 = sink - array;
  int mid2;
  int max2 = max1;
  int i1, i2;
  Declaration attr1 = source->fibered_attr.attr;
  Declaration attr2 = sink->fibered_attr.attr;
  Declaration node1 = source->node;
  Declaration node2 = sink->node;
  Declaration field1 = NULL;
  Declaration field2 = NULL;
  Declaration rfield1 = NULL;
  Declaration rfield2 = NULL;
  int reverse1 = source->fibered_attr.fiber_is_reverse;
  int reverse2 = sink->fibered_attr.fiber_is_reverse;

  if (kind == no_dependency) return;

  /* first just add the edge */
  add_edge_to_graph(source,sink,cond,kind,aug_graph);

  if (source->fibered_attr.fiber != NULL) {
    field1 = source->fibered_attr.fiber->field;
    rfield1 = reverse_field(field1);
  }
  if (sink->fibered_attr.fiber != NULL) {
    field2 = sink->fibered_attr.fiber->field;
    rfield2 = reverse_field(field2);
  }

  if (field1 != NULL) {
    /* move back start1 */
    while (array[start1].fibered_attr.fiber != NULL) --start1;
  }
  if (field2 != NULL) {
    /* move back start2 */
    while (array[start2].fibered_attr.fiber != NULL) --start2;
  }

  for (i1 = start1 + 1; i1 < max1; ++i1) {
    if (!(array[i1].fibered_attr.attr == attr1 &&
	  array[i1].fibered_attr.fiber_is_reverse == FALSE &&
	  array[i1].node == node1)) break;
  }
  mid1 = i1;
  for (i1 = mid1; i1 < max1; ++i1) {
    if (!(array[i1].fibered_attr.attr == attr1 &&
	  array[i1].fibered_attr.fiber_is_reverse == TRUE &&
	  array[i1].node == node1)) break;
  }
  max1 = i1;

  for (i2 = start2 + 1; i2 < max2; ++i2) {
    if (!(array[i2].fibered_attr.attr == attr2 &&
	  array[i2].fibered_attr.fiber_is_reverse == FALSE &&
	  array[i2].node == node2)) break;
  }
  mid2 = i2;
  for (i2 = mid2; i2 < max2; ++i2) {
    if (!(array[i2].fibered_attr.attr == attr2 &&
	  array[i2].fibered_attr.fiber_is_reverse == TRUE &&
	  array[i2].node == node2)) break;
  }
  max2 = i2;

  /*
  printf("Dependencies (%d,%d) -> [%d,%d), [%d,%d) -> (%d,%d)\n",
	 start1,mid1,mid2,max2,
	 mid1,max1,start2,mid2);
  */

  /* The range (start,mid) holds regular fibered attributes, and
   * the range [mid,max) holds reverse fibered attributes.
   * Now for each case where the two ranges have a fiber in common
   * we connect an edge (in the normal or reverse direction)
   */

  /*
  if (reverse1 != reverse2)
    printf("A cross dependency! (%d,%d) -> [%d,%d), [%d,%d) -> (%d,%d)\n",
	   start1,mid1,mid2,max2,
	   mid1,max1,start2,mid2);
  */

  for (i1 = start1+1; i1 < max1; ++i1) {
    INSTANCE *in1 = &array[i1];
    FIBER f1 = array[i1].fibered_attr.fiber;
    Declaration field1 = NULL;
    if (source->fibered_attr.fiber != NULL)
      field1 = source->fibered_attr.fiber->field;
    if (field1 != NULL && (reverse1 != (i1 >= mid1)))
      field1 = reverse_field(field1);
    if (field1 == NULL || f1->field == field1) { /* shorten is possible */
      FIBER f1a, f1b;
      if (field1 == NULL) {
	f1a = f1b = f1;
      } else if (FIELD_DECL_IS_CYCLIC(field1)) {
	f1a = f1; f1b = f1->shorter;
      } else {
	f1a = f1b = f1->shorter;
      }
      /* f1a and f1b are the "results" of shorten(field1,f1) */
      for (i2 = start2+1; i2 < max2; ++i2) {
	INSTANCE *in2 = &array[i2];
	FIBER f2 = array[i2].fibered_attr.fiber;
	Declaration field2 = NULL;
	if (sink->fibered_attr.fiber != NULL)
	  field2 = sink->fibered_attr.fiber->field;
	if (field2 != NULL && (reverse2 != (i2 >= mid2)))
	  field2 = reverse_field(field2);
	if ((reverse1 == (i1 >= mid1)) == (reverse2 == (i2 >= mid2)) &&
	    (field2 == NULL || f2->field == field2)) { /* shorten possible */
	  FIBER f2a, f2b;
	  if (field2 == NULL) {
	    f2a = f2b = f2;
	  } else if (FIELD_DECL_IS_CYCLIC(field2)) {
	    f2a = f2; f2b = f2->shorter;
	  } else {
	    f2a = f2b = f2->shorter;
	  }
	  if (f1a == f2a || f1b == f2a || f1b == f2a || f1b == f2b) {
	    if (reverse1 == (i1 >= mid1)) 
	      add_edge_to_graph(in1,in2,cond,fiber_dependency,aug_graph);
	    else
	      add_edge_to_graph(in2,in1,cond,fiber_dependency,aug_graph);
	  }
	}
      }
    }
  }
  
#ifdef UNDEF
  if (field1 != NULL && field2 != NULL) {
    print_instance(source,stderr);
    fprintf(stderr,"->");
    print_instance(sink,stderr);
    fprintf(stderr,"\n");
    fatal_error("Cannot do this case yet");
  }

  if (reverse1) {
    for (i1 = start1+1; i1 < mid1; ++i1) { /* reverse2 -> normal1 */
      INSTANCE *in1 = &array[i1];
      FIBER f1 = array[i1].fibered_attr.fiber;
      if (f1->field == rfield1)
	for (i2 = mid2; i2 < max2; ++i2) {
	  INSTANCE *in2 = &array[i2];
	  FIBER f2 = array[i2].fibered_attr.fiber;
	  if (lengthen_fiber(rfield1,f2) == f1)
	    add_edge_to_graph(in2,in1,cond,fiber_dependency,aug_graph);
	}
    }
    for (i1 = mid1; i1 < max1; ++i1) { /* reverse1 -> normal2 */
      INSTANCE *in1 = &array[i1];
      FIBER f1 = array[i1].fibered_attr.fiber;
      if (f1->field == field1)
	for (i2 = start2+1; i2 < mid2; ++i2) {
	  INSTANCE *in2 = &array[i2];
	  FIBER f2 = array[i2].fibered_attr.fiber;
	  if (lengthen_fiber(field1,f2) == f1)
	    add_edge_to_graph(in1,in2,cond,fiber_dependency,aug_graph);
	}
    }
  } else if (reverse2) {
    for (i2 = start2+1; i2 < mid2; ++i2) { /* normal2 -> reverse1 */
      INSTANCE *in2 = &array[i2];
      FIBER f2 = array[i2].fibered_attr.fiber;
      if (f2->field == rfield2)
	for (i1 = mid1; i1 < max1; ++i1) {
	  INSTANCE *in1 = &array[i1];
	  FIBER f1 = array[i1].fibered_attr.fiber;
	  if (lengthen_fiber(rfield2,f1) == f2)
	    add_edge_to_graph(in2,in1,cond,fiber_dependency,aug_graph);
	}
    }
    for (i2 = mid2; i2 < max2; ++i2) { /* normal1 -> reverse2 */
      INSTANCE *in2 = &array[i2];
      FIBER f2 = array[i2].fibered_attr.fiber;
      if (f2->field == field2)
	for (i1 = start1+1; i1 < mid1; ++i1) {
	  INSTANCE *in1 = &array[i1];
	  FIBER f1 = array[i1].fibered_attr.fiber;
	  if (lengthen_fiber(field2,f1) == f2)
	    add_edge_to_graph(in1,in2,cond,fiber_dependency,aug_graph);
	}
    }
  } else {
    /* we assume one of field1,field2 is NULL */
    for (i1 = start1+1; i1 < mid1; ++i1) { /* normal1 -> normal2 */
      INSTANCE *in1 = &array[i1];
      FIBER f1 = array[i1].fibered_attr.fiber;
      if (field1 == NULL || f1->field == field1)
	for (i2 = start2+1; i2 < mid2; ++i2) {
	  INSTANCE *in2 = &array[i2];
	  FIBER f2 = array[i2].fibered_attr.fiber;
	  if (lengthen_fiber(field1,f2) == lengthen_fiber(field2,f1))
	    add_edge_to_graph(in1,in2,cond,fiber_dependency,aug_graph);
	}
    }
    for (i1 = mid1; i1 < max1; ++i1) { /* reverse2 -> reverse1 */
      INSTANCE *in1 = &array[i1];
      FIBER f1 = array[i1].fibered_attr.fiber;
      if (rfield1 == NULL || f1->field == rfield1)
	for (i2 = mid2; i2 < max2; ++i2) {
	  INSTANCE *in2 = &array[i2];
	  FIBER f2 = array[i2].fibered_attr.fiber;
	  if (lengthen_fiber(rfield1,f2) == lengthen_fiber(rfield2,f1))
	    add_edge_to_graph(in2,in1,cond,fiber_dependency,aug_graph);
	}
    }
  }
 
#endif
	/*
	{ print_instance(source,stdout);
	  printf(" -> ");
	  print_instance(sink,stdout);
	  printf(" implies? ");
	  print_instance(&array[i1],stdout);
	  printf(" -> ");
	  print_instance(&array[i2],stdout);
	  printf("\n");
	}
	*/

  /* Done */
}

/* Return the instance for a given expression.
 * It is an error if the expression is something other than an instance.
 * @return null if the expression refers to constant (external) things.
 */
INSTANCE *get_expression_instance(FIBER fiber, int frev,
				  Expression e, AUG_GRAPH *aug_graph) {
  switch (Expression_KEY(e)) {
  default:
    fatal_error("%d: Cannot get expression instance",tnode_line_number(e));
    break;
  case KEYfuncall:
    { Declaration decl;
      if ((decl = attr_ref_p(e)) != NULL) {
	Expression node = attr_ref_object(e);
	Declaration ndecl = NULL;
	switch (Expression_KEY(node)) {
	default: fatal_error("%d: can't handle this attribute instance",
			     tnode_line_number(node));
	case KEYvalue_use:
	  ndecl = USE_DECL(value_use_use(node));
	  break;
	}
	return get_instance(decl,fiber,frev,ndecl,aug_graph);
      } else if ((decl = field_ref_p(e)) != NULL) {
	Expression node = field_ref_object(e);
	Declaration ndecl = NULL;
	switch (Expression_KEY(node)) {
	default: fatal_error("%d: can't handle this attribute instance",
			     tnode_line_number(node));
	case KEYvalue_use:
	  ndecl = USE_DECL(value_use_use(node));
	  break;
	}
	if (fiber != NULL && fiber != base_fiber) {
	  /*printf("Trying untested techniques\n");*/
	  if (fiber->shorter == 0) fatal_error("What base fiber?");
	  fiber = lengthen_fiber(decl,fiber);
	  decl = ndecl;
	  ndecl = NULL;
	}
	return get_instance(decl,fiber,frev,ndecl,aug_graph);
      } else {
	fatal_error("%d: Cannot get expression instance",tnode_line_number(e));
	return NULL;
      }
    }
    break;
  case KEYvalue_use:
    { Declaration decl=Use_info(value_use_use(e))->use_decl;
      if (decl == NULL)
	fatal_error("%d: unbound expression",tnode_line_number(e));

      if (DECL_IS_LOCAL(decl)) {
	Declaration rdecl;
	if (DECL_IS_SHARED(decl) &&
	    (rdecl = responsible_node_declaration(e)) != NULL) {
	  fatal_error("%d: Cannot get expression instance for shared %s",
		      tnode_line_number(e),decl_name(decl));
	  return NULL;
	} else if (Declaration_info(decl)->decl_flags &
		   (ATTR_DECL_INH_FLAG|ATTR_DECL_SYN_FLAG)) {
	  /* a use of parameter or result (we hope) */
	  Declaration fdecl = aug_graph->match_rule;
	  switch (Declaration_KEY(decl)) {
	  case KEYnormal_formal:
	  case KEYvalue_decl:
	    break;
	  default:
	    fatal_error("%d: incomplete attribute %s",
			tnode_line_number(e),decl_name(decl));
	  }
	  return get_instance(decl,fiber,frev,fdecl,aug_graph);
	} else if (Declaration_info(decl)->decl_flags &
		   (DECL_LHS_FLAG|DECL_RHS_FLAG)) {
	  /* no dependency need be added */
	  return NULL;
	} else {
	  /* an unshared (local) dependency within an aug graph */
	  return get_instance(decl,fiber,frev,NULL,aug_graph);
	}
      } else {
	return NULL;
      }
    }
    break;
  }
}

/** Add edges to the dependency graph to represent dependencies
 * from sink to the value computed in the expression.
 * @param cond condition under which dependency holds
 * @param fiber fibers of the value depended on (usually NULL)
 * @param frev whether the fiber is the reverse fiber
 * @param kind whether a real dependency or a fiber dependency
 * @param carrying whether the dependency carries a value.
 *        If not, then we don't add additional fiber dependencies.
 */
static void record_expression_dependencies(INSTANCE *sink, CONDITION *cond,
					   FIBER fiber, int frev,
					   DEPENDENCY kind, int carrying,
					   Expression e, AUG_GRAPH *aug_graph)
{
  /* Several different cases
   *
   * l
   * n.attr
   * f(...)
   * constructor(...)
   * expr.field
   * shared
   */
  switch (Expression_KEY(e)) {
  default:
    fprintf(stderr,"fatal_error: %d: cannot handle this expression (%d)\n",
		tnode_line_number(e), Expression_KEY(e));
    repeat_expr(e); /* force crash */
    break;
  case KEYinteger_const:
  case KEYreal_const:
  case KEYstring_const:
  case KEYchar_const:
    /* nothing to do */
    break;
  case KEYrepeat:
    record_expression_dependencies(sink,cond,fiber,frev,kind,carrying,
				   repeat_expr(e),aug_graph);
    break;
  case KEYvalue_use:
    { Declaration decl=Use_info(value_use_use(e))->use_decl;
      Declaration rdecl;
      INSTANCE *source;
      if (decl == NULL)
	fatal_error("%d: unbound expression",tnode_line_number(e));
      if (DECL_IS_LOCAL(decl) &&
	  DECL_IS_SHARED(decl) &&
	  (rdecl = responsible_node_declaration(e)) != NULL) {
	/* a shared dependency: we get it from the shared_info */
	Declaration phy = node_decl_phylum(rdecl);
	Declaration sattr =
	  phylum_shared_info_attribute(phy,aug_graph->global_state);
	FIBER new_fiber = lengthen_fiber(decl,fiber);
	INSTANCE *osrc = get_instance(sattr,fiber,frev,rdecl,aug_graph);
	source = get_instance(sattr,new_fiber,frev,rdecl,aug_graph);
	if (carrying) {
	  add_edges_to_graph(source,sink,cond,kind,aug_graph);
	} else {
	  add_edge_to_graph(source,sink,cond,kind,aug_graph);
	}
	add_edge_to_graph(osrc,sink,cond,kind,aug_graph);
      } else {
	source = get_expression_instance(fiber,frev,e,aug_graph);
	if (source != NULL) {
	  if (carrying) {
	    add_edges_to_graph(source,sink,cond,kind,aug_graph);
	  } else {
	    add_edge_to_graph(source,sink,cond,kind,aug_graph);
	  }
	}
      }
    }
    break;
  case KEYfuncall:
    { Declaration decl;
      if ((decl = attr_ref_p(e)) != NULL) {
	INSTANCE *source = get_expression_instance(fiber,frev,e,aug_graph);
	if (carrying) {
	  add_edges_to_graph(source,sink,cond,kind,aug_graph);
	} else {
	  add_edge_to_graph(source,sink,cond,kind,aug_graph);
	}
      } else if ((decl = field_ref_p(e)) != NULL) {
	Expression object = field_ref_object(e);
	INSTANCE *osrc =  get_expression_instance(fiber,frev,object,aug_graph);
	FIBER f2 = lengthen_fiber(decl,fiber);
	INSTANCE *source = get_expression_instance(f2,frev,object,aug_graph);
	/* a fiber dependency */
	if (carrying) {
	  add_edges_to_graph(source,sink,cond,kind,aug_graph);
	} else {
	  /* printf("Adding non-carrying field reference ");
	   * print_instance(source,stdout);
	   * printf("->");
	   * print_instance(sink,stdout);
	   * printf(": ");
	   */
	  add_edge_to_graph(source,sink,cond,kind,aug_graph);
	}
	/* and also depend on object itself (not a carrying dependency) */
	add_edge_to_graph(osrc,sink,cond,kind&~DEPENDENCY_MAYBE_CARRYING,aug_graph);
      } else if ((decl = local_call_p(e)) != NULL) {
	Declaration result = some_function_decl_result(decl);
	Expression actual = first_Actual(funcall_actuals(e));
	/* Two possibilities:
	 * 1> function
	 *    - We depend on all arguments, and on all
	 *      fibers that the result depends on.
	 *    - Then fibers of the call are made to depend on
	 *      what arguments and fibers of arguments that
	 *      the corresponding fibers of the result depend on.
	 * 2> procedure
	 *    - We have an instance for this call.
	 *    - We use the summary I/O graph for procedure to find out
	 *      what parameters and what fibers of them we depend on.
	 */
	switch (Declaration_KEY(decl)) {
	case KEYprocedure_decl:
	  fatal_error("%d: Cannot handle procedure calls here\n",
		      tnode_line_number(e));
	  break;
	case KEYfunction_decl:
	  /* first depend on the arguments (not carrying, no fibers) */
	  for (; actual != NULL; actual=Expression_info(actual)->next_actual) {
	    record_expression_dependencies(sink,cond,0,FALSE,dependency,FALSE,
					   actual,aug_graph);
	  }

	  /* attach to result, and somewhere else ? attach actuals */
	  printf("%d: looking at local function %s\n",
		 tnode_line_number(e),decl_name(decl));
	  {
	    Declaration proxy = Expression_info(e)->funcall_proxy;
	    Declaration rd = some_function_decl_result(decl);
	    INSTANCE *source = get_instance(rd,fiber,frev,proxy,aug_graph);
	    
	    if (carrying) {
	      add_edges_to_graph(source,sink,cond,kind,aug_graph);
	    } else {
	      add_edge_to_graph(source,sink,cond,kind,aug_graph);
	    }
	  }
	}
      } else if ((decl = constructor_call_p(e)) != NULL) {
	Expression actual = first_Actual(funcall_actuals(e));
	for (; actual != NULL; actual=Expression_info(actual)->next_actual) {
	  record_expression_dependencies(sink,cond,fiber,frev,kind,carrying,
					 actual,aug_graph);
	}
      } else {
	/* some random (external) function call */
	Expression actual = first_Actual(funcall_actuals(e));
	for (; actual != NULL; actual=Expression_info(actual)->next_actual) {
	  record_expression_dependencies(sink,cond,fiber,frev,kind,carrying,
					 actual,aug_graph);
	}
      }
    }
    break;
  }
}

void record_condition_dependencies(INSTANCE *sink, CONDITION *cond,
				   AUG_GRAPH *aug_graph) {
  int i;
  unsigned bits=cond->positive|cond->negative;
  /*
  { print_instance(sink,stdout);
    printf(" <- ");
    print_condition(cond,stdout);
    printf(" = 0%o\n",bits); }
    */
  for (i=0; i < aug_graph->if_rules.length; ++i) {
    int mask = (1 << i);
    if (mask & bits) {
      void* if_rule = aug_graph->if_rules.array[i];
      /* printf("Getting dependencies for condition %d\n",i); */
      CONDITION *cond2 = if_rule_cond(if_rule);
      int index = if_rule_index(if_rule);
      INSTANCE* if_instance = &aug_graph->instances.array[index];
      if (index > 32 || if_instance->index != index) 
	fatal_error("something is fishy");
      add_edge_to_graph(if_instance,sink,cond2,control_dependency,aug_graph);
    }
  }
}

/* Initialize the edge set in the augmented dependency graph
 * from each rule for the production.  This is the meat of
 * the analysis process.  We use fiber information to get the
 * dependencies.
 */
static void *get_edges(void *vaug_graph, void *node) {
  AUG_GRAPH *aug_graph = (AUG_GRAPH *)vaug_graph;
  switch (ABSTRACT_APS_tnode_phylum(node)) {
  default:
    break;
  case KEYDeclaration:
    { Declaration decl = (Declaration)node;
      CONDITION *cond = &Declaration_info(decl)->decl_cond;
      /* Several different cases:
       *
       * l : type := value;
       * o : type := constr(...);
       * l := value
       * n.attr := value;
       * o.field := value
       * expr.coll :> value;
       * shared :> value;
       * and then "if" and "case."
       *
       * In all cases, we have to use the condition
       * on the declaration as well.
       *
       */
      switch (Declaration_KEY(decl)) {
      case KEYsome_function_decl:
      case KEYtop_level_match:
      case KEYattribute_decl:
      case KEYpragma_call:
      case KEYphylum_decl:
      case KEYtype_decl:
      case KEYconstructor_decl:
	/* Don't look in nested things */
	return NULL;
      case KEYformal:
	{ Declaration case_stmt = formal_in_case_p(decl);
	  if (case_stmt != NULL) {
	    Expression expr = case_stmt_expr(case_stmt);
	    INSTANCE *i = get_instance(decl,NULL,FALSE,NULL,aug_graph);
	    record_condition_dependencies(i,cond,aug_graph);
	    record_expression_dependencies(i,cond,NULL,FALSE,dependency,TRUE,
					   expr,aug_graph);
	  }
	}
	break;
      case KEYvalue_decl:
	{ INSTANCE *i=get_instance(decl,NULL,FALSE,NULL,aug_graph);
	  Default def = value_decl_default(decl);
	  Declaration cdecl;
	  if (i == NULL)
	    fatal_error("%d: panic: instance is null",tnode_line_number(decl));
	  record_condition_dependencies(i,cond,aug_graph);
	  switch (Default_KEY(def)) {
	  case KEYno_default: break;
	  case KEYsimple:
	    record_expression_dependencies(i,cond,NULL,FALSE,dependency,TRUE,
					   simple_value(def),aug_graph);
	    if ((cdecl = constructor_call_p(simple_value(def))) != NULL) {
	      FIBERSET fs = fiberset_for(decl,FIBERSET_NORMAL_FINAL);
	      FIBERSET rfs = fiberset_for(decl,FIBERSET_REVERSE_FINAL);
	      Declaration pdecl = constructor_decl_phylum(cdecl);
	      Declaration fdecl;
	      /*
	      printf("Looking at %s which instantiates %s\n",decl_name(decl),
		     decl_name(cdecl));
	      printf("Normal: ");
	      print_fiberset(fs,stdout);
	      printf("\nReverse: ");
	      print_fiberset(rfs,stdout);
	      printf("\n");
	      */
	      /* add fiber dependencies for fields */
	      for (fdecl = NEXT_FIELD(pdecl);
		   fdecl != NULL;
		   fdecl = NEXT_FIELD(fdecl)) {
		Declaration rfdecl = reverse_field(fdecl);
		FIBERSET fs1;
		for (fs1 = fs; fs1 != NULL; fs1=fs1->rest) {
		  FIBER fiber = fs1->fiber;
		  if ((fiber->field == fdecl ||
		       fiber->field == rfdecl) &&
		      member_fiberset(fiber,rfs)) {
		    INSTANCE *source =
		      get_instance(decl,fiber,TRUE,NULL,aug_graph);
		    INSTANCE *sink =
		      get_instance(decl,fiber,FALSE,NULL,aug_graph);
		    if (fiber->field == fdecl &&
			fiber->shorter == base_fiber) {
		      INSTANCE* between =
			get_instance(fdecl,NULL,FALSE,decl,aug_graph);
		      /* not a fiber dependency because we have to collect
		       * the values together.
		       */
		      /*
		      printf("Adding extra edges ");
		      print_instance(source,stdout);
		      printf(" -> ");
		      print_instance(between,stdout);
		      printf(" -> ");
		      print_instance(sink,stdout);
		      printf("\n");
		      */
		      /* And put the instance between */
		      add_edge_to_graph(source,between,cond,dependency,aug_graph);
		      add_edge_to_graph(between,sink,cond,dependency,aug_graph);
		      /* but also add a direct fiber dependency
		       * so we know we have a direct dependency
		       * between them (pure incremental purposes)
		       */
		      add_edge_to_graph(source,sink,cond,fiber_dependency,aug_graph);
		    } else {
		      /*
		      printf("Avoiding extra edges ");
		      print_instance(source,stdout);
		      printf(" -> ");
		      print_instance(sink,stdout);
		      printf("\n");
		      */
		      add_edge_to_graph(source,sink,cond,
					fiber_dependency,aug_graph);
		    }
		  }
		}
	      }
	    }
	    break;
	  case KEYcomposite:
	    record_expression_dependencies(i,cond,NULL,FALSE,dependency,TRUE,
					   composite_initial(def),aug_graph);
	    break;
	  }
	  if (DECL_IS_SHARED(decl)) {
	    /* add edges for shared info */
	    STATE *s = aug_graph->global_state;
	    Declaration sattr =
	      phylum_shared_info_attribute(s->start_phylum,s);
	    FIBER fiber = lengthen_fiber(decl,base_fiber);
	    Declaration module = aug_graph->match_rule;
	    INSTANCE *i = get_instance(decl,NULL,FALSE,NULL,aug_graph);
	    INSTANCE *use = get_instance_or_null(sattr,fiber,FALSE,
						 module,aug_graph);
	    INSTANCE *def = get_instance_or_null(sattr,fiber,TRUE,
						 module,aug_graph);
	    if (use != NULL)
	      add_edges_to_graph(i,use,cond,dependency,aug_graph);
	    if (def != NULL)
	      add_edges_to_graph(def,i,cond,dependency,aug_graph);
	  }
	}
	break;
      case KEYassign:
	{ Expression lhs=assign_lhs(decl);
	  Expression rhs=assign_rhs(decl);
	  Declaration field;
	  Declaration pdecl;
	  if ((field = field_ref_p(lhs)) != NULL) {
	    /* Assignment of a field */
	    Expression object = field_ref_object(lhs);
	    INSTANCE *osrc =
	      get_expression_instance(NULL,FALSE,object,aug_graph);
	    FIBER fiber = lengthen_fiber(field,base_fiber);
	    if (direction_is_collection(attribute_decl_direction(field))) {
	      INSTANCE *sink = get_expression_instance(fiber,TRUE,
						       object,aug_graph);
	      Expression_info(rhs)->value_for = sink;
	      /* assignment requires the object is ready to assign */
	      add_edge_to_graph(osrc,sink,cond,dependency,aug_graph);
	      record_condition_dependencies(sink,cond,aug_graph);
	      record_expression_dependencies(sink,cond,NULL,FALSE,
					     dependency,TRUE,rhs,aug_graph);
	    } else {
	      INSTANCE *sink = get_expression_instance(NULL,FALSE,
						       lhs,aug_graph);
	      INSTANCE *fsink = get_expression_instance(fiber,FALSE,
							object,aug_graph);
	      Expression_info(rhs)->value_for = sink;
	      /* assignment also requires the object is ready to assign */
	      if (osrc != fsink) { /* avoid untracked fibers */
		/* tracked but strict fields must still be assigned
		 * before object is created.
		 */
		if (FIELD_DECL_IS_STRICT(field))
		  add_edge_to_graph(fsink,osrc,cond,dependency,aug_graph);
		/* Otherwise they must be assigned *after*
		 * the object is created.
		 *?? Why 2002/3/7?
		 *?? These edges seem unnecessary
		 */
		else
		  add_edge_to_graph(osrc,fsink,cond,dependency,aug_graph);
	      }
	      record_condition_dependencies(sink,cond,aug_graph);
	      record_expression_dependencies(sink,cond,NULL,FALSE,
					     dependency,TRUE,rhs,aug_graph);
	      record_expression_dependencies(fsink,cond,NULL,FALSE,
					     dependency,TRUE,rhs,aug_graph);
	      add_edge_to_graph(sink,fsink,cond,dependency,aug_graph);
	    }
	  } else if ((field = shared_use_p(lhs)) != NULL) {
	    /* Assignment of shared global */
	    Declaration node = responsible_node_declaration(decl);
	    Declaration sattr =
	      phylum_shared_info_attribute(node_decl_phylum(node),
					   aug_graph->global_state);
	    FIBER fiber = lengthen_fiber(field,base_fiber);
	    INSTANCE *sink = get_instance(sattr,fiber,TRUE,node,aug_graph);
	    Expression_info(rhs)->value_for = sink;
	    record_condition_dependencies(sink,cond,aug_graph);
	    record_expression_dependencies(sink,cond,NULL,FALSE,
					   dependency,TRUE,rhs,aug_graph);
	  } else if ((pdecl = proc_call_p(rhs)) != NULL) {
	    /* procedure call: connect up instances with locals */
	    Declarations formals =
	      function_type_formals(some_function_decl_type(pdecl));
	    Declaration result = some_function_decl_result(pdecl);
	    Actuals actuals = funcall_actuals(rhs);
	    Declaration formal;
	    Expression actual;
	    /* connect the result */
	    { INSTANCE *sink = get_expression_instance(NULL,FALSE,lhs,aug_graph);
	      INSTANCE *src = get_instance(result,NULL,FALSE,decl,aug_graph);
	      Expression_info(rhs)->value_for = sink;
	      record_condition_dependencies(sink,cond,aug_graph);
	      add_edges_to_graph(src,sink,cond,dependency,aug_graph);
	    }
	    /* connect the parameters */
	    for (actual = first_Actual(actuals),
		 formal = first_Declaration(formals);
		 actual != NULL && formal != NULL;
		 actual = Expression_info(actual)->next_actual,
		 formal = Declaration_info(formal)->next_decl) {
	      INSTANCE *sink = get_instance(formal,NULL,FALSE,decl,aug_graph);
	      record_condition_dependencies(sink,cond,aug_graph);
	      record_expression_dependencies(sink,cond,NULL,FALSE,
					     dependency,TRUE,actual,aug_graph);
	    }
	    /* connect up the shared info */
	    { STATE *s = aug_graph->global_state;
	      Declaration node = responsible_node_declaration(decl);
	      Declaration nodephy = node_decl_phylum(node);
	      Declaration lattr = phylum_shared_info_attribute(nodephy,s);
	      Declaration rattr = phylum_shared_info_attribute(pdecl,s);
	      INSTANCE *source = get_instance(lattr,NULL,FALSE,node,aug_graph);
	      INSTANCE *sink = get_instance(rattr,NULL,FALSE,decl,aug_graph);
	      add_edges_to_graph(source,sink,cond,dependency,aug_graph);
	    }
	  } else {
	    INSTANCE *sink = get_expression_instance(NULL,FALSE,lhs,aug_graph);
	    Expression_info(rhs)->value_for = sink;
	    record_condition_dependencies(sink,cond,aug_graph);
	    record_expression_dependencies(sink,cond,NULL,FALSE,
					   dependency,TRUE,rhs,aug_graph);
	  }
	}
	break;
      case KEYif_stmt:
	{
	  int index = Declaration_info(decl)->if_index;
	  INSTANCE* sink = &aug_graph->instances.array[index];
	  Expression test = if_stmt_cond(decl);
	  if (sink->index != index) fatal_error("%d:something is fishy",
						tnode_line_number(decl));

	  record_condition_dependencies(sink,cond,aug_graph);
	  record_expression_dependencies(sink,cond,NULL,FALSE,
					 control_dependency,FALSE,test,aug_graph);
	}
	break;
      case KEYcase_stmt:
	{
	  Match m;
	  for (m=first_Match(case_stmt_matchers(decl)); m; m=MATCH_NEXT(m)) {
	    int index = Match_info(m)->if_index;
	    INSTANCE* sink = &aug_graph->instances.array[index];
	    Expression test = Match_info(m)->match_test;

	    if (sink->index != index) fatal_error("something is fishy");

	    record_condition_dependencies(sink,cond,aug_graph);

	    for (; test != 0; test = Expression_info(test)->next_expr) {
	      record_expression_dependencies(sink,cond,NULL,FALSE,
					     control_dependency,FALSE,test,aug_graph);
	    }
	  }
	}
	break;
      default:
	printf("%d: don't handle this kind yet\n",tnode_line_number(decl));
	break;
      }
    }
    break;
  case KEYExpression:
    {
      Expression e = (Expression) node;
      Declaration fdecl;
      
      if ((fdecl = local_call_p(e)) != NULL &&
	  Declaration_KEY(fdecl) == KEYfunction_decl) {
	Declaration proxy = Expression_info(e)->funcall_proxy;
	CONDITION *cond;
	void *parent = tnode_parent(node);

	while (ABSTRACT_APS_tnode_phylum(parent) != KEYDeclaration) {
	  parent = tnode_parent(parent);
	}
	cond = &Declaration_info((Declaration)parent)->decl_cond;

	/* connect result to conditions */
	{
	  Declaration rd = some_function_decl_result(fdecl);
	  INSTANCE* sink = get_instance(rd,NULL,FALSE,proxy,aug_graph);
	  record_condition_dependencies(sink,cond,aug_graph);
	}

	/* connect formals and actuals */
	{
	  Type ft = function_decl_type(fdecl);
	  Declaration f = first_Declaration(function_type_formals(ft));
	  Expression a = first_Actual(funcall_actuals(e));
	  for (; f != NULL; f = DECL_NEXT(f), a = EXPR_NEXT(a)) {
	    INSTANCE *sink = get_instance(f,NULL,FALSE,proxy,aug_graph);
	    record_expression_dependencies(sink,cond,NULL,FALSE,
					   dependency,TRUE,a,aug_graph);
	    record_condition_dependencies(sink,cond,aug_graph);
	  }
	}

	/* connect shared info */
	{
	  STATE *s = aug_graph->global_state;
	  Declaration rnode = responsible_node_declaration(e);
	  Declaration rnodephy = node_decl_phylum(rnode);
	  Declaration lattr = phylum_shared_info_attribute(rnodephy,s);
	  Declaration rattr = phylum_shared_info_attribute(fdecl,s);
	  INSTANCE *source = get_instance(lattr,NULL,FALSE,rnode,aug_graph);
	  INSTANCE *sink = get_instance(rattr,NULL,FALSE,proxy,aug_graph);
	  add_edges_to_graph(source,sink,cond,dependency,aug_graph);
	  record_condition_dependencies(sink,cond,aug_graph);
	}
      }
    }
    break;
  }
  return vaug_graph;
}


/*** AUXILIARY FUNCTIONS FOR SUMMARY INFORMATION AND FOR PHYLA ***/

PHY_GRAPH* summary_graph_for(STATE *state, Declaration pdecl)
{
  int i;
  for (i=0; i < state->phyla.length; ++i) {
    if (state->phyla.array[i] == pdecl) {
      return &state->phy_graphs[i];
    }
  }
  fatal_error("could not find summary graph for %s",decl_name(pdecl));
  /*NOTREACHED*/
  return 0;
}

ATTRSET attrset_for(STATE *s, Declaration phylum) {
  return (ATTRSET)get(s->phylum_attrset_table,phylum);
}

void add_attrset_for(STATE *s, Declaration phylum, Declaration attr) {
  ATTRSET attrset = (ATTRSET)HALLOC(sizeof(struct attrset));
  attrset->rest = get(s->phylum_attrset_table,phylum);
  attrset->attr = attr;
  set(s->phylum_attrset_table,phylum,attrset);
}


/*** INITIALIZATION ***/

static void *mark_local(void *ignore, void *node) {
  if (ABSTRACT_APS_tnode_phylum(node) == KEYDeclaration) {
    Declaration_info((Declaration)node)->decl_flags |= DECL_LOCAL_FLAG;
  }
}

static void init_node_phy_graph2(Declaration node, Type ty, STATE *state) { 
  switch (Type_KEY(ty)) {
  default:
    fprintf(stderr,"%d: cannot handle type: ",tnode_line_number(ty));
    print_Type(ty,stderr);
    fputc('\n',stderr);
    fatal_error("Abort");
  case KEYtype_use:
    { Declaration phylum=Use_info(type_use_use(ty))->use_decl;
      if (phylum == NULL)
	fatal_error("%d: unbound type",tnode_line_number(ty));
      switch (Declaration_KEY(phylum)) {
      case KEYphylum_decl:
	Declaration_info(node)->node_phy_graph =
	  summary_graph_for(state,phylum);
	break;
      case KEYtype_decl:
	break;
      default:
	aps_error(node,"could not find type for summary graph");
	break;
      }
    }
    break;
  case KEYremote_type:
    init_node_phy_graph2(node,remote_type_nodetype(ty),state);
    break;
  }
}


static void init_node_phy_graph(Declaration node, STATE *state) {
  Type ty=infer_formal_type(node);
  init_node_phy_graph2(node,ty,state);
}

static void init_augmented_dependency_graph(AUG_GRAPH *aug_graph, 
					    Declaration tlm,
					    STATE *state)
{
  Block body;
  aug_graph->match_rule = tlm;
  aug_graph->global_state = state;

  switch (Declaration_KEY(tlm)) {
  default: fatal_error("%d:unknown top-level-match",tnode_line_number(tlm));
  case KEYmodule_decl: /* representing shared instances. */
    aug_graph->syntax_decl = tlm;
    aug_graph->lhs_decl = tlm;
    aug_graph->first_rhs_decl = NULL;
    { int i;
      for (i=0; i < state->phyla.length; ++i) {
	if (state->phyla.array[i] == state->start_phylum) break;
      }
      if (i == state->phyla.length)
	fatal_error("%d: Cannot find start phylum summary graph",
		    tnode_line_number(tlm));
      Declaration_info(tlm)->node_phy_graph = &state->phy_graphs[i];
      Declaration_info(tlm)->decl_flags |= DECL_RHS_FLAG;
    }
    body = module_decl_contents(tlm);
    break;
  case KEYsome_function_decl:
    aug_graph->syntax_decl = tlm;
    aug_graph->lhs_decl = tlm;
    aug_graph->first_rhs_decl = NULL;
    { int i;
      for (i=0; i < state->phyla.length; ++i) {
	if (state->phyla.array[i] == tlm) break;
      }
      if (i == state->phyla.length)
	fatal_error("%d: Cannot find summary phylum graph",
		    tnode_line_number(tlm));
      Declaration_info(tlm)->node_phy_graph = &state->phy_graphs[i];
    }
    body = some_function_decl_body(tlm);
    Declaration_info(tlm)->decl_flags |= DECL_LHS_FLAG;
    { Type ftype=some_function_decl_type(tlm);
      Declaration formal=first_Declaration(function_type_formals(ftype));
      Declaration result=first_Declaration(function_type_return_values(ftype));
      for (; formal != NULL; formal=Declaration_info(formal)->next_decl) {
	Declaration_info(formal)->decl_flags |= ATTR_DECL_INH_FLAG;
      }
      for (; result != NULL; result=Declaration_info(result)->next_decl) {
	Declaration_info(result)->decl_flags |= ATTR_DECL_SYN_FLAG;
      }
    }
    break;
  case KEYtop_level_match:
    body = matcher_body(top_level_match_m(tlm));
    { Pattern pat=matcher_pat(top_level_match_m(tlm));
      switch (Pattern_KEY(pat)) {
      default: fatal_error("%d:improper top-level-match",
			   tnode_line_number(tlm));
      case KEYand_pattern:
	switch (Pattern_KEY(and_pattern_p1(pat))) {
	default: fatal_error("%d:improper top-level-match",
			     tnode_line_number(tlm));
	case KEYpattern_var:
	  aug_graph->lhs_decl = pattern_var_formal(and_pattern_p1(pat));
	  Declaration_info(aug_graph->lhs_decl)->decl_flags |= DECL_LHS_FLAG;
	  init_node_phy_graph(aug_graph->lhs_decl,state);
	  break;
	}
	pat = and_pattern_p2(pat);
      }
      switch (Pattern_KEY(pat)) {
      default: fatal_error("%d:misformed pattern",tnode_line_number(pat));
      case KEYpattern_call:
	switch (Pattern_KEY(pattern_call_func(pat))) {
	default:
	  fatal_error("%d:unknown pattern function",tnode_line_number(pat));
	case KEYpattern_use:
	  { Declaration decl =
	      Use_info(pattern_use_use(pattern_call_func(pat)))->use_decl;
	    if (decl == NULL) fatal_error("%d:unbound pfunc",
					  tnode_line_number(pat));
	    aug_graph->syntax_decl = decl;
	  }
	}
	{ Declaration last_rhs = NULL;
	  Pattern next_pat;
	  for (next_pat = first_PatternActual(pattern_call_actuals(pat));
	       next_pat != NULL;
	       next_pat = Pattern_info(next_pat)->next_pattern_actual) {
	    switch (Pattern_KEY(next_pat)) {
	    default:
	      aps_error(next_pat,"too complex a pattern");
	      break;
	    case KEYpattern_var:
	      { Declaration next_rhs = pattern_var_formal(next_pat);
		Declaration_info(next_rhs)->decl_flags |= DECL_RHS_FLAG;
		init_node_phy_graph(next_rhs,state);
		if (last_rhs == NULL) {
		  aug_graph->first_rhs_decl = next_rhs;
		} else {
		  Declaration_info(last_rhs)->next_decl = next_rhs;
		}
		last_rhs = next_rhs;
	      }
	      break;
	    }
	  }
	}
	break;
      }
    }
    break;
  }

  /* initialize the if_rules vector */
  { int num_if_rules = 0;
    CONDITION cond;
    traverse_Declaration(count_if_rules,&num_if_rules,tlm);
    if (num_if_rules > 32)
      fatal_error("Can handle up to 32 conditionals (got %d)",num_if_rules);

    VECTORALLOC(aug_graph->if_rules,void*,num_if_rules);
    traverse_Declaration(get_if_rules,aug_graph->if_rules.array,tlm);
    /* now initialize the decl_cond on every Declaration */
    cond.positive = 0;
    cond.negative = 0;
    traverse_Declaration(init_decl_cond,&cond,tlm);
  }

  /* initialize the instances vector */
  { 
    int i, n = aug_graph->if_rules.length;
    aug_graph->instances.length = n; /* add ifs */
    aug_graph->instances.array = NULL;
    traverse_Declaration(get_instances,aug_graph,tlm);
    VECTORALLOC(aug_graph->instances,INSTANCE,aug_graph->instances.length);
    for (i=0; i < n; ++i) {
      assign_instance(aug_graph->instances.array, i,
		      (Declaration)aug_graph->if_rules.array[i], /* kludge */
		      0,0,0);
    }
    traverse_Declaration(get_instances,aug_graph,tlm);
  }

  /* allocate the edge set array */
  { int n = aug_graph->instances.length;
    int i;
    aug_graph->graph = (EDGESET *)HALLOC(n*n*sizeof(EDGESET));
    for (i=n*n-1; i >= 0; --i) {
      aug_graph->graph[i] = NULL;
    }
  }

  /* initialize the edge set array */
  traverse_Block(get_edges,aug_graph,body);

  /* add shared_info edges for rhs decls */
  if (aug_graph->first_rhs_decl != NULL) {
    Declaration lattr = phylum_shared_info_attribute
      (node_decl_phylum(aug_graph->lhs_decl),state);
    INSTANCE *source =
      get_instance(lattr,NULL,FALSE,aug_graph->lhs_decl,aug_graph);
    CONDITION cond;
    Declaration decl;
    cond.positive = 0; cond.negative = 0;
    for (decl = aug_graph->first_rhs_decl;
	 decl != NULL;
	 decl = DECL_NEXT(decl)) {
      Declaration phy = node_decl_phylum(decl);
      if (phy != NULL) {
	Declaration rattr = phylum_shared_info_attribute(phy,state);
	INSTANCE *sink = get_instance(rattr,NULL,FALSE,decl,aug_graph);
	add_edges_to_graph(source,sink,&cond,dependency,aug_graph);
      }
    }
  }
  
  aug_graph->next_in_aug_worklist = NULL;
  aug_graph->schedule = (int *)HALLOC(aug_graph->instances.length*sizeof(int));
}

static void init_summary_dependency_graph(PHY_GRAPH *phy_graph,
					  Declaration phylum,
					  STATE *state)
{
  ATTRSET attrset=attrset_for(state,phylum);
  int count=0;
  phy_graph->phylum = phylum;
  phy_graph->global_state = state;
  { ATTRSET as=attrset;
    for (; as != NULL; as=as->rest) {
      FIBERSET fs;
      ++count; /* base attribute */
      for (fs = fiberset_for(as->attr,FIBERSET_NORMAL_FINAL); fs != NULL; fs=fs->rest) {
	++count;
      }
      for (fs = fiberset_for(as->attr,FIBERSET_REVERSE_FINAL); fs != NULL; fs=fs->rest) {
	++count;
      }
    }
  }
  VECTORALLOC(phy_graph->instances,INSTANCE,count);
  { int index=0;
    ATTRSET as=attrset;
    INSTANCE *array=phy_graph->instances.array;
    for (; as != NULL; as=as->rest) {
      FIBERSET fs;
      assign_instance(array,index++,as->attr,NULL,FALSE,NULL); /* base attribute */
      for (fs=fiberset_for(as->attr,FIBERSET_NORMAL_FINAL); fs != NULL; fs=fs->rest) {
	assign_instance(array,index++,as->attr,fs->fiber,FALSE,NULL);
      }
      for (fs=fiberset_for(as->attr,FIBERSET_REVERSE_FINAL); fs != NULL; fs=fs->rest) {
	assign_instance(array,index++,as->attr,fs->fiber,TRUE,NULL);
      }
    }
  }
  { int total = count*count;
    int i;
    phy_graph->mingraph = (DEPENDENCY *)HALLOC(total*sizeof(DEPENDENCY));
    for (i=0; i < total; ++i) {
      phy_graph->mingraph[i] = no_dependency;
    }
  }
  phy_graph->next_in_phy_worklist = NULL;
  phy_graph->summary_schedule = (int *)HALLOC(count*sizeof(int));
}

static void init_analysis_state(STATE *s, Declaration module) {
  Declarations type_formals = module_decl_type_formals(module);
  Declarations decls = block_body(module_decl_contents(module));
  s->module = module;
  s->phylum_attrset_table = new_table();

  /* mark all local declarations such */
  traverse_Declaration(mark_local,module,module);

  /* get phyla (imported only) */
  { Declaration tf=first_Declaration(type_formals);
    Declarations edecls = NULL;
    while (tf != NULL && !TYPE_FORMAL_IS_EXTENSION(tf)) {
      tf = Declaration_info(tf)->next_decl;
    }
    if (tf != NULL) {
      Signature sig = some_type_formal_sig(tf);
      switch (Signature_KEY(sig)) {
      default:
	fatal_error("%d:cannot handle the signature of extension",
		    tnode_line_number(tf));
	break;
      case KEYsig_inst:
	/*! ignore is_input and is_var */
	{ Class cl = sig_inst_class(sig);
	  switch (Class_KEY(cl)) {
	  default: fatal_error("%d: bad class",tnode_line_number(cl));
	    break;
	  case KEYclass_use:
	    { Declaration d = Use_info(class_use_use(cl))->use_decl;
	      if (d == NULL) fatal_error("%d: class not found",
					 tnode_line_number(cl));
	      switch (Declaration_KEY(d)) {
	      default: fatal_error("%d: bad class_decl %s",
				   tnode_line_number(cl),
				   symbol_name(def_name(declaration_def(d))));
		break;
	      case KEYsome_class_decl:
		edecls = block_body(some_class_decl_contents(d));
		break;
	      }
	    }
	    break;
	  }
	}
	break;
      }
    }
    { int phyla_count = 0;
      if (edecls == NULL) {
	aps_error(module,"no extension to module %s",
		  symbol_name(def_name(declaration_def(module))));
      } else {
	Declaration edecl = first_Declaration(edecls);
	/*DEBUG fprintf(stderr,"got an extension!\n"); */
	for (; edecl != NULL; edecl = Declaration_info(edecl)->next_decl) {
	  switch (Declaration_KEY(edecl)) {
	  case KEYphylum_decl:
	    if (def_is_public(phylum_decl_def(edecl))) ++phyla_count;
	    if (DECL_IS_START_PHYLUM(edecl)) s->start_phylum = edecl;
	    break;
	  }
	}
      }
      if (s->start_phylum == NULL)
	fatal_error("no root_phylum indicated");
      /* we count functions and procedures as *both* phyla
       * and match rules (for convenience).  Here we count them as phyla:
       */
      { Declaration decl = first_Declaration(decls);
	for (; decl != NULL; decl = DECL_NEXT(decl)) {
	  switch (Declaration_KEY(decl)) {
	  case KEYsome_function_decl:
	    ++phyla_count;
	    break;
	  }
	}
      }
      VECTORALLOC(s->phyla,Declaration,phyla_count);
      phyla_count = 0;
      if (edecls != NULL) {
	Declaration edecl;
	for (edecl = first_Declaration(edecls);
	     edecl != NULL; edecl = Declaration_info(edecl)->next_decl) {
	  switch (Declaration_KEY(edecl)) {
	  case KEYphylum_decl:
	    if (def_is_public(phylum_decl_def(edecl)))  {
	      s->phyla.array[phyla_count++] = edecl;
	    }
	    break;
	  }
	}
      }
      { Declaration decl = first_Declaration(decls);
	for (; decl != NULL; decl = DECL_NEXT(decl)) {
	  switch (Declaration_KEY(decl)) {
	  case KEYsome_function_decl:
	    s->phyla.array[phyla_count++] = decl;
	    break;
	  }
	}
      }
    }
  }

  /* get match rules */
  { int match_rule_count = 0;
    Declaration decl = first_Declaration(decls);
    if (decl == NULL) aps_error(module,"empty module");
    for (; decl != NULL; decl = Declaration_info(decl)->next_decl) {
      switch (Declaration_KEY(decl)) {
      case KEYsome_function_decl:
      case KEYtop_level_match: ++match_rule_count; break;
	/*DEBUG
      case KEYdeclaration:
	fprintf(stderr,"Found decl: %s\n",
		symbol_name(def_name(declaration_def(decl))));
	break;
      default:
	fprintf(stderr,"Found something\n");
	break;*/
      }
    }
    VECTORALLOC(s->match_rules,Declaration,match_rule_count);
    match_rule_count=0;
    for (decl = first_Declaration(decls);
	 decl != NULL;
	 decl = Declaration_info(decl)->next_decl) {
      switch (Declaration_KEY(decl)) {
      case KEYsome_function_decl:
      case KEYtop_level_match:
	s->match_rules.array[match_rule_count++] = decl;
	break;
      }
    }
  }
  
  /* perform fibering */
  fiber_module(s->module,s);

  /* initialize attrset_table */
  { Declaration decl = first_Declaration(decls);
    for (; decl != NULL; decl = Declaration_info(decl)->next_decl) {
      switch (Declaration_KEY(decl)) {
      case KEYattribute_decl:
	if (!ATTR_DECL_IS_SYN(decl) && !ATTR_DECL_IS_INH(decl) &&
	    !FIELD_DECL_P(decl)) {
	  aps_error(decl,"%s not declared either synthesized or inherited",
		    decl_name(decl));
	  Declaration_info(decl)->decl_flags |= ATTR_DECL_SYN_FLAG;
	}
	{ Type ftype = attribute_decl_type(decl);
	  Declaration formal = first_Declaration(function_type_formals(ftype));
	  Type ntype = formal_type(formal);
	  switch (Type_KEY(ntype)) {
	  case KEYtype_use:
	    { Declaration phylum=Use_info(type_use_use(ntype))->use_decl;
	      if (phylum == NULL)
		fatal_error("%d: unknown phylum",tnode_line_number(ntype));
	      add_attrset_for(s,phylum,decl);
	    }
	    break;
	  }
	}
	break;
      case KEYsome_function_decl:
	/* The parameters are inherited attributes
	 * and the results are synthesized ones.
	 */
	{ Type ftype = some_function_decl_type(decl);
	  Declaration d;
	  for (d = first_Declaration(function_type_formals(ftype));
	       d != NULL;
	       d = DECL_NEXT(d)) {
	    Declaration_info(d)->decl_flags |= ATTR_DECL_INH_FLAG;
	    add_attrset_for(s,decl,d);
	  }
	  for (d = first_Declaration(function_type_return_values(ftype));
	       d != NULL;
	       d = DECL_NEXT(d)) {
	    Declaration_info(d)->decl_flags |= ATTR_DECL_SYN_FLAG;
	    add_attrset_for(s,decl,d);
	  }
	}
	break;
      }
    }
  }
  /* add special shared_info attributes */
  { int i;
    for (i=0; i < s->phyla.length; ++i) {
      Declaration phy = s->phyla.array[i];
      add_attrset_for(s,phy,phylum_shared_info_attribute(phy,s));
    }
  }

  /* initialize graphs */
  s->aug_graphs = (AUG_GRAPH *)HALLOC(s->match_rules.length*sizeof(AUG_GRAPH));
  s->phy_graphs = (PHY_GRAPH *)HALLOC(s->phyla.length*sizeof(PHY_GRAPH));
  { int i;
    for (i=0; i < s->match_rules.length; ++i) {
      init_augmented_dependency_graph(&s->aug_graphs[i],
				      s->match_rules.array[i],s);
    }
    init_augmented_dependency_graph(&s->global_dependencies,module,s);
    for (i=0; i < s->phyla.length; ++i) {
      init_summary_dependency_graph(&s->phy_graphs[i],
				    s->phyla.array[i],s);
    }
  } 
}


/*** ANALYSIS ***/

static void synchronize_dependency_graphs(AUG_GRAPH *aug_graph,
					  int start,
					  PHY_GRAPH *phy_graph) {
  int n=aug_graph->instances.length;
  int max;
  int phy_n;
  int i,j;

  if (phy_graph == NULL) {
    /* a semantic child of a constructor */
    return;
  }

  phy_n = phy_graph->instances.length;

  /* discover when the instances for this node end.
   */
  max = start + phy_n;
  
  for (i=start; i < max; ++i) {
    INSTANCE *source = &aug_graph->instances.array[i];
    INSTANCE *phy_source = &phy_graph->instances.array[i-start];
    if (!fibered_attr_equal(&source->fibered_attr,
			    &phy_source->fibered_attr)) {
      print_instance(source,stderr);
      fputs(" != ",stderr);
      print_instance(phy_source,stderr);
      fputc('\n',stderr);
      fatal_error("instances %d vs %d in different order",i,i-start);
    }
    for (j=start; j < max; ++j) {
      INSTANCE *sink = &aug_graph->instances.array[j];
      int aug_index = i*n + j;
      int sum_index = (i-start)*phy_n + (j-start);
      DEPENDENCY kind=edgeset_kind(aug_graph->graph[aug_index]);
      if (!AT_MOST(kind,phy_graph->mingraph[sum_index])) {
	kind = dependency_indirect(kind); //! more precisely DNC artificial
	kind = dependency_join(kind,phy_graph->mingraph[sum_index]);
	if (analysis_debug & SUMMARY_EDGE) {
	  printf("Adding to summary edge %d: ",kind);
	  print_instance(source,stdout);
	  printf(" -> ");
	  print_instance(sink,stdout);
	  printf("\n");
	}
	phy_graph->mingraph[sum_index] = kind;
	/*?? put on a worklist somehow ? */
      } else if (!AT_MOST(phy_graph->mingraph[sum_index],
			  edgeset_lowerbound(aug_graph->graph[aug_index]))) {
	CONDITION cond;
	cond.positive=0; cond.negative=0;
	kind = dependency_join(kind,phy_graph->mingraph[sum_index]);
	if (analysis_debug & SUMMARY_EDGE_EXTRA) {
	  printf("Possibly adding summary edge %d: ",kind);
	  print_instance(source,stdout);
	  printf(" -> ");
	  print_instance(sink,stdout);
	  printf("\n");
	}
	add_edge_to_graph(source,sink,&cond,kind,aug_graph);
      }
    }
  }
}

static void augment_dependency_graph_for_node(AUG_GRAPH *aug_graph,
					      Declaration node) {
  int start=Declaration_info(node)->instance_index;
  PHY_GRAPH *phy_graph = Declaration_info(node)->node_phy_graph;

  synchronize_dependency_graphs(aug_graph,start,phy_graph);
}

/** Augment the dependencies between edges associated with a procedure call,
 * or a function call.
 * @see traverse_Declaration
 */
void *augment_dependency_graph_func_calls(void *paug_graph, void *node) {
  AUG_GRAPH *aug_graph = (AUG_GRAPH *)paug_graph;
  switch (ABSTRACT_APS_tnode_phylum(node)) {
  default:
    break;
  case KEYExpression:
    {
      Expression e = (Expression)node;
      Declaration fdecl = 0;
      if ((fdecl = local_call_p(e)) != NULL &&
	  Declaration_KEY(fdecl) == KEYfunction_decl) {
	Declaration proxy = Expression_info(e)->funcall_proxy;
	if (proxy == NULL)
	  fatal_error("missing funcall proxy");
	augment_dependency_graph_for_node(aug_graph,proxy);
      }
    }
    break;
  case KEYDeclaration:
    { Declaration decl = (Declaration)node;
      switch (Declaration_KEY(decl)) {
      case KEYsome_function_decl:
      case KEYtop_level_match:
	/* don't look inside (unless its what we're doing the analysis for) */
	if (aug_graph->match_rule != node) return NULL;
	break;
      case KEYassign:
	{ Declaration pdecl = proc_call_p(assign_rhs(decl));
	  if (pdecl != NULL) {
	    augment_dependency_graph_for_node(aug_graph,decl);
	  }
	}
	break;
      }
    }
    break;
  }
  return paug_graph;
}

/* copy in (and out!) summary dependencies */
void augment_dependency_graph(AUG_GRAPH *aug_graph) {
  Declaration rhs_decl;
  switch (Declaration_KEY(aug_graph->match_rule)) {
  default:
    fatal_error("unexpected match rule");
    break;
  case KEYmodule_decl:
    augment_dependency_graph_for_node(aug_graph,aug_graph->match_rule);
    break;
  case KEYsome_function_decl:
    augment_dependency_graph_for_node(aug_graph,aug_graph->match_rule);
    break;
  case KEYtop_level_match:
    augment_dependency_graph_for_node(aug_graph,aug_graph->lhs_decl);
    for (rhs_decl = aug_graph->first_rhs_decl;
	 rhs_decl != NULL;
	 rhs_decl = Declaration_info(rhs_decl)->next_decl) {
      augment_dependency_graph_for_node(aug_graph,rhs_decl);
    }
    break;
  }
  /* find procedure calls */
  traverse_Declaration(augment_dependency_graph_func_calls,
		       aug_graph,aug_graph->match_rule);
}

static void close_using_edge(AUG_GRAPH *aug_graph, EDGESET edge) {
  int i,j;
  int source_index = edge->source->index;
  int sink_index = edge->sink->index;
  int n=aug_graph->instances.length;

  if (analysis_debug & CLOSE_EDGE) {
    printf("Closing with ");
    print_edge(edge,stdout);
  }

  for (i=0; i < n; ++i) {
    EDGESET e;
    /* first: instance[i]->source */
    for (e = aug_graph->graph[i*n+source_index];
	 e != NULL;
	 e = e->rest) {
      add_transitive_edge_to_graph(e->source,edge->sink,
				   &e->cond,&edge->cond,
				   e->kind,edge->kind,
				   aug_graph);
    }
    /* then sink->instance[i] */
    for (e = aug_graph->graph[sink_index*n+i];
	 e != NULL;
	 e = e->rest) {
      add_transitive_edge_to_graph(edge->source,e->sink,
				   &edge->cond,&e->cond,
				   edge->kind,e->kind,
				   aug_graph);
    }
  }
}

/* return whether any changes were noticed */
BOOL close_augmented_dependency_graph(AUG_GRAPH *aug_graph) {
  augment_dependency_graph(aug_graph);
  if (aug_graph->worklist_head == NULL) {
    if (analysis_debug & DNC_ITERATE)
      printf("Worklist is empty\n");
    return FALSE;
  }

  while (aug_graph->worklist_head != NULL) {
    EDGESET edge=aug_graph->worklist_head;
    aug_graph->worklist_head = edge->next_in_edge_worklist;
    if (aug_graph->worklist_tail == edge) {
      if (edge->next_in_edge_worklist != NULL)
	fatal_error("worklist out of whack!");
      aug_graph->worklist_tail = NULL;
    }
    edge->next_in_edge_worklist = NULL;
    close_using_edge(aug_graph,edge);
  }

  augment_dependency_graph(aug_graph);
  return TRUE;
}

/* return whether any changes were noticed */
BOOL close_summary_dependency_graph(PHY_GRAPH *phy_graph) {
  int i,j,k;
  int n = phy_graph->instances.length;
  BOOL any_changed = FALSE;
  BOOL changed;
  do {
    changed = FALSE;
    /* no worklists, just a dumb in-place matrix squaring */
    for (i=0; i < n; ++i) {
      for (j=0; j < n; ++j) {
	DEPENDENCY ij=phy_graph->mingraph[i*n+j];
	if (ij != max_dependency) {
	  /* maybe could be made stronger */
	  for (k=0; k<n; ++k) {
	    DEPENDENCY ik = phy_graph->mingraph[i*n+k];
	    DEPENDENCY kj = phy_graph->mingraph[k*n+j];
	    DEPENDENCY tmpij = dependency_trans(ik,kj);
	    if (!AT_MOST(tmpij,ij)) {
	      ij=dependency_join(tmpij,ij);
	      changed = TRUE;
	      any_changed = TRUE;
	      phy_graph->mingraph[i*n+j] = ij;
	      if (ij == max_dependency) break;
	    }
	  }
	}
      }
    }
  } while (changed);
  return any_changed;
}

DEPENDENCY analysis_state_cycle(STATE *s) {
  int i,j;
  DEPENDENCY kind = no_dependency;
  /** test for cycles **/
  for (i=0; i < s->phyla.length; ++i) {
    PHY_GRAPH *phy_graph = &s->phy_graphs[i];
    int n = phy_graph->instances.length;
    for (j=0; j < n; ++j) {
      DEPENDENCY k1 = phy_graph->mingraph[j*n+j];
      kind = dependency_join(kind,k1);
    }
  }
  for (i=0; i < s->match_rules.length; ++i) {
    AUG_GRAPH *aug_graph = &s->aug_graphs[i];
    int n = aug_graph->instances.length;
    for (j=0; j < n; ++j) {
      DEPENDENCY k1 = edgeset_kind(aug_graph->graph[j*n+j]);
      kind = dependency_join(kind,k1);
    }
  }
  return kind;
}

STATE *compute_dnc(Declaration module) {
  STATE *s=(STATE *)HALLOC(sizeof(STATE));
  int i,j;
  BOOL changed;
  init_analysis_state(s,module);
  for (i=0; ; ++i) {
    if (analysis_debug & DNC_ITERATE) {
      printf("*** AFTER %d ITERATIONS ***\n",i);
      print_analysis_state(s,stdout);
    }
    changed = FALSE;
    for (j=0; j < s->match_rules.length; ++j) {
      if (analysis_debug & DNC_ITERATE) {
	printf("Checking rule %d\n",j);
      }
      changed |= close_augmented_dependency_graph(&s->aug_graphs[j]);
    }
    changed |= close_augmented_dependency_graph(&s->global_dependencies);
    for (j=0; j < s->phyla.length; ++j) {
      if (analysis_debug & DNC_ITERATE) {
	printf("Checking phylum %s\n",
	       symbol_name(def_name(declaration_def(s->phyla.array[j]))));
      }
      changed |= close_summary_dependency_graph(&s->phy_graphs[j]);
    }
    if (!changed) break;
  }
  if (analysis_debug & (DNC_ITERATE|DNC_FINAL)) {
    printf("*** FINAL ANALYSIS STATE ***\n");
    print_analysis_state(s,stdout);
    print_cycles(s,stdout);
  }
  return s;
}


/*** DEBUGGING OUTPUT ***/

void print_attrset(ATTRSET s, FILE *stream) {
  fputc('{',stream);
  while (s != NULL) {
    fputs(symbol_name(def_name(declaration_def(s->attr))),stream);
    s=s->rest;
    if (s != NULL) fputc(',',stream);
  }
  fputc('}',stream);
}

void print_instance(INSTANCE *i, FILE *stream) {
  if (i->node != NULL) {
    if (ABSTRACT_APS_tnode_phylum(i->node) != KEYDeclaration) {
      fprintf(stream,"%d:?<%d>",tnode_line_number(i->node),
	      ABSTRACT_APS_tnode_phylum(i->node));
    } else if (Declaration_KEY(i->node) == KEYnormal_assign) {
      Declaration pdecl = proc_call_p(normal_assign_rhs(i->node));
      fprintf(stream,"%s(...)@%d",decl_name(pdecl),
	      tnode_line_number(i->node));
    } else if (Declaration_KEY(i->node) == KEYpragma_call) {
      fprintf(stream,"%s(...):%d",symbol_name(pragma_call_name(i->node)),
	      tnode_line_number(i->node));
    } else {
      fputs(symbol_name(def_name(declaration_def(i->node))),stream);
    }
    fputc('.',stream);
  }
  if (i->fibered_attr.attr == NULL) {
    fputs("(nil)",stream);
  } else if (ABSTRACT_APS_tnode_phylum(i->fibered_attr.attr) == KEYMatch) {
    fprintf(stream,"<match@%d>",tnode_line_number(i->fibered_attr.attr));
  } else switch(Declaration_KEY(i->fibered_attr.attr)) {
  case KEYcollect_assign: {
    Expression lhs = collect_assign_lhs(i->node);
    Declaration field = field_ref_p(lhs);
    fprintf(stream,"[%d:?.",tnode_line_number(i->fibered_attr.attr));
    fputs(symbol_name(def_name(declaration_def(field))),stream);
    fputs(":>?]",stream);
  }
  case KEYif_stmt:
  case KEYcase_stmt:
    fprintf(stream,"<cond@%d>",tnode_line_number(i->fibered_attr.attr));
    break;
  default:
    fputs(symbol_name(def_name(declaration_def(i->fibered_attr.attr))),stream);
  }
  if (i->fibered_attr.fiber != NULL) {
    fputc('$',stream);
    if (i->fibered_attr.fiber_is_reverse) {
      fputc('!',stream);
    }
    print_fiber(i->fibered_attr.fiber,stream);
  }
}

void print_edge_helper(EDGESET e, FILE* stream) {
  switch (e->kind) {
  case no_dependency: fputc('!',stream); break;
  case indirect_control_fiber_dependency:
  case indirect_fiber_dependency: fputc('?',stream); /* fall through */
  case control_fiber_dependency:
  case fiber_dependency: fputc('(',stream); break;
  case indirect_control_dependency:
  case indirect_dependency: fputc('?',stream); /* fall through */
  case control_dependency:
  case dependency: break;
  }
  print_condition(&e->cond,stream);
  if ((e->kind & DEPENDENCY_NOT_JUST_FIBER) == 0) {
    fputc(')',stream);
  }
}

void print_edge(EDGESET e, FILE *stream) {
  print_instance(e->source,stream);
  fputs("->",stream);
  print_instance(e->sink,stream);
  fputc(':',stream);
  print_edge_helper(e,stream);
  fputc('\n',stream);
}
  
void print_edgeset(EDGESET e, FILE *stream) {
  if (e != NULL) {
    EDGESET tmp=e;
    print_instance(e->source,stream);
    fputs("->",stream);
    print_instance(e->sink,stream);
    fputc(':',stream);
    while (tmp != NULL) {
      if (tmp->source != e->source) {
	fputs("!!SOURCE=",stream);
	print_instance(tmp->source,stream);
      }
      if (tmp->sink != e->sink) {
	fputs("!!SINK=",stream);
	print_instance(tmp->sink,stream);
      }
      print_edge_helper(tmp,stream);
      tmp = tmp->rest;
      if (tmp != NULL) fputc(',',stream);
    }
    fputc('\n',stream);
  }
}

char *aug_graph_name(AUG_GRAPH *aug_graph) {
  switch (Declaration_KEY(aug_graph->match_rule)) {
  case KEYtop_level_match:
    { Pattern pat=matcher_pat(top_level_match_m(aug_graph->match_rule));
      switch (Pattern_KEY(pat)) {
      case KEYand_pattern:
	pat = and_pattern_p2(pat);
      }
      switch (Pattern_KEY(pat)) {
      case KEYpattern_call:
	switch (Pattern_KEY(pattern_call_func(pat))) {
	case KEYpattern_use:
	  { Declaration decl =
	      Use_info(pattern_use_use(pattern_call_func(pat)))->use_decl;
	    if (decl != NULL)
	      return symbol_name(def_name(declaration_def(decl)));
	    else
	      return "unbound pattern use";
	  }
	default:
	  return "unknown pattern function";
	}
      default:
	return "unknown pattern";
      }
    }
    break;
  case KEYfunction_decl:
  case KEYprocedure_decl:
    return symbol_name(def_name(declaration_def(aug_graph->match_rule)));
  case KEYmodule_decl:
    return "global dependencies";
  default:
    return "unknown production";
  }
}

void print_aug_graph(AUG_GRAPH *aug_graph, FILE *stream) {
  fputs("Augmented dependency graph for ",stream);
  switch (Declaration_KEY(aug_graph->match_rule)) {
  case KEYtop_level_match:
    { Pattern pat=matcher_pat(top_level_match_m(aug_graph->match_rule));
      switch (Pattern_KEY(pat)) {
      case KEYand_pattern:
	pat = and_pattern_p2(pat);
      }
      switch (Pattern_KEY(pat)) {
      case KEYpattern_call:
	switch (Pattern_KEY(pattern_call_func(pat))) {
	case KEYpattern_use:
	  print_Use(pattern_use_use(pattern_call_func(pat)),stdout);
#ifdef UNDEF
	  { Declaration decl =
	      Use_info(pattern_use_use(pattern_call_func(pat)))->use_decl;
	    if (decl != NULL)
	      fputs(symbol_name(def_name(declaration_def(decl))),stream);
	    else
	      fputs("unbound pattern use",stream);
	  }
#endif
	break;
	default:
	  fputs("unknown pattern function",stream);
	}
	break;
      default:
	fputs("unknown pattern",stream);
      }
    }
    break;
  case KEYfunction_decl:
  case KEYprocedure_decl:
    fputs(symbol_name(def_name(declaration_def(aug_graph->match_rule))),
	  stream);
    break;
  case KEYmodule_decl:
    fputs("global dependencies",stream);
    break;
  default:
    fputs("unknown production",stream);
  }
  fputs("\n",stream);
  { int n = aug_graph->instances.length;
    int max = n*n;
    int i;
    for (i=0; i < n; ++i) {
      if (i == 0) printf(" (");
      else printf(",");
      print_instance(&aug_graph->instances.array[i],stream);
    }
    printf(")\n");
    for (i=0; i < max; ++i) {
      print_edgeset(aug_graph->graph[i],stream);
    }
  }
  fputc('\n',stream);
}

void print_phy_graph(PHY_GRAPH *phy_graph, FILE *stream) {
  int i=0;
  int j=0;
  int n=phy_graph->instances.length;
  
  fprintf(stream,"\nSummary dependency graph for %s\n",
	  symbol_name(def_name(declaration_def(phy_graph->phylum))));
  for (i=0; i < n; ++i) {
    print_instance(&phy_graph->instances.array[i],stream);
    fputs(" -> ",stream);
    for (j=0; j < n; ++j) {
      DEPENDENCY kind= phy_graph->mingraph[i*n+j];
      if (kind == no_dependency) continue;
      if (kind == fiber_dependency) fputc('(',stream);
      print_instance(&phy_graph->instances.array[j],stream);
      if (kind == fiber_dependency) fputc(')',stream);
      fputc(' ',stream);
    }
    fputc('\n',stream);
  }
}

void print_analysis_state(STATE *s, FILE *stream) {
  int i;
  fprintf(stream,"Analysis state for %s\n",
	  symbol_name(def_name(declaration_def(s->module))));
  print_aug_graph(&s->global_dependencies,stream);
  for (i=0; i < s->match_rules.length; ++i) {
    print_aug_graph(&s->aug_graphs[i],stream);
  }
  for (i=0; i < s->phyla.length; ++i) {
    print_phy_graph(&s->phy_graphs[i],stream);
  }
}

void print_cycles(STATE *s, FILE *stream) {
  int i,j;
  /** test for cycles **/
  for (i=0; i < s->phyla.length; ++i) {
    BOOL fiber_cycle = FALSE;
    PHY_GRAPH *phy_graph = &s->phy_graphs[i];
    int n = phy_graph->instances.length;
    for (j=0; j < n; ++j) {
      switch (phy_graph->mingraph[j*n+j]) {
      case no_dependency: break;
      case indirect_control_fiber_dependency:
      case control_fiber_dependency:
      case indirect_fiber_dependency:
      case fiber_dependency:
	fprintf(stream,"fiber ");
	/* fall through */
      default:
	fprintf(stream,"summary cycle involving %s.",
		symbol_name(def_name(declaration_def(phy_graph->phylum))));
	print_instance(&phy_graph->instances.array[j],stdout);
	fprintf(stream,"\n");
	break;
      }
    }
  }
  for (i=0; i < s->match_rules.length; ++i) {
    AUG_GRAPH *aug_graph = &s->aug_graphs[i];
    int n = aug_graph->instances.length;
    for (j=0; j < n; ++j) {
      switch (edgeset_kind(aug_graph->graph[j*n+j])) {
      case no_dependency: break;
      case indirect_control_fiber_dependency:
      case control_fiber_dependency:
      case indirect_fiber_dependency:
      case fiber_dependency:
	fprintf(stream,"fiber ");
	/* fall through */
      default:
	fprintf(stream,"local cycle for %s involving ",
		aug_graph_name(aug_graph));
	print_instance(&aug_graph->instances.array[j],stdout);
	fprintf(stream,"\n");
	break;
      }
    }
  }
}



