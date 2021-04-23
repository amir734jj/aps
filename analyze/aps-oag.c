#include <stdio.h>
#include "jbb.h"
#include "jbb-alloc.h"
#include "aps-ag.h"

int oag_debug;

void schedule_summary_dependency_graph(PHY_GRAPH *phy_graph) {
  int n = phy_graph->instances.length;
  int done = 0;
  int local_done = 0;
  int i,j;
  int phase = 0;
  if (oag_debug & TOTAL_ORDER) {
    printf("Scheduling order for %s\n",decl_name(phy_graph->phylum));
  }
  for (i=0; i < n; ++i)
    phy_graph->summary_schedule[i] = 0;
  while (done < n) {
    ++phase; local_done = 0;
    /* find inherited instances for the phase. */
    for (i=0; i < n; ++i) {
      INSTANCE *in = &phy_graph->instances.array[i];
      if (instance_direction(in) == instance_inward &&
	  phy_graph->summary_schedule[i] == 0) {
	for (j=0; j < n; ++j) {
	  if (phy_graph->summary_schedule[j] == 0 &&
	      phy_graph->mingraph[j*n+i] != no_dependency)
	    break;
	}
	if (j == n) {
	  phy_graph->summary_schedule[i] = -phase;
	  ++done; ++local_done;
	  for (j=0; j < n; ++j) { /* force extra dependencies */
	    int sch = phy_graph->summary_schedule[j];
	    if (sch != 0 && sch != -phase)
	      phy_graph->mingraph[j*n+i] = indirect_control_dependency;
	  }
	  if (oag_debug & TOTAL_ORDER) {
	    printf("%d- ",phase);
	    print_instance(in,stdout);
	    printf("\n");
	  }
	}
      }
    }
    /* now schedule synthesized attributes */
    for (i=0; i < n; ++i) {
      INSTANCE *in = &phy_graph->instances.array[i];
      if (instance_direction(in) == instance_outward &&
	  phy_graph->summary_schedule[i] == 0) {
	for (j=0; j < n; ++j) {
	  if (phy_graph->summary_schedule[j] == 0 &&
	      phy_graph->mingraph[j*n+i] != no_dependency)
	    break;
	}
	if (j == n) {
	  phy_graph->summary_schedule[i] = phase;
	  ++done; ++local_done;
	  for (j=0; j < n; ++j) { /* force extra dependencies */
	    int sch = phy_graph->summary_schedule[j];
	    if (sch != 0 && sch != phase)
	      phy_graph->mingraph[j*n+i] = indirect_control_dependency;
	  }
	  if (oag_debug & TOTAL_ORDER) {
	    printf("%d+ ",phase);
	    print_instance(in,stdout);
	    printf("\n");
	  }
	}
      }
    }
    if (local_done == 0) {
      if (cycle_debug & PRINT_CYCLE) {
	for (i=0; i <n; ++i) {
	  INSTANCE *in = &phy_graph->instances.array[i];
	  int s = phy_graph->summary_schedule[i];
	  print_instance(in,stdout);
	  switch (instance_direction(in)) {
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
	    if (s < 0) printf(": phase -%d\n",-s);
	    else printf(":phase +%d\n",s);
	  } else {
	    printf(" depends on ");
	    for (j=0; j < n; ++j) {
	      if (phy_graph->summary_schedule[j] == 0 &&
		  phy_graph->mingraph[j*n+i] != no_dependency) {
		INSTANCE *in2 = &phy_graph->instances.array[j];
		print_instance(in2,stdout);
		if (phy_graph->mingraph[j*n+i] == fiber_dependency)
		  printf("(?)");
		putc(' ',stdout);
	      }
	    }
	    putc('\n',stdout);
	  }
	}
      }
      fatal_error("Cycle detected when scheduling phase %d for %s",
		  phase,decl_name(phy_graph->phylum));
    }
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

CTO_NODE* schedule_rest(AUG_GRAPH *aug_graph,
			CTO_NODE* prev,
			CONDITION cond,
			int remaining)
{
  CTO_NODE* cto_node = 0;
  int i;
  int n = aug_graph->instances.length;
  int needed_condition_bits;
  int sane_remaining = 0;
  INSTANCE* in;

  /* If nothing more to do, we are done. */
  if (remaining == 0) return 0;

  for (i=0; i < n; ++i) {
    INSTANCE *in1 = &aug_graph->instances.array[i];
    int j;

    /* If already scheduled, then ignore. */
    if (aug_graph->schedule[i] != 0) continue;

    ++sane_remaining;

    /* Look for a predecessor edge */
    for (j=0; j < n; ++j) {
      INSTANCE *in2 = &aug_graph->instances.array[j];
      int index = j*n+i;
      EDGESET edges = 0;

      if (aug_graph->schedule[j] != 0) {
	/* j is scheduled already, so we can ignore dependencies */
	continue;
      }

      /* Look at all dependencies from j to i */
      for (edges = aug_graph->graph[index]; edges != 0; edges=edges->rest) {
	CONDITION merged;
	merged.positive = cond.positive | edges->cond.positive;
	merged.negative = cond.negative | edges->cond.negative;

	/* if the merge condition is impossible, ignore this edge */
	if (merged.positive & merged.negative) continue;

	if (oag_debug & PROD_ORDER_DEBUG) {
	  int i=n-remaining;
	  for (; i > 0; --i) printf("  ");
	  if (aug_graph->schedule[j] == 0)
	    printf("! ");
	  else
	    printf("? ");
	  print_edge(edges,stdout);
	}

	/* If j not scheduled, then i cannot be considered */
	break; /* leave edges != 0 */
      }

      /* If a remaining edge, then i cannot be considered */
      if (edges != 0) break;
    }

    /* If we got through all predecessors, we can stop */
    if (j == n) break;
  }

  if (i == n) {
    fflush(stdout);
    if (sane_remaining != remaining) {
      fprintf(stderr,"remaining out of sync %d != %d\n",
	      sane_remaining, remaining);
    }
    fprintf(stderr,"Cannot make conditional total order!\n");
    for (i=0; i < n; ++i) {
      INSTANCE *in1 = &aug_graph->instances.array[i];
      int j;

      if (aug_graph->schedule[i] != 0) continue;

      fprintf(stderr,"  ");
      print_instance(in1,stderr);
      fprintf(stderr," requires:\n");

      for (j=0; j < n; ++j) {
	INSTANCE *in2 = &aug_graph->instances.array[j];
	int index = j*n+i;
	EDGESET edges = 0;
	
	if (aug_graph->schedule[j] != 0) {
	  /* j is scheduled already, so we can ignore dependencies */
	  continue;
	}

	/* Look at all dependencies from j to i */
	for (edges = aug_graph->graph[index]; edges != 0; edges=edges->rest) {
	  CONDITION merged;
	  merged.positive = cond.positive | edges->cond.positive;
	  merged.negative = cond.negative | edges->cond.negative;
	  
	  /* if the merge condition is impossible, ignore this edge */
	  if (merged.positive & merged.negative) continue;
	  break; /* leave edges != 0 */
	}

	if (edges != 0) {
	  fputs("    ",stderr);
	  print_instance(in2,stderr);
	  fputs("\n",stderr);
	}
      }
    }
    fatal_error("Cannot make conditional total order!");
  }

  in = &aug_graph->instances.array[i];

  /* check to see if makes sense
   * (No need to schedule something that
   * occurs only in a different condition branch.)
   */
  {
    CONDITION icond = instance_condition(in);
    if ((cond.positive|icond.positive)&
	(cond.negative|icond.negative)) {
      if (oag_debug & PROD_ORDER) {
	int i=n-remaining;
	for (; i > 0; --i) printf("  ");
	print_instance(in,stdout);
	puts(" (ignored)");
      }
      aug_graph->schedule[i] = 1;
      cto_node = schedule_rest(aug_graph,prev,cond,remaining-1);
      aug_graph->schedule[i] = 0;
      return cto_node;
    }
  }

  if (oag_debug & PROD_ORDER) {
    int i=n-remaining;
    for (; i > 0; --i) printf("  ");
    print_instance(in,stdout);
    putchar('\n');
  }

  cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
  cto_node->cto_prev = prev;
  cto_node->cto_instance = in;

  aug_graph->schedule[i] = 1;
  if (if_rule_p(in->fibered_attr.attr)) {
    int cmask = 1 << (if_rule_index(in->fibered_attr.attr));
    cond.negative |= cmask;
    cto_node->cto_if_false =
      schedule_rest(aug_graph,cto_node,cond,remaining-1);
    cond.negative &= ~cmask;
    cond.positive |= cmask;
    cto_node->cto_if_true =
      schedule_rest(aug_graph,cto_node,cond,remaining-1);
    cond.positive &= ~cmask;
  } else {
    cto_node->cto_next = schedule_rest(aug_graph,cto_node,cond,remaining-1);
  }
  aug_graph->schedule[i] = 0;

  return cto_node;
}

// Instance group exogenous linkedlist
typedef struct instance_group_item_type INSTANCE_GROUP_ITEM;

struct instance_group_item_type
{ 
  INSTANCE* instance;
  INSTANCE_GROUP_ITEM* next;
};

// Scheduling groups
// 1) <-ph,nch> inh attr of parent
// 2) <+ph,nch> syn attr of parent
// 3) <ph,ch>   all attrs of child
// 4) <0,0>     for all locals and conditionals
typedef struct instance_groups {
  INSTANCE_GROUP_ITEM* group1;
  INSTANCE_GROUP_ITEM* group2;
  INSTANCE_GROUP_ITEM* group3;
  INSTANCE_GROUP_ITEM* group4;
} INSTANCE_GROUPS;

static INSTANCE_GROUP_ITEM* get_group_item(INSTANCE_GROUPS* instance_groups, KEY_SCHEDULE_GROUP group_key)
{
  switch (group_key)
  {
  case KEY_SCHEDULE_GROUP1:
    return instance_groups->group1;
  case KEY_SCHEDULE_GROUP2:
    return instance_groups->group2;
  case KEY_SCHEDULE_GROUP3:
    return instance_groups->group3;
  case KEY_SCHEDULE_GROUP4:
    return instance_groups->group4;
  }
}

/*
 * Returns boolean indicating if condition is impossible
 * @param cond
 * @return true is condition is impossible or false if possible
 */
static bool condition_is_impossible(CONDITION* cond)
{
  return cond->positive & cond->negative;
}

static bool ready_to_go(AUG_GRAPH *aug_graph, int* schedule, INSTANCE_GROUP_ITEM* instance_group)
{
  // TODO: how to test if groups is ready to go?
}

static KEY_SCHEDULE_GROUP schedule_group(INSTANCE* instance)
{
  if (if_rule_p(instance->fibered_attr.attr))
  {
    return KEY_SCHEDULE_GROUP4;
  }

  switch (instance_direction(instance))
  {
  case instance_local:
    return KEY_SCHEDULE_GROUP4;
  case instance_inward:
    return KEY_SCHEDULE_GROUP2;
  case instance_outward:
    return KEY_SCHEDULE_GROUP1;
  }
}

// When trying to add the next thing(s) to a CTO, we don’t select an attribute which is part of a group unless *all* the attributes part of that group are ready to go.
// Maybe a helper function for “ready to go” would be useful, but it will need to take the “schedule” array as well as the dependency graph.
// If the attribute that is ready is part of a group: check to see if any earlier attributes in same group (in which case reject)
//    or if any later attributes in the same group are NOT ready yet (in case reject), otherwise: we found a group to schedule!
// If it’s a child group, arrange the inherited first, then a child visit marker and then the synthesized
// If it’s a parent group, 
// if it’s inherited attributes, they should be first, this means we have a phase change.
// This means we start in phase 0 before the parent inherited attributes.
// If a synthesized group, its the end of a phase, schedule and phase change and update child phase.
// Maybe we won’t need a child_phase array because all the children attributes are labeled by their phase anyway.
static CTO_NODE* schedule_visits(AUG_GRAPH *aug_graph, CTO_NODE* prev, CONDITION cond, CHILD_PHASE* instance_group)
{
  CTO_NODE* cto_node = 0;
  int i, j;
  int n = aug_graph->instances.length;
  int* schedule = alloca(n);

  // Step1) create scheduling groups
  INSTANCE_GROUPS* instance_groups = (INSTANCE_GROUPS*)alloca(sizeof(struct instance_groups));
  instance_groups->group1 = NULL;
  instance_groups->group2 = NULL;
  instance_groups->group3 = NULL;
  instance_groups->group4 = NULL;

  for (i = 0; i < n; i++)
  {
    INSTANCE *instance = &aug_graph->instances.array[i];

    KEY_SCHEDULE_GROUP group_key = schedule_group(instance);
    INSTANCE_GROUP_ITEM* instance_group_item = (INSTANCE_GROUP_ITEM*) alloca(sizeof(struct instance_group_item_type));
    instance_group_item->instance = instance;

    switch (group_key)
    {
    case KEY_SCHEDULE_GROUP1:
      instance_group_item->next = instance_groups->group1;
      instance_groups->group1 = instance_group_item;
      break;
    case KEY_SCHEDULE_GROUP2:
      instance_group_item->next = instance_groups->group2;
      instance_groups->group2 = instance_group_item;
      break;
    case KEY_SCHEDULE_GROUP3:
      instance_group_item->next = instance_groups->group3;
      instance_groups->group3 = instance_group_item;
      break;
    case KEY_SCHEDULE_GROUP4:
      instance_group_item->next = instance_groups->group4;
      instance_groups->group4 = instance_group_item;
      break;
    }
  }

  for (i = 0; i < n; i++)
  {
    INSTANCE *instance = &aug_graph->instances.array[i];

    KEY_SCHEDULE_GROUP group_key = schedule_group(instance);

    if (oag_debug & PROD_ORDER_DEBUG)
    {
      print_instance(instance, stdout);
      printf("\n");
    }

    for (j = 0; j < n; j++)
    {
      // edges from j to i
      EDGESET edges = aug_graph->graph[j * n + i];

      if (aug_graph->schedule[j] != 0)
      {
        /* j is scheduled already, so we can ignore its dependencies */
        continue;
      }

      /* Look at all dependencies from j to i */
      while (edges != NULL)
      {
        // TODO

        edges = edges->rest;
      }

      if (ready_to_go(aug_graph, schedule, get_group_item(instance_groups, group_key)))
      {
        // TODO: schedule the attribute
      }
    }
  }

  return cto_node;
}

void schedule_augmented_dependency_graph(AUG_GRAPH *aug_graph) {
  int n = aug_graph->instances.length;
  int i;
  CONDITION cond;

  (void)close_augmented_dependency_graph(aug_graph);

  /** Now schedule graph: we need to generate a conditional total order. */

  if (oag_debug & PROD_ORDER) {
    printf("Scheduling conditional total order for %s\n",
	   aug_graph_name(aug_graph));
  }

  /* we use the schedule array as temp storage */
  for (i=0; i < n; ++i) {
    aug_graph->schedule[i] = 0; /* This means: not scheduled yet */
  }
  cond.positive = 0;
  cond.negative = 0;

  aug_graph->total_order = schedule_rest(aug_graph,0,cond,n);
  schedule_visits(aug_graph, 0, cond, n, NULL);
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



