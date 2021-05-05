#include <stdio.h>
#include <stdlib.h>
#include <string.h>
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

#define CONDITION_IS_IMPOSSIBLE(cond) (cond.positive & cond.negative)
#define MERGED_CONDITION_IS_IMPOSSIBLE(cond1, cond2) ((cond1.positive|cond2.positive) & (cond1.negative|cond2.negative))

// TODO: temporarily
static void print_indent(int count, FILE *stream)
{
  while (count-- > 0)
  {
    fprintf(stream, " ");
  }
}

// TODO: temporarily
static void print_total_order_rec(CTO_NODE *cto, CHILD_PHASE *instance_groups, int indent, FILE *stream)
{
  if (stream == 0) stream = stdout;
  if (cto == NULL || cto->cto_instance == NULL) return;

  CHILD_PHASE *group_key = &instance_groups[cto->cto_instance->index];
  print_indent(indent, stream);
  print_instance(cto->cto_instance, stream);
  printf(" <%d,%d>", group_key->ph, group_key->ch);
  printf("\n");
  indent++;

  if (cto->cto_if_true != NULL)
  {
    print_total_order_rec(cto->cto_if_true, instance_groups, indent, stdout);
    printf("\n");
  }

  print_total_order_rec(cto->cto_next, instance_groups, indent, stdout);
}

// TODO: temporarily
static void print_total_order(CTO_NODE *cto, CHILD_PHASE *instance_groups, FILE *stream)
{
  print_total_order_rec(cto, instance_groups, 0, stream);
}

/**
 * Returns true if two attribute instances belong to the same group
 * @param aug_graph Augmented dependency graph
 * @param cond current condition
 * @param instance_groups array of <ph,ch>
 * @param i instance index to test
 * @return boolean indicating if two attributes are in the same group
 */ 
static bool instances_are_in_same_group(AUG_GRAPH *aug_graph, CHILD_PHASE* instance_groups, const int i, const int j)
{
  CHILD_PHASE *group_key1 = &instance_groups[i];
  CHILD_PHASE *group_key2 = &instance_groups[j];

  // locals
  if (!group_key1->ph && !group_key2->ph)
  {
    return i == j;
  }
  // Anything else
  else
  {
    return group_key1->ph == group_key2->ph && group_key1->ch == group_key2->ch;
  }
}

/**
 * Given a geneirc instance index it returns boolean indicating if its ready to be scheduled or not
 * @param aug_graph Augmented dependency graph
 * @param cond current condition
 * @param instance_groups array of <ph,ch>
 * @param i instance index to test
 */
static bool instance_ready_to_go(AUG_GRAPH *aug_graph, CONDITION cond, CHILD_PHASE* instance_groups, const int i)
{
  int j;
  EDGESET edges;
  int n = aug_graph->instances.length;
  
  for (j = 0; j < n; j++)
  {
    // Already scheduled then ignore
    if (aug_graph->schedule[j] != 0) continue;

    int index = j * n + i;  // j (source) >--> i (sink) edge

    /* Look at all dependencies from j to i */
    for (edges = aug_graph->graph[index]; edges != NULL; edges=edges->rest)
    {
      /* If the merge condition is impossible, ignore this edge */
      if (MERGED_CONDITION_IS_IMPOSSIBLE(cond, edges->cond)) continue;

      // Can't continue with scheduling if a dependency with a "possible" condition has not been scheduled yet
      printf("This edgeset was not ready: ");
      print_edgeset(edges, stdout);

      return false;
    }
  }

  return true;
}

/**
 * Given a generic instance index it returns boolean indicating if its ready to be scheduled or not
 * @param aug_graph Augmented dependency graph
 * @param cond current condition
 * @param instance_groups array of <ph,ch>
 * @param i instance index to test
 */
static bool group_ready_to_go(AUG_GRAPH *aug_graph, CONDITION cond, CHILD_PHASE* instance_groups, const int i)
{
  int n = aug_graph->instances.length;
  int j;
  for (j = 0; j < n; j++)
  {
    // Instance in the same group but cannot be considered
    if (instances_are_in_same_group(aug_graph, instance_groups, i, j))
    {
      if (aug_graph->schedule[j] != 0) continue;

      if (!instance_ready_to_go(aug_graph, cond, instance_groups, j))
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
 * @param instance_groups array of <ph,ch> indexed by INSTANCE index
 * @param parent_group parent group key
 * @return boolean indicating if there is more in this group that needs to be scheduled
 */
static bool is_there_more_to_schedule_in_group(AUG_GRAPH *aug_graph, CHILD_PHASE* instance_groups, CHILD_PHASE *parent_group)
{
  int n = aug_graph->instances.length;
  int i;
  for (i = 0; i < n; i++)
  {
    // Instance in the same group but cannot be considered
    CHILD_PHASE *group_key = &instance_groups[i];

    // Check if in the same group
    if (group_key->ph == parent_group->ph && group_key->ch == parent_group->ch)
    {
      if (aug_graph->schedule[i] == 0) return true;
    }
  }

  return false;
}

// Signature of function
static CTO_NODE* schedule_visits(AUG_GRAPH *aug_graph, CTO_NODE* prev, CONDITION cond, CHILD_PHASE* instance_groups, int remaining);

/**
 * Recursive scheduling function
 * @param aug_graph Augmented dependency graph
 * @param prev previous CTO node
 * @param cond current CONDITION
 * @param instance_groups array of <ph,ch> indexed by INSTANCE index
 * @param remaining count of remaining instances to schedule
 * @param parent_group parent group key
 */
static CTO_NODE* schedule_visits_group(AUG_GRAPH *aug_graph, CTO_NODE* prev, CONDITION cond, CHILD_PHASE* instance_groups, int remaining, CHILD_PHASE *parent_group)
{
  int i;
  int n = aug_graph->instances.length;
  int sane_remaining = 0;
  CTO_NODE* cto_node = NULL;
  
  /* If nothing more to do, we are done. */
  if (remaining == 0) return NULL;

  /* Outer condition is impossible, its a dead-end branch */
  if (CONDITION_IS_IMPOSSIBLE(cond)) return NULL;

  // If we find ourselves scheduling a <-ph,ch>, we need to (after putting in all the
  // instances in that group), we need to schedule the visit of the child (add a CTO
  // node with a null instance but with <ph,ch) and then ALSO schedule immediately
  // all the syn attributes of that child’s phase. (<+ph,ch> group, if any).
  if (parent_group->ph < 0 && parent_group->ch > -1)
  {
    // Group is finished
    if (!is_there_more_to_schedule_in_group(aug_graph, instance_groups, parent_group))
    {
      // Visit marker
      CTO_NODE *cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
      cto_node->cto_prev = prev;
      cto_node->cto_instance = NULL;
      cto_node->child_phase.ph = -parent_group->ph;
      cto_node->child_phase.ch = parent_group->ch;
      cto_node->cto_next = schedule_visits_group(aug_graph, cto_node, cond, instance_groups, remaining - 1, &(cto_node->child_phase));

      return cto_node;
    }
    else
    {
      return schedule_visits(aug_graph, prev, cond, instance_groups, remaining /* no change */);  
    }
  }

  // If we find ourselves scheduling a <+ph,-1>, this means that after we put all these ones in the schedule
  // (which we should do as a group NOW), this visit phase is over. And we should mark it with a <ph,-1> marker in the CTO.
  if (parent_group->ph >= 0 && parent_group->ch == -1)
  {
    // Group is finished
    if (!is_there_more_to_schedule_in_group(aug_graph, instance_groups, parent_group))
    {
      // Visit marker
      CTO_NODE *cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
      cto_node->cto_prev = prev;
      cto_node->cto_instance = NULL;
      cto_node->child_phase.ph = parent_group->ph;
      cto_node->child_phase.ch = parent_group->ch;
      cto_node->cto_next = schedule_visits(aug_graph, prev, cond, instance_groups, remaining /* no change */);

      return cto_node;
    }
  }

  for (i = 0; i < n; i++)
  {
    INSTANCE *instance = &aug_graph->instances.array[i];
    CHILD_PHASE *group_key = &instance_groups[i];

    // Already scheduled then ignore
    if (aug_graph->schedule[i] != 0) continue;

    sane_remaining++;

    // Check if everything is in the same group, don't check for dependencies
    if (group_key->ph == parent_group->ph && group_key->ch == parent_group->ch)
    {
      cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
      cto_node->cto_prev = prev;
      cto_node->cto_instance = instance;
      cto_node->child_phase = *group_key;

      aug_graph->schedule[i] = 1; // instance has been scheduled (and will not be considered for scheduling in the recursive call)

      if (if_rule_p(instance->fibered_attr.attr))
      {
        int cmask = 1 << (if_rule_index(instance->fibered_attr.attr));
        cond.negative |= cmask;
        cto_node->cto_if_false = schedule_visits_group(aug_graph, cto_node, cond, instance_groups, remaining-1, parent_group);
        cond.negative &= ~cmask;
        cond.positive |= cmask;
        cto_node->cto_if_true = schedule_visits_group(aug_graph, cto_node, cond, instance_groups, remaining-1, parent_group);
        cond.positive &= ~cmask;
      }
      else
      {
        cto_node->cto_next = schedule_visits_group(aug_graph, cto_node, cond, instance_groups, remaining-1, parent_group);
      }

      aug_graph->schedule[i] = 0; // Release it

      return cto_node;
    }
  }

  // TODO: add more debugging information
  fflush(stdout);
  if (sane_remaining != remaining)
  {
    fprintf(stderr,"remaining out of sync %d != %d\n", sane_remaining, remaining);
  }

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
 */
static CTO_NODE* schedule_visits(AUG_GRAPH *aug_graph, CTO_NODE* prev, CONDITION cond, CHILD_PHASE* instance_groups, int remaining)
{
  int i;
  int n = aug_graph->instances.length;
  int sane_remaining = 0;
  CTO_NODE* cto_node = NULL;
  
  /* If nothing more to do, we are done. */
  if (remaining == 0) return NULL;

  /* Outer condition is impossible, its a dead-end branch */
  if (CONDITION_IS_IMPOSSIBLE(cond)) return NULL;

  for (i = 0; i < n; i++)
  {
    INSTANCE *instance = &aug_graph->instances.array[i];
    CHILD_PHASE *group_key = &instance_groups[i];

    // Already scheduled then ignore
    if (aug_graph->schedule[i] != 0) continue;

    sane_remaining++;

    // If edgeset condition is not impossible then go ahead with scheduling
    if (group_ready_to_go(aug_graph, cond, instance_groups, i))
    {
      cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
      cto_node->cto_prev = prev;
      cto_node->cto_instance = instance;
      cto_node->child_phase = *group_key;

      aug_graph->schedule[i] = 1; // instance has been scheduled (and will not be considered for scheduling in the recursive call)

      // If it is local then continue scheduling
      if (!group_key->ph && !group_key->ch)
      {
        if (if_rule_p(instance->fibered_attr.attr))
        {
          int cmask = 1 << (if_rule_index(instance->fibered_attr.attr));
          cond.negative |= cmask;
          cto_node->cto_if_false = schedule_visits(aug_graph, cto_node, cond, instance_groups, remaining-1);
          cond.negative &= ~cmask;
          cond.positive |= cmask;
          cto_node->cto_if_true = schedule_visits(aug_graph, cto_node, cond, instance_groups, remaining-1);
          cond.positive &= ~cmask;
        }
        else
        {
          cto_node->cto_next = schedule_visits(aug_graph, cto_node, cond, instance_groups, remaining-1);
        }

        aug_graph->schedule[i] = 0; // Release it

        return cto_node;
      }
      // Instance is not local then delegate it to group scheduler
      else
      {
        // If we find ourselves scheduling a <+ph,ch>, this means that somehow, we didn’t have any <-ph,ch>
        // for that same ph and ch -- apparently the phase has no inherited attributes! 0 and so we need
        // to *first* put in the child visit node, and *then* the syn attributes from this group.
        if (group_key->ph >= 0 && group_key->ch > -1)
        {
          // Visit marker
          CTO_NODE *cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
          cto_node->cto_prev = prev;
          cto_node->cto_instance = NULL;
          cto_node->child_phase.ph = group_key->ph + 1;
          cto_node->child_phase.ch = group_key->ch;
          cto_node->cto_next = schedule_visits_group(aug_graph, prev, cond, instance_groups, remaining /* no change */, group_key);
        }

        // If we find ourselves schedule a parent inherited attribute (that wasn’t handled in the case case),
        // this means that the previous visit ended without any synthesized attributes, so we need to stick in the visit end
        // (Visit(child = -1, ph = +(one less then the -ph we are on now).
        if (group_key->ph < 0 && group_key->ch == -1)
        {
          // Visit marker
          CTO_NODE *cto_node = (CTO_NODE*)HALLOC(sizeof(CTO_NODE));
          cto_node->cto_prev = prev;
          cto_node->cto_instance = NULL;
          cto_node->child_phase.ph = group_key->ph - 1;
          cto_node->child_phase.ch = -1;
          cto_node->cto_next = schedule_visits_group(aug_graph, prev, cond, instance_groups, remaining /* no change */, group_key);
        }

        return schedule_visits_group(aug_graph, prev, cond, instance_groups, remaining, group_key);
      }
    }
  }

  // TODO: add more debugging information
  fflush(stdout);
  if (sane_remaining != remaining)
  {
    fprintf(stderr,"remaining out of sync %d != %d\n", sane_remaining, remaining);
  }

  fatal_error("Cannot make conditional total order!");

  return NULL;
}

/** Return phase (synthesized) or -phase (inherited)
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
  int i;

  (void)close_augmented_dependency_graph(aug_graph);

  /** Now schedule graph: we need to generate a conditional total order. */

  if (oag_debug & PROD_ORDER) {
    printf("Scheduling conditional total order for %s\n",
	   aug_graph_name(aug_graph));
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

  if (oag_debug & DEBUG_ORDER)
  {
    printf("\nInstances:\n");
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
        PHY_GRAPH *npg = Declaration_info(in->node)->node_phy_graph;
        int ph = attribute_schedule(npg,&(in->fibered_attr));
        printf("<%d,%d>\n", group.ph, group.ch);
      }
    }
  }

  /* we use the schedule array as temp storage */
  for (i=0; i < n; ++i) {
    aug_graph->schedule[i] = 0; /* This means: not scheduled yet */
  }

  cond.positive = 0;
  cond.negative = 0;
  aug_graph->total_order = schedule_visits(aug_graph, NULL, cond, instance_groups, n);

  if (oag_debug & DEBUG_ORDER)
  {
    printf("\nSchedule\n");
    print_total_order(aug_graph->total_order, instance_groups, stdout);
  }

  printf("\n");
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



