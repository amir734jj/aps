#include <stdio.h>
#include <jbb.h>

#include "aps-ag.h"

/*
Several phases:
  1> fibering
  2> constructing production dependency graphs
  3> iterating to DNC solution
  4> fiber cycle detection and removal
  5> OAG construction and test.
  6> schedule creation.
  7> diagnostic output
*/

bool is_there(int d, int thing) {
  return ((d & thing) == thing);
}

static void *analyze_thing(void *ignore, void *node)
{
  STATE *s;
  DEPENDENCY d;
  if (ABSTRACT_APS_tnode_phylum(node) == KEYDeclaration) {
    Declaration decl = (Declaration)node;
    switch (Declaration_KEY(decl)) {
    case KEYmodule_decl:
      s = compute_dnc(decl);
      d = analysis_state_cycle(s);

      printf("=>%d\n", d);

      if (is_there(d, SOME_DEPENDENCY)) {
        printf("SOME_DEPENDENCY\n");
      }
      if (is_there(d, DEPENDENCY_NOT_JUST_FIBER)) {
        printf("DEPENDENCY_NOT_JUST_FIBER\n");
      }
      if (d & DEPENDENCY_MAYBE_CARRYING) {
        printf("DEPENDENCY_MAYBE_CARRYING\n");
      }
      if (is_there(d, DEPENDENCY_MAYBE_DIRECT)) {
        printf("DEPENDENCY_MAYBE_DIRECT\n");
      }
      if (is_there(d, DEPENDENCY_MAYBE_SIMPLE)) {
        printf("DEPENDENCY_MAYBE_SIMPLE\n");
      }

      if (is_there(d, fiber_dependency)) {
        printf("fiber_dependency\n");
      }

      if (is_there(d, control_fiber_dependency)) {
        printf("control_fiber_dependency\n");
      }
      if (is_there(d, control_dependency)) {
        printf("control_dependency\n");
      }
      if (is_there(d, indirect_fiber_dependency)) {
        printf("indirect_fiber_dependency\n");
      }
      if (is_there(d, indirect_dependency)) {
        printf("indirect_dependency\n");
      }
      if (is_there(d, indirect_control_fiber_dependency)) {
        printf("indirect_control_fiber_dependency\n");
      }
      if (is_there(d, indirect_control_dependency)) {
        printf("indirect_control_dependency\n");
      }
      if (is_there(d, indirect_circular_dependency)) {
        printf("indirect_circular_dependency\n");
      }

      switch (d) {
      default:
	aps_error(decl,"Cycle detected; Attribute grammar is not DNC %d", d);
	break;
      case indirect_dependency:   // break 
      case indirect_circular_dependency:
        break_fiber_cycles(decl,s, indirect_circular_dependency);
        compute_oag(decl,s);
        break;
      case indirect_control_fiber_dependency:
      case control_fiber_dependency:
      case indirect_fiber_dependency:
      case fiber_dependency:
	printf("Fiber cycle detected; cycle being removed\n");
	break_fiber_cycles(decl,s, fiber_dependency);
	/* fall through */
      case no_dependency:
	compute_oag(decl,s);
	d = analysis_state_cycle(s);
	switch (d) {
	case no_dependency:
	  break;
	default:
	  aps_error(decl,"Cycle detected; Attribute grammar is not OAG %d", d);
	  break;
	}
	break;
      }
      if (cycle_debug & PRINT_CYCLE) {
      print_cycles(s,stdout);
      }
      Declaration_info(decl)->analysis_state = s;
      break;
    }
    return NULL;
  }
  return ignore;
}

void analyze_Program(Program p)
{
  char *saved_filename = aps_yyfilename;
  printf("saved_filename: %s\n", saved_filename);
  aps_yyfilename = (char *)program_name(p);
  traverse_Program(analyze_thing,p,p);
  aps_yyfilename = saved_filename;
}
