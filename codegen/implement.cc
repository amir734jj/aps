#include <iostream>
extern "C" {
#include <stdio.h>
#include "aps-ag.h"
}
#include "dump.h"
#include "implement.h"

Implementation::ModuleInfo::ModuleInfo(Declaration module)
  : module_decl(module) 
{}

void Implementation::ModuleInfo::note_top_level_match(Declaration tlm,
						 GEN_OUTPUT&)
{
  top_level_matches.push_back(tlm);
}

void Implementation::ModuleInfo::note_var_value_decl(Declaration vd,
						GEN_OUTPUT&)
{
  var_value_decls.push_back(vd);
}

void Implementation::ModuleInfo::note_local_attribute(Declaration ld,
						 GEN_OUTPUT&)
{
  local_attributes.push_back(ld);
}

void Implementation::ModuleInfo::note_attribute_decl(Declaration ad,
						     GEN_OUTPUT&)
{
  attribute_decls.push_back(ad);
}

static void *clear_impl_marks(void *ignore, void *node) {
  if (ABSTRACT_APS_tnode_phylum(node) == KEYDeclaration) {
    Declaration_info((Declaration)node)->decl_flags &= ~IMPLEMENTATION_MARKS;
  }
  return ignore;
}

void clear_implementation_marks(Declaration d) {
  int nothing;
  traverse_Declaration(clear_impl_marks,&nothing,d);
}

bool sequence_search_pattern(Pattern p, Pattern *middle)
{
  Symbol sequence_symbol = intern_symbol("{}");
  if (Pattern_KEY(p) != KEYpattern_call) return false;

  Pattern pf = pattern_call_func(p);
  if (Pattern_KEY(pf) != KEYpattern_use) return false;
  Declaration pfdecl = USE_DECL(pattern_use_use(pf));
  if (!pfdecl || def_name(declaration_def(pfdecl)) != sequence_symbol) return false;

  Pattern leading = first_PatternActual(pattern_call_actuals(p));
  Pattern element = leading ? PAT_NEXT(leading) : 0;
  Pattern trailing = element ? PAT_NEXT(element) : 0;
  if (!leading || Pattern_KEY(leading) != KEYrest_pattern ||
      Pattern_KEY(rest_pattern_constraint(leading)) != KEYno_pattern ||
      !element || !trailing || Pattern_KEY(trailing) != KEYrest_pattern ||
      Pattern_KEY(rest_pattern_constraint(trailing)) != KEYno_pattern ||
      PAT_NEXT(trailing)) {
    return false;
  }

  *middle = element;
  return true;
}

bool sequence_search_matcher(Declaration decl, Match *match, Pattern *middle)
{
  Matches matchers;
  switch (Declaration_KEY(decl)) {
  case KEYcase_stmt:
    matchers = case_stmt_matchers(decl);
    break;
  case KEYfor_stmt:
    matchers = for_stmt_matchers(decl);
    break;
  default:
    return false;
  }
  Match first = first_Match(matchers);
  if (!first || MATCH_NEXT(first)) return false;
  if (!sequence_search_pattern(matcher_pat(first),middle)) return false;
  if (match) *match = first;
  return true;
}

bool block_assigns_to(Block b, void *vdecl)
{
  for (Declaration d = first_Declaration(block_body(b)); d; d = DECL_NEXT(d)) {
    switch (Declaration_KEY(d)) {
    case KEYassign:
      {
	Expression lhs = assign_lhs(d);
	if (Expression_KEY(lhs) == KEYvalue_use &&
	    USE_DECL(value_use_use(lhs)) == vdecl) return true;
	if (Expression_KEY(lhs) == KEYfuncall &&
	    USE_DECL(value_use_use(funcall_f(lhs))) == vdecl) return true;
      }
      break;
    case KEYblock_stmt:
      if (block_assigns_to(block_stmt_body(d),vdecl)) return true;
      break;
    case KEYif_stmt:
      if (block_assigns_to(if_stmt_if_true(d),vdecl) ||
	  block_assigns_to(if_stmt_if_false(d),vdecl)) return true;
      break;
    case KEYcase_stmt:
      for (Match m = first_Match(case_stmt_matchers(d)); m; m = MATCH_NEXT(m)) {
	if (block_assigns_to(matcher_body(m),vdecl)) return true;
      }
      if (block_assigns_to(case_stmt_default(d),vdecl)) return true;
      break;
    case KEYfor_stmt:
      for (Match m = first_Match(for_stmt_matchers(d)); m; m = MATCH_NEXT(m)) {
	if (block_assigns_to(matcher_body(m),vdecl)) return true;
      }
      break;
    case KEYfor_in_stmt:
      if (block_assigns_to(for_in_stmt_body(d),vdecl)) return true;
      break;
    default:
      break;
    }
  }
  return false;
}
