#include <iostream>
#include <sstream>
#include <stack>
#include <vector>
extern "C" {
#include <stdio.h>
#include "aps-ag.h"
}
#include "dump-cpp.h"
#include "implement.h"

using namespace std;

#define LOCAL_ATTRIBUTE_FLAG (1<<24)

struct ContextRecordNode {
  Declaration context;
  void *extra; /* branch in context (if any) */
  ContextRecordNode* outer;
  ContextRecordNode(Declaration d, void* e, ContextRecordNode* o)
    : context(d), extra(e), outer(o) {}
};

typedef void (*ASSIGNFUNC)(void *,Declaration,ostream&);
void dump_Block(Block,ASSIGNFUNC,void*arg,ostream&);

static const int MAXDEPTH = 200;

static void *attr_context[MAXDEPTH];
static int attr_context_depth = 0;   /* current depth of attribute assigns */
static int attr_context_started = 0; /* depth of last activation */

static void push_attr_context(void *node)
{
  if (attr_context_depth >= MAXDEPTH) {
    aps_error(node,"nested too deep");
  } else {
    attr_context[attr_context_depth++] = node;
  }
}

string matcher_bindings(string node, Match m)
{
  Pattern p = matcher_pat(m);
  ostringstream os1, os2;
  dump_Pattern_cond(p,node,os1);
  dump_Pattern_bindings(p,os2);
  // ignore os1 contents
  return os2.str();
}

static void dump_context_open(void *c, ostream& os) {
  switch (ABSTRACT_APS_tnode_phylum(c)) {
  case KEYDeclaration:
    {
      Declaration decl = (Declaration)c;
      switch (Declaration_KEY(decl)) {
      case KEYif_stmt:
	os << indent() << "{ bool cond = ";
	++nesting_level;
	dump_Expression(if_stmt_cond(decl),os);
	os << ";\n";
	return;
      case KEYcase_stmt:
	{
	  Type ty = infer_expr_type(case_stmt_expr(decl));
	  os << indent() << "{ ";
	  ++nesting_level;
	  dump_Type(ty,os);
	  os << " node = ";
	  dump_Expression(case_stmt_expr(decl),os);
	  os << ";\n";
	  os << indent() << "Constructor* cons = node->cons;\n";
	}
	return;
      case KEYfor_stmt:
	{
	  //!! Doesn't work.
	  Type ty = infer_expr_type(for_stmt_expr(decl));
	  os << indent() << "{ ";
	  ++nesting_level;
	  dump_Type(ty,os);
	  os << " node = ";
	  dump_Expression(for_stmt_expr(decl),os);
	  os << ";\n";
	  os << indent() << "Constructor* cons = node->cons;\n";
	}
	return;
      case KEYfor_in_stmt:
	{
	  Declaration f = for_in_stmt_formal(decl);
	  Type ty = infer_formal_type(f);
	  os << indent() << "for (CollectionIterator<";
	  dump_Type(ty,os);
	  os << "> ci = CollectionIterator<";
	  dump_Type(ty,os);
	  os << ">(";
	  dump_Expression(for_in_stmt_seq(decl),os);
	  os << "); ci.has_item(); ci.advance()) {";
	  ++nesting_level;
	  os << indent() << ty
	     << " v_" << decl_name(f) << " = ci.item();\n";
	}
	return;
      case KEYtop_level_match:
	{
	  Type ty = infer_pattern_type(matcher_pat(top_level_match_m(decl)));
	  os << indent() << "for (int i=";
	  dump_Type_value(ty,os);
	  os << "->size(); i >= 0; --i) {\n";
	  ++nesting_level;
	  os << indent() << ty << " node = " << as_val(ty) << "->node(i);\n";
	  os << indent() << "Constructor* cons = node->cons;\n";
	}
	return;
      default:
	break;
      }
    }
    break;
  case KEYBlock:
    {
      Block b = (Block)c;
      // only for if_stmt for now
      Declaration parent = (Declaration)tnode_parent(b);
      if (b == if_stmt_if_true(parent)) {
	os << indent() << "if (cond) {\n";
      } else {
	os << indent() << "if (!cond) {\n";
      }
      ++nesting_level;
      return;
    }
  case KEYMatch:
    {
      Match m = (Match)c;
      Pattern p = matcher_pat(m);
      os << indent() << "if (";
      dump_Pattern_cond(p,"node",os);
      os << ") {\n";
      nesting_level+=1;
      dump_Pattern_bindings(p,os);
      return;
    }
  default:
    break;
  }
  aps_error(c,"unknown context");
  os << indent() << "UNKNOWN {\n";
}

static void activate_attr_context(ostream& os)
{
  while (attr_context_started < attr_context_depth) {
    dump_context_open(attr_context[attr_context_started],os);
    ++attr_context_started;
  }
}

static void pop_attr_context(ostream& os)
{
  --attr_context_depth;
  while (attr_context_started > attr_context_depth) {
    --attr_context_started;
    --nesting_level;
    os << indent() << "}\n";
  }
}

static void dump_attr_assign(void *vdecl, Declaration ass, ostream& os)
{
  Declaration decl = (Declaration)vdecl;
  Expression lhs = assign_lhs(ass);
  Expression rhs = assign_rhs(ass);
  Direction dir;
  Default def;
  Type ty = infer_expr_type(lhs);
  switch (Expression_KEY(lhs)) {
  case KEYvalue_use:
    if (USE_DECL(value_use_use(lhs)) != decl) return;
    dir = value_decl_direction(decl);
    def = value_decl_default(decl);
    activate_attr_context(os);
    os << indent();
    break;
  case KEYfuncall:
    if (USE_DECL(value_use_use(funcall_f(lhs))) != decl) return;
    activate_attr_context(os);
    dir = attribute_decl_direction(decl);
    def = attribute_decl_default(decl);
    os << indent() << "if (anode == ";
    dump_Expression(first_Actual(funcall_actuals(lhs)),os);
    os << ") ";
    break;
  default:
    return;
  }
  if (direction_is_collection(dir)) {
    os << "collection = ";
    switch (Default_KEY(def)) {
    case KEYno_default:
    case KEYsimple:
      dump_Type_value(ty,os);
      os << "->v_combine";
      break;
    case KEYcomposite:
      dump_Expression(composite_combiner(def),os);
      break;
    }
    os << "(collection,";
    dump_Expression(rhs,os);
    os << ");\n";
  } else {
    os << "return ";
    dump_Expression(rhs,os);
    os << ";\n";
  }
}

bool depends_on(void *vdecl, Declaration local, Block b)
{
  //! need to check if this is needed
  return true;
}

void dump_local_decl(void *, Declaration local, ostream& o)
{
  activate_attr_context(o);
  o << indent();
  dump_Typed_decl(value_decl_type(local),local,"v_",o);
  o << " = ";
  Default init = value_decl_default(local);
  switch (Default_KEY(init)) {
  case KEYsimple:
    dump_Expression(simple_value(init),o);
    break;
  default:
    aps_error(local,"Can only handle initialized locals");
    o << "0";
  }
  o << ";\n";
}


void dump_Matches(Matches ms, bool exclusive, ASSIGNFUNC f, void*arg, ostream&os)
{
  FOR_SEQUENCE
    (Match,m,Matches,ms,
     push_attr_context(m);
     dump_Block(matcher_body(m),f,arg,os);
     bool need_else = attr_context_started >= attr_context_depth;
     pop_attr_context(os);
     if (exclusive && need_else) os << indent() << "else\n";
     );
}

void dump_Block(Block b,ASSIGNFUNC f,void*arg,ostream&os)
{
  FOR_SEQUENCE
    (Declaration,d,Declarations,block_body(b),
     switch (Declaration_KEY(d)) {
     case KEYassign:
       (*f)(arg,d,os);
       break;
     case KEYif_stmt:
       push_attr_context(d);
       { Block true_block = if_stmt_if_true(d);
         Block false_block = if_stmt_if_false(d);
	 push_attr_context(true_block);
	 dump_Block(true_block,f,arg,os);
	 pop_attr_context(os);
	 push_attr_context(false_block);
	 dump_Block(false_block,f,arg,os);
	 pop_attr_context(os);
       }
       pop_attr_context(os);
       break;
     case KEYcase_stmt:
       push_attr_context(d);
       //!! we implement case and for!!
       dump_Matches(case_stmt_matchers(d),true,f,arg,os);
       os << indent() << "{\n"; // because of "else"
       dump_Block(case_stmt_default(d),f,arg,os);
       os << indent() << "}\n";
       pop_attr_context(os);
       break;
     case KEYfor_stmt:
       push_attr_context(d);
       dump_Matches(for_stmt_matchers(d),false,f,arg,os);
       pop_attr_context(os);
       break;
     case KEYvalue_decl:
       if (!(Declaration_info(d)->decl_flags & LOCAL_ATTRIBUTE_FLAG) &&
	   depends_on(arg,d,b)) {
	 dump_local_decl(arg,d,os);
       }
       break;
     default:
       aps_error(d,"cannot handle this kind of statement");
       os << "0";
       break;
     });
}

void dump_default_return(Default deft, Direction dir, string ns, ostream& os)
{
  if (direction_is_collection(dir)) {
    os << indent() << "return collection;\n";
  } else switch (Default_KEY(deft)) {
  default:
    os << indent() << "throw UndefinedAttributeException(" << ns << ");\n";
    break;
  case KEYsimple:
    os << indent() << "return " << simple_value(deft) << ";\n";
    break;
  }
}

Block local_attribute_block(Declaration d)
{
  void *p = d;
  while ((p = tnode_parent(p)) != 0 &&
	 ABSTRACT_APS_tnode_phylum(p) != KEYBlock)
    ;
  return (Block)p;
}

string local_attribute_context_bindings(Declaration d)
{
  string bindings = "";
  void *p = d;
  while ((p = tnode_parent(p)) != 0) {
    switch (ABSTRACT_APS_tnode_phylum(p)) {
    default:
      break;
    case KEYDeclaration:
      if (Declaration_KEY((Declaration)p) == KEYtop_level_match)
	return bindings;
      break;
    case KEYMatch:
      {
	Match m = (Match)p;
	Declaration header = Match_info(m)->header;
	ostringstream hs;
	switch (Declaration_KEY(header)) {
	case KEYtop_level_match:
	  hs << "anchor";
	  break;
	case KEYcase_stmt:
	  hs << case_stmt_expr(header);
	  break;
	default:
	  aps_error(header,"Cannot handle this header for Match");
	  break;
	}
	bindings = matcher_bindings(hs.str(),m) + bindings;
      }
      break;
    }
  }
  aps_error(d,"internal error: reached null parent!");
  return bindings;
}

void implement_local_attributes(vector<Declaration>& local_attributes,
				const output_streams& oss)
{
  ostream& hs = oss.hs;
  ostream& cpps = oss.cpps;
  // ostream& is = oss.is;
  ostream& bs = inline_definitions ? hs : cpps;
  string prefix = oss.prefix;

  int n = local_attributes.size();
  for (int j=0; j <n; ++j) {
    Declaration d = local_attributes[j];
    Block b = local_attribute_block(d);
    int i = LOCAL_UNIQUE_PREFIX(d);
    char *name = decl_name(d);
    hs << indent() << value_decl_type(d)
       << " c" << i << "_" << name << "(C_PHYLUM::Node* anchor)";
    INDEFINITION;
    if (!inline_definitions) {
      hs << ";\n";
      dump_Type_prefixed(value_decl_type(d),cpps);
      cpps << " " << prefix << "c" << i << "_" << name 
	   << "(C_PHYLUM::Node* anchor)";
    }
    bs << " {\n";
    ++nesting_level;
    bs << local_attribute_context_bindings(d);
    bs << "\n"; // blank line
    dump_Block(b,dump_attr_assign,d,bs);
    dump_default_return(value_decl_default(d),value_decl_direction(d),
			string("\"local ")+name+"\"",bs);
    --nesting_level;
    bs << indent() << "}\n";
  }
}

void implement_attributes(const vector<Declaration>& attrs,
			  const vector<Declaration>& tlms,
			  const output_streams& oss)
{
  ostream& hs = oss.hs;
  ostream& cpps = oss.cpps;
  // ostream& is = oss.is;
  ostream& bs = inline_definitions ? hs : cpps;
  string prefix = oss.prefix;

  int n = attrs.size();
  for (int i=0; i <n; ++i) {
    Declaration ad = attrs[i];
    char *name = decl_name(ad);
    Declarations afs = function_type_formals(attribute_decl_type(ad));
    Declaration af = first_Declaration(afs);
    Type at = formal_type(af);
    // Declaration pd = USE_DECL(type_use_use(at));
    Declarations rdecls = function_type_return_values(attribute_decl_type(ad));
    Type rt = value_decl_type(first_Declaration(rdecls));
    bool inh = (ATTR_DECL_IS_INH(ad) != 0);
    
    hs << "  "; dump_Type(rt,hs); hs << " c_" << name << "(";
    dump_Type(at,hs);
    hs << " anode)";
    //cout << "Before INDEF, ns = " << nesting_level << endl;
    INDEFINITION;
    //cout << "After INDEF, ns = " << nesting_level << endl;
    if (!inline_definitions) {
      hs << ";\n";
      dump_Type(rt,cpps);
      cpps << " " << prefix << "c_" << name << "(";
      dump_Type(at,cpps);
      cpps << " anode)";
    }
    bs << " {\n";  
    ++nesting_level;
    if (inh) {
      bs << indent() << "C_PHYLUM::Node* node=anode->parent;\n";
      bs << indent() << "if (node != 0) {\n";
      ++nesting_level;
    } else {
      bs << indent() << "C_PHYLUM::Node* node = anode;\n";
    }
    bs << indent() << "C_PHYLUM::Node* anchor = node;\n";
    bs << indent() << "Constructor* cons = node->cons;\n";
    for (vector<Declaration>::const_iterator i = tlms.begin();
	 i != tlms.end(); ++i) {
      Match m = top_level_match_m(*i);
      push_attr_context(m);
      Block body = matcher_body(m);
      dump_Block(body,dump_attr_assign,ad,bs);
      pop_attr_context(bs);
    }
    if (inh) {
      --nesting_level;
      bs << indent() << "}\n";
    }
    dump_default_return(attribute_decl_default(ad),
			attribute_decl_direction(ad),
			string("anode->to_string()+\".") + name + "\"", bs);
    --nesting_level;
    bs << indent() << "}\n";
  }
}

class Dynamic : public Implementation
{
public:
  typedef Implementation::ModuleInfo Super;
  class ModuleInfo : public Super {
  public:
    ModuleInfo(Declaration mdecl) : Implementation::ModuleInfo(mdecl) {}

    void note_top_level_match(Declaration tlm, const output_streams& oss) {
      Super::note_top_level_match(tlm,oss);
    }

    void note_local_attribute(Declaration ld, const output_streams& oss) {
      Super::note_local_attribute(ld,oss);
      Declaration_info(ld)->decl_flags |= LOCAL_ATTRIBUTE_FLAG;
    }

    void note_var_value_decl(Declaration vd, const output_streams& oss) {
      Super::note_var_value_decl(vd,oss);
    }

    void implement(const output_streams& oss) {
      implement_local_attributes(local_attributes,oss);
      implement_attributes(attribute_decls,top_level_matches,oss);

      ostream& hs = oss.hs;
      ostream& cpps = oss.cpps;
      ostream& bs = inline_definitions ? hs : cpps;
      char *name = decl_name(module_decl);

      Declarations ds = block_body(module_decl_contents(module_decl));
      
      // Implement finish routine:
      hs << "  void finish()";
      if (!inline_definitions) {
	hs << ";\n";
	cpps << "void C_" << name << "::finish()";
      }
      bs << " {";
      for (Declaration d = first_Declaration(ds); d; d = DECL_NEXT(d)) {
	char* kind = NULL;
	switch(Declaration_KEY(d)) {
	case KEYphylum_decl:
	case KEYtype_decl:
	  kind = "t_";
	  break;
	case KEYattribute_decl:
	  kind = "a_";
	  break;
	default:
	  break;
	}
	if (kind != NULL) {
	  char *n = decl_name(d);
	  bs << "\n  " << kind << n << "->finish(); ";
	}
      }
      bs << " }\n\n";
    }
  };

  Super* get_module_info(Declaration m) {
    return new ModuleInfo(m);
  }

  void implement_function_body(Declaration f, ostream& os) {
    // os << indent() << "// Indent = " << nesting_level*2 << endl;
    Type fty = function_decl_type(f);
    Declaration rdecl = first_Declaration(function_type_return_values(fty));
    Block b = function_decl_body(f);
    dump_Block(b,dump_attr_assign,rdecl,os);
    os << indent()
       << "throw UndefinedAttributeException(\"" << decl_name(f) << "\");\n";
  }

  void implement_attr_call(Declaration, Expression, ostream&) {
    // not called
  }

  void implement_value_use(Declaration vd, ostream& os) {
    if (Declaration_info(vd)->decl_flags & LOCAL_ATTRIBUTE_FLAG) {
      os << "a" << LOCAL_UNIQUE_PREFIX(vd) << "_"
	 << decl_name(vd) << "->evaluate(anchor)"; 
    } else {
      aps_error(vd,"internal_error: What is special about this?");
    }
  }
};

Implementation *dynamic_impl = new Dynamic();
