#ifndef APS_TREE_H
#define APS_TREE_H

/* Generated by a program written by John Boyland */
#include "jbb-tree.h"
#include "aps-tree.handcode.h"

/* Automatically generated file */

/* Typedefs for the phyla of the language: ABSTRACT_APS */
typedef struct Signature__struct *Signature;
typedef struct Type__struct *Type;
typedef struct Expression__struct *Expression;
typedef struct Pattern__struct *Pattern;
typedef struct Module__struct *Module;
typedef struct Class__struct *Class;
typedef struct Def__struct *Def;
typedef struct Use__struct *Use;
typedef struct Program__struct *Program;
typedef struct Unit__struct *Unit;
typedef struct Declaration__struct *Declaration;
typedef struct Block__struct *Block;
typedef struct Match__struct *Match;
typedef struct Direction__struct *Direction;
typedef struct Default__struct *Default;
typedef struct Units__struct *Units;
typedef struct Declarations__struct *Declarations;
typedef struct Matches__struct *Matches;
typedef struct Types__struct *Types;
typedef struct Expressions__struct *Expressions;
typedef struct Patterns__struct *Patterns;
typedef struct Actuals__struct *Actuals;
typedef struct TypeActuals__struct *TypeActuals;
typedef struct PatternActuals__struct *PatternActuals;

/* the phylum key */

enum KEYTYPE_ABSTRACT_APS_Phylum {
  KEYSignature,
  KEYType,
  KEYExpression,
  KEYPattern,
  KEYModule,
  KEYClass,
  KEYDef,
  KEYUse,
  KEYProgram,
  KEYUnit,
  KEYDeclaration,
  KEYBlock,
  KEYMatch,
  KEYDirection,
  KEYDefault,
  KEYUnits,
  KEYDeclarations,
  KEYMatches,
  KEYTypes,
  KEYExpressions,
  KEYPatterns,
  KEYActuals,
  KEYTypeActuals,
  KEYPatternActuals,
  KEY_ABSTRACT_APS_None
};
extern enum KEYTYPE_ABSTRACT_APS_Phylum ABSTRACT_APS_tnode_phylum(void *);

/* Phyla, constructors and accessors */

enum KEYTYPE_Signature {
  KEYsig_use,
  KEYsig_inst,
  KEYno_sig,
  KEYmult_sig,
  KEYfixed_sig
};
extern enum KEYTYPE_Signature Signature_KEY(Signature);
extern Signature copy_Signature(Signature);
extern void assert_Signature(Signature);

enum KEYTYPE_Type {
  KEYtype_use,
  KEYtype_inst,
  KEYno_type,
  KEYremote_type,
  KEYprivate_type,
  KEYfunction_type
};
extern enum KEYTYPE_Type Type_KEY(Type);
extern Type copy_Type(Type);
extern void assert_Type(Type);

enum KEYTYPE_Expression {
  KEYvalue_use,
  KEYtyped_value,
  KEYinteger_const,
  KEYreal_const,
  KEYstring_const,
  KEYchar_const,
  KEYundefined,
  KEYno_expr,
  KEYfuncall,
  KEYappend,
  KEYempty,
  KEYclass_value,
  KEYmodule_value,
  KEYsignature_value,
  KEYtype_value,
  KEYpattern_value,
  KEYrepeat,
  KEYcontrolled,
  KEYguarded
};
extern enum KEYTYPE_Expression Expression_KEY(Expression);
extern Expression copy_Expression(Expression);
extern void assert_Expression(Expression);

enum KEYTYPE_Pattern {
  KEYpattern_use,
  KEYno_pattern,
  KEYtyped_pattern,
  KEYmatch_pattern,
  KEYpattern_call,
  KEYpattern_actual,
  KEYrest_pattern,
  KEYchoice_pattern,
  KEYand_pattern,
  KEYpattern_var,
  KEYcondition,
  KEYpattern_function,
  KEYhole
};
extern enum KEYTYPE_Pattern Pattern_KEY(Pattern);
extern Pattern copy_Pattern(Pattern);
extern void assert_Pattern(Pattern);

enum KEYTYPE_Module {
  KEYmodule_use
};
extern enum KEYTYPE_Module Module_KEY(Module);
extern Module copy_Module(Module);
extern void assert_Module(Module);

enum KEYTYPE_Class {
  KEYclass_use
};
extern enum KEYTYPE_Class Class_KEY(Class);
extern Class copy_Class(Class);
extern void assert_Class(Class);

enum KEYTYPE_Def {
  KEYdef
};
extern enum KEYTYPE_Def Def_KEY(Def);
extern Def copy_Def(Def);
extern void assert_Def(Def);

enum KEYTYPE_Use {
  KEYqual_use,
  KEYuse
};
extern enum KEYTYPE_Use Use_KEY(Use);
extern Use copy_Use(Use);
extern void assert_Use(Use);

enum KEYTYPE_Program {
  KEYprogram
};
extern enum KEYTYPE_Program Program_KEY(Program);
extern Program copy_Program(Program);
extern void assert_Program(Program);

enum KEYTYPE_Unit {
  KEYno_unit,
  KEYdecl_unit,
  KEYwith_unit
};
extern enum KEYTYPE_Unit Unit_KEY(Unit);
extern Unit copy_Unit(Unit);
extern void assert_Unit(Unit);

enum KEYTYPE_Declaration {
  KEYno_decl,
  KEYclass_decl,
  KEYmodule_decl,
  KEYsignature_decl,
  KEYphylum_decl,
  KEYtype_decl,
  KEYvalue_decl,
  KEYattribute_decl,
  KEYfunction_decl,
  KEYprocedure_decl,
  KEYconstructor_decl,
  KEYpattern_decl,
  KEYinheritance,
  KEYpolymorphic,
  KEYpragma_call,
  KEYtop_level_match,
  KEYclass_replacement,
  KEYmodule_replacement,
  KEYsignature_replacement,
  KEYtype_replacement,
  KEYvalue_replacement,
  KEYpattern_replacement,
  KEYclass_renaming,
  KEYmodule_renaming,
  KEYsignature_renaming,
  KEYtype_renaming,
  KEYvalue_renaming,
  KEYpattern_renaming,
  KEYnormal_formal,
  KEYseq_formal,
  KEYtype_formal,
  KEYphylum_formal,
  KEYblock_stmt,
  KEYeffect,
  KEYmulti_call,
  KEYnormal_assign,
  KEYcollect_assign,
  KEYif_stmt,
  KEYfor_in_stmt,
  KEYcase_stmt,
  KEYfor_stmt
};
extern enum KEYTYPE_Declaration Declaration_KEY(Declaration);
extern Declaration copy_Declaration(Declaration);
extern void assert_Declaration(Declaration);

enum KEYTYPE_Block {
  KEYblock
};
extern enum KEYTYPE_Block Block_KEY(Block);
extern Block copy_Block(Block);
extern void assert_Block(Block);

enum KEYTYPE_Match {
  KEYmatcher
};
extern enum KEYTYPE_Match Match_KEY(Match);
extern Match copy_Match(Match);
extern void assert_Match(Match);

enum KEYTYPE_Direction {
  KEYdirection
};
extern enum KEYTYPE_Direction Direction_KEY(Direction);
extern Direction copy_Direction(Direction);
extern void assert_Direction(Direction);

enum KEYTYPE_Default {
  KEYsimple,
  KEYno_default,
  KEYcomposite
};
extern enum KEYTYPE_Default Default_KEY(Default);
extern Default copy_Default(Default);
extern void assert_Default(Default);

enum KEYTYPE_Units {
  KEYnil_Units,
  KEYlist_Units,
  KEYappend_Units
};
extern enum KEYTYPE_Units Units_KEY(Units);
extern Units copy_Units(Units);
extern void assert_Units(Units);

extern Units nil_Units();

extern Units list_Units(Unit);
extern Unit list_Units_elem(Units);

extern Units append_Units(Units,Units);
extern Units append_Units_l1(Units);
extern Units append_Units_l2(Units);

#define xcons_Units(l,x) append_Units(l,list_Units(x))
#define cons_Units(x,l) append_Units(list_Units(x),l)

enum KEYTYPE_Declarations {
  KEYnil_Declarations,
  KEYlist_Declarations,
  KEYappend_Declarations
};
extern enum KEYTYPE_Declarations Declarations_KEY(Declarations);
extern Declarations copy_Declarations(Declarations);
extern void assert_Declarations(Declarations);

extern Declarations nil_Declarations();

extern Declarations list_Declarations(Declaration);
extern Declaration list_Declarations_elem(Declarations);

extern Declarations append_Declarations(Declarations,Declarations);
extern Declarations append_Declarations_l1(Declarations);
extern Declarations append_Declarations_l2(Declarations);

#define xcons_Declarations(l,x) append_Declarations(l,list_Declarations(x))
#define cons_Declarations(x,l) append_Declarations(list_Declarations(x),l)

enum KEYTYPE_Matches {
  KEYnil_Matches,
  KEYlist_Matches,
  KEYappend_Matches
};
extern enum KEYTYPE_Matches Matches_KEY(Matches);
extern Matches copy_Matches(Matches);
extern void assert_Matches(Matches);

extern Matches nil_Matches();

extern Matches list_Matches(Match);
extern Match list_Matches_elem(Matches);

extern Matches append_Matches(Matches,Matches);
extern Matches append_Matches_l1(Matches);
extern Matches append_Matches_l2(Matches);

#define xcons_Matches(l,x) append_Matches(l,list_Matches(x))
#define cons_Matches(x,l) append_Matches(list_Matches(x),l)

enum KEYTYPE_Types {
  KEYnil_Types,
  KEYlist_Types,
  KEYappend_Types
};
extern enum KEYTYPE_Types Types_KEY(Types);
extern Types copy_Types(Types);
extern void assert_Types(Types);

extern Types nil_Types();

extern Types list_Types(Type);
extern Type list_Types_elem(Types);

extern Types append_Types(Types,Types);
extern Types append_Types_l1(Types);
extern Types append_Types_l2(Types);

#define xcons_Types(l,x) append_Types(l,list_Types(x))
#define cons_Types(x,l) append_Types(list_Types(x),l)

enum KEYTYPE_Expressions {
  KEYnil_Expressions,
  KEYlist_Expressions,
  KEYappend_Expressions
};
extern enum KEYTYPE_Expressions Expressions_KEY(Expressions);
extern Expressions copy_Expressions(Expressions);
extern void assert_Expressions(Expressions);

extern Expressions nil_Expressions();

extern Expressions list_Expressions(Expression);
extern Expression list_Expressions_elem(Expressions);

extern Expressions append_Expressions(Expressions,Expressions);
extern Expressions append_Expressions_l1(Expressions);
extern Expressions append_Expressions_l2(Expressions);

#define xcons_Expressions(l,x) append_Expressions(l,list_Expressions(x))
#define cons_Expressions(x,l) append_Expressions(list_Expressions(x),l)

enum KEYTYPE_Patterns {
  KEYnil_Patterns,
  KEYlist_Patterns,
  KEYappend_Patterns
};
extern enum KEYTYPE_Patterns Patterns_KEY(Patterns);
extern Patterns copy_Patterns(Patterns);
extern void assert_Patterns(Patterns);

extern Patterns nil_Patterns();

extern Patterns list_Patterns(Pattern);
extern Pattern list_Patterns_elem(Patterns);

extern Patterns append_Patterns(Patterns,Patterns);
extern Patterns append_Patterns_l1(Patterns);
extern Patterns append_Patterns_l2(Patterns);

#define xcons_Patterns(l,x) append_Patterns(l,list_Patterns(x))
#define cons_Patterns(x,l) append_Patterns(list_Patterns(x),l)

enum KEYTYPE_Actuals {
  KEYnil_Actuals,
  KEYlist_Actuals,
  KEYappend_Actuals
};
extern enum KEYTYPE_Actuals Actuals_KEY(Actuals);
extern Actuals copy_Actuals(Actuals);
extern void assert_Actuals(Actuals);

extern Actuals nil_Actuals();

extern Actuals list_Actuals(Expression);
extern Expression list_Actuals_elem(Actuals);

extern Actuals append_Actuals(Actuals,Actuals);
extern Actuals append_Actuals_l1(Actuals);
extern Actuals append_Actuals_l2(Actuals);

#define xcons_Actuals(l,x) append_Actuals(l,list_Actuals(x))
#define cons_Actuals(x,l) append_Actuals(list_Actuals(x),l)

enum KEYTYPE_TypeActuals {
  KEYnil_TypeActuals,
  KEYlist_TypeActuals,
  KEYappend_TypeActuals
};
extern enum KEYTYPE_TypeActuals TypeActuals_KEY(TypeActuals);
extern TypeActuals copy_TypeActuals(TypeActuals);
extern void assert_TypeActuals(TypeActuals);

extern TypeActuals nil_TypeActuals();

extern TypeActuals list_TypeActuals(Type);
extern Type list_TypeActuals_elem(TypeActuals);

extern TypeActuals append_TypeActuals(TypeActuals,TypeActuals);
extern TypeActuals append_TypeActuals_l1(TypeActuals);
extern TypeActuals append_TypeActuals_l2(TypeActuals);

#define xcons_TypeActuals(l,x) append_TypeActuals(l,list_TypeActuals(x))
#define cons_TypeActuals(x,l) append_TypeActuals(list_TypeActuals(x),l)

enum KEYTYPE_PatternActuals {
  KEYnil_PatternActuals,
  KEYlist_PatternActuals,
  KEYappend_PatternActuals
};
extern enum KEYTYPE_PatternActuals PatternActuals_KEY(PatternActuals);
extern PatternActuals copy_PatternActuals(PatternActuals);
extern void assert_PatternActuals(PatternActuals);

extern PatternActuals nil_PatternActuals();

extern PatternActuals list_PatternActuals(Pattern);
extern Pattern list_PatternActuals_elem(PatternActuals);

extern PatternActuals append_PatternActuals(PatternActuals,PatternActuals);
extern PatternActuals append_PatternActuals_l1(PatternActuals);
extern PatternActuals append_PatternActuals_l2(PatternActuals);

#define xcons_PatternActuals(l,x) append_PatternActuals(l,list_PatternActuals(x))
#define cons_PatternActuals(x,l) append_PatternActuals(list_PatternActuals(x),l)

extern Program program(String,Units);
extern String program_name(Program);
extern Units program_units(Program);

extern Unit no_unit();

extern Unit with_unit(String);
extern String with_unit_name(Unit);

extern Unit decl_unit(Declaration);
extern Declaration decl_unit_decl(Unit);

extern Declaration no_decl();

extern Block block(Declarations);
extern Declarations block_body(Block);

extern Declaration class_decl(Def,Declarations,Declaration,Signature,Block);
extern Def class_decl_def(Declaration);
extern Declarations class_decl_type_formals(Declaration);
extern Declaration class_decl_result_type(Declaration);
extern Signature class_decl_parent(Declaration);
extern Block class_decl_contents(Declaration);

extern Declaration module_decl(Def,Declarations,Declarations,Declaration,Signature,Block);
extern Def module_decl_def(Declaration);
extern Declarations module_decl_type_formals(Declaration);
extern Declarations module_decl_value_formals(Declaration);
extern Declaration module_decl_result_type(Declaration);
extern Signature module_decl_parent(Declaration);
extern Block module_decl_contents(Declaration);

extern Declaration signature_decl(Def,Signature);
extern Def signature_decl_def(Declaration);
extern Signature signature_decl_sig(Declaration);

extern Declaration phylum_decl(Def,Signature,Type);
extern Def phylum_decl_def(Declaration);
extern Signature phylum_decl_sig(Declaration);
extern Type phylum_decl_type(Declaration);

extern Declaration type_decl(Def,Signature,Type);
extern Def type_decl_def(Declaration);
extern Signature type_decl_sig(Declaration);
extern Type type_decl_type(Declaration);

extern Declaration value_decl(Def,Type,Direction,Default);
extern Def value_decl_def(Declaration);
extern Type value_decl_type(Declaration);
extern Direction value_decl_direction(Declaration);
extern Default value_decl_default(Declaration);

extern Declaration attribute_decl(Def,Type,Direction,Default);
extern Def attribute_decl_def(Declaration);
extern Type attribute_decl_type(Declaration);
extern Direction attribute_decl_direction(Declaration);
extern Default attribute_decl_default(Declaration);

extern Declaration function_decl(Def,Type,Block);
extern Def function_decl_def(Declaration);
extern Type function_decl_type(Declaration);
extern Block function_decl_body(Declaration);

extern Declaration procedure_decl(Def,Type,Block);
extern Def procedure_decl_def(Declaration);
extern Type procedure_decl_type(Declaration);
extern Block procedure_decl_body(Declaration);

extern Declaration constructor_decl(Def,Type);
extern Def constructor_decl_def(Declaration);
extern Type constructor_decl_type(Declaration);

extern Declaration pattern_decl(Def,Type,Pattern);
extern Def pattern_decl_def(Declaration);
extern Type pattern_decl_type(Declaration);
extern Pattern pattern_decl_choices(Declaration);

extern Declaration inheritance(Def,Type,Block);
extern Def inheritance_def(Declaration);
extern Type inheritance_used(Declaration);
extern Block inheritance_body(Declaration);

extern Declaration polymorphic(Def,Declarations,Block);
extern Def polymorphic_def(Declaration);
extern Declarations polymorphic_type_formals(Declaration);
extern Block polymorphic_body(Declaration);

extern Declaration pragma_call(Symbol,Expressions);
extern Symbol pragma_call_name(Declaration);
extern Expressions pragma_call_parameters(Declaration);

extern Declaration top_level_match(Match);
extern Match top_level_match_m(Declaration);

extern Declaration class_replacement(Class,Class);
extern Class class_replacement_class(Declaration);
extern Class class_replacement_as(Declaration);

extern Declaration module_replacement(Module,Module);
extern Module module_replacement_module(Declaration);
extern Module module_replacement_as(Declaration);

extern Declaration signature_replacement(Signature,Signature);
extern Signature signature_replacement_sig(Declaration);
extern Signature signature_replacement_as(Declaration);

extern Declaration type_replacement(Type,Type);
extern Type type_replacement_type(Declaration);
extern Type type_replacement_as(Declaration);

extern Declaration value_replacement(Expression,Expression);
extern Expression value_replacement_value(Declaration);
extern Expression value_replacement_as(Declaration);

extern Declaration pattern_replacement(Pattern,Pattern);
extern Pattern pattern_replacement_pattern(Declaration);
extern Pattern pattern_replacement_as(Declaration);

extern Declaration class_renaming(Def,Class);
extern Def class_renaming_def(Declaration);
extern Class class_renaming_old(Declaration);

extern Declaration module_renaming(Def,Module);
extern Def module_renaming_def(Declaration);
extern Module module_renaming_old(Declaration);

extern Declaration signature_renaming(Def,Signature);
extern Def signature_renaming_def(Declaration);
extern Signature signature_renaming_old(Declaration);

extern Declaration type_renaming(Def,Type);
extern Def type_renaming_def(Declaration);
extern Type type_renaming_old(Declaration);

extern Declaration value_renaming(Def,Expression);
extern Def value_renaming_def(Declaration);
extern Expression value_renaming_old(Declaration);

extern Declaration pattern_renaming(Def,Pattern);
extern Def pattern_renaming_def(Declaration);
extern Pattern pattern_renaming_old(Declaration);

extern Direction direction(Boolean,Boolean,Boolean);
extern Boolean direction_is_input(Direction);
extern Boolean direction_is_collection(Direction);
extern Boolean direction_is_circular(Direction);

extern Default simple(Expression);
extern Expression simple_value(Default);

extern Default composite(Expression,Expression);
extern Expression composite_initial(Default);
extern Expression composite_combiner(Default);

extern Default no_default();

extern Declaration normal_formal(Def,Type);
extern Def normal_formal_def(Declaration);
extern Type normal_formal_type(Declaration);

extern Declaration seq_formal(Def,Type);
extern Def seq_formal_def(Declaration);
extern Type seq_formal_type(Declaration);

extern Declaration type_formal(Def,Signature);
extern Def type_formal_def(Declaration);
extern Signature type_formal_sig(Declaration);

extern Declaration phylum_formal(Def,Signature);
extern Def phylum_formal_def(Declaration);
extern Signature phylum_formal_sig(Declaration);

extern Def def(Symbol,Boolean,Boolean);
extern Symbol def_name(Def);
extern Boolean def_is_constant(Def);
extern Boolean def_is_public(Def);

extern Use use(Symbol);
extern Symbol use_name(Use);

extern Use qual_use(Type,Symbol);
extern Type qual_use_from(Use);
extern Symbol qual_use_name(Use);

extern Class class_use(Use);
extern Use class_use_use(Class);

extern Module module_use(Use);
extern Use module_use_use(Module);

extern Type type_use(Use);
extern Use type_use_use(Type);

extern Type type_inst(Module,TypeActuals,Actuals);
extern Module type_inst_module(Type);
extern TypeActuals type_inst_type_actuals(Type);
extern Actuals type_inst_actuals(Type);

extern Type no_type();

extern Expression value_use(Use);
extern Use value_use_use(Expression);

#define no_value no_expr
extern Expression typed_value(Expression,Type);
extern Expression typed_value_expr(Expression);
extern Type typed_value_type(Expression);

extern Signature sig_use(Use);
extern Use sig_use_use(Signature);

extern Signature sig_inst(Boolean,Boolean,Class,TypeActuals);
extern Boolean sig_inst_is_input(Signature);
extern Boolean sig_inst_is_var(Signature);
extern Class sig_inst_class(Signature);
extern TypeActuals sig_inst_actuals(Signature);

extern Signature no_sig();

extern Pattern pattern_use(Use);
extern Use pattern_use_use(Pattern);

extern Pattern no_pattern();

extern Pattern typed_pattern(Pattern,Type);
extern Pattern typed_pattern_pat(Pattern);
extern Type typed_pattern_type(Pattern);

extern Signature fixed_sig(Types);
extern Types fixed_sig_types(Signature);

extern Signature mult_sig(Signature,Signature);
extern Signature mult_sig_sig1(Signature);
extern Signature mult_sig_sig2(Signature);

extern Type remote_type(Type);
extern Type remote_type_nodetype(Type);

extern Type function_type(Declarations,Declarations);
extern Declarations function_type_formals(Type);
extern Declarations function_type_return_values(Type);

extern Type private_type(Type);
extern Type private_type_rep(Type);

extern Pattern match_pattern(Pattern,Type);
extern Pattern match_pattern_pat(Pattern);
extern Type match_pattern_type(Pattern);

extern Pattern pattern_call(Pattern,PatternActuals);
extern Pattern pattern_call_func(Pattern);
extern PatternActuals pattern_call_actuals(Pattern);

extern Pattern pattern_actual(Pattern,Expression);
extern Pattern pattern_actual_arg(Pattern);
extern Expression pattern_actual_formal(Pattern);

extern Pattern rest_pattern(Pattern);
extern Pattern rest_pattern_constraint(Pattern);

extern Pattern choice_pattern(Patterns);
extern Patterns choice_pattern_choices(Pattern);

extern Pattern and_pattern(Pattern,Pattern);
extern Pattern and_pattern_p1(Pattern);
extern Pattern and_pattern_p2(Pattern);

extern Pattern pattern_var(Declaration);
extern Declaration pattern_var_formal(Pattern);

extern Pattern condition(Expression);
extern Expression condition_e(Pattern);

extern Pattern hole();

extern Pattern pattern_function(Declarations,Pattern);
extern Declarations pattern_function_formals(Pattern);
extern Pattern pattern_function_body(Pattern);

extern Declaration block_stmt(Block);
extern Block block_stmt_body(Declaration);

extern Declaration effect(Expression);
extern Expression effect_e(Declaration);

extern Declaration multi_call(Expression,Actuals,Actuals);
extern Expression multi_call_proc(Declaration);
extern Actuals multi_call_actuals(Declaration);
extern Actuals multi_call_results(Declaration);

#define procall multi_call
extern Declaration normal_assign(Expression,Expression);
extern Expression normal_assign_lhs(Declaration);
extern Expression normal_assign_rhs(Declaration);

extern Declaration collect_assign(Expression,Expression);
extern Expression collect_assign_lhs(Declaration);
extern Expression collect_assign_rhs(Declaration);

extern Declaration if_stmt(Expression,Block,Block);
extern Expression if_stmt_cond(Declaration);
extern Block if_stmt_if_true(Declaration);
extern Block if_stmt_if_false(Declaration);

extern Declaration for_in_stmt(Declaration,Expression,Block);
extern Declaration for_in_stmt_formal(Declaration);
extern Expression for_in_stmt_seq(Declaration);
extern Block for_in_stmt_body(Declaration);

extern Declaration for_stmt(Expression,Matches);
extern Expression for_stmt_expr(Declaration);
extern Matches for_stmt_matchers(Declaration);

extern Declaration case_stmt(Expression,Matches,Block);
extern Expression case_stmt_expr(Declaration);
extern Matches case_stmt_matchers(Declaration);
extern Block case_stmt_default(Declaration);

extern Match matcher(Pattern,Block);
extern Pattern matcher_pat(Match);
extern Block matcher_body(Match);

extern Expression integer_const(String);
extern String integer_const_token(Expression);

extern Expression real_const(String);
extern String real_const_token(Expression);

extern Expression string_const(String);
extern String string_const_token(Expression);

extern Expression char_const(String);
extern String char_const_token(Expression);

extern Expression undefined();

extern Expression no_expr();

extern Expression funcall(Expression,Actuals);
extern Expression funcall_f(Expression);
extern Actuals funcall_actuals(Expression);

extern Expression append(Expression,Expression);
extern Expression append_s1(Expression);
extern Expression append_s2(Expression);

extern Expression empty();

extern Expression class_value(Class);
extern Class class_value_c(Expression);

extern Expression module_value(Module);
extern Module module_value_m(Expression);

extern Expression signature_value(Signature);
extern Signature signature_value_s(Expression);

extern Expression type_value(Type);
extern Type type_value_T(Expression);

extern Expression pattern_value(Pattern);
extern Pattern pattern_value_p(Expression);

extern Expression repeat(Expression);
extern Expression repeat_expr(Expression);

extern Expression guarded(Expression,Expression);
extern Expression guarded_expr(Expression);
extern Expression guarded_cond(Expression);

extern Expression controlled(Expression,Declaration,Expression);
extern Expression controlled_expr(Expression);
extern Declaration controlled_formal(Expression);
extern Expression controlled_set(Expression);

#endif
