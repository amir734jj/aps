// Generated by aps2scala version 0.3.6
import basic_implicit._;
object cool_symbol_implicit {
  val cool_symbol_loaded = true;
  val t_Symbol = new M_SYMBOL("Symbol")

  type T_Symbol = /*TI*/T_SYMBOL;
  val v_make_symbol : (T_String) => T_Symbol = t_Symbol.v_create;
  val v_symbol_name : (T_Symbol) => T_String = t_Symbol.v_name;
  val v_symbol_equal : (T_Symbol,T_Symbol) => T_Boolean = t_Symbol.v_equal;
  val v_null_symbol:T_Symbol = t_Symbol.v_null;
  val v_gensym = f_gensym _;
  def f_gensym():T_Symbol;
}
import cool_symbol_implicit._;

trait C_SYMBOL[T_Result] extends C_TYPE[T_Result] with C_BASIC[T_Result] with C_PRINTABLE[T_Result] with C_ORDERED[T_Result] {
  val v_assert : (T_Result) => Unit;
  val v_equal : (T_Result,T_Result) => T_Boolean;
  val v_create : (T_String) => T_Result;
  val v_name : (T_Result) => T_String;
  val v_less : (T_Result,T_Result) => T_Boolean;
  val v_less_equal : (T_Result,T_Result) => T_Boolean;
  def v_string : (T_Result) => T_String;
  def v_null : T_Result;
}

abstract class T_SYMBOL(t : C_SYMBOL[T_SYMBOL]) extends Value(t) { }

class M_SYMBOL(name : String)
  extends I_TYPE[T_SYMBOL](name)
  with C_SYMBOL[T_SYMBOL]
{
  val t_Result : this.type = this;
  val v_assert = f_assert _;
  def f_assert(v__1 : T_Result);
  val v_equal = f_equal _;
  def f_equal(v__2 : T_Result, v__3 : T_Result):T_Boolean;
  val v_create = f_create _;
  def f_create(v__4 : T_String):T_Result;
  val v_name = f_name _;
  def f_name(v__5 : T_Result):T_String;
  val v_less = f_less _;
  def f_less(v__6 : T_Result, v__7 : T_Result):T_Boolean;
  val v_less_equal = f_less_equal _;
  def f_less_equal(v__8 : T_Result, v__9 : T_Result):T_Boolean;
  val v_string : (T_Result) => T_String = v_name;
  val v_null:T_Result;
  override def finish() : Unit = {
    super.finish();
  }

}
