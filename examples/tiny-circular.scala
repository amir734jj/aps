// Generated by aps2scala version 0.3.6
import basic_implicit._;
object tiny_circular_implicit {
  val tiny_circular_loaded = true;
import basic_implicit._;
import tiny_implicit._;
type T_TINY_CIRCULAR[T_T] = T_T;
}
import tiny_circular_implicit._;

import basic_implicit._;
import tiny_implicit._;
trait C_TINY_CIRCULAR[T_Result, T_T] extends C_TYPE[T_Result] with C_TINY[T_Result] {
  type T_S <: Node;
  val t_S : C_PHYLUM[T_S];
  type T_RemoteS;
  val t_RemoteS : C_TYPE[T_RemoteS];
  type T_Integers;
  val t_Integers : C_TYPE[T_Integers]with C_SET[T_Integers,T_Integer];
  type T_IntegerLattice;
  val t_IntegerLattice : C_TYPE[T_IntegerLattice]with C_UNION_LATTICE[T_IntegerLattice,T_Integer,T_Integers];
  val v_s_bag1 : (T_S) => T_IntegerLattice;
  val v_s_bag2 : (T_S) => T_IntegerLattice;
  val v_result : (T_Root) => T_Integers;
  val v_w_s : (T_Wood) => T_RemoteS;
  val p_s_constructor : PatternFunction[(T_S)];
  def v_s_constructor : () => T_S;
}

class M_TINY_CIRCULAR[T_T](name : String,val t_T : C_TYPE[T_T] with C_TINY[T_T])
  extends Module(name)
  with C_TINY_CIRCULAR[T_T,T_T]
{
  type T_Result = T_T;
  val v_equal = t_T.v_equal;
  val v_string = t_T.v_string;
  val v_assert = t_T.v_assert;
  val v_node_equivalent = t_T.v_node_equivalent;
  type T_Root = t_T.T_Root;
  val t_Root = t_T.t_Root;
  type T_Wood = t_T.T_Wood;
  val t_Wood = t_T.t_Wood;
  val p_root = t_T.p_root;
  val v_root = t_T.v_root;
  val p_branch = t_T.p_branch;
  val v_branch = t_T.v_branch;
  val p_leaf = t_T.p_leaf;
  val v_leaf = t_T.v_leaf;

  val t_Result : this.type = this;
  abstract class T_S(t : I_PHYLUM[T_S]) extends Node(t) {}
  val t_S = new I_PHYLUM[T_S]("S");

  type T_RemoteS = T_S;
  val t_RemoteS = t_S;
  val t_Integers = new M_SET[T_Integer]("Integers",t_Integer)

  type T_Integers = /*TI*/T_SET[T_Integer];
  val t_IntegerLattice = new M_UNION_LATTICE[T_Integer,T_Integers]("IntegerLattice",t_Integer,t_Integers)
    /* dumping traits */
    with C_TYPE[T_Integers]
    with C_SET[T_Integers, T_Integer] {
      override val v_assert = t_Integers.v_assert;
      override val v_equal = t_Integers.v_equal;
      override val v_node_equivalent = t_Integers.v_node_equivalent;
      override val v_string = t_Integers.v_string;
      override val v_less = t_Integers.v_less;
      override val v_less_equal = t_Integers.v_less_equal;
      override val v_none = t_Integers.v_none;
      override val v_single = t_Integers.v_single;
      override val v_append = t_Integers.v_append;
      override val v__op_AC = t_Integers.v__op_AC;
      override val p__op_AC = t_Integers.p__op_AC;
      override val v_member = t_Integers.v_member;
      override val v_union = t_Integers.v_union;
      override val v_intersect = t_Integers.v_intersect;
      override val v_difference = t_Integers.v_difference;
      override val v_combine = t_Integers.v_combine;
    }

  type T_IntegerLattice = /*TI*/T_UNION_LATTICE[T_Integer,T_Integers];
  private class E_s_bag1(anchor : T_S) extends Evaluation[T_S,T_IntegerLattice](anchor,anchor.toString()+"."+"s_bag1") with CircularEvaluation[T_S,T_IntegerLattice] with CollectionEvaluation[T_S,T_IntegerLattice] {
    override def getDefault = t_IntegerLattice.v_none();
    override def combine(v1 : T_IntegerLattice, v2 : T_IntegerLattice) = t_IntegerLattice.v_combine(v1,v2);
    def lattice() : C_LATTICE[T_IntegerLattice] = t_IntegerLattice;

  }
  private object a_s_bag1 extends Attribute[T_S,T_IntegerLattice](t_S,t_IntegerLattice,"s_bag1") {
    override def createEvaluation(anchor : T_S) : Evaluation[T_S,T_IntegerLattice] = new E_s_bag1(anchor);
  }
  val v_s_bag1 : T_S => T_IntegerLattice = a_s_bag1.get _;

  private class E_s_bag2(anchor : T_S) extends Evaluation[T_S,T_IntegerLattice](anchor,anchor.toString()+"."+"s_bag2") with CircularEvaluation[T_S,T_IntegerLattice] with CollectionEvaluation[T_S,T_IntegerLattice] {
    override def getDefault = t_IntegerLattice.v_none();
    override def combine(v1 : T_IntegerLattice, v2 : T_IntegerLattice) = t_IntegerLattice.v_combine(v1,v2);
    def lattice() : C_LATTICE[T_IntegerLattice] = t_IntegerLattice;

  }
  private object a_s_bag2 extends Attribute[T_S,T_IntegerLattice](t_S,t_IntegerLattice,"s_bag2") {
    override def createEvaluation(anchor : T_S) : Evaluation[T_S,T_IntegerLattice] = new E_s_bag2(anchor);
  }
  val v_s_bag2 : T_S => T_IntegerLattice = a_s_bag2.get _;

  private class E_result(anchor : T_Root) extends Evaluation[T_Root,T_Integers](anchor,anchor.toString()+"."+"result") {
  }
  private object a_result extends Attribute[T_Root,T_Integers](t_Root,t_Integers,"result") {
    override def createEvaluation(anchor : T_Root) : Evaluation[T_Root,T_Integers] = new E_result(anchor);
  }
  val v_result : T_Root => T_Integers = a_result.get _;

  private class E_w_s(anchor : T_Wood) extends Evaluation[T_Wood,T_RemoteS](anchor,anchor.toString()+"."+"w_s") {
  }
  private object a_w_s extends Attribute[T_Wood,T_RemoteS](t_Wood,t_RemoteS,"w_s") {
    override def createEvaluation(anchor : T_Wood) : Evaluation[T_Wood,T_RemoteS] = new E_w_s(anchor);
  }
  val v_w_s : T_Wood => T_RemoteS = a_w_s.get _;

  case class c_s_constructor() extends T_S(t_S) {
    override def children : List[Node] = List();
    override def toString() : String = Debug.with_level {
      "s_constructor("+ ")";
    }
  }
  def u_s_constructor(x:Any) : Option[(T_S)] = x match {
    case x@c_s_constructor() => Some(x);
    case _ => None };
  val v_s_constructor = f_s_constructor _;
  def f_s_constructor():T_S = c_s_constructor().register;
  val p_s_constructor = new PatternFunction[(T_S)](u_s_constructor);

  private class E1_t(anchor : t_Result.T_Wood) extends Evaluation[t_Result.T_Wood,T_S](anchor,anchor.toString()+"."+"t") {
  }
  private object a1_t extends Attribute[t_Result.T_Wood,T_S](t_Result.t_Wood,t_S,"t") {
    override def createEvaluation(anchor : t_Result.T_Wood) : Evaluation[t_Result.T_Wood,T_S] = new E1_t(anchor);
  }
  private class E2_v(anchor : t_Result.T_Wood) extends Evaluation[t_Result.T_Wood,T_S](anchor,anchor.toString()+"."+"v") {
  }
  private object a2_v extends Attribute[t_Result.T_Wood,T_S](t_Result.t_Wood,t_S,"v") {
    override def createEvaluation(anchor : t_Result.T_Wood) : Evaluation[t_Result.T_Wood,T_S] = new E2_v(anchor);
  }
  private class E3_i(anchor : t_Result.T_Wood) extends Evaluation[t_Result.T_Wood,T_IntegerLattice](anchor,anchor.toString()+"."+"i") with CircularEvaluation[t_Result.T_Wood,T_IntegerLattice] {
    def lattice() : C_LATTICE[T_IntegerLattice] = t_IntegerLattice;

  }
  private object a3_i extends Attribute[t_Result.T_Wood,T_IntegerLattice](t_Result.t_Wood,t_IntegerLattice,"i") {
    override def createEvaluation(anchor : t_Result.T_Wood) : Evaluation[t_Result.T_Wood,T_IntegerLattice] = new E3_i(anchor);
  }
  private class E4_i(anchor : t_Result.T_Root) extends Evaluation[t_Result.T_Root,T_IntegerLattice](anchor,anchor.toString()+"."+"i") with CircularEvaluation[t_Result.T_Root,T_IntegerLattice] {
    def lattice() : C_LATTICE[T_IntegerLattice] = t_IntegerLattice;

  }
  private object a4_i extends Attribute[t_Result.T_Root,T_IntegerLattice](t_Result.t_Root,t_IntegerLattice,"i") {
    override def createEvaluation(anchor : t_Result.T_Root) : Evaluation[t_Result.T_Root,T_IntegerLattice] = new E4_i(anchor);
  }
  def visit_0_1(node : T_Root) : Unit = node match {
    case p_root(_,_) => visit_0_1_0(node);
  };
  def visit_0_1_0(anchor : T_Root) : Unit = anchor match {
    case p_root(v_p,v_b) => {
      // p.G[Root]'shared_info is ready now.
      // shared info for b is ready.
      visit_1_1(v_b);
      // b.w_s is ready now.
      // b.UP[Wood]-0 is ready now.
      // UP[root]-0 is ready now
      a_result.assign(v_p,a_s_bag1.get(a_w_s.get(v_b)));
      // b.DOWN[Wood]-0 implicit.
    }
  }


  def visit_1_1(node : T_Wood) : Unit = node match {
    case p_leaf(_,_) => visit_1_1_1(node);
    case p_branch(_,_,_) => visit_1_1_0(node);
  };
  def visit_1_2(node : T_Wood) : Unit = node match {
    case p_leaf(_,_) => visit_1_2_1(node);
    case p_branch(_,_,_) => visit_1_2_0(node);
  };
  def visit_1_1_1(anchor : T_Wood) : Unit = anchor match {
    case p_leaf(v_l,v_x) => {
      // l.G[Wood]'shared_info is ready now.
      a1_t.assign(anchor,v_s_constructor());
      a_w_s.assign(v_l,a1_t.get(anchor));
      a_s_bag1.assign(a1_t.get(anchor),t_IntegerLattice.v_single(v_x));
      // t$s_bag1
      // l.UP[Wood]-0 implicit.
    }
  }

  def visit_1_2_1(anchor : T_Wood) : Unit = anchor match {
    case p_leaf(v_l,v_x) => {
      // l.DOWN[Wood]-0 is ready now.
    }
  }

  def visit_1_1_0(anchor : T_Wood) : Unit = anchor match {
    case p_branch(v_b,v_x,v_y) => {
      // b.G[Wood]'shared_info is ready now.
      // shared info for x is ready.
      visit_1_1(v_x);
      // x.w_s is ready now.
      // x.UP[Wood]-0 is ready now.
      // shared info for y is ready.
      visit_1_1(v_y);
      // y.w_s is ready now.
      // y.UP[Wood]-0 is ready now.
      a2_v.assign(anchor,v_s_constructor());
      a_w_s.assign(v_b,a2_v.get(anchor));
      // b.UP[Wood]-0 implicit.
    }
  }

  def visit_1_2_0(anchor : T_Wood) : Unit = anchor match {
    case p_branch(v_b,v_x,v_y) => {
      // b.DOWN[Wood]-0 is ready now.
      // x.DOWN[Wood]-0 implicit.
      // y.DOWN[Wood]-0 implicit.
    }
  }


  def visit() : Unit = {
    val roots = t_Root.nodes;
    // shared info for TINY_CIRCULAR is ready.
    for (root <- roots) {
      visit_0_1(root);
    }
    // TINY_CIRCULAR.result is ready now.
  }

  override def finish() : Unit = {
    visit();
    t_S.finish();
    t_Integers.finish();
    t_IntegerLattice.finish();
super.finish();
  }

}

