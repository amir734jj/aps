object FarrowLvDriver extends App {

  val symb = new M_SYMBOL("Symbol")
  symb.finish()

  val ss = new FarrowLvScanner(new java.io.FileReader(args(0)));
  val sp = new FarrowLvParser();
  sp.reset(ss, args(0));
  if (!sp.yyparse()) {
    println("Errors found.\n");
    System.exit(1);
  }
  var farrow_lv_tree = sp.getTree();
  val p = farrow_lv_tree.t_Program;
  
  val m_farrow_lv_tree = farrow_lv_tree;
  val m_farrow_lv = new M_FARROW_LV[m_farrow_lv_tree.T_Result]("FarrowLv", m_farrow_lv_tree.t_Result);

  if (args.contains("--debug")) Debug.activate();

  m_farrow_lv_tree.finish();
  m_farrow_lv.finish();

  println("Results:");
  m_farrow_lv.v_program_live(m_farrow_lv.t_Program.nodes(0)).toSeq.map(_.name).sorted.foreach(println);

}
