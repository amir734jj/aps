APSTOP= ../..
SCALAC= scalac
SCALA= scala
SCALAV= 2.12
APSLIB = ${APSTOP}/lib/aps-library-${SCALAV}.jar
SCALAFLAGS= -cp .:${APSLIB}
SCALACFLAGS= ${SCALAFLAGS}
APS2SCALA = ${APSTOP}/bin/aps2scala
APS2SCALAFLAGS = -p ..:${APSTOP}/base -G

SCALAGEN = simple.scala classic-binding.scala tiny.scala \
	test-coll.scala test-use-coll.scala test-cycle.scala use-global.scala \
	grammar.scala first.scala follow.scala

MISC_SCALAGEN = nested-cycles.scala GrammarParser.scala SimpleParser.scala \
	GrammarTokens.scala SimpleTokens.scala *.scala~ GrammarScanner.scala \
	*.output *.lex *.y  *Tokens.scala *_static.scala *_dynamic.scala *.scala~

.PHONY: all clean

all : ${SCALAGEN}
all : grammar_implicit.class simple_implicit.class classic_binding_implicit.class Classic.class
all : GrammarScanner.class GrammarTokens.class SimpleScanner.class SimpleTokens.class
all : GrammarParserBase.class GrammarParser.class SimpleParserBase.class SimpleParser.class
all : test_coll_implicit.class TestCollDriver.class
all : test_cycle_implicit.class TestCycleDriver.class
all : test_use_coll_implicit.class TestUseCollDriver.class
all : grammar_implicit.class GrammarDriver.class
all : nested_cycles_implicit.class NestedCyclesDriver.class

.PHONY: run

run: Classic.run TestCollDriver.run TestCycleDriver.run NestedCyclesDriver.run

nested-cycles.scala: ../nested-cycles.aps ${APS2SCALA}
	${APS2SCALA} ${APS2SCALAFLAGS} -S $(basename $(@F))

nested_cycles_dynamic.scala:  ../nested-cycles.aps ${APS2SCALA}
	${APS2SCALA} ${APS2SCALAFLAGS} -m nested_cycles_dynamic nested-cycles

nested_cycles_static.scala:  ../nested-cycles.aps ${APS2SCALA}
	${APS2SCALA} ${APS2SCALAFLAGS} -S -m nested_cycles_static nested-cycles

first.scala: ../first.aps ${APS2SCALA}
	${APS2SCALA} ${APS2SCALAFLAGS} -S $(basename $(@F))

first_static.scala: ../first.aps ${APS2SCALA}
	${APS2SCALA} ${APS2SCALAFLAGS} -S -m first_static first

first_dynamic.scala: ../first.aps ${APS2SCALA}
	${APS2SCALA} ${APS2SCALAFLAGS} -m first_dynamic first

follow.scala: ../follow.aps ${APS2SCALA}
	${APS2SCALA} ${APS2SCALAFLAGS} -S $(basename $(@F))

follow_static.scala: ../follow.aps ${APS2SCALA}
	${APS2SCALA} ${APS2SCALAFLAGS} -S -m follow_static follow

follow_dynamic.scala: ../follow.aps ${APS2SCALA}
	${APS2SCALA} ${APS2SCALAFLAGS} -m follow_dynamic follow

nullable.scala: ../nullable.aps ${APS2SCALA}
	${APS2SCALA} ${APS2SCALAFLAGS} -S $(basename $(@F))

nullable_static.scala: ../nullable.aps ${APS2SCALA}
	${APS2SCALA} ${APS2SCALAFLAGS} -S -m nullable_static nullable

nullable_dynamic.scala: ../nullable.aps ${APS2SCALA}
	${APS2SCALA} ${APS2SCALAFLAGS} -m nullable_dynamic nullable

%.scala: ../%.aps ${APS2SCALA}
	${APS2SCALA} ${APS2SCALAFLAGS} $*

%_implicit.class : %.scala
	${SCALAC} ${SCALACFLAGS} $*.scala

Grammar.lex : ../grammar.lex Grammar.lex.scala
	cat Grammar.lex.scala ../grammar.lex > $@

GrammarScanner.scala : Grammar.lex
	java -jar ${SCALAFLEX} --scala $<

Grammar.y : ../grammar.y Grammar.y.scala
	cat $< Grammar.y.scala > $@

GrammarParser.scala GrammarTokens.scala : Grammar.y ${SCALABISON}
	bison -v Grammar.y
	rm Grammar.tab.c
	${SCALA} -classpath ${SCALABISON} edu.uwm.cs.scalabison.RunGenerator Grammar.y

GrammarScanner.class : GrammarScanner.scala GrammarTokens.class
	${SCALAC} ${SCALACFLAGS} $<

GrammarParser.class : GrammarParser.scala GrammarScanner.class GrammarParserBase.class
	${SCALAC} ${SCALACFLAGS} $<

GrammarParserBase.class : GrammarParserBase.scala grammar_implicit.class
	${SCALAC} ${SCALACFLAGS} $<

GrammarTokens.class : GrammarTokens.scala
	${SCALAC} ${SCALACFLAGS} $<

Simple.lex : ../simple.lex Simple.lex.scala
	cat Simple.lex.scala ../simple.lex > $@

SimpleScanner.scala : Simple.lex
	java -jar ${SCALAFLEX} --scala $<

Simple.y : ../simple.y Simple.y.scala
	cat $< Simple.y.scala > $@

SimpleParser.scala SimpleTokens.scala : Simple.y ${SCALABISON}
	bison -v Simple.y
	rm Simple.tab.c
	${SCALA} -classpath ${SCALABISON} edu.uwm.cs.scalabison.RunGenerator Simple.y

SimpleScanner.class : SimpleScanner.scala SimpleTokens.class
	${SCALAC} ${SCALACFLAGS} $<

SimpleParser.class : SimpleParser.scala SimpleParserBase.class SimpleScanner.class
	${SCALAC} ${SCALACFLAGS} $<

SimpleParserBase.class : SimpleParserBase.scala simple_implicit.class
	${SCALAC} ${SCALACFLAGS} $<

SimpleTokens.class : SimpleTokens.scala
	${SCALAC} ${SCALACFLAGS} $<

nested-cycles.class nested_cycles_static.class nested_cycles_dynamic.class: simple_implicit.class nested-cycles.scala nested_cycles_static.scala nested_cycles_dynamic.scala
	${SCALAC} ${SCALACFLAGS} $(basename $(@F)).scala

first.class follow.class first_static.class first_dynamic.class follow_static.class follow_dynamic.class nullable_static.class nullable_dynamic.class: grammar_implicit.class first.scala follow.scala first_static.scala first_dynamic.scala follow_static.scala follow_dynamic.scala  nullable_static.scala nullable_dynamic.scala
	${SCALAC} ${SCALACFLAGS} $(basename $(@F)).scala

.PHONY: nested_cycles_implicit.class
nested_cycles_implicit.class : nested-cycles.class nested_cycles_static.class nested_cycles_dynamic.class simple_implicit.class ;

NestedCyclesDriver.class: nested_cycles_implicit.class SimpleParser.class
	${SCALAC} ${SCALACFLAGS} nested-cycles-driver.scala

classic_binding_implicit.class : classic-binding.scala
	${SCALAC} ${SCALACFLAGS} $<

Classic.class : classic-driver.scala SimpleParser.class
	${SCALAC} ${SCALACFLAGS} $<

Classic.class   classic_binding_implicit.class : simple_implicit.class
Classic.class : classic_binding_implicit.class

test_coll_implicit.class : test-coll.scala tiny_implicit.class
	${SCALAC} ${SCALACFLAGS} $<

test_use_coll_implicit.class : test-use-coll.scala
	${SCALAC} ${SCALACFLAGS} $<

TestCollDriver.class : test_coll_implicit.class test-coll-driver.scala
	${SCALAC} ${SCALACFLAGS}  test-coll-driver.scala

TestUseCollDriver.class : test_use_coll_implicit.class test-use-coll-driver.scala tiny_implicit.class
	${SCALAC} ${SCALACFLAGS}  test-use-coll-driver.scala

test_cycle_implicit.class : test-cycle.scala
	${SCALAC} ${SCALACFLAGS} $<

TestCycleDriver.class : test_cycle_implicit.class test-cycle-driver.scala
	${SCALAC} ${SCALACFLAGS}  test-cycle-driver.scala

grammar_implicit.class : grammar.scala first.scala follow.scala nullable.scala
	${SCALAC} ${SCALACFLAGS} $^

GrammarDriver.class : grammar_implicit.class GrammarParser.class first_static.class first_dynamic.class follow_static.class follow_dynamic.class  nullable_static.class nullable_dynamic.class
	${SCALAC} ${SCALACFLAGS} grammar-driver.scala

TinyParser.class : tiny-parser.handcode.scala tiny_implicit.class
	${SCALAC} ${SCALACFLAGS} tiny-parser.handcode.scala

use_global_implicit.class : use-global.scala tiny_implicit.class
	${SCALAC} ${SCALACFLAGS} use-global.scala

UseGlobal.class : use_global_implicit.class TinyParser.class
UseGlobal.class : use-global-driver.scala
	${SCALAC} ${SCALACFLAGS} $<

.PHONY: %.run

%.run : %.class
	scala ${SCALAFLAGS} $* ${ARGS}

clean:
	rm -f *.class ${SCALAGEN} ${MISC_SCALAGEN}

