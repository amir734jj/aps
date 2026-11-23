.DEFAULT_GOAL := all
APSTOP = ../..
AST ?= $(error Invoke the Scala build through the example Makefile)
SCALAC = scalac -J-Xmx4g
SCALA = scala
JVMFLAGS = -J-Xss64m -J-Xmx16g
APSLIB = ${APSTOP}/lib/aps-library.jar
SCALABISON = ${HOME}/git/scala-bison/scala-bison-2.13.jar
SCALAFLEX = ${HOME}/Documents/Courses/sp26-cs654/etc/JFlex.jar
APS2SCALA = ${APSTOP}/bin/aps2scala
AST_DIRS := $(sort $(patsubst %/,%,$(dir $(wildcard ../*/*.aps))))
APSPATH = $(subst $() $(),:,$(abspath ${AST_DIRS} ${APSTOP}/base))
APS2SCALAFLAGS = -p ${APSPATH} -G
EVALUATOR ?= DYNAMIC

OUTPUT_DYNAMIC = dynamic
OUTPUT_STATIC = static
OUTPUT_FARROW = farrow
OUTPUT_SCC = scc
ifeq (${OUTPUT_${EVALUATOR}},)
$(error Unknown EVALUATOR '${EVALUATOR}'; expected DYNAMIC, STATIC, FARROW or SCC)
endif

OUT = ../scala/${OUTPUT_${EVALUATOR}}
FLAGS_STATIC = -S -C
FLAGS_FARROW = -F
FLAGS_SCC = -C
EVALUATOR_FLAGS = ${FLAGS_${EVALUATOR}}
TREE_MODULES := $(basename ${AST})

vpath %.aps ${AST_DIRS}
vpath %.scala scala

include scala/scala.mk

DRIVERS = $(sort $(foreach run,${RUNS},$(DRIVER.$(run))))
driver-module = $(basename $(firstword $(SOURCES.$1)))
driver-sources = $(SOURCES.$1)
driver-main = $(or $(MAIN.$1),$1)
run-driver = $(DRIVER.$1)
run-module = $(call driver-module,$(call run-driver,$1))
run-main = $(call driver-main,$(call run-driver,$1))

define validate-driver
$(if $(filter %.aps,$(firstword $(SOURCES.$1))),,$(error SOURCES.$1 must start with an .aps input))
$(if $(filter-out %.aps %.scala,$(SOURCES.$1)),$(error SOURCES.$1 must contain only APS or Scala inputs))
$(if $(word 2,$(MAIN.$1)),$(error MAIN.$1 allows only one main object))
endef

define validate-run
$(if $(filter 1,$(words $(DRIVER.$1))),,$(error DRIVER.$1 must specify one driver))
$(if $(EVALUATORS.$1),,$(error EVALUATORS.$1 must specify evaluators))
$(if $(filter-out DYNAMIC STATIC FARROW SCC,$(EVALUATORS.$1)),$(error Unknown evaluator in EVALUATORS.$1: $(EVALUATORS.$1)))
endef

$(foreach run,${RUNS},$(call validate-run,$(run)))
$(foreach driver,${DRIVERS},$(call validate-driver,$(driver)))
TEST_RUNS ?= ${RUNS}
TEST_PROGRAMS ?= programs/*
TEST_INPUTS = $(foreach pattern,$(TEST_PROGRAMS),$(or $(wildcard $(pattern)),$(error No program files found for: $(pattern))))
include ../scala/rules.mk

.PHONY: all clean run test
.DELETE_ON_ERROR:
.SECONDARY:

all: ${RUN_CLASSES}

test:
	+@status=0; \
	$(foreach run,$(TEST_RUNS), \
	  for program in $(foreach input,$(TEST_INPUTS),'$(input)'); do \
	    bash ../scala/compare-evaluators.sh $(run) "$$program" \
	      '$(EVALUATORS.$(run))' || status=1; \
	  done;) \
	exit $$status

run: ${RUN_TARGETS}

%.scala: %.aps
	$(MAKE) -f ../scala/Makefile ${OUT}/$*/generate

clean:
	rm -rf $(foreach output,dynamic static farrow scc,$(addprefix ../scala/$(output)/,${MODULES}))
