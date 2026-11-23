SHARED_SOURCES = tiny-parser.handcode.scala

RUNS = broad-fiber-cycle below-fiber-cycle below-single-fiber-cycle \
	local-fiber-cycle test-coll test-use-coll test-cycle use-global \
	test-fields test-for test-for-patterns test-case-patterns \
	test-nested-patterns test-finish

SOURCES.BroadFiberCycleDriver = broad-fiber-cycle.aps broad-fiber-cycle-driver.scala
DRIVER.broad-fiber-cycle = BroadFiberCycleDriver
EVALUATORS.broad-fiber-cycle = DYNAMIC STATIC

SOURCES.BelowFiberCycleDriver = below-fiber-cycle.aps below-fiber-cycle-driver.scala
DRIVER.below-fiber-cycle = BelowFiberCycleDriver
EVALUATORS.below-fiber-cycle = DYNAMIC STATIC

SOURCES.BelowSingleFiberCycleDriver = below-single-fiber-cycle.aps below-single-fiber-cycle-driver.scala
DRIVER.below-single-fiber-cycle = BelowSingleFiberCycleDriver
EVALUATORS.below-single-fiber-cycle = DYNAMIC STATIC

SOURCES.LocalFiberCycleDriver = local-fiber-cycle.aps local-fiber-cycle-driver.scala
DRIVER.local-fiber-cycle = LocalFiberCycleDriver
EVALUATORS.local-fiber-cycle = DYNAMIC STATIC

SOURCES.TestCollDriver = test-coll.aps test-coll-driver.scala
DRIVER.test-coll = TestCollDriver
EVALUATORS.test-coll = DYNAMIC STATIC

SOURCES.TestUseCollDriver = test-use-coll.aps test-use-coll-driver.scala
DRIVER.test-use-coll = TestUseCollDriver
EVALUATORS.test-use-coll = DYNAMIC STATIC

SOURCES.TestCycleDriver = test-cycle.aps test-cycle-driver.scala
DRIVER.test-cycle = TestCycleDriver
EVALUATORS.test-cycle = DYNAMIC STATIC

SOURCES.UseGlobal = use-global.aps use-global-driver.scala
DRIVER.use-global = UseGlobal
EVALUATORS.use-global = DYNAMIC STATIC

SOURCES.TestFieldsDriver = test-fields.aps test-fields-driver.scala
DRIVER.test-fields = TestFieldsDriver
EVALUATORS.test-fields = DYNAMIC STATIC

SOURCES.TestForDriver = test-for.aps test-for-driver.scala
DRIVER.test-for = TestForDriver
EVALUATORS.test-for = DYNAMIC STATIC

SOURCES.TestForPatternsDriver = test-for-patterns.aps test-for-patterns-driver.scala
DRIVER.test-for-patterns = TestForPatternsDriver
EVALUATORS.test-for-patterns = DYNAMIC STATIC

SOURCES.TestCasePatternsDriver = test-case-patterns.aps test-case-patterns-driver.scala
DRIVER.test-case-patterns = TestCasePatternsDriver
EVALUATORS.test-case-patterns = DYNAMIC STATIC

SOURCES.TestNestedPatternsDriver = test-nested-patterns.aps test-nested-patterns-driver.scala
DRIVER.test-nested-patterns = TestNestedPatternsDriver
EVALUATORS.test-nested-patterns = DYNAMIC STATIC

SOURCES.FinishDriver = test-finish.aps finish-driver.scala
DRIVER.test-finish = FinishDriver
EVALUATORS.test-finish = DYNAMIC STATIC
