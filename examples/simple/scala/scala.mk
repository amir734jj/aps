PARSER_BASENAME = Simple

RUNS = classic-binding nested-cycles simple-binding simple-binding1 \
	simple-binding2 simple-binding3 simple-snc simple-snc-fiber

SOURCES.Classic = classic-binding.aps classic-driver.scala
DRIVER.classic-binding = Classic
EVALUATORS.classic-binding = DYNAMIC STATIC

SOURCES.NestedCyclesDriver = nested-cycles.aps nested-cycles-driver.scala
DRIVER.nested-cycles = NestedCyclesDriver
EVALUATORS.nested-cycles = DYNAMIC STATIC

SOURCES.SimpleSncDriver = simple-snc.aps simple-snc-driver.scala
DRIVER.simple-snc = SimpleSncDriver
EVALUATORS.simple-snc = DYNAMIC FARROW

SOURCES.SimpleSncFiberDriver = simple-snc-fiber.aps simple-snc-fiber-driver.scala
DRIVER.simple-snc-fiber = SimpleSncFiberDriver
EVALUATORS.simple-snc-fiber = DYNAMIC

SOURCES.SimpleBindingDriver = simple-binding.aps simple-binding-driver.scala
DRIVER.simple-binding = SimpleBindingDriver
EVALUATORS.simple-binding = DYNAMIC STATIC

SOURCES.SimpleBinding1Driver = simple-binding1.aps simple-binding-driver.scala
DRIVER.simple-binding1 = SimpleBinding1Driver
EVALUATORS.simple-binding1 = DYNAMIC STATIC
MAIN.SimpleBinding1Driver = SimpleBindingDriver

SOURCES.SimpleBinding2Driver = simple-binding2.aps simple-binding-driver.scala
DRIVER.simple-binding2 = SimpleBinding2Driver
EVALUATORS.simple-binding2 = DYNAMIC STATIC
MAIN.SimpleBinding2Driver = SimpleBindingDriver

SOURCES.SimpleBinding3Driver = simple-binding3.aps simple-binding-driver.scala
DRIVER.simple-binding3 = SimpleBinding3Driver
EVALUATORS.simple-binding3 = DYNAMIC STATIC
MAIN.SimpleBinding3Driver = SimpleBindingDriver
