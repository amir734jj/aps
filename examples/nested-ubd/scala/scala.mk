PARSER_BASENAME = NestedUbd

RUNS = baseline fiber

SOURCES.NestedUbdDriver = nested-ubd.aps nested-ubd-driver.scala
DRIVER.baseline = NestedUbdDriver
EVALUATORS.baseline = DYNAMIC STATIC FARROW

SOURCES.NestedUbdFiberDriver = nested-ubd-fiber.aps nested-ubd-fiber-driver.scala
DRIVER.fiber = NestedUbdFiberDriver
EVALUATORS.fiber = DYNAMIC STATIC