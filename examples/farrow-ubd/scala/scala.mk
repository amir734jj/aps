PARSER_BASENAME = FarrowUbd

RUNS = farrow-ubd farrow-ubd-fiber

SOURCES.FarrowUbdDriver = farrow-ubd.aps farrow-ubd-driver.scala
DRIVER.farrow-ubd = FarrowUbdDriver
EVALUATORS.farrow-ubd = DYNAMIC STATIC FARROW

SOURCES.FarrowUbdFiberDriver = farrow-ubd-fiber.aps farrow-ubd-fiber-driver.scala
DRIVER.farrow-ubd-fiber = FarrowUbdFiberDriver
EVALUATORS.farrow-ubd-fiber = DYNAMIC STATIC
