PARSER_BASENAME = NestedUbd

# This should be run
# And run has evluation techniques, scala source, evluation source and APS source
DRIVERS = NestedUbdDriver NestedUbdFiberDriver

# Driver has driver source and APS source
DRIVER.NestedUbdDriver = nested-ubd.aps DYNAMIC,STATIC,FARROW nested-ubd-driver.scala

DRIVER.NestedUbdFiberDriver = nested-ubd-fiber.aps DYNAMIC,STATIC nested-ubd-fiber-driver.scala

APS_DRIVER_NAME>.SOURCES =
DRIVER. 

RUN has source, evaluations
3 Runs, each run has it's own pices

Driver