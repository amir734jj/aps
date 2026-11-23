PARSER_BASENAME = Grammar

RUNS = first follow nullable

SOURCES.FirstDriver = first.aps first-driver.scala
DRIVER.first = FirstDriver
EVALUATORS.first = DYNAMIC STATIC

SOURCES.FollowDriver = follow.aps follow-driver.scala
DRIVER.follow = FollowDriver
EVALUATORS.follow = DYNAMIC STATIC

SOURCES.NullableDriver = nullable.aps nullable-driver.scala
DRIVER.nullable = NullableDriver
EVALUATORS.nullable = DYNAMIC STATIC
