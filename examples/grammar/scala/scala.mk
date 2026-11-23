PARSER_BASENAME = Grammar

DRIVERS = FirstDriver FollowDriver NullableDriver

DRIVER.FirstDriver = first.aps DYNAMIC,STATIC first-driver.scala

DRIVER.FollowDriver = follow.aps DYNAMIC,STATIC follow-driver.scala

DRIVER.NullableDriver = nullable.aps DYNAMIC,STATIC nullable-driver.scala
