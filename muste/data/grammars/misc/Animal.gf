abstract Animal = {
  flags startcat = S ;
  cat
    Animal ; Action ; Object ; S ;
  fun
    eat : Action ;
    drink : Action ;
    produce : Action ;
    wolf : Animal ;
    sheep : Animal ;
    lamb : Animal ;
    milk : Object ;
    wool : Object ;
    grass : Object ;
    abuse : Animal -> Object ;
    apply : Action -> Animal -> Object -> S ;
  }