(* Taken from Example 1 of
   Hofmann and Chen, "Buchi Types for Infinite Traces and Liveness", CSL-LICS 2014 *)
let rec f () = event "A"; event "B"; f()
let main () = f()


(* Property to be checked: "Every finite trace contains infinitely many B's."
   Their paper also mentions the property "Every finite trace generated by f ends with B".
   This property can be separately checked by an ordinary safety property checker
   (e.g. by plain MoCHi)
  *)
(*{SPEC}
   fairness: (B, Never)
{SPEC}*)
