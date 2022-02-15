
value parse_flag pfun = parser [
  [: _ = pfun :] -> True
| [: :] -> False
]
;

value parse_left_assoc lhs restrhs combiner = parser [
  [: x = lhs ; rv = parser [ [: y = restrhs :] -> combiner x y | [: :] -> x ] :] -> rv 
]
;
