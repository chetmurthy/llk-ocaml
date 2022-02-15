
value parse_flag pfun = parser [
  [: _ = pfun :] -> True
| [: :] -> False
]
;
