open Brzozowski ;
open Llk_regexps ;

module Token = Llk_regexps.PatternBaseToken ;

(*
for i = 1 to m:
  if final(i):
    B[i] := ε
  else:
    B[i] := ∅
and 𝐴:

for i = 1 to m:
  for j = 1 to m:
    for a in Σ:
      if trans(i, a, j):
        A[i,j] := a
      else:
        A[i,j] := ∅
and then the solving:

for n = m decreasing to 1:
  B[n] := star(A[n,n]) . B[n]
  for j = 1 to n:
    A[n,j] := star(A[n,n]) . A[n,j];
  for i = 1 to n:
    B[i] += A[i,n] . B[n]
    for j = 1 to n:
      A[i,j] += A[i,n] . A[n,j]
the final expression is then:

e := B[1]
 *)
type state_t =
  {
    num : int
  ; final: option Token.t
  ; transitions: list (Token.t * int)
  }
;
type dfa_t =
  {
    initial : int
  ; states :  list state_t
  }
;
