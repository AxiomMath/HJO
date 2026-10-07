/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidCDLetterRank

/-! # The window hypothesis of the type-`C` letter, discharged two ways

`HJO.Mellit.Isolates.entryRank_positionPair_snd_of_eventType_C` and the letter it produces carry a
window hypothesis `hwin : rk̂(P) < ηlo + (b(aN+1)N - 1)`, which is what stops the fractional part
wrapping. Reading that hypothesis as a limit of the type-`C` clause invites the conclusion that the
clause has a gap the type-`A` clause does not. That conclusion is wrong, and this file states the
reason so that it can be checked rather than argued.

## The two dischargers, and either alone suffices

* `HJO.Mellit.Isolates.pointRank_lt_add_of_eventType_C_of_lt` needs `a < b`, and
  `HJO.Mellit.shuffle_of_lhs_and_induction` **quantifies over `a < b`**. So wherever that theorem
  uses the clause the hypothesis is supplied by its own `a < b` and costs nothing.
* `HJO.Mellit.Isolates.pointRank_lt_add_of_eventType_C_of_succ` needs `ηhi = ηlo + 1` and **uses no
  relation between `a` and `b` at all**. That is the hypothesis
  `HJO.Mellit.Isolates.zCount_sub_eq_zero_of_eventType_C` already carries.

  **Consecutive admissible levels are not what the sweep iteration presents.**
  `HJO.Mellit.consecutive_levels_unavailable_two_three_one` (`HJO/Shuffle/MellitFloorStepGap.lean`)
  shows that the chain the sweep iteration walks is **not** consecutive. At `(a,b,N) = (2,3,1)`
  every rank is `6Y - 8X`, hence **even**, so the admissible above-floor level `9/2` has **no**
  bracketing pair with gap `≤ 1` at all -- and `9/2` is the first stop after `7/2`, the level of the
  worked example in `HJO/Shuffle/MellitThm58Iteration.lean`. So a clause restricted to
  `ηhi = ηlo + 1` is **vacuous exactly where the iteration needs a drop**. The `ηhi = ηlo + 1` route
  to the window hypothesis is therefore sound as a *lemma* but useless as the *iteration's*
  discharger, and only the `a < b` route above is load-bearing.

So the excluded configuration -- `b ≤ a` together with a level gap exceeding `b(aN+1)N - 1` -- is
outside the quantification of `HJO.Mellit.shuffle_of_lhs_and_induction` **on the `a < b` route**,
which is the one that matters. **What remains true, and is the precise form of the limit:** the
type-`C` letter identification is not proved for an arbitrary `HJO.Mellit.Isolates` pair in
isolation, whereas the type-`A` clause is. That is a statement about the standalone generality of a
lemma, not about `HJO.Mellit.shuffle_of_lhs_and_induction`.

## What this file does NOT do

It does not discharge `htrain`, and it does not close the type-`C` clause. Both theorems below are
the clause with one hypothesis traded for another; the residual braid identity is untouched and is
stated at `HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_train`.

## References

The definitions and results this file concerns:
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, `HJO.Braid.specialBraid` and
`HJO.Mellit.sweepOperator`.
-/

@[expose] public section

namespace HJO.Mellit.Isolates

open Finset HJO.Sweep HJO.Paths HJO.Braid

variable {a b N X Y : ℕ} {ηlo ηhi : ℚ}

/-- **The type-`C` letter, with the window hypothesis traded for `a < b`** -- the relation
`HJO.Mellit.shuffle_of_lhs_and_induction` quantifies over. So in that theorem the window costs
nothing: `a < b` is already among its hypotheses.

This is `HJO.Mellit.Isolates.braidStep_positionPair_snd_of_eventType_C` with
`HJO.Mellit.Isolates.pointRank_lt_add_of_eventType_C_of_lt` substituted, and it is stated so that
"the window is free here" is a checked statement rather than a remark. -/
theorem braidStep_positionPair_snd_of_eventType_C_of_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : a < b)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y)) :
    braidStep (sweepTheta a b N)
        (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
          (braidDataOfColouring a b N y ηhi k).2).2 j
      = braidTrainDown k 1 k * braidYtilde k k :=
  braidStep_positionPair_snd_of_eventType_C ha hb hN hI hηlo hy hev hk j hj
    (pointRank_lt_add_of_eventType_C_of_lt ha hN hab hI hev)

/-- **The type-`C` letter, with the window hypothesis traded for consecutive levels** -- and this
route uses **no relation between `a` and `b` whatever**.

`ηhi = ηlo + 1` is the hypothesis `HJO.Mellit.Isolates.zCount_sub_eq_zero_of_eventType_C` already
carries, so this is the route on which the type-`C` letter identification has no parameter
restriction at all. It is not the route the sweep iteration can use: its level pairs are not
consecutive in general (`HJO.Mellit.consecutive_levels_unavailable_two_three_one`). -/
theorem braidStep_positionPair_snd_of_eventType_C_of_succ (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hstep : ηhi = ηlo + 1)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y)) :
    braidStep (sweepTheta a b N)
        (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
          (braidDataOfColouring a b N y ηhi k).2).2 j
      = braidTrainDown k 1 k * braidYtilde k k :=
  braidStep_positionPair_snd_of_eventType_C ha hb hN hI hηlo hy hev hk j hj
    (pointRank_lt_add_of_eventType_C_of_succ ha hb hN hI hstep)

end HJO.Mellit.Isolates

end
