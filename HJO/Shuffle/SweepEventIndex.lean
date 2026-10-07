/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepHookCount
public meta import HJO.Attr

/-! # What the two sums of `HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount` are
indexed by

`HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount` regroups the crossed-pair count
of `HJO.Paths.aboveHookCount_eq_card_crossingPairs` by the swept point at which each pair is read
off, and its display is a sum over the type-`A`-or-`D` points plus a sum over the type-`A`-or-`C`
points. To turn either sum into a sum over the *steps* of the path — which is what the pair count is
indexed by — one needs to know which swept points those two classes are.

For the type-`A`-or-`C` points that is already proved: they are exactly the heads of north steps,
`HJO.Paths.isSweepHead_iff_eventType`. This file settles the other class, and it is the one with a
surprise in it.

## Main results

* `HJO.Paths.eventType_eq_A_or_D_iff`: a swept point has type `A` or `D` exactly when it is the top
  of a column — `P = (s, ŷ_{s+1})` with `s < aN`, that is `HJO.Paths.eastLeft y s` — **or** is the
  corner `(aN, bN)`.
* `HJO.Paths.sweepRight_corner`: the corner contributes nothing, `a_{P̂}(aN, bN) = 0`.

## Implementation notes

### The corner is a type-`D` point and is not the top of any column

The type-`A`-or-`D` points are the swept points whose *outgoing* letter is `E`, and on the swept
region that forces the ordinate to be `ŷ⁺_x`. For `x < aN` that says `P = eastLeft y x`, the left
endpoint of the east step there. But `x = aN` also passes: there `ŷ⁺_{aN} = bN = ŷ_{aN}`, so the
only swept point in that column is the corner `(aN, bN)`, whose outgoing letter is `E` because the
guard `x + 1 ≤ aN` fails — see the "truncated subtraction in the outgoing letter" note of
`HJO/Shuffle/Sweep.lean`, which is where that guard is live.

So the first sum of `HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount` is **not** a
sum over the east steps: it is a sum over the east steps plus one extra term at the corner.
`HJO.Paths.sweepRight_corner` is what makes that term harmless — every live north step has column
`< aN`, so none is strictly right of the corner and `a_{P̂}` vanishes there. Without that lemma the
reindexing of the first sum to `∑_{s < aN} a_{P̂}(eastLeft y s)` is not just unproved but off by the
corner's value.

## References

A. Mellit, *Toric braids and `(m, n)`-parking
functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-- **A swept point has type `A` or `D` exactly when it is the top of a column, or the corner.**
Those two types are the ones whose outgoing letter is `E`, which on the swept region forces the
ordinate up to `ŷ⁺_x`; for `x < aN` that is `HJO.Paths.eastLeft y x`, and for `x = aN` it is the
corner `(aN, bN)`, whose outgoing letter is `E` because the guard `x + 1 ≤ aN` fails.

The corner is therefore an index of the first sum of
`HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount` that is not the left endpoint of
any east step; `HJO.Paths.sweepRight_corner` is what makes it contribute nothing. -/
theorem eventType_eq_A_or_D_iff {y : Heights a b N} (hy : IsAboveDiagonal y) {P : ℕ × ℕ}
    (hP : P ∈ sweptRegion y) :
    (eventType y P = EventType.A ∨ eventType y P = EventType.D) ↔
      ((P.1 < a * N ∧ P.2 = ht y (P.1 + 1)) ∨ (P.1 = a * N ∧ P.2 = b * N)) := by
  obtain ⟨hx, -, hup⟩ := mem_sweptRegion.1 hP
  have hmono : ht y P.1 ≤ ht y (P.1 + 1) := ht_mono hy.2.2.1 (Nat.le_succ _)
  rcases Nat.lt_or_ge P.1 (a * N) with hlt | hge
  · rw [eventType]
    split_ifs <;> simp_all <;> omega
  · have hx0 : P.1 = a * N := le_antisymm hx hge
    have htop : ht y (P.1 + 1) = b * N := by rw [hx0]; exact ht_of_gt y (by omega)
    have hbot : ht y P.1 = b * N := by rw [hx0]; exact hy.2.1
    have hP2 : P.2 ≤ ht y P.1 := by omega
    have hbne : ¬(P.1 + 1 ≤ a * N) := by omega
    rw [eventType]
    split_ifs <;> simp_all <;> omega

/-- **The corner has no live north step to its right**, so it contributes `0` to the first sum of
`HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount`. Every north step has column
`< aN` by `HJO.Paths.northSteps`, and the count `a_{P̂}` asks for a live step of column strictly
greater than the point's, which at the corner is `aN`. -/
theorem sweepRight_corner (y : Heights a b N) : sweepRight y (a * N, b * N) = 0 := by
  rw [sweepRight, card_eq_zero]
  refine filter_eq_empty_iff.2 fun {u} hu hcon => ?_
  have h1 := (mem_northSteps_iff.1 (liveSteps_subset y _ hu)).1
  simp only at hcon
  omega

end HJO.Paths
