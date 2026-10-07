/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepEventIndex
public meta import HJO.Attr

/-! # The marked pairs are the type-`C` events

`HJO.Paths.sum_sweepRight_add_leftEastCount_A_eq_sum_sweepWidth_sub_one_B` balances the three counts
`#𝒜(P̂)`, `#S(P̂)` and the widths against the event types, and one of its inputs is that `#S(P̂)` is
simply the number of type-`C` swept points. That is what this file proves.

The identification is immediate from two lemmas proved earlier. A type-`C` point is a foot
(`HJO.Paths.mem_northSteps_iff_eventType`, types `B` and `C`), and among the feet type `C` is being
the upper member of a marked pair (`HJO.Paths.eventType_stepFoot_eq_C_iff`). So the type-`C` points
are the images of the marked pairs under "take the upper member", and that map is injective because
a marked pair's lower member is determined by its upper one — `HJO.Paths.sweepMarked` asks for
`t = s + 1`.

## Main results

* `HJO.Paths.card_sweepMarked_eq_card_filter_eventType_C`.

## Implementation notes

The usual argument goes through the rank-order listing `u_1, …, u_{bN}` and observes that for each
`j` there is at most one `i` with `(i,j) ∈ S(P̂)`. On the height indexing that observation is the
second clause of `HJO.Paths.sweepMarked` read directly: `t = s + 1` determines `s` from `t`, with no
appeal to the listing being injective. So the injectivity half of the bijection is `omega` on that
clause, and the surjectivity half is `HJO.Paths.eventType_stepFoot_eq_C_iff`.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-- **`#S(P̂)` is the number of type-`C` swept points.**
`HJO.Paths.card_sweepMarked_eq_card_filter_eventType_C`.

The type-`C` points are exactly the feet that are upper members of marked pairs: a type-`C` point is
a foot by `HJO.Paths.mem_northSteps_iff_eventType`, and among the feet type `C` is being a marked
pair's upper member by `HJO.Paths.eventType_stepFoot_eq_C_iff`. Taking the upper member is injective
on `HJO.Paths.sweepMarked` because that predicate asks for `t = s + 1`, which recovers `s`. -/
@[hjo "lem_swb_marked_count"]
theorem card_sweepMarked_eq_card_filter_eventType_C {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    #(sweepMarked y) = #{P ∈ sweptRegion y | eventType y P = EventType.C} := by
  have himg : {P ∈ sweptRegion y | eventType y P = EventType.C}
      = (sweepMarked y).image fun p => stepFoot y p.2 := by
    ext P
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hP, hC⟩
      have hmem : P ∈ northSteps y :=
        (mem_northSteps_iff_eventType hP).2 (Or.inr hC)
      rw [northSteps_eq_image hy] at hmem
      obtain ⟨t, -, rfl⟩ := mem_image.1 hmem
      obtain ⟨s, hs⟩ := (eventType_stepFoot_eq_C_iff hy t).1 hC
      exact ⟨(s, t), hs, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      have hmem : stepFoot y p.2 ∈ northSteps y := by
        rw [northSteps_eq_image hy]
        exact mem_image_of_mem _ (mem_univ p.2)
      refine ⟨(mem_sweptRegion_of_mem_northSteps hy hmem).1, ?_⟩
      exact (eventType_stepFoot_eq_C_iff hy p.2).2 ⟨p.1, hp⟩
  rw [himg, card_image_of_injOn]
  intro p hp q hq h
  have h2 : p.2 = q.2 := stepFoot_injective y h
  simp only [mem_coe, sweepMarked, mem_filter, mem_univ, true_and] at hp hq
  have h1 : (p.1 : ℕ) = (q.1 : ℕ) := by
    have := hp.2
    have := hq.2
    omega
  rw [Prod.ext_iff]
  exact ⟨Fin.val_injective h1, h2⟩

end HJO.Paths
