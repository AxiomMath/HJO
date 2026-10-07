/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ColouringStep
public import HJO.Shuffle.SweepWordV0

/-! # The partial sweep word is a function of the trace

`HJO.Mellit.dsc` sums one term per *trace* and picks a path realising each; the object is well
defined only because the partial sweep word does not see the rest of the path. That is this file:
two above-diagonal paths with the same trace at a level have the same partial word there.

The trace records, at each swept point above the level, the point, the event type and the live count
to the right — but **not** the width, which the event operator also reads. The width is recovered as
follows: the highest-ranked swept point has width `0`, and each step down the rank order changes the
width by `+1` at a type-`A` event, `-1` at type `B` and `0` otherwise, so the widths above the level
are a function of the event types above the level.

## Main results

* `HJO.Mellit.sweptAbove_eq_of_levelTrace_eq`, `HJO.Mellit.eventType_eq_of_levelTrace_eq`,
  `HJO.Mellit.sweepRight_eq_of_levelTrace_eq` — the three data the trace records.
* `HJO.Mellit.sweepWidth_eq_of_levelTrace_eq` — the datum it does not record, recovered.
* `HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq`.

## Implementation notes

`0 < a` and `0 < N` are carried, though left implicit informally. Both come from
`HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent`, whose Lean form
`HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent` needs them: the rank is injective on the swept
region only for `0 < a`, and the width bookkeeping at a rank-adjacent pair is read against a
rectangle with a row.

The base case is "the highest-ranked point of `Sw(P̂)` has width `0`", which is about
the whole swept region and not only the part above the level. The two agree, by
`HJO.Mellit.maximal_of_maximal_sweptAbove` — a swept point outranking the highest one *above* the
level would itself be above the level — and that is what lets one point identified by the trace
alone serve as the base for both paths, whose swept regions below the level may well differ.

## References

This file concerns `HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq`, using
`HJO.Mellit.partialSweepWord`, `HJO.Mellit.levelTrace`, `HJO.Mellit.sweepOperator`,
`HJO.Paths.sweepWidth`, `HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent` and
`HJO.Mellit.sweepWord_mem_piece_zero`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### What the trace records -/

/-- **Two paths with the same trace sweep the same points above the level.** -/
theorem sweptAbove_eq_of_levelTrace_eq {η : ℚ} {y₁ y₂ : Heights a b N}
    (h : levelTrace y₁ η = levelTrace y₂ η) : sweptAbove y₁ η = sweptAbove y₂ η :=
  Finset.ext fun _ =>
    ⟨fun hP => mem_sweptAbove_of_levelTrace_eq h hP,
      fun hP => mem_sweptAbove_of_levelTrace_eq h.symm hP⟩

/-- The event type and the live count to the right at a swept point above the level are the second
and third components the trace records, so two paths with the same trace agree on both. -/
theorem eventType_and_sweepRight_eq_of_levelTrace_eq {η : ℚ} {y₁ y₂ : Heights a b N}
    (h : levelTrace y₁ η = levelTrace y₂ η) {P : ℕ × ℕ} (hP : P ∈ sweptAbove y₁ η) :
    eventType y₁ P = eventType y₂ P ∧ sweepRight y₁ P = sweepRight y₂ P := by
  have h1 : (P, eventType y₁ P, sweepRight y₁ P) ∈ levelTrace y₂ η := by
    rw [← h, levelTrace]
    exact Finset.mem_image_of_mem _ hP
  rw [levelTrace, Finset.mem_image] at h1
  obtain ⟨Q, -, hQ'⟩ := h1
  have hfst : Q = P := congrArg Prod.fst hQ'
  have hev : eventType y₂ Q = eventType y₁ P := congrArg (fun t => t.2.1) hQ'
  have hright : sweepRight y₂ Q = sweepRight y₁ P := congrArg (fun t => t.2.2) hQ'
  rw [hfst] at hev hright
  exact ⟨hev.symm, hright.symm⟩

/-- The event type at a swept point above the level is recorded by the trace. -/
theorem eventType_eq_of_levelTrace_eq {η : ℚ} {y₁ y₂ : Heights a b N}
    (h : levelTrace y₁ η = levelTrace y₂ η) {P : ℕ × ℕ} (hP : P ∈ sweptAbove y₁ η) :
    eventType y₁ P = eventType y₂ P :=
  (eventType_and_sweepRight_eq_of_levelTrace_eq h hP).1

/-- The live count to the right at a swept point above the level is recorded by the trace. -/
theorem sweepRight_eq_of_levelTrace_eq {η : ℚ} {y₁ y₂ : Heights a b N}
    (h : levelTrace y₁ η = levelTrace y₂ η) {P : ℕ × ℕ} (hP : P ∈ sweptAbove y₁ η) :
    sweepRight y₁ P = sweepRight y₂ P :=
  (eventType_and_sweepRight_eq_of_levelTrace_eq h hP).2

/-! ### What the trace does not record: the width -/

/-- **A swept point above the level that nothing above the level outranks is maximal in the whole
swept region.** A swept point of higher rank would outrank the level too, so it would be one of the
points compared already. -/
theorem maximal_of_maximal_sweptAbove {η : ℚ} {y : Heights a b N} {P : ℕ × ℕ}
    (hP : P ∈ sweptAbove y η)
    (hmax : ∀ R ∈ sweptAbove y η, pointRank a b N R ≤ pointRank a b N P) :
    ∀ R ∈ sweptRegion y, abovePointRank a b N R.1 R.2 ≤ abovePointRank a b N P.1 P.2 := by
  intro R hR
  by_contra hcon
  have hlt : pointRank a b N P < pointRank a b N R := not_le.1 hcon
  have hPη : η < ((pointRank a b N P : ℤ) : ℚ) := (Finset.mem_filter.1 hP).2
  have hRη : η < ((pointRank a b N R : ℤ) : ℚ) := hPη.trans (by exact_mod_cast hlt)
  exact absurd (hmax R (Finset.mem_filter.2 ⟨hR, hRη⟩)) (not_le.2 hlt)

/-- **The width at a swept point above the level is a function of the trace.** The recovery of the
one datum the trace does not carry: downwards from the highest-ranked swept point, where the width
is `0`, each rank-adjacent step changes the width by an amount read off the event type at the point
above, and the event types above the level are recorded.

The induction is on the number of swept points above the level that outrank `P`; the point `Q`
realising the least such rank is rank-adjacent to `P` in *both* swept regions, since a point of
either region with rank between them would outrank the level and so lie in the common set. -/
theorem sweepWidth_eq_of_levelTrace_eq (ha : 0 < a) (hN : 0 < N) {η : ℚ}
    {y₁ y₂ : Heights a b N} (hy₁ : IsAboveDiagonal y₁) (hy₂ : IsAboveDiagonal y₂)
    (h : levelTrace y₁ η = levelTrace y₂ η) :
    ∀ P ∈ sweptAbove y₁ η, sweepWidth y₁ P = sweepWidth y₂ P := by
  have hset := sweptAbove_eq_of_levelTrace_eq h
  have key : ∀ n : ℕ, ∀ P ∈ sweptAbove y₁ η,
      #{R ∈ sweptAbove y₁ η | pointRank a b N P < pointRank a b N R} = n →
      sweepWidth y₁ P = sweepWidth y₂ P := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P hP hn
      have hPη : η < ((pointRank a b N P : ℤ) : ℚ) := (Finset.mem_filter.1 hP).2
      have hP₂ : P ∈ sweptAbove y₂ η := by rw [← hset]; exact hP
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · have hmax : ∀ R ∈ sweptAbove y₁ η, pointRank a b N R ≤ pointRank a b N P := by
          intro R hR
          by_contra hcon
          have hcard : 0 < #{R ∈ sweptAbove y₁ η | pointRank a b N P < pointRank a b N R} :=
            Finset.card_pos.2 ⟨R, Finset.mem_filter.2 ⟨hR, not_le.1 hcon⟩⟩
          omega
        have hmax₂ : ∀ R ∈ sweptAbove y₂ η, pointRank a b N R ≤ pointRank a b N P := by
          rw [← hset]; exact hmax
        rw [sweepWidth_eq_zero_of_maximal hy₁ (maximal_of_maximal_sweptAbove hP hmax),
          sweepWidth_eq_zero_of_maximal hy₂ (maximal_of_maximal_sweptAbove hP₂ hmax₂)]
      · obtain ⟨Q, hQS, hQmin⟩ :=
          Finset.exists_min_image
            {R ∈ sweptAbove y₁ η | pointRank a b N P < pointRank a b N R}
            (pointRank a b N) (Finset.card_pos.1 (by omega))
        obtain ⟨hQ, hQlt⟩ := Finset.mem_filter.1 hQS
        have hQ₂ : Q ∈ sweptAbove y₂ η := by rw [← hset]; exact hQ
        have hadj₁ : RankAdjacent a b N y₁ P Q := by
          refine ⟨(Finset.mem_filter.1 hP).1, (Finset.mem_filter.1 hQ).1, hQlt,
            fun R hR hR' => ?_⟩
          have hRη : η < ((pointRank a b N R : ℤ) : ℚ) := hPη.trans (by exact_mod_cast hR'.1)
          exact absurd (hQmin R (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hR, hRη⟩, hR'.1⟩))
            (not_le.2 hR'.2)
        have hadj₂ : RankAdjacent a b N y₂ P Q := by
          refine ⟨(Finset.mem_filter.1 hP₂).1, (Finset.mem_filter.1 hQ₂).1, hQlt,
            fun R hR hR' => ?_⟩
          have hRη : η < ((pointRank a b N R : ℤ) : ℚ) := hPη.trans (by exact_mod_cast hR'.1)
          have hR₁ : R ∈ sweptAbove y₁ η := by
            rw [hset]; exact Finset.mem_filter.2 ⟨hR, hRη⟩
          exact absurd (hQmin R (Finset.mem_filter.2 ⟨hR₁, hR'.1⟩)) (not_le.2 hR'.2)
        have hlt : #{R ∈ sweptAbove y₁ η | pointRank a b N Q < pointRank a b N R} < n := by
          rw [← hn]
          refine Finset.card_lt_card ⟨fun R hR => ?_, fun hsub => ?_⟩
          · obtain ⟨hR1, hR2⟩ := Finset.mem_filter.1 hR
            exact Finset.mem_filter.2 ⟨hR1, hQlt.trans hR2⟩
          · exact absurd (Finset.mem_filter.1 (hsub hQS)).2 (lt_irrefl _)
        have hIH : sweepWidth y₁ Q = sweepWidth y₂ Q := ih _ hlt Q hQ rfl
        have he₁ := sweepWidth_sub_sweepWidth_of_rankAdjacent hy₁ ha hN hadj₁
        have he₂ := sweepWidth_sub_sweepWidth_of_rankAdjacent hy₂ ha hN hadj₂
        rw [eventType_eq_of_levelTrace_eq h hQ, hIH] at he₁
        have hcomb := he₁.trans he₂.symm
        omega
  exact fun P hP => key _ P hP rfl

/-! ### The partial word -/

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The partial word is a function of the trace.**
`HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq`: two above-diagonal paths with the same trace at
an admissible level have the same partial sweep word there.

The trace fixes the index set of the product and its rank listing; at each point of it, the event
type and the live count to the right are recorded outright and the width is recovered by
`HJO.Mellit.sweepWidth_eq_of_levelTrace_eq`. Those three are all that `HJO.Mellit.sweepOperator`
reads, so the two products are factor by factor the same. -/
@[hjo "lem_colouring_word_trace"]
theorem partialSweepWord_eq_of_levelTrace_eq (q u : L) (ha : 0 < a) (hN : 0 < N) {η : ℚ}
    {y₁ y₂ : Heights a b N} (hy₁ : IsAboveDiagonal y₁) (hy₂ : IsAboveDiagonal y₂)
    (h : levelTrace y₁ η = levelTrace y₂ η) :
    partialSweepWord q u y₁ η = partialSweepWord q u y₂ η := by
  have hset := sweptAbove_eq_of_levelTrace_eq h
  rw [partialSweepWord, partialSweepWord, ← hset]
  congr 1
  refine List.map_congr_left fun P hP => ?_
  have hPmem : P ∈ sweptAbove y₁ η := mem_sortByRank.1 hP
  unfold sweepOperator
  rw [eventType_eq_of_levelTrace_eq h hPmem, sweepRight_eq_of_levelTrace_eq h hPmem,
    sweepWidth_eq_of_levelTrace_eq ha hN hy₁ hy₂ h P hPmem]

end HJO.Mellit
