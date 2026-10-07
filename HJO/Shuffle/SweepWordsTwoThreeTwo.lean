/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepInductionInstanceTwo
public import HJO.Shuffle.SweepOperatorValuesTwoThree

/-! # The four sweep words of the `4 × 6` rectangle at `c_{(1,1)}`

`HJO.Mellit.filter_aboveDiagonal_compColouring_two_three_one_one` names the four above-diagonal
`(4,6)`-paths whose colouring at the level `9/2` is `c_{(1,1)}`. This file peels each of their
partial sweep words into an explicit product of event operators of `HJO.Mellit.sweepOperator`.

## The peeling, and the gaps in it

`HJO.Mellit.partialSweepWord_eq_sweepOperator_mul` lowers the level past one swept point at a time,
and asks that the window it crosses contain exactly one *lattice* rank — not one swept rank. The
`4 × 6` rectangle has thirty-five ranks and each of the four paths sweeps at most ten of them, so
between two consecutive swept points a window may enclose a rank the path does not sweep. That is
what `HJO.Mellit.partialSweepWord_skip` is for: where no swept point of the path outranks `m`
without also outranking `n`, the two partial words coincide, because the index set
`HJO.Mellit.sweptAbove` is literally the same `Finset`. Three of the four words need it, at the
ranks `51` and `60`.

## References

This file computes with `HJO.Mellit.sweepOperator`, `HJO.Mellit.partialSweepWord`,
`HJO.Mellit.partialSweepWord_eq_sweepOperator_mul` and `HJO.Mellit.dsc`.
-/

@[expose] public section

namespace HJO.Mellit

open Finset HJO.Paths HJO.Sweep

/-! ### The ranks of the `4 × 6` rectangle -/

/-- **The thirty-five ranks of the `4 × 6` rectangle.** Every lattice point with `0 ≤ x ≤ 4` and
`0 ≤ y ≤ 6` has one of these above-diagonal ranks; the isolating windows of the four words are
checked against this list. -/
theorem rank_mem_two_three_two (Q : ℕ × ℕ) (h1 : Q.1 ≤ 4) (h2 : Q.2 ≤ 6) :
    pointRank 2 3 2 Q ∈ ({-116, -96, -87, -76, -67, -58, -56, -47, -38, -36, -29, -27, -18, -16,
      -9, -7, 0, 2, 4, 11, 13, 20, 22, 31, 33, 40, 42, 51, 60, 62, 71, 80, 91, 100,
      120} : Finset ℤ) := by
  obtain ⟨x, y⟩ := Q
  simp only at h1 h2
  interval_cases x <;> interval_cases y <;> decide

/-- **An isolating window of the `4 × 6` rectangle.** Between the half-integer levels `m + 1/2` and
`n + 1/2` the only rank of the rectangle is `r`, which is the isolation hypothesis of
`HJO.Mellit.partialSweepWord_eq_sweepOperator_mul`. -/
theorem iso_of_window_two {m n r : ℤ}
    (hr : ∀ z ∈ ({-116, -96, -87, -76, -67, -58, -56, -47, -38, -36, -29, -27, -18, -16,
        -9, -7, 0, 2, 4, 11, 13, 20, 22, 31, 33, 40, 42, 51, 60, 62, 71, 80, 91, 100,
        120} : Finset ℤ), m < z → z ≤ n → z = r)
    {P : ℕ × ℕ} (hPr : pointRank 2 3 2 P = r) :
    ∀ Q : ℕ × ℕ, Q.1 ≤ 2 * 2 → Q.2 ≤ 3 * 2 →
      ((m : ℚ) + 1 / 2) < ((pointRank 2 3 2 Q : ℤ) : ℚ) →
      ((pointRank 2 3 2 Q : ℤ) : ℚ) < ((n : ℚ) + 1 / 2) →
      pointRank 2 3 2 Q = pointRank 2 3 2 P := by
  intro Q hQ1 hQ2 hlo hup
  rw [hPr]
  exact hr _ (rank_mem_two_three_two Q (by omega) (by omega)) (lt_of_half_lt hlo)
    (le_of_lt_half hup)

/-- The separating level of `N = 2` is `9/2`, the half-integer above the rank `4`. -/
theorem sepLevel_two_two : sepLevel 2 2 = ((4 : ℤ) : ℚ) + 1 / 2 := by
  rw [sepLevel]
  norm_num

section Words

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- Above the top rank of a path the partial word is empty. -/
theorem partialSweepWord_top_two (q u : L) {y : Heights 2 3 2} {m : ℤ}
    (h : ∀ P ∈ sweptRegion y, pointRank 2 3 2 P ≤ m) :
    partialSweepWord q u y (((m : ℚ)) + 1 / 2) = 1 := by
  refine partialSweepWord_of_forall_le q u y _ fun P hP => ?_
  have hle : ((pointRank 2 3 2 P : ℤ) : ℚ) ≤ ((m : ℤ) : ℚ) := by exact_mod_cast h P hP
  linarith

/-- One step of the peeling at `(a,b) = (2,3)`, `N = 2`. -/
theorem partialSweepWord_step_two (q u : L) {y : Heights 2 3 2} {P : ℕ × ℕ} {m n r : ℤ}
    (hr : ∀ z ∈ ({-116, -96, -87, -76, -67, -58, -56, -47, -38, -36, -29, -27, -18, -16,
        -9, -7, 0, 2, 4, 11, 13, 20, 22, 31, 33, 40, 42, 51, 60, 62, 71, 80, 91, 100,
        120} : Finset ℤ), m < z → z ≤ n → z = r)
    (hPr : pointRank 2 3 2 P = r) (hlo : ((m : ℚ) + 1 / 2) < (r : ℚ))
    (hup : ((r : ℚ)) < ((n : ℚ) + 1 / 2)) (hPmem : P ∈ sweptRegion y) :
    partialSweepWord q u y ((m : ℚ) + 1 / 2)
      = sweepOperator q u y P * partialSweepWord q u y ((n : ℚ) + 1 / 2) := by
  refine partialSweepWord_eq_sweepOperator_mul q u (by omega)
    (isAdmissibleLevel_int_add_half n) ?_ ?_ (iso_of_window_two hr hPr) hPmem
  · rw [hPr]; exact_mod_cast hlo
  · rw [hPr]; exact_mod_cast hup

/-- **Crossing a rank the path does not sweep changes nothing.** Where no point of the swept region
outranks `m` without also outranking `n`, the two index sets `HJO.Mellit.sweptAbove` are the same
`Finset` and the two partial words are equal by definition. This is what lets the peeling step
past a
lattice rank of the rectangle at which the path has no event — which
`HJO.Mellit.partialSweepWord_eq_sweepOperator_mul` cannot do, its isolation hypothesis ranging over
all lattice points and not over the swept ones. -/
theorem partialSweepWord_skip (q u : L) {a b N : ℕ} {y : Heights a b N} {m n : ℤ} (hmn : m ≤ n)
    (h : ∀ P ∈ sweptRegion y, m < pointRank a b N P → n < pointRank a b N P) :
    partialSweepWord q u y ((m : ℚ) + 1 / 2) = partialSweepWord q u y ((n : ℚ) + 1 / 2) := by
  have hmn' : ((m : ℤ) : ℚ) ≤ ((n : ℤ) : ℚ) := by exact_mod_cast hmn
  have hset : sweptAbove y ((m : ℚ) + 1 / 2) = sweptAbove y ((n : ℚ) + 1 / 2) := by
    ext P
    simp only [sweptAbove, Finset.mem_filter, and_congr_right_iff]
    intro hP
    refine ⟨fun hlt => ?_, fun hlt => by linarith⟩
    have hn := h P hP (lt_of_half_lt hlt)
    have hn1 : n + 1 ≤ pointRank a b N P := by omega
    have : ((n : ℤ) : ℚ) + 1 ≤ ((pointRank a b N P : ℤ) : ℚ) := by exact_mod_cast hn1
    linarith
  rw [partialSweepWord, partialSweepWord, hset]

/-! ### The word of `(0,2,3,5,6)`

The only one of the four whose swept ranks are *all* the lattice ranks above the level, so the
peeling needs no skip. Eight events: four raisings up to width `4`, two corners there, and two
lowerings back. -/

set_option maxRecDepth 100000 in
/-- **The word of `(0,2,3,5,6)`:**
`d_-^{(3)}d_-^{(4)}q^{-3}Δ^{(4)}q^{-1}Δ^{(4)}d_+^{(3)}d_+^{(2)}d_+^{(1)}d_+^{(0)}`. -/
theorem partialSweepWord_baseTwoThreeTwoA (q u : L) :
    partialSweepWord q u baseTwoThreeTwoA (sepLevel 2 2)
      = dminus q 3 * (dminus q 4 * ((((q : L) ^ (-3 : ℤ)) • corner q 4)
          * ((((q : L) ^ (-1 : ℤ)) • corner q 4)
            * (dplus q 3 * (dplus q 2 * (dplus q 1 * (dplus q 0 * 1))))))) := by
  have op11 : sweepOperator q u baseTwoThreeTwoA ((1, 2) : ℕ × ℕ) = dminus q 3 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoA ((1, 2) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth baseTwoThreeTwoA ((1, 2) : ℕ × ℕ) = 3 from by decide]
  have op13 : sweepOperator q u baseTwoThreeTwoA ((3, 5) : ℕ × ℕ) = dminus q 4 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoA ((3, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth baseTwoThreeTwoA ((3, 5) : ℕ × ℕ) = 4 from by decide]
  have op20 : sweepOperator q u baseTwoThreeTwoA ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-3 : ℤ)) • corner q 4 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoA ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth baseTwoThreeTwoA ((0, 1) : ℕ × ℕ) = 4 from by decide,
      show sweepRight baseTwoThreeTwoA ((0, 1) : ℕ × ℕ) = 3 from by decide]
    norm_num
  have op22 : sweepOperator q u baseTwoThreeTwoA ((2, 4) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 4 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoA ((2, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth baseTwoThreeTwoA ((2, 4) : ℕ × ℕ) = 4 from by decide,
      show sweepRight baseTwoThreeTwoA ((2, 4) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op31 : sweepOperator q u baseTwoThreeTwoA ((1, 3) : ℕ × ℕ) = dplus q 3 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoA ((1, 3) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth baseTwoThreeTwoA ((1, 3) : ℕ × ℕ) = 3 from by decide]
  have op33 : sweepOperator q u baseTwoThreeTwoA ((3, 6) : ℕ × ℕ) = dplus q 2 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoA ((3, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth baseTwoThreeTwoA ((3, 6) : ℕ × ℕ) = 2 from by decide]
  have op40 : sweepOperator q u baseTwoThreeTwoA ((0, 2) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoA ((0, 2) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth baseTwoThreeTwoA ((0, 2) : ℕ × ℕ) = 1 from by decide]
  have op42 : sweepOperator q u baseTwoThreeTwoA ((2, 5) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoA ((2, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth baseTwoThreeTwoA ((2, 5) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11) (by decide)
      (by decide)
      (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13) (by decide)
      (by decide)
      (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20) (by decide)
      (by decide)
      (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22) (by decide)
      (by decide)
      (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31) (by decide)
      (by decide)
      (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33) (by decide)
      (by decide)
      (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40) (by decide)
      (by decide)
      (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42) (by decide)
      (by decide)
      (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 42) (by decide),
    op11, op13, op20, op22, op31, op33, op40, op42]

/-! ### The word of `(0,2,3,6,6)` -/

set_option maxRecDepth 100000 in
/-- **The word of `(0,2,3,6,6)`:** nine events, with one type-`E` supplying the `u`, one type-`D`
supplying `q^0 = 1`, and the widths reaching only `3`. -/
theorem partialSweepWord_baseTwoThreeTwoB (q u : L) :
    partialSweepWord q u baseTwoThreeTwoB (sepLevel 2 2)
      = (dminus q 3) * ((u • (1 : Module.End L (Total L))) * ((((q : L) ^ (-2 : ℤ)) • corner q 3) *
          ((corner q 3) * ((dplus q 2) * (((1 : Module.End L (Total L))) * ((dplus q 1) *
          ((corner q 1) * ((dplus q 0) * ((1 : Module.End L (Total L))))))))))) := by
  have op11 : sweepOperator q u baseTwoThreeTwoB ((1, 2) : ℕ × ℕ)
      = dminus q 3 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoB ((1, 2) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth baseTwoThreeTwoB ((1, 2) : ℕ × ℕ) = 3 from by decide]
  have op13 : sweepOperator q u baseTwoThreeTwoB ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoB ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op20 : sweepOperator q u baseTwoThreeTwoB ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-2 : ℤ)) • corner q 3 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoB ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth baseTwoThreeTwoB ((0, 1) : ℕ × ℕ) = 3 from by decide,
      show sweepRight baseTwoThreeTwoB ((0, 1) : ℕ × ℕ) = 2 from by decide]
    norm_num
  have op22 : sweepOperator q u baseTwoThreeTwoB ((2, 4) : ℕ × ℕ)
      = corner q 3 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoB ((2, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth baseTwoThreeTwoB ((2, 4) : ℕ × ℕ) = 3 from by decide,
      show sweepRight baseTwoThreeTwoB ((2, 4) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op31 : sweepOperator q u baseTwoThreeTwoB ((1, 3) : ℕ × ℕ)
      = dplus q 2 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoB ((1, 3) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth baseTwoThreeTwoB ((1, 3) : ℕ × ℕ) = 2 from by decide]
  have op33 : sweepOperator q u baseTwoThreeTwoB ((3, 6) : ℕ × ℕ)
      = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoB ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight baseTwoThreeTwoB ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op40 : sweepOperator q u baseTwoThreeTwoB ((0, 2) : ℕ × ℕ)
      = dplus q 1 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoB ((0, 2) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth baseTwoThreeTwoB ((0, 2) : ℕ × ℕ) = 1 from by decide]
  have op42 : sweepOperator q u baseTwoThreeTwoB ((2, 5) : ℕ × ℕ)
      = corner q 1 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoB ((2, 5) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth baseTwoThreeTwoB ((2, 5) : ℕ × ℕ) = 1 from by decide,
      show sweepRight baseTwoThreeTwoB ((2, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op62 : sweepOperator q u baseTwoThreeTwoB ((2, 6) : ℕ × ℕ)
      = dplus q 0 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoB ((2, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth baseTwoThreeTwoB ((2, 6) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 42) (n := 60) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 62) (by decide),
    op11, op13, op20, op22, op31, op33, op40, op42, op62]

/-! ### The word of `(0,3,3,5,6)` -/

set_option maxRecDepth 100000 in
/-- **The word of `(0,3,3,5,6)`:** nine events; the only one of the four with a type-`D` event
whose exponent is not `0`, namely `q^2` at `(1,3)`. -/
theorem partialSweepWord_baseTwoThreeTwoC (q u : L) :
    partialSweepWord q u baseTwoThreeTwoC (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((dminus q 3) * ((((q : L) ^ (-2 : ℤ)) • corner q 3) *
          ((((q : L) ^ (-1 : ℤ)) • corner q 3) * (((q ^ 2 : L) • (1 : Module.End L (Total L))) *
          ((dplus q 2) * ((((q : L) ^ (-1 : ℤ)) • corner q 2) * ((dplus q 1) * ((dplus q 0) *
          ((1 : Module.End L (Total L))))))))))) := by
  have op11 : sweepOperator q u baseTwoThreeTwoC ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoC ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op13 : sweepOperator q u baseTwoThreeTwoC ((3, 5) : ℕ × ℕ)
      = dminus q 3 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoC ((3, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth baseTwoThreeTwoC ((3, 5) : ℕ × ℕ) = 3 from by decide]
  have op20 : sweepOperator q u baseTwoThreeTwoC ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-2 : ℤ)) • corner q 3 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoC ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth baseTwoThreeTwoC ((0, 1) : ℕ × ℕ) = 3 from by decide,
      show sweepRight baseTwoThreeTwoC ((0, 1) : ℕ × ℕ) = 2 from by decide]
    norm_num
  have op22 : sweepOperator q u baseTwoThreeTwoC ((2, 4) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 3 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoC ((2, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth baseTwoThreeTwoC ((2, 4) : ℕ × ℕ) = 3 from by decide,
      show sweepRight baseTwoThreeTwoC ((2, 4) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op31 : sweepOperator q u baseTwoThreeTwoC ((1, 3) : ℕ × ℕ)
      = (q ^ 2 : L) • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoC ((1, 3) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight baseTwoThreeTwoC ((1, 3) : ℕ × ℕ) = 2 from by decide]
  have op33 : sweepOperator q u baseTwoThreeTwoC ((3, 6) : ℕ × ℕ)
      = dplus q 2 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoC ((3, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth baseTwoThreeTwoC ((3, 6) : ℕ × ℕ) = 2 from by decide]
  have op40 : sweepOperator q u baseTwoThreeTwoC ((0, 2) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoC ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth baseTwoThreeTwoC ((0, 2) : ℕ × ℕ) = 2 from by decide,
      show sweepRight baseTwoThreeTwoC ((0, 2) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op42 : sweepOperator q u baseTwoThreeTwoC ((2, 5) : ℕ × ℕ)
      = dplus q 1 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoC ((2, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth baseTwoThreeTwoC ((2, 5) : ℕ × ℕ) = 1 from by decide]
  have op60 : sweepOperator q u baseTwoThreeTwoC ((0, 3) : ℕ × ℕ)
      = dplus q 0 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoC ((0, 3) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth baseTwoThreeTwoC ((0, 3) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 42) (n := 51) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 60) (by decide),
    op11, op13, op20, op22, op31, op33, op40, op42, op60]

/-! ### The word of `(0,3,3,6,6)` -/

set_option maxRecDepth 100000 in
/-- **The word of `(0,3,3,6,6)`:** ten events, every width `2`, so this word never leaves `V_2`;
its two type-`E` events give it the only `u^2` of the four. -/
theorem partialSweepWord_baseTwoThreeTwoD (q u : L) :
    partialSweepWord q u baseTwoThreeTwoD (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) *
          ((((q : L) ^ (-1 : ℤ)) • corner q 2) * ((corner q 2) *
          ((q • (1 : Module.End L (Total L))) * (((1 : Module.End L (Total L))) *
          ((((q : L) ^ (-1 : ℤ)) • corner q 2) * ((corner q 2) * ((dplus q 1) * ((dplus q 0) *
          ((1 : Module.End L (Total L)))))))))))) := by
  have op11 : sweepOperator q u baseTwoThreeTwoD ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoD ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op13 : sweepOperator q u baseTwoThreeTwoD ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoD ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op20 : sweepOperator q u baseTwoThreeTwoD ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoD ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth baseTwoThreeTwoD ((0, 1) : ℕ × ℕ) = 2 from by decide,
      show sweepRight baseTwoThreeTwoD ((0, 1) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op22 : sweepOperator q u baseTwoThreeTwoD ((2, 4) : ℕ × ℕ)
      = corner q 2 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoD ((2, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth baseTwoThreeTwoD ((2, 4) : ℕ × ℕ) = 2 from by decide,
      show sweepRight baseTwoThreeTwoD ((2, 4) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op31 : sweepOperator q u baseTwoThreeTwoD ((1, 3) : ℕ × ℕ)
      = q • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoD ((1, 3) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight baseTwoThreeTwoD ((1, 3) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op33 : sweepOperator q u baseTwoThreeTwoD ((3, 6) : ℕ × ℕ)
      = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoD ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight baseTwoThreeTwoD ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op40 : sweepOperator q u baseTwoThreeTwoD ((0, 2) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoD ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth baseTwoThreeTwoD ((0, 2) : ℕ × ℕ) = 2 from by decide,
      show sweepRight baseTwoThreeTwoD ((0, 2) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op42 : sweepOperator q u baseTwoThreeTwoD ((2, 5) : ℕ × ℕ)
      = corner q 2 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoD ((2, 5) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth baseTwoThreeTwoD ((2, 5) : ℕ × ℕ) = 2 from by decide,
      show sweepRight baseTwoThreeTwoD ((2, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op60 : sweepOperator q u baseTwoThreeTwoD ((0, 3) : ℕ × ℕ)
      = dplus q 1 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoD ((0, 3) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth baseTwoThreeTwoD ((0, 3) : ℕ × ℕ) = 1 from by decide]
  have op62 : sweepOperator q u baseTwoThreeTwoD ((2, 6) : ℕ × ℕ)
      = dplus q 0 := by
    rw [sweepOperator,
      show eventType baseTwoThreeTwoD ((2, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth baseTwoThreeTwoD ((2, 6) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 42) (n := 51) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 62) (by decide),
    op11, op13, op20, op22, op31, op33, op40, op42, op60, op62]
end Words

end HJO.Mellit

end
