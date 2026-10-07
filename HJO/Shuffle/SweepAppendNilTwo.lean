/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendTwoThree

/-! # The `α = []`, `A = 2` instance of `HJO.Mellit.SweepAppend` at `(a,b) = (1,2)`

`HJO/Shuffle/SweepAppendTwoThree.lean` crosses the singleton boundary of
`HJO.Mellit.sweepAppend_nil_one_one_b` in the `a` direction. This file crosses it in the other one:
`HJO.Mellit.one_lt_card_aboveReturnPaths_one_two_two` exhibits two above-diagonal paths of the
`2 × 4` rectangle with return composition `(2)`, the paths `HJO.Paths.tailEx1` and
`HJO.Paths.tailEx2`, and `HJO.Mellit.sweepAppend_nil_one_two_two` proves the `append` field of
`HJO.Mellit.SweepAppend` there, for every `q ∉ {0,1}` and `u ≠ 0`. Both sides are
`-e_1y_1^3 + uy_1^4`.

Together with `HJO.Mellit.sweepAppend_nil_two_three_one` this settles the `α = []` clause at
**both** parameter points where the index set is known to stop being a singleton — the two witnesses
the `SweepAppendOneB` docstring names as the obstruction to its own method.
## What is new here, and what is reused

The word of `HJO.Paths.tailEx1` is the `2 × 3` word of `HJO.Mellit.partialSweepWord_baseTwoThreeA`
with one further corner event on top:
`Δ^{(1)}d_-^{(2)}q^{-1}Δ^{(2)}d_+^{(1)}d_+^{(0)}`. The event operators do not depend on `(a,b)` —
only the geometry that selects them does — so the whole width-`2` computation is reused verbatim,
and the one new operator step is `Δ^{(1)}` applied to `e_1y_1^2`, an element of `y_1V_1` with a
NONTRIVIAL `Λ`-coefficient. That is `HJO.Sweep.corner_one_auxVar_mul`, which holds on all
of `y_1V_1` and not merely on the monomials `y_1^m`, so no new commutator is computed.

The right-hand side, by contrast, is genuinely new: at `A = 2` the stage carries one power of
`HJO.Mellit.replTwoTotal`, so the `z_1` of `HJO.Sweep.zop` appears where at `A = 1` only `d^*_+`
did. It is read by `HJO.Sweep.zopOneStar_one_auxVar_sq` together with the displacement
`HJO.Sweep.dplusStar_zero_C_elemSymm_two`, and its scalar `(qu)^{1-A} = (qu)^{-1}` cancels the
`(q-1)u` of that displacement exactly as at `A = 1` — the same two field identities
serve both.

## The peeling helpers are stated generically here

`HJO.Mellit.partialSweepWord_step_of_ranks` and `HJO.Mellit.partialSweepWord_top_of_ranks` take the
finite set of ranks of the rectangle as a parameter, so they serve any `(a, b, N)`; the versions in
`HJO/Shuffle/SweepAppendTwoThree.lean` are the `(2,3,1)` case.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep HJO.Sym HJO.Paths Finset

/-! ### Generic peeling, given the ranks of the rectangle -/

section Peel

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-- Above the top rank of a path the partial word is empty. -/
theorem partialSweepWord_top_of_ranks (q u : L) {y : Heights a b N} {m : ℤ}
    (h : ∀ P ∈ sweptRegion y, pointRank a b N P ≤ m) :
    partialSweepWord q u y ((m : ℚ) + 1 / 2) = 1 := by
  refine partialSweepWord_of_forall_le q u y _ fun P hP => ?_
  have hle : ((pointRank a b N P : ℤ) : ℚ) ≤ ((m : ℤ) : ℚ) := by exact_mod_cast h P hP
  linarith

/-- **One step of the peeling, from the list of ranks of the rectangle.** The isolation hypothesis
of `HJO.Mellit.partialSweepWord_eq_sweepOperator_mul` asks that the window `(m + 1/2, n + 1/2)`
contain exactly one rank; given a finite set `S` containing every rank, that is one decidable
statement about the elements of `S`, and the two half-integer levels turn the rational comparisons
into `m < rk ≤ n`. -/
theorem partialSweepWord_step_of_ranks (q u : L) (ha : 0 < a) {S : Finset ℤ}
    (hS : ∀ Q : ℕ × ℕ, Q.1 ≤ a * N → Q.2 ≤ b * N → pointRank a b N Q ∈ S)
    {y : Heights a b N} {P : ℕ × ℕ} {m n r : ℤ} (hr : ∀ z ∈ S, m < z → z ≤ n → z = r)
    (hPr : pointRank a b N P = r) (hlo : ((m : ℚ) + 1 / 2) < (r : ℚ))
    (hup : ((r : ℚ)) < ((n : ℚ) + 1 / 2)) (hPmem : P ∈ sweptRegion y) :
    partialSweepWord q u y ((m : ℚ) + 1 / 2)
      = sweepOperator q u y P * partialSweepWord q u y ((n : ℚ) + 1 / 2) := by
  refine partialSweepWord_eq_sweepOperator_mul q u ha (isAdmissibleLevel_int_add_half n) ?_ ?_
    (fun Q hQ1 hQ2 hQlo hQup => ?_) hPmem
  · rw [hPr]; exact_mod_cast hlo
  · rw [hPr]; exact_mod_cast hup
  · rw [hPr]
    exact hr _ (hS Q hQ1 hQ2) (lt_of_half_lt hQlo) (le_of_lt_half hQup)

end Peel

/-! ### The two above-diagonal paths of the `2 × 4` rectangle with one return -/

theorem ht_tailEx1_zero : ht tailEx1 0 = 0 := by decide
theorem ht_tailEx1_one : ht tailEx1 1 = 3 := by decide
theorem ht_tailEx1_two : ht tailEx1 2 = 4 := by decide
theorem ht_tailEx2_zero : ht tailEx2 0 = 0 := by decide
theorem ht_tailEx2_one : ht tailEx2 1 = 4 := by decide
theorem ht_tailEx2_two : ht tailEx2 2 = 4 := by decide

/-- **The above-diagonal paths of the `2 × 4` rectangle with return composition `(2)` are exactly
two.** The end heights are pinned, `ŷ_0 = 0` and `ŷ_2 = 4`; above the diagonal `ŷ_1 ≥ 2`; and the
return condition of `HJO.Paths.HasAboveReturns` FORBIDS a return at `k = 1`, i.e. `ŷ_1 ≠ 2`. So
`ŷ_1 ∈ {3, 4}`. -/
theorem eq_tailEx {y : Heights 1 2 2} (hy : HasAboveReturns [2] y) :
    y = tailEx1 ∨ y = tailEx2 := by
  have h0 : ht y 0 = 0 := hy.1.1
  have h2 : ht y 2 = 4 := by
    have h := hy.1.2.1
    norm_num at h
    exact h
  have hge : 2 ≤ ht y 1 := by
    have h := hy.1.2.2.2 1 (by omega)
    norm_num at h
    exact h
  have hle : ht y 1 ≤ 4 := by
    have h := ht_le_mul y 1
    norm_num at h
    exact h
  have hne : ht y 1 ≠ 2 := by
    intro hc
    have h := (hy.2.2.2 1 (by omega)).1 (by norm_num [hc])
    rw [show ([2] : List ℕ).scanl (· + ·) 0 = [0, 2] from by
      simp [List.scanl_cons, List.scanl_nil]] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    omega
  have hcase : ht y 1 = 3 ∨ ht y 1 = 4 := by omega
  have hfun : ∀ z : Heights 1 2 2, ht z 0 = 0 → ht z 1 = ht y 1 → ht z 2 = 4 → y = z := by
    intro z hz0 hz1 hz2
    funext r
    apply Fin.val_injective
    rw [← ht_coe y r, ← ht_coe z r]
    have hlt := r.isLt
    have hr : (r : ℕ) = 0 ∨ (r : ℕ) = 1 ∨ (r : ℕ) = 2 := by omega
    rcases hr with hr | hr | hr <;> rw [hr]
    · rw [h0, hz0]
    · rw [hz1]
    · rw [h2, hz2]
  rcases hcase with hc | hc
  · exact Or.inl (hfun tailEx1 ht_tailEx1_zero (by rw [ht_tailEx1_one, hc]) ht_tailEx1_two)
  · exact Or.inr (hfun tailEx2 ht_tailEx2_zero (by rw [ht_tailEx2_one, hc]) ht_tailEx2_two)

/-- **The index set of the `α = []`, `A = 2` sum at `(a,b) = (1,2)`**: the two paths of
`HJO.Mellit.one_lt_card_aboveReturnPaths_one_two_two`, and no others. -/
theorem aboveReturnPaths_one_two_two : aboveReturnPaths 1 2 2 [2] = {tailEx1, tailEx2} := by
  ext y
  rw [mem_aboveReturnPaths_iff, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨eq_tailEx, ?_⟩
  rintro (rfl | rfl)
  · exact hasAboveReturns_tailEx1
  · exact hasAboveReturns_tailEx2

/-! ### The ranks of the `2 × 4` rectangle -/

/-- The fifteen ranks `6(y - 2x) + x` of the `2 × 4` rectangle. -/
theorem rank_mem_one_two_two (Q : ℕ × ℕ) (h1 : Q.1 ≤ 1 * 2) (h2 : Q.2 ≤ 2 * 2) :
    pointRank 1 2 2 Q
      ∈ ({-22, -16, -11, -10, -5, -4, 0, 1, 2, 6, 7, 12, 13, 18, 24} : Finset ℤ) := by
  obtain ⟨x, y⟩ := Q
  simp only at h1 h2
  interval_cases x <;> interval_cases y <;> decide

theorem sepLevel_one_two : sepLevel 1 2 = ((2 : ℤ) : ℚ) + 1 / 2 := by
  rw [sepLevel]
  norm_num

theorem pointRank_zero_one' : pointRank 1 2 2 ((0, 1) : ℕ × ℕ) = 6 := by decide
theorem pointRank_one_three' : pointRank 1 2 2 ((1, 3) : ℕ × ℕ) = 7 := by decide
theorem pointRank_zero_two' : pointRank 1 2 2 ((0, 2) : ℕ × ℕ) = 12 := by decide
theorem pointRank_one_four' : pointRank 1 2 2 ((1, 4) : ℕ × ℕ) = 13 := by decide
theorem pointRank_zero_three' : pointRank 1 2 2 ((0, 3) : ℕ × ℕ) = 18 := by decide
theorem pointRank_zero_four' : pointRank 1 2 2 ((0, 4) : ℕ × ℕ) = 24 := by decide

/-! ### The events of the two paths -/

theorem eventType_tailEx1_zero_one : eventType tailEx1 ((0, 1) : ℕ × ℕ) = EventType.C := by decide
theorem sweepWidth_tailEx1_zero_one : sweepWidth tailEx1 ((0, 1) : ℕ × ℕ) = 1 := by decide
theorem sweepRight_tailEx1_zero_one : sweepRight tailEx1 ((0, 1) : ℕ × ℕ) = 0 := by decide
theorem eventType_tailEx1_one_three : eventType tailEx1 ((1, 3) : ℕ × ℕ) = EventType.B := by decide
theorem sweepWidth_tailEx1_one_three : sweepWidth tailEx1 ((1, 3) : ℕ × ℕ) = 2 := by decide
theorem eventType_tailEx1_zero_two : eventType tailEx1 ((0, 2) : ℕ × ℕ) = EventType.C := by decide
theorem sweepWidth_tailEx1_zero_two : sweepWidth tailEx1 ((0, 2) : ℕ × ℕ) = 2 := by decide
theorem sweepRight_tailEx1_zero_two : sweepRight tailEx1 ((0, 2) : ℕ × ℕ) = 1 := by decide
theorem eventType_tailEx1_one_four : eventType tailEx1 ((1, 4) : ℕ × ℕ) = EventType.A := by decide
theorem sweepWidth_tailEx1_one_four : sweepWidth tailEx1 ((1, 4) : ℕ × ℕ) = 1 := by decide
theorem eventType_tailEx1_zero_three : eventType tailEx1 ((0, 3) : ℕ × ℕ) = EventType.A := by decide
theorem sweepWidth_tailEx1_zero_three : sweepWidth tailEx1 ((0, 3) : ℕ × ℕ) = 0 := by decide

theorem eventType_tailEx2_zero_one : eventType tailEx2 ((0, 1) : ℕ × ℕ) = EventType.C := by decide
theorem sweepWidth_tailEx2_zero_one : sweepWidth tailEx2 ((0, 1) : ℕ × ℕ) = 1 := by decide
theorem sweepRight_tailEx2_zero_one : sweepRight tailEx2 ((0, 1) : ℕ × ℕ) = 0 := by decide
theorem eventType_tailEx2_one_three : eventType tailEx2 ((1, 3) : ℕ × ℕ) = EventType.E := by decide
theorem eventType_tailEx2_zero_two : eventType tailEx2 ((0, 2) : ℕ × ℕ) = EventType.C := by decide
theorem sweepWidth_tailEx2_zero_two : sweepWidth tailEx2 ((0, 2) : ℕ × ℕ) = 1 := by decide
theorem sweepRight_tailEx2_zero_two : sweepRight tailEx2 ((0, 2) : ℕ × ℕ) = 0 := by decide
theorem eventType_tailEx2_one_four : eventType tailEx2 ((1, 4) : ℕ × ℕ) = EventType.D := by decide
theorem sweepRight_tailEx2_one_four : sweepRight tailEx2 ((1, 4) : ℕ × ℕ) = 0 := by decide
theorem eventType_tailEx2_zero_three : eventType tailEx2 ((0, 3) : ℕ × ℕ) = EventType.C := by decide
theorem sweepWidth_tailEx2_zero_three : sweepWidth tailEx2 ((0, 3) : ℕ × ℕ) = 1 := by decide
theorem sweepRight_tailEx2_zero_three : sweepRight tailEx2 ((0, 3) : ℕ × ℕ) = 0 := by decide
theorem eventType_tailEx2_zero_four : eventType tailEx2 ((0, 4) : ℕ × ℕ) = EventType.A := by decide
theorem sweepWidth_tailEx2_zero_four : sweepWidth tailEx2 ((0, 4) : ℕ × ℕ) = 0 := by decide

theorem mem_sweptRegion_tailEx1_zero_one : ((0, 1) : ℕ × ℕ) ∈ sweptRegion tailEx1 := by decide
theorem mem_sweptRegion_tailEx1_one_three : ((1, 3) : ℕ × ℕ) ∈ sweptRegion tailEx1 := by decide
theorem mem_sweptRegion_tailEx1_zero_two : ((0, 2) : ℕ × ℕ) ∈ sweptRegion tailEx1 := by decide
theorem mem_sweptRegion_tailEx1_one_four : ((1, 4) : ℕ × ℕ) ∈ sweptRegion tailEx1 := by decide
theorem mem_sweptRegion_tailEx1_zero_three : ((0, 3) : ℕ × ℕ) ∈ sweptRegion tailEx1 := by decide
theorem mem_sweptRegion_tailEx2_zero_one : ((0, 1) : ℕ × ℕ) ∈ sweptRegion tailEx2 := by decide
theorem mem_sweptRegion_tailEx2_one_three : ((1, 3) : ℕ × ℕ) ∈ sweptRegion tailEx2 := by decide
theorem mem_sweptRegion_tailEx2_zero_two : ((0, 2) : ℕ × ℕ) ∈ sweptRegion tailEx2 := by decide
theorem mem_sweptRegion_tailEx2_one_four : ((1, 4) : ℕ × ℕ) ∈ sweptRegion tailEx2 := by decide
theorem mem_sweptRegion_tailEx2_zero_three : ((0, 3) : ℕ × ℕ) ∈ sweptRegion tailEx2 := by decide
theorem mem_sweptRegion_tailEx2_zero_four : ((0, 4) : ℕ × ℕ) ∈ sweptRegion tailEx2 := by decide

theorem pointRank_le_tailEx1 : ∀ P ∈ sweptRegion tailEx1, pointRank 1 2 2 P ≤ 18 := by decide
theorem pointRank_le_tailEx2 : ∀ P ∈ sweptRegion tailEx2, pointRank 1 2 2 P ≤ 24 := by decide

/-! ### The two words of the `2 × 4` rectangle at the separating level -/

section Words

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **The width-`2` core of both rectangles.**
`d_-^{(2)}q^{-1}Δ^{(2)}d_+^{(1)}d_+^{(0)}(1) = e_1y_1^2`: the event operators of
`HJO.Mellit.sweepOperator` do not depend on `(a,b)`, so this is the same computation that
`HJO.Mellit.partialSweepWord_baseTwoThreeA_apply_one` performs in the `2 × 3` rectangle, and the
`q^{-1}` of the type-`C` event is where `q ≠ 0` is spent. -/
theorem dminus_corner_two_chain (q : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dminus q 2 (((q ^ (-1 : ℤ) : L)) • corner q 2 (dplus q 1 (dplus q 0 (1 : Total L))))
      = MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2 := by
  have hs : (scal ((q : L) ^ (-1 : ℤ)) : Total L) * scal q = 1 := by
    rw [← scal_mul, zpow_neg_one, inv_mul_cancel₀ hq0, scal_one]
  have hmid : ((q : L) ^ (-1 : ℤ))
        • (-(scal q * ((MvPolynomial.X 0 : Total L) ^ 2 * MvPolynomial.X 1)))
      = -((MvPolynomial.X 0 : Total L) ^ 2 * MvPolynomial.X 1) := by
    rw [smul_neg, smul_eq_scal_mul, ← mul_assoc, hs, one_mul]
  rw [dplus_zero_one, map_neg, dplus_one_X_zero, neg_neg, corner_two_X_zero_mul_X_one hq1, hmid,
    map_neg, dminus_two_X_zero_sq_mul_X_one, neg_neg]

/-- `e_1y_1 ∈ V_1`: the coefficient is a scalar of the base `Λ`. -/
theorem C_elemSymm_one_mul_X_zero_mem_piece_one :
    (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L)) ∈ piece L 1 := by
  refine mul_mem ?_ (auxVar_mem_piece (i := 1) le_rfl le_rfl)
  have h : (MvPolynomial.C (elemSymm L 1) : Total L)
      = algebraMap (Sym.Lambda L) (Total L) (elemSymm L 1) := rfl
  rw [h]
  exact (piece L 1).algebraMap_mem _

/-- **`Δ^{(1)}(e_1y_1^2) = -e_1y_1^3`.** `HJO.Sweep.corner_one_auxVar_mul` holds on all of
`y_1V_1`, so the nontrivial `Λ`-coefficient costs nothing. -/
theorem corner_one_C_elemSymm_one_mul_X_zero_sq (hq1 : q ≠ 1) :
    corner q 1 (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2)
      = -(MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 3) := by
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hform : MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2
      = (auxVar 1 : Total L) * (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L)) := by
    rw [hav]; ring
  rw [hform, corner_one_auxVar_mul hq1 C_elemSymm_one_mul_X_zero_mem_piece_one, hav]
  ring

/-- **The word of `HJO.Paths.tailEx1 = (0,3,4)`:** the width-`2` core with one corner event on top.
-/
theorem partialSweepWord_tailEx1 (q u : L) :
    partialSweepWord q u tailEx1 (sepLevel 1 2)
      = corner q 1 * (dminus q 2 * ((((q ^ (-1 : ℤ) : L)) • corner q 2)
        * (dplus q 1 * (dplus q 0 * 1)))) := by
  have op1 : sweepOperator q u tailEx1 ((0, 1) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator, eventType_tailEx1_zero_one, sweepWidth_tailEx1_zero_one,
      sweepRight_tailEx1_zero_one]
    norm_num
  have op2 : sweepOperator q u tailEx1 ((1, 3) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator, eventType_tailEx1_one_three, sweepWidth_tailEx1_one_three]
  have op3 : sweepOperator q u tailEx1 ((0, 2) : ℕ × ℕ)
      = ((q ^ (-1 : ℤ) : L)) • corner q 2 := by
    rw [sweepOperator, eventType_tailEx1_zero_two, sweepWidth_tailEx1_zero_two,
      sweepRight_tailEx1_zero_two]
    norm_num
  have op4 : sweepOperator q u tailEx1 ((1, 4) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator, eventType_tailEx1_one_four, sweepWidth_tailEx1_one_four]
  have op5 : sweepOperator q u tailEx1 ((0, 3) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator, eventType_tailEx1_zero_three, sweepWidth_tailEx1_zero_three]
  rw [sepLevel_one_two,
    partialSweepWord_step_of_ranks q u (by omega) rank_mem_one_two_two (m := 2) (n := 6) (r := 6)
      (by decide) pointRank_zero_one' (by norm_num) (by norm_num)
      mem_sweptRegion_tailEx1_zero_one,
    partialSweepWord_step_of_ranks q u (by omega) rank_mem_one_two_two (m := 6) (n := 7) (r := 7)
      (by decide) pointRank_one_three' (by norm_num) (by norm_num)
      mem_sweptRegion_tailEx1_one_three,
    partialSweepWord_step_of_ranks q u (by omega) rank_mem_one_two_two (m := 7) (n := 12) (r := 12)
      (by decide) pointRank_zero_two' (by norm_num) (by norm_num)
      mem_sweptRegion_tailEx1_zero_two,
    partialSweepWord_step_of_ranks q u (by omega) rank_mem_one_two_two (m := 12) (n := 13) (r := 13)
      (by decide) pointRank_one_four' (by norm_num) (by norm_num)
      mem_sweptRegion_tailEx1_one_four,
    partialSweepWord_step_of_ranks q u (by omega) rank_mem_one_two_two (m := 13) (n := 18) (r := 18)
      (by decide) pointRank_zero_three' (by norm_num) (by norm_num)
      mem_sweptRegion_tailEx1_zero_three,
    partialSweepWord_top_of_ranks q u pointRank_le_tailEx1, op1, op2, op3, op4, op5]

/-- **The word of `HJO.Paths.tailEx2 = (0,4,4)`:** three corner events of width `1`, one type-`E`
event and one type-`D` event. -/
theorem partialSweepWord_tailEx2 (q u : L) :
    partialSweepWord q u tailEx2 (sepLevel 1 2)
      = corner q 1 * ((u • (1 : Module.End L (Total L))) * (corner q 1
        * ((1 : Module.End L (Total L)) * (corner q 1 * (dplus q 0 * 1))))) := by
  have op1 : sweepOperator q u tailEx2 ((0, 1) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator, eventType_tailEx2_zero_one, sweepWidth_tailEx2_zero_one,
      sweepRight_tailEx2_zero_one]
    norm_num
  have op2 : sweepOperator q u tailEx2 ((1, 3) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator, eventType_tailEx2_one_three]
  have op3 : sweepOperator q u tailEx2 ((0, 2) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator, eventType_tailEx2_zero_two, sweepWidth_tailEx2_zero_two,
      sweepRight_tailEx2_zero_two]
    norm_num
  have op4 : sweepOperator q u tailEx2 ((1, 4) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator, eventType_tailEx2_one_four, sweepRight_tailEx2_one_four]
    norm_num
  have op5 : sweepOperator q u tailEx2 ((0, 3) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator, eventType_tailEx2_zero_three, sweepWidth_tailEx2_zero_three,
      sweepRight_tailEx2_zero_three]
    norm_num
  have op6 : sweepOperator q u tailEx2 ((0, 4) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator, eventType_tailEx2_zero_four, sweepWidth_tailEx2_zero_four]
  rw [sepLevel_one_two,
    partialSweepWord_step_of_ranks q u (by omega) rank_mem_one_two_two (m := 2) (n := 6) (r := 6)
      (by decide) pointRank_zero_one' (by norm_num) (by norm_num)
      mem_sweptRegion_tailEx2_zero_one,
    partialSweepWord_step_of_ranks q u (by omega) rank_mem_one_two_two (m := 6) (n := 7) (r := 7)
      (by decide) pointRank_one_three' (by norm_num) (by norm_num)
      mem_sweptRegion_tailEx2_one_three,
    partialSweepWord_step_of_ranks q u (by omega) rank_mem_one_two_two (m := 7) (n := 12) (r := 12)
      (by decide) pointRank_zero_two' (by norm_num) (by norm_num)
      mem_sweptRegion_tailEx2_zero_two,
    partialSweepWord_step_of_ranks q u (by omega) rank_mem_one_two_two (m := 12) (n := 13) (r := 13)
      (by decide) pointRank_one_four' (by norm_num) (by norm_num)
      mem_sweptRegion_tailEx2_one_four,
    partialSweepWord_step_of_ranks q u (by omega) rank_mem_one_two_two (m := 13) (n := 18) (r := 18)
      (by decide) pointRank_zero_three' (by norm_num) (by norm_num)
      mem_sweptRegion_tailEx2_zero_three,
    partialSweepWord_step_of_ranks q u (by omega) rank_mem_one_two_two (m := 18) (n := 24) (r := 24)
      (by decide) pointRank_zero_four' (by norm_num) (by norm_num)
      mem_sweptRegion_tailEx2_zero_four,
    partialSweepWord_top_of_ranks q u pointRank_le_tailEx2, op1, op2, op3, op4, op5, op6]

/-- **`HJO.Paths.tailEx1` contributes `-e_1y_1^3`.** -/
theorem partialSweepWord_tailEx1_apply_one (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u tailEx1 (sepLevel 1 2) (1 : Total L)
      = -(MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 3) := by
  rw [partialSweepWord_tailEx1 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [dminus_corner_two_chain q hq0 hq1, corner_one_C_elemSymm_one_mul_X_zero_sq hq1]

/-- **`HJO.Paths.tailEx2` contributes `uy_1^4`.** -/
theorem partialSweepWord_tailEx2_apply_one (q u : L) (hq1 : q ≠ 1) :
    partialSweepWord q u tailEx2 (sepLevel 1 2) (1 : Total L)
      = scal u * (MvPolynomial.X 0 : Total L) ^ 4 := by
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hc2 : corner q 1 ((MvPolynomial.X 0 : Total L) ^ 2)
      = -((MvPolynomial.X 0 : Total L) ^ 3) := by
    have h := corner_one_auxVar_pow (L := L) hq1 2
    rw [hav] at h
    exact h
  have hc3 : corner q 1 ((MvPolynomial.X 0 : Total L) ^ 3)
      = -((MvPolynomial.X 0 : Total L) ^ 4) := by
    have h := corner_one_auxVar_pow (L := L) hq1 3
    rw [hav] at h
    exact h
  rw [partialSweepWord_tailEx2 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [dplus_zero_one, map_neg, corner_one_X_zero (q := q) hq1, neg_neg, hc2, map_smul, map_neg,
    hc3, neg_neg, smul_eq_scal_mul]

/-- **`D_{5/2,c_{(2)}} = -e_1y_1^3 + uy_1^4` in the `2 × 4` rectangle**, for `q ∉ {0,1}`. -/
theorem dsc_one_two_two (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dsc q u 1 2 2 (sepLevel 1 2) (compColouring 1 2 [2])
      = -(MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 3)
        + scal u * (MvPolynomial.X 0 : Total L) ^ 4 := by
  have hne : tailEx1 ≠ tailEx2 := by decide
  rw [dsc_compColouring_eq_sum_partialSweepWord q u (isAdmissibleLevel_sepLevel 1 2)
      (separatesDiagonal_sepLevel' 1 2 2) (by decide) (by omega) (by omega)
      (by simp) (by simp),
    aboveReturnPaths_one_two_two, Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    partialSweepWord_tailEx1_apply_one q u hq0 hq1, partialSweepWord_tailEx2_apply_one q u hq1]

/-! ### The stage at `(1,2)`, `α = []`, `A = 2`, and the instance -/

/-- **`Ξ_{1,2}` is multiplication by `-y_1`.** At `a = 1` the slope word of
`HJO.Braid.slopeBraid` has no `𝗓` (`HJO.Mellit.slopeWord_one_left`), so `Ξ_{1,n}` is
`(-y_1)^{n-1}`. -/
theorem slopeOperator_one_two_apply (q u : L) (G : Total L) :
    slopeOperator q u 1 1 2 G = -(auxVar 1 : Total L) * G := by
  rw [slopeOperator_eq_slopeEval, slopeEval_one_left _ _ (show 0 < 2 by omega),
    show (2 : ℕ) - 1 = 1 from rfl, neg_mulLeft_pow_apply, pow_one]

/-- **`Ω(2;1,2)(y_1^2) = y_1^2z_1(y_1^2)`.** -/
theorem replTwoTotal_one_two_X_zero_sq (q u : L) :
    replTwoTotal q u 1 2 0 ((MvPolynomial.X 0 : Total L) ^ 2)
      = (MvPolynomial.X 0 : Total L) ^ 2 * zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2) := by
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  rw [replTwoTotal]
  simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply, Nat.sub_self,
    pow_zero, one_smul]
  rw [slopeOperator_one_two_apply, hav]
  ring

/-- **`z_1(y_1^2) = q/(1-q)·(q-1)u(e_1y_1 - uy_1^2)`**, that is
`HJO.Sweep.zopOneStar_one_auxVar_sq` with the displacement of
`HJO.Sweep.dplusStar_zero_C_elemSymm_two` substituted. -/
theorem zopOneStar_one_X_zero_sq_eq (q u : L) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2)
      = (q / (1 - q)) • (scal ((q - 1) * u)
          * (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L))
        - scal ((q - 1) * u ^ 2) * ((MvPolynomial.X 0 : Total L) ^ 2)) := by
  rw [zopOneStar_one_auxVar_sq, dplusStar_zero_C_elemSymm_two]
  congr 1
  ring

/-- **`HJO.Mellit.SweepAppend` at `α = []`, `A = 2`, `(a,b) = (1,2)`, verbatim, and it is TRUE for
every `q ∉ {0,1}` and every `u ≠ 0`.** Both sides are `-e_1y_1^3 + uy_1^4`: the left by
`HJO.Mellit.dsc_one_two_two`, a sum over the TWO paths of
`HJO.Mellit.aboveReturnPaths_one_two_two`, and the right by
`HJO.Mellit.replTwoTotal_one_two_X_zero_sq` on `HJO.Sweep.replOneTotal_one_left`.

This is the `A`-direction counterpart of `HJO.Mellit.sweepAppend_nil_two_three_one`: the second of
the two parameter points at which `HJO.Mellit.sweepAppend_nil_one_one_b`'s singleton index set
fails, and the first `α = []` instance at `A ≥ 2`, where `HJO.Mellit.stageTotal` carries a power of
`HJO.Mellit.replTwoTotal` and so reads `HJO.Sweep.zop`. -/
theorem sweepAppend_nil_one_two_two (q u : L) (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    dsc q u 1 2 (([] : List ℕ).sum + 2) (sepLevel 1 (([] : List ℕ).sum + 2))
        (compColouring 1 2 ([] ++ [2]))
      = ((-1 : L) ^ ((1 - 1) * 2) * (q * u) ^ (1 - ((2 : ℕ) : ℤ))) •
          stageTotal q u 1 2 ([] : List ℕ).length 2
            (dsc q u 1 2 ([] : List ℕ).sum (sepLevel 1 ([] : List ℕ).sum)
              (compColouring 1 2 ([] : List ℕ))) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hc : compColouring 1 2 ([] : List ℕ) = (∅ : Finset (ℕ × ℕ)) := by
    simp [compColouring]
  have hone : dsc q u 1 2 0 (sepLevel 1 0) (compColouring 1 2 ([] : List ℕ)) = (1 : Total L) := by
    rw [hc]
    exact dsc_empty_eq_one q u (isAdmissibleLevel_sepLevel 1 0)
      (separatesDiagonal_sepLevel' 1 2 0) (Nat.coprime_one_left 2) (by omega) (by omega)
  have hrepl : replOneTotal q u 1 2 0 (1 : Total L) = (MvPolynomial.X 0 : Total L) ^ 2 := by
    rw [replOneTotal_one_left q u (show 0 < 2 by omega), hav]
    ring
  have ha : (scal ((q * u)⁻¹) : Total L) * scal (q / (1 - q)) * scal ((q - 1) * u) = -1 := by
    rw [← scal_mul, ← scal_mul, show (q * u)⁻¹ * (q / (1 - q)) * ((q - 1) * u) = -1 from by
      field_simp
      ring, scal_neg, scal_one]
  have hb : (scal ((q * u)⁻¹) : Total L) * scal (q / (1 - q)) * scal ((q - 1) * u ^ 2)
      = -scal u := by
    rw [← scal_mul, ← scal_mul, show (q * u)⁻¹ * (q / (1 - q)) * ((q - 1) * u ^ 2) = -u from by
      field_simp
      ring, scal_neg]
  simp only [List.sum_nil, List.length_nil, List.nil_append, Nat.zero_add]
  rw [hone, stageTotal_zero, show (2 : ℕ) - 1 = 1 from rfl, pow_one, Module.End.mul_apply, hrepl,
    replTwoTotal_one_two_X_zero_sq, zopOneStar_one_X_zero_sq_eq, dsc_one_two_two q u hq0 hq1,
    show ((1 : ℤ) - ((2 : ℕ) : ℤ)) = (-1 : ℤ) from by norm_num, zpow_neg_one,
    show ((-1 : L) ^ ((1 - 1) * 2) * (q * u)⁻¹) = (q * u)⁻¹ from by norm_num,
    smul_eq_scal_mul, smul_eq_scal_mul]
  linear_combination (-(MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 3)) * ha
    + ((MvPolynomial.X 0 : Total L) ^ 4) * hb

end Words

end HJO.Mellit
