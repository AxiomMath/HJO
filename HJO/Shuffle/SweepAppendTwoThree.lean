/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendOneB
public import HJO.Shuffle.MellitLhsSlopeBase

/-! # The `α = []`, `A = 1` instance of `HJO.Mellit.SweepAppend` at `(a,b) = (2,3)`

`HJO.Mellit.sweepAppend_nil_one_one_b` (`HJO/Shuffle/SweepAppendOneB.lean`) proves the
`α = []` clause of `HJO.Mellit.SweepAppend` at `A = 1` and `a = 1`, for every `b > 0`, and records
that its method — peel the word event by event — stops exactly there, because the index set
`HJO.Mellit.aboveReturnPaths` is a singleton at exactly those parameters and at no others
(`HJO.Mellit.one_lt_card_aboveReturnPaths_two_three_one`,
`HJO.Mellit.one_lt_card_aboveReturnPaths_one_two_two`).

This file crosses that boundary in the first direction: it proves the same clause at
`(a,b) = (2,3)`, `A = 1`, where the index set has TWO paths, by evaluating each word separately and
adding. `HJO.Mellit.sweepAppend_nil_two_three_one` is the `append` field of
`HJO.Mellit.SweepAppend` at those parameters, verbatim, for every `q ∉ {0,1}` and `u ≠ 0`.

## What the two paths contribute

`HJO.Mellit.aboveReturnPaths_two_three_one`: the index set is `{(0,2,3), (0,3,3)}` and nothing else,
because the two end heights are pinned and `3 ≤ 2ŷ_1 ≤ 6` leaves `ŷ_1 ∈ {2,3}`.

* The path `(0,3,3)` hugs the right wall. Its four events above `HJO.Mellit.sepLevel 2 1 = 5/2` all
  have width `0` or `1`, so it stays inside `y_1V_1` and
  `HJO.Sweep.corner_one_auxVar_pow` evaluates it: `uΔ^{(1)}Δ^{(1)}d_+^{(0)}(1) = -uy_1^3`. One
  type-`E` event contributes the `u` and one type-`D` event contributes `q^0 = 1`.
* The path `(0,2,3)` leaves `y_1V_1`: its word is `d_-^{(2)}q^{-1}Δ^{(2)}d_+^{(1)}d_+^{(0)}`, whose
  corner operator is read at **width 2**. `HJO.Sweep.corner_two_X_zero_mul_X_one` computes it from
  `HJO.Sweep.corner` directly — `Δ^{(2)}(y_1y_2) = -qy_1^2y_2`, the two composites `d_-d_+` and
  `d_+d_-` both producing `e_1y_1y_2` and cancelling, with the residue `q(q-1)y_1^2y_2` that
  `τ_{2,2}` put into the coefficient. The contribution is `e_1y_1^2`.

No rank listing is computed: the events are peeled one at a time by
`HJO.Mellit.partialSweepWord_step`, whose isolation hypothesis is discharged from the twelve ranks
of the `2 × 3` rectangle (`HJO.Mellit.rank_mem_two_three`) by one decidable check per window.

## The other side

`HJO.Mellit.replOneTotal_two_three` evaluates `Ω(1;2,3)(1)`. The slope word `β_{2,3} = yzy`
carries a letter `z`, so this is the first `α = []` instance whose right-hand side reads
`HJO.Sweep.zop` at all:
`HJO.Sweep.slopeOperator_two_three_auxVar` supplies the word and
`HJO.Sweep.zopOneStar_one_auxVar_sq` the middle letter, and what remains is the one-letter
displacement `HJO.Sweep.dplusStar_zero_C_elemSymm_two`:
`d^*_+{}^{(0)}(Ce_2) - Ce_2 = (q-1)u(e_1y_1 - uy_1^2)`. Both sides are `e_1y_1^2 - uy_1^3`.

## Genericity, and why both conditions are needed

`q ≠ 1` is necessary: `HJO.Mellit.not_sweepAppend_one_left` refutes the clause at `q = 1`, and it
enters here through `(q-1)^{-1}` of `HJO.Sweep.corner`. `q ≠ 0` is necessary too once `a ≥ 2`, and
that refutation is proved here —
`HJO.Mellit.not_sweepAppend_nil_two_three_one_of_q_zero`, for every `u ≠ 0`:
the type-`C` event at `(0,1)` of the path `(0,2,3)` has one live north step to its right, so its
operator carries `q^{-1}`, and the `z` letter of `β_{2,3}` carries `(qu)^{-1}`; in a field the
value `0⁻¹ = 0` would annihilate both. `u ≠ 0` enters only through that `(qu)^{-1}`.

## What this does NOT prove

The `hzero` hypothesis of `HJO.Mellit.sweepAppend_of_forall_band` quantifies over every `A > 0`;
this file settles `A = 1`. At `A ≥ 2` the index set grows again
(`HJO.Mellit.one_lt_card_aboveReturnPaths_one_two_two` already at `a = 1`), and the right-hand side
acquires the `A-1` powers of `HJO.Mellit.replTwoTotal` that `HJO.Mellit.stageTotal` carries.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

/-! ### The braid operator on the monomials of the `2 × 3` word -/

omit [Algebra ℚ L] in
theorem braid_one_X_zero_mul_X_one (q : L) :
    braid q 1 ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1)
      = (MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 := by
  rw [braid_apply, dividedDiff_one_X_zero_mul_X_one, map_mul, swapAux_X, swapAux_X]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, Nat.sub_self]
  ring

omit [Algebra ℚ L] in
theorem dividedDiff_one_X_zero_mul_X_one_sq :
    dividedDiff 1 ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 ^ 2)
      = (MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 := by
  refine (dividedDiff_unique (i := 1) le_rfl ?_).symm
  rw [map_mul, map_pow, swapAux_X, swapAux_X]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, Nat.sub_self]
  ring

omit [Algebra ℚ L] in
/-- **`T_1(y_1y_2^2) = qy_1^2y_2`.** -/
theorem braid_one_X_zero_mul_X_one_sq (q : L) :
    braid q 1 ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 ^ 2)
      = scal q * ((MvPolynomial.X 0 : Total L) ^ 2 * MvPolynomial.X 1) := by
  rw [braid_apply, dividedDiff_one_X_zero_mul_X_one_sq, map_mul, map_pow, swapAux_X, swapAux_X]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, Nat.sub_self]
  have h : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  rw [h, ← scal_one_add_scal_sub_one q, scal_one]
  ring

omit [Algebra ℚ L] in
theorem dividedDiff_prod {i : ℕ} (hi : i = 1 ∨ i = 2) :
    dividedDiff i ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 * MvPolynomial.X 2) = 0 := by
  rcases hi with rfl | rfl
  · refine (dividedDiff_unique (i := 1) le_rfl ?_).symm
    rw [mul_zero, map_mul, map_mul, swapAux_X, swapAux_X, swapAux_X]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, Nat.sub_self]
    rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
    ring
  · refine (dividedDiff_unique (i := 2) (by omega) ?_).symm
    rw [mul_zero, map_mul, map_mul, swapAux_X, swapAux_X, swapAux_X]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, show (2 : ℕ) - 1 = 1 from rfl]
    rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
    ring

omit [Algebra ℚ L] in
/-- **`T_1` and `T_2` fix `y_1y_2y_3`**, which is symmetric in all three. -/
theorem braid_prod (q : L) {i : ℕ} (hi : i = 1 ∨ i = 2) :
    braid q i ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 * MvPolynomial.X 2)
      = (MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 * MvPolynomial.X 2 := by
  rw [braid_apply, dividedDiff_prod hi, mul_zero, add_zero]
  rcases hi with rfl | rfl
  · rw [map_mul, map_mul, swapAux_X, swapAux_X, swapAux_X]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, Nat.sub_self]
    rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
    ring
  · rw [map_mul, map_mul, swapAux_X, swapAux_X, swapAux_X]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, show (2 : ℕ) - 1 = 1 from rfl]
    rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
    ring

/-! ### `d_+` and `d_-` on those monomials -/

omit [Algebra ℚ L] in
theorem auxVar_three : (auxVar 3 : Total L) = MvPolynomial.X 2 := by rw [auxVar]

omit [Algebra ℚ L] in
/-- The two-letter ascending train `T_{1↗3} = T_1T_2`. -/
theorem trainUpEnd_one_three (q : L) : trainUpEnd q 1 3 = braidEnd q 1 * braidEnd q 2 := by
  rw [trainUpEnd, Braid.trainUp]
  norm_num [Braid.ascendingWord, List.range']

omit [Algebra ℚ L] in
/-- `τ_{k,i}` fixes a monomial in the auxiliary variables: it moves only the power sums. -/
theorem qshift_X_zero_mul_X_one (q : L) (i : ℕ) :
    qshift q i ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1)
      = (MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 := by
  rw [map_mul, qshift_auxVar, qshift_auxVar]

omit [Algebra ℚ L] in
/-- **`d_+^{(2)}(y_1y_2) = -y_1y_2y_3`.** The two-letter train fixes the symmetric product. -/
theorem dplus_two_X_zero_mul_X_one (q : L) :
    dplus q 2 ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1)
      = -((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 * MvPolynomial.X 2) := by
  rw [dplus_apply, show (2 : ℕ) + 1 = 3 from rfl, qshift_X_zero_mul_X_one, auxVar_three,
    trainUpEnd_one_three]
  rw [show (MvPolynomial.X 2 : Total L) * (MvPolynomial.X 0 * MvPolynomial.X 1)
      = MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 from by ring]
  rw [Module.End.mul_apply, braidEnd, braidEnd, LinearMap.restrictScalars_apply,
    LinearMap.restrictScalars_apply, braid_prod q (Or.inr rfl), braid_prod q (Or.inl rfl)]

theorem bopExt_monomial_one (q : L) (r : ℤ) (d : ℕ →₀ ℕ) :
    bopExt q r (MvPolynomial.monomial d 1 : Total L)
      = MvPolynomial.monomial d 1 * MvPolynomial.C (elemSymmAlt L r) := by
  have h := bopExt_monomial_mul q r d (1 : Total L)
  rw [mul_one] at h
  rw [h, bopExt_one]

theorem elemSymmAlt_one : elemSymmAlt L (1 : ℤ) = -elemSymm L 1 := by
  rw [show ((1 : ℤ)) = ((1 : ℕ) : ℤ) from rfl, elemSymmAlt_natCast]
  ring

/-- **`d_-^{(3)}(y_1y_2y_3) = -e_1y_1y_2`.** -/
theorem dminus_three_prod (q : L) :
    dminus q 3 ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 * MvPolynomial.X 2)
      = -(MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 * MvPolynomial.X 1 : Total L)) := by
  have hmem : (MvPolynomial.X 0 * MvPolynomial.X 1 : Total L) ∈ piece L 2 :=
    mul_mem (auxVar_mem_piece (i := 1) le_rfl (by omega))
      (auxVar_mem_piece (i := 2) (by omega) (by omega))
  have hform : (MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 * MvPolynomial.X 2
      = (auxVar (2 + 1) : Total L) ^ 1 * (MvPolynomial.X 0 * MvPolynomial.X 1) := by
    rw [show (2 : ℕ) + 1 = 3 from rfl, auxVar_three, pow_one]; ring
  rw [hform, show (3 : ℕ) = 2 + 1 from rfl, dminus_auxVar_pow_mul q 2 1 hmem,
    monomial_X_zero_X_one, bopExt_monomial_one, ← monomial_X_zero_X_one, Nat.cast_one,
    elemSymmAlt_one, MvPolynomial.C_neg]
  ring

/-- **`d_-^{(2)}(y_1^2y_2) = -e_1y_1^2`.** -/
theorem dminus_two_X_zero_sq_mul_X_one (q : L) :
    dminus q 2 ((MvPolynomial.X 0 : Total L) ^ 2 * MvPolynomial.X 1)
      = -(MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2) := by
  have hmem : ((MvPolynomial.X 0 : Total L) ^ 2) ∈ piece L 1 :=
    pow_mem (auxVar_mem_piece (i := 1) le_rfl le_rfl) 2
  have hform : (MvPolynomial.X 0 : Total L) ^ 2 * MvPolynomial.X 1
      = (auxVar (1 + 1) : Total L) ^ 1 * ((MvPolynomial.X 0 : Total L) ^ 2) := by
    rw [show (1 : ℕ) + 1 = 2 from rfl, auxVar_two, pow_one]; ring
  rw [hform, show (2 : ℕ) = 1 + 1 from rfl, dminus_auxVar_pow_mul q 1 1 hmem,
    MvPolynomial.X_pow_eq_monomial, bopExt_monomial_one, ← MvPolynomial.X_pow_eq_monomial,
    Nat.cast_one, elemSymmAlt_one, MvPolynomial.C_neg]
  ring

/-- **`d_+^{(1)}(e_1y_1) = -e_1y_1y_2 - q(q-1)y_1^2y_2`.** The `τ_{2,2}` of `HJO.Sweep.qshift` puts
the letter `(q-1)y_2` into `e_1 = p_1`, and `T_1` turns the resulting `y_1y_2^2` into
`qy_1^2y_2`. -/
theorem dplus_one_C_elemSymm_one_mul_X_zero (q : L) :
    dplus q 1 (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L))
      = -(MvPolynomial.C (elemSymm L 1) * ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1))
        - scal (q * (q - 1)) * ((MvPolynomial.X 0 : Total L) ^ 2 * MvPolynomial.X 1) := by
  have hq2 : qshift q 2 (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L))
      = (MvPolynomial.C (Sym.powerSum L 1) + scal (q - 1) * MvPolynomial.X 1)
        * (MvPolynomial.X 0 : Total L) := by
    rw [map_mul, qshift_auxVar,
      show elemSymm L 1 = Sym.powerSum L 1 from elemSymm_one_eq_powerSum, qshift_two_powerSum]
  rw [dplus_apply, show (1 : ℕ) + 1 = 2 from rfl, hq2, auxVar_two, trainUpEnd_one_two]
  rw [show (MvPolynomial.X 1 : Total L)
        * ((MvPolynomial.C (Sym.powerSum L 1) + scal (q - 1) * MvPolynomial.X 1)
          * MvPolynomial.X 0)
      = MvPolynomial.C (Sym.powerSum L 1) * (MvPolynomial.X 0 * MvPolynomial.X 1)
        + scal (q - 1) * (MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2) from by ring]
  rw [braidEnd, LinearMap.restrictScalars_apply, map_add, braid_C_mul,
    braid_one_X_zero_mul_X_one, braid_scal_mul, braid_one_X_zero_mul_X_one_sq,
    show elemSymm L 1 = Sym.powerSum L 1 from elemSymm_one_eq_powerSum, scal_mul]
  ring

/-- **`Δ^{(2)}(y_1y_2) = -qy_1^2y_2`**, for every `q ≠ 1`: the two composites of
`HJO.Sweep.corner` both produce `e_1y_1y_2`, which cancels, and the residue is the
`q(q-1)y_1^2y_2` that `τ_{2,2}` put into the coefficient. -/
theorem corner_two_X_zero_mul_X_one (hq : q ≠ 1) :
    corner q 2 ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1)
      = -(scal q * ((MvPolynomial.X 0 : Total L) ^ 2 * MvPolynomial.X 1)) := by
  have hq' : q - 1 ≠ 0 := sub_ne_zero.2 hq
  have hs : (scal ((q - 1)⁻¹) : Total L) * scal (q * (q - 1)) = scal q := by
    rw [← scal_mul]
    congr 1
    field_simp
  rw [corner_of_pos q (show (2 : ℕ) ≠ 0 by omega), LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply, show (2 : ℕ) + 1 = 3 from rfl,
    show (2 : ℕ) - 1 = 1 from rfl, dplus_two_X_zero_mul_X_one, map_neg, dminus_three_prod,
    dminus_two_X_zero_mul_X_one, map_neg, dplus_one_C_elemSymm_one_mul_X_zero,
    smul_eq_scal_mul]
  linear_combination (-((MvPolynomial.X 0 : Total L) ^ 2 * MvPolynomial.X 1)) * hs

end HJO.Sweep

namespace HJO.Mellit

open HJO.Sweep HJO.Paths Finset

/-! ### The two above-diagonal paths of the `2 × 3` rectangle, and nothing else -/

theorem ht_baseTwoThreeA_zero : ht baseTwoThreeA 0 = 0 := by decide
theorem ht_baseTwoThreeA_one : ht baseTwoThreeA 1 = 2 := by decide
theorem ht_baseTwoThreeA_two : ht baseTwoThreeA 2 = 3 := by decide
theorem ht_baseTwoThreeB_zero : ht baseTwoThreeB 0 = 0 := by decide
theorem ht_baseTwoThreeB_one : ht baseTwoThreeB 1 = 3 := by decide
theorem ht_baseTwoThreeB_two : ht baseTwoThreeB 2 = 3 := by decide

/-- **The above-diagonal paths of the `2 × 3` rectangle are exactly two.** The end heights are
pinned, `ŷ_0 = 0` and `ŷ_2 = 3`, and the single free height satisfies `3 ≤ 2ŷ_1 ≤ 6`, so
`ŷ_1 ∈ {2, 3}`. The analogue of `HJO.Mellit.eq_baseOne` at `a = 2`, where the conclusion is a
disjunction rather than an equality — which is why the `α = []` identity here is a sum. -/
theorem eq_baseTwoThree {y : Heights 2 3 1} (hy : IsAboveDiagonal y) :
    y = baseTwoThreeA ∨ y = baseTwoThreeB := by
  have h0 : ht y 0 = 0 := hy.1
  have h2 : ht y 2 = 3 := by
    have h := hy.2.1
    norm_num at h
    exact h
  have hge : 3 ≤ 2 * ht y 1 := by
    have h := hy.2.2.2 1 (by omega)
    norm_num at h
    exact h
  have hle : ht y 1 ≤ 3 := by
    have h := ht_le_mul y 1
    norm_num at h
    exact h
  have hcase : ht y 1 = 2 ∨ ht y 1 = 3 := by omega
  have hfun : ∀ z : Heights 2 3 1, ht z 0 = 0 → ht z 1 = ht y 1 → ht z 2 = 3 → y = z := by
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
  · exact Or.inl (hfun baseTwoThreeA ht_baseTwoThreeA_zero
      (by rw [ht_baseTwoThreeA_one, hc]) ht_baseTwoThreeA_two)
  · exact Or.inr (hfun baseTwoThreeB ht_baseTwoThreeB_zero
      (by rw [ht_baseTwoThreeB_one, hc]) ht_baseTwoThreeB_two)

/-- **The index set of the `α = []`, `A = 1` sum at `(a,b) = (2,3)`**: the two paths of
`HJO.Mellit.one_lt_card_aboveReturnPaths_two_three_one`, and no others. -/
theorem aboveReturnPaths_two_three_one :
    aboveReturnPaths 2 3 1 [1] = {baseTwoThreeA, baseTwoThreeB} := by
  ext y
  rw [mem_aboveReturnPaths_iff, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨fun h => eq_baseTwoThree h.1, ?_⟩
  rintro (rfl | rfl)
  · exact hasAboveReturns_baseTwoThreeA
  · exact hasAboveReturns_baseTwoThreeB

/-! ### The ranks of the `2 × 3` rectangle, and the isolating windows -/

theorem rank_mem_two_three (Q : ℕ × ℕ) (h1 : Q.1 ≤ 2) (h2 : Q.2 ≤ 3) :
    pointRank 2 3 1 Q ∈ ({-16, -10, -8, -4, -2, 0, 2, 4, 6, 10, 12, 18} : Finset ℤ) := by
  obtain ⟨x, y⟩ := Q
  simp only at h1 h2
  interval_cases x <;> interval_cases y <;> decide

theorem lt_of_half_lt {m z : ℤ} (h : ((m : ℚ) + 1 / 2) < (z : ℚ)) : m < z := by
  by_contra hc
  have hle : ((z : ℚ)) ≤ (m : ℚ) := by exact_mod_cast not_lt.1 hc
  linarith

theorem le_of_lt_half {m z : ℤ} (h : (z : ℚ) < (m : ℚ) + 1 / 2) : z ≤ m := by
  by_contra hc
  have hle : ((m : ℚ) + 1) ≤ (z : ℚ) := by
    have : m + 1 ≤ z := by omega
    exact_mod_cast this
  linarith

/-- **An isolating window of the `2 × 3` rectangle.** Between two half-integer levels `m + 1/2` and
`n + 1/2` the only rank of the rectangle is `r`, which is the isolation hypothesis of
`HJO.Mellit.partialSweepWord_eq_sweepOperator_mul`. The finite list of ranks is
`HJO.Mellit.rank_mem_two_three`, so the check is one decidable statement about twelve integers. -/
theorem iso_of_window {m n r : ℤ}
    (hr : ∀ z ∈ ({-16, -10, -8, -4, -2, 0, 2, 4, 6, 10, 12, 18} : Finset ℤ),
      m < z → z ≤ n → z = r)
    {P : ℕ × ℕ} (hPr : pointRank 2 3 1 P = r) :
    ∀ Q : ℕ × ℕ, Q.1 ≤ 2 * 1 → Q.2 ≤ 3 * 1 →
      ((m : ℚ) + 1 / 2) < ((pointRank 2 3 1 Q : ℤ) : ℚ) →
      ((pointRank 2 3 1 Q : ℤ) : ℚ) < ((n : ℚ) + 1 / 2) →
      pointRank 2 3 1 Q = pointRank 2 3 1 P := by
  intro Q hQ1 hQ2 hlo hup
  rw [hPr]
  exact hr _ (rank_mem_two_three Q (by omega) (by omega)) (lt_of_half_lt hlo) (le_of_lt_half hup)

theorem isAdmissibleLevel_int_add_half (m : ℤ) : IsAdmissibleLevel ((m : ℚ) + 1 / 2) :=
  ⟨m, rfl⟩

theorem pointRank_one_two : pointRank 2 3 1 ((1, 2) : ℕ × ℕ) = 4 := by decide
theorem pointRank_zero_one : pointRank 2 3 1 ((0, 1) : ℕ × ℕ) = 6 := by decide
theorem pointRank_one_three : pointRank 2 3 1 ((1, 3) : ℕ × ℕ) = 10 := by decide
theorem pointRank_zero_two : pointRank 2 3 1 ((0, 2) : ℕ × ℕ) = 12 := by decide
theorem pointRank_zero_three : pointRank 2 3 1 ((0, 3) : ℕ × ℕ) = 18 := by decide

theorem sepLevel_two_one : sepLevel 2 1 = ((2 : ℤ) : ℚ) + 1 / 2 := by
  rw [sepLevel]
  norm_num

/-! ### The events of the two paths, and their operators -/

theorem eventType_baseTwoThreeA_one_two :
    eventType baseTwoThreeA ((1, 2) : ℕ × ℕ) = EventType.B := by decide
theorem sweepWidth_baseTwoThreeA_one_two :
    sweepWidth baseTwoThreeA ((1, 2) : ℕ × ℕ) = 2 := by decide
theorem eventType_baseTwoThreeA_zero_one :
    eventType baseTwoThreeA ((0, 1) : ℕ × ℕ) = EventType.C := by decide
theorem sweepWidth_baseTwoThreeA_zero_one :
    sweepWidth baseTwoThreeA ((0, 1) : ℕ × ℕ) = 2 := by decide
theorem sweepRight_baseTwoThreeA_zero_one :
    sweepRight baseTwoThreeA ((0, 1) : ℕ × ℕ) = 1 := by decide
theorem eventType_baseTwoThreeA_one_three :
    eventType baseTwoThreeA ((1, 3) : ℕ × ℕ) = EventType.A := by decide
theorem sweepWidth_baseTwoThreeA_one_three :
    sweepWidth baseTwoThreeA ((1, 3) : ℕ × ℕ) = 1 := by decide
theorem eventType_baseTwoThreeA_zero_two :
    eventType baseTwoThreeA ((0, 2) : ℕ × ℕ) = EventType.A := by decide
theorem sweepWidth_baseTwoThreeA_zero_two :
    sweepWidth baseTwoThreeA ((0, 2) : ℕ × ℕ) = 0 := by decide

theorem eventType_baseTwoThreeB_one_two :
    eventType baseTwoThreeB ((1, 2) : ℕ × ℕ) = EventType.E := by decide
theorem eventType_baseTwoThreeB_zero_one :
    eventType baseTwoThreeB ((0, 1) : ℕ × ℕ) = EventType.C := by decide
theorem sweepWidth_baseTwoThreeB_zero_one :
    sweepWidth baseTwoThreeB ((0, 1) : ℕ × ℕ) = 1 := by decide
theorem sweepRight_baseTwoThreeB_zero_one :
    sweepRight baseTwoThreeB ((0, 1) : ℕ × ℕ) = 0 := by decide
theorem eventType_baseTwoThreeB_one_three :
    eventType baseTwoThreeB ((1, 3) : ℕ × ℕ) = EventType.D := by decide
theorem sweepRight_baseTwoThreeB_one_three :
    sweepRight baseTwoThreeB ((1, 3) : ℕ × ℕ) = 0 := by decide
theorem eventType_baseTwoThreeB_zero_two :
    eventType baseTwoThreeB ((0, 2) : ℕ × ℕ) = EventType.C := by decide
theorem sweepWidth_baseTwoThreeB_zero_two :
    sweepWidth baseTwoThreeB ((0, 2) : ℕ × ℕ) = 1 := by decide
theorem sweepRight_baseTwoThreeB_zero_two :
    sweepRight baseTwoThreeB ((0, 2) : ℕ × ℕ) = 0 := by decide
theorem eventType_baseTwoThreeB_zero_three :
    eventType baseTwoThreeB ((0, 3) : ℕ × ℕ) = EventType.A := by decide
theorem sweepWidth_baseTwoThreeB_zero_three :
    sweepWidth baseTwoThreeB ((0, 3) : ℕ × ℕ) = 0 := by decide

theorem mem_sweptRegion_baseTwoThreeA_one_two :
    ((1, 2) : ℕ × ℕ) ∈ sweptRegion baseTwoThreeA := by decide
theorem mem_sweptRegion_baseTwoThreeA_zero_one :
    ((0, 1) : ℕ × ℕ) ∈ sweptRegion baseTwoThreeA := by decide
theorem mem_sweptRegion_baseTwoThreeA_one_three :
    ((1, 3) : ℕ × ℕ) ∈ sweptRegion baseTwoThreeA := by decide
theorem mem_sweptRegion_baseTwoThreeA_zero_two :
    ((0, 2) : ℕ × ℕ) ∈ sweptRegion baseTwoThreeA := by decide
theorem mem_sweptRegion_baseTwoThreeB_one_two :
    ((1, 2) : ℕ × ℕ) ∈ sweptRegion baseTwoThreeB := by decide
theorem mem_sweptRegion_baseTwoThreeB_zero_one :
    ((0, 1) : ℕ × ℕ) ∈ sweptRegion baseTwoThreeB := by decide
theorem mem_sweptRegion_baseTwoThreeB_one_three :
    ((1, 3) : ℕ × ℕ) ∈ sweptRegion baseTwoThreeB := by decide
theorem mem_sweptRegion_baseTwoThreeB_zero_two :
    ((0, 2) : ℕ × ℕ) ∈ sweptRegion baseTwoThreeB := by decide
theorem mem_sweptRegion_baseTwoThreeB_zero_three :
    ((0, 3) : ℕ × ℕ) ∈ sweptRegion baseTwoThreeB := by decide

theorem pointRank_le_baseTwoThreeA :
    ∀ P ∈ sweptRegion baseTwoThreeA, pointRank 2 3 1 P ≤ 12 := by decide
theorem pointRank_le_baseTwoThreeB :
    ∀ P ∈ sweptRegion baseTwoThreeB, pointRank 2 3 1 P ≤ 18 := by decide

section Words

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- Above the top rank of a path the partial word is empty. -/
theorem partialSweepWord_top (q u : L) {y : Heights 2 3 1} {m : ℤ}
    (h : ∀ P ∈ sweptRegion y, pointRank 2 3 1 P ≤ m) :
    partialSweepWord q u y (((m : ℚ)) + 1 / 2) = 1 := by
  refine partialSweepWord_of_forall_le q u y _ fun P hP => ?_
  have hle : ((pointRank 2 3 1 P : ℤ) : ℚ) ≤ ((m : ℤ) : ℚ) := by exact_mod_cast h P hP
  linarith

/-- One step of the peeling at `(a,b) = (2,3)`, `N = 1`. -/
theorem partialSweepWord_step (q u : L) {y : Heights 2 3 1} {P : ℕ × ℕ} {m n r : ℤ}
    (hr : ∀ z ∈ ({-16, -10, -8, -4, -2, 0, 2, 4, 6, 10, 12, 18} : Finset ℤ),
      m < z → z ≤ n → z = r)
    (hPr : pointRank 2 3 1 P = r) (hlo : ((m : ℚ) + 1 / 2) < (r : ℚ))
    (hup : ((r : ℚ)) < ((n : ℚ) + 1 / 2)) (hPmem : P ∈ sweptRegion y) :
    partialSweepWord q u y ((m : ℚ) + 1 / 2)
      = sweepOperator q u y P * partialSweepWord q u y ((n : ℚ) + 1 / 2) := by
  refine partialSweepWord_eq_sweepOperator_mul q u (by omega)
    (isAdmissibleLevel_int_add_half n) ?_ ?_ (iso_of_window hr hPr) hPmem
  · rw [hPr]; exact_mod_cast hlo
  · rw [hPr]; exact_mod_cast hup

/-! ### The two words of the `2 × 3` rectangle at the separating level -/

/-- **The word of the above-diagonal path `(0,2,3)`:** `d_-^{(2)}q^{-1}Δ^{(2)}d_+^{(1)}d_+^{(0)}`.
The four events are peeled one at a time by `HJO.Mellit.partialSweepWord_step`; the widths reach
`2`, so this is the first `hzero` word that leaves `y_1V_1`. -/
theorem partialSweepWord_baseTwoThreeA (q u : L) :
    partialSweepWord q u baseTwoThreeA (sepLevel 2 1)
      = dminus q 2 * ((((q ^ (-1 : ℤ) : L)) • corner q 2) * (dplus q 1 * (dplus q 0 * 1))) := by
  have op1 : sweepOperator q u baseTwoThreeA ((1, 2) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator, eventType_baseTwoThreeA_one_two, sweepWidth_baseTwoThreeA_one_two]
  have op2 : sweepOperator q u baseTwoThreeA ((0, 1) : ℕ × ℕ)
      = ((q ^ (-1 : ℤ) : L)) • corner q 2 := by
    rw [sweepOperator, eventType_baseTwoThreeA_zero_one, sweepWidth_baseTwoThreeA_zero_one,
      sweepRight_baseTwoThreeA_zero_one]
    norm_num
  have op3 : sweepOperator q u baseTwoThreeA ((1, 3) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator, eventType_baseTwoThreeA_one_three, sweepWidth_baseTwoThreeA_one_three]
  have op4 : sweepOperator q u baseTwoThreeA ((0, 2) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator, eventType_baseTwoThreeA_zero_two, sweepWidth_baseTwoThreeA_zero_two]
  rw [sepLevel_two_one,
    partialSweepWord_step q u (m := 2) (n := 4) (r := 4) (by decide) pointRank_one_two
      (by norm_num) (by norm_num) mem_sweptRegion_baseTwoThreeA_one_two,
    partialSweepWord_step q u (m := 4) (n := 7) (r := 6) (by decide) pointRank_zero_one
      (by norm_num) (by norm_num) mem_sweptRegion_baseTwoThreeA_zero_one,
    partialSweepWord_step q u (m := 7) (n := 10) (r := 10) (by decide) pointRank_one_three
      (by norm_num) (by norm_num) mem_sweptRegion_baseTwoThreeA_one_three,
    partialSweepWord_step q u (m := 10) (n := 12) (r := 12) (by decide) pointRank_zero_two
      (by norm_num) (by norm_num) mem_sweptRegion_baseTwoThreeA_zero_two,
    partialSweepWord_top q u pointRank_le_baseTwoThreeA, op1, op2, op3, op4]

/-- **The word of the above-diagonal path `(0,3,3)`:** `uΔ^{(1)}Δ^{(1)}d_+^{(0)}`, with one
type-`E` event contributing the `u` and one type-`D` event contributing `q^0 = 1`. Every width is
`1`, so this path stays inside `y_1V_1` and `HJO.Sweep.corner_one_auxVar_pow` evaluates
it. -/
theorem partialSweepWord_baseTwoThreeB (q u : L) :
    partialSweepWord q u baseTwoThreeB (sepLevel 2 1)
      = (u • (1 : Module.End L (Total L))) * (corner q 1 * ((1 : Module.End L (Total L))
        * (corner q 1 * (dplus q 0 * 1)))) := by
  have op1 : sweepOperator q u baseTwoThreeB ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator, eventType_baseTwoThreeB_one_two]
  have op2 : sweepOperator q u baseTwoThreeB ((0, 1) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator, eventType_baseTwoThreeB_zero_one, sweepWidth_baseTwoThreeB_zero_one,
      sweepRight_baseTwoThreeB_zero_one]
    norm_num
  have op3 : sweepOperator q u baseTwoThreeB ((1, 3) : ℕ × ℕ)
      = (1 : Module.End L (Total L)) := by
    rw [sweepOperator, eventType_baseTwoThreeB_one_three, sweepRight_baseTwoThreeB_one_three]
    norm_num
  have op4 : sweepOperator q u baseTwoThreeB ((0, 2) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator, eventType_baseTwoThreeB_zero_two, sweepWidth_baseTwoThreeB_zero_two,
      sweepRight_baseTwoThreeB_zero_two]
    norm_num
  have op5 : sweepOperator q u baseTwoThreeB ((0, 3) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator, eventType_baseTwoThreeB_zero_three, sweepWidth_baseTwoThreeB_zero_three]
  rw [sepLevel_two_one,
    partialSweepWord_step q u (m := 2) (n := 4) (r := 4) (by decide) pointRank_one_two
      (by norm_num) (by norm_num) mem_sweptRegion_baseTwoThreeB_one_two,
    partialSweepWord_step q u (m := 4) (n := 7) (r := 6) (by decide) pointRank_zero_one
      (by norm_num) (by norm_num) mem_sweptRegion_baseTwoThreeB_zero_one,
    partialSweepWord_step q u (m := 7) (n := 10) (r := 10) (by decide) pointRank_one_three
      (by norm_num) (by norm_num) mem_sweptRegion_baseTwoThreeB_one_three,
    partialSweepWord_step q u (m := 10) (n := 12) (r := 12) (by decide) pointRank_zero_two
      (by norm_num) (by norm_num) mem_sweptRegion_baseTwoThreeB_zero_two,
    partialSweepWord_step q u (m := 12) (n := 18) (r := 18) (by decide) pointRank_zero_three
      (by norm_num) (by norm_num) mem_sweptRegion_baseTwoThreeB_zero_three,
    partialSweepWord_top q u pointRank_le_baseTwoThreeB, op1, op2, op3, op4, op5]

/-! ### The two words at the vacuum -/

/-- **The `(0,2,3)` path contributes `e_1y_1^2`.** -/
theorem partialSweepWord_baseTwoThreeA_apply_one (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u baseTwoThreeA (sepLevel 2 1) (1 : Total L)
      = MvPolynomial.C (Sym.elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2 := by
  have hs : (scal ((q : L) ^ (-1 : ℤ)) : Total L) * scal q = 1 := by
    rw [← scal_mul, zpow_neg_one, inv_mul_cancel₀ hq0, scal_one]
  have hmid : ((q : L) ^ (-1 : ℤ))
        • (-(scal q * ((MvPolynomial.X 0 : Total L) ^ 2 * MvPolynomial.X 1)))
      = -((MvPolynomial.X 0 : Total L) ^ 2 * MvPolynomial.X 1) := by
    rw [smul_neg, smul_eq_scal_mul, ← mul_assoc, hs, one_mul]
  rw [partialSweepWord_baseTwoThreeA q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [dplus_zero_one, map_neg, dplus_one_X_zero, neg_neg, corner_two_X_zero_mul_X_one hq1, hmid,
    map_neg, dminus_two_X_zero_sq_mul_X_one, neg_neg]

/-- **The `(0,3,3)` path contributes `-uy_1^3`.** -/
theorem partialSweepWord_baseTwoThreeB_apply_one (q u : L) (hq1 : q ≠ 1) :
    partialSweepWord q u baseTwoThreeB (sepLevel 2 1) (1 : Total L)
      = -(scal u * (MvPolynomial.X 0 : Total L) ^ 3) := by
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hc2 : corner q 1 ((MvPolynomial.X 0 : Total L) ^ 2)
      = -((MvPolynomial.X 0 : Total L) ^ 3) := by
    have h := corner_one_auxVar_pow (L := L) hq1 2
    rw [hav] at h
    exact h
  rw [partialSweepWord_baseTwoThreeB q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [dplus_zero_one, map_neg, corner_one_X_zero (q := q) hq1, neg_neg, hc2, smul_neg,
    smul_eq_scal_mul]

/-! ### The invariant of the `2 × 3` rectangle at `c_{(1)}` -/

/-- **`D_{5/2,c_{(1)}} = e_1y_1^2 - uy_1^3` in the `2 × 3` rectangle**, for `q ∉ {0, 1}`: the sum
of the two words of `HJO.Mellit.aboveReturnPaths_two_three_one`. This is the first evaluation of a
`HJO.Mellit.dsc` at `a ≥ 2`, where the index set is not a singleton. -/
theorem dsc_two_three_one (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dsc q u 2 3 1 (sepLevel 2 1) (compColouring 2 3 [1])
      = MvPolynomial.C (Sym.elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2
        - scal u * (MvPolynomial.X 0 : Total L) ^ 3 := by
  have hne : baseTwoThreeA ≠ baseTwoThreeB := by decide
  rw [dsc_compColouring_eq_sum_partialSweepWord q u (isAdmissibleLevel_sepLevel 2 1)
      (separatesDiagonal_sepLevel' 2 3 1) (by decide) (by omega) (by omega)
      (by simp) (by simp),
    aboveReturnPaths_two_three_one, Finset.sum_insert (by simpa using hne),
    Finset.sum_singleton, partialSweepWord_baseTwoThreeA_apply_one q u hq0 hq1,
    partialSweepWord_baseTwoThreeB_apply_one q u hq1]
  ring

end Words

end HJO.Mellit

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The one-letter displacement of `e_2` -/

omit [Algebra ℚ L] in
theorem scal_two : (scal (2 : L) : Total L) = 2 := by
  rw [scal_eq_algebraMap]
  exact map_ofNat _ 2

omit [Algebra ℚ L] in
theorem scal_pow' (x : L) (n : ℕ) : (scal (x ^ n) : Total L) = scal x ^ n := by
  rw [scal_eq_algebraMap, scal_eq_algebraMap, map_pow]

theorem scal_half_mul_two :
    (scal (algebraMap ℚ L (2⁻¹ : ℚ)) : Total L) * 2 = 1 := by
  have h2 : (2 : L) = algebraMap ℚ L (2 : ℚ) := by norm_num
  rw [← scal_two, ← scal_mul, h2, ← map_mul]
  norm_num

theorem C_elemSymm_two_eq (L : Type*) [Field L] [Algebra ℚ L] :
    (MvPolynomial.C (elemSymm L 2) : Total L)
      = scal (algebraMap ℚ L (2⁻¹ : ℚ))
        * (MvPolynomial.C (powerSum L 1) * MvPolynomial.C (powerSum L 1)
          - MvPolynomial.C (powerSum L 2)) := by
  rw [elemSymm_two_eq, map_mul, map_sub, map_mul]
  rfl

omit [Algebra ℚ L] in
theorem qshift_one_C_powerSum_one (q : L) :
    qshift q 1 (MvPolynomial.C (powerSum L 1) : Total L)
      = MvPolynomial.C (powerSum L 1) + scal (q - 1) * (MvPolynomial.X 0 : Total L) := by
  have h := qshift_powerSum q 1 0
  rw [show (0 : ℕ) + 1 = 1 from rfl, pow_one, pow_one] at h
  exact h

omit [Algebra ℚ L] in
theorem qshift_one_C_powerSum_two (q : L) :
    qshift q 1 (MvPolynomial.C (powerSum L 2) : Total L)
      = MvPolynomial.C (powerSum L 2) + scal (q ^ 2 - 1) * (MvPolynomial.X 0 : Total L) ^ 2 := by
  have h := qshift_powerSum q 1 1
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  exact h

/-- **`d^*_+{}^{(0)}(Ce_2) - Ce_2 = (q-1)u(e_1y_1 - uy_1^2)`.** The starred raising operator adds
the virtual letter `(q-1)uy_1` to the alphabet: `τ_{1,1}` of `HJO.Sweep.qshift` puts `(q-1)y_1` into
each power sum and `cy_1` of `HJO.Sweep.cycleShift` then multiplies `y_1` by `u`. On
`e_2 = (p_1^2 - p_2)/2` the displacement is the single cross term, the two `y_1^2` contributions
`(q-1)^2` and `q^2-1` differing by exactly `-2(q-1)`. -/
theorem dplusStar_zero_C_elemSymm_two (q u : L) :
    dplusStar q u 0 (MvPolynomial.C (elemSymm L 2) : Total L)
      = MvPolynomial.C (elemSymm L 2)
        + scal ((q - 1) * u) * (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L))
        - scal ((q - 1) * u ^ 2) * ((MvPolynomial.X 0 : Total L) ^ 2) := by
  have hc : (scal (algebraMap ℚ L (2⁻¹ : ℚ)) : Total L) * 2 = 1 := scal_half_mul_two
  rw [dplusStar_apply, C_elemSymm_two_eq, elemSymm_one_eq_powerSum]
  simp only [show (0 : ℕ) + 1 = 1 from rfl, map_mul, map_sub, map_add, map_pow, map_one,
    qshift_scal, qshift_one_C_powerSum_one, qshift_one_C_powerSum_two, cycleShift_scal,
    cycleShift_C, cycleShift_zero_X_zero, scal_mul, scal_sub, scal_one, scal_pow']
  linear_combination ((scal q - 1) * scal u * (MvPolynomial.C (powerSum L 1) * MvPolynomial.X 0)
    - (scal q - 1) * scal u ^ 2 * (MvPolynomial.X 0 : Total L) ^ 2) * hc

end HJO.Sweep

namespace HJO.Mellit

open HJO.Sweep HJO.Sym HJO.Paths Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The stage at `(2,3)`, `α = []`, `A = 1` -/

/-- **`Ω(1;2,3)(1) = -(e_1y_1^2 - uy_1^3)`.** The slope word `β_{2,3} = yzy` is read by
`HJO.Sweep.slopeOperator_two_three_auxVar`, whose middle letter is
`HJO.Sweep.zopOneStar_one_auxVar_sq`, and the displacement is
`HJO.Sweep.dplusStar_zero_C_elemSymm_two`. The three inverses of the word — `(qu)^{-1}` from
`HJO.Sweep.slopeOperator` and `(1-q)^{-1}` from `HJO.Sweep.zop` — cancel the `(q-1)u` of the
displacement exactly, which is where `q ∉ {0,1}` and `u ≠ 0` are spent. -/
theorem replOneTotal_two_three (q u : L) (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    replOneTotal q u 2 3 0 (1 : Total L)
      = -(MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2
          - scal u * (MvPolynomial.X 0 : Total L) ^ 3) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have ha : (scal ((q * u)⁻¹ * (q / (1 - q))) : Total L) * scal ((q - 1) * u) = -1 := by
    rw [← scal_mul, show (q * u)⁻¹ * (q / (1 - q)) * ((q - 1) * u) = -1 from by
      field_simp
      ring, scal_neg, scal_one]
  have hb : (scal ((q * u)⁻¹ * (q / (1 - q))) : Total L) * scal ((q - 1) * u ^ 2) = -scal u := by
    rw [← scal_mul, show (q * u)⁻¹ * (q / (1 - q)) * ((q - 1) * u ^ 2) = -u from by
      field_simp
      ring, scal_neg]
  have hstep : replOneTotal q u 2 3 0 (1 : Total L)
      = slopeOperator q u 1 2 3 (auxVar 1 : Total L) := by
    rw [replOneTotal]
    simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.neg_apply,
      LinearMap.mulLeft_apply, dplusStar_one, mul_one, map_neg]
    norm_num
  rw [hstep, slopeOperator_two_three_auxVar, dplusStar_zero_C_elemSymm_two, hav,
    smul_eq_scal_mul]
  linear_combination (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2) * ha
    - ((MvPolynomial.X 0 : Total L) ^ 3) * hb

/-! ### The instance -/

/-- **`HJO.Mellit.SweepAppend` at `α = []`, `A = 1`, `(a,b) = (2,3)`, verbatim, and it is TRUE for
every `q ∉ {0, 1}` and every `u ≠ 0`.** Both sides are `e_1y_1^2 - uy_1^3`: the left by
`HJO.Mellit.dsc_two_three_one`, a sum over the TWO paths of
`HJO.Mellit.aboveReturnPaths_two_three_one`, and the right by
`HJO.Mellit.replOneTotal_two_three`.

This is the first instance of the `α = []` clause — the `hzero` hypothesis of
`HJO.Mellit.sweepAppend_of_forall_band` — at `a ≥ 2`, where
`HJO.Mellit.one_lt_card_aboveReturnPaths_two_three_one` says the index set is not a singleton, so
`HJO.Mellit.sweepAppend_nil_one_one_b`'s method does not reach it. The widths of the first path's
word reach `2`, so the identity is not a statement about `y_1V_1` either: it needs
`HJO.Sweep.corner_two_X_zero_mul_X_one`, a corner operator at width `2`.

`q ≠ 1` is necessary (`HJO.Mellit.not_sweepAppend_one_left`); `q ≠ 0` is necessary too at
`a = 2`, the type-`C` event at `(0,1)` carrying `q^{-1}` and the `z` letter of `β_{2,3}` carrying
`(qu)^{-1}`, both of which the field's `0⁻¹ = 0` would annihilate. -/
theorem sweepAppend_nil_two_three_one (q u : L) (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    dsc q u 2 3 (([] : List ℕ).sum + 1) (sepLevel 2 (([] : List ℕ).sum + 1))
        (compColouring 2 3 ([] ++ [1]))
      = ((-1 : L) ^ ((2 - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) •
          stageTotal q u 2 3 ([] : List ℕ).length 1
            (dsc q u 2 3 ([] : List ℕ).sum (sepLevel 2 ([] : List ℕ).sum)
              (compColouring 2 3 ([] : List ℕ))) := by
  have hc : compColouring 2 3 ([] : List ℕ) = (∅ : Finset (ℕ × ℕ)) := by
    simp [compColouring]
  have hone : dsc q u 2 3 0 (sepLevel 2 0) (compColouring 2 3 ([] : List ℕ)) = (1 : Total L) := by
    rw [hc]
    exact dsc_empty_eq_one q u (isAdmissibleLevel_sepLevel 2 0)
      (separatesDiagonal_sepLevel' 2 3 0) (by decide) (by omega) (by omega)
  simp only [List.sum_nil, List.length_nil, List.nil_append, Nat.zero_add]
  rw [hone, stageTotal_one, Module.End.mul_apply,
    show trainDownEnd q (0 + 1) 1 = 1 from Braid.trainDown_self _ _ 1, Module.End.one_apply,
    replOneTotal_two_three q u hq0 hu0 hq1, dsc_two_three_one q u hq0 hq1]
  norm_num

/-! ### Why `q ≠ 0` is not decoration

`HJO.Mellit.not_sweepAppend_one_left` refutes the `α = []` clause at `q = 1`, where `(q-1)^{-1}` of
`HJO.Sweep.corner` collapses. At `a ≥ 2` there is a second degenerate value, and it is NOT visible
at `a = 1`: the type-`C` event at `(0,1)` of the path `(0,2,3)` has one live north step to its
right, so `HJO.Mellit.sweepOperator` gives it the factor `q^{-a_{P̂}} = q^{-1}`, and the letter `z`
of `β_{2,3} = yzy` carries `(qu)^{-1}` from `HJO.Sweep.slopeOperator`. In a field `0⁻¹ = 0`, so at
`q = 0` the first annihilates the path `(0,2,3)` and the second annihilates the whole right-hand
side, while the path `(0,3,3)` survives untouched. -/

/-- `Ω(1;2,3)(1)` is the slope operator at `y_1`, with no hypothesis on `q` or `u`. -/
theorem replOneTotal_two_three_eq_slopeOperator (q u : L) :
    replOneTotal q u 2 3 0 (1 : Total L) = slopeOperator q u 1 2 3 (auxVar 1 : Total L) := by
  rw [replOneTotal]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.neg_apply,
    LinearMap.mulLeft_apply, dplusStar_one, mul_one, map_neg]
  norm_num

/-- **At `q = 0` the right-hand side is zero.** The `z` letter of `β_{2,3}` carries `(qu)^{-1}`, and
`0⁻¹ = 0` in a field makes that letter the zero map. -/
theorem replOneTotal_two_three_zero (u : L) :
    replOneTotal (0 : L) u 2 3 0 (1 : Total L) = 0 := by
  rw [replOneTotal_two_three_eq_slopeOperator, slopeOperator_two_three]
  simp only [zero_mul, inv_zero, zero_smul, mul_zero, LinearMap.zero_apply]

/-- **At `q = 0` the path `(0,2,3)` is annihilated**, its type-`C` event carrying `q^{-1}`. -/
theorem partialSweepWord_baseTwoThreeA_apply_one_zero (u : L) :
    partialSweepWord (0 : L) u baseTwoThreeA (sepLevel 2 1) (1 : Total L) = 0 := by
  rw [partialSweepWord_baseTwoThreeA (0 : L) u]
  simp only [Module.End.mul_apply, Module.End.one_apply, zpow_neg_one, inv_zero, zero_smul,
    LinearMap.zero_apply, map_zero]

/-- **At `q = 0` the invariant is `-uy_1^3`**, the surviving path `(0,3,3)` alone. -/
theorem dsc_two_three_one_zero (u : L) :
    dsc (0 : L) u 2 3 1 (sepLevel 2 1) (compColouring 2 3 [1])
      = -(scal u * (MvPolynomial.X 0 : Total L) ^ 3) := by
  have hne : baseTwoThreeA ≠ baseTwoThreeB := by decide
  rw [dsc_compColouring_eq_sum_partialSweepWord (0 : L) u (isAdmissibleLevel_sepLevel 2 1)
      (separatesDiagonal_sepLevel' 2 3 1) (by decide) (by omega) (by omega)
      (by simp) (by simp),
    aboveReturnPaths_two_three_one, Finset.sum_insert (by simpa using hne),
    Finset.sum_singleton, partialSweepWord_baseTwoThreeA_apply_one_zero u,
    partialSweepWord_baseTwoThreeB_apply_one (0 : L) u (by norm_num), zero_add]

/-- **The `α = []`, `A = 1`, `(a,b) = (2,3)` clause is FALSE at `q = 0`, for every `u ≠ 0`.** So the
hypothesis `q ≠ 0` of `HJO.Mellit.sweepAppend_nil_two_three_one` is necessary, and the `α = []`
clause needs `q ∉ {0,1}` rather than the `q ≠ 1` that suffices at `a = 1`: at `a = 1` no event has a
live north step to its right and the slope word has no letter `z`, so no negative power of `q`
occurs anywhere. -/
theorem not_sweepAppend_nil_two_three_one_of_q_zero (u : L) (hu : u ≠ 0) :
    dsc (0 : L) u 2 3 (([] : List ℕ).sum + 1) (sepLevel 2 (([] : List ℕ).sum + 1))
        (compColouring 2 3 ([] ++ [1]))
      ≠ (((-1 : L)) ^ ((2 - 1) * 1) * ((0 : L) * u) ^ (1 - ((1 : ℕ) : ℤ))) •
          stageTotal (0 : L) u 2 3 ([] : List ℕ).length 1
            (dsc (0 : L) u 2 3 ([] : List ℕ).sum (sepLevel 2 ([] : List ℕ).sum)
              (compColouring 2 3 ([] : List ℕ))) := by
  have hc : compColouring 2 3 ([] : List ℕ) = (∅ : Finset (ℕ × ℕ)) := by
    simp [compColouring]
  have hone : dsc (0 : L) u 2 3 0 (sepLevel 2 0) (compColouring 2 3 ([] : List ℕ))
      = (1 : Total L) := by
    rw [hc]
    exact dsc_empty_eq_one (0 : L) u (isAdmissibleLevel_sepLevel 2 0)
      (separatesDiagonal_sepLevel' 2 3 0) (by decide) (by omega) (by omega)
  have hnz : (scal u * (MvPolynomial.X 0 : Total L) ^ 3) ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero 3 (MvPolynomial.X_ne_zero 0))
    rw [scal]
    exact MvPolynomial.C_ne_zero.2 (MvPolynomial.C_ne_zero.2 hu)
  simp only [List.sum_nil, List.length_nil, List.nil_append, Nat.zero_add]
  rw [hone, stageTotal_one, Module.End.mul_apply,
    show trainDownEnd (0 : L) (0 + 1) 1 = 1 from Braid.trainDown_self _ _ 1,
    Module.End.one_apply, replOneTotal_two_three_zero u, smul_zero,
    dsc_two_three_one_zero u]
  exact neg_ne_zero.2 hnz


/-- **At `u = 0` the right-hand side is zero too**, for every `q`: the `z` letter of `β_{2,3}`
carries `(qu)^{-1}`, which `u = 0` annihilates just as `q = 0` does. -/
theorem replOneTotal_two_three_u_zero (q : L) :
    replOneTotal q (0 : L) 2 3 0 (1 : Total L) = 0 := by
  rw [replOneTotal_two_three_eq_slopeOperator, slopeOperator_two_three]
  simp only [mul_zero, zero_mul, inv_zero, zero_smul, LinearMap.zero_apply]

/-- **The `α = []`, `A = 1`, `(a,b) = (2,3)` clause is FALSE at `u = 0`, for every `q ∉ {0,1}`.** So
the hypothesis `u ≠ 0` of `HJO.Mellit.sweepAppend_nil_two_three_one` is necessary as well: the
sweep side is untouched by `u = 0` — the type-`E` event of the path `(0,3,3)` merely contributes
the factor `0`, leaving the other path's `e_1y_1^2` — while the slope operator's `(qu)^{-1}`
collapses. With
`HJO.Mellit.not_sweepAppend_nil_two_three_one_of_q_zero` and
`HJO.Mellit.not_sweepAppend_one_left` this accounts for all three hypotheses. -/
theorem not_sweepAppend_nil_two_three_one_of_u_zero (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dsc q (0 : L) 2 3 (([] : List ℕ).sum + 1) (sepLevel 2 (([] : List ℕ).sum + 1))
        (compColouring 2 3 ([] ++ [1]))
      ≠ (((-1 : L)) ^ ((2 - 1) * 1) * (q * (0 : L)) ^ (1 - ((1 : ℕ) : ℤ))) •
          stageTotal q (0 : L) 2 3 ([] : List ℕ).length 1
            (dsc q (0 : L) 2 3 ([] : List ℕ).sum (sepLevel 2 ([] : List ℕ).sum)
              (compColouring 2 3 ([] : List ℕ))) := by
  have hc : compColouring 2 3 ([] : List ℕ) = (∅ : Finset (ℕ × ℕ)) := by
    simp [compColouring]
  have hone : dsc q (0 : L) 2 3 0 (sepLevel 2 0) (compColouring 2 3 ([] : List ℕ))
      = (1 : Total L) := by
    rw [hc]
    exact dsc_empty_eq_one q (0 : L) (isAdmissibleLevel_sepLevel 2 0)
      (separatesDiagonal_sepLevel' 2 3 0) (by decide) (by omega) (by omega)
  have hnz : (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2) ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero 2 (MvPolynomial.X_ne_zero 0))
    rw [elemSymm_one_eq_X]
    exact MvPolynomial.C_ne_zero.2 (MvPolynomial.X_ne_zero 0)
  simp only [List.sum_nil, List.length_nil, List.nil_append, Nat.zero_add]
  rw [hone, stageTotal_one, Module.End.mul_apply,
    show trainDownEnd q (0 + 1) 1 = 1 from Braid.trainDown_self _ _ 1,
    Module.End.one_apply, replOneTotal_two_three_u_zero q, smul_zero,
    dsc_two_three_one q (0 : L) hq0 hq1, scal_zero, zero_mul, sub_zero]
  exact hnz

end HJO.Mellit
