/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitLevelRaise

/-! # The slope word on the row `a = 2`, and `z_1` on the graded piece of index `2`

`HJO.Sweep.lowerRun_two_stageTotal_levelKernelOne`
(`HJO/Shuffle/MellitLevelRaise.lean`) reduces the level-raising factorization question to a
single missing input: the slope operator `Ξ_{a,b}` read on the graded piece `V_2` rather than on
`V_1`, applied to one explicit vector. This file supplies the two structural halves of that input
on the whole coprime row `a = 2`.

## The slope word on the row carries exactly one `z`

`HJO.Mellit.slopeWord_two_odd`: `β_{2,2k+1} = y^k z y^k`. So **whatever `k`**, the word has exactly
one `z` letter, sitting in the middle, with `k` copies of `y` on each side. Coprimality of `(2,b)`
forces `b` odd, so this is the whole row. Consequently the only place a slope in this row can
differ from the unit slope is that single `z`, read at the grading in question.

## `z_1` on `V_2`, reduced to the grading-one evaluation

`HJO.Sweep.zCommTwo` is the commutator half `d^*_+{}^{(1)}d_-^{(2)} - d_-^{(3)}d^*_+{}^{(2)}` of
`HJO.Sweep.zop` at `k = 2`, and `HJO.Sweep.zopOneStar_two_eq` reads off
`z_1^{(2)} = q^2/(1-q) · zCommTwo · T_1^{-1}`.

The evaluation is `HJO.Sweep.zCommTwo_monomial`: on a monomial of `V_2`,

`zCommTwo(C(A)·y_1^m y_2^n) = y_2^m · (d^*_+{}^{(0)}(C(B_n A)) - B_n(d^*_+{}^{(0)}(C A)))`.

So `z_1` on `V_2` is **the same failure of `B_n` to commute with the one-letter displacement** that
`z_1` on `V_1` already measures, with the factor `y_2^m` riding through untouched. That is the
reduction this file exists for: the grading-two reading is not new content beyond the grading-one
one, plus a spectator variable.

## The assembly

`HJO.Sweep.slopeOperator_two_odd`: `Ξ^{(K)}_{2,2k+1} = (-y_1)^k · (qu)^{-1} z_1^{(K)} · (-y_1)^k`,
at **every** grading `K` and every `k`, the two structural halves above put together by
`HJO.Sweep.slopeOperator`. `HJO.Sweep.slopeOperator_two_three` is its case `K = k = 1`.

## Genericity

The `(qu)^{-1}` in the assembly and the `q^2/(1-q)` in `zopOneStar_two_eq` are **not** removable
normalisations: in a field `0⁻¹ = 0`, so at `q = 0`, at `u = 0` and at `q = 1` the corresponding
letter is the **zero map** and any clause reading `0 = something nonzero` is *false* rather than
vacuous. The three statements here carry those scalars symbolically and so need no hypothesis; the
evaluation of the assembly does need all three exclusions.
-/

@[expose] public section

namespace HJO.Mellit

/-- **The slope letter on the row `a = 2`**: reading `β_{2,2k+1}` from the top, the `j`-th letter is
`z` exactly when `j = k`, and `y` otherwise. -/
@[hjo "lem_mellit_slope_operator_two_row"]
theorem slopeLetter_two_odd {k j : ℕ} (hj : j < 2 * k + 1) :
    slopeLetter 2 (2 * k + 1) (2 * k + 1 - j)
      = if j = k then SlopeLetter.z else SlopeLetter.y := by
  have hM : 2 + (2 * k + 1) = 2 * k + 3 := by ring
  have hres : slopeResidue 2 (2 * k + 1) (2 * k + 1 - j)
      = if j < k then (2 * k + 1 - j) * 2 - (2 * k + 3) else (2 * k + 1 - j) * 2 := by
    rw [slopeResidue, hM]
    split_ifs with h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [slopeLetter, hres]
  split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega)

/-- **The slope word on the whole row `a = 2` carries exactly one `z`**:
`β_{2,2k+1} = y^k z y^k`, for every `k`. -/
@[hjo "lem_mellit_slope_operator_two_row"]
theorem slopeWord_two_odd (k : ℕ) :
    slopeWord 2 (2 * k + 1)
      = List.replicate k SlopeLetter.y
        ++ SlopeLetter.z :: List.replicate k SlopeLetter.y := by
  have hM : 2 + (2 * k + 1) - 2 = 2 * k + 1 := by omega
  have hmap : ∀ j ∈ List.range (2 * k + 1),
      slopeLetter 2 (2 * k + 1) (2 * k + 1 - j)
        = if j = k then SlopeLetter.z else SlopeLetter.y :=
    fun j hj => slopeLetter_two_odd (List.mem_range.1 hj)
  rw [slopeWord, hM, List.map_congr_left hmap, show 2 * k + 1 = k + (k + 1) from by omega,
    List.range_add, List.map_append, List.map_map, List.range_succ_eq_map, List.map_cons,
    List.map_map]
  simp only [Function.comp_apply, add_zero, ite_true]
  refine congrArg₂ (fun l₁ l₂ => l₁ ++ SlopeLetter.z :: l₂) ?_ ?_
  · refine List.eq_replicate_iff.2 ⟨by simp, fun b hb => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
    have : j ≠ k := (List.mem_range.1 hj).ne
    simp [this]
  · refine List.eq_replicate_iff.2 ⟨by simp, fun b hb => ?_⟩
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hb
    simp

end HJO.Mellit

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- The commutator half of `z_1` on `V_2`. -/
noncomputable def zCommTwo (q u : L) : Module.End L (Total L) :=
  dplusStar q u 1 * dminus q 2 - dminus q 3 * dplusStar q u 2

/-- **`z_1` on `V_2` in terms of its commutator half**, the train being the single inverse letter
`T_1^{-1}`. -/
theorem zopOneStar_two_eq (q u : L) :
    zopOneStar q u 2 = (q ^ 2 / (1 - q)) • (zCommTwo q u * braidInvEnd q 1) := by
  rw [zopOneStar, zCommTwo, trainUpEnd,
    show Braid.trainUp (braidEnd q) (braidInvEnd q) 2 1 = braidInvEnd q 1 from
      Braid.trainUp_succ_self _ _ 1]

theorem dplusStar_two_auxVar_pow_mul_C (q u : L) (m n : ℕ) (A : Sym.Lambda L) :
    dplusStar q u 2 ((auxVar 1 : Total L) ^ m * ((auxVar 2 : Total L) ^ n * MvPolynomial.C A))
      = (auxVar 2 : Total L) ^ m
          * ((auxVar 3 : Total L) ^ n * dplusStar q u 0 (MvPolynomial.C A)) := by
  rw [map_auxVar_pow_mul_of_map_auxVar_mul (Φ := (dplusStar q u 2 : Total L →ₗ[L] Total L))
      (S := (auxVar 2 : Total L)) (dplusStar_auxVar_mul q u le_rfl (by omega)) m,
    map_auxVar_pow_mul_of_map_auxVar_mul (Φ := (dplusStar q u 2 : Total L →ₗ[L] Total L))
      (S := (auxVar 3 : Total L)) (dplusStar_auxVar_mul q u (by omega) le_rfl) n,
    dplusStar_C_level q u 2 0]

theorem dminus_three_auxVar_pow_mul (q : L) (m n : ℕ) {H : Total L} (hH : H ∈ piece L 1) :
    dminus q 3 ((auxVar 2 : Total L) ^ m * ((auxVar 3 : Total L) ^ n * H))
      = (auxVar 2 : Total L) ^ m * bopExt q (n : ℤ) H := by
  have hmem : ((auxVar 2 : Total L) ^ m * H) ∈ piece L 2 :=
    mul_mem (pow_mem (auxVar_mem_piece (by omega) le_rfl) m) (piece_mono (by omega) hH)
  have hZ : ((auxVar 2 : Total L) ^ m) ∈ auxSubalg L :=
    pow_mem (auxVar_mem_auxSubalg 2) m
  rw [show (auxVar 2 : Total L) ^ m * ((auxVar 3 : Total L) ^ n * H)
      = (auxVar 3 : Total L) ^ n * ((auxVar 2 : Total L) ^ m * H) from by ring,
    show (3 : ℕ) = 2 + 1 from rfl, dminus_auxVar_pow_mul q 2 n hmem,
    bopExt_auxSubalg_mul q _ hZ]

/-- **`z_1`'s commutator on a monomial of `V_2`.** The bracket on the right is the failure of `B_n`
to commute with the one-letter displacement — the same quantity `z_1` on `V_1` measures — and the
factor `y_2^m` rides through untouched. -/
theorem zCommTwo_monomial (q u : L) (m n : ℕ) (A : Sym.Lambda L) :
    zCommTwo q u (MvPolynomial.C A * ((auxVar 1 : Total L) ^ m * (auxVar 2 : Total L) ^ n))
      = (auxVar 2 : Total L) ^ m
          * (dplusStar q u 0 (MvPolynomial.C (Sym.Bop q (n : ℤ) A))
            - bopExt q (n : ℤ) (dplusStar q u 0 (MvPolynomial.C A))) := by
  have hrw : (MvPolynomial.C A : Total L) * ((auxVar 1 : Total L) ^ m * (auxVar 2 : Total L) ^ n)
      = (auxVar 1 : Total L) ^ m * ((auxVar 2 : Total L) ^ n * MvPolynomial.C A) := by ring
  have hH : dplusStar q u 0 (MvPolynomial.C A : Total L) ∈ piece L 1 :=
    dplusStar_zero_C_mem_piece_one q u A
  rw [zCommTwo, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  rw [dminus_two_term q n m A,
    show (MvPolynomial.C (Sym.Bop q (n : ℤ) A) : Total L) * (auxVar 1 : Total L) ^ m
      = (auxVar 1 : Total L) ^ m * MvPolynomial.C (Sym.Bop q (n : ℤ) A) from by ring,
    dplusStar_one_auxVar_pow_mul_C, hrw, dplusStar_two_auxVar_pow_mul_C,
    dminus_three_auxVar_pow_mul q m n hH, mul_sub]

/-! ### The assembly: the slope operator of the row at a general grading -/

/-- **`Ξ^{(K)}_{2,2k+1} = (-y_1)^k·(qu)^{-1}z_1^{(K)}·(-y_1)^k`**, at **every** grading `K` and
every `k`.

`HJO.Mellit.slopeWord_two_odd` says the word is `y^kzy^k`, and `HJO.Sweep.slopeOperator` reads
each `y` as multiplication by `-y_1` and the single `z` as `(qu)^{-1}z_1`, the head of the list
being the outermost factor. `HJO.Sweep.slopeOperator_two_three` is the case `K = k = 1`.

Unconditional: `(qu)^{-1}` is carried symbolically, and at `qu = 0` both sides are the zero map
(see the genericity note in the module docstring) rather than the statement being false. -/
@[hjo "lem_mellit_slope_operator_two_row"]
theorem slopeOperator_two_odd (q u : L) (K k : ℕ) :
    slopeOperator q u K 2 (2 * k + 1)
      = (-LinearMap.mulLeft L (auxVar 1 : Total L)) ^ k
          * ((q * u)⁻¹ • zopOneStar q u K)
          * (-LinearMap.mulLeft L (auxVar 1 : Total L)) ^ k := by
  rw [slopeOperator, Mellit.slopeWord_two_odd]
  simp only [List.map_append, List.map_cons, List.map_replicate, List.prod_append,
    List.prod_cons, List.prod_replicate, zop_one]
  rw [mul_assoc]

end HJO.Sweep

end
