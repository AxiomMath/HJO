/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.LhsSingletonAxisResidual
public import HJO.Shuffle.MellitTwoPartTwoThreeValue
public import HJO.Shuffle.MellitTwoPartTwoThreeClause
public import HJO.Shuffle.MellitVertexStepGeneral
public import HJO.Shuffle.MellitLevelRaiseTwoThree

/-! # The one-part stage word at `[2]`, and the clause at `[2]`

`HJO.Mellit.lhsAt_two_three_two_iff_qop` reduces the `hlhs` clause at `(a,b) = (2,3)` and the
composition `[2]` to a `Θ`-free identity in `Λ` whose right-hand side is known in closed form. Its
left-hand side is the Hall--Littlewood sum `∑_m B_m((G_2)_m)` on the one-part stage word. This file
computes that value and discharges the identity.

## The route

`G_2 = Z^{(1)}_{2,3}(G_1)` (`HJO.Mellit.stageWordTotal_singleton_succ`) with
`G_1 = -e_1y_1^2 + uy_1^3`, and `Z^{(1)}_{2,3} = (qu)^{-1}y_1z_1y_1^2z_1`
(`HJO.Sweep.replicatedTotal_two_three_zero_apply`). The whole computation therefore consists of two
applications of `HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C` — `z_1` on one monomial `y_1^mC(A)` of
`V_1` — and one final `ct ∘ d_-^{(1)}`
(`HJO.Sweep.constantCoeff_dminus_one_of_mem_piece`). Nothing of width above `2` is read, as
`HJO.Sweep.replicatedTotal_two_three_zero_eq_width_two` predicts.

Each `z_1` value is a *difference* of two `B_m`-shaped terms: the displacement `d^*_+{}^{(0)}` after
`B_m` minus `B_m` coefficientwise after the displacement. The six monomials the computation meets
are handled by the six lemmas `HJO.Sweep.zopOneStar_one_auxVar_*`, each of which carries the factor
`q` out front — the `q/(1-q)` of `HJO.Sweep.zop` against a `1-q` that the two halves' difference
always produces. That cancellation is why the answer is polynomial in `q` and `u` with no
denominator, and it is where `q ≠ 1` is spent.

## What is proved

* `HJO.Mellit.stageWordTotal_two_three_two_eq` — **the one-part stage word at `[2]`**, written out:
  eleven monomials over the `y_1`-degrees `2` to `6`, every coefficient divisible by `qu`.

* `HJO.Mellit.sum_bop_stageWordTotal_two_three_two` — **`∑_m B_m((G_2)_m)`**, the sweep side of the
  clause at `[2]`: nine `e`-monomials of degree six, coefficients of `(q,u)`-degree up to nine.

* `HJO.Mellit.lhsAt_two_three_two_of_axis` — **the clause at `[2]` HOLDS**, at every slope
  homomorphism. `HJO.Mellit.lhsAt_two_three_two_iff_qop` is an equivalence and the computed sweep
  side discharges its right-hand side against
  `HJO.Sym.qop_two_three_apply_qop_two_three_apply_one` and `HJO.Sym.qop_four_six_apply_one`.

  This is the first instance of the `hlhs` clause past the base case, and the comparison is a
  *check*, not a definition: the two sides are computed by routes that share no lemma — the left by
  `z_1` and `HJO.Sym.Bop` on the total space, the right by the slope operators of `HJO.Sym.Qop` on
  `Λ` — so a sign or a normalisation lost on either side would leave the final identity unprovable.

* `HJO.Mellit.dminus_one_stageWordTotal_two_three_one_eq` — the consistency check at `A = 1`: the
  same plumbing (`ct ∘ d_-^{(1)}` monomial by monomial, `HJO.Sym.Bop` at the index read off the
  `y_1`-degree) reproduces the decided singleton value `-e_1e_2 + (1-q-u)e_3`, which
  `HJO.Mellit.sum_bop_stageWordTotal_two_three_one` obtains through
  `HJO.Sweep.dminus_one_stageTotal_two_three_zero_one_one` instead, i.e. through the sweep word and
  not through `HJO.Sym.Bop` at all.

## Genericity

`q ≠ 1` in every `z_1` value and everything downstream of one: the scalar `q/(1-q)` of
`HJO.Sweep.zop`. `q ≠ 0` and `u ≠ 0` from the `(qu)^{-1}` of `HJO.Sweep.slopeOperator` — in a field
`0⁻¹ = 0`, so there the letter is the zero map and the clause is false rather than vacuous — and
they are also what `HJO.Mellit.stageWordTotal_two_three_singleton` spends on the seed.

`HJO.Mellit.lhsAt_two_three_two_of_axis` adds `M = (1-q)(1-u) ≠ 0` for the `M^{-1}` of `HJO.Sym.Qop`
(hence `u ≠ 1`), `qu ≠ 0` and `qu ≠ 1` for the normalising scalar `v/(v-1)` of `HJO.Sym.axisGen`,
and `qu ≠ -1` for the cancellation of `1 + qu` in `HJO.Mellit.lhsAt_two_three_two_iff_qop`. At
algebraically independent `q, u` all of these hold, and `(2,3)` is coprime with `1 < a < b`.

The `B_k` and `d^*_+` tables below need no hypothesis at all: they are identities of two polynomial
expressions.

## Implementation notes

What is decided is one clause of one binder: `hlhs` at `[2]`, at every slope homomorphism.
`IsSlopeHom` is a hypothesis throughout this file (existence is `HJO.Sym.exists_isSlopeHom`, not
used here), so the statement is the clause at any slope homomorphism, exactly as for the instances
at `[1]`.

The results are values of `HJO.Sym.Bop`, `HJO.Sweep.zop` and `HJO.Mellit.stage` and
reductions of the clause of `HJO.Mellit.lhsRewrite_sweepWitness`, not that statement itself.

## References

This file works with `HJO.Mellit.lhsRewrite_sweepWitness`, `HJO.Mellit.stage`,
`HJO.Mellit.replicatedLetter`, `HJO.Sweep.zop`, `HJO.Sweep.slopeOperator`, `HJO.Sym.Bop`,
`HJO.Sweep.dplusStar`, `HJO.Sweep.dminus`, `HJO.Sym.Qop` and `HJO.Sym.elemSymm`.
-/

@[expose] public section

-- Every computation below closes on a polynomial identity in the `e`-monomials and the scalars
-- `C q`, `C u`, and each is normalised by the *same* rewrite set: which members of it fire depends
-- on the monomial, so some are unused in each individual proof. This is the arrangement of
-- `HJO/Shuffle/MellitTwoPartTwoThreeValue.lean`, and its linter exemption too.
set_option linter.unusedSimpArgs false

-- Every exponent written as a numeral in this file is a natural number. Saying so up front lets
-- each `x ^ n` resolve `HPow _ ℕ _` at once instead of retrying instance resolution for the
-- pending numeral type until defaulting, which dominated elaboration here. The elaborated terms
-- are the ones the default instance would produce.
local macro_rules | `($x ^ $n:num) => `(rightact% HPow.hPow $x ($n : ℕ))

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The vacuum values `B_k(1) = (-1)^ke_k` at the indices the computation reads -/

/-- `B_2(1) = e_2`. -/
theorem bop_two_one (q : L) : Bop q ((2 : ℕ) : ℤ) (1 : Lambda L) = elemSymm L 2 := by
  rw [bop_natCast_one]; norm_num

/-- `B_4(1) = e_4`. -/
theorem bop_four_one (q : L) : Bop q ((4 : ℕ) : ℤ) (1 : Lambda L) = elemSymm L 4 := by
  rw [bop_natCast_one]; norm_num

/-- `B_5(1) = -e_5`. -/
theorem bop_five_one (q : L) : Bop q ((5 : ℕ) : ℤ) (1 : Lambda L) = -elemSymm L 5 := by
  rw [bop_natCast_one]; norm_num

/-- `B_6(1) = e_6`. -/
theorem bop_six_one (q : L) : Bop q ((6 : ℕ) : ℤ) (1 : Lambda L) = elemSymm L 6 := by
  rw [bop_natCast_one]; norm_num

/-! ### The two Pieri rules at the literal indices

`HJO.Sym.bop_elemSymm_one_mul` and `HJO.Sym.bop_elemSymm_two_mul` carry `k + 1` and `k + 2` in the
conclusion, which no numeral matches after the index has been normalised; the instances below write
the numerals out, exactly as `HJO/Shuffle/MellitTwoPartTwoThreeValue.lean` does. -/

/-- `B_2(e_1f)`. -/
theorem bop_two_elemSymm_one_mul (q : L) (f : Lambda L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * f)
      = elemSymm L 1 * Bop q ((2 : ℕ) : ℤ) f + (1 - q) • Bop q ((3 : ℕ) : ℤ) f :=
  bop_elemSymm_one_mul q 2 f

/-- `B_3(e_1f)`. -/
theorem bop_three_elemSymm_one_mul (q : L) (f : Lambda L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 1 * f)
      = elemSymm L 1 * Bop q ((3 : ℕ) : ℤ) f + (1 - q) • Bop q ((4 : ℕ) : ℤ) f :=
  bop_elemSymm_one_mul q 3 f

/-- `B_4(e_1f)`. -/
theorem bop_four_elemSymm_one_mul (q : L) (f : Lambda L) :
    Bop q ((4 : ℕ) : ℤ) (elemSymm L 1 * f)
      = elemSymm L 1 * Bop q ((4 : ℕ) : ℤ) f + (1 - q) • Bop q ((5 : ℕ) : ℤ) f :=
  bop_elemSymm_one_mul q 4 f

/-- `B_5(e_1f)`. -/
theorem bop_five_elemSymm_one_mul (q : L) (f : Lambda L) :
    Bop q ((5 : ℕ) : ℤ) (elemSymm L 1 * f)
      = elemSymm L 1 * Bop q ((5 : ℕ) : ℤ) f + (1 - q) • Bop q ((6 : ℕ) : ℤ) f :=
  bop_elemSymm_one_mul q 5 f

/-- `B_2(e_2f)`. -/
theorem bop_two_elemSymm_two_mul (q : L) (f : Lambda L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 2 * f)
      = elemSymm L 2 * Bop q ((2 : ℕ) : ℤ) f
        + (1 - q) • (elemSymm L 1 * Bop q ((3 : ℕ) : ℤ) f)
        + (-(q * (1 - q))) • Bop q ((4 : ℕ) : ℤ) f :=
  bop_elemSymm_two_mul q 2 f

/-! ### The `B_k` values on one elementary function, past the earlier ones -/

/-- `B_4(e_1) = e_1e_4 - (1-q)e_5`, the Pieri rule at `f = 1`. -/
theorem bop_four_elemSymm_one (q : L) :
    Bop q ((4 : ℕ) : ℤ) (elemSymm L 1)
      = elemSymm L 1 * elemSymm L 4 + (q - 1) • elemSymm L 5 := by
  have h := bop_four_elemSymm_one_mul (L := L) q 1
  rw [mul_one, bop_four_one, bop_five_one] at h
  rw [h]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_one]
  ring

/-- `B_5(e_1) = -e_1e_5 + (1-q)e_6`. -/
theorem bop_five_elemSymm_one (q : L) :
    Bop q ((5 : ℕ) : ℤ) (elemSymm L 1)
      = -(elemSymm L 1 * elemSymm L 5) + (1 - q) • elemSymm L 6 := by
  have h := bop_five_elemSymm_one_mul (L := L) q 1
  rw [mul_one, bop_five_one, bop_six_one] at h
  rw [h]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_one]
  ring

/-! ### The `B_k` values on the `e`-monomials the two `z_1` steps and the projection read -/

/-- `B_3(e_1^2)`. -/
theorem bop_three_elemSymm_one_sq (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1)
      = (-1 : L) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
        + (-2 * q + 2) • (elemSymm L 1 * elemSymm L 4)
        + (-q ^ 2 + 2 * q - 1) • elemSymm L 5 := by
  rw [bop_three_elemSymm_one_mul, bop_three_elemSymm_one, bop_four_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- `B_4(e_1^2)`. -/
theorem bop_four_elemSymm_one_sq (q : L) :
    Bop q ((4 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1)
      = (1 : L) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (2 * q - 2) • (elemSymm L 1 * elemSymm L 5)
        + (q ^ 2 - 2 * q + 1) • elemSymm L 6 := by
  rw [bop_four_elemSymm_one_mul, bop_four_elemSymm_one, bop_five_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- `B_3(e_1^3)`. -/
theorem bop_three_elemSymm_one_cube (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))
      = (-1 : L) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (-3 * q + 3) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (-3 * q ^ 2 + 6 * q - 3) • (elemSymm L 1 * elemSymm L 5)
        + (-q ^ 3 + 3 * q ^ 2 - 3 * q + 1) • elemSymm L 6 := by
  rw [bop_three_elemSymm_one_mul, bop_three_elemSymm_one_sq, bop_four_elemSymm_one_sq]
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- `B_3(e_1e_2)`. -/
theorem bop_three_elemSymm_one_mul_two (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 2)
      = (-1 : L) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))
        + (-q + 1) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (-2 * q ^ 2 + 3 * q - 1) • (elemSymm L 1 * elemSymm L 5)
        + (-q + 1) • (elemSymm L 2 * elemSymm L 4)
        + (-q ^ 3 + 2 * q ^ 2 - q) • elemSymm L 6 := by
  rw [bop_three_elemSymm_one_mul, bop_three_elemSymm_two, bop_four_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- `B_2(e_1e_3)`. -/
theorem bop_two_elemSymm_one_mul_three (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 3)
      = (q : L) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))
        + (q ^ 2 - q) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (2 * q ^ 3 - 3 * q ^ 2 + q) • (elemSymm L 1 * elemSymm L 5)
        + (q ^ 2 - 2 * q + 1) • (elemSymm L 2 * elemSymm L 4)
        + (q - 1) • (elemSymm L 3 * elemSymm L 3)
        + (q ^ 4 - 2 * q ^ 3 + q ^ 2) • elemSymm L 6 := by
  rw [bop_two_elemSymm_one_mul, bop_two_elemSymm_three, bop_three_elemSymm_three]
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- `B_2(e_2^2)`. -/
theorem bop_two_elemSymm_two_sq (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 2 * elemSymm L 2)
      = (1 : L) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))
        + (2 * q - 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))
        + (q ^ 2 - 2 * q + 1) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (2 * q ^ 3 - 4 * q ^ 2 + 2 * q) • (elemSymm L 1 * elemSymm L 5)
        + (2 * q ^ 2 - 2 * q) • (elemSymm L 2 * elemSymm L 4)
        + (q ^ 4 - 2 * q ^ 3 + q ^ 2) • elemSymm L 6 := by
  rw [bop_two_elemSymm_two_mul, bop_two_elemSymm_two', bop_three_elemSymm_two,
    bop_four_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- `B_2(e_1e_2)`, the inner step of `HJO.Sym.bop_two_elemSymm_one_sq_mul_two`. -/
theorem bop_two_elemSymm_one_mul_two (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 2)
      = (1 : L) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))
        + (q - 1) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
        + (2 * q ^ 2 - 3 * q + 1) • (elemSymm L 1 * elemSymm L 4)
        + (q - 1) • (elemSymm L 2 * elemSymm L 3)
        + (q ^ 3 - 2 * q ^ 2 + q) • elemSymm L 5 := by
  rw [bop_two_elemSymm_one_mul, bop_two_elemSymm_two', bop_three_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- `B_2(e_1^2e_2)`. -/
theorem bop_two_elemSymm_one_sq_mul_two (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))
      = (1 : L) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (q - 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (3 * q ^ 2 - 5 * q + 2) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (2 * q - 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))
        + (3 * q ^ 3 - 7 * q ^ 2 + 5 * q - 1) • (elemSymm L 1 * elemSymm L 5)
        + (q ^ 2 - 2 * q + 1) • (elemSymm L 2 * elemSymm L 4)
        + (q ^ 4 - 3 * q ^ 3 + 3 * q ^ 2 - q) • elemSymm L 6 := by
  rw [bop_two_elemSymm_one_mul, bop_two_elemSymm_one_mul_two, bop_three_elemSymm_one_mul_two]
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

end HJO.Sym

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### Two conveniences -/

omit [Algebra ℚ L] in
/-- A `Λ`-scalar multiple under `MvPolynomial.C` is the module action on the total space. -/
theorem C_smul_total (x : L) (f : Lambda L) :
    (MvPolynomial.C (x • f) : Total L) = x • MvPolynomial.C f := by
  rw [← scal_mul_C, smul_eq_scal_mul]

/-- `HJO.Sweep.bopExt_auxVar_pow_mul_C` at the first power. -/
theorem bopExt_auxVar_mul_C (q : L) (r : ℤ) (A : Lambda L) :
    bopExt q r ((auxVar 1 : Total L) * MvPolynomial.C A)
      = (auxVar 1 : Total L) * MvPolynomial.C (Bop q r A) := by
  simpa using bopExt_auxVar_pow_mul_C q r 1 A

/-! ### `d^*_+` on the two elementary functions past the earlier table -/

/-- `d^*_+(e_4) = e_4 + (q-1)uy_1e_3 - (q-1)(uy_1)^2e_2 + (q-1)(uy_1)^3e_1 - (q-1)(uy_1)^4`. -/
theorem dplusStar_C_elemSymm_four (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 4))
      = MvPolynomial.C (elemSymm L 4)
        + scal (q - 1) * starLetter u * MvPolynomial.C (elemSymm L 3)
        - scal (q - 1) * starLetter u ^ 2 * MvPolynomial.C (elemSymm L 2)
        + scal (q - 1) * starLetter u ^ 3 * MvPolynomial.C (elemSymm L 1)
        - scal (q - 1) * starLetter u ^ 4 := by
  rw [dplusStar_C_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  norm_num [elemSymm_zero L]
  ring

/-- `d^*_+(e_5)`, one letter further. -/
theorem dplusStar_C_elemSymm_five (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 5))
      = MvPolynomial.C (elemSymm L 5)
        + scal (q - 1) * starLetter u * MvPolynomial.C (elemSymm L 4)
        - scal (q - 1) * starLetter u ^ 2 * MvPolynomial.C (elemSymm L 3)
        + scal (q - 1) * starLetter u ^ 3 * MvPolynomial.C (elemSymm L 2)
        - scal (q - 1) * starLetter u ^ 4 * MvPolynomial.C (elemSymm L 1)
        + scal (q - 1) * starLetter u ^ 5 := by
  rw [dplusStar_C_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [elemSymm_zero L]
  ring

/-! ### The displacement in the graded form `∑_j y_1^j·Cf` that `bopExt` reads

`HJO.Sweep.bopExt` is `HJO.Sym.Bop` applied to each `y_1`-coefficient, so to compute it on a
`d^*_+` image that image has to be written as a sum of terms `y_1^j·Cf`. These four are the
arguments the two `z_1` steps meet. -/

/-- `d^*_+` fixes the vacuum. -/
theorem dplusStar_C_one (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (1 : Lambda L) : Total L) = MvPolynomial.C (1 : Lambda L) := by
  rw [map_one, ← dplusStarAlg_eq_dplusStar, map_one]

/-- `d^*_+(e_1)`, graded. -/
theorem dplusStar_C_elemSymm_one_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 1) : Total L)
      = MvPolynomial.C (elemSymm L 1)
        + ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (1 : Lambda L)) := by
  rw [dplusStar_C_elemSymm_one]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- `d^*_+(e_2)`, graded. -/
theorem dplusStar_C_elemSymm_two_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 2) : Total L)
      = MvPolynomial.C (elemSymm L 2)
        + ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1))
        + ((1 - q) * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (1 : Lambda L)) := by
  rw [dplusStar_C_elemSymm_two]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- `d^*_+(e_1^2)`, graded: the square of `HJO.Sweep.dplusStar_C_elemSymm_one_expand`. -/
theorem dplusStar_C_elemSymm_one_sq_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 1 * elemSymm L 1) : Total L)
      = MvPolynomial.C (elemSymm L 1 * elemSymm L 1)
        + (2 * ((q - 1) * u)) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1))
        + ((q - 1) ^ 2 * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (1 : Lambda L)) := by
  rw [dplusStar_C_mul, dplusStar_C_elemSymm_one]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- `bopExt` on a scalar multiple of `y_1^m·Cf`, the shape the graded displacement is in. -/
theorem bopExt_smul_auxVar_pow_mul_C (q : L) (r : ℤ) (x : L) (m : ℕ) (A : Lambda L) :
    bopExt q r (x • ((auxVar 1 : Total L) ^ m * MvPolynomial.C A))
      = x • ((auxVar 1 : Total L) ^ m * MvPolynomial.C (Bop q r A)) := by
  rw [map_smul, bopExt_auxVar_pow_mul_C]

/-! ### `z_1` on the six monomials of `V_1` the two steps meet

`HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C` evaluates `z_1(y_1^mC(A))` as
`q/(1-q)·(d^*_+(C(B_mA)) - B_m(d^*_+(C A)))`, the second `B_m` coefficientwise in `y_1`. In every
one of the six cases below the bracket is divisible by `1 - q`, so the value is `q` times a
polynomial: the failure of `HJO.Sym.Bop` to commute with the displacement `(q-1)uy_1` vanishes to
first order at `q = 1`. That is the whole reason the answer at `[2]` has no denominator, and `q ≠ 1`
is spent exactly here. -/

/-- `z_1(y_1^2C(e_1))`. -/
theorem zopOneStar_one_auxVar_sq_mul_C_elemSymm_one (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1))
      = q • ((-(q * u) + u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 2))
          + (-u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
          + u ^ 2 • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1))) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have hbr : dplusStar q u 0 (MvPolynomial.C (Bop q ((2 : ℕ) : ℤ) (elemSymm L 1)))
        - bopExt q ((2 : ℕ) : ℤ) (dplusStar q u 0 (MvPolynomial.C (elemSymm L 1) : Total L))
      = (1 - q) • ((-(q * u) + u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 2))
          + (-u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
          + u ^ 2 • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1))) := by
    rw [dplusStar_C_elemSymm_one_expand, map_add, bopExt_C, bopExt_smul_auxVar_pow_mul_C,
      bop_two_elemSymm_one', bop_two_one]
    simp only [map_add, map_sub, map_neg, C_smul_total, map_smul, dplusStar_C_mul,
      dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
      dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five]
    simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
      MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
      map_ofNat]
    ring
  rw [zopOneStar_one_auxVar_pow_mul_C, hbr, smul_smul,
    show q / (1 - q) * (1 - q) = q from by field_simp]

/-- `z_1(y_1^3C(1))`: the second monomial of the seed. -/
theorem zopOneStar_one_auxVar_cube_mul_C_one (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Lambda L))
      = q • (u • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 2))
      + (-u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1))
      + u ^ 3 • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Lambda L))) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have hbr : dplusStar q u 0 (MvPolynomial.C (Bop q ((3 : ℕ) : ℤ) (1 : Lambda L)))
        - bopExt q ((3 : ℕ) : ℤ) (dplusStar q u 0 (MvPolynomial.C (1 : Lambda L) : Total L))
      = (1 - q) • (u • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 2))
        + (-u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1))
        + u ^ 3 • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Lambda L))) := by
    simp only [dplusStar_C_one, map_add, bopExt_C, bopExt_smul_auxVar_pow_mul_C, bop_three_one]
    simp only [map_add, map_sub, map_neg, C_smul_total, map_smul, dplusStar_C_mul,
      dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
      dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five]
    simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
      MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
      map_ofNat]
    ring
  rw [zopOneStar_one_auxVar_pow_mul_C, hbr, smul_smul,
    show q / (1 - q) * (1 - q) = q from by field_simp]

/-- `z_1(y_1^3C(e_1^2))`: the first monomial of `y_1^2z_1(G_1)`. -/
theorem zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_sq (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
      = q • ((q ^ 2 * u - 2 * q * u + u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 4))
      + (2 * q * u - 2 * u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
      + u • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
      + (q ^ 2 * u ^ 2 - 2 * q * u ^ 2 + u ^ 2)
          • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3))
      + (-u ^ 2)
          • ((auxVar 1 : Total L) ^ 2
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
      + u ^ 3 • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have hbr : dplusStar q u 0 (MvPolynomial.C (Bop q ((3 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1)))
        - bopExt q ((3 : ℕ) : ℤ)
            (dplusStar q u 0 (MvPolynomial.C (elemSymm L 1 * elemSymm L 1) : Total L))
      = (1 - q)
          • ((q ^ 2 * u - 2 * q * u + u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 4))
        + (2 * q * u - 2 * u)
            • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + u • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (q ^ 2 * u ^ 2 - 2 * q * u ^ 2 + u ^ 2)
            • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3))
        + (-u ^ 2)
            • ((auxVar 1 : Total L) ^ 2
                * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
        + u ^ 3 • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))) := by
    simp only [dplusStar_C_elemSymm_one_sq_expand, map_add, bopExt_C,
      bopExt_smul_auxVar_pow_mul_C, bop_three_elemSymm_one_sq, bop_three_elemSymm_one,
      bop_three_one]
    simp only [map_add, map_sub, map_neg, C_smul_total, map_smul, dplusStar_C_mul,
      dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
      dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five]
    simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
      MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
      map_ofNat]
    ring
  rw [zopOneStar_one_auxVar_pow_mul_C, hbr, smul_smul,
    show q / (1 - q) * (1 - q) = q from by field_simp]

/-- `z_1(y_1^3C(e_2))`: the second monomial of `y_1^2z_1(G_1)`. -/
theorem zopOneStar_one_auxVar_cube_mul_C_elemSymm_two (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))
      = q • ((q ^ 2 * u - q * u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 4))
      + u • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
      + (q * u - u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
      + (-(q * u ^ 2) + u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3))
      + (-u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
      + u ^ 3 • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have hbr : dplusStar q u 0 (MvPolynomial.C (Bop q ((3 : ℕ) : ℤ) (elemSymm L 2)))
        - bopExt q ((3 : ℕ) : ℤ) (dplusStar q u 0 (MvPolynomial.C (elemSymm L 2) : Total L))
      = (1 - q) • ((q ^ 2 * u - q * u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 4))
        + u • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
        + (q * u - u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (-(q * u ^ 2) + u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3))
        + (-u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + u ^ 3 • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))) := by
    simp only [dplusStar_C_elemSymm_two_expand, map_add, bopExt_C,
      bopExt_smul_auxVar_pow_mul_C, bop_three_elemSymm_two, bop_three_elemSymm_one,
      bop_three_one]
    simp only [map_add, map_sub, map_neg, C_smul_total, map_smul, dplusStar_C_mul,
      dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
      dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five]
    simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
      MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
      map_ofNat]
    ring
  rw [zopOneStar_one_auxVar_pow_mul_C, hbr, smul_smul,
    show q / (1 - q) * (1 - q) = q from by field_simp]

/-- `z_1(y_1^4C(e_1))`: the third monomial of `y_1^2z_1(G_1)`. -/
theorem zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_one (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))
      = q • ((-(q * u) + u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 4))
      + (-u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
      + u ^ 2 • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
      + (-u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
      + u ^ 4 • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have hbr : dplusStar q u 0 (MvPolynomial.C (Bop q ((4 : ℕ) : ℤ) (elemSymm L 1)))
        - bopExt q ((4 : ℕ) : ℤ) (dplusStar q u 0 (MvPolynomial.C (elemSymm L 1) : Total L))
      = (1 - q) • ((-(q * u) + u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 4))
        + (-u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + u ^ 2 • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (-u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + u ^ 4 • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))) := by
    simp only [dplusStar_C_elemSymm_one_expand, map_add, bopExt_C,
      bopExt_smul_auxVar_pow_mul_C, bop_four_elemSymm_one, bop_four_one]
    simp only [map_add, map_sub, map_neg, C_smul_total, map_smul, dplusStar_C_mul,
      dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
      dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five]
    simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
      MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
      map_ofNat]
    ring
  rw [zopOneStar_one_auxVar_pow_mul_C, hbr, smul_smul,
    show q / (1 - q) * (1 - q) = q from by field_simp]

/-- `z_1(y_1^5C(1))`: the top monomial of `y_1^2z_1(G_1)`. -/
theorem zopOneStar_one_auxVar_pow_five_mul_C_one (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (1 : Lambda L))
      = q • (u • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 4))
      + (-u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3))
      + u ^ 3 • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))
      + (-u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))
      + u ^ 5 • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (1 : Lambda L))) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have hbr : dplusStar q u 0 (MvPolynomial.C (Bop q ((5 : ℕ) : ℤ) (1 : Lambda L)))
        - bopExt q ((5 : ℕ) : ℤ) (dplusStar q u 0 (MvPolynomial.C (1 : Lambda L) : Total L))
      = (1 - q) • (u • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 4))
        + (-u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3))
        + u ^ 3 • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))
        + (-u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))
        + u ^ 5 • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (1 : Lambda L))) := by
    simp only [dplusStar_C_one, map_add, bopExt_C, bopExt_smul_auxVar_pow_mul_C, bop_five_one]
    simp only [map_add, map_sub, map_neg, C_smul_total, map_smul, dplusStar_C_mul,
      dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
      dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five]
    simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
      MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
      map_ofNat]
    ring
  rw [zopOneStar_one_auxVar_pow_mul_C, hbr, smul_smul,
    show q / (1 - q) * (1 - q) = q from by field_simp]

end HJO.Sweep


namespace HJO.Mellit

open HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The seed, in the monomial form the `z_1` values read -/

/-- **The one-part stage word at `[1]`**, `-e_1y_1^2 + uy_1^3`
(`HJO.Sweep.stageTotal_two_three_zero_one_one`), written as a combination of the monomials
`y_1^m·Cf` that `HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C` and
`HJO.Sweep.dminus_one_auxVar_pow_mul_C` read. -/
theorem stageWordTotal_two_three_one_expand (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    (stageWordTotal q u 2 3 [1] : Total L)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1))
        + u • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Lambda L)) := by
  rw [stageWordTotal_singleton, stageTotal_two_three_zero_one_one hq0 hu0 hq1]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-! ### The `A = 1` consistency check on the projection

The plumbing this file uses for the final step — `ct ∘ d_-^{(1)}` applied monomial by monomial,
`HJO.Sym.Bop` at the index read off the `y_1`-degree — reproduces the decided singleton value at
`A = 1`. `HJO.Mellit.sum_bop_stageWordTotal_two_three_one` obtains the same value through
`HJO.Sweep.dminus_one_stageTotal_two_three_zero_one_one`, i.e. through the sweep word and without
`HJO.Sym.Bop` anywhere, so a lost sign or a misread index here would separate the two. -/

/-- **`ct(d_-^{(1)}G_1) = -e_1e_2 + (1-q-u)e_3`**, by the monomial route. -/
theorem dminus_one_stageWordTotal_two_three_one_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    MvPolynomial.constantCoeff (dminus q 1 (stageWordTotal q u 2 3 [1] : Total L))
      = -(elemSymm L 1 * elemSymm L 2) + (1 - q - u) • elemSymm L 3 := by
  have hdm : dminus q 1 (stageWordTotal q u 2 3 [1] : Total L)
      = MvPolynomial.C (-(elemSymm L 1 * elemSymm L 2) + (1 - q - u) • elemSymm L 3) := by
    rw [stageWordTotal_two_three_one_expand hq0 hu0 hq1]
    simp only [map_add, map_smul, dminus_one_auxVar_pow_mul_C, bop_two_elemSymm_one',
      bop_three_one]
    simp only [smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
      MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
      map_ofNat]
    ring
  rw [hdm, MvPolynomial.constantCoeff_C]

/-! ### The two `z_1` steps -/

/-- **`z_1(G_1)`**: the two monomial values `HJO.Sweep.zopOneStar_one_auxVar_sq_mul_C_elemSymm_one`
and `HJO.Sweep.zopOneStar_one_auxVar_cube_mul_C_one`, assembled. Every coefficient carries `qu`. -/
theorem zopOneStar_one_stageWordTotal_two_three_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    zopOneStar q u 1 (stageWordTotal q u 2 3 [1] : Total L)
      =
      (q * u ^ 2 + q ^ 2 * u - q * u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 2))
        + (q * u) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (-(q * u ^ 3) - q * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1))
        + (q * u ^ 4) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Lambda L)) := by
  rw [stageWordTotal_two_three_one_expand hq0 hu0 hq1]
  simp only [map_add, map_smul, zopOneStar_one_auxVar_sq_mul_C_elemSymm_one hq1,
    zopOneStar_one_auxVar_cube_mul_C_one hq1]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- **`y_1^2z_1(G_1)`**, the argument of the outer `z_1`: the same four monomials two
`y_1`-degrees up, which is where `HJO.Sweep.auxVar_sq_mul_zopOneStar_one_mem_piece` keeps them
inside `V_1`. -/
theorem auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_one (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 (stageWordTotal q u 2 3 [1]) : Total L)
      =
      (q * u ^ 2 + q ^ 2 * u - q * u) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))
        + (q * u) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (-(q * u ^ 3) - q * u ^ 2) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))
        + (q * u ^ 4) • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (1 : Lambda L)) := by
  rw [zopOneStar_one_stageWordTotal_two_three_one hq0 hu0 hq1]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- **The outer `z_1`**: eleven monomials over the `y_1`-degrees `1` to `5`, the common factor
`q^2u` being the two `q`'s of the two `z_1` letters and the `u` of the seed. -/
theorem zopOneStar_one_auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_one (hq0 : q ≠ 0)
    (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 (stageWordTotal q u 2 3 [1]))
      = (q ^ 2 * u) • (
      (u ^ 4 + q * u ^ 3 + q ^ 2 * u ^ 2 + q ^ 3 * u - u ^ 3 - q ^ 2 * u - u ^ 2 - q * u + u)
          • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 4))
        + (u ^ 2 + q * u - u)
            • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
        + (u ^ 3 + q * u ^ 2 + q ^ 2 * u - u)
            • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + u • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (-u ^ 5 - q * u ^ 3 + u ^ 3) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3))
        + (-u ^ 4 - 2 * u ^ 3 - q * u ^ 2 + u ^ 2)
            • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (-u ^ 2)
            • ((auxVar 1 : Total L) ^ 2
                * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
        + (u ^ 6 + u ^ 4 + q * u ^ 3 - u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))
        + (u ^ 5 + u ^ 4 + u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (-u ^ 7 - u ^ 6 - u ^ 5) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))
        + u ^ 8 • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (1 : Lambda L))) := by
  rw [auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_one hq0 hu0 hq1]
  simp only [map_add, map_smul, zopOneStar_one_auxVar_cube_mul_C_elemSymm_two hq1,
    zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_sq hq1,
    zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_one hq1,
    zopOneStar_one_auxVar_pow_five_mul_C_one hq1]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-! ### The one-part stage word at `[2]` -/

/-- **`G_2 = Z^{(1)}_{2,3}(G_1)`, written out.** Eleven monomials over the `y_1`-degrees `2` to
`6`; every coefficient is divisible by `qu`, which is what the `(qu)^{-1}` of
`HJO.Sweep.slopeOperator` cancels against.

`HJO.Mellit.stageWordTotal_singleton_succ` is the recursion,
`HJO.Sweep.replicatedTotal_two_three_zero_apply` the letter as `(qu)^{-1}y_1z_1y_1^2z_1`, and the
two `z_1` values above are its two steps. -/
theorem stageWordTotal_two_three_two_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    (stageWordTotal q u 2 3 [2] : Total L)
      =
      (q * u ^ 4 + q ^ 2 * u ^ 3 + q ^ 3 * u ^ 2 + q ^ 4 * u - q * u ^ 3 - q ^ 3 * u - q * u ^ 2
          - q ^ 2 * u + q * u) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 4))
        + (q * u ^ 2 + q ^ 2 * u - q * u)
            • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
        + (q * u ^ 3 + q ^ 2 * u ^ 2 + q ^ 3 * u - q * u)
            • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (q * u)
            • ((auxVar 1 : Total L) ^ 2
                * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (-(q * u ^ 5) - q ^ 2 * u ^ 3 + q * u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 3))
        + (-(q * u ^ 4) - 2 * q * u ^ 3 - q ^ 2 * u ^ 2 + q * u ^ 2)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (-(q * u ^ 2))
            • ((auxVar 1 : Total L) ^ 3
                * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
        + (q * u ^ 6 + q * u ^ 4 + q ^ 2 * u ^ 3 - q * u ^ 3)
            • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2))
        + (q * u ^ 5 + q * u ^ 4 + q * u ^ 3)
            • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (-(q * u ^ 7) - q * u ^ 6 - q * u ^ 5)
            • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1))
        + (q * u ^ 8) • ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C (1 : Lambda L)) := by
  have hrec := stageWordTotal_singleton_succ (L := L) q u 2 3 0
  norm_num at hrec
  rw [hrec, replicatedTotal_two_three_zero_apply,
    zopOneStar_one_auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_one hq0 hu0 hq1,
    mul_smul_comm, smul_smul, show (q * u)⁻¹ * (q ^ 2 * u) = q from by field_simp]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-! ### The sweep side of the clause at `[2]` -/

/-- **`d_-^{(1)}G_2` is the constant `∑_m B_m((G_2)_m)`**: `HJO.Sym.Bop` at the index `m` on the
`m`-th `y_1`-coefficient (`HJO.Sweep.dminus_one_auxVar_pow_mul_C`), for each of the eleven monomials
of `HJO.Mellit.stageWordTotal_two_three_two_eq`, the eleven values read off the `B_k` table. Nine
`e`-monomials of degree six survive. -/
theorem dminus_one_stageWordTotal_two_three_two (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    dminus q 1 (stageWordTotal q u 2 3 [2] : Total L)
      = MvPolynomial.C (
      (q * u ^ 8 + q ^ 2 * u ^ 7 + q ^ 3 * u ^ 6 + q ^ 4 * u ^ 5 + q ^ 5 * u ^ 4 + q ^ 6 * u ^ 3
          + q ^ 7 * u ^ 2 + q ^ 8 * u - q * u ^ 7 - q ^ 7 * u - q * u ^ 6 - q ^ 2 * u ^ 5
          - q ^ 5 * u ^ 2 - q ^ 6 * u - 2 * q ^ 2 * u ^ 4 - 3 * q ^ 3 * u ^ 3 - 2 * q ^ 4 * u ^ 2
          + q * u ^ 4 + q ^ 2 * u ^ 3 + q ^ 3 * u ^ 2 + q ^ 4 * u + q * u ^ 3 + 2 * q ^ 2 * u ^ 2
          + q ^ 3 * u - q * u ^ 2 - q ^ 2 * u) • elemSymm L 6
        + (q * u ^ 5 + q ^ 2 * u ^ 4 + q ^ 3 * u ^ 3 + q ^ 4 * u ^ 2 + q ^ 5 * u - q * u ^ 4
            - q ^ 4 * u - q * u ^ 3 - 2 * q ^ 2 * u ^ 2 - q ^ 3 * u + q * u ^ 2 + q ^ 2 * u)
            • (elemSymm L 3 * elemSymm L 3)
        + (q * u ^ 6 + q ^ 2 * u ^ 5 + q ^ 3 * u ^ 4 + q ^ 4 * u ^ 3 + q ^ 5 * u ^ 2 + q ^ 6 * u
            - q * u ^ 5 - q ^ 5 * u + q * u ^ 4 + q ^ 2 * u ^ 3 + q ^ 3 * u ^ 2 + q ^ 4 * u
            - 2 * q * u ^ 3 - 2 * q ^ 2 * u ^ 2 - 2 * q ^ 3 * u + q * u)
            • (elemSymm L 2 * elemSymm L 4)
        + (q * u ^ 7 + q ^ 2 * u ^ 6 + q ^ 3 * u ^ 5 + q ^ 4 * u ^ 4 + q ^ 5 * u ^ 3
            + q ^ 6 * u ^ 2 + q ^ 7 * u + q ^ 2 * u ^ 5 + q ^ 3 * u ^ 4 + q ^ 4 * u ^ 3
            + q ^ 5 * u ^ 2 - q * u ^ 5 + q ^ 3 * u ^ 3 - q ^ 5 * u - 2 * q * u ^ 4
            - 4 * q ^ 2 * u ^ 3 - 4 * q ^ 3 * u ^ 2 - 2 * q ^ 4 * u + q * u ^ 3 + q ^ 3 * u
            + 2 * q * u ^ 2 + 2 * q ^ 2 * u - q * u) • (elemSymm L 1 * elemSymm L 5)
        + (q * u ^ 2 + q ^ 2 * u - q * u) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))
        + (q * u ^ 4 + q ^ 2 * u ^ 3 + q ^ 3 * u ^ 2 + q ^ 4 * u + 2 * q * u ^ 3
            + 3 * q ^ 2 * u ^ 2 + 2 * q ^ 3 * u - 3 * q * u ^ 2 - 3 * q ^ 2 * u)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))
        + (q * u ^ 5 + q ^ 2 * u ^ 4 + q ^ 3 * u ^ 3 + q ^ 4 * u ^ 2 + q ^ 5 * u + q ^ 2 * u ^ 3
            + q ^ 3 * u ^ 2 - q * u ^ 3 - q ^ 2 * u ^ 2 - q ^ 3 * u - q * u ^ 2 - q ^ 2 * u
            + q * u) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (q * u) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (q * u ^ 2 + q ^ 2 * u - q * u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))) := by
  rw [stageWordTotal_two_three_two_eq hq0 hu0 hq1]
  simp only [map_add, map_smul, dminus_one_auxVar_pow_mul_C, bop_two_elemSymm_four,
    bop_two_elemSymm_two_sq, bop_two_elemSymm_one_mul_three, bop_two_elemSymm_one_sq_mul_two,
    bop_three_elemSymm_three, bop_three_elemSymm_one_mul_two, bop_three_elemSymm_one_cube,
    bop_four_elemSymm_two, bop_four_elemSymm_one_sq, bop_five_elemSymm_one, bop_six_one]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- **`∑_m B_m((G_2)_m)`, the sweep side of the `hlhs` clause at `[2]`.**

`HJO.Sweep.constantCoeff_dminus_one_of_mem_piece` turns the support sum into `ct ∘ d_-^{(1)}` on
`V_1` — the membership is `HJO.Mellit.stageWordTotal_singleton_mem_piece` — and
`HJO.Mellit.dminus_one_stageWordTotal_two_three_two` evaluates it. This is the value
`HJO.Mellit.lhsAt_two_three_two_iff_qop` needs. -/
theorem sum_bop_stageWordTotal_two_three_two (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    ∑ d ∈ (stageWordTotal q u 2 3 [2] : Total L).support,
        Bop q ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d (stageWordTotal q u 2 3 [2] : Total L))
      =
      (q * u ^ 8 + q ^ 2 * u ^ 7 + q ^ 3 * u ^ 6 + q ^ 4 * u ^ 5 + q ^ 5 * u ^ 4 + q ^ 6 * u ^ 3
          + q ^ 7 * u ^ 2 + q ^ 8 * u - q * u ^ 7 - q ^ 7 * u - q * u ^ 6 - q ^ 2 * u ^ 5
          - q ^ 5 * u ^ 2 - q ^ 6 * u - 2 * q ^ 2 * u ^ 4 - 3 * q ^ 3 * u ^ 3 - 2 * q ^ 4 * u ^ 2
          + q * u ^ 4 + q ^ 2 * u ^ 3 + q ^ 3 * u ^ 2 + q ^ 4 * u + q * u ^ 3 + 2 * q ^ 2 * u ^ 2
          + q ^ 3 * u - q * u ^ 2 - q ^ 2 * u) • elemSymm L 6
        + (q * u ^ 5 + q ^ 2 * u ^ 4 + q ^ 3 * u ^ 3 + q ^ 4 * u ^ 2 + q ^ 5 * u - q * u ^ 4
            - q ^ 4 * u - q * u ^ 3 - 2 * q ^ 2 * u ^ 2 - q ^ 3 * u + q * u ^ 2 + q ^ 2 * u)
            • (elemSymm L 3 * elemSymm L 3)
        + (q * u ^ 6 + q ^ 2 * u ^ 5 + q ^ 3 * u ^ 4 + q ^ 4 * u ^ 3 + q ^ 5 * u ^ 2 + q ^ 6 * u
            - q * u ^ 5 - q ^ 5 * u + q * u ^ 4 + q ^ 2 * u ^ 3 + q ^ 3 * u ^ 2 + q ^ 4 * u
            - 2 * q * u ^ 3 - 2 * q ^ 2 * u ^ 2 - 2 * q ^ 3 * u + q * u)
            • (elemSymm L 2 * elemSymm L 4)
        + (q * u ^ 7 + q ^ 2 * u ^ 6 + q ^ 3 * u ^ 5 + q ^ 4 * u ^ 4 + q ^ 5 * u ^ 3
            + q ^ 6 * u ^ 2 + q ^ 7 * u + q ^ 2 * u ^ 5 + q ^ 3 * u ^ 4 + q ^ 4 * u ^ 3
            + q ^ 5 * u ^ 2 - q * u ^ 5 + q ^ 3 * u ^ 3 - q ^ 5 * u - 2 * q * u ^ 4
            - 4 * q ^ 2 * u ^ 3 - 4 * q ^ 3 * u ^ 2 - 2 * q ^ 4 * u + q * u ^ 3 + q ^ 3 * u
            + 2 * q * u ^ 2 + 2 * q ^ 2 * u - q * u) • (elemSymm L 1 * elemSymm L 5)
        + (q * u ^ 2 + q ^ 2 * u - q * u) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))
        + (q * u ^ 4 + q ^ 2 * u ^ 3 + q ^ 3 * u ^ 2 + q ^ 4 * u + 2 * q * u ^ 3
            + 3 * q ^ 2 * u ^ 2 + 2 * q ^ 3 * u - 3 * q * u ^ 2 - 3 * q ^ 2 * u)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))
        + (q * u ^ 5 + q ^ 2 * u ^ 4 + q ^ 3 * u ^ 3 + q ^ 4 * u ^ 2 + q ^ 5 * u + q ^ 2 * u ^ 3
            + q ^ 3 * u ^ 2 - q * u ^ 3 - q ^ 2 * u ^ 2 - q ^ 3 * u - q * u ^ 2 - q ^ 2 * u
            + q * u) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (q * u) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (q * u ^ 2 + q ^ 2 * u - q * u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))) := by
  rw [← constantCoeff_dminus_one_of_mem_piece q (stageWordTotal_singleton_mem_piece q u 2 3 2),
    dminus_one_stageWordTotal_two_three_two hq0 hu0 hq1, MvPolynomial.constantCoeff_C]

/-! ### The clause at `[2]` -/

/-- **The `hlhs` clause at `(a,b) = (2,3)` and the composition `[2]` HOLDS**, at every slope
homomorphism.

`HJO.Mellit.lhsAt_two_three_two_iff_qop` makes the clause equivalent to the `Θ`-free identity

  `-(1 + qu)∑_m B_m((G_2)_m) = qu(Q_{2,3}(Q_{2,3}1) - Q_{4,6}(1))`,

and both sides are now known outright: the left by
`HJO.Mellit.sum_bop_stageWordTotal_two_three_two`, the right by
`HJO.Sym.qop_two_three_apply_qop_two_three_apply_one` and `HJO.Sym.qop_four_six_apply_one`. The
identity is then one comparison of two explicit combinations of the nine degree-six `e`-monomials.

**The comparison is a check and not a construction.** The two sides share no lemma: the left is
`z_1` of `HJO.Sweep.zop` and `HJO.Sym.Bop` on the total space, run twice from the seed
`-e_1y_1^2 + uy_1^3` and projected by `ct ∘ d_-^{(1)}`; the right is the slope operators of
`HJO.Sym.Qop` on `Λ`, reached through `HJO.Mellit.theta_completeHomog_two_apply_one_smul` and the
axis expansion of `HJO.Sym.completeHomog`. A sign or a normalising scalar lost on either route would
leave the final identity unprovable, and at `A = 1` the same two routes are checked against each
other by `HJO.Mellit.theta_completeHomog_one_apply_one_eq_sum_bop`.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, `qu ≠ 0`, `qu ≠ 1` and `qu ≠ -1` are
`HJO.Mellit.lhsAt_two_three_two_iff_qop`'s, and `M = (1-q)(1-u) ≠ 0` — hence also `u ≠ 1` — is what
`HJO.Sym.Qop`'s `M^{-1}` costs on the right-hand side. Each is an inverse that becomes the zero map
where it fails, so at those parameters the clause is false rather than vacuous;
`HJO.Mellit.not_lhsWord_two_three_of_slopeHom_u_one` refutes a neighbouring clause at `u = 1`
outright. At algebraically independent `q, u` all of them hold.

`hΘ` is a hypothesis and no slope homomorphism is constructed here, so what is proved is the
clause *at any slope homomorphism* — the same standing caveat as the earlier instances
at `[1]`. -/
theorem lhsAt_two_three_two_of_axis (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) (hvn : q * u + 1 ≠ 0)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) :
    LhsAt q u 2 3 Θ [2] := by
  refine (lhsAt_two_three_two_iff_qop hq0 hu0 hq1 hv0 hv1 hvn hΘ).2 ?_
  rw [sum_bop_stageWordTotal_two_three_two hq0 hu0 hq1,
    qop_two_three_apply_qop_two_three_apply_one hM, qop_four_six_apply_one hM]
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

end HJO.Mellit

end
