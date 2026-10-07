/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepOnePartStageTwoTable

/-! # The letter `z_1` on the monomials of weight six

The values `z_1(y_1^jCf)` of the replicated letter at the monomials of total weight six — the
eleven monomials of the one-part stage word `G_2` — and what they read: the graded displacements
`d^*_+(Cf)` at weight five to eight (`HJO.Sweep.dplusStar_C_elemSymm_six`, `_seven`, `_eight` and
the `HJO.Sweep.dplusStar_C_elemSymm_*_expand` rows), and the two bookkeeping lemmas
`HJO.Sweep.div_one_sub_smul_eq_smul` and `HJO.Sweep.auxVar_pow_mul_smul_auxVar_pow_mul_C`.

Each value is `HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C`,
`z_1(y_1^mCA) = q/(1-q)·(d^*_+(C(B_mA)) - B_m(d^*_+(CA)))`, against the graded displacement of its
coefficient and the Hall--Littlewood table of `HJO/Shuffle/SweepOnePartStageTwoTable.lean`;
the bracket is `1 - q` times the answer, which is where `q ≠ 1` is spent. The route is described in
`HJO/Shuffle/SweepOnePartStageTwoLetter.lean`.

## References

This file computes with `HJO.Sweep.zop`, `HJO.Sym.Bop`, `HJO.Sweep.bopExt`, `HJO.Sweep.dplusStar`
and `HJO.Sym.elemSymm`.
-/

@[expose] public section

-- Every computation below closes on a polynomial identity in the `e`-monomials and the scalars
-- `C q`, `C u`, and each is normalised by the *same* rewrite set: which members of it fire depends
-- on the monomial, so some are unused in each individual proof.
set_option linter.unusedSimpArgs false

-- Every exponent written as a numeral in this file is a natural number. Saying so up front lets
-- each `x ^ n` resolve `HPow _ ℕ _` at once instead of retrying instance resolution for the
-- pending numeral type until defaulting, which dominated elaboration here. The elaborated terms
-- are the ones the default instance would produce.
local macro_rules | `($x ^ $n:num) => `(rightact% HPow.hPow $x ($n : ℕ))

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- `d^*_+(e_6)`, one letter past `HJO.Sweep.dplusStar_C_elemSymm_five`: the weight the first
half of the `z_1` step on `G_2` reaches, since every `B_m` there lands at weight six. -/
theorem dplusStar_C_elemSymm_six (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 6))
      = MvPolynomial.C (elemSymm L 6)
        + scal (q - 1) * starLetter u * MvPolynomial.C (elemSymm L 5)
        - scal (q - 1) * starLetter u ^ 2 * MvPolynomial.C (elemSymm L 4)
        + scal (q - 1) * starLetter u ^ 3 * MvPolynomial.C (elemSymm L 3)
        - scal (q - 1) * starLetter u ^ 4 * MvPolynomial.C (elemSymm L 2)
        + scal (q - 1) * starLetter u ^ 5 * MvPolynomial.C (elemSymm L 1)
        - scal (q - 1) * starLetter u ^ 6 := by
  rw [dplusStar_C_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [elemSymm_zero L]
  ring

/-- `d^*_+(e_7)`, one letter past `HJO.Sweep.dplusStar_C_elemSymm_six`. -/
theorem dplusStar_C_elemSymm_seven (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 7))
      = MvPolynomial.C (elemSymm L 7)
        + scal (q - 1) * starLetter u * MvPolynomial.C (elemSymm L 6)
        - scal (q - 1) * starLetter u ^ 2 * MvPolynomial.C (elemSymm L 5)
        + scal (q - 1) * starLetter u ^ 3 * MvPolynomial.C (elemSymm L 4)
        - scal (q - 1) * starLetter u ^ 4 * MvPolynomial.C (elemSymm L 3)
        + scal (q - 1) * starLetter u ^ 5 * MvPolynomial.C (elemSymm L 2)
        - scal (q - 1) * starLetter u ^ 6 * MvPolynomial.C (elemSymm L 1)
        + scal (q - 1) * starLetter u ^ 7 := by
  rw [dplusStar_C_elemSymm,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [elemSymm_zero L]
  ring

/-- `d^*_+(e_8)`, one letter past `HJO.Sweep.dplusStar_C_elemSymm_seven`. -/
theorem dplusStar_C_elemSymm_eight (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 8))
      = MvPolynomial.C (elemSymm L 8)
        + scal (q - 1) * starLetter u * MvPolynomial.C (elemSymm L 7)
        - scal (q - 1) * starLetter u ^ 2 * MvPolynomial.C (elemSymm L 6)
        + scal (q - 1) * starLetter u ^ 3 * MvPolynomial.C (elemSymm L 5)
        - scal (q - 1) * starLetter u ^ 4 * MvPolynomial.C (elemSymm L 4)
        + scal (q - 1) * starLetter u ^ 5 * MvPolynomial.C (elemSymm L 3)
        - scal (q - 1) * starLetter u ^ 6 * MvPolynomial.C (elemSymm L 2)
        + scal (q - 1) * starLetter u ^ 7 * MvPolynomial.C (elemSymm L 1)
        - scal (q - 1) * starLetter u ^ 8 := by
  rw [dplusStar_C_elemSymm,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [elemSymm_zero L]
  ring

/-- `d^*_+(e_5)`, graded. Unconditional, at every level. -/
theorem dplusStar_C_elemSymm_five_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 5) : Total L)
      = (1 : L) • (MvPolynomial.C (elemSymm L 5))
      + (q * u - u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 4))
      + (-(q * u ^ 2) + u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3))
      + (q * u ^ 3 - u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))
      + (-(q * u ^ 4) + u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))
      + (q * u ^ 5 - u ^ 5) • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C ((1 : Lambda L))) := by
  rw [dplusStar_C_elemSymm_five]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `d^*_+(e_1e_4)`, graded. Unconditional, at every level. -/
theorem dplusStar_C_elemSymm_one_mul_four_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 1 * elemSymm L 4) : Total L)
      = (1 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
      + (q * u - u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 4))
      + (q * u - u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
      + (q ^ 2 * u ^ 2 - 2 * q * u ^ 2 + u ^ 2)
            • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3))
      + (-(q * u ^ 2) + u ^ 2)
            • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
      + (-(q ^ 2 * u ^ 3) + 2 * q * u ^ 3 - u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))
      + (q * u ^ 3 - u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
      + (q ^ 2 * u ^ 4 - 3 * q * u ^ 4 + 2 * u ^ 4)
            • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))
      + (-(q ^ 2 * u ^ 5) + 2 * q * u ^ 5 - u ^ 5)
            • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C ((1 : Lambda L))) := by
  rw [dplusStar_C_mul, dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_four]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `d^*_+(e_2e_3)`, graded. Unconditional, at every level. -/
theorem dplusStar_C_elemSymm_two_mul_three_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 2 * elemSymm L 3) : Total L)
      = (1 : L) • (MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
      + (q * u - u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
      + (q * u - u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
      + (-(q * u ^ 2) + u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3))
      + (q ^ 2 * u ^ 2 - 3 * q * u ^ 2 + 2 * u ^ 2)
            • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
      + (-(q ^ 2 * u ^ 3) + 3 * q * u ^ 3 - 2 * u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))
      + (-(q ^ 2 * u ^ 3) + 2 * q * u ^ 3 - u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
      + (2 * q ^ 2 * u ^ 4 - 4 * q * u ^ 4 + 2 * u ^ 4)
            • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))
      + (-(q ^ 2 * u ^ 5) + 2 * q * u ^ 5 - u ^ 5)
            • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C ((1 : Lambda L))) := by
  rw [dplusStar_C_mul, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `d^*_+(e_1^2e_3)`, graded. Unconditional, at every level. -/
theorem dplusStar_C_elemSymm_one_sq_mul_three_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)) : Total L)
      = (1 : L) • (MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
      + (2 * q * u - 2 * u)
            • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
      + (q * u - u)
            • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
      + (q ^ 2 * u ^ 2 - 2 * q * u ^ 2 + u ^ 2)
            • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3))
      + (2 * q ^ 2 * u ^ 2 - 4 * q * u ^ 2 + 2 * u ^ 2)
            • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
      + (-(q * u ^ 2) + u ^ 2)
            • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
      + (q ^ 3 * u ^ 3 - 3 * q ^ 2 * u ^ 3 + 3 * q * u ^ 3 - u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))
      + (-(2 * q ^ 2 * u ^ 3) + 5 * q * u ^ 3 - 3 * u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
      + (-(q ^ 3 * u ^ 4) + 5 * q ^ 2 * u ^ 4 - 7 * q * u ^ 4 + 3 * u ^ 4)
            • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))
      + (q ^ 3 * u ^ 5 - 3 * q ^ 2 * u ^ 5 + 3 * q * u ^ 5 - u ^ 5)
            • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C ((1 : Lambda L))) := by
  rw [dplusStar_C_mul, dplusStar_C_mul, dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_three]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `d^*_+(e_1e_2^2)`, graded. Unconditional, at every level. -/
theorem dplusStar_C_elemSymm_one_mul_two_sq_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)) : Total L)
      = (1 : L) • (MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
      + (q * u - u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
      + (2 * q * u - 2 * u)
            • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
      + (2 * q ^ 2 * u ^ 2 - 6 * q * u ^ 2 + 4 * u ^ 2)
            • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
      + (q ^ 2 * u ^ 2 - 2 * q * u ^ 2 + u ^ 2)
            • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
      + (-(2 * q ^ 2 * u ^ 3) + 4 * q * u ^ 3 - 2 * u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))
      + (q ^ 3 * u ^ 3 - 5 * q ^ 2 * u ^ 3 + 7 * q * u ^ 3 - 3 * u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
      + (-(2 * q ^ 3 * u ^ 4) + 7 * q ^ 2 * u ^ 4 - 8 * q * u ^ 4 + 3 * u ^ 4)
            • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))
      + (q ^ 3 * u ^ 5 - 3 * q ^ 2 * u ^ 5 + 3 * q * u ^ 5 - u ^ 5)
            • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C ((1 : Lambda L))) := by
  rw [dplusStar_C_mul, dplusStar_C_mul, dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `d^*_+(e_1^3e_2)`, graded. Unconditional, at every level. -/
theorem dplusStar_C_elemSymm_one_cube_mul_two_expand (q u : L) (k : ℕ) :
    dplusStar q u k
        (MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))) : Total L)
      = (1 : L) • (MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))))
      + (3 * q * u - 3 * u)
            • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
      + (q * u - u)
            • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))))
      + (3 * q ^ 2 * u ^ 2 - 6 * q * u ^ 2 + 3 * u ^ 2)
            • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
      + (3 * q ^ 2 * u ^ 2 - 7 * q * u ^ 2 + 4 * u ^ 2)
            • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
      + (q ^ 3 * u ^ 3 - 3 * q ^ 2 * u ^ 3 + 3 * q * u ^ 3 - u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))
      + (3 * q ^ 3 * u ^ 3 - 12 * q ^ 2 * u ^ 3 + 15 * q * u ^ 3 - 6 * u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
      + (q ^ 4 * u ^ 4 - 7 * q ^ 3 * u ^ 4 + 15 * q ^ 2 * u ^ 4 - 13 * q * u ^ 4 + 4 * u ^ 4)
            • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))
      + (-(q ^ 4 * u ^ 5) + 4 * q ^ 3 * u ^ 5 - 6 * q ^ 2 * u ^ 5 + 4 * q * u ^ 5 - u ^ 5)
            • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C ((1 : Lambda L))) := by
  rw [dplusStar_C_mul, dplusStar_C_mul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `d^*_+(e_1^4)`, graded. Unconditional, at every level. -/
theorem dplusStar_C_elemSymm_one_pow_four_expand (q u : L) (k : ℕ) :
    dplusStar q u k
        (MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))) : Total L)
      = (1 : L) • (MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))))
      + (4 * q * u - 4 * u)
            • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
      + (6 * q ^ 2 * u ^ 2 - 12 * q * u ^ 2 + 6 * u ^ 2)
            • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
      + (4 * q ^ 3 * u ^ 3 - 12 * q ^ 2 * u ^ 3 + 12 * q * u ^ 3 - 4 * u ^ 3)
            • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1))
      + (q ^ 4 * u ^ 4 - 4 * q ^ 3 * u ^ 4 + 6 * q ^ 2 * u ^ 4 - 4 * q * u ^ 4 + u ^ 4)
            • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C ((1 : Lambda L))) := by
  rw [dplusStar_C_mul, dplusStar_C_mul, dplusStar_C_mul, dplusStar_C_elemSymm_one]
  simp only [starLetter, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow,
    MvPolynomial.smul_eq_C_mul, scal, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

omit [Algebra ℚ L] in
/-- Clearing `γ = q/(1-q)` against a factor `1 - q`: every value `z_1(y_1^jCf)` below is
`HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C`, `γ` times a bracket, and the bracket is computed as
`1 - q` times the answer. Stating it once lets each proof compute the bracket without restating
the answer. -/
theorem div_one_sub_smul_eq_smul {M : Type*} [AddCommGroup M] [Module L M]
    (h1q : (1 : L) - q ≠ 0) {X B : M} (h : X = (1 - q) • B) : (q / (1 - q)) • X = q • B := by
  rw [h, smul_smul, div_mul_cancel₀ q h1q]

/-! ### The termwise `y_1`-shift the replicated letter performs -/

omit [Algebra ℚ L] in
/-- `y_1^n·(x·y_1^kCf) = x·y_1^{n+k}Cf`: the outer `y_1` powers of
`HJO.Sweep.replicatedTotal_two_three_zero_apply` on one monomial of `V_1`, with its scalar
carried through. Applied under `mul_add` this performs the whole shift **syntactically**, so
neither the argument of the outer `z_1` nor the stage word at `[3]` needs any polynomial
normalisation. Unconditional. -/
theorem auxVar_pow_mul_smul_auxVar_pow_mul_C (x : L) (n k : ℕ) (f : Lambda L) :
    (auxVar 1 : Total L) ^ n * (x • ((auxVar 1 : Total L) ^ k * MvPolynomial.C f))
      = x • ((auxVar 1 : Total L) ^ (n + k) * MvPolynomial.C f) := by
  rw [mul_smul_comm, ← mul_assoc, ← pow_add]
/-- `z_1(y_1^2 C(e_4))`. -/
theorem zopOneStar_one_auxVar_sq_mul_C_elemSymm_four (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 4))
      = q • (
          (-(q ^ 4 * u) + q ^ 3 * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 5))
        + (-(q ^ 3 * u) + q ^ 2 * u - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(q ^ 2 * u) + u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (q ^ 3 * u ^ 2 - q ^ 2 * u ^ 2 + u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 4))
        + (q ^ 2 * u ^ 2 - q * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
        + (-(q ^ 2 * u ^ 3) + q * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 3))
        + (-(q * u ^ 3) + u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (q * u ^ 4 - u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_four_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C,
    bop_two_elemSymm_four, bop_two_elemSymm_one', bop_two_elemSymm_three,
    bop_two_elemSymm_two', bop_two_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^2 C(e_1e_3))`. -/
theorem zopOneStar_one_auxVar_sq_mul_C_elemSymm_one_mul_three (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
      = q • (
          (-(q ^ 4 * u) + 2 * q ^ 3 * u - q ^ 2 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 5))
        + (-(2 * q ^ 3 * u) + 3 * q ^ 2 * u - q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(q ^ 2 * u) + q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (-(q ^ 2 * u) + q * u - u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (-(q * u) + u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (-(q ^ 4 * u ^ 2) + 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 2 + q * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 4))
        + (-(q ^ 3 * u ^ 2) + 4 * q ^ 2 * u ^ 2 - 4 * q * u ^ 2 + 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (-(q ^ 2 * u ^ 2) + 2 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
        + (q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (q ^ 3 * u ^ 3 - 3 * q ^ 2 * u ^ 3 + 3 * q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 3))
        + (q ^ 2 * u ^ 3 - 3 * q * u ^ 3 + 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (-(q ^ 2 * u ^ 4) + 2 * q * u ^ 4 - u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_mul_three_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C,
    bop_two_elemSymm_one', bop_two_elemSymm_one_mul_three, bop_two_elemSymm_one_mul_two,
    bop_two_elemSymm_one_sq, bop_two_elemSymm_three, bop_two_elemSymm_two', bop_two_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^2 C(e_2^2))`. -/
theorem zopOneStar_one_auxVar_sq_mul_C_elemSymm_two_sq (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
      = q • (
          (-(q ^ 4 * u) + 2 * q ^ 3 * u - q ^ 2 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 5))
        + (-(2 * q ^ 3 * u) + 4 * q ^ 2 * u - 2 * q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(2 * q ^ 2 * u) + 2 * q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (-(q ^ 2 * u) + 2 * q * u - u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (-(2 * q * u) + u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (-(q ^ 4 * u ^ 2) + 4 * q ^ 3 * u ^ 2 - 5 * q ^ 2 * u ^ 2 + 2 * q * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 4))
        + (-(2 * q ^ 3 * u ^ 2) + 6 * q ^ 2 * u ^ 2 - 6 * q * u ^ 2 + 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (2 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
        + (-(q ^ 2 * u ^ 2) + 2 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (2 * q ^ 3 * u ^ 3 - 5 * q ^ 2 * u ^ 3 + 4 * q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 3))
        + (2 * q ^ 2 * u ^ 3 - 4 * q * u ^ 3 + 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (-(q ^ 2 * u ^ 4) + 2 * q * u ^ 4 - u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_two_sq_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C,
    bop_two_elemSymm_one', bop_two_elemSymm_one_mul_two, bop_two_elemSymm_one_sq,
    bop_two_elemSymm_two', bop_two_elemSymm_two_sq, bop_two_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^2 C(e_1^2e_2))`. -/
theorem zopOneStar_one_auxVar_sq_mul_C_elemSymm_one_sq_mul_two (hq1 : q ≠ 1) :
    zopOneStar q u 1
        ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
      = q • (
          (-(q ^ 4 * u) + 3 * q ^ 3 * u - 3 * q ^ 2 * u + q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 5))
        + (-(3 * q ^ 3 * u) + 7 * q ^ 2 * u - 5 * q * u + u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(q ^ 2 * u) + 2 * q * u - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (-(3 * q ^ 2 * u) + 5 * q * u - 2 * u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (-(2 * q * u) + 2 * u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (-(q * u))
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))))
        + (-(2 * q ^ 4 * u ^ 2) + 7 * q ^ 3 * u ^ 2 - 9 * q ^ 2 * u ^ 2 + 5 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 4))
        + (-(4 * q ^ 3 * u ^ 2) + 12 * q ^ 2 * u ^ 2 - 12 * q * u ^ 2 + 4 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (-(q ^ 2 * u ^ 2) + 2 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
        + (-(2 * q ^ 2 * u ^ 2) + 5 * q * u ^ 2 - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (-(q ^ 4 * u ^ 3) + 5 * q ^ 3 * u ^ 3 - 9 * q ^ 2 * u ^ 3 + 7 * q * u ^ 3 - 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 3))
        + (-(q ^ 3 * u ^ 3) + 5 * q ^ 2 * u ^ 3 - 7 * q * u ^ 3 + 3 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (q ^ 3 * u ^ 4 - 3 * q ^ 2 * u ^ 4 + 3 * q * u ^ 4 - u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_sq_mul_two_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C,
    bop_two_elemSymm_one', bop_two_elemSymm_one_cube, bop_two_elemSymm_one_mul_two,
    bop_two_elemSymm_one_sq, bop_two_elemSymm_one_sq_mul_two, bop_two_elemSymm_two',
    bop_two_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^3 C(e_3))`. -/
theorem zopOneStar_one_auxVar_cube_mul_C_elemSymm_three (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 3))
      = q • (
          (q ^ 3 * u - q ^ 2 * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 5))
        + (q ^ 2 * u - q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (q * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (-(q ^ 2 * u ^ 2) + q * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 4))
        + (-(q * u ^ 2))
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (q * u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 3))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_three_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C,
    bop_three_elemSymm_one, bop_three_elemSymm_three, bop_three_elemSymm_two, bop_three_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^3 C(e_1e_2))`. -/
theorem zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_mul_two (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
      = q • (
          (q ^ 3 * u - 2 * q ^ 2 * u + q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 5))
        + (2 * q ^ 2 * u - 3 * q * u + u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (q * u - u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (q * u - u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 2 + 3 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 4))
        + (q ^ 2 * u ^ 2 - 3 * q * u ^ 2 + 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (-(u ^ 2))
              • ((auxVar 1 : Total L) ^ 2
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (-(q ^ 2 * u ^ 3) + 2 * q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 3))
        + (u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_mul_two_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C,
    bop_three_elemSymm_one, bop_three_elemSymm_one_mul_two, bop_three_elemSymm_one_sq,
    bop_three_elemSymm_two, bop_three_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^3 C(e_1^3))`. -/
theorem zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_cube (hq1 : q ≠ 1) :
    zopOneStar q u 1
        ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
      = q • (
          (q ^ 3 * u - 3 * q ^ 2 * u + 3 * q * u - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 5))
        + (3 * q ^ 2 * u - 6 * q * u + 3 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (3 * q * u - 3 * u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))))
        + (2 * q ^ 3 * u ^ 2 - 6 * q ^ 2 * u ^ 2 + 6 * q * u ^ 2 - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 4))
        + (3 * q ^ 2 * u ^ 2 - 6 * q * u ^ 2 + 3 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (-(u ^ 2))
              • ((auxVar 1 : Total L) ^ 2
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))))
        + (q ^ 3 * u ^ 3 - 3 * q ^ 2 * u ^ 3 + 3 * q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 3))
        + (u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_cube_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C,
    bop_three_elemSymm_one, bop_three_elemSymm_one_cube, bop_three_elemSymm_one_sq,
    bop_three_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^4 C(e_2))`. -/
theorem zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_two (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2))
      = q • (
          (-(q ^ 2 * u) + q * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 5))
        + (-(q * u) + u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (q * u ^ 2 - u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 4))
        + (u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
        + (-(u ^ 3)) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_two_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C,
    bop_four_elemSymm_one, bop_four_elemSymm_two, bop_four_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^4 C(e_1^2))`. -/
theorem zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_one_sq (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
      = q • (
          (-(q ^ 2 * u) + 2 * q * u - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 5))
        + (-(2 * q * u) + 2 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (-(q ^ 2 * u ^ 2) + 2 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 4))
        + (u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (-(u ^ 3))
              • ((auxVar 1 : Total L) ^ 3
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
        + (u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_sq_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C,
    bop_four_elemSymm_one, bop_four_elemSymm_one_sq, bop_four_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^5 C(e_1))`. -/
theorem zopOneStar_one_auxVar_pow_five_mul_C_elemSymm_one (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1))
      = q • (
          (q * u - u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 5))
        + (u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(u ^ 2)) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (-(u ^ 4)) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (u ^ 5) • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C,
    bop_five_elemSymm_one, bop_five_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^6 C(1))`. -/
theorem zopOneStar_one_auxVar_pow_six_mul_C_one (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C ((1 : Lambda L)))
      = q • (
          (-u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 5))
        + (u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 4))
        + (-(u ^ 3)) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 3))
        + (u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2))
        + (-(u ^ 5)) • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1))
        + (u ^ 6) • ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C ((1 : Lambda L)))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_one, map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C,
    bop_six_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

end HJO.Sweep

end
