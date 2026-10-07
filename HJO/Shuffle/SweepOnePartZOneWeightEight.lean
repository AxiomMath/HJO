/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepOnePartZOneWeightSix

/-! # The letter `z_1` on the monomials of weight eight

The values `z_1(y_1^jCf)` of the replicated letter at the eighteen monomials of total weight eight
that `y_1^2z_1(G_2)` carries, `j` from `3` to `8`: the outer `z_1` of the stage word at `[3]` reads
exactly these. Each is `HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C` against the graded displacement
of its coefficient (`HJO/Shuffle/SweepOnePartZOneWeightSix.lean`) and the Hall--Littlewood
table (`HJO/Shuffle/SweepOnePartStageTwoTable.lean`); only `q ≠ 1` is read. The route is
described in `HJO/Shuffle/SweepOnePartStageTwoLetter.lean`.

## References

The computation uses `HJO.Sweep.zop`, `HJO.Sym.Bop`, `HJO.Sweep.bopExt` and `HJO.Sweep.dplusStar`.
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

/-- `z_1(y_1^3 C(e_5))`. -/
theorem zopOneStar_one_auxVar_cube_mul_C_elemSymm_five (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
      = q • (
          (q ^ 5 * u - q ^ 4 * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (q ^ 4 * u - q ^ 3 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (q ^ 3 * u - q ^ 2 * u + u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (q ^ 2 * u - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 3 * elemSymm L 4))
        + (-(q ^ 4 * u ^ 2) + q ^ 3 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (-(q ^ 3 * u ^ 2) + q ^ 2 * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (-(q ^ 2 * u ^ 2) + q * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 4))
        + (-(q * u ^ 2) + u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3 * elemSymm L 3))
        + (q ^ 3 * u ^ 3 - q ^ 2 * u ^ 3 + u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (q ^ 2 * u ^ 3 - q * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (-(q ^ 2 * u ^ 4) + q * u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
        + (-(q * u ^ 4) + u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (q * u ^ 5 - u ^ 5) • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 3))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_five_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^3 C(e_1e_4))`. -/
theorem zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_mul_four (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
      = q • (
          (q ^ 5 * u - 2 * q ^ 4 * u + q ^ 3 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (2 * q ^ 4 * u - 3 * q ^ 3 * u + q ^ 2 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (q ^ 3 * u - 2 * q ^ 2 * u + q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (q ^ 2 * u - q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 3 * elemSymm L 4))
        + (q ^ 3 * u - q ^ 2 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (q ^ 2 * u - q * u + u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (q * u - u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3)))
        + (q ^ 5 * u ^ 2 - 3 * q ^ 4 * u ^ 2 + 3 * q ^ 3 * u ^ 2 - q ^ 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (q ^ 4 * u ^ 2 - 4 * q ^ 3 * u ^ 2 + 4 * q ^ 2 * u ^ 2 - q * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 2 + 3 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 4))
        + (q ^ 2 * u ^ 2 - 2 * q * u ^ 2 + u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3 * elemSymm L 3))
        + (-(q ^ 2 * u ^ 2) + q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))
        + (-(q * u ^ 2) + u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))
        + (-(q ^ 4 * u ^ 3) + 3 * q ^ 3 * u ^ 3 - 3 * q ^ 2 * u ^ 3 + q * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (-(q ^ 3 * u ^ 3) + 4 * q ^ 2 * u ^ 3 - 4 * q * u ^ 3 + 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(q ^ 2 * u ^ 3) + 2 * q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (q ^ 3 * u ^ 4 - 3 * q ^ 2 * u ^ 4 + 3 * q * u ^ 4 - u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
        + (q ^ 2 * u ^ 4 - 3 * q * u ^ 4 + 2 * u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (-(q ^ 2 * u ^ 5) + 2 * q * u ^ 5 - u ^ 5)
              • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 3))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_mul_four_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^3 C(e_2e_3))`. -/
theorem zopOneStar_one_auxVar_cube_mul_C_elemSymm_two_mul_three (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
      = q • (
          (q ^ 5 * u - 2 * q ^ 4 * u + q ^ 3 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (2 * q ^ 4 * u - 4 * q ^ 3 * u + 2 * q ^ 2 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (2 * q ^ 3 * u - 3 * q ^ 2 * u + q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (q ^ 2 * u - q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 3 * elemSymm L 4))
        + (q ^ 3 * u - 2 * q ^ 2 * u + q * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (2 * q ^ 2 * u - 3 * q * u + u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (q * u - u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3)))
        + (q * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3)))
        + (q ^ 5 * u ^ 2 - 4 * q ^ 4 * u ^ 2 + 5 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (2 * q ^ 4 * u ^ 2 - 7 * q ^ 3 * u ^ 2 + 8 * q ^ 2 * u ^ 2 - 3 * q * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (q ^ 3 * u ^ 2 - 4 * q ^ 2 * u ^ 2 + 4 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 4))
        + (-(q * u ^ 2) + u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3 * elemSymm L 3))
        + (q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 2 + 3 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))
        + (q ^ 2 * u ^ 2 - 3 * q * u ^ 2 + u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))
        + (-(2 * q ^ 4 * u ^ 3) + 6 * q ^ 3 * u ^ 3 - 6 * q ^ 2 * u ^ 3 + 2 * q * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (-(3 * q ^ 3 * u ^ 3) + 8 * q ^ 2 * u ^ 3 - 7 * q * u ^ 3 + 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(q ^ 2 * u ^ 3) + 3 * q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (-(q ^ 2 * u ^ 3) + 2 * q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (2 * q ^ 3 * u ^ 4 - 5 * q ^ 2 * u ^ 4 + 4 * q * u ^ 4 - u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
        + (2 * q ^ 2 * u ^ 4 - 4 * q * u ^ 4 + 2 * u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (-(q ^ 2 * u ^ 5) + 2 * q * u ^ 5 - u ^ 5)
              • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 3))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_two_mul_three_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^3 C(e_1^2e_3))`. -/
theorem zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_sq_mul_three (hq1 : q ≠ 1) :
    zopOneStar q u 1
        ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
      = q • (
          (q ^ 5 * u - 3 * q ^ 4 * u + 3 * q ^ 3 * u - q ^ 2 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (3 * q ^ 4 * u - 7 * q ^ 3 * u + 5 * q ^ 2 * u - q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (q ^ 3 * u - 3 * q ^ 2 * u + 3 * q * u - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (q ^ 2 * u - 2 * q * u + u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 3 * elemSymm L 4))
        + (3 * q ^ 3 * u - 5 * q ^ 2 * u + 2 * q * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (2 * q ^ 2 * u - 4 * q * u + 2 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (2 * q * u - 2 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3)))
        + (q ^ 2 * u - q * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))))
        + (q * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))))
        + (2 * q ^ 5 * u ^ 2 - 7 * q ^ 4 * u ^ 2 + 9 * q ^ 3 * u ^ 2 - 5 * q ^ 2 * u ^ 2
            + q * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (4 * q ^ 4 * u ^ 2 - 13 * q ^ 3 * u ^ 2 + 15 * q ^ 2 * u ^ 2 - 7 * q * u ^ 2 + u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (2 * q ^ 3 * u ^ 2 - 6 * q ^ 2 * u ^ 2 + 6 * q * u ^ 2 - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 4))
        + (q ^ 2 * u ^ 2 - 2 * q * u ^ 2 + u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3 * elemSymm L 3))
        + (2 * q ^ 3 * u ^ 2 - 7 * q ^ 2 * u ^ 2 + 7 * q * u ^ 2 - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))
        + (2 * q ^ 2 * u ^ 2 - 4 * q * u ^ 2 + 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))
        + (-(q * u ^ 2))
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))))
        + (q ^ 5 * u ^ 3 - 5 * q ^ 4 * u ^ 3 + 10 * q ^ 3 * u ^ 3 - 10 * q ^ 2 * u ^ 3
            + 5 * q * u ^ 3 - u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (q ^ 4 * u ^ 3 - 7 * q ^ 3 * u ^ 3 + 15 * q ^ 2 * u ^ 3 - 13 * q * u ^ 3 + 4 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (q ^ 3 * u ^ 3 - 3 * q ^ 2 * u ^ 3 + 3 * q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (-(2 * q ^ 2 * u ^ 3) + 5 * q * u ^ 3 - 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (-(q ^ 4 * u ^ 4) + 5 * q ^ 3 * u ^ 4 - 9 * q ^ 2 * u ^ 4 + 7 * q * u ^ 4 - 2 * u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
        + (-(q ^ 3 * u ^ 4) + 5 * q ^ 2 * u ^ 4 - 7 * q * u ^ 4 + 3 * u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (q ^ 3 * u ^ 5 - 3 * q ^ 2 * u ^ 5 + 3 * q * u ^ 5 - u ^ 5)
              • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 3))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_sq_mul_three_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^3 C(e_1e_2^2))`. -/
theorem zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_mul_two_sq (hq1 : q ≠ 1) :
    zopOneStar q u 1
        ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
      = q • (
          (q ^ 5 * u - 3 * q ^ 4 * u + 3 * q ^ 3 * u - q ^ 2 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (3 * q ^ 4 * u - 8 * q ^ 3 * u + 7 * q ^ 2 * u - 2 * q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (2 * q ^ 3 * u - 4 * q ^ 2 * u + 2 * q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (3 * q ^ 3 * u - 7 * q ^ 2 * u + 5 * q * u - u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (4 * q ^ 2 * u - 6 * q * u + 2 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (q * u - u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3)))
        + (q ^ 2 * u - 2 * q * u + u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))))
        + (2 * q * u - 2 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))))
        + (u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))))
        + (2 * q ^ 5 * u ^ 2 - 8 * q ^ 4 * u ^ 2 + 12 * q ^ 3 * u ^ 2 - 8 * q ^ 2 * u ^ 2
            + 2 * q * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (5 * q ^ 4 * u ^ 2 - 18 * q ^ 3 * u ^ 2 + 23 * q ^ 2 * u ^ 2 - 12 * q * u ^ 2
            + 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (2 * q ^ 3 * u ^ 2 - 6 * q ^ 2 * u ^ 2 + 6 * q * u ^ 2 - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 4))
        + (4 * q ^ 3 * u ^ 2 - 12 * q ^ 2 * u ^ 2 + 12 * q * u ^ 2 - 4 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))
        + (2 * q ^ 2 * u ^ 2 - 6 * q * u ^ 2 + 4 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))
        + (q ^ 2 * u ^ 2 - 2 * q * u ^ 2 + u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))))
        + (-(u ^ 2))
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))))
        + (q ^ 5 * u ^ 3 - 7 * q ^ 4 * u ^ 3 + 16 * q ^ 3 * u ^ 3 - 16 * q ^ 2 * u ^ 3
            + 7 * q * u ^ 3 - u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (2 * q ^ 4 * u ^ 3 - 12 * q ^ 3 * u ^ 3 + 23 * q ^ 2 * u ^ 3 - 18 * q * u ^ 3
            + 5 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(2 * q ^ 2 * u ^ 3) + 4 * q * u ^ 3 - 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (q ^ 3 * u ^ 3 - 5 * q ^ 2 * u ^ 3 + 7 * q * u ^ 3 - 3 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (-(2 * q ^ 4 * u ^ 4) + 8 * q ^ 3 * u ^ 4 - 12 * q ^ 2 * u ^ 4 + 8 * q * u ^ 4
            - 2 * u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
        + (-(2 * q ^ 3 * u ^ 4) + 7 * q ^ 2 * u ^ 4 - 8 * q * u ^ 4 + 3 * u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (q ^ 3 * u ^ 5 - 3 * q ^ 2 * u ^ 5 + 3 * q * u ^ 5 - u ^ 5)
              • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 3))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_mul_two_sq_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^3 C(e_1^3e_2))`. -/
theorem zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_cube_mul_two (hq1 : q ≠ 1) :
    zopOneStar q u 1
        ((auxVar 1 : Total L) ^ 3
          * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))))
      = q • (
          (q ^ 5 * u - 4 * q ^ 4 * u + 6 * q ^ 3 * u - 4 * q ^ 2 * u + q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (4 * q ^ 4 * u - 13 * q ^ 3 * u + 15 * q ^ 2 * u - 7 * q * u + u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (q ^ 3 * u - 3 * q ^ 2 * u + 3 * q * u - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (6 * q ^ 3 * u - 15 * q ^ 2 * u + 12 * q * u - 3 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (3 * q ^ 2 * u - 6 * q * u + 3 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (4 * q ^ 2 * u - 7 * q * u + 3 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))))
        + (3 * q * u - 3 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))))
        + (q * u - u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))))
        + (u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))))
        + (3 * q ^ 5 * u ^ 2 - 13 * q ^ 4 * u ^ 2 + 22 * q ^ 3 * u ^ 2 - 18 * q ^ 2 * u ^ 2
            + 7 * q * u ^ 2 - u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (9 * q ^ 4 * u ^ 2 - 33 * q ^ 3 * u ^ 2 + 45 * q ^ 2 * u ^ 2 - 27 * q * u ^ 2
            + 6 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (2 * q ^ 3 * u ^ 2 - 6 * q ^ 2 * u ^ 2 + 6 * q * u ^ 2 - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 4))
        + (9 * q ^ 3 * u ^ 2 - 27 * q ^ 2 * u ^ 2 + 27 * q * u ^ 2 - 9 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))
        + (3 * q ^ 2 * u ^ 2 - 6 * q * u ^ 2 + 3 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))
        + (3 * q ^ 2 * u ^ 2 - 7 * q * u ^ 2 + 4 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))))
        + (-(u ^ 2))
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))))
        + (3 * q ^ 5 * u ^ 3 - 15 * q ^ 4 * u ^ 3 + 30 * q ^ 3 * u ^ 3 - 30 * q ^ 2 * u ^ 3
            + 15 * q * u ^ 3 - 3 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (6 * q ^ 4 * u ^ 3 - 27 * q ^ 3 * u ^ 3 + 45 * q ^ 2 * u ^ 3 - 33 * q * u ^ 3
            + 9 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (q ^ 3 * u ^ 3 - 3 * q ^ 2 * u ^ 3 + 3 * q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (3 * q ^ 3 * u ^ 3 - 12 * q ^ 2 * u ^ 3 + 15 * q * u ^ 3 - 6 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))))
        + (q ^ 5 * u ^ 4 - 7 * q ^ 4 * u ^ 4 + 18 * q ^ 3 * u ^ 4 - 22 * q ^ 2 * u ^ 4
            + 13 * q * u ^ 4 - 3 * u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
        + (q ^ 4 * u ^ 4 - 7 * q ^ 3 * u ^ 4 + 15 * q ^ 2 * u ^ 4 - 13 * q * u ^ 4 + 4 * u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (-(q ^ 4 * u ^ 5) + 4 * q ^ 3 * u ^ 5 - 6 * q ^ 2 * u ^ 5 + 4 * q * u ^ 5 - u ^ 5)
              • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 3))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_cube_mul_two_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^4 C(e_4))`. -/
theorem zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_four (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
      = q • (
          (-(q ^ 4 * u) + q ^ 3 * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (-(q ^ 3 * u) + q ^ 2 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (-(q ^ 2 * u) + q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (-(q * u)) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 3 * elemSymm L 4))
        + (q ^ 3 * u ^ 2 - q ^ 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (q ^ 2 * u ^ 2 - q * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (q * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 4))
        + (-(q ^ 2 * u ^ 3) + q * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (-(q * u ^ 3))
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (q * u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_four_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^4 C(e_1e_3))`. -/
theorem zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_one_mul_three (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
      = q • (
          (-(q ^ 4 * u) + 2 * q ^ 3 * u - q ^ 2 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (-(2 * q ^ 3 * u) + 3 * q ^ 2 * u - q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (-(q ^ 2 * u) + 2 * q * u - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (-(q * u) + u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 3 * elemSymm L 4))
        + (-(q ^ 2 * u) + q * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (-(q * u) + u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (-u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3)))
        + (-(q ^ 4 * u ^ 2) + 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 2 + q * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (-(q ^ 3 * u ^ 2) + 4 * q ^ 2 * u ^ 2 - 4 * q * u ^ 2 + u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (-(q ^ 2 * u ^ 2) + 2 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 4))
        + (q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))
        + (u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))
        + (q ^ 3 * u ^ 3 - 3 * q ^ 2 * u ^ 3 + 3 * q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (q ^ 2 * u ^ 3 - 3 * q * u ^ 3 + 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(u ^ 3))
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (-(q ^ 2 * u ^ 4) + 2 * q * u ^ 4 - u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
        + (u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_mul_three_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^4 C(e_2^2))`. -/
theorem zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_two_sq (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
      = q • (
          (-(q ^ 4 * u) + 2 * q ^ 3 * u - q ^ 2 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (-(2 * q ^ 3 * u) + 4 * q ^ 2 * u - 2 * q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (-(2 * q ^ 2 * u) + 2 * q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (-(q ^ 2 * u) + 2 * q * u - u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (-(2 * q * u) + 2 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (-u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3)))
        + (-(q ^ 4 * u ^ 2) + 4 * q ^ 3 * u ^ 2 - 5 * q ^ 2 * u ^ 2 + 2 * q * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (-(2 * q ^ 3 * u ^ 2) + 6 * q ^ 2 * u ^ 2 - 6 * q * u ^ 2 + 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (2 * q * u ^ 2 - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 4))
        + (-(q ^ 2 * u ^ 2) + 2 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))
        + (u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2)))
        + (2 * q ^ 3 * u ^ 3 - 5 * q ^ 2 * u ^ 3 + 4 * q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (2 * q ^ 2 * u ^ 3 - 4 * q * u ^ 3 + 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(u ^ 3))
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (-(q ^ 2 * u ^ 4) + 2 * q * u ^ 4 - u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
        + (u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_two_sq_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^4 C(e_1^2e_2))`. -/
theorem zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_one_sq_mul_two (hq1 : q ≠ 1) :
    zopOneStar q u 1
        ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
      = q • (
          (-(q ^ 4 * u) + 3 * q ^ 3 * u - 3 * q ^ 2 * u + q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (-(3 * q ^ 3 * u) + 7 * q ^ 2 * u - 5 * q * u + u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (-(q ^ 2 * u) + 2 * q * u - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (-(3 * q ^ 2 * u) + 5 * q * u - 2 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (-(2 * q * u) + 2 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (-(q * u) + u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))))
        + (-u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))))
        + (-(2 * q ^ 4 * u ^ 2) + 7 * q ^ 3 * u ^ 2 - 9 * q ^ 2 * u ^ 2 + 5 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (-(4 * q ^ 3 * u ^ 2) + 12 * q ^ 2 * u ^ 2 - 12 * q * u ^ 2 + 4 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (-(q ^ 2 * u ^ 2) + 2 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 4))
        + (-(2 * q ^ 2 * u ^ 2) + 5 * q * u ^ 2 - 3 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))
        + (u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))))
        + (-(q ^ 4 * u ^ 3) + 5 * q ^ 3 * u ^ 3 - 9 * q ^ 2 * u ^ 3 + 7 * q * u ^ 3 - 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (-(q ^ 3 * u ^ 3) + 5 * q ^ 2 * u ^ 3 - 7 * q * u ^ 3 + 3 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(u ^ 3))
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))))
        + (q ^ 3 * u ^ 4 - 3 * q ^ 2 * u ^ 4 + 3 * q * u ^ 4 - u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
        + (u ^ 4)
              • ((auxVar 1 : Total L) ^ 4
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_sq_mul_two_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^4 C(e_1^4))`. -/
theorem zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_one_pow_four (hq1 : q ≠ 1) :
    zopOneStar q u 1
        ((auxVar 1 : Total L) ^ 4
          * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))))
      = q • (
          (-(q ^ 4 * u) + 4 * q ^ 3 * u - 6 * q ^ 2 * u + 4 * q * u - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (-(4 * q ^ 3 * u) + 12 * q ^ 2 * u - 12 * q * u + 4 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (-(6 * q ^ 2 * u) + 12 * q * u - 6 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (-(4 * q * u) + 4 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))))
        + (-u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))))
        + (-(3 * q ^ 4 * u ^ 2) + 12 * q ^ 3 * u ^ 2 - 18 * q ^ 2 * u ^ 2 + 12 * q * u ^ 2
            - 3 * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (-(8 * q ^ 3 * u ^ 2) + 24 * q ^ 2 * u ^ 2 - 24 * q * u ^ 2 + 8 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (-(6 * q ^ 2 * u ^ 2) + 12 * q * u ^ 2 - 6 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))
        + (u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))))
        + (-(3 * q ^ 4 * u ^ 3) + 12 * q ^ 3 * u ^ 3 - 18 * q ^ 2 * u ^ 3 + 12 * q * u ^ 3
            - 3 * u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (-(4 * q ^ 3 * u ^ 3) + 12 * q ^ 2 * u ^ 3 - 12 * q * u ^ 3 + 4 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(u ^ 3))
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))))
        + (-(q ^ 4 * u ^ 4) + 4 * q ^ 3 * u ^ 4 - 6 * q ^ 2 * u ^ 4 + 4 * q * u ^ 4 - u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
        + (u ^ 4)
              • ((auxVar 1 : Total L) ^ 4
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_pow_four_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^5 C(e_3))`. -/
theorem zopOneStar_one_auxVar_pow_five_mul_C_elemSymm_three (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 3))
      = q • (
          (q ^ 3 * u - q ^ 2 * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (q ^ 2 * u - q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (q * u - u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 3 * elemSymm L 4))
        + (-(q ^ 2 * u ^ 2) + q * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (-(q * u ^ 2) + u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (-(u ^ 2)) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3 * elemSymm L 3))
        + (q * u ^ 3 - u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (-(u ^ 4)) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (u ^ 5) • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 3))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_three_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^5 C(e_1e_2))`. -/
theorem zopOneStar_one_auxVar_pow_five_mul_C_elemSymm_one_mul_two (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
      = q • (
          (q ^ 3 * u - 2 * q ^ 2 * u + q * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (2 * q ^ 2 * u - 3 * q * u + u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (q * u - u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (q * u - u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 2 + 3 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (q ^ 2 * u ^ 2 - 3 * q * u ^ 2 + 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (-(u ^ 2))
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))
        + (-(q ^ 2 * u ^ 3) + 2 * q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (-(u ^ 4))
              • ((auxVar 1 : Total L) ^ 4
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (u ^ 5) • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_mul_two_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^5 C(e_1^3))`. -/
theorem zopOneStar_one_auxVar_pow_five_mul_C_elemSymm_one_cube (hq1 : q ≠ 1) :
    zopOneStar q u 1
        ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
      = q • (
          (q ^ 3 * u - 3 * q ^ 2 * u + 3 * q * u - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (3 * q ^ 2 * u - 6 * q * u + 3 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (3 * q * u - 3 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))))
        + (2 * q ^ 3 * u ^ 2 - 6 * q ^ 2 * u ^ 2 + 6 * q * u ^ 2 - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (3 * q ^ 2 * u ^ 2 - 6 * q * u ^ 2 + 3 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (-(u ^ 2))
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))))
        + (q ^ 3 * u ^ 3 - 3 * q ^ 2 * u ^ 3 + 3 * q * u ^ 3 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))))
        + (-(u ^ 4))
              • ((auxVar 1 : Total L) ^ 4
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))))
        + (u ^ 5)
              • ((auxVar 1 : Total L) ^ 5
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_cube_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^6 C(e_2))`. -/
theorem zopOneStar_one_auxVar_pow_six_mul_C_elemSymm_two (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C (elemSymm L 2))
      = q • (
          (-(q ^ 2 * u) + q * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (-(q * u) + u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (-u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (q * u ^ 2 - u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 4))
        + (-(u ^ 3)) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
        + (-(u ^ 5)) • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (u ^ 6) • ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C (elemSymm L 2))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_two_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^6 C(e_1^2))`. -/
theorem zopOneStar_one_auxVar_pow_six_mul_C_elemSymm_one_sq (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
      = q • (
          (-(q ^ 2 * u) + 2 * q * u - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (-(2 * q * u) + 2 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (-u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (-(q ^ 2 * u ^ 2) + 2 * q * u ^ 2 - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))
        + (-(u ^ 3))
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (u ^ 4)
              • ((auxVar 1 : Total L) ^ 4
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (-(u ^ 5))
              • ((auxVar 1 : Total L) ^ 5
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
        + (u ^ 6) • ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_sq_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^7 C(e_1))`. -/
theorem zopOneStar_one_auxVar_pow_seven_mul_C_elemSymm_one (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 7 * MvPolynomial.C (elemSymm L 1))
      = q • (
          (q * u - u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (-(u ^ 2)) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(u ^ 4)) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (u ^ 5) • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (-(u ^ 6)) • ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (u ^ 7) • ((auxVar 1 : Total L) ^ 7 * MvPolynomial.C (elemSymm L 1))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_elemSymm_one_expand, LinearMap.map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, LinearMap.map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_neg, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, C_smul_total, LinearMap.map_smul, dplusStar_C_mul,
    dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three,
    dplusStar_C_elemSymm_four, dplusStar_C_elemSymm_five, dplusStar_C_elemSymm_six,
    dplusStar_C_elemSymm_seven, dplusStar_C_elemSymm_eight]
  simp only [starLetter, C_smul_total, smul_eq_scal_mul, scal, MvPolynomial.C_add,
    MvPolynomial.C_sub, MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1,
    MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `z_1(y_1^8 C(1))`. -/
theorem zopOneStar_one_auxVar_pow_eight_mul_C_one (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 8 * MvPolynomial.C ((1 : Lambda L)))
      = q • (
          (-u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (-(u ^ 3)) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
        + (-(u ^ 5)) • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 3))
        + (u ^ 6) • ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C (elemSymm L 2))
        + (-(u ^ 7)) • ((auxVar 1 : Total L) ^ 7 * MvPolynomial.C (elemSymm L 1))
        + (u ^ 8) • ((auxVar 1 : Total L) ^ 8 * MvPolynomial.C ((1 : Lambda L)))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar_one_auxVar_pow_mul_C]
  refine div_one_sub_smul_eq_smul h1q ?_
  simp only [dplusStar_C_one, map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, map_smul,
    bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_two_one,
    bop_three_one, bop_four_one, bop_five_one, bop_six_one, bop_seven_one,
    bop_eight_one,
    bop_three_elemSymm_one, bop_three_elemSymm_two, bop_three_elemSymm_three,
    bop_three_elemSymm_four, bop_three_elemSymm_five, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_five_elemSymm_one, bop_five_elemSymm_two, bop_five_elemSymm_three,
    bop_six_elemSymm_one, bop_six_elemSymm_two, bop_seven_elemSymm_one]
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
