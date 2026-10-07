/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepOnePartZOneWeightEight

/-! # The stage word at `[3]`, and the inner value `w_2`

The one-part stage word `G_3 = Z^{(1)}_{2,3}(G_2)`, written out, and the vectors on the way to it:
`z_1(G_2)`, `y_1^2z_1(G_2)`, the inner value `w_2 = HJO.Mellit.onePartInnerValue q u 2` read off
the second, and the outer `z_1(y_1^2z_1(G_2))`. Each `z_1` is applied monomialwise through the
values of `HJO/Shuffle/SweepOnePartZOneWeightSix.lean` and
`HJO/Shuffle/SweepOnePartZOneWeightEight.lean`. The route and the genericity are described in
`HJO/Shuffle/SweepOnePartStageTwoLetter.lean`, which reads `V_3` off `G_3`.

## References

The objects involved are `HJO.Sweep.zop`, `HJO.Mellit.replicatedLetter`, `HJO.Mellit.stage`,
`HJO.Sym.Bop`, `HJO.Sweep.dplusStar`.
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

namespace HJO.Mellit

open HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **`z_1(G_2)`**: the eleven monomials of `HJO.Mellit.stageWordTotal_two_three_two_eq`, each
through its own `HJO.Sweep.zopOneStar_one_auxVar_*_mul_C_*` value, assembled. Eighteen monomials
over the `y_1`-degrees `1` to `6`, every coefficient divisible by `q^2u^2` — the `q` of the letter
against the `qu` of `G_2` and the `u` of the seed. Homogeneous of total weight `6`. -/
theorem zopOneStar_one_stageWordTotal_two_three_two (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    zopOneStar q u 1 (stageWordTotal q u 2 3 [2] : Total L)
      = (q ^ 2 * u ^ 2) • (
          (-(q ^ 7) - q ^ 6 * u - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5
            - q * u ^ 6 - u ^ 7 + q ^ 6 + u ^ 6 + q ^ 5 + q ^ 4 * u + q * u ^ 4 + u ^ 5
            + 2 * q ^ 3 * u + 3 * q ^ 2 * u ^ 2 + 2 * q * u ^ 3 - q ^ 3 - q ^ 2 * u - q * u ^ 2
            - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2 + q + u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 5))
        + (-(q ^ 6) - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4 - q * u ^ 5
            - u ^ 6 - q ^ 4 * u - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3 - q * u ^ 4 + q ^ 4
            - q ^ 2 * u ^ 2 + u ^ 4 + q ^ 3 + 3 * q ^ 2 * u + 3 * q * u ^ 2 + u ^ 3 - q - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(q ^ 5) - q ^ 4 * u - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3 - q * u ^ 4 - u ^ 5 - q ^ 3 * u
            - q ^ 2 * u ^ 2 - q * u ^ 3 + q ^ 3 + u ^ 3 + 2 * q ^ 2 + 4 * q * u + 2 * u ^ 2
            - 2 * q - 2 * u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (-(q ^ 4) - q ^ 3 * u - q ^ 2 * u ^ 2 - q * u ^ 3 - u ^ 4 - q ^ 2 * u - q * u ^ 2 + q
            + u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (-(q ^ 3) - q ^ 2 * u - q * u ^ 2 - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2 + 2 * q + 2 * u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (-q - u)
              • ((auxVar 1 : Total L) ^ 1
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))))
        + (u ^ 8 + q * u ^ 6 + q ^ 2 * u ^ 4 + q * u ^ 5 - u ^ 6 + q ^ 4 * u + 2 * q ^ 3 * u ^ 2
            + 2 * q ^ 2 * u ^ 3 - u ^ 5 - q ^ 3 * u - 2 * q ^ 2 * u ^ 2 - 3 * q * u ^ 3
            - q ^ 2 * u + u ^ 3 + q * u)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 4))
        + (u ^ 7 + q * u ^ 5 + u ^ 6 + q ^ 2 * u ^ 3 + 2 * q * u ^ 4 + u ^ 5 + q ^ 3 * u
            + 2 * q ^ 2 * u ^ 2 + 2 * q * u ^ 3 - 2 * u ^ 4 - 2 * q * u ^ 2 - 2 * u ^ 3 - q * u
            + u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (u ^ 6 + q * u ^ 4 + q ^ 2 * u ^ 2 + q * u ^ 3 + q ^ 2 * u - u ^ 3 - q * u)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
        + (u ^ 5 + q * u ^ 3 + 2 * u ^ 4 + 2 * q * u ^ 2 + 2 * u ^ 3 + q * u - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))))
        + (-(u ^ 9) - q * u ^ 6 - q * u ^ 5 - q ^ 2 * u ^ 3 - q * u ^ 4 + u ^ 5 + 2 * q * u ^ 3
            + u ^ 4 - u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 3))
        + (-(u ^ 8) - 2 * u ^ 7 - q * u ^ 5 - u ^ 6 - 2 * q * u ^ 4 - u ^ 5 - 2 * q * u ^ 3
            + 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (-(u ^ 6) - u ^ 5 - u ^ 4 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
        + (u ^ 10 + u ^ 8 + q * u ^ 6 + q * u ^ 5 - u ^ 5)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2))
        + (u ^ 9 + u ^ 8 + 2 * u ^ 7 + u ^ 6 + u ^ 5)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (-(u ^ 11) - u ^ 10 - u ^ 9 - u ^ 8)
              • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1))
        + (u ^ 12) • ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C ((1 : Lambda L)))
      ) := by
  rw [stageWordTotal_two_three_two_eq hq0 hu0 hq1]
  simp only [map_add, map_smul,
    zopOneStar_one_auxVar_sq_mul_C_elemSymm_four hq1,
    zopOneStar_one_auxVar_sq_mul_C_elemSymm_one_mul_three hq1,
    zopOneStar_one_auxVar_sq_mul_C_elemSymm_two_sq hq1,
    zopOneStar_one_auxVar_sq_mul_C_elemSymm_one_sq_mul_two hq1,
    zopOneStar_one_auxVar_cube_mul_C_elemSymm_three hq1,
    zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_mul_two hq1,
    zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_cube hq1,
    zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_two hq1,
    zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_one_sq hq1,
    zopOneStar_one_auxVar_pow_five_mul_C_elemSymm_one hq1,
    zopOneStar_one_auxVar_pow_six_mul_C_one hq1]
  match_scalars <;> grobner

/-- **`y_1^2z_1(G_2)`**, the argument of the outer `z_1` and the vector
`HJO.Mellit.onePartInnerValue` projects: the same eighteen monomials two `y_1`-degrees up, which
is where `HJO.Sweep.auxVar_sq_mul_zopOneStar_one_mem_piece` keeps them inside `V_1`. -/
theorem auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_two (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 (stageWordTotal q u 2 3 [2]) : Total L)
      = (q ^ 2 * u ^ 2) • (
          (-(q ^ 7) - q ^ 6 * u - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5
            - q * u ^ 6 - u ^ 7 + q ^ 6 + u ^ 6 + q ^ 5 + q ^ 4 * u + q * u ^ 4 + u ^ 5
            + 2 * q ^ 3 * u + 3 * q ^ 2 * u ^ 2 + 2 * q * u ^ 3 - q ^ 3 - q ^ 2 * u - q * u ^ 2
            - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2 + q + u)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (-(q ^ 6) - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4 - q * u ^ 5
            - u ^ 6 - q ^ 4 * u - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3 - q * u ^ 4 + q ^ 4
            - q ^ 2 * u ^ 2 + u ^ 4 + q ^ 3 + 3 * q ^ 2 * u + 3 * q * u ^ 2 + u ^ 3 - q - u)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(q ^ 5) - q ^ 4 * u - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3 - q * u ^ 4 - u ^ 5 - q ^ 3 * u
            - q ^ 2 * u ^ 2 - q * u ^ 3 + q ^ 3 + u ^ 3 + 2 * q ^ 2 + 4 * q * u + 2 * u ^ 2
            - 2 * q - 2 * u)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (-(q ^ 4) - q ^ 3 * u - q ^ 2 * u ^ 2 - q * u ^ 3 - u ^ 4 - q ^ 2 * u - q * u ^ 2 + q
            + u)
              • ((auxVar 1 : Total L) ^ 3
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (-(q ^ 3) - q ^ 2 * u - q * u ^ 2 - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2 + 2 * q + 2 * u)
              • ((auxVar 1 : Total L) ^ 3
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (-q - u)
              • ((auxVar 1 : Total L) ^ 3
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))))
        + (u ^ 8 + q * u ^ 6 + q ^ 2 * u ^ 4 + q * u ^ 5 - u ^ 6 + q ^ 4 * u + 2 * q ^ 3 * u ^ 2
            + 2 * q ^ 2 * u ^ 3 - u ^ 5 - q ^ 3 * u - 2 * q ^ 2 * u ^ 2 - 3 * q * u ^ 3
            - q ^ 2 * u + u ^ 3 + q * u)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
        + (u ^ 7 + q * u ^ 5 + u ^ 6 + q ^ 2 * u ^ 3 + 2 * q * u ^ 4 + u ^ 5 + q ^ 3 * u
            + 2 * q ^ 2 * u ^ 2 + 2 * q * u ^ 3 - 2 * u ^ 4 - 2 * q * u ^ 2 - 2 * u ^ 3 - q * u
            + u ^ 2) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (u ^ 6 + q * u ^ 4 + q ^ 2 * u ^ 2 + q * u ^ 3 + q ^ 2 * u - u ^ 3 - q * u)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
        + (u ^ 5 + q * u ^ 3 + 2 * u ^ 4 + 2 * q * u ^ 2 + 2 * u ^ 3 + q * u - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 4
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (u ^ 2)
              • ((auxVar 1 : Total L) ^ 4
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))))
        + (-(u ^ 9) - q * u ^ 6 - q * u ^ 5 - q ^ 2 * u ^ 3 - q * u ^ 4 + u ^ 5 + 2 * q * u ^ 3
            + u ^ 4 - u ^ 3) • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 3))
        + (-(u ^ 8) - 2 * u ^ 7 - q * u ^ 5 - u ^ 6 - 2 * q * u ^ 4 - u ^ 5 - 2 * q * u ^ 3
            + 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (-(u ^ 6) - u ^ 5 - u ^ 4 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 5
              * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
        + (u ^ 10 + u ^ 8 + q * u ^ 6 + q * u ^ 5 - u ^ 5)
              • ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C (elemSymm L 2))
        + (u ^ 9 + u ^ 8 + 2 * u ^ 7 + u ^ 6 + u ^ 5)
              • ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (-(u ^ 11) - u ^ 10 - u ^ 9 - u ^ 8)
              • ((auxVar 1 : Total L) ^ 7 * MvPolynomial.C (elemSymm L 1))
        + (u ^ 12) • ((auxVar 1 : Total L) ^ 8 * MvPolynomial.C ((1 : Lambda L)))
      ) := by
  rw [zopOneStar_one_stageWordTotal_two_three_two hq0 hu0 hq1, mul_smul_comm]
  simp only [mul_add, auxVar_pow_mul_smul_auxVar_pow_mul_C, Nat.reduceAdd]
/-- **`w_2 = ct(d_-^{(1)}(y_1^2z_1G_2))`, written out**: the eighteen monomials of
`HJO.Mellit.auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_two`, each through
`HJO.Sym.Bop` at the index read off its `y_1`-degree. Sixteen `e`-monomials of weight eight,
every coefficient divisible by `q^2u^2`. -/
theorem onePartInnerValue_two (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    onePartInnerValue q u 2 = (q ^ 2 * u ^ 2) • (
          (q ^ 12 + q ^ 11 * u + q ^ 10 * u ^ 2 + q ^ 9 * u ^ 3 + q ^ 8 * u ^ 4 + q ^ 7 * u ^ 5
            + q ^ 6 * u ^ 6 + q ^ 5 * u ^ 7 + q ^ 4 * u ^ 8 + q ^ 3 * u ^ 9 + q ^ 2 * u ^ 10
            + q * u ^ 11 + u ^ 12 - q ^ 11 - u ^ 11 - q ^ 10 - q ^ 9 * u - q * u ^ 9 - u ^ 10
            - q ^ 8 * u - q ^ 7 * u ^ 2 - q ^ 2 * u ^ 7 - q * u ^ 8 - 2 * q ^ 7 * u
            - 3 * q ^ 6 * u ^ 2 - 3 * q ^ 5 * u ^ 3 - 2 * q ^ 4 * u ^ 4 - 3 * q ^ 3 * u ^ 5
            - 3 * q ^ 2 * u ^ 6 - 2 * q * u ^ 7 + 2 * q ^ 7 + 2 * q ^ 6 * u - 2 * q ^ 4 * u ^ 3
            - 2 * q ^ 3 * u ^ 4 + 2 * q * u ^ 6 + 2 * u ^ 7 + 2 * q ^ 5 * u + 3 * q ^ 4 * u ^ 2
            + 3 * q ^ 3 * u ^ 3 + 3 * q ^ 2 * u ^ 4 + 2 * q * u ^ 5 + q ^ 4 * u
            + 3 * q ^ 3 * u ^ 2 + 3 * q ^ 2 * u ^ 3 + q * u ^ 4 - q ^ 4 - q ^ 3 * u
            - 2 * q ^ 2 * u ^ 2 - q * u ^ 3 - u ^ 4 - q ^ 3 - 2 * q ^ 2 * u - 2 * q * u ^ 2
            - u ^ 3 + q ^ 2 + q * u + u ^ 2) • elemSymm L 8
        + (q ^ 11 + q ^ 10 * u + q ^ 9 * u ^ 2 + q ^ 8 * u ^ 3 + q ^ 7 * u ^ 4 + q ^ 6 * u ^ 5
            + q ^ 5 * u ^ 6 + q ^ 4 * u ^ 7 + q ^ 3 * u ^ 8 + q ^ 2 * u ^ 9 + q * u ^ 10 + u ^ 11
            + q ^ 9 * u + q ^ 8 * u ^ 2 + q ^ 7 * u ^ 3 + q ^ 6 * u ^ 4 + q ^ 5 * u ^ 5
            + q ^ 4 * u ^ 6 + q ^ 3 * u ^ 7 + q ^ 2 * u ^ 8 + q * u ^ 9 - q ^ 9 + q ^ 7 * u ^ 2
            + q ^ 6 * u ^ 3 + q ^ 5 * u ^ 4 + q ^ 4 * u ^ 5 + q ^ 3 * u ^ 6 + q ^ 2 * u ^ 7
            - u ^ 9 - q ^ 8 - q ^ 7 * u + q ^ 5 * u ^ 3 + q ^ 4 * u ^ 4 + q ^ 3 * u ^ 5
            - q * u ^ 7 - u ^ 8 - 2 * q ^ 7 - 5 * q ^ 6 * u - 5 * q ^ 5 * u ^ 2
            - 4 * q ^ 4 * u ^ 3 - 4 * q ^ 3 * u ^ 4 - 5 * q ^ 2 * u ^ 5 - 5 * q * u ^ 6
            - 2 * u ^ 7 + 2 * q ^ 6 - q ^ 5 * u - 5 * q ^ 4 * u ^ 2 - 6 * q ^ 3 * u ^ 3
            - 5 * q ^ 2 * u ^ 4 - q * u ^ 5 + 2 * u ^ 6 + 2 * q ^ 5 + 4 * q ^ 4 * u
            + 3 * q ^ 3 * u ^ 2 + 3 * q ^ 2 * u ^ 3 + 4 * q * u ^ 4 + 2 * u ^ 5 + q ^ 4
            + 4 * q ^ 3 * u + 7 * q ^ 2 * u ^ 2 + 4 * q * u ^ 3 + u ^ 4 - q ^ 3 - q ^ 2 * u
            - q * u ^ 2 - u ^ 3 - 2 * q ^ 2 - 3 * q * u - 2 * u ^ 2 + q + u)
              • (elemSymm L 1 * elemSymm L 7)
        + (q ^ 10 + q ^ 9 * u + q ^ 8 * u ^ 2 + q ^ 7 * u ^ 3 + q ^ 6 * u ^ 4 + q ^ 5 * u ^ 5
            + q ^ 4 * u ^ 6 + q ^ 3 * u ^ 7 + q ^ 2 * u ^ 8 + q * u ^ 9 + u ^ 10 - q ^ 9 - u ^ 9
            + q ^ 6 * u ^ 2 + q ^ 5 * u ^ 3 + q ^ 4 * u ^ 4 + q ^ 3 * u ^ 5 + q ^ 2 * u ^ 6
            - q ^ 7 - q ^ 6 * u - q ^ 5 * u ^ 2 - q ^ 2 * u ^ 5 - q * u ^ 6 - u ^ 7
            - 2 * q ^ 5 * u - 2 * q ^ 4 * u ^ 2 - 3 * q ^ 3 * u ^ 3 - 2 * q ^ 2 * u ^ 4
            - 2 * q * u ^ 5 + q ^ 5 - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3 + u ^ 5
            + 2 * q ^ 3 * u + 3 * q ^ 2 * u ^ 2 + 2 * q * u ^ 3 + q ^ 3 + q ^ 2 * u + q * u ^ 2
            + u ^ 3 - q ^ 2 - q * u - u ^ 2) • (elemSymm L 2 * elemSymm L 6)
        + (q ^ 9 + q ^ 8 * u + q ^ 7 * u ^ 2 + q ^ 6 * u ^ 3 + q ^ 5 * u ^ 4 + q ^ 4 * u ^ 5
            + q ^ 3 * u ^ 6 + q ^ 2 * u ^ 7 + q * u ^ 8 + u ^ 9 - q ^ 8 - u ^ 8 + q ^ 5 * u ^ 2
            + q ^ 4 * u ^ 3 + q ^ 3 * u ^ 4 + q ^ 2 * u ^ 5 + q ^ 3 * u ^ 3 - 2 * q ^ 5
            - 3 * q ^ 4 * u - 4 * q ^ 3 * u ^ 2 - 4 * q ^ 2 * u ^ 3 - 3 * q * u ^ 4 - 2 * u ^ 5
            + q ^ 4 - q ^ 3 * u - q ^ 2 * u ^ 2 - q * u ^ 3 + u ^ 4 + 2 * q ^ 3 + 3 * q ^ 2 * u
            + 3 * q * u ^ 2 + 2 * u ^ 3 + q * u - q - u) • (elemSymm L 3 * elemSymm L 5)
        + (q ^ 8 + q ^ 7 * u + q ^ 6 * u ^ 2 + q ^ 5 * u ^ 3 + q ^ 4 * u ^ 4 + q ^ 3 * u ^ 5
            + q ^ 2 * u ^ 6 + q * u ^ 7 + u ^ 8 - q ^ 7 - u ^ 7 - q ^ 6 - q ^ 5 * u - q * u ^ 5
            - u ^ 6 - q ^ 4 * u - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3 - q * u ^ 4 + q ^ 4 - q ^ 3 * u
            - 2 * q ^ 2 * u ^ 2 - q * u ^ 3 + u ^ 4 + q ^ 3 + 3 * q ^ 2 * u + 3 * q * u ^ 2
            + u ^ 3 - q ^ 2 - q * u - u ^ 2) • (elemSymm L 4 * elemSymm L 4)
        + (q ^ 9 + q ^ 8 * u + q ^ 7 * u ^ 2 + q ^ 6 * u ^ 3 + q ^ 5 * u ^ 4 + q ^ 4 * u ^ 5
            + q ^ 3 * u ^ 6 + q ^ 2 * u ^ 7 + q * u ^ 8 + u ^ 9 + q ^ 7 * u + q ^ 6 * u ^ 2
            + q ^ 5 * u ^ 3 + q ^ 4 * u ^ 4 + q ^ 3 * u ^ 5 + q ^ 2 * u ^ 6 + q * u ^ 7
            + q ^ 6 * u + 2 * q ^ 5 * u ^ 2 + 2 * q ^ 4 * u ^ 3 + 2 * q ^ 3 * u ^ 4
            + 2 * q ^ 2 * u ^ 5 + q * u ^ 6 - 2 * q ^ 6 - 2 * q ^ 5 * u - q ^ 4 * u ^ 2
            - q ^ 2 * u ^ 4 - 2 * q * u ^ 5 - 2 * u ^ 6 - q ^ 5 - 4 * q ^ 4 * u
            - 5 * q ^ 3 * u ^ 2 - 5 * q ^ 2 * u ^ 3 - 4 * q * u ^ 4 - u ^ 5 + q ^ 4
            - 2 * q ^ 2 * u ^ 2 + u ^ 4 + q ^ 3 + 3 * q ^ 2 * u + 3 * q * u ^ 2 + u ^ 3 + q ^ 2
            + q * u + u ^ 2 - q - u) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6))
        + (q ^ 8 + q ^ 7 * u + q ^ 6 * u ^ 2 + q ^ 5 * u ^ 3 + q ^ 4 * u ^ 4 + q ^ 3 * u ^ 5
            + q ^ 2 * u ^ 6 + q * u ^ 7 + u ^ 8 + q ^ 7 + 2 * q ^ 6 * u + 2 * q ^ 5 * u ^ 2
            + 2 * q ^ 4 * u ^ 3 + 2 * q ^ 3 * u ^ 4 + 2 * q ^ 2 * u ^ 5 + 2 * q * u ^ 6 + u ^ 7
            - 2 * q ^ 6 + q ^ 4 * u ^ 2 + q ^ 3 * u ^ 3 + q ^ 2 * u ^ 4 - 2 * u ^ 6 - q ^ 5
            - 2 * q ^ 4 * u - 2 * q * u ^ 4 - u ^ 5 - 3 * q ^ 3 * u - 6 * q ^ 2 * u ^ 2
            - 3 * q * u ^ 3 - q ^ 3 - q ^ 2 * u - q * u ^ 2 - u ^ 3 + 3 * q ^ 2 + 4 * q * u
            + 3 * u ^ 2 - q - u) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5))
        + (q ^ 7 + q ^ 6 * u + q ^ 5 * u ^ 2 + q ^ 4 * u ^ 3 + q ^ 3 * u ^ 4 + q ^ 2 * u ^ 5
            + q * u ^ 6 + u ^ 7 + q ^ 6 + 2 * q ^ 5 * u + 2 * q ^ 4 * u ^ 2 + 2 * q ^ 3 * u ^ 3
            + 2 * q ^ 2 * u ^ 4 + 2 * q * u ^ 5 + u ^ 6 + 2 * q ^ 4 * u + 3 * q ^ 3 * u ^ 2
            + 3 * q ^ 2 * u ^ 3 + 2 * q * u ^ 4 - 4 * q ^ 4 - 3 * q ^ 3 * u - 2 * q ^ 2 * u ^ 2
            - 3 * q * u ^ 3 - 4 * u ^ 4 - q ^ 3 - 6 * q ^ 2 * u - 6 * q * u ^ 2 - u ^ 3
            + 3 * q ^ 2 + 4 * q * u + 3 * u ^ 2) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))
        + (q ^ 6 + q ^ 5 * u + q ^ 4 * u ^ 2 + q ^ 3 * u ^ 3 + q ^ 2 * u ^ 4 + q * u ^ 5 + u ^ 6
            - q ^ 5 - u ^ 5 + q ^ 2 * u ^ 2 - q ^ 3 - 2 * q ^ 2 * u - 2 * q * u ^ 2 - u ^ 3
            + q ^ 2 + q * u + u ^ 2) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4))
        + (q ^ 5 + q ^ 4 * u + q ^ 3 * u ^ 2 + q ^ 2 * u ^ 3 + q * u ^ 4 + u ^ 5 + q ^ 3 * u
            + q ^ 2 * u ^ 2 + q * u ^ 3 - q ^ 3 - u ^ 3 - 2 * q ^ 2 - 4 * q * u - 2 * u ^ 2
            + 2 * q + 2 * u) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3))
        + (q ^ 6 + q ^ 5 * u + q ^ 4 * u ^ 2 + q ^ 3 * u ^ 3 + q ^ 2 * u ^ 4 + q * u ^ 5 + u ^ 6
            + q ^ 4 * u + q ^ 3 * u ^ 2 + q ^ 2 * u ^ 3 + q * u ^ 4 - q ^ 4 - q ^ 3 * u
            - q * u ^ 3 - u ^ 4 - q ^ 2 * u - q * u ^ 2 - q ^ 2 - q * u - u ^ 2 + q + u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (q ^ 5 + q ^ 4 * u + q ^ 3 * u ^ 2 + q ^ 2 * u ^ 3 + q * u ^ 4 + u ^ 5 + q ^ 4
            + 2 * q ^ 3 * u + 2 * q ^ 2 * u ^ 2 + 2 * q * u ^ 3 + u ^ 4 + q ^ 2 * u + q * u ^ 2
            - 4 * q ^ 2 - 5 * q * u - 4 * u ^ 2 + 2 * q + 2 * u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (q ^ 4 + q ^ 3 * u + q ^ 2 * u ^ 2 + q * u ^ 3 + u ^ 4 + q ^ 2 * u + q * u ^ 2 - q - u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3)))
        + (q ^ 3 + q ^ 2 * u + q * u ^ 2 + u ^ 3 + q ^ 2 + 2 * q * u + u ^ 2 - 2 * q - 2 * u)
              • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3)))
        + (q ^ 2 + q * u + u ^ 2 - q - u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))))
        + (q + u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))))
      ) := by
  rw [onePartInnerValue, auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_two
    hq0 hu0 hq1]
  simp only [map_smul, constantCoeff_smul, map_add, dminus_one_auxVar_pow_mul_C,
    MvPolynomial.constantCoeff_C, bop_elemSymm_one_mul, bop_elemSymm_two_mul,
    bop_elemSymm_three_mul, bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_four_elemSymm_one, bop_four_elemSymm_two,
    bop_four_elemSymm_three, bop_four_elemSymm_four, bop_five_elemSymm_one,
    bop_five_elemSymm_two, bop_five_elemSymm_three, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_seven_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- **The outer `z_1`**: `z_1(y_1^2z_1G_2)`, the eighteen monomials of
`HJO.Mellit.auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_two` each through its own
`HJO.Sweep.zopOneStar_one_auxVar_*_mul_C_*` value. Forty-two monomials over the
`y_1`-degrees `1` to `8`, the common factor `q^3u^3` being the three `q`'s of the three
`z_1` letters and the `u` of the seed. Homogeneous of total weight `8`. -/
theorem zopOneStar_one_auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_two
    (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    zopOneStar q u 1
        ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 (stageWordTotal q u 2 3 [2]))
      = (q ^ 3 * u ^ 3) • (
          (-(q ^ 12) - q ^ 11 * u - q ^ 10 * u ^ 2 - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5
            - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7 - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10
            - q * u ^ 11 - u ^ 12 + q ^ 11 + u ^ 11 + q ^ 10 + q ^ 9 * u + q * u ^ 9 + u ^ 10
            + q ^ 8 * u + q ^ 7 * u ^ 2 + q ^ 2 * u ^ 7 + q * u ^ 8 + 2 * q ^ 7 * u
            + 3 * q ^ 6 * u ^ 2 + 3 * q ^ 5 * u ^ 3 + 2 * q ^ 4 * u ^ 4 + 3 * q ^ 3 * u ^ 5
            + 3 * q ^ 2 * u ^ 6 + 2 * q * u ^ 7 - 2 * q ^ 7 - 2 * q ^ 6 * u + 2 * q ^ 4 * u ^ 3
            + 2 * q ^ 3 * u ^ 4 - 2 * q * u ^ 6 - 2 * u ^ 7 - 2 * q ^ 5 * u - 3 * q ^ 4 * u ^ 2
            - 3 * q ^ 3 * u ^ 3 - 3 * q ^ 2 * u ^ 4 - 2 * q * u ^ 5 - q ^ 4 * u
            - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3 - q * u ^ 4 + q ^ 4 + q ^ 3 * u
            + 2 * q ^ 2 * u ^ 2 + q * u ^ 3 + u ^ 4 + q ^ 3 + 2 * q ^ 2 * u + 2 * q * u ^ 2
            + u ^ 3 - q ^ 2 - q * u - u ^ 2)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 7))
        + (-(q ^ 11) - q ^ 10 * u - q ^ 9 * u ^ 2 - q ^ 8 * u ^ 3 - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5
            - q ^ 5 * u ^ 6 - q ^ 4 * u ^ 7 - q ^ 3 * u ^ 8 - q ^ 2 * u ^ 9 - q * u ^ 10 - u ^ 11
            - q ^ 9 * u - q ^ 8 * u ^ 2 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4 - q ^ 5 * u ^ 5
            - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 - q * u ^ 9 + q ^ 9 - q ^ 7 * u ^ 2
            - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5 - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7
            + u ^ 9 + q ^ 8 + q ^ 7 * u - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5
            + q * u ^ 7 + u ^ 8 + 2 * q ^ 7 + 5 * q ^ 6 * u + 5 * q ^ 5 * u ^ 2
            + 4 * q ^ 4 * u ^ 3 + 4 * q ^ 3 * u ^ 4 + 5 * q ^ 2 * u ^ 5 + 5 * q * u ^ 6
            + 2 * u ^ 7 - 2 * q ^ 6 + q ^ 5 * u + 5 * q ^ 4 * u ^ 2 + 6 * q ^ 3 * u ^ 3
            + 5 * q ^ 2 * u ^ 4 + q * u ^ 5 - 2 * u ^ 6 - 2 * q ^ 5 - 4 * q ^ 4 * u
            - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3 - 4 * q * u ^ 4 - 2 * u ^ 5 - q ^ 4
            - 4 * q ^ 3 * u - 7 * q ^ 2 * u ^ 2 - 4 * q * u ^ 3 - u ^ 4 + q ^ 3 + q ^ 2 * u
            + q * u ^ 2 + u ^ 3 + 2 * q ^ 2 + 3 * q * u + 2 * u ^ 2 - q - u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (-(q ^ 10) - q ^ 9 * u - q ^ 8 * u ^ 2 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4 - q ^ 5 * u ^ 5
            - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 - q * u ^ 9 - u ^ 10 + q ^ 9 + u ^ 9
            - q ^ 6 * u ^ 2 - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5 - q ^ 2 * u ^ 6
            - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 + q ^ 6 + 2 * q ^ 5 * u + 2 * q ^ 4 * u ^ 2
            + 3 * q ^ 3 * u ^ 3 + 2 * q ^ 2 * u ^ 4 + 2 * q * u ^ 5 + u ^ 6 + q ^ 4 * u
            + 2 * q ^ 3 * u ^ 2 + 2 * q ^ 2 * u ^ 3 + q * u ^ 4 - 2 * q ^ 3 - 2 * q ^ 2 * u
            - 2 * q * u ^ 2 - 2 * u ^ 3 - q * u + q + u)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (-(q ^ 9) - q ^ 8 * u - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5
            - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7 - q * u ^ 8 - u ^ 9 - q ^ 7 * u - q ^ 6 * u ^ 2
            - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5 - q ^ 2 * u ^ 6 - q * u ^ 7
            + 2 * q ^ 7 + q ^ 6 * u + q * u ^ 6 + 2 * u ^ 7 + q ^ 5 * u - q ^ 3 * u ^ 3
            + q * u ^ 5 + q ^ 5 + 3 * q ^ 4 * u + 5 * q ^ 3 * u ^ 2 + 5 * q ^ 2 * u ^ 3
            + 3 * q * u ^ 4 + u ^ 5 - 2 * q ^ 4 - 2 * u ^ 4 - 2 * q ^ 3 - 5 * q ^ 2 * u
            - 5 * q * u ^ 2 - 2 * u ^ 3 + 2 * q ^ 2 + 2 * q * u + 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 3 * elemSymm L 4))
        + (-(q ^ 9) - q ^ 8 * u - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5
            - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7 - q * u ^ 8 - u ^ 9 - q ^ 7 * u - q ^ 6 * u ^ 2
            - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5 - q ^ 2 * u ^ 6 - q * u ^ 7
            - q ^ 6 * u - 2 * q ^ 5 * u ^ 2 - 2 * q ^ 4 * u ^ 3 - 2 * q ^ 3 * u ^ 4
            - 2 * q ^ 2 * u ^ 5 - q * u ^ 6 + 2 * q ^ 6 + 2 * q ^ 5 * u + q ^ 4 * u ^ 2
            + q ^ 2 * u ^ 4 + 2 * q * u ^ 5 + 2 * u ^ 6 + q ^ 5 + 4 * q ^ 4 * u
            + 5 * q ^ 3 * u ^ 2 + 5 * q ^ 2 * u ^ 3 + 4 * q * u ^ 4 + u ^ 5 - q ^ 4
            + 2 * q ^ 2 * u ^ 2 - u ^ 4 - q ^ 3 - 3 * q ^ 2 * u - 3 * q * u ^ 2 - u ^ 3 - q ^ 2
            - q * u - u ^ 2 + q + u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (-(q ^ 8) - q ^ 7 * u - q ^ 6 * u ^ 2 - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5
            - q ^ 2 * u ^ 6 - q * u ^ 7 - u ^ 8 - q ^ 7 - 2 * q ^ 6 * u - 2 * q ^ 5 * u ^ 2
            - 2 * q ^ 4 * u ^ 3 - 2 * q ^ 3 * u ^ 4 - 2 * q ^ 2 * u ^ 5 - 2 * q * u ^ 6 - u ^ 7
            + q ^ 6 - q ^ 5 * u - 2 * q ^ 4 * u ^ 2 - 2 * q ^ 3 * u ^ 3 - 2 * q ^ 2 * u ^ 4
            - q * u ^ 5 + u ^ 6 + q ^ 5 + q ^ 4 * u - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3 + q * u ^ 4
            + u ^ 5 + q ^ 4 + 3 * q ^ 3 * u + 5 * q ^ 2 * u ^ 2 + 3 * q * u ^ 3 + u ^ 4
            + 2 * q ^ 3 + 4 * q ^ 2 * u + 4 * q * u ^ 2 + 2 * u ^ 3 - 3 * q ^ 2 - 4 * q * u
            - 3 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (-(q ^ 7) - q ^ 6 * u - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5
            - q * u ^ 6 - u ^ 7 - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4
            - q * u ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3 - q * u ^ 4
            + 3 * q ^ 4 + 3 * q ^ 3 * u + 3 * q ^ 2 * u ^ 2 + 3 * q * u ^ 3 + 3 * u ^ 4
            + 3 * q ^ 2 * u + 3 * q * u ^ 2 - 3 * q ^ 2 - 4 * q * u - 3 * u ^ 2 + q + u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3)))
        + (-(q ^ 6) - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4 - q * u ^ 5
            - u ^ 6 - q ^ 4 * u - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3 - q * u ^ 4 - q ^ 3 * u
            - 2 * q ^ 2 * u ^ 2 - q * u ^ 3 + 2 * q ^ 3 + 2 * q ^ 2 * u + 2 * q * u ^ 2
            + 2 * u ^ 3 + q ^ 2 + 3 * q * u + u ^ 2 - 2 * q - 2 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3)))
        + (-(q ^ 6) - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4 - q * u ^ 5
            - u ^ 6 - q ^ 4 * u - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3 - q * u ^ 4 + q ^ 4 + q ^ 3 * u
            + q * u ^ 3 + u ^ 4 + q ^ 2 * u + q * u ^ 2 + q ^ 2 + q * u + u ^ 2 - q - u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))))
        + (-(q ^ 5) - q ^ 4 * u - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3 - q * u ^ 4 - u ^ 5 - 2 * q ^ 4
            - 3 * q ^ 3 * u - 3 * q ^ 2 * u ^ 2 - 3 * q * u ^ 3 - 2 * u ^ 4 - 2 * q ^ 2 * u
            - 2 * q * u ^ 2 + 4 * q ^ 2 + 5 * q * u + 4 * u ^ 2 - q - u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))))
        + (-(q ^ 3) - q ^ 2 * u - q * u ^ 2 - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2 + 2 * q + 2 * u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))))
        + (-(q ^ 2) - q * u - u ^ 2 + q + u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))))
        + (-q - u)
              • ((auxVar 1 : Total L) ^ 1
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))))
        + (u ^ 13 + q * u ^ 11 + q ^ 2 * u ^ 9 + q * u ^ 10 - u ^ 11 + q ^ 3 * u ^ 7
            + q ^ 2 * u ^ 8 - u ^ 10 + q ^ 8 * u + 2 * q ^ 7 * u ^ 2 + 2 * q ^ 6 * u ^ 3
            + 2 * q ^ 5 * u ^ 4 + 3 * q ^ 4 * u ^ 5 + 3 * q ^ 3 * u ^ 6 + 2 * q ^ 2 * u ^ 7
            - q * u ^ 8 - u ^ 9 - 2 * q ^ 7 * u - 2 * q ^ 6 * u ^ 2 - q ^ 3 * u ^ 5
            - 4 * q ^ 2 * u ^ 6 - 5 * q * u ^ 7 - 3 * q ^ 5 * u ^ 2 - 5 * q ^ 4 * u ^ 3
            - 6 * q ^ 3 * u ^ 4 - 6 * q ^ 2 * u ^ 5 - q * u ^ 6 + 2 * u ^ 7 + q ^ 5 * u
            + q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 + 2 * q ^ 2 * u ^ 4 + 4 * q * u ^ 5 + 2 * u ^ 6
            + q ^ 4 * u + 4 * q ^ 3 * u ^ 2 + 6 * q ^ 2 * u ^ 3 + 4 * q * u ^ 4 - q * u ^ 3
            - 2 * u ^ 4 - 2 * q ^ 2 * u - 3 * q * u ^ 2 - u ^ 3 + q * u + u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 6))
        + (u ^ 12 + q * u ^ 10 + u ^ 11 + q ^ 2 * u ^ 8 + 2 * q * u ^ 9 + q ^ 3 * u ^ 6
            + 2 * q ^ 2 * u ^ 7 + 2 * q * u ^ 8 - u ^ 9 + 2 * q ^ 7 * u + 3 * q ^ 6 * u ^ 2
            + 3 * q ^ 5 * u ^ 3 + 4 * q ^ 4 * u ^ 4 + 5 * q ^ 3 * u ^ 5 + 5 * q ^ 2 * u ^ 6
            + q * u ^ 7 - 2 * u ^ 8 - 2 * q ^ 6 * u + q ^ 5 * u ^ 2 + 3 * q ^ 4 * u ^ 3
            + 3 * q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5 - 6 * q * u ^ 6 - 3 * u ^ 7 - 2 * q ^ 5 * u
            - 7 * q ^ 4 * u ^ 2 - 8 * q ^ 3 * u ^ 3 - 11 * q ^ 2 * u ^ 4 - 7 * q * u ^ 5
            - 3 * q ^ 3 * u ^ 2 - 4 * q ^ 2 * u ^ 3 + q * u ^ 4 + 3 * u ^ 5 + 2 * q ^ 3 * u
            + 6 * q ^ 2 * u ^ 2 + 6 * q * u ^ 3 + 3 * u ^ 4 + 2 * q ^ 2 * u + 2 * q * u ^ 2
            - 2 * q * u - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (u ^ 11 + q * u ^ 9 + q ^ 2 * u ^ 7 + q * u ^ 8 + u ^ 9 + q ^ 3 * u ^ 5 + q ^ 2 * u ^ 6
            + 2 * q * u ^ 7 - u ^ 8 + q ^ 6 * u + 2 * q ^ 5 * u ^ 2 + 3 * q ^ 4 * u ^ 3
            + 3 * q ^ 3 * u ^ 4 + 4 * q ^ 2 * u ^ 5 + q * u ^ 6 - 2 * u ^ 7 - 2 * q ^ 5 * u
            - q ^ 4 * u ^ 2 - 2 * q ^ 2 * u ^ 4 - 5 * q * u ^ 5 - 2 * u ^ 6 + q ^ 4 * u
            - 2 * q ^ 3 * u ^ 2 - 4 * q ^ 2 * u ^ 3 - 3 * q * u ^ 4 + u ^ 5 - q ^ 3 * u
            - 2 * q ^ 2 * u ^ 2 + 2 * u ^ 4 + 2 * q ^ 2 * u + 4 * q * u ^ 2 + u ^ 3 - q * u
            - u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 4))
        + (u ^ 10 + q * u ^ 8 + q ^ 2 * u ^ 6 + q * u ^ 7 - u ^ 8 + q ^ 3 * u ^ 4 + q ^ 2 * u ^ 5
            + q ^ 5 * u + 2 * q ^ 4 * u ^ 2 + 2 * q ^ 3 * u ^ 3 + q ^ 2 * u ^ 4 - u ^ 6
            - 2 * q ^ 4 * u - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3 - 4 * q * u ^ 4 - u ^ 5
            - q ^ 2 * u ^ 2 + 2 * u ^ 4 + 2 * q ^ 2 * u + 3 * q * u ^ 2 + u ^ 3 - q * u - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3 * elemSymm L 3))
        + (u ^ 10 + q * u ^ 8 + u ^ 9 + q ^ 2 * u ^ 6 + 2 * q * u ^ 7 + u ^ 8 + q ^ 6 * u
            + q ^ 5 * u ^ 2 + q ^ 4 * u ^ 3 + 2 * q ^ 3 * u ^ 4 + 3 * q ^ 2 * u ^ 5
            + 3 * q * u ^ 6 + q ^ 5 * u + 4 * q ^ 4 * u ^ 2 + 5 * q ^ 3 * u ^ 3
            + 5 * q ^ 2 * u ^ 4 + q * u ^ 5 - 2 * u ^ 6 - 2 * q ^ 4 * u - 2 * q ^ 3 * u ^ 2
            - 3 * q ^ 2 * u ^ 3 - 5 * q * u ^ 4 - 3 * u ^ 5 - q ^ 3 * u - 5 * q ^ 2 * u ^ 2
            - 4 * q * u ^ 3 - u ^ 4 - q ^ 2 * u + u ^ 3 + 2 * q * u + 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))
        + (u ^ 9 + q * u ^ 7 + 3 * u ^ 8 + q ^ 2 * u ^ 5 + 4 * q * u ^ 6 + u ^ 7 + q ^ 5 * u
            + q ^ 4 * u ^ 2 + 2 * q ^ 3 * u ^ 3 + 5 * q ^ 2 * u ^ 4 + 5 * q * u ^ 5 + u ^ 6
            + q ^ 4 * u + 5 * q ^ 3 * u ^ 2 + 5 * q ^ 2 * u ^ 3 + 3 * q * u ^ 4 - 3 * u ^ 5
            - q ^ 3 * u - 2 * q ^ 2 * u ^ 2 - 5 * q * u ^ 3 - 6 * u ^ 4 - 5 * q ^ 2 * u
            - 8 * q * u ^ 2 - u ^ 3 + 4 * q * u + 4 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))
        + (u ^ 7 + q * u ^ 5 + q ^ 2 * u ^ 3 + q * u ^ 4 + q ^ 2 * u ^ 2 - u ^ 4 - q * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2)))
        + (u ^ 7 + q * u ^ 5 + u ^ 6 + q ^ 4 * u + q ^ 3 * u ^ 2 + 2 * q ^ 2 * u ^ 3
            + 2 * q * u ^ 4 + u ^ 5 + 2 * q ^ 2 * u ^ 2 + q * u ^ 3 + q ^ 2 * u - u ^ 3
            - 2 * q * u - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))))
        + (u ^ 6 + q * u ^ 4 + 2 * u ^ 5 + q ^ 3 * u + q ^ 2 * u ^ 2 + 3 * q * u ^ 3 + 3 * u ^ 4
            + q ^ 2 * u + 3 * q * u ^ 2 - u ^ 3 - 2 * q * u - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))))
        + (u ^ 3 + q * u + u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))))
        + (-(u ^ 14) - q * u ^ 11 - q * u ^ 10 + u ^ 11 - q ^ 2 * u ^ 8 - q * u ^ 9 + u ^ 10
            - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5 - 2 * q ^ 3 * u ^ 6
            - 3 * q ^ 2 * u ^ 7 + q ^ 6 * u ^ 2 - q ^ 5 * u ^ 3 - 2 * q ^ 4 * u ^ 4
            - 3 * q ^ 3 * u ^ 5 + 4 * q * u ^ 7 + u ^ 8 + q ^ 5 * u ^ 2 + 3 * q ^ 4 * u ^ 3
            + 4 * q ^ 3 * u ^ 4 + 6 * q ^ 2 * u ^ 5 + 3 * q * u ^ 6 - u ^ 7 + 2 * q ^ 3 * u ^ 3
            + 2 * q ^ 2 * u ^ 4 - q * u ^ 5 - u ^ 6 - q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3
            - 3 * q * u ^ 4 - u ^ 5 - q ^ 2 * u ^ 2 - q * u ^ 3 + q * u ^ 2 + u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 5))
        + (-(u ^ 13) - u ^ 12 - q * u ^ 10 - u ^ 11 - 2 * q * u ^ 9 - u ^ 10 - q ^ 2 * u ^ 7
            - 3 * q * u ^ 8 + 2 * u ^ 9 - q ^ 6 * u ^ 2 - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4
            - 2 * q ^ 3 * u ^ 5 - 5 * q ^ 2 * u ^ 6 - 3 * q * u ^ 7 + 2 * u ^ 8
            - 3 * q ^ 4 * u ^ 3 - 6 * q ^ 3 * u ^ 4 - 4 * q ^ 2 * u ^ 5 + 3 * q * u ^ 6
            + 3 * u ^ 7 + q ^ 4 * u ^ 2 + 2 * q ^ 3 * u ^ 3 + 5 * q ^ 2 * u ^ 4 + 6 * q * u ^ 5
            + q ^ 3 * u ^ 2 + 5 * q ^ 2 * u ^ 3 + 3 * q * u ^ 4 - u ^ 5 - 2 * q * u ^ 3 - u ^ 4
            - q * u ^ 2 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(u ^ 12) - u ^ 11 - q * u ^ 9 - u ^ 10 - 2 * q * u ^ 8 + u ^ 9 - q ^ 2 * u ^ 6
            - 3 * q * u ^ 7 - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - 3 * q ^ 2 * u ^ 5
            - q * u ^ 6 + 2 * u ^ 7 - 2 * q ^ 3 * u ^ 3 - 2 * q ^ 2 * u ^ 4 + 2 * q * u ^ 5
            + u ^ 6 + q ^ 3 * u ^ 2 + 2 * q ^ 2 * u ^ 3 + 2 * q * u ^ 4 + 2 * q ^ 2 * u ^ 2
            + 3 * q * u ^ 3 + u ^ 4 - 2 * q * u ^ 2 - 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (-(u ^ 11) - u ^ 10 - q * u ^ 8 - 3 * u ^ 9 - 2 * q * u ^ 7 - u ^ 8 - 2 * q ^ 2 * u ^ 5
            - 4 * q * u ^ 6 - u ^ 7 - q ^ 4 * u ^ 2 - 2 * q ^ 3 * u ^ 3 - 4 * q ^ 2 * u ^ 4
            - 3 * q * u ^ 5 + 3 * u ^ 6 - 2 * q ^ 2 * u ^ 3 + q * u ^ 4 + 3 * u ^ 5
            + 2 * q * u ^ 3 + q * u ^ 2 + u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (-(u ^ 10) - 2 * u ^ 9 - q * u ^ 7 - 2 * u ^ 8 - 3 * q * u ^ 6 - u ^ 7 - q ^ 2 * u ^ 4
            - 3 * q * u ^ 5 - q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3 - q * u ^ 4 + 2 * u ^ 5
            - q ^ 2 * u ^ 2 - q * u ^ 3 - u ^ 4 + 2 * q * u ^ 2 + 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (-(u ^ 8) - 2 * u ^ 7 - q * u ^ 5 - 3 * u ^ 6 - 2 * q * u ^ 4 - 3 * u ^ 5 - q * u ^ 3
            + 2 * u ^ 4 - q * u ^ 2 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))))
        + (-(u ^ 4))
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))))
        + (u ^ 15 + q * u ^ 11 + q * u ^ 10 + q * u ^ 9 - u ^ 10 + q ^ 3 * u ^ 6
            + 3 * q ^ 2 * u ^ 7 + q * u ^ 8 - u ^ 9 + q ^ 4 * u ^ 4 + 2 * q ^ 3 * u ^ 5
            - 3 * q * u ^ 7 - u ^ 8 - q ^ 3 * u ^ 4 - 2 * q ^ 2 * u ^ 5 - 2 * q * u ^ 6 + u ^ 7
            - q ^ 2 * u ^ 4 + u ^ 6 + q * u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 4))
        + (u ^ 14 + u ^ 13 + 2 * u ^ 12 + q * u ^ 10 + u ^ 11 + 2 * q * u ^ 9 + 3 * q * u ^ 8
            + 3 * q ^ 2 * u ^ 6 + 4 * q * u ^ 7 - u ^ 8 + q ^ 3 * u ^ 4 + 2 * q ^ 2 * u ^ 5
            - q * u ^ 6 - 4 * u ^ 7 - 2 * q * u ^ 5 - u ^ 6 - q * u ^ 4 + u ^ 5)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (u ^ 13 + u ^ 11 + q * u ^ 9 + q * u ^ 8 + u ^ 9 + q * u ^ 7 - u ^ 8 + q ^ 2 * u ^ 5
            + q * u ^ 6 + q ^ 2 * u ^ 4 - u ^ 6 - q * u ^ 4)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
        + (u ^ 12 + 2 * u ^ 11 + 4 * u ^ 10 + q * u ^ 8 + 2 * u ^ 9 + 2 * q * u ^ 7 + 3 * u ^ 8
            + 3 * q * u ^ 6 + 2 * u ^ 7 + 2 * q * u ^ 5 + q * u ^ 4 - 2 * u ^ 5)
              • ((auxVar 1 : Total L) ^ 4
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (u ^ 9 + u ^ 8 + u ^ 7 + u ^ 6 + u ^ 5)
              • ((auxVar 1 : Total L) ^ 4
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))))
        + (-(u ^ 16) - u ^ 13 - q * u ^ 11 - q * u ^ 10 + u ^ 11 - q * u ^ 9 - q ^ 2 * u ^ 7
            - q * u ^ 8 + u ^ 9 + 2 * q * u ^ 7 + u ^ 8 - u ^ 7)
              • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 3))
        + (-(u ^ 15) - 2 * u ^ 14 - u ^ 13 - 3 * u ^ 12 - q * u ^ 10 - 2 * u ^ 11 - 2 * q * u ^ 9
            - u ^ 10 - 2 * q * u ^ 8 - 2 * q * u ^ 7 + 2 * u ^ 7)
              • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (-(u ^ 13) - u ^ 12 - 2 * u ^ 11 - 2 * u ^ 10 - 2 * u ^ 9 - u ^ 8 - u ^ 7)
              • ((auxVar 1 : Total L) ^ 5
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
        + (u ^ 17 + u ^ 15 + u ^ 13 + q * u ^ 11 + q * u ^ 10 - u ^ 10)
              • ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C (elemSymm L 2))
        + (u ^ 16 + u ^ 15 + 2 * u ^ 14 + 2 * u ^ 13 + 2 * u ^ 12 + u ^ 11 + u ^ 10)
              • ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (-(u ^ 18) - u ^ 17 - u ^ 16 - u ^ 15 - u ^ 14)
              • ((auxVar 1 : Total L) ^ 7 * MvPolynomial.C (elemSymm L 1))
        + (u ^ 19) • ((auxVar 1 : Total L) ^ 8 * MvPolynomial.C ((1 : Lambda L)))
      ) := by
  rw [auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_two hq0 hu0 hq1]
  simp only [map_smul, map_add,
    zopOneStar_one_auxVar_cube_mul_C_elemSymm_five hq1,
    zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_mul_four hq1,
    zopOneStar_one_auxVar_cube_mul_C_elemSymm_two_mul_three hq1,
    zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_sq_mul_three hq1,
    zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_mul_two_sq hq1,
    zopOneStar_one_auxVar_cube_mul_C_elemSymm_one_cube_mul_two hq1,
    zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_four hq1,
    zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_one_mul_three hq1,
    zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_two_sq hq1,
    zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_one_sq_mul_two hq1,
    zopOneStar_one_auxVar_pow_four_mul_C_elemSymm_one_pow_four hq1,
    zopOneStar_one_auxVar_pow_five_mul_C_elemSymm_three hq1,
    zopOneStar_one_auxVar_pow_five_mul_C_elemSymm_one_mul_two hq1,
    zopOneStar_one_auxVar_pow_five_mul_C_elemSymm_one_cube hq1,
    zopOneStar_one_auxVar_pow_six_mul_C_elemSymm_two hq1,
    zopOneStar_one_auxVar_pow_six_mul_C_elemSymm_one_sq hq1,
    zopOneStar_one_auxVar_pow_seven_mul_C_elemSymm_one hq1,
    zopOneStar_one_auxVar_pow_eight_mul_C_one hq1]
  match_scalars <;> grobner

/-- **`G_3 = Z^{(1)}_{2,3}(G_2)`, written out.** Forty-two monomials over the
`y_1`-degrees `2` to `9`; every coefficient is divisible by `q^2u^2`.

`HJO.Mellit.stageWordTotal_singleton_succ` is the recursion,
`HJO.Sweep.replicatedTotal_two_three_zero_apply` the letter as `(qu)^{-1}y_1z_1y_1^2z_1`,
and `HJO.Mellit.zopOneStar_one_stageWordTotal_two_three_two` with
`HJO.Mellit.zopOneStar_one_auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_two` are
its two steps. -/
theorem stageWordTotal_two_three_three_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    (stageWordTotal q u 2 3 [3] : Total L) = (q ^ 2 * u ^ 2) • (
          (-(q ^ 12) - q ^ 11 * u - q ^ 10 * u ^ 2 - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5
            - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7 - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10
            - q * u ^ 11 - u ^ 12 + q ^ 11 + u ^ 11 + q ^ 10 + q ^ 9 * u + q * u ^ 9 + u ^ 10
            + q ^ 8 * u + q ^ 7 * u ^ 2 + q ^ 2 * u ^ 7 + q * u ^ 8 + 2 * q ^ 7 * u
            + 3 * q ^ 6 * u ^ 2 + 3 * q ^ 5 * u ^ 3 + 2 * q ^ 4 * u ^ 4 + 3 * q ^ 3 * u ^ 5
            + 3 * q ^ 2 * u ^ 6 + 2 * q * u ^ 7 - 2 * q ^ 7 - 2 * q ^ 6 * u + 2 * q ^ 4 * u ^ 3
            + 2 * q ^ 3 * u ^ 4 - 2 * q * u ^ 6 - 2 * u ^ 7 - 2 * q ^ 5 * u - 3 * q ^ 4 * u ^ 2
            - 3 * q ^ 3 * u ^ 3 - 3 * q ^ 2 * u ^ 4 - 2 * q * u ^ 5 - q ^ 4 * u
            - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3 - q * u ^ 4 + q ^ 4 + q ^ 3 * u
            + 2 * q ^ 2 * u ^ 2 + q * u ^ 3 + u ^ 4 + q ^ 3 + 2 * q ^ 2 * u + 2 * q * u ^ 2
            + u ^ 3 - q ^ 2 - q * u - u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 7))
        + (-(q ^ 11) - q ^ 10 * u - q ^ 9 * u ^ 2 - q ^ 8 * u ^ 3 - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5
            - q ^ 5 * u ^ 6 - q ^ 4 * u ^ 7 - q ^ 3 * u ^ 8 - q ^ 2 * u ^ 9 - q * u ^ 10 - u ^ 11
            - q ^ 9 * u - q ^ 8 * u ^ 2 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4 - q ^ 5 * u ^ 5
            - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 - q * u ^ 9 + q ^ 9 - q ^ 7 * u ^ 2
            - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5 - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7
            + u ^ 9 + q ^ 8 + q ^ 7 * u - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5
            + q * u ^ 7 + u ^ 8 + 2 * q ^ 7 + 5 * q ^ 6 * u + 5 * q ^ 5 * u ^ 2
            + 4 * q ^ 4 * u ^ 3 + 4 * q ^ 3 * u ^ 4 + 5 * q ^ 2 * u ^ 5 + 5 * q * u ^ 6
            + 2 * u ^ 7 - 2 * q ^ 6 + q ^ 5 * u + 5 * q ^ 4 * u ^ 2 + 6 * q ^ 3 * u ^ 3
            + 5 * q ^ 2 * u ^ 4 + q * u ^ 5 - 2 * u ^ 6 - 2 * q ^ 5 - 4 * q ^ 4 * u
            - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3 - 4 * q * u ^ 4 - 2 * u ^ 5 - q ^ 4
            - 4 * q ^ 3 * u - 7 * q ^ 2 * u ^ 2 - 4 * q * u ^ 3 - u ^ 4 + q ^ 3 + q ^ 2 * u
            + q * u ^ 2 + u ^ 3 + 2 * q ^ 2 + 3 * q * u + 2 * u ^ 2 - q - u)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1 * elemSymm L 6))
        + (-(q ^ 10) - q ^ 9 * u - q ^ 8 * u ^ 2 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4 - q ^ 5 * u ^ 5
            - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 - q * u ^ 9 - u ^ 10 + q ^ 9 + u ^ 9
            - q ^ 6 * u ^ 2 - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5 - q ^ 2 * u ^ 6
            - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 + q ^ 6 + 2 * q ^ 5 * u + 2 * q ^ 4 * u ^ 2
            + 3 * q ^ 3 * u ^ 3 + 2 * q ^ 2 * u ^ 4 + 2 * q * u ^ 5 + u ^ 6 + q ^ 4 * u
            + 2 * q ^ 3 * u ^ 2 + 2 * q ^ 2 * u ^ 3 + q * u ^ 4 - 2 * q ^ 3 - 2 * q ^ 2 * u
            - 2 * q * u ^ 2 - 2 * u ^ 3 - q * u + q + u)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2 * elemSymm L 5))
        + (-(q ^ 9) - q ^ 8 * u - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5
            - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7 - q * u ^ 8 - u ^ 9 - q ^ 7 * u - q ^ 6 * u ^ 2
            - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5 - q ^ 2 * u ^ 6 - q * u ^ 7
            + 2 * q ^ 7 + q ^ 6 * u + q * u ^ 6 + 2 * u ^ 7 + q ^ 5 * u - q ^ 3 * u ^ 3
            + q * u ^ 5 + q ^ 5 + 3 * q ^ 4 * u + 5 * q ^ 3 * u ^ 2 + 5 * q ^ 2 * u ^ 3
            + 3 * q * u ^ 4 + u ^ 5 - 2 * q ^ 4 - 2 * u ^ 4 - 2 * q ^ 3 - 5 * q ^ 2 * u
            - 5 * q * u ^ 2 - 2 * u ^ 3 + 2 * q ^ 2 + 2 * q * u + 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3 * elemSymm L 4))
        + (-(q ^ 9) - q ^ 8 * u - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5
            - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7 - q * u ^ 8 - u ^ 9 - q ^ 7 * u - q ^ 6 * u ^ 2
            - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5 - q ^ 2 * u ^ 6 - q * u ^ 7
            - q ^ 6 * u - 2 * q ^ 5 * u ^ 2 - 2 * q ^ 4 * u ^ 3 - 2 * q ^ 3 * u ^ 4
            - 2 * q ^ 2 * u ^ 5 - q * u ^ 6 + 2 * q ^ 6 + 2 * q ^ 5 * u + q ^ 4 * u ^ 2
            + q ^ 2 * u ^ 4 + 2 * q * u ^ 5 + 2 * u ^ 6 + q ^ 5 + 4 * q ^ 4 * u
            + 5 * q ^ 3 * u ^ 2 + 5 * q ^ 2 * u ^ 3 + 4 * q * u ^ 4 + u ^ 5 - q ^ 4
            + 2 * q ^ 2 * u ^ 2 - u ^ 4 - q ^ 3 - 3 * q ^ 2 * u - 3 * q * u ^ 2 - u ^ 3 - q ^ 2
            - q * u - u ^ 2 + q + u)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (-(q ^ 8) - q ^ 7 * u - q ^ 6 * u ^ 2 - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5
            - q ^ 2 * u ^ 6 - q * u ^ 7 - u ^ 8 - q ^ 7 - 2 * q ^ 6 * u - 2 * q ^ 5 * u ^ 2
            - 2 * q ^ 4 * u ^ 3 - 2 * q ^ 3 * u ^ 4 - 2 * q ^ 2 * u ^ 5 - 2 * q * u ^ 6 - u ^ 7
            + q ^ 6 - q ^ 5 * u - 2 * q ^ 4 * u ^ 2 - 2 * q ^ 3 * u ^ 3 - 2 * q ^ 2 * u ^ 4
            - q * u ^ 5 + u ^ 6 + q ^ 5 + q ^ 4 * u - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3 + q * u ^ 4
            + u ^ 5 + q ^ 4 + 3 * q ^ 3 * u + 5 * q ^ 2 * u ^ 2 + 3 * q * u ^ 3 + u ^ 4
            + 2 * q ^ 3 + 4 * q ^ 2 * u + 4 * q * u ^ 2 + 2 * u ^ 3 - 3 * q ^ 2 - 4 * q * u
            - 3 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (-(q ^ 7) - q ^ 6 * u - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5
            - q * u ^ 6 - u ^ 7 - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4
            - q * u ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3 - q * u ^ 4
            + 3 * q ^ 4 + 3 * q ^ 3 * u + 3 * q ^ 2 * u ^ 2 + 3 * q * u ^ 3 + 3 * u ^ 4
            + 3 * q ^ 2 * u + 3 * q * u ^ 2 - 3 * q ^ 2 - 4 * q * u - 3 * u ^ 2 + q + u)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3)))
        + (-(q ^ 6) - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4 - q * u ^ 5
            - u ^ 6 - q ^ 4 * u - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3 - q * u ^ 4 - q ^ 3 * u
            - 2 * q ^ 2 * u ^ 2 - q * u ^ 3 + 2 * q ^ 3 + 2 * q ^ 2 * u + 2 * q * u ^ 2
            + 2 * u ^ 3 + q ^ 2 + 3 * q * u + u ^ 2 - 2 * q - 2 * u)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3)))
        + (-(q ^ 6) - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4 - q * u ^ 5
            - u ^ 6 - q ^ 4 * u - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3 - q * u ^ 4 + q ^ 4 + q ^ 3 * u
            + q * u ^ 3 + u ^ 4 + q ^ 2 * u + q * u ^ 2 + q ^ 2 + q * u + u ^ 2 - q - u)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))))
        + (-(q ^ 5) - q ^ 4 * u - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3 - q * u ^ 4 - u ^ 5 - 2 * q ^ 4
            - 3 * q ^ 3 * u - 3 * q ^ 2 * u ^ 2 - 3 * q * u ^ 3 - 2 * u ^ 4 - 2 * q ^ 2 * u
            - 2 * q * u ^ 2 + 4 * q ^ 2 + 5 * q * u + 4 * u ^ 2 - q - u)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))))
        + (-(q ^ 3) - q ^ 2 * u - q * u ^ 2 - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2 + 2 * q + 2 * u)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))))
        + (-(q ^ 2) - q * u - u ^ 2 + q + u)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))))
        + (-q - u)
              • ((auxVar 1 : Total L) ^ 2
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))))
        + (u ^ 13 + q * u ^ 11 + q ^ 2 * u ^ 9 + q * u ^ 10 - u ^ 11 + q ^ 3 * u ^ 7
            + q ^ 2 * u ^ 8 - u ^ 10 + q ^ 8 * u + 2 * q ^ 7 * u ^ 2 + 2 * q ^ 6 * u ^ 3
            + 2 * q ^ 5 * u ^ 4 + 3 * q ^ 4 * u ^ 5 + 3 * q ^ 3 * u ^ 6 + 2 * q ^ 2 * u ^ 7
            - q * u ^ 8 - u ^ 9 - 2 * q ^ 7 * u - 2 * q ^ 6 * u ^ 2 - q ^ 3 * u ^ 5
            - 4 * q ^ 2 * u ^ 6 - 5 * q * u ^ 7 - 3 * q ^ 5 * u ^ 2 - 5 * q ^ 4 * u ^ 3
            - 6 * q ^ 3 * u ^ 4 - 6 * q ^ 2 * u ^ 5 - q * u ^ 6 + 2 * u ^ 7 + q ^ 5 * u
            + q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 + 2 * q ^ 2 * u ^ 4 + 4 * q * u ^ 5 + 2 * u ^ 6
            + q ^ 4 * u + 4 * q ^ 3 * u ^ 2 + 6 * q ^ 2 * u ^ 3 + 4 * q * u ^ 4 - q * u ^ 3
            - 2 * u ^ 4 - 2 * q ^ 2 * u - 3 * q * u ^ 2 - u ^ 3 + q * u + u ^ 2)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 6))
        + (u ^ 12 + q * u ^ 10 + u ^ 11 + q ^ 2 * u ^ 8 + 2 * q * u ^ 9 + q ^ 3 * u ^ 6
            + 2 * q ^ 2 * u ^ 7 + 2 * q * u ^ 8 - u ^ 9 + 2 * q ^ 7 * u + 3 * q ^ 6 * u ^ 2
            + 3 * q ^ 5 * u ^ 3 + 4 * q ^ 4 * u ^ 4 + 5 * q ^ 3 * u ^ 5 + 5 * q ^ 2 * u ^ 6
            + q * u ^ 7 - 2 * u ^ 8 - 2 * q ^ 6 * u + q ^ 5 * u ^ 2 + 3 * q ^ 4 * u ^ 3
            + 3 * q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5 - 6 * q * u ^ 6 - 3 * u ^ 7 - 2 * q ^ 5 * u
            - 7 * q ^ 4 * u ^ 2 - 8 * q ^ 3 * u ^ 3 - 11 * q ^ 2 * u ^ 4 - 7 * q * u ^ 5
            - 3 * q ^ 3 * u ^ 2 - 4 * q ^ 2 * u ^ 3 + q * u ^ 4 + 3 * u ^ 5 + 2 * q ^ 3 * u
            + 6 * q ^ 2 * u ^ 2 + 6 * q * u ^ 3 + 3 * u ^ 4 + 2 * q ^ 2 * u + 2 * q * u ^ 2
            - 2 * q * u - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 5))
        + (u ^ 11 + q * u ^ 9 + q ^ 2 * u ^ 7 + q * u ^ 8 + u ^ 9 + q ^ 3 * u ^ 5 + q ^ 2 * u ^ 6
            + 2 * q * u ^ 7 - u ^ 8 + q ^ 6 * u + 2 * q ^ 5 * u ^ 2 + 3 * q ^ 4 * u ^ 3
            + 3 * q ^ 3 * u ^ 4 + 4 * q ^ 2 * u ^ 5 + q * u ^ 6 - 2 * u ^ 7 - 2 * q ^ 5 * u
            - q ^ 4 * u ^ 2 - 2 * q ^ 2 * u ^ 4 - 5 * q * u ^ 5 - 2 * u ^ 6 + q ^ 4 * u
            - 2 * q ^ 3 * u ^ 2 - 4 * q ^ 2 * u ^ 3 - 3 * q * u ^ 4 + u ^ 5 - q ^ 3 * u
            - 2 * q ^ 2 * u ^ 2 + 2 * u ^ 4 + 2 * q ^ 2 * u + 4 * q * u ^ 2 + u ^ 3 - q * u
            - u ^ 2) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2 * elemSymm L 4))
        + (u ^ 10 + q * u ^ 8 + q ^ 2 * u ^ 6 + q * u ^ 7 - u ^ 8 + q ^ 3 * u ^ 4 + q ^ 2 * u ^ 5
            + q ^ 5 * u + 2 * q ^ 4 * u ^ 2 + 2 * q ^ 3 * u ^ 3 + q ^ 2 * u ^ 4 - u ^ 6
            - 2 * q ^ 4 * u - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3 - 4 * q * u ^ 4 - u ^ 5
            - q ^ 2 * u ^ 2 + 2 * u ^ 4 + 2 * q ^ 2 * u + 3 * q * u ^ 2 + u ^ 3 - q * u - u ^ 2)
              • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 3 * elemSymm L 3))
        + (u ^ 10 + q * u ^ 8 + u ^ 9 + q ^ 2 * u ^ 6 + 2 * q * u ^ 7 + u ^ 8 + q ^ 6 * u
            + q ^ 5 * u ^ 2 + q ^ 4 * u ^ 3 + 2 * q ^ 3 * u ^ 4 + 3 * q ^ 2 * u ^ 5
            + 3 * q * u ^ 6 + q ^ 5 * u + 4 * q ^ 4 * u ^ 2 + 5 * q ^ 3 * u ^ 3
            + 5 * q ^ 2 * u ^ 4 + q * u ^ 5 - 2 * u ^ 6 - 2 * q ^ 4 * u - 2 * q ^ 3 * u ^ 2
            - 3 * q ^ 2 * u ^ 3 - 5 * q * u ^ 4 - 3 * u ^ 5 - q ^ 3 * u - 5 * q ^ 2 * u ^ 2
            - 4 * q * u ^ 3 - u ^ 4 - q ^ 2 * u + u ^ 3 + 2 * q * u + 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))
        + (u ^ 9 + q * u ^ 7 + 3 * u ^ 8 + q ^ 2 * u ^ 5 + 4 * q * u ^ 6 + u ^ 7 + q ^ 5 * u
            + q ^ 4 * u ^ 2 + 2 * q ^ 3 * u ^ 3 + 5 * q ^ 2 * u ^ 4 + 5 * q * u ^ 5 + u ^ 6
            + q ^ 4 * u + 5 * q ^ 3 * u ^ 2 + 5 * q ^ 2 * u ^ 3 + 3 * q * u ^ 4 - 3 * u ^ 5
            - q ^ 3 * u - 2 * q ^ 2 * u ^ 2 - 5 * q * u ^ 3 - 6 * u ^ 4 - 5 * q ^ 2 * u
            - 8 * q * u ^ 2 - u ^ 3 + 4 * q * u + 4 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))
        + (u ^ 7 + q * u ^ 5 + q ^ 2 * u ^ 3 + q * u ^ 4 + q ^ 2 * u ^ 2 - u ^ 4 - q * u ^ 2)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2)))
        + (u ^ 7 + q * u ^ 5 + u ^ 6 + q ^ 4 * u + q ^ 3 * u ^ 2 + 2 * q ^ 2 * u ^ 3
            + 2 * q * u ^ 4 + u ^ 5 + 2 * q ^ 2 * u ^ 2 + q * u ^ 3 + q ^ 2 * u - u ^ 3
            - 2 * q * u - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))))
        + (u ^ 6 + q * u ^ 4 + 2 * u ^ 5 + q ^ 3 * u + q ^ 2 * u ^ 2 + 3 * q * u ^ 3 + 3 * u ^ 4
            + q ^ 2 * u + 3 * q * u ^ 2 - u ^ 3 - 2 * q * u - 2 * u ^ 2)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))))
        + (u ^ 3 + q * u + u ^ 2)
              • ((auxVar 1 : Total L) ^ 3
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))))
        + (-(u ^ 14) - q * u ^ 11 - q * u ^ 10 + u ^ 11 - q ^ 2 * u ^ 8 - q * u ^ 9 + u ^ 10
            - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5 - 2 * q ^ 3 * u ^ 6
            - 3 * q ^ 2 * u ^ 7 + q ^ 6 * u ^ 2 - q ^ 5 * u ^ 3 - 2 * q ^ 4 * u ^ 4
            - 3 * q ^ 3 * u ^ 5 + 4 * q * u ^ 7 + u ^ 8 + q ^ 5 * u ^ 2 + 3 * q ^ 4 * u ^ 3
            + 4 * q ^ 3 * u ^ 4 + 6 * q ^ 2 * u ^ 5 + 3 * q * u ^ 6 - u ^ 7 + 2 * q ^ 3 * u ^ 3
            + 2 * q ^ 2 * u ^ 4 - q * u ^ 5 - u ^ 6 - q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3
            - 3 * q * u ^ 4 - u ^ 5 - q ^ 2 * u ^ 2 - q * u ^ 3 + q * u ^ 2 + u ^ 3)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 5))
        + (-(u ^ 13) - u ^ 12 - q * u ^ 10 - u ^ 11 - 2 * q * u ^ 9 - u ^ 10 - q ^ 2 * u ^ 7
            - 3 * q * u ^ 8 + 2 * u ^ 9 - q ^ 6 * u ^ 2 - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4
            - 2 * q ^ 3 * u ^ 5 - 5 * q ^ 2 * u ^ 6 - 3 * q * u ^ 7 + 2 * u ^ 8
            - 3 * q ^ 4 * u ^ 3 - 6 * q ^ 3 * u ^ 4 - 4 * q ^ 2 * u ^ 5 + 3 * q * u ^ 6
            + 3 * u ^ 7 + q ^ 4 * u ^ 2 + 2 * q ^ 3 * u ^ 3 + 5 * q ^ 2 * u ^ 4 + 6 * q * u ^ 5
            + q ^ 3 * u ^ 2 + 5 * q ^ 2 * u ^ 3 + 3 * q * u ^ 4 - u ^ 5 - 2 * q * u ^ 3 - u ^ 4
            - q * u ^ 2 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 4))
        + (-(u ^ 12) - u ^ 11 - q * u ^ 9 - u ^ 10 - 2 * q * u ^ 8 + u ^ 9 - q ^ 2 * u ^ 6
            - 3 * q * u ^ 7 - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - 3 * q ^ 2 * u ^ 5
            - q * u ^ 6 + 2 * u ^ 7 - 2 * q ^ 3 * u ^ 3 - 2 * q ^ 2 * u ^ 4 + 2 * q * u ^ 5
            + u ^ 6 + q ^ 3 * u ^ 2 + 2 * q ^ 2 * u ^ 3 + 2 * q * u ^ 4 + 2 * q ^ 2 * u ^ 2
            + 3 * q * u ^ 3 + u ^ 4 - 2 * q * u ^ 2 - 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2 * elemSymm L 3))
        + (-(u ^ 11) - u ^ 10 - q * u ^ 8 - 3 * u ^ 9 - 2 * q * u ^ 7 - u ^ 8 - 2 * q ^ 2 * u ^ 5
            - 4 * q * u ^ 6 - u ^ 7 - q ^ 4 * u ^ 2 - 2 * q ^ 3 * u ^ 3 - 4 * q ^ 2 * u ^ 4
            - 3 * q * u ^ 5 + 3 * u ^ 6 - 2 * q ^ 2 * u ^ 3 + q * u ^ 4 + 3 * u ^ 5
            + 2 * q * u ^ 3 + q * u ^ 2 + u ^ 3)
              • ((auxVar 1 : Total L) ^ 4
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (-(u ^ 10) - 2 * u ^ 9 - q * u ^ 7 - 2 * u ^ 8 - 3 * q * u ^ 6 - u ^ 7 - q ^ 2 * u ^ 4
            - 3 * q * u ^ 5 - q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3 - q * u ^ 4 + 2 * u ^ 5
            - q ^ 2 * u ^ 2 - q * u ^ 3 - u ^ 4 + 2 * q * u ^ 2 + 2 * u ^ 3)
              • ((auxVar 1 : Total L) ^ 4
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
        + (-(u ^ 8) - 2 * u ^ 7 - q * u ^ 5 - 3 * u ^ 6 - 2 * q * u ^ 4 - 3 * u ^ 5 - q * u ^ 3
            + 2 * u ^ 4 - q * u ^ 2 - u ^ 3)
              • ((auxVar 1 : Total L) ^ 4
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))))
        + (-(u ^ 4))
              • ((auxVar 1 : Total L) ^ 4
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))))
        + (u ^ 15 + q * u ^ 11 + q * u ^ 10 + q * u ^ 9 - u ^ 10 + q ^ 3 * u ^ 6
            + 3 * q ^ 2 * u ^ 7 + q * u ^ 8 - u ^ 9 + q ^ 4 * u ^ 4 + 2 * q ^ 3 * u ^ 5
            - 3 * q * u ^ 7 - u ^ 8 - q ^ 3 * u ^ 4 - 2 * q ^ 2 * u ^ 5 - 2 * q * u ^ 6 + u ^ 7
            - q ^ 2 * u ^ 4 + u ^ 6 + q * u ^ 4)
              • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 4))
        + (u ^ 14 + u ^ 13 + 2 * u ^ 12 + q * u ^ 10 + u ^ 11 + 2 * q * u ^ 9 + 3 * q * u ^ 8
            + 3 * q ^ 2 * u ^ 6 + 4 * q * u ^ 7 - u ^ 8 + q ^ 3 * u ^ 4 + 2 * q ^ 2 * u ^ 5
            - q * u ^ 6 - 4 * u ^ 7 - 2 * q * u ^ 5 - u ^ 6 - q * u ^ 4 + u ^ 5)
              • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1 * elemSymm L 3))
        + (u ^ 13 + u ^ 11 + q * u ^ 9 + q * u ^ 8 + u ^ 9 + q * u ^ 7 - u ^ 8 + q ^ 2 * u ^ 5
            + q * u ^ 6 + q ^ 2 * u ^ 4 - u ^ 6 - q * u ^ 4)
              • ((auxVar 1 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 2 * elemSymm L 2))
        + (u ^ 12 + 2 * u ^ 11 + 4 * u ^ 10 + q * u ^ 8 + 2 * u ^ 9 + 2 * q * u ^ 7 + 3 * u ^ 8
            + 3 * q * u ^ 6 + 2 * u ^ 7 + 2 * q * u ^ 5 + q * u ^ 4 - 2 * u ^ 5)
              • ((auxVar 1 : Total L) ^ 5
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
        + (u ^ 9 + u ^ 8 + u ^ 7 + u ^ 6 + u ^ 5)
              • ((auxVar 1 : Total L) ^ 5
                  * MvPolynomial.C (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))))
        + (-(u ^ 16) - u ^ 13 - q * u ^ 11 - q * u ^ 10 + u ^ 11 - q * u ^ 9 - q ^ 2 * u ^ 7
            - q * u ^ 8 + u ^ 9 + 2 * q * u ^ 7 + u ^ 8 - u ^ 7)
              • ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C (elemSymm L 3))
        + (-(u ^ 15) - 2 * u ^ 14 - u ^ 13 - 3 * u ^ 12 - q * u ^ 10 - 2 * u ^ 11 - 2 * q * u ^ 9
            - u ^ 10 - 2 * q * u ^ 8 - 2 * q * u ^ 7 + 2 * u ^ 7)
              • ((auxVar 1 : Total L) ^ 6 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (-(u ^ 13) - u ^ 12 - 2 * u ^ 11 - 2 * u ^ 10 - 2 * u ^ 9 - u ^ 8 - u ^ 7)
              • ((auxVar 1 : Total L) ^ 6
                  * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
        + (u ^ 17 + u ^ 15 + u ^ 13 + q * u ^ 11 + q * u ^ 10 - u ^ 10)
              • ((auxVar 1 : Total L) ^ 7 * MvPolynomial.C (elemSymm L 2))
        + (u ^ 16 + u ^ 15 + 2 * u ^ 14 + 2 * u ^ 13 + 2 * u ^ 12 + u ^ 11 + u ^ 10)
              • ((auxVar 1 : Total L) ^ 7 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (-(u ^ 18) - u ^ 17 - u ^ 16 - u ^ 15 - u ^ 14)
              • ((auxVar 1 : Total L) ^ 8 * MvPolynomial.C (elemSymm L 1))
        + (u ^ 19) • ((auxVar 1 : Total L) ^ 9 * MvPolynomial.C ((1 : Lambda L)))
      ) := by
  have hrec := stageWordTotal_singleton_succ (L := L) q u 2 3 1
  norm_num at hrec
  rw [hrec, replicatedTotal_two_three_zero_apply,
    zopOneStar_one_auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_two hq0 hu0 hq1,
    mul_smul_comm, smul_smul,
    show (q * u)⁻¹ * (q ^ 3 * u ^ 3) = q ^ 2 * u ^ 2 from by field_simp]
  -- The letter's outer `y_1` is a bare `auxVar 1`, so the shift is the `n = 1` case.
  have hshift (x : L) (k : ℕ) (f : Lambda L) :
      (auxVar 1 : Total L) * (x • ((auxVar 1 : Total L) ^ k * MvPolynomial.C f))
        = x • ((auxVar 1 : Total L) ^ (k + 1) * MvPolynomial.C f) := by
    rw [mul_smul_comm, ← mul_assoc, ← pow_succ']
  simp only [mul_add, hshift, Nat.reduceAdd]

end HJO.Mellit

end
