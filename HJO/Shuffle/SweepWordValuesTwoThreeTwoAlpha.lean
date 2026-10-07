/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWordsTwoThreeTwoAlpha
public import HJO.Shuffle.SweepMonomialValuesTwoThreeTwo

/-! # The nineteen sweep words of the `4 × 6` rectangle at `c_{(2)}`, evaluated on the vacuum

`HJO/Shuffle/SweepWordsTwoThreeTwoAlpha.lean` writes each of the nineteen words as a product of
event operators. This file applies each product to `1` and reads off the value.
Each word is named for its heights `ŷ_1ŷ_2ŷ_3` (`alphaTwoPath245` is the path `![0, 2, 4, 5, 6]`).
The ten words whose first height is `2` or `3`, `alphaTwoPath245` to `alphaTwoPath366`, are
evaluated here; the nine whose first height is at least `4`, `alphaTwoPath445` to
`alphaTwoPath666`, in `HJO/Shuffle/SweepWordValuesTwoThreeTwoAlphaUpper.lean`, because the
nineteen together are longer than a file should be.

## The shape of every value

The grading here is `1`, not `2`: the composition `(2)` has one part, so every one of the nineteen
values lies in `V_1` and is a polynomial in `y_1` alone with symmetric coefficients. The
`y_1`-degrees run from `2` to `6`, and the total degree is `6` throughout.

## The three operator tables

`HJO/Shuffle/SweepMonomialValuesTwoThreeTwo.lean` supplies what the tree did not have: the
corner at width `2` on `y_1^ay_2^b` with `a < b + 1`, the raising on a power of the bottom variable,
the lowering at an exponent above `1`, and the two raisings that meet a symmetric coefficient. Each
step below is one `simp only` over those tables followed by one `ring`.

## Genericity

Only `q ≠ 0` and `q ≠ 1` are ever read, both of them `HJO.Sweep.corner`'s own — `q ≠ 0` also
for the negative powers the type-`C` events carry. `u` is unrestricted: it enters only through the
type-`E` events, which multiply by it.

## References

This file concerns `HJO.Mellit.sweepOperator`, `HJO.Mellit.partialSweepWord`, `HJO.Sweep.dplus`,
`HJO.Sweep.dminus`, `HJO.Sweep.corner`, `HJO.Sym.Bop`.
-/

@[expose] public section

-- Every step closes on a polynomial identity normalised by the same rewrite set, and every step is
-- written in the same shape: which members of the set fire, and whether the closing normalisation
-- is needed at all, depends on the monomial the operator meets. So a step may leave a simp argument
-- unused, or reach its value before the normalisation runs.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

-- Every exponent written as a numeral in this file is a natural number. Saying so up front lets
-- each `x ^ n` resolve `HPow _ ℕ _` at once instead of retrying instance resolution for the
-- pending numeral type until defaulting, which dominated elaboration here. The elaborated terms
-- are the ones the default instance would produce.
local macro_rules | `($x ^ $n:num) => `(rightact% HPow.hPow $x ($n : ℕ))

namespace HJO.Mellit

open Finset HJO.Paths HJO.Sweep HJO.Sym MvPolynomial

section Values

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

theorem partialSweepWord_alphaTwoPath245_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath245 (sepLevel 2 2) (1 : Total L)
      = ((q - 1) ^ 2*(q + 1) : L) • (MvPolynomial.C (elemSymm L 4) * ((auxVar 1 : Total L) ^ 2))
        + (q - 1 : L) • (MvPolynomial.C (elemSymm L 2 ^ 2) * ((auxVar 1 : Total L) ^ 2))
        + ((q - 1)*(q + 1) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 3) * ((auxVar 1 :
            Total L) ^ 2))
        + (1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 2))
            := by
  have hv1 : dplus q 0 ((1 : Total L))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_zero_monoZero q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv2 : dplus q 1 ((-1 : L) • ((auxVar 1 : Total L) ^ 1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_one_monoOne_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv3 : dplus q 2 ((1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)
          := by
    simp only [map_add, map_smul, dplus_two_monoTwo_one_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv4 : dplus q 3 ((-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3
      : Total L) ^ 1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1 *
          (auxVar 4 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_three_monoThree_one_one_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv5 : corner q 4 ((1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3
      : Total L) ^ 1 * (auxVar 4 : Total L) ^ 1))
      = (-q ^ 3 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L)
          ^ 1 * (auxVar 4 : Total L) ^ 1) := by
    simp only [map_add, map_smul, corner_four_monoFour_one_one_one_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz6_0 : ((q : L) ^ (-2 : ℤ)) * (-q ^ 3 : L) = (-q : L) := by
    field_simp
    all_goals ring
  have hv6 : ((q : L) ^ (-2 : ℤ)) • ((-q ^ 3 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total
      L) ^ 1 * (auxVar 3 : Total L) ^ 1 * (auxVar 4 : Total L) ^ 1))
      = (-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1
          * (auxVar 4 : Total L) ^ 1) := by
    simp only [smul_add, smul_smul, hz6_0]
  have hv7 : dminus q 4 ((-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar
      3 : Total L) ^ 1 * (auxVar 4 : Total L) ^ 1))
      = (q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L)
          ^ 1 * (auxVar 3 : Total L) ^ 1)) := by
    simp only [map_add, map_smul, dminus_four_monoFour q, bopNat_one_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : corner q 3 ((q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 *
      (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)))
      = (-q ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
          Total L) ^ 2 * (auxVar 3 : Total L) ^ 1)) := by
    simp only [map_add, map_smul, corner_three_monoThree_two_one_one_C hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz9_0 : ((q : L) ^ (-2 : ℤ)) * (-q ^ 2 : L) = (-1 : L) := by
    field_simp
    all_goals ring
  have hv9 : ((q : L) ^ (-2 : ℤ)) • ((-q ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 :
      Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 1)))
      = (-1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total
          L) ^ 2 * (auxVar 3 : Total L) ^ 1)) := by
    simp only [smul_add, smul_smul, hz9_0]
  have hv10 : dminus q 3 ((-1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 *
      (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 1)))
      = (q - 1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
          Total L) ^ 2))
        + (1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
            Total L) ^ 2)) := by
    simp only [map_add, map_smul, dminus_three_monoThree_C q, bopNat_one_elemSymm_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv11 : dminus q 2 ((q - 1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2
      * (auxVar 2 : Total L) ^ 2))
          + (1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
              Total L) ^ 2)))
      = ((q - 1) ^ 2*(q + 1) : L) • (MvPolynomial.C (elemSymm L 4) * ((auxVar 1 : Total L) ^ 2))
        + (q - 1 : L) • (MvPolynomial.C (elemSymm L 2 ^ 2) * ((auxVar 1 : Total L) ^ 2))
        + ((q - 1)*(q + 1) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 3) * ((auxVar 1 :
            Total L) ^ 2))
        + (1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 2))
            := by
    simp only [map_add, map_smul, dminus_two_monoTwo_C q, bopNat_two_elemSymm_one_sq,
        bopNat_two_elemSymm_two]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath245 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11]

theorem partialSweepWord_alphaTwoPath246_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath246 (sepLevel 2 2) (1 : Total L)
      = (q*u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 4) * ((auxVar 1 : Total L) ^ 2))
        + (u : L) • (MvPolynomial.C (elemSymm L 2 ^ 2) * ((auxVar 1 : Total L) ^ 2))
        + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 3) * ((auxVar 1 : Total L) ^
            2))
        + (q*u*(q - 1) ^ 2 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (q*u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L)
            ^ 3)) := by
  have hv1 : dplus q 0 ((1 : Total L))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_zero_monoZero q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv2 : dplus q 1 ((-1 : L) • ((auxVar 1 : Total L) ^ 1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_one_monoOne_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv3 : corner q 2 ((1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1))
      = (-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, corner_two_monoTwo_one_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv4 : dplus q 2 ((-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1))
      = (q : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 1)
        + (-q*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 :
            Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_two_monoTwo_two_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv5 : corner q 3 ((q : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar 3
      : Total L) ^ 1)
          + (-q*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 :
              Total L) ^ 1))
      = (-q ^ 2 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L)
          ^ 2)
        + (q ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 :
            Total L) ^ 1) := by
    simp only [map_add, map_smul, corner_three_monoThree_two_one_one hq0 hq1,
        corner_three_monoThree_one_two_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz6_0 : ((q : L) ^ (-1 : ℤ)) * (-q ^ 2 : L) = (-q : L) := by
    field_simp
    all_goals ring
  have hz6_1 : ((q : L) ^ (-1 : ℤ)) * (q ^ 2*(q - 1) : L) = (q*(q - 1) : L) := by
    field_simp
    all_goals ring
  have hv6 : ((q : L) ^ (-1 : ℤ)) • ((-q ^ 2 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total
      L) ^ 1 * (auxVar 3 : Total L) ^ 2)
          + (q ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3
              : Total L) ^ 1))
      = (-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 2)
        + (q*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 :
            Total L) ^ 1) := by
    simp only [smul_add, smul_smul, hz6_0, hz6_1]
  have hv7 : dminus q 3 ((-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar
      3 : Total L) ^ 2)
          + (q*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 :
              Total L) ^ 1))
      = (-q : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total
          L) ^ 1))
        + (-q*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2
            : Total L) ^ 2)) := by
    simp only [map_add, map_smul, dminus_three_monoThree q, bopNat_one_one, bopNat_two_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : corner q 2 ((-q : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 *
      (auxVar 2 : Total L) ^ 1))
          + (-q*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar
              2 : Total L) ^ 2)))
      = (q : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L)
          ^ 2))
        + (q ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 *
            (auxVar 2 : Total L) ^ 2)) := by
    simp only [map_add, map_smul, corner_two_monoTwo_two_two_C hq0 hq1,
        corner_two_monoTwo_two_one_C hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz9_0 : ((q : L) ^ (-1 : ℤ)) * (q : L) = (1 : L) := by
    field_simp
    all_goals ring
  have hz9_1 : ((q : L) ^ (-1 : ℤ)) * (q ^ 2*(q - 1) : L) = (q*(q - 1) : L) := by
    field_simp
    all_goals ring
  have hv9 : ((q : L) ^ (-1 : ℤ)) • ((q : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total
      L) ^ 2 * (auxVar 2 : Total L) ^ 2))
          + (q ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 *
              (auxVar 2 : Total L) ^ 2)))
      = (1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L)
          ^ 2))
        + (q*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2
            : Total L) ^ 2)) := by
    simp only [smul_add, smul_smul, hz9_0, hz9_1]
  have hv10 : (u : L) • ((1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 *
      (auxVar 2 : Total L) ^ 2))
          + (q*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar
              2 : Total L) ^ 2)))
      = (u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L)
          ^ 2))
        + (q*u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar
            2 : Total L) ^ 2)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv11 : dminus q 2 ((u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 *
      (auxVar 2 : Total L) ^ 2))
          + (q*u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 *
              (auxVar 2 : Total L) ^ 2)))
      = (q*u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 4) * ((auxVar 1 : Total L) ^ 2))
        + (u : L) • (MvPolynomial.C (elemSymm L 2 ^ 2) * ((auxVar 1 : Total L) ^ 2))
        + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 3) * ((auxVar 1 : Total L) ^
            2))
        + (q*u*(q - 1) ^ 2 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (q*u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L)
            ^ 3)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo_C q, bopNat_two_elemSymm_one,
        bopNat_two_elemSymm_two]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath246 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11]

theorem partialSweepWord_alphaTwoPath255_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath255 (sepLevel 2 2) (1 : Total L)
      = (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 4) * ((auxVar 1 : Total L) ^ 2))
        + (u : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 3) * ((auxVar 1 : Total L) ^ 2))
        + (u*(q - 1) ^ 2 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^
            3)) := by
  have hv1 : dplus q 0 ((1 : Total L))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_zero_monoZero q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv2 : corner q 1 ((-1 : L) • ((auxVar 1 : Total L) ^ 1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 2) := by
    simp only [map_add, map_smul, corner_one_auxVar_pow hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv3 : dplus q 1 ((1 : L) • ((auxVar 1 : Total L) ^ 2))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_one_monoOne_two q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv4 : dplus q 2 ((-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2)
          + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 2)
        + (1 - q : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L)
            ^ 1)
        + (1 - q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L)
            ^ 1) := by
    simp only [map_add, map_smul, dplus_two_monoTwo_two_one q, dplus_two_monoTwo_one_two q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv5 : corner q 3 ((1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3
      : Total L) ^ 2)
          + (1 - q : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total
              L) ^ 1)
          + (1 - q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total
              L) ^ 1))
      = (-q ^ 2 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L)
          ^ 1) := by
    simp only [map_add, map_smul, corner_three_monoThree_two_one_one hq0 hq1,
        corner_three_monoThree_one_two_one hq0 hq1, corner_three_monoThree_one_one_two hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz6_0 : ((q : L) ^ (-1 : ℤ)) * (-q ^ 2 : L) = (-q : L) := by
    field_simp
    all_goals ring
  have hv6 : ((q : L) ^ (-1 : ℤ)) • ((-q ^ 2 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total
      L) ^ 1 * (auxVar 3 : Total L) ^ 1))
      = (-q : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)
          := by
    simp only [smul_add, smul_smul, hz6_0]
  have hv7 : (u : L) • ((-q : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3
      : Total L) ^ 1))
      = (-q*u : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^
          1) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : corner q 3 ((-q*u : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 *
      (auxVar 3 : Total L) ^ 1))
      = (q ^ 2*u : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3 * (auxVar 3 : Total L)
          ^ 1)
        + (-q ^ 2*u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2 * (auxVar 3
            : Total L) ^ 1) := by
    simp only [map_add, map_smul, corner_three_monoThree_three_one_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz9_0 : ((q : L) ^ (-2 : ℤ)) * (q ^ 2*u : L) = (u : L) := by
    field_simp
    all_goals ring
  have hz9_1 : ((q : L) ^ (-2 : ℤ)) * (-q ^ 2*u*(q - 1) : L) = (-u*(q - 1) : L) := by
    field_simp
    all_goals ring
  have hv9 : ((q : L) ^ (-2 : ℤ)) • ((q ^ 2*u : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total
      L) ^ 3 * (auxVar 3 : Total L) ^ 1)
          + (-q ^ 2*u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2 * (auxVar
              3 : Total L) ^ 1))
      = (u : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3 * (auxVar 3 : Total L) ^ 1)
        + (-u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 :
            Total L) ^ 1) := by
    simp only [smul_add, smul_smul, hz9_0, hz9_1]
  have hv10 : dminus q 3 ((u : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3 * (auxVar
      3 : Total L) ^ 1)
          + (-u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 :
              Total L) ^ 1))
      = (-u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total
          L) ^ 3))
        + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2
            : Total L) ^ 2)) := by
    simp only [map_add, map_smul, dminus_three_monoThree q, bopNat_one_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv11 : dminus q 2 ((-u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 *
      (auxVar 2 : Total L) ^ 3))
          + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar
              2 : Total L) ^ 2)))
      = (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 4) * ((auxVar 1 : Total L) ^ 2))
        + (u : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 3) * ((auxVar 1 : Total L) ^ 2))
        + (u*(q - 1) ^ 2 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^
            3)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo_C q, bopNat_two_elemSymm_one,
        bopNat_three_elemSymm_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath255 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11]

theorem partialSweepWord_alphaTwoPath256_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath256 (sepLevel 2 2) (1 : Total L)
      = (u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 4) * ((auxVar 1 : Total L) ^ 2))
        + (u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 3) * ((auxVar 1 : Total L) ^ 2))
        + (q*u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total
            L) ^ 3)) := by
  have hv1 : dplus q 0 ((1 : Total L))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_zero_monoZero q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv2 : dplus q 1 ((-1 : L) • ((auxVar 1 : Total L) ^ 1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_one_monoOne_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv3 : corner q 2 ((1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1))
      = (-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, corner_two_monoTwo_one_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz4_0 : ((q : L) ^ (-1 : ℤ)) * (-q : L) = (-1 : L) := by
    field_simp
    all_goals ring
  have hv4 : ((q : L) ^ (-1 : ℤ)) • ((-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^
      1))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1) := by
    simp only [smul_add, smul_smul, hz4_0]
  have hv5 : dminus q 2 ((-1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1))
      = (1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo q, bopNat_one_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv6 : dplus q 1 ((1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2)))
      = (-1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total
          L) ^ 2))
        + (q - 1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
            Total L) ^ 1))
        + (1 - q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) := by
    simp only [map_add, map_smul, dplus_one_monoOne_two_C_elemSymm_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : corner q 2 ((-1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1 *
      (auxVar 2 : Total L) ^ 2))
          + (q - 1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
              Total L) ^ 1))
          + (1 - q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
      = (q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L)
          ^ 1))
        + (q*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
    simp only [map_add, map_smul, corner_two_monoTwo_two_two hq0 hq1, corner_two_monoTwo_two_one_C
        hq0 hq1, corner_two_monoTwo_one_two_C hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : (u : L) • ((q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 *
      (auxVar 2 : Total L) ^ 1))
          + (q*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
      = (q*u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total
          L) ^ 1))
        + (q*u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv9 : corner q 2 ((q*u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 *
      (auxVar 2 : Total L) ^ 1))
          + (q*u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
      = (-q*u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total
          L) ^ 3))
        + (q*u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar
            2 : Total L) ^ 2))
        + (-q*u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) := by
    simp only [map_add, map_smul, corner_two_monoTwo_three_two hq0 hq1,
        corner_two_monoTwo_three_one_C hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz10_0 : ((q : L) ^ (-1 : ℤ)) * (-q*u : L) = (-u : L) := by
    field_simp
    all_goals ring
  have hz10_1 : ((q : L) ^ (-1 : ℤ)) * (q*u*(q - 1) : L) = (u*(q - 1) : L) := by
    field_simp
    all_goals ring
  have hz10_2 : ((q : L) ^ (-1 : ℤ)) * (-q*u*(q - 1) : L) = (-u*(q - 1) : L) := by
    field_simp
    all_goals ring
  have hv10 : ((q : L) ^ (-1 : ℤ)) • ((-q*u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 :
      Total L) ^ 2 * (auxVar 2 : Total L) ^ 3))
          + (q*u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 *
              (auxVar 2 : Total L) ^ 2))
          + (-q*u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3))
      = (-u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total
          L) ^ 3))
        + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2
            : Total L) ^ 2))
        + (-u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) := by
    simp only [smul_add, smul_smul, hz10_0, hz10_1, hz10_2]
  have hv11 : (u : L) • ((-u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 *
      (auxVar 2 : Total L) ^ 3))
          + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar
              2 : Total L) ^ 2))
          + (-u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3))
      = (-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
          Total L) ^ 3))
        + (u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 *
            (auxVar 2 : Total L) ^ 2))
        + (-u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv12 : dminus q 2 ((-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2
      * (auxVar 2 : Total L) ^ 3))
          + (u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 *
              (auxVar 2 : Total L) ^ 2))
          + (-u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3))
      = (u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 4) * ((auxVar 1 : Total L) ^ 2))
        + (u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 3) * ((auxVar 1 : Total L) ^ 2))
        + (q*u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total
            L) ^ 3)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo q, bopNat_three_one, dminus_two_monoTwo_C q,
        bopNat_two_elemSymm_one, bopNat_three_elemSymm_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath256 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12]

theorem partialSweepWord_alphaTwoPath266_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath266 (sepLevel 2 2) (1 : Total L)
      = (u ^ 3 : L) • (MvPolynomial.C (elemSymm L 4) * ((auxVar 1 : Total L) ^ 2))
        + (u ^ 3*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u ^ 3*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
  have hv1 : dplus q 0 ((1 : Total L))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_zero_monoZero q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv2 : corner q 1 ((-1 : L) • ((auxVar 1 : Total L) ^ 1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 2) := by
    simp only [map_add, map_smul, corner_one_auxVar_pow hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv3 : corner q 1 ((1 : L) • ((auxVar 1 : Total L) ^ 2))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 3) := by
    simp only [map_add, map_smul, corner_one_auxVar_pow hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv4 : (u : L) • ((-1 : L) • ((auxVar 1 : Total L) ^ 3))
      = (-u : L) • ((auxVar 1 : Total L) ^ 3) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv5 : dplus q 1 ((-u : L) • ((auxVar 1 : Total L) ^ 3))
      = (u : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3)
        + (-u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
        + (-u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_one_monoOne_three q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv6 : corner q 2 ((u : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3)
          + (-u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
          + (-u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1))
      = (-q*u : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, corner_two_monoTwo_three_one hq0 hq1, corner_two_monoTwo_two_two
        hq0 hq1, corner_two_monoTwo_one_three hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : (u : L) • ((-q*u : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1))
      = (-q*u ^ 2 : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : corner q 2 ((-q*u ^ 2 : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1))
      = (q*u ^ 2 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 4)
        + (-q*u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3)
        + (-q*u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2) := by
    simp only [map_add, map_smul, corner_two_monoTwo_four_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz9_0 : ((q : L) ^ (-1 : ℤ)) * (q*u ^ 2 : L) = (u ^ 2 : L) := by
    field_simp
    all_goals ring
  have hz9_1 : ((q : L) ^ (-1 : ℤ)) * (-q*u ^ 2*(q - 1) : L) = (-u ^ 2*(q - 1) : L) := by
    field_simp
    all_goals ring
  have hz9_2 : ((q : L) ^ (-1 : ℤ)) * (-q*u ^ 2*(q - 1) : L) = (-u ^ 2*(q - 1) : L) := by
    field_simp
    all_goals ring
  have hv9 : ((q : L) ^ (-1 : ℤ)) • ((q*u ^ 2 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total
      L) ^ 4)
          + (-q*u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3)
          + (-q*u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2))
      = (u ^ 2 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 4)
        + (-u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3)
        + (-u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2) := by
    simp only [smul_add, smul_smul, hz9_0, hz9_1, hz9_2]
  have hv10 : (u : L) • ((u ^ 2 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 4)
          + (-u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3)
          + (-u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2))
      = (u ^ 3 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 4)
        + (-u ^ 3*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3)
        + (-u ^ 3*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv11 : dminus q 2 ((u ^ 3 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 4)
          + (-u ^ 3*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3)
          + (-u ^ 3*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2))
      = (u ^ 3 : L) • (MvPolynomial.C (elemSymm L 4) * ((auxVar 1 : Total L) ^ 2))
        + (u ^ 3*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u ^ 3*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo q, bopNat_two_one, bopNat_three_one,
        bopNat_four_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath266 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11]

theorem partialSweepWord_alphaTwoPath345_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath345 (sepLevel 2 2) (1 : Total L)
      = (-u*(q - 1) ^ 2*(q + 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u*(q - 1)*(q + 2) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 :
            Total L) ^ 3))
        + (-u : L) • (MvPolynomial.C (elemSymm L 1 ^ 3) * ((auxVar 1 : Total L) ^ 3)) := by
  have hv1 : dplus q 0 ((1 : Total L))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_zero_monoZero q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv2 : dplus q 1 ((-1 : L) • ((auxVar 1 : Total L) ^ 1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_one_monoOne_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv3 : dplus q 2 ((1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)
          := by
    simp only [map_add, map_smul, dplus_two_monoTwo_one_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv4 : corner q 3 ((-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar
      3 : Total L) ^ 1))
      = (q ^ 2 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^
          1) := by
    simp only [map_add, map_smul, corner_three_monoThree_one_one_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz5_0 : ((q : L) ^ (-2 : ℤ)) * (q ^ 2 : L) = (1 : L) := by
    field_simp
    all_goals ring
  have hv5 : ((q : L) ^ (-2 : ℤ)) • ((q ^ 2 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L)
      ^ 1 * (auxVar 3 : Total L) ^ 1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)
          := by
    simp only [smul_add, smul_smul, hz5_0]
  have hv6 : dplus q 3 ((1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3
      : Total L) ^ 1))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 1
          * (auxVar 4 : Total L) ^ 1)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L)
            ^ 1 * (auxVar 4 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_three_monoThree_two_one_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : dminus q 4 ((-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar
      3 : Total L) ^ 1 * (auxVar 4 : Total L) ^ 1)
          + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total
              L) ^ 1 * (auxVar 4 : Total L) ^ 1))
      = (1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L)
          ^ 2 * (auxVar 3 : Total L) ^ 1))
        + (1 - q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
            Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)) := by
    simp only [map_add, map_smul, dminus_four_monoFour q, bopNat_one_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : dminus q 3 ((1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1 *
      (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 1))
          + (1 - q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
              Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)))
      = (1 - q : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 :
          Total L) ^ 2))
        + (-1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 :
            Total L) ^ 2))
        + ((q - 1) ^ 2 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar
            2 : Total L) ^ 1))
        + (q - 1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2
            : Total L) ^ 1)) := by
    simp only [map_add, map_smul, dminus_three_monoThree_C q, bopNat_one_elemSymm_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv9 : corner q 2 ((1 - q : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 1 *
      (auxVar 2 : Total L) ^ 2))
          + (-1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 :
              Total L) ^ 2))
          + ((q - 1) ^ 2 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 *
              (auxVar 2 : Total L) ^ 1))
          + (q - 1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar
              2 : Total L) ^ 1)))
      = (q*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 :
          Total L) ^ 1))
        + (q : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 :
            Total L) ^ 1)) := by
    simp only [map_add, map_smul, corner_two_monoTwo_two_one_C hq0 hq1,
        corner_two_monoTwo_one_two_C hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz10_0 : ((q : L) ^ (-1 : ℤ)) * (q*(q - 1) : L) = (q - 1 : L) := by
    field_simp
    all_goals ring
  have hz10_1 : ((q : L) ^ (-1 : ℤ)) * (q : L) = (1 : L) := by
    field_simp
    all_goals ring
  have hv10 : ((q : L) ^ (-1 : ℤ)) • ((q*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1
      : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1))
          + (q : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 :
              Total L) ^ 1)))
      = (q - 1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 :
          Total L) ^ 1))
        + (1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 :
            Total L) ^ 1)) := by
    simp only [smul_add, smul_smul, hz10_0, hz10_1]
  have hv11 : dminus q 2 ((q - 1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3
      * (auxVar 2 : Total L) ^ 1))
          + (1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 :
              Total L) ^ 1)))
      = (-(q - 1) ^ 2*(q + 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-(q - 1)*(q + 2) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 :
            Total L) ^ 3))
        + (-1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 3) * ((auxVar 1 : Total L) ^ 3)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo_C q, bopNat_one_elemSymm_one_sq,
        bopNat_one_elemSymm_two]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv12 : (u : L) • ((-(q - 1) ^ 2*(q + 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 :
      Total L) ^ 3))
          + (-(q - 1)*(q + 2) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 :
              Total L) ^ 3))
          + (-1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 3) * ((auxVar 1 : Total L) ^ 3)))
      = (-u*(q - 1) ^ 2*(q + 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u*(q - 1)*(q + 2) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 :
            Total L) ^ 3))
        + (-u : L) • (MvPolynomial.C (elemSymm L 1 ^ 3) * ((auxVar 1 : Total L) ^ 3)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath345 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12]

theorem partialSweepWord_alphaTwoPath346_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath346 (sepLevel 2 2) (1 : Total L)
      = (-q*u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-q*u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^
            3)) := by
  have hv1 : dplus q 0 ((1 : Total L))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_zero_monoZero q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv2 : dplus q 1 ((-1 : L) • ((auxVar 1 : Total L) ^ 1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_one_monoOne_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv3 : dplus q 2 ((1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)
          := by
    simp only [map_add, map_smul, dplus_two_monoTwo_one_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv4 : corner q 3 ((-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar
      3 : Total L) ^ 1))
      = (q ^ 2 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^
          1) := by
    simp only [map_add, map_smul, corner_three_monoThree_one_one_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv5 : corner q 3 ((q ^ 2 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 *
      (auxVar 3 : Total L) ^ 1))
      = (-q ^ 3 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L)
          ^ 1) := by
    simp only [map_add, map_smul, corner_three_monoThree_two_one_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz6_0 : ((q : L) ^ (-2 : ℤ)) * (-q ^ 3 : L) = (-q : L) := by
    field_simp
    all_goals ring
  have hv6 : ((q : L) ^ (-2 : ℤ)) • ((-q ^ 3 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total
      L) ^ 2 * (auxVar 3 : Total L) ^ 1))
      = (-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 1)
          := by
    simp only [smul_add, smul_smul, hz6_0]
  have hv7 : dminus q 3 ((-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar
      3 : Total L) ^ 1))
      = (q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L)
          ^ 2)) := by
    simp only [map_add, map_smul, dminus_three_monoThree q, bopNat_one_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : dminus q 2 ((q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 *
      (auxVar 2 : Total L) ^ 2)))
      = (q*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 2))
        + (q : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 2)) :=
            by
    simp only [map_add, map_smul, dminus_two_monoTwo_C q, bopNat_two_elemSymm_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv9 : corner q 1 ((q*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^
      2))
          + (q : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 2)))
      = (-q*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-q : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)) :=
            by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv10 : (u : L) • ((-q*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L)
      ^ 3))
          + (-q : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)))
      = (-q*u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-q*u : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 3))
            := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv11 : (u : L) • ((-q*u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total
      L) ^ 3))
          + (-q*u : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^
              3)))
      = (-q*u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-q*u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^
            3)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath346 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11]

theorem partialSweepWord_alphaTwoPath355_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath355 (sepLevel 2 2) (1 : Total L)
      = (-u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^
            3)) := by
  have hv1 : dplus q 0 ((1 : Total L))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_zero_monoZero q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv2 : dplus q 1 ((-1 : L) • ((auxVar 1 : Total L) ^ 1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_one_monoOne_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv3 : corner q 2 ((1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1))
      = (-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, corner_two_monoTwo_one_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv4 : corner q 2 ((-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1))
      = (q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) := by
    simp only [map_add, map_smul, corner_two_monoTwo_two_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz5_0 : ((q : L) ^ (-1 : ℤ)) * (q : L) = (1 : L) := by
    field_simp
    all_goals ring
  have hv5 : ((q : L) ^ (-1 : ℤ)) • ((q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^
      2))
      = (1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) := by
    simp only [smul_add, smul_smul, hz5_0]
  have hv6 : dplus q 2 ((1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 2)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L)
            ^ 2)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L)
            ^ 1) := by
    simp only [map_add, map_smul, dplus_two_monoTwo_two_two q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : dminus q 3 ((-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar
      3 : Total L) ^ 2)
          + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total
              L) ^ 2)
          + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total
              L) ^ 1))
      = (-1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total
          L) ^ 2))
        + (q - 1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
            Total L) ^ 1))
        + (1 - q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
            Total L) ^ 2)) := by
    simp only [map_add, map_smul, dminus_three_monoThree q, bopNat_one_one, bopNat_two_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : (u : L) • ((-1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 1 *
      (auxVar 2 : Total L) ^ 2))
          + (q - 1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
              Total L) ^ 1))
          + (1 - q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
              Total L) ^ 2)))
      = (-u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total
          L) ^ 2))
        + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2
            : Total L) ^ 1))
        + (-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2
            : Total L) ^ 2)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv9 : corner q 2 ((-u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 1 *
      (auxVar 2 : Total L) ^ 2))
          + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2 * (auxVar
              2 : Total L) ^ 1))
          + (-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar
              2 : Total L) ^ 2)))
      = (q*u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total
          L) ^ 1))
        + (q*u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar
            2 : Total L) ^ 2)) := by
    simp only [map_add, map_smul, corner_two_monoTwo_two_two_C hq0 hq1,
        corner_two_monoTwo_two_one_C hq0 hq1, corner_two_monoTwo_one_two_C hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz10_0 : ((q : L) ^ (-1 : ℤ)) * (q*u : L) = (u : L) := by
    field_simp
    all_goals ring
  have hz10_1 : ((q : L) ^ (-1 : ℤ)) * (q*u*(q - 1) : L) = (u*(q - 1) : L) := by
    field_simp
    all_goals ring
  have hv10 : ((q : L) ^ (-1 : ℤ)) • ((q*u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 :
      Total L) ^ 3 * (auxVar 2 : Total L) ^ 1))
          + (q*u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 *
              (auxVar 2 : Total L) ^ 2)))
      = (u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L)
          ^ 1))
        + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2
            : Total L) ^ 2)) := by
    simp only [smul_add, smul_smul, hz10_0, hz10_1]
  have hv11 : dminus q 2 ((u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3 *
      (auxVar 2 : Total L) ^ 1))
          + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar
              2 : Total L) ^ 2)))
      = (-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)) :=
            by
    simp only [map_add, map_smul, dminus_two_monoTwo_C q, bopNat_two_elemSymm_one,
        bopNat_one_elemSymm_two]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv12 : (u : L) • ((-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L)
      ^ 3))
          + (-u : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)))
      = (-u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^
            3)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath355 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12]

theorem partialSweepWord_alphaTwoPath356_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath356 (sepLevel 2 2) (1 : Total L)
      = (-u ^ 3*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^
            3)) := by
  have hv1 : dplus q 0 ((1 : Total L))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_zero_monoZero q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv2 : dplus q 1 ((-1 : L) • ((auxVar 1 : Total L) ^ 1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_one_monoOne_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv3 : dplus q 2 ((1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)
          := by
    simp only [map_add, map_smul, dplus_two_monoTwo_one_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv4 : corner q 3 ((-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar
      3 : Total L) ^ 1))
      = (q ^ 2 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^
          1) := by
    simp only [map_add, map_smul, corner_three_monoThree_one_one_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz5_0 : ((q : L) ^ (-1 : ℤ)) * (q ^ 2 : L) = (q : L) := by
    field_simp
    all_goals ring
  have hv5 : ((q : L) ^ (-1 : ℤ)) • ((q ^ 2 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L)
      ^ 1 * (auxVar 3 : Total L) ^ 1))
      = (q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)
          := by
    simp only [smul_add, smul_smul, hz5_0]
  have hv6 : dminus q 3 ((q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3
      : Total L) ^ 1))
      = (-q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total
          L) ^ 1)) := by
    simp only [map_add, map_smul, dminus_three_monoThree q, bopNat_one_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : corner q 2 ((-q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 *
      (auxVar 2 : Total L) ^ 1)))
      = (q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L)
          ^ 2)) := by
    simp only [map_add, map_smul, corner_two_monoTwo_two_one_C hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz8_0 : ((q : L) ^ (-1 : ℤ)) * (q : L) = (1 : L) := by
    field_simp
    all_goals ring
  have hv8 : ((q : L) ^ (-1 : ℤ)) • ((q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total
      L) ^ 2 * (auxVar 2 : Total L) ^ 2)))
      = (1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L)
          ^ 2)) := by
    simp only [smul_add, smul_smul, hz8_0]
  have hv9 : dminus q 2 ((1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 *
      (auxVar 2 : Total L) ^ 2)))
      = (q - 1 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 2))
        + (1 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 2)) :=
            by
    simp only [map_add, map_smul, dminus_two_monoTwo_C q, bopNat_two_elemSymm_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv10 : (u : L) • ((q - 1 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 2))
          + (1 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 2)))
      = (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 2))
        + (u : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 2)) :=
            by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv11 : corner q 1 ((u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L)
      ^ 2))
          + (u : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 2)))
      = (-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)) :=
            by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv12 : (u : L) • ((-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L)
      ^ 3))
          + (-u : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)))
      = (-u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^
            3)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv13 : (u : L) • ((-u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total
      L) ^ 3))
          + (-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^
              3)))
      = (-u ^ 3*(q - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) * ((auxVar 1 : Total L) ^
            3)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath356 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13]

theorem partialSweepWord_alphaTwoPath366_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath366 (sepLevel 2 2) (1 : Total L)
      = (-u ^ 4 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u ^ 4*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
  have hv1 : dplus q 0 ((1 : Total L))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_zero_monoZero q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv2 : corner q 1 ((-1 : L) • ((auxVar 1 : Total L) ^ 1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 2) := by
    simp only [map_add, map_smul, corner_one_auxVar_pow hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv3 : dplus q 1 ((1 : L) • ((auxVar 1 : Total L) ^ 2))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_one_monoOne_two q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv4 : corner q 2 ((-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2)
          + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1))
      = (q : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, corner_two_monoTwo_two_one hq0 hq1, corner_two_monoTwo_one_two
        hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv5 : (u : L) • ((q : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1))
      = (q*u : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv6 : corner q 2 ((q*u : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1))
      = (-q*u : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + (q*u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
    simp only [map_add, map_smul, corner_two_monoTwo_three_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz7_0 : ((q : L) ^ (-1 : ℤ)) * (-q*u : L) = (-u : L) := by
    field_simp
    all_goals ring
  have hz7_1 : ((q : L) ^ (-1 : ℤ)) * (q*u*(q - 1) : L) = (u*(q - 1) : L) := by
    field_simp
    all_goals ring
  have hv7 : ((q : L) ^ (-1 : ℤ)) • ((-q*u : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L)
      ^ 3)
          + (q*u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
      = (-u : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
    simp only [smul_add, smul_smul, hz7_0, hz7_1]
  have hv8 : dminus q 2 ((-u : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
          + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
      = (u : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 2))
        + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo q, bopNat_two_one, bopNat_three_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv9 : (u : L) • ((u : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 2))
          + (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)))
      = (u ^ 2 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 2))
        + (u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv10 : corner q 1 ((u ^ 2 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 2))
          + (u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)))
      = (-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv11 : (u : L) • ((-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
          + (-u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)))
      = (-u ^ 3 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u ^ 3*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv12 : (u : L) • ((-u ^ 3 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
          + (-u ^ 3*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)))
      = (-u ^ 4 : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L) ^ 3))
        + (-u ^ 4*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath366 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12]

end Values

end HJO.Mellit

end
