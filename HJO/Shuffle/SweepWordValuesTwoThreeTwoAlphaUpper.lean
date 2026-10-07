/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWordsTwoThreeTwoAlpha
public import HJO.Shuffle.SweepMonomialValuesTwoThreeTwo

/-! # The sweep words of first height at least `4` of the `4 × 6` rectangle at `c_{(2)}`

The nine of the nineteen values of `HJO/Shuffle/SweepWordValuesTwoThreeTwoAlpha.lean` whose
path has first height `ŷ_1 ≥ 4`: the words `alphaTwoPath445` to `alphaTwoPath666`. The method,
the operator tables and the genericity are those described there; the ten words of first height
`2` or `3` are in that file.

## References

Built on `HJO.Mellit.sweepOperator`, `HJO.Mellit.partialSweepWord`, `HJO.Sweep.dplus`,
`HJO.Sweep.dminus`, `HJO.Sweep.corner` and `HJO.Sym.Bop`. -/

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

theorem partialSweepWord_alphaTwoPath445_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath445 (sepLevel 2 2) (1 : Total L)
      = (u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4))
        + (u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 4)) := by
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
  have hz5_0 : ((q : L) ^ (-1 : ℤ)) * (q : L) = (1 : L) := by
    field_simp
    all_goals ring
  have hv5 : ((q : L) ^ (-1 : ℤ)) • ((q : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^
      1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1) := by
    simp only [smul_add, smul_smul, hz5_0]
  have hv6 : dplus q 2 ((1 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1))
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3 * (auxVar 3 : Total L) ^ 1)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L)
            ^ 1)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L)
            ^ 1) := by
    simp only [map_add, map_smul, dplus_two_monoTwo_three_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : (u : L) • ((-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3 * (auxVar 3
      : Total L) ^ 1)
          + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total
              L) ^ 1)
          + (q - 1 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total
              L) ^ 1))
      = (-u : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3 * (auxVar 3 : Total L) ^ 1)
        + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 :
            Total L) ^ 1)
        + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 :
            Total L) ^ 1) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : dminus q 3 ((-u : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3 * (auxVar
      3 : Total L) ^ 1)
          + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 :
              Total L) ^ 1)
          + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 :
              Total L) ^ 1))
      = (u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L)
          ^ 3))
        + (-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2
            : Total L) ^ 2))
        + (-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2
            : Total L) ^ 1)) := by
    simp only [map_add, map_smul, dminus_three_monoThree q, bopNat_one_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv9 : corner q 2 ((u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1 *
      (auxVar 2 : Total L) ^ 3))
          + (-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar
              2 : Total L) ^ 2))
          + (-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar
              2 : Total L) ^ 1)))
      = (-q*u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total
          L) ^ 1)) := by
    simp only [map_add, map_smul, corner_two_monoTwo_three_one_C hq0 hq1,
        corner_two_monoTwo_two_two_C hq0 hq1, corner_two_monoTwo_one_three_C hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz10_0 : ((q : L) ^ (-1 : ℤ)) * (-q*u : L) = (-u : L) := by
    field_simp
    all_goals ring
  have hv10 : ((q : L) ^ (-1 : ℤ)) • ((-q*u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 :
      Total L) ^ 4 * (auxVar 2 : Total L) ^ 1)))
      = (-u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total
          L) ^ 1)) := by
    simp only [smul_add, smul_smul, hz10_0]
  have hv11 : dminus q 2 ((-u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4 *
      (auxVar 2 : Total L) ^ 1)))
      = (u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4))
        + (u : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 4)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo_C q, bopNat_one_elemSymm_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv12 : (u : L) • ((u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^
      4))
          + (u : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 4)))
      = (u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4))
        + (u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath445 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12]

theorem partialSweepWord_alphaTwoPath446_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath446 (sepLevel 2 2) (1 : Total L)
      = (q*u ^ 3 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
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
  have hv5 : (q : L) • ((-1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1))
      = (-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv6 : corner q 2 ((-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1))
      = (q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) := by
    simp only [map_add, map_smul, corner_two_monoTwo_two_one hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : corner q 2 ((q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
      = (-q ^ 2 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
    simp only [map_add, map_smul, corner_two_monoTwo_two_two hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz8_0 : ((q : L) ^ (-1 : ℤ)) * (-q ^ 2 : L) = (-q : L) := by
    field_simp
    all_goals ring
  have hv8 : ((q : L) ^ (-1 : ℤ)) • ((-q ^ 2 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total
      L) ^ 2))
      = (-q : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
    simp only [smul_add, smul_smul, hz8_0]
  have hv9 : (u : L) • ((-q : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
      = (-q*u : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv10 : dminus q 2 ((-q*u : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
      = (-q*u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo q, bopNat_two_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv11 : corner q 1 ((-q*u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)))
      = (q*u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv12 : (u : L) • ((q*u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)))
      = (q*u ^ 2 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv13 : (u : L) • ((q*u ^ 2 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^
      4)))
      = (q*u ^ 3 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath446 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13]

theorem partialSweepWord_alphaTwoPath455_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath455 (sepLevel 2 2) (1 : Total L)
      = (u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 4)) := by
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
  have hv6 : corner q 1 ((1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2)))
      = (-1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3)) := by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : dplus q 1 ((-1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3)))
      = (1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L)
          ^ 3))
        + (1 - q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
            Total L) ^ 2))
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + (1 - q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 :
            Total L) ^ 1))
        + (-(q - 1) ^ 2 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
    simp only [map_add, map_smul, dplus_one_monoOne_three_C_elemSymm_one q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : (u : L) • ((1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1 *
      (auxVar 2 : Total L) ^ 3))
          + (1 - q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
              Total L) ^ 2))
          + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
          + (1 - q : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 :
              Total L) ^ 1))
          + (-(q - 1) ^ 2 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
      = (u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L)
          ^ 3))
        + (-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2
            : Total L) ^ 2))
        + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + (-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2
            : Total L) ^ 1))
        + (-u*(q - 1) ^ 2 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv9 : (u : L) • ((u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1 *
      (auxVar 2 : Total L) ^ 3))
          + (-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar
              2 : Total L) ^ 2))
          + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
          + (-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar
              2 : Total L) ^ 1))
          + (-u*(q - 1) ^ 2 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
      = (u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 :
          Total L) ^ 3))
        + (-u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 *
            (auxVar 2 : Total L) ^ 2))
        + (u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + (-u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 *
            (auxVar 2 : Total L) ^ 1))
        + (-u ^ 2*(q - 1) ^ 2 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv10 : corner q 2 ((u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1
      * (auxVar 2 : Total L) ^ 3))
          + (-u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 *
              (auxVar 2 : Total L) ^ 2))
          + (u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
          + (-u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 *
              (auxVar 2 : Total L) ^ 1))
          + (-u ^ 2*(q - 1) ^ 2 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
      = (-q*u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4 * (auxVar 2 :
          Total L) ^ 1))
        + (-q*u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2) := by
    simp only [map_add, map_smul, corner_two_monoTwo_three_two hq0 hq1,
        corner_two_monoTwo_three_one_C hq0 hq1, corner_two_monoTwo_two_three hq0 hq1,
        corner_two_monoTwo_two_two_C hq0 hq1, corner_two_monoTwo_one_three_C hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz11_0 : ((q : L) ^ (-1 : ℤ)) * (-q*u ^ 2 : L) = (-u ^ 2 : L) := by
    field_simp
    all_goals ring
  have hz11_1 : ((q : L) ^ (-1 : ℤ)) * (-q*u ^ 2*(q - 1) : L) = (-u ^ 2*(q - 1) : L) := by
    field_simp
    all_goals ring
  have hv11 : ((q : L) ^ (-1 : ℤ)) • ((-q*u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1
      : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1))
          + (-q*u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2))
      = (-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4 * (auxVar 2 :
          Total L) ^ 1))
        + (-u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2) := by
    simp only [smul_add, smul_smul, hz11_0, hz11_1]
  have hv12 : dminus q 2 ((-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4
      * (auxVar 2 : Total L) ^ 1))
          + (-u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2))
      = (u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 4)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo q, bopNat_two_one, dminus_two_monoTwo_C q,
        bopNat_one_elemSymm_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv13 : (u : L) • ((u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^
      4)))
      = (u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath455 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13]

theorem partialSweepWord_alphaTwoPath456_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath456 (sepLevel 2 2) (1 : Total L)
      = (u ^ 4*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4))
        + (u ^ 4 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 4)) := by
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
  have hv6 : dminus q 3 ((1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3
      : Total L) ^ 1))
      = (-1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total
          L) ^ 1)) := by
    simp only [map_add, map_smul, dminus_three_monoThree q, bopNat_one_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : dminus q 2 ((-1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 *
      (auxVar 2 : Total L) ^ 1)))
      = (q - 1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2))
        + (1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 2)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo_C q, bopNat_one_elemSymm_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : corner q 1 ((q - 1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2))
          + (1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 2)))
      = (1 - q : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3))
        + (-1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 3)) := by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv9 : (u : L) • ((1 - q : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3))
          + (-1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 3)))
      = (-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3))
        + (-u : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 3)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv10 : (u : L) • ((-u*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L)
      ^ 3))
          + (-u : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 3)))
      = (-u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3))
        + (-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 3)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv11 : corner q 1 ((-u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 :
      Total L) ^ 3))
          + (-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 3)))
      = (u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4))
        + (u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 4)) := by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv12 : (u : L) • ((u ^ 2*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total
      L) ^ 4))
          + (u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 4)))
      = (u ^ 3*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4))
        + (u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv13 : (u : L) • ((u ^ 3*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total
      L) ^ 4))
          + (u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 4)))
      = (u ^ 4*(q - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4))
        + (u ^ 4 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath456 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13]

theorem partialSweepWord_alphaTwoPath466_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath466 (sepLevel 2 2) (1 : Total L)
      = (u ^ 5 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
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
  have hv6 : dminus q 2 ((1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
      = (1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo q, bopNat_two_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : (u : L) • ((1 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2)))
      = (u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : corner q 1 ((u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 2)))
      = (-u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)) := by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv9 : (u : L) • ((-u : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)))
      = (-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv10 : (u : L) • ((-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^
      3)))
      = (-u ^ 3 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 3)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv11 : corner q 1 ((-u ^ 3 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^
      3)))
      = (u ^ 3 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv12 : (u : L) • ((u ^ 3 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)))
      = (u ^ 4 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv13 : (u : L) • ((u ^ 4 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)))
      = (u ^ 5 : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath466 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13]

theorem partialSweepWord_alphaTwoPath555_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath555 (sepLevel 2 2) (1 : Total L)
      = (-u ^ 4 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 5)) := by
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
  have hv5 : corner q 1 ((-u : L) • ((auxVar 1 : Total L) ^ 3))
      = (u : L) • ((auxVar 1 : Total L) ^ 4) := by
    simp only [map_add, map_smul, corner_one_auxVar_pow hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv6 : dplus q 1 ((u : L) • ((auxVar 1 : Total L) ^ 4))
      = (-u : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 4)
        + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, dplus_one_monoOne_four q]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : (u : L) • ((-u : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 4)
          + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
          + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
          + (u*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1))
      = (-u ^ 2 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 4)
        + (u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + (u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        + (u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : (u : L) • ((-u ^ 2 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 4)
          + (u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
          + (u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
          + (u ^ 2*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1))
      = (-u ^ 3 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 4)
        + (u ^ 3*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + (u ^ 3*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        + (u ^ 3*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv9 : corner q 2 ((-u ^ 3 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 4)
          + (u ^ 3*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
          + (u ^ 3*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
          + (u ^ 3*(q - 1) : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1))
      = (q*u ^ 3 : L) • ((auxVar 1 : Total L) ^ 5 * (auxVar 2 : Total L) ^ 1) := by
    simp only [map_add, map_smul, corner_two_monoTwo_four_one hq0 hq1, corner_two_monoTwo_three_two
        hq0 hq1, corner_two_monoTwo_two_three hq0 hq1, corner_two_monoTwo_one_four hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hz10_0 : ((q : L) ^ (-1 : ℤ)) * (q*u ^ 3 : L) = (u ^ 3 : L) := by
    field_simp
    all_goals ring
  have hv10 : ((q : L) ^ (-1 : ℤ)) • ((q*u ^ 3 : L) • ((auxVar 1 : Total L) ^ 5 * (auxVar 2 : Total
      L) ^ 1))
      = (u ^ 3 : L) • ((auxVar 1 : Total L) ^ 5 * (auxVar 2 : Total L) ^ 1) := by
    simp only [smul_add, smul_smul, hz10_0]
  have hv11 : dminus q 2 ((u ^ 3 : L) • ((auxVar 1 : Total L) ^ 5 * (auxVar 2 : Total L) ^ 1))
      = (-u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 5)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo q, bopNat_one_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv12 : (u : L) • ((-u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^
      5)))
      = (-u ^ 4 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 5)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath555 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12]

theorem partialSweepWord_alphaTwoPath556_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath556 (sepLevel 2 2) (1 : Total L)
      = (-u ^ 5 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 5)) := by
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
  have hz5_0 : ((q : L) ^ (-1 : ℤ)) * (q : L) = (1 : L) := by
    field_simp
    all_goals ring
  have hv5 : ((q : L) ^ (-1 : ℤ)) • ((q : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^
      1))
      = (1 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1) := by
    simp only [smul_add, smul_smul, hz5_0]
  have hv6 : (u : L) • ((1 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1))
      = (u : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : dminus q 2 ((u : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1))
      = (-u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3)) := by
    simp only [map_add, map_smul, dminus_two_monoTwo q, bopNat_one_one]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : corner q 1 ((-u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3)))
      = (u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4)) := by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv9 : (u : L) • ((u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4)))
      = (u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv10 : (u : L) • ((u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4)))
      = (u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv11 : corner q 1 ((u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^
      4)))
      = (-u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 5)) := by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv12 : (u : L) • ((-u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^
      5)))
      = (-u ^ 4 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 5)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv13 : (u : L) • ((-u ^ 4 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^
      5)))
      = (-u ^ 5 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 5)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath556 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13]

theorem partialSweepWord_alphaTwoPath566_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath566 (sepLevel 2 2) (1 : Total L)
      = (-u ^ 6 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 5)) := by
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
  have hv6 : corner q 1 ((1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2)))
      = (-1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3)) := by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : (u : L) • ((-1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3)))
      = (-u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : (u : L) • ((-u : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3)))
      = (-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv9 : corner q 1 ((-u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^
      3)))
      = (u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4)) := by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv10 : (u : L) • ((u ^ 2 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4)))
      = (u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv11 : (u : L) • ((u ^ 3 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4)))
      = (u ^ 4 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 4)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv12 : corner q 1 ((u ^ 4 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^
      4)))
      = (-u ^ 4 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 5)) := by
    simp only [map_add, map_smul, corner_one_C_mul_auxVar_pow hq0 hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv13 : (u : L) • ((-u ^ 4 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^
      5)))
      = (-u ^ 5 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 5)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv14 : (u : L) • ((-u ^ 5 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^
      5)))
      = (-u ^ 6 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 5)) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath566 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14]

theorem partialSweepWord_alphaTwoPath666_apply_one (hq1 : q ≠ 1) :
    partialSweepWord q u alphaTwoPath666 (sepLevel 2 2) (1 : Total L)
      = (u ^ 7 : L) • ((auxVar 1 : Total L) ^ 6) := by
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
  have hv5 : corner q 1 ((-u : L) • ((auxVar 1 : Total L) ^ 3))
      = (u : L) • ((auxVar 1 : Total L) ^ 4) := by
    simp only [map_add, map_smul, corner_one_auxVar_pow hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv6 : (u : L) • ((u : L) • ((auxVar 1 : Total L) ^ 4))
      = (u ^ 2 : L) • ((auxVar 1 : Total L) ^ 4) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv7 : (u : L) • ((u ^ 2 : L) • ((auxVar 1 : Total L) ^ 4))
      = (u ^ 3 : L) • ((auxVar 1 : Total L) ^ 4) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv8 : corner q 1 ((u ^ 3 : L) • ((auxVar 1 : Total L) ^ 4))
      = (-u ^ 3 : L) • ((auxVar 1 : Total L) ^ 5) := by
    simp only [map_add, map_smul, corner_one_auxVar_pow hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv9 : (u : L) • ((-u ^ 3 : L) • ((auxVar 1 : Total L) ^ 5))
      = (-u ^ 4 : L) • ((auxVar 1 : Total L) ^ 5) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv10 : (u : L) • ((-u ^ 4 : L) • ((auxVar 1 : Total L) ^ 5))
      = (-u ^ 5 : L) • ((auxVar 1 : Total L) ^ 5) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv11 : corner q 1 ((-u ^ 5 : L) • ((auxVar 1 : Total L) ^ 5))
      = (u ^ 5 : L) • ((auxVar 1 : Total L) ^ 6) := by
    simp only [map_add, map_smul, corner_one_auxVar_pow hq1]
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv12 : (u : L) • ((u ^ 5 : L) • ((auxVar 1 : Total L) ^ 6))
      = (u ^ 6 : L) • ((auxVar 1 : Total L) ^ 6) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  have hv13 : (u : L) • ((u ^ 6 : L) • ((auxVar 1 : Total L) ^ 6))
      = (u ^ 7 : L) • ((auxVar 1 : Total L) ^ 6) := by
    all_goals try simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add,
      map_sub, map_neg, map_mul, map_one, map_pow, map_ofNat]
    all_goals ring
  rw [partialSweepWord_alphaTwoPath666 q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13]

end Values

end HJO.Mellit

end
