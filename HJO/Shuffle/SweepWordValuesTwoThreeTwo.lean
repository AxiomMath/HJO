/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWordsTwoThreeTwo

/-! # The four sweep words of the `4 × 6` rectangle at `c_{(1,1)}`, evaluated on the vacuum

`HJO/Shuffle/SweepWordsTwoThreeTwo.lean` writes each of the four words as an explicit product
of event operators. This file applies each product to `1` and reads off the value, using the
operator table of `HJO/Shuffle/SweepOperatorValuesTwoThree.lean`.

## What each word contributes

| path | value |
| --- | --- |
| `(0,2,3,5,6)` | `qe_1^2y_1^2y_2^2 + q(q-1)e_2y_1^2y_2^2` |
| `(0,2,3,6,6)` | `-que_1y_1^2y_2^3 + q(q-1)ue_1y_1^3y_2^2` |
| `(0,3,3,5,6)` | `-q^2ue_1y_1^3y_2^2` |
| `(0,3,3,6,6)` | `qu^2y_1^3y_2^3` |

Only the first reaches width `4`, and only the first produces an `e_2` — the `e_2` comes from the
displacement `B_1(e_1)` of `HJO.Sweep.dminus_auxVar_succ_mul_C_elemSymm_one_mul`, which is the one
`d_-` in the four words that meets a symmetric-function coefficient.

## Genericity

`q ≠ 0` and `q ≠ 1` throughout and no more; `u` is unrestricted here, entering only through the
type-`E` events, which multiply by it. Both exclusions are irreducible and neither is bookkeeping:
`q ≠ 1` is `HJO.Sweep.corner`'s `(q-1)^{-1}`, and `q ≠ 0` is needed twice over — for the negative
powers `q^{-a_{P̂}(P)}` that `HJO.Mellit.sweepOperator` attaches to every type-`C` event to be
inverses at all, and for the inverted braid letters of the corner's train identity.

## References

This file evaluates `HJO.Mellit.sweepOperator` and `HJO.Mellit.partialSweepWord`, in terms of
`HJO.Sweep.dplus`, `HJO.Sweep.dminus` and `HJO.Sweep.corner`.
-/

@[expose] public section

namespace HJO.Mellit

open Finset HJO.Paths HJO.Sweep HJO.Sym

section Values

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### Two scalar manipulations the type-`C` events need -/

omit [Algebra ℚ L] in
/-- A `Λ`-coefficient scalar read as the module action. -/
theorem neg_scal_mul_eq_smul (x : L) (F : Total L) : -(scal x * F) = (-x) • F := by
  rw [scal_mul_eq_smul_total, neg_smul]

omit [Algebra ℚ L] in
/-- The `q^{-a}` of a type-`C` event absorbed into the `Λ`-coefficient the corner emitted. -/
theorem smul_scal_mul (x y : L) (F : Total L) : x • (scal y * F) = scal (x * y) * F := by
  rw [smul_eq_scal_mul, ← mul_assoc, ← scal_mul]

omit [Algebra ℚ L] in
/-- An event operator is `𝕜`-linear, so a scalar coefficient passes it. -/
theorem End_apply_scal_mul (f : Module.End L (Total L)) (x : L) (F : Total L) :
    f (scal x * F) = scal x * f F := by
  rw [scal_mul_eq_smul_total, map_smul, scal_mul_eq_smul_total]

/-! ### The word of `(0,2,3,5,6)`: `qe_1^2y_1^2y_2^2 + q(q-1)e_2y_1^2y_2^2` -/

/-- **The `(0,2,3,5,6)` path contributes `qe_1^2y_1^2y_2^2 + q(q-1)e_2y_1^2y_2^2`.**

The only one of the four words that reaches width `4`, and the only one whose `d_-` meets a
symmetric-function coefficient: the second lowering acts on `e_1y_1^2y_2^2y_3` and the displacement
`B_1(e_1) = -e_1^2 + (1-q)e_2` of `HJO.Sym.bop_one_elemSymm_one` is where the `e_2` of the whole
instance comes from.

The two width-`4` corners are where the doubled bottom variable shows: the first emits `q^3`
(`HJO.Sweep.corner_four_prod'`) and the second only `q^2`
(`HJO.Sweep.corner_four_auxVar_one_mul_prod`), because the train's cascade stops one step early on
`y_1·y_1⋯y_4`. Together with the two `q^{-a}` the type-`C` events carry, that is what leaves a
single `q` in front. -/
theorem partialSweepWord_baseTwoThreeTwoA_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u baseTwoThreeTwoA (sepLevel 2 2) (1 : Total L)
      = scal q * (MvPolynomial.C (elemSymm L 1 * elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
        + scal (q * (q - 1)) * (MvPolynomial.C (elemSymm L 2)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)) := by
  have hmem3p : ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * auxVar 3) ∈ piece L 3 := by
    have h := monoThree_mem_piece (L := L) 2 2 1
    rwa [pow_one] at h
  have hmem3a : ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * auxVar 3)
      ∈ auxSubalg L := by
    have h := monoThree_mem_auxSubalg (L := L) 2 2 1
    rwa [pow_one] at h
  have hmem2p : ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) ∈ piece L 2 :=
    monoTwo_mem_piece 2 2
  have hmem2a : ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) ∈ auxSubalg L :=
    monoTwo_mem_auxSubalg 2 2
  have hv1 : dplus q 0 (1 : Total L) = -(auxVar 1 : Total L) := dplus_zero_one q
  have hv2 : dplus q 1 (-(auxVar 1 : Total L)) = (auxVar 1 : Total L) * auxVar 2 := by
    have h := dplus_auxVarProd (L := L) q 1
    rw [auxVarProd_one, show (1 : ℕ) + 1 = 2 from rfl, auxVarProd_two',
      show (MvPolynomial.X 0 : Total L) = auxVar 1 from rfl] at h
    rw [map_neg, h, neg_neg]
  have hv3 : dplus q 2 ((auxVar 1 : Total L) * auxVar 2)
      = -((auxVar 1 : Total L) * auxVar 2 * auxVar 3) := by
    have h := dplus_auxVarProd (L := L) q 2
    rwa [show (2 : ℕ) + 1 = 3 from rfl, auxVarProd_two', auxVarProd_three'] at h
  have hv4 : dplus q 3 (-((auxVar 1 : Total L) * auxVar 2 * auxVar 3))
      = (auxVar 1 : Total L) * auxVar 2 * auxVar 3 * auxVar 4 := by
    have h := dplus_auxVarProd (L := L) q 3
    rw [show (3 : ℕ) + 1 = 4 from rfl, auxVarProd_three', auxVarProd_four'] at h
    rw [map_neg, h, neg_neg]
  have hv5 : ((q : L) ^ (-1 : ℤ)) • corner q 4 ((auxVar 1 : Total L) * auxVar 2 * auxVar 3
        * auxVar 4)
      = (-(q ^ 2) : L) • ((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3 * auxVar 4) := by
    have hc : ((q : L) ^ (-1 : ℤ)) * -(q ^ 3) = -(q ^ 2) := by field_simp
    rw [corner_four_prod' hq0 hq1, neg_scal_mul_eq_smul, smul_smul, hc]
  have hv6 : ((q : L) ^ (-3 : ℤ)) • corner q 4 ((-(q ^ 2) : L)
        • ((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3 * auxVar 4))
      = (q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * auxVar 3 * auxVar 4) := by
    have hc : ((q : L) ^ (-3 : ℤ) * -(q ^ 2)) * -(q ^ 2) = q := by field_simp
    rw [map_smul, corner_four_auxVar_one_mul_prod hq0 hq1, neg_scal_mul_eq_smul, smul_smul,
      smul_smul, hc]
  have hv7 : dminus q 4 ((q : L)
        • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * auxVar 3 * auxVar 4))
      = (-q : L) • (MvPolynomial.C (elemSymm L 1)
          * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * auxVar 3)) := by
    rw [show ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * auxVar 3 * auxVar 4)
        = (auxVar (3 + 1) : Total L)
          * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * auxVar 3) from by
        norm_num; ring,
      map_smul, dminus_auxVar_succ_mul q 3 hmem3p hmem3a, smul_neg, ← neg_smul]
  have hv8 : dminus q 3 ((-q : L) • (MvPolynomial.C (elemSymm L 1)
        * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * auxVar 3)))
      = scal q * (MvPolynomial.C (elemSymm L 1 * elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
        + scal (q * (q - 1)) * (MvPolynomial.C (elemSymm L 2)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)) := by
    rw [show (MvPolynomial.C (elemSymm L 1)
          * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * auxVar 3))
        = (auxVar (2 + 1) : Total L) * (MvPolynomial.C (elemSymm L 1)
          * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)) from by norm_num; ring,
      map_smul, dminus_auxVar_succ_mul_C_elemSymm_one_mul q 2 hmem2p hmem2a, smul_add, smul_neg,
      smul_eq_scal_mul, smul_eq_scal_mul]
    simp only [scal_eq_algebraMap, map_sub, map_mul, map_neg, map_one]
    ring
  rw [partialSweepWord_baseTwoThreeTwoA q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8]


/-! ### The word of `(0,2,3,6,6)`: `-que_1y_1^2y_2^3 + q(q-1)ue_1y_1^3y_2^2` -/

/-- **The `(0,2,3,6,6)` path contributes `-que_1y_1^2y_2^3 + q(q-1)ue_1y_1^3y_2^2`.**

Nine events, widths reaching only `3`. The two width-`3` corners cancel each other's `q(q-1)` terms
outright — after the first the value is the single monomial `-q^2y_1^3y_2y_3` — and the type-`E`
event at `(3,5)` supplies the one factor of `u`. -/
theorem partialSweepWord_baseTwoThreeTwoB_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u baseTwoThreeTwoB (sepLevel 2 2) (1 : Total L)
      = -(scal (q * u) * (MvPolynomial.C (elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)))
        + scal (q * (q - 1) * u) * (MvPolynomial.C (elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)) := by
  have hw1 : dplus q 0 (1 : Total L) = -(auxVar 1 : Total L) := dplus_zero_one q
  have hw2 : corner q 1 (-(auxVar 1 : Total L)) = (auxVar 1 : Total L) ^ 2 := by
    rw [map_neg, show (auxVar 1 : Total L) = MvPolynomial.X 0 from rfl, corner_one_X_zero q hq1,
      neg_neg]
  have hw3 : dplus q 1 ((auxVar 1 : Total L) ^ 2)
      = -((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * auxVar 2) := dplus_one_auxVar_one_sq q
  have hw5 : dplus q 2 (-((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * auxVar 2))
      = (auxVar 1 : Total L) * auxVar 2 * (auxVar 3 : Total L) ^ 2
        - scal (q - 1) * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 * auxVar 3)
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3) := by
    rw [map_add, map_neg, End_apply_scal_mul, dplus_two_auxVar_one_mul_auxVar_two_sq,
      dplus_two_auxVar_one_sq_mul_auxVar_two]
    simp only [scal_eq_algebraMap, map_sub, map_mul, map_one]
    ring
  have hw6 : corner q 3 ((auxVar 1 : Total L) * auxVar 2 * (auxVar 3 : Total L) ^ 2
        - scal (q - 1) * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 * auxVar 3)
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3))
      = -(scal (q ^ 2) * ((auxVar 1 : Total L) ^ 3 * auxVar 2 * auxVar 3)) := by
    rw [map_sub, map_sub, End_apply_scal_mul, End_apply_scal_mul,
      corner_three_prod_mul_auxVar_three hq0 hq1,
      corner_three_auxVar_one_mul_auxVar_two_sq_mul_auxVar_three hq0 hq1,
      corner_three_auxVar_one_sq_mul_auxVar_two_mul_auxVar_three hq0 hq1]
    simp only [scal_eq_algebraMap, map_sub, map_mul, map_one, map_pow]
    ring
  have hw7 : ((q : L) ^ (-2 : ℤ)) • corner q 3
        (-(scal (q ^ 2) * ((auxVar 1 : Total L) ^ 3 * auxVar 2 * auxVar 3)))
      = scal q * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3 * auxVar 3)
        - scal (q * (q - 1)) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2
            * auxVar 3) := by
    have hc1 : ((q : L) ^ (-2 : ℤ)) * (q ^ 2 * q) = q := by field_simp
    have hc2 : ((q : L) ^ (-2 : ℤ)) * -(q ^ 2 * (q * (q - 1))) = -(q * (q - 1)) := by
      field_simp
    rw [map_neg, End_apply_scal_mul,
      corner_three_auxVar_one_cube_mul_auxVar_two_mul_auxVar_three hq0 hq1]
    rw [show -((scal (q ^ 2) : Total L)
          * (-(scal q * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3 * auxVar 3))
            + scal (q * (q - 1)) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2
              * auxVar 3)))
        = scal (q ^ 2 * q) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3 * auxVar 3)
          + scal (-(q ^ 2 * (q * (q - 1)))) * ((auxVar 1 : Total L) ^ 3
            * (auxVar 2 : Total L) ^ 2 * auxVar 3) from by
        simp only [scal_eq_algebraMap, map_sub, map_mul, map_neg, map_one, map_pow]
        ring,
      smul_add, smul_scal_mul, smul_scal_mul, hc1, hc2]
    simp only [scal_eq_algebraMap, map_sub, map_mul, map_neg, map_one]
    ring
  have hmemp : ∀ a b : ℕ, ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b) ∈ piece L 2 :=
    fun a b => monoTwo_mem_piece a b
  have hmema : ∀ a b : ℕ, ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b) ∈ auxSubalg L :=
    fun a b => monoTwo_mem_auxSubalg a b
  have hd23 : dminus q 3 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3 * auxVar 3)
      = -(MvPolynomial.C (elemSymm L 1)
          * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)) := by
    rw [show ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3 * auxVar 3)
        = (auxVar (2 + 1) : Total L)
          * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3) from by norm_num; ring]
    exact dminus_auxVar_succ_mul q 2 (hmemp 2 3) (hmema 2 3)
  have hd32 : dminus q 3 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2 * auxVar 3)
      = -(MvPolynomial.C (elemSymm L 1)
          * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)) := by
    rw [show ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2 * auxVar 3)
        = (auxVar (2 + 1) : Total L)
          * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) from by norm_num; ring]
    exact dminus_auxVar_succ_mul q 2 (hmemp 3 2) (hmema 3 2)
  rw [partialSweepWord_baseTwoThreeTwoB q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hw1, hw2, hw3, hw5, hw6, hw7, smul_sub, smul_scal_mul, smul_scal_mul, map_sub,
    End_apply_scal_mul, End_apply_scal_mul, hd23, hd32]
  simp only [scal_eq_algebraMap, map_sub, map_mul, map_one]
  ring

/-! ### The word of `(0,3,3,5,6)`: `-q^2ue_1y_1^3y_2^2` -/

/-- **The `(0,3,3,5,6)` path contributes `-q^2ue_1y_1^3y_2^2`.**

The only one of the four with a type-`D` event whose exponent is not `0` — `q^2` at `(1,3)` — and
the only one whose two width-`3` corners cancel down to a single monomial at the *second* of them.
Its value is a single term. -/
theorem partialSweepWord_baseTwoThreeTwoC_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u baseTwoThreeTwoC (sepLevel 2 2) (1 : Total L)
      = -(scal (q ^ 2 * u) * (MvPolynomial.C (elemSymm L 1)
          * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))) := by
  have hc1 : dplus q 0 (1 : Total L) = -(auxVar 1 : Total L) := dplus_zero_one q
  have hc2 : dplus q 1 (-(auxVar 1 : Total L)) = (auxVar 1 : Total L) * auxVar 2 := by
    have h := dplus_auxVarProd (L := L) q 1
    rw [auxVarProd_one, show (1 : ℕ) + 1 = 2 from rfl, auxVarProd_two',
      show (MvPolynomial.X 0 : Total L) = auxVar 1 from rfl] at h
    rw [map_neg, h, neg_neg]
  have hc3 : ((q : L) ^ (-1 : ℤ)) • corner q 2 ((auxVar 1 : Total L) * auxVar 2)
      = -((auxVar 1 : Total L) ^ 2 * auxVar 2) := by
    have hcs : ((q : L) ^ (-1 : ℤ)) * -q = -1 := by field_simp
    rw [corner_two_prod hq0 hq1, neg_scal_mul_eq_smul, smul_smul, hcs, neg_one_smul]
  have hc4 : dplus q 2 (-((auxVar 1 : Total L) ^ 2 * auxVar 2))
      = (auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 * auxVar 3
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3) := by
    rw [map_neg, dplus_two_auxVar_one_sq_mul_auxVar_two]
    ring
  have hc6 : ((q : L) ^ (-1 : ℤ)) • corner q 3 ((q ^ 2 : L)
        • ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 * auxVar 3
          - scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3)))
      = -(scal (q ^ 2) * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * (auxVar 3 : Total L) ^ 2))
        + scal (q ^ 2 * (q - 1)) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
            * auxVar 3) := by
    have hcs1 : ((q : L) ^ (-1 : ℤ)) * (q ^ 2 * -q) = -(q ^ 2) := by field_simp
    have hcs2 : ((q : L) ^ (-1 : ℤ)) * (q ^ 2 * ((q - 1) * q)) = q ^ 2 * (q - 1) := by
      field_simp
    rw [map_smul, map_sub, End_apply_scal_mul,
      corner_three_auxVar_one_mul_auxVar_two_sq_mul_auxVar_three hq0 hq1,
      corner_three_auxVar_one_sq_mul_auxVar_two_mul_auxVar_three hq0 hq1]
    rw [show (-((scal q : Total L)
            * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * (auxVar 3 : Total L) ^ 2))
          - scal (q - 1) * -(scal q * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
            * auxVar 3)))
        = scal (-q) * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * (auxVar 3 : Total L) ^ 2)
          + scal ((q - 1) * q) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
            * auxVar 3) from by
        simp only [scal_eq_algebraMap, map_sub, map_mul, map_neg, map_one]
        ring,
      smul_add, smul_scal_mul, smul_scal_mul, smul_add, smul_scal_mul, smul_scal_mul, hcs1, hcs2]
    simp only [scal_eq_algebraMap, map_sub, map_mul, map_neg, map_one, map_pow]
    ring
  have hc7 : ((q : L) ^ (-2 : ℤ)) • corner q 3
        (-(scal (q ^ 2) * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * (auxVar 3 : Total L) ^ 2))
          + scal (q ^ 2 * (q - 1)) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
            * auxVar 3))
      = scal (q ^ 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2 * auxVar 3) := by
    have hcs : ((q : L) ^ (-2 : ℤ)) * (q ^ 2 * q ^ 2) = q ^ 2 := by field_simp
    rw [map_add, map_neg, End_apply_scal_mul, End_apply_scal_mul,
      corner_three_auxVar_one_sq_mul_auxVar_two_mul_auxVar_three_sq hq0 hq1,
      corner_three_auxVar_one_sq_mul_auxVar_two_sq_mul_auxVar_three hq0 hq1]
    rw [show -((scal (q ^ 2) : Total L)
            * (-(scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
                * (auxVar 3 : Total L) ^ 2))
              - scal (q ^ 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2 * auxVar 3)))
          + scal (q ^ 2 * (q - 1)) * -((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
              * (auxVar 3 : Total L) ^ 2)
        = scal (q ^ 2 * q ^ 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2
            * auxVar 3) from by
        simp only [scal_eq_algebraMap, map_sub, map_mul, map_one, map_pow]
        ring,
      smul_scal_mul, hcs]
  have hc8 : dminus q 3 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2 * auxVar 3)
      = -(MvPolynomial.C (elemSymm L 1)
          * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)) := by
    rw [show ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2 * auxVar 3)
        = (auxVar (2 + 1) : Total L)
          * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) from by norm_num; ring]
    exact dminus_auxVar_succ_mul q 2 (monoTwo_mem_piece 3 2) (monoTwo_mem_auxSubalg 3 2)
  rw [partialSweepWord_baseTwoThreeTwoC q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hc1, hc2, hc3, hc4, hc6, hc7, End_apply_scal_mul, hc8, smul_scal_mul]
  simp only [scal_eq_algebraMap, map_mul, map_pow]
  ring

/-! ### The word of `(0,3,3,6,6)`: `qu^2y_1^3y_2^3` -/

/-- **The `(0,3,3,6,6)` path contributes `qu^2y_1^3y_2^3`.**

Ten events, every width `2`, so this word never leaves `V_2` and has no `d_-` at all: its value
carries no symmetric function. Its two type-`E` events give it the only `u^2` of the four, and its
four corners alternate between the balanced pair, which emits nothing, and the pair `(b, b+1)`,
which
emits one `q` — against the two `q^{-1}` of the type-`C` exponents that leaves a single `q`. -/
theorem partialSweepWord_baseTwoThreeTwoD_apply_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    partialSweepWord q u baseTwoThreeTwoD (sepLevel 2 2) (1 : Total L)
      = scal (q * u ^ 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) := by
  have hd1 : dplus q 0 (1 : Total L) = -(auxVar 1 : Total L) := dplus_zero_one q
  have hd2 : dplus q 1 (-(auxVar 1 : Total L)) = (auxVar 1 : Total L) * auxVar 2 := by
    have h := dplus_auxVarProd (L := L) q 1
    rw [auxVarProd_one, show (1 : ℕ) + 1 = 2 from rfl, auxVarProd_two',
      show (MvPolynomial.X 0 : Total L) = auxVar 1 from rfl] at h
    rw [map_neg, h, neg_neg]
  have hd4 : ((q : L) ^ (-1 : ℤ)) • corner q 2
        (-(scal q * ((auxVar 1 : Total L) ^ 2 * auxVar 2)))
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 := by
    have hcs : ((q : L) ^ (-1 : ℤ)) * q = 1 := by field_simp
    rw [map_neg, End_apply_scal_mul, corner_two_auxVar_one_sq_mul_auxVar_two hq0 hq1,
      show -((scal q : Total L) * -((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
        = scal q * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) from by ring,
      smul_scal_mul, hcs, scal_one, one_mul]
  have hd7 : corner q 2 ((q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
      = -(scal (q ^ 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)) := by
    rw [map_smul, corner_two_auxVar_one_sq_mul_auxVar_two_sq hq0 hq1, smul_neg, smul_scal_mul]
    simp only [scal_eq_algebraMap, map_mul, map_pow]
    ring
  have hd8 : ((q : L) ^ (-1 : ℤ)) • corner q 2
        (-(scal (q ^ 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)))
      = scal q * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) := by
    have hcs : ((q : L) ^ (-1 : ℤ)) * q ^ 2 = q := by field_simp
    rw [map_neg, End_apply_scal_mul, corner_two_auxVar_one_cube_mul_auxVar_two_sq hq0 hq1,
      show -((scal (q ^ 2) : Total L) * -((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3))
        = scal (q ^ 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) from by ring,
      smul_scal_mul, hcs]
  rw [partialSweepWord_baseTwoThreeTwoD q u]
  simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply]
  rw [hd1, hd2, corner_two_prod hq0 hq1, hd4, hd7, hd8, smul_scal_mul, smul_scal_mul]
  simp only [scal_eq_algebraMap, map_mul, map_pow]
  ring

end Values

end HJO.Mellit

end
