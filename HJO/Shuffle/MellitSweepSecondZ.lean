/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.StarElemSymm
public import HJO.Shuffle.MellitQopThreeFour
public import HJO.Shuffle.MellitZopOneV1
public meta import HJO.Attr

/-! # The second `z` of the slope word `β_{3,4} = yzyzy`

`HJO/Shuffle/MellitQopThreeFour.lean` records that `(3,4)` is the smallest slope whose word
`β_{3,4} = yzyzy` (`HJO.Mellit.slopeWord_three_four`) applies a `z` to an element of `V_1` with
nontrivial `Λ`-coefficient: the first `z` acts on `y_1^2`, as at `(2,3)`, but the second acts on
`y_1·d^*_+{}^{(0)}(Ce_2) - y_1Ce_2`. That is the step `HJO.Sweep.zopOneStar_one_auxVar_sq` cannot
reach, and the obstacle is not `z_1` — `HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C` supplies that —
but the need for an expansion of `d^*_+{}^{(0)}` on a `C` of an elementary symmetric function,
without which the argument cannot be put in the `y_1^m·Cf` form that evaluation reads.

`HJO.Sweep.dplusStar_C_elemSymm` supplies that expansion, and this file takes the step.

## Main results

* `HJO.Sym.bop_two_elemSymm_one`: `B_2(e_1) = e_1e_2 - (1-q)e_3`, off `HJO.Sym.bop_natCast` and
  `HJO.Sym.dop_elemSymm` — the `Λ`-side value the step needs, and the reason `d^*_+` is needed on
  `e_1e_2` and on `e_3` and not only on `e_2`.
* `HJO.Sym.bop_three_one`: `B_3(1) = -e_3`.
* `HJO.Sweep.zopOneStar_one_auxVar_mul_dplusStar_C_elemSymm_two_sub`: **the step**, `z_1` on
  `y_1·(d^*_+{}^{(0)}(Ce_2) - Ce_2)` in closed form, with every `d^*_+` discharged and nothing
  opaque on the right.

## Genericity

No hypothesis on `q` or `u`. The scalar `q/(1-q)` of `HJO.Sweep.zop` is carried symbolically,
exactly as in `HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C`, and the expansion it is applied to is
unconditional. The conditions `q ∉ {0,1}`, `u ∉ {0,1}` belong to the statements that use it.
-/

@[expose] public section

open HJO.Sym HJO.Bglx

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### Two values of the Hall--Littlewood operator -/

/-- **`B_2(e_1) = e_1e_2 - (1-q)e_3`.** `B_r` is the basic operator at `u = 0`
(`HJO.Sym.bop_natCast`), so this is `HJO.Sym.dop_elemSymm` at `k = 2`, `r = 1`, `u = 0`, against the
two kernel values `κ(e_0) = 1` and `κ(e_1) = (1-q)(1-u)`.

This is the value that makes the `(3,4)` sweep side need `d^*_+` on a *product*: the first `z` puts
`e_1` in the `Λ`-coefficient, and `B_2` of it is `e_1e_2` plus a multiple of `e_3`. -/
theorem bop_two_elemSymm_one (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1)
      = elemSymm L 1 * elemSymm L 2 - MvPolynomial.C (1 - q) * elemSymm L 3 := by
  rw [show Bop q ((2 : ℕ) : ℤ) (elemSymm L 1) = Dop q 0 2 (elemSymm L 1) from by
    rw [bop_natCast q 2]]
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_one]
  rw [paramPleth_elemSymm_zero, paramPleth_elemSymm_one_eq]
  norm_num [elemSymm_zero]
  ring

/-- **`B_3(1) = -e_3`.** `HJO.Sym.bop_one` at `r = 3`: `B_r(1) = Ω_r`, and `Ω_3 = (-1)^3e_3`. -/
theorem bop_three_one (q : L) : Bop q ((3 : ℕ) : ℤ) (1 : Lambda L) = -elemSymm L 3 := by
  rw [bop_one, elemSymmAlt_natCast]
  norm_num

end HJO.Sym

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The step -/

/-- **`z_1` on `y_1·(d^*_+{}^{(0)}(Ce_2) - Ce_2)`**, the second `z` of `β_{3,4} = yzyzy`, in closed
form with every `d^*_+` discharged:

`z_1(y_1(d^*_+(Ce_2) - Ce_2)) = q/(1-q)·[ (q-1)u·(d^*_+(C(e_1e_2)) - (1-q)d^*_+(Ce_3)
  - C(e_1e_2) + (1-q)Ce_3 - (q-1)u·y_1·Ce_2)
  - (1-q)u^2·(d^*_+(Ce_3) - Ce_3) ]`,

each `d^*_+` on the right then being one of `HJO.Sweep.dplusStar_C_elemSymm_one_mul_two`,
`HJO.Sweep.dplusStar_C_elemSymm_three`.

The route: `HJO.Sweep.dplusStar_C_elemSymm_two_sub` puts the argument in the `y_1^m·Cf` form
`(q-1)u·y_1^2Ce_1 + (1-q)u^2·y_1^3`, which is what
`HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C` reads; its two `B_m` are then
`HJO.Sym.bop_two_elemSymm_one` and `HJO.Sym.bop_three_one`, and its `bopExt` half is
`HJO.Sweep.dplusStar_C_elemSymm_one` pushed through `HJO.Sweep.bopExt_auxSubalg_mul`,
`HJO.Sweep.bopExt_C` and `HJO.Sweep.bopExt_one`.

This is the step `HJO/Shuffle/MellitQopThreeFour.lean`'s docstring names as the one the
`(3,4)` check turns on. -/
theorem zopOneStar_one_auxVar_mul_dplusStar_C_elemSymm_two_sub (q u : L) :
    zopOneStar q u 1 ((auxVar 1 : Total L) *
        (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 2))
          - MvPolynomial.C (Sym.elemSymm L 2)))
      = (q / (1 - q)) •
          (((q - 1) * u) •
              (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 2))
                - (1 - q) • dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 3))
                - MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 2)
                + (1 - q) • (MvPolynomial.C (Sym.elemSymm L 3) : Total L)
                - ((q - 1) * u) •
                    ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 2)))
            + ((1 - q) * u ^ 2) • (MvPolynomial.C (Sym.elemSymm L 3)
                - dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 3)))) := by
  have hone : (MvPolynomial.C (1 : Sym.Lambda L) : Total L) = 1 := map_one _
  have hdone : dplusStar q u 0 (1 : Total L) = 1 := by
    rw [← dplusStarAlg_eq_dplusStar, map_one]
  have hZmem : ∀ x : L, (scal x * (auxVar 1 : Total L)) ∈ auxSubalg L := fun x =>
    mul_mem (scal_mem_auxSubalg x) (auxVar_mem_auxSubalg 1)
  -- `d^*_+` on `e_1`, with the letter written as a single scalar times `y_1`
  have hd1 : dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = MvPolynomial.C (Sym.elemSymm L 1) + scal ((q - 1) * u) * (auxVar 1 : Total L) := by
    rw [dplusStar_C_elemSymm_one, starLetter, scal_mul]
    ring
  -- the argument, in the `y_1^m·Cf` form `zopOneStar_one_auxVar_pow_mul_C` reads
  have harg : (auxVar 1 : Total L) *
      (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 2))
        - MvPolynomial.C (Sym.elemSymm L 2))
      = ((q - 1) * u) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (Sym.elemSymm L 1))
        + ((1 - q) * u ^ 2) •
            ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Sym.Lambda L)) := by
    rw [dplusStar_C_elemSymm_two_sub, hone]
    simp only [smul_eq_scal_mul]
    ring
  -- the `bopExt` half of the `m = 2` value, off the expansion of `d^*_+` on `e_1`
  have hb2 : bopExt q ((2 : ℕ) : ℤ) (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1)))
      = MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 2)
        - (1 - q) • (MvPolynomial.C (Sym.elemSymm L 3) : Total L)
        + ((q - 1) * u) • ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 2)) := by
    rw [hd1, map_add,
      show (scal ((q - 1) * u) * (auxVar 1 : Total L))
          = scal ((q - 1) * u) * (auxVar 1 : Total L) * 1 from (mul_one _).symm,
      bopExt_auxSubalg_mul q _ (hZmem _), bopExt_C, bopExt_one, Sym.bop_two_elemSymm_one,
      Sym.elemSymmAlt_natCast]
    simp only [map_sub, map_mul, map_pow, map_neg, map_one, smul_eq_scal_mul, scal]
    norm_num
    ring
  -- the two `z_1` values
  have hz2 : zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (Sym.elemSymm L 1))
      = (q / (1 - q)) •
          (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 2))
            - (1 - q) • dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 3))
            - MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 2)
            + (1 - q) • (MvPolynomial.C (Sym.elemSymm L 3) : Total L)
            - ((q - 1) * u) • ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 2))) := by
    rw [zopOneStar_one_auxVar_pow_mul_C, Sym.bop_two_elemSymm_one, hb2]
    congr 1
    rw [show (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 2
            - MvPolynomial.C (1 - q) * Sym.elemSymm L 3) : Total L)
        = MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 2)
          - (1 - q) • (MvPolynomial.C (Sym.elemSymm L 3) : Total L) from by
      simp only [map_sub, map_mul, smul_eq_scal_mul, scal]]
    rw [map_sub, map_smul]
    abel
  have hz3 : zopOneStar q u 1 ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Sym.Lambda L))
      = (q / (1 - q)) • (MvPolynomial.C (Sym.elemSymm L 3)
          - dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 3))) := by
    rw [zopOneStar_one_auxVar_pow_mul_C, Sym.bop_three_one, hone, hdone, bopExt_one,
      Sym.elemSymmAlt_natCast]
    congr 1
    simp only [map_neg, map_mul, map_pow, map_one]
    norm_num
    ring
  rw [harg, map_add, map_smul, map_smul, hz2, hz3]
  module

end HJO.Sweep
