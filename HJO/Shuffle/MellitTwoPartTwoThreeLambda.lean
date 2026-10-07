/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitTwoPartTwoThreeValue
public import HJO.Shuffle.MellitNestTransfer

/-! # The basic-operator table the `Λ` side of the two-part clause at `(2,3)` needs

`HJO.Mellit.qop_double_apply_one_of_lhsWord` reads the clause of
`HJO.Mellit.lhsRewrite_sweepWitness` at the composition `α = (1,1)` as one identity in `Λ`,

`(u+1)·Q_{a,b}(Q_{a,b}1) + u(q-1)·Q_{2a,2b}(1) = (qu+1)·ct(d_-^2G_{2,1}G_{1,1}(1))`.

`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three_eval` computes the **right-hand
side** at `(a,b) = (2,3)` in closed form. The left-hand side is a word in the basic operators:
`HJO.Sym.Qop`'s coprime recursion reads `Q_{2,3} = M^{-1}[D_2,D_1]`, and `HJO.Sweep.qop_three_row`
with `HJO.Sweep.qop_four_row` read `Q_{4,6} = M^{-3}[[D_2,[D_2,D_1]],D_1]`, so both terms are values
of four-letter words in `D_1` and `D_2` on the vacuum, in the grading six.

This file supplies the table those words bottom out in, at a **general** `u` — the values `D_k(e_r)`
and the two Pieri rules at the literal indices the words reach. With `HJO.Sym.dop_apply_one` and the
known values `D_1(e_1)`, `D_2(e_1)`, `D_3(e_1)`, `D_1(e_2)`, `D_2(e_2)`, `D_1(e_3)` this closes the
table: every four-letter word in `D_1, D_2` on the vacuum is now a finite `e`-basis expression.

The one new kernel coefficient is `HJO.Bglx.paramPleth_elemSymm_five_eq`,
`κ(e_5) = (q^4+q^3u+q^2u^2+qu^3+u^4)M`, continuing the pattern `κ(e_n) = (-1)^{n-1}h_{n-1}M` one
step past `HJO.Bglx.paramPleth_elemSymm_four_eq`.

## What is not here

The assembly of the four-letter words into `Q_{2,3}(Q_{2,3}1)` and `Q_{4,6}(1)`, and the comparison
with the sweep side, are **not** done here. Cleared of the normalisations `M^{-1}`, the two words
have coefficients of degree eleven in `q` and `u` with a hundred terms apiece, and the comparison
does not go through `ring` at that size; the tractable decomposition divides by `M` at every
recursion step, as `HJO.Sym.qop_two_three_apply_one` and
`HJO.Sym.qop_two_three_apply_elemSymm_one` do, keeping the intermediate values small. That is the
work this table is for, and it is carried out in `HJO/Shuffle/MellitTwoPartTwoThreeClause.lean`.

Nothing here is about the clause: these are values of `HJO.Sym.DopInt`, unconditional in `q` and
`u`. Neither the `hlhs` binder of `HJO.Mellit.shuffle_of_lhs_and_induction` nor its `hind` binder
is discharged here.

## References

This file works with `HJO.Sym.DopInt` and `HJO.Sym.Qop`.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`κ(e_5) = (q^4+q^3u+q^2u^2+qu^3+u^4)M`**, the kernel recursion
`HJO.Bglx.paramPleth_elemSymm_add_two` at `n = 3`, one step past
`HJO.Bglx.paramPleth_elemSymm_four_eq`. -/
theorem paramPleth_elemSymm_five_eq (q u : L) :
    paramPleth q u (elemSymm L 5)
      = (q ^ 4 + q ^ 3 * u + q ^ 2 * u ^ 2 + q * u ^ 3 + u ^ 4) * ((1 - q) * (1 - u)) := by
  have h := paramPleth_elemSymm_add_two (K := L) q u 3
  rw [show (3 : ℕ) + 2 = 5 from rfl, show (3 : ℕ) + 1 = 4 from rfl,
    paramPleth_elemSymm_four_eq, paramPleth_elemSymm_three_eq] at h
  simp only [OfNat.ofNat_ne_zero, ite_false] at h
  linear_combination h

end HJO.Bglx

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The Pieri rules at the literal indices the computation uses -/

theorem dop_one_mul_one (q u : L) (f : Lambda L) :
    Dop q u 1 (elemSymm L 1 * f)
      = elemSymm L 1 * Dop q u 1 f + ((1 - q) * (1 - u)) • Dop q u 2 f :=
  dop_elemSymm_one_mul q u 1 f

theorem dop_one_mul_two (q u : L) (f : Lambda L) :
    Dop q u 2 (elemSymm L 1 * f)
      = elemSymm L 1 * Dop q u 2 f + ((1 - q) * (1 - u)) • Dop q u 3 f :=
  dop_elemSymm_one_mul q u 2 f

theorem dop_one_mul_three (q u : L) (f : Lambda L) :
    Dop q u 3 (elemSymm L 1 * f)
      = elemSymm L 1 * Dop q u 3 f + ((1 - q) * (1 - u)) • Dop q u 4 f :=
  dop_elemSymm_one_mul q u 3 f

/-- `D_k(e_2f)` for a general `k`: `HJO.Sym.dop_elemSymm_mul` at `n = 2`, unfolded. -/
theorem dop_two_mul (q u : L) (k : ℕ) (f : Lambda L) :
    Dop q u k (elemSymm L 2 * f)
      = elemSymm L 2 * Dop q u k f
        + ((1 - q) * (1 - u)) • (elemSymm L 1 * Dop q u (k + 1) f)
        + (-((q + u) * ((1 - q) * (1 - u)))) • Dop q u (k + 2) f := by
  rw [dop_elemSymm_mul, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq]
  simp only [Nat.sub_zero, Nat.sub_self, elemSymm_zero, Nat.add_zero, zero_add, one_smul]
  ring_nf

theorem dop_two_mul_one (q u : L) (f : Lambda L) :
    Dop q u 1 (elemSymm L 2 * f)
      = elemSymm L 2 * Dop q u 1 f
        + ((1 - q) * (1 - u)) • (elemSymm L 1 * Dop q u 2 f)
        + (-((q + u) * ((1 - q) * (1 - u)))) • Dop q u 3 f := dop_two_mul q u 1 f

theorem dop_two_mul_two (q u : L) (f : Lambda L) :
    Dop q u 2 (elemSymm L 2 * f)
      = elemSymm L 2 * Dop q u 2 f
        + ((1 - q) * (1 - u)) • (elemSymm L 1 * Dop q u 3 f)
        + (-((q + u) * ((1 - q) * (1 - u)))) • Dop q u 4 f := dop_two_mul q u 2 f

/-! ### The base values `D_k(e_r)` the computation bottoms out in -/

theorem dop_three_elemSymm_two (q u : L) :
    Dop q u 3 (elemSymm L 2)
      = (u - u ^ 2 + q - 2 * q * u + q * u ^ 2 - q ^ 2 + q ^ 2 * u) • elemSymm L 5
        + (-1 : L) • (elemSymm L 2 * elemSymm L 3)
        + (1 - u - q + q * u) • (elemSymm L 1 * elemSymm L 4) := by
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_pow,
    map_ofNat, Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

theorem dop_four_elemSymm_two (q u : L) :
    Dop q u 4 (elemSymm L 2)
      = (-u + u ^ 2 - q + 2 * q * u - q * u ^ 2 + q ^ 2 - q ^ 2 * u) • elemSymm L 6
        + (1 : L) • (elemSymm L 2 * elemSymm L 4)
        + (-1 + u + q - q * u) • (elemSymm L 1 * elemSymm L 5) := by
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_pow,
    map_ofNat, Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

theorem dop_two_elemSymm_three (q u : L) :
    Dop q u 2 (elemSymm L 3)
      = (-u ^ 2 + u ^ 3 - q * u + 2 * q * u ^ 2 - q * u ^ 3 - q ^ 2 + 2 * q ^ 2 * u
          - q ^ 2 * u ^ 2 + q ^ 3 - q ^ 3 * u) • elemSymm L 5
        + (u + q - q * u) • (elemSymm L 2 * elemSymm L 3)
        + (-u + u ^ 2 - q + 2 * q * u - q * u ^ 2 + q ^ 2 - q ^ 2 * u)
            • (elemSymm L 1 * elemSymm L 4) := by
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero,
    Bglx.paramPleth_elemSymm_one_eq, Bglx.paramPleth_elemSymm_two_eq,
    Bglx.paramPleth_elemSymm_three_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_pow,
    map_ofNat, Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

theorem dop_three_elemSymm_three (q u : L) :
    Dop q u 3 (elemSymm L 3)
      = (u ^ 2 - u ^ 3 + q * u - 2 * q * u ^ 2 + q * u ^ 3 + q ^ 2 - 2 * q ^ 2 * u
          + q ^ 2 * u ^ 2 - q ^ 3 + q ^ 3 * u) • elemSymm L 6
        + (-1 : L) • elemSymm L 3 ^ 2
        + (1 - u - q + q * u) • (elemSymm L 2 * elemSymm L 4)
        + (u - u ^ 2 + q - 2 * q * u + q * u ^ 2 - q ^ 2 + q ^ 2 * u)
            • (elemSymm L 1 * elemSymm L 5) := by
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero,
    Bglx.paramPleth_elemSymm_one_eq, Bglx.paramPleth_elemSymm_two_eq,
    Bglx.paramPleth_elemSymm_three_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_pow,
    map_ofNat, Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

theorem dop_one_elemSymm_four (q u : L) :
    Dop q u 1 (elemSymm L 4)
      = (u ^ 3 - u ^ 4 + q * u ^ 2 - 2 * q * u ^ 3 + q * u ^ 4 + q ^ 2 * u - 2 * q ^ 2 * u ^ 2
          + q ^ 2 * u ^ 3 + q ^ 3 - 2 * q ^ 3 * u + q ^ 3 * u ^ 2 - q ^ 4 + q ^ 4 * u)
            • elemSymm L 5
        + (1 - u ^ 2 - q * u + q * u ^ 2 - q ^ 2 + q ^ 2 * u) • (elemSymm L 2 * elemSymm L 3)
        + (-1 + u ^ 2 - u ^ 3 + q * u - 2 * q * u ^ 2 + q * u ^ 3 + q ^ 2 - 2 * q ^ 2 * u
            + q ^ 2 * u ^ 2 - q ^ 3 + q ^ 3 * u) • (elemSymm L 1 * elemSymm L 4) := by
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq,
    Bglx.paramPleth_elemSymm_four_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_pow,
    map_ofNat, Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

theorem dop_two_elemSymm_four (q u : L) :
    Dop q u 2 (elemSymm L 4)
      = (-u ^ 3 + u ^ 4 - q * u ^ 2 + 2 * q * u ^ 3 - q * u ^ 4 - q ^ 2 * u + 2 * q ^ 2 * u ^ 2
          - q ^ 2 * u ^ 3 - q ^ 3 + 2 * q ^ 3 * u - q ^ 3 * u ^ 2 + q ^ 4 - q ^ 4 * u)
            • elemSymm L 6
        + (-1 + u + q - q * u) • elemSymm L 3 ^ 2
        + (1 - u + u ^ 2 - q + 2 * q * u - q * u ^ 2 + q ^ 2 - q ^ 2 * u)
            • (elemSymm L 2 * elemSymm L 4)
        + (-u ^ 2 + u ^ 3 - q * u + 2 * q * u ^ 2 - q * u ^ 3 - q ^ 2 + 2 * q ^ 2 * u
            - q ^ 2 * u ^ 2 + q ^ 3 - q ^ 3 * u) • (elemSymm L 1 * elemSymm L 5) := by
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq,
    Bglx.paramPleth_elemSymm_four_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_pow,
    map_ofNat, Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

theorem dop_one_elemSymm_five (q u : L) :
    Dop q u 1 (elemSymm L 5)
      = (u ^ 4 - u ^ 5 + q * u ^ 3 - 2 * q * u ^ 4 + q * u ^ 5 + q ^ 2 * u ^ 2
          - 2 * q ^ 2 * u ^ 3 + q ^ 2 * u ^ 4 + q ^ 3 * u - 2 * q ^ 3 * u ^ 2 + q ^ 3 * u ^ 3
          + q ^ 4 - 2 * q ^ 4 * u + q ^ 4 * u ^ 2 - q ^ 5 + q ^ 5 * u) • elemSymm L 6
        + (u - u ^ 2 + q - 2 * q * u + q * u ^ 2 - q ^ 2 + q ^ 2 * u) • elemSymm L 3 ^ 2
        + (1 - u + u ^ 2 - u ^ 3 - q + 2 * q * u - 2 * q * u ^ 2 + q * u ^ 3 + q ^ 2
            - 2 * q ^ 2 * u + q ^ 2 * u ^ 2 - q ^ 3 + q ^ 3 * u)
            • (elemSymm L 2 * elemSymm L 4)
        + (-1 + u ^ 3 - u ^ 4 + q * u ^ 2 - 2 * q * u ^ 3 + q * u ^ 4 + q ^ 2 * u
            - 2 * q ^ 2 * u ^ 2 + q ^ 2 * u ^ 3 + q ^ 3 - 2 * q ^ 3 * u + q ^ 3 * u ^ 2 - q ^ 4
            + q ^ 4 * u) • (elemSymm L 1 * elemSymm L 5) := by
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq,
    Bglx.paramPleth_elemSymm_four_eq, Bglx.paramPleth_elemSymm_five_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_pow,
    map_ofNat, Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

end HJO.Sym

end
