/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepOnePartLambdaStep
public import HJO.Shuffle.ZDefectEBasisTable
public import HJO.Shuffle.MellitTwoPartTwoThreeLambda

/-! # The Hall--Littlewood table and the defect functional of the one-part sweep step

The values `HJO/Shuffle/SweepOnePartDefectValues.lean` assembles its two defects from: the
Hall--Littlewood values past the existing table and the Pieri rules at `e_3` and `e_4` (`HJO.Sym`),
the functional `HJO.Sweep.twistProj` with its additivity, the values of `HJO.Sweep.twistDop` the
one-part defects at `[1]` read, and the eleven values `T_{2,m}` the inner defect at `[2]` reads.
The method is described in that file, which assembles the defects; the table is a file of its own
because the two together are longer than a file should be.

## References

This file works with `HJO.Sym.Bop`, `HJO.Sweep.bopExt`, `HJO.Sweep.dplusStar`, `HJO.Sweep.dminus`
and `HJO.Sym.elemSymm`.
-/

set_option linter.unusedSimpArgs false

@[expose] public section

-- Every exponent written as a numeral in this file is a natural number. Saying so up front lets
-- each `x ^ n` resolve `HPow _ ℕ _` at once instead of retrying instance resolution for the
-- pending numeral type until defaulting, which dominated elaboration here. The elaborated terms
-- are the ones the default instance would produce.
local macro_rules | `($x ^ $n:num) => `(rightact% HPow.hPow $x ($n : ℕ))

namespace HJO.Bglx

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`κ(e_6) = -(q^5+q^4u+q^3u^2+q^2u^3+qu^4+u^5)M`**, the kernel recursion
`HJO.Bglx.paramPleth_elemSymm_add_two` at `n = 4`, one step past
`HJO.Bglx.paramPleth_elemSymm_five_eq`. -/
theorem paramPleth_elemSymm_six_eq (q u : L) :
    paramPleth q u (elemSymm L 6)
      = -((q ^ 5 + q ^ 4 * u + q ^ 3 * u ^ 2 + q ^ 2 * u ^ 3 + q * u ^ 4 + u ^ 5)
          * ((1 - q) * (1 - u))) := by
  have h := paramPleth_elemSymm_add_two (K := L) q u 4
  rw [show (4 : ℕ) + 2 = 6 from rfl, show (4 : ℕ) + 1 = 5 from rfl,
    paramPleth_elemSymm_five_eq, paramPleth_elemSymm_four_eq] at h
  simp only [OfNat.ofNat_ne_zero, ite_false] at h
  linear_combination h

end HJO.Bglx

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The Hall--Littlewood values at the index `1` past the existing table

`HJO.Sym.bop_natCast` reads `B_k` as `HJO.Sym.DopInt`'s `D_k` at `u = 0`, so each base row below is
a known `D`-value specialised there; the products are the two Pieri rules of
`HJO.Sym.bop_elemSymm_one_mul` and `HJO.Sym.bop_elemSymm_two_mul`, which hold at every index. -/

/-- `B_1(e_3)`, off `HJO.Sym.dop_one_elemSymm_three` at `u = 0`. -/
theorem bop_one_elemSymm_three (q : L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 3)
      = (-q ^ 3 + q ^ 2) • elemSymm L 4
        + (-q ^ 2 + q - 1) • (elemSymm L 1 * elemSymm L 3)
        + (1 - q) • (elemSymm L 2 * elemSymm L 2) := by
  rw [bop_natCast, dop_one_elemSymm_three]
  module

/-- `B_1(e_4)`, off `HJO.Sym.dop_one_elemSymm_four` at `u = 0`. -/
theorem bop_one_elemSymm_four (q : L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 4)
      = (-q ^ 4 + q ^ 3) • elemSymm L 5
        + (-q ^ 3 + q ^ 2 - 1) • (elemSymm L 1 * elemSymm L 4)
        + (1 - q ^ 2) • (elemSymm L 2 * elemSymm L 3) := by
  rw [bop_natCast, dop_one_elemSymm_four]
  module

/-- `B_1(e_5)`, off `HJO.Sym.dop_one_elemSymm_five` at `u = 0`. -/
theorem bop_one_elemSymm_five (q : L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 5)
      = (-q ^ 5 + q ^ 4) • elemSymm L 6
        + (-q ^ 4 + q ^ 3 - 1) • (elemSymm L 1 * elemSymm L 5)
        + (-q ^ 3 + q ^ 2 - q + 1) • (elemSymm L 2 * elemSymm L 4)
        + (-q ^ 2 + q) • (elemSymm L 3 * elemSymm L 3) := by
  rw [bop_natCast, dop_one_elemSymm_five]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, MvPolynomial.C_0, map_ofNat]
  grobner

/-- `B_1(e_1f)`, the first Pieri rule at the index `1`. -/
theorem bop_one_elemSymm_one_mul (q : L) (f : Lambda L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 1 * f)
      = elemSymm L 1 * Bop q ((1 : ℕ) : ℤ) f + (1 - q) • Bop q ((2 : ℕ) : ℤ) f :=
  bop_elemSymm_one_mul q 1 f

/-- `B_1(e_2f)`, the second Pieri rule at the index `1`. -/
theorem bop_one_elemSymm_two_mul (q : L) (f : Lambda L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 2 * f)
      = elemSymm L 2 * Bop q ((1 : ℕ) : ℤ) f
        + (1 - q) • (elemSymm L 1 * Bop q ((2 : ℕ) : ℤ) f)
        + (-(q * (1 - q))) • Bop q ((3 : ℕ) : ℤ) f :=
  bop_elemSymm_two_mul q 1 f

/-- `B_1(e_1e_3)`. -/
theorem bop_one_elemSymm_one_mul_three (q : L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 3)
      = (-q ^ 4 + 2 * q ^ 3 - q ^ 2) • elemSymm L 5
        + (-2 * q ^ 3 + 3 * q ^ 2 - q) • (elemSymm L 1 * elemSymm L 4)
        + (-q ^ 2 + q) • (elemSymm L 2 * elemSymm L 3)
        + (-q ^ 2 + q - 1) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
        + (1 - q) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)) := by
  rw [bop_one_elemSymm_one_mul, bop_one_elemSymm_three, bop_two_elemSymm_three]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_1(e_1e_4)`. -/
theorem bop_one_elemSymm_one_mul_four (q : L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 4)
      = (-q ^ 5 + 2 * q ^ 4 - q ^ 3) • elemSymm L 6
        + (-2 * q ^ 4 + 3 * q ^ 3 - q ^ 2) • (elemSymm L 1 * elemSymm L 5)
        + (-q ^ 3 + 2 * q ^ 2 - 2 * q + 1) • (elemSymm L 2 * elemSymm L 4)
        + (-q ^ 2 + 2 * q - 1) • (elemSymm L 3 * elemSymm L 3)
        + (-q ^ 3 + q ^ 2 - 1) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (1 - q ^ 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)) := by
  rw [bop_one_elemSymm_one_mul, bop_one_elemSymm_four, bop_two_elemSymm_four]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_1(e_2e_3)`. -/
theorem bop_one_elemSymm_two_mul_three (q : L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 2 * elemSymm L 3)
      = (-q ^ 5 + 2 * q ^ 4 - q ^ 3) • elemSymm L 6
        + (-2 * q ^ 4 + 4 * q ^ 3 - 2 * q ^ 2) • (elemSymm L 1 * elemSymm L 5)
        + (-2 * q ^ 3 + 3 * q ^ 2 - q) • (elemSymm L 2 * elemSymm L 4)
        + (-q ^ 2 + q) • (elemSymm L 3 * elemSymm L 3)
        + (-q ^ 3 + 2 * q ^ 2 - q) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (-2 * q ^ 2 + 2 * q - 1) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))
        + (1 - q) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2)) := by
  rw [bop_one_elemSymm_two_mul, bop_one_elemSymm_three, bop_two_elemSymm_three,
    bop_three_elemSymm_three]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_1(e_1^2e_3)`. -/
theorem bop_one_elemSymm_one_sq_mul_three (q : L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
      = (-q ^ 5 + 3 * q ^ 4 - 3 * q ^ 3 + q ^ 2) • elemSymm L 6
        + (-3 * q ^ 4 + 7 * q ^ 3 - 5 * q ^ 2 + q) • (elemSymm L 1 * elemSymm L 5)
        + (-q ^ 3 + 3 * q ^ 2 - 3 * q + 1) • (elemSymm L 2 * elemSymm L 4)
        + (-q ^ 2 + 2 * q - 1) • (elemSymm L 3 * elemSymm L 3)
        + (-3 * q ^ 3 + 5 * q ^ 2 - 2 * q) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (-2 * q ^ 2 + 2 * q) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))
        + (-q ^ 2 + q - 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (1 - q) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))) := by
  rw [bop_one_elemSymm_one_mul, bop_one_elemSymm_one_mul_three, bop_two_elemSymm_one_mul_three]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-! ### The Pieri rules at `e_3` and `e_4`, and three more base rows

`HJO.Sym.bop_elemSymm_one_mul` and `HJO.Sym.bop_elemSymm_two_mul` strip a factor `e_1` or `e_2` at
every index; the `A = 2` defect meets `e_3` and `e_4` in a leading position too, and these are the
same unfolding of `HJO.Sym.dop_elemSymm_mul` at `n = 3` and `n = 4`, `u = 0`. -/

/-- **`B_k(e_3f)`** at every index, the four kernel coefficients at `u = 0` being `1`, `1-q`,
`-q(1-q)` and `q^2(1-q)`. -/
theorem bop_elemSymm_three_mul (q : L) (k : ℕ) (f : Lambda L) :
    Bop q ((k : ℕ) : ℤ) (elemSymm L 3 * f)
      = elemSymm L 3 * Bop q ((k : ℕ) : ℤ) f
        + (1 - q) • (elemSymm L 2 * Bop q ((k + 1 : ℕ) : ℤ) f)
        + (-(q * (1 - q))) • (elemSymm L 1 * Bop q ((k + 2 : ℕ) : ℤ) f)
        + (q ^ 2 * (1 - q)) • Bop q ((k + 3 : ℕ) : ℤ) f := by
  simp only [bop_natCast]
  rw [dop_elemSymm_mul, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero,
    Bglx.paramPleth_elemSymm_one_eq, Bglx.paramPleth_elemSymm_two_eq,
    Bglx.paramPleth_elemSymm_three_eq]
  simp only [Nat.sub_zero, Nat.sub_self, elemSymm_zero, Nat.add_zero, zero_add, one_smul]
  norm_num

/-- **`B_k(e_4f)`** at every index, one kernel coefficient further. -/
theorem bop_elemSymm_four_mul (q : L) (k : ℕ) (f : Lambda L) :
    Bop q ((k : ℕ) : ℤ) (elemSymm L 4 * f)
      = elemSymm L 4 * Bop q ((k : ℕ) : ℤ) f
        + (1 - q) • (elemSymm L 3 * Bop q ((k + 1 : ℕ) : ℤ) f)
        + (-(q * (1 - q))) • (elemSymm L 2 * Bop q ((k + 2 : ℕ) : ℤ) f)
        + (q ^ 2 * (1 - q)) • (elemSymm L 1 * Bop q ((k + 3 : ℕ) : ℤ) f)
        + (-(q ^ 3 * (1 - q))) • Bop q ((k + 4 : ℕ) : ℤ) f := by
  simp only [bop_natCast]
  rw [dop_elemSymm_mul, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq,
    Bglx.paramPleth_elemSymm_four_eq]
  simp only [Nat.sub_zero, Nat.sub_self, elemSymm_zero, Nat.add_zero, zero_add, one_smul]
  norm_num

/-- `B_2(e_5)`. -/
theorem bop_two_elemSymm_five (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 5)
      = (q ^ 5 - q ^ 4) • elemSymm L 7
        + (q ^ 4 - q ^ 3) • (elemSymm L 1 * elemSymm L 6)
        + (q ^ 3 - q ^ 2 + 1) • (elemSymm L 2 * elemSymm L 5)
        + (q ^ 2 - 1) • (elemSymm L 3 * elemSymm L 4) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq,
    Bglx.paramPleth_elemSymm_four_eq, Bglx.paramPleth_elemSymm_five_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_3(e_5)`. -/
theorem bop_three_elemSymm_five (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 5)
      = (-q ^ 5 + q ^ 4) • elemSymm L 8
        + (-q ^ 4 + q ^ 3) • (elemSymm L 1 * elemSymm L 7)
        + (-q ^ 3 + q ^ 2) • (elemSymm L 2 * elemSymm L 6)
        + (-q ^ 2 + q - 1) • (elemSymm L 3 * elemSymm L 5)
        + (1 - q) • (elemSymm L 4 * elemSymm L 4) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq,
    Bglx.paramPleth_elemSymm_four_eq, Bglx.paramPleth_elemSymm_five_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_2(e_6)`, the one row that needs `HJO.Bglx.paramPleth_elemSymm_six_eq`. -/
theorem bop_two_elemSymm_six (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 6)
      = (q ^ 6 - q ^ 5) • elemSymm L 8
        + (q ^ 5 - q ^ 4) • (elemSymm L 1 * elemSymm L 7)
        + (q ^ 4 - q ^ 3 + 1) • (elemSymm L 2 * elemSymm L 6)
        + (q ^ 3 - q ^ 2 + q - 1) • (elemSymm L 3 * elemSymm L 5)
        + (q ^ 2 - q) • (elemSymm L 4 * elemSymm L 4) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero,
    Bglx.paramPleth_elemSymm_one_eq, Bglx.paramPleth_elemSymm_two_eq,
    Bglx.paramPleth_elemSymm_three_eq, Bglx.paramPleth_elemSymm_four_eq,
    Bglx.paramPleth_elemSymm_five_eq, Bglx.paramPleth_elemSymm_six_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_7(1) = -e_7`. -/
theorem bop_seven_one (q : L) : Bop q ((7 : ℕ) : ℤ) (1 : Lambda L) = -elemSymm L 7 := by
  rw [bop_natCast_one]; norm_num

/-- `B_8(1) = e_8`. -/
theorem bop_eight_one (q : L) : Bop q ((8 : ℕ) : ℤ) (1 : Lambda L) = elemSymm L 8 := by
  rw [bop_natCast_one]; norm_num

/-- `B_4(e_3)`. -/
theorem bop_four_elemSymm_three (q : L) :
    Bop q ((4 : ℕ) : ℤ) (elemSymm L 3)
      = (q ^ 3 - q ^ 2) • elemSymm L 7
        + (q ^ 2 - q) • (elemSymm L 1 * elemSymm L 6)
        + (q - 1) • (elemSymm L 2 * elemSymm L 5)
        + (1 : L) • (elemSymm L 3 * elemSymm L 4) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_5(e_3)`. -/
theorem bop_five_elemSymm_three (q : L) :
    Bop q ((5 : ℕ) : ℤ) (elemSymm L 3)
      = (-q ^ 3 + q ^ 2) • elemSymm L 8
        + (-q ^ 2 + q) • (elemSymm L 1 * elemSymm L 7)
        + (1 - q) • (elemSymm L 2 * elemSymm L 6)
        + (-1 : L) • (elemSymm L 3 * elemSymm L 5) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_3(e_4)`. -/
theorem bop_three_elemSymm_four (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 4)
      = (-q ^ 4 + q ^ 3) • elemSymm L 7
        + (-q ^ 3 + q ^ 2) • (elemSymm L 1 * elemSymm L 6)
        + (-q ^ 2 + q) • (elemSymm L 2 * elemSymm L 5)
        + (-q) • (elemSymm L 3 * elemSymm L 4) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq,
    Bglx.paramPleth_elemSymm_four_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_4(e_4)`. -/
theorem bop_four_elemSymm_four (q : L) :
    Bop q ((4 : ℕ) : ℤ) (elemSymm L 4)
      = (q ^ 4 - q ^ 3) • elemSymm L 8
        + (q ^ 3 - q ^ 2) • (elemSymm L 1 * elemSymm L 7)
        + (q ^ 2 - q) • (elemSymm L 2 * elemSymm L 6)
        + (q - 1) • (elemSymm L 3 * elemSymm L 5)
        + (1 : L) • (elemSymm L 4 * elemSymm L 4) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq,
    Bglx.paramPleth_elemSymm_four_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_5(e_2)`. -/
theorem bop_five_elemSymm_two (q : L) :
    Bop q ((5 : ℕ) : ℤ) (elemSymm L 2)
      = (-q ^ 2 + q) • elemSymm L 7
        + (1 - q) • (elemSymm L 1 * elemSymm L 6)
        + (-1 : L) • (elemSymm L 2 * elemSymm L 5) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero,
    Bglx.paramPleth_elemSymm_one_eq, Bglx.paramPleth_elemSymm_two_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_6(e_2)`. -/
theorem bop_six_elemSymm_two (q : L) :
    Bop q ((6 : ℕ) : ℤ) (elemSymm L 2)
      = (q ^ 2 - q) • elemSymm L 8
        + (q - 1) • (elemSymm L 1 * elemSymm L 7)
        + (1 : L) • (elemSymm L 2 * elemSymm L 6) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero,
    Bglx.paramPleth_elemSymm_one_eq, Bglx.paramPleth_elemSymm_two_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

end HJO.Sym

namespace HJO.Sweep

open Finset HJO.Sym HJO.Mellit

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The functional `T_{l,m}` reads on the total space -/

/-- `F ↦ ct(d_-^{(1)}(y_1^l·B_mF))`, the outer half of `HJO.Sweep.twistDop` read as a function of
the *displaced* argument rather than of the coefficient. -/
noncomputable def twistProj (q : L) (l : ℕ) (m : ℤ) (F : Total L) : Lambda L :=
  MvPolynomial.constantCoeff (dminus q 1 ((auxVar 1 : Total L) ^ l * bopExt q m F))

theorem twistDop_eq_twistProj (q u : L) (l : ℕ) (m : ℤ) (g : Lambda L) :
    twistDop q u l m g = twistProj q l m (dplusStar q u 0 (MvPolynomial.C g : Total L)) := rfl

theorem twistProj_add (q : L) (l : ℕ) (m : ℤ) (F G : Total L) :
    twistProj q l m (F + G) = twistProj q l m F + twistProj q l m G := by
  simp only [twistProj, map_add, mul_add]

theorem twistProj_sub (q : L) (l : ℕ) (m : ℤ) (F G : Total L) :
    twistProj q l m (F - G) = twistProj q l m F - twistProj q l m G := by
  simp only [twistProj, map_sub, mul_sub]

theorem twistProj_smul (q : L) (l : ℕ) (m : ℤ) (x : L) (F : Total L) :
    twistProj q l m (x • F) = x • twistProj q l m F := by
  rw [twistProj, twistProj, map_smul, mul_smul_comm, map_smul, constantCoeff_smul]

/-- **`ct(d_-^{(1)}(y_1^l·B_m(x·y_1^jCf))) = x·B_{l+j}(B_mf)`**: the one graded term the displaced
argument is built from. `HJO.Sweep.bopExt_smul_auxVar_pow_mul_C` carries `B_m` onto the coefficient,
the two powers of the letter add, and `HJO.Sweep.dminus_one_auxVar_pow_mul_C` reads the total
exponent as the outer Hall--Littlewood index. Unconditional. -/
theorem twistProj_smul_auxVar_pow_mul_C (q : L) (l : ℕ) (m : ℤ) (x : L) (j : ℕ) (f : Lambda L) :
    twistProj q l m (x • ((auxVar 1 : Total L) ^ j * MvPolynomial.C f))
      = x • Bop q ((l + j : ℕ) : ℤ) (Bop q m f) := by
  rw [twistProj, bopExt_smul_auxVar_pow_mul_C, mul_smul_comm,
    show (auxVar 1 : Total L) ^ l * ((auxVar 1 : Total L) ^ j * MvPolynomial.C (Bop q m f))
        = (auxVar 1 : Total L) ^ (l + j) * MvPolynomial.C (Bop q m f) from by
      rw [pow_add]; ring,
    map_smul, constantCoeff_smul, dminus_one_auxVar_pow_mul_C, MvPolynomial.constantCoeff_C]

/-- The `j = 0` row of `HJO.Sweep.twistProj_smul_auxVar_pow_mul_C`, at the shape `Cf` in which the
`Λ`-constant term of a displacement is written. -/
theorem twistProj_C (q : L) (l : ℕ) (m : ℤ) (f : Lambda L) :
    twistProj q l m (MvPolynomial.C f : Total L) = Bop q (l : ℤ) (Bop q m f) := by
  rw [twistProj, bopExt_C, dminus_one_auxVar_pow_mul_C, MvPolynomial.constantCoeff_C]

theorem twistDop_add (q u : L) (l : ℕ) (m : ℤ) (g h : Lambda L) :
    twistDop q u l m (g + h) = twistDop q u l m g + twistDop q u l m h := by
  rw [twistDop_eq_twistProj, twistDop_eq_twistProj, twistDop_eq_twistProj, map_add, map_add,
    twistProj_add]

/-! ### The defect sum is additive in the vector -/

/-- The defect sum may be taken over any superset of the support: off the support the coefficient is
`0` and `HJO.Sweep.twistDop_zero` kills the summand. -/
theorem sum_twistDop_eq_of_subset (q u : L) (l : ℕ) {F : Total L} {s : Finset (ℕ →₀ ℕ)}
    (hs : F.support ⊆ s) :
    ∑ d ∈ F.support, twistDop q u l ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d F)
      = ∑ d ∈ s, twistDop q u l ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d F) := by
  refine Finset.sum_subset hs fun d _ hd => ?_
  rw [MvPolynomial.notMem_support_iff.1 hd, twistDop_zero]

/-- **The defect sum is additive.** Both sides are read over the union of the three supports by
`HJO.Sweep.sum_twistDop_eq_of_subset`, where `MvPolynomial.coeff_add` and
`HJO.Sweep.twistDop_add` finish it. This is what lets an explicitly expanded vector be fed to the
defect one monomial at a time. Unconditional. -/
theorem sum_twistDop_add (q u : L) (l : ℕ) (F G : Total L) :
    ∑ d ∈ (F + G).support, twistDop q u l ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d (F + G))
      = (∑ d ∈ F.support, twistDop q u l ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d F))
        + ∑ d ∈ G.support, twistDop q u l ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d G) := by
  classical
  have h1 : (F + G).support ⊆ (F + G).support ∪ (F.support ∪ G.support) := Finset.subset_union_left
  have h2 : F.support ⊆ (F + G).support ∪ (F.support ∪ G.support) :=
    fun d hd => Finset.mem_union_right _ (Finset.mem_union_left _ hd)
  have h3 : G.support ⊆ (F + G).support ∪ (F.support ∪ G.support) :=
    fun d hd => Finset.mem_union_right _ (Finset.mem_union_right _ hd)
  rw [sum_twistDop_eq_of_subset q u l h1, sum_twistDop_eq_of_subset q u l h2,
    sum_twistDop_eq_of_subset q u l h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_add, twistDop_add]

/-- The defect sum at a scalar multiple of one monomial of `V_1`. Unconditional: at `x = 0` or
`a = 0` both sides are `0` by `HJO.Sweep.twistDop_zero`. -/
theorem sum_twistDop_smul_auxVar_pow_mul_C (q u : L) (l j : ℕ) (x : L) (a : Lambda L) :
    ∑ d ∈ (x • ((auxVar 1 : Total L) ^ j * MvPolynomial.C a)).support,
        twistDop q u l ((d 0 : ℕ) : ℤ)
          (MvPolynomial.coeff d (x • ((auxVar 1 : Total L) ^ j * MvPolynomial.C a)))
      = x • twistDop q u l (j : ℤ) a := by
  rw [show x • ((auxVar 1 : Total L) ^ j * MvPolynomial.C a)
      = (auxVar 1 : Total L) ^ j * MvPolynomial.C (x • a) from by
    rw [C_smul_total, mul_smul_comm], sum_twistDop_auxVar_pow_mul_C, twistDop_smul]

/-! ### The defect sum through the one-letter evaluation -/

/-- **THE DEFECT SUM AT EVERY `l` AND ON ALL OF `V_1`, as a value:**

  `γ·∑_m T_{l,m}(F_m) = γ·D_l(ct(d_-^{(1)}F)) - ct(d_-^{(1)}(y_1^lz_1F))`,  `γ = q/(1-q)`.

This is `HJO.Sweep.constantCoeff_dminus_one_auxVar_pow_mul_zopOneStar_one_of_mem_piece` solved for
the defect sum, and it is what makes the two defects of the one-part step **computable**: their
right-hand sides are a value of `HJO.Sym.DopInt` on a known value and one known `z_1` evaluation,
with no `HJO.Sweep.twistDop` left in them.

`γ` is carried on the left and never inverted, so there is **no hypothesis on `q` or `u`**: at
`q = 0` and `q = 1` both sides are `0`. `F ∈ V_1` is the one-letter evaluation's own. -/
theorem smul_sum_twistDop_of_mem_piece (q u : L) (l : ℕ) {F : Total L} (hF : F ∈ piece L 1) :
    (q / (1 - q)) • ∑ d ∈ F.support, twistDop q u l ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d F)
      = (q / (1 - q)) • Dop q u l (MvPolynomial.constantCoeff (dminus q 1 F))
        - MvPolynomial.constantCoeff
            (dminus q 1 ((auxVar 1 : Total L) ^ l * zopOneStar q u 1 F)) := by
  rw [constantCoeff_dminus_one_auxVar_pow_mul_zopOneStar_one_of_mem_piece q u l hF, smul_sub]
  abel

/-! ### The values of `T_{l,m}` the one-part defects at `[1]` read -/

/-- `T_{2,3}(1) = B_2(B_3(1)) = -B_2(e_3)`: the displacement fixes the vacuum, so the whole value is
one Hall--Littlewood composite. Unconditional. -/
theorem twistDop_two_three_one (q u : L) :
    twistDop q u 2 ((3 : ℕ) : ℤ) (1 : Lambda L)
      = (-q ^ 3 + q ^ 2) • elemSymm L 5
        + (-q ^ 2 + q) • (elemSymm L 1 * elemSymm L 4)
        + (-q) • (elemSymm L 2 * elemSymm L 3) := by
  rw [twistDop_eq_twistProj, dplusStar_C_one, twistProj_C, bop_three_one', map_neg,
    bop_two_elemSymm_three]
  module

/-- `T_{2,2}(e_1)`. The displacement `d^*_+(Ce_1) = Ce_1 + (q-1)uy_1` has two graded terms, so the
value is `B_2(B_2e_1) + (q-1)u·B_3(B_2(1))`. Unconditional. -/
theorem twistDop_two_two_elemSymm_one (q u : L) :
    twistDop q u 2 ((2 : ℕ) : ℤ) (elemSymm L 1)
      = (q ^ 4 - q ^ 3 * u - q ^ 3 + 2 * q ^ 2 * u - q ^ 2 - q * u + q) • elemSymm L 5
        + (q ^ 3 - q ^ 2 * u + 2 * q * u - 2 * q - u + 1) • (elemSymm L 1 * elemSymm L 4)
        + (q ^ 2 - q * u + u - 1) • (elemSymm L 2 * elemSymm L 3)
        + (q - 1) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
        + (1 : L) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_one_expand, twistProj_add, twistProj_C,
    twistProj_smul_auxVar_pow_mul_C, show (2 + 1 : ℕ) = 3 from rfl, bop_two_elemSymm_one',
    bop_two_one, bop_three_elemSymm_two]
  simp only [map_add, map_sub, map_neg, map_smul]
  rw [bop_two_elemSymm_one_mul_two, bop_two_elemSymm_three]
  module

/-- `T_{1,3}(e_2)`. Three graded terms of `d^*_+(Ce_2)`, so
`B_1(B_3e_2) + (q-1)u·B_2(B_3e_1) + (1-q)u^2·B_3(B_3(1))`. Unconditional. -/
theorem twistDop_one_three_elemSymm_two (q u : L) :
    twistDop q u 1 ((3 : ℕ) : ℤ) (elemSymm L 2)
      = (q ^ 7 - q ^ 6 * u - q ^ 6 + 2 * q ^ 5 * u - q ^ 5 - q ^ 4 * u ^ 2 + q ^ 4
            + 2 * q ^ 3 * u ^ 2 - 2 * q ^ 3 * u - q ^ 2 * u ^ 2 + q ^ 2 * u) • elemSymm L 6
        + (q ^ 6 - q ^ 5 * u + q ^ 4 * u - 2 * q ^ 4 - q ^ 3 * u ^ 2 + 2 * q ^ 3 * u
            + 2 * q ^ 2 * u ^ 2 - 3 * q ^ 2 * u + 2 * q ^ 2 - q * u ^ 2 + q * u - q)
            • (elemSymm L 1 * elemSymm L 5)
        + (q ^ 5 - q ^ 4 * u - q ^ 4 + 2 * q ^ 3 * u + q ^ 3 - q ^ 2 * u ^ 2 - q ^ 2 * u - q ^ 2
            + 2 * q * u ^ 2 - q - u ^ 2 + 1) • (elemSymm L 2 * elemSymm L 4)
        + (q ^ 4 - q ^ 3 * u - q ^ 3 + 2 * q ^ 2 * u - q ^ 2 - q * u ^ 2 - q * u + 2 * q + u ^ 2
            - 1) • (elemSymm L 3 * elemSymm L 3)
        + (q ^ 4 - q ^ 3 * u - q ^ 3 + 2 * q ^ 2 * u - q ^ 2 - q * u + 2 * q - 1)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (q ^ 3 - q ^ 2 * u + q ^ 2 + q * u - 3 * q + 2)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))
        + (q - 1) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2)) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_two_expand, twistProj_add, twistProj_add,
    twistProj_C, twistProj_smul_auxVar_pow_mul_C, twistProj_smul_auxVar_pow_mul_C,
    show (1 + 1 : ℕ) = 2 from rfl, show (1 + 2 : ℕ) = 3 from rfl, bop_three_elemSymm_two,
    bop_three_elemSymm_one, bop_three_one']
  simp only [map_add, map_sub, map_neg, map_smul]
  rw [bop_one_elemSymm_five, bop_one_elemSymm_two_mul_three, bop_one_elemSymm_one_mul_four,
    bop_two_elemSymm_one_mul_three, bop_two_elemSymm_four, bop_three_elemSymm_three]
  module

/-- `T_{1,3}(e_1^2)`. Unconditional. -/
theorem twistDop_one_three_elemSymm_one_sq (q u : L) :
    twistDop q u 1 ((3 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1)
      = (q ^ 7 - 2 * q ^ 6 * u - q ^ 6 + q ^ 5 * u ^ 2 + 4 * q ^ 5 * u - 2 * q ^ 5
            - 3 * q ^ 4 * u ^ 2 + 2 * q ^ 4 + 3 * q ^ 3 * u ^ 2 - 4 * q ^ 3 * u + q ^ 3
            - q ^ 2 * u ^ 2 + 2 * q ^ 2 * u - q ^ 2) • elemSymm L 6
        + (q ^ 6 - 2 * q ^ 5 * u + q ^ 5 + q ^ 4 * u ^ 2 + 2 * q ^ 4 * u - 4 * q ^ 4
            - 3 * q ^ 3 * u ^ 2 + 4 * q ^ 3 * u + 3 * q ^ 2 * u ^ 2 - 6 * q ^ 2 * u + 4 * q ^ 2
            - q * u ^ 2 + 2 * q * u - 3 * q + 1) • (elemSymm L 1 * elemSymm L 5)
        + (q ^ 5 - 2 * q ^ 4 * u - q ^ 4 + q ^ 3 * u ^ 2 + 4 * q ^ 3 * u - q ^ 3
            - 3 * q ^ 2 * u ^ 2 - 2 * q ^ 2 * u + q ^ 2 + 3 * q * u ^ 2 - u ^ 2)
            • (elemSymm L 2 * elemSymm L 4)
        + (q ^ 4 - 2 * q ^ 3 * u - q ^ 3 + q ^ 2 * u ^ 2 + 4 * q ^ 2 * u - 2 * q ^ 2
            - 2 * q * u ^ 2 - 2 * q * u + 3 * q + u ^ 2 - 1) • (elemSymm L 3 * elemSymm L 3)
        + (2 * q ^ 4 - 2 * q ^ 3 * u - q ^ 3 + 4 * q ^ 2 * u - 3 * q ^ 2 - 2 * q * u + 4 * q - 2)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (2 * q ^ 3 - 2 * q ^ 2 * u + 2 * q * u - 4 * q + 2)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))
        + (q ^ 2 - q + 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (q - 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_one_sq_expand, twistProj_add, twistProj_add,
    twistProj_C, twistProj_smul_auxVar_pow_mul_C, twistProj_smul_auxVar_pow_mul_C,
    show (1 + 1 : ℕ) = 2 from rfl, show (1 + 2 : ℕ) = 3 from rfl, bop_three_elemSymm_one_sq,
    bop_three_elemSymm_one, bop_three_one']
  simp only [map_add, map_sub, map_neg, map_smul]
  rw [bop_one_elemSymm_five, bop_one_elemSymm_one_sq_mul_three, bop_one_elemSymm_one_mul_four,
    bop_two_elemSymm_one_mul_three, bop_two_elemSymm_four, bop_three_elemSymm_three]
  module

/-- `T_{1,4}(e_1)`. Unconditional. -/
theorem twistDop_one_four_elemSymm_one (q u : L) :
    twistDop q u 1 ((4 : ℕ) : ℤ) (elemSymm L 1)
      = (-q ^ 6 + q ^ 5 * u + q ^ 5 - 2 * q ^ 4 * u + q ^ 4 + q ^ 3 * u - q ^ 3) • elemSymm L 6
        + (-q ^ 5 + q ^ 4 * u - 2 * q ^ 3 * u + 2 * q ^ 3 + q ^ 2 * u - q ^ 2 - q + 1)
            • (elemSymm L 1 * elemSymm L 5)
        + (-q ^ 4 + q ^ 3 * u + q ^ 3 - 2 * q ^ 2 * u + 2 * q * u - u)
            • (elemSymm L 2 * elemSymm L 4)
        + (-q ^ 3 + q ^ 2 * u + q ^ 2 - 2 * q * u + q + u - 1) • (elemSymm L 3 * elemSymm L 3)
        + (-q ^ 3 + q ^ 2 - 1) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (1 - q ^ 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_one_expand, twistProj_add, twistProj_C,
    twistProj_smul_auxVar_pow_mul_C, show (1 + 1 : ℕ) = 2 from rfl, bop_four_elemSymm_one,
    bop_four_one]
  simp only [map_add, map_sub, map_neg, map_smul]
  rw [bop_one_elemSymm_one_mul_four, bop_one_elemSymm_five, bop_two_elemSymm_four]
  module

/-- `T_{1,5}(1) = B_1(B_5(1)) = -B_1(e_5)`. Unconditional. -/
theorem twistDop_one_five_one (q u : L) :
    twistDop q u 1 ((5 : ℕ) : ℤ) (1 : Lambda L)
      = (q ^ 5 - q ^ 4) • elemSymm L 6
        + (q ^ 4 - q ^ 3 + 1) • (elemSymm L 1 * elemSymm L 5)
        + (q ^ 3 - q ^ 2 + q - 1) • (elemSymm L 2 * elemSymm L 4)
        + (q ^ 2 - q) • (elemSymm L 3 * elemSymm L 3) := by
  rw [twistDop_eq_twistProj, dplusStar_C_one, twistProj_C, bop_five_one, map_neg,
    bop_one_elemSymm_five]
  module

/-! ### The values of `T_{2,m}` the inner defect at `[2]` reads

One per monomial of `HJO.Mellit.stageWordTotal_two_three_two_eq`, each off the graded
displacement of its coefficient and the Hall--Littlewood table. All unconditional. -/

/-- `T_{2,2}(e4)`. Unconditional. -/
theorem twistDop_two_two_elemSymm_four (q u : L) :
    twistDop q u 2 ((2 : ℕ) : ℤ) (elemSymm L 4)
      = (q^10 - q^9*u - q^9 + 2*q^8*u - q^8 - q^7*u^2 + q^7 + 2*q^6*u^2 - 2*q^6*u - q^5*u^3
            + q^5*u + 2*q^4*u^3 - 2*q^4*u^2 - q^3*u^4 + q^3*u^2 + 2*q^2*u^4 - 2*q^2*u^3 - q*u^4
            + q*u^3) • (elemSymm L 8)
        + (q^9 - q^8*u + q^7*u - 2*q^7 - q^6*u^2 + 2*q^6*u + q^5*u^2 - 2*q^5*u + q^5 - q^4*u^3
            + 2*q^4*u^2 - q^4*u + q^3*u^3 - 2*q^3*u^2 + q^3*u - q^2*u^4 + 2*q^2*u^3 - q^2*u^2
            + 2*q*u^4 - 3*q*u^3 + q*u^2 - u^4 + u^3) • (elemSymm L 1 * elemSymm L 7)
        + (q^8 - q^7*u - q^7 + 2*q^6*u - q^5*u^2 - q^5*u + 2*q^4*u^2 - q^3*u^3 - q^3*u^2 + q^3
            + 2*q^2*u^3 - q^2*u^2 - q^2 - q*u^4 - q*u^3 + 2*q*u^2 + u^4 - u^2)
            • (elemSymm L 2 * elemSymm L 6)
        + (q^7 - q^6*u - q^6 + 2*q^5*u - q^4*u^2 - q^4*u + q^4 + 2*q^3*u^2 - q^3*u - 2*q^3
            - q^2*u^3 + 2*q^2*u + 2*q*u^3 - 2*q*u^2 - q*u + q - u^3 + u^2)
            • (elemSymm L 3 * elemSymm L 5)
        + (q^6 - q^5*u - q^5 + 2*q^4*u - q^4 - q^3*u^2 + q^3 + 2*q^2*u^2 - 2*q^2*u + q^2 - q*u^2
            + q*u - q) • (elemSymm L 4 * elemSymm L 4)
        + (q^7 - q^6*u - q^6 + 2*q^5*u - q^5 - q^4*u^2 + q^4 + 2*q^3*u^2 - 2*q^3*u - q^2*u^3
            + q^2*u + 2*q*u^3 - 2*q*u^2 - u^3 + u^2)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6))
        + (q^6 - q^5*u + q^4*u - 2*q^4 - q^3*u^2 + 2*q^3*u + q^3 + q^2*u^2 - 3*q^2*u + q^2
            - q*u^3 + q*u^2 + q*u - q + u^3 - u^2)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5))
        + (q^5 - q^4*u + q^3*u - q^3 - q^2*u^2 + q^2*u - q^2 + 2*q*u^2 - q*u + q - u^2)
            • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))
        + (q^4 - q^3*u - q^3 + 2*q^2*u - q*u^2 - q*u + q + u^2)
            • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4))
        + (q^3 - q^2*u + q*u - q) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3)) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_four_expand]
  simp only [twistProj_add, twistProj_C, twistProj_smul_auxVar_pow_mul_C, Nat.reduceAdd]
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, bop_two_one, bop_three_one', bop_four_one, bop_five_one, bop_six_one,
    bop_seven_one, bop_eight_one, bop_two_elemSymm_one', bop_three_elemSymm_one,
    bop_four_elemSymm_one, bop_five_elemSymm_one, bop_two_elemSymm_two', bop_three_elemSymm_two,
    bop_four_elemSymm_two, bop_five_elemSymm_two, bop_six_elemSymm_two,
    bop_two_elemSymm_three, bop_three_elemSymm_three,
    bop_four_elemSymm_three, bop_five_elemSymm_three, bop_two_elemSymm_four,
    bop_three_elemSymm_four, bop_four_elemSymm_four, bop_two_elemSymm_five,
    bop_three_elemSymm_five, bop_two_elemSymm_six, Nat.reduceAdd, map_add, map_sub, map_neg,
    map_smul]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `T_{2,2}(e2e2)`. Unconditional. -/
theorem twistDop_two_two_elemSymm_two_sq (q u : L) :
    twistDop q u 2 ((2 : ℕ) : ℤ) (elemSymm L 2 * elemSymm L 2)
      = (q^10 - 2*q^9*u - q^9 + q^8*u^2 + 4*q^8*u - 2*q^8 - 5*q^7*u^2 + 2*q^7*u + 2*q^7
            + 2*q^6*u^3 + 5*q^6*u^2 - 8*q^6*u + q^6 - 6*q^5*u^3 + 5*q^5*u^2 + 2*q^5*u - q^5
            + q^4*u^4 + 4*q^4*u^3 - 9*q^4*u^2 + 4*q^4*u - 3*q^3*u^4 + 4*q^3*u^3 + q^3*u^2
            - 2*q^3*u + 3*q^2*u^4 - 6*q^2*u^3 + 3*q^2*u^2 - q*u^4 + 2*q*u^3 - q*u^2)
            • (elemSymm L 8)
        + (q^9 - 2*q^8*u + q^8 + q^7*u^2 - 4*q^7 - 3*q^6*u^2 + 10*q^6*u - 2*q^6 + 2*q^5*u^3
            - 3*q^5*u^2 - 6*q^5*u + 5*q^5 - 4*q^4*u^3 + 13*q^4*u^2 - 10*q^4*u + q^4 + q^3*u^4
            - 2*q^3*u^3 - 5*q^3*u^2 + 8*q^3*u - 2*q^3 - 3*q^2*u^4 + 10*q^2*u^3 - 9*q^2*u^2
            + 2*q^2*u + 3*q*u^4 - 8*q*u^3 + 7*q*u^2 - 2*q*u - u^4 + 2*u^3 - u^2)
            • (elemSymm L 1 * elemSymm L 7)
        + (q^8 - 2*q^7*u - q^7 + q^6*u^2 + 4*q^6*u - 5*q^5*u^2 + 2*q^4*u^3 + 5*q^4*u^2 - 4*q^4*u
            - 6*q^3*u^3 + 4*q^3*u^2 + q^2*u^4 + 6*q^2*u^3 - 11*q^2*u^2 + 6*q^2*u - q^2 - 2*q*u^4
            - 2*q*u^3 + 9*q*u^2 - 6*q*u + q + u^4 - 3*u^2 + 2*u)
            • (elemSymm L 2 * elemSymm L 6)
        + (q^7 - 2*q^6*u - q^6 + q^5*u^2 + 4*q^5*u - q^5 - 5*q^4*u^2 + q^4 + 2*q^3*u^3
            + 6*q^3*u^2 - 4*q^3*u - q^3 - 6*q^2*u^3 + 2*q^2*u^2 + 2*q^2*u + q^2 + 6*q*u^3
            - 7*q*u^2 + q - 2*u^3 + 3*u^2 - 1) • (elemSymm L 3 * elemSymm L 5)
        + (q^6 - 2*q^5*u - q^5 + q^4*u^2 + 4*q^4*u - 2*q^4 - 6*q^3*u^2 + 2*q^3*u + 3*q^3
            + 10*q^2*u^2 - 10*q^2*u - 6*q*u^2 + 8*q*u - 2*q + u^2 - 2*u + 1)
            • (elemSymm L 4 * elemSymm L 4)
        + (2*q^7 - 4*q^6*u - q^6 + 2*q^5*u^2 + 6*q^5*u - 5*q^5 - 7*q^4*u^2 + 6*q^4*u + 2*q^4
            + 2*q^3*u^3 + 5*q^3*u^2 - 12*q^3*u + 4*q^3 - 6*q^2*u^3 + 7*q^2*u^2 - q^2 + 6*q*u^3
            - 11*q*u^2 + 6*q*u - q - 2*u^3 + 4*u^2 - 2*u)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6))
        + (2*q^6 - 4*q^5*u + 2*q^4*u^2 + 6*q^4*u - 4*q^4 - 8*q^3*u^2 + 4*q^3*u + 2*q^3
            + 2*q^2*u^3 + 8*q^2*u^2 - 12*q^2*u - 4*q*u^3 + 8*q*u - 2*q + 2*u^3 - 2*u^2 - 2*u + 2)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5))
        + (2*q^5 - 4*q^4*u + 2*q^3*u^2 + 4*q^3*u - 6*q^3 - 8*q^2*u^2 + 10*q^2*u + 2*q^2
            + 10*q*u^2 - 16*q*u + 4*q - 4*u^2 + 6*u - 2)
            • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))
        + (2*q^4 - 2*q^3*u - 2*q^3 + 4*q^2*u + q^2 - 2*q*u^2 - 2*q*u + q + 2*u^2 - 2)
            • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4))
        + (2*q^3 - 2*q^2*u - 2*q^2 + 4*q*u - 2*q - 2*u + 2)
            • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3))
        + (q^5 - 2*q^4*u - q^4 + q^3*u^2 + 4*q^3*u - 2*q^3 - 3*q^2*u^2 + 2*q^2 + 3*q*u^2 - 4*q*u
            + q - u^2 + 2*u - 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (q^4 - 2*q^3*u + q^3 + q^2*u^2 + 2*q^2*u - 3*q^2 - 2*q*u^2 + 2*q*u - q + u^2 - 2*u + 2)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (q^3 - 2*q^2*u - q^2 + 4*q*u - q - 2*u + 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3)))
        + (2*q^2 - 2*q*u + q + 2*u - 3)
            • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3)))
        + (1) • (elemSymm L 2 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_two_sq_expand]
  simp only [twistProj_add, twistProj_C, twistProj_smul_auxVar_pow_mul_C, Nat.reduceAdd]
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, bop_two_one, bop_three_one', bop_four_one, bop_five_one, bop_six_one,
    bop_seven_one, bop_eight_one, bop_two_elemSymm_one', bop_three_elemSymm_one,
    bop_four_elemSymm_one, bop_five_elemSymm_one, bop_two_elemSymm_two', bop_three_elemSymm_two,
    bop_four_elemSymm_two, bop_five_elemSymm_two, bop_six_elemSymm_two,
    bop_two_elemSymm_three, bop_three_elemSymm_three,
    bop_four_elemSymm_three, bop_five_elemSymm_three, bop_two_elemSymm_four,
    bop_three_elemSymm_four, bop_four_elemSymm_four, bop_two_elemSymm_five,
    bop_three_elemSymm_five, bop_two_elemSymm_six, Nat.reduceAdd, map_add, map_sub, map_neg,
    map_smul]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `T_{2,2}(e1e3)`. Unconditional. -/
theorem twistDop_two_two_elemSymm_one_mul_three (q u : L) :
    twistDop q u 2 ((2 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 3)
      = (q^10 - 2*q^9*u - q^9 + q^8*u^2 + 4*q^8*u - 2*q^8 - 4*q^7*u^2 + q^7*u + 2*q^7 + q^6*u^3
            + 4*q^6*u^2 - 6*q^6*u + q^6 - 4*q^5*u^3 + 3*q^5*u^2 + 2*q^5*u - q^5 + q^4*u^4
            + 4*q^4*u^3 - 7*q^4*u^2 + 2*q^4*u - 3*q^3*u^4 + 2*q^3*u^3 + 2*q^3*u^2 - q^3*u
            + 3*q^2*u^4 - 5*q^2*u^3 + 2*q^2*u^2 - q*u^4 + 2*q*u^3 - q*u^2)
            • (elemSymm L 8)
        + (q^9 - 2*q^8*u + q^8 + q^7*u^2 + q^7*u - 4*q^7 - 3*q^6*u^2 + 7*q^6*u - q^6 + q^5*u^3
            - q^5*u^2 - 5*q^5*u + 4*q^5 - 3*q^4*u^3 + 9*q^4*u^2 - 6*q^4*u + q^3*u^4 - 5*q^3*u^2
            + 5*q^3*u - q^3 - 3*q^2*u^4 + 7*q^2*u^3 - 5*q^2*u^2 + q^2*u + 3*q*u^4 - 7*q*u^3
            + 5*q*u^2 - q*u - u^4 + 2*u^3 - u^2) • (elemSymm L 1 * elemSymm L 7)
        + (q^8 - 2*q^7*u - q^7 + q^6*u^2 + 4*q^6*u - q^6 - 4*q^5*u^2 - q^5*u + q^5 + q^4*u^3
            + 5*q^4*u^2 - 2*q^4*u - 4*q^3*u^3 + q^3*u^2 + q^2*u^4 + 5*q^2*u^3 - 8*q^2*u^2
            + 3*q^2*u - 2*q*u^4 - 2*q*u^3 + 7*q*u^2 - 3*q*u + u^4 - 2*u^2 + u)
            • (elemSymm L 2 * elemSymm L 6)
        + (q^7 - 2*q^6*u - q^6 + q^5*u^2 + 4*q^5*u - q^5 - 4*q^4*u^2 - q^4*u + 2*q^4 + q^3*u^3
            + 4*q^3*u^2 - 3*q^3*u - q^3 - 4*q^2*u^3 + 2*q^2*u^2 + 3*q^2*u - q^2 + 5*q*u^3
            - 5*q*u^2 - q*u + q - 2*u^3 + 2*u^2) • (elemSymm L 3 * elemSymm L 5)
        + (q^6 - 2*q^5*u - q^5 + q^4*u^2 + 4*q^4*u - 2*q^4 - 4*q^3*u^2 + q^3*u + 2*q^3
            + 6*q^2*u^2 - 7*q^2*u + q^2 - 4*q*u^2 + 5*q*u - q + u^2 - u)
            • (elemSymm L 4 * elemSymm L 4)
        + (2*q^7 - 3*q^6*u - q^6 + q^5*u^2 + 5*q^5*u - 4*q^5 - 5*q^4*u^2 + 3*q^4*u + 2*q^4
            + q^3*u^3 + 5*q^3*u^2 - 8*q^3*u + 2*q^3 - 4*q^2*u^3 + 4*q^2*u^2 + q^2*u - q^2
            + 5*q*u^3 - 8*q*u^2 + 3*q*u - 2*u^3 + 3*u^2 - u)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6))
        + (2*q^6 - 3*q^5*u - q^5 + q^4*u^2 + 4*q^4*u - 3*q^4 - 4*q^3*u^2 + 4*q^3*u + 2*q^3
            + q^2*u^3 + 4*q^2*u^2 - 9*q^2*u + q^2 - 3*q*u^3 + 5*q*u - q + 2*u^3 - u^2 - u)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5))
        + (2*q^5 - 3*q^4*u + q^3*u^2 + 3*q^3*u - 4*q^3 - 5*q^2*u^2 + 6*q^2*u + q^2 + 7*q*u^2
            - 9*q*u + q - 3*u^2 + 3*u)
            • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))
        + (q^4 - 2*q^3*u - q^3 + q^2*u^2 + 4*q^2*u - q^2 - 2*q*u^2 - 2*q*u + q + u^2)
            • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4))
        + (q^3 - 2*q^2*u + 3*q*u - q - u)
            • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3))
        + (q^5 - q^4*u - q^4 + 2*q^3*u - q^3 - q^2*u^2 + q^2 + 2*q*u^2 - 2*q*u - u^2 + u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (q^4 - q^3*u + q^2*u - q^2 - q*u^2 + q*u + u^2 - u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (q^3 - q^2*u - q^2 + 2*q*u - u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3)))
        + (q^2 - q*u + u)
            • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3))) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_one_mul_three_expand]
  simp only [twistProj_add, twistProj_C, twistProj_smul_auxVar_pow_mul_C, Nat.reduceAdd]
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, bop_two_one, bop_three_one', bop_four_one, bop_five_one, bop_six_one,
    bop_seven_one, bop_eight_one, bop_two_elemSymm_one', bop_three_elemSymm_one,
    bop_four_elemSymm_one, bop_five_elemSymm_one, bop_two_elemSymm_two', bop_three_elemSymm_two,
    bop_four_elemSymm_two, bop_five_elemSymm_two, bop_six_elemSymm_two,
    bop_two_elemSymm_three, bop_three_elemSymm_three,
    bop_four_elemSymm_three, bop_five_elemSymm_three, bop_two_elemSymm_four,
    bop_three_elemSymm_four, bop_four_elemSymm_four, bop_two_elemSymm_five,
    bop_three_elemSymm_five, bop_two_elemSymm_six, Nat.reduceAdd, map_add, map_sub, map_neg,
    map_smul]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `T_{2,2}(e1e1e2)`. Unconditional. -/
theorem twistDop_two_two_elemSymm_one_sq_mul_two (q u : L) :
    twistDop q u 2 ((2 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))
      = (q^10 - 3*q^9*u - q^9 + 3*q^8*u^2 + 6*q^8*u - 3*q^8 - q^7*u^3 - 10*q^7*u^2 + 4*q^7*u
            + 3*q^7 + 6*q^6*u^3 + 6*q^6*u^2 - 14*q^6*u + 3*q^6 - q^5*u^4 - 11*q^5*u^3 + 13*q^5*u^2
            + 2*q^5*u - 3*q^5 + 4*q^4*u^4 + 4*q^4*u^3 - 17*q^4*u^2 + 10*q^4*u - q^4 - 6*q^3*u^4
            + 9*q^3*u^3 - 4*q^3*u + q^3 + 4*q^2*u^4 - 10*q^2*u^3 + 8*q^2*u^2 - 2*q^2*u - q*u^4
            + 3*q*u^3 - 3*q*u^2 + q*u) • (elemSymm L 8)
        + (q^9 - 3*q^8*u + 2*q^8 + 3*q^7*u^2 - q^7*u - 6*q^7 - q^6*u^3 - 5*q^6*u^2 + 18*q^6*u
            - 4*q^6 + 5*q^5*u^3 - 11*q^5*u^2 - 9*q^5*u + 10*q^5 - q^4*u^4 - 5*q^4*u^3 + 27*q^4*u^2
            - 22*q^4*u + 2*q^4 + 4*q^3*u^4 - 8*q^3*u^3 - 7*q^3*u^2 + 17*q^3*u - 6*q^3 - 6*q^2*u^4
            + 19*q^2*u^3 - 19*q^2*u^2 + 6*q^2*u + 4*q*u^4 - 13*q*u^3 + 15*q*u^2 - 7*q*u + q - u^4
            + 3*u^3 - 3*u^2 + u) • (elemSymm L 1 * elemSymm L 7)
        + (q^8 - 3*q^7*u - q^7 + 3*q^6*u^2 + 6*q^6*u - 2*q^6 - q^5*u^3 - 10*q^5*u^2 + 2*q^5*u
            + 2*q^5 + 6*q^4*u^3 + 7*q^4*u^2 - 10*q^4*u + 2*q^4 - q^3*u^4 - 12*q^3*u^3 + 13*q^3*u^2
            - q^3*u - 3*q^3 + 3*q^2*u^4 + 10*q^2*u^3 - 26*q^2*u^2 + 16*q^2*u - 3*q*u^4 - 3*q*u^3
            + 17*q*u^2 - 14*q*u + 2*q + u^4 - 4*u^2 + 4*u - 1)
            • (elemSymm L 2 * elemSymm L 6)
        + (q^7 - 3*q^6*u - q^6 + 3*q^5*u^2 + 6*q^5*u - 2*q^5 - q^4*u^3 - 10*q^4*u^2 + q^4*u
            + 2*q^4 + 6*q^3*u^3 + 8*q^3*u^2 - 8*q^3*u + q^3 - 12*q^2*u^3 + 6*q^2*u^2 + 3*q^2*u
            - q^2 + 10*q*u^3 - 11*q*u^2 + 2*q*u - 3*u^3 + 4*u^2 - u)
            • (elemSymm L 3 * elemSymm L 5)
        + (q^6 - 3*q^5*u - q^5 + 3*q^4*u^2 + 6*q^4*u - 3*q^4 - 12*q^3*u^2 + 4*q^3*u + 4*q^3
            + 18*q^2*u^2 - 18*q^2*u + q^2 - 12*q*u^2 + 15*q*u - 3*q + 3*u^2 - 4*u + 1)
            • (elemSymm L 4 * elemSymm L 4)
        + (3*q^7 - 7*q^6*u + 5*q^5*u^2 + 9*q^5*u - 10*q^5 - q^4*u^3 - 15*q^4*u^2 + 15*q^4*u
            + 2*q^4 + 6*q^3*u^3 + 7*q^3*u^2 - 24*q^3*u + 10*q^3 - 12*q^2*u^3 + 18*q^2*u^2
            - 3*q^2*u - 3*q^2 + 10*q*u^3 - 22*q*u^2 + 15*q*u - 3*q - 3*u^3 + 7*u^2 - 5*u + 1)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6))
        + (3*q^6 - 7*q^5*u - 2*q^5 + 5*q^4*u^2 + 12*q^4*u - 6*q^4 - q^3*u^3 - 16*q^3*u^2
            + 7*q^3*u + 6*q^3 + 5*q^2*u^3 + 16*q^2*u^2 - 27*q^2*u + q^2 - 7*q*u^3 - 4*q*u^2
            + 20*q*u - 4*q + 3*u^3 - u^2 - 5*u + 2)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5))
        + (3*q^5 - 7*q^4*u + 5*q^3*u^2 + 7*q^3*u - 10*q^3 - 17*q^2*u^2 + 19*q^2*u + 4*q^2
            + 19*q*u^2 - 31*q*u + 7*q - 7*u^2 + 12*u - 4)
            • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))
        + (q^4 - 2*q^3*u - q^3 + q^2*u^2 + 4*q^2*u - q^2 - 2*q*u^2 - 2*q*u + q + u^2)
            • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4))
        + (q^3 - 2*q^2*u - q^2 + 4*q*u - q - 2*u + 1)
            • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3))
        + (3*q^5 - 5*q^4*u - 2*q^4 + 2*q^3*u^2 + 9*q^3*u - 6*q^3 - 7*q^2*u^2 + 2*q^2*u + 4*q^2
            + 8*q*u^2 - 11*q*u + 3*q - 3*u^2 + 5*u - 2)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (3*q^4 - 5*q^3*u - q^3 + 2*q^2*u^2 + 8*q^2*u - 3*q^2 - 5*q*u^2 - q*u + 3*u^2 - 2*u + 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (3*q^3 - 5*q^2*u - 3*q^2 + 10*q*u - 3*q - 5*u + 3)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3)))
        + (2*q^2 - 2*q*u + 2*u - 2)
            • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3)))
        + (q^3 - q^2*u - q^2 + 2*q*u - q - u + 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))))
        + (q^2 - q*u + q + u - 2)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))))
        + (1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2)))) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_one_sq_mul_two_expand]
  simp only [twistProj_add, twistProj_C, twistProj_smul_auxVar_pow_mul_C, Nat.reduceAdd]
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, bop_two_one, bop_three_one', bop_four_one, bop_five_one, bop_six_one,
    bop_seven_one, bop_eight_one, bop_two_elemSymm_one', bop_three_elemSymm_one,
    bop_four_elemSymm_one, bop_five_elemSymm_one, bop_two_elemSymm_two', bop_three_elemSymm_two,
    bop_four_elemSymm_two, bop_five_elemSymm_two, bop_six_elemSymm_two,
    bop_two_elemSymm_three, bop_three_elemSymm_three,
    bop_four_elemSymm_three, bop_five_elemSymm_three, bop_two_elemSymm_four,
    bop_three_elemSymm_four, bop_four_elemSymm_four, bop_two_elemSymm_five,
    bop_three_elemSymm_five, bop_two_elemSymm_six, Nat.reduceAdd, map_add, map_sub, map_neg,
    map_smul]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `T_{2,3}(e3)`. Unconditional. -/
theorem twistDop_two_three_elemSymm_three (q u : L) :
    twistDop q u 2 ((3 : ℕ) : ℤ) (elemSymm L 3)
      = (-q^9 + q^8*u + q^8 - 2*q^7*u + q^7 + q^6*u^2 - q^6 - 2*q^5*u^2 + 2*q^5*u + q^4*u^3
            - q^4*u - 2*q^3*u^3 + 2*q^3*u^2 + q^2*u^3 - q^2*u^2) • (elemSymm L 8)
        + (-q^8 + q^7*u - q^6*u + 2*q^6 + q^5*u^2 - 2*q^5*u - q^4*u^2 + 2*q^4*u - q^4 + q^3*u^3
            - 2*q^3*u^2 + q^3*u - 2*q^2*u^3 + 3*q^2*u^2 - q^2*u + q*u^3 - q*u^2)
            • (elemSymm L 1 * elemSymm L 7)
        + (-q^7 + q^6*u + q^6 - 2*q^5*u + q^4*u^2 + q^4*u - 2*q^3*u^2 + q^2*u^3 - 2*q*u^3
            + 2*q*u^2 + u^3 - u^2) • (elemSymm L 2 * elemSymm L 6)
        + (-q^6 + q^5*u + q^5 - 2*q^4*u + q^3*u^2 + q^3*u - q^3 - 2*q^2*u^2 + q^2*u + q^2 + q*u^3
            + q*u^2 - 2*q*u - u^3 + u) • (elemSymm L 3 * elemSymm L 5)
        + (-q^5 + q^4*u + q^4 - 2*q^3*u + q^3 + q^2*u^2 - q^2 - 2*q*u^2 + 2*q*u + u^2 - u)
            • (elemSymm L 4 * elemSymm L 4)
        + (-q^6 + q^5*u + q^5 - 2*q^4*u + q^4 + q^3*u^2 - q^3 - 2*q^2*u^2 + 2*q^2*u + q*u^2 - q*u)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6))
        + (-q^5 + q^4*u - q^3*u + 2*q^3 + q^2*u^2 - 2*q^2*u - q^2 - 2*q*u^2 + 3*q*u + u^2 - u)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5))
        + (-q^4 + q^3*u - q^2*u + q^2 + q*u^2 - q*u - u^2 + u)
            • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))
        + (-q^3 + q^2*u + q^2 - 2*q*u + u)
            • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4))
        + (-q^2 + q*u - u) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3)) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_three_expand]
  simp only [twistProj_add, twistProj_C, twistProj_smul_auxVar_pow_mul_C, Nat.reduceAdd]
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, bop_two_one, bop_three_one', bop_four_one, bop_five_one, bop_six_one,
    bop_seven_one, bop_eight_one, bop_two_elemSymm_one', bop_three_elemSymm_one,
    bop_four_elemSymm_one, bop_five_elemSymm_one, bop_two_elemSymm_two', bop_three_elemSymm_two,
    bop_four_elemSymm_two, bop_five_elemSymm_two, bop_six_elemSymm_two,
    bop_two_elemSymm_three, bop_three_elemSymm_three,
    bop_four_elemSymm_three, bop_five_elemSymm_three, bop_two_elemSymm_four,
    bop_three_elemSymm_four, bop_four_elemSymm_four, bop_two_elemSymm_five,
    bop_three_elemSymm_five, bop_two_elemSymm_six, Nat.reduceAdd, map_add, map_sub, map_neg,
    map_smul]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `T_{2,3}(e1e2)`. Unconditional. -/
theorem twistDop_two_three_elemSymm_one_mul_two (q u : L) :
    twistDop q u 2 ((3 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 2)
      = (-q^9 + 2*q^8*u + q^8 - q^7*u^2 - 4*q^7*u + 2*q^7 + 4*q^6*u^2 - q^6*u - 2*q^6 - q^5*u^3
            - 4*q^5*u^2 + 6*q^5*u - q^5 + 3*q^4*u^3 - 2*q^4*u^2 - 2*q^4*u + q^4 - 3*q^3*u^3
            + 5*q^3*u^2 - 2*q^3*u + q^2*u^3 - 2*q^2*u^2 + q^2*u) • (elemSymm L 8)
        + (-q^8 + 2*q^7*u - q^7 - q^6*u^2 - q^6*u + 4*q^6 + 3*q^5*u^2 - 7*q^5*u + q^5 - q^4*u^3
            + 6*q^4*u - 4*q^4 + 3*q^3*u^3 - 7*q^3*u^2 + 4*q^3*u - 3*q^2*u^3 + 7*q^2*u^2 - 5*q^2*u
            + q^2 + q*u^3 - 2*q*u^2 + q*u) • (elemSymm L 1 * elemSymm L 7)
        + (-q^7 + 2*q^6*u + q^6 - q^5*u^2 - 4*q^5*u + q^5 + 4*q^4*u^2 - q^4 - q^3*u^3 - 4*q^3*u^2
            + 4*q^3*u - q^3 + 3*q^2*u^3 - 2*q^2*u^2 - q^2*u + 2*q^2 - 3*q*u^3 + 5*q*u^2 - 2*q*u
            - q + u^3 - 2*u^2 + u) • (elemSymm L 2 * elemSymm L 6)
        + (-q^6 + 2*q^5*u + q^5 - q^4*u^2 - 4*q^4*u + q^4 + 4*q^3*u^2 + q^3*u - q^3 - q^2*u^3
            - 5*q^2*u^2 + 3*q^2*u + 2*q*u^3 + 2*q*u^2 - 3*q*u - u^3 + u)
            • (elemSymm L 3 * elemSymm L 5)
        + (-q^5 + 2*q^4*u + q^4 - q^3*u^2 - 4*q^3*u + 2*q^3 + 4*q^2*u^2 - 3*q^2 - 5*q*u^2 + 4*q*u
            + q + 2*u^2 - 2*u) • (elemSymm L 4 * elemSymm L 4)
        + (-2*q^6 + 3*q^5*u + q^5 - q^4*u^2 - 5*q^4*u + 4*q^4 + 4*q^3*u^2 - 2*q^3*u - 2*q^3
            - 5*q^2*u^2 + 7*q^2*u - 2*q^2 + 2*q*u^2 - 3*q*u + q)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6))
        + (-2*q^5 + 3*q^4*u + q^4 - q^3*u^2 - 5*q^3*u + 3*q^3 + 4*q^2*u^2 - 2*q^2*u - 3*q^2
            - 5*q*u^2 + 7*q*u + q + 2*u^2 - 3*u)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5))
        + (-2*q^4 + 3*q^3*u - q^2*u^2 - 3*q^2*u + 5*q^2 + 3*q*u^2 - 3*q*u - 3*q - 2*u^2 + 3*u)
            • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))
        + (-q^3 + q^2*u + q^2 - 2*q*u + u)
            • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4))
        + (-q^2 + q*u + q - u) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3))
        + (-q^4 + q^3*u + q^3 - 2*q^2*u + q^2 + q*u - q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (-q^3 + q^2*u - 2*q*u + q + u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (-q^2 + q*u + q - u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3)))
        + (-q) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3))) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_one_mul_two_expand]
  simp only [twistProj_add, twistProj_C, twistProj_smul_auxVar_pow_mul_C, Nat.reduceAdd]
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, bop_two_one, bop_three_one', bop_four_one, bop_five_one, bop_six_one,
    bop_seven_one, bop_eight_one, bop_two_elemSymm_one', bop_three_elemSymm_one,
    bop_four_elemSymm_one, bop_five_elemSymm_one, bop_two_elemSymm_two', bop_three_elemSymm_two,
    bop_four_elemSymm_two, bop_five_elemSymm_two, bop_six_elemSymm_two,
    bop_two_elemSymm_three, bop_three_elemSymm_three,
    bop_four_elemSymm_three, bop_five_elemSymm_three, bop_two_elemSymm_four,
    bop_three_elemSymm_four, bop_four_elemSymm_four, bop_two_elemSymm_five,
    bop_three_elemSymm_five, bop_two_elemSymm_six, Nat.reduceAdd, map_add, map_sub, map_neg,
    map_smul]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `T_{2,3}(e1e1e1)`. Unconditional. -/
theorem twistDop_two_three_elemSymm_one_cube (q u : L) :
    twistDop q u 2 ((3 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))
      = (-q^9 + 3*q^8*u + q^8 - 3*q^7*u^2 - 6*q^7*u + 3*q^7 + q^6*u^3 + 9*q^6*u^2 - 3*q^6*u
            - 3*q^6 - 4*q^5*u^3 - 6*q^5*u^2 + 12*q^5*u - 3*q^5 + 6*q^4*u^3 - 6*q^4*u^2 - 3*q^4*u
            + 3*q^4 - 4*q^3*u^3 + 9*q^3*u^2 - 6*q^3*u + q^3 + q^2*u^3 - 3*q^2*u^2 + 3*q^2*u - q^2)
            • (elemSymm L 8)
        + (-q^8 + 3*q^7*u - 2*q^7 - 3*q^6*u^2 + 6*q^6 + q^5*u^3 + 6*q^5*u^2 - 15*q^5*u + 3*q^5
            - 4*q^4*u^3 + 3*q^4*u^2 + 12*q^4*u - 9*q^4 + 6*q^3*u^3 - 15*q^3*u^2 + 9*q^3*u
            - 4*q^2*u^3 + 12*q^2*u^2 - 12*q^2*u + 4*q^2 + q*u^3 - 3*q*u^2 + 3*q*u - q)
            • (elemSymm L 1 * elemSymm L 7)
        + (-q^7 + 3*q^6*u + q^6 - 3*q^5*u^2 - 6*q^5*u + 3*q^5 + q^4*u^3 + 9*q^4*u^2 - 3*q^4*u
            - 3*q^4 - 4*q^3*u^3 - 6*q^3*u^2 + 12*q^3*u - 4*q^3 + 6*q^2*u^3 - 6*q^2*u^2 - 3*q^2*u
            + 6*q^2 - 4*q*u^3 + 9*q*u^2 - 6*q*u - 2*q + u^3 - 3*u^2 + 3*u)
            • (elemSymm L 2 * elemSymm L 6)
        + (-q^6 + 3*q^5*u + q^5 - 3*q^4*u^2 - 6*q^4*u + 2*q^4 + q^3*u^3 + 9*q^3*u^2 - 2*q^3
            - 3*q^2*u^3 - 9*q^2*u^2 + 6*q^2*u - q^2 + 3*q*u^3 + 3*q*u^2 - 3*q*u + q - u^3)
            • (elemSymm L 3 * elemSymm L 5)
        + (-q^5 + 3*q^4*u + q^4 - 3*q^3*u^2 - 6*q^3*u + 3*q^3 + 9*q^2*u^2 - 5*q^2 - 9*q*u^2
            + 6*q*u + 2*q + 3*u^2 - 3*u) • (elemSymm L 4 * elemSymm L 4)
        + (-3*q^6 + 6*q^5*u - 3*q^4*u^2 - 9*q^4*u + 9*q^4 + 9*q^3*u^2 - 6*q^3*u - 3*q^3
            - 9*q^2*u^2 + 15*q^2*u - 6*q^2 + 3*q*u^2 - 6*q*u + 3*q)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6))
        + (-3*q^5 + 6*q^4*u + 3*q^4 - 3*q^3*u^2 - 12*q^3*u + 6*q^3 + 9*q^2*u^2 - 9*q^2 - 9*q*u^2
            + 12*q*u + 3*q + 3*u^2 - 6*u)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5))
        + (-3*q^4 + 6*q^3*u - 3*q^2*u^2 - 6*q^2*u + 9*q^2 + 6*q*u^2 - 6*q*u - 6*q - 3*u^2 + 6*u)
            • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))
        + (-3*q^4 + 3*q^3*u + 2*q^3 - 6*q^2*u + 4*q^2 + 3*q*u - 3*q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (-3*q^3 + 3*q^2*u + 3*q^2 - 6*q*u + 3*u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (-3*q^2 + 3*q*u + 3*q - 3*u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3)))
        + (-q^2 + q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))))
        + (-q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_one_cube_expand]
  simp only [twistProj_add, twistProj_C, twistProj_smul_auxVar_pow_mul_C, Nat.reduceAdd]
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, bop_two_one, bop_three_one', bop_four_one, bop_five_one, bop_six_one,
    bop_seven_one, bop_eight_one, bop_two_elemSymm_one', bop_three_elemSymm_one,
    bop_four_elemSymm_one, bop_five_elemSymm_one, bop_two_elemSymm_two', bop_three_elemSymm_two,
    bop_four_elemSymm_two, bop_five_elemSymm_two, bop_six_elemSymm_two,
    bop_two_elemSymm_three, bop_three_elemSymm_three,
    bop_four_elemSymm_three, bop_five_elemSymm_three, bop_two_elemSymm_four,
    bop_three_elemSymm_four, bop_four_elemSymm_four, bop_two_elemSymm_five,
    bop_three_elemSymm_five, bop_two_elemSymm_six, Nat.reduceAdd, map_add, map_sub, map_neg,
    map_smul]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `T_{2,4}(e2)`. Unconditional. -/
theorem twistDop_two_four_elemSymm_two (q u : L) :
    twistDop q u 2 ((4 : ℕ) : ℤ) (elemSymm L 2)
      = (q^8 - q^7*u - q^7 + 2*q^6*u - q^6 - q^5*u^2 + q^5 + 2*q^4*u^2 - 2*q^4*u - q^3*u^2
            + q^3*u) • (elemSymm L 8)
        + (q^7 - q^6*u + q^5*u - 2*q^5 - q^4*u^2 + 2*q^4*u + 2*q^3*u^2 - 3*q^3*u + q^3 - q^2*u^2
            + q^2*u) • (elemSymm L 1 * elemSymm L 7)
        + (q^6 - q^5*u - q^5 + 2*q^4*u - q^3*u^2 + 2*q^2*u^2 - 2*q^2*u + q^2 - q*u^2 + q*u - q)
            • (elemSymm L 2 * elemSymm L 6)
        + (q^5 - q^4*u - q^4 + 2*q^3*u - q^2*u^2 - q^2*u + 2*q*u^2 - q - u^2 + 1)
            • (elemSymm L 3 * elemSymm L 5)
        + (q^4 - q^3*u - q^3 + 2*q^2*u - q^2 - q*u^2 - q*u + 2*q + u^2 - 1)
            • (elemSymm L 4 * elemSymm L 4)
        + (q^5 - q^4*u - q^4 + 2*q^3*u - q^3 - q^2*u + q^2)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6))
        + (q^4 - q^3*u + 2*q^2*u - 2*q^2 - q*u + 2*q - 1)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5))
        + (q^3 - q^2*u + q*u - 2*q + 1)
            • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))
        + (q^2 - q + 1) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4))
        + (q - 1) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3)) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_two_expand]
  simp only [twistProj_add, twistProj_C, twistProj_smul_auxVar_pow_mul_C, Nat.reduceAdd]
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, bop_two_one, bop_three_one', bop_four_one, bop_five_one, bop_six_one,
    bop_seven_one, bop_eight_one, bop_two_elemSymm_one', bop_three_elemSymm_one,
    bop_four_elemSymm_one, bop_five_elemSymm_one, bop_two_elemSymm_two', bop_three_elemSymm_two,
    bop_four_elemSymm_two, bop_five_elemSymm_two, bop_six_elemSymm_two,
    bop_two_elemSymm_three, bop_three_elemSymm_three,
    bop_four_elemSymm_three, bop_five_elemSymm_three, bop_two_elemSymm_four,
    bop_three_elemSymm_four, bop_four_elemSymm_four, bop_two_elemSymm_five,
    bop_three_elemSymm_five, bop_two_elemSymm_six, Nat.reduceAdd, map_add, map_sub, map_neg,
    map_smul]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `T_{2,4}(e1e1)`. Unconditional. -/
theorem twistDop_two_four_elemSymm_one_sq (q u : L) :
    twistDop q u 2 ((4 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1)
      = (q^8 - 2*q^7*u - q^7 + q^6*u^2 + 4*q^6*u - 2*q^6 - 3*q^5*u^2 + 2*q^5 + 3*q^4*u^2
            - 4*q^4*u + q^4 - q^3*u^2 + 2*q^3*u - q^3) • (elemSymm L 8)
        + (q^7 - 2*q^6*u + q^6 + q^5*u^2 + 2*q^5*u - 4*q^5 - 3*q^4*u^2 + 4*q^4*u + 3*q^3*u^2
            - 6*q^3*u + 3*q^3 - q^2*u^2 + 2*q^2*u - q^2)
            • (elemSymm L 1 * elemSymm L 7)
        + (q^6 - 2*q^5*u - q^5 + q^4*u^2 + 4*q^4*u - 2*q^4 - 3*q^3*u^2 + 2*q^3 + 3*q^2*u^2
            - 4*q^2*u + 2*q^2 - q*u^2 + 2*q*u - 3*q + 1)
            • (elemSymm L 2 * elemSymm L 6)
        + (q^5 - 2*q^4*u - q^4 + q^3*u^2 + 4*q^3*u - q^3 - 3*q^2*u^2 - 2*q^2*u + q^2 + 3*q*u^2
            - u^2) • (elemSymm L 3 * elemSymm L 5)
        + (q^4 - 2*q^3*u - q^3 + q^2*u^2 + 4*q^2*u - 2*q^2 - 2*q*u^2 - 2*q*u + 3*q + u^2 - 1)
            • (elemSymm L 4 * elemSymm L 4)
        + (2*q^5 - 2*q^4*u - q^4 + 4*q^3*u - 3*q^3 - 2*q^2*u + 2*q^2)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6))
        + (2*q^4 - 2*q^3*u - 2*q^3 + 4*q^2*u - 2*q^2 - 2*q*u + 4*q - 2)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5))
        + (2*q^3 - 2*q^2*u + 2*q*u - 4*q + 2)
            • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))
        + (q^3 - q^2)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (q^2 - q + 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (q - 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3))) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_one_sq_expand]
  simp only [twistProj_add, twistProj_C, twistProj_smul_auxVar_pow_mul_C, Nat.reduceAdd]
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, bop_two_one, bop_three_one', bop_four_one, bop_five_one, bop_six_one,
    bop_seven_one, bop_eight_one, bop_two_elemSymm_one', bop_three_elemSymm_one,
    bop_four_elemSymm_one, bop_five_elemSymm_one, bop_two_elemSymm_two', bop_three_elemSymm_two,
    bop_four_elemSymm_two, bop_five_elemSymm_two, bop_six_elemSymm_two,
    bop_two_elemSymm_three, bop_three_elemSymm_three,
    bop_four_elemSymm_three, bop_five_elemSymm_three, bop_two_elemSymm_four,
    bop_three_elemSymm_four, bop_four_elemSymm_four, bop_two_elemSymm_five,
    bop_three_elemSymm_five, bop_two_elemSymm_six, Nat.reduceAdd, map_add, map_sub, map_neg,
    map_smul]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `T_{2,5}(e1)`. Unconditional. -/
theorem twistDop_two_five_elemSymm_one (q u : L) :
    twistDop q u 2 ((5 : ℕ) : ℤ) (elemSymm L 1)
      = (-q^7 + q^6*u + q^6 - 2*q^5*u + q^5 + q^4*u - q^4) • (elemSymm L 8)
        + (-q^6 + q^5*u - 2*q^4*u + 2*q^4 + q^3*u - q^3)
            • (elemSymm L 1 * elemSymm L 7)
        + (-q^5 + q^4*u + q^4 - 2*q^3*u + q^3 + q^2*u - q^2 - q + 1)
            • (elemSymm L 2 * elemSymm L 6)
        + (-q^4 + q^3*u + q^3 - 2*q^2*u + 2*q*u - u) • (elemSymm L 3 * elemSymm L 5)
        + (-q^3 + q^2*u + q^2 - 2*q*u + q + u - 1) • (elemSymm L 4 * elemSymm L 4)
        + (-q^4 + q^3) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6))
        + (-q^3 + q^2 - 1) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5))
        + (1 - q^2) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4)) := by
  rw [twistDop_eq_twistProj, dplusStar_C_elemSymm_one_expand]
  simp only [twistProj_add, twistProj_C, twistProj_smul_auxVar_pow_mul_C, Nat.reduceAdd]
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, bop_two_one, bop_three_one', bop_four_one, bop_five_one, bop_six_one,
    bop_seven_one, bop_eight_one, bop_two_elemSymm_one', bop_three_elemSymm_one,
    bop_four_elemSymm_one, bop_five_elemSymm_one, bop_two_elemSymm_two', bop_three_elemSymm_two,
    bop_four_elemSymm_two, bop_five_elemSymm_two, bop_six_elemSymm_two,
    bop_two_elemSymm_three, bop_three_elemSymm_three,
    bop_four_elemSymm_three, bop_five_elemSymm_three, bop_two_elemSymm_four,
    bop_three_elemSymm_four, bop_four_elemSymm_four, bop_two_elemSymm_five,
    bop_three_elemSymm_five, bop_two_elemSymm_six, Nat.reduceAdd, map_add, map_sub, map_neg,
    map_smul]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `T_{2,6}(1)`. Unconditional. -/
theorem twistDop_two_six_one (q u : L) :
    twistDop q u 2 ((6 : ℕ) : ℤ) ((1 : Lambda L))
      = (q^6 - q^5) • (elemSymm L 8)
        + (q^5 - q^4) • (elemSymm L 1 * elemSymm L 7)
        + (q^4 - q^3 + 1) • (elemSymm L 2 * elemSymm L 6)
        + (q^3 - q^2 + q - 1) • (elemSymm L 3 * elemSymm L 5)
        + (q^2 - q) • (elemSymm L 4 * elemSymm L 4) := by
  rw [twistDop_eq_twistProj, dplusStar_C_one]
  simp only [twistProj_add, twistProj_C, twistProj_smul_auxVar_pow_mul_C, Nat.reduceAdd]
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, bop_two_one, bop_three_one', bop_four_one, bop_five_one, bop_six_one,
    bop_seven_one, bop_eight_one, bop_two_elemSymm_one', bop_three_elemSymm_one,
    bop_four_elemSymm_one, bop_five_elemSymm_one, bop_two_elemSymm_two', bop_three_elemSymm_two,
    bop_four_elemSymm_two, bop_five_elemSymm_two, bop_six_elemSymm_two,
    bop_two_elemSymm_three, bop_three_elemSymm_three,
    bop_four_elemSymm_three, bop_five_elemSymm_three, bop_two_elemSymm_four,
    bop_three_elemSymm_four, bop_four_elemSymm_four, bop_two_elemSymm_five,
    bop_three_elemSymm_five, bop_two_elemSymm_six, Nat.reduceAdd, map_add, map_sub, map_neg,
    map_smul, mul_add, mul_sub, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, smul_add,
    smul_sub, smul_neg, neg_smul, smul_smul]

end HJO.Sweep

end
