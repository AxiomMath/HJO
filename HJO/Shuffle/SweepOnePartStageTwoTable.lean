/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepOnePartDefectValues

/-! # The Hall--Littlewood table of the one-part stage word at `[3]`

The values `B_m(f)` of `HJO.Sym.Bop` that `HJO/Shuffle/SweepOnePartStageTwoLetter.lean` and
the `z_1` values before it read: the kernel value `HJO.Bglx.paramPleth_elemSymm_seven_eq`, the base
rows `B_m(e_n)` at `n ≥ 5` and at the indices past the existing table, the composite rows of weight
up to nine (each a Pieri reduction, `HJO.Sym.bop_elemSymm_one_mul` to `_four_mul`, down to the
vacuum), and the consistency check `HJO.Sym.bop_hmz_two_seven_eq`, which checks four of the new rows
against the Haglund--Morse--Zabrocki relation. The method and the genericity are described in
`HJO/Shuffle/SweepOnePartStageTwoLetter.lean`.

## References

This file computes values of `HJO.Sym.Bop` on `HJO.Sym.elemSymm`, with `HJO.Sweep.bopExt` and
`HJO.Sym.bop_pair_antisymm`, for `HJO.Sweep.zop` and `HJO.Sweep.dplusStar`.
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

namespace HJO.Bglx

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`κ(e_7) = (q^6+q^5u+q^4u^2+q^3u^3+q^2u^4+qu^5+u^6)M`**, the kernel recursion
`HJO.Bglx.paramPleth_elemSymm_add_two` at `n = 5`, one step past
`HJO.Bglx.paramPleth_elemSymm_six_eq`. -/
theorem paramPleth_elemSymm_seven_eq (q u : L) :
    paramPleth q u (elemSymm L 7)
      = (q ^ 6 + q ^ 5 * u + q ^ 4 * u ^ 2 + q ^ 3 * u ^ 3 + q ^ 2 * u ^ 4 + q * u ^ 5
          + u ^ 6) * ((1 - q) * (1 - u)) := by
  have h := paramPleth_elemSymm_add_two (K := L) q u 5
  rw [show (5 : ℕ) + 2 = 7 from rfl, show (5 : ℕ) + 1 = 6 from rfl,
    paramPleth_elemSymm_six_eq, paramPleth_elemSymm_five_eq] at h
  simp only [OfNat.ofNat_ne_zero, ite_false] at h
  linear_combination h
end HJO.Bglx

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- `B_2(e_1^3)`, the one `B`-value at the index `2` the `z_1` step on `G_2` needs and the existing
table does not have: `HJO.Sym.bop_two_elemSymm_one_mul` against
`HJO.Sym.bop_two_elemSymm_one_sq` and `HJO.Sym.bop_three_elemSymm_one_sq`. -/
theorem bop_two_elemSymm_one_cube (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))
      = (q ^ 3 - 3 * q ^ 2 + 3 * q - 1) • elemSymm L 5
        + (3 * q ^ 2 - 6 * q + 3) • (elemSymm L 1 * elemSymm L 4)
        + (3 * q - 3) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
        + (1 : L) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))) := by
  rw [bop_two_elemSymm_one_mul, bop_two_elemSymm_one_sq, bop_three_elemSymm_one_sq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-! ### Two `B`-values at the indices the projection of `y_1^2z_1G_2` reads -/

/-- `B_6(e_1) = e_1e_6 + (q-1)e_7`: `HJO.Sym.bop_elemSymm_one_mul` at `k = 6` against the vacuum
row `HJO.Sym.bop_natCast_one`. -/
theorem bop_six_elemSymm_one (q : L) :
    Bop q ((6 : ℕ) : ℤ) (elemSymm L 1)
      = (q - 1) • elemSymm L 7 + (1 : L) • (elemSymm L 1 * elemSymm L 6) := by
  have h := bop_elemSymm_one_mul q 6 (1 : Lambda L)
  rw [mul_one] at h
  rw [h, bop_natCast_one, bop_natCast_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  norm_num
  ring

/-- `B_7(e_1) = -e_1e_7 + (1-q)e_8`, the same Pieri step one index up. -/
theorem bop_seven_elemSymm_one (q : L) :
    Bop q ((7 : ℕ) : ℤ) (elemSymm L 1)
      = (-q + 1) • elemSymm L 8 + (-1 : L) • (elemSymm L 1 * elemSymm L 7) := by
  have h := bop_elemSymm_one_mul q 7 (1 : Lambda L)
  rw [mul_one] at h
  rw [h, bop_natCast_one, bop_natCast_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  norm_num
  ring

/-- `B_2(e_7)`, off `HJO.Sym.dop_elemSymm` at `u = 0`. -/
theorem bop_two_elemSymm_seven (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 7)
      =  (q ^ 7 - q ^ 6) • elemSymm L 9
      + (q ^ 6 - q ^ 5) • (elemSymm L 1 * elemSymm L 8)
      + (q ^ 5 - q ^ 4 + 1) • (elemSymm L 2 * elemSymm L 7)
      + (q ^ 4 - q ^ 3 + q - 1) • (elemSymm L 3 * elemSymm L 6)
      + (q ^ 3 - q) • (elemSymm L 4 * elemSymm L 5) := by
  rw [bop_natCast, dop_elemSymm,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq,
    Bglx.paramPleth_elemSymm_four_eq, Bglx.paramPleth_elemSymm_five_eq,
    Bglx.paramPleth_elemSymm_six_eq, Bglx.paramPleth_elemSymm_seven_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_3(e_6)`, off `HJO.Sym.dop_elemSymm` at `u = 0`. -/
theorem bop_three_elemSymm_six (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 6)
      =  (-(q ^ 6) + q ^ 5) • elemSymm L 9
      + (-(q ^ 5) + q ^ 4) • (elemSymm L 1 * elemSymm L 8)
      + (-(q ^ 4) + q ^ 3) • (elemSymm L 2 * elemSymm L 7)
      + (-(q ^ 3) + q ^ 2 - 1) • (elemSymm L 3 * elemSymm L 6)
      + (-(q ^ 2) + 1) • (elemSymm L 4 * elemSymm L 5) := by
  rw [bop_natCast, dop_elemSymm,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq,
    Bglx.paramPleth_elemSymm_four_eq, Bglx.paramPleth_elemSymm_five_eq,
    Bglx.paramPleth_elemSymm_six_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_4(e_5)`, off `HJO.Sym.dop_elemSymm` at `u = 0`. -/
theorem bop_four_elemSymm_five (q : L) :
    Bop q ((4 : ℕ) : ℤ) (elemSymm L 5)
      =  (q ^ 5 - q ^ 4) • elemSymm L 9
      + (q ^ 4 - q ^ 3) • (elemSymm L 1 * elemSymm L 8)
      + (q ^ 3 - q ^ 2) • (elemSymm L 2 * elemSymm L 7)
      + (q ^ 2 - q) • (elemSymm L 3 * elemSymm L 6)
      + (q) • (elemSymm L 4 * elemSymm L 5) := by
  rw [bop_natCast, dop_elemSymm,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq,
    Bglx.paramPleth_elemSymm_four_eq, Bglx.paramPleth_elemSymm_five_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_5(e_4)`, off `HJO.Sym.dop_elemSymm` at `u = 0`. -/
theorem bop_five_elemSymm_four (q : L) :
    Bop q ((5 : ℕ) : ℤ) (elemSymm L 4)
      =  (-(q ^ 4) + q ^ 3) • elemSymm L 9
      + (-(q ^ 3) + q ^ 2) • (elemSymm L 1 * elemSymm L 8)
      + (-(q ^ 2) + q) • (elemSymm L 2 * elemSymm L 7)
      + (-q + 1) • (elemSymm L 3 * elemSymm L 6)
      + (-1 : L) • (elemSymm L 4 * elemSymm L 5) := by
  rw [bop_natCast, dop_elemSymm,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero,
    Bglx.paramPleth_elemSymm_one_eq, Bglx.paramPleth_elemSymm_two_eq,
    Bglx.paramPleth_elemSymm_three_eq, Bglx.paramPleth_elemSymm_four_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_6(e_3)`, off `HJO.Sym.dop_elemSymm` at `u = 0`. -/
theorem bop_six_elemSymm_three (q : L) :
    Bop q ((6 : ℕ) : ℤ) (elemSymm L 3)
      =  (q ^ 3 - q ^ 2) • elemSymm L 9
      + (q ^ 2 - q) • (elemSymm L 1 * elemSymm L 8)
      + (q - 1) • (elemSymm L 2 * elemSymm L 7)
      + (1 : L) • (elemSymm L 3 * elemSymm L 6) := by
  rw [bop_natCast, dop_elemSymm,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_7(e_2)`, off `HJO.Sym.dop_elemSymm` at `u = 0`. -/
theorem bop_seven_elemSymm_two (q : L) :
    Bop q ((7 : ℕ) : ℤ) (elemSymm L 2)
      =  (-(q ^ 2) + q) • elemSymm L 9
      + (-q + 1) • (elemSymm L 1 * elemSymm L 8)
      + (-1 : L) • (elemSymm L 2 * elemSymm L 7) := by
  rw [bop_natCast, dop_elemSymm,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_8(e_1)`, off `HJO.Sym.dop_elemSymm` at `u = 0`. -/
theorem bop_eight_elemSymm_one (q : L) :
    Bop q ((8 : ℕ) : ℤ) (elemSymm L 1)
      =  (q - 1) • elemSymm L 9
      + (1 : L) • (elemSymm L 1 * elemSymm L 8) := by
  rw [bop_natCast, dop_elemSymm,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_pow, Nat.sub_zero,
    Nat.sub_self, elemSymm_zero]
  norm_num
  ring
/-- `B_2(e_one_mul_six)` at weight nine. -/
theorem bop_two_elemSymm_one_mul_six (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 6)
      = (q ^ 7 - 2 * q ^ 6 + q ^ 5) • elemSymm L 9
      + (2 * q ^ 6 - 3 * q ^ 5 + q ^ 4) • (elemSymm L 1 * elemSymm L 8)
      + (q ^ 5 - 2 * q ^ 4 + q ^ 3) • (elemSymm L 2 * elemSymm L 7)
      + (q ^ 4 - 2 * q ^ 3 + q ^ 2 + q - 1) • (elemSymm L 3 * elemSymm L 6)
      + (q ^ 3 - q ^ 2 - q + 1) • (elemSymm L 4 * elemSymm L 5)
      + (q ^ 5 - q ^ 4) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (q ^ 4 - q ^ 3 + 1) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (q ^ 3 - q ^ 2 + q - 1) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (q ^ 2 - q) • (elemSymm L 1 * (elemSymm L 4 * elemSymm L 4)) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_2(e_two_mul_five)` at weight nine. -/
theorem bop_two_elemSymm_two_mul_five (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 2 * elemSymm L 5)
      = (q ^ 7 - 2 * q ^ 6 + q ^ 5) • elemSymm L 9
      + (2 * q ^ 6 - 4 * q ^ 5 + 2 * q ^ 4) • (elemSymm L 1 * elemSymm L 8)
      + (2 * q ^ 5 - 3 * q ^ 4 + q ^ 3) • (elemSymm L 2 * elemSymm L 7)
      + (q ^ 4 - 2 * q ^ 3 + q ^ 2) • (elemSymm L 3 * elemSymm L 6)
      + (q ^ 3 - q ^ 2) • (elemSymm L 4 * elemSymm L 5)
      + (q ^ 5 - 2 * q ^ 4 + q ^ 3) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (2 * q ^ 4 - 3 * q ^ 3 + q ^ 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (q ^ 3 - 2 * q ^ 2 + 2 * q - 1) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (q ^ 2 - 2 * q + 1) • (elemSymm L 1 * (elemSymm L 4 * elemSymm L 4))
      + (q ^ 3 - q ^ 2 + 1) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (q ^ 2 - 1) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 4)) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_2(e_three_mul_four)` at weight nine. -/
theorem bop_two_elemSymm_three_mul_four (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 3 * elemSymm L 4)
      = (q ^ 7 - 2 * q ^ 6 + q ^ 5) • elemSymm L 9
      + (2 * q ^ 6 - 4 * q ^ 5 + 2 * q ^ 4) • (elemSymm L 1 * elemSymm L 8)
      + (2 * q ^ 5 - 4 * q ^ 4 + 2 * q ^ 3) • (elemSymm L 2 * elemSymm L 7)
      + (2 * q ^ 4 - 3 * q ^ 3 + q ^ 2) • (elemSymm L 3 * elemSymm L 6)
      + (q ^ 3 - q ^ 2) • (elemSymm L 4 * elemSymm L 5)
      + (q ^ 5 - 2 * q ^ 4 + q ^ 3) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (2 * q ^ 4 - 4 * q ^ 3 + 2 * q ^ 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (2 * q ^ 3 - 3 * q ^ 2 + q) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (q ^ 2 - q) • (elemSymm L 1 * (elemSymm L 4 * elemSymm L 4))
      + (q ^ 3 - 2 * q ^ 2 + q) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (2 * q ^ 2 - 2 * q + 1) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 4))
      + (q - 1) • (elemSymm L 3 * (elemSymm L 3 * elemSymm L 3)) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_2(e_one_sq_mul_five)` at weight nine. -/
theorem bop_two_elemSymm_one_sq_mul_five (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))
      = (q ^ 7 - 3 * q ^ 6 + 3 * q ^ 5 - q ^ 4) • elemSymm L 9
      + (3 * q ^ 6 - 7 * q ^ 5 + 5 * q ^ 4 - q ^ 3) • (elemSymm L 1 * elemSymm L 8)
      + (q ^ 5 - 3 * q ^ 4 + 3 * q ^ 3 - q ^ 2) • (elemSymm L 2 * elemSymm L 7)
      + (q ^ 4 - 3 * q ^ 3 + 3 * q ^ 2 - q) • (elemSymm L 3 * elemSymm L 6)
      + (q ^ 3 - 2 * q ^ 2 + q) • (elemSymm L 4 * elemSymm L 5)
      + (3 * q ^ 5 - 5 * q ^ 4 + 2 * q ^ 3) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (2 * q ^ 4 - 4 * q ^ 3 + 2 * q ^ 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (2 * q ^ 3 - 4 * q ^ 2 + 4 * q - 2) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (2 * q ^ 2 - 4 * q + 2) • (elemSymm L 1 * (elemSymm L 4 * elemSymm L 4))
      + (q ^ 4 - q ^ 3) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (q ^ 3 - q ^ 2 + 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (q ^ 2 - 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_2(e_one_mul_two_mul_four)` at weight nine. -/
theorem bop_two_elemSymm_one_mul_two_mul_four (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4))
      = (q ^ 7 - 3 * q ^ 6 + 3 * q ^ 5 - q ^ 4) • elemSymm L 9
      + (3 * q ^ 6 - 8 * q ^ 5 + 7 * q ^ 4 - 2 * q ^ 3) • (elemSymm L 1 * elemSymm L 8)
      + (2 * q ^ 5 - 5 * q ^ 4 + 4 * q ^ 3 - q ^ 2) • (elemSymm L 2 * elemSymm L 7)
      + (q ^ 4 - 3 * q ^ 3 + 3 * q ^ 2 - q) • (elemSymm L 3 * elemSymm L 6)
      + (q ^ 3 - 2 * q ^ 2 + q) • (elemSymm L 4 * elemSymm L 5)
      + (3 * q ^ 5 - 7 * q ^ 4 + 5 * q ^ 3 - q ^ 2)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (4 * q ^ 4 - 8 * q ^ 3 + 5 * q ^ 2 - q) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (2 * q ^ 3 - 5 * q ^ 2 + 4 * q - 1) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (2 * q ^ 2 - 3 * q + 1) • (elemSymm L 1 * (elemSymm L 4 * elemSymm L 4))
      + (q ^ 3 - 2 * q ^ 2 + q) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (q ^ 2 - q) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 4))
      + (q ^ 4 - 2 * q ^ 3 + q ^ 2)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (2 * q ^ 3 - 3 * q ^ 2 + q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (q ^ 2 - q) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4)))
      + (q ^ 2 - q + 1) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4)))
      + (q - 1) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_2(e_one_mul_three_sq)` at weight nine. -/
theorem bop_two_elemSymm_one_mul_three_sq (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3))
      = (q ^ 7 - 3 * q ^ 6 + 3 * q ^ 5 - q ^ 4) • elemSymm L 9
      + (3 * q ^ 6 - 8 * q ^ 5 + 7 * q ^ 4 - 2 * q ^ 3) • (elemSymm L 1 * elemSymm L 8)
      + (2 * q ^ 5 - 6 * q ^ 4 + 6 * q ^ 3 - 2 * q ^ 2) • (elemSymm L 2 * elemSymm L 7)
      + (2 * q ^ 4 - 4 * q ^ 3 + 2 * q ^ 2) • (elemSymm L 3 * elemSymm L 6)
      + (3 * q ^ 5 - 7 * q ^ 4 + 5 * q ^ 3 - q ^ 2)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (4 * q ^ 4 - 10 * q ^ 3 + 8 * q ^ 2 - 2 * q)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (4 * q ^ 3 - 6 * q ^ 2 + 2 * q) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (q ^ 3 - 3 * q ^ 2 + 3 * q - 1) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (2 * q ^ 2 - 4 * q + 2) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 4))
      + (q - 1) • (elemSymm L 3 * (elemSymm L 3 * elemSymm L 3))
      + (q ^ 4 - 2 * q ^ 3 + q ^ 2)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (2 * q ^ 3 - 4 * q ^ 2 + 2 * q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (2 * q ^ 2 - 2 * q) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4)))
      + (q ^ 2 - 2 * q + 1) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4)))
      + (2 * q - 1) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_2(e_two_sq_mul_three)` at weight nine. -/
theorem bop_two_elemSymm_two_sq_mul_three (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3))
      = (q ^ 7 - 3 * q ^ 6 + 3 * q ^ 5 - q ^ 4) • elemSymm L 9
      + (3 * q ^ 6 - 9 * q ^ 5 + 9 * q ^ 4 - 3 * q ^ 3) • (elemSymm L 1 * elemSymm L 8)
      + (3 * q ^ 5 - 7 * q ^ 4 + 5 * q ^ 3 - q ^ 2) • (elemSymm L 2 * elemSymm L 7)
      + (q ^ 4 - 2 * q ^ 3 + q ^ 2) • (elemSymm L 3 * elemSymm L 6)
      + (3 * q ^ 5 - 9 * q ^ 4 + 9 * q ^ 3 - 3 * q ^ 2)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (6 * q ^ 4 - 14 * q ^ 3 + 10 * q ^ 2 - 2 * q)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (2 * q ^ 3 - 4 * q ^ 2 + 2 * q) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (3 * q ^ 3 - 5 * q ^ 2 + 2 * q) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (2 * q ^ 2 - 2 * q) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 4))
      + (q ^ 4 - 3 * q ^ 3 + 3 * q ^ 2 - q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (3 * q ^ 3 - 7 * q ^ 2 + 5 * q - 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (q ^ 2 - 2 * q + 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4)))
      + (3 * q ^ 2 - 5 * q + 2) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4)))
      + (2 * q - 2) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3)))
      + (q) • (elemSymm L 2 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_2(e_one_cube_mul_four)` at weight nine. -/
theorem bop_two_elemSymm_one_cube_mul_four (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))
      = (q ^ 7 - 4 * q ^ 6 + 6 * q ^ 5 - 4 * q ^ 4 + q ^ 3) • elemSymm L 9
      + (4 * q ^ 6 - 13 * q ^ 5 + 15 * q ^ 4 - 7 * q ^ 3 + q ^ 2) • (elemSymm L 1 * elemSymm L 8)
      + (q ^ 5 - 4 * q ^ 4 + 6 * q ^ 3 - 4 * q ^ 2 + q) • (elemSymm L 2 * elemSymm L 7)
      + (q ^ 4 - 4 * q ^ 3 + 6 * q ^ 2 - 4 * q + 1) • (elemSymm L 3 * elemSymm L 6)
      + (q ^ 3 - 3 * q ^ 2 + 3 * q - 1) • (elemSymm L 4 * elemSymm L 5)
      + (6 * q ^ 5 - 15 * q ^ 4 + 12 * q ^ 3 - 3 * q ^ 2)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (3 * q ^ 4 - 9 * q ^ 3 + 9 * q ^ 2 - 3 * q)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (3 * q ^ 3 - 9 * q ^ 2 + 9 * q - 3) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (3 * q ^ 2 - 6 * q + 3) • (elemSymm L 1 * (elemSymm L 4 * elemSymm L 4))
      + (4 * q ^ 4 - 7 * q ^ 3 + 3 * q ^ 2)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (3 * q ^ 3 - 6 * q ^ 2 + 3 * q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (3 * q ^ 2 - 3 * q) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4)))
      + (q ^ 3 - q ^ 2)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
      + (q ^ 2 - q + 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4))))
      + (q - 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3))))
      := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_2(e_one_sq_mul_two_mul_three)` at weight nine. -/
theorem bop_two_elemSymm_one_sq_mul_two_mul_three (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))
      = (q ^ 7 - 4 * q ^ 6 + 6 * q ^ 5 - 4 * q ^ 4 + q ^ 3) • elemSymm L 9
      + (4 * q ^ 6 - 14 * q ^ 5 + 18 * q ^ 4 - 10 * q ^ 3 + 2 * q ^ 2)
            • (elemSymm L 1 * elemSymm L 8)
      + (2 * q ^ 5 - 7 * q ^ 4 + 9 * q ^ 3 - 5 * q ^ 2 + q) • (elemSymm L 2 * elemSymm L 7)
      + (q ^ 4 - 3 * q ^ 3 + 3 * q ^ 2 - q) • (elemSymm L 3 * elemSymm L 6)
      + (6 * q ^ 5 - 18 * q ^ 4 + 19 * q ^ 3 - 8 * q ^ 2 + q)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (6 * q ^ 4 - 17 * q ^ 3 + 17 * q ^ 2 - 7 * q + 1)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (3 * q ^ 3 - 7 * q ^ 2 + 5 * q - 1) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (q ^ 3 - 3 * q ^ 2 + 3 * q - 1) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (q ^ 2 - 2 * q + 1) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 4))
      + (4 * q ^ 4 - 10 * q ^ 3 + 8 * q ^ 2 - 2 * q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (6 * q ^ 3 - 13 * q ^ 2 + 9 * q - 2)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (3 * q ^ 2 - 5 * q + 2) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4)))
      + (2 * q ^ 2 - 4 * q + 2) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4)))
      + (2 * q - 2) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3)))
      + (q ^ 3 - 2 * q ^ 2 + q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
      + (2 * q ^ 2 - 3 * q + 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4))))
      + (q - 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3))))
      + (q) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3))))
      := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_2(e_one_mul_two_cube)` at weight nine. -/
theorem bop_two_elemSymm_one_mul_two_cube (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2)))
      = (q ^ 7 - 4 * q ^ 6 + 6 * q ^ 5 - 4 * q ^ 4 + q ^ 3) • elemSymm L 9
      + (4 * q ^ 6 - 15 * q ^ 5 + 21 * q ^ 4 - 13 * q ^ 3 + 3 * q ^ 2)
            • (elemSymm L 1 * elemSymm L 8)
      + (3 * q ^ 5 - 9 * q ^ 4 + 9 * q ^ 3 - 3 * q ^ 2) • (elemSymm L 2 * elemSymm L 7)
      + (6 * q ^ 5 - 21 * q ^ 4 + 27 * q ^ 3 - 15 * q ^ 2 + 3 * q)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (9 * q ^ 4 - 24 * q ^ 3 + 21 * q ^ 2 - 6 * q)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (3 * q ^ 3 - 6 * q ^ 2 + 3 * q) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (4 * q ^ 4 - 13 * q ^ 3 + 15 * q ^ 2 - 7 * q + 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (9 * q ^ 3 - 21 * q ^ 2 + 15 * q - 3)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (6 * q ^ 2 - 9 * q + 3) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4)))
      + (q - 1) • (elemSymm L 2 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3)))
      + (q ^ 3 - 3 * q ^ 2 + 3 * q - 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
      + (3 * q ^ 2 - 6 * q + 3)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4))))
      + (3 * q - 3)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3))))
      + (1 : L) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))))
      := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_2(e_one_pow_four_mul_three)` at weight nine. -/
theorem bop_two_elemSymm_one_pow_four_mul_three (q : L) :
    Bop q ((2 : ℕ) : ℤ)
        (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))))
      = (q ^ 7 - 5 * q ^ 6 + 10 * q ^ 5 - 10 * q ^ 4 + 5 * q ^ 3 - q ^ 2) • elemSymm L 9
      + (5 * q ^ 6 - 21 * q ^ 5 + 34 * q ^ 4 - 26 * q ^ 3 + 9 * q ^ 2 - q)
            • (elemSymm L 1 * elemSymm L 8)
      + (q ^ 5 - 5 * q ^ 4 + 10 * q ^ 3 - 10 * q ^ 2 + 5 * q - 1) • (elemSymm L 2 * elemSymm L 7)
      + (q ^ 4 - 4 * q ^ 3 + 6 * q ^ 2 - 4 * q + 1) • (elemSymm L 3 * elemSymm L 6)
      + (10 * q ^ 5 - 34 * q ^ 4 + 42 * q ^ 3 - 22 * q ^ 2 + 4 * q)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (4 * q ^ 4 - 16 * q ^ 3 + 24 * q ^ 2 - 16 * q + 4)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (4 * q ^ 3 - 12 * q ^ 2 + 12 * q - 4) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (10 * q ^ 4 - 26 * q ^ 3 + 22 * q ^ 2 - 6 * q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (6 * q ^ 3 - 18 * q ^ 2 + 18 * q - 6)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (6 * q ^ 2 - 12 * q + 6) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4)))
      + (5 * q ^ 3 - 9 * q ^ 2 + 4 * q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
      + (4 * q ^ 2 - 8 * q + 4)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4))))
      + (4 * q - 4)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3))))
      + (q ^ 2 - q)
            • (elemSymm L 1
                * (elemSymm L 1
                    * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))))
      + (q)
            • (elemSymm L 1
                * (elemSymm L 1
                    * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_2(e_one_cube_mul_two_sq)` at weight nine. -/
theorem bop_two_elemSymm_one_cube_mul_two_sq (q : L) :
    Bop q ((2 : ℕ) : ℤ)
        (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))))
      = (q ^ 7 - 5 * q ^ 6 + 10 * q ^ 5 - 10 * q ^ 4 + 5 * q ^ 3 - q ^ 2) • elemSymm L 9
      + (5 * q ^ 6 - 22 * q ^ 5 + 38 * q ^ 4 - 32 * q ^ 3 + 13 * q ^ 2 - 2 * q)
            • (elemSymm L 1 * elemSymm L 8)
      + (2 * q ^ 5 - 8 * q ^ 4 + 12 * q ^ 3 - 8 * q ^ 2 + 2 * q) • (elemSymm L 2 * elemSymm L 7)
      + (10 * q ^ 5 - 38 * q ^ 4 + 55 * q ^ 3 - 37 * q ^ 2 + 11 * q - 1)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (8 * q ^ 4 - 26 * q ^ 3 + 30 * q ^ 2 - 14 * q + 2)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (q ^ 3 - 3 * q ^ 2 + 3 * q - 1) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (10 * q ^ 4 - 32 * q ^ 3 + 37 * q ^ 2 - 18 * q + 3)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (12 * q ^ 3 - 30 * q ^ 2 + 24 * q - 6)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (3 * q ^ 2 - 6 * q + 3) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4)))
      + (5 * q ^ 3 - 13 * q ^ 2 + 11 * q - 3)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
      + (8 * q ^ 2 - 14 * q + 6)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4))))
      + (3 * q - 3)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3))))
      + (q ^ 2 - 2 * q + 1)
            • (elemSymm L 1
                * (elemSymm L 1
                    * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))))
      + (2 * q - 2)
            • (elemSymm L 1
                * (elemSymm L 1
                    * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))))
      + (1 : L)
            • (elemSymm L 1
                * (elemSymm L 1
                    * (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_3(e_one_mul_five)` at weight nine. -/
theorem bop_three_elemSymm_one_mul_five (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 5)
      = (-(q ^ 6) + 2 * q ^ 5 - q ^ 4) • elemSymm L 9
      + (-(2 * q ^ 5) + 3 * q ^ 4 - q ^ 3) • (elemSymm L 1 * elemSymm L 8)
      + (-(q ^ 4) + 2 * q ^ 3 - q ^ 2) • (elemSymm L 2 * elemSymm L 7)
      + (-(q ^ 3) + 2 * q ^ 2 - q) • (elemSymm L 3 * elemSymm L 6)
      + (-(q ^ 2) + q) • (elemSymm L 4 * elemSymm L 5)
      + (-(q ^ 4) + q ^ 3) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (-(q ^ 3) + q ^ 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (-(q ^ 2) + q - 1) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (-q + 1) • (elemSymm L 1 * (elemSymm L 4 * elemSymm L 4)) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_3(e_two_mul_four)` at weight nine. -/
theorem bop_three_elemSymm_two_mul_four (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 2 * elemSymm L 4)
      = (-(q ^ 6) + 2 * q ^ 5 - q ^ 4) • elemSymm L 9
      + (-(2 * q ^ 5) + 4 * q ^ 4 - 2 * q ^ 3) • (elemSymm L 1 * elemSymm L 8)
      + (-(2 * q ^ 4) + 3 * q ^ 3 - q ^ 2) • (elemSymm L 2 * elemSymm L 7)
      + (-(q ^ 3) + 2 * q ^ 2 - q) • (elemSymm L 3 * elemSymm L 6)
      + (-(q ^ 2) + q) • (elemSymm L 4 * elemSymm L 5)
      + (-(q ^ 4) + 2 * q ^ 3 - q ^ 2) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (-(2 * q ^ 3) + 3 * q ^ 2 - q) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (-(q ^ 2) + 2 * q - 1) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (-q + 1) • (elemSymm L 1 * (elemSymm L 4 * elemSymm L 4))
      + (-(q ^ 2) + q) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (-q) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 4)) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_3(e_three_sq)` at weight nine. -/
theorem bop_three_elemSymm_three_sq (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 3 * elemSymm L 3)
      = (-(q ^ 6) + 2 * q ^ 5 - q ^ 4) • elemSymm L 9
      + (-(2 * q ^ 5) + 4 * q ^ 4 - 2 * q ^ 3) • (elemSymm L 1 * elemSymm L 8)
      + (-(2 * q ^ 4) + 4 * q ^ 3 - 2 * q ^ 2) • (elemSymm L 2 * elemSymm L 7)
      + (-(2 * q ^ 3) + 2 * q ^ 2) • (elemSymm L 3 * elemSymm L 6)
      + (-(q ^ 4) + 2 * q ^ 3 - q ^ 2) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (-(2 * q ^ 3) + 4 * q ^ 2 - 2 * q) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (-(2 * q ^ 2) + 2 * q) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (-(q ^ 2) + 2 * q - 1) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (-(2 * q) + 2) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 4))
      + (-1 : L) • (elemSymm L 3 * (elemSymm L 3 * elemSymm L 3)) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_3(e_one_sq_mul_four)` at weight nine. -/
theorem bop_three_elemSymm_one_sq_mul_four (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
      = (-(q ^ 6) + 3 * q ^ 5 - 3 * q ^ 4 + q ^ 3) • elemSymm L 9
      + (-(3 * q ^ 5) + 7 * q ^ 4 - 5 * q ^ 3 + q ^ 2) • (elemSymm L 1 * elemSymm L 8)
      + (-(q ^ 4) + 3 * q ^ 3 - 3 * q ^ 2 + q) • (elemSymm L 2 * elemSymm L 7)
      + (-(q ^ 3) + 3 * q ^ 2 - 3 * q + 1) • (elemSymm L 3 * elemSymm L 6)
      + (-(q ^ 2) + 2 * q - 1) • (elemSymm L 4 * elemSymm L 5)
      + (-(3 * q ^ 4) + 5 * q ^ 3 - 2 * q ^ 2) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (-(2 * q ^ 3) + 4 * q ^ 2 - 2 * q) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (-(2 * q ^ 2) + 4 * q - 2) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (-(2 * q) + 2) • (elemSymm L 1 * (elemSymm L 4 * elemSymm L 4))
      + (-(q ^ 3) + q ^ 2) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (-(q ^ 2) + q) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (-q) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_3(e_one_mul_two_mul_three)` at weight nine. -/
theorem bop_three_elemSymm_one_mul_two_mul_three (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))
      = (-(q ^ 6) + 3 * q ^ 5 - 3 * q ^ 4 + q ^ 3) • elemSymm L 9
      + (-(3 * q ^ 5) + 8 * q ^ 4 - 7 * q ^ 3 + 2 * q ^ 2) • (elemSymm L 1 * elemSymm L 8)
      + (-(2 * q ^ 4) + 5 * q ^ 3 - 4 * q ^ 2 + q) • (elemSymm L 2 * elemSymm L 7)
      + (-(q ^ 3) + 2 * q ^ 2 - q) • (elemSymm L 3 * elemSymm L 6)
      + (-(3 * q ^ 4) + 7 * q ^ 3 - 5 * q ^ 2 + q)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (-(4 * q ^ 3) + 8 * q ^ 2 - 5 * q + 1) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (-(2 * q ^ 2) + 3 * q - 1) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (-(q ^ 2) + 2 * q - 1) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (-q + 1) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 4))
      + (-(q ^ 3) + 2 * q ^ 2 - q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (-(2 * q ^ 2) + 3 * q - 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (-q + 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4)))
      + (-q + 1) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4)))
      + (-1 : L) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_3(e_two_cube)` at weight nine. -/
theorem bop_three_elemSymm_two_cube (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))
      = (-(q ^ 6) + 3 * q ^ 5 - 3 * q ^ 4 + q ^ 3) • elemSymm L 9
      + (-(3 * q ^ 5) + 9 * q ^ 4 - 9 * q ^ 3 + 3 * q ^ 2) • (elemSymm L 1 * elemSymm L 8)
      + (-(3 * q ^ 4) + 6 * q ^ 3 - 3 * q ^ 2) • (elemSymm L 2 * elemSymm L 7)
      + (-(3 * q ^ 4) + 9 * q ^ 3 - 9 * q ^ 2 + 3 * q)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (-(6 * q ^ 3) + 12 * q ^ 2 - 6 * q) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (-(3 * q ^ 2) + 3 * q) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (-(q ^ 3) + 3 * q ^ 2 - 3 * q + 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (-(3 * q ^ 2) + 6 * q - 3)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (-(3 * q) + 3) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4)))
      + (-1 : L) • (elemSymm L 2 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_3(e_one_cube_mul_three)` at weight nine. -/
theorem bop_three_elemSymm_one_cube_mul_three (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
      = (-(q ^ 6) + 4 * q ^ 5 - 6 * q ^ 4 + 4 * q ^ 3 - q ^ 2) • elemSymm L 9
      + (-(4 * q ^ 5) + 13 * q ^ 4 - 15 * q ^ 3 + 7 * q ^ 2 - q) • (elemSymm L 1 * elemSymm L 8)
      + (-(q ^ 4) + 4 * q ^ 3 - 6 * q ^ 2 + 4 * q - 1) • (elemSymm L 2 * elemSymm L 7)
      + (-(q ^ 3) + 3 * q ^ 2 - 3 * q + 1) • (elemSymm L 3 * elemSymm L 6)
      + (-(6 * q ^ 4) + 15 * q ^ 3 - 12 * q ^ 2 + 3 * q)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (-(3 * q ^ 3) + 9 * q ^ 2 - 9 * q + 3) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (-(3 * q ^ 2) + 6 * q - 3) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (-(4 * q ^ 3) + 7 * q ^ 2 - 3 * q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (-(3 * q ^ 2) + 6 * q - 3)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (-(3 * q) + 3) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4)))
      + (-(q ^ 2) + q)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
      + (-q + 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4))))
      + (-1 : L)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3))))
      := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_3(e_one_sq_mul_two_sq)` at weight nine. -/
theorem bop_three_elemSymm_one_sq_mul_two_sq (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)))
      = (-(q ^ 6) + 4 * q ^ 5 - 6 * q ^ 4 + 4 * q ^ 3 - q ^ 2) • elemSymm L 9
      + (-(4 * q ^ 5) + 14 * q ^ 4 - 18 * q ^ 3 + 10 * q ^ 2 - 2 * q)
            • (elemSymm L 1 * elemSymm L 8)
      + (-(2 * q ^ 4) + 6 * q ^ 3 - 6 * q ^ 2 + 2 * q) • (elemSymm L 2 * elemSymm L 7)
      + (-(6 * q ^ 4) + 18 * q ^ 3 - 19 * q ^ 2 + 8 * q - 1)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (-(6 * q ^ 3) + 14 * q ^ 2 - 10 * q + 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (-(q ^ 2) + 2 * q - 1) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (-(4 * q ^ 3) + 10 * q ^ 2 - 8 * q + 2)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (-(6 * q ^ 2) + 10 * q - 4)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (-(2 * q) + 2) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4)))
      + (-(q ^ 2) + 2 * q - 1)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
      + (-(2 * q) + 2)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4))))
      + (-1 : L)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3))))
      := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_3(e_one_pow_four_mul_two)` at weight nine. -/
theorem bop_three_elemSymm_one_pow_four_mul_two (q : L) :
    Bop q ((3 : ℕ) : ℤ)
        (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))))
      = (-(q ^ 6) + 5 * q ^ 5 - 10 * q ^ 4 + 10 * q ^ 3 - 5 * q ^ 2 + q) • elemSymm L 9
      + (-(5 * q ^ 5) + 21 * q ^ 4 - 34 * q ^ 3 + 26 * q ^ 2 - 9 * q + 1)
            • (elemSymm L 1 * elemSymm L 8)
      + (-(q ^ 4) + 4 * q ^ 3 - 6 * q ^ 2 + 4 * q - 1) • (elemSymm L 2 * elemSymm L 7)
      + (-(10 * q ^ 4) + 34 * q ^ 3 - 42 * q ^ 2 + 22 * q - 4)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (-(4 * q ^ 3) + 12 * q ^ 2 - 12 * q + 4) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (-(10 * q ^ 3) + 26 * q ^ 2 - 22 * q + 6)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (-(6 * q ^ 2) + 12 * q - 6)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (-(5 * q ^ 2) + 9 * q - 4)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
      + (-(4 * q) + 4)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4))))
      + (-q + 1)
            • (elemSymm L 1
                * (elemSymm L 1
                    * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))))
      + (-1 : L)
            • (elemSymm L 1
                * (elemSymm L 1
                    * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_4(e_one_mul_four)` at weight nine. -/
theorem bop_four_elemSymm_one_mul_four (q : L) :
    Bop q ((4 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 4)
      = (q ^ 5 - 2 * q ^ 4 + q ^ 3) • elemSymm L 9
      + (2 * q ^ 4 - 3 * q ^ 3 + q ^ 2) • (elemSymm L 1 * elemSymm L 8)
      + (q ^ 3 - 2 * q ^ 2 + q) • (elemSymm L 2 * elemSymm L 7)
      + (q ^ 2 - 2 * q + 1) • (elemSymm L 3 * elemSymm L 6)
      + (q - 1) • (elemSymm L 4 * elemSymm L 5)
      + (q ^ 3 - q ^ 2) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (q ^ 2 - q) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (q - 1) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (1 : L) • (elemSymm L 1 * (elemSymm L 4 * elemSymm L 4)) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_4(e_two_mul_three)` at weight nine. -/
theorem bop_four_elemSymm_two_mul_three (q : L) :
    Bop q ((4 : ℕ) : ℤ) (elemSymm L 2 * elemSymm L 3)
      = (q ^ 5 - 2 * q ^ 4 + q ^ 3) • elemSymm L 9
      + (2 * q ^ 4 - 4 * q ^ 3 + 2 * q ^ 2) • (elemSymm L 1 * elemSymm L 8)
      + (2 * q ^ 3 - 3 * q ^ 2 + q) • (elemSymm L 2 * elemSymm L 7)
      + (q ^ 2 - q) • (elemSymm L 3 * elemSymm L 6)
      + (q ^ 3 - 2 * q ^ 2 + q) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (2 * q ^ 2 - 3 * q + 1) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (q - 1) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (q - 1) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (1 : L) • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 4)) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_4(e_one_sq_mul_three)` at weight nine. -/
theorem bop_four_elemSymm_one_sq_mul_three (q : L) :
    Bop q ((4 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
      = (q ^ 5 - 3 * q ^ 4 + 3 * q ^ 3 - q ^ 2) • elemSymm L 9
      + (3 * q ^ 4 - 7 * q ^ 3 + 5 * q ^ 2 - q) • (elemSymm L 1 * elemSymm L 8)
      + (q ^ 3 - 3 * q ^ 2 + 3 * q - 1) • (elemSymm L 2 * elemSymm L 7)
      + (q ^ 2 - 2 * q + 1) • (elemSymm L 3 * elemSymm L 6)
      + (3 * q ^ 3 - 5 * q ^ 2 + 2 * q) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (2 * q ^ 2 - 4 * q + 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (2 * q - 2) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
      + (q ^ 2 - q) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (q - 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (1 : L) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_4(e_one_mul_two_sq)` at weight nine. -/
theorem bop_four_elemSymm_one_mul_two_sq (q : L) :
    Bop q ((4 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))
      = (q ^ 5 - 3 * q ^ 4 + 3 * q ^ 3 - q ^ 2) • elemSymm L 9
      + (3 * q ^ 4 - 8 * q ^ 3 + 7 * q ^ 2 - 2 * q) • (elemSymm L 1 * elemSymm L 8)
      + (2 * q ^ 3 - 4 * q ^ 2 + 2 * q) • (elemSymm L 2 * elemSymm L 7)
      + (3 * q ^ 3 - 7 * q ^ 2 + 5 * q - 1) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (4 * q ^ 2 - 6 * q + 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (q - 1) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
      + (q ^ 2 - 2 * q + 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (2 * q - 2) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (1 : L) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_4(e_one_cube_mul_two)` at weight nine. -/
theorem bop_four_elemSymm_one_cube_mul_two (q : L) :
    Bop q ((4 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)))
      = (q ^ 5 - 4 * q ^ 4 + 6 * q ^ 3 - 4 * q ^ 2 + q) • elemSymm L 9
      + (4 * q ^ 4 - 13 * q ^ 3 + 15 * q ^ 2 - 7 * q + 1) • (elemSymm L 1 * elemSymm L 8)
      + (q ^ 3 - 3 * q ^ 2 + 3 * q - 1) • (elemSymm L 2 * elemSymm L 7)
      + (6 * q ^ 3 - 15 * q ^ 2 + 12 * q - 3) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (3 * q ^ 2 - 6 * q + 3) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (4 * q ^ 2 - 7 * q + 3) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (3 * q - 3) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
      + (q - 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
      + (1 : L) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4))))
      := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_4(e_one_pow_five)` at weight nine. -/
theorem bop_four_elemSymm_one_pow_five (q : L) :
    Bop q ((4 : ℕ) : ℤ)
        (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))))
      = (q ^ 5 - 5 * q ^ 4 + 10 * q ^ 3 - 10 * q ^ 2 + 5 * q - 1) • elemSymm L 9
      + (5 * q ^ 4 - 20 * q ^ 3 + 30 * q ^ 2 - 20 * q + 5) • (elemSymm L 1 * elemSymm L 8)
      + (10 * q ^ 3 - 30 * q ^ 2 + 30 * q - 10) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (10 * q ^ 2 - 20 * q + 10)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (5 * q - 5)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
      + (1 : L)
            • (elemSymm L 1
                * (elemSymm L 1
                    * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_5(e_one_mul_three)` at weight nine. -/
theorem bop_five_elemSymm_one_mul_three (q : L) :
    Bop q ((5 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 3)
      = (-(q ^ 4) + 2 * q ^ 3 - q ^ 2) • elemSymm L 9
      + (-(2 * q ^ 3) + 3 * q ^ 2 - q) • (elemSymm L 1 * elemSymm L 8)
      + (-(q ^ 2) + 2 * q - 1) • (elemSymm L 2 * elemSymm L 7)
      + (-q + 1) • (elemSymm L 3 * elemSymm L 6)
      + (-(q ^ 2) + q) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (-q + 1) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (-1 : L) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5)) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_5(e_two_sq)` at weight nine. -/
theorem bop_five_elemSymm_two_sq (q : L) :
    Bop q ((5 : ℕ) : ℤ) (elemSymm L 2 * elemSymm L 2)
      = (-(q ^ 4) + 2 * q ^ 3 - q ^ 2) • elemSymm L 9
      + (-(2 * q ^ 3) + 4 * q ^ 2 - 2 * q) • (elemSymm L 1 * elemSymm L 8)
      + (-(2 * q ^ 2) + 2 * q) • (elemSymm L 2 * elemSymm L 7)
      + (-(q ^ 2) + 2 * q - 1) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (-(2 * q) + 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (-1 : L) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5)) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_5(e_one_sq_mul_two)` at weight nine. -/
theorem bop_five_elemSymm_one_sq_mul_two (q : L) :
    Bop q ((5 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))
      = (-(q ^ 4) + 3 * q ^ 3 - 3 * q ^ 2 + q) • elemSymm L 9
      + (-(3 * q ^ 3) + 7 * q ^ 2 - 5 * q + 1) • (elemSymm L 1 * elemSymm L 8)
      + (-(q ^ 2) + 2 * q - 1) • (elemSymm L 2 * elemSymm L 7)
      + (-(3 * q ^ 2) + 5 * q - 2) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (-(2 * q) + 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
      + (-q + 1) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (-1 : L) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_5(e_one_pow_four)` at weight nine. -/
theorem bop_five_elemSymm_one_pow_four (q : L) :
    Bop q ((5 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
      = (-(q ^ 4) + 4 * q ^ 3 - 6 * q ^ 2 + 4 * q - 1) • elemSymm L 9
      + (-(4 * q ^ 3) + 12 * q ^ 2 - 12 * q + 4) • (elemSymm L 1 * elemSymm L 8)
      + (-(6 * q ^ 2) + 12 * q - 6) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (-(4 * q) + 4) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
      + (-1 : L)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
      := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_6(e_one_mul_two)` at weight nine. -/
theorem bop_six_elemSymm_one_mul_two (q : L) :
    Bop q ((6 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 2)
      = (q ^ 3 - 2 * q ^ 2 + q) • elemSymm L 9
      + (2 * q ^ 2 - 3 * q + 1) • (elemSymm L 1 * elemSymm L 8)
      + (q - 1) • (elemSymm L 2 * elemSymm L 7)
      + (q - 1) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (1 : L) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6)) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_6(e_one_cube)` at weight nine. -/
theorem bop_six_elemSymm_one_cube (q : L) :
    Bop q ((6 : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))
      = (q ^ 3 - 3 * q ^ 2 + 3 * q - 1) • elemSymm L 9
      + (3 * q ^ 2 - 6 * q + 3) • (elemSymm L 1 * elemSymm L 8)
      + (3 * q - 3) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
      + (1 : L) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6))) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_7(e_one_sq)` at weight nine. -/
theorem bop_seven_elemSymm_one_sq (q : L) :
    Bop q ((7 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1)
      = (-(q ^ 2) + 2 * q - 1) • elemSymm L 9
      + (-(2 * q) + 2) • (elemSymm L 1 * elemSymm L 8)
      + (-1 : L) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7)) := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `B_9(one)` at weight nine. -/
theorem bop_nine_one (q : L) :
    Bop q ((9 : ℕ) : ℤ) ((1 : Lambda L))
      = (-1 : L) • elemSymm L 9 := by
  simp only [bop_elemSymm_one_mul, bop_elemSymm_two_mul, bop_elemSymm_three_mul,
    bop_elemSymm_four_mul, Nat.reduceAdd, bop_natCast_one,
    bop_two_elemSymm_two', bop_two_elemSymm_three, bop_two_elemSymm_four,
    bop_two_elemSymm_five, bop_two_elemSymm_six, bop_two_elemSymm_seven,
    bop_three_elemSymm_two, bop_three_elemSymm_three, bop_three_elemSymm_four,
    bop_three_elemSymm_five, bop_three_elemSymm_six, bop_four_elemSymm_one,
    bop_four_elemSymm_two, bop_four_elemSymm_three, bop_four_elemSymm_four,
    bop_four_elemSymm_five, bop_five_elemSymm_one, bop_five_elemSymm_two,
    bop_five_elemSymm_three, bop_five_elemSymm_four, bop_six_elemSymm_one,
    bop_six_elemSymm_two, bop_six_elemSymm_three, bop_seven_elemSymm_one,
    bop_seven_elemSymm_two, bop_eight_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-! ### The consistency check: the Haglund--Morse--Zabrocki relation on four of the new rows -/

/-- **THE CHECK, first route: the relation itself.** `HJO.Sym.bop_pair_antisymm_apply` at
`(m, n) = (2, 7)` on the vacuum. No value of `B` occurs in this proof. -/
theorem bop_hmz_two_seven_of_hmz (q : L) :
    Bop q ((2 : ℕ) : ℤ) (Bop q ((7 : ℕ) : ℤ) (1 : Lambda L))
        - q • Bop q ((3 : ℕ) : ℤ) (Bop q ((6 : ℕ) : ℤ) (1 : Lambda L))
      = q • Bop q ((7 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (1 : Lambda L))
        - Bop q ((6 : ℕ) : ℤ) (Bop q ((3 : ℕ) : ℤ) (1 : Lambda L)) := by
  have h := bop_pair_antisymm_apply q ((2 : ℕ) : ℤ) ((7 : ℕ) : ℤ) (1 : Lambda L)
  rw [show (((2 : ℕ) : ℤ) + 1) = ((3 : ℕ) : ℤ) from by norm_num,
    show (((7 : ℕ) : ℤ) - 1) = ((6 : ℕ) : ℤ) from by norm_num] at h
  exact h

/-- **THE CHECK, second route: the four values.** The same `Prop` read off
`HJO.Sym.bop_two_elemSymm_seven`, `bop_three_elemSymm_six`, `bop_seven_elemSymm_two` and
`bop_six_elemSymm_three` — four of the new weight-nine rows, two of which are the only place
`HJO.Bglx.paramPleth_elemSymm_seven_eq` is read — and closed on a polynomial identity in the
weight-nine `e`-monomials. The relation itself is never used.

`HJO.Sym.bop_hmz_two_seven_eq` is the `rfl` between the two. -/
theorem bop_hmz_two_seven_of_table (q : L) :
    Bop q ((2 : ℕ) : ℤ) (Bop q ((7 : ℕ) : ℤ) (1 : Lambda L))
        - q • Bop q ((3 : ℕ) : ℤ) (Bop q ((6 : ℕ) : ℤ) (1 : Lambda L))
      = q • Bop q ((7 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (1 : Lambda L))
        - Bop q ((6 : ℕ) : ℤ) (Bop q ((3 : ℕ) : ℤ) (1 : Lambda L)) := by
  simp only [bop_seven_one, bop_six_one, bop_two_one, bop_three_one, map_neg,
    bop_two_elemSymm_seven, bop_three_elemSymm_six, bop_seven_elemSymm_two,
    bop_six_elemSymm_three]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- **The two routes prove literally the same `Prop`.** This typechecks only if the two statements
are identical, so it confirms that the check compares what it claims to compare. -/
theorem bop_hmz_two_seven_eq (q : L) :
    bop_hmz_two_seven_of_table (L := L) q = bop_hmz_two_seven_of_hmz q := rfl

end HJO.Sym

end
