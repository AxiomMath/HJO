/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitTwoPartTwoThree
public import HJO.Shuffle.SweepWitnessLhsRefuted

/-! # The two-part clause at `(2,3)`: the sweep side in the `e`-basis

`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three` reduces the right-hand side of the
clause of `HJO.Mellit.lhsRewrite_sweepWitness` at `α = (1,1)`, `(a,b) = (2,3)`, to five compositions
of Hall--Littlewood operators. This file evaluates those five outright, in the basis of
`e`-monomials of degree six, and reads off two consequences.

## The table

Every value is an unfolding of `HJO.Sym.dop_elemSymm` (`HJO.Sym.DopInt`) at `u = 0`, where
`HJO.Sym.bop_natCast` puts `B_k`, and of the two Pieri rules `HJO.Sym.dop_elemSymm_one_mul` and
`HJO.Sym.dop_elemSymm_mul`. The one new kernel coefficient is
`HJO.Bglx.paramPleth_elemSymm_four_eq`, `κ(e_4) = -(q^3+q^2u+qu^2+u^3)M`, off the three-term
recursion, continuing the pattern `κ(e_n) = (-1)^{n-1}h_{n-1}M`.

## The consequences

* `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three_eval`: the closed form of the
  clause's right-hand side, a degree-six element of `Λ` with polynomial coefficients in `q` and `u`.
  Its `e_1^2e_2^2` coefficient is `q` and its `e_2^3` coefficient is `q^2-q`.
* `HJO.Mellit.not_lhsWord_two_three_of_slopeHom_u_one`: **at `u = 1` the clause is FALSE at
  `(a,b) = (2,3)`, `α = (1,1)`**, for every `q` outside `{0, 1, -1}` and at every slope
  homomorphism. At `u = 1` the normalisation `M = (1-q)(1-u)` of `HJO.Sym.Qop` vanishes, so
  `Q_{2,3}` and `Q_{4,6}` are both the **zero map** and the `Λ` side of
  `HJO.Mellit.qop_double_apply_one_of_lhsWord` is `0`; the sweep side is not, its `e_2^3`
  coefficient being `q^2-q`. This is the inverse-becomes-zero hazard
  again, and it is a parameter the other refutations do **not** reach:
  `HJO.Mellit.not_lhsComputes_of_degenerate` needs `qu ∈ {0,1}` as well as `M = 0`, and at `u = 1`
  with `q ∉ {0,1}` we have `qu = q ∉ {0,1}`. So `u ≠ 1` is a **real** exclusion for this clause,
  not an artefact of any route.

## What is not proved here

This is one side of one instance (`α = (1,1)` at one slope) of the `hlhs` binder of
`HJO.Mellit.shuffle_of_lhs_and_induction`; neither of its binders, `hlhs` and `hind`, is discharged
here.

## References

This file bears on `HJO.Mellit.lhsRewrite_sweepWitness`, using `HJO.Sym.DopInt`, `HJO.Sym.Bop` and
`HJO.Sym.Qop`.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`κ(e_4) = -(q^3+q^2u+qu^2+u^3)M`**, from the kernel recursion
`HJO.Bglx.paramPleth_elemSymm_add_two` at `n = 2`, whose inhomogeneous term vanishes there. This
continues the pattern `κ(e_n) = (-1)^{n-1}h_{n-1}M` one step past
`HJO.Bglx.paramPleth_elemSymm_three_eq`, and it is the coefficient `B_2(e_4)` needs. -/
theorem paramPleth_elemSymm_four_eq (q u : L) :
    paramPleth q u (elemSymm L 4)
      = -((q ^ 3 + q ^ 2 * u + q * u ^ 2 + u ^ 3) * ((1 - q) * (1 - u))) := by
  have h := paramPleth_elemSymm_add_two (K := L) q u 2
  rw [show (2 : ℕ) + 2 = 4 from rfl, show (2 : ℕ) + 1 = 3 from rfl,
    paramPleth_elemSymm_three_eq, paramPleth_elemSymm_two_eq] at h
  simp only [OfNat.ofNat_ne_zero, ite_false] at h
  linear_combination h

end HJO.Bglx

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The Pieri rules at `u = 0` -/

/-- **`B_k(e_1f) = e_1B_k(f) + (1-q)B_{k+1}(f)`**, `HJO.Sym.dop_elemSymm_one_mul` at `u = 0`. -/
theorem bop_elemSymm_one_mul (q : L) (k : ℕ) (f : Lambda L) :
    Bop q ((k : ℕ) : ℤ) (elemSymm L 1 * f)
      = elemSymm L 1 * Bop q ((k : ℕ) : ℤ) f + (1 - q) • Bop q ((k + 1 : ℕ) : ℤ) f := by
  rw [bop_natCast, bop_natCast, dop_elemSymm_one_mul]
  norm_num

/-- **`B_k(e_2f) = e_2B_k(f) + (1-q)e_1B_{k+1}(f) - q(1-q)B_{k+2}(f)`**,
`HJO.Sym.dop_elemSymm_mul` at `n = 2`, `u = 0`: the three kernel coefficients read are
`κ(e_0) = 1`, `κ(e_1) = 1-q` and `κ(e_2) = -q(1-q)`. -/
theorem bop_elemSymm_two_mul (q : L) (k : ℕ) (f : Lambda L) :
    Bop q ((k : ℕ) : ℤ) (elemSymm L 2 * f)
      = elemSymm L 2 * Bop q ((k : ℕ) : ℤ) f
        + (1 - q) • (elemSymm L 1 * Bop q ((k + 1 : ℕ) : ℤ) f)
        + (-(q * (1 - q))) • Bop q ((k + 2 : ℕ) : ℤ) f := by
  simp only [bop_natCast]
  rw [dop_elemSymm_mul,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq]
  simp only [Nat.sub_zero, Nat.sub_self, elemSymm_zero, Nat.add_zero, mul_one, sub_zero,
    zero_add, one_smul]
  norm_num

/-! ### The base values `B_k(e_r)` -/

/-- `B_3(e_2) = q(1-q)e_5 - e_2e_3 + (1-q)e_1e_4`. -/
theorem bop_three_elemSymm_two (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 2)
      = (q * (1 - q)) • elemSymm L 5 - elemSymm L 2 * elemSymm L 3
        + (1 - q) • (elemSymm L 1 * elemSymm L 4) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero,
    Bglx.paramPleth_elemSymm_one_eq, Bglx.paramPleth_elemSymm_two_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_zero,
    Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_4(e_2) = -q(1-q)e_6 + e_2e_4 - (1-q)e_1e_5`. -/
theorem bop_four_elemSymm_two (q : L) :
    Bop q ((4 : ℕ) : ℤ) (elemSymm L 2)
      = (-(q * (1 - q))) • elemSymm L 6 + elemSymm L 2 * elemSymm L 4
        - (1 - q) • (elemSymm L 1 * elemSymm L 5) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero,
    Bglx.paramPleth_elemSymm_one_eq, Bglx.paramPleth_elemSymm_two_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_zero,
    Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_2(e_3) = -q^2(1-q)e_5 + qe_2e_3 - q(1-q)e_1e_4`. -/
theorem bop_two_elemSymm_three (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 3)
      = (-(q ^ 2 * (1 - q))) • elemSymm L 5 + q • (elemSymm L 2 * elemSymm L 3)
        - (q * (1 - q)) • (elemSymm L 1 * elemSymm L 4) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_zero,
    map_pow, Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_3(e_3) = q^2(1-q)e_6 - e_3^2 + (1-q)e_2e_4 + q(1-q)e_1e_5`. -/
theorem bop_three_elemSymm_three (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 3)
      = (q ^ 2 * (1 - q)) • elemSymm L 6 - elemSymm L 3 * elemSymm L 3
        + (1 - q) • (elemSymm L 2 * elemSymm L 4)
        + (q * (1 - q)) • (elemSymm L 1 * elemSymm L 5) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_zero,
    map_pow, Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- `B_2(e_4) = -q^3(1-q)e_6 - (1-q)e_3^2 + (1-q+q^2)e_2e_4 - q^2(1-q)e_1e_5`. -/
theorem bop_two_elemSymm_four (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 4)
      = (-(q ^ 3 * (1 - q))) • elemSymm L 6 - (1 - q) • (elemSymm L 3 * elemSymm L 3)
        + (1 - q + q ^ 2) • (elemSymm L 2 * elemSymm L 4)
        + (-(q ^ 2 * (1 - q))) • (elemSymm L 1 * elemSymm L 5) := by
  rw [bop_natCast, dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq, Bglx.paramPleth_elemSymm_three_eq,
    Bglx.paramPleth_elemSymm_four_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_zero,
    map_pow, Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-! ### The five compositions the sweep side reads

Each is computed by the two Pieri rules, which strip a factor `e_1` or `e_2`, bottoming out in the
base values above. The rewriting is done at `HJO.Sym.Dop q 0 k` rather than at `B_k`, because the
index of `HJO.Sym.Bop` is an integer and the cast normalises away under `simp`, after which no
`B_k`-shaped rule matches. -/

theorem bop_two_elemSymm_one' (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1)
      = elemSymm L 1 * elemSymm L 2 - (1 - q) • elemSymm L 3 := by
  rw [MvPolynomial.smul_eq_C_mul]; exact bop_two_elemSymm_one q

theorem bop_three_one' (q : L) : Bop q ((3 : ℕ) : ℤ) (1 : Lambda L) = -elemSymm L 3 := by
  rw [bop_natCast_one]; norm_num

private theorem d0_one_mul (q : L) (k : ℕ) (f : Lambda L) :
    Dop q 0 k (elemSymm L 1 * f)
      = elemSymm L 1 * Dop q 0 k f + (1 - q) • Dop q 0 (k + 1) f := by
  simpa only [bop_natCast] using bop_elemSymm_one_mul (L := L) q k f

private theorem d0_two_mul (q : L) (k : ℕ) (f : Lambda L) :
    Dop q 0 k (elemSymm L 2 * f)
      = elemSymm L 2 * Dop q 0 k f + (1 - q) • (elemSymm L 1 * Dop q 0 (k + 1) f)
        + (-(q * (1 - q))) • Dop q 0 (k + 2) f := by
  simpa only [bop_natCast] using bop_elemSymm_two_mul (L := L) q k f

private theorem d0_2e1 (q : L) :
    Dop q 0 2 (elemSymm L 1) = elemSymm L 1 * elemSymm L 2 - (1 - q) • elemSymm L 3 := by
  simpa only [bop_natCast] using bop_two_elemSymm_one' (L := L) q

private theorem d0_3e1 (q : L) :
    Dop q 0 3 (elemSymm L 1) = -(elemSymm L 1 * elemSymm L 3) + (1 - q) • elemSymm L 4 := by
  simpa only [bop_natCast] using bop_three_elemSymm_one (L := L) q

private theorem d0_2e2 (q : L) :
    Dop q 0 2 (elemSymm L 2)
      = elemSymm L 2 * elemSymm L 2 - (1 - q) • (elemSymm L 1 * elemSymm L 3)
        - (q * (1 - q)) • elemSymm L 4 := by
  simpa only [bop_natCast] using bop_two_elemSymm_two' (L := L) q

private theorem d0_3e2 (q : L) :
    Dop q 0 3 (elemSymm L 2)
      = (q * (1 - q)) • elemSymm L 5 - elemSymm L 2 * elemSymm L 3
        + (1 - q) • (elemSymm L 1 * elemSymm L 4) := by
  simpa only [bop_natCast] using bop_three_elemSymm_two (L := L) q

private theorem d0_4e2 (q : L) :
    Dop q 0 4 (elemSymm L 2)
      = (-(q * (1 - q))) • elemSymm L 6 + elemSymm L 2 * elemSymm L 4
        - (1 - q) • (elemSymm L 1 * elemSymm L 5) := by
  simpa only [bop_natCast] using bop_four_elemSymm_two (L := L) q

private theorem d0_2e3 (q : L) :
    Dop q 0 2 (elemSymm L 3)
      = (-(q ^ 2 * (1 - q))) • elemSymm L 5 + q • (elemSymm L 2 * elemSymm L 3)
        - (q * (1 - q)) • (elemSymm L 1 * elemSymm L 4) := by
  simpa only [bop_natCast] using bop_two_elemSymm_three (L := L) q

private theorem d0_3e3 (q : L) :
    Dop q 0 3 (elemSymm L 3)
      = (q ^ 2 * (1 - q)) • elemSymm L 6 - elemSymm L 3 * elemSymm L 3
        + (1 - q) • (elemSymm L 2 * elemSymm L 4)
        + (q * (1 - q)) • (elemSymm L 1 * elemSymm L 5) := by
  simpa only [bop_natCast] using bop_three_elemSymm_three (L := L) q

private theorem d0_2e4 (q : L) :
    Dop q 0 2 (elemSymm L 4)
      = (-(q ^ 3 * (1 - q))) • elemSymm L 6 - (1 - q) • (elemSymm L 3 * elemSymm L 3)
        + (1 - q + q ^ 2) • (elemSymm L 2 * elemSymm L 4)
        + (-(q ^ 2 * (1 - q))) • (elemSymm L 1 * elemSymm L 5) := by
  simpa only [bop_natCast] using bop_two_elemSymm_four (L := L) q

private theorem d0_31 (q : L) : Dop q 0 3 (1 : Lambda L) = -elemSymm L 3 := by
  simpa only [bop_natCast] using bop_three_one' (L := L) q

/- The Pieri rules at the three literal indices the computation uses. The general-`k` forms carry
`k + 1` and `k + 2` in the conclusion, which do not match a numeral after `simp` has normalised the
index, so the instances have to be stated with the numerals written out. -/

private theorem d0_one_mul_two (q : L) (f : Lambda L) :
    Dop q 0 2 (elemSymm L 1 * f)
      = elemSymm L 1 * Dop q 0 2 f + (1 - q) • Dop q 0 3 f := d0_one_mul q 2 f

private theorem d0_one_mul_three (q : L) (f : Lambda L) :
    Dop q 0 3 (elemSymm L 1 * f)
      = elemSymm L 1 * Dop q 0 3 f + (1 - q) • Dop q 0 4 f := d0_one_mul q 3 f

private theorem d0_two_mul_two (q : L) (f : Lambda L) :
    Dop q 0 2 (elemSymm L 2 * f)
      = elemSymm L 2 * Dop q 0 2 f + (1 - q) • (elemSymm L 1 * Dop q 0 3 f)
        + (-(q * (1 - q))) • Dop q 0 4 f := d0_two_mul q 2 f

/- The five compositions below are all proved by the *same* rewrite set, listing the whole table;
which members fire depends on the composition, so some are unused in each individual proof. -/
set_option linter.unusedSimpArgs false in
/-- `B_2B_2(e_1^2)`, the first of the five compositions of
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three`. -/
theorem bop_two_bop_two_elemSymm_one_sq' (q : L) :
    Bop q ((2 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1))
      = (1 : L) • (elemSymm L 1 ^ 2 * elemSymm L 2 ^ 2)
        + (-1 + q) • (elemSymm L 1 ^ 3 * elemSymm L 3)
        + (2 - 3 * q - q ^ 2 + 2 * q ^ 3) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (-2 + 2 * q ^ 2) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (-1 + 3 * q - 4 * q ^ 3 + q ^ 4 + q ^ 5) • (elemSymm L 1 * elemSymm L 5)
        + (q - q ^ 2 - q ^ 3 + q ^ 4) • (elemSymm L 2 * elemSymm L 4)
        + (1 - q - q ^ 2 + q ^ 3) • elemSymm L 3 ^ 2
        + (-q + q ^ 2 + 2 * q ^ 3 - 2 * q ^ 4 - q ^ 5 + q ^ 6) • elemSymm L 6 := by
  simp only [bop_natCast, d0_one_mul_two, d0_one_mul_three, d0_two_mul_two, d0_2e1, d0_3e1,
    d0_2e2, d0_3e2, d0_4e2, d0_2e3, d0_3e3, d0_2e4, d0_31, map_add, map_sub, map_smul, map_neg]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

set_option linter.unusedSimpArgs false in
/-- `B_2B_2(e_2)`, the second of the five: the only one carrying `e_2^3`, with coefficient `1`. -/
theorem bop_two_bop_two_elemSymm_two (q : L) :
    Bop q ((2 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 2))
      = (1 : L) • elemSymm L 2 ^ 3
        + (-2 + q + q ^ 2) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (1 - q - q ^ 2 + q ^ 3) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (q - 2 * q ^ 3 + q ^ 5) • (elemSymm L 1 * elemSymm L 5)
        + (-1 + q ^ 2 - q ^ 3 + q ^ 4) • (elemSymm L 2 * elemSymm L 4)
        + (1 - q - q ^ 2 + q ^ 3) • elemSymm L 3 ^ 2
        + (q ^ 3 - q ^ 4 - q ^ 5 + q ^ 6) • elemSymm L 6 := by
  simp only [bop_natCast, d0_one_mul_two, d0_one_mul_three, d0_two_mul_two, d0_2e1, d0_3e1,
    d0_2e2, d0_3e2, d0_4e2, d0_2e3, d0_3e3, d0_2e4, d0_31, map_add, map_sub, map_smul, map_neg]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

set_option linter.unusedSimpArgs false in
/-- `B_3B_2(e_1)`, the third of the five. -/
theorem bop_three_bop_two_elemSymm_one (q : L) :
    Bop q ((3 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 1))
      = (-1 : L) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (1 - q) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (-1 + 2 * q - q ^ 3) • (elemSymm L 1 * elemSymm L 5)
        + (q - q ^ 2) • (elemSymm L 2 * elemSymm L 4)
        + (1 - q) • elemSymm L 3 ^ 2
        + (-q + q ^ 2 + q ^ 3 - q ^ 4) • elemSymm L 6 := by
  simp only [bop_natCast, d0_one_mul_two, d0_one_mul_three, d0_two_mul_two, d0_2e1, d0_3e1,
    d0_2e2, d0_3e2, d0_4e2, d0_2e3, d0_3e3, d0_2e4, d0_31, map_add, map_sub, map_smul, map_neg]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

set_option linter.unusedSimpArgs false in
/-- `B_2B_3(e_1)`, the fourth of the five. It is `q` times `HJO.Sym.bop_three_bop_two_elemSymm_one`:
the two orders of the composition differ by the single scalar `q`. -/
theorem bop_two_bop_three_elemSymm_one (q : L) :
    Bop q ((2 : ℕ) : ℤ) (Bop q ((3 : ℕ) : ℤ) (elemSymm L 1))
      = (-q) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (q - q ^ 2) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (-q + 2 * q ^ 2 - q ^ 4) • (elemSymm L 1 * elemSymm L 5)
        + (q ^ 2 - q ^ 3) • (elemSymm L 2 * elemSymm L 4)
        + (q - q ^ 2) • elemSymm L 3 ^ 2
        + (-q ^ 2 + q ^ 3 + q ^ 4 - q ^ 5) • elemSymm L 6 := by
  simp only [bop_natCast, d0_one_mul_two, d0_one_mul_three, d0_two_mul_two, d0_2e1, d0_3e1,
    d0_2e2, d0_3e2, d0_4e2, d0_2e3, d0_3e3, d0_2e4, d0_31, map_add, map_sub, map_smul, map_neg]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

set_option linter.unusedSimpArgs false in
/-- `B_3B_3(1)`, the fifth of the five. -/
theorem bop_three_bop_three_one (q : L) :
    Bop q ((3 : ℕ) : ℤ) (Bop q ((3 : ℕ) : ℤ) (1 : Lambda L))
      = (1 : L) • elemSymm L 3 ^ 2 + (-1 + q) • (elemSymm L 2 * elemSymm L 4)
        + (-q + q ^ 2) • (elemSymm L 1 * elemSymm L 5)
        + (-q ^ 2 + q ^ 3) • elemSymm L 6 := by
  simp only [bop_natCast, d0_one_mul_two, d0_one_mul_three, d0_two_mul_two, d0_2e1, d0_3e1,
    d0_2e2, d0_3e2, d0_4e2, d0_2e3, d0_3e3, d0_2e4, d0_31, map_add, map_sub, map_smul, map_neg]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring


/-- **The nine degree-six `e`-monomials that occur are linearly independent enough**: a combination
of them with nonzero `e_2^3` coefficient is nonzero. The substitution `p_k ↦ e_k` is injective over
a field of characteristic zero (`HJO.Sym.elemSymmSub_injective`), so the relation pulls back to one
among the free generators, where the nine monomials are distinct; evaluating at `p_2 = 1` and every
other generator `0` leaves the `e_2^3` coefficient alone.

The degree-six analogue of `HJO.Sym.elemSymm_two_sq_add_smul_ne_zero`. -/
@[hjo "lem_sym_elem_deg_six_ne_zero"]
theorem elemSymm_deg_six_ne_zero (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : L) {c : L} (hc : c ≠ 0) :
    c₀ • (elemSymm L 1 ^ 2 * elemSymm L 2 ^ 2)
        + c • elemSymm L 2 ^ 3
        + c₁ • (elemSymm L 1 ^ 3 * elemSymm L 3)
        + c₂ • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + c₃ • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + c₄ • (elemSymm L 1 * elemSymm L 5)
        + c₅ • (elemSymm L 2 * elemSymm L 4)
        + c₆ • elemSymm L 3 ^ 2
        + c₇ • elemSymm L 6 ≠ 0 := by
  intro h
  set P : Lambda L :=
    c₀ • ((MvPolynomial.X 0 : Lambda L) ^ 2 * (MvPolynomial.X 1 : Lambda L) ^ 2)
      + c • (MvPolynomial.X 1 : Lambda L) ^ 3
      + c₁ • ((MvPolynomial.X 0 : Lambda L) ^ 3 * (MvPolynomial.X 2 : Lambda L))
      + c₂ • ((MvPolynomial.X 0 : Lambda L) ^ 2 * (MvPolynomial.X 3 : Lambda L))
      + c₃ • ((MvPolynomial.X 0 : Lambda L) * (MvPolynomial.X 1 : Lambda L)
          * (MvPolynomial.X 2 : Lambda L))
      + c₄ • ((MvPolynomial.X 0 : Lambda L) * (MvPolynomial.X 4 : Lambda L))
      + c₅ • ((MvPolynomial.X 1 : Lambda L) * (MvPolynomial.X 3 : Lambda L))
      + c₆ • (MvPolynomial.X 2 : Lambda L) ^ 2
      + c₇ • (MvPolynomial.X 5 : Lambda L) with hP
  have hpre : elemSymmSub L P
      = c₀ • (elemSymm L 1 ^ 2 * elemSymm L 2 ^ 2)
        + c • elemSymm L 2 ^ 3
        + c₁ • (elemSymm L 1 ^ 3 * elemSymm L 3)
        + c₂ • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + c₃ • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + c₄ • (elemSymm L 1 * elemSymm L 5)
        + c₅ • (elemSymm L 2 * elemSymm L 4)
        + c₆ • elemSymm L 3 ^ 2
        + c₇ • elemSymm L 6 := by
    rw [hP]
    simp only [map_add, map_mul, map_pow, map_smul, elemSymmSub_X]
  have hzero : P = 0 := elemSymmSub_injective L (by rw [hpre, h, map_zero])
  have hev := congrArg (MvPolynomial.aeval fun i : ℕ => if i = 1 then (1 : L) else 0) hzero
  rw [hP] at hev
  simp only [map_add, map_mul, map_pow, map_smul, MvPolynomial.aeval_X, map_zero] at hev
  norm_num at hev
  exact hc hev

end HJO.Sym

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The closed form of the sweep side -/

/-- **The right-hand side of the clause at `α = (1,1)`, `(a,b) = (2,3)`, in the `e`-basis.**

`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three` with the five compositions
evaluated. Nine `e`-monomials of degree six occur; the `e_1^2e_2^2` coefficient is `q` and the
`e_2^3` coefficient is `q^2 - q`, and neither carries any `u`. -/
@[hjo "lem_mellit_lhs_two_three_value"]
theorem constantCoeff_lowerRun_two_stageWordTotal_two_three_eval (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 (Mellit.stageWordTotal q u 2 3 [1, 1]))
      = q • (elemSymm L 1 ^ 2 * elemSymm L 2 ^ 2)
        + (-q + q ^ 2) • elemSymm L 2 ^ 3
        + (-q + q ^ 2) • (elemSymm L 1 ^ 3 * elemSymm L 3)
        + (q - q * u - q ^ 2 - q ^ 3 + q ^ 3 * u + q ^ 5) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (q * u - 3 * q ^ 2 + q ^ 2 * u + 2 * q ^ 3 + q ^ 4)
            • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (-q + q * u + 2 * q ^ 2 - q ^ 2 * u - q ^ 2 * u ^ 2 + q ^ 3 - 2 * q ^ 3 * u
            + q ^ 3 * u ^ 2 - 2 * q ^ 4 + q ^ 4 * u - q ^ 5 + q ^ 5 * u + q ^ 7)
            • (elemSymm L 1 * elemSymm L 5)
        + (q - q * u ^ 2 - q ^ 2 * u + q ^ 2 * u ^ 2 - 2 * q ^ 3 + q ^ 4 + q ^ 4 * u - q ^ 5
            + q ^ 6) • (elemSymm L 2 * elemSymm L 4)
        + (-q * u + q * u ^ 2 + q ^ 2 - q ^ 3 + q ^ 3 * u - q ^ 4 + q ^ 5) • elemSymm L 3 ^ 2
        + (-q ^ 2 + q ^ 2 * u + q ^ 3 - q ^ 3 * u ^ 2 + q ^ 4 - 2 * q ^ 4 * u + q ^ 4 * u ^ 2
            - q ^ 6 + q ^ 6 * u - q ^ 7 + q ^ 8) • elemSymm L 6 := by
  rw [constantCoeff_lowerRun_two_stageWordTotal_two_three hq0 hu0 hq1,
    bop_two_bop_two_elemSymm_one_sq', bop_two_bop_two_elemSymm_two,
    bop_three_bop_two_elemSymm_one, bop_two_bop_three_elemSymm_one, bop_three_bop_three_one]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-! ### The clause at `α = (1,1)`, `(a,b) = (2,3)` is FALSE at `u = 1` -/

/-- The sweep side at `u = 1`: nine `e`-monomials, with `e_2^3` coefficient `q^2-q`. -/
theorem constantCoeff_lowerRun_two_stageWordTotal_two_three_u_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 (Mellit.stageWordTotal q (1 : L) 2 3 [1, 1]))
      = q • (elemSymm L 1 ^ 2 * elemSymm L 2 ^ 2)
        + (-q + q ^ 2) • elemSymm L 2 ^ 3
        + (-q + q ^ 2) • (elemSymm L 1 ^ 3 * elemSymm L 3)
        + (-q ^ 2 + q ^ 5) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (q - 2 * q ^ 2 + 2 * q ^ 3 + q ^ 4) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (-q ^ 4 + q ^ 7) • (elemSymm L 1 * elemSymm L 5)
        + (-2 * q ^ 3 + 2 * q ^ 4 - q ^ 5 + q ^ 6) • (elemSymm L 2 * elemSymm L 4)
        + (q ^ 2 - q ^ 4 + q ^ 5) • elemSymm L 3 ^ 2
        + (-q ^ 7 + q ^ 8) • elemSymm L 6 := by
  rw [constantCoeff_lowerRun_two_stageWordTotal_two_three_eval hq0 one_ne_zero hq1]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

end HJO.Sweep

namespace HJO.Mellit

open HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

/-- **The `Λ`-level clause at `α = (1,1)` is FALSE at `u = 1`, `(a,b) = (2,3)`**, for every `q`
outside `{0, 1, -1}`.

At `u = 1` the normalisation `M = (1-q)(1-u)` of `HJO.Sym.Qop` vanishes, so by
`HJO.Sym.qop_eq_zero_of_one_lt` both `Q_{2,3}` and `Q_{4,6}` are the **zero map**, and the `Λ` side
of `HJO.Mellit.qop_double_apply_one_of_lhsWord` is `0`. The sweep side is not: its `e_2^3`
coefficient is `q^2-q`, nonzero, and `qu+1 = q+1` is a unit. So the clause equates `0` with
something nonzero.

This is the inverse-becomes-zero hazard, and it reaches a parameter the other refutations do not:
`HJO.Mellit.not_lhsComputes_of_degenerate` asks for `qu ∈ {0,1}` **as well as** `M = 0`, and at
`u = 1` with `q ∉ {0,1}` we have `qu = q ∉ {0,1}`. So `u ≠ 1` is a **real** exclusion for the clause
at `α = (1,1)`, not an artefact of any route to it.

The hypothesis `hΘ` is the honest form of the statement and not decoration: `HJO.Mellit.LhsWord`
opens with `∀ Θ`, and no slope homomorphism is constructed here, so what is refuted
is the clause *at any slope homomorphism there may be* — exactly the non-vacuity caveat
`HJO/Shuffle/SweepWitnessLhsRefuted.lean` records. -/
@[hjo "not_mellit_lhs_two_three_u_one"]
theorem not_lhsWord_two_three_of_slopeHom_u_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqm : q ≠ -1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q 1 Θ) :
    ¬ LhsWord q (1 : L) 2 3 := by
  intro hw
  have hM : (1 - q) * (1 - (1 : L)) = 0 := by ring
  have hne : q + 1 ≠ 0 := fun h => hqm (by linear_combination h)
  have hq1s : q - 1 ≠ 0 := sub_ne_zero.2 hq1
  have hc : (q + 1) * (-q + q ^ 2) ≠ 0 := by
    refine mul_ne_zero hne ?_
    rw [show -q + q ^ 2 = q * (q - 1) from by ring]
    exact mul_ne_zero hq0 hq1s
  have key := qop_double_apply_one_of_lhsWord (by simpa using hq0) (by simpa using hq1) hΘ hw
  rw [qop_eq_zero_of_one_lt hM (by omega) 3, qop_eq_zero_of_one_lt hM (by omega) 6] at key
  simp only [LinearMap.zero_apply, smul_zero, add_zero] at key
  rw [constantCoeff_lowerRun_two_stageWordTotal_two_three_u_one hq0 hq1,
    show q * (1 : L) + 1 = q + 1 from by ring] at key
  refine elemSymm_deg_six_ne_zero (L := L) ((q + 1) * q) ((q + 1) * (-q + q ^ 2))
    ((q + 1) * (-q ^ 2 + q ^ 5)) ((q + 1) * (q - 2 * q ^ 2 + 2 * q ^ 3 + q ^ 4))
    ((q + 1) * (-q ^ 4 + q ^ 7)) ((q + 1) * (-2 * q ^ 3 + 2 * q ^ 4 - q ^ 5 + q ^ 6))
    ((q + 1) * (q ^ 2 - q ^ 4 + q ^ 5)) ((q + 1) * (-q ^ 7 + q ^ 8)) hc ?_
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat] at key ⊢
  linear_combination -key

end HJO.Mellit

end
