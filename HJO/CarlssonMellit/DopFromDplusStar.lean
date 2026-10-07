/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.HbTwist
public import HJO.CMStructure.StarEasy
public meta import HJO.Attr

/-! # The basic operator from the starred raising operator

One lemma: on `V_0 = Λ` the basic operator `D_1` is `-d_-d^*_+`.

The mechanism is that the three substitutions compose to the plethystic displacement. On a constant
`f ∈ Λ` the starred raising operator `d^*_+` of `HJO.Sweep.dplusStar` at `k = 0` is `cy_1 τ_{1,1}`,
and `d_-` of `HJO.Sweep.dminusCM` begins with `τ^-_{1,1}`; following `p_r` through,
`τ_{1,1}` adds `(q^r - 1)y_1^r`, `cy_1` turns `y_1` into `u y_1` and so the added term
into `(q^r-1)u^ry_1^r`, and `τ^-_{1,1}` subtracts `(q^r-1)y_1^r` again, leaving
`p_r + (q^r-1)(u^r-1)y_1^r = p_r + (1-q^r)(1-u^r)y_1^r`. That is exactly `HJO.Sym.plethShift` with
`y_1` in place of `z⁻¹`, so the composite is `f[X + M/z]` transported along `w ↦ y_1`, and the
`j`-th coefficient of the result is the displacement coefficient `f_{[j]}` of `HJO.Sym.shiftCoeff`.

What `d_-` then does to that expansion is pair the coefficient of `y_1^j` against
`(-1)^je_{j+1}`, and what `D_1` does by `HJO.Sym.DopInt` is pair it against `(-1)^{1+j}e_{1+j}`. The
two families differ by a global sign, which is the sign of the lemma.

## Main results

* `HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`,
  `D_1f = -d_-(d^*_+f)` for `f ∈ Λ = V_0`.

## Implementation notes

**`V_0 = Λ` is the constants.** `HJO.Sweep.piece L 0` is the `Λ`-subalgebra of
`HJO.Sweep.Total L = Λ[y_1, y_2, …]` using no auxiliary variable, so an element of `V_0` is
`MvPolynomial.C f` for an `f : Λ`, and a claim about `V_0` is a claim about those. That is the shape
`HJO.Sweep.dminusCM_cmDPlus_C` is already stated in, and this file
follows it: the hypothesis `f ∈ Λ = V_0` is discharged by the encoding rather than carried.

**No side condition.** Nothing here divides, and the scalars `q^r - 1` and `u^r - 1` are defined at
every `q` and `u`. In particular the lemma holds at `q = 1` and at `u = 1`, where both sides are the
value of the same degenerate substitution.

**The sign lives in the pairing family, not in the operators.** `d_-` pairs against `e_{j+1}` with
the sign `(-1)^j` and `D_1` against `e_{1+j}` with the sign `(-1)^{1+j}`; the elementary functions
agree and the signs are opposite, term by term, which is why the identity is exact rather than up to
a correction.

## References

This file proves `HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`, from `HJO.Sym.DopInt`,
`HJO.Sym.shiftCoeff`, `HJO.Sym.plethShift`, `HJO.Sweep.qshift`, `HJO.Sweep.qshiftNeg`,
`HJO.Sweep.dminusCM` and `HJO.Sweep.dplusStar`.
-/

@[expose] public section

open Finset

namespace HJO.Sweep

section DopFromDplusStar

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The three substitutions compose to the plethystic displacement -/

omit [Algebra ℚ L] in
/-- `cy_1` sends `y_1` to `u y_1`, which is `cycleShift_auxVar_last` at `k = 0` with the auxiliary
variable spelled out as the polynomial generator. -/
theorem cycleShift_zero_X_zero (u : L) :
    cycleShift u 0 (MvPolynomial.X 0 : Total L) = scal u * MvPolynomial.X 0 :=
  cycleShift_auxVar_last u 0

omit [Algebra ℚ L] in
/-- **The composite on a power sum.** Following `p_{i+1}` through `τ_{1,1}`, `cy_1` and `τ^-_{1,1}`
adds `(q^{i+1}-1)(u^{i+1}-1)y_1^{i+1}` to it, which is `(1-q^{i+1})(1-u^{i+1})y_1^{i+1}` -- the
scalar `HJO.Sym.plethShift` attaches to `p_{i+1}`. -/
theorem qshiftNeg_cycleShift_qshift_gen (q u : L) (i : ℕ) :
    qshiftNeg q 1 (cycleShift u 0 (qshift q 1 (MvPolynomial.C (MvPolynomial.X i) : Total L)))
      = Polynomial.aeval (MvPolynomial.X 0 : Total L)
          (Sym.plethShift q u (MvPolynomial.X i)) := by
  have hps : (MvPolynomial.X i : Sym.Lambda L) = Sym.powerSum L (i + 1) := by
    rw [Sym.powerSum, Nat.add_sub_cancel]
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := by rw [auxVar, Nat.sub_self]
  have hrhs : Polynomial.aeval (MvPolynomial.X 0 : Total L)
        (Sym.plethShift q u (MvPolynomial.X i))
      = MvPolynomial.C (Sym.powerSum L (i + 1))
        + scal ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))
          * (MvPolynomial.X 0 : Total L) ^ (i + 1) := by
    rw [Sym.plethShift, MvPolynomial.aeval_X, map_add, map_mul, map_pow, Polynomial.aeval_C,
      Polynomial.aeval_C, Polynomial.aeval_X]
    rfl
  have hlhs : qshiftNeg q 1 (cycleShift u 0 (qshift q 1
        (MvPolynomial.C (MvPolynomial.X i) : Total L)))
      = MvPolynomial.C (Sym.powerSum L (i + 1))
        - scal (q ^ (i + 1) - 1) * (MvPolynomial.X 0 : Total L) ^ (i + 1)
        + scal (q ^ (i + 1) - 1) * scal (u ^ (i + 1))
          * (MvPolynomial.X 0 : Total L) ^ (i + 1) := by
    rw [hps, qshift_powerSum, hav, map_add, map_mul, map_pow, cycleShift_C, cycleShift_scal,
      cycleShift_zero_X_zero, mul_pow, ← scal_pow, map_add, map_mul, map_mul, map_pow,
      qshiftNeg_powerSum, qshiftNeg_scal, qshiftNeg_scal, qshiftNeg_auxVar, hav]
    ring
  have hkey : (scal ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1))) : Total L)
      = -scal (q ^ (i + 1) - 1) + scal (q ^ (i + 1) - 1) * scal (u ^ (i + 1)) := by
    rw [← scal_mul, ← scal_neg, ← scal_add]
    congr 1
    ring
  rw [hlhs, hrhs, hkey]
  ring

omit [Algebra ℚ L] in
/-- **The composite is the plethystic displacement, transported along `w ↦ y_1`.** For every
`f ∈ Λ`, `τ^-_{1,1}(cy_1(τ_{1,1}(f))) = f[X + M/z]` with `z⁻¹` read as `y_1`.

All three substitutions are algebra homomorphisms, as are `HJO.Sym.plethShift` and the evaluation
`w ↦ y_1`, so the identity reduces to the power sums. -/
theorem qshiftNeg_cycleShift_qshift_C (q u : L) (f : Sym.Lambda L) :
    qshiftNeg q 1 (cycleShift u 0 (qshift q 1 (MvPolynomial.C f : Total L)))
      = Polynomial.aeval (MvPolynomial.X 0 : Total L) (Sym.plethShift q u f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have hscal : (MvPolynomial.C (MvPolynomial.C a : Sym.Lambda L) : Total L) = scal a := rfl
    rw [Sym.plethShift_C, hscal, Polynomial.aeval_C]
    have halg : (algebraMap (Sym.Lambda L) (Total L) (MvPolynomial.C a)) = scal a := rfl
    rw [halg, scal_eq_algebraMap, (qshift q 1).commutes, ← scal_eq_algebraMap, cycleShift_scal,
      qshiftNeg_scal]
  | add p g hp hg => simp only [map_add]; rw [hp, hg]
  | mul_X p i hp =>
    simp only [map_mul]
    rw [hp, qshiftNeg_cycleShift_qshift_gen]

/-! ### The lowering operator against the transported displacement -/

/-- `d_-`'s coefficient extraction on a power of `y_1`: the single surviving term carries
`(-1)^je_{j+1}`. -/
theorem lowerCoeffShift_zero_X_pow (j : ℕ) :
    lowerCoeffShift L 0 ((MvPolynomial.X 0 : Total L) ^ j)
      = (-1 : Total L) ^ j * MvPolynomial.C (Sym.elemSymm L (j + 1)) := by
  have hpow : ((MvPolynomial.X 0 : Total L)) ^ j
      = MvPolynomial.monomial (Finsupp.single 0 j) 1 := MvPolynomial.X_pow_eq_monomial
  rw [hpow, lowerCoeffShift_monomial]
  simp

/-- **`d_-`'s extraction is the pairing against `(-1)^je_{j+1}`.** Transporting a polynomial in
`w = z⁻¹` over `Λ` to `Λ[y]` along `w ↦ y_1` and applying the extraction gives the constant whose
value is `HJO.Sym.coeffPairing` against the family `(-1)^je_{j+1}`. -/
theorem lowerCoeffShift_zero_aeval (P : Polynomial (Sym.Lambda L)) :
    lowerCoeffShift L 0 (Polynomial.aeval (MvPolynomial.X 0 : Total L) P)
      = MvPolynomial.C (Sym.coeffPairing (fun j => (-1) ^ j * Sym.elemSymm L (j + 1)) P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add]; rw [hP, hQ]
  | monomial j a =>
    have hsmul : (algebraMap (Sym.Lambda L) (Total L) a) * (MvPolynomial.X 0 : Total L) ^ j
        = a • ((MvPolynomial.X 0 : Total L) ^ j) := (Algebra.smul_def a _).symm
    have hneg : ((-1 : Total L)) = MvPolynomial.C (-1 : Sym.Lambda L) := by simp
    rw [Polynomial.aeval_monomial, hsmul, map_smul, lowerCoeffShift_zero_X_pow,
      Sym.coeffPairing_monomial, Algebra.smul_def, hneg, ← map_pow, ← map_mul,
      MvPolynomial.algebraMap_eq, ← map_mul]

/-! ### The main result -/

/-- **The basic operator from the starred raising operator.** For
every `f ∈ Λ = V_0`, `D_1f = -d_-(d^*_+f)`.

The three substitutions making up `d_-d^*_+` compose to the plethystic displacement transported
along `w ↦ y_1` (`HJO.Sweep.qshiftNeg_cycleShift_qshift_C`), and what remains on each side is a
pairing of its coefficients: `d_-` against `(-1)^je_{j+1}` and `D_1` against `(-1)^{1+j}e_{1+j}`.
Those families are negatives of each other term by term, which is the sign.

`f ∈ V_0` is the constant `MvPolynomial.C f`, and no condition on `q` or `u` is carried. -/
@[hjo "lem_cm_d1_dminus_dplusstar"]
theorem dop_one_eq_neg_dminusCM_dplusStar (q u : L) (f : Sym.Lambda L) :
    MvPolynomial.C (Sym.Dop q u 1 f)
      = -dminusCM q 1 (dplusStar q u 0 (MvPolynomial.C f : Total L)) := by
  have hstep : dminusCM q 1 (dplusStar q u 0 (MvPolynomial.C f : Total L))
      = lowerCoeffShift L 0 (Polynomial.aeval (MvPolynomial.X 0 : Total L)
          (Sym.plethShift q u f)) := by
    change lowerCoeffShift L 0
      (qshiftNeg q 1 (cycleShift u 0 (qshift q 1 (MvPolynomial.C f : Total L)))) = _
    rw [qshiftNeg_cycleShift_qshift_C]
  rw [hstep, lowerCoeffShift_zero_aeval, ← map_neg]
  congr 1
  set N := (Sym.plethShift q u f).natDegree + 1 with hN
  have hzero : ∀ j : ℕ, N ≤ j → (Sym.plethShift q u f).coeff j = 0 := fun j hj =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [Sym.dop_apply, Sym.coeffPairing_eq_sum_range _ _ hzero,
    Sym.coeffPairing_eq_sum_range _ _ hzero, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (1 : ℕ) + j = j + 1 from Nat.add_comm 1 j, pow_succ]
  ring

end DopFromDplusStar

end HJO.Sweep
