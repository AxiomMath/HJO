/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import HJO.CarlssonMellit.Parameters
public import HJO.Evaluation.PhiE
public import HJO.Symmetric.AxisFree
public meta import HJO.Attr

/-! # The double displacement and the sign of the grading

Two more operations on the ring of symmetric functions are needed in the Haglund--Morse--Zabrocki
part of the Carlsson--Mellit argument: the displacement `β₂` in *both* auxiliary variables at once,
which is what a composition of two single displacements produces, and the sign `ε_±` of the
grading, which acts on the degree-`n` component as multiplication by `(-1)^n`.

## Main definitions

* `HJO.Sym.plethShiftTwo`: `β₂`.
* `HJO.Sym.signGrading`: `ε_±`.

## Implementation notes

`β₂` sends `p_k` to `p_k + (1 - q^k)(z^{-k} + w^{-k})`, so its image consists of Laurent
polynomials in the two variables: the target here is `Λ[z, z⁻¹][w, w⁻¹]`, the subring of the
Laurent series ring `𝒵 = Λ[[z]][z⁻¹][[w]][w⁻¹]` in which the image actually lies, exactly as the
target of `HJO.Sym.plethHallLittlewood` is the polynomial ring in which its image lies rather than
the whole of `Λ[z, z⁻¹]`. Every coefficient extraction `[z^aw^b]` performed on `β₂` is the
extraction on this subring, and the inclusion into `𝒵` is coefficientwise.

`ε_±` is `HJO.Sym.plethScale (-1)`, and that identification is a theorem rather than the
definition: `signGrading_of_mem_lambdaComp` is the defining property — multiplication by
`(-1)^n` on the degree-`n` component — and it holds because the scaling `σ_c` multiplies a weighted
homogeneous element of degree `n` by `c^n`. So `ε_±` is an *algebra* map and not merely a linear
one, which is what makes it an involution.

Note that `ε_±` is not `HJO.Sym.plethNegate`: the latter sends `p_k` to `-p_k`, whereas `ε_±` sends
it to `(-1)^k p_k`, and `p_k` is homogeneous of degree `k`.

## References

This file defines `HJO.Sym.plethShiftTwo` and `HJO.Sym.signGrading`.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The double displacement -/

/-- **The double displacement** `β₂ : f ↦ f[X - (q-1)/z - (q-1)/w]`: the `K`-algebra homomorphism
from `Lambda K` sending the power sum `p_k` to `p_k + (1 - q^k)(z^{-k} + w^{-k})`. It is the
addition of the two virtual alphabets `-(q-1)/z` and `-(q-1)/w`. The target is the two-variable
Laurent ring `Λ[z, z⁻¹][w, w⁻¹]`, the subring of the Laurent series ring `𝒵` in which the image
lies: the inner `LaurentPolynomial.T` is the variable `z` and the outer one is `w`. -/
@[hjo "def_cm_bshift_double"]
noncomputable def plethShiftTwo {K : Type*} [CommRing K] (q : K) :
    Lambda K →ₐ[K] LaurentPolynomial (LaurentPolynomial (Lambda K)) :=
  MvPolynomial.aeval fun i =>
    LaurentPolynomial.C (LaurentPolynomial.C (powerSum K (i + 1))) +
      LaurentPolynomial.C (LaurentPolynomial.C (MvPolynomial.C (1 - q ^ (i + 1)))) *
        (LaurentPolynomial.C (LaurentPolynomial.T (-(i + 1 : ℤ))) +
          LaurentPolynomial.T (-(i + 1 : ℤ)))

section Shift

variable {K : Type*} [CommRing K]

/-- The double displacement on the generator `i` of `Lambda K`, which stands for `p_{i+1}`. -/
@[simp]
theorem plethShiftTwo_X (q : K) (i : ℕ) :
    plethShiftTwo q (MvPolynomial.X i) =
      LaurentPolynomial.C (LaurentPolynomial.C (powerSum K (i + 1))) +
        LaurentPolynomial.C (LaurentPolynomial.C (MvPolynomial.C (1 - q ^ (i + 1)))) *
          (LaurentPolynomial.C (LaurentPolynomial.T (-(i + 1 : ℤ))) +
            LaurentPolynomial.T (-(i + 1 : ℤ))) := by
  rw [plethShiftTwo, MvPolynomial.aeval_X]

/-- **The defining property of `β₂`**: it sends the power sum `p_k` to
`p_k + (1 - q^k)(z^{-k} + w^{-k})` for every `k ≥ 1`. -/
@[hjo "def_cm_bshift_double"]
theorem plethShiftTwo_powerSum (q : K) {k : ℕ} (hk : 0 < k) :
    plethShiftTwo q (powerSum K k) =
      LaurentPolynomial.C (LaurentPolynomial.C (powerSum K k)) +
        LaurentPolynomial.C (LaurentPolynomial.C (MvPolynomial.C (1 - q ^ k))) *
          (LaurentPolynomial.C (LaurentPolynomial.T (-(k : ℤ))) +
            LaurentPolynomial.T (-(k : ℤ))) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hX : powerSum K (m + 1) = MvPolynomial.X m := by rw [powerSum, Nat.add_sub_cancel]
  have hT : (-((m : ℤ) + 1)) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hX, plethShiftTwo_X, hX, hT]

/-- The double displacement of a constant is that constant. -/
@[simp]
theorem plethShiftTwo_C (q : K) (a : K) :
    plethShiftTwo q (MvPolynomial.C a) =
      LaurentPolynomial.C (LaurentPolynomial.C (MvPolynomial.C a)) := by
  rw [plethShiftTwo, MvPolynomial.aeval_C]
  rfl

end Shift

/-! ### The sign of the grading -/

/-- **The sign of the grading** `ε_±`: the endomorphism of `Lambda K` acting on the homogeneous
component of degree `n` as multiplication by `(-1)^n`. It is the scaling of the alphabet by `-1`,
which is what `signGrading_of_mem_lambdaComp` records; being an algebra map rather than merely a
linear one is what makes it an involution.

It is *not* `HJO.Sym.plethNegate`, which sends `p_k` to `-p_k`: this one sends `p_k` to
`(-1)^k p_k`, and `p_k` is homogeneous of degree `k`. -/
@[hjo "def_cm_sign_grading"]
noncomputable def signGrading (K : Type*) [CommRing K] : Lambda K →ₐ[K] Lambda K :=
  plethScale (-1)

variable {K : Type*} [CommRing K]

/-- **The defining property of `ε_±`**: on the homogeneous component of degree `n` it is
multiplication by `(-1)^n`. -/
@[hjo "def_cm_sign_grading"]
theorem signGrading_of_mem_lambdaComp {n : ℕ} {f : Lambda K} (hf : f ∈ LambdaComp K n) :
    signGrading K f = (-1 : K) ^ n • f := by
  rw [signGrading, HJO.PhiE.plethScale_of_isWeightedHomogeneous (mem_lambdaComp.1 hf),
    MvPolynomial.smul_eq_C_mul]

/-- `ε_±` negates the generator `i` of `Lambda K` an odd number of times: it sends `p_{i+1}` to
`(-1)^{i+1} p_{i+1}`, which is the degree-`(i+1)` case of its defining property. -/
@[simp]
theorem signGrading_X (i : ℕ) :
    signGrading K (MvPolynomial.X i) = MvPolynomial.C ((-1 : K) ^ (i + 1)) * MvPolynomial.X i := by
  rw [signGrading, plethScale, diagScale_X]

/-- **`ε_±` is an involution**, as multiplication by `(-1)^n` on each component must be: the two
applications contribute `(-1)^{2(i+1)} = 1` at every generator. -/
@[hjo "def_cm_sign_grading"]
theorem signGrading_signGrading (f : Lambda K) : signGrading K (signGrading K f) = f := by
  suffices h : (signGrading K).comp (signGrading K) = AlgHom.id K (Lambda K) by
    exact congrArg (fun g => g f) h
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, signGrading_X, map_mul, signGrading_X, signGrading, plethScale,
    diagScale_C, AlgHom.id_apply, ← mul_assoc, ← MvPolynomial.C_mul, ← pow_add,
    show i + 1 + (i + 1) = 2 * (i + 1) by ring, pow_mul]
  norm_num

/-- `ε_±` differs from `ω₋`: on the generator standing for `p_2`, a component of even degree, the
sign map is the identity while `ω₋` negates. The two agree on the odd components and nowhere else,
which is the confusion the bracket notation invites. -/
theorem signGrading_ne_plethNegate_X_one [Nontrivial K] (h : (2 : K) ≠ 0) :
    signGrading K (MvPolynomial.X 1) ≠ plethNegate K (MvPolynomial.X 1) := by
  rw [signGrading_X, plethNegate_X]
  intro hx
  refine h ?_
  have hc : (1 : K) = -1 := by
    have := congrArg (MvPolynomial.coeff (Finsupp.single 1 1)) hx
    simpa using this
  have h0 : (1 : K) - (-1) = 0 := sub_eq_zero_of_eq hc
  rw [sub_neg_eq_add] at h0
  rw [show (2 : K) = 1 + 1 from by norm_num]
  exact h0

end HJO.Sym
