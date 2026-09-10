/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.Multiplication

/-! # The evaluation map is an algebra homomorphism

The evaluation map is the composition of three multiplicative steps. Scaling the alphabet by
`(-1) ^ (b + 1)` multiplies the weighted homogeneous component of degree `N` by
`(-1) ^ (N * (b + 1))`, so the sign carried by the evaluation map is the effect of an algebra
endomorphism of the ring of symmetric functions and needs no homogeneity to be multiplicative.
Applying the operator attached to a symmetric function to `1` is multiplicative once the
coefficients are specialised, because a specialisation sending the parameter to `1` kills every
term of positive index in the expansion of an operator of the order filtration and leaves a
multiplication operator. Specialising the coefficients and extracting the sign are ring
homomorphisms.

The parameter is sent to `1` only in the image of the specialisation, never in the base field:
the normalised commutators defining the slope operators divide by `(1 - q) (1 - u)`, so imposing
`u = 1` in the base field would collapse every slope operator of first index at least `2` to
zero, and with it the operators a slope homomorphism is required to hit.

No result of this library uses the map built here: over a field the hypothesis `spec u = 1` is
degenerate, as `phi_isUnitalAlgHom` records. The evaluation map everything else is stated for is
`HJO.PhiMul.phiReg`, which carries the specialisation on a coefficient ring mapping into the base
field.
-/

@[expose] public section

open Finset

namespace HJO.PhiHom

open MvPolynomial HJO.Sym HJO.Multiplication HJO.UkRegular HJO.ReesSpecial

/-! ### Scaling the alphabet as a twist of the weighted grading -/

section Twist

variable {K : Type*} [CommRing K]

/-- The weighted degree of a monomial, the generator of index `i` weighing `i + 1`, written as a
sum over the support of the exponent vector. -/
lemma weight_eq_sum_support (d : ℕ →₀ ℕ) :
    Finsupp.weight (fun i => i + 1) d = ∑ i ∈ d.support, (i + 1) * d i := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]

/-- Scaling the alphabet by `c` multiplies the weighted homogeneous component of degree `N` by
`c ^ N`, the components above the weighted total degree contributing nothing. -/
lemma plethScale_eq_sum_component (c : K) (f : Lambda K) :
    plethScale c f = ∑ N ∈ range (weightedTotalDegree (fun i => i + 1) f + 1),
      C (c ^ N) * weightedHomogeneousComponent (fun i => i + 1) N f := by
  classical
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_plethScale, coeff_sum, ← weight_eq_sum_support]
  by_cases hf : coeff d f = 0
  · rw [hf, mul_zero]
    refine (Finset.sum_eq_zero fun N _ => ?_).symm
    rw [coeff_C_mul, coeff_weightedHomogeneousComponent, hf]
    simp
  · have hmem : Finsupp.weight (fun i => i + 1) d ∈
        range (weightedTotalDegree (fun i => i + 1) f + 1) := by
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact le_weightedTotalDegree _ (MvPolynomial.mem_support_iff.mpr hf)
    rw [Finset.sum_eq_single_of_mem _ hmem]
    · rw [coeff_C_mul, coeff_weightedHomogeneousComponent, ite_eq_left rfl]
    · intro N _ hN
      rw [coeff_C_mul, coeff_weightedHomogeneousComponent, ite_eq_right (Ne.symm hN), mul_zero]

end Twist

/-! ### The unsigned part of the evaluation map -/

section EvalOne

variable {L : Type*} [Field L] {F : Type*} [CommRing F]

/-- Sign extraction sends a constant symmetric function to itself. -/
lemma signExtract_C (x : F) : signExtract F (C x : Lambda F) = x := by
  simp [signExtract]

/-- Under a specialisation sending the parameter to `1`, an operator of the order filtration
becomes multiplication by the specialisation of its own value on `1`: the terms of positive index
in its expansion in `1 - u` are killed, and the constant term is a multiplication operator. -/
lemma map_apply_eq_of_mem_rees {u : L} (spec : L →+* F) (hspec : spec u = 1)
    {P : Module.End L (Lambda L)} (hP : P ∈ Rees u) (g : Lambda L) :
    MvPolynomial.map spec (P g) = MvPolynomial.map spec (P 1) * MvPolynomial.map spec g := by
  obtain ⟨Q, hQord, hQsum⟩ := hP
  obtain ⟨h, hh⟩ := exists_mulLeft_of_hasDiffOrderAtMost_zero (hQord 0)
  have hcoefs : ∀ i : ℕ, spec ((1 - u) ^ (i + 1)) = 0 := fun i => by
    rw [map_pow, map_sub, map_one, hspec, sub_self, zero_pow (Nat.succ_ne_zero i)]
  have key : ∀ f : Lambda L,
      MvPolynomial.map spec (P f) = MvPolynomial.map spec h * MvPolynomial.map spec f := by
    intro f
    obtain ⟨N, hN, hPf⟩ := hQsum f
    have hterm : ∀ i : ℕ,
        MvPolynomial.map spec (((1 - u) ^ (i + 1)) • Q (i + 1) f) = 0 := fun i => by
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hcoefs i, map_zero, zero_mul]
    have h0 : MvPolynomial.map spec (P f) = MvPolynomial.map spec (Q 0 f) := by
      rcases N with _ | M
      · rw [hPf, Finset.range_zero, Finset.sum_empty, map_zero, hN 0 le_rfl, map_zero]
      · rw [hPf, Finset.sum_range_succ', map_add, map_sum,
          Finset.sum_eq_zero fun i _ => hterm i, zero_add, pow_zero, one_smul]
    rw [h0, hh, LinearMap.mulLeft_apply, map_mul]
  rw [key g, key 1, map_one (MvPolynomial.map spec), mul_one]

/-- The unsigned part of the evaluation map: the value on `1` of the operator attached to `f`,
with its coefficients specialised by `spec` and its sign extracted. -/
noncomputable def evalOne (spec : L →+* F) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L))
    (f : Lambda L) : F :=
  signExtract F (MvPolynomial.map spec (Θ f 1))

variable (spec : L →+* F) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L))

/-- The unsigned part of the evaluation map vanishes on `0`. -/
@[simp] lemma evalOne_zero : evalOne spec Θ 0 = 0 := by
  rw [evalOne, map_zero, LinearMap.zero_apply, map_zero, map_zero]

/-- The unsigned part of the evaluation map is additive. -/
lemma evalOne_add (f g : Lambda L) :
    evalOne spec Θ (f + g) = evalOne spec Θ f + evalOne spec Θ g := by
  rw [evalOne, evalOne, evalOne, map_add, LinearMap.add_apply, map_add, map_add]

/-- The unsigned part of the evaluation map commutes with finite sums. -/
lemma evalOne_sum {ι : Type*} (t : Finset ι) (g : ι → Lambda L) :
    evalOne spec Θ (∑ i ∈ t, g i) = ∑ i ∈ t, evalOne spec Θ (g i) := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih => rw [Finset.sum_cons, evalOne_add, ih, Finset.sum_cons]

/-- The unsigned part of the evaluation map takes `1` to `1`. -/
@[simp] lemma evalOne_one : evalOne spec Θ 1 = 1 := by
  have h : Θ (1 : Lambda L) 1 = (1 : Lambda L) := by
    rw [map_one Θ]
    exact Module.End.one_apply _
  rw [evalOne, h, map_one (MvPolynomial.map spec), map_one (signExtract F)]

/-- Scalars are pulled out of the unsigned part of the evaluation map through `spec`. -/
lemma evalOne_smul (c : L) (f : Lambda L) :
    evalOne spec Θ (c • f) = spec c * evalOne spec Θ f := by
  rw [evalOne, evalOne, map_smul, LinearMap.smul_apply, MvPolynomial.smul_eq_C_mul,
    map_mul, MvPolynomial.map_C, map_mul, signExtract_C]

/-- Constants are pulled out of the unsigned part of the evaluation map through `spec`. -/
lemma evalOne_C_mul (c : L) (f : Lambda L) :
    evalOne spec Θ (C c * f) = spec c * evalOne spec Θ f := by
  rw [← MvPolynomial.smul_eq_C_mul, evalOne_smul]

section Slope

variable [Algebra ℚ L]

/-- The unsigned part of the evaluation map is multiplicative for a slope homomorphism whose
parameter the specialisation sends to `1`: the operator attached to a product is the composite of
the two operators, and after specialisation the outer one is multiplication by its value on
`1`. -/
lemma evalOne_mul {a b : ℕ} {q u : L} (hspec : spec u = 1) (hv0 : q * u ≠ 0)
    (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1) (hΘ : IsSlopeHom a b q u Θ) (f g : Lambda L) :
    evalOne spec Θ (f * g) = evalOne spec Θ f * evalOne spec Θ g := by
  rw [evalOne, evalOne, evalOne, map_mul, Module.End.mul_apply,
    map_apply_eq_of_mem_rees spec hspec (mem_rees_of_isSlopeHom hv0 hv1 hΘ f) (Θ g 1), map_mul]

end Slope

end EvalOne

/-! ### The evaluation map -/

section Phi

variable {L : Type*} [Field L] {F : Type*} [CommRing F]
  (b : ℕ) (spec : L →+* F) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L))

/-- The evaluation map is the unsigned part precomposed with the scaling of the alphabet by
`(-1) ^ (b + 1)`: that scaling multiplies the component of degree `N` by `(-1) ^ (N * (b + 1))`,
which is exactly the sign the evaluation map carries there. -/
lemma phi_eq_evalOne_plethScale (f : Lambda L) :
    Phi b spec Θ f = evalOne spec Θ (plethScale ((-1 : L) ^ (b + 1)) f) := by
  have hsign : ∀ N : ℕ, spec (((-1 : L) ^ (b + 1)) ^ N) = (-1 : F) ^ (N * (b + 1)) := by
    intro N
    rw [← pow_mul, mul_comm (b + 1) N, map_pow, map_neg, map_one]
  rw [plethScale_eq_sum_component, evalOne_sum, Phi]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [evalOne_C_mul, hsign N, evalOne]

/-- The evaluation map is additive. -/
lemma phi_add (f g : Lambda L) : Phi b spec Θ (f + g) = Phi b spec Θ f + Phi b spec Θ g := by
  rw [phi_eq_evalOne_plethScale, phi_eq_evalOne_plethScale, phi_eq_evalOne_plethScale, map_add,
    evalOne_add]

/-- The evaluation map vanishes on `0`. -/
@[simp] lemma phi_zero : Phi b spec Θ 0 = 0 := by
  rw [phi_eq_evalOne_plethScale, map_zero, evalOne_zero]

/-- The evaluation map is unital. -/
@[simp] lemma phi_one : Phi b spec Θ 1 = 1 := by
  rw [phi_eq_evalOne_plethScale, map_one, evalOne_one]

/-- Scalars are pulled out of the evaluation map through `spec`. -/
lemma phi_C_mul (c : L) (f : Lambda L) :
    Phi b spec Θ (C c * f) = spec c * Phi b spec Θ f := by
  rw [← MvPolynomial.smul_eq_C_mul, phi_eq_evalOne_plethScale, phi_eq_evalOne_plethScale,
    map_smul, evalOne_smul]

section Slope

variable [Algebra ℚ L]

/-- The evaluation map is multiplicative for a slope homomorphism whose parameter the
specialisation sends to `1`. The sign needs no homogeneity hypothesis: it is the effect of an
algebra endomorphism of the ring of symmetric functions, namely the scaling of the alphabet by
`(-1) ^ (b + 1)`. -/
lemma phi_mul {a : ℕ} {q u : L} (hspec : spec u = 1) (hv0 : q * u ≠ 0)
    (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1) (hΘ : IsSlopeHom a b q u Θ) (f g : Lambda L) :
    Phi b spec Θ (f * g) = Phi b spec Θ f * Phi b spec Θ g := by
  rw [phi_eq_evalOne_plethScale, phi_eq_evalOne_plethScale, phi_eq_evalOne_plethScale, map_mul,
    evalOne_mul spec Θ hspec hv0 hv1 hΘ]

/-- The evaluation map attached to a slope homomorphism whose parameter the specialisation sends
to `1`, bundled as a ring homomorphism from the ring of symmetric functions to the target of the
specialisation. -/
noncomputable def phiRingHom {a : ℕ} {q u : L} (hspec : spec u = 1) (hv0 : q * u ≠ 0)
    (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1) (hΘ : IsSlopeHom a b q u Θ) : Lambda L →+* F where
  toFun := Phi b spec Θ
  map_one' := phi_one b spec Θ
  map_mul' := phi_mul b spec Θ hspec hv0 hv1 hΘ
  map_zero' := phi_zero b spec Θ
  map_add' := phi_add b spec Θ

/-- The bundled evaluation map is the evaluation map. -/
@[simp] lemma phiRingHom_apply {a : ℕ} {q u : L} (hspec : spec u = 1) (hv0 : q * u ≠ 0)
    (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1) (hΘ : IsSlopeHom a b q u Θ) (f : Lambda L) :
    phiRingHom b spec Θ hspec hv0 hv1 hΘ f = Phi b spec Θ f := rfl

/-- For a slope homomorphism at `(a, b)` whose parameter the specialisation sends to `1`, the
evaluation map is a unital algebra homomorphism on the whole ring of symmetric functions: it takes
`1` to `1`, it is additive and multiplicative, and it is semilinear over the specialisation of the
scalars.

Over a field the hypothesis is degenerate: `spec u = 1` forces `u = 1`
(`Multiplication.eq_one_of_map_eq_one`), and at `u = 1` the normalisation `((1 - q) * (1 - u))⁻¹`
is zero, so every slope operator of first index at least two vanishes and `Θ` collapses to a
scalar multiple of the identity. The nondegenerate form of the statement carries the
specialisation on operators whose expansion coefficients are regular at `u = 1`, over the local
coefficient ring of `HJO.ReesRegular` rather than over a field. -/
theorem phi_isUnitalAlgHom {a : ℕ} {q u : L} (hspec : spec u = 1) (hv0 : q * u ≠ 0)
    (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1) (hΘ : IsSlopeHom a b q u Θ) :
    Phi b spec Θ 1 = 1 ∧
      (∀ f g : Lambda L, Phi b spec Θ (f + g) = Phi b spec Θ f + Phi b spec Θ g) ∧
      (∀ f g : Lambda L, Phi b spec Θ (f * g) = Phi b spec Θ f * Phi b spec Θ g) ∧
      (∀ (c : L) (f : Lambda L), Phi b spec Θ (C c * f) = spec c * Phi b spec Θ f) :=
  ⟨phi_one b spec Θ, phi_add b spec Θ, phi_mul b spec Θ hspec hv0 hv1 hΘ,
    phi_C_mul b spec Θ⟩

end Slope

end Phi

end HJO.PhiHom
