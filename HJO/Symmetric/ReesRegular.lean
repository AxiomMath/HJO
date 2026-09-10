/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.ReesClosed

/-! # Symmetric functions over a coefficient ring, and the specialisation setting

The base field `L` (to be read as `ℚ(q, u)`) admits no ring homomorphism sending `u` to `1`
unless the target is the zero ring, because `u - 1` is invertible there. The setting of this
file is the one in which such a specialisation does exist: a coefficient ring `R` mapping into
`L` -- to be read as the elements of `ℚ(q, u)` regular at `u = 1`, which form a local ring, not
a field -- together with a ring homomorphism `sp : R →+* F` sending `u` to `1`, whose kernel
contains `1 - u` and is therefore nonzero.

This file supplies the coefficientwise inclusion `coeffInc` of the symmetric functions over `R`
into those over `L`, its image `regSub`, and the compatibilities of both with the partial
derivations. It then fixes the specialisation itself: no ring homomorphism out of `L` can send
`u` to `1` without collapsing its target, which is why the specialisation is taken on `R`.

A model section instantiates the setting with `R = ℚ[u] ⊂ L = ℚ(u)` and `sp` evaluation at
`u = 1`, and exhibits there an operator that is not a multiplication operator, so neither the
hypotheses nor the conclusion are vacuous. A final section bounds the reach of the filtration:
the total derivation sending every generator to `1` has no differential order at all.

The order filtration used by the development is `HJO.DiffOrder.ReesRegComm`, which tracks the
coefficient ring through the commutator filtration.
-/

@[expose] public section

open Finset

namespace HJO.ReesRegular

open HJO.Sym HJO.ReesClosed

/-! ### Symmetric functions with coefficients in the coefficient ring -/

section Inclusion

variable (R : Type*) [CommRing R] (L : Type*) [CommRing L] [Algebra R L]

/-- The coefficientwise inclusion of the symmetric functions over the coefficient ring `R` into
the symmetric functions over `L`, an `R`-algebra homomorphism. -/
noncomputable def coeffInc : Lambda R →ₐ[R] Lambda L :=
  MvPolynomial.mapAlgHom (Algebra.ofId R L)

/-- The coefficientwise inclusion applies the structure map to every coefficient. -/
theorem coeffInc_apply (f : Lambda R) : coeffInc R L f = MvPolynomial.map (algebraMap R L) f := rfl

/-- The symmetric functions whose coefficients come from `R`, as an `R`-submodule of the
symmetric functions over `L`. -/
noncomputable def regSub : Submodule R (Lambda L) := LinearMap.range (coeffInc R L).toLinearMap

variable {R L}

/-- Membership in the image of the coefficientwise inclusion. -/
theorem mem_regSub {x : Lambda L} : x ∈ regSub R L ↔ ∃ g : Lambda R, coeffInc R L g = x :=
  LinearMap.mem_range

/-- Symmetric functions over `R` have coefficients in `R`. -/
theorem coeffInc_mem_regSub (f : Lambda R) : coeffInc R L f ∈ regSub R L :=
  mem_regSub.mpr ⟨f, rfl⟩

/-- The coefficientwise inclusion is injective as soon as the structure map is. -/
theorem coeffInc_injective (hinj : Function.Injective (algebraMap R L)) :
    Function.Injective (coeffInc R L) := MvPolynomial.map_injective _ hinj

/-- Scaling by an element of `R` is scaling by its image in `L`. -/
theorem algebraMap_smul_eq (r : R) (x : Lambda L) : (algebraMap R L r) • x = r • x :=
  algebraMap_smul L r x

/-- Partial derivatives are defined over the coefficient ring. -/
theorem pderiv_coeffInc (i : ℕ) (f : Lambda R) :
    MvPolynomial.pderiv i (coeffInc R L f) = coeffInc R L (MvPolynomial.pderiv i f) := by
  simp [coeffInc_apply, MvPolynomial.pderiv_map]

end Inclusion

/-! ### The differential-order filtration over the coefficient ring -/

section DiffOrderReg

variable (R : Type*) [CommRing R] (L : Type*) [CommRing L] [Algebra R L]

variable {R L}

end DiffOrderReg

/-! ### The order filtration over the coefficient ring -/

section ReesReg

variable (R : Type*) [CommRing R] (L : Type*) [Field L] [Algebra R L]

variable {R L}

end ReesReg

/-! ### The specialisation -/

section Specialisation

variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L]
  {F : Type*} [CommRing F]

end Specialisation

/-! ### The filtration over the coefficient ring is closed under normalised commutators -/

section CommutatorOrder

variable {R : Type*} [CommRing R] {L : Type*} [CommRing L] [Algebra R L]

end CommutatorOrder

section ReesRegClosed

variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L]

end ReesRegClosed

/-! ### A non-degenerate instance

Everything above is stated for a coefficient ring mapping into the base field. This section
supplies one: the polynomials in `u` over `ℚ` inside the rational functions in `u` over `ℚ`,
with the specialisation being evaluation at `u = 1`. There the specialisation sends `u` to `1`
while `u` itself is not `1`, so the hypotheses do not collapse; the base field admits no such
homomorphism at all; and the filtration over the coefficient ring contains an operator that is
not a multiplication operator, so the specialisation statement is not an identity.
-/

namespace Model

/-- The coefficient ring of the model instance: the polynomials in `u` over `ℚ`. -/
abbrev Coeff : Type := Polynomial ℚ

/-- The base field of the model instance: the rational functions in `u` over `ℚ`. -/
abbrev Base : Type := RatFunc ℚ

/-- The parameter `u` of the model instance, the variable itself. -/
noncomputable def u : Coeff := Polynomial.X

/-- The specialisation of the model instance: evaluation of a polynomial at `u = 1`. -/
noncomputable def sp : Coeff →+* ℚ := Polynomial.evalRingHom 1

/-- The structure map of the model instance is injective. -/
theorem algebraMap_injective : Function.Injective (algebraMap Coeff Base) :=
  RatFunc.algebraMap_injective ℚ

/-- The specialisation sends the parameter to `1`. -/
@[simp] theorem sp_u : sp u = 1 := by simp [sp, u]

/-- The parameter is not `1`: the specialisation has a nonzero kernel, so sending `u` to `1` does
not force `u = 1`. -/
theorem u_ne_one : u ≠ 1 := by
  intro h
  have hcoeff := congrArg (fun p : Coeff => Polynomial.coeff p 0) h
  simp [u] at hcoeff

/-- The parameter is not `1` in the base field either. -/
theorem algebraMap_u_ne_one : algebraMap Coeff Base u ≠ 1 := by
  intro h
  exact u_ne_one (algebraMap_injective (by rw [h, map_one]))

/-- The deformation parameter `ℏ = 1 - u` is nonzero in the base field, so the filtration is not
the filtration at a point where `u` already equals `1`. -/
theorem one_sub_algebraMap_u_ne_zero : (1 : Base) - algebraMap Coeff Base u ≠ 0 := fun h =>
  algebraMap_u_ne_one (eq_of_sub_eq_zero h).symm

/-- The base field admits no specialisation: a ring homomorphism out of it sending `u` to `1`
forces the target to be the zero ring, since `u - 1` is invertible there. This is why the
specialisation has to be taken on the coefficient ring. -/
theorem eq_zero_of_ringHom_eq_one {F : Type*} [CommRing F] (spec : Base →+* F)
    (h : spec (algebraMap Coeff Base u) = 1) : (1 : F) = 0 := by
  have hne : algebraMap Coeff Base u - 1 ≠ 0 := fun hzero =>
    algebraMap_u_ne_one (eq_of_sub_eq_zero hzero)
  have hspec : spec (algebraMap Coeff Base u - 1) = 0 := by rw [map_sub, h, map_one, sub_self]
  calc (1 : F)
      = spec ((algebraMap Coeff Base u - 1) * (algebraMap Coeff Base u - 1)⁻¹) := by
        rw [mul_inv_cancel₀ hne, map_one]
    _ = 0 := by rw [map_mul, hspec, zero_mul]

/-- A model operator: multiplication by a symmetric function with polynomial coefficients plus
`ℏ` times one partial derivative. -/
noncomputable def op (g : Lambda Coeff) : Module.End Base (Lambda Base) :=
  LinearMap.mulLeft Base (coeffInc Coeff Base g)
    + (1 - algebraMap Coeff Base u) • pderivEnd Base 0

/-- The expansion coefficients of the model operator: multiplication by `g` in degree zero, a
single partial derivative in degree one, and zero beyond. -/
noncomputable def opCoeff (g : Lambda Coeff) : ℕ → Module.End Base (Lambda Base)
  | 0 => LinearMap.mulLeft Base (coeffInc Coeff Base g)
  | 1 => pderivEnd Base 0
  | _ + 2 => 0

/-- The model operator is not a multiplication operator: its value on the first power sum sees the
partial derivative, whose coefficient `1 - u` is nonzero in the base field. So the filtration over
the coefficient ring is strictly larger than the multiplication operators, and the specialisation
statement is not an identity. -/
theorem op_ne_mulLeft (g : Lambda Coeff) (h : Lambda Base) :
    op g ≠ LinearMap.mulLeft Base h := by
  intro hop
  have hval : ∀ f : Lambda Base, coeffInc Coeff Base g * f
      + (1 - algebraMap Coeff Base u) • MvPolynomial.pderiv 0 f = h * f := by
    intro f
    have := congrArg (fun P : Module.End Base (Lambda Base) => P f) hop
    simpa [op, pderivEnd] using this
  have h1 : h = coeffInc Coeff Base g := by
    have := hval 1
    simpa using this.symm
  have h2 := hval (MvPolynomial.X 0)
  rw [h1, MvPolynomial.pderiv_X_self, add_eq_left] at h2
  rcases smul_eq_zero.mp h2 with hz | hz
  · exact one_sub_algebraMap_u_ne_zero hz
  · exact one_ne_zero hz

/-- Non-degeneracy of the model instance: the specialisation sends the parameter to `1` in a
nontrivial target while the parameter differs from `1` both in the coefficient ring and in the base
field, so the deformation parameter `ℏ = 1 - u` does not vanish. -/
theorem nondegenerate : Nontrivial ℚ ∧ sp u = 1 ∧ u ≠ 1 ∧ algebraMap Coeff Base u ≠ 1 ∧
    (1 : Base) - algebraMap Coeff Base u ≠ 0 :=
  ⟨inferInstance, sp_u, u_ne_one, algebraMap_u_ne_one, one_sub_algebraMap_u_ne_zero⟩

end Model

/-! ### The reach of the differential-order filtration

The differential order of `HasDiffOrderAtMost` is membership in a span of products of a
multiplication operator with finitely many partial derivatives, so each of its elements involves
only finitely many of the generators. That is a genuine restriction, and this section measures it:
the derivation sending every generator `p_k` to `1` -- an operator of first order in the sense of
Grothendieck, its commutator with any two multiplication operators vanishing -- has no
differential order in the span sense at all. Consequently an operator presented as a locally
finite sum `∑ᵢ cᵢ ∂ / ∂pᵢ` over all the generators, such as the coefficient of `ℏ` in the
expansion of a basic operator graded by the number of derivatives, is outside the filtration
however small its true order.
-/

section Reach

variable (K : Type*) [CommRing K]

/-- The derivation of the ring of symmetric functions sending every generator `p_k` to `1`, that
is the sum of all the partial derivatives, taken as a single operator. -/
noncomputable def totalDeriv : Module.End K (Lambda K) :=
  (MvPolynomial.mkDerivation K fun _ : ℕ => (1 : Lambda K)).toLinearMap

variable {K}

/-- The commutator of the total derivation with a multiplication operator is multiplication by the
total derivative of the multiplier: the Leibniz rule. -/
theorem totalDeriv_commutator (g : Lambda K) :
    totalDeriv K * LinearMap.mulLeft K g - LinearMap.mulLeft K g * totalDeriv K
      = LinearMap.mulLeft K (totalDeriv K g) := by
  refine LinearMap.ext fun x => ?_
  have hleib := (MvPolynomial.mkDerivation K fun _ : ℕ => (1 : Lambda K)).leibniz g x
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply, totalDeriv,
    Derivation.coeFn_coe]
  rw [hleib]
  simp only [smul_eq_mul]
  ring

/-- The total derivation moves multiplication by a generator: its commutator there is the
identity. -/
theorem totalDeriv_commutator_X (j : ℕ) :
    totalDeriv K * LinearMap.mulLeft K (MvPolynomial.X j)
        - LinearMap.mulLeft K (MvPolynomial.X j) * totalDeriv K = 1 := by
  rw [totalDeriv_commutator]
  have hX : totalDeriv K (MvPolynomial.X j) = 1 := by
    simp [totalDeriv, MvPolynomial.mkDerivation_X]
  rw [hX]
  exact LinearMap.ext fun x => by simp

/-- Every operator of differential order at most `n` commutes with multiplication by all but
finitely many of the generators, namely all those absent from its derivatives. -/
theorem exists_finset_commute_of_hasDiffOrderAtMost {n : ℕ} {P : Module.End K (Lambda K)}
    (hP : HasDiffOrderAtMost n P) :
    ∃ S : Finset ℕ, ∀ j ∉ S, Commute P (LinearMap.mulLeft K (MvPolynomial.X j)) := by
  have hpderiv : ∀ (l : List ℕ) (j : ℕ), j ∉ l →
      Commute (pderivProd K l) (LinearMap.mulLeft K (MvPolynomial.X j)) := by
    intro l j hj
    induction l with
    | nil => simp [Commute, SemiconjBy]
    | cons i t ih =>
      have hij : i ≠ j := fun h => hj (by simp [h])
      have hi : Commute (pderivEnd K i) (LinearMap.mulLeft K (MvPolynomial.X j)) := by
        have h := pderivEnd_mul_mulLeft (K := K) i (MvPolynomial.X j)
        rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij)] at h
        simpa [Commute, SemiconjBy] using h
      rw [pderivProd_cons]
      exact hi.mul_left (ih fun h => hj (by simp [h]))
  refine Submodule.span_induction
    (p := fun Q _ => ∃ S : Finset ℕ, ∀ j ∉ S,
      Commute Q (LinearMap.mulLeft K (MvPolynomial.X j))) ?_ ⟨∅, fun j _ => by simp⟩ ?_ ?_ hP
  · rintro Q ⟨f, l, -, rfl⟩
    refine ⟨l.toFinset, fun j hj => ?_⟩
    have hf : Commute (LinearMap.mulLeft K f) (LinearMap.mulLeft K (MvPolynomial.X j)) := by
      have h : LinearMap.mulLeft K f * LinearMap.mulLeft K (MvPolynomial.X j)
          = LinearMap.mulLeft K (MvPolynomial.X j) * LinearMap.mulLeft K f :=
        LinearMap.ext fun x => by simp [mul_left_comm]
      exact h
    exact hf.mul_left (hpderiv l j (by simpa using hj))
  · rintro P₁ P₂ - - ⟨S₁, h₁⟩ ⟨S₂, h₂⟩
    refine ⟨S₁ ∪ S₂, fun j hj => ?_⟩
    rw [Finset.mem_union, not_or] at hj
    exact (h₁ j hj.1).add_left (h₂ j hj.2)
  · rintro a P - ⟨S, h⟩
    exact ⟨S, fun j hj => (h j hj).smul_left a⟩

/-- The total derivation has no differential order in the span sense: it fails to commute with
multiplication by every single generator, while an operator of differential order at most `n`
commutes with all but finitely many of them. -/
theorem not_hasDiffOrderAtMost_totalDeriv [Nontrivial K] (n : ℕ) :
    ¬ HasDiffOrderAtMost n (totalDeriv K) := by
  intro hP
  obtain ⟨S, hS⟩ := exists_finset_commute_of_hasDiffOrderAtMost hP
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset S
  have hcomm := hS j hj
  have hone : (1 : Module.End K (Lambda K)) = 0 := by
    rw [← totalDeriv_commutator_X (K := K) j, hcomm, sub_self]
  have := congrArg (fun P : Module.End K (Lambda K) => P 1) hone
  simp at this

end Reach

end HJO.ReesRegular
