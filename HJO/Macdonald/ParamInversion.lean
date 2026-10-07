/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.EigenbasisFamily
public import HJO.Macdonald.StandingFacts
public meta import HJO.Attr

/-! # The parameter inversions of the standing coefficient field

There are two substitutions on the coefficient field `𝕜 = ℚ(q, u)`, and the whole
starred half of the modified Macdonald theory is read through them:

* `ι` (`HJO.Sym.paramQUInv`) fixes `ℚ` and sends **both** parameters to their inverses,
  `q ↦ q⁻¹` and `u ↦ u⁻¹`;
* `υ` (`HJO.Sym.paramUInv`) fixes `ℚ` **and `q`** and sends only `u ↦ u⁻¹`.

They are two different maps, not one: `ι` inverts two parameters and `υ` one. The
difference is used: composing them at `HJO.Standing.inversion_macHtilde_param` gives the
endomorphism sending `q ↦ q⁻¹` and fixing `u`.

## Why this needs a field, and which one

Neither map exists over a general coefficient field: at `L = ℚ` and `u = 2` there is no element for
`u⁻¹`'s preimage to be, and indeed `2 ↦ 2⁻¹` extends to no ring endomorphism of `ℚ`. So an
argument over a general field `L` cannot construct them, and
`HJO/Macdonald/EigenbasisFamily.lean` accordingly carries `ι` as *hypothesised data* -- an
arbitrary `ι : L →+* L` with `ι q = q⁻¹`, `ι u = u⁻¹`, `ι ∘ ι = id` and `ι` fixing `ℚ` as four
hypotheses. **This file discharges those four at the standing field**, so that the hypotheses are
known to be satisfiable and are not an unsatisfiable-hypothesis risk.

The standing field is spelled as in `HJO/Ascent/Embedding.lean`: a field `K` presented as a
field of fractions of `ParamRing = ℚ[q, u] = MvPolynomial (Fin 2) ℚ`, whose two parameters are
`paramQ K` and `paramU K`. That module's `paramEmbedding` builds an injective `ℚ`-algebra map
`K → L` out of an algebraically independent pair in `L`; taking `L := K` and the pair
`(paramQ K, (paramU K)⁻¹)` -- or `((paramQ K)⁻¹, (paramU K)⁻¹)` -- turns the same machine into an
endomorphism of `K` inverting the parameters. The proof of `HJO.Debt.collinearCommutation_general`
says exactly this: the embedding of `HJO.Ascent.exists_paramEmbedding` is what lets the parameter
inversions be reached at any instance other than the standing one.

## The one thing that has to be proved

`paramEmbedding` consumes algebraic independence of the target pair over `ℤ`, so the inversions rest
on `algebraicIndependent_invCoords`: **inverting any set of coordinates of an algebraically
independent family in a field leaves it algebraically independent.** The proof is denominator
clearing made explicit. Given `P` vanishing at the inverted family, let `N` bound the exponents
occurring in `P` and reflect each exponent vector `d` to `i ↦ N - d i` on the inverted coordinates
(`reflExp`), giving a polynomial `reflPoly` whose value at the *original* family is
`(∏ x i ^ N) · 0 = 0`. Independence of the original family kills `reflPoly`, and reflection permutes
the coefficients injectively, so `P = 0`.

## From an embedding to an automorphism

`paramEmbedding` returns an injective homomorphism, not a bijection. What upgrades it is
`ringHom_ext_param`: a ring endomorphism of `K` is determined by its values at the two parameters,
because `K` is a localisation of `ParamRing` (`IsLocalization.ringHom_ext`) and a ring hom out of
`ParamRing = ℚ[q, u]` is determined by its values on `ℚ` and on the two indeterminates -- the values
on `ℚ` being forced, there being only one ring homomorphism `ℚ →+* K`. Each inversion composed with
itself fixes both parameters, hence is the identity, hence each inversion is an involution and so a
bijection. Both are therefore constructed as `K ≃ₐ[ℚ] K`, which records the fixing of `ℚ` in the
type.

## Main definitions

* `HJO.Sym.paramQUInv`: the inversion `ι`, the `ℚ`-algebra automorphism of `𝕜` with
  `ι q = q⁻¹` and `ι u = u⁻¹` (`HJO.Sym.paramQUInv`).
* `HJO.Sym.paramUInv`: the inversion `υ`, the `ℚ`-algebra automorphism of `𝕜` fixing `q` with
  `υ u = u⁻¹` (`HJO.Sym.paramUInv`).

## Main results

* `HJO.Ascent.algebraicIndependent_invCoords`: inverting coordinates preserves independence.
* `HJO.Ascent.ringHom_ext_param`: an endomorphism of `𝕜` is fixed by its values at `q` and `u`.
* `HJO.Sym.paramQUInv_involutive` and
  `HJO.Sym.paramUInv_involutive`: both inversions are involutions.
* `HJO.Standing.exists_isModifiedMacdonaldFamily_param`,
  `HJO.Standing.exists_isMacdonaldConjugator_param`: the reductions of
  `HJO/Macdonald/EigenbasisFamily.lean` with the four hypotheses on `ι` discharged, so the
  only hypothesis left standing is the existence of an eigenbasis with covering Pieri support.

## Implementation notes

The two inversions are built from one parametrised homomorphism `paramInvHom K s`, `s` the set of
coordinates to invert; `ι` is `s = univ` and `υ` is `s = {1}`. The exchange `τ` of the two
parameters (`HJO.Sym.paramSwap`) is *not* built here: it is not an instance of this construction,
being a permutation of the coordinates rather than an inversion of some of them, though the same
`paramEmbedding`-plus-`ringHom_ext_param` route reaches it from
`AlgebraicIndependent.comp` at the swap of `Fin 2`.

`ι` can also be built as the automorphism induced by negation on the exponent group of the Laurent
presentation `ℚ[q^{±1}, u^{±1}]` of the same field. That is the shorter construction, but it is
stated at a presentation of `𝕜` that this library does not carry, so nothing in the library
could consume it. This file builds `ι` at the presentation every statement about Macdonald
polynomials is written in.

## References

Definition `HJO.Sym.paramQUInv`, Lemma `HJO.Sym.paramQUInv_involutive` and Definition
`HJO.Sym.paramUInv`, as used in the proof of Proposition
`HJO.Debt.collinearCommutation_general`: there the parameter inversions are reachable only at the
standing instance and travel outward along `HJO.Ascent.exists_paramEmbedding`.
-/

@[expose] public section

open MvPolynomial

namespace HJO.Ascent

/-! ### Inverting coordinates preserves algebraic independence -/

section Reflection

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {L : Type*} [Field L]

/-- The family `x` with the coordinates indexed by `s` replaced by their inverses, the others left
alone. At `σ = Fin 2` and `s = {1}` this is `![q, u⁻¹]`, and at `s = univ` it is `![q⁻¹, u⁻¹]`. -/
def invCoords (s : Finset σ) (x : σ → L) : σ → L := fun i => if i ∈ s then (x i)⁻¹ else x i

/-- The reflection of an exponent vector in the window `N` along the coordinates in `s`: the
exponent `d i` becomes `N - d i` for `i ∈ s` and is kept for `i ∉ s`. This is the exponent
bookkeeping of denominator clearing: multiplying a monomial `x^d` by `∏_{i ∈ s} x i ^ N` after
inverting the coordinates in `s` produces the monomial with this exponent vector. -/
noncomputable def reflExp (s : Finset σ) (N : ℕ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => if i ∈ s then N - d i else d i

/-- The reflected exponent, coordinate by coordinate. -/
theorem reflExp_apply (s : Finset σ) (N : ℕ) (d : σ →₀ ℕ) (i : σ) :
    reflExp s N d i = if i ∈ s then N - d i else d i := rfl

/-- Reflection is injective on the exponent vectors the window `N` dominates: the truncated
subtraction `N - ·` does not truncate there, so it can be undone. -/
theorem reflExp_inj {s : Finset σ} {N : ℕ} {d e : σ →₀ ℕ} (hd : ∀ i ∈ s, d i ≤ N)
    (he : ∀ i ∈ s, e i ≤ N) (h : reflExp s N d = reflExp s N e) : d = e := by
  refine Finsupp.ext fun i => ?_
  have hi := congrArg (fun f => f i) h
  simp only [reflExp_apply] at hi
  by_cases his : i ∈ s
  · simp only [his, ite_true] at hi
    have := hd i his
    have := he i his
    omega
  · simpa [his] using hi

/-- The reflection of a polynomial in the window `N` along the coordinates in `s`: each monomial
keeps its coefficient and has its exponent vector reflected. -/
noncomputable def reflPoly (s : Finset σ) (N : ℕ) (P : MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  ∑ d ∈ P.support, monomial (reflExp s N d) (coeff d P)

/-- Reflection moves each coefficient of `P` to the reflected exponent and loses nothing, the
reflection being injective on the exponents `P` actually carries. -/
theorem coeff_reflPoly_reflExp {s : Finset σ} {N : ℕ} {P : MvPolynomial σ ℤ}
    (hN : ∀ d ∈ P.support, ∀ i ∈ s, d i ≤ N) {e : σ →₀ ℕ} (he : e ∈ P.support) :
    coeff (reflExp s N e) (reflPoly s N P) = coeff e P := by
  classical
  rw [reflPoly, coeff_sum, Finset.sum_eq_single e]
  · simp
  · intro d hd hde
    have hne : reflExp s N d ≠ reflExp s N e := fun h => hde (reflExp_inj (hN d hd) (hN e he) h)
    simp [coeff_monomial, hne]
  · intro h
    exact absurd he h

/-- Only the zero polynomial reflects to zero, within the window. -/
theorem eq_zero_of_reflPoly_eq_zero {s : Finset σ} {N : ℕ} {P : MvPolynomial σ ℤ}
    (hN : ∀ d ∈ P.support, ∀ i ∈ s, d i ≤ N) (h : reflPoly s N P = 0) : P = 0 := by
  by_contra hP
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hP
  have h2 := coeff_reflPoly_reflExp hN he
  rw [h, coeff_zero] at h2
  exact (Finsupp.mem_support_iff.mp he) h2.symm

/-- **Denominator clearing on one monomial.** Evaluating the reflected exponent vector at `x` is
evaluating the original one at the inverted family and multiplying by `∏_{i ∈ s} x i ^ N`. This is
where the inverted coordinates have to be nonzero and where the window has to dominate `d`. -/
theorem prod_pow_reflExp {s : Finset σ} {N : ℕ} {x : σ → L} (hx : ∀ i ∈ s, x i ≠ 0)
    {d : σ →₀ ℕ} (hd : ∀ i ∈ s, d i ≤ N) :
    (∏ i, x i ^ (reflExp s N d) i) = (∏ i ∈ s, x i ^ N) * ∏ i, invCoords s x i ^ d i := by
  have hsub : s ⊆ Finset.univ := Finset.subset_univ s
  rw [← Finset.prod_sdiff hsub (f := fun i => x i ^ (reflExp s N d) i),
    ← Finset.prod_sdiff hsub (f := fun i => invCoords s x i ^ d i)]
  have h1 : ∀ i ∈ Finset.univ \ s, x i ^ (reflExp s N d) i = invCoords s x i ^ d i := fun i hi => by
    simp [reflExp_apply, invCoords, (Finset.mem_sdiff.mp hi).2]
  rw [Finset.prod_congr rfl h1]
  have h2 : ∀ i ∈ s, x i ^ (reflExp s N d) i = x i ^ N * invCoords s x i ^ d i := fun i hi => by
    simp only [reflExp_apply, invCoords, hi, ite_true]
    rw [pow_sub₀ _ (hx i hi) (hd i hi), inv_pow]
  rw [Finset.prod_congr rfl h2, Finset.prod_mul_distrib]
  ring

omit [DecidableEq σ] in
/-- Evaluating a monomial, with the product taken over all of `σ` rather than over the support of
the exponent vector, which the zeroth power makes the same thing. -/
theorem aeval_monomial_prod_univ (x : σ → L) (d : σ →₀ ℕ) (c : ℤ) :
    aeval x (monomial d c) = ((c : ℤ) : L) * ∏ i, x i ^ d i := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ fun i => pow_zero (x i)]
  simp

omit [DecidableEq σ] in
/-- Evaluation as the sum over the support of the coefficient times the monomial's value. -/
theorem aeval_eq_sum_support (x : σ → L) (P : MvPolynomial σ ℤ) :
    aeval x P = ∑ d ∈ P.support, ((coeff d P : ℤ) : L) * ∏ i, x i ^ d i := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun d _ => aeval_monomial_prod_univ x d _

/-- **Denominator clearing.** The reflected polynomial evaluated at `x` is the original polynomial
evaluated at the inverted family, times the monomial `∏_{i ∈ s} x i ^ N` that cleared it. -/
theorem aeval_reflPoly {s : Finset σ} {N : ℕ} {x : σ → L} (hx : ∀ i ∈ s, x i ≠ 0)
    {P : MvPolynomial σ ℤ} (hN : ∀ d ∈ P.support, ∀ i ∈ s, d i ≤ N) :
    aeval x (reflPoly s N P) = (∏ i ∈ s, x i ^ N) * aeval (invCoords s x) P := by
  rw [reflPoly, map_sum, aeval_eq_sum_support, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aeval_monomial_prod_univ, prod_pow_reflExp hx (hN d hd)]
  ring

omit [Fintype σ] [DecidableEq σ] in
/-- No member of an algebraically independent family in a field is zero: the indeterminate is a
nonzero polynomial, so its value is not the value of `0`. -/
theorem ne_zero_of_algebraicIndependent {x : σ → L} (h : AlgebraicIndependent ℤ x) (i : σ) :
    x i ≠ 0 := by
  rw [algebraicIndependent_iff_injective_aeval] at h
  intro h0
  refine MvPolynomial.X_ne_zero i (h (a₂ := 0) ?_)
  simp [h0]

omit [Fintype σ] [DecidableEq σ] in
/-- The total degree is a window for every exponent vector a polynomial carries. -/
theorem exp_le_totalDegree {P : MvPolynomial σ ℤ} {d : σ →₀ ℕ} (hd : d ∈ P.support) (i : σ) :
    d i ≤ P.totalDegree := by
  classical
  have h1 : d i ≤ d.sum fun _ e => e := by
    by_cases h : i ∈ d.support
    · exact Finset.single_le_sum (f := fun j => d j) (fun _ _ => Nat.zero_le _) h
    · simp [Finsupp.notMem_support_iff.mp h]
  exact h1.trans (MvPolynomial.le_totalDegree hd)

end Reflection

/-- **Inverting coordinates preserves algebraic independence over `ℤ`.** If a finitely indexed
family `x` in a field satisfies no nonzero integer polynomial relation then neither does the family
obtained by inverting the coordinates indexed by `s`.

Given `P` vanishing at the inverted family, reflect it in the window `P.totalDegree`: the reflected
polynomial vanishes at `x` itself by `aeval_reflPoly`, hence is zero, hence `P` is zero --
reflection being injective on the exponents `P` carries. The two parameter
inversions rest on it, `paramEmbedding` needing algebraic independence of the pair it is to send the
parameters to. -/
@[hjo "lem_generic_inv_indep"]
theorem algebraicIndependent_invCoords {σ : Type*} [Finite σ] [DecidableEq σ] {L : Type*}
    [Field L] {x : σ → L} (h : AlgebraicIndependent ℤ x) (s : Finset σ) :
    AlgebraicIndependent ℤ (invCoords s x) := by
  have := Fintype.ofFinite σ
  have hx : ∀ i ∈ s, x i ≠ 0 := fun i _ => ne_zero_of_algebraicIndependent h i
  rw [algebraicIndependent_iff_injective_aeval] at h ⊢
  refine (injective_iff_map_eq_zero _).mpr fun P hP => ?_
  have hN : ∀ d ∈ P.support, ∀ i ∈ s, d i ≤ P.totalDegree :=
    fun d hd i _ => exp_le_totalDegree hd i
  refine eq_zero_of_reflPoly_eq_zero hN (h (a₂ := 0) ?_)
  rw [aeval_reflPoly hx hN, hP, mul_zero, map_zero]

/-! ### The inverted parameter pairs of the standing field -/

section InvertedParams

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

omit [IsFractionRing ParamRing K] in
/-- Inverting the second coordinate of the parameter pair gives the pair `(q, u⁻¹)` the inversion
`υ` of the second parameter is to be built from. -/
theorem invCoords_singleton_one_param :
    invCoords {1} ![paramQ K, paramU K] = ![paramQ K, (paramU K)⁻¹] := by
  funext i
  fin_cases i <;> simp [invCoords]

omit [IsFractionRing ParamRing K] in
/-- Inverting both coordinates of the parameter pair gives the pair `(q⁻¹, u⁻¹)` the inversion `ι`
of both parameters is to be built from. -/
theorem invCoords_univ_param :
    invCoords Finset.univ ![paramQ K, paramU K] = ![(paramQ K)⁻¹, (paramU K)⁻¹] := by
  funext i
  fin_cases i <;> simp [invCoords]

/-- **`(q, u⁻¹)` is algebraically independent over `ℤ`.** This is what makes the inversion of the
second parameter reachable through `paramEmbedding`. -/
theorem algebraicIndependent_param_invU :
    AlgebraicIndependent ℤ ![paramQ K, (paramU K)⁻¹] :=
  invCoords_singleton_one_param K ▸ algebraicIndependent_invCoords
    (algebraicIndependent_param K) {1}

/-- **`(q⁻¹, u⁻¹)` is algebraically independent over `ℤ`.** This is what makes the inversion of
both parameters reachable through `paramEmbedding`. -/
theorem algebraicIndependent_param_invQU :
    AlgebraicIndependent ℤ ![(paramQ K)⁻¹, (paramU K)⁻¹] :=
  invCoords_univ_param K ▸ algebraicIndependent_invCoords
    (algebraicIndependent_param K) Finset.univ

end InvertedParams

/-! ### An endomorphism of the standing field is fixed by its values at the two parameters -/

section Rigidity

variable {K : Type*} [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

omit [IsFractionRing ParamRing K] in
/-- Every ring endomorphism of the standing field fixes the rational constants: composing it with
the inclusion of `ℚ` gives a second ring homomorphism `ℚ →+* K`, and there is only one. -/
theorem ringHom_algebraMap_C_rat (φ : K →+* K) (r : ℚ) :
    φ (algebraMap ParamRing K (MvPolynomial.C r)) = algebraMap ParamRing K (MvPolynomial.C r) :=
  RingHom.congr_fun
    (Subsingleton.elim (φ.comp ((algebraMap ParamRing K).comp (MvPolynomial.C : ℚ →+* ParamRing)))
      ((algebraMap ParamRing K).comp (MvPolynomial.C : ℚ →+* ParamRing))) r

/-- **The standing field is rigid over its two parameters.** Two ring endomorphisms of `𝕜` that
agree at `q` and at `u` are equal.

This is the argument "`𝕜` is generated over `ℚ` by `q` and `u`, so a field endomorphism of `𝕜`
over `ℚ` is determined by its values at those two elements", carried out: a ring homomorphism out of
a localisation is determined by its restriction to the base (`IsLocalization.ringHom_ext`), and a
ring homomorphism out of `ℚ[q, u]` is determined by its values on the constants and on the two
indeterminates, the values on the constants being forced. -/
theorem ringHom_ext_param {φ ψ : K →+* K} (hq : φ (paramQ K) = ψ (paramQ K))
    (hu : φ (paramU K) = ψ (paramU K)) : φ = ψ := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors ParamRing) (MvPolynomial.ringHom_ext ?_ ?_)
  · intro r
    simpa using (ringHom_algebraMap_C_rat φ r).trans (ringHom_algebraMap_C_rat ψ r).symm
  · intro i
    fin_cases i
    · simpa [paramQ] using hq
    · simpa [paramU] using hu

/-- An endomorphism of the standing field fixing both parameters is the identity. -/
theorem ringHom_eq_id_of_param_fixed {φ : K →+* K} (hq : φ (paramQ K) = paramQ K)
    (hu : φ (paramU K) = paramU K) : φ = RingHom.id K :=
  ringHom_ext_param (ψ := RingHom.id K) hq hu

end Rigidity

/-! ### The parameter inversions as endomorphisms -/

section InversionHom

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- The inversion of the second parameter as a ring endomorphism of `𝕜`: the embedding of `𝕜` into
itself carrying `q` to `q` and `u` to `u⁻¹`. -/
noncomputable def paramUInvHom : K →+* K := paramEmbedding K (algebraicIndependent_param_invU K)

/-- The inversion of both parameters as a ring endomorphism of `𝕜`: the embedding of `𝕜` into
itself carrying `q` to `q⁻¹` and `u` to `u⁻¹`. -/
noncomputable def paramQUInvHom : K →+* K := paramEmbedding K (algebraicIndependent_param_invQU K)

@[simp]
theorem paramUInvHom_paramQ : paramUInvHom K (paramQ K) = paramQ K :=
  paramEmbedding_paramQ (algebraicIndependent_param_invU K)

@[simp]
theorem paramUInvHom_paramU : paramUInvHom K (paramU K) = (paramU K)⁻¹ :=
  paramEmbedding_paramU (algebraicIndependent_param_invU K)

@[simp]
theorem paramQUInvHom_paramQ : paramQUInvHom K (paramQ K) = (paramQ K)⁻¹ :=
  paramEmbedding_paramQ (algebraicIndependent_param_invQU K)

@[simp]
theorem paramQUInvHom_paramU : paramQUInvHom K (paramU K) = (paramU K)⁻¹ :=
  paramEmbedding_paramU (algebraicIndependent_param_invQU K)

/-- The inversion of the second parameter, composed with itself, is the identity: it fixes `q` and
sends `u` to `(u⁻¹)⁻¹ = u`, and the standing field is rigid over those two values. -/
theorem paramUInvHom_comp_self : (paramUInvHom K).comp (paramUInvHom K) = RingHom.id K := by
  refine ringHom_eq_id_of_param_fixed ?_ ?_ <;> simp [RingHom.comp_apply]

/-- The inversion of both parameters, composed with itself, is the identity, by the same rigidity:
both `q` and `u` come back to themselves. -/
theorem paramQUInvHom_comp_self : (paramQUInvHom K).comp (paramQUInvHom K) = RingHom.id K := by
  refine ringHom_eq_id_of_param_fixed ?_ ?_ <;> simp [RingHom.comp_apply]

/-- The inversion of the second parameter is an involution. -/
theorem paramUInvHom_involutive (c : K) : paramUInvHom K (paramUInvHom K c) = c :=
  RingHom.congr_fun (paramUInvHom_comp_self K) c

/-- The inversion of both parameters is an involution. -/
theorem paramQUInvHom_involutive (c : K) : paramQUInvHom K (paramQUInvHom K c) = c :=
  RingHom.congr_fun (paramQUInvHom_comp_self K) c

end InversionHom

end HJO.Ascent

/-! ### The two parameter inversions as automorphisms over `ℚ`

The inversions `ι` and `υ` are *automorphisms* fixing `ℚ`. Both facts are theorems: fixing `ℚ`
is `HJO.Ascent.ringHom_algebraMap_rat`, automatic for a ring homomorphism between fields of
characteristic zero, and bijectivity follows from each map being its own inverse.
-/

namespace HJO.Sym

open HJO.Ascent

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- **The inversion of the second parameter**, `υ`: the automorphism of the standing
coefficient field `𝕜 = ℚ(q, u)` over `ℚ` which fixes `q` and sends `u` to `u⁻¹`. It is the
substitution the sources print as `F[X; q, 1/u]` on the coefficients, and it is what the starred
eigenvalue and the inverted normalising product of Macdonald's polynomials are read through.

It is not `ι` inverts both parameters and this one inverts only the second. -/
@[hjo "def_mac_uinv_field"]
noncomputable def paramUInv : K ≃ₐ[ℚ] K :=
  AlgEquiv.ofAlgHom (toRatAlgHom (paramUInvHom K)) (toRatAlgHom (paramUInvHom K))
    (AlgHom.ext fun c => paramUInvHom_involutive K c)
    (AlgHom.ext fun c => paramUInvHom_involutive K c)

/-- **The inversion of both parameters**, `ι`: the automorphism of the standing
coefficient field `𝕜 = ℚ(q, u)` over `ℚ` which sends `q` to `q⁻¹` and `u` to `u⁻¹`. It is the
substitution the sources print inside a bracket, in `D_μ(1/q, 1/u)` and `B_μ(1/q, 1/u)`. -/
@[hjo "def_ght2_param_inv"]
noncomputable def paramQUInv : K ≃ₐ[ℚ] K :=
  AlgEquiv.ofAlgHom (toRatAlgHom (paramQUInvHom K)) (toRatAlgHom (paramQUInvHom K))
    (AlgHom.ext fun c => paramQUInvHom_involutive K c)
    (AlgHom.ext fun c => paramQUInvHom_involutive K c)

@[simp]
theorem paramUInv_apply (c : K) : paramUInv K c = paramUInvHom K c := rfl

@[simp]
theorem paramQUInv_apply (c : K) : paramQUInv K c = paramQUInvHom K c := rfl

/-- `υ` fixes the dinv parameter. -/
@[simp]
theorem paramUInv_paramQ : paramUInv K (paramQ K) = paramQ K := paramUInvHom_paramQ K

/-- `υ` inverts the area parameter. -/
@[simp]
theorem paramUInv_paramU : paramUInv K (paramU K) = (paramU K)⁻¹ := paramUInvHom_paramU K

/-- `ι` inverts the dinv parameter. -/
@[simp]
theorem paramQUInv_paramQ : paramQUInv K (paramQ K) = (paramQ K)⁻¹ := paramQUInvHom_paramQ K

/-- `ι` inverts the area parameter. -/
@[simp]
theorem paramQUInv_paramU : paramQUInv K (paramU K) = (paramU K)⁻¹ := paramQUInvHom_paramU K

/-- `υ` fixes `ℚ` pointwise, which for a map of `ℚ`-algebras is `AlgEquiv.commutes`. -/
theorem paramUInv_algebraMap_rat (r : ℚ) :
    paramUInv K (algebraMap ℚ K r) = algebraMap ℚ K r := (paramUInv K).commutes r

/-- `ι` fixes `ℚ` pointwise. -/
theorem paramQUInv_algebraMap_rat (r : ℚ) :
    paramQUInv K (algebraMap ℚ K r) = algebraMap ℚ K r := (paramQUInv K).commutes r

/-- **`υ` is an involution**: the composite fixes `q` and `u`, and the standing field is rigid over
those two values. -/
theorem paramUInv_involutive (c : K) : paramUInv K (paramUInv K c) = c :=
  paramUInvHom_involutive K c

/-- **`ι` is an involution.** This is `HJO.Sym.paramQUInv_involutive`, and its proof is the
standard one: `ι ∘ ι` is an endomorphism of `𝕜` over `ℚ` sending `q` to `(q⁻¹)⁻¹ = q` and `u` to
`u`, and `𝕜` is generated over `ℚ` by `q` and `u`, so it is the identity. -/
@[hjo "lem_ght2_param_inv_involutive"]
theorem paramQUInv_involutive (c : K) : paramQUInv K (paramQUInv K c) = c :=
  paramQUInvHom_involutive K c

end HJO.Sym

/-! ### The payoff: the hypothesised coefficient inversion of `EigenbasisFamily.lean`, discharged

`HJO/Macdonald/EigenbasisFamily.lean` runs over a general field `L` and therefore carries the
coefficient inversion as hypothesised data: a ring endomorphism `ι : L →+* L` together with
`ι q = q⁻¹`, `ι u = u⁻¹`, `∀ c, ι (ι c) = c` and `∀ r : ℚ, ι (algebraMap ℚ L r) = algebraMap ℚ L r`.
All four are now theorems at the standing field, for `HJO.Ascent.paramQUInvHom`, so the reductions
of that file hold there with nothing assumed about a coefficient inversion.
-/

namespace HJO.Standing

open HJO.Ascent HJO.Sym

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- **The four hypotheses `EigenbasisFamily.lean` makes on the coefficient inversion are
satisfiable**, and `HJO.Ascent.paramQUInvHom` satisfies them: it inverts both parameters, is an
involution, and fixes `ℚ`. This is what rules out the reading of that file's `ι` as an
unsatisfiable hypothesis. -/
theorem exists_coefficientInversion :
    ∃ ι : K →+* K, ι (paramQ K) = (paramQ K)⁻¹ ∧ ι (paramU K) = (paramU K)⁻¹ ∧
      (∀ c : K, ι (ι c) = c) ∧ ∀ r : ℚ, ι (algebraMap ℚ K r) = algebraMap ℚ K r :=
  ⟨paramQUInvHom K, paramQUInvHom_paramQ K, paramQUInvHom_paramU K, paramQUInvHom_involutive K,
    ringHom_algebraMap_rat (paramQUInvHom K)⟩

/-- **A modified Macdonald family exists at the standing field**, given a Macdonald eigenbasis for
the constructed coefficient inversion whose `e₁`-products have covering support.

This is `HJO.Sym.exists_isModifiedMacdonaldFamily` with every hypothesis but one discharged: the
nonvanishing of `q` and of `u` and the genericity of the pair come from this file's neighbours in
`HJO/Macdonald/StandingFacts.lean` -- genericity carries the nonvanishing of the parameter
product with it -- and the coefficient inversion with its four properties is
`HJO.Ascent.paramQUInvHom`. What remains is the existence hypothesis, which is
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_param` together with
`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`. -/
theorem exists_isModifiedMacdonaldFamily_param
    (hex : ∃ H : YoungDiagram → Lambda K,
      IsMacdonaldEigenbasis (paramQUInvHom K) (paramQ K) (paramU K) H ∧
      ∀ ν, elemSymm K 1 * H ν ∈
        Submodule.span K (H '' {μ : YoungDiagram | Covers μ ν})) :
    ∃ H : YoungDiagram → Lambda K, IsModifiedMacdonaldFamily (paramQ K) (paramU K) H :=
  HJO.Sym.exists_isModifiedMacdonaldFamily (paramQ_ne_zero K) (paramU_ne_zero K)
    (algebraicIndependent_param K) (paramQUInvHom K) (paramQUInvHom_paramQ K)
    (paramQUInvHom_paramU K) (paramQUInvHom_involutive K)
    (ringHom_algebraMap_rat (paramQUInvHom K)) hex

/-- **A Macdonald conjugator exists at the standing field**, given a Macdonald eigenbasis for the
constructed coefficient inversion with covering Pieri support. The whole collinear side assembled at
`𝕜`, with the parameter inversion no longer assumed. -/
theorem exists_isMacdonaldConjugator_param
    (hex : ∃ H : YoungDiagram → Lambda K,
      IsMacdonaldEigenbasis (paramQUInvHom K) (paramQ K) (paramU K) H ∧
      ∀ ν, elemSymm K 1 * H ν ∈
        Submodule.span K (H '' {μ : YoungDiagram | Covers μ ν})) :
    ∃ nabla : Module.End K (Lambda K), IsMacdonaldConjugator (paramQ K) (paramU K) nabla :=
  HJO.Sym.exists_isMacdonaldConjugator_of_exists_isMacdonaldEigenbasis (paramQ_ne_zero K)
    (paramU_ne_zero K) (algebraicIndependent_param K) (paramQUInvHom K) (paramQUInvHom_paramQ K)
    (paramQUInvHom_paramU K) (paramQUInvHom_involutive K)
    (ringHom_algebraMap_rat (paramQUInvHom K)) hex

end HJO.Standing
