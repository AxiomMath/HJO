/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.KernelExpansion
public meta import HJO.Attr

/-! # The exponential factor as a product over the variables

The exponential factor `E_k = ∑_{r ∈ ℕ^k} (-1)^{r_1+⋯+r_k} e_{r_1}⋯e_{r_k} z^r` of
`HJO/Collinear/KernelExpansion.lean` is defined by its coefficients, which is its
displayed form. BGLX write it instead as the product `∏_{i=1}^k ∑_{r ≥ 0} (-z_i)^r e_r` of one
one-variable series per variable, and that is what this file proves: each factor is the image of
`HJO.Bglx.expSeries` under the ray homomorphism of `HJO/Collinear/RaySeries.lean` at the
exponent `e_i`, and the product of the `k` factors is `E_k`.

The product form is what a computation in the last variable needs. A ring homomorphism out of the
cone ring — or a displacement of one variable — may be applied factor by factor to a product, and
cannot be applied at all to a coefficient family given by a formula.

## Main statements

* `HJO.Bglx.single_one_mem_cone` and `HJO.Bglx.single_one_ne_zero`: the two hypotheses that make
  `e_i` the base of a ray, so that a power series may be read along it.
* `HJO.Bglx.coeff_expRay`: the coefficients of one variable's factor along its own ray.
* `HJO.Bglx.coeff_prod_expRay`: the coefficients of a partial product, over a finset `s` of
  variables, at an exponent supported in `s`.
* `HJO.Bglx.coeff_prod_expRay_of_exists`: the same partial product vanishes at an exponent that is
  nonzero at a variable outside `s`.
* `HJO.Bglx.expAlphabet_eq_prod`: **the exponential factor is the product of the one-variable
  factors.**

## Implementation notes

**The partial product is computed over a finset of variables, by induction on it.** The statement
`coeff_prod_expRay` needs the hypothesis that the exponent vanishes outside `s`, and the induction
step needs the *converse* direction as well — that the partial product vanishes when it does not.
Rather than pack the two into one equation with an `if` over `∀ i ∉ s, α i = 0` (which would need a
`Decidable` instance for that quantifier), the two directions are two lemmas:
`coeff_prod_expRay_of_exists` is proved first, by its own induction on `s`, and
`coeff_prod_expRay` then uses it through `forall_eq_zero_of_coeff_prod_expRay_ne_zero`.

**Only one exponent contributes to the convolution at each step.** Multiplying the factor of the
variable `a` into the partial product over `s'`, the pairs contributing to the coefficient at `α`
are cut down to the single exponent `e_a α_a`: the first factor is supported on the ray of `e_a`,
which gives `α' = a ↦ n` for some `n : ℕ`, and the second factor vanishes unless `α - α'` is
supported in `s'`, which at `a ∉ s'` forces `n = α_a`. So `ConeRing.coeff_mul_of_subset` is applied
to a singleton and the convolution is a single product of two coefficients, one read off
`coeff_expRay` and one off the inductive hypothesis.

## References

The reference for the definition `HJO.Bglx.expAlphabet` is
F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the
theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, whose
Proposition 1.2 writes the exponential factor as the product `∏_i ∑_{r ≥ 0} (-z_i)^r e_r` over the
variables.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {K : Type*} [CommRing K] [Algebra ℚ K] {k : ℕ} {τ : Equiv.Perm (Fin k)}

/-! ### The ray of a single variable -/

/-- The exponent `e_i` lies in every cone: it is nonnegative, and every nonnegative exponent has
nonnegative partial sums along every ordering. -/
theorem single_one_mem_cone (τ : Equiv.Perm (Fin k)) (i : Fin k) :
    Finsupp.single i (1 : ℤ) ∈ cone τ :=
  mem_cone_of_nonneg (Finsupp.single_nonneg.2 zero_le_one)

/-- The exponent `e_i` is nonzero, so it is the base of a ray of the cone. -/
theorem single_one_ne_zero (i : Fin k) : Finsupp.single i (1 : ℤ) ≠ 0 :=
  Finsupp.single_ne_zero.2 one_ne_zero

/-- A nonnegative multiple of `e_i` is `e_i` scaled: `n • e_i` is the exponent `i ↦ n`. -/
theorem nsmul_single_one (i : Fin k) (n : ℕ) :
    n • Finsupp.single i (1 : ℤ) = Finsupp.single i (n : ℤ) := by
  rw [Finsupp.smul_single, nsmul_eq_mul, mul_one]

/-! ### One variable's factor -/

/-- **One variable's factor of the exponential factor**: the ray `∑_{r ≥ 0} (-z_i)^r e_r` along the
exponent `e_i`, the one-variable series `expSeries` read along that ray. -/
noncomputable def expRay (K : Type*) [CommRing K] [Algebra ℚ K] (τ : Equiv.Perm (Fin k))
    (i : Fin k) : ConeRing k τ (Lambda K) :=
  rayHom τ (Finsupp.single i 1) (single_one_mem_cone τ i) (single_one_ne_zero i) (expSeries K)

/-- **The coefficients of one variable's factor along its ray**: at the exponent `c e_i` it is
`(-1)^c e_c` for `c ≥ 0` and `0` for `c < 0`, the ray being indexed by the natural numbers. -/
theorem coeff_expRay (i : Fin k) (c : ℤ) :
    (expRay K τ i).coeff (Finsupp.single i c)
      = if 0 ≤ c then (-1) ^ c.toNat * elemSymm K c.toNat else 0 := by
  by_cases hc : 0 ≤ c
  · rw [← Int.toNat_of_nonneg hc, ← nsmul_single_one i c.toNat, expRay, coeff_rayHom_nsmul,
      coeff_expSeries, Int.toNat_natCast, ite_eq_left (by simp)]
  · rw [expRay, ite_eq_right hc]
    refine coeff_rayHom_of_forall_ne _ _ _ fun n hn => hc ?_
    have h := congrArg (fun β : Fin k →₀ ℤ => β i) hn
    rw [nsmul_single_one] at h
    simp only [Finsupp.single_eq_same] at h
    exact h.symm.le.trans' (Int.natCast_nonneg n)

/-- An exponent carrying a nonzero coefficient of one variable's factor is a nonnegative multiple
of `e_i`. -/
theorem exists_natCast_of_coeff_expRay_ne_zero (i : Fin k) {α : Fin k →₀ ℤ}
    (h : (expRay K τ i).coeff α ≠ 0) : ∃ n : ℕ, α = Finsupp.single i (n : ℤ) := by
  by_contra hex
  refine h (coeff_rayHom_of_forall_ne _ _ _ fun n hn => ?_)
  exact hex ⟨n, by rw [hn, nsmul_single_one]⟩

/-- An exponent carrying a nonzero coefficient of one variable's factor is concentrated at `i`. -/
theorem eq_single_of_coeff_expRay_ne_zero (i : Fin k) {α : Fin k →₀ ℤ}
    (h : (expRay K τ i).coeff α ≠ 0) : α = Finsupp.single i (α i) := by
  obtain ⟨n, rfl⟩ := exists_natCast_of_coeff_expRay_ne_zero i h
  rw [Finsupp.single_eq_same]

/-! ### The product over a finset of variables -/

/-- **A partial product of the one-variable factors vanishes off the variables it involves**: the
product over `s` has coefficient `0` at any exponent that is nonzero at some variable outside
`s`. -/
theorem coeff_prod_expRay_of_exists :
    ∀ (s : Finset (Fin k)) (α : Fin k →₀ ℤ), (∃ i ∉ s, α i ≠ 0) →
      (∏ i ∈ s, expRay K τ i).coeff α = 0 := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    rintro α ⟨i, -, hi⟩
    rw [Finset.prod_empty, ConeRing.coeff_one, ite_eq_right fun h => hi (by rw [h]; rfl)]
  | insert a s' ha ih =>
    rintro α ⟨j, hj, hj0⟩
    have hja : j ≠ a := fun h => hj (by rw [h]; exact Finset.mem_insert_self a s')
    have hjs : j ∉ s' := fun h => hj (Finset.mem_insert_of_mem h)
    have hsub : ConeRing.convSupport (expRay K τ a) (∏ i ∈ s', expRay K τ i) α
        ⊆ ↑(∅ : Finset (Fin k →₀ ℤ)) := by
      rintro α' ⟨h1, h2⟩
      obtain ⟨n, rfl⟩ := exists_natCast_of_coeff_expRay_ne_zero a h1
      refine absurd (ih _ ⟨j, hjs, ?_⟩) h2
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hja, sub_zero]
      exact hj0
    rw [Finset.prod_insert ha, ConeRing.coeff_mul_of_subset _ _ α _ hsub, Finset.sum_empty]

/-- A nonzero coefficient of a partial product forces the exponent to be supported in the variables
the product involves. -/
theorem forall_eq_zero_of_coeff_prod_expRay_ne_zero (s : Finset (Fin k)) (α : Fin k →₀ ℤ)
    (h : (∏ i ∈ s, expRay K τ i).coeff α ≠ 0) {i : Fin k} (hi : i ∉ s) : α i = 0 := by
  by_contra hne
  exact h (coeff_prod_expRay_of_exists s α ⟨i, hi, hne⟩)

/-- **The coefficients of a partial product of the one-variable factors**: at an exponent supported
in `s`, the coefficient is the product over `s` of the per-variable coefficients of the exponential
factor. At `s = univ` this is the defining coefficient family of `expAlphabet`. -/
theorem coeff_prod_expRay :
    ∀ (s : Finset (Fin k)) (α : Fin k →₀ ℤ), (∀ i ∉ s, α i = 0) →
      (∏ i ∈ s, expRay K τ i).coeff α
        = ∏ i ∈ s, (if 0 ≤ α i then (-1) ^ (α i).toNat * elemSymm K (α i).toNat else 0) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro α hα
    rw [Finset.prod_empty, ConeRing.coeff_one, Finset.prod_empty,
      ite_eq_left (Finsupp.ext fun i => hα i (Finset.notMem_empty i))]
  | insert a s' ha ih =>
    intro α hα
    have hβ : ∀ i ∉ s', (α - Finsupp.single a (α a)) i = 0 := by
      intro i hi
      rw [Finsupp.sub_apply]
      by_cases h : i = a
      · rw [h, Finsupp.single_eq_same, sub_self]
      · rw [Finsupp.single_eq_of_ne h, sub_zero]
        exact hα i fun hmem => (Finset.mem_insert.1 hmem).elim h hi
    have hsub : ConeRing.convSupport (expRay K τ a) (∏ i ∈ s', expRay K τ i) α
        ⊆ ↑({Finsupp.single a (α a)} : Finset (Fin k →₀ ℤ)) := by
      rintro α' ⟨h1, h2⟩
      have h3 := eq_single_of_coeff_expRay_ne_zero a h1
      have h4 : α a - α' a = 0 := by
        rw [← Finsupp.sub_apply]
        exact forall_eq_zero_of_coeff_prod_expRay_ne_zero s' _ h2 ha
      rw [Finset.mem_coe, Finset.mem_singleton, h3, sub_eq_zero.1 h4]
    have key : (∏ i ∈ s', expRay K τ i).coeff (α - Finsupp.single a (α a))
        = ∏ i ∈ s', (if 0 ≤ α i then (-1) ^ (α i).toNat * elemSymm K (α i).toNat else 0) := by
      rw [ih _ hβ]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne (fun h : i = a => ha (h ▸ hi)), sub_zero]
    rw [Finset.prod_insert ha, ConeRing.coeff_mul_of_subset _ _ α _ hsub, Finset.sum_singleton,
      coeff_expRay, key, Finset.prod_insert ha]

/-- **The exponential factor is the product of the one-variable factors.** This is BGLX's form
`∏_{i=1}^k ∑_{r ≥ 0} (-z_i)^r e_r` of `E_k`, the factor of the variable `i` being the exponential
series read along the ray of `e_i`. -/
theorem expAlphabet_eq_prod (K : Type*) [CommRing K] [Algebra ℚ K] (k : ℕ)
    (τ : Equiv.Perm (Fin k)) : expAlphabet K k τ = ∏ i : Fin k, expRay K τ i :=
  ConeRing.ext (funext fun α => by
    rw [coeff_prod_expRay Finset.univ α fun i hi => absurd (Finset.mem_univ i) hi,
      coeff_expAlphabet])

end HJO.Bglx
