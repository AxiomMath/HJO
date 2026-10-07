/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.PadStructure
public meta import HJO.Attr

/-! # The factors whose coefficients are scalars

Two of the four factors of BGLX's composite formula — the monomial `z^{-a}` and the expansion `Ω̂_k`
of the kernel factor — have all their coefficients in the base field rather than in `Λ`. For those
the displacement in the last variable does nothing but pad, since `δ` fixes the scalars, and that is
the observation recorded with `HJO.Bglx.shiftExtend`. To use it one needs to know that
the property survives the product, which is what this file supplies.

The property is recorded as a *pair* of conditions: the coefficients are scalars, and the support
lies in the hyperplane of exponents whose coordinates sum to `0`. The second is what makes such a
family degree-controlled with the bound `N = 0`, which is the hypothesis the displacement in the
last variable needs; it holds for the kernel expansion because each ray runs along `e_i - e_j`.

## Main definitions

* `HJO.Bglx.IsBalancedScalar`: scalar coefficients, supported on the coordinate-sum-zero exponents.

## Main statements

* `HJO.Bglx.IsBalancedScalar.mul`, `.one`, `.prod`: the property survives products.
* `HJO.Bglx.isBalancedScalar_kernelRay`, `HJO.Bglx.isBalancedScalar_kernelExpansion`: the expansion
  of the kernel factor has it.
* `HJO.Bglx.isDegreeControlled_of_isBalancedScalar`: such a family is degree-controlled.
* `HJO.Bglx.shiftExtendElem_of_isBalancedScalar`: on such a family the displacement in the last
  variable is the padding.
* `HJO.Bglx.shiftExtendElem_monoElem`: and on a monomial too — a monomial is not balanced, but its
  one nonzero coefficient is a scalar, so it is degree-controlled for a different reason.

## References

F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some
remarkable new plethystic operators in the theory of Macdonald polynomials*, arXiv:1405.0316v1,
J. Comb. **7** (2016) 671--714, Proposition 1.2.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {K : Type*} [CommRing K] {k : ℕ}

/-- A formal sum whose coefficients are scalars and whose support lies in the hyperplane of
exponents with coordinate sum `0`. -/
structure IsBalancedScalar (f : Family k (Lambda K)) : Prop where
  /-- every coefficient is a scalar -/
  scalar : ∀ α, ∃ a : K, f α = MvPolynomial.C a
  /-- the support lies in the coordinate-sum-zero hyperplane -/
  balanced : ∀ α, f α ≠ 0 → coordSum α = 0

lemma IsBalancedScalar.one (τ : Equiv.Perm (Fin k)) :
    IsBalancedScalar (1 : ConeRing k τ (Lambda K)).coeff where
  scalar α := by
    rw [ConeRing.coeff_one]
    by_cases h : α = 0
    · exact ⟨1, by rw [ite_eq_left h, map_one]⟩
    · exact ⟨0, by rw [ite_eq_right h, map_zero]⟩
  balanced α h := by
    rw [ConeRing.coeff_one] at h
    by_cases hα : α = 0
    · rw [hα, coordSum]
      simp
    · exact absurd (ite_eq_right hα) h

lemma IsBalancedScalar.mul {τ : Equiv.Perm (Fin k)} {x y : ConeRing k τ (Lambda K)}
    (hx : IsBalancedScalar x.coeff) (hy : IsBalancedScalar y.coeff) :
    IsBalancedScalar (x * y).coeff where
  scalar α := by
    classical
    rw [ConeRing.coeff_mul_of_subset x y α (ConeRing.finite_convSupport x y α).toFinset
      (by rw [Set.Finite.coe_toFinset])]
    refine ⟨∑ α' ∈ (ConeRing.finite_convSupport x y α).toFinset,
      (hx.scalar α').choose * (hy.scalar (α - α')).choose, ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun α' _ => ?_
    rw [map_mul, ← (hx.scalar α').choose_spec, ← (hy.scalar (α - α')).choose_spec]
  balanced α h := by
    classical
    rw [ConeRing.coeff_mul_of_subset x y α (ConeRing.finite_convSupport x y α).toFinset
      (by rw [Set.Finite.coe_toFinset])] at h
    obtain ⟨α', -, hα'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := hx.balanced α' (left_ne_zero_of_mul hα')
    have h2 := hy.balanced (α - α') (right_ne_zero_of_mul hα')
    rw [coordSum_sub] at h2
    omega

lemma IsBalancedScalar.prod {ι : Type*} {τ : Equiv.Perm (Fin k)} (s : Finset ι)
    (f : ι → ConeRing k τ (Lambda K)) (hf : ∀ i ∈ s, IsBalancedScalar (f i).coeff) :
    IsBalancedScalar (∏ i ∈ s, f i).coeff := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    exact IsBalancedScalar.one τ
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- **A balanced scalar family is degree-controlled**, with the bound `N = 0`: a scalar has degree
`0`, and the exponents carrying a nonzero coefficient have coordinate sum `0`. -/
theorem isDegreeControlled_of_isBalancedScalar [Algebra ℚ K] {f : Family k (Lambda K)}
    (hf : IsBalancedScalar f) : IsDegreeControlled f := by
  classical
  refine ⟨0, fun α e he => ?_⟩
  obtain ⟨a, ha⟩ := hf.scalar α
  have hne : f α ≠ 0 := by
    intro hc
    rw [hc] at he
    simp at he
  rw [hf.balanced α hne, add_zero]
  rw [ha, MvPolynomial.support_C] at he
  by_cases hazero : a = 0
  · rw [hazero, map_zero] at ha
    exact absurd ha hne
  · rw [ite_eq_right hazero, Finset.mem_singleton] at he
    rw [he]
    simp

/-! ### The two factors that have the property -/

@[simp] lemma coordSum_single (i : Fin k) (c : ℤ) : coordSum (Finsupp.single i c) = c := by
  have h : ∀ b ∈ (Finset.univ : Finset (Fin k)), b ≠ i → (Finsupp.single i c) b = 0 :=
    fun b _ hb => Finsupp.single_apply_eq_zero.2 fun hib => absurd hib hb
  rw [coordSum, Finset.sum_eq_single_of_mem i (Finset.mem_univ i) h, Finsupp.single_eq_same]

lemma coordSum_nsmul (α : Fin k →₀ ℤ) (n : ℕ) : coordSum (n • α) = n * coordSum α := by
  rw [coordSum, coordSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp

lemma coordSum_sub_single (i j : Fin k) :
    coordSum (Finsupp.single i (1 : ℤ) - Finsupp.single j 1) = 0 := by
  rw [coordSum_sub, coordSum_single, coordSum_single, sub_self]

/-- **The rays of the kernel expansion are balanced scalar families**: their coefficients are the
scalars `(-1)^s κ(e_s)` and they run along `e_i - e_j`, of coordinate sum `0`. -/
theorem isBalancedScalar_kernelRay [Algebra ℚ K] (q u : K) {i j : Fin k} (h : i < j) :
    IsBalancedScalar (kernelRay q u h).coeff where
  scalar α := by
    by_cases hα : ∃ s : ℕ, α = s • (Finsupp.single i (1 : ℤ) - Finsupp.single j 1)
    · obtain ⟨s, rfl⟩ := hα
      exact ⟨(-1) ^ s * paramPleth q u (elemSymm K s), by
        rw [kernelRay, coeff_rayHom_nsmul, coeff_kernelSeries]⟩
    · exact ⟨0, by
        rw [kernelRay, coeff_rayHom_of_forall_ne _ _ _ fun s hs => hα ⟨s, hs⟩, map_zero]⟩
  balanced α hne := by
    by_cases hα : ∃ s : ℕ, α = s • (Finsupp.single i (1 : ℤ) - Finsupp.single j 1)
    · obtain ⟨s, rfl⟩ := hα
      rw [coordSum_nsmul, coordSum_sub_single, mul_zero]
    · exact absurd (by
        rw [kernelRay, coeff_rayHom_of_forall_ne _ _ _ fun s hs => hα ⟨s, hs⟩]) hne

/-- **The expansion of the kernel factor is a balanced scalar family.** -/
theorem isBalancedScalar_kernelExpansion [Algebra ℚ K] (q u : K) (k : ℕ) :
    IsBalancedScalar (kernelExpansion q u k).coeff := by
  rw [kernelExpansion]
  refine IsBalancedScalar.prod _ _ fun i _ => IsBalancedScalar.prod _ _ fun j hj => ?_
  rw [kernelRayIf_of_lt q u (Finset.mem_Ioi.1 hj)]
  exact isBalancedScalar_kernelRay q u (Finset.mem_Ioi.1 hj)

/-! ### The displacement on such a family is the padding -/

/-- **On a balanced scalar family the displacement in the last variable is the padding**, the
displacement fixing the scalars. -/
theorem shiftExtendElem_of_isBalancedScalar [Algebra ℚ K] (q u : K) (x : ConeRing k 1 (Lambda K))
    (hx : IsBalancedScalar x.coeff) :
    shiftExtendElem q u x (isDegreeControlled_of_isBalancedScalar hx) = padElem x :=
  ConeRing.ext (shiftExtend_eq_padFamily q u x.coeff hx.scalar)

/-- A monomial is degree-controlled: its one nonzero coefficient is a scalar. -/
theorem isDegreeControlled_monoElem [Algebra ℚ K] (β : Fin k →₀ ℤ) :
    IsDegreeControlled (monoElem 1 β : ConeRing k 1 (Lambda K)).coeff := by
  classical
  refine ⟨-coordSum β, fun α => ?_⟩
  by_cases hα : α = β
  · rw [coeff_monoElem, ite_eq_left hα, hα, neg_add_cancel]
    exact DegLEZ_one
  · rw [coeff_monoElem, ite_eq_right hα]
    exact DegLEZ_zero

/-- **On a monomial the displacement in the last variable is the padding.** -/
theorem shiftExtendElem_monoElem [Algebra ℚ K] (q u : K) (β : Fin k →₀ ℤ) :
    shiftExtendElem q u (monoElem 1 β) (isDegreeControlled_monoElem β)
      = padElem (monoElem 1 β) := by
  refine ConeRing.ext (shiftExtend_eq_padFamily q u _ fun α => ?_)
  classical
  rw [coeff_monoElem]
  by_cases hα : α = β
  · exact ⟨1, by rw [ite_eq_left hα, map_one]⟩
  · exact ⟨0, by rw [ite_eq_right hα, map_zero]⟩

end HJO.Bglx
