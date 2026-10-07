/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.ConeGraded
public import HJO.Collinear.ExpAlphabetProd
public meta import HJO.Attr

/-! # Padding is a ring homomorphism, and the three factors split off their last variable

BGLX's composite formula is proved by induction on the number of variables, and the induction step
compares the four factors in `k+1` variables with the four in `k` variables padded with a last
variable. Two things are needed for that and are supplied here.

First, **padding is a ring homomorphism** `R^{id}_k → R^{id}_{k+1}`: the convolution of two padded
families is the padding of the convolution, only the pair of zero last coordinates contributing.
This is the multiplicativity read off `HJO.Bglx.padFamily`.

Second, **each of the three parameter-free factors splits**: the exponential factor, the expansion
of the kernel factor and a monomial in `k+1` variables are each the padding of their `k`-variable
version times the part involving the last variable,

* `E_{k+1} = E_k · ∑_{r ≥ 0} (-z_{k+1})^r e_r`,
* `Ω̂_{k+1} = Ω̂_k · ∏_{i ≤ k} ∑_{s ≥ 0} (-1)^s κ(e_s) z^{s(e_i - e_{k+1})}`,
* `z^{(β, n)} = z^β · z_{k+1}^n`,

the first factor on each right-hand side being the padding.

## Main definitions

* `HJO.Bglx.padElem`: the padding of `HJO.Bglx.padFamily` as an element of the cone ring.

## Main statements

* `HJO.Bglx.padElem_mul`, `HJO.Bglx.padElem_one`: padding is a ring homomorphism.
* `HJO.Bglx.coeff_padElem_rayHom`: the padding of a ray is the ray at the padded exponent.
* `HJO.Bglx.expAlphabet_succ`, `HJO.Bglx.kernelExpansion_succ`, `HJO.Bglx.monoElem_snocExp`: the
  three splittings.

## Implementation notes

The splittings are proved from the *product* descriptions of the two factors — `expAlphabet_eq_prod`
for the exponential factor and the definition for the kernel expansion — by splitting the index set
of the product: `Finset.univ` on `Fin (k+1)` is the image of `Fin.castSucc` with `Fin.last k`
adjoined, and `Finset.Ioi (Fin.castSucc i)` is the image of `Finset.Ioi i` with `Fin.last k`
adjoined. What makes the padded part come out as a padding is `coeff_padElem_rayHom`: a ray along
`b` in `k` variables pads to the ray along `(b, 0)`.

## References

The reference for the definition `HJO.Bglx.padFamily` and for the induction step of
`HJO.Bglx.dopComp_eq_ct`, which is where all four splittings are used, is F. Bergeron,
A. M. Garsia, E. Leven and G. Xin,
*Some remarkable new plethystic operators in the theory of Macdonald polynomials*,
arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, Proposition 1.2.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {K : Type*} [CommRing K] {k : ℕ}

/-! ### Two small facts about monomials -/

/-- Multiplying two monomials adds their exponents. -/
lemma monoElem_mul_monoElem {R : Type*} [CommRing R] (τ : Equiv.Perm (Fin k))
    (β γ : Fin k →₀ ℤ) :
    (monoElem τ β : ConeRing k τ R) * monoElem τ γ = monoElem τ (β + γ) := by
  refine ConeRing.ext (funext fun α => ?_)
  rw [coeff_monoElem_mul, monoMul_apply, coeff_monoElem, coeff_monoElem]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · rw [← h]; abel
  · rw [h]; abel

/-- The exponent `-a` of the monomial `z_1^{-a_1} ⋯ z_k^{-a_k}` attached to a word. -/
noncomputable def negExp (a : Fin k → ℕ) : Fin k →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm fun i => -(a i : ℤ)

@[simp] lemma negExp_apply (a : Fin k → ℕ) (i : Fin k) : negExp a i = -(a i : ℤ) := by
  simp [negExp]

/-! ### Padding as a ring homomorphism -/

lemma snocExp_nsmul (b : Fin k →₀ ℤ) (n : ℕ) : n • snocExp b 0 = snocExp (n • b) 0 := by
  induction n with
  | zero =>
    refine Finsupp.ext fun i => ?_
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp
  | succ m ih =>
    rw [succ_nsmul, ih, succ_nsmul, ← snocExp_add, add_zero]

lemma snocExp_injective : Function.Injective fun α : Fin k →₀ ℤ => snocExp α 0 :=
  fun α β h => by simpa using congrArg initExp h


/-- The padding of a cone-bounded formal sum, as an element of the cone ring in one more
variable. -/
noncomputable def padElem (x : ConeRing k 1 (Lambda K)) : ConeRing (k + 1) 1 (Lambda K) where
  coeff := padFamily x.coeff
  isConeBounded := isConeBounded_padFamily x.isConeBounded

@[simp] lemma coeff_padElem (x : ConeRing k 1 (Lambda K)) (γ : Fin (k + 1) →₀ ℤ) :
    (padElem x).coeff γ = if lastExp γ = 0 then x.coeff (initExp γ) else 0 := rfl

lemma coeff_padElem_snocExp (x : ConeRing k 1 (Lambda K)) (α : Fin k →₀ ℤ) :
    (padElem x).coeff (snocExp α 0) = x.coeff α := by
  rw [coeff_padElem, lastExp_snocExp, ite_eq_left rfl, initExp_snocExp]

lemma coeff_padElem_of_ne (x : ConeRing k 1 (Lambda K)) {γ : Fin (k + 1) →₀ ℤ}
    (h : lastExp γ ≠ 0) : (padElem x).coeff γ = 0 := by
  rw [coeff_padElem, ite_eq_right h]

/-- **Padding preserves the product.** Only the pair of zero last coordinates contributes to the
convolution, and what is left is the convolution in `k` variables. -/
theorem padElem_mul (x y : ConeRing k 1 (Lambda K)) :
    padElem (x * y) = padElem x * padElem y := by
  classical
  refine ConeRing.ext (funext fun γ => ?_)
  by_cases hγ : lastExp γ = 0
  · obtain ⟨α, rfl⟩ : ∃ α, γ = snocExp α 0 := ⟨initExp γ, by rw [← hγ, snocExp_initExp]⟩
    set s : Finset (Fin k →₀ ℤ) := (ConeRing.finite_convSupport x y α).toFinset with hs
    have hsub : ConeRing.convSupport (padElem x) (padElem y) (snocExp α 0)
        ⊆ ↑(s.image fun α' => snocExp α' 0) := by
      rintro γ' ⟨h1, h2⟩
      have hl1 : lastExp γ' = 0 := by
        by_contra hc
        exact h1 (coeff_padElem_of_ne x hc)
      have hl2 : lastExp (snocExp α 0 - γ') = 0 := by
        by_contra hc
        exact h2 (coeff_padElem_of_ne y hc)
      have hγ' : γ' = snocExp (initExp γ') 0 := by rw [← hl1, snocExp_initExp]
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨initExp γ', ?_, hγ'.symm⟩
      rw [hs, Set.Finite.mem_toFinset]
      refine ⟨?_, ?_⟩
      · rw [coeff_padElem, ite_eq_left hl1] at h1
        exact h1
      · rw [coeff_padElem, ite_eq_left hl2] at h2
        rw [show α - initExp γ' = initExp (snocExp α 0 - γ') by
          rw [initExp_sub, initExp_snocExp]]
        exact h2
    rw [coeff_padElem_snocExp, ConeRing.coeff_mul_of_subset _ _ _ _ hsub,
      ConeRing.coeff_mul_of_subset x y α s (by rw [hs, Set.Finite.coe_toFinset])]
    rw [Finset.sum_image fun a _ b _ h => snocExp_injective h]
    refine Finset.sum_congr rfl fun α' _ => ?_
    rw [coeff_padElem_snocExp, coeff_padElem, initExp_sub, lastExp_sub, lastExp_snocExp,
      lastExp_snocExp, sub_zero, ite_eq_left rfl, initExp_snocExp, initExp_snocExp]
  · rw [coeff_padElem_of_ne _ hγ]
    refine ((ConeRing.coeff_mul_of_subset (padElem x) (padElem y) γ
      (∅ : Finset (Fin (k + 1) →₀ ℤ)) ?_).trans Finset.sum_empty).symm
    rintro γ' ⟨h1, h2⟩
    have hl1 : lastExp γ' = 0 := by
      by_contra hc
      exact h1 (coeff_padElem_of_ne x hc)
    have hl2 : lastExp (γ - γ') = 0 := by
      by_contra hc
      exact h2 (coeff_padElem_of_ne y hc)
    rw [lastExp_sub, hl1, sub_zero] at hl2
    exact absurd hl2 hγ

@[simp] theorem padElem_one : padElem (1 : ConeRing k 1 (Lambda K)) = 1 := by
  refine ConeRing.ext (funext fun γ => ?_)
  rw [coeff_padElem, ConeRing.coeff_one, ConeRing.coeff_one]
  by_cases hγ : lastExp γ = 0
  · rw [ite_eq_left hγ]
    refine if_congr ?_ rfl rfl
    constructor
    · intro h
      refine Finsupp.ext fun i => ?_
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa using congrArg (fun f : Fin k →₀ ℤ => f j) h
      · simpa [lastExp] using hγ
    · intro h
      rw [h]
      exact Finsupp.ext fun i => by simp
  · rw [ite_eq_right hγ, ite_eq_right]
    intro h
    rw [h] at hγ
    exact absurd rfl hγ

theorem padElem_prod {ι : Type*} (s : Finset ι) (f : ι → ConeRing k 1 (Lambda K)) :
    padElem (∏ i ∈ s, f i) = ∏ i ∈ s, padElem (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, padElem_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, padElem_mul, ih]

/-! ### Padding a ray -/

/-- The exponent `e_i` of `k` variables pads to the exponent `e_i` of `k+1` variables. -/
lemma snocExp_single_one (i : Fin k) :
    snocExp (Finsupp.single i (1 : ℤ)) 0 = Finsupp.single i.castSucc 1 := by
  refine Finsupp.ext fun j => ?_
  rcases Fin.eq_castSucc_or_eq_last j with ⟨l, rfl⟩ | rfl
  · rw [snocExp_castSucc, Finsupp.single_apply, Finsupp.single_apply]
    exact if_congr (by simp [Fin.castSucc_inj]) rfl rfl
  · rw [snocExp_last, Finsupp.single_apply, ite_eq_right]
    intro h
    exact absurd h (Fin.castSucc_lt_last i).ne

/-- The exponent `e_i - e_j` of `k` variables pads to `e_i - e_j` of `k+1` variables. -/
lemma snocExp_single_sub_single (i j : Fin k) :
    snocExp (Finsupp.single i (1 : ℤ) - Finsupp.single j 1) 0
      = Finsupp.single i.castSucc (1 : ℤ) - Finsupp.single j.castSucc 1 := by
  refine Finsupp.ext fun j => ?_
  rcases Fin.eq_castSucc_or_eq_last j with ⟨l, rfl⟩ | rfl
  · rw [snocExp_castSucc, Finsupp.sub_apply, Finsupp.sub_apply, ← snocExp_single_one,
      ← snocExp_single_one, snocExp_castSucc, snocExp_castSucc]
  · rw [snocExp_last, Finsupp.sub_apply, ← snocExp_single_one, ← snocExp_single_one,
      snocExp_last, snocExp_last, sub_zero]

/-- **The padding of a ray is the ray at the padded exponent.** -/
theorem padElem_rayHom {b : Fin k →₀ ℤ} (hb : b ∈ cone (1 : Equiv.Perm (Fin k))) (hb0 : b ≠ 0)
    {b' : Fin (k + 1) →₀ ℤ} (hb' : b' ∈ cone (1 : Equiv.Perm (Fin (k + 1)))) (hb0' : b' ≠ 0)
    (hbb' : b' = snocExp b 0) (s : PowerSeries (Lambda K)) :
    padElem (rayHom 1 b hb hb0 s) = rayHom 1 b' hb' hb0' s := by
  subst hbb'
  refine ConeRing.ext (funext fun γ => ?_)
  by_cases hγ : lastExp γ = 0
  · obtain ⟨α, rfl⟩ : ∃ α, γ = snocExp α 0 := ⟨initExp γ, by rw [← hγ, snocExp_initExp]⟩
    rw [coeff_padElem_snocExp]
    by_cases hα : ∃ n : ℕ, α = n • b
    · obtain ⟨n, rfl⟩ := hα
      rw [coeff_rayHom_nsmul, ← snocExp_nsmul, coeff_rayHom_nsmul]
    · rw [coeff_rayHom_of_forall_ne hb hb0 s (fun n h => hα ⟨n, h⟩),
        coeff_rayHom_of_forall_ne hb' hb0' s]
      intro n h
      refine hα ⟨n, ?_⟩
      have h' : snocExp α 0 = snocExp (n • b) 0 := by rw [h, snocExp_nsmul]
      simpa using congrArg initExp h'
  · rw [coeff_padElem_of_ne _ hγ, coeff_rayHom_of_forall_ne hb' hb0' s]
    intro n h
    refine hγ ?_
    rw [h, snocExp_nsmul, lastExp_snocExp]

/-! ### The three splittings -/

section Splittings

variable [Algebra ℚ K]

/-- The padding of the factor of one variable is the factor of the same variable. -/
theorem padElem_expRay (i : Fin k) :
    padElem (expRay K 1 i) = expRay K 1 i.castSucc :=
  padElem_rayHom _ _ (single_one_mem_cone 1 i.castSucc) (single_one_ne_zero i.castSucc)
    (snocExp_single_one i).symm _

/-- **The exponential factor splits off its last variable.** -/
theorem expAlphabet_succ (K : Type*) [CommRing K] [Algebra ℚ K] (k : ℕ) :
    expAlphabet K (k + 1) 1 = padElem (expAlphabet K k 1) * expRay K 1 (Fin.last k) := by
  rw [expAlphabet_eq_prod, expAlphabet_eq_prod, padElem_prod, Fin.prod_univ_castSucc]
  congr 1
  exact (Finset.prod_congr rfl fun i _ => padElem_expRay i).symm

omit [Algebra ℚ K] in
/-- The padding of a monomial is the monomial at the padded exponent. -/
theorem padElem_monoElem (β : Fin k →₀ ℤ) :
    padElem (monoElem 1 β : ConeRing k 1 (Lambda K)) = monoElem 1 (snocExp β 0) := by
  refine ConeRing.ext (funext fun γ => ?_)
  by_cases hγ : lastExp γ = 0
  · obtain ⟨α, rfl⟩ : ∃ α, γ = snocExp α 0 := ⟨initExp γ, by rw [← hγ, snocExp_initExp]⟩
    rw [coeff_padElem_snocExp, coeff_monoElem, coeff_monoElem]
    exact if_congr ⟨fun h => by rw [h], fun h => snocExp_injective h⟩ rfl rfl
  · rw [coeff_padElem_of_ne _ hγ, coeff_monoElem]
    refine (ite_eq_right ?_).symm
    intro h
    rw [h, lastExp_snocExp] at hγ
    exact absurd rfl hγ

omit [Algebra ℚ K] in
lemma snocExp_add_single_last (β : Fin k →₀ ℤ) (n : ℤ) :
    snocExp β 0 + Finsupp.single (Fin.last k) n = snocExp β n := by
  refine Finsupp.ext fun i => ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Finsupp.add_apply, snocExp_castSucc, snocExp_castSucc,
      Finsupp.single_eq_of_ne (Fin.ne_of_lt (Fin.castSucc_lt_last j)), add_zero]
  · rw [Finsupp.add_apply, snocExp_last, snocExp_last, Finsupp.single_eq_same, zero_add]

omit [Algebra ℚ K] in
/-- **A monomial splits off its last variable.** -/
theorem monoElem_snocExp (β : Fin k →₀ ℤ) (n : ℤ) :
    (monoElem 1 (snocExp β n) : ConeRing (k + 1) 1 (Lambda K))
      = padElem (monoElem 1 β) * monoElem 1 (Finsupp.single (Fin.last k) n) := by
  rw [padElem_monoElem, monoElem_mul_monoElem, snocExp_add_single_last]

/-- The indices above `i` in `k+1` variables: those above `i` in `k` variables, and the last one. -/
lemma Ioi_castSucc (i : Fin k) :
    Finset.Ioi i.castSucc = insert (Fin.last k) ((Finset.Ioi i).image Fin.castSucc) := by
  ext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨l, rfl⟩ | rfl
  · simp only [Finset.mem_Ioi, Finset.mem_insert, Finset.mem_image,
      Fin.castSucc_lt_castSucc_iff]
    refine ⟨fun h => Or.inr ⟨l, h, rfl⟩, ?_⟩
    rintro (h | ⟨l', hl', hll'⟩)
    · exact absurd h (Fin.castSucc_lt_last l).ne
    · rw [Fin.castSucc_inj] at hll'
      rw [← hll']
      exact hl'
  · simp only [Finset.mem_Ioi, Finset.mem_insert, true_or, iff_true]
    exact Fin.castSucc_lt_last i

/-- The padding of a factor of the kernel expansion is the factor at the padded indices. -/
theorem padElem_kernelRay (q u : K) {i j : Fin k} (h : i < j) :
    padElem (kernelRay q u h) = kernelRay q u (Fin.castSucc_lt_castSucc_iff.2 h) :=
  padElem_rayHom _ _ (sub_single_mem_cone (Fin.castSucc_lt_castSucc_iff.2 h))
    (sub_single_ne_zero (ne_of_lt (Fin.castSucc_lt_castSucc_iff.2 h)))
    (snocExp_single_sub_single i j).symm _

lemma kernelRayIf_of_not_lt (q u : K) {i j : Fin k} (h : ¬ i < j) :
    kernelRayIf q u i j = 1 := dite_eq_right h

/-- The padding of a factor of the kernel expansion, in the totalised form. -/
theorem padElem_kernelRayIf (q u : K) (i j : Fin k) :
    padElem (kernelRayIf q u i j) = kernelRayIf q u i.castSucc j.castSucc := by
  by_cases h : i < j
  · rw [kernelRayIf_of_lt q u h, kernelRayIf_of_lt q u (Fin.castSucc_lt_castSucc_iff.2 h),
      padElem_kernelRay]
  · rw [kernelRayIf_of_not_lt q u h, kernelRayIf_of_not_lt q u
      (fun hc => h (Fin.castSucc_lt_castSucc_iff.1 hc)), padElem_one]

/-- **The expansion of the kernel factor splits off its last variable.** -/
theorem kernelExpansion_succ (q u : K) (k : ℕ) :
    kernelExpansion q u (k + 1)
      = padElem (kernelExpansion q u k)
        * ∏ i : Fin k, kernelRay q u (Fin.castSucc_lt_last i) := by
  rw [kernelExpansion, kernelExpansion, padElem_prod, Fin.prod_univ_castSucc,
    show Finset.Ioi (Fin.last k) = (∅ : Finset (Fin (k + 1))) from by
      rw [← Fin.top_eq_last]; exact Finset.Ioi_top,
    Finset.prod_empty, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Ioi_castSucc, Finset.prod_insert (by
    simp only [Finset.mem_image, not_exists]
    intro l hl
    exact (Fin.castSucc_lt_last l).ne hl.2),
    Finset.prod_image fun a _ b _ h => Fin.castSucc_inj.1 h, kernelRayIf_of_lt q u
      (Fin.castSucc_lt_last i), padElem_prod, mul_comm]
  refine congrArg (fun x => x * kernelRay q u (Fin.castSucc_lt_last i)) ?_
  exact (Finset.prod_congr rfl fun l _ => padElem_kernelRayIf q u i l).symm

end Splittings

end HJO.Bglx
