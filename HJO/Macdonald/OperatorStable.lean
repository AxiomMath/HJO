/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.PairFactors
public meta import HJO.Attr

/-! # Macdonald's operator preserves symmetry, and acts on a graded piece

Two lemmas: `HJO.Mac.permAct_macOp`, that a permutation of the alphabet commutes with
`D^{(n)}_1`, and `HJO.Mac.exists_eq_macOp_algebraMap`, that `D^{(n)}_1` carries `𝒮_{n,d}` into
itself. With them the finite-alphabet ground of the Macdonald construction is `HJO.Mac.macOp`,
`HJO.Mac.macOp_smul_add`, `HJO.Mac.vandermondeProd_mul_macOp` (`HJO/Macdonald/FiniteAlphabet.lean`)
and these two.

## Main definitions

* `HJO.Mac.permAct`: the action of a permutation of the alphabet on `𝕜(x_1, …, x_n)`.
* `HJO.Mac.scaleAct`: rescaling every variable by one unit, on `𝕜(x_1, …, x_n)`.
* `HJO.Mac.macOpNum`: the right-hand side of `HJO.Mac.vandermondeProd_mul_macOp`, as a polynomial.
* `HJO.Mac.macOpComp`: `D^{(n)}_1` as an endomorphism of `𝒮_{n,d}`, which is the form the later
  constructions use.

## Main results

* `HJO.Mac.macOp_permAct`: `w (D^{(n)}_1 f) = D^{(n)}_1 (w f)` -- `HJO.Mac.permAct_macOp` is the
  case `w f = f`.
* `HJO.Mac.macOp_scaleAct`: `D^{(n)}_1` commutes with rescaling all the variables.
* `HJO.Mac.exists_eq_macOp_algebraMap`.
* `HJO.Mac.algebraMap_macOpComp`, `HJO.Mac.eq_macOpComp`: `macOpComp` is `D^{(n)}_1` on `𝒮_{n,d}`,
  and that property determines it.

## Implementation notes

`𝒮_{n,d}` lives in the polynomial ring and `D^{(n)}_1` on the rational function field, so
"`D^{(n)}_1 f ∈ 𝒮_{n,d}`" is stated as: there is a `g ∈ 𝒮_{n,d}` whose image in the function field
is `D^{(n)}_1 f`. That is what the claim says -- the operator applied to a graded
symmetric polynomial *is* a graded symmetric polynomial -- and it is the form the later results
want, since they go on to treat `D^{(n)}_1` as an endomorphism of `𝒮_{n,d}`.

The degree count of the usual proof is replaced by the rescaling action: `D^{(n)}_1` commutes
with rescaling every variable by one unit `c` (its coefficients `A_i` are ratios of forms of equal
degree, and the two diagonal rescalings commute), and a polynomial is homogeneous of degree `d`
exactly when rescaling multiplies it by `c^d` for one `c` no two of whose powers agree -- `c = 2`,
which is where `[Algebra ℚ K]` is used a second time. This avoids computing the degree of
`𝒱_{N∖{i}}`, i.e. counting the pairs of an alphabet with one letter removed.

`[Algebra ℚ K]` is not an extra hypothesis: the usual proof of
`HJO.Mac.exists_eq_macOp_algebraMap` invokes "the characteristic of `𝕜` being zero" to get
`2 φ(G) = 0 ⇒ φ(G) = 0`, and `𝕜 = ℚ(q, u)` throughout. It is carried in a statement here rather than
in the ambient setting.

## References

This file proves `HJO.Mac.permAct_macOp` and
`HJO.Mac.exists_eq_macOp_algebraMap`. Macdonald's operator is his `D^1_n` and
Garsia--Haiman--Tesler's `D^{(n)}_1`, with their second parameter `t` written `u`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

/-! ### The permutation action on the rational function field -/

section PermAct

variable {σ K : Type*} [Field K]

/-- The action of a permutation `w` of the alphabet on the rational function field: the extension to
the fraction field of the renaming `x_k ↦ x_{w k}`. This is the permutation action `w`, "written
also for the `𝕜`-algebra automorphism of `𝕜(x_1, …, x_n)` sending `x_k` to `x_{w(k)}`". -/
noncomputable def permAct (w : Equiv.Perm σ) :
    FractionRing (MvPolynomial σ K) ≃ₐ[K] FractionRing (MvPolynomial σ K) :=
  IsFractionRing.fieldEquivOfAlgEquiv K (FractionRing (MvPolynomial σ K))
    (FractionRing (MvPolynomial σ K)) (renameEquiv K w)

@[simp]
theorem permAct_algebraMap (w : Equiv.Perm σ) (p : MvPolynomial σ K) :
    permAct w (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p) =
      algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (rename w p) :=
  IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K _ _ _ p

/-- Rescaling every variable by one unit `c`, on the rational function field. -/
noncomputable def scaleAct (c : Kˣ) :
    FractionRing (MvPolynomial σ K) ≃ₐ[K] FractionRing (MvPolynomial σ K) :=
  IsFractionRing.fieldEquivOfAlgEquiv K (FractionRing (MvPolynomial σ K))
    (FractionRing (MvPolynomial σ K)) (rescaleEquiv fun _ : σ => c)

@[simp]
theorem scaleAct_algebraMap (c : Kˣ) (p : MvPolynomial σ K) :
    scaleAct c (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p) =
      algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
        (rescaleEquiv (fun _ : σ => c) p) :=
  IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K _ _ _ p

end PermAct

/-! ### How the two actions meet the parameter shift and the coefficients -/

section Commute

variable {σ K : Type*} [Field K] [DecidableEq σ]

/-- Renaming the variables carries the shift of `x_i` to the shift of `x_{w i}`. -/
theorem rename_rescaleEquiv_mulSingle (q : Kˣ) (w : Equiv.Perm σ) (i : σ)
    (p : MvPolynomial σ K) :
    rename w (rescaleEquiv (Pi.mulSingle i q) p) =
      rescaleEquiv (Pi.mulSingle (w i) q) (rename w p) := by
  have hcomp : (rename (R := K) w).comp (rescaleEquiv (Pi.mulSingle i q)).toAlgHom =
      (rescaleEquiv (Pi.mulSingle (w i) q)).toAlgHom.comp (rename w) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    have hscal : (Pi.mulSingle i q : σ → Kˣ) j = (Pi.mulSingle (w i) q : σ → Kˣ) (w j) := by
      rcases eq_or_ne j i with rfl | hj
      · rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne fun h => hj (w.injective h)]
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, rescaleEquiv_X, rename_X, map_smul]
    rw [hscal]
  exact AlgHom.congr_fun hcomp p

/-- Renaming the variables carries `T_{q,x_i}` to `T_{q,x_{w i}}`. -/
theorem permAct_qShift (q : Kˣ) (w : Equiv.Perm σ) (i : σ)
    (f : FractionRing (MvPolynomial σ K)) :
    permAct w (qShift q i f) = qShift q (w i) (permAct w f) := by
  obtain ⟨p, r, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ K) f
  simp only [map_div₀, qShift_algebraMap, permAct_algebraMap, rename_rescaleEquiv_mulSingle]

/-- Rescaling every variable commutes with the shift of one variable: the two are rescalings of the
variables and those commute. -/
theorem scaleAct_qShift (q : Kˣ) (c : Kˣ) (i : σ) (f : FractionRing (MvPolynomial σ K)) :
    scaleAct c (qShift q i f) = qShift q i (scaleAct c f) := by
  have hpoly : ∀ p : MvPolynomial σ K,
      rescaleEquiv (fun _ : σ => c) (rescaleEquiv (Pi.mulSingle i q) p) =
        rescaleEquiv (Pi.mulSingle i q) (rescaleEquiv (fun _ : σ => c) p) := by
    intro p
    have h1 := AlgEquiv.congr_fun
      (rescaleEquiv_trans (R := K) (σ := σ) (Pi.mulSingle i q) (fun _ => c)) p
    have h2 := AlgEquiv.congr_fun
      (rescaleEquiv_trans (R := K) (σ := σ) (fun _ => c) (Pi.mulSingle i q)) p
    rw [AlgEquiv.trans_apply] at h1 h2
    rw [h1, h2, mul_comm]
  obtain ⟨p, r, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ K) f
  simp only [map_div₀, qShift_algebraMap, scaleAct_algebraMap, hpoly]

end Commute

/-! ### The two actions on the coefficients of Macdonald's operator -/

section Coeff

variable {σ K : Type*} [Field K]

@[simp]
theorem rescaleEquiv_C (c : σ → Kˣ) (a : K) : rescaleEquiv c (C a) = C a := by
  rw [← MvPolynomial.algebraMap_eq]
  exact (rescaleEquiv c).commutes a

variable [LinearOrder σ] [Fintype σ]

/-- Renaming the variables carries the coefficient attached to `i` to the one attached to `w i`: as
`j` runs over the letters other than `i`, `w j` runs over those other than `w i`. -/
theorem permAct_macCoeff (u : K) (w : Equiv.Perm σ) (i : σ) :
    permAct w (macCoeff u i) = macCoeff u (w i) := by
  rw [macCoeff, map_prod, macCoeff]
  refine Finset.prod_nbij' (fun j => w j) (fun j => w.symm j) (fun j hj => ?_) (fun j hj => ?_)
    (fun j _ => ?_) (fun j _ => ?_) fun j _ => ?_
  · rw [Finset.mem_erase] at hj ⊢
    exact ⟨fun h => hj.1 (w.injective h), Finset.mem_univ _⟩
  · rw [Finset.mem_erase] at hj ⊢
    refine ⟨fun h => hj.1 ?_, Finset.mem_univ _⟩
    rw [← h, Equiv.apply_symm_apply]
  · simp
  · simp
  · rw [map_div₀, permAct_algebraMap, permAct_algebraMap]
    simp

/-- Rescaling every variable fixes the coefficients of Macdonald's operator: numerator and
denominator are both multiplied by `c`. -/
theorem scaleAct_macCoeff (u : K) (c : Kˣ) (i : σ) :
    scaleAct c (macCoeff u i) = macCoeff u i := by
  rw [macCoeff, map_prod]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hnum : rescaleEquiv (fun _ : σ => c) (C u * X i - X j) =
      C (c : K) * (C u * X i - X j) := by
    rw [map_sub, map_mul, rescaleEquiv_C, rescaleEquiv_X, rescaleEquiv_X, smul_eq_C_mul,
      smul_eq_C_mul]
    ring
  have hden : rescaleEquiv (fun _ : σ => c) (X i - X j) = C (c : K) * (X i - X j) := by
    rw [map_sub, rescaleEquiv_X, rescaleEquiv_X, smul_eq_C_mul, smul_eq_C_mul]
    ring
  have hc : algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (C (c : K)) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _), C_eq_zero]
    exact c.ne_zero
  rw [map_div₀, scaleAct_algebraMap, scaleAct_algebraMap, hnum, hden, map_mul, map_mul,
    mul_div_mul_left _ _ hc]

end Coeff

/-! ### Macdonald's operator against the two actions -/

section Equivariance

variable {σ K : Type*} [Field K] [LinearOrder σ] [Fintype σ]

/-- **Macdonald's operator commutes with a permutation of the alphabet.** The coefficient attached
to `i` goes to the one attached to `w i` and the shift of `x_i` to the shift of `x_{w i}`, so the
sum is reindexed by `w`. -/
theorem macOp_permAct (q : Kˣ) (u : K) (w : Equiv.Perm σ)
    (f : FractionRing (MvPolynomial σ K)) :
    permAct w (macOp q u f) = macOp q u (permAct w f) := by
  rw [macOp_apply, map_sum, macOp_apply]
  refine Fintype.sum_equiv w _ _ fun i => ?_
  rw [map_mul, permAct_macCoeff, permAct_qShift]

/-- **Macdonald's operator preserves symmetry.** If `f` is fixed by the permutation `w` of the
alphabet then so is `D^{(n)}_1 f`. -/
@[hjo "lem_mac_dop_symmetric"]
theorem permAct_macOp (q : Kˣ) (u : K) (w : Equiv.Perm σ)
    {f : FractionRing (MvPolynomial σ K)} (hf : permAct w f = f) :
    permAct w (macOp q u f) = macOp q u f := by
  rw [macOp_permAct, hf]

/-- **Macdonald's operator commutes with rescaling every variable.** -/
theorem macOp_scaleAct (q : Kˣ) (u : K) (c : Kˣ) (f : FractionRing (MvPolynomial σ K)) :
    scaleAct c (macOp q u f) = macOp q u (scaleAct c f) := by
  rw [macOp_apply, map_sum, macOp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, scaleAct_macCoeff, scaleAct_qShift]

end Equivariance

/-! ### Rescaling reads the degree -/

section Rescale

variable {σ K : Type*} [Field K]

private theorem weight_one_eq_sum (e : σ →₀ ℕ) :
    (Finsupp.weight 1) e = ∑ i ∈ e.support, e i := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- The coefficient of a monomial after rescaling the variables. -/
theorem coeff_rescaleEquiv (c : σ → Kˣ) (e : σ →₀ ℕ) (p : MvPolynomial σ K) :
    coeff e (rescaleEquiv c p) = coeff e p * ∏ i ∈ e.support, (c i : K) ^ e i := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum, coeff_sum]
  rcases eq_or_ne (coeff e p) 0 with h0 | h0
  · rw [h0, zero_mul, Finset.sum_eq_zero]
    intro e' he'
    rw [rescaleEquiv_monomial, coeff_monomial]
    rcases eq_or_ne e' e with rfl | hne
    · exact absurd h0 (mem_support_iff.1 he')
    · simp [hne]
  · rw [Finset.sum_eq_single e]
    · rw [rescaleEquiv_monomial, coeff_monomial]
      simp
    · intro e' _ hne
      rw [rescaleEquiv_monomial, coeff_monomial]
      simp [hne]
    · intro he
      exact absurd (mem_support_iff.2 h0) he

/-- A homogeneous polynomial of degree `d` is multiplied by `c^d` when every variable is rescaled
by `c`. -/
theorem rescaleEquiv_const_of_isHomogeneous {d : ℕ} {p : MvPolynomial σ K}
    (hp : p.IsHomogeneous d) (c : Kˣ) :
    rescaleEquiv (fun _ : σ => c) p = ((c : K) ^ d) • p := by
  refine MvPolynomial.ext _ _ fun e => ?_
  rw [coeff_rescaleEquiv, coeff_smul, smul_eq_mul]
  rcases eq_or_ne (coeff e p) 0 with h0 | h0
  · rw [h0, zero_mul, mul_zero]
  · have hdeg : ∑ i ∈ e.support, e i = d := by
      rw [← weight_one_eq_sum]
      exact hp h0
    rw [Finset.prod_pow_eq_pow_sum, hdeg, mul_comm]

/-- A polynomial rescaled to `c^d` times itself by one unit `c` no two of whose powers agree is
homogeneous of degree `d`. -/
theorem isHomogeneous_of_rescaleEquiv_const {d : ℕ} {p : MvPolynomial σ K} (c : Kˣ)
    (hc : ∀ a b : ℕ, (c : K) ^ a = (c : K) ^ b → a = b)
    (h : rescaleEquiv (fun _ : σ => c) p = ((c : K) ^ d) • p) : p.IsHomogeneous d := by
  intro e he
  have hcoeff := congrArg (coeff e) h
  rw [coeff_rescaleEquiv, coeff_smul, smul_eq_mul, Finset.prod_pow_eq_pow_sum] at hcoeff
  have hpow : (c : K) ^ (∑ i ∈ e.support, e i) = (c : K) ^ d :=
    mul_left_cancel₀ he (by rw [hcoeff, mul_comm])
  rw [weight_one_eq_sum]
  exact hc _ _ hpow

end Rescale

/-! ### Macdonald's operator acts on a graded piece -/

section Stable

variable {σ K : Type*} [Field K] [LinearOrder σ] [Fintype σ]

/-- The numerator of Macdonald's operator against the Vandermonde product: the right-hand side of
`HJO.Mac.vandermondeProd_mul_macOp`, read in the polynomial ring. -/
noncomputable def macOpNum (q : Kˣ) (u : K) (f : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ i : σ, (-1) ^ #{k ∈ (univ : Finset σ) | k < i} *
    (Finset.univ.erase i).vandermondeProd X *
    (∏ j ∈ Finset.univ.erase i, (C u * X i - X j)) *
    rescaleEquiv (Pi.mulSingle i q) f

/-- `𝒱_N D^{(n)}_1 f` is a polynomial, and `macOpNum` is that polynomial. -/
theorem algebraMap_macOpNum (q : Kˣ) (u : K) (f : MvPolynomial σ K) :
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (macOpNum q u f) =
      algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          ((univ : Finset σ).vandermondeProd X) *
        macOp q u (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) f) := by
  rw [vandermondeProd_mul_macOp, macOpNum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, map_mul, map_pow, map_neg, map_one, qShift_algebraMap]

omit [LinearOrder σ] [Fintype σ] in
/-- The inclusion of the polynomials in the rational function field is `𝕜`-linear. -/
theorem algebraMap_smul (r : K) (p : MvPolynomial σ K) :
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (r • p) =
      r • algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply K (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))]

/-- The Vandermonde product is not zero: its factors are differences of distinct variables. -/
theorem vandermondeProd_univ_ne_zero :
    ((univ : Finset σ).vandermondeProd X : MvPolynomial σ K) ≠ 0 := by
  rw [vandermondeProd_eq_prod_orderedPairs, Finset.prod_ne_zero_iff]
  intro p hp
  exact X_sub_X_ne_zero (mem_orderedPairs.1 hp).2.ne

/-- `𝒱_N D^{(n)}_1 f` is antisymmetric when `f` is symmetric: `𝒱_N` is antisymmetric and
`D^{(n)}_1 f` is symmetric. -/
theorem rename_swap_macOpNum (q : Kˣ) (u : K) {f : MvPolynomial σ K} (hf : f.IsSymmetric)
    {a b : σ} (hab : a ≠ b) :
    rename (Equiv.swap a b) (macOpNum q u f) = -macOpNum q u f := by
  refine IsFractionRing.injective (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) ?_
  set w := Equiv.swap a b with hw
  calc algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (rename w (macOpNum q u f))
      = permAct w (algebraMap _ _ (macOpNum q u f)) := (permAct_algebraMap w _).symm
    _ = permAct w (algebraMap _ _ ((univ : Finset σ).vandermondeProd X) *
          macOp q u (algebraMap _ _ f)) := by rw [algebraMap_macOpNum]
    _ = permAct w (algebraMap _ _ ((univ : Finset σ).vandermondeProd X)) *
          permAct w (macOp q u (algebraMap _ _ f)) := map_mul _ _ _
    _ = algebraMap _ _ (rename w ((univ : Finset σ).vandermondeProd X)) *
          macOp q u (permAct w (algebraMap _ _ f)) := by
          rw [permAct_algebraMap, macOp_permAct]
    _ = algebraMap _ _ (-((univ : Finset σ).vandermondeProd X)) *
          macOp q u (algebraMap _ _ f) := by
          rw [hw, rename_swap_vandermondeProd hab, permAct_algebraMap, hf w]
    _ = -(algebraMap _ _ ((univ : Finset σ).vandermondeProd X) *
          macOp q u (algebraMap _ _ f)) := by rw [map_neg, neg_mul]
    _ = algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (-macOpNum q u f) := by
          rw [map_neg, algebraMap_macOpNum]

/-- **Macdonald's operator acts on a graded piece.** For `f` symmetric and homogeneous of degree
`d`, `D^{(n)}_1 f` is (the image of) a symmetric polynomial homogeneous of degree `d`.

The division is legitimate because `𝒱_N D^{(n)}_1 f` is antisymmetric and `𝒱_N` is a product of
pairwise non-associate primes; the degree is read off by rescaling all the variables. -/
@[hjo "lem_mac_dop_stable"]
theorem exists_eq_macOp_algebraMap [Algebra ℚ K] (q : Kˣ) (u : K) {d : ℕ} {f : MvPolynomial σ K}
    (hf : f ∈ symmetricHomogeneousSubmodule σ K d) :
    ∃ g ∈ symmetricHomogeneousSubmodule σ K d,
      macOp q u (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) f) =
        algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) g := by
  have hchar : CharZero K := charZero_of_injective_algebraMap
    (algebraMap ℚ K).injective
  obtain ⟨hfsymm, hfhom⟩ := mem_symmetricHomogeneousSubmodule.1 hf
  -- the Vandermonde product divides the numerator
  obtain ⟨g, hg⟩ : ((univ : Finset σ).vandermondeProd X : MvPolynomial σ K) ∣ macOpNum q u f :=
    vandermondeProd_univ_dvd_of_antisymm fun a b hab => rename_swap_macOpNum q u hfsymm hab
  have hVne : algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
      ((univ : Finset σ).vandermondeProd X) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact vandermondeProd_univ_ne_zero
  -- so the operator lands on `g`
  have hmac : macOp q u (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) f) =
      algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) g := by
    refine mul_left_cancel₀ hVne ?_
    rw [← algebraMap_macOpNum, hg, map_mul]
  refine ⟨g, mem_symmetricHomogeneousSubmodule.2 ⟨fun w => ?_, ?_⟩, hmac⟩
  · -- `g` is symmetric, because `D^{(n)}_1` commutes with the permutation action
    refine IsFractionRing.injective (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) ?_
    rw [← permAct_algebraMap w, ← hmac, macOp_permAct, permAct_algebraMap, hfsymm w, hmac]
  · -- `g` is homogeneous of degree `d`, because `D^{(n)}_1` commutes with rescaling
    set c : Kˣ := Units.mk0 (2 : K) two_ne_zero with hcdef
    have hcpow : ∀ a b : ℕ, (c : K) ^ a = (c : K) ^ b → a = b := by
      intro a b hpow
      have hcast : ((2 ^ a : ℕ) : K) = ((2 ^ b : ℕ) : K) := by
        push_cast
        simpa [hcdef] using hpow
      exact Nat.pow_right_injective le_rfl (Nat.cast_injective hcast)
    refine isHomogeneous_of_rescaleEquiv_const c hcpow ?_
    refine IsFractionRing.injective (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) ?_
    calc algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          (rescaleEquiv (fun _ : σ => c) g)
        = scaleAct c (macOp q u (algebraMap _ _ f)) := by rw [hmac, scaleAct_algebraMap]
      _ = macOp q u (algebraMap _ _ (rescaleEquiv (fun _ : σ => c) f)) := by
          rw [macOp_scaleAct, scaleAct_algebraMap]
      _ = macOp q u (((c : K) ^ d) • algebraMap _ _ f) := by
          rw [rescaleEquiv_const_of_isHomogeneous hfhom c, algebraMap_smul]
      _ = ((c : K) ^ d) • macOp q u (algebraMap _ _ f) := map_smul _ _ _
      _ = algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
            (((c : K) ^ d) • g) := by rw [hmac, algebraMap_smul]

end Stable

/-! ### Macdonald's operator as an endomorphism of a graded piece

`HJO.Mac.exists_eq_macOp_algebraMap` says that `D^{(n)}_1` does not leave `𝒮_{n,d}`; its
consumers -- the triangularity of `D^{(n)}_1` on the monomial symmetric polynomials and the
uniqueness of the monic eigenfunction -- want the endomorphism of `𝒮_{n,d}` that follows, which is
what this section builds. The stability is the substance; turning it into a map is linear algebra.
-/

section Component

variable {σ K : Type*} [Field K] [LinearOrder σ] [Fintype σ] [Algebra ℚ K]

private theorem choose_spec_algebraMap (q : Kˣ) (u : K) {d : ℕ}
    (v : symmetricHomogeneousSubmodule σ K d) :
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
        ((exists_eq_macOp_algebraMap q u v.2).choose) =
      macOp q u (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
        (v : MvPolynomial σ K)) :=
  ((exists_eq_macOp_algebraMap q u v.2).choose_spec.2).symm

private theorem choose_eq (q : Kˣ) (u : K) {d : ℕ} (v : symmetricHomogeneousSubmodule σ K d)
    (g : MvPolynomial σ K)
    (h : macOp q u (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
      (v : MvPolynomial σ K)) =
        algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) g) :
    (exists_eq_macOp_algebraMap q u v.2).choose = g :=
  IsFractionRing.injective (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
    (by rw [choose_spec_algebraMap, h])

/-- **Macdonald's operator on a graded piece**: the `𝕜`-endomorphism of `𝒮_{n,d}` that
`HJO.Mac.exists_eq_macOp_algebraMap` provides. On the image of `𝒮_{n,d}` in the rational function
field it agrees with `D^{(n)}_1` (`algebraMap_macOpComp`), and that pins it (`eq_macOpComp`). -/
noncomputable def macOpComp (q : Kˣ) (u : K) (d : ℕ) :
    Module.End K (symmetricHomogeneousSubmodule σ K d) where
  toFun v := ⟨(exists_eq_macOp_algebraMap q u v.2).choose,
    (exists_eq_macOp_algebraMap q u v.2).choose_spec.1⟩
  map_add' v w := Subtype.ext (by
    refine choose_eq q u (v + w) _ ?_
    simp only [Submodule.coe_add, map_add]
    rw [choose_spec_algebraMap, choose_spec_algebraMap])
  map_smul' a v := Subtype.ext (by
    refine choose_eq q u (a • v) _ ?_
    simp only [SetLike.val_smul, algebraMap_smul, map_smul, RingHom.id_apply]
    rw [choose_spec_algebraMap])

/-- The defining property of `macOpComp`: on `𝒮_{n,d}` it is Macdonald's operator. -/
theorem algebraMap_macOpComp (q : Kˣ) (u : K) (d : ℕ)
    (v : symmetricHomogeneousSubmodule σ K d) :
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
        ((macOpComp q u d v : MvPolynomial σ K)) =
      macOp q u (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
        (v : MvPolynomial σ K)) :=
  choose_spec_algebraMap q u v

/-- That property pins the endomorphism: if `D^{(n)}_1` carries `v` to `w`, so does
`macOpComp`. -/
theorem eq_macOpComp (q : Kˣ) (u : K) (d : ℕ) {v w : symmetricHomogeneousSubmodule σ K d}
    (h : macOp q u (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
      (v : MvPolynomial σ K)) = algebraMap (MvPolynomial σ K)
        (FractionRing (MvPolynomial σ K)) (w : MvPolynomial σ K)) :
    macOpComp q u d v = w :=
  Subtype.ext (choose_eq q u v (w : MvPolynomial σ K) h)

end Component

end HJO.Mac
