/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Prime
public import HJO.Macdonald.FiniteAlphabet

/-! # The linear factors `x_k - x_l`, and what the Vandermonde product divides

Groundwork for `HJO.Mac.exists_eq_macOp_algebraMap`: Macdonald's operator lands in the polynomial
ring because `𝒱_N D^{(n)}_1 f` is antisymmetric and `𝒱_N` is a product of pairwise non-associate
primes. Nothing here mentions the operator; it is all about the linear factors `x_k - x_l`.

## Main results

* `HJO.Mac.prime_X_sub_X`: `x_k - x_l` is prime for `k ≠ l`.
* `HJO.Mac.X_sub_X_dvd_of_substVar_eq_zero`: a polynomial killed by `x_l ↦ x_k` is divisible by
  `x_k - x_l`.
* `HJO.Mac.not_X_sub_X_dvd`: distinct linear factors are non-associate.
* `HJO.Mac.vandermondeProd_eq_prod_orderedPairs`: `𝒱_S` as a single product over ordered pairs.
* `HJO.Mac.rename_swap_vandermondeProd`: `𝒱_N` is antisymmetric.
* `HJO.Mac.vandermondeProd_univ_dvd_of_antisymm`: `𝒱_N` divides every antisymmetric polynomial.

## Implementation notes

`splitAt l` reads `𝕜[x_j : j]` as polynomials in `x_l` over the other variables, which is how both
the primality and the divisibility are got: under it `x_l - x_k` becomes the monic linear
`X - C (x_k)`, prime by `Polynomial.prime_X_sub_C`, and vanishing at `x_k` becomes being a root.

The antisymmetry of `𝒱_N` is proved over `ℤ` and transported, rather than proved over the
coefficient ring: the argument rules out `w 𝒱_N = 𝒱_N` using `2 ≠ 0`, while the identity itself has
integer coefficients and so holds over every commutative ring.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

/-! ### Substituting one variable for another -/

section Subst

variable {σ R : Type*} [CommRing R] [DecidableEq σ]

/-- The substitution `x_l ↦ x_k`, fixing every other variable. -/
noncomputable def substVar (k l : σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval (Function.update (X : σ → MvPolynomial σ R) l (X k))

@[simp]
theorem substVar_X_self (k l : σ) : substVar (R := R) k l (X l) = X k := by
  simp [substVar]

@[simp]
theorem substVar_X_of_ne (k : σ) {j l : σ} (h : j ≠ l) :
    substVar (R := R) k l (X j) = X j := by
  simp [substVar, Function.update_of_ne h]

/-- The substitution `x_l ↦ x_k` kills `x_k - x_l`, whether or not `k = l`. -/
@[simp]
theorem substVar_X_sub_X (k l : σ) : substVar (R := R) k l (X k - X l) = 0 := by
  rcases eq_or_ne k l with rfl | h
  · simp
  · rw [map_sub, substVar_X_of_ne k h, substVar_X_self, sub_self]

end Subst

/-! ### Reading the polynomial ring as polynomials in one variable -/

section SplitAt

variable {σ R : Type*} [CommRing R] [DecidableEq σ]

/-- The polynomial ring in the alphabet `σ`, read as polynomials in the single variable `x_l` over
the polynomial ring in the other variables. -/
noncomputable def splitAt (l : σ) :
    MvPolynomial σ R ≃ₐ[R] Polynomial (MvPolynomial {b : σ // b ≠ l} R) :=
  (renameEquiv R (Equiv.optionSubtypeNe l).symm).trans (optionEquivLeft R _)

@[simp]
theorem splitAt_X_self (l : σ) : splitAt (R := R) l (X l) = Polynomial.X := by
  rw [splitAt]
  simp

@[simp]
theorem splitAt_X_of_ne {j l : σ} (h : j ≠ l) :
    splitAt (R := R) l (X j) = Polynomial.C (X ⟨j, h⟩) := by
  rw [splitAt]
  simp [Equiv.optionSubtypeNe_symm_of_ne h]

@[simp]
theorem splitAt_C (l : σ) (r : R) :
    splitAt (R := R) l (C r) = Polynomial.C (C r) := by
  rw [splitAt]
  simp

theorem splitAt_symm_X (l : σ) : (splitAt (R := R) l).symm Polynomial.X = X l := by
  rw [← splitAt_X_self (R := R) l, AlgEquiv.symm_apply_apply]

theorem splitAt_symm_C_X {j l : σ} (h : j ≠ l) :
    (splitAt (R := R) l).symm (Polynomial.C (X ⟨j, h⟩)) = X j := by
  rw [← splitAt_X_of_ne (R := R) h, AlgEquiv.symm_apply_apply]

end SplitAt

/-! ### The linear factors are primes, and pairwise non-associate -/

section Factors

variable {σ R : Type*} [CommRing R] [IsDomain R]

/-- **`x_k - x_l` is prime.** Read as a polynomial in `x_l`, it is the monic linear
`X - C (x_k)`. -/
theorem prime_X_sub_X {k l : σ} (h : k ≠ l) : Prime (X k - X l : MvPolynomial σ R) := by
  classical
  have hp : Prime (splitAt (R := R) l (X k - X l)) := by
    rw [map_sub, splitAt_X_self, splitAt_X_of_ne h, ← neg_sub]
    exact (Polynomial.prime_X_sub_C (X (⟨k, h⟩ : {b : σ // b ≠ l}))).neg
  exact (MulEquiv.prime_iff (splitAt (R := R) l).toMulEquiv).1 hp

omit [IsDomain R] in
/-- **A polynomial killed by `x_l ↦ x_k` is divisible by `x_k - x_l`.** Read as a polynomial in
`x_l`, it has `x_k` as a root. -/
theorem X_sub_X_dvd_of_substVar_eq_zero [DecidableEq σ] {k l : σ} (h : k ≠ l)
    {p : MvPolynomial σ R}
    (hp : substVar k l p = 0) : (X k - X l : MvPolynomial σ R) ∣ p := by
  set k' : {b : σ // b ≠ l} := ⟨k, h⟩ with hk'
  set ρ : MvPolynomial {b : σ // b ≠ l} R →+* MvPolynomial σ R :=
    (rename (Subtype.val) : MvPolynomial {b : σ // b ≠ l} R →ₐ[R] MvPolynomial σ R).toRingHom
    with hρ
  -- the composite `evaluate at x_k, then forget the subtype` is the substitution
  set γ : Polynomial (MvPolynomial {b : σ // b ≠ l} R) →+* MvPolynomial σ R :=
    Polynomial.eval₂RingHom ρ (X k) with hγ
  have hρX : ∀ j : {b : σ // b ≠ l}, ρ (X j) = X (j : σ) := fun j => by simp [hρ]
  have hcomp : γ.comp (splitAt (R := R) l).toAlgHom.toRingHom = (substVar k l).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun j => ?_
    · simp [hγ, hρ, substVar]
    · rcases eq_or_ne j l with rfl | hj
      · simp [hγ]
      · simp [hγ, hj, hρ]
  have hγ0 : γ (splitAt (R := R) l p) = 0 := by
    have hfun := RingHom.congr_fun hcomp p
    simpa [hp] using hfun
  -- so `x_k` is a root of the one-variable reading
  have hroot : (splitAt (R := R) l p).eval (X k') = 0 := by
    have hval : ρ ((splitAt (R := R) l p).eval (X k')) = 0 := by
      rw [Polynomial.eval, Polynomial.hom_eval₂, RingHom.comp_id, hρX k']
      simpa [hγ, hk'] using hγ0
    have hinj : Function.Injective ρ := by
      rw [hρ]; exact rename_injective _ Subtype.val_injective
    exact hinj (by simpa using hval)
  have hdvd : (Polynomial.X - Polynomial.C (X k')) ∣ splitAt (R := R) l p :=
    Polynomial.dvd_iff_isRoot.2 hroot
  have := map_dvd (splitAt (R := R) l).symm hdvd
  rw [map_sub, splitAt_symm_X, splitAt_symm_C_X h, AlgEquiv.symm_apply_apply] at this
  rwa [← neg_sub, neg_dvd]

/-- **Distinct linear factors are non-associate.** For `k < l` and `k' < l'` with `(k, l)` and
`(k', l')` distinct, `x_k - x_l` does not divide `x_{k'} - x_{l'}`. -/
theorem not_X_sub_X_dvd [LinearOrder σ] {k l k' l' : σ} (hkl : k < l) (hk'l' : k' < l')
    (hne : (k, l) ≠ (k', l')) :
    ¬ (X k - X l : MvPolynomial σ R) ∣ (X k' - X l') := by
  classical
  intro hdvd
  have hzero : substVar (R := R) k l (X k' - X l') = 0 := by
    have hmap := map_dvd (substVar (R := R) k l) hdvd
    rw [substVar_X_sub_X k l] at hmap
    exact zero_dvd_iff.1 hmap
  have hXeq : ∀ a b : σ, (X a - X b : MvPolynomial σ R) = 0 → a = b := fun a b hab =>
    (X_inj a b).1 (sub_eq_zero.1 hab)
  rw [map_sub] at hzero
  rcases eq_or_ne k' l with rfl | hk'
  · rcases eq_or_ne l' k' with rfl | hl'
    · exact absurd hk'l' (lt_irrefl _)
    · rw [substVar_X_self, substVar_X_of_ne k hl'] at hzero
      exact absurd hkl (by rw [hXeq _ _ hzero]; exact not_lt.2 hk'l'.le)
  · rcases eq_or_ne l' l with rfl | hl'
    · rw [substVar_X_of_ne k hk', substVar_X_self] at hzero
      exact hne (Prod.ext (hXeq _ _ hzero).symm rfl)
    · rw [substVar_X_of_ne k hk', substVar_X_of_ne k hl'] at hzero
      exact absurd (hXeq _ _ hzero) hk'l'.ne

end Factors

/-! ### The Vandermonde product as a product over ordered pairs -/

section Pairs

variable {σ R : Type*} [CommRing R] [LinearOrder σ]

/-- The ordered pairs drawn from `S`: the index set of the factors of `𝒱_S`. -/
def orderedPairs (S : Finset σ) : Finset (σ × σ) := {p ∈ S ×ˢ S | p.1 < p.2}

@[simp]
theorem mem_orderedPairs {S : Finset σ} {p : σ × σ} :
    p ∈ orderedPairs S ↔ (p.1 ∈ S ∧ p.2 ∈ S) ∧ p.1 < p.2 := by
  simp [orderedPairs, Finset.mem_product]

/-- **The Vandermonde product as one product over ordered pairs**:
`𝒱_S = ∏_{(k, l), k < l}(v k - v l)`, the nested double product of `Finset.vandermondeProd`
flattened. -/
theorem vandermondeProd_eq_prod_orderedPairs (S : Finset σ) (v : σ → R) :
    S.vandermondeProd v = ∏ p ∈ orderedPairs S, (v p.1 - v p.2) := by
  rw [orderedPairs, Finset.prod_filter, Finset.prod_product, Finset.vandermondeProd]
  exact Finset.prod_congr rfl fun k _ => Finset.prod_filter _ _

end Pairs

/-! ### The Vandermonde product is antisymmetric -/

section Antisymm

variable {σ : Type*}

/-- The off-diagonal product `∏_{k ≠ l}(x_k - x_l)` is symmetric: a permutation permutes the
off-diagonal pairs. -/
theorem rename_prod_offDiag [Fintype σ] {R : Type*} [CommRing R] (w : Equiv.Perm σ) :
    rename w (∏ p ∈ (univ : Finset σ).offDiag, (X p.1 - X p.2) : MvPolynomial σ R) =
      ∏ p ∈ (univ : Finset σ).offDiag, (X p.1 - X p.2) := by
  rw [map_prod]
  refine Finset.prod_nbij' (fun p => (w p.1, w p.2)) (fun p => (w.symm p.1, w.symm p.2))
    (fun p hp => ?_) (fun p hp => ?_) (fun p _ => ?_) (fun p _ => ?_) fun p _ => ?_
  · rw [Finset.mem_offDiag] at hp ⊢
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, fun h => hp.2.2 (w.injective h)⟩
  · rw [Finset.mem_offDiag] at hp ⊢
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, fun h => hp.2.2 (w.symm.injective h)⟩
  · simp
  · simp
  · simp

/-- The off-diagonal product is the Vandermonde product squared, up to sign: each unordered pair
contributes both of its ordered readings. -/
theorem prod_offDiag_eq_vandermondeProd_sq [LinearOrder σ] [Fintype σ] {R : Type*} [CommRing R] :
    (∏ p ∈ (univ : Finset σ).offDiag, (X p.1 - X p.2) : MvPolynomial σ R) =
      (-1) ^ #(orderedPairs (univ : Finset σ)) *
        ((univ : Finset σ).vandermondeProd X) ^ 2 := by
  set P := orderedPairs (univ : Finset σ) with hP
  have hsplit : (univ : Finset σ).offDiag = P ∪ P.image Prod.swap := by
    refine Finset.ext fun p => ?_
    simp only [Finset.mem_offDiag, Finset.mem_union, Finset.mem_image, hP, mem_orderedPairs,
      Finset.mem_univ, true_and, and_true]
    constructor
    · intro h
      rcases lt_or_gt_of_ne h with hlt | hgt
      · exact Or.inl hlt
      · exact Or.inr ⟨(p.2, p.1), hgt, rfl⟩
    · rintro (h | ⟨q, hq, rfl⟩)
      · exact h.ne
      · exact hq.ne'
  have hdisj : Disjoint P (P.image Prod.swap) := by
    rw [Finset.disjoint_right]
    rintro p hp hp'
    rw [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [hP, mem_orderedPairs] at hp' hq
    exact absurd hq.2 (not_lt.2 hp'.2.le)
  rw [hsplit, Finset.prod_union hdisj,
    Finset.prod_image (fun p _ q _ h => Prod.swap_injective h)]
  have hneg : ∏ p ∈ P, (X (Prod.swap p).1 - X (Prod.swap p).2 : MvPolynomial σ R) =
      (-1) ^ #P * ∏ p ∈ P, (X p.1 - X p.2) := by
    rw [← Finset.prod_const (-1 : MvPolynomial σ R), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => by simp [Prod.swap]
  rw [hneg, vandermondeProd_eq_prod_orderedPairs, ← hP]
  ring

/-- Substituting `x_l ↦ x_k` absorbs the transposition of `k` and `l`. -/
theorem substVar_rename_swap {R : Type*} [CommRing R] [DecidableEq σ] (k l : σ)
    (p : MvPolynomial σ R) :
    substVar k l (rename (Equiv.swap k l) p) = substVar k l p := by
  have hcomp : (substVar (R := R) k l).comp (rename (Equiv.swap k l)) = substVar k l := by
    refine MvPolynomial.algHom_ext fun j => ?_
    rcases eq_or_ne k l with rfl | hkl
    · simp
    rcases eq_or_ne j k with rfl | hjk
    · rw [AlgHom.comp_apply, rename_X, Equiv.swap_apply_left, substVar_X_self,
        substVar_X_of_ne _ hkl]
    rcases eq_or_ne j l with rfl | hjl
    · rw [AlgHom.comp_apply, rename_X, Equiv.swap_apply_right, substVar_X_of_ne _ hkl,
        substVar_X_self]
    · rw [AlgHom.comp_apply, rename_X, Equiv.swap_apply_of_ne_of_ne hjk hjl,
        substVar_X_of_ne _ hjl]
  exact AlgHom.congr_fun hcomp p

/-- The `ℤ` case of the antisymmetry of `𝒱_N`, where the step ruling out the `+` sign has `2 ≠ 0`
available. -/
private theorem rename_swap_vandermondeProd_int [LinearOrder σ] [Fintype σ] {a b : σ}
    (hab : a < b) :
    rename (Equiv.swap a b) ((univ : Finset σ).vandermondeProd X : MvPolynomial σ ℤ) =
      -((univ : Finset σ).vandermondeProd X) := by
  set V : MvPolynomial σ ℤ := (univ : Finset σ).vandermondeProd X with hV
  set P := orderedPairs (univ : Finset σ) with hP
  set w := Equiv.swap a b with hw
  -- `V²` is symmetric, being the off-diagonal product up to a sign
  have hunit : ((-1 : MvPolynomial σ ℤ)) ^ #P ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have hsq : rename w V * rename w V = V * V := by
    have hoff := prod_offDiag_eq_vandermondeProd_sq (σ := σ) (R := ℤ)
    have hs := rename_prod_offDiag (R := ℤ) w
    rw [hoff, map_mul, map_pow, map_neg, map_one, map_pow, ← hV, ← hP] at hs
    have := mul_left_cancel₀ hunit hs
    rw [pow_two, pow_two] at this
    exact this
  rcases mul_self_eq_mul_self_iff.1 hsq with heq | heq
  · -- the `+` sign is impossible: it makes `x_a - x_b` divide the remaining factors
    exfalso
    have habP : (a, b) ∈ P := by rw [hP, mem_orderedPairs]; exact ⟨⟨mem_univ _, mem_univ _⟩, hab⟩
    set W := ∏ p ∈ P.erase (a, b), (X p.1 - X p.2 : MvPolynomial σ ℤ) with hW
    have hVW : V = (X a - X b) * W := by
      rw [hV, vandermondeProd_eq_prod_orderedPairs, ← hP, hW]
      exact (Finset.mul_prod_erase P _ habP).symm
    have hne0 : (X a - X b : MvPolynomial σ ℤ) ≠ 0 := fun h0 =>
      hab.ne ((X_inj a b).1 (sub_eq_zero.1 h0))
    have hrn : rename w W = -W := by
      have h1 : rename w V = -((X a - X b) * rename w W) := by
        rw [hVW, map_mul, map_sub, rename_X, rename_X, hw, Equiv.swap_apply_left,
          Equiv.swap_apply_right, ← neg_sub (X a) (X b), neg_mul]
      rw [heq, hVW] at h1
      have h2 : (X a - X b) * W = (X a - X b) * -(rename w W) := by rw [h1, mul_neg]
      have h3 := mul_left_cancel₀ hne0 h2
      linear_combination h3
    -- so the transposition-absorbing substitution kills `W`
    have hself : substVar a b W = -substVar a b W := by
      rw [← map_neg (substVar (R := ℤ) a b) W, ← hrn, substVar_rename_swap]
    have hzero : substVar a b W = 0 := by
      refine MvPolynomial.ext _ _ fun n => ?_
      have hc := congrArg (MvPolynomial.coeff n) hself
      rw [MvPolynomial.coeff_neg] at hc
      rw [MvPolynomial.coeff_zero]
      omega
    obtain ⟨q, hq, hqd⟩ :=
      (prime_X_sub_X (R := ℤ) hab.ne).exists_mem_finset_dvd
        (X_sub_X_dvd_of_substVar_eq_zero hab.ne hzero)
    exact not_X_sub_X_dvd hab (mem_orderedPairs.1 (Finset.mem_of_mem_erase hq)).2
      (Ne.symm (Finset.ne_of_mem_erase hq)) hqd
  · exact heq

/-- **The Vandermonde product is antisymmetric**: a transposition of two letters negates
`𝒱_N`. -/
theorem rename_swap_vandermondeProd {R : Type*} [CommRing R] [LinearOrder σ] [Fintype σ]
    {a b : σ} (hab : a ≠ b) :
    rename (Equiv.swap a b) ((univ : Finset σ).vandermondeProd X : MvPolynomial σ R) =
      -((univ : Finset σ).vandermondeProd X) := by
  -- the identity has integer coefficients, so it is enough over `ℤ`
  have key : ∀ {c d : σ}, c < d →
      rename (Equiv.swap c d) ((univ : Finset σ).vandermondeProd X : MvPolynomial σ R) =
        -((univ : Finset σ).vandermondeProd X) := by
    intro c d hcd
    have hmap : ∀ v : σ → MvPolynomial σ ℤ,
        MvPolynomial.map (Int.castRingHom R) ((univ : Finset σ).vandermondeProd v) =
          (univ : Finset σ).vandermondeProd fun i => MvPolynomial.map (Int.castRingHom R) (v i) :=
      fun v => Finset.map_vandermondeProd _ _ v
    have hVR : MvPolynomial.map (Int.castRingHom R)
        ((univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ ℤ)) =
        (univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ R) := by
      rw [hmap]
      simp
    calc rename (Equiv.swap c d) ((univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ R))
        = rename (Equiv.swap c d) (MvPolynomial.map (Int.castRingHom R)
            ((univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ ℤ))) := by rw [hVR]
      _ = MvPolynomial.map (Int.castRingHom R) (rename (Equiv.swap c d)
            ((univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ ℤ))) := by
            rw [MvPolynomial.map_rename]
      _ = -((univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ R)) := by
            rw [rename_swap_vandermondeProd_int hcd, map_neg, hVR]
  rcases lt_or_gt_of_ne hab with h | h
  · exact key h
  · rw [Equiv.swap_comm]; exact key h

end Antisymm

/-! ### A product of pairwise non-associate primes divides what each factor divides -/

theorem prod_dvd_of_prime {R ι : Type*} [CommMonoidWithZero R] (s : Finset ι) (p : ι → R) :
    ∀ n : R, (∀ i ∈ s, Prime (p i)) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ p i ∣ p j) →
      (∀ i ∈ s, p i ∣ n) → (∏ i ∈ s, p i) ∣ n := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
      intro n hp hne hdvd
      obtain ⟨m, hm⟩ := hdvd a (Finset.mem_cons_self a s)
      have hmem : ∀ i ∈ s, i ∈ Finset.cons a s ha := fun i hi => Finset.mem_cons_of_mem hi
      have hdvd' : ∀ i ∈ s, p i ∣ m := by
        intro i hi
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        have hin := hdvd i (hmem i hi)
        rw [hm] at hin
        exact ((hp i (hmem i hi)).2.2 _ _ hin).resolve_left
          (hne i (hmem i hi) a (Finset.mem_cons_self a s) hia)
      rw [Finset.prod_cons, hm]
      exact mul_dvd_mul_left _ (ih m (fun i hi => hp i (hmem i hi))
        (fun i hi j hj => hne i (hmem i hi) j (hmem j hj)) hdvd')

/-! ### The Vandermonde product divides every antisymmetric polynomial -/

section Divides

variable {σ R : Type*} [CommRing R] [IsDomain R] [CharZero R] [LinearOrder σ] [Fintype σ]

private theorem eq_zero_of_eq_neg {S : Type*} [CommRing S] [NoZeroDivisors S] (h2 : (2 : S) ≠ 0)
    {x : S} (h : x = -x) : x = 0 :=
  (mul_eq_zero.1 (show (2 : S) * x = 0 by linear_combination h)).resolve_left h2

/-- **`𝒱_N` divides every antisymmetric polynomial.** The factors `x_k - x_l`, `k < l`, are pairwise
non-associate primes, and each divides an antisymmetric `p`: the substitution `x_l ↦ x_k` absorbs
the transposition, so it sends `p` to its own negative and hence to `0`. -/
theorem vandermondeProd_univ_dvd_of_antisymm {p : MvPolynomial σ R}
    (hp : ∀ a b : σ, a ≠ b → rename (Equiv.swap a b) p = -p) :
    ((univ : Finset σ).vandermondeProd X : MvPolynomial σ R) ∣ p := by
  have h2 : (2 : MvPolynomial σ R) ≠ 0 := by
    rw [← map_ofNat C 2, Ne, C_eq_zero]
    exact two_ne_zero
  rw [vandermondeProd_eq_prod_orderedPairs]
  refine prod_dvd_of_prime _ _ p (fun q hq => prime_X_sub_X (mem_orderedPairs.1 hq).2.ne)
    (fun q hq q' hq' hne => ?_) fun q hq => ?_
  · exact not_X_sub_X_dvd (mem_orderedPairs.1 hq).2 (mem_orderedPairs.1 hq').2 hne
  · refine X_sub_X_dvd_of_substVar_eq_zero (mem_orderedPairs.1 hq).2.ne ?_
    refine eq_zero_of_eq_neg h2 ?_
    rw [← map_neg (substVar (R := R) q.1 q.2) p, ← hp q.1 q.2 (mem_orderedPairs.1 hq).2.ne,
      substVar_rename_swap]

end Divides

end HJO.Mac
