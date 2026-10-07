/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.PairFactors

/-! # The coefficients of `splitAt`: reading one variable off a multivariable polynomial

`HJO.Mac.splitAt l` reads `R[x_b : b ∈ σ]` as polynomials in the single variable `x_l` over
`R[x_b : b ≠ l]`. `HJO/Macdonald/PairFactors.lean` introduces it and says what it does to a
variable and to a constant, which is all the primality of `x_k - x_l` needs. This file says what it
does to a *coefficient*, and draws the consequences a proof that extracts the coefficient
of `x_l^k` actually uses: the degree in `x_l`, and the symmetry and homogeneity of the extracted
coefficient.

## The bridge

`HJO.Mac.splitAt_coeff_coeff` is the whole content:
```
coeff m ((splitAt l p).coeff k) = coeff (Finsupp.mapDomain Subtype.val m + Finsupp.single l k) p
```
— the coefficient of `x^m x_l^k`, with `m` an exponent on the small alphabet, read on either side of
the split. It is not proved by monomial induction: Mathlib's `optionEquivLeft_coeff_coeff` is this
statement for `Option σ`, and `splitAt` is `optionEquivLeft` after
`rename (Equiv.optionSubtypeNe l).symm`, so the only work is to identify
`Finsupp.mapDomain (Equiv.optionSubtypeNe l).symm` of the exponent with `Finsupp.optionElim`. For
the same reason `natDegree_splitAt` is Mathlib's `degreeOf_eq_natDegree` transported, not a new
proof.

## The corollaries

`natDegree_splitAt_le` turns an entrywise bound on the support at the letter `l` into a bound on the
degree in `x_l`; the consumer supplying such a bound is
`HJO.Mac.apply_le_partExp_of_mem_support_macPpoly`, whose conclusion is
entrywise at every letter.

`isSymmetric_coeff_splitAt` and `isHomogeneous_coeff_splitAt` are the two halves of "the extracted
coefficient lies in `𝒮_{n-1,d-k}`". The symmetry goes through `Equiv.Perm.extendDomain`: a
permutation of `{b // b ≠ l}` extends to one of `σ` fixing `l`, and the bridge turns the
`mapDomain` of the extension into the `mapDomain` of the permutation. The homogeneity is stated as
`k + j = d` rather than `j = d - k` on purpose: `ℕ` subtraction truncates, and a statement written
with it is satisfied vacuously when `d < k`.

`splitAt_rename_val` is the converse direction: a polynomial in the small alphabet, pushed into the
big one, is a constant in `x_l`. It is what lets an identity between extracted coefficients be
transported back.

## Generality

Everything here is at an arbitrary commutative ring and an arbitrary alphabet with `DecidableEq`;
no finiteness, no linear order, no parameters, and in particular none of the genericity in `q` and
`u` that the Macdonald layer spends. No proof below uses subtraction or negation, so each statement
also holds verbatim at a `CommSemiring`; the `CommRing` is inherited from where `splitAt` is
declared (`HJO/Macdonald/PairFactors.lean`), whose own consumers need a domain.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

variable {σ R : Type*} [CommRing R] [DecidableEq σ] {l : σ}

/-! ### The bridge -/

/-- **The coefficient bridge for `splitAt`.** The coefficient of `x^m` in the coefficient of
`x_l^k` of `splitAt l p` is the coefficient of `x^m x_l^k` in `p`, where `m` — an exponent on the
alphabet `{b // b ≠ l}` — is pushed forward to `σ` along `Subtype.val`.

This is Mathlib's `MvPolynomial.optionEquivLeft_coeff_coeff` after the renaming that `splitAt`
is built from; the work is the identification of the two exponents. -/
theorem splitAt_coeff_coeff (p : MvPolynomial σ R) (k : ℕ) (m : {b : σ // b ≠ l} →₀ ℕ) :
    coeff m (Polynomial.coeff (splitAt (R := R) l p) k)
      = coeff (Finsupp.mapDomain Subtype.val m + Finsupp.single l k) p := by
  rw [splitAt]
  simp only [AlgEquiv.trans_apply, renameEquiv_apply]
  rw [optionEquivLeft_coeff_coeff, ← coeff_rename_mapDomain (f := (Equiv.optionSubtypeNe l).symm)
    (Equiv.injective _) p (Finsupp.mapDomain Subtype.val m + Finsupp.single l k)]
  congr 1
  rw [← Finsupp.equivMapDomain_eq_mapDomain]
  ext a
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm]
  cases a with
  | none =>
    rw [Equiv.optionSubtypeNe_none, Finsupp.add_apply,
      Finsupp.mapDomain_of_notMem_range _ _ (by simp), Finsupp.single_eq_same,
      Finsupp.optionElim_apply_none, zero_add]
  | some b =>
    rw [Equiv.optionSubtypeNe_some, Finsupp.add_apply,
      Finsupp.mapDomain_apply Subtype.val_injective, Finsupp.single_eq_of_ne b.2,
      Finsupp.optionElim_apply_some, add_zero]

/-- The support of the coefficient of `x_l^k`, read on the other side of the split. -/
theorem mem_support_coeff_splitAt {p : MvPolynomial σ R} {k : ℕ} {m : {b : σ // b ≠ l} →₀ ℕ} :
    m ∈ (Polynomial.coeff (splitAt (R := R) l p) k).support ↔
      Finsupp.mapDomain Subtype.val m + Finsupp.single l k ∈ p.support := by
  simp only [mem_support_iff, splitAt_coeff_coeff]

/-- **A polynomial in the small alphabet is a constant in `x_l`.** -/
theorem splitAt_rename_val (g : MvPolynomial {b : σ // b ≠ l} R) :
    splitAt (R := R) l (rename Subtype.val g) = Polynomial.C g := by
  induction g using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p b hp =>
    rw [map_mul, map_mul, hp, rename_X, splitAt_X_of_ne b.2, Polynomial.C_mul]

/-- `splitAt` back-substituted: `Polynomial.C g` is `g` renamed into the big alphabet. -/
theorem splitAt_symm_C (g : MvPolynomial {b : σ // b ≠ l} R) :
    (splitAt (R := R) l).symm (Polynomial.C g) = rename Subtype.val g := by
  rw [← splitAt_rename_val (R := R) (l := l) g, AlgEquiv.symm_apply_apply]

/-! ### The degree in `x_l` -/

/-- **The degree of `splitAt l p` is the degree of `p` in the variable `x_l`.** Mathlib's
`MvPolynomial.degreeOf_eq_natDegree`, stated for `splitAt`. -/
theorem natDegree_splitAt (p : MvPolynomial σ R) :
    (splitAt (R := R) l p).natDegree = p.degreeOf l := by
  rw [degreeOf_eq_natDegree]
  rfl

/-- **An entrywise bound on the support at `l` bounds the degree in `x_l`.** This is the form in
which `HJO.Mac.apply_le_partExp_of_mem_support_macPpoly` is consumed. -/
theorem natDegree_splitAt_le {p : MvPolynomial σ R} {B : ℕ} (h : ∀ c ∈ p.support, c l ≤ B) :
    (splitAt (R := R) l p).natDegree ≤ B := by
  rw [natDegree_splitAt]
  exact degreeOf_le_iff.mpr h

/-- Above the bound the coefficients vanish. -/
theorem coeff_splitAt_eq_zero {p : MvPolynomial σ R} {B k : ℕ} (h : ∀ c ∈ p.support, c l ≤ B)
    (hk : B < k) : Polynomial.coeff (splitAt (R := R) l p) k = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt ((natDegree_splitAt_le h).trans_lt hk)

/-! ### The extracted coefficient is symmetric and homogeneous -/

/-- A permutation of `{b // b ≠ l}`, extended to `σ` by fixing `l`, moves a letter of the small
alphabet as the permutation does. -/
theorem extendDomain_val (w : Equiv.Perm {b : σ // b ≠ l}) (b : {b : σ // b ≠ l}) :
    w.extendDomain (Equiv.refl {b : σ // b ≠ l}) b.1 = (w b).1 := by
  rw [Equiv.Perm.extendDomain_apply_subtype (p := fun x : σ => x ≠ l) w (Equiv.refl _) b.2]
  simp

/-- A permutation of `{b // b ≠ l}`, extended to `σ`, fixes `l`. -/
theorem extendDomain_self (w : Equiv.Perm {b : σ // b ≠ l}) :
    w.extendDomain (Equiv.refl {b : σ // b ≠ l}) l = l :=
  Equiv.Perm.extendDomain_apply_not_subtype (p := fun x : σ => x ≠ l) w (Equiv.refl _) (by simp)

/-- The extension acts on the exponent `x^m x_l^k` by permuting `m` and fixing the `x_l`-part. -/
theorem mapDomain_extendDomain (w : Equiv.Perm {b : σ // b ≠ l}) (m : {b : σ // b ≠ l} →₀ ℕ)
    (k : ℕ) :
    Finsupp.mapDomain (w.extendDomain (Equiv.refl {b : σ // b ≠ l}))
        (Finsupp.mapDomain Subtype.val m + Finsupp.single l k)
      = Finsupp.mapDomain Subtype.val (Finsupp.mapDomain w m) + Finsupp.single l k := by
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, extendDomain_self,
    ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 2
  funext b
  exact extendDomain_val w b

/-- **The coefficient of `x_l^k` in a symmetric polynomial is symmetric in the other letters.**
A permutation `w` of `{b // b ≠ l}` extends to a permutation of `σ` fixing `l`; that extension
fixes `p`, and under the bridge it acts on the exponents of the extracted coefficient exactly as
`w` does. -/
theorem isSymmetric_coeff_splitAt {p : MvPolynomial σ R} (hp : p.IsSymmetric) (k : ℕ) :
    (Polynomial.coeff (splitAt (R := R) l p) k).IsSymmetric := by
  intro w
  refine MvPolynomial.ext _ _ fun m => ?_
  set W : Equiv.Perm σ := w.extendDomain (Equiv.refl {b : σ // b ≠ l}) with hW
  have key : ∀ c : {b : σ // b ≠ l} →₀ ℕ,
      coeff (Finsupp.mapDomain w c) (Polynomial.coeff (splitAt (R := R) l p) k)
        = coeff c (Polynomial.coeff (splitAt (R := R) l p) k) := fun c => by
    have h := coeff_rename_mapDomain (⇑W) W.injective p
      (Finsupp.mapDomain Subtype.val c + Finsupp.single l k)
    rw [hp W] at h
    rw [splitAt_coeff_coeff, splitAt_coeff_coeff, ← mapDomain_extendDomain w c k, ← hW, h]
  have hm : m = Finsupp.mapDomain w (Finsupp.mapDomain w.symm m) := by
    rw [← Finsupp.mapDomain_comp]
    simp
  rw [hm, coeff_rename_mapDomain (⇑w) w.injective, key]

/-- **The coefficient of `x_l^k` in a homogeneous polynomial of degree `d` is homogeneous of
degree `j`, where `k + j = d`.** The hypothesis is an equation rather than `j = d - k`: `ℕ`
subtraction truncates, and the subtracted form is satisfied vacuously when `d < k`. -/
theorem isHomogeneous_coeff_splitAt {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d)
    {k j : ℕ} (hkj : k + j = d) :
    (Polynomial.coeff (splitAt (R := R) l p) k).IsHomogeneous j := by
  intro m hm
  rw [splitAt_coeff_coeff] at hm
  have hw : (Finsupp.weight (1 : σ → ℕ))
      (Finsupp.mapDomain Subtype.val m + Finsupp.single l k)
      = (Finsupp.weight (1 : {b : σ // b ≠ l} → ℕ)) m + k := by
    have h1 : (Finsupp.weight (1 : σ → ℕ)) (Finsupp.mapDomain Subtype.val m)
        = (Finsupp.weight (1 : {b : σ // b ≠ l} → ℕ)) m := by
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
      exact Finsupp.sum_mapDomain_index_inj (h := fun _ ↦ id) Subtype.val_injective
    have h2 : (Finsupp.weight (1 : σ → ℕ)) (Finsupp.single l k) = k := by
      simp [Finsupp.weight_single]
    rw [map_add, h1, h2]
  have := hp hm
  rw [hw] at this
  omega

end HJO.Mac

end
