/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.DopCut
public import HJO.Macdonald.PpolyDegree
public import HJO.Macdonald.SplitCoeff

/-! # `P_λ[X_n]` read as a polynomial in the last variable

`HJO.Mac.coeff_partExp_splitAt_macPpoly_eq` extracts the coefficient of `x_n^{λ_1}` from `P_λ[X_n]`,
read as a polynomial in `x_n` over `𝕜[x_1,…,x_{n-1}]`, and identifies it with `P_κ[X_{n-1}]` for the
partition `κ` with `κ_i = λ_{i+1}`. This file is the part of that argument which needs no operator:
the shape of `P_λ[X_n]` in `x_n` (Step 1 of that argument) and the fact that the extracted
coefficient lies in `𝒮_{n-1,d-r}` (the conclusion drawn inside its Step 3).

Both come from `HJO/Macdonald/SplitCoeff.lean` applied to what is already known about
`P_λ[X_n]`, and neither spends any genericity in `q` and `u` beyond the `hqu` that naming
`HJO.Mac.macPpoly` already costs.

## The degree in `x_t` is `λ_1` exactly, not merely at most

Step 1 of that argument only needs `≤ λ_1`, which is `HJO.Mac.natDegree_splitAt_le` fed with
`HJO.Mac.apply_le_partExp_of_mem_support_macPpoly` at the letter `t`; that lemma was proved
entrywise at every letter, so `t` need not be the letter named in that argument. Equality is just as
cheap and is recorded because it is what makes the extracted coefficient the *leading* coefficient,
hence nonzero: `P_λ[X_n]` is symmetric, so transposing the least letter `i` with `t` carries the
exponent `\bar\lambda` — which occurs, with coefficient `1` — to an exponent whose entry at `t` is
`\bar\lambda_i = λ_1`.

Note that `t` is the letter the polynomial is read in and `i` is the least letter, which is where
`λ_1` is read off `\bar\lambda`; they are unrelated, and in the instance used there they are
the two ends of the alphabet.

## The alphabet `splitAt t` produces is itself a top extension

`splitAt t` reads the polynomial ring over the alphabet `{b : τ // b ≠ t}`, whereas the descent
machinery (`HJO.Mac.IsTopExtension`, `HJO.Mac.killComplComp_macPpoly`) is stated for an abstract
`e : σ → τ`. The two need not be reconciled by a transport along `e`:
`HJO.Mac.isTopExtension_subtypeVal` says `Subtype.val` on `{b : τ // b ≠ t}` is a top extension for
`t` as soon as `t` is the greatest letter, and `HJO.Mac.IsTopExtension.isTop` says any top extension
for `t` makes it so. A statement about the coefficient of `x_t^k` can therefore be made directly on
`{b : τ // b ≠ t}`.

## Main results

* `HJO.Mac.IsTopExtension.isTop` and `HJO.Mac.isTopExtension_subtypeVal`.
* `HJO.Mac.natDegree_splitAt_macPpoly_le` (Step 1 of that argument).
* `HJO.Mac.natDegree_splitAt_macPpoly`: the degree in `x_t` is `λ_1` exactly.
* `HJO.Mac.coeff_splitAt_macPpoly_mem`: every coefficient of `x_t^k` lies in `𝒮_{n-1,j}` for
  `k + j = d`.
* `HJO.Mac.coeff_partExp_splitAt_macPpoly_mem`: the case `k = λ_1`, which is
  `g ∈ 𝒮_{n-1,d-r}`.
* `HJO.Mac.coeff_partExp_splitAt_macPpoly_ne_zero`: that `g ≠ 0`.

## References

This file formalises the lemma `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`, Steps 1 and 3, on
Definitions `MvPolynomial.symmetricSubalgebra`, `MvPolynomial.symmetricHomogeneousSubmodule` and
`HJO.Mac.macPpoly` and Lemma `HJO.Mac.apply_le_partExp_of_mem_support_macPpoly`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ}
  {u : K} {d : ℕ}

/-! ### The alphabet `{b : τ // b ≠ t}` is a top extension -/

section TopLetter

variable {τ : Type*} [LinearOrder τ] {t : τ}

/-- **A top extension makes its new letter the greatest.** Every letter other than `t` is in the
image of `e`, and every letter in the image is below `t`. -/
theorem IsTopExtension.isTop {σ : Type*} [LinearOrder σ] {e : σ → τ} (hd : IsTopExtension e t) :
    IsTop t := fun b => by
  rcases eq_or_ne b t with rfl | hb
  · exact le_rfl
  · obtain ⟨a, ha⟩ := hd.exists_eq hb
    exact (ha ▸ hd.lt_top a).le

/-- **`{b : τ // b ≠ t}` with its inclusion is a top extension for `t`**, as soon as `t` is the
greatest letter. This is the alphabet `HJO.Mac.splitAt t` produces, so a statement about the
coefficient of `x_t^k` can be made on it directly rather than transported along an abstract
`e : σ → τ`. -/
theorem isTopExtension_subtypeVal (ht : IsTop t) :
    IsTopExtension (Subtype.val : {b : τ // b ≠ t} → τ) t where
  strictMono := fun _ _ h => h
  lt_top := fun a => lt_of_le_of_ne (ht a.1) a.2
  exists_eq := fun {_} hb => ⟨⟨_, hb⟩, rfl⟩

omit [LinearOrder τ] in
/-- The small alphabet has one letter fewer. -/
theorem card_subtype_ne [Fintype τ] [DecidableEq τ] (t : τ) :
    Fintype.card {b : τ // b ≠ t} = Fintype.card τ - 1 := by
  simp [Fintype.card_subtype_compl]

end TopLetter

/-! ### Every part is at most the size -/

/-- A part of a partition of `d` is at most `d`. -/
theorem partExp_le (μ : PartIdx σ d) (i : σ) : partExp σ μ i ≤ d :=
  (Finsupp.le_degree i (partExp σ μ)).trans_eq (degree_partExp μ)

/-! ### The shape of `P_λ[X_n]` in one variable -/

/-- **The degree of `P_λ[X_n]` in `x_t` is at most `λ_1`**, Step 1 of the proof of
`HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`. Here `i` is the least letter of the alphabet, so
`partExp σ μ i` is `λ_1`, and `t` is the letter the polynomial is read in; the two are unrelated.
This is `HJO.Mac.natDegree_splitAt_le` fed with `HJO.Mac.apply_le_partExp_of_mem_support_macPpoly`,
which bounds the exponent entry at *every* letter. -/
theorem natDegree_splitAt_macPpoly_le (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) {i : σ} (hi : IsBot i) (t : σ) :
    (splitAt t (macPpoly hqu μ : MvPolynomial σ K)).natDegree ≤ partExp σ μ i :=
  natDegree_splitAt_le fun _ hc => apply_le_partExp_of_mem_support_macPpoly hqu μ hc hi t

/-- **The degree of `P_λ[X_n]` in `x_t` is `λ_1` exactly.** For `≥`: `P_λ[X_n]` is symmetric, so
transposing the least letter `i` with `t` carries the exponent `\bar\lambda`, which occurs, to one
whose entry at `t` is `\bar\lambda_i`. -/
theorem natDegree_splitAt_macPpoly (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) {i : σ} (hi : IsBot i) (t : σ) :
    (splitAt t (macPpoly hqu μ : MvPolynomial σ K)).natDegree = partExp σ μ i := by
  refine le_antisymm (natDegree_splitAt_macPpoly_le hqu μ hi t) ?_
  rw [natDegree_splitAt, degreeOf_eq_sup]
  have hmem : Finsupp.mapDomain (Equiv.swap i t) (partExp σ μ)
      ∈ (macPpoly hqu μ : MvPolynomial σ K).support := by
    rw [mem_support_iff,
      IsSymmetric.coeff_mapDomain (mem_symmetricHomogeneousSubmodule.1 (macPpoly hqu μ).2).1,
      coeff_partExp_macPpoly]
    exact one_ne_zero
  have hval : Finsupp.mapDomain (Equiv.swap i t) (partExp σ μ) t = partExp σ μ i := by
    rw [← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply, Equiv.symm_swap,
      Equiv.swap_apply_right]
  exact hval ▸ Finset.le_sup (f := fun m : σ →₀ ℕ => m t) hmem

/-- Above `λ_1` the coefficients of `P_λ[X_n]` in `x_t` vanish, which is the other half of
`f = ∑_{k ≤ r} x_n^k g_k`. -/
theorem coeff_splitAt_macPpoly_eq_zero (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) {i : σ} (hi : IsBot i) (t : σ) {k : ℕ} (hk : partExp σ μ i < k) :
    Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K)) k = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt ((natDegree_splitAt_macPpoly_le hqu μ hi t).trans_lt hk)

/-! ### The extracted coefficient lies in `𝒮_{n-1,d-r}` -/

/-- **Each coefficient of `x_t^k` in `P_λ[X_n]` is symmetric in the other letters and homogeneous
of degree `j`, where `k + j = d`.** Step 3 of the proof of
`HJO.Mac.coeff_partExp_splitAt_macPpoly_eq` deduces exactly this for `k = λ_1`.

The hypothesis is the equation `k + j = d`, not `j = d - k`: `ℕ` subtraction truncates, so the
subtracted form is satisfied vacuously whenever `d < k`. -/
theorem coeff_splitAt_macPpoly_mem (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) (t : σ) {k j : ℕ} (hkj : k + j = d) :
    Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K)) k
      ∈ symmetricHomogeneousSubmodule {b : σ // b ≠ t} K j := by
  obtain ⟨hs, hh⟩ := mem_symmetricHomogeneousSubmodule.1 (macPpoly hqu μ).2
  exact mem_symmetricHomogeneousSubmodule.2
    ⟨isSymmetric_coeff_splitAt hs k, isHomogeneous_coeff_splitAt hh hkj⟩

/-- **The `g ∈ 𝒮_{n-1,d-r}`.** The subtraction is safe here: `λ_1 ≤ d`. -/
theorem coeff_partExp_splitAt_macPpoly_mem (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) (i t : σ) :
    Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K)) (partExp σ μ i)
      ∈ symmetricHomogeneousSubmodule {b : σ // b ≠ t} K (d - partExp σ μ i) :=
  coeff_splitAt_macPpoly_mem hqu μ t (Nat.add_sub_cancel' (partExp_le μ i))

/-- **`g` is nonzero**, being the leading coefficient of a nonzero polynomial: the degree in `x_t`
is `λ_1` exactly. -/
theorem coeff_partExp_splitAt_macPpoly_ne_zero (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) {i : σ} (hi : IsBot i) (t : σ) :
    Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K)) (partExp σ μ i) ≠ 0 := by
  have h0 : (macPpoly hqu μ : MvPolynomial σ K) ≠ 0 := fun h => by
    simpa [h] using coeff_partExp_macPpoly hqu μ
  rw [← natDegree_splitAt_macPpoly hqu μ hi t]
  exact Polynomial.leadingCoeff_ne_zero.2 (by simpa using h0)

end HJO.Mac

end
