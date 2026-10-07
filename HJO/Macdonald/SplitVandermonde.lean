/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.DopCut
public import HJO.Macdonald.SplitCoeff
public import HJO.Macdonald.Triangular

/-! # The Vandermonde product under `splitAt`

The Vandermonde half of Step 2 of the proof of `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`: read
`𝒱_S = ∏_{k < l}(x_k - x_l)` as a polynomial in the greatest variable `x_t`, and say what its
degree and leading coefficient are.

Everything reduces to one decomposition. If `t` is the greatest letter and `S` is a set of letters
of the small alphabet `{b : σ // b ≠ t}`, then adjoining `t` to `S` contributes exactly the factors
`x_b - x_t` for `b ∈ S` — the factors with `t` on the *right*, there being none with `t` on the
left — so

`𝒱_{insert t S} = (∏_{b ∈ S}(x_b - x_t)) · 𝒱_S`,

and under `splitAt t` the first factor becomes `∏_{b ∈ S}(C x_b - X)`, of degree `#S` and leading
coefficient `(-1)^{#S}`, while the second becomes the *constant* `C 𝒱_S`, being a polynomial in the
small alphabet only.

## Where the two halves come from

`HJO.Mac.vandermondeProd_image_val` is `Finset.vandermondeProd_image` (`DopCut.lean`) at
`e = Subtype.val`, which is `StrictMono` because the order on `{b // b ≠ t}` is the one induced
from `σ`; it identifies `𝒱` over `S.image Subtype.val ⊆ σ` with `𝒱` over `S ⊆ {b // b ≠ t}` renamed
along `Subtype.val`, and then `HJO.Mac.splitAt_rename_val` turns that into a `Polynomial.C`.

`HJO.Mac.vandermondeProd_insert_top` is `Finset.vandermondeProd_insert` with the two filters
evaluated: `{l ∈ S | t < l}` is empty and `{k ∈ S | k < t}` is all of `S`, both because `t` is
greatest. This is the only place `IsTop t` is spent, and it is spent essentially — at a letter in
the middle of the alphabet both filters are nontrivial and the product does not factor this way.

## No `ℕ` subtraction

The usual proof reads the coefficient of `x_n^{n-1}`, and of `x_n^{n-2}` for the erased product.
The statements here are indexed by `Fintype.card {b : σ // b ≠ t}` and by the cardinality of an
erased `Finset` instead. These *are* `n-1` and `n-2` (`HJO.Mac.card_subtype_ne`,
`Finset.card_erase_of_mem`) but are not written as truncated subtractions, so the statements say
what they mean with no positivity hypothesis on `Fintype.card σ`.

## Main results

* `HJO.Mac.splitAt_vandermondeProd_image`: `𝒱` of the small alphabet is a constant in `x_t`.
* `HJO.Mac.splitAt_vandermondeProd_insert_top`: the decomposition, under the split, with
  `natDegree_splitAt_vandermondeProd_insert_top` and
  `leadingCoeff_splitAt_vandermondeProd_insert_top`.
* `HJO.Mac.natDegree_prod_C_sub_X`, `HJO.Mac.leadingCoeff_prod_C_sub_X`.
* `HJO.Mac.splitAt_vandermondeProd_univ` and its degree and leading coefficient: the
  product `𝒱_N` has degree `n-1` in `x_n`, with `(-1)^{n-1}𝒱_{N'}` there.
* `HJO.Mac.splitAt_vandermondeProd_erase` and its degree and leading coefficient: the
  product `𝒱_{N∖{i}}` for `i ≠ n` has degree `n-2` in `x_n`, with `(-1)^{n-2}𝒱_{N'∖{i}}` there.

## References

This is Step 2 of the proof of `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`, about Macdonald's
polynomials, on `Finset.vandermondeProd`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

/-! ### A product of linear factors `C a - X` -/

section Linear

variable {R : Type*} [CommRing R] {ι : Type*}

theorem leadingCoeff_C_sub_X (a : R) :
    (Polynomial.C a - Polynomial.X : Polynomial R).leadingCoeff = -1 := by
  rw [← neg_sub, Polynomial.leadingCoeff_neg, Polynomial.monic_X_sub_C a]

theorem natDegree_C_sub_X [Nontrivial R] (a : R) :
    (Polynomial.C a - Polynomial.X : Polynomial R).natDegree = 1 := by
  rw [← neg_sub, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]

theorem C_sub_X_ne_zero [Nontrivial R] (a : R) :
    (Polynomial.C a - Polynomial.X : Polynomial R) ≠ 0 := by
  rw [← neg_sub, neg_ne_zero]
  exact Polynomial.X_sub_C_ne_zero a

theorem prod_C_sub_X_ne_zero [IsDomain R] (S : Finset ι) (a : ι → R) :
    (∏ i ∈ S, (Polynomial.C (a i) - Polynomial.X)) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => C_sub_X_ne_zero (a i)

/-- **A product of `#S` linear factors `C a - X` has degree `#S`.** -/
theorem natDegree_prod_C_sub_X [IsDomain R] (S : Finset ι) (a : ι → R) :
    (∏ i ∈ S, (Polynomial.C (a i) - Polynomial.X)).natDegree = S.card := by
  rw [Polynomial.natDegree_prod _ _ fun i _ => C_sub_X_ne_zero (a i),
    Finset.sum_congr rfl (fun i _ => natDegree_C_sub_X (a i) :
      ∀ i ∈ S, (Polynomial.C (a i) - Polynomial.X : Polynomial R).natDegree = 1)]
  simp

/-- **Its leading coefficient is `(-1)^{#S}`**, each factor contributing `-1`. -/
theorem leadingCoeff_prod_C_sub_X [IsDomain R] (S : Finset ι) (a : ι → R) :
    (∏ i ∈ S, (Polynomial.C (a i) - Polynomial.X)).leadingCoeff = (-1) ^ S.card := by
  rw [Polynomial.leadingCoeff_prod]
  exact (Finset.prod_congr rfl fun i _ => leadingCoeff_C_sub_X (a i)).trans (Finset.prod_const _)

end Linear

/-! ### The Vandermonde product of the small alphabet -/

section Split

variable {σ K : Type*} [Field K] [LinearOrder σ] {t : σ}

/-- **`𝒱` over a set of small letters, pushed into the big alphabet, is `𝒱` renamed.**
`Finset.vandermondeProd_image` at `e = Subtype.val`, which is `StrictMono` because the order on
`{b // b ≠ t}` is the one induced from `σ`. -/
theorem vandermondeProd_image_val (S : Finset {b : σ // b ≠ t}) :
    (S.image Subtype.val).vandermondeProd (X : σ → MvPolynomial σ K)
      = rename Subtype.val (S.vandermondeProd X) := by
  rw [Finset.vandermondeProd_image (e := (Subtype.val : {b : σ // b ≠ t} → σ))
    (fun _ _ h => h) S X]
  simp [Finset.vandermondeProd, map_prod]

/-- **`𝒱` of the small alphabet is a constant in `x_t`**: it does not mention `x_t` at all. -/
theorem splitAt_vandermondeProd_image (S : Finset {b : σ // b ≠ t}) :
    splitAt t ((S.image Subtype.val).vandermondeProd (X : σ → MvPolynomial σ K))
      = Polynomial.C (S.vandermondeProd X) := by
  rw [vandermondeProd_image_val, splitAt_rename_val]

/-! ### Adjoining the greatest letter -/

/-- **Adjoining the greatest letter `t` to `S` contributes exactly the factors `x_b - x_t`.** There
are no factors with `t` on the left, `t` being greatest, and every letter of `S` gives one with `t`
on the right. This is the one place `IsTop t` is spent, and it is spent essentially. -/
theorem vandermondeProd_insert_top (ht : IsTop t) (S : Finset {b : σ // b ≠ t}) :
    (insert t (S.image Subtype.val)).vandermondeProd (X : σ → MvPolynomial σ K)
      = (∏ b ∈ S, (X (b : σ) - X t)) * rename Subtype.val (S.vandermondeProd X) := by
  have hnot : t ∉ S.image Subtype.val := by simp
  have h1 : {l ∈ S.image Subtype.val | t < l} = ∅ :=
    Finset.filter_eq_empty_iff.2 fun {b} _ hlt => absurd (ht b) (not_le_of_gt hlt)
  have h2 : {k ∈ S.image Subtype.val | k < t} = S.image Subtype.val :=
    Finset.filter_true_of_mem fun b hb => by
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hb
      exact lt_of_le_of_ne (ht _) c.2
  rw [Finset.vandermondeProd_insert hnot, h1, h2, Finset.prod_empty, one_mul,
    Finset.prod_image fun x _ y _ h => Subtype.ext h, vandermondeProd_image_val]

/-- **The decomposition, read in `x_t`.** The adjoined factors become `∏_{b ∈ S}(C x_b - X)` and
the rest becomes the constant `C 𝒱_S`. -/
theorem splitAt_vandermondeProd_insert_top (ht : IsTop t) (S : Finset {b : σ // b ≠ t}) :
    splitAt t ((insert t (S.image Subtype.val)).vandermondeProd (X : σ → MvPolynomial σ K))
      = (∏ b ∈ S, (Polynomial.C (X b) - Polynomial.X)) * Polynomial.C (S.vandermondeProd X) := by
  rw [vandermondeProd_insert_top ht, map_mul, splitAt_rename_val, map_prod]
  refine congrArg (· * _) (Finset.prod_congr rfl fun b _ => ?_)
  rw [map_sub, splitAt_X_of_ne b.2, splitAt_X_self]

section Degree

variable [Finite σ]

/-- The degree in `x_t` is `#S`: the `C 𝒱_S` factor is a nonzero constant. -/
theorem natDegree_splitAt_vandermondeProd_insert_top (ht : IsTop t)
    (S : Finset {b : σ // b ≠ t}) :
    (splitAt t ((insert t (S.image Subtype.val)).vandermondeProd
      (X : σ → MvPolynomial σ K))).natDegree = S.card := by
  rw [splitAt_vandermondeProd_insert_top ht,
    Polynomial.natDegree_mul (prod_C_sub_X_ne_zero S _)
      (Polynomial.C_ne_zero.2 (vandermondeProd_ne_zero S)),
    natDegree_prod_C_sub_X, Polynomial.natDegree_C, add_zero]

omit [Finite σ] in
/-- The coefficient there is `(-1)^{#S}𝒱_S`. `Polynomial.leadingCoeff_mul` needs no nonvanishing,
the coefficient ring being a domain, so unlike the degree this needs no finiteness. -/
theorem leadingCoeff_splitAt_vandermondeProd_insert_top (ht : IsTop t)
    (S : Finset {b : σ // b ≠ t}) :
    (splitAt t ((insert t (S.image Subtype.val)).vandermondeProd
      (X : σ → MvPolynomial σ K))).leadingCoeff = (-1) ^ S.card * S.vandermondeProd X := by
  rw [splitAt_vandermondeProd_insert_top ht, Polynomial.leadingCoeff_mul,
    leadingCoeff_prod_C_sub_X, Polynomial.leadingCoeff_C]

end Degree

/-! ### The two instances used -/

section Univ

variable [Fintype σ]

/-- The whole alphabet is the small one with `t` put back. -/
theorem univ_eq_insert_image (t : σ) :
    (Finset.univ : Finset σ)
      = insert t ((Finset.univ : Finset {b : σ // b ≠ t}).image Subtype.val) := by
  refine Finset.ext fun b => ?_
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_image, true_and]
  rcases eq_or_ne b t with rfl | hb
  · exact Or.inl rfl
  · exact Or.inr ⟨⟨b, hb⟩, rfl⟩

/-- Erasing a letter `i ≠ t` from the whole alphabet is erasing it from the small one, with `t` put
back. -/
theorem erase_eq_insert_image {i : σ} (h : i ≠ t) :
    (Finset.univ : Finset σ).erase i
      = insert t (((Finset.univ : Finset {b : σ // b ≠ t}).erase ⟨i, h⟩).image Subtype.val) := by
  refine Finset.ext fun b => ?_
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_insert, Finset.mem_image]
  rcases eq_or_ne b t with rfl | hb
  · exact ⟨fun _ => Or.inl rfl, fun _ => Ne.symm h⟩
  · refine ⟨fun hbi => Or.inr ⟨⟨b, hb⟩, fun hc => hbi (congrArg Subtype.val hc), rfl⟩, ?_⟩
    rintro (rfl | ⟨c, hc, rfl⟩)
    · exact absurd rfl hb
    · exact fun hbi => hc (Subtype.ext hbi)

/-- **`𝒱_N` read in the greatest variable.** -/
theorem splitAt_vandermondeProd_univ (ht : IsTop t) :
    splitAt t ((Finset.univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ K))
      = (∏ b : {b : σ // b ≠ t}, (Polynomial.C (X b) - Polynomial.X)) *
          Polynomial.C ((Finset.univ : Finset {b : σ // b ≠ t}).vandermondeProd X) := by
  rw [univ_eq_insert_image t, splitAt_vandermondeProd_insert_top ht]

/-- **`𝒱_N` has degree `n-1` in the greatest variable**, written without a truncated
subtraction. -/
theorem natDegree_splitAt_vandermondeProd_univ (ht : IsTop t) :
    (splitAt t ((Finset.univ : Finset σ).vandermondeProd
      (X : σ → MvPolynomial σ K))).natDegree = Fintype.card {b : σ // b ≠ t} := by
  rw [univ_eq_insert_image t, natDegree_splitAt_vandermondeProd_insert_top ht, Finset.card_univ]

/-- **The coefficient there is `(-1)^{n-1}𝒱_{N'}`.** -/
theorem leadingCoeff_splitAt_vandermondeProd_univ (ht : IsTop t) :
    (splitAt t ((Finset.univ : Finset σ).vandermondeProd
        (X : σ → MvPolynomial σ K))).leadingCoeff
      = (-1) ^ Fintype.card {b : σ // b ≠ t} *
          (Finset.univ : Finset {b : σ // b ≠ t}).vandermondeProd X := by
  rw [univ_eq_insert_image t, leadingCoeff_splitAt_vandermondeProd_insert_top ht,
    Finset.card_univ]

/-- **`𝒱_{N∖{i}}` read in the greatest variable, for `i ≠ t`.** -/
theorem splitAt_vandermondeProd_erase (ht : IsTop t) {i : σ} (h : i ≠ t) :
    splitAt t (((Finset.univ : Finset σ).erase i).vandermondeProd (X : σ → MvPolynomial σ K))
      = (∏ b ∈ (Finset.univ : Finset {b : σ // b ≠ t}).erase ⟨i, h⟩,
            (Polynomial.C (X b) - Polynomial.X)) *
          Polynomial.C
            (((Finset.univ : Finset {b : σ // b ≠ t}).erase ⟨i, h⟩).vandermondeProd X) := by
  rw [erase_eq_insert_image h, splitAt_vandermondeProd_insert_top ht]

/-- **`𝒱_{N∖{i}}` has degree `n-2` in the greatest variable**, written without a truncated
subtraction: the small alphabet with one more letter erased. -/
theorem natDegree_splitAt_vandermondeProd_erase (ht : IsTop t) {i : σ} (h : i ≠ t) :
    (splitAt t (((Finset.univ : Finset σ).erase i).vandermondeProd
        (X : σ → MvPolynomial σ K))).natDegree
      = ((Finset.univ : Finset {b : σ // b ≠ t}).erase ⟨i, h⟩).card := by
  rw [erase_eq_insert_image h, natDegree_splitAt_vandermondeProd_insert_top ht]

/-- **The coefficient there is `(-1)^{n-2}𝒱_{N'∖{i}}`.** -/
theorem leadingCoeff_splitAt_vandermondeProd_erase (ht : IsTop t) {i : σ} (h : i ≠ t) :
    (splitAt t (((Finset.univ : Finset σ).erase i).vandermondeProd
        (X : σ → MvPolynomial σ K))).leadingCoeff
      = (-1) ^ ((Finset.univ : Finset {b : σ // b ≠ t}).erase ⟨i, h⟩).card *
          ((Finset.univ : Finset {b : σ // b ≠ t}).erase ⟨i, h⟩).vandermondeProd X := by
  rw [erase_eq_insert_image h, leadingCoeff_splitAt_vandermondeProd_insert_top ht]

end Univ

end Split

end HJO.Mac

end
