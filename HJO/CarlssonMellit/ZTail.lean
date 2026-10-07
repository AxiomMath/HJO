/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PowerRing
public import HJO.DyckWordMonomial
public meta import HJO.Attr

/-! # The free part of a labelling monomial

A labelling `w` of the `N` positions of a partial Dyck path of level `k` contributes to the
characteristic function `ν_σ(π)` the monomial

`z^{(k)}_{w,♭} = ∏_{i=k+1}^{N} z^{(k)}_{w_i} ∈ P_k`

in the merged variables `HJO.Sym.zvar`: the product over the positions *at or above the level*, the
first `k` positions — whose letters `σ` prescribes — being dropped. That is
`HJO.Sym.ztail`, and this file defines it.

The word *free* is the point of the truncation. Carlsson and Mellit's `χ'_σ(π)` keeps the first `k`
factors, which for a `σ` permuting `{1, …, k}` are `z^{(k)}_{σ_1} ⋯ z^{(k)}_{σ_k} = y_1 ⋯ y_k` for
*every* labelling; dropping them divides `χ'_σ(π)` by `y_1 ⋯ y_k` without having to prove a
divisibility, which is what makes `ν_σ(π)` rather than `χ'_σ(π)` the object the recursions are
stated at.

## Main definitions

* `HJO.Sym.ztail`: `z^{(k)}_{w,♭}`.
* `HJO.Sym.zvarExponent`, `HJO.Sym.zvarCoeff`: the merged variable `z^{(k)}_j` read as a monomial —
  the exponent it contributes to the alphabet and the coefficient it contributes in
  `𝕜[y_1, …, y_k]`.
* `HJO.Sym.ztailExponent`, `HJO.Sym.ztailCoeff`: the same for `z^{(k)}_{w,♭}`.

## Main results

* `HJO.Sym.ztail_eq_monomial` and `HJO.Sym.coeff_ztail`: `z^{(k)}_{w,♭}` is a *monomial* of `P_k`,
  with exponent `ztailExponent` in the alphabet and coefficient `ztailCoeff` in `𝕜[y_1, …, y_k]`.
  This is what makes the sum `ν_σ(π) = ∑_w q ^ inv · z^{(k)}_{w,♭}` a well-defined element of `P_k`
  although it has infinitely many terms: only the finitely many `w` with a given `ztailExponent`
  contribute to a given monomial of the alphabet.
* `HJO.Sym.ztail_of_le`: below the level there is nothing to take, and the value is `1`.
* `HJO.Sym.ztail_zero_level`: at level `0` the free part is the whole labelling monomial `x_w` of
  `HJO.Sym.wordMonomial`.

## Implementation notes

*No hypothesis `N ≥ k`.* The product runs over the positions `i` of `Fin N` with `k ≤ i`, which is
empty when `N ≤ k`, so the definition is total and `HJO.Sym.ztail_of_le` records the value there.
The condition `N ≥ k` is the standing hypothesis of the construction, not a side condition
of this product.

*Positions and letters are indexed from `0`*, as everywhere in this part of the library, so the
product over `k + 1 ≤ i ≤ N` is the product over `k ≤ i < N` and its `z^{(k)}_{w_i}` is
`zvar K k (w i)` with `HJO.Sym.zvar`'s own `0`-based convention: `zvar K k j` is `y_{j+1}` exactly
for `j < k`.

*The monomial decomposition is stated through two auxiliary functions rather than by a
`Finsupp`-valued formula with a case split inside.* `zvarExponent k j` is `0` below the level and
`single (j - k) 1` at or above it, and `zvarCoeff K k j` is `y_{j+1}` below and `1` above; the two
are multiplicative in the sense that the product of the monomials is the monomial of the sum and the
product, which is `HJO.Sym.prod_monomial_eq_monomial`. A proof extracting the alphabet exponent
of `z^{(k)}_{w,♭}` — which is what a coefficientwise definition of `ν_σ(π)` must do — reads
`ztailExponent`, and the coefficient in `𝕜[y]` is `ztailCoeff`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4, where the monomial is
`z^{(k)}_w` with its special factors divided out. Used by `HJO.Dyck.partialCharSeries`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

variable {K : Type*} [CommRing K]

/-! ### A product of monomials -/

/-- A finite product of monomials of a formal power series ring is the monomial at the sum of the
exponents with the product of the coefficients. -/
theorem prod_monomial_eq_monomial {A : Type*} [CommRing A] {ι : Type*} (s : Finset ι)
    (e : ι → (ℕ →₀ ℕ)) (c : ι → A) :
    (∏ i ∈ s, MvPowerSeries.monomial (e i) (c i) : MvPowerSeries ℕ A) =
      MvPowerSeries.monomial (∑ i ∈ s, e i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha, ih,
      MvPowerSeries.monomial_mul_monomial]

/-! ### The merged variable as a monomial -/

/-- The exponent that the merged variable `z^{(k)}_{j+1}` contributes to the alphabet: nothing below
the level, where it is an auxiliary variable, and the letter `x_{j+1-k}` at or above it. -/
noncomputable def zvarExponent (k j : ℕ) : ℕ →₀ ℕ :=
  if j < k then 0 else Finsupp.single (j - k) 1

/-- The coefficient that the merged variable `z^{(k)}_{j+1}` contributes in `𝕜[y_1, …, y_k]`: the
auxiliary variable `y_{j+1}` below the level, and `1` at or above it. -/
noncomputable def zvarCoeff (K : Type*) [CommRing K] (k j : ℕ) : MvPolynomial (Fin k) K :=
  if h : j < k then MvPolynomial.X ⟨j, h⟩ else 1

/-- **The merged variable is a monomial of `P_k`**, with exponent `HJO.Sym.zvarExponent` in the
alphabet and coefficient `HJO.Sym.zvarCoeff` in the auxiliary variables. -/
theorem zvar_eq_monomial (K : Type*) [CommRing K] (k j : ℕ) :
    zvar K k j = MvPowerSeries.monomial (zvarExponent k j) (zvarCoeff K k j) := by
  by_cases h : j < k
  · rw [zvar_of_lt h]
    simp only [zvarExponent, zvarCoeff, h, ↓reduceIte, ↓reduceDIte]
    exact (MvPowerSeries.monomial_zero_eq_C_apply _).symm
  · rw [zvar_of_le (Nat.not_lt.1 h)]
    simp only [zvarExponent, zvarCoeff, h, ↓reduceIte, ↓reduceDIte]
    rw [MvPowerSeries.X]

/-! ### The free part of a labelling monomial -/

/-- **The free part `z^{(k)}_{w,♭}` of the labelling monomial of `w`**: the product of the merged
variables `z^{(k)}_{w_i}` over the positions `i` at or above the level `k`, that is,
`∏_{i=k+1}^{N} z^{(k)}_{w_i}`. The first `k` positions, whose letters the tuple `σ` of special
values prescribes, contribute nothing; that truncation is what divides Carlsson and Mellit's
`χ'_σ(π)` by `y_1 ⋯ y_k`.

Total in `N` and `k`: when `N ≤ k` there are no positions at or above the level and the value is the
empty product `1` (`HJO.Sym.ztail_of_le`). -/
@[hjo "def_cm_ztail"]
noncomputable def ztail (K : Type*) [CommRing K] (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
    AuxAlphabetSeries K k :=
  ∏ i ∈ {i : Fin N | k ≤ (i : ℕ)}, zvar K k (w i)

theorem ztail_apply (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
    ztail K k w = ∏ i ∈ {i : Fin N | k ≤ (i : ℕ)}, zvar K k (w i) :=
  rfl

/-- Below the level there is nothing to take: a labelling of `N ≤ k` positions has free part `1`.
This is the value at the empty path, where the level and the length are both `0`. -/
@[simp]
theorem ztail_of_le {k N : ℕ} (h : N ≤ k) (w : Fin N → ℕ) : ztail K k w = 1 := by
  refine Finset.prod_eq_one fun i hi => absurd (mem_filter_univ i |>.1 hi) ?_
  have := i.isLt
  omega

/-- At level `0` every position is free and every merged variable is a letter, so the free part is
the whole labelling monomial `x_w` of `HJO.Sym.wordMonomial`. -/
theorem ztail_zero_level {N : ℕ} (w : Fin N → ℕ) :
    ztail K 0 w = wordMonomial (MvPolynomial (Fin 0) K) w := by
  rw [ztail_apply, wordMonomial]
  refine Finset.prod_congr (Finset.ext fun i => by simp) fun i _ => ?_
  rw [zvar_zero]

/-- The exponent in the alphabet of the monomial `z^{(k)}_{w,♭}`: the sum, over the positions at or
above the level whose letter is at or above the level, of the letter shifted down by `k`. This is
the datum a coefficientwise sum over the labellings groups them by. -/
noncomputable def ztailExponent (k : ℕ) {N : ℕ} (w : Fin N → ℕ) : ℕ →₀ ℕ :=
  ∑ i ∈ {i : Fin N | k ≤ (i : ℕ)}, zvarExponent k (w i)

/-- The coefficient in `𝕜[y_1, …, y_k]` of the monomial `z^{(k)}_{w,♭}`: the product of the
auxiliary variables named by the letters below the level at the positions at or above it. -/
noncomputable def ztailCoeff (K : Type*) [CommRing K] (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
    MvPolynomial (Fin k) K :=
  ∏ i ∈ {i : Fin N | k ≤ (i : ℕ)}, zvarCoeff K k (w i)

/-- **The free part of a labelling monomial is a monomial of `P_k`**, with exponent
`HJO.Sym.ztailExponent` in the alphabet and coefficient `HJO.Sym.ztailCoeff` in the auxiliary
variables.

This is what makes the sum `ν_σ(π) = ∑_w q ^ inv(At(π), w) z^{(k)}_{w,♭}` an element of
`P_k` despite having infinitely many terms: the coefficient of a given monomial of the alphabet
receives contributions only from the labellings with that `ztailExponent`, and there are finitely
many of those, the total number of positions being fixed. -/
theorem ztail_eq_monomial (K : Type*) [CommRing K] (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
    ztail K k w = MvPowerSeries.monomial (ztailExponent k w) (ztailCoeff K k w) := by
  rw [ztail_apply, Finset.prod_congr rfl fun i _ => zvar_eq_monomial K k (w i),
    prod_monomial_eq_monomial, ztailExponent, ztailCoeff]

/-- The coefficients of `z^{(k)}_{w,♭}`: the coefficient of the monomial with exponent `e` is
`ztailCoeff` when `e` is the exponent of `z^{(k)}_{w,♭}` and `0` otherwise. -/
theorem coeff_ztail (K : Type*) [CommRing K] (k : ℕ) {N : ℕ} (w : Fin N → ℕ) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (ztail K k w) =
      if e = ztailExponent k w then ztailCoeff K k w else 0 := by
  rw [ztail_eq_monomial, MvPowerSeries.coeff_monomial]

/-! ### Value checks

At the level `k = 2` and the length `N = 4` the free positions are `2` and `3`, so the free part of
a labelling reads only its last two letters. Taking the letters `1` and `3` there — in `1`-based
notation `w_3 = 2`, `w_4 = 4` — gives `y_2 x_2`: the letter `1` lies below the level and names the
auxiliary variable `y_2`, and the letter `3` lies above it and names the letter `x_{3-2} = x_1` of
the `0`-based alphabet. -/

theorem ztail_value_check :
    ztail K 2 ![0, 0, 1, 3] =
      MvPowerSeries.C (MvPolynomial.X (1 : Fin 2)) * MvPowerSeries.X 1 := by
  have hs : ({i : Fin 4 | 2 ≤ (i : ℕ)} : Finset (Fin 4)) = {2, 3} := by decide
  rw [ztail_apply, hs, Finset.prod_insert (by decide), Finset.prod_singleton]
  change zvar K 2 1 * zvar K 2 3 = _
  rw [zvar_of_lt (show (1 : ℕ) < 2 by omega), zvar_of_le (show (2 : ℕ) ≤ 3 by omega)]
  norm_num

/-- The two positions below the level contribute nothing, however their letters are chosen: the
free part of a labelling of `𝔻_{2,4}` is unchanged by moving its first two letters. This is the
truncation being real rather than cosmetic. -/
theorem ztail_ignores_special :
    ztail K 2 ![0, 0, 1, 3] = ztail K 2 ![5, 7, 1, 3] := by
  have hs : ({i : Fin 4 | 2 ≤ (i : ℕ)} : Finset (Fin 4)) = {2, 3} := by decide
  rw [ztail_apply, ztail_apply, hs, Finset.prod_insert (by decide), Finset.prod_singleton,
    Finset.prod_insert (by decide), Finset.prod_singleton]
  rfl

end HJO.Sym
