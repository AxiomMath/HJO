/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ChiPrimeNu
public import HJO.CarlssonMellit.LowerPieces
public meta import HJO.Attr

/-! # The freed characteristic series factors

One lemma, `HJO.Dyck.unnormalisedCharSeries_lowerTuple`: for a partial Dyck path
`π ∈ 𝔻_{k,N}` of level
`k = m + 1 ≥ 1` and `r ≥ 0`,

`χ'_{σ^{[r]}}(π) = y_1 ⋯ y_{k-1} · z^{(k)}_{k+r} · μ_r(π)`,

the empty product `y_1 ⋯ y_{k-1}` being `1` at `k = 1`.

The two series `HJO.Dyck.unnormalisedCharSeries` and `HJO.Dyck.lowerCharPiece` are the same sum over
the same index set `U(π, σ^{[r]})`, differing only in that the first keeps the `k` factors the
positions below the level contribute. The prescription `σ^{[r]} = (1, …, k-1, k+r)` fixes the
letters at those positions for *every* labelling of `U(π, σ^{[r]})`, so those factors are the one
monomial `z^{(k)}_1 ⋯ z^{(k)}_{k-1} z^{(k)}_{k+r} = y_1 ⋯ y_{k-1} z^{(k)}_{k+r}`, and the quotient
of the two series is that monomial.

This is `HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul` with a prescription whose last entry
lies *at or above* the level, where the extra factor is no longer a coefficient of `P_k` but a
monomial: the freed label `k + r` names the letter `x_r` of the alphabet as soon as `r ≥ 1`. So the
identity cannot be read off a coefficientwise identity of the two sums position by position, and the
general statement below carries the shift of the alphabet exponent explicitly.

## Main results

* `HJO.Dyck.zmonExponent_eq_ztailExponent_add`: the alphabet exponent of the full labelling monomial
  of a labelling of `U(π, σ)` is the exponent of its free part shifted by the fixed contribution of
  the prescribed letters.
* `HJO.Dyck.unnormalisedCharSeries_eq_monomial_mul`: the abstract form of the factorisation — once
  the full monomial of every labelling of `U(π, σ)` is its free part times a *fixed* monomial, the
  same holds of the two series.
* `HJO.Dyck.unnormalisedCharSeries_eq_prod_zvar_mul`: `χ'_σ(π) = (∏_j z^{(k)}_{σ_j}) · ν_σ(π)` for
  *every* tuple `σ` of special values, with no bound on its entries.
* `HJO.Dyck.unnormalisedCharSeries_lowerTuple`: the main statement,
  `χ'_{σ^{[r]}}(π) = y_1 ⋯ y_{k-1} z^{(k)}_{k+r} μ_r(π)`.

## Implementation notes

*The general factorisation drops the bound `σ_j < k` of
`HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul`.* That bound is what makes the extra factor a
constant series `MvPowerSeries.C`, and the statement there is about multiplication by a coefficient.
Here the factor is the product of the merged variables `HJO.Sym.zvar` themselves, which is a
monomial of `P_k` by `HJO.Sym.prod_monomial_eq_monomial` whatever the entries of `σ` are, and
multiplying by a monomial *shifts* the alphabet exponent. So the coefficientwise comparison happens
at `e` on the left and at `e` minus that shift on the right, and the coefficients of a monomial `e`
below the shift vanish on both sides — no labelling has an exponent that small.

*`π ∈ 𝔻_{k,N}` is not a hypothesis, and `N ≥ k` is.* Neither series reads the path except through
its attack set, and the factorisation is an identity of the summands: the only thing used is that a
labelling of `U(π, σ)` carries the letter `σ_j` at the position `j`, which needs the `k` positions
below the level to be positions of the path, that is `k ≤ N`. Dropping `π ∈ 𝔻_{k,N}` is a
generalisation of the statement.

*The `z^{(k)}_{k+r}` is `HJO.Sym.zvar K (m+1) (m+r)`*, because `zvar K k j` is the merged variable
written `z^{(k)}_{j+1}` above: labels are indexed from `0` in this layer, so the label `k + r` is
the label `k + r - 1 = m + r` here, which is exactly the last entry of `HJO.Dyck.lowerTuple m r`.
The index is read off the tuple and not chosen, so there is no room for a shift to slip in.

*The empty product is handled by the type and not by a case split.* At `k = 1`, so `m = 0`, the
product `∏ j : Fin m, y_{j+1}` is over `Fin 0` and is `1`; the parenthetical about
`k = 1` is a remark on its own notation.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4, where their `χ'_{k,r}(π)` is this series. Consumed by
`HJO.Dyck.isZDelta_zvar_mul_lowerCharPiece` and `HJO.Dyck.isSummableFamily_zvar_mul_lowerCharPiece`.
-/

@[expose] public section

open Finset HJO.Sym

namespace HJO.Dyck

variable {K : Type*} [CommRing K] {N k m r : ℕ} {q : K} {x : Fin N → ℕ} {σ : Fin k → ℕ}
  {w : Fin N → ℕ} {e : ℕ →₀ ℕ}

/-! ### Splitting the prescribed factors off the labelling monomial -/

/-- **The prescribed letters shift the alphabet exponent by a fixed amount**: for a labelling of
`U(π, σ)` the positions below the level carry the letters `σ_1, …, σ_k`, so the alphabet exponent of
the full labelling monomial is the exponent of its free part plus the fixed contribution
`∑_j zvarExponent k (σ j)` of those letters.

This is `HJO.Dyck.zmonExponent_eq_ztailExponent` with the bound `σ_j < k` dropped: with the bound
the extra contribution is `0`, and without it the prescribed letters at or above the level record
themselves in the alphabet. -/
theorem zmonExponent_eq_ztailExponent_add (hk : k ≤ N) (hw : w ∈ noAttackLabellings x σ) :
    zmonExponent k w = ztailExponent k w + ∑ j : Fin k, zvarExponent k (σ j) := by
  rw [zmonExponent, ztailExponent, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin N => k ≤ (i : ℕ)) fun i => zvarExponent k (w i)]
  congr 1
  rw [filter_not_le_eq_image_castLE hk,
    Finset.sum_image fun a _ b _ h => Fin.castLE_injective hk h]
  exact Finset.sum_congr rfl fun j _ => by
    rw [apply_castLE_of_mem_noAttackLabellings hk hw j]

/-- **The two characteristic series differ by a fixed monomial**, in the abstract form: if the full
labelling monomial of every labelling of `U(π, σ)` is its free part times one fixed monomial
`MvPowerSeries.monomial E c`, then `χ'_σ(π) = monomial E c · ν_σ(π)`.

Both series are sums over the same `U(π, σ)`, but multiplying by a monomial shifts the alphabet
exponent, so the comparison is between the coefficient of `E + d` on the left and the coefficient of
`d` on the right; there the labellings summed over are literally the same, the two conditions
`zmonExponent k w = E + d` and `ztailExponent k w = d` being equivalent. At a monomial `e` that does
not dominate `E` both sides vanish, no labelling having so small an exponent. -/
theorem unnormalisedCharSeries_eq_monomial_mul {E : ℕ →₀ ℕ} {c : MvPolynomial (Fin k) K}
    (hE : ∀ w ∈ noAttackLabellings x σ, zmonExponent k w = ztailExponent k w + E)
    (hc : ∀ w ∈ noAttackLabellings x σ, zmonCoeff K k w = ztailCoeff K k w * c) :
    unnormalisedCharSeries q k x σ
      = MvPowerSeries.monomial E c * partialCharSeries q k x σ := by
  refine MvPowerSeries.ext fun e => ?_
  rw [MvPowerSeries.coeff_monomial_mul]
  by_cases hEe : E ≤ e
  · rw [ite_eq_left hEe]
    obtain ⟨d, rfl⟩ : ∃ d, e = E + d := ⟨e - E, (add_tsub_cancel_of_le hEe).symm⟩
    rw [add_tsub_cancel_left,
      coeff_unnormalisedCharSeries_of_subset (s := zmonLetters k (E + d) ∪ nuLetters k d σ)
        Finset.subset_union_left,
      coeff_partialCharSeries_of_subset (s := zmonLetters k (E + d) ∪ nuLetters k d σ)
        Finset.subset_union_right, Finset.mul_sum]
    refine Finset.sum_congr (Finset.ext fun w => ?_) fun w hw => ?_
    · simp only [Finset.mem_filter]
      refine and_congr_right fun _ => and_congr_right fun hU => ?_
      rw [hE w hU, add_comm (ztailExponent k w) E]
      exact add_right_inj E
    · rw [hc w (Finset.mem_filter.1 hw).2.1, mul_smul_comm, mul_comm (ztailCoeff K k w)]
  · rw [ite_eq_right hEe, coeff_unnormalisedCharSeries]
    refine Finset.sum_eq_zero fun w hw => absurd ?_ hEe
    have hmem := Finset.mem_filter.1 hw
    rw [← hmem.2.2, hE w hmem.2.1]
    exact le_add_self

/-- **The two characteristic series differ by the prescribed factors**, for *every* tuple of special
values:

`χ'_σ(π) = (∏_j z^{(k)}_{σ_j}) · ν_σ(π)`.

This is `HJO.Dyck.unnormalisedCharSeries_eq_C_prod_mul` with the bound `σ_j < k` removed. The extra
factor is then a monomial of `P_k` rather than a coefficient — a prescribed letter at or above the
level names a letter of the alphabet — and it is still the same factor for every labelling of
`U(π, σ)`, which is all the identity needs. -/
theorem unnormalisedCharSeries_eq_prod_zvar_mul (hk : k ≤ N) :
    unnormalisedCharSeries q k x σ
      = (∏ j : Fin k, zvar K k (σ j)) * partialCharSeries q k x σ := by
  rw [Finset.prod_congr rfl fun j _ => zvar_eq_monomial K k (σ j), prod_monomial_eq_monomial]
  exact unnormalisedCharSeries_eq_monomial_mul (fun _ hw => zmonExponent_eq_ztailExponent_add hk hw)
    fun _ hw => zmonCoeff_eq_ztailCoeff_mul hk hw

/-! ### The freed characteristic series -/

/-- **The prescribed factors of the lower tuple** are `y_1 ⋯ y_{k-1} z^{(k)}_{k+r}`: the first `m`
entries of `σ^{[r]}` are the labels `0, …, m-1`, all below the level `k = m + 1`, and so name the
auxiliary variables `y_1, …, y_{k-1}`; the last entry is the freed label `m + r`, Carlsson and
Mellit's `k + r`, and names the merged variable `z^{(k)}_{k+r}`, which is a letter of the alphabet
as soon as `r ≥ 1`. -/
theorem prod_zvar_lowerTuple (K : Type*) [CommRing K] (m r : ℕ) :
    (∏ j : Fin (m + 1), zvar K (m + 1) (lowerTuple m r j))
      = MvPowerSeries.C (∏ j : Fin m, MvPolynomial.X j.castSucc) * zvar K (m + 1) (m + r) := by
  rw [Fin.prod_univ_castSucc, lowerTuple_last, map_prod]
  refine congrArg (· * zvar K (m + 1) (m + r)) (Finset.prod_congr rfl fun j _ => ?_)
  rw [lowerTuple_castSucc, zvar_of_lt (show (j : ℕ) < m + 1 from Nat.lt_succ_of_lt j.isLt)]
  rfl

/-- **The freed characteristic series factors**, `HJO.Dyck.unnormalisedCharSeries_lowerTuple`: for a
partial Dyck path of level `k = m + 1` and `r ≥ 0`,

`χ'_{σ^{[r]}}(π) = y_1 ⋯ y_{k-1} · z^{(k)}_{k+r} · μ_r(π)`.

The prescription `σ^{[r]} = (1, …, k-1, k+r)` fixes the first `k` letters of every labelling of
`U(π, σ^{[r]})`, so the factors `χ'_{σ^{[r]}}(π)` keeps and `μ_r(π)` drops are
`y_1 ⋯ y_{k-1} z^{(k)}_{k+r}` for all of them at once. At `k = 1` the product `y_1 ⋯ y_{k-1}` is
empty and the statement reads `χ'_{σ^{[r]}}(π) = z^{(1)}_{1+r} μ_r(π)`. -/
@[hjo "lem_cm_chiprime_lower"]
theorem unnormalisedCharSeries_lowerTuple (hk : m + 1 ≤ N) :
    unnormalisedCharSeries q (m + 1) x (lowerTuple m r)
      = MvPowerSeries.C (∏ j : Fin m, MvPolynomial.X j.castSucc) * zvar K (m + 1) (m + r)
        * lowerCharPiece q m x r := by
  rw [lowerCharPiece, ← prod_zvar_lowerTuple K m r, unnormalisedCharSeries_eq_prod_zvar_mul hk]

/-- The same factorisation with the auxiliary variables written as merged variables:
`∏_{j < k-1} z^{(k)}_{j+1}` is `y_1 ⋯ y_{k-1}`, every one of those labels lying below the level.
This is the shape in which the lowering recursion meets the product, its own factors being merged
variables. -/
theorem unnormalisedCharSeries_lowerTuple' (hk : m + 1 ≤ N) :
    unnormalisedCharSeries q (m + 1) x (lowerTuple m r)
      = (∏ j : Fin m, zvar K (m + 1) (j : ℕ)) * zvar K (m + 1) (m + r)
        * lowerCharPiece q m x r := by
  rw [unnormalisedCharSeries_lowerTuple hk, map_prod]
  refine congrArg (· * zvar K (m + 1) (m + r) * lowerCharPiece q m x r)
    (Finset.prod_congr rfl fun j _ => ?_).symm
  rw [zvar_of_lt (show (j : ℕ) < m + 1 from Nat.lt_succ_of_lt j.isLt)]
  rfl

end HJO.Dyck
