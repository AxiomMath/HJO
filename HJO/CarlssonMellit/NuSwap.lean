/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ChiPrimeNu
public import HJO.CarlssonMellit.ChiPrimeSwap
public meta import HJO.Attr

/-! # The swapping operator on the normalised characteristic series

`HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple` states the swapping identity for
the *unnormalised* series `χ'_σ(π)`. The raising recursion reads it on the normalised series
`ν_σ(π)`, which differs from it by the single monomial `y_1y_2⋯y_k`. This file makes that passage,
which is `HJO.Dyck.auxToFrac_partialCharSeries_transposeTuple`: the monomial is symmetric in the two
auxiliary variables the operator moves, so `Δ_m` pulls it out, and it is a nonzero element of the
coefficient field, so it cancels.

## Main results

* `HJO.Dyck.auxToFrac_partialCharSeries_transposeTuple`,
  `ν_{τ_mσ}(π) = Δ_m(ν_σ(π))`.
* `HJO.Sym.mul_left_cancel_C`: a constant series at a nonzero coefficient cancels on the left in
  `P°_k`, the coefficient being a unit of the coefficient field.

## Implementation notes

*The identity lives in `P°_k`.* `Δ_m` is defined only on the fraction ring, so the statement is one
between images under the coefficientwise inclusion `HJO.Sym.auxToFrac`, exactly as
`HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple` is. `HJO.Sym.auxToFrac_injective`
recovers any statement in `P_k` that a consumer wants, but no consumer wants one: the recursion
applies `Δ*_m` next.

*The cancellation is by invertibility, not by integrality.* The direct argument divides
by `Y = y_1⋯y_k` after observing that `P°_k` is an integral domain. That is a statement about a
power series ring in infinitely many letters, which Mathlib does not carry in the form needed; and
it is not necessary, because `Y` is a nonzero element of the coefficient *field* and so
`MvPowerSeries.C Y` is a unit of `P°_k` outright. `HJO.Sym.mul_left_cancel_C` is that argument, and
it is the same device as `HJO.Sym.sub_yFrac_ne_zero` in `HJO.Sym.pdeltaStar`.

*The two side conditions of `HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple` are carried
verbatim.* Its hypotheses name the positions `a` and `b` of the labels `m` and `m + 1` and require
`a < b`, which is the condition `σ^{-1}(m) < σ^{-1}(m+1)` stated without an inverse function, and
the pair `i j : Fin k` with `(i : ℕ) = m`, `(j : ℕ) = m + 1` indexing the operator. Both are passed
through unchanged, so a consumer discharges them once for both lemmas. The `k ≥ 2` and `1 ≤ m ≤ k-1`
are the content of `(j : ℕ) = m + 1` together with `j.isLt`, and `N ≥ k` is the hypothesis `hk` that
`HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul` consumes.

## References

E. Carlsson and A. Mellit,
*A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ}

/-- **A constant series at a nonzero coefficient cancels on the left in `P°_k`.** The coefficients
form a field, so such a constant series is a unit, with inverse the constant series at the inverse
coefficient; no integrality of the power series ring is needed. -/
theorem mul_left_cancel_C {c : AuxFrac K k} (hc : c ≠ 0) {F G : AuxAlphabetSeriesFrac K k}
    (h : MvPowerSeries.C c * F = MvPowerSeries.C c * G) : F = G := by
  have hunit : (MvPowerSeries.C c⁻¹ * MvPowerSeries.C c : AuxAlphabetSeriesFrac K k) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  calc F = MvPowerSeries.C c⁻¹ * (MvPowerSeries.C c * F) := by rw [← mul_assoc, hunit, one_mul]
    _ = MvPowerSeries.C c⁻¹ * (MvPowerSeries.C c * G) := by rw [h]
    _ = G := by rw [← mul_assoc, hunit, one_mul]

variable {i j : Fin k}

omit [IsDomain K] in
/-- **The transposition of two auxiliary variables fixes the product of them all**: renaming along a
transposition permutes the factors of `y_1y_2⋯y_k`. -/
theorem fracSwapAux_prod_yFrac :
    fracSwapAux K i j (algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k)
        (∏ l : Fin k, MvPolynomial.X l)) =
      algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k) (∏ l : Fin k, MvPolynomial.X l) := by
  rw [fracSwapAux_algebraMap, map_prod]
  refine congrArg _ (Fintype.prod_equiv (Equiv.swap i j) _ _ fun l => ?_)
  rw [MvPolynomial.rename_X]

/-- The product `y_1y_2⋯y_k` is a nonzero element of the coefficient field: it is a monomial of the
polynomial ring, which is a domain, and the localization map is injective. -/
theorem prod_yFrac_ne_zero :
    algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k) (∏ l : Fin k, MvPolynomial.X l) ≠ 0 := by
  have hne : (∏ l : Fin k, MvPolynomial.X l : MvPolynomial (Fin k) K) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => MvPolynomial.X_ne_zero l
  exact fun h => hne (IsFractionRing.injective (MvPolynomial (Fin k) K) (AuxFrac K k)
    (by rw [map_zero]; exact h))

end HJO.Sym

namespace HJO.Dyck

open HJO.Sym

variable {K : Type*} [Field K] {k N m : ℕ} {x : Fin N → ℕ} {σ : Fin k → ℕ} {i j : Fin k}

/-- **The swapping operator on the normalised series.** For a partial Dyck path
`π ∈ 𝔻_{k,N}` and a tuple `σ` listing the labels of the level once each, with the label `m` at an
earlier position than the label `m + 1`,

`ν_{τ_mσ}(π) = Δ_m(ν_σ(π))`

inside `P°_k`.

By `HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul` both `χ'_σ(π)` and `χ'_{τ_mσ}(π)` are `y_1⋯y_k`
times the corresponding normalised series, `τ_mσ` being again a listing of the labels by
`HJO.Dyck.transposeTuple_lt_and_injective`. The monomial `y_1⋯y_k` is fixed by `ŝ_m`, so
`HJO.Sym.pdelta_mul_of_pswap_eq` pulls it out of `Δ_m`, and
`HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple` identifies the two sides after that. What
remains is a nonzero constant series multiplying both, and it cancels by
`HJO.Sym.mul_left_cancel_C`. -/
@[hjo "lem_cm_nu_swap"]
theorem auxToFrac_partialCharSeries_transposeTuple (q : K) (hk : k ≤ N)
    (hx : IsPartialDyck k N x) (hσ : Function.Injective σ) (hlt : ∀ l, σ l < k)
    (hmi : (i : ℕ) = m) (hmj : (j : ℕ) = m + 1)
    {a b : Fin k} (ha : σ a = m) (hb : σ b = m + 1) (hab : (a : ℕ) < (b : ℕ)) :
    auxToFrac K k (partialCharSeries q k x (transposeTuple m σ)) =
      pdelta q i j (auxToFrac K k (partialCharSeries q k x σ)) := by
  have hmk : m + 1 < k := hmj ▸ j.isLt
  obtain ⟨hlt', hσ'⟩ := transposeTuple_lt_and_injective hmk hlt hσ
  -- The special monomial, read in the coefficient field.
  set Y : AuxFrac K k :=
    algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k) (∏ l : Fin k, MvPolynomial.X l) with hY
  have hchi : ∀ τ : Fin k → ℕ, (∀ l, τ l < k) → Function.Injective τ →
      auxToFrac K k (unnormalisedCharSeries q k x τ) =
        MvPowerSeries.C Y * auxToFrac K k (partialCharSeries q k x τ) := by
    intro τ hτlt hτinj
    rw [unnormalisedCharSeries_eq_C_prod_X_mul hk hτlt hτinj, map_mul, auxToFrac_C]
  -- `HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple`, with the monomial pulled out of the
  -- operator on the right.
  have hswap := auxToFrac_unnormalisedCharSeries_transposeTuple q hx hσ hmi hmj ha hb hab (K := K)
  rw [hchi _ hlt' hσ', hchi _ hlt hσ,
    pdelta_mul_of_pswap_eq (MvPowerSeries.ext fun e => by
      rw [coeff_pswap]
      simp only [MvPowerSeries.coeff_C]
      split
      · exact fracSwapAux_prod_yFrac
      · exact map_zero _)] at hswap
  exact mul_left_cancel_C prod_yFrac_ne_zero hswap

end HJO.Dyck
