/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ChiPrime
public import HJO.CarlssonMellit.PartialCharSeries
public meta import HJO.Attr

/-! # The two characteristic series differ by the special monomial

One lemma, `HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul`: for a partial Dyck path
`π ∈ 𝔻_{k,N}` and a tuple `σ`
listing `{1, …, k}` once each,

`χ'_σ(π) = y_1 y_2 ⋯ y_k · ν_σ(π)`.

The two series of `HJO.Dyck.unnormalisedCharSeries` and `HJO.Dyck.partialCharSeries` are the same
sum over the same index set `U(π, σ)`, differing only in that the first keeps the `k` factors the
positions below the level contribute and the second drops them. Those factors are the merged
variables `z^{(k)}_{σ_1}, …, z^{(k)}_{σ_k}` for *every* labelling of `U(π, σ)`, the prescription
fixing the letters there; and when `σ` lists the labels below the level once each they are
`y_1, …, y_k` in some order. So the quotient is the constant `y_1 ⋯ y_k`, and dividing it out is
what makes `ν_σ(π)` rather than `χ'_σ(π)` the object the recursions are stated at.

## Main results

* `HJO.Dyck.zmonExponent_eq_ztailExponent` and `HJO.Dyck.zmonCoeff_eq_ztailCoeff_mul`: the full
  labelling monomial of a labelling of `U(π, σ)` is its free part times the fixed product
  `∏_j z^{(k)}_{σ_j}`, provided every entry of `σ` lies below the level, so that the extra factor is
  a coefficient and not a letter.
* `HJO.Dyck.unnormalisedCharSeries_eq_C_prod_mul`: `χ'_σ(π) = (∏_j z^{(k)}_{σ_j}) · ν_σ(π)` for
  every `σ` with entries below the level.
* `HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul`: the main statement,
`χ'_σ(π) = y_1 ⋯ y_k · ν_σ(π)`.

## Implementation notes

*The hypothesis "`σ` lists `{1, …, k}` once each" is `(∀ j, σ j < k)` together with
`Function.Injective σ`.* A tuple of `k` pairwise distinct labels all below the level lists the `k`
labels below the level once each, so this is the hypothesis and not a weakening of it;
splitting it in two is what lets the general statement above keep only the half it needs.

*The general statement asks only that the entries of `σ` lie below the level, not that they are
distinct.* Distinctness enters exactly once, to turn `∏_j y_{σ_j}` into `y_1 ⋯ y_k`; everything else
is the observation that a labelling of `U(π, σ)` carries the letter `σ_j` at the position `j`. The
bound `σ_j < k` is not removable: a special value at or above the level contributes a *letter* to
the monomial, so the quotient of the two series would no longer be a constant of `P_k`, and the
statement would have a different shape rather than a weaker one.

*`k ≤ N` is a hypothesis*, being the standing assumption `N ≥ k` of the statement as usually given:
it is what identifies the `k` positions below the level with the `k` entries of `σ`. Neither series
imposes it, and without it there are fewer than `k` such positions and the extra factor is a proper
subproduct.

*The special monomial is a constant series.* `y_1 ⋯ y_k` is `MvPowerSeries.C (∏ l, y_l)` and not a
product of merged variables `HJO.Sym.zvar`, so the identity is a statement about multiplication by a
coefficient; the two spellings agree because every `σ_j` lies below the level.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4.
-/

@[expose] public section

open Finset HJO.Sym

namespace HJO.Dyck

variable {K : Type*} [CommRing K] {N k : ℕ} {q : K} {x : Fin N → ℕ} {σ : Fin k → ℕ}
  {w : Fin N → ℕ} {e : ℕ →₀ ℕ}

/-! ### The positions below the level -/

/-- The positions of `Fin N` below the level are the images of the `k` positions of `Fin k`: this is
where the assumption `N ≥ k` is spent, identifying the positions the prescription speaks of with the
entries of the prescribing tuple. -/
theorem filter_not_le_eq_image_castLE (hk : k ≤ N) :
    Finset.filter (fun i : Fin N => ¬ k ≤ (i : ℕ)) Finset.univ
      = Finset.image (Fin.castLE hk) Finset.univ := by
  refine Finset.ext fun i => ?_
  simp only [mem_filter_univ, Finset.mem_image, Finset.mem_univ, true_and, not_le]
  refine ⟨fun h => ⟨⟨(i : ℕ), h⟩, Fin.ext rfl⟩, ?_⟩
  rintro ⟨j, rfl⟩
  simp

/-! ### The labelling monomial and its free part -/

/-- **The positions below the level contribute nothing to the alphabet exponent** of a labelling of
`U(π, σ)` whose special values all lie below the level: at such a position the letter is prescribed
by `σ`, hence names an auxiliary variable, hence leaves no trace in the alphabet. So the exponent of
the full labelling monomial is the exponent of its free part. -/
theorem zmonExponent_eq_ztailExponent (hlt : ∀ j, σ j < k) (hw : w ∈ noAttackLabellings x σ) :
    zmonExponent k w = ztailExponent k w := by
  rw [zmonExponent, ztailExponent]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi => ?_).symm
  have hik : (i : ℕ) < k := by
    have hni : ¬ k ≤ (i : ℕ) := fun h => hi (mem_filter_univ i |>.2 h)
    omega
  rw [eq_of_mem_noAttackLabellings hw (j := ⟨(i : ℕ), hik⟩) rfl]
  simp only [zvarExponent, hlt ⟨(i : ℕ), hik⟩, ↓reduceIte]

/-- **The full labelling monomial is its free part times the special factors**: for a labelling of
`U(π, σ)` the positions below the level carry the letters `σ_1, …, σ_k`, so the coefficient of the
full monomial is the coefficient of the free part times the fixed product `∏_j z^{(k)}_{σ_j}`, which
does not depend on the labelling. -/
theorem zmonCoeff_eq_ztailCoeff_mul (hk : k ≤ N) (hw : w ∈ noAttackLabellings x σ) :
    zmonCoeff K k w = ztailCoeff K k w * ∏ j : Fin k, zvarCoeff K k (σ j) := by
  rw [zmonCoeff, ztailCoeff, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i : Fin N => k ≤ (i : ℕ)) fun i => zvarCoeff K k (w i)]
  congr 1
  rw [filter_not_le_eq_image_castLE hk,
    Finset.prod_image fun a _ b _ h => Fin.castLE_injective hk h]
  exact Finset.prod_congr rfl fun j _ => by
    rw [apply_castLE_of_mem_noAttackLabellings hk hw j]

/-! ### The two characteristic series -/

/-- **The two characteristic series differ by the special factors**: for a tuple `σ` of special
values all below the level,

`χ'_σ(π) = (∏_j z^{(k)}_{σ_j}) · ν_σ(π)`,

the extra factor being a coefficient of `P_k` because every `σ_j` names an auxiliary variable. Both
series are sums over the same `U(π, σ)`, and on each labelling the summands differ by exactly that
factor; the index sets cut out coefficientwise agree because the two exponents agree, by
`HJO.Dyck.zmonExponent_eq_ztailExponent`. -/
theorem unnormalisedCharSeries_eq_C_prod_mul (hk : k ≤ N) (hlt : ∀ j, σ j < k) :
    unnormalisedCharSeries q k x σ
      = MvPowerSeries.C (∏ j : Fin k, zvarCoeff K k (σ j)) * partialCharSeries q k x σ := by
  refine MvPowerSeries.ext fun e => ?_
  rw [MvPowerSeries.coeff_C_mul,
    coeff_unnormalisedCharSeries_of_subset (s := zmonLetters k e ∪ nuLetters k e σ)
      Finset.subset_union_left,
    coeff_partialCharSeries_of_subset (s := zmonLetters k e ∪ nuLetters k e σ)
      Finset.subset_union_right, Finset.mul_sum]
  refine Finset.sum_congr (Finset.ext fun w => ?_) fun w hw => ?_
  · simp only [Finset.mem_filter]
    refine and_congr_right fun _ => and_congr_right fun hU => ?_
    rw [zmonExponent_eq_ztailExponent hlt hU]
  · rw [zmonCoeff_eq_ztailCoeff_mul hk (Finset.mem_filter.1 hw).2.1, mul_smul_comm,
      mul_comm (ztailCoeff K k w)]

/-- **The two characteristic series differ by the special monomial**,
`HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul`: for a tuple `σ` listing the labels below the
level once each,

`χ'_σ(π) = y_1 y_2 ⋯ y_k · ν_σ(π)`.

Every labelling of `U(π, σ)` carries the letters `σ_1, …, σ_k` at the positions below the level, so
the factors `χ'_σ(π)` keeps and `ν_σ(π)` drops are `y_{σ_1} ⋯ y_{σ_k}` for all of them at once; and
since `σ` takes each label below the level exactly once, that product is `y_1 ⋯ y_k`. -/
@[hjo "lem_cm_chiprime_nu"]
theorem unnormalisedCharSeries_eq_C_prod_X_mul (hk : k ≤ N) (hlt : ∀ j, σ j < k)
    (hinj : Function.Injective σ) :
    unnormalisedCharSeries q k x σ
      = MvPowerSeries.C (∏ l : Fin k, MvPolynomial.X l) * partialCharSeries q k x σ := by
  have hbij : Function.Bijective fun j : Fin k => (⟨σ j, hlt j⟩ : Fin k) :=
    Finite.injective_iff_bijective.1 fun a b hab => hinj (by simpa using congrArg Fin.val hab)
  rw [unnormalisedCharSeries_eq_C_prod_mul hk hlt,
    Fintype.prod_bijective _ hbij (fun j => zvarCoeff K k (σ j))
      (fun l : Fin k => (MvPolynomial.X l : MvPolynomial (Fin k) K))
      fun j => by simp only [zvarCoeff, hlt j, ↓reduceDIte]]

end HJO.Dyck
