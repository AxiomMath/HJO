/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SignSumBlocks
public import HJO.CarlssonMellit.PartialCharacter
public meta import HJO.Attr

/-! # The characteristic series of a partial Dyck path at level zero

At level `0` the ring `P_0` of auxiliary series has no auxiliary variables, so it is the ring `𝒫` of
series in the alphabet with the coefficients `𝕜[y_1, …, y_0] = 𝕜` spelt as polynomials in an empty
family. This file names that identification, `HJO.Dyck.auxZeroMap`, and computes `ν_σ(π)` across it:
at the empty tuple of special values, `ν_σ(π)` is the no-attack sum

`∑_{w : w_i ≠ w_j for every attacking pair} q^{inv(At(π), w)}x_w`

of `HJO.Dyck.noAttackSummand`. That is the right-hand side of
`HJO.Dyck.isSigmaCharacter_of_eq_pathCharSeries` with the level-zero bookkeeping discharged, and the
form in which `HJO.Dyck.summableSum_pow_superInvNumber_smul_superMonomial` delivers it.

## Main definitions

* `HJO.Dyck.auxZeroMap`: the isomorphism `P_0 → 𝒫`, the coefficientwise
  `MvPolynomial.isEmptyAlgEquiv`.

## Main results

* `HJO.Dyck.auxZeroMap_injective`: it is injective, so an identity in `𝒫` proves one in `P_0` —
  which is how `HJO.Dyck.isSigmaCharacter_of_eq_pathCharSeries` transports its computation back to
  the character equation.
* `HJO.Dyck.auxZeroMap_apply_C`: `HJO.Dyck.ofAuxRealisationZero` is `ι_0` followed by it, so
  `ι(F)` and `ι_0(C F)` are the same element read on the two sides.
* `HJO.Dyck.auxZeroMap_partialCharSeries_zero`: `ν_σ(π)` at level `0` is the no-attack sum.

## Implementation notes

*Three level-zero collapses, each an arithmetic identity rather than a construction.* At `k = 0` the
merged variable `z^{(0)}_j` is the letter `x_j`, so `HJO.Sym.zvarCoeff` is `1` and
`HJO.Sym.ztailExponent` is `HJO.Sym.wordExponent`; the letters `HJO.Dyck.nuLetters` cuts the
defining sum down to are exactly the support of the monomial, the range below the level and the
image of the empty tuple both being empty; and `HJO.Dyck.noAttackLabellings` at the empty tuple
imposes only the no-attack condition, which is the condition of `HJO.Dyck.noAttackSummand` read
through `HJO.Dyck.finPairs`.

*The identification is a map and not an `AlgEquiv`.* Only injectivity is used, and it is immediate
from `MvPolynomial.isEmptyAlgEquiv` being injective coefficient by coefficient; building the inverse
would add nothing.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Sections 3 and 4.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

open HJO.Sym

variable {K : Type*} [CommRing K]

/-! ### The ring of auxiliary series at level zero -/

/-- **`P_0 = 𝒫`**: at level `0` the coefficients are polynomials in an empty family of auxiliary
variables, so they are the scalars, and the identification is coefficientwise. This is the
identification `HJO.Sym.AuxAlphabetSeries` makes silently and `HJO.Dyck.IsAuxRealisation` uses to
read `ι_0` as a realisation. -/
noncomputable def auxZeroMap (K : Type*) [CommRing K] :
    Sym.AuxAlphabetSeries K 0 →ₐ[K] Sym.AlphabetSeries K :=
  MvPowerSeries.mapAlgHom (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toAlgHom

theorem coeff_auxZeroMap (F : Sym.AuxAlphabetSeries K 0) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (auxZeroMap K F)
      = MvPolynomial.isEmptyAlgEquiv K (Fin 0) (MvPowerSeries.coeff d F) :=
  rfl

/-- The identification is injective: a coefficient of the image determines the coefficient of the
source, `MvPolynomial.isEmptyAlgEquiv` being an equivalence. -/
theorem auxZeroMap_injective : Function.Injective (auxZeroMap K) := fun F G h =>
  MvPowerSeries.ext fun d => (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).injective
    (by rw [← coeff_auxZeroMap, ← coeff_auxZeroMap, h])

/-- **`ι_0` read through the identification is the realisation `HJO.Dyck.ofAuxRealisationZero`**:
the two are the same composite, so the `ι(F)` and `ι_0(F)` denote the same series. -/
theorem auxZeroMap_apply_C (ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K 0) (F : Sym.Lambda K) :
    auxZeroMap K (ι (MvPolynomial.C F)) = ofAuxRealisationZero ι F :=
  rfl

/-! ### The level-zero collapses -/

/-- At level `0` no letter is an auxiliary variable, so the coefficient of a merged variable is
`1`. -/
@[simp]
theorem zvarCoeff_zero_level (K : Type*) [CommRing K] (j : ℕ) : zvarCoeff K 0 j = 1 := by
  simp [zvarCoeff]

/-- At level `0` the free part of a labelling monomial has the exponent vector of the labelling read
as a word. -/
theorem ztailExponent_zero_level {n : ℕ} (w : Fin n → ℕ) : ztailExponent 0 w = wordExponent w := by
  simp [ztailExponent, wordExponent, zvarExponent]

/-- At level `0` the coefficient of the free part is `1`, every position being free and every letter
being a letter. -/
@[simp]
theorem ztailCoeff_zero_level (K : Type*) [CommRing K] {n : ℕ} (w : Fin n → ℕ) :
    ztailCoeff K 0 w = 1 :=
  Finset.prod_eq_one fun i _ => zvarCoeff_zero_level K (w i)

/-- At level `0` the letters a labelling may carry, given the monomial it contributes to, are
exactly the letters of that monomial. -/
@[simp]
theorem nuLetters_zero_level (d : ℕ →₀ ℕ) (σ : Fin 0 → ℕ) : nuLetters 0 d σ = d.support := by
  simp [nuLetters]

/-- At level `0` and the empty tuple of special values, a labelling lies in `U(π, σ)` exactly when
it gives distinct letters to the two positions of every attacking pair — the prescription below the
level being vacuous. -/
theorem mem_noAttackLabellings_zero_level {n : ℕ} {x : Fin n → ℕ} {σ : Fin 0 → ℕ} {w : Fin n → ℕ} :
    w ∈ noAttackLabellings x σ ↔ ∀ p ∈ finPairs n (attackSet x), w p.1 ≠ w p.2 := by
  rw [mem_noAttackLabellings]
  refine ⟨fun h p hp => h.2 p.1 p.2 (mem_finPairs.1 hp), fun h => ⟨fun _ j => j.elim0, ?_⟩⟩
  exact fun i j hij => h (i, j) (mem_finPairs.2 hij)

/-! ### The characteristic series at level zero -/

/-- **`ν_σ(π)` at level `0` and the empty tuple is the no-attack sum.** Across the identification
`P_0 = 𝒫`,

`ν_σ(π) = ∑_{w}q^{inv(At(π),w)}x_w` over the labellings giving distinct letters to the two
positions of every attacking pair,

which is the right-hand side in `HJO.Dyck.isSigmaCharacter_of_eq_pathCharSeries` and what
`HJO.Dyck.summableSum_pow_superInvNumber_smul_superMonomial` produces.

Both sides are computed at one monomial. The defining sum of `ν_σ(π)` runs over the labellings with
letters among `HJO.Dyck.nuLetters`, which at level `0` are the letters of the monomial, whose free
part has that monomial's exponent vector, and which satisfy the no-attack condition; the family
`HJO.Dyck.noAttackSummand` reaches the monomial at exactly those labellings, with the same weight,
the level-zero coefficient of a free part being `1`. -/
theorem auxZeroMap_partialCharSeries_zero (q : K) {n : ℕ} (x : Fin n → ℕ) (σ : Fin 0 → ℕ) :
    auxZeroMap K (partialCharSeries q 0 x σ)
      = summableSum fun u : Fin n → ℕ => noAttackSummand K q (finPairs n (attackSet x)) u := by
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_auxZeroMap, coeff_partialCharSeries, Finset.sum_filter, map_sum,
    coeff_summableSum_eq_sum (s := Fintype.piFinset fun _ : Fin n => d.support)
      fun _ hu => mem_piFinset_support_of_coeff_noAttackSummand_ne_zero q _ hu]
  simp only [nuLetters_zero_level]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [noAttackSummand, invNumber]
  by_cases hadm : ∀ p ∈ finPairs n (attackSet x), u p.1 ≠ u p.2
  · have hmem : u ∈ noAttackLabellings x σ := mem_noAttackLabellings_zero_level.2 hadm
    rw [ite_eq_left hadm,
      show MvPowerSeries.coeff d (q ^ #(invSet (finPairs n (attackSet x)) u) • wordMonomial K u)
        = q ^ #(invSet (finPairs n (attackSet x)) u) *
          MvPowerSeries.coeff d (wordMonomial K u) from rfl,
      coeff_wordMonomial]
    by_cases hd : wordExponent u = d
    · rw [ite_eq_left ⟨hmem, by rw [ztailExponent_zero_level, hd]⟩, ite_eq_left hd.symm, mul_one,
        ztailCoeff_zero_level, map_smul, map_one, smul_eq_mul, mul_one]
    · rw [ite_eq_right fun h => hd (by rw [← ztailExponent_zero_level]; exact h.2),
        ite_eq_right (Ne.symm hd), mul_zero, map_zero]
  · have hmem : u ∉ noAttackLabellings x σ := fun h =>
      hadm (mem_noAttackLabellings_zero_level.1 h)
    rw [ite_eq_right hadm, ite_eq_right fun h => hmem h.1, map_zero, map_zero]

end HJO.Dyck
