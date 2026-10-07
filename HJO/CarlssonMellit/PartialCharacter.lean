/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PartialCharSeries
public import HJO.CarlssonMellit.SweepCM
public import HJO.Evaluation.PhiMul
public meta import HJO.Attr

/-! # Realisation with auxiliary variables, and the characters of a partial Dyck path

Two definitions and one lemma. The recursion of Carlsson and Mellit's Section 4 computes the
characteristic series `ν_σ(π)` of `HJO.Dyck.partialCharSeries` not directly but through a symmetric
function: an element `G` of `V_k` is a *`σ`-character* of `π` when

`ι_k(θ_k(G)) = (q - 1) ^ (N - k) · ν_σ(π)`,

where `θ_k` is the plethysm by `(q-1)X` of `HJO.Sweep.theta` and `ι_k` realises the power sums in
the alphabet while fixing the auxiliary variables. The whole recursion is then a statement about
characters, run forwards from the empty path, whose character is `1`.

## Main definitions

* `HJO.Dyck.IsAuxRealisation`: `ι_k` — the `𝕜[y_1, …, y_k]`-algebra homomorphism `V_k → P_k` sending
  `p_r` to the power sum `∑_i x_i^r`.
* `HJO.Dyck.auxRealise`: one such homomorphism, so the predicate is not vacuous.
* `HJO.Dyck.IsSigmaCharacter`: `G` is a `σ`-character of `π`.

## Main results

* `HJO.Dyck.isAuxRealisation_auxRealise`: `ι_k` exists.
* `HJO.Dyck.eq_of_isAuxRealisation`: and is unique on `V_k`: there is exactly one such
  homomorphism there.
* `HJO.Dyck.isRealisation_ofAuxRealisationZero`: at `k = 0` it is a realisation in the sense of
  `HJO.Sym.IsRealisation`.
* `HJO.Dyck.isSigmaCharacter_one_of_isEmpty`: `1` is a `σ`-character of the empty path.

## Implementation notes

*`ι_k` is a predicate on a homomorphism and not a construction*, exactly as `HJO.Sym.IsRealisation`
is: the power sum `∑_i x_i^r` is an element of a power series ring specified by its coefficients,
and what every consumer needs is those coefficients. Unlike `HJO.Sym.IsRealisation`, this file also
supplies a witness, `HJO.Dyck.auxRealise`, and its uniqueness on `V_k`, so the predicate
is known to describe exactly one map on `V_k`.

*The domain is the total space `HJO.Sweep.Total K` and not the subalgebra `V_k`.* This is the
convention of the layer, the one `HJO.Sweep.theta` follows: every operator is an endomorphism of one
space and the `V_k` is the subalgebra `HJO.Sweep.piece K k` on which it is read. A
`K`-algebra homomorphism satisfying `HJO.Dyck.IsAuxRealisation.map_auxVar` is a
`𝕜[y_1, …, y_k]`-algebra homomorphism where that matters, `𝕜[y_1, …, y_k]` being generated over `K`
by the auxiliary variables; and `HJO.Dyck.eq_of_isAuxRealisation` is uniqueness *on `V_k`*, not on
the total space, where the values at the auxiliary variables above the level are unconstrained and
`auxRealise` sets them to `0`.

*The exponent `N - k` in `HJO.Dyck.IsSigmaCharacter` is truncated subtraction*, and it is Carlsson
and Mellit's `|π|`, the number of north steps of the partial path, exactly under the standing
hypothesis `k ≤ N` — which every consumer has, `π` being an element of `𝔻_{k,N}`. At `N < k` the
predicate reads `ι_k(θ_k(G)) = ν_σ(π)`; no consumer forms it there, and no claim is made about that
case.

*`HJO.Dyck.isSigmaCharacter_one_of_isEmpty` needs no hypothesis on `ι`.* Both sides of the character
equation at the empty path are computed from `ι` and `θ_k` being algebra homomorphisms —
`ι(θ(1)) = 1` — together with `HJO.Dyck.partialCharSeries_of_isEmpty`, which carries the content:
the empty path has exactly one labelling, it inverts nothing, and its free labelling monomial is the
empty product. So it is proved for an arbitrary `K`-algebra homomorphism, which is stronger than
requiring `ι_0` to be a realisation.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4 and its equation (4.5), read as a property of `G` rather than as a construction
of it: that is what lets the recursion run forwards from the empty path with no existence statement
about `χ_σ(π)` anywhere. Consumed by `HJO.Dyck.isSigmaCharacter_cmDPlus` and
`HJO.Dyck.isSigmaCharacter_dminusCM'`. -/

@[expose] public section

open Finset

namespace HJO.Dyck

variable {K : Type*} [CommRing K]

/-! ### Realisation with auxiliary variables -/

/-- **`ι_k`, a realisation with auxiliary variables**: a `K`-algebra homomorphism from the total
space of the sweep to `P_k` that sends the power sum `p_{r+1}` to the actual power sum
`∑_i x_i^{r+1}` of the alphabet — recorded by its coefficients, which are `1` on the monomials
`x_i^{r+1}` and `0` elsewhere — and fixes each of the `k` auxiliary variables `y_1, …, y_k`.

Fixing the auxiliary variables is what makes it a `𝕜[y_1, …, y_k]`-algebra homomorphism, that
algebra being generated over `K` by them; and on `V_k = HJO.Sweep.piece K k` there is exactly one
such map, by `HJO.Dyck.eq_of_isAuxRealisation`. At `k = 0` it is a realisation in the sense of
`HJO.Sym.IsRealisation`, by `HJO.Dyck.isRealisation_ofAuxRealisationZero`, which is the `ι_0`.

Nothing constrains the auxiliary variables *above* the level, which do not occur in `V_k`. -/
@[hjo "def_cm_realisation_k"]
structure IsAuxRealisation (k : ℕ) (ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k) :
    Prop where
  coeff_pow : ∀ r i : ℕ, MvPowerSeries.coeff (Finsupp.single i (r + 1))
    (ι (MvPolynomial.C (Sym.powerSum K (r + 1)))) = 1
  coeff_of_ne : ∀ (r : ℕ) (d : ℕ →₀ ℕ), (∀ i, d ≠ Finsupp.single i (r + 1)) →
    MvPowerSeries.coeff d (ι (MvPolynomial.C (Sym.powerSum K (r + 1)))) = 0
  map_auxVar : ∀ j : Fin k,
    ι (Sweep.auxVar ((j : ℕ) + 1)) = MvPowerSeries.C (MvPolynomial.X j)

/-- One `ι_k`, so that `HJO.Dyck.IsAuxRealisation` is not vacuous: the power sums go to the power
sums of the alphabet with coefficients in `𝕜[y_1, …, y_k]`, the auxiliary variables below the level
go to themselves, and those above it go to `0`. -/
noncomputable def auxRealise (K : Type*) [CommRing K] (k : ℕ) :
    Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k :=
  MvPolynomial.aevalTower
    (MvPolynomial.aeval fun i : ℕ => PhiMul.alphabetPowerSum (MvPolynomial (Fin k) K) (i + 1))
    fun j : ℕ => if h : j < k then MvPowerSeries.C (MvPolynomial.X ⟨j, h⟩) else 0

theorem isAuxRealisation_auxRealise (K : Type*) [CommRing K] (k : ℕ) :
    IsAuxRealisation k (auxRealise K k) where
  coeff_pow r i := by
    rw [auxRealise, MvPolynomial.aevalTower_C, Sym.powerSum, Nat.add_sub_cancel,
      MvPolynomial.aeval_X, PhiMul.coeff_alphabetPowerSum_single]
  coeff_of_ne r d hd := by
    rw [auxRealise, MvPolynomial.aevalTower_C, Sym.powerSum, Nat.add_sub_cancel,
      MvPolynomial.aeval_X, PhiMul.coeff_alphabetPowerSum_of_ne _ _ _ hd]
  map_auxVar j := by
    rw [Sweep.auxVar, Nat.add_sub_cancel, auxRealise, MvPolynomial.aevalTower_X]
    simp only [j.isLt, ↓reduceDIte, Fin.eta]

/-- **`ι_k` is unique on `V_k` up to its values on the power sums**: two realisations with auxiliary
variables agree on every element of `Λ`, read inside the total space as a constant. Both composites
`Λ → P_k` are `K`-algebra homomorphisms agreeing on each generator `p_{r+1}`, whose image is pinned
coefficient by coefficient. -/
theorem apply_C_eq_of_isAuxRealisation {k : ℕ}
    {ι₁ ι₂ : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k}
    (h₁ : IsAuxRealisation k ι₁) (h₂ : IsAuxRealisation k ι₂) (F : Sym.Lambda K) :
    ι₁ (MvPolynomial.C F) = ι₂ (MvPolynomial.C F) := by
  have hgen : ∀ r : ℕ,
      ι₁ (MvPolynomial.C (MvPolynomial.X r : Sym.Lambda K)) =
        ι₂ (MvPolynomial.C (MvPolynomial.X r : Sym.Lambda K)) := by
    intro r
    have hps : (MvPolynomial.X r : Sym.Lambda K) = Sym.powerSum K (r + 1) := by
      rw [Sym.powerSum, Nat.add_sub_cancel]
    rw [hps]
    refine MvPowerSeries.ext fun d => ?_
    by_cases hd : ∃ i, d = Finsupp.single i (r + 1)
    · obtain ⟨i, rfl⟩ := hd
      rw [h₁.coeff_pow r i, h₂.coeff_pow r i]
    · simp only [not_exists] at hd
      rw [h₁.coeff_of_ne r d hd, h₂.coeff_of_ne r d hd]
  have := MvPolynomial.algHom_ext (f := ι₁.comp (IsScalarTower.toAlgHom K (Sym.Lambda K)
    (Sweep.Total K))) (g := ι₂.comp (IsScalarTower.toAlgHom K (Sym.Lambda K) (Sweep.Total K)))
    hgen
  exact AlgHom.congr_fun this F

theorem eq_of_isAuxRealisation {k : ℕ}
    {ι₁ ι₂ : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k}
    (h₁ : IsAuxRealisation k ι₁) (h₂ : IsAuxRealisation k ι₂) {G : Sweep.Total K}
    (hG : G ∈ Sweep.piece K k) : ι₁ G = ι₂ G := by
  rw [Sweep.piece, MvPolynomial.supported_eq_adjoin_X] at hG
  induction hG using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hlt : j < k := hj
    have hj' : ((⟨j, hlt⟩ : Fin k) : ℕ) + 1 - 1 = j := by simp
    rw [show (MvPolynomial.X j : Sweep.Total K) = Sweep.auxVar (((⟨j, hlt⟩ : Fin k) : ℕ) + 1) by
      rw [Sweep.auxVar, hj'], h₁.map_auxVar ⟨j, hlt⟩, h₂.map_auxVar ⟨j, hlt⟩]
  | algebraMap r => exact apply_C_eq_of_isAuxRealisation h₁ h₂ r
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]

/-! ### The realisation at level zero -/

/-- `ι_0` read as a map `Λ → 𝒫`: the level-`0` coefficients `𝕜[y_1, …, y_0]` are `𝕜`, and the
level-`0` piece of the total space is `Λ` read as constants, so `ι_0` restricts to a `K`-algebra
homomorphism from `Λ` to the power series in the alphabet. -/
noncomputable def ofAuxRealisationZero (ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K 0) :
    Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K :=
  (MvPowerSeries.mapAlgHom (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toAlgHom).comp
    (ι.comp (IsScalarTower.toAlgHom K (Sym.Lambda K) (Sweep.Total K)))

theorem coeff_ofAuxRealisationZero (ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K 0)
    (F : Sym.Lambda K) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (ofAuxRealisationZero ι F) =
      MvPolynomial.isEmptyAlgEquiv K (Fin 0)
        (MvPowerSeries.coeff d (ι (MvPolynomial.C F))) := by
  rfl

theorem isRealisation_ofAuxRealisationZero
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K 0} (h : IsAuxRealisation 0 ι) :
    Sym.IsRealisation (ofAuxRealisationZero ι) where
  coeff_pow k i := by rw [coeff_ofAuxRealisationZero, h.coeff_pow k i, map_one]
  coeff_of_ne k d hd := by rw [coeff_ofAuxRealisationZero, h.coeff_of_ne k d hd, map_zero]

/-! ### A character of a partial Dyck path -/

/-- **`G` is a `σ`-character of `π`**:

`ι_k(θ_k(G)) = (q - 1) ^ (N - k) · ν_σ(π)`,

Carlsson and Mellit's equation (4.5) read as a *property* of `G` rather than as a construction of
it. That reading is what lets the character recursion run forwards from the empty path: no existence
statement about `χ_σ(π)` is needed anywhere, and in particular the symmetry of `χ'_σ(π)` in the
alphabet — the one place where Carlsson and Mellit appeal to their Proposition 3.5 for a
well-definedness — is never used.

The exponent `N - k` is Carlsson and Mellit's `|π|`, the number of north steps of the partial path;
it is truncated subtraction, honest under the standing hypothesis `k ≤ N` that every consumer has.
-/
@[hjo "def_cm_char"]
def IsSigmaCharacter (q : K) (k : ℕ) (ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k)
    {N : ℕ} (x : Fin N → ℕ) (σ : Fin k → ℕ) (G : Sweep.Total K) : Prop :=
  ι (Sweep.theta q G) = (q - 1) ^ (N - k) • partialCharSeries q k x σ

/-- **The empty path has character one**: `1 ∈ V_0` is a `σ`-character of the empty path, for the
empty tuple of special values.

The empty path lies in `𝔻_{0,0}` and has no attacking pairs, so its single labelling — the empty
tuple — inverts nothing and has the empty product for its free labelling monomial; hence
`ν_σ(π) = 1` by `HJO.Dyck.partialCharSeries_of_isEmpty`, and `(q-1)^{0-0} = 1`. On the other side
`θ_0(1) = 1` and `ι_0(1) = 1`, both maps being algebra homomorphisms — which is all that is used of
`ι`, so no hypothesis of `HJO.Dyck.IsAuxRealisation` appears. -/
@[hjo "lem_cm_char_empty"]
theorem isSigmaCharacter_one_of_isEmpty (q : K)
    (ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K 0) (x : Fin 0 → ℕ) (σ : Fin 0 → ℕ) :
    (1 : Sweep.Total K) ∈ Sweep.piece K 0 ∧ IsSigmaCharacter q 0 ι x σ 1 := by
  refine ⟨Subalgebra.one_mem _, ?_⟩
  rw [IsSigmaCharacter, map_one, map_one, partialCharSeries_of_isEmpty]
  simp

end HJO.Dyck
