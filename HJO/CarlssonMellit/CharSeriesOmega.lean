/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CharSeries
public import HJO.Classical.OmegaGessel
public import HJO.DyckAttackNumber
public meta import HJO.Attr

/-! # The involution on characteristic functions

`HJO.Dyck.realisation_omegaBar_pathCharSeries`, Carlsson--Mellit's Proposition 3.4: the conjugate
involution `ω̄ = ω₋ ∘ cj` sends a symmetric function realising the characteristic series of a Dyck
path to `(-1)^n q^{-at(π)}` times that series.

## Main statements

* `HJO.Dyck.realisation_omegaBar_pathCharSeries`.

## Implementation notes

Four steps, each a lemma proved elsewhere.

* `cj` commutes with a realisation (`HJO.Sym.realisation_paramInvLambda`), because the coefficients
  of `ι(p_k)` are `0` and `1` and a ring homomorphism fixes those; so `ι(f̄)` is the fundamental
  expansion of `HJO.Dyck.charSeries_eq_sum_gessel` with `q` replaced by `q⁻¹`, the fundamentals
  themselves being fixed (`HJO.ParkingFunctions.paramInvSeries_gessel`).
* `HJO.ParkingFunctions.realisation_plethNegate_gessel` complements every descent set and
  contributes the sign.
* `HJO.gessel_reverse_sum` reflects each complemented set, and `HJO.Sym.invDescentSet_trans_revPerm`
  identifies the reflected complement of `Des(σ⁻¹)` with `Des((σ^{rv})⁻¹)`.
* Reindexing by the involution `σ ↦ σ^{rv}` of the permutations and using
  `HJO.Dyck.invNumber_add_invNumber_revPerm` in the form `inv(R,σ) + inv(R,σ^{rv}) = #R` turns `q⁻¹`
  back into `q` and leaves the single scalar `q^{-#R}`.

*Three hypotheses of the statement as usually given are not needed and one is added.* Not needed:
`π` a Dyck path — the proof reads of `At(π)` only that its pairs increase, which holds of
`HJO.Dyck.attackSet` at *every* sequence, so the statement is for an arbitrary `x`; `n ≥ 1`; and any
relation between `cj` and `u`. Added: `q ≠ 0`, and `cj` is carried as an arbitrary ring automorphism
`τ` of the base with `τ q = q⁻¹`. Over the coefficient field `𝕜 = ℚ(q,u)` both are automatic, `q`
being an indeterminate; over an arbitrary field they are not, and `q = 0` genuinely breaks the
statement, the step `q⁻¹ ^ a * q ^ a = 1` being where it is spent.

`HJO.Dyck.card_finPairs_attackSet` is the only bookkeeping: `inv(R,σ)` counts pairs of positions
`Fin n × Fin n` while `at(π)` counts pairs of naturals, and the two agree because every attacking
cell has both coordinates below `n`.

## References

The lemma `HJO.Dyck.realisation_omegaBar_pathCharSeries`. Following E. Carlsson and A. Mellit, *A
proof of the shuffle conjecture*, Proposition 3.4.
-/

@[expose] public section

open Finset HJO.ParkingFunctions

namespace HJO.Sym

variable {L : Type*} [CommRing L] {ι : Lambda L →ₐ[L] AlphabetSeries L}

/-- **Inverting the parameters commutes with a realisation**: `ι(f̄) = ι(f)‾`. Both sides are ring
homomorphisms out of the polynomial ring on the power sums, and they agree on the generators because
the coefficients of `ι(p_k)` are `0` and `1`, which every ring homomorphism fixes, and on the
constants because `ι` is the structure map there. -/
theorem realisation_paramInvLambda (hι : IsRealisation ι) (τ : L ≃+* L) (g : Lambda L) :
    ι (paramInvLambda τ g) = paramInvSeries τ (ι g) := by
  have hX : ∀ i : ℕ, paramInvSeries τ (ι (MvPolynomial.X i)) = ι (MvPolynomial.X i) := by
    intro i
    refine MvPowerSeries.ext fun d => ?_
    rw [coeff_paramInvSeries,
      show (MvPolynomial.X i : Lambda L) = powerSum L (i + 1) from by
        rw [powerSum, Nat.add_sub_cancel]]
    by_cases h : ∃ j, d = Finsupp.single j (i + 1)
    · obtain ⟨j, rfl⟩ := h
      rw [hι.coeff_pow i j, map_one]
    · rw [hι.coeff_of_ne i d (by simpa using h), map_zero]
  have hC : ∀ a : L, paramInvSeries τ (ι (MvPolynomial.C a)) = ι (MvPolynomial.C (τ a)) := by
    intro a
    refine MvPowerSeries.ext fun d => ?_
    rw [coeff_paramInvSeries]
    change τ (MvPowerSeries.coeff d (ι (algebraMap L (Lambda L) a)))
      = MvPowerSeries.coeff d (ι (algebraMap L (Lambda L) (τ a)))
    rw [AlgHom.commutes, AlgHom.commutes]
    change τ (MvPowerSeries.coeff d (MvPowerSeries.C a))
      = MvPowerSeries.coeff d (MvPowerSeries.C (τ a))
    rw [MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
    split_ifs <;> simp
  induction g using MvPolynomial.induction_on with
  | C a => rw [paramInvLambda_C, hC a]
  | add p r hp hr =>
    simp only [map_add]
    rw [hp, hr]
  | mul_X p i hp =>
    simp only [map_mul, paramInvLambda_X]
    rw [hp, hX i]

/-- Inverting the parameters moves a scalar out of a scalar multiple. -/
theorem paramInvSeries_smul (τ : L ≃+* L) (c : L) (G : AlphabetSeries L) :
    paramInvSeries τ (c • G) = τ c • paramInvSeries τ G := by
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_paramInvSeries, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul,
    coeff_paramInvSeries, map_mul]

end HJO.Sym

namespace HJO.ParkingFunctions

/-- **A fundamental is fixed by inverting the parameters**: its coefficients are `0` and `1`. -/
theorem paramInvSeries_gessel {L : Type*} [CommRing L] (τ : L ≃+* L) (n : ℕ) (S : Finset ℕ) :
    Sym.paramInvSeries τ (gessel L n S) = gessel L n S := by
  refine MvPowerSeries.ext fun d => ?_
  rw [Sym.coeff_paramInvSeries]
  by_cases h : ∃ i : ℕ → ℕ, (∀ j ∈ Ico 1 n, i j ≤ i (j + 1)) ∧ (∀ j ∈ S, i j < i (j + 1)) ∧
      d = ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1
  · rw [coeff_gessel_eq_one L h, map_one]
  · rw [coeff_gessel_eq_zero L h, map_zero]

end HJO.ParkingFunctions

namespace HJO.Dyck

open HJO.Sym

/-- **The attacking pairs counted on the positions are the attacking cells.** `inv(R, ·)` reads `R`
as a set of pairs of positions `Fin n × Fin n` and `at(π)` counts pairs of naturals; the two agree,
every attacking cell having both coordinates below `n`. -/
theorem card_finPairs_attackSet {n : ℕ} (x : Fin n → ℕ) :
    #({p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ attackSet x} : Finset _) = attackNumber x := by
  classical
  have hinj : Function.Injective fun p : Fin n × Fin n => ((p.1 : ℕ), (p.2 : ℕ)) := by
    intro p p' h
    exact Prod.ext (Fin.val_inj.1 (congrArg Prod.fst h)) (Fin.val_inj.1 (congrArg Prod.snd h))
  rw [attackNumber, ← card_image_of_injective
    ({p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ attackSet x} : Finset _) hinj]
  congr 1
  refine Finset.ext fun p => ?_
  simp only [mem_image, mem_filter, mem_univ, true_and]
  refine ⟨fun ⟨r, hr, hrp⟩ => hrp ▸ hr, fun hp => ?_⟩
  have h2 : p.2 < n := snd_lt_of_mem_attackSet hp
  have h1 : p.1 < p.2 := fst_lt_snd_of_mem_attackSet hp
  exact ⟨(⟨p.1, by omega⟩, ⟨p.2, h2⟩), hp, rfl⟩

/-- **The involution on characteristic functions.** For a realisation `ι`, a
ring automorphism `τ` of the base inverting `q`, and `f ∈ Λ` with `ι f = χ(π)`,

`ι(ω̄ f) = (-1)^n q^{-at(π)} χ(π)`.

Inverting the parameters replaces `q` by `q⁻¹` in the fundamental expansion of
`HJO.Dyck.charSeries_eq_sum_gessel`; `HJO.ParkingFunctions.realisation_plethNegate_gessel` then
complements every inverse descent set and contributes `(-1)^n`; `HJO.gessel_reverse_sum` reflects
each complement, which `HJO.Sym.invDescentSet_trans_revPerm` identifies with the inverse descent set
of `σ^{rv}`; and reindexing by the involution `σ ↦ σ^{rv}`, whose effect on the inversion count is
`#R - inv(R,σ)` by `HJO.Dyck.invNumber_add_invNumber_revPerm`, turns `q⁻¹` back into `q` and leaves
the scalar `q^{-at(π)}`.

The usual hypotheses that `π` be a Dyck path and that `n ≥ 1` are not used: all the argument
reads of the attack set is that its pairs increase, which holds at every sequence `x`. `q ≠ 0` is
needed in this generality and is automatic over the coefficient field `𝕜 = ℚ(q,u)`. -/
@[hjo "lem_cm_chi_omega"]
theorem realisation_omegaBar_pathCharSeries {L : Type*} [Field L] [Algebra ℚ L]
    {ι : Lambda L →ₐ[L] AlphabetSeries L} (hι : IsRealisation ι) (τ : L ≃+* L) {q : L}
    (hq : q ≠ 0) (hτ : τ q = q⁻¹) {n : ℕ} {x : Fin n → ℕ} {f : Lambda L}
    (hf : ι f = pathCharSeries q x) :
    ι (omegaBar τ f) = ((-1 : L) ^ n * (q ^ attackNumber x)⁻¹) • pathCharSeries q x := by
  classical
  set R' : Finset (Fin n × Fin n) :=
    {p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ attackSet x} with hR'
  have hRlt : ∀ p ∈ R', p.1 < p.2 := by
    intro p hp
    rw [hR', mem_filter] at hp
    exact Fin.lt_def.2 (fst_lt_snd_of_mem_attackSet hp.2)
  set ee : Equiv.Perm (Fin n) → ℕ := fun σ => invNumber R' fun i => σ i with hee
  have hchi : pathCharSeries q x
      = ∑ σ : Equiv.Perm (Fin n), q ^ ee σ • gessel L n (invDescentSet σ) :=
    charSeries_eq_sum_gessel q n (attackSet x) fun p hp => fst_lt_snd_of_mem_attackSet hp
  have hbar : ι (paramInvLambda τ f)
      = ∑ σ : Equiv.Perm (Fin n), q⁻¹ ^ ee σ • gessel L n (invDescentSet σ) := by
    rw [realisation_paramInvLambda hι, hf, hchi, map_sum]
    exact Finset.sum_congr rfl fun σ _ => by
      rw [paramInvSeries_smul, paramInvSeries_gessel, map_pow, hτ]
  have homega := realisation_plethNegate_gessel hι n (Equiv.Perm (Fin n)) univ
    (fun σ => q⁻¹ ^ ee σ) (fun σ => invDescentSet σ)
    (fun σ _ => invDescentSet_subset_Ico σ) hbar
  have hstep : ι (omegaBar τ f) = ∑ σ : Equiv.Perm (Fin n),
      ((-1 : L) ^ n * q⁻¹ ^ ee σ) • gessel L n (Ico 1 n \ invDescentSet σ) := by
    rw [omegaBar_apply, homega, Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ => by rw [smul_smul]
  have hrev := HJO.gessel_reverse_sum ι hι n (Equiv.Perm (Fin n)) univ
    (fun σ => (-1 : L) ^ n * q⁻¹ ^ ee σ) (fun σ => Ico 1 n \ invDescentSet σ)
    (fun σ _ => sdiff_subset) (omegaBar τ f) hstep
  have hinv : Function.Involutive fun σ : Equiv.Perm (Fin n) => σ.trans Fin.revPerm := fun σ =>
    Equiv.ext fun i => by simp
  have hcount : ∀ σ : Equiv.Perm (Fin n), ee σ + ee (σ.trans Fin.revPerm) = #R' := fun σ =>
    invNumber_add_invNumber_revPerm R' hRlt (σ := fun i => σ i) σ.injective
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      ((-1 : L) ^ n * q⁻¹ ^ ee σ) • gessel L n (descentReverse n (Ico 1 n \ invDescentSet σ))
        = ((-1 : L) ^ n * q⁻¹ ^ ee σ) • gessel L n (invDescentSet (σ.trans Fin.revPerm)) :=
    fun σ => by rw [invDescentSet_trans_revPerm]
  rw [hrev, Finset.sum_congr rfl fun σ (_ : σ ∈ univ) => hterm σ]
  refine (Fintype.sum_bijective _ hinv.bijective _
    (fun ρ => ((-1 : L) ^ n * q⁻¹ ^ #R') • (q ^ ee ρ • gessel L n (invDescentSet ρ))) ?_).trans ?_
  · intro σ
    rw [smul_smul]
    congr 1
    have hqq : q⁻¹ * q = 1 := inv_mul_cancel₀ hq
    rw [← hcount σ, pow_add, mul_assoc, mul_assoc, ← mul_pow, hqq, one_pow, mul_one]
  · rw [← Finset.smul_sum, ← hchi, card_finPairs_attackSet, inv_pow]

end HJO.Dyck
