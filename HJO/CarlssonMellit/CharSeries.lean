/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Fintype.Perm
public import HJO.CarlssonMellit.MarkedCharSeries
public import HJO.Classical.StdFibre
public meta import HJO.Attr

/-! # The characteristic series of an attack set, and its fundamental expansion

Two definitions and one lemma. The unconstrained characteristic series `χ(R, n)` is the marked
series of `HJO.Dyck.markedCharSeries` at the empty marking, and `χ(π)` is that at the attack set of
a path; their fundamental expansion groups the labellings by their standardisation.

## Main definitions

* `HJO.Dyck.charSeries`: `χ(R, n)`.
* `HJO.Dyck.pathCharSeries`: `χ(π)`.

## Main statements

* `HJO.Dyck.coeff_charSeries_eq_coeff_sum_wordMonomial`: `HJO.Dyck.charSeries` in its
  defining display, `χ(R, n) = ∑_w q^{inv(R,w)}x_w`.
* `HJO.Dyck.charSeries_eq_sum_gessel`.

## Implementation notes

`χ(R, n)` is *defined* as `markedCharSeries q n R ∅` rather than written out again, as the
implementation notes of `HJO.CarlssonMellit.MarkedCharSeries` ask: `IsMarkedLabelling ∅` is
vacuous, so the marked series at the empty marking sums over all labellings. Everything that file
proves about `markedCharSeries` therefore applies verbatim, in particular that the series is built
one coefficient at a time because the sum has infinitely many terms.

`HJO.Dyck.charSeries_eq_sum_gessel` is an honest `Finset.sum`: its index set is the permutations of
the `n` positions, a finite type. The hypothesis that `R` consist of increasing pairs is the
condition `R ⊆ \{(j,j') : 1 ≤ j < j' ≤ n\}` of the statement as usually given and is needed — it is
what `HJO.Dyck.invSet_std` consumes, the tie-breaking clause of `HJO.Sym.std_lt_std_iff` being
invisible only across an increasing pair. The usual condition `n ≥ 1` is not needed: at `n = 0` both
sides are `1`.

The exponent `inv(R, σ)` is read with `σ` as a labelling by *positions*, its values being compared
in `Fin n`; `HJO.Dyck.invNumber_fin_std` is the identification with `inv(R, w)` for a word `w`
standardising to `σ`, and it is `HJO.Dyck.invSet_std` plus the fact that the order on `Fin n` is the
order on the values.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §3.1. -/

@[expose] public section

open Finset HJO.Sym HJO.ParkingFunctions

namespace HJO.Dyck

/-! ### The characteristic series -/

/-- **The characteristic series of an attack set**
`χ(R, n) = ∑_w q^{inv(R,w)}x_w`, the sum over all labellings `w` of the `n` positions. It is the
marked series at the empty marking, `IsMarkedLabelling ∅` being vacuous. -/
@[hjo "def_cm_chi_set"]
noncomputable abbrev charSeries {K : Type*} [CommRing K] (q : K) (n : ℕ) (R : Finset (ℕ × ℕ)) :
    AlphabetSeries K :=
  markedCharSeries q n R ∅

/-- **The characteristic series of a Dyck path** `χ(π) = χ(At(π), n)`, where `π` has
coarea sequence `x`: the labellings of its `n` rows, each weighted by `q` to the number of attacking
pairs it inverts. -/
@[hjo "def_cm_chi"]
noncomputable abbrev pathCharSeries {K : Type*} [CommRing K] (q : K) {n : ℕ} (x : Fin n → ℕ) :
    AlphabetSeries K :=
  charSeries q n (attackSet x)

variable {K : Type*} [CommRing K] {q : K} {n : ℕ} {R : Finset (ℕ × ℕ)} {d : ℕ →₀ ℕ}

/-- The labellings the unconstrained series sums over at a given monomial: all of them, the empty
marking imposing nothing. -/
theorem filter_isMarkedLabelling_empty (s : Finset ℕ) :
    {w ∈ Fintype.piFinset fun _ : Fin n => s | wordExponent w = d ∧ IsMarkedLabelling ∅ w}
      = {w ∈ Fintype.piFinset fun _ : Fin n => s | wordExponent w = d} :=
  filter_congr fun w _ => and_iff_left (isMarkedLabelling_empty w)

/-- **The defining property of `χ(R, n)`**: the coefficient of the monomial with exponent vector `d`
is the finite sum of `q^{inv(R,w)}` over the labellings `w` with that exponent vector. -/
theorem coeff_charSeries :
    MvPowerSeries.coeff d (charSeries q n R) =
      ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin n => d.support | wordExponent w = d},
        q ^ #(invSet {p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ R} w) := by
  rw [coeff_markedCharSeries, filter_isMarkedLabelling_empty]

/-- **`HJO.Dyck.charSeries` is the display**: on the monomials supported in a finite set `s`
of letters, `χ(R, n)` agrees with the honest finite sum of `q^{inv(R,w)}x_w` over the labellings
with
letters in `s`. Every monomial is supported in some such `s`, so this determines the series; the sum
over *all* labellings cannot be formed in `𝒫`, which is why the definition is coefficientwise. -/
@[hjo "def_cm_chi_set"]
theorem coeff_charSeries_eq_coeff_sum_wordMonomial {s : Finset ℕ} (hs : d.support ⊆ s) :
    MvPowerSeries.coeff d (charSeries q n R) =
      MvPowerSeries.coeff d (∑ w ∈ Fintype.piFinset fun _ : Fin n => s,
        q ^ #(invSet {p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ R} w) • wordMonomial K w) := by
  rw [coeff_markedCharSeries_eq_coeff_sum_wordMonomial hs,
    filter_true_of_mem fun w (_ : w ∈ Fintype.piFinset fun _ : Fin n => s) =>
      isMarkedLabelling_empty w]

/-- **`HJO.Dyck.pathCharSeries` is the display**, the same statement at the attack set of a path. -/
@[hjo "def_cm_chi"]
theorem coeff_pathCharSeries_eq_coeff_sum_wordMonomial {x : Fin n → ℕ} {s : Finset ℕ}
    (hs : d.support ⊆ s) :
    MvPowerSeries.coeff d (pathCharSeries q x) =
      MvPowerSeries.coeff d (∑ w ∈ Fintype.piFinset fun _ : Fin n => s,
        q ^ #(invSet {p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ attackSet x} w) •
          wordMonomial K w) :=
  coeff_charSeries_eq_coeff_sum_wordMonomial hs

/-! ### The fundamental expansion -/

/-- **The inversion count of a word is that of its standardisation, read as a permutation.** For a
set of increasing pairs, `HJO.Dyck.invSet_std` replaces the word by its standardisation, and the
order on the positions is the order on the values of the permutation. -/
theorem invNumber_fin_std {R' : Finset (Fin n × Fin n)} (hR : ∀ p ∈ R', p.1 < p.2)
    {w : Fin n → ℕ} {σ : Equiv.Perm (Fin n)} (hw : stdPerm w = σ) :
    invNumber R' w = invNumber R' fun i => σ i := by
  have h : invSet R' (Sym.std w) = invSet R' fun i => σ i := by
    rw [invSet, invSet]
    refine filter_congr fun p _ => ?_
    rw [stdPerm_eq_iff] at hw
    rw [Fin.lt_def, hw p.2, hw p.1]
  rw [invNumber, invNumber, invSet_std R' hR w, h]

/-- Two labellings with the same exponent vector and the same standardisation are equal: listed in
the order the standardisation ranks them both become the *same* weakly increasing word, and a weakly
increasing word is determined by its exponent vector. -/
theorem eq_of_stdPerm_eq_of_wordExponent_eq {w w' : Fin n → ℕ} {σ : Equiv.Perm (Fin n)}
    (hw : stdPerm w = σ) (hw' : stdPerm w' = σ) (hd : wordExponent w = wordExponent w') :
    w = w' := by
  have ha := (isAscendingWord_comp_symm_iff σ w).2 hw
  have ha' := (isAscendingWord_comp_symm_iff σ w').2 hw'
  have hcomp : w ∘ σ.symm = w' ∘ σ.symm :=
    eq_of_monotone_of_wordExponent_eq ha.monotone ha'.monotone
      (by rw [wordExponent_comp_equiv, wordExponent_comp_equiv, hd])
  funext i
  have := congrFun hcomp (σ i)
  simpa using this

/-- **The fundamental expansion of the characteristic series.**
`χ(R, n) = ∑_σ q^{inv(R,σ)}F_{n,Des(σ⁻¹)}`, the sum over the permutations of the `n` positions.

The standardisation sends the labellings to the permutations, so the defining sum may be taken over
its fibres; `HJO.Dyck.invSet_std` makes the exponent of `q` constant on a fibre, and
`HJO.ParkingFunctions.sum_wordMonomial_stdPerm` sums the fibre to the fundamental of the inverse
descent set. Coefficient by coefficient that is a bijection between the labellings carrying a given
monomial and the permutations whose fibre carries it. -/
@[hjo "lem_cm_chi_gessel"]
theorem charSeries_eq_sum_gessel (q : K) (n : ℕ) (R : Finset (ℕ × ℕ))
    (hR : ∀ p ∈ R, p.1 < p.2) :
    charSeries q n R
      = ∑ σ : Equiv.Perm (Fin n),
          q ^ invNumber {p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ R} (fun i => σ i)
            • gessel K n (invDescentSet σ) := by
  classical
  set R' : Finset (Fin n × Fin n) := {p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ R} with hR'
  have hRlt : ∀ p ∈ R', p.1 < p.2 := by
    intro p hp
    rw [hR', mem_filter] at hp
    exact Fin.lt_def.2 (hR _ hp.2)
  refine MvPowerSeries.ext fun d => ?_
  have hrhs : MvPowerSeries.coeff d (∑ σ : Equiv.Perm (Fin n),
        q ^ invNumber R' (fun i => σ i) • gessel K n (invDescentSet σ))
      = ∑ σ ∈ {σ : Equiv.Perm (Fin n) | ∃ w : Fin n → ℕ, stdPerm w = σ ∧ wordExponent w = d},
          q ^ invNumber R' (fun i => σ i) := by
    rw [map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_smul, smul_eq_mul]
    by_cases h : ∃ w : Fin n → ℕ, stdPerm w = σ ∧ wordExponent w = d
    · rw [coeff_gessel_invDescentSet_eq_one K h, mul_one, ite_eq_left h]
    · rw [coeff_gessel_invDescentSet_eq_zero K h, mul_zero, ite_eq_right h]
  rw [coeff_charSeries, hrhs]
  refine Finset.sum_nbij (fun w => stdPerm w) (fun w hw => ?_) (fun w hw w' hw' hst => ?_)
    (fun σ hσ => ?_) fun w hw => ?_
  · rw [mem_filter] at hw
    exact mem_filter.2 ⟨mem_univ _, ⟨w, rfl, hw.2⟩⟩
  · rw [mem_coe, mem_filter] at hw hw'
    exact eq_of_stdPerm_eq_of_wordExponent_eq hst rfl (hw.2.trans hw'.2.symm)
  · rw [mem_coe, mem_filter] at hσ
    obtain ⟨w, hw, hd⟩ := hσ.2
    refine ⟨w, ?_, hw⟩
    rw [mem_coe, mem_filter, Fintype.mem_piFinset]
    exact ⟨fun k => hd ▸ (mem_support_wordExponent w (w k)).2 ⟨k, rfl⟩, hd⟩
  · rw [mem_filter] at hw
    rw [← invNumber, invNumber_fin_std hRlt (σ := stdPerm w) rfl]

end HJO.Dyck
