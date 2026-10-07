/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SignSum
public import HJO.CarlssonMellit.EqualPartnerLast
public import HJO.CarlssonMellit.Runs
public import HJO.CarlssonMellit.TwoLetterChar
public meta import HJO.Attr

/-! # The two values of the block sum, and the super sum over the whole alphabet

`HJO.Dyck.sum_pow_superInvNumber_smul_superMonomial` evaluates the block
`∑_{v ∈ 𝒜^n, |v| = u}q^{inv^±(R,v)}z_v` as `q^{inv(R,u)}x_u∏_i(q - q^{d_i(R,u)})`. This file reads
off the two values that expression takes and sums them over the blocks.

A factor `q - q^{d_i(R,u)}` vanishes exactly when `d_i(R,u) = 1`, and for a *transitive* attack set
`HJO.Sym.exists_equalPartners_eq_one` produces such a position as soon as some attacking pair of `u`
carries equal letters; so the block of an attacked `u` sums to `0`. At an unattacked `u` every
equal-partner count is `0`, so every factor is `q - 1` and the block sums to
`(q-1)^{n}q^{inv(R,u)}x_u`. The blocks partition `𝒜^n`, which leaves the super sum over the whole
alphabet as `(q-1)^{n}` times the no-attack sum.

## Main definitions

* `HJO.Dyck.noAttackSummand`: the summand `q^{inv(R,u)}x_u` of the no-attack sum, extended by `0` to
  the tuples that do attack.

## Main results

* `HJO.Dyck.mem_piFinset_letterFinset_of_coeff_superMonomial_ne_zero`: the finite set of super words
  that reach a given monomial, which is what every summability argument here names.
* `HJO.Dyck.equalPartners_finPairs`: the equal-partner count does not care whether the positions are
  read in `Fin n` or in `ℕ`, which is what lets the `ℕ`-indexed
  `HJO.Sym.exists_equalPartners_eq_one` be applied to a block of super words.
* `HJO.Dyck.sum_pow_superInvNumber_smul_superMonomial_eq_zero`.
* `HJO.Dyck.sum_pow_superInvNumber_smul_superMonomial_of_forall_ne`.
* `HJO.Dyck.summableSum_pow_superInvNumber_smul_superMonomial`.

## Implementation notes

*Two indexings of the pairs, bridged rather than duplicated.* `HJO.Sym.superInvNumber` is formed at
pairs of `Fin n`, while `HJO.Dyck.IsTransitiveAttackSet` and `HJO.Sym.exists_equalPartners_eq_one`
are stated for a `Finset (ℕ × ℕ)` — the shape an attack set `At(π)` has. `HJO.Dyck.finPairs` is the
coercion between them, as everywhere in this layer, and `HJO.Dyck.equalPartners_finPairs` is the one
piece of bookkeeping needed: the pairs counted by `d_i` have both entries inside the window, so
`Fin.val` is a bijection between the two descriptions. No second copy of the maximality argument of
`HJO.Sym.exists_equalPartners_eq_one` is made.

*The sum over all of `𝒜^n` is `HJO.Sym.summableSum`, not a `Finset.sum`.* The sums
`∑_{v ∈ 𝒜^n}` and `∑_u` are both infinite, and both are formed here the way this layer forms an
infinite sum of series: as the sum of a family whose summability — only finitely many members reach
a given monomial — is proved separately, in
`HJO.Dyck.isSummableFamily_pow_superInvNumber_smul_superMonomial` and
`HJO.Dyck.isSummableFamily_noAttackSummand`. Both proofs are the one in
`HJO.Sym.isSummableFamily_superFundamental`: a word reaching `x^d` has every letter, or every
absolute value, in the support of `d`. That same bound is what makes the regrouping by blocks a
finite regrouping at each monomial.

*The no-attack sum is a family over all tuples, with the attacked ones sent to `0`.* The
second sum runs over a subset of `ℤ_{>0}^n`; written as `HJO.Dyck.noAttackSummand` it needs no
subtype, and the summability argument reads the same at every index.

*Hypotheses dropped.* `HJO.Dyck.sum_pow_superInvNumber_smul_superMonomial_of_forall_ne` is stated
here at an arbitrary `R : Finset (Fin n × Fin n)`: the containment `R ⊆ {(j,j') : j < j'}` is not
used, as it is not used by `HJO.Dyck.sum_pow_superInvNumber_smul_superMonomial`, and the positivity
of the entries of `u` is vacuous with letters indexed from `0`.
`HJO.Dyck.sum_pow_superInvNumber_smul_superMonomial_eq_zero` and
`HJO.Dyck.summableSum_pow_superInvNumber_smul_superMonomial` keep transitivity, which
`HJO.Sym.exists_equalPartners_eq_one` genuinely needs; the `n ≥ 0` is no hypothesis at all.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer.
Math. Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

open HJO.Sym

variable {n : ℕ} {K : Type*} [CommRing K]

/-! ### The equal-partner count in the two indexings -/

/-- **The equal-partner count is the same in both indexings of the positions.** The pairs of `R`
counted by `d_i` have both entries inside the window `< n` — the second by hypothesis, the first
because it is `i` — so `Fin.val` is a bijection from the pairs counted at `i : Fin n` for
`HJO.Dyck.finPairs n R` onto those counted at `(i : ℕ)` for `R`. This is the bridge that lets
`HJO.Sym.exists_equalPartners_eq_one`, stated on `ℕ`, be read on a block of super words. -/
theorem equalPartners_finPairs {R : Finset (ℕ × ℕ)} (hR : ∀ p ∈ R, p.2 < n) (u : Fin n → ℕ)
    (i : Fin n) : equalPartners (finPairs n R) u i = equalPartners R (wordOfFin u) (i : ℕ) := by
  rw [equalPartners, equalPartners]
  refine Finset.card_nbij (fun p => ((p.1 : ℕ), (p.2 : ℕ))) (fun p hp => ?_)
    (fun p _ p' _ hpp' => ?_) fun c hc => ?_
  · rw [Finset.mem_coe, mem_filter, mem_finPairs] at hp
    rw [Finset.mem_coe, mem_filter]
    dsimp only
    refine ⟨hp.1, congrArg Fin.val hp.2.1, ?_⟩
    rw [wordOfFin_val, wordOfFin_val]
    exact hp.2.2
  · obtain ⟨e1, e2⟩ := Prod.mk.injEq .. ▸ hpp'
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  · rw [Finset.mem_coe, mem_filter] at hc
    have h2 : c.2 < n := hR c hc.1
    have h1 : c.1 < n := hc.2.1 ▸ i.isLt
    refine ⟨(⟨c.1, h1⟩, ⟨c.2, h2⟩), ?_, rfl⟩
    rw [Finset.mem_coe, mem_filter, mem_finPairs]
    refine ⟨hc.1, Fin.ext hc.2.1, ?_⟩
    have hval := hc.2.2
    rwa [wordOfFin_of_lt u h2, wordOfFin_val] at hval

/-! ### The block at an attacked word -/

/-- **The sum over the signs vanishes at an attacked labelling.** For a
transitive attack set `R` on `{1, …, n}` and a word `u` giving equal letters to the two positions of
some attacking pair, `∑_{v ∈ 𝒜^n, |v| = u}q^{inv^±(R,v)}z_v = 0`.

By `HJO.Sym.exists_equalPartners_eq_one` some position `i^*` has exactly one attack partner of its
own letter, and `HJO.Dyck.sum_pow_superInvNumber_smul_superMonomial` factors the block sum with
`q - q^{d_{i^*}(R,u)} = q - q = 0` among its factors. -/
@[hjo "lem_cm_sign_sum_vanishes"]
theorem sum_pow_superInvNumber_smul_superMonomial_eq_zero (K : Type*) [CommRing K] (q : K)
    {n : ℕ} {R : Finset (ℕ × ℕ)} (hR : IsTransitiveAttackSet n R) (u : Fin n → ℕ) {i j : Fin n}
    (hij : ((i : ℕ), (j : ℕ)) ∈ R) (hu : u i = u j) :
    ∑ v ∈ superFibre u, q ^ superInvNumber (finPairs n R) v • superMonomial K q v = 0 := by
  obtain ⟨i', hi'n, hone⟩ :=
    exists_equalPartners_eq_one (u := wordOfFin u) hR hij (by rw [wordOfFin_val, wordOfFin_val, hu])
  have hzero : q - q ^ equalPartners (finPairs n R) u ⟨i', hi'n⟩ = 0 := by
    rw [equalPartners_finPairs (fun p hp => hR.snd_lt p hp) u ⟨i', hi'n⟩,
      show ((⟨i', hi'n⟩ : Fin n) : ℕ) = i' from rfl, hone, pow_one, sub_self]
  rw [sum_pow_superInvNumber_smul_superMonomial, Finset.prod_eq_zero (Finset.mem_univ ⟨i', hi'n⟩)
    hzero, mul_zero, zero_smul]

/-! ### The block at an unattacked word -/

/-- At a word giving distinct letters to the two positions of every attacking pair, every
equal-partner count is `0`: a partner counted at `i` would be the second entry of a pair of `R`
carrying the letter of the first. -/
theorem equalPartners_eq_zero_of_forall_ne {R : Finset (Fin n × Fin n)} {u : Fin n → ℕ}
    (hu : ∀ p ∈ R, u p.1 ≠ u p.2) (i : Fin n) : equalPartners R u i = 0 := by
  rw [equalPartners, Finset.card_eq_zero]
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  rw [mem_filter] at hp
  exact hu p hp.1 (hp.2.1 ▸ hp.2.2.symm)

/-- **The sum over the signs at an unattacked labelling.** For a word
`u` giving distinct letters to the two positions of every pair of `R`,
`∑_{v ∈ 𝒜^n, |v| = u}q^{inv^±(R,v)}z_v = (q-1)^{n}q^{inv(R,u)}x_u`.

Every equal-partner count is `0`, so each of the `n` factors of
`HJO.Dyck.sum_pow_superInvNumber_smul_superMonomial` is `q - q^{0}`. The containment
`R ⊆ {(j,j') : j < j'}` is not used, nor is the positivity of the entries of `u`. -/
@[hjo "lem_cm_sign_sum_noattack"]
theorem sum_pow_superInvNumber_smul_superMonomial_of_forall_ne (K : Type*) [CommRing K] (q : K)
    {n : ℕ} {R : Finset (Fin n × Fin n)} {u : Fin n → ℕ} (hu : ∀ p ∈ R, u p.1 ≠ u p.2) :
    ∑ v ∈ superFibre u, q ^ superInvNumber R v • superMonomial K q v
      = ((q - 1) ^ n * q ^ invNumber R u) • wordMonomial K u := by
  rw [sum_pow_superInvNumber_smul_superMonomial,
    Finset.prod_congr rfl fun i (_ : i ∈ (univ : Finset (Fin n))) =>
      show q - q ^ equalPartners R u i = q - 1 by
        rw [equalPartners_eq_zero_of_forall_ne hu i, pow_zero],
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]

/-! ### Summability of the two families -/

/-- **A super word whose monomial reaches `x^d` has every absolute value in the support of `d`**:
`z_v` is a scalar times `∏_i x_{|v_i|}`, whose exponent vector has every `|v_i|` in its support.
This is the bound behind every summability statement about super words, isolated so that the
finite set it names can be chosen rather than merely known to exist. -/
theorem mem_piFinset_letterFinset_of_coeff_superMonomial_ne_zero (q : K) {d : ℕ →₀ ℕ}
    {v : Fin n → SuperLetter} (hv : MvPowerSeries.coeff d (superMonomial K q v) ≠ 0) :
    v ∈ Fintype.piFinset fun _ : Fin n => letterFinset d.support := by
  simp only [Fintype.mem_piFinset, mem_letterFinset]
  intro i
  rw [superMonomial, coeff_prod_superVar] at hv
  by_cases hd : d = ∑ j : Fin n, Finsupp.single (v j).absVal 1
  · rw [hd]
    exact absVal_mem_support_sum univ v (mem_univ i)
  · exact absurd (ite_eq_right hd) hv

/-- The same bound for a scalar multiple of the monomial, which is the shape the super sum's
summands have. -/
theorem mem_piFinset_letterFinset_of_coeff_ne_zero (q : K) (R : Finset (Fin n × Fin n))
    {d : ℕ →₀ ℕ} {v : Fin n → SuperLetter}
    (hv : MvPowerSeries.coeff d (q ^ superInvNumber R v • superMonomial K q v) ≠ 0) :
    v ∈ Fintype.piFinset fun _ : Fin n => letterFinset d.support := by
  refine mem_piFinset_letterFinset_of_coeff_superMonomial_ne_zero q fun h => hv ?_
  rw [show MvPowerSeries.coeff d (q ^ superInvNumber R v • superMonomial K q v)
    = q ^ superInvNumber R v * MvPowerSeries.coeff d (superMonomial K q v) from rfl, h, mul_zero]

/-- The super words reaching a given monomial lie in a finite set, so the family the super sum is
formed from is summable. -/
theorem isSummableFamily_pow_superInvNumber_smul_superMonomial (q : K)
    (R : Finset (Fin n × Fin n)) :
    IsSummableFamily fun v : Fin n → SuperLetter =>
      q ^ superInvNumber R v • superMonomial K q v :=
  pointwiseFinite_of_forall_exists_finset fun _d =>
    ⟨_, fun _ hv => mem_piFinset_letterFinset_of_coeff_ne_zero q R hv⟩

/-- **The summand of the no-attack sum**: the `q^{inv(R,u)}x_u` at a tuple `u` giving
distinct letters to the two positions of every pair of `R`, and `0` at every other tuple. Written
this way the sum over a subset of `ℤ_{>0}^n` is a family indexed by all tuples. -/
noncomputable def noAttackSummand (K : Type*) [CommRing K] (q : K) {n : ℕ}
    (R : Finset (Fin n × Fin n)) (u : Fin n → ℕ) : AlphabetSeries K :=
  if ∀ p ∈ R, u p.1 ≠ u p.2 then q ^ invNumber R u • wordMonomial K u else 0

/-- A tuple whose no-attack summand reaches `x^d` has every letter in the support of `d`. -/
theorem mem_piFinset_support_of_coeff_noAttackSummand_ne_zero (q : K)
    (R : Finset (Fin n × Fin n)) {d : ℕ →₀ ℕ} {u : Fin n → ℕ}
    (hu : MvPowerSeries.coeff d (noAttackSummand K q R u) ≠ 0) :
    u ∈ Fintype.piFinset fun _ : Fin n => d.support := by
  simp only [Fintype.mem_piFinset]
  intro i
  rw [noAttackSummand] at hu
  by_cases hadm : ∀ p ∈ R, u p.1 ≠ u p.2
  · rw [ite_eq_left hadm,
      show MvPowerSeries.coeff d (q ^ invNumber R u • wordMonomial K u)
        = q ^ invNumber R u * MvPowerSeries.coeff d (wordMonomial K u) from rfl,
      coeff_wordMonomial] at hu
    by_cases hd : d = wordExponent u
    · rw [hd]
      exact (mem_support_wordExponent u (u i)).2 ⟨i, rfl⟩
    · exact absurd (by rw [ite_eq_right hd, mul_zero]) hu
  · exact absurd (by rw [ite_eq_right hadm, map_zero]) hu

/-- The tuples reaching a given monomial lie in a finite set, so the no-attack family is
summable. -/
theorem isSummableFamily_noAttackSummand (q : K) (R : Finset (Fin n × Fin n)) :
    IsSummableFamily fun u : Fin n → ℕ => noAttackSummand K q R u :=
  pointwiseFinite_of_forall_exists_finset fun _d =>
    ⟨_, fun _ hu => mem_piFinset_support_of_coeff_noAttackSummand_ne_zero q R hu⟩

/-! ### The super sum over the whole alphabet -/

/-- The block of a tuple with letters in a finite set `s` consists of words with letters of absolute
value in `s`: the inclusion that makes the blocks a partition of the words bounded by `s`. -/
theorem superFibre_subset {u : Fin n → ℕ} {s : Finset ℕ} (hu : ∀ i, u i ∈ s) :
    superFibre u ⊆ Fintype.piFinset fun _ : Fin n => letterFinset s := fun v hv =>
  Fintype.mem_piFinset.2 fun i => mem_letterFinset.2 (by
    rw [← superAbs_apply, mem_superFibre.1 hv]; exact hu i)

/-- The words with letters of absolute value in `s` are partitioned by their absolute values: the
block of a tuple with letters in `s` is exactly the part of the fibre of `HJO.Sym.superAbs`. -/
theorem filter_superAbs_eq_superFibre {u : Fin n → ℕ} {s : Finset ℕ} (hu : ∀ i, u i ∈ s) :
    {v ∈ Fintype.piFinset fun _ : Fin n => letterFinset s | superAbs v = u} = superFibre u := by
  refine Finset.ext fun v => ?_
  rw [mem_filter, mem_superFibre]
  exact ⟨fun h => h.2, fun h => ⟨superFibre_subset hu (mem_superFibre.2 h), h⟩⟩

/-- **The super sum is the no-attack sum.** For a transitive attack set
`R` on `{1, …, n}`,
`∑_{v ∈ 𝒜^n}q^{inv^±(R,v)}z_v = (q-1)^{n}∑_{u}q^{inv(R,u)}x_u`, the second sum over the tuples
giving distinct letters to the two positions of every attacking pair.

The blocks `{v : |v| = u}` partition `𝒜^n`, so at a fixed monomial the left side is the sum of the
block sums over the finitely many tuples with letters in the support of that monomial;
`HJO.Dyck.sum_pow_superInvNumber_smul_superMonomial_eq_zero` kills the attacked blocks and
`HJO.Dyck.sum_pow_superInvNumber_smul_superMonomial_of_forall_ne` evaluates the others, which is the
right side coefficient by coefficient. -/
@[hjo "lem_cm_super_sum_noattack"]
theorem summableSum_pow_superInvNumber_smul_superMonomial (K : Type*) [CommRing K] (q : K) {n : ℕ}
    {R : Finset (ℕ × ℕ)} (hR : IsTransitiveAttackSet n R) :
    summableSum (fun v : Fin n → SuperLetter =>
        q ^ superInvNumber (finPairs n R) v • superMonomial K q v)
      = (q - 1) ^ n • summableSum fun u : Fin n → ℕ => noAttackSummand K q (finPairs n R) u := by
  classical
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_summableSum_eq_sum (s := Fintype.piFinset fun _ : Fin n => letterFinset d.support)
      fun _ hv => mem_piFinset_letterFinset_of_coeff_ne_zero q (finPairs n R) hv,
    ← Finset.sum_fiberwise_of_maps_to (g := superAbs)
      (t := Fintype.piFinset fun _ : Fin n => d.support)
      (fun v hv => Fintype.mem_piFinset.2 fun i =>
        mem_letterFinset.1 (Fintype.mem_piFinset.1 hv i))
      fun v => MvPowerSeries.coeff d (q ^ superInvNumber (finPairs n R) v • superMonomial K q v),
    show MvPowerSeries.coeff d ((q - 1) ^ n •
        summableSum fun u : Fin n → ℕ => noAttackSummand K q (finPairs n R) u)
      = (q - 1) ^ n * MvPowerSeries.coeff d
        (summableSum fun u : Fin n → ℕ => noAttackSummand K q (finPairs n R) u) from rfl,
    coeff_summableSum_eq_sum (s := Fintype.piFinset fun _ : Fin n => d.support)
      fun _ hu => mem_piFinset_support_of_coeff_noAttackSummand_ne_zero q (finPairs n R) hu,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hus : ∀ i, u i ∈ d.support := Fintype.mem_piFinset.1 hu
  rw [filter_superAbs_eq_superFibre hus, ← map_sum, noAttackSummand]
  by_cases hadm : ∀ p ∈ finPairs n R, u p.1 ≠ u p.2
  · rw [ite_eq_left hadm,
      sum_pow_superInvNumber_smul_superMonomial_of_forall_ne K q hadm,
      show MvPowerSeries.coeff d (((q - 1) ^ n * q ^ invNumber (finPairs n R) u) •
          wordMonomial K u)
        = ((q - 1) ^ n * q ^ invNumber (finPairs n R) u) *
          MvPowerSeries.coeff d (wordMonomial K u) from rfl,
      show MvPowerSeries.coeff d (q ^ invNumber (finPairs n R) u • wordMonomial K u)
        = q ^ invNumber (finPairs n R) u * MvPowerSeries.coeff d (wordMonomial K u) from rfl,
      mul_assoc]
  · obtain ⟨p, hp, hpu⟩ := by
      simpa only [not_forall, exists_prop, not_not] using hadm
    rw [ite_eq_right hadm, map_zero, mul_zero,
      sum_pow_superInvNumber_smul_superMonomial_eq_zero K q hR u (i := p.1) (j := p.2)
        (mem_finPairs.1 hp) hpu, map_zero]

end HJO.Dyck
