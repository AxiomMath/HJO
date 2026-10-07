/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import HJO.SignExtraction.Basic
public meta import HJO.Attr

/-! # The fundamental quasisymmetric functions are linearly independent

Gessel's fundamental quasisymmetric functions `F_{n,S}`, one for each set of steps `S` inside the
window `{1, …, n-1}`, are linearly independent over the coefficient ring. The witness separating
them is the *minimal ascending word* `w^{n,S}`, the tuple whose entry at a position is the number
of steps of `S` at or before it: it climbs by one at each step of `S` and stays put at every other
step, so it is an `S'`-ascending word exactly when every step of `S'` inside the window is a step
of `S`. Since a word is recovered from its exponent vector, the coefficient of `F_{n,S'}` at the
monomial `x^{𝐝(w^{n,S})}` is therefore `1` for `S' ⊆ S` and `0` otherwise, which is the
triangularity the independence is read off.

The elimination is one line rather than the induction on `#T`. Reading a relation
`∑_S a_S F_{n,S} = 0` at the monomial of `w^{n,T}` gives `∑_{S ⊆ T} a_S = 0`; taking `T` of least
cardinality in the support, an `S` in the support with `S ⊆ T` has `#T ≤ #S`, hence `S = T`, so the
sum is the single term `a_T` and `T` was not in the support after all. No division is used, so the
statement holds over an arbitrary commutative coefficient ring, not only over a field.

Together with the spanning statements for the fundamentals this is what lets a quasisymmetric
identity be proved coefficient by coefficient: two expansions in the `F_{n,S}` agree only if their
coefficients agree.

## Main definitions

* `HJO.Sym.minAscendingWord`: the minimal `S`-ascending word `w^{n,S}` of length `n`, as a tuple
  `Fin n → ℕ`.

## Main results

* `HJO.Sym.isAscendingWord_minAscendingWord_iff`: `w^{n,S}` is an `S'`-ascending word of length `n`
  if and only if every step of `S'` lying in the window `{1, …, n-1}` is a step of `S`.
* `HJO.ParkingFunctions.coeff_wordExponent_minAscendingWord_gessel` and
  `HJO.ParkingFunctions.coeff_wordExponent_minAscendingWord_gessel_eq_zero_of_not_subset`: the
  coefficient of `F_{n,S'}` at `x^{𝐝(w^{n,S})}` is `1` when `S' ⊆ S` and `0` otherwise.
* `HJO.ParkingFunctions.linearIndepOn_gessel`: the family `S ↦ F_{n,S}`, restricted to the sets of
  steps contained in the window `{1, …, n-1}`, is linearly independent over `K`.

## Implementation notes

The conventions are those already fixed for the words of this library,
`HJO.Sym.IsAscendingWord` and `HJO.Sym.wordExponent`: a word `(i_1, …, i_n)` of length `n` is a
tuple `Fin n → ℕ` whose value at the `0`-based position `k` is `i_{k+1}`, the alphabet is indexed
from `0` so that the letter `x_i` of the `1`-based numbering is the letter `i - 1` here, and a
descent set `S : Finset ℕ` stays `1`-based, the step `j ∈ S` being the step into the `0`-based
position `j`. Under that reindexing the `1`-based entry `1 + #(S ∩ {1, …, j-1})` at the position
`j = k + 1` is
`#(S ∩ Icc 1 k)`, which is why `minAscendingWord` adds no `1`: keeping it would name a tuple that
is *not* the minimal ascending word, while changing nothing about the membership and coefficient
statements, which are invariant under a uniform shift of the alphabet.

Neither `minAscendingWord` nor the membership criterion carries a hypothesis. The criterion is
usually stated under `n ≥ 1` and `S, S' ⊆ {1, …, n-1}` with conclusion `S' ⊆ S`; neither hypothesis
on `S` nor the bound `n ≥ 1` is used, and the hypothesis on `S'` is used only to rewrite
`S' ∩ {1, …, n-1}` as `S'`, so the form here is the hypothesis-free equivalence whose right-hand
side is `S' ∩ Finset.Ico 1 n ⊆ S`. That is strictly stronger: `IsAscendingWord n S' w` constrains a
step `l ∈ S'` only through a pair of positions `k, l : Fin n` with `k + 1 = l`, and such a pair
exists exactly for `1 ≤ l < n`, so steps of `S'` outside the window are inert on the left and must
be discarded on the right — `w^{3,∅}` is a `{0,5}`-ascending word while `{0,5} ⊄ ∅`.

The minimal ascending word is the step count of `HJO.Sym.stepCount` with the value `0` discarded:
`minAscendingWord n S k = stepCount (S.erase 0) k`, the intersection with `Icc 1 k` cutting off
exactly the element `0`. That identification is what lets the step-count arithmetic already proved
for the word count serve here unchanged.

The independence is usually stated as an implication about a family of scalars: given `a_S ∈ 𝕜`
for each `S ⊆ {1, …, n-1}` with `∑_S a_S F_{n,S} = 0`, every `a_S` is `0`. That is exactly
Mathlib's `LinearIndepOn K (gessel K n) {S | S ⊆ Ico 1 n}`, stated here because it is the concept
and it carries the API (`LinearIndepOn.mono`, `LinearIndepOn.injOn`, the span and basis machinery)
that the implication does not; `linearIndepOn_finset_iff` returns that
implication in one step.

The window `{1, …, n-1}` is the index set rather than a hypothesis because the statement is false
without it: `gessel` is total in `S`, and a step outside the window constrains only the auxiliary
sequence beyond the `n` positions a word occupies, where it is freely satisfiable, so distinct such
sets can name the same series — `gessel K 2 {5} = gessel K 2 ∅` is a non-trivial relation over any
non-trivial `K`. The `n ≥ 1` is dead: at `n = 0` the window is empty, the index set is
the singleton `{∅}`, and `F_{0,∅} = 1` has coefficient `1` at the empty monomial.

The coefficient ring is an arbitrary `CommRing K`, weaker than a field `𝕜`, the triangular
elimination being integral; and the ambient ring is the one `gessel` is valued in,
`HJO.Sym.AlphabetSeries K = MvPowerSeries ℕ K`, the ring `𝒫` of power series in the alphabet,
whose `K`-module structure is the one the linear combination is formed in.

## References

The file formalises the definition `HJO.Sym.minAscendingWord` and the lemmas
`HJO.Sym.isAscendingWord_minAscendingWord_iff`,
`HJO.ParkingFunctions.coeff_wordExponent_minAscendingWord_gessel`,
`HJO.ParkingFunctions.coeff_wordExponent_minAscendingWord_gessel_eq_zero_of_not_subset` and
`HJO.ParkingFunctions.linearIndepOn_gessel`; the consumers of the last are
`HJO.Dyck.charSeries_eq_sum_gessel`, `HJO.ParkingFunctions.realisation_completeHomogComp` and
`HJO.Sym.schurSeries_eq_sum_gessel`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The minimal ascending word of a descent set -/

/-- The minimal `S`-ascending word `w^{n,S}` of length `n`: the tuple whose entry at the `0`-based
position `k` is the number of steps of `S` in `{1, …, k}`, that is, the number of steps of `S`
strictly before the position. In the `1`-based numbering of positions and letters its
`j`-th entry is `1 + #(S ∩ {1, …, j-1})`; the alphabet being indexed from `0` here, the `1` is
absorbed into the reindexing. It is weakly increasing, it climbs by exactly one at each step of
`S` and stays put at every other step, and it is pointwise least among the `S`-ascending words of
length `n`. -/
@[hjo "def_cm_min_word"]
def minAscendingWord (n : ℕ) (S : Finset ℕ) : Fin n → ℕ :=
  fun k => #(S ∩ Icc 1 (k : ℕ))

/-- The minimal ascending word is the step count of the descent set with the value `0` discarded:
intersecting with `Icc 1 k` cuts off exactly the element `0`, which constrains no position. -/
theorem minAscendingWord_eq_stepCount (n : ℕ) (S : Finset ℕ) (k : Fin n) :
    minAscendingWord n S k = stepCount (S.erase 0) (k : ℕ) := by
  rw [minAscendingWord, stepCount]
  congr 1
  ext s
  simp only [mem_inter, mem_filter, mem_Icc, mem_erase]
  exact ⟨fun ⟨hs, h1, h2⟩ => ⟨⟨by omega, hs⟩, h2⟩, fun ⟨⟨h0, hs⟩, h2⟩ => ⟨hs, by omega, h2⟩⟩

/-- The minimal ascending word is weakly increasing: a longer initial window contains at least as
many steps. -/
theorem monotone_minAscendingWord (n : ℕ) (S : Finset ℕ) : Monotone (minAscendingWord n S) := by
  intro k l hkl
  rw [minAscendingWord_eq_stepCount, minAscendingWord_eq_stepCount]
  exact stepCount_mono (Fin.le_def.mp hkl)

/-- **The minimal ascending word ascends exactly on its own set**: the word `w^{n,S}` is an
`S'`-ascending word of length `n` if and only if every step of `S'` inside the window
`{1, …, n-1}` is a step of `S`. For `S'` contained in that window this is the usual
`w^{n,S} ∈ W_{n,S'} ↔ S' ⊆ S`; steps of `S'` outside it constrain no pair of positions of
`Fin n`, so they are discarded. -/
@[hjo "lem_cm_min_word_mem"]
theorem isAscendingWord_minAscendingWord_iff {n : ℕ} {S S' : Finset ℕ} :
    IsAscendingWord n S' (minAscendingWord n S) ↔ S' ∩ Ico 1 n ⊆ S := by
  constructor
  · intro hw l hl
    rw [mem_inter, mem_Ico] at hl
    obtain ⟨hlS', h1, hln⟩ := hl
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    have hlt : stepCount (S.erase 0) k < stepCount (S.erase 0) (k + 1) := by
      simpa [minAscendingWord_eq_stepCount] using
        hw.lt_of_mem ⟨k, by omega⟩ ⟨k + 1, hln⟩ rfl hlS'
    by_contra hnot
    rw [stepCount_succ_of_notMem fun h => hnot (mem_of_mem_erase h)] at hlt
    omega
  · intro hsub
    refine ⟨monotone_minAscendingWord n S, fun k l hkl hmem => ?_⟩
    have hlS : (l : ℕ) ∈ S := hsub (mem_inter.mpr ⟨hmem, mem_Ico.mpr ⟨by omega, l.2⟩⟩)
    have hk1 : (k : ℕ) + 1 ∈ S.erase 0 := mem_erase.mpr ⟨by omega, hkl ▸ hlS⟩
    have hstep : stepCount (S.erase 0) (l : ℕ) = stepCount (S.erase 0) (k : ℕ) + 1 := by
      rw [← hkl]
      exact stepCount_succ_of_mem hk1
    rw [minAscendingWord_eq_stepCount, minAscendingWord_eq_stepCount, hstep]
    omega

end HJO.Sym

namespace HJO.ParkingFunctions

/-! ### The fundamentals at the monomial of a minimal ascending word -/

/-- **The fundamental of a subset at the minimal word**: for a set of steps `S'` inside the window
`{1, …, n-1}` all of whose steps are steps of `S`, the coefficient of Gessel's fundamental
quasisymmetric function `F_{n,S'}` at the monomial `x^{𝐝(w^{n,S})}` of the minimal `S`-ascending
word is `1`. Together with the vanishing for `S' ⊄ S` this is the triangularity behind the linear
independence of the fundamentals. -/
@[hjo "lem_cm_min_word_coeff"]
theorem coeff_wordExponent_minAscendingWord_gessel (K : Type*) [CommRing K] {n : ℕ}
    {S S' : Finset ℕ} (hS' : S' ⊆ Ico 1 n) (hsub : S' ⊆ S) :
    MvPowerSeries.coeff (Sym.wordExponent (Sym.minAscendingWord n S)) (gessel K n S') = 1 :=
  coeff_wordExponent_gessel K hS'
    (Sym.isAscendingWord_minAscendingWord_iff.mpr (inter_subset_left.trans hsub))

/-- **The fundamental of a non-subset vanishes at the minimal word**: if some step of `S'` inside
the window `{1, …, n-1}` is not a step of `S`, then the coefficient of Gessel's fundamental
quasisymmetric function `F_{n,S'}` at the monomial `x^{𝐝(w^{n,S})}` of the minimal `S`-ascending
word is `0`. For `S'` contained in that window the hypothesis is `S' ⊄ S`; steps of
`S'` outside it constrain no pair of positions of `Fin n`, so they are discarded. Together with the
value `1` for `S' ⊆ S` this is the triangularity behind the linear independence of the
fundamentals. -/
@[hjo "lem_cm_min_word_coeff_zero"]
theorem coeff_wordExponent_minAscendingWord_gessel_eq_zero_of_not_subset (K : Type*) [CommRing K]
    {n : ℕ} {S S' : Finset ℕ} (hsub : ¬ S' ∩ Ico 1 n ⊆ S) :
    MvPowerSeries.coeff (Sym.wordExponent (Sym.minAscendingWord n S)) (gessel K n S') = 0 := by
  refine coeff_gessel_eq_zero_of_forall_ne K fun w hw heq => hsub ?_
  have hwe : Sym.minAscendingWord n S = w :=
    Sym.eq_of_monotone_of_wordExponent_eq (Sym.monotone_minAscendingWord n S) hw.monotone heq
  exact Sym.isAscendingWord_minAscendingWord_iff.mp (by rw [hwe]; exact hw)

/-! ### The independence -/

/-- **The fundamentals are linearly independent**: the family of Gessel fundamental
quasisymmetric functions `F_{n,S}`, indexed by the sets of steps `S` inside the window
`{1, …, n-1}`, is linearly independent over the coefficient ring `K`. Unfolded, a relation
`∑_S a_S F_{n,S} = 0` over those `S` forces every `a_S` to vanish; the index set cannot be
enlarged beyond the window, where `F_{n,S}` is a totalization and distinct sets can name the same
series. -/
@[hjo "lem_cm_gessel_independent"]
theorem linearIndepOn_gessel (K : Type*) [CommRing K] (n : ℕ) :
    LinearIndepOn K (gessel K n) {S : Finset ℕ | S ⊆ Ico 1 n} := by
  rw [linearIndepOn_iff]
  intro l hl hsum
  rw [Finsupp.mem_supported] at hl
  by_contra hne
  obtain ⟨T, hT, hTmin⟩ :=
    l.support.exists_min_image (fun S => #S) (Finsupp.support_nonempty_iff.mpr hne)
  have hTw : T ⊆ Ico 1 n := hl (mem_coe.mpr hT)
  set d := Sym.wordExponent (Sym.minAscendingWord n T) with hd
  have key : ∑ S ∈ l.support, l S * MvPowerSeries.coeff d (gessel K n S) = 0 := by
    have h0 : MvPowerSeries.coeff d (Finsupp.linearCombination K (gessel K n) l) = 0 := by
      rw [hsum, map_zero]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum] at h0
    simpa only [map_smul, smul_eq_mul] using h0
  have hzero : ∀ S ∈ l.support, S ≠ T → l S * MvPowerSeries.coeff d (gessel K n S) = 0 := by
    intro S hS hST
    refine mul_eq_zero_of_right _
      (coeff_wordExponent_minAscendingWord_gessel_eq_zero_of_not_subset K ?_)
    rw [inter_eq_left.mpr (hl (mem_coe.mpr hS))]
    exact fun hsub => hST (eq_of_subset_of_card_le hsub (hTmin S hS))
  rw [sum_eq_single T hzero fun h => absurd hT h,
    coeff_wordExponent_minAscendingWord_gessel K hTw subset_rfl, mul_one] at key
  exact Finsupp.mem_support_iff.mp hT key

end HJO.ParkingFunctions
