/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.GetD
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.IntervalCases
public meta import HJO.Attr

/-! # The word statistics of the Carlsson--Mellit recursions

Six statistics of a word are read by the recursions of Carlsson and Mellit, and none of
them is in `Mathlib`. This file defines them and nothing else: each is a plain function on tuples,
and the identities relating them live above.

* the descent set `Des(σ)` of a permutation or a word, the steps at which it goes down;
* the reversal `w^R` of a word;
* the costandardisation `Std⁻(w)`, the rank of each letter counting smaller letters and later
  ties;
* the two-letter support `S_m(w)`, the positions carrying one of two consecutive letters;
* the cut set `C(R, S)`, the places where a chain of attacks along `S` breaks;
* the equal-partner count `d_i(R, u)`, the attack partners of a position carrying its own letter.

## Main definitions

* `HJO.Sym.descentSet`: `Des(σ)`.
* `HJO.Sym.wordReverse`: `w^R`.
* `HJO.Sym.coStd`: `Std⁻(w)`.
* `HJO.Sym.twoLetterSupport`: `S_m(w)`.
* `HJO.Sym.cutSet`: `C(R, S)`.
* `HJO.Sym.equalPartners`: `d_i(R, u)`.

## Implementation notes

Positions and letters are indexed from `0`, as everywhere in this part of the library, so the
`1`-based position `j` is `j - 1` here; descent sets keep the `1`-based indexing of steps used
throughout the library, in which `j ∈ S` names the step from the position `j - 1` to the position
`j`, and live in the window `Finset.Ico 1 n`, matching `HJO.Sym.IsAscendingWord` and
`HJO.ParkingFunctions.descentReverse`. So `descentSet n w` is literally the usual
`{i ∈ {1, …, n-1} : σ_i > σ_{i+1}}`, with nothing shifted.

Words on a window are taken as total functions `ℕ → α` rather than `Fin n → α` wherever the lemmas
using them extend, restrict or shift the window: `descentSet`, `twoLetterSupport` and `cutSet` read
only the letters inside their window, which is recorded as a congruence lemma for each. `coStd` and
`wordReverse` instead take `Fin n → α`, the whole tuple being their argument and their value.

`coStd` returns the usual `1`-based rank lowered by one, so that it is a `0`-based position like
every other index here; the count `#\{j ≥ i : w_j = w_i\}` always contains `j = i`, so the
subtraction is genuine and `coStd_lt` bounds the value by `n`.

`equalPartners` counts *pairs* of the attack set rather than second coordinates, which avoids a
`Fintype` assumption on the positions; `equalPartners_eq_card_image` identifies the count with the
number of partners `j`.

## References

This file defines `HJO.Sym.descentSet`, `HJO.Sym.wordReverse`, `HJO.Sym.coStd`,
`HJO.Sym.twoLetterSupport`, `HJO.Sym.cutSet` and `HJO.Sym.equalPartners`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The descent set -/

variable {α : Type*}

section LinearOrder

variable [LinearOrder α] {n : ℕ} {w w' : ℕ → α} {j : ℕ}

/-- The descent set `Des(σ)` of the word `σ` on the positions `0, 1, …, n - 1`: the steps of the
window at which the word strictly decreases. The usual `Des(σ) = {i : σ_i > σ_{i+1}}` for
`1 ≤ i ≤ n - 1` is this set unchanged — a step `j` is the step from the position `j - 1` to the
position `j`, so the usual step `i` is the step `i` here, and the window `Finset.Ico 1 n` is the
usual `{1, …, n-1}`. Stated for a word rather than only for a permutation, the lemmas using it
applying `Des` to standardisations of words as well as to permutations. -/
@[hjo "def_cm_des"]
def descentSet (n : ℕ) (w : ℕ → α) : Finset ℕ :=
  {j ∈ Ico 1 n | w j < w (j - 1)}

/-- Membership in the descent set: the defining condition `σ_i > σ_{i+1}` on the window
`{1, …, n-1}`. -/
@[simp]
theorem mem_descentSet : j ∈ descentSet n w ↔ 1 ≤ j ∧ j < n ∧ w j < w (j - 1) := by
  simp only [descentSet, mem_filter, mem_Ico, and_assoc]

/-- The descent set lies in the window `{1, …, n-1}` of steps, which is what makes its
complement `Ico 1 n \ Des(σ)` the ascent set. -/
theorem descentSet_subset_Ico (n : ℕ) (w : ℕ → α) : descentSet n w ⊆ Ico 1 n :=
  filter_subset _ _

/-- Only the letters inside the window are read: two words agreeing there have the same descent
set. In particular a word given on `Fin n` may be extended off the window by any letters. -/
theorem descentSet_congr (h : ∀ j < n, w' j = w j) : descentSet n w' = descentSet n w :=
  filter_congr fun j hj => by
    obtain ⟨h1, h2⟩ := mem_Ico.mp hj
    rw [h j h2, h (j - 1) (by omega)]

/-- A word of length at most one has no descents: there is no step in the window. -/
@[simp]
theorem descentSet_one (w : ℕ → α) : descentSet 1 w = ∅ := by
  simp [descentSet]

/-- A value check in `1`-based indices: the permutation `σ = (2, 1, 3)` of `{1, 2, 3}` has
`Des(σ) = {1}`, its only descent being the step from `σ_1 = 2` to `σ_2 = 1`. The word is recorded
from position `0`, so `σ_i` is the letter at the position `i - 1`. -/
theorem descentSet_source_example :
    descentSet 3 (fun j => [2, 1, 3].getD j 0) = {1} := by
  ext j
  simp only [mem_descentSet, mem_singleton]
  constructor
  · rintro ⟨h1, h2, h3⟩
    interval_cases j
    · rfl
    · norm_num [List.getD] at h3
  · rintro rfl
    norm_num [List.getD]

/-! ### The reversal of a word -/

end LinearOrder

/-- The reversal `w^R` of a word: the tuple whose `i`-th entry is the entry of `w` at the mirrored
position. The usual `w^R_i = w_{n+1-i}` is this map unchanged, positions being indexed from
`0`, where the mirror of the position `i` is `n - 1 - i`, which is `Fin.rev i`. -/
@[hjo "def_om_word_reverse"]
def wordReverse {n : ℕ} (w : Fin n → α) : Fin n → α :=
  w ∘ Fin.rev

/-- The entries of the reversal, by definition. -/
@[simp]
theorem wordReverse_apply {n : ℕ} (w : Fin n → α) (i : Fin n) : wordReverse w i = w i.rev :=
  rfl

/-- Reversal is an involution: `(w^R)^R = w`. -/
@[simp]
theorem wordReverse_wordReverse {n : ℕ} (w : Fin n → α) : wordReverse (wordReverse w) = w :=
  funext fun i => by rw [wordReverse_apply, wordReverse_apply, Fin.rev_rev]

/-- A value check in `1`-based indices: the reversal of `(4, 1, 5)` is `(5, 1, 4)`. -/
theorem wordReverse_source_example :
    wordReverse ![4, 1, 5] = ![5, 1, 4] := by
  decide

/-! ### The costandardisation -/

section CoStd

variable [LinearOrder α] {n : ℕ}

/-- The costandardisation `Std⁻(w)` of a word: the entry at the position `i` is the number of
positions carrying a strictly smaller letter, plus the number of positions at or after `i` carrying
the same letter, lowered by one. The usual
`Std⁻(w)_i = \#\{j : w_j < w_i\} + \#\{j ≥ i : w_j = w_i\}` is a rank in `{1, …, n}`; the value here
is that rank minus one, a `0`-based position, as everywhere in this part of the library. The second
count always contains `j = i`, so the subtraction is genuine, and `HJO.Sym.coStd_lt` bounds the
value by `n`. Positivity of the letters is not used, so it is not assumed. -/
@[hjo "def_om_costd"]
def coStd (w : Fin n → α) (i : Fin n) : ℕ :=
  #{j | w j < w i} + #{j | i ≤ j ∧ w j = w i} - 1

/-- The `1`-based rank, before it is lowered: the number of positions carrying a smaller letter
plus the number of positions at or after `i` carrying the same letter. Adding the one back is
legitimate because the second count contains `j = i`. -/
theorem coStd_add_one (w : Fin n → α) (i : Fin n) :
    coStd w i + 1 = #{j | w j < w i} + #{j | i ≤ j ∧ w j = w i} := by
  have hi : i ∈ ({j | i ≤ j ∧ w j = w i} : Finset (Fin n)) := by simp
  have : 1 ≤ #{j | i ≤ j ∧ w j = w i} := card_pos.2 ⟨i, hi⟩
  rw [coStd]
  omega

/-- The two counts of the costandardisation are disjoint, a letter being either smaller than
`w i` or equal to it but not both, so their sum is at most the length of the word. -/
theorem coStd_bound (w : Fin n → α) (i : Fin n) :
    #{j | w j < w i} + #{j | i ≤ j ∧ w j = w i} ≤ n := by
  have hdisj : Disjoint ({j | w j < w i} : Finset (Fin n))
      ({j | i ≤ j ∧ w j = w i} : Finset (Fin n)) :=
    disjoint_filter.2 fun j _ hj hj' => absurd (hj'.2 ▸ hj) (lt_irrefl _)
  calc #{j | w j < w i} + #{j | i ≤ j ∧ w j = w i}
      = #(({j | w j < w i} : Finset (Fin n)) ∪ ({j | i ≤ j ∧ w j = w i} : Finset (Fin n))) :=
        (card_union_of_disjoint hdisj).symm
    _ ≤ #(univ : Finset (Fin n)) := card_le_card (subset_univ _)
    _ = n := by simp

/-- The costandardisation takes values among the positions: the `1`-based rank lies in `{1, …, n}`,
so its `0`-based form lies below `n`. This is what lets later lemmas read `Std⁻(w)` as a
permutation of the positions. -/
theorem coStd_lt (w : Fin n → α) (i : Fin n) : coStd w i < n := by
  have h := coStd_bound w i
  have h' := coStd_add_one w i
  omega

/-- A value check in `1`-based indices: for `w = (2, 1, 2)` the `1`-based rank at the first
position is `\#\{j : w_j < 2\} + \#\{j ≥ 1 : w_j = 2\} = 1 + 2 = 3`, at the second position
`0 + 1 = 1`, and at the third `1 + 1 = 2`, so `Std⁻(w) = (3, 1, 2)`. In the `0`-based form that is
`(2, 0, 1)`. The later-ties convention is what makes the first position outrank the third; counting
earlier ties instead would give `(1, 0, 2) + 1 = (2, 1, 3)`, a different tuple. -/
theorem coStd_source_example : coStd ![2, 1, 2] = ![2, 0, 1] := by
  decide

end CoStd

/-! ### The two-letter support -/

section Support

variable [DecidableEq α] {N : ℕ} {a b : α} {w w' : ℕ → α} {j : ℕ}

/-- The two-letter support of the word `w` on the positions `0, 1, …, N - 1` for the letters `a`
and `b`: the positions of the window carrying one of the two letters. For a labelling `w` of a
Dyck path and the two consecutive letters `m`, `m + 1` this is the usual
`S_m(w) = {j : w_j ∈ \{m, m+1\}}`, whose increasing listing `s_1 < ⋯ < s_p` is cut into runs by
`HJO.Sym.cutSet`. Positions are indexed from `0`, as for the paths of `HJO.Dyck.IsSquareDyck`, so
the `1`-based `1 ≤ j ≤ N` is `j < N`. -/
@[hjo "def_cm_msupport"]
def twoLetterSupport (N : ℕ) (a b : α) (w : ℕ → α) : Finset ℕ :=
  {j ∈ range N | w j = a ∨ w j = b}

/-- Membership in the two-letter support: the positions of the window whose letter is `a` or `b`.
This is the defining condition for `S_m(w)`. -/
@[simp]
theorem mem_twoLetterSupport :
    j ∈ twoLetterSupport N a b w ↔ j < N ∧ (w j = a ∨ w j = b) := by
  simp only [twoLetterSupport, mem_filter, mem_range]

/-- The support lies in the window of positions. -/
theorem twoLetterSupport_subset_range (N : ℕ) (a b : α) (w : ℕ → α) :
    twoLetterSupport N a b w ⊆ range N :=
  filter_subset _ _

/-- The support has at most `N` elements: that is, `p ≤ N`. -/
theorem card_twoLetterSupport_le (N : ℕ) (a b : α) (w : ℕ → α) :
    #(twoLetterSupport N a b w) ≤ N :=
  (card_le_card (twoLetterSupport_subset_range N a b w)).trans_eq (card_range N)

/-- Every position of the support carries one of the two letters. This is the form in which the
alternation of the letters along a run is read: `w_{s_c} ∈ \{m, m+1\}` for every index `c`. -/
theorem eq_or_eq_of_mem_twoLetterSupport (h : j ∈ twoLetterSupport N a b w) :
    w j = a ∨ w j = b :=
  (mem_twoLetterSupport.mp h).2

/-- A position of the window outside the support carries neither letter. This is the form in which
the monomial `∏_{i ∉ S_m(w)} z_{w_i}` is seen to be fixed by the swap of `m` and `m + 1`. -/
theorem ne_and_ne_of_notMem_twoLetterSupport (hj : j < N)
    (h : j ∉ twoLetterSupport N a b w) : w j ≠ a ∧ w j ≠ b := by
  simp only [mem_twoLetterSupport, hj, true_and, not_or] at h
  exact h

/-- The two letters enter the support symmetrically. -/
theorem twoLetterSupport_comm (N : ℕ) (a b : α) (w : ℕ → α) :
    twoLetterSupport N a b w = twoLetterSupport N b a w := by
  ext j; simp [or_comm]

/-- Only the letters inside the window are read: two words agreeing there have the same support.
In particular a word given on `Fin N` may be extended off the window by any letters at all. -/
theorem twoLetterSupport_congr (a b : α) (h : ∀ j < N, w' j = w j) :
    twoLetterSupport N a b w' = twoLetterSupport N a b w :=
  filter_congr fun j hj => by rw [h j (mem_range.mp hj)]

/-- A word that avoids both letters from the position `N` on carries `a` or `b` exactly on its
two-letter support. For the labellings of a Dyck path this holds of every window containing them,
the letters being positive and `a = m`, `b = m + 1` with `m ≥ 1`. -/
theorem mem_twoLetterSupport_iff_of_forall_ge (h : ∀ j, N ≤ j → w j ≠ a ∧ w j ≠ b) (j : ℕ) :
    (w j = a ∨ w j = b) ↔ j ∈ twoLetterSupport N a b w := by
  refine ⟨fun hj => mem_twoLetterSupport.mpr ⟨?_, hj⟩, eq_or_eq_of_mem_twoLetterSupport⟩
  by_contra hjN
  exact hj.elim (h j (Nat.le_of_not_lt hjN)).1 (h j (Nat.le_of_not_lt hjN)).2

/-- The empty window has empty support. -/
@[simp]
theorem twoLetterSupport_zero (a b : α) (w : ℕ → α) : twoLetterSupport 0 a b w = ∅ := by
  simp [twoLetterSupport]

end Support

/-! ### The cut set -/

/-- The cut set `C(R, S)` of a set `S` of positions for a set `R` of attacking pairs: writing
`s_1 < ⋯ < s_p` for the increasing listing of `S`, where `p = #S`, the indices `1 ≤ c ≤ p - 1` at
which the chain of attacks breaks, `(s_c, s_{c+1}) ∉ R`. Positions are indexed from `0`, as for the
paths of `HJO.Dyck.IsSquareDyck`, so the `1`-based `s_c` is `S.sort.getD (c - 1) 0`, while the
indices `c` are numbered from `1`: the cut `c` is the step from the index `c` to the index `c + 1`,
the same convention as for `HJO.Sym.descentSet`. The `C(R, S)`-blocks of `{1, …, p}` index the runs
of `S`. -/
@[hjo "def_cm_cutset"]
def cutSet (R : Finset (ℕ × ℕ)) (S : Finset ℕ) : Finset ℕ :=
  {c ∈ Ico 1 #S | (S.sort.getD (c - 1) 0, S.sort.getD c 0) ∉ R}

/-- Membership in the cut set: the cuts are the indices `c` with `1 ≤ c ≤ #S - 1` whose two
neighbouring elements in the increasing listing of `S` do not attack each other. -/
@[simp]
theorem mem_cutSet {R : Finset (ℕ × ℕ)} {S : Finset ℕ} {c : ℕ} :
    c ∈ cutSet R S ↔ 1 ≤ c ∧ c < #S ∧ (S.sort.getD (c - 1) 0, S.sort.getD c 0) ∉ R := by
  simp only [cutSet, mem_filter, mem_Ico, and_assoc]

/-- The cut set lies in the window `{1, …, p-1}` of steps of the listing, which is what
makes its blocks of `{1, …, p}` the runs of `S`. -/
theorem cutSet_subset_Ico (R : Finset (ℕ × ℕ)) (S : Finset ℕ) : cutSet R S ⊆ Ico 1 #S :=
  filter_subset _ _

/-- A set with at most one element has no cuts: the listing has no step. -/
@[simp]
theorem cutSet_of_card_le_one {R : Finset (ℕ × ℕ)} {S : Finset ℕ} (h : #S ≤ 1) :
    cutSet R S = ∅ := by
  refine eq_empty_of_forall_notMem fun c hc => ?_
  have := mem_cutSet.mp hc
  omega

/-! ### The equal-partner count -/

/-- The number of attack partners of the position `i` carrying the same letter as `i`: the usual
`d_i(R, u) = \#\{j : (i, j) ∈ R \text{ and } u_j = u_i\}`. The count is taken over the pairs of `R`
with first coordinate `i`, which carries no `Fintype` assumption on the positions;
`HJO.Sym.equalPartners_eq_card_image` identifies it with the number of partners `j`, the pairs of
`R` having their first coordinate fixed. -/
@[hjo "def_cm_equal_partners"]
def equalPartners {ι : Type*} [DecidableEq ι] [DecidableEq α] (R : Finset (ι × ι)) (u : ι → α)
    (i : ι) : ℕ :=
  #{p ∈ R | p.1 = i ∧ u p.2 = u i}

section EqualPartners

variable {ι : Type*} [DecidableEq ι] [DecidableEq α] {R : Finset (ι × ι)} {u : ι → α} {i : ι}

/-- The equal-partner count is the number of partners `j`, which is the form of the usual
definition: the pairs counted all have first coordinate `i`, so taking the second coordinate is
injective on them. -/
theorem equalPartners_eq_card_image :
    equalPartners R u i = #(({p ∈ R | p.1 = i ∧ u p.2 = u i} : Finset (ι × ι)).image Prod.snd) := by
  refine (card_image_of_injOn fun p hp p' hp' h => ?_).symm
  rw [mem_coe, mem_filter] at hp hp'
  exact Prod.ext (hp.2.1.trans hp'.2.1.symm) h

/-- A position of the image of the equal-partner count is an attack partner carrying the same
letter, and conversely. -/
@[simp]
theorem mem_image_equalPartners {j : ι} :
    j ∈ ({p ∈ R | p.1 = i ∧ u p.2 = u i} : Finset (ι × ι)).image Prod.snd ↔
      (i, j) ∈ R ∧ u j = u i := by
  refine ⟨fun h => ?_, fun h => mem_image.2 ⟨(i, j), by simp [mem_filter, h.1, h.2], rfl⟩⟩
  obtain ⟨p, hp, rfl⟩ := mem_image.mp h
  rw [mem_filter] at hp
  exact ⟨hp.2.1 ▸ hp.1, hp.2.2⟩

/-- No pair of the empty attack set counts. -/
@[simp]
theorem equalPartners_empty (u : ι → α) (i : ι) : equalPartners (∅ : Finset (ι × ι)) u i = 0 := by
  simp [equalPartners]

/-- The equal-partner count never exceeds the number of attacking pairs. -/
theorem equalPartners_le_card (R : Finset (ι × ι)) (u : ι → α) (i : ι) :
    equalPartners R u i ≤ #R :=
  card_filter_le _ _

end EqualPartners

end HJO.Sym
