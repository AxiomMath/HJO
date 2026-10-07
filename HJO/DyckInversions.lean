/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Order.Cover
public meta import HJO.Attr

/-! # The inversions of a labelling among an abstract set of pairs

The inversion statistic of the shuffle theorem is counted against an abstract set `R` of pairs of
positions: `Inv(R, w) = {(i, j) ∈ R : w j < w i}`, the pairs of `R` whose earlier position carries
the larger letter, and `inv(R, w)` is its cardinality. Taking `R` to be the attacking pairs of a
Dyck path recovers the path's inversion number, and taking it to be a subset of those recovers the
partial counts the two-letter analysis needs.

This file fixes that set and its elementary API, and proves the one substantial fact about it that
the two-letter analysis turns on: the inversions *outside* a two-letter block do not see which of
the two letters stands at each position of the block. Because the two letters `a ⋖ b` are
consecutive, a letter from outside the block compares the same way with `a` as with `b`, so the
count is determined by the letters off the block alone.

## Main definitions

* `HJO.Dyck.invSet`: the inversions of the labelling `w` among the pairs of `R`.

## Main results

* `HJO.Dyck.card_filter_invSet_congr_of_covBy`: two labellings whose `{a, b}`-positions are the
  same set `S` and which agree off `S` invert the same number of pairs not internal to `S`.

## Implementation notes

The two-letter statement is proved not by a bijection between the two inversion sets but by
observing that they are the *same* set: `invSet_filter` moves the restriction "not internal to `S`"
from the inversion set to the set of pairs, and `invSet_congr` then needs only that `w` and `w'`
invert each surviving pair alike. That comparison is `lt_iff_lt_of_covBy_left` and
`lt_iff_lt_of_covBy_right`, the two halves of the observation that a letter outside `{a, b}` lies
either below both or above both — which is exactly what `a ⋖ b` says.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

variable {ι α : Type*}

section LT

variable [LT α] [DecidableLT α]

/-- The inversions of the labelling `w` among the pairs of `R`: the set
`Inv(R, w) = {(i, j) ∈ R : w j < w i}`, the pairs of `R` whose earlier position carries the larger
letter. Its cardinality is the inversion number `inv(R, w)`. -/
@[hjo "def_dyck_inv_set"]
def invSet (R : Finset (ι × ι)) (w : ι → α) : Finset (ι × ι) := {p ∈ R | w p.2 < w p.1}

/-- The inversion number `inv(R, w) = #Inv(R, w)`: the number of pairs of `R` that the labelling
`w` inverts. This is the exponent of `q` in every term of the characteristic function `χ(R, n)`,
and the statistic the two-letter analysis compares across a deletion. -/
@[hjo "def_dyck_inv"]
def invNumber (R : Finset (ι × ι)) (w : ι → α) : ℕ := #(invSet R w)

/-- A pair is an inversion of `w` exactly when it is a pair of `R` and its letters decrease. -/
@[simp]
theorem mem_invSet {R : Finset (ι × ι)} {w : ι → α} {p : ι × ι} :
    p ∈ invSet R w ↔ p ∈ R ∧ w p.2 < w p.1 :=
  Finset.mem_filter

/-- Every inversion is a pair of `R`. -/
theorem invSet_subset (R : Finset (ι × ι)) (w : ι → α) : invSet R w ⊆ R :=
  Finset.filter_subset _ _

/-- The inversion set grows with the set of pairs. -/
theorem invSet_subset_invSet {R R' : Finset (ι × ι)} (h : R ⊆ R') (w : ι → α) :
    invSet R w ⊆ invSet R' w :=
  Finset.filter_subset_filter _ h

/-- A labelling has no inversions among no pairs. -/
@[simp]
theorem invSet_empty (w : ι → α) : invSet (∅ : Finset (ι × ι)) w = ∅ :=
  Finset.filter_empty _

/-- The inversions among a union of two sets of pairs are the union of the inversions. -/
theorem invSet_union [DecidableEq ι] (R R' : Finset (ι × ι)) (w : ι → α) :
    invSet (R ∪ R') w = invSet R w ∪ invSet R' w :=
  Finset.filter_union _ _ _

/-- Deleting a pair from `R` deletes it from the inversion set. This is the form in which the
deletion of a single pair from an attack set enters the two-letter difference
`χ₂(R, m) - χ₂(R ∖ {(a, b)}, m)`, where the two inversion sets differ at most in `(a, b)`. -/
theorem invSet_erase [DecidableEq ι] (R : Finset (ι × ι)) (p : ι × ι) (w : ι → α) :
    invSet (R.erase p) w = (invSet R w).erase p :=
  Finset.filter_erase _ _ _

/-- Forming the inversion set commutes with restricting the pairs: the inversions among the pairs
of `R` that satisfy `P` are the inversions of `R` that satisfy `P`. With
`Finset.card_filter_add_card_filter_not` this is the splitting of `inv(R, w)` into the pairs with
both entries in a block and the pairs without, which is how the symmetry of `χ(R, n)` in two
neighbouring letters is proved. -/
theorem invSet_filter (P : ι × ι → Prop) [DecidablePred P] (R : Finset (ι × ι)) (w : ι → α) :
    invSet {p ∈ R | P p} w = {p ∈ invSet R w | P p} :=
  Finset.filter_comm _ _ _

/-- Only the comparisons of `w` on the pairs of `R` enter the inversion set: two labellings that
agree on all of them have the same inversions. This is the shape in which standardisation, letter
reversal and any other relabelling that preserves the comparisons preserves the inversion set. -/
theorem invSet_congr {R : Finset (ι × ι)} {w w' : ι → α}
    (h : ∀ p ∈ R, (w p.2 < w p.1 ↔ w' p.2 < w' p.1)) : invSet R w = invSet R w' :=
  Finset.filter_congr h

/-- Every pair of `R` is an inversion exactly when the letters decrease along each of them. -/
theorem invSet_eq_self {R : Finset (ι × ι)} {w : ι → α} :
    invSet R w = R ↔ ∀ p ∈ R, w p.2 < w p.1 :=
  Finset.filter_eq_self

/-- A constant labelling has no inversions, whatever the pairs. -/
theorem invSet_const [Std.Irrefl (· < · : α → α → Prop)] (R : Finset (ι × ι)) (a : α) :
    invSet R (fun _ => a) = ∅ := by
  simp [invSet, Std.Irrefl.irrefl (r := (· < · : α → α → Prop)) a]

/-! ### The inversion number -/

/-- No pairs, no inversions. -/
@[simp]
theorem invNumber_empty (w : ι → α) : invNumber (∅ : Finset (ι × ι)) w = 0 := by
  rw [invNumber, invSet_empty, Finset.card_empty]

/-- The inversion number is at most the number of pairs: the exponent of `q` in `χ(R, n)` is
bounded by `#R`. -/
theorem invNumber_le_card (R : Finset (ι × ι)) (w : ι → α) : invNumber R w ≤ #R :=
  Finset.card_le_card (invSet_subset R w)

/-- The inversion number grows with the set of pairs. -/
theorem invNumber_le_invNumber {R R' : Finset (ι × ι)} (h : R ⊆ R') (w : ι → α) :
    invNumber R w ≤ invNumber R' w :=
  Finset.card_le_card (invSet_subset_invSet h w)

/-- Only the comparisons of `w` along the pairs of `R` enter the inversion number: this is what
makes `inv(R, ·)` invariant under standardisation and under letter reversal. -/
theorem invNumber_congr {R : Finset (ι × ι)} {w w' : ι → α}
    (h : ∀ p ∈ R, (w p.2 < w p.1 ↔ w' p.2 < w' p.1)) : invNumber R w = invNumber R w' :=
  congrArg Finset.card (invSet_congr h)

/-- A constant labelling has inversion number `0`. -/
theorem invNumber_const [Std.Irrefl (· < · : α → α → Prop)] (R : Finset (ι × ι)) (a : α) :
    invNumber R (fun _ => a) = 0 := by
  rw [invNumber, invSet_const, Finset.card_empty]

/-- Every pair is inverted exactly when the inversion number is the number of pairs. -/
theorem invNumber_eq_card_iff {R : Finset (ι × ι)} {w : ι → α} :
    invNumber R w = #R ↔ ∀ p ∈ R, w p.2 < w p.1 := by
  rw [invNumber, ← invSet_eq_self]
  exact ⟨fun h => Finset.eq_of_subset_of_card_le (invSet_subset R w) h.ge,
    fun h => congrArg Finset.card h⟩

end LT

section CovBy

variable [LinearOrder α] {a b : α}

/-- A letter outside `{a, b}` lies below `b` exactly when it lies below `a`, for consecutive
letters `a ⋖ b`: there is nothing between them to separate the two comparisons. -/
theorem lt_iff_lt_of_covBy_left (hab : a ⋖ b) {x y : α} (hx : x = a ∨ x = b)
    (hy : ¬(y = a ∨ y = b)) : y < x ↔ y < a := by
  rcases hx with rfl | rfl
  · exact Iff.rfl
  · refine ⟨fun h => ?_, fun h => h.trans hab.1⟩
    rcases lt_trichotomy y a with h' | h' | h'
    · exact h'
    · exact absurd (Or.inl h') hy
    · exact absurd h (hab.2 h')

/-- A letter outside `{a, b}` lies above `a` exactly when it lies above `b`, for consecutive
letters `a ⋖ b`: there is nothing between them to separate the two comparisons. -/
theorem lt_iff_lt_of_covBy_right (hab : a ⋖ b) {x y : α} (hx : x = a ∨ x = b)
    (hy : ¬(y = a ∨ y = b)) : x < y ↔ b < y := by
  rcases hx with rfl | rfl
  · refine ⟨fun h => ?_, fun h => hab.1.trans h⟩
    rcases lt_trichotomy b y with h' | h' | h'
    · exact h'
    · exact absurd (Or.inr h'.symm) hy
    · exact absurd h' (hab.2 h)
  · exact Iff.rfl

/-- **The inversions outside a two-letter block are determined by the block's complement**: let
`a ⋖ b` be consecutive letters, let `S` be a finite set of positions, and let `w` and `w'` be
words whose letters lie in `{a, b}` exactly on `S` and which agree off `S`. Then `w` and `w'`
invert the same number of pairs of `R` that are not internal to `S`. The instance used for the
symmetry of `χ(R, n)` is `ι = α = ℕ` with positions and letters numbered from `1`, `b = a + 1` by
`Order.covBy_succ`, and `S = {l : w l ∈ {a, a + 1}}` with the common restriction of `w` and `w'` off
`S` as its `f`. -/
@[hjo "lem_cm_inv_outside_block"]
theorem card_filter_invSet_congr_of_covBy [DecidableEq ι]
    (hab : a ⋖ b) (R : Finset (ι × ι)) (S : Finset ι) {w w' : ι → α}
    (hw : ∀ l, (w l = a ∨ w l = b) ↔ l ∈ S)
    (hw' : ∀ l, (w' l = a ∨ w' l = b) ↔ l ∈ S)
    (hoff : ∀ l ∉ S, w' l = w l) :
    #{p ∈ invSet R w | ¬(p.1 ∈ S ∧ p.2 ∈ S)} =
      #{p ∈ invSet R w' | ¬(p.1 ∈ S ∧ p.2 ∈ S)} := by
  rw [← invSet_filter, ← invSet_filter]
  congr 1
  refine invSet_congr fun p hp => ?_
  simp only [Finset.mem_filter, not_and] at hp
  obtain ⟨-, hnot⟩ := hp
  by_cases h1 : p.1 ∈ S
  · have h2 : p.2 ∉ S := hnot h1
    rw [lt_iff_lt_of_covBy_left hab ((hw p.1).mpr h1) (fun hc => h2 ((hw p.2).mp hc)),
      lt_iff_lt_of_covBy_left hab ((hw' p.1).mpr h1) (fun hc => h2 ((hw' p.2).mp hc)),
      hoff p.2 h2]
  · by_cases h2 : p.2 ∈ S
    · rw [lt_iff_lt_of_covBy_right hab ((hw p.2).mpr h2) (fun hc => h1 ((hw p.1).mp hc)),
        lt_iff_lt_of_covBy_right hab ((hw' p.2).mpr h2) (fun hc => h1 ((hw' p.1).mp hc)),
        hoff p.1 h1]
    · rw [hoff p.1 h1, hoff p.2 h2]

end CovBy

end HJO.Dyck
