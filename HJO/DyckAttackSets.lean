/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SquareDyck
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.GetD
public import Mathlib.Order.Lattice.Nat
public meta import HJO.Attr

/-! # The attack set of a square Dyck path, transitive attack sets, restriction and recovery

The cells lying strictly between a square Dyck path and the main diagonal are Carlsson--Mellit's
`Area(π)`; for such a cell `(i, j)` they call the rows `i` and `j` *attacking*, and since
both `Area` and `area` are already in use in this library for statistics of rectangular paths,
the set is called the **attack set** `At(π)`. Writing `x_1 ≤ ⋯ ≤ x_n` for the coarea sequence of
`π`, so that `(x_j, j)` is the cell immediately to the right of the `j`-th north step, a cell
`(i, j)` lies under the path exactly when `i ≤ j - 1` and weakly to the right of that north step,
so `At(π) = {(i, j) : 1 ≤ j ≤ n, x_j ≤ i ≤ j - 1}`.

This file carries the four definitions the Carlsson--Mellit `χ` combinatorics and the sweep map read
that set through: the set itself, the abstract property that characterises which sets of pairs arise
this way, the restriction of such a set along a subset of the positions, and the sequence of rowwise
minima that recovers the path from the set.

Here `i` indexes the columns and `j` the rows, as in Carlsson--Mellit, so `At(π)` is the disjoint
union over the rows `j` of the intervals `{x_j, …, j - 1}`, the row `j` contributing their
`a_j = j - x_j` cells. That row decomposition is the definition below and the shape of every
argument about the attack set: the flip of a set of corners changes one row at a time, the partial
paths `𝔻_{k,n}` are those whose first `k` rows are full, and the attack number is the sum of the
row counts.

## Main definitions

* `HJO.Dyck.attackSet`: the attack set `At(π)` of a sequence `π`, as a finite set of cells.
* `HJO.Dyck.IsTransitiveAttackSet`: a transitive attack set on `{1, …, n}`, Carlsson--Mellit's
  property `(*)`.
* `HJO.Dyck.attackRestrict`: the restriction `R_S` of a set of attacking pairs along a set `S` of
  positions, renumbered by the increasing enumeration of `S`.
* `HJO.Dyck.attackPartner`: the square partner `P̂'`, the sequence of rowwise minima
  `x'_j = min({i : (i, j) ∈ A} ∪ {j})`.

## Main results

The definitions are used through these, not by unfolding them.

* `HJO.Dyck.mem_attackSet`, `HJO.Dyck.mem_attackSet_coe`: a cell `(i, j)` lies in `At(π)` exactly
  when `j` is a row of the path and `x_j ≤ i < j`.
* `HJO.Dyck.attackSet_subset_filter_lt`,
  `HJO.Dyck.IsTransitiveAttackSet.subset_filter_lt`: both sides lie in the window
  `{(j, j') : 1 ≤ j < j' ≤ n}`, in one piece.
* `HJO.Dyck.attackSet_filter_snd`: row `k` of `At(π)` is the interval `{x_k, …, k - 1}`.
* `HJO.Dyck.attackSet_congr`, `HJO.Dyck.attackSet_update_zero`: the attack set does not read the
  entry at position `0`, row `0` being empty; so it depends on the path only away from there.
* `HJO.Dyck.card_attackSet`: the attack number is the sum of the row counts.
* `HJO.Dyck.IsTransitiveAttackSet.mem_of_le_of_lt_of_le`: the iterated form of `(*)`, closure
  under passing to a subinterval.
* `HJO.Dyck.mem_attackRestrict`, `HJO.Dyck.mem_attackRestrict_iff_of_forall_lt`: membership in
  `R_S`, the second dropping the increasingness clause for an `R` of increasing pairs.
* `HJO.Dyck.attackPartner_attackSet`: the rowwise minima of `At(π)` return `π`.
* `HJO.Dyck.isTransitiveAttackSet_attackSet` and
  `HJO.Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet`: the two directions making `At`
  a bijection from the square Dyck paths of length `n` onto the transitive attack sets on
  `{1, …, n}`. `HJO.Dyck.isSquareDyck_attackPartner` is the second with the recovered sequence
  supplied.
* `HJO.Dyck.isTransitiveAttackSet_attackRestrict`, `HJO.Dyck.card_attackRestrict_le`: restriction
  preserves transitivity and does not increase the size.

## Implementation notes

All positions and entries are indexed from `0`, as in `HJO.Dyck.IsSquareDyck`: Carlsson--Mellit's
`x_j` is `x ⟨j - 1, _⟩`, their cell `(i, j)` is `(i - 1, j - 1)`, and their window `1 ≤ j < j' ≤ n`
is `j < j' < n`.

`attackSet` is presented by rows — a `Finset.biUnion` of the row intervals — rather than as a
filter of a square, because every consumer changes or reads one row at a time and because
`card_attackSet` is then the disjointness of the rows.

`IsTransitiveAttackSet` splits Carlsson--Mellit's `(*)` into its two halves `mem_lower` and
`mem_upper`, which is the shape of `HJO.Paths.isTransitiveAttackSet_attackPositions`, and carries
the window as two fields rather than a containment, so that neither is unpacked at use. It is
decidable, at the cost `instDecidableIsTransitiveAttackSet` charges: the splitting clause is
quantified over the pairs of `R` and the positions strictly between their entries, so it tests `#R`
pairs where the written-out form enumerates `n ^ 3` triples.

`attackRestrict` renumbers along `Finset.sort` rather than along `Finset.orderEmbOfFin`, so that
the enumeration is a plain function of a natural number and no bound proof rides inside the
subject; `Finset.getD_sort_eq_orderEmbOfFin` identifies the two where the bound is at hand. The
junk value of the enumeration outside the range is `0`, and no statement reads it: every clause
guards the index by `#S`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §2.2, where the attack set is
`Area(π)`, and §3.1, where the transitivity condition is the property `(*)`, the restriction is
`R_S` and the bijection is the one at the head of the proof of the proposition that `χ(π)` is
symmetric.

Consumed by `HJO.Dyck.attackNumber`, the partial-path and corner-flip lemmas of the
Carlsson--Mellit sections (`HJO.Dyck.mem_attackSet_of_lt_level`, `HJO.Dyck.attackSet_flipCorners`,
`HJO.Dyck.isPartialDyck_prependEast`), and `HJO.Dyck.letterPerm_swap_charSeries`.
-/

@[expose] public section

open Finset

namespace Finset

/-- The `j`-th element of the increasing enumeration of a finset lies in it. -/
theorem getD_sort_mem {α : Type*} [LinearOrder α] (S : Finset α) (d : α) {j : ℕ} (h : j < #S) :
    (S.sort).getD j d ∈ S := by
  have hlen : j < (S.sort).length := by rwa [Finset.length_sort]
  rw [_root_.List.getD_eq_getElem _ _ hlen]
  exact (Finset.mem_sort _).1 (List.getElem_mem hlen)

/-- The increasing enumeration of a finset is strictly increasing on the indices below its
cardinality, and reflects the order there. -/
theorem getD_sort_lt_getD_sort_iff {α : Type*} [LinearOrder α] (S : Finset α) (d : α) {j j' : ℕ}
    (hj : j < #S) (hj' : j' < #S) : (S.sort).getD j d < (S.sort).getD j' d ↔ j < j' := by
  have hlen : j < (S.sort).length := by rwa [Finset.length_sort]
  have hlen' : j' < (S.sort).length := by rwa [Finset.length_sort]
  rw [_root_.List.getD_eq_getElem _ _ hlen, _root_.List.getD_eq_getElem _ _ hlen']
  exact (Finset.sortedLT_sort S).getElem_lt_getElem_iff

/-- The increasing enumeration of a finset is injective on the indices below its cardinality. -/
theorem getD_sort_inj {α : Type*} [LinearOrder α] (S : Finset α) (d : α) {j j' : ℕ}
    (hj : j < #S) (hj' : j' < #S) (h : (S.sort).getD j d = (S.sort).getD j' d) : j = j' :=
  le_antisymm (not_lt.1 fun hc => ((getD_sort_lt_getD_sort_iff S d hj' hj).2 hc).ne' h)
    (not_lt.1 fun hc => ((getD_sort_lt_getD_sort_iff S d hj hj').2 hc).ne h)

/-- The increasing enumeration of a finset is Mathlib's order embedding `Finset.orderEmbOfFin`,
read at a plain natural number index. -/
theorem getD_sort_eq_orderEmbOfFin {α : Type*} [LinearOrder α] (S : Finset α) (d : α) {j : ℕ}
    (h : j < #S) : (S.sort).getD j d = S.orderEmbOfFin rfl ⟨j, h⟩ := by
  have hlen : j < (S.sort).length := by rwa [Finset.length_sort]
  rw [_root_.List.getD_eq_getElem _ _ hlen, Finset.orderEmbOfFin_apply]
  rfl

end Finset

namespace HJO.Dyck

/-! ### The attack set -/

/-- The attack set `At(π)` of a sequence `x : Fin n → ℕ`: the cells `(i, k)` with `x k ≤ i < k`,
which for a square Dyck path `π` with coarea sequence `x` are the cells lying between `π` and the
main diagonal, Carlsson--Mellit's `Area(π) = {(i, j) : 1 ≤ j ≤ n, x_j ≤ i ≤ j - 1}` with rows and
columns indexed from `0`. It is presented by rows: row `k` is the interval `{x k, …, k - 1}`, empty
when `k ≤ x k`. -/
@[hjo "def_dyck_attack"]
def attackSet {n : ℕ} (x : Fin n → ℕ) : Finset (ℕ × ℕ) :=
  univ.biUnion fun k : Fin n => Ico (x k) (k : ℕ) ×ˢ {(k : ℕ)}

variable {n : ℕ} {x : Fin n → ℕ}

/-- A cell `(i, j)` lies in the attack set exactly when `j` is a row of the path and
`x_j ≤ i ≤ j - 1`: Carlsson--Mellit's defining condition. -/
theorem mem_attackSet {i j : ℕ} :
    (i, j) ∈ attackSet x ↔ ∃ h : j < n, x ⟨j, h⟩ ≤ i ∧ i < j := by
  simp only [attackSet, mem_biUnion, mem_univ, true_and, mem_product, mem_Ico, mem_singleton]
  refine ⟨fun ⟨k, ⟨h1, h2⟩, h3⟩ => ?_, fun ⟨h, h1, h2⟩ => ⟨⟨j, h⟩, ⟨h1, h2⟩, rfl⟩⟩
  subst h3
  exact ⟨k.isLt, by simpa using h1, h2⟩

/-- Membership in the attack set at a row given as an element of `Fin n`, the form in which the
row decomposition is read off. -/
@[simp]
theorem mem_attackSet_coe {i : ℕ} {k : Fin n} :
    (i, (k : ℕ)) ∈ attackSet x ↔ x k ≤ i ∧ i < (k : ℕ) := by
  rw [mem_attackSet]
  exact ⟨fun ⟨_, h1, h2⟩ => ⟨by simpa using h1, h2⟩,
    fun ⟨h1, h2⟩ => ⟨k.isLt, by simpa using h1, h2⟩⟩

/-- An attacking cell is strictly above the diagonal: Carlsson--Mellit's `i ≤ j - 1`. -/
theorem fst_lt_snd_of_mem_attackSet {p : ℕ × ℕ} (hp : p ∈ attackSet x) : p.1 < p.2 :=
  (mem_attackSet.1 hp).2.2

/-- The row of an attacking cell is a row of a path of length `n`: Carlsson--Mellit's `j ≤ n`. -/
theorem snd_lt_of_mem_attackSet {p : ℕ × ℕ} (hp : p ∈ attackSet x) : p.2 < n :=
  (mem_attackSet.1 hp).1

/-- The attack set lies in the window `{(j, j') : 1 ≤ j < j' ≤ n}` that a transitive attack set on
`{1, …, n}` is required to lie in, in one piece. -/
theorem attackSet_subset_filter_lt (x : Fin n → ℕ) :
    attackSet x ⊆ {p ∈ range n ×ˢ range n | p.1 < p.2} := fun _ hp =>
  mem_filter.2 ⟨mem_product.2 ⟨mem_range.2 ((fst_lt_snd_of_mem_attackSet hp).trans
    (snd_lt_of_mem_attackSet hp)), mem_range.2 (snd_lt_of_mem_attackSet hp)⟩,
    fst_lt_snd_of_mem_attackSet hp⟩

/-- Row `k` of the attack set is the interval `{x k, …, k - 1}`: the row decomposition, and the
form in which a change to one entry of the path is compared with the attack set. -/
theorem attackSet_filter_snd (x : Fin n → ℕ) (k : Fin n) :
    {p ∈ attackSet x | p.2 = (k : ℕ)} = Ico (x k) (k : ℕ) ×ˢ {(k : ℕ)} := by
  ext ⟨i, j⟩
  simp only [mem_filter, mem_product, mem_Ico, mem_singleton]
  refine ⟨fun ⟨hp, hj⟩ => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · subst hj
    exact ⟨mem_attackSet_coe.1 hp, rfl⟩
  · subst h2
    exact ⟨mem_attackSet_coe.2 h1, rfl⟩

/-- **The attack set reads the path only away from position `0`**: row `0` of the presentation is
`Ico (x 0) 0`, empty whatever the entry there is, so two sequences agreeing at every positive
position have the same attack set. -/
theorem attackSet_congr {y : Fin n → ℕ} (h : ∀ k : Fin n, (k : ℕ) ≠ 0 → x k = y k) :
    attackSet x = attackSet y := by
  ext ⟨i, j⟩
  simp only [mem_attackSet]
  refine exists_congr fun hj => and_congr_left fun hij => ?_
  rw [h ⟨j, hj⟩ (by simpa using ((Nat.zero_le i).trans_lt hij).ne')]

/-- **The attack set does not read the first entry of the path**: row `0` contributes
`Ico (x 0) 0 = ∅`, so the entry there may be replaced by anything. Stated at length `n + 1`, where
the position `0` exists; the form at an arbitrary length is `HJO.Dyck.attackSet_congr`. -/
theorem attackSet_update_zero {n : ℕ} (x : Fin (n + 1) → ℕ) (c : ℕ) :
    attackSet (Function.update x 0 c) = attackSet x :=
  attackSet_congr fun _ hk => Function.update_of_ne (Fin.val_ne_zero_iff.1 hk) c x

/-- The attack number `at(π) = #At(π)` is the sum of the row counts: Carlsson--Mellit's
`area(π) = ∑_j a_j` together with its `a_j + x_j = j`. -/
theorem card_attackSet (x : Fin n → ℕ) : #(attackSet x) = ∑ k : Fin n, ((k : ℕ) - x k) := by
  rw [attackSet, Finset.card_biUnion]
  · simp
  · intro k _ l _ hkl
    simp only [disjoint_left, mem_product, mem_singleton]
    exact fun p hp hp' => hkl (Fin.val_injective (hp.2.symm.trans hp'.2))

/-- Lowering a path enlarges its attack set: each row grows on the left. -/
theorem attackSet_antitone : Antitone (attackSet : (Fin n → ℕ) → Finset (ℕ × ℕ)) := by
  intro y x hyx p hp
  obtain ⟨i, j⟩ := p
  obtain ⟨h, h1, h2⟩ := mem_attackSet.1 hp
  exact mem_attackSet.2 ⟨h, (hyx _).trans h1, h2⟩

/-- The staircase path hugging the diagonal, whose `j`-th north step has the abscissa
`x_j = j`, has empty attack set: there is no room between it and the diagonal. -/
@[simp]
theorem attackSet_val (n : ℕ) : attackSet (Fin.val : Fin n → ℕ) = ∅ := by
  ext ⟨i, j⟩
  simp only [notMem_empty, iff_false, mem_attackSet, not_exists]
  exact fun h hi => absurd hi.1 (by simpa using hi.2.not_ge)

/-- Among square Dyck paths the staircase is the only one with empty attack set: an entry with
`x k < k` contributes the cell `(x k, k)`, and `le_index` leaves `x k = k` otherwise. -/
theorem IsSquareDyck.attackSet_eq_empty_iff (h : IsSquareDyck n x) :
    attackSet x = ∅ ↔ x = Fin.val := by
  refine ⟨fun he => funext fun k => ?_, fun hx => hx ▸ attackSet_val n⟩
  refine (h.le_index k).antisymm (not_lt.1 fun hlt => ?_)
  have : ((x k, (k : ℕ)) : ℕ × ℕ) ∈ attackSet x := mem_attackSet_coe.2 ⟨le_rfl, hlt⟩
  simp [he] at this

/-- The path whose `n` north steps all precede its east steps, all of whose entries are the
`x_j = 1` of Carlsson--Mellit's indexing, has the whole window `{(j, j') : 1 ≤ j < j' ≤ n}` for its
attack set: it is the largest attack set of a path of length `n`. -/
theorem attackSet_zero (n : ℕ) :
    attackSet (0 : Fin n → ℕ) = {p ∈ range n ×ˢ range n | p.1 < p.2} := by
  ext ⟨i, j⟩
  simp only [mem_attackSet, mem_filter, mem_product, mem_range, Pi.zero_apply]
  exact ⟨fun ⟨h, _, h2⟩ => ⟨⟨h2.trans h, h⟩, h2⟩, fun ⟨⟨_, hj⟩, h⟩ => ⟨hj, Nat.zero_le _, h⟩⟩

/-! ### Transitive attack sets -/

/-- `R` is a transitive attack set on `{1, …, n}`: a finite set of pairs of positions lying in the
window `j < j' < n` — Carlsson--Mellit's `1 ≤ j < j' ≤ n` with both coordinates indexed from `0` —
that is closed under splitting, in that `(j, j'') ∈ R` and `j < j' < j''` force both `(j, j') ∈ R`
and `(j', j'') ∈ R`. These are exactly the attack sets of square Dyck paths of length `n`. -/
@[hjo "def_dyck_transitive"]
structure IsTransitiveAttackSet (n : ℕ) (R : Finset (ℕ × ℕ)) : Prop where
  /-- Every attacking pair is increasing: Carlsson--Mellit's `j < j'`. -/
  fst_lt_snd : ∀ p ∈ R, p.1 < p.2
  /-- Every attacking pair lies inside `{1, …, n}`: Carlsson--Mellit's `j' ≤ n`, which on positions
  indexed from `0` reads `j' < n`. -/
  snd_lt : ∀ p ∈ R, p.2 < n
  /-- Splitting an attacking pair at an intermediate position keeps the lower half: this is the
  first half of Carlsson--Mellit's `(*)`. -/
  mem_lower : ∀ {j j' j'' : ℕ}, j < j' → j' < j'' → (j, j'') ∈ R → (j, j') ∈ R
  /-- Splitting an attacking pair at an intermediate position keeps the upper half: this is the
  second half of Carlsson--Mellit's `(*)`. -/
  mem_upper : ∀ {j j' j'' : ℕ}, j < j' → j' < j'' → (j, j'') ∈ R → (j', j'') ∈ R

namespace IsTransitiveAttackSet

variable {R : Finset (ℕ × ℕ)}

/-- Both positions of an attacking pair are positions of `{1, …, n}`, so they index a labelling
`w : Fin n → ℕ`. -/
theorem fst_lt (h : IsTransitiveAttackSet n R) {p : ℕ × ℕ} (hp : p ∈ R) : p.1 < n :=
  (h.fst_lt_snd p hp).trans (h.snd_lt p hp)

/-- The window containment in Carlsson--Mellit's form: `R ⊆ {(j, j') : j < j' < n}`. -/
theorem subset_filter_lt (h : IsTransitiveAttackSet n R) :
    R ⊆ {p ∈ range n ×ˢ range n | p.1 < p.2} := fun p hp =>
  mem_filter.2 ⟨mem_product.2 ⟨mem_range.2 (h.fst_lt hp), mem_range.2 (h.snd_lt p hp)⟩,
    h.fst_lt_snd p hp⟩

/-- A transitive attack set is closed under passing to a subinterval: an attacking pair
`(j, j'') ∈ R` forces `(a, b) ∈ R` for every `j ≤ a < b ≤ j''`. This is the iterated form of the
property `(*)` of Carlsson--Mellit, and the form in which it is used. -/
theorem mem_of_le_of_lt_of_le (h : IsTransitiveAttackSet n R) {j j'' a b : ℕ}
    (hR : (j, j'') ∈ R) (hja : j ≤ a) (hab : a < b) (hb : b ≤ j'') : (a, b) ∈ R := by
  have haj'' : a < j'' := hab.trans_le hb
  have ha : (a, j'') ∈ R := by
    rcases eq_or_lt_of_le hja with rfl | hlt
    · exact hR
    · exact h.mem_upper hlt haj'' hR
  rcases eq_or_lt_of_le hb with rfl | hlt
  · exact ha
  · exact h.mem_lower hab hlt ha

end IsTransitiveAttackSet

/-- Being a transitive attack set is decidable: the window clause quantifies over the pairs of `R`
and the splitting clause over the pairs of `R` and the positions strictly between their entries. -/
instance instDecidableIsTransitiveAttackSet (n : ℕ) (R : Finset (ℕ × ℕ)) :
    Decidable (IsTransitiveAttackSet n R) :=
  decidable_of_iff ((∀ p ∈ R, p.1 < p.2 ∧ p.2 < n) ∧
      ∀ p ∈ R, ∀ j ∈ Ioo p.1 p.2, (p.1, j) ∈ R ∧ (j, p.2) ∈ R)
    ⟨fun h => ⟨fun p hp => (h.1 p hp).1, fun p hp => (h.1 p hp).2,
        fun hjj' hj'j'' hR => (h.2 _ hR _ (mem_Ioo.2 ⟨hjj', hj'j''⟩)).1,
        fun hjj' hj'j'' hR => (h.2 _ hR _ (mem_Ioo.2 ⟨hjj', hj'j''⟩)).2⟩,
      fun h => ⟨fun p hp => ⟨h.fst_lt_snd p hp, h.snd_lt p hp⟩, fun p hp j hj => by
        obtain ⟨hj1, hj2⟩ := mem_Ioo.1 hj
        exact ⟨h.mem_lower hj1 hj2 hp, h.mem_upper hj1 hj2 hp⟩⟩⟩

/-- The empty set is a transitive attack set on `{1, …, n}`: the attack set of the staircase path
hugging the diagonal, and the smallest one. -/
theorem isTransitiveAttackSet_empty (n : ℕ) : IsTransitiveAttackSet n (∅ : Finset (ℕ × ℕ)) :=
  ⟨by simp, by simp, by simp, by simp⟩

/-- The whole window is a transitive attack set on `{1, …, n}`: the attack set of the path whose
`n` north steps all precede its east steps, and the largest one. -/
theorem isTransitiveAttackSet_filter_lt (n : ℕ) :
    IsTransitiveAttackSet n {p ∈ range n ×ˢ range n | p.1 < p.2} := by
  have hmem : ∀ a b : ℕ,
      ((a, b) ∈ ({p ∈ range n ×ˢ range n | p.1 < p.2} : Finset (ℕ × ℕ))) ↔ a < n ∧ b < n ∧ a < b :=
    fun a b => by simp [mem_filter, mem_product, and_assoc]
  refine ⟨fun p hp => (mem_filter.1 hp).2,
      fun p hp => mem_range.1 (mem_product.1 (mem_filter.1 hp).1).2, ?_, ?_⟩ <;>
    intro j j' j'' h1 h2 h3 <;> rw [hmem] at h3 ⊢ <;> omega

/-! ### The restriction of an attack set -/

/-- The restriction `R_S` of a set `R` of attacking pairs of positions to a set `S` of positions:
writing `s_0 < s_1 < ⋯ < s_{m-1}` for the increasing enumeration of `S`, where `m = #S`, the pairs
`(j, j')` with `j < j' < m` and `(s_j, s_{j'}) ∈ R`. Positions are indexed from `0`, as for the
paths of `HJO.Dyck.IsSquareDyck`, so Carlsson--Mellit's `s_j` for `1 ≤ j ≤ m` is
`S.sort.getD (j - 1) 0` and their range condition `1 ≤ j < j' ≤ m` is `j < j' < m`. -/
@[hjo "def_dyck_restrict"]
def attackRestrict (R : Finset (ℕ × ℕ)) (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  {p ∈ range #S ×ˢ range #S | p.1 < p.2 ∧ (S.sort.getD p.1 0, S.sort.getD p.2 0) ∈ R}

/-- Membership in the restriction `R_S`: the pairs of `R_S` are the `(j, j')` with `j < j' < #S`
whose images under the increasing enumeration of `S` attack each other. -/
@[simp]
theorem mem_attackRestrict {R : Finset (ℕ × ℕ)} {S : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ attackRestrict R S ↔
      p.1 < p.2 ∧ p.2 < #S ∧ (S.sort.getD p.1 0, S.sort.getD p.2 0) ∈ R := by
  simp only [attackRestrict, mem_filter, mem_product, mem_range]
  exact ⟨fun h => ⟨h.2.1, h.1.2, h.2.2⟩, fun h => ⟨⟨h.1.trans h.2.1, h.2.1⟩, h.1, h.2.2⟩⟩

/-- For an `R` consisting of increasing pairs — as every attack set is — the clause `j < j'` in
the restriction is automatic, so `R_S` is Carlsson--Mellit's `{(j, j') : (s_j, s_{j'}) ∈ R}`. -/
theorem mem_attackRestrict_iff_of_forall_lt {R : Finset (ℕ × ℕ)} (hR : ∀ q ∈ R, q.1 < q.2)
    {S : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ attackRestrict R S ↔
      p.1 < #S ∧ p.2 < #S ∧ (S.sort.getD p.1 0, S.sort.getD p.2 0) ∈ R := by
  rw [mem_attackRestrict]
  refine ⟨fun h => ⟨h.1.trans h.2.1, h.2.1, h.2.2⟩, fun h => ⟨?_, h.2.1, h.2.2⟩⟩
  exact (Finset.getD_sort_lt_getD_sort_iff S 0 h.1 h.2.1).1 (hR _ h.2.2)

/-- Restricting along the whole index set `{0, …, n-1}` is inert: it keeps the increasing pairs of
`R` inside the range and renumbers nothing. -/
theorem attackRestrict_range (R : Finset (ℕ × ℕ)) (n : ℕ) :
    attackRestrict R (range n) = {p ∈ R | p.1 < p.2 ∧ p.2 < n} := by
  have hget : ∀ i, i < n → (range n).sort.getD i 0 = i := fun i hi => by
    rw [Finset.sort_range, _root_.List.getD_eq_getElem _ _ (by simpa using hi),
      _root_.List.getElem_range]
  ext p
  simp only [mem_attackRestrict, Finset.card_range, mem_filter]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hget _ (h.1.trans h.2.1), hget _ h.2.1] at h
    exact ⟨h.2.2, h.1, h.2.1⟩
  · rw [hget _ (h.2.1.trans h.2.2), hget _ h.2.2]
    exact ⟨h.2.1, h.2.2, h.1⟩

/-- Restricting to no positions leaves no pairs. -/
@[simp]
theorem attackRestrict_empty (R : Finset (ℕ × ℕ)) : attackRestrict R ∅ = ∅ := by
  ext p; simp

/-! ### The square partner of an above-diagonal path -/

/-- **The square partner `P̂'` of an above-diagonal path**, as the sequence of rowwise minima of a
set of attacking pairs: `x'_j = min({i : (i, j) ∈ A} ∪ {j})`, the union with `{j}` reading an empty
row as a north step on the diagonal.

In the application `A` is the attack set `𝒜(P̂)` of an above-diagonal `(aN, bN)`-path, whose
north steps are listed in strictly increasing order of above-diagonal rank, and calls the resulting
sequence the square partner. The definition is stated at a general `A : Finset (ℕ × ℕ)` because
nothing about the minimum reads the path:
`HJO.Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet` is stated with exactly this
formula as a hypothesis and needs only that `A` is a transitive attack set, and stating it here at a
path would fix the rank-order relabelling of `HJO.Paths.sweepAttack` — which indexes north steps by
the height of their feet, not by position in the rank order — inside the definition, where no
consumer wants it. Generalising the input weakens nothing.

`sInf` is `Nat.sInf`, and the set is nonempty, containing `j` by the disjunct `i = j`; so this is a
genuine minimum and not the junk value `0` (`HJO.Dyck.attackPartner_le`). Positions are indexed
from `0`, so the `x'_j` for `1 ≤ j ≤ bN` is `attackPartner A (j - 1)`. -/
@[hjo "def_sweep_dyck_partner"]
noncomputable def attackPartner (A : Finset (ℕ × ℕ)) (j : ℕ) : ℕ :=
  sInf {i | (i, j) ∈ A ∨ i = j}

/-- The partner entry is at most the row index: the minimum is over a set containing `j`, so this
is the square Dyck path condition `x'_j ≤ j` and, in particular, `sInf` is not the junk value. -/
theorem attackPartner_le (A : Finset (ℕ × ℕ)) (j : ℕ) : attackPartner A j ≤ j :=
  Nat.sInf_le (Or.inr rfl)

/-- Either the partner entry is the row index — an empty row, a north step on the diagonal — or it
is the leftmost column attacking that row. -/
theorem attackPartner_spec (A : Finset (ℕ × ℕ)) (j : ℕ) :
    (attackPartner A j, j) ∈ A ∨ attackPartner A j = j :=
  Nat.sInf_mem (s := {i | (i, j) ∈ A ∨ i = j}) ⟨j, Or.inr rfl⟩

/-- The partner entry is a lower bound for its row: every column attacking the row `j` lies weakly
right of `x'_j`. -/
theorem attackPartner_le_of_mem {A : Finset (ℕ × ℕ)} {i j : ℕ} (hi : (i, j) ∈ A) :
    attackPartner A j ≤ i :=
  Nat.sInf_le (Or.inl hi)

/-- **The rowwise minima of `At(π)` return `π`.** This is the value check on `attackPartner`: at the
attack set of a square Dyck path the definition recovers the path, so the minimum is the inverse of
`HJO.Dyck.attackSet` and not merely some sequence attached to it. Together with
`HJO.Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet` — whose hypothesis is exactly this
formula, discharged here by `attackPartner` itself — it makes `At` a bijection from the square Dyck
paths of length `n` onto the transitive attack sets on `{1, …, n}`.

Only the diagonal bound `x_k ≤ k` of `HJO.Dyck.IsSquareDyck` is used, not the monotonicity. -/
theorem attackPartner_attackSet {n : ℕ} {x : Fin n → ℕ} (h : ∀ k : Fin n, x k ≤ (k : ℕ))
    (k : Fin n) : attackPartner (attackSet x) (k : ℕ) = x k := by
  have hmem : x k ∈ {i | (i, (k : ℕ)) ∈ attackSet x ∨ i = (k : ℕ)} := by
    rcases eq_or_lt_of_le (h k) with heq | hlt
    · exact Or.inr heq
    · exact Or.inl (mem_attackSet_coe.2 ⟨le_rfl, hlt⟩)
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨x k, hmem⟩ ?_)
  rintro i (hi | rfl)
  · exact (mem_attackSet_coe.1 hi).1
  · exact h k

/-- The square partner of a square Dyck path is the path itself, in the form a consumer holding
`HJO.Dyck.IsSquareDyck` wants. -/
theorem IsSquareDyck.attackPartner_attackSet {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x)
    (k : Fin n) : attackPartner (attackSet x) (k : ℕ) = x k :=
  _root_.HJO.Dyck.attackPartner_attackSet h.le_index k

/-- The empty attack set has the staircase for its partner, `x'_j = j` for every row: the minimum is
over `{j}` alone. -/
@[simp]
theorem attackPartner_empty (j : ℕ) : attackPartner ∅ j = j := by
  rw [attackPartner]
  refine le_antisymm (Nat.sInf_le (Or.inr rfl)) (le_csInf ⟨j, Or.inr rfl⟩ ?_)
  rintro i (hi | rfl)
  · exact absurd hi (notMem_empty (i, j))
  · exact le_rfl

/-! ### `At` is a bijection onto the transitive attack sets

The two directions: the attack set of a path is a transitive attack set, and every transitive attack
set is the attack set of the path recovered from it by rowwise minima. -/

/-- **The attack set `At(π)` of a square Dyck path `π` of length `n` is a transitive attack set on
`{1, …, n}`**: Carlsson--Mellit's property `(*)`, that an attacking pair `(j, j'')` splits at every
intermediate position `j'` into attacking pairs `(j, j')` and `(j', j'')`, together with the
containment in the window `1 ≤ j < j' ≤ n`.

Only the monotonicity of the coarea sequence is needed, so a path is passed in as
`HJO.Dyck.IsSquareDyck.mono`. The window clauses hold for an arbitrary sequence; monotonicity enters
only in the two splitting clauses, where the lower half needs `x_{j'} ≤ x_{j''}` and the upper half
needs nothing but `x_{j''} ≤ j < j'`. -/
@[hjo "lem_dyck_attack_transitive"]
theorem isTransitiveAttackSet_attackSet {n : ℕ} {x : Fin n → ℕ} (hx : Monotone x) :
    IsTransitiveAttackSet n (attackSet x) where
  fst_lt_snd _ hp := fst_lt_snd_of_mem_attackSet hp
  snd_lt _ hp := snd_lt_of_mem_attackSet hp
  mem_lower {j j' j''} hjj' hj'j'' hR := by
    obtain ⟨hn, hxj, -⟩ := mem_attackSet.1 hR
    exact mem_attackSet.2 ⟨hj'j''.trans hn, (hx hj'j''.le).trans hxj, hjj'⟩
  mem_upper {j j' j''} hjj' hj'j'' hR := by
    obtain ⟨hn, hxj, -⟩ := mem_attackSet.1 hR
    exact mem_attackSet.2 ⟨hn, hxj.trans hjj'.le, hj'j''⟩

/-- **A transitive attack set is the attack set of a square Dyck path, recovered from it by rowwise
minima.** Let `A` be a transitive attack set on `{1, …, n}` and let `x` be its sequence of rowwise
minima, `x_j = min({i : (i, j) ∈ A} ∪ {j})` — that is, `HJO.Dyck.attackPartner A j`. Then `x` is a
square Dyck path of length `n` and its attack set is `A`.

In the application `A` is the attack
set `𝒜(P̂)` of an above-diagonal path — a transitive attack set by
`HJO.Paths.isTransitiveAttackSet_attackPositions` — and `x` is the square partner `P̂'` of
`HJO.Dyck.attackPartner`. Together with `HJO.Dyck.isTransitiveAttackSet_attackSet` it says that `At`
is a bijection from the square Dyck paths of length `n` onto the transitive attack sets on
`{1, …, n}`.

The recovered sequence is pinned by `hx` rather than written into the conclusion, which is the form
both consumers want; `HJO.Dyck.isSquareDyck_attackPartner` is the instance at
`x = attackPartner A`, where `hx` is `rfl`.

Three of the four fields of `hA` are used: `mem_lower` (through `mem_of_le_of_lt_of_le` at `a = j`)
for `Monotone x`, `mem_upper` (the same lemma at `b = j''`) for `At(x) ⊆ A`, and the two window
fields for `A ⊆ At(x)`. -/
@[hjo "lem_sweep_partner_attack"]
theorem isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet {n : ℕ} {A : Finset (ℕ × ℕ)}
    {x : Fin n → ℕ} (hA : IsTransitiveAttackSet n A)
    (hx : ∀ k : Fin n, x k = attackPartner A (k : ℕ)) :
    IsSquareDyck n x ∧ attackSet x = A := by
  have hle : ∀ k : Fin n, x k ≤ (k : ℕ) := fun k =>
    (hx k).trans_le (attackPartner_le A (k : ℕ))
  have hlow : ∀ (k : Fin n) (i : ℕ), (i, (k : ℕ)) ∈ A → x k ≤ i := fun k i hi =>
    (hx k).trans_le (attackPartner_le_of_mem hi)
  have hmem : ∀ k : Fin n, (x k, (k : ℕ)) ∈ A ∨ x k = (k : ℕ) := fun k => by
    rw [hx k]; exact attackPartner_spec A (k : ℕ)
  refine ⟨⟨fun k l hkl => ?_, hle⟩, ?_⟩
  · have hkl' : (k : ℕ) ≤ (l : ℕ) := hkl
    rcases hmem l with h | h
    · rcases le_or_gt (k : ℕ) (x l) with hc | hc
      · exact (hle k).trans hc
      · exact hlow k (x l) (hA.mem_of_le_of_lt_of_le h le_rfl hc hkl')
    · exact (hle k).trans (hkl'.trans_eq h.symm)
  · ext ⟨i, j⟩
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · obtain ⟨hj, h1, h2⟩ := mem_attackSet.1 hp
      refine hA.mem_of_le_of_lt_of_le ?_ h1 h2 le_rfl
      rcases hmem ⟨j, hj⟩ with h | h
      · exact h
      · exact absurd h2 (by have h' : x ⟨j, hj⟩ = j := h; omega)
    · exact mem_attackSet.2 ⟨hA.snd_lt _ hp, hlow ⟨j, hA.snd_lt _ hp⟩ i hp, hA.fst_lt_snd _ hp⟩

/-- The square partner of a transitive attack set on `{1, …, n}` is a square Dyck path of length `n`
whose attack set is that set: `HJO.Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet` with
the recovered sequence supplied, where the pinning hypothesis is `rfl`. -/
theorem isSquareDyck_attackPartner {n : ℕ} {A : Finset (ℕ × ℕ)}
    (hA : IsTransitiveAttackSet n A) :
    IsSquareDyck n (fun k : Fin n => attackPartner A (k : ℕ)) ∧
      attackSet (fun k : Fin n => attackPartner A (k : ℕ)) = A :=
  isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet hA fun _ => rfl

/-! ### Restriction preserves transitivity and does not increase the size -/

/-- **A restriction of a transitive attack set is a transitive attack set.** `R_S` lies in the
window `{(j, j') : j < j' < #S}` by `HJO.Dyck.mem_attackRestrict`, and splits because the increasing
enumeration of `S` is order-reflecting: from `j < j' < j''` it gives `s_j < s_{j'} < s_{j''}`, and
then the two splitting clauses of `R` apply.

The rank `n` of `R` plays no part in the conclusion — the window of `R_S` is `#S`, read off the
restriction itself — so `hR` is used only for its two splitting fields. -/
@[hjo "lem_dyck_restrict_transitive"]
theorem isTransitiveAttackSet_attackRestrict {n : ℕ} {R : Finset (ℕ × ℕ)} (S : Finset ℕ)
    (hR : IsTransitiveAttackSet n R) : IsTransitiveAttackSet #S (attackRestrict R S) where
  fst_lt_snd _ hp := (mem_attackRestrict.1 hp).1
  snd_lt _ hp := (mem_attackRestrict.1 hp).2.1
  mem_lower {j j' j''} hjj' hj'j'' hp := by
    obtain ⟨h1, h2, h3⟩ := mem_attackRestrict.1 hp
    refine mem_attackRestrict.2 ⟨hjj', hj'j''.trans h2, ?_⟩
    exact hR.mem_lower ((getD_sort_lt_getD_sort_iff S 0 (h1.trans h2) (hj'j''.trans h2)).2 hjj')
      ((getD_sort_lt_getD_sort_iff S 0 (hj'j''.trans h2) h2).2 hj'j'') h3
  mem_upper {j j' j''} hjj' hj'j'' hp := by
    obtain ⟨h1, h2, h3⟩ := mem_attackRestrict.1 hp
    refine mem_attackRestrict.2 ⟨hj'j'', h2, ?_⟩
    exact hR.mem_upper ((getD_sort_lt_getD_sort_iff S 0 (h1.trans h2) (hj'j''.trans h2)).2 hjj')
      ((getD_sort_lt_getD_sort_iff S 0 (hj'j''.trans h2) h2).2 hj'j'') h3

/-- **A restriction is no larger than the set it restricts**: `#R_S ≤ #R`, because
`(j, j') ↦ (s_j, s_{j'})` is injective and carries `R_S` into `R`.

The hypothesis that `R` lies in the window `{(j, j') : 1 ≤ j < j' ≤ n}` is not needed:
the injection lands in `R` by the definition of `R_S`, whatever `R` is. -/
@[hjo "lem_dyck_restrict_card"]
theorem card_attackRestrict_le (R : Finset (ℕ × ℕ)) (S : Finset ℕ) :
    #(attackRestrict R S) ≤ #R := by
  refine Finset.card_le_card_of_injOn
    (fun p => (S.sort.getD p.1 0, S.sort.getD p.2 0)) (fun p hp => (mem_attackRestrict.1 hp).2.2)
    (fun p hp q hq h => ?_)
  obtain ⟨hp1, hp2, -⟩ := mem_attackRestrict.1 hp
  obtain ⟨hq1, hq2, -⟩ := mem_attackRestrict.1 hq
  obtain ⟨e1, e2⟩ := Prod.mk.injEq .. ▸ h
  exact Prod.ext (getD_sort_inj S 0 (hp1.trans hp2) (hq1.trans hq2) e1)
    (getD_sort_inj S 0 hp2 hq2 e2)

/-! ### Value checks against Carlsson--Mellit's worked example

Carlsson--Mellit's running path of length `8` has coarea sequence `x = (1,2,2,2,3,3,7,7)`, which on
entries and positions indexed from `0` is `![0,1,1,1,2,2,6,6]` — the path of
`HJO.Dyck.isSquareDyck_source_example`. Its row counts `j - x_j` are
`0,0,1,2,2,3,0,1`, so its attack number is `9`; row `3` is the pair of cells `(1,3), (2,3)`. -/

theorem card_attackSet_source_example : #(attackSet ![0, 1, 1, 1, 2, 2, 6, 6]) = 9 := by decide

theorem attackSet_filter_snd_source_example :
    {p ∈ attackSet ![0, 1, 1, 1, 2, 2, 6, 6] | p.2 = 3} = {(1, 3), (2, 3)} := by decide

/-- The attack set of Carlsson--Mellit's example is a transitive attack set on `{1, …, 8}`: the
conclusion of `HJO.Dyck.isTransitiveAttackSet_attackSet` at one path, checked by computation. -/
theorem isTransitiveAttackSet_attackSet_source_example :
    IsTransitiveAttackSet 8 (attackSet ![0, 1, 1, 1, 2, 2, 6, 6]) := by decide

/-- `{(0, 2)}` is not a transitive attack set: splitting the pair at `1` produces `(0, 1)`, which
is absent. This is the condition being live rather than vacuous. -/
theorem not_isTransitiveAttackSet_singleton : ¬IsTransitiveAttackSet 3 {((0 : ℕ), (2 : ℕ))} := by
  decide

/-- The increasing enumeration of `{2, 3, 5}`. `Finset.sort` is a merge sort on a quotient and does
not reduce in the kernel, so the enumeration is computed by `Finset.sort_insert` rather than by
`decide`. -/
theorem sort_two_three_five : ({2, 3, 5} : Finset ℕ).sort = [2, 3, 5] := by
  rw [Finset.sort_insert (r := fun a b : ℕ => a ≤ b) (by decide) (by decide),
    Finset.sort_insert (r := fun a b : ℕ => a ≤ b) (by decide) (by decide),
    Finset.sort_singleton]

/-- Restricting Carlsson--Mellit's example to the rows `{2, 3, 5}` renumbers them as `0, 1, 2` and
keeps the pairs `(2,3), (2,5), (3,5)`, that is `(0,1), (0,2), (1,2)`: every one of the three rows
attacks the others, because row `5` reaches down to column `2`. The renumbering is what is being
checked: the answer mentions none of `2`, `3`, `5`. -/
theorem attackRestrict_source_example :
    attackRestrict (attackSet ![0, 1, 1, 1, 2, 2, 6, 6]) {2, 3, 5} =
      {(0, 1), (0, 2), (1, 2)} := by
  rw [attackRestrict, sort_two_three_five]
  decide

end HJO.Dyck
