/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ColouringBraidData

/-! # Inserting one point into a column listing

`HJO.Mellit.colStep` lists a finite set of lattice points in increasing order of column, and
`HJO.Mellit.ColumnInjective` says the set meets each column at most once — which both halves of a
colouring do. This file answers the one question the level recursion asks of that listing: **what
happens to it when a single point is inserted in a fresh column?**

The answer is the expected one, and the point of the file is to state it as an equation rather
than as a sentence. With

`j = #{Q ∈ S | x(Q) < x(P)}`

the number of members already left of the new point,

* `HJO.Mellit.colStep_insert_self` — the new point is the `j`-th member of the longer listing;
* `HJO.Mellit.colStep_insert_of_lt`, `HJO.Mellit.colStep_insert_of_le` — every old member keeps its
  index below `j` and has it raised by one at or above `j`.

Together those two are exactly `colStep (insert P S) ∘ j.succAbove = colStep S` read on `ℕ`, which
is the shape `HJO.Braid.specialMoveList_eq_map_succAbove` and the whole rank-raise layer take their
insertion index in.

## The engine

Everything runs off one characterisation, `HJO.Mellit.card_filter_fst_lt_colStep`: for a
column-injective set the index of a member in the listing is the *number of members strictly left of
it*,

`#{Q ∈ S | x(Q) < x(colStep S i)} = i`.

That is proved by squeezing the two counting bounds `HJO.Mellit.card_filter_fst_lt_le` and
`HJO.Mellit.le_card_filter_fst_lt` that `HJO/Shuffle/ColouringBraidData.lean` already carries,
using that a column carrying a member carries exactly one. Read backwards
(`HJO.Mellit.colStep_card_filter_fst_lt`) it says that the listing of a column-injective set is
determined pointwise by the count, which is what makes the insertion computation a count computation
and so avoids reasoning about `List.mergeSort` at all.

No hypothesis beyond column-injectivity is used, and nothing here is about colourings: `S` is an
arbitrary finite set of lattice points meeting each column once, and `P` an arbitrary point in a
column `S` does not meet.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

/-! ### The index of a member is the number of members to its left -/

/-- **A column carrying a member of a column-injective set carries exactly one**, which is the step
that turns the two counting bounds into an equality. -/
theorem card_filter_fst_eq_colStep {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) {i : ℕ}
    (hi : i < #S) : #({P ∈ S | P.1 = (colStep S i).1}) = 1 :=
  Finset.card_eq_one.2 ⟨colStep S i, Finset.eq_singleton_iff_unique_mem.2
    ⟨Finset.mem_filter.2 ⟨colStep_mem hi, rfl⟩, fun _Q hQ =>
      hcol _ (Finset.mem_filter.1 hQ).1 _ (colStep_mem hi) (Finset.mem_filter.1 hQ).2⟩⟩

/-- **The index of a member in the column listing is the number of members strictly left of it.**
`HJO.Mellit.card_filter_fst_lt_le` gives `≤ i` at the member's own column and
`HJO.Mellit.le_card_filter_fst_lt` gives `≥ i + 1` one column further right; the difference between
the two counts is the single member in that column. -/
theorem card_filter_fst_lt_colStep {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) {i : ℕ}
    (hi : i < #S) : #({P ∈ S | P.1 < (colStep S i).1}) = i := by
  refine le_antisymm (card_filter_fst_lt_le hcol hi le_rfl) ?_
  have h1 := le_card_filter_fst_lt hcol hi (Nat.lt_succ_self (colStep S i).1)
  rw [card_filter_fst_lt_succ, card_filter_fst_eq_colStep hcol hi] at h1
  omega

/-- **The column listing of a column-injective set is recovered from the counting function**: a
member sits at the index counting the members to its left. This is
`HJO.Mellit.card_filter_fst_lt_colStep` read backwards, and it is what makes every statement below a
computation with `Finset.card` rather than with the sorted list. -/
theorem colStep_card_filter_fst_lt {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) {P : ℕ × ℕ}
    (hP : P ∈ S) : colStep S #({Q ∈ S | Q.1 < P.1}) = P := by
  obtain ⟨i, hi, rfl⟩ := exists_colStep hP
  rw [card_filter_fst_lt_colStep hcol hi]

/-! ### Counting past an inserted point -/

/-- Inserting a point left of a column adds one to the count there. -/
theorem card_filter_fst_lt_insert_of_lt {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP : P ∉ S) {t : ℕ}
    (h : P.1 < t) : #({Q ∈ insert P S | Q.1 < t}) = #({Q ∈ S | Q.1 < t}) + 1 := by
  classical
  rw [Finset.filter_insert, ite_eq_left_of_eq_true _ _ (eq_true h),
    Finset.card_insert_of_notMem fun hc => hP (Finset.mem_filter.1 hc).1]

/-- Inserting a point at or right of a column leaves the count there alone. -/
theorem card_filter_fst_lt_insert_of_not_lt {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} {t : ℕ}
    (h : ¬ P.1 < t) : #({Q ∈ insert P S | Q.1 < t}) = #({Q ∈ S | Q.1 < t}) := by
  classical
  rw [Finset.filter_insert, ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- **Inserting a point in a fresh column preserves column-injectivity.** -/
theorem columnInjective_insert {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hcol : ColumnInjective S) (hnew : ∀ Q ∈ S, Q.1 ≠ P.1) : ColumnInjective (insert P S) := by
  intro Q hQ R hR hQR
  rcases Finset.mem_insert.1 hQ with rfl | hQ' <;> rcases Finset.mem_insert.1 hR with rfl | hR'
  · rfl
  · exact absurd hQR.symm (hnew R hR')
  · exact absurd hQR (hnew Q hQ')
  · exact hcol Q hQ' R hR' hQR

/-- A member strictly right of the inserted point has at least as many members of the old set to
its left as the inserted point does. -/
theorem le_card_filter_of_lt_fst_colStep {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hcol : ColumnInjective S) {i : ℕ} (hi : i < #S) (h : P.1 < (colStep S i).1) :
    #({Q ∈ S | Q.1 < P.1}) ≤ i := by
  have hsub : {Q ∈ S | Q.1 < P.1} ⊆ {Q ∈ S | Q.1 < (colStep S i).1} := fun Q hQ =>
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hQ).1, (Finset.mem_filter.1 hQ).2.trans h⟩
  have hc := Finset.card_le_card hsub
  rwa [card_filter_fst_lt_colStep hcol hi] at hc

/-- A member strictly left of the inserted point is itself counted by the inserted point's index,
so that index is strictly larger. -/
theorem lt_card_filter_of_fst_colStep_lt {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hcol : ColumnInjective S) {i : ℕ} (hi : i < #S) (h : (colStep S i).1 < P.1) :
    i < #({Q ∈ S | Q.1 < P.1}) := by
  have hnm : colStep S i ∉ {Q ∈ S | Q.1 < (colStep S i).1} :=
    fun hc => absurd (Finset.mem_filter.1 hc).2 (lt_irrefl _)
  have hsub : insert (colStep S i) {Q ∈ S | Q.1 < (colStep S i).1} ⊆ {Q ∈ S | Q.1 < P.1} := by
    intro Q hQ
    rcases Finset.mem_insert.1 hQ with rfl | hQ'
    · exact Finset.mem_filter.2 ⟨colStep_mem hi, h⟩
    · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hQ').1,
        (Finset.mem_filter.1 hQ').2.trans h⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnm, card_filter_fst_lt_colStep hcol hi] at hcard
  omega

/-! ### The listing of an insertion -/

/-- **The inserted point sits at the index counting the members already to its left.** -/
theorem colStep_insert_self {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hcol : ColumnInjective S)
    (hnew : ∀ Q ∈ S, Q.1 ≠ P.1) :
    colStep (insert P S) #({Q ∈ S | Q.1 < P.1}) = P := by
  have h := colStep_card_filter_fst_lt (columnInjective_insert hcol hnew)
    (Finset.mem_insert_self P S)
  rwa [card_filter_fst_lt_insert_of_not_lt (lt_irrefl _)] at h

/-- **Below the insertion index the listing is unchanged.** -/
theorem colStep_insert_of_lt {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hcol : ColumnInjective S)
    (hnew : ∀ Q ∈ S, Q.1 ≠ P.1) {i : ℕ} (hi : i < #S)
    (hij : i < #({Q ∈ S | Q.1 < P.1})) : colStep (insert P S) i = colStep S i := by
  have h := colStep_card_filter_fst_lt (columnInjective_insert hcol hnew)
    (Finset.mem_insert_of_mem (colStep_mem hi) : colStep S i ∈ insert P S)
  have hnp : ¬ P.1 < (colStep S i).1 := fun hp =>
    absurd (le_card_filter_of_lt_fst_colStep hcol hi hp) (by omega)
  rwa [card_filter_fst_lt_insert_of_not_lt hnp, card_filter_fst_lt_colStep hcol hi] at h

/-- **At or above the insertion index every index of the listing is raised by one.** -/
theorem colStep_insert_of_le {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hcol : ColumnInjective S)
    (hP : P ∉ S) (hnew : ∀ Q ∈ S, Q.1 ≠ P.1) {i : ℕ} (hi : i < #S)
    (hij : #({Q ∈ S | Q.1 < P.1}) ≤ i) : colStep (insert P S) (i + 1) = colStep S i := by
  have h := colStep_card_filter_fst_lt (columnInjective_insert hcol hnew)
    (Finset.mem_insert_of_mem (colStep_mem hi) : colStep S i ∈ insert P S)
  have hnp : P.1 < (colStep S i).1 := by
    by_contra hcon
    exact absurd (lt_card_filter_of_fst_colStep_lt hcol hi
      (lt_of_le_of_ne (not_lt.1 hcon) (hnew _ (colStep_mem hi)))) (by omega)
  rwa [card_filter_fst_lt_insert_of_lt hP hnp, card_filter_fst_lt_colStep hcol hi] at h

/-- **The listing of an insertion, read through `Fin.succAbove`.** With `j` the insertion index the
longer listing restricted along `j.succAbove` is the shorter one: this is the form the rank-raise
layer's `HJO.Braid.specialMoveList_eq_map_succAbove` and
`HJO.Mellit.braidValueOfData_succAbove_eq_dplus` take their bottom insertion in. -/
theorem colStep_insert_succAbove {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hcol : ColumnInjective S)
    (hP : P ∉ S) (hnew : ∀ Q ∈ S, Q.1 ≠ P.1) {k : ℕ} (hk : #S = k) (j : Fin (k + 1))
    (hj : (j : ℕ) = #({Q ∈ S | Q.1 < P.1})) (i : Fin k) :
    colStep (insert P S) ((j.succAbove i : Fin (k + 1)) : ℕ) = colStep S (i : ℕ) := by
  have hi : (i : ℕ) < #S := by rw [hk]; exact i.isLt
  rcases lt_or_ge (i : ℕ) (j : ℕ) with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (show i.castSucc < j from h), Fin.val_castSucc]
    exact colStep_insert_of_lt hcol hnew hi (by omega)
  · rw [Fin.succAbove_of_le_castSucc _ _ (show j ≤ i.castSucc from h), Fin.val_succ]
    exact colStep_insert_of_le hcol hP hnew hi (by omega)

end HJO.Mellit

end
