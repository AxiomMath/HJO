/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.List.GetD
public import HJO.CarlssonMellit.Tableaux
public meta import HJO.Attr

/-! # The diagram of a partition, the row bound on a tableau entry, and the Kostka numbers

Three results of classical symmetric-function theory: `D_λ`, the Young diagram whose
`i`-th row has `λ_i` cells; the bound `T(i,j) ≥ i` forced on a semistandard tableau by column
strictness; and `K_D(α)`, the number of semistandard tableaux of shape `D` and content `α`.

## Main definitions

* `HJO.Sym.partitionDiagram`: `D_λ`.
* `HJO.Sym.kostka`: `K_D(α)`.

## Main statements

* `YoungDiagram.card_eq_sum_rowLen`: the number of cells is the sum of the row lengths.
* `HJO.Sym.card_partitionDiagram`, `D_λ` has `d` cells.
* `SemistandardYoungTableau.row_le_entry`.
* `HJO.Sym.finite_ssyt_wt_eq`: the tableaux of a given content are finite, which is the clause
  the definition of `HJO.Sym.kostka` attaches to its count.

## Implementation notes

The version of `Mathlib` used here has no map from `Nat.Partition` to `YoungDiagram` — the
`ofPartition` / `toPartition` pair lives in a later revision, and neither does
`card_eq_sum_rowLens`. Both are supplied here. `partitionDiagram` is `YoungDiagram.ofRowLens`
applied to the nonincreasing listing `p.parts.sort (· ≥ ·)`, whose sortedness is
`Multiset.pairwise_sort` and whose positivity is `Nat.Partition.parts_pos`; everything else is read
off `rowLen_ofRowLens`.

Indices are `Mathlib`'s, so `0`-based: the `1`-based rows `1, …, m` are `0, …, m-1` and the
`1`-based `T(i,j) ≥ i` reads `i ≤ T i j` with both sides lowered by one, which is the same
inequality.

`kostka` is a `Set.ncard` rather than a `Finset.card`: `SemistandardYoungTableau μ` carries no
`Fintype` instance in that version, and the finiteness asserted alongside the usual definition is
exactly `finite_ssyt_wt_eq`, proved separately. Content is read as the `Finsupp`
`SemistandardYoungTableau.wt`, which `wt_apply` identifies with the content `ct(T)`.

## References

This file formalises `HJO.Sym.partitionDiagram`, `HJO.Sym.card_partitionDiagram`,
`SemistandardYoungTableau.row_le_entry` and `HJO.Sym.finite_ssyt_wt_eq`.
-/

@[expose] public section

open Finset

/-- A prefix sum of a list of naturals, read as a sum over an index range with the list extended by
zeros: the shape in which the partial sums of a partition get compared. -/
theorem List.sum_take_eq_sum_range_getD (l : List ℕ) (i : ℕ) :
    (l.take i).sum = ∑ j ∈ Finset.range i, l.getD j 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, ← ih]
    by_cases h : i < l.length
    · rw [List.sum_take_succ _ _ h, _root_.List.getD_eq_getElem l 0 h]
    · rw [_root_.List.getD_eq_default l 0 (by omega), add_zero,
        List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

namespace YoungDiagram

/-- **The number of cells is the sum of the row lengths**, over any window containing every
nonempty row. Grouping the cells by their first coordinate is `card_eq_sum_card_fiberwise`, and the
fibre over `i` is the row `μ.row i`, whose cardinality is `μ.rowLen i`. -/
theorem card_eq_sum_rowLen (μ : YoungDiagram) {N : ℕ} (hN : μ.colLen 0 ≤ N) :
    μ.card = ∑ i ∈ range N, μ.rowLen i := by
  have hmaps : Set.MapsTo Prod.fst (↑μ.cells : Set (ℕ × ℕ)) (↑(range N) : Set ℕ) := by
    rintro ⟨i, j⟩ hc
    rw [Finset.mem_coe, mem_cells] at hc
    rw [Finset.mem_coe, mem_range]
    exact lt_of_lt_of_le (mem_iff_lt_colLen.1 (μ.up_left_mem le_rfl (Nat.zero_le j) hc)) hN
  rw [YoungDiagram.card, card_eq_sum_card_fiberwise hmaps]
  exact sum_congr rfl fun i _ => μ.rowLen_eq_card.symm

/-- A row past the last nonempty one is empty. -/
theorem rowLen_eq_zero_of_colLen_le {μ : YoungDiagram} {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  by_contra h
  exact absurd (mem_iff_lt_colLen.1 (mem_iff_lt_rowLen.2 (Nat.pos_of_ne_zero h))) (by omega)

end YoungDiagram

namespace SemistandardYoungTableau

/-- **A tableau entry is at least its row index.** Column strictness makes
the entries of a column strictly increasing downwards, and they are natural numbers, so the entry in
row `i` has climbed at least `i` steps above the entry in row `0`.

The usual convention reads rows and entries from `1`; `Mathlib` reads both from `0`, so the
`1`-based `T(i,j) ≥ i` is this inequality with each side lowered by one. -/
@[hjo "lem_sf_ssyt_row_bound"]
theorem row_le_entry {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j : ℕ}
    (hc : (i, j) ∈ μ) : i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hc' : (i, j) ∈ μ := μ.up_left_mem (Nat.le_succ i) le_rfl hc
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hc') (T.col_strict (Nat.lt_succ_self i) hc))

end SemistandardYoungTableau

namespace HJO.Sym

/-! ### The diagram of a partition -/

/-- **The diagram `D_λ` of a partition.** The Young diagram whose `i`-th
row has `λ_i` cells, `λ` being listed in nonincreasing order; the `1`-based pairs `(i,j)` with
`i ≤ m` and `j ≤ λ_i`, read `0`-based as `i < m` and `j < λ_i`. -/
@[hjo "def_sf_partition_diagram"]
def partitionDiagram {d : ℕ} (p : Nat.Partition d) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·))
    (List.sortedGE_iff_pairwise.2 (Multiset.pairwise_sort _ _))

/-- The parts of a partition, listed in nonincreasing order, are positive. -/
theorem pos_of_mem_sort {d : ℕ} (p : Nat.Partition d) {x : ℕ} (hx : x ∈ p.parts.sort (· ≥ ·)) :
    0 < x :=
  p.parts_pos (by rwa [← Multiset.mem_sort (r := (· ≥ ·))])

/-- **The rows of `D_λ` are the parts of `λ`**: the `i`-th row has `λ_i` cells, and none past the
length of `λ`. -/
@[hjo "def_sf_partition_diagram"]
theorem rowLen_partitionDiagram {d : ℕ} (p : Nat.Partition d) (i : ℕ) :
    (partitionDiagram p).rowLen i = (p.parts.sort (· ≥ ·)).getD i 0 := by
  rw [partitionDiagram]
  by_cases hi : i < (p.parts.sort (· ≥ ·)).length
  · rw [YoungDiagram.rowLen_ofRowLens ⟨i, hi⟩, List.getD_eq_getElem _ 0 hi]
    rfl
  · rw [List.getD_eq_default _ 0 (by omega)]
    refine YoungDiagram.rowLen_eq_zero_of_colLen_le ?_
    rw [← YoungDiagram.length_rowLens,
      YoungDiagram.rowLens_ofRowLens_eq_self fun _ hx => pos_of_mem_sort p hx]
    omega

/-- **`(i,j)` is a cell of `D_λ` exactly when `j < λ_i`**, which is the `1`-based condition `i ≤ m`
and `j ≤ λ_i` read `0`-based: `λ_i` is zero past the length of `λ`, so the first condition is
carried by the second. -/
@[hjo "def_sf_partition_diagram"]
theorem mem_partitionDiagram_iff {d : ℕ} (p : Nat.Partition d) (i j : ℕ) :
    (i, j) ∈ partitionDiagram p ↔ j < (p.parts.sort (· ≥ ·)).getD i 0 := by
  rw [YoungDiagram.mem_iff_lt_rowLen, rowLen_partitionDiagram]

/-- **`HJO.Sym.card_partitionDiagram`: `D_λ` has `d` cells** when `λ` is a partition of `d`. The
rows are the parts, and the parts sum to `d`. -/
@[hjo "lem_sf_partition_diagram_shape"]
theorem card_partitionDiagram {d : ℕ} (p : Nat.Partition d) : (partitionDiagram p).card = d := by
  have hlen : (partitionDiagram p).colLen 0 = (p.parts.sort (· ≥ ·)).length := by
    rw [← YoungDiagram.length_rowLens, partitionDiagram,
      YoungDiagram.rowLens_ofRowLens_eq_self fun _ hx => pos_of_mem_sort p hx]
  rw [(partitionDiagram p).card_eq_sum_rowLen (N := (p.parts.sort (· ≥ ·)).length) hlen.le,
    sum_congr rfl fun i _ => rowLen_partitionDiagram p i,
    ← List.sum_take_eq_sum_range_getD, List.take_of_length_le le_rfl, ← Multiset.sum_coe,
    Multiset.sort_eq, p.parts_sum]

/-! ### The Kostka numbers -/

/-- **The tableaux of a given content are finite**, the clause `HJO.Sym.finite_ssyt_wt_eq` attaches
to its count: a tableau of content `α` takes its values among the finitely many `a` with `α_a > 0`,
and its shape has finitely many cells, so it is one of finitely many functions on the cells. -/
@[hjo "def_sf_kostka"]
theorem finite_ssyt_wt_eq (μ : YoungDiagram) (α : ℕ →₀ ℕ) :
    {T : SemistandardYoungTableau μ | T.wt = α}.Finite := by
  rw [← Set.finite_coe_iff]
  have hb : ∀ T ∈ {T : SemistandardYoungTableau μ | T.wt = α}, ∀ c ∈ μ.cells,
      T c.1 c.2 < α.support.sup id + 1 := by
    rintro T hT c hc
    have hne : α (T c.1 c.2) ≠ 0 := by
      rw [← hT, SemistandardYoungTableau.wt_apply, ← Nat.pos_iff_ne_zero,
        SemistandardYoungTableau.content, card_pos]
      exact ⟨c, mem_filter.2 ⟨hc, rfl⟩⟩
    exact Nat.lt_succ_of_le (le_sup (f := id) (Finsupp.mem_support_iff.2 hne))
  refine Finite.of_injective
    (β := μ.cells → Fin (α.support.sup id + 1))
    (fun T c => ⟨(T : SemistandardYoungTableau μ) c.1.1 c.1.2, hb T T.2 c.1 c.2⟩) ?_
  intro T₁ T₂ h
  refine Subtype.ext (SemistandardYoungTableau.ext fun i j => ?_)
  by_cases hc : (i, j) ∈ μ
  · exact congrArg Fin.val (congrFun h ⟨(i, j), by rwa [YoungDiagram.mem_cells]⟩)
  · rw [(T₁ : SemistandardYoungTableau μ).zeros hc, (T₂ : SemistandardYoungTableau μ).zeros hc]

/-- **The Kostka number `K_D(α)`**, the number of semistandard tableaux
of shape `D` whose content is `α`. Content is the `Finsupp` `SemistandardYoungTableau.wt`, which
`wt_apply` identifies with the content `ct(T)`; a partition is read as such a sequence by the
extension by zeros that a `Finsupp` already is.

It is a `Set.ncard` because `SemistandardYoungTableau μ` carries no `Fintype` instance;
`finite_ssyt_wt_eq` is the finiteness asserted alongside the usual definition. -/
@[hjo "def_sf_kostka"]
noncomputable def kostka (μ : YoungDiagram) (α : ℕ →₀ ℕ) : ℕ :=
  {T : SemistandardYoungTableau μ | T.wt = α}.ncard

end HJO.Sym
