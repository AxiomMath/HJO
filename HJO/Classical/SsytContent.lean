/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.PartitionDominance
public meta import HJO.Attr

/-! # The content of a tableau is bounded by its shape

`HJO.Sym.sum_content_le_partialSum`: for `T ∈ SSYT(D_λ)`,
`ct(T)_1 + ⋯ + ct(T)_i ≤ λ_1 + ⋯ + λ_i`.

## Main statements

* `HJO.Sym.card_filter_entry_lt`, `HJO.Sym.card_filter_row_lt`,
  `HJO.Sym.filter_entry_lt_subset`: the two counts and the inclusion the bound is made of; they are
  named because `HJO.Sym.kostka_partitionExponent` needs them as an *equality* of cell sets, not
  just an inequality of counts.
* `HJO.Sym.sum_content_le_partialSum`.

## Implementation notes

Both sides are cardinalities of sets of cells, and the inequality is an inclusion. The left side
counts the cells whose entry is below `i`, grouped by that entry; the right side counts the cells in
the first `i` rows, grouped by the row. `SemistandardYoungTableau.row_le_entry` says a cell with
entry below `i` lies in a row below `i`, which is the inclusion. No geometry and no arithmetic with
the parts is needed.

The right-hand side is stated as `HJO.Sym.partialSum`, the `λ_1 + ⋯ + λ_i` with the
extension by zeros past the length built in; `HJO.Sym.partialSum_eq_sum_rowLen` is what turns it
into the row count.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-- **The cells with entry below `i`, counted by their entry.** -/
theorem card_filter_entry_lt {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (i : ℕ) :
    #{c ∈ μ.cells | T c.1 c.2 < i} = ∑ a ∈ range i, SemistandardYoungTableau.content T a := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun c : ℕ × ℕ => T c.1 c.2) (t := range i)
    fun c hc => by
      rw [Finset.mem_coe, mem_filter] at hc
      exact Finset.mem_coe.2 (mem_range.2 hc.2)]
  refine sum_congr rfl fun a ha => ?_
  rw [SemistandardYoungTableau.content]
  refine congrArg Finset.card ?_
  ext c
  simp only [mem_filter, mem_range] at ha ⊢
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by rw [h.2]; exact ha⟩, h.2⟩⟩

/-- **The cells in the first `i` rows, counted by their row.** -/
theorem card_filter_row_lt (μ : YoungDiagram) (i : ℕ) :
    #{c ∈ μ.cells | c.1 < i} = ∑ r ∈ range i, μ.rowLen r := by
  classical
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := range i) fun c hc => by
    rw [Finset.mem_coe, mem_filter] at hc
    exact Finset.mem_coe.2 (mem_range.2 hc.2)]
  refine sum_congr rfl fun r hr => ?_
  rw [YoungDiagram.rowLen_eq_card]
  refine congrArg Finset.card ?_
  ext c
  simp only [mem_filter, YoungDiagram.mem_row_iff, YoungDiagram.mem_cells, mem_range] at hr ⊢
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by rw [h.2]; exact hr⟩, h.2⟩⟩

/-- **A cell with entry below `i` lies in a row below `i`**, which is
`SemistandardYoungTableau.row_le_entry` read as an inclusion of cell sets. -/
theorem filter_entry_lt_subset {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (i : ℕ) :
    {c ∈ μ.cells | T c.1 c.2 < i} ⊆ {c ∈ μ.cells | c.1 < i} := by
  classical
  rintro ⟨x, y⟩ hc
  rw [mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_le_of_lt (T.row_le_entry ((YoungDiagram.mem_cells _).1 hc.1)) hc.2⟩

/-- **The content of a tableau is bounded by its shape.** The cells of
`D_λ` whose entry is below `i` all lie in the first `i` rows, by
`SemistandardYoungTableau.row_le_entry`; counting the former by their entry gives
`ct(T)_1 + ⋯ + ct(T)_i` and the latter by their row gives `λ_1 + ⋯ + λ_i`. -/
@[hjo "lem_sf_ssyt_content_bound"]
theorem sum_content_le_partialSum {d : ℕ} (p : Nat.Partition d)
    (T : SemistandardYoungTableau (partitionDiagram p)) (i : ℕ) :
    ∑ a ∈ range i, SemistandardYoungTableau.content T a ≤ partialSum p i := by
  classical
  rw [← card_filter_entry_lt, partialSum_eq_sum_rowLen, ← card_filter_row_lt]
  exact card_le_card (filter_entry_lt_subset T i)

end HJO.Sym
