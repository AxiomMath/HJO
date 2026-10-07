/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.MonomialBasis
public import HJO.Classical.SsytContent
public meta import HJO.Attr

/-! # The Kostka number at the shape itself, and its triangularity

`HJO.Sym.kostka_partitionExponent`: `K_{D_λ}(λ) = 1`. `HJO.Sym.dominates_of_kostka_ne_zero`:
`K_{D_λ}(μ) ≠ 0` forces `λ ⪰ μ`.

## Main statements

* `HJO.Sym.kostka_partitionExponent`.
* `HJO.Sym.dominates_of_kostka_ne_zero`.

## Implementation notes

The triangularity is `HJO.Sym.sum_content_le_partialSum` read off a witnessing tableau: a nonzero
Kostka number produces one, and its content bound *is* the dominance inequality.

The diagonal value needs the witness and its uniqueness. The witness is `Mathlib`'s
`SemistandardYoungTableau.highestWeight`, whose `i`-th row is constant `i`; its content is the row
lengths, which for `D_λ` are the parts of `λ`. Uniqueness is the argument, and the shape
it wants is an *equality* of cell sets rather than the inequality of counts that
`HJO.Sym.sum_content_le_partialSum` records: for a tableau of content `λ` the cells with entry below
`i` and the cells in the first `i` rows are equinumerous, and one contains the other, so they
coincide — at `i = r + 1` that pins the entry in row `r` to `r`. `HJO.Sym.card_filter_entry_lt`,
`HJO.Sym.card_filter_row_lt` and `HJO.Sym.filter_entry_lt_subset` are the three pieces.

`λ` read as a sequence of multiplicities is `HJO.Sym.partitionExponent`, which is the extension by
zeros that the definition of `K_D(α)` prescribes.

## References

This file formalises `HJO.Sym.kostka_partitionExponent` and
`HJO.Sym.dominates_of_kostka_ne_zero`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### Triangularity -/

/-- **The Kostka numbers are triangular for dominance.** A nonzero
`K_{D_λ}(μ)` produces a tableau of shape `D_λ` and content `μ`, and
`HJO.Sym.sum_content_le_partialSum` turns its content bound into `λ ⪰ μ`. -/
@[hjo "lem_sf_kostka_triangular"]
theorem dominates_of_kostka_ne_zero {d : ℕ} (p q : Nat.Partition d)
    (h : kostka (partitionDiagram p) (partitionExponent q) ≠ 0) : Dominates p q := by
  obtain ⟨T, hT⟩ : {T : SemistandardYoungTableau (partitionDiagram p) |
      T.wt = partitionExponent q}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero h
  intro i
  have h1 : partialSum q i = #{c ∈ (partitionDiagram p).cells | T c.1 c.2 < i} := by
    rw [card_filter_entry_lt, partialSum, List.sum_take_eq_sum_range_getD]
    exact sum_congr rfl fun a _ => by
      rw [← partitionExponent_apply, ← hT, SemistandardYoungTableau.wt_apply]
  have h2 : partialSum p i = #{c ∈ (partitionDiagram p).cells | c.1 < i} := by
    rw [partialSum_eq_sum_rowLen, card_filter_row_lt]
  rw [h1, h2]
  exact card_le_card (filter_entry_lt_subset T i)

/-! ### The diagonal value -/

/-- The content of the highest-weight tableau is the sequence of row lengths: its `i`-th row is
constant `i`, so the value `a` occurs exactly on row `a`. -/
theorem content_highestWeight (μ : YoungDiagram) (a : ℕ) :
    SemistandardYoungTableau.content (SemistandardYoungTableau.highestWeight μ) a
      = μ.rowLen a := by
  classical
  rw [SemistandardYoungTableau.content, YoungDiagram.rowLen_eq_card, YoungDiagram.row]
  refine congrArg Finset.card (Finset.filter_congr fun c hc => ?_)
  rw [YoungDiagram.mem_cells] at hc
  rw [SemistandardYoungTableau.highestWeight_apply,
    ite_eq_left (show (c.1, c.2) ∈ μ by rwa [Prod.mk.eta])]

/-- The highest-weight tableau of `D_λ` has content `λ`. -/
theorem wt_highestWeight_partitionDiagram {d : ℕ} (p : Nat.Partition d) :
    (SemistandardYoungTableau.highestWeight (partitionDiagram p)).wt = partitionExponent p := by
  refine Finsupp.ext fun a => ?_
  rw [SemistandardYoungTableau.wt_apply, content_highestWeight, rowLen_partitionDiagram,
    partitionExponent_apply]

/-- **The highest-weight tableau is the only one of content `λ` on `D_λ`.** Its content forces the
cells with entry below `i` to be exactly the cells in the first `i` rows, for every `i`; at
`i = r + 1` that says every entry of row `r` is at most `r`, and
`SemistandardYoungTableau.row_le_entry` says it is at least `r`. -/
theorem eq_highestWeight_of_wt_eq {d : ℕ} (p : Nat.Partition d)
    {T : SemistandardYoungTableau (partitionDiagram p)} (hT : T.wt = partitionExponent p) :
    T = SemistandardYoungTableau.highestWeight (partitionDiagram p) := by
  classical
  have hcard : ∀ i, #{c ∈ (partitionDiagram p).cells | c.1 < i}
      ≤ #{c ∈ (partitionDiagram p).cells | T c.1 c.2 < i} := by
    intro i
    rw [card_filter_entry_lt, card_filter_row_lt]
    exact le_of_eq (sum_congr rfl fun a _ => by
      rw [rowLen_partitionDiagram, ← partitionExponent_apply, ← hT,
        SemistandardYoungTableau.wt_apply])
  have hset : ∀ i, {c ∈ (partitionDiagram p).cells | T c.1 c.2 < i}
      = {c ∈ (partitionDiagram p).cells | c.1 < i} := fun i =>
    Finset.eq_of_subset_of_card_le (filter_entry_lt_subset T i) (hcard i)
  refine SemistandardYoungTableau.ext fun x y => ?_
  by_cases hc : (x, y) ∈ partitionDiagram p
  · rw [SemistandardYoungTableau.highestWeight_apply, ite_eq_left hc]
    have hle : T x y ≤ x := by
      have hmem : ((x, y) : ℕ × ℕ) ∈ {c ∈ (partitionDiagram p).cells | c.1 < x + 1} :=
        mem_filter.2 ⟨(YoungDiagram.mem_cells _).2 hc, by omega⟩
      rw [← hset (x + 1), mem_filter] at hmem
      exact Nat.lt_succ_iff.1 hmem.2
    have hge : x ≤ T x y := T.row_le_entry hc
    omega
  · rw [T.zeros hc, (SemistandardYoungTableau.highestWeight (partitionDiagram p)).zeros hc]

/-- **The Kostka number at the shape itself is one.** The highest-weight
tableau of `D_λ` has content `λ`, and it is the only one that does. -/
@[hjo "lem_sf_kostka_diagonal"]
theorem kostka_partitionExponent {d : ℕ} (p : Nat.Partition d) :
    kostka (partitionDiagram p) (partitionExponent p) = 1 := by
  rw [kostka, show {T : SemistandardYoungTableau (partitionDiagram p) |
      T.wt = partitionExponent p}
        = {SemistandardYoungTableau.highestWeight (partitionDiagram p)} from
    Set.eq_singleton_iff_unique_mem.2
      ⟨wt_highestWeight_partitionDiagram p, fun T hT => eq_highestWeight_of_wt_eq p hT⟩,
    Set.ncard_singleton]

end HJO.Sym
