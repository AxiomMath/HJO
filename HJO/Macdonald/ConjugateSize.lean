/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.Vocabulary
public meta import HJO.Attr

/-! # Conjugation preserves the size of a diagram, and therefore covering

`HJO.Sym.card_transpose`: `|μ'| = |μ|`.

## Why this file exists

`HJO.Sym.card_transpose` is not in Mathlib: **there is no `YoungDiagram.card_transpose` in the
Mathlib this library is pinned to.** `Mathlib/Combinatorics/Young/YoungDiagram.lean` at the pinned
revision proves `transpose_transpose`, `transpose_eq_iff`, `transpose_le_iff`, `transpose_mono`,
`le_of_transpose_le`, `mem_transpose`, `rowLen_transpose` and `colLen_transpose` -- and no statement
about `card` at all. So the library has the shape of the fact (conjugation is an involutive order
isomorphism of diagrams) but not the fact.

The proof is three lines: `c ∈ μ'` iff `c.swap ∈ μ` (`YoungDiagram.mem_transpose`), so the cells of
`μ'` are the image of the cells of `μ` under the swap, and the swap is injective.

That conjugation is monotone and involutive is genuinely present, as
`YoungDiagram.transpose_mono` and `YoungDiagram.transpose_transpose`; only the size statement is
missing.

## The companion

`HJO.Sym.covers_transpose_iff` puts the two together: `μ' ⋗ ν'` iff `μ ⋗ ν`. That is the last step
of `HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short`, which derives `ν' ⊆ λ'` and has
to come back to `ν ⊆ λ` with the sizes intact, and it is the only form in which either fact is used
there.

## The row lengths as coordinates

Every proof in the Pieri block argues about containment through the row lengths -- "every cell
`(i,j)` of `ρ`, having `j ≤ ρ_i ≤ λ'_i`, is a cell of `λ'`" -- and reads the length of a partition
as the first entry of its conjugate. Mathlib has `mem_iff_lt_rowLen`, `mem_iff_lt_colLen`,
`rowLen_anti` and `rowLen_transpose`, but not the four statements those arguments actually quote, so
they are here: `le_iff_rowLen_le`, `lt_colLen_zero_iff_rowLen_ne_zero`, `rowLen_colLen_zero` and
`colLen_zero_le_card`. Together they say that `μ.colLen 0` IS the length `l` of `μ`, the number of
indices `i` with `μ_i ≥ 1`: the rows below it are nonempty, the row at it is empty, and it is at
most `|μ|`.

## Main results

* `HJO.Sym.card_transpose`.
* `HJO.Sym.covers_transpose_iff`: covering is invariant under conjugation.
* `HJO.Sym.le_iff_rowLen_le`: containment of diagrams is the entrywise comparison of row lengths.
* `HJO.Sym.lt_colLen_zero_iff_rowLen_ne_zero`, `HJO.Sym.rowLen_colLen_zero`,
  `HJO.Sym.colLen_zero_le_card`: `μ.colLen 0` is the number of nonempty rows.

## References

This file proves `HJO.Sym.card_transpose`, about `HJO.Sym.cells`,
`HJO.Sym.rowLen_transpose_eq_natCard` and `HJO.Sym.Covers`.
-/

@[expose] public section

namespace HJO.Sym

/-- **Conjugation preserves the size of a diagram**, `|μ'| = |μ|`.

`c ∈ μ'` iff `c.swap ∈ μ` (`YoungDiagram.mem_transpose`), so the cells of `μ'` are the image of
those of `μ` under `Prod.swap`, which is injective.

Not available from Mathlib at the pinned revision: see the module docstring. -/
@[hjo "lem_dua_conjugate_size"]
theorem card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  classical
  have h : μ.transpose.cells = μ.cells.image Prod.swap := by
    ext c
    simp only [Finset.mem_image]
    constructor
    · intro hc
      exact ⟨c.swap, YoungDiagram.mem_transpose.mp hc, Prod.swap_swap c⟩
    · rintro ⟨d, hd, rfl⟩
      exact YoungDiagram.mem_transpose.mpr (by rwa [Prod.swap_swap])
  rw [YoungDiagram.card, YoungDiagram.card, h,
    Finset.card_image_of_injective _ Prod.swap_injective]

/-- **Containment of diagrams is the entrywise comparison of row lengths**: `μ ⊆ ν` iff
`μ_i ≤ ν_i` for every `i`.

This is the reading of `HJO.Sym.cells` that every containment argument of the Pieri block uses --
"every cell `(i,j)` of `μ`, having `j < μ_i ≤ ν_i`, is a cell of `ν`" -- and the converse direction
is the cell `(i, ν_i)`, which would lie in `μ` and not in `ν` were the inequality to fail.
`YoungDiagram.mem_iff_lt_rowLen` is both halves. -/
theorem le_iff_rowLen_le {μ ν : YoungDiagram} : μ ≤ ν ↔ ∀ i, μ.rowLen i ≤ ν.rowLen i := by
  constructor
  · intro h i
    by_contra hlt
    rw [not_le] at hlt
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp
      (h (YoungDiagram.mem_iff_lt_rowLen.mpr hlt))) (lt_irrefl _)
  · intro h c hc
    rw [YoungDiagram.mem_iff_lt_rowLen] at hc ⊢
    exact lt_of_lt_of_le hc (h c.1)

/-- **`μ.colLen 0` is the number of nonempty rows of `μ`**: row `i` is nonempty exactly when
`i < μ.colLen 0`. This is the length `l`, the number of indices `i` with `ν_i ≥ 1`, and it is
also `μ'_1` (`YoungDiagram.rowLen_transpose`), which is the form
`HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short` reads it in. Both directions are
`(i, 0) ∈ μ`. -/
theorem lt_colLen_zero_iff_rowLen_ne_zero {μ : YoungDiagram} {i : ℕ} :
    i < μ.colLen 0 ↔ μ.rowLen i ≠ 0 := by
  rw [← YoungDiagram.mem_iff_lt_colLen (i := i) (j := 0), YoungDiagram.mem_iff_lt_rowLen,
    Nat.pos_iff_ne_zero]

/-- **The row at the number of nonempty rows is empty**, the statement `ν_{l+1} = 0`. -/
theorem rowLen_colLen_zero (μ : YoungDiagram) : μ.rowLen (μ.colLen 0) = 0 := by
  by_contra h
  exact absurd (lt_colLen_zero_iff_rowLen_ne_zero.mpr h) (lt_irrefl _)

/-- **A diagram has at most `|μ|` nonempty rows**, the bound `l ≤ d`: the first column is a
subset of the cells. -/
theorem colLen_zero_le_card (μ : YoungDiagram) : μ.colLen 0 ≤ μ.card := by
  rw [YoungDiagram.colLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- **Covering is invariant under conjugation**: `μ' ⋗ ν'` iff `μ ⋗ ν`.

`HJO.Sym.Covers` is containment together with one more cell, and conjugation preserves both:
containment by `YoungDiagram.transpose_le_iff` and the size by `HJO.Sym.card_transpose`. -/
theorem covers_transpose_iff {μ ν : YoungDiagram} :
    Covers μ.transpose ν.transpose ↔ Covers μ ν := by
  rw [Covers, Covers, YoungDiagram.transpose_le_iff, card_transpose, card_transpose]

end HJO.Sym
