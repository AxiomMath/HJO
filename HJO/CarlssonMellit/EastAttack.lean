/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PartialPaths
public import HJO.DyckAttackSets
public meta import HJO.Attr

/-! # The attack set after prepending an east step

Prepending an east step to a partial Dyck path of level `k` carries `𝔻_{k,n}` into `𝔻_{k+1,n+1}`
(`HJO.Dyck.isPartialDyck_prependEast`); this file records what the move does to the attack set. The
new path carries the `k + 1` virtual north steps of its level at the left edge, so its first `k + 1`
rows are full: every cell between the diagonal and those rows lies under `E_kπ`, and together they
contribute the whole window `{(i, j) : i < j ≤ k}` in which an attack set of a path of length
`k + 1` lies. Above the level nothing else happens — the path is the translate of `π` by `(1, 1)` —
so a cell of `At(π)` becomes the cell `(i + 1, j + 1)`. Hence

`At(E_kπ) = {(i, j) : i < j ≤ k} ∪ {(i + 1, j + 1) : (i, j) ∈ At(π)}`.

That union overlaps: a cell of a row `j < k` of `At(π)` has `i < j`, so its shift `(i + 1, j + 1)`
has `i + 1 < j + 1 ≤ k` and lies in the window already. The strict `j < k` is the point — row `k`
of `At(π)` lies in the window too, while its shift does not. Cutting the shifted part down to the
rows `j ≥ k` therefore removes exactly the overlap and leaves a *disjoint* decomposition,

`At(E_kπ) = {(i, j) : i < j ≤ k} ⊔ {(i + 1, j + 1) : (i, j) ∈ At(π), j ≥ k}`,

and disjointness is visible on the second coordinate alone: a pair of the window has `j ≤ k`, a
shifted pair has `j ≥ k + 1`, so the two parts sit on opposite sides of the new level.

Both halves of the disjoint form are used, and by different consumers. The labelling bijection of
`HJO.Dyck.EastLabelling` checks the paper's no-attack condition on the two parts separately — on
the window the prepended labels `k, 0, 1, …, k - 1` are pairwise distinct whatever the pattern
there is, on the shifted part distinctness is inherited from `π` — and so needs the two parts to
*cover* `At(E_kπ)`; `HJO.Dyck.invNumber_prependEast_prependLabel` splits the inversion count over
the two parts, `k` over the window and `inv(At(π), w)` over the shifted part, and a sum splits
along a union only when the union is disjoint.

## Main results

* `HJO.Dyck.mem_attackSet_prependEast_iff`: the cells of `At(E_kπ)`, pointwise.
* `HJO.Dyck.attackSet_prependEast`: the attack set of `E_kπ` as the window of the new level
  together with the translate of the whole of `At(π)`.
* `HJO.Dyck.attackSet_prependEast_disjoint_union`: the same as a *disjoint* union, the translate
  cut down to the rows at or above the level.

## Implementation notes

Rows and columns are indexed from `0`, as in `HJO.Dyck.attackSet` and `HJO.Dyck.prependEast`, so
the paper's cell `(i, j)` is `(i - 1, j - 1)`. The `{(i, j) : 1 ≤ i < j ≤ k+1}` is
therefore the pairs `i < j` drawn from `{0, …, k}`, written here as the window
`{p ∈ range (k + 1) ×ˢ range (k + 1) | p.1 < p.2}` in which every transitive attack set on a path
of length `k + 1` lies — it is `attackSet (0 : Fin (k + 1) → ℕ)` by `HJO.Dyck.attackSet_zero`, the
largest such set, and `E_k` does send the one path of `𝔻_{k,k}` to that zero path
(`HJO.Dyck.prependEast_self`). The `j ≥ k+1` on a row of `At(π)` becomes `k ≤ p.2`, and
the translation `(i, j) ↦ (i + 1, j + 1)` is untouched by the reindexing, both coordinates dropping
by one on each side of it. The cut is taken on the row of the cell *in* `At(π)`, before the shift;
the same set arises by cutting the shifted part at `k + 1 ≤ p.2`, but the
pre-shift form is the one whose rows are rows of `π`, which is what a consumer transporting a
property of `π` across the shift has in hand.

"Is the disjoint union of" is two facts about one pair of sets and both are consumed, so the
statement is their conjunction: the equality first, the disjointness second. An equality with
`Finset.disjUnion` would carry the disjointness as a proof term inside the statement rather than as
something the statement asserts, and the equality alone would be a weaker
statement.

The translate is a `Finset.image` rather than a `Finset.map` along an embedding: it is the
set-builder of the displayed formula, and being injective it loses nothing — `Finset.mem_image`
reads a shifted cell back off it and `Finset.card_image_of_injective` counts the shifted part.

Hypotheses are weakened to what is spent. Of the `π ∈ 𝔻_{k,n}` only `k ≤ n` is carried:
`attackSet` is defined for every sequence, the two clauses of `prependEast` determine every entry
of `E_kπ` without reference to the Dyck conditions, and no clause of `IsPartialDyck` enters
anywhere — so the appeal to `HJO.Dyck.isPartialDyck_prependEast`, needed there only to say that `At`
may be applied to `E_kπ` at all, is not needed here, nor is its appeal to
`HJO.Dyck.mem_attackSet_of_lt_level` for the rows below the level, whose spent half
`(i, j) ∈ At(π) → i < j` is `HJO.Dyck.fst_lt_snd_of_mem_attackSet` for an arbitrary sequence. A
consumer holding `IsPartialDyck k n x` applies these through `h.le_length`.

The remaining `k ≤ n` is used, and used by the equalities rather than by the disjointness: for
`n < k` the cell `(n, k)` lies in the window, being a pair `n < k` drawn from `{0, …, k}`, while
every cell of an attack set of a path of length `n + 1` has its row below `n + 1`
(`HJO.Dyck.snd_lt_of_mem_attackSet`), so no choice of `x` puts that cell on the left; at `n = 0`,
`k = 1` the left side is empty while the right side is the window `{(0, 1)}`. The disjointness
conjunct holds for every `k`, `n` and `x` regardless, the two parts being separated by the level on
the second coordinate. Taken over `min k n + 1` instead of `k + 1` the identities hold with no
hypothesis at all — above the length the prepended path is the zero path, whose attack set is the
whole window of `{0, …, n}` — but that is not the stated form, `k ≤ n` being the standing hypothesis
of the paper's recursion, past which `E_k` collapses every path to the zero path and is no longer
the paper's raising operator.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, arXiv:1508.06239v3, J. Amer. Math.
Soc. **31** (2018) 661--697: Section 2.2 for `Area(π)`, the coarea sequence and `a_j + x_j = j`;
for the attack relation, `i` and `j` attack when `i < j` and `(i, j) ∈ Area(π)`; Section 4
for `𝔻_{k,n}`, the paths from `(0, k)` to `(n, n)`, whose union over `k` "is closed under the
operation of adding a North or East step to the beginning of the path"; Section 4.2 for `U_{π,σ}`
and its no-attack condition; and Section 4.3 ("Raising operator"), where `π ∈ 𝔻_{k,n}` gives
`Eπ ∈ 𝔻_{k+1,n+1}` and where the attack pattern of the first row of `Eπ` is what makes the
bijection `f : U_{π,Id_k} → U_{Eπ,σ}` with `σ = (k+1, 1, …, k)` well defined.
The decomposition of `At(Eπ)` is the bookkeeping for that
step rather than a display of the paper's: lemmas `HJO.Dyck.attackSet_prependEast` and
`HJO.Dyck.attackSet_prependEast_disjoint_union`, against `HJO.Dyck.attackSet`,
`HJO.Dyck.IsPartialDyck` and `HJO.Dyck.prependEast`, consumed by
`HJO.Dyck.bijOn_prependLabel_noAttackLabellings` and `HJO.Dyck.invNumber_prependEast_prependLabel`
and so by `HJO.Dyck.partialCharSeries_prependEast` transitively.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

/-- The cells of `At(E_kπ)`: a cell of the prepended path lies either in the window
`{(a, b) : a < b ≤ k}` of the new level, whose rows are full because they carry its `k + 1` virtual
north steps, or is the translate by `(1, 1)` of a cell of `At(π)` in a row at or above the level.
This is the membership form of the disjoint decomposition below, read off the definition of the
attack set and the two value lemmas of `E_k`. -/
theorem mem_attackSet_prependEast_iff {k n : ℕ} (x : Fin n → ℕ) (hk : k ≤ n) (a b : ℕ) :
    (a, b) ∈ attackSet (prependEast k x) ↔
      (a < b ∧ b ≤ k) ∨ ∃ i j : ℕ, (i, j) ∈ attackSet x ∧ k ≤ j ∧ a = i + 1 ∧ b = j + 1 := by
  rw [mem_attackSet]
  constructor
  · rintro ⟨hb, hxa, hab⟩
    rcases le_or_gt b k with hbk | hbk
    -- Below the level the entry is minimal, so the cell lies in the window.
    · exact Or.inl ⟨hab, hbk⟩
    -- Above it the entry is `x_{b-1} + 1`, so the cell is the translate of `(a - 1, b - 1)`.
    · rw [prependEast_mk_of_lt x hb hbk] at hxa
      obtain ⟨b, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
      obtain ⟨a, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
      refine Or.inr ⟨a, b, mem_attackSet.2 ⟨by omega, ?_, by omega⟩, by omega, rfl, rfl⟩
      simpa using hxa
  · rintro (⟨hab, hbk⟩ | ⟨i, j, hij, hj, rfl, rfl⟩)
    -- A cell of the window: the entry there is minimal, and the row is one of the path's.
    · exact ⟨by omega, by rw [prependEast_of_le x (by simpa using hbk)]; exact Nat.zero_le _, hab⟩
    -- A translated cell: the entry is `x_j + 1`, and `x_j ≤ i < j` translates.
    · obtain ⟨hjn, hxi, hijlt⟩ := mem_attackSet.1 hij
      refine ⟨by omega, ?_, by omega⟩
      rw [prependEast_mk_of_lt x (by omega) (by omega)]
      simpa using hxi

/-- The attack set of `E_kπ`, the path got by prepending an east step to a partial Dyck path of
level `k`: the whole window `{(i, j) : i < j ≤ k}` of the new level, whose rows are full because
they carry the `k + 1` virtual north steps, together with the translate by `(1, 1)` of the attack
set of `π`. This is the identity
`At(E_kπ) = {(i,j) : 1 ≤ i < j ≤ k+1} ∪ {(i+1,j+1) : (i,j) ∈ At(π)}` with rows and columns indexed
from `0`, and with the `π ∈ 𝔻_{k,n}` weakened to the one part of it that is used,
`k ≤ n`; a consumer holding `IsPartialDyck k n x` applies it through `h.le_length`. The union is
not disjoint — the shifted cells of the rows of `At(π)` below the level land inside the window —
and `attackSet_prependEast_disjoint_union` is the disjoint form. -/
@[hjo "lem_cm_east_attack"]
theorem attackSet_prependEast {k n : ℕ} (x : Fin n → ℕ) (hk : k ≤ n) :
    attackSet (prependEast k x) =
      {p ∈ range (k + 1) ×ˢ range (k + 1) | p.1 < p.2} ∪
        (attackSet x).image fun p => (p.1 + 1, p.2 + 1) := by
  ext ⟨a, b⟩
  rw [mem_attackSet_prependEast_iff x hk]
  simp only [mem_union, mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro (⟨hab, hbk⟩ | ⟨i, j, hij, -, rfl, rfl⟩)
    · exact Or.inl ⟨⟨by omega, by omega⟩, hab⟩
    · exact Or.inr ⟨i, j, hij, rfl, rfl⟩
  · rintro (⟨⟨-, hb⟩, hab⟩ | ⟨i, j, hij, rfl, rfl⟩)
    · exact Or.inl ⟨hab, by omega⟩
    -- The shifts of the rows below the level land inside the window.
    · rcases le_or_gt k j with hj | hj
      · exact Or.inr ⟨i, j, hij, hj, rfl, rfl⟩
      · exact Or.inl ⟨by have := fst_lt_snd_of_mem_attackSet hij; omega, by omega⟩

/-- The attack set of `E_kπ`, the path got by prepending an east step to a partial Dyck path of
level `k`, is the disjoint union of the window `{(i, j) : i < j ≤ k}` of the new level, whose rows
are full because they carry its `k + 1` virtual north steps, and the translate by `(1, 1)` of the
part of `At(π)` lying in the rows at or above the level. This is the identity
`At(E_kπ) = {(i,j) : 1 ≤ i < j ≤ k+1} ⊔ {(i+1,j+1) : (i,j) ∈ At(π), j ≥ k+1}` with rows and
columns indexed from `0`, and with the `π ∈ 𝔻_{k,n}` weakened to the one part of it
that is used, `k ≤ n`; a consumer holding `IsPartialDyck k n x` applies it through `h.le_length`.
Cutting the translate at the level is what makes the union disjoint: without the cut the shifts of
the rows below the level fall inside the window, which is `attackSet_prependEast`. -/
@[hjo "lem_cm_east_attack_overlap"]
theorem attackSet_prependEast_disjoint_union {k n : ℕ} (x : Fin n → ℕ) (hk : k ≤ n) :
    attackSet (prependEast k x) =
        {p ∈ range (k + 1) ×ˢ range (k + 1) | p.1 < p.2} ∪
          ({p ∈ attackSet x | k ≤ p.2}).image (fun p => (p.1 + 1, p.2 + 1)) ∧
      Disjoint ({p ∈ range (k + 1) ×ˢ range (k + 1) | p.1 < p.2} : Finset (ℕ × ℕ))
        (({p ∈ attackSet x | k ≤ p.2}).image (fun p => (p.1 + 1, p.2 + 1))) := by
  refine ⟨?_, ?_⟩
  · ext ⟨a, b⟩
    rw [mem_attackSet_prependEast_iff x hk]
    simp only [mem_union, mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq,
      Prod.exists]
    constructor
    · rintro (⟨hab, hbk⟩ | ⟨i, j, hij, hj, rfl, rfl⟩)
      · exact Or.inl ⟨⟨by omega, by omega⟩, hab⟩
      · exact Or.inr ⟨i, j, ⟨hij, hj⟩, rfl, rfl⟩
    · rintro (⟨⟨-, hb⟩, hab⟩ | ⟨i, j, ⟨hij, hj⟩, rfl, rfl⟩)
      · exact Or.inl ⟨hab, by omega⟩
      · exact Or.inr ⟨i, j, hij, hj, rfl, rfl⟩
  -- The two parts are separated by the level on the second coordinate.
  · refine Finset.disjoint_left.2 ?_
    rintro ⟨a, b⟩ hw hs
    simp only [mem_filter, mem_product, mem_range] at hw
    simp only [mem_image, mem_filter, Prod.mk.injEq, Prod.exists] at hs
    obtain ⟨i, j, ⟨-, hj⟩, -, rfl⟩ := hs
    omega

end HJO.Dyck
