/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PartialPaths
public import HJO.DyckAttackSets
public meta import HJO.Attr

/-! # Flipping a set of corners of a Dyck path

`HJO.Dyck.flipCorners` lowers the entry of a coarea sequence at each position whose corner cell
lies in a prescribed set `S`. Two facts make that operation usable, and they are the content of
this file: for `S ⊆ c(π)` the flipped sequence is again a square Dyck path, and its attack set is
the attack set of `π` with the cells of `S` adjoined, disjointly.

Both are row-by-row statements. The attack set of a sequence is the disjoint union over the rows
`k` of the intervals `{x k, …, k - 1}`; a corner of row `k` is the cell `(x k - 1, k)`, which sits
immediately to the *left* of that interval, so lowering the entry at `k` extends the interval by
exactly one cell at its left end and changes no other row. That is why the union is disjoint: the
adjoined cell was not there before.

The hypothesis `S ⊆ c(π)` is what makes the flip legitimate. It is used twice, and for different
reasons. For the path property it supplies, at each flipped position `k`, that `k` is a *corner
position* — `x_{k-1} < x_k` — which is what keeps the lowered entry weakly above the entry below
it; without it the flip of a path need not be monotone. For the attack set it supplies that each
cell of `S` is the corner cell of its own row, so that it is precisely the cell the lowered entry
adjoins, and that it is not already an attacking cell.

## Main results

* `HJO.Dyck.IsSquareDyck.flipCorners`: `π_S` is a square Dyck path of length `n`.
* `HJO.Dyck.attackSet_flipCorners`: `At(π_S) = At(π) ∪ S`.
* `HJO.Dyck.disjoint_attackSet_of_subset_corner`: that union is disjoint.

## Implementation notes

The disjointness is stated separately, as `Disjoint (attackSet x) S`, rather than folded into the
union: it needs only `S ⊆ c(π)` and not the flip at all, and every consumer of the
inclusion--exclusion identity uses it to turn the count `inv(At(π_S), w)` into the sum
`inv(At(π), w) + #(S ∩ D(w))`, where the two summands come from the two halves of a disjoint union.

Neither statement assumes `S ⊆ c(π)` in the form `S ⊆ corner x` where it could be avoided:
`attackSet_flipCorners` genuinely needs it, since an arbitrary `S` contributes cells to
`attackSet (flipCorners x S)` only through the positions it flips and contributes none of its own.
At `S = {(5, 5)}` and the staircase path of length `3`, for instance, no entry moves and the right
side would acquire a cell outside the square.

## References

Lemmas `HJO.Dyck.IsSquareDyck.flipCorners` and `HJO.Dyck.attackSet_flipCorners`, using
`HJO.Dyck.IsSquareDyck`, `HJO.Dyck.attackSet`, `HJO.Dyck.corner` and `HJO.Dyck.flipCorners`.
Transcribing E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §3.1, where `π_S` is
the path obtained from `π` by flipping the corners in `S` and the displayed identity
`Area(π_S) = Area(π) ⊔ S` is the step preceding the paper's equation (3.7). Consumed by
`HJO.Dyck.pathMarkedCharSeries_inclusion_exclusion` and, through it, by
`HJO.Mellit.map_constantCoeff_markedWordOp'`.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

variable {n : ℕ} {x : Fin n → ℕ} {S : Finset (ℕ × ℕ)}

/-- A flipped position of a set of corners is a corner position: if the corner cell `(x k - 1, k)`
of the position `k` lies in `S ⊆ c(π)`, then `k` is one of the positions `c(π)` is built from, so
`x_{k-1} < x_k`. This is the one consequence of `S ⊆ c(π)` that the path property needs. -/
theorem isCornerIndex_of_mem_of_subset_corner (hS : S ⊆ corner x) {k : Fin n}
    (hk : (x k - 1, (k : ℕ)) ∈ S) : IsCornerIndex x k := by
  obtain ⟨l, hl, hlk⟩ := mem_corner.1 (hS hk)
  obtain rfl : l = k := Fin.ext (Prod.mk.injEq .. ▸ hlk).2.symm
  exact hl

/-- **A flip is a Dyck path.** For a square Dyck path `π` of length `n` and a set `S ⊆ c(π)` of its
corners, the flipped sequence `π_S` is again a square Dyck path of length `n`.

The bound `x'_k ≤ k` is inherited from `π` because a flip never raises an entry. Monotonicity is
the point: at a position `k` whose corner is flipped, `k` is a corner position by
`HJO.Dyck.isCornerIndex_of_mem_of_subset_corner`, so the entry below `k` is already strictly
smaller than `x_k`, hence at most the lowered entry `x_k - 1`. -/
@[hjo "lem_cm_flip_path"]
theorem IsSquareDyck.flipCorners (h : IsSquareDyck n x) (hS : S ⊆ corner x) :
    IsSquareDyck n (flipCorners x S) where
  mono := by
    intro j k hjk
    rcases hjk.lt_or_eq with hlt | rfl
    swap
    · exact le_rfl
    by_cases hk : (x k - 1, (k : ℕ)) ∈ S
    · rw [HJO.Dyck.flipCorners_of_mem hk]
      refine (HJO.Dyck.flipCorners_le x S j).trans ?_
      obtain ⟨l, hl, hlk⟩ := isCornerIndex_of_mem_of_subset_corner hS hk
      have hjl : j ≤ l := by
        refine Fin.le_def.2 ?_
        have : (j : ℕ) < (k : ℕ) := hlt
        omega
      have := h.mono hjl
      omega
    · rw [HJO.Dyck.flipCorners_of_notMem hk]
      exact (HJO.Dyck.flipCorners_le x S j).trans (h.mono hjk)
  le_index k := (HJO.Dyck.flipCorners_le x S k).trans (h.le_index k)

/-- A set of corners of a square Dyck path meets its attack set in nothing: a corner cell
`(x k - 1, k)` has first coordinate strictly below `x k`, while row `k` of the attack set starts at
`x k`. This is the disjointness of the union `At(π_S) = At(π) ∪ S`. -/
theorem disjoint_attackSet_of_subset_corner (hS : S ⊆ corner x) : Disjoint (attackSet x) S := by
  refine Finset.disjoint_left.2 fun c hc hcS => ?_
  obtain ⟨hlt, hle, -⟩ := mem_attackSet.1 (show (c.1, c.2) ∈ attackSet x from hc)
  exact absurd (fst_lt_of_mem_corner (hS hcS) hlt) hle.not_gt

/-- **A flip adds exactly the flipped cells**: `At(π_S) = At(π) ∪ S` for every square Dyck path `π`
and every `S ⊆ c(π)`; the union is disjoint by
`HJO.Dyck.disjoint_attackSet_of_subset_corner`.

Row by row: at a position `k` whose corner is not flipped the two sequences agree, so the rows
agree; at a flipped position the entry drops from `x k` to `x k - 1`, so row `k` of the left side is
row `k` of the right with the single cell `(x k - 1, k)` — the corner of that row, and the only cell
`S` has there — adjoined. -/
@[hjo "lem_cm_flip_attack"]
theorem attackSet_flipCorners (h : IsSquareDyck n x) (hS : S ⊆ corner x) :
    attackSet (flipCorners x S) = attackSet x ∪ S := by
  ext ⟨i, j⟩
  simp only [Finset.mem_union, mem_attackSet]
  constructor
  · rintro ⟨hj, hle, hij⟩
    by_cases hk : (x ⟨j, hj⟩ - 1, j) ∈ S
    · rw [HJO.Dyck.flipCorners_of_mem hk] at hle
      rcases Nat.lt_or_ge i (x ⟨j, hj⟩) with hlt | hge
      · refine Or.inr ?_
        obtain rfl : i = x ⟨j, hj⟩ - 1 := by omega
        exact hk
      · exact Or.inl ⟨hj, hge, hij⟩
    · rw [HJO.Dyck.flipCorners_of_notMem hk] at hle
      exact Or.inl ⟨hj, hle, hij⟩
  · rintro (⟨hj, hle, hij⟩ | hmem)
    · exact ⟨hj, (HJO.Dyck.flipCorners_le x S ⟨j, hj⟩).trans hle, hij⟩
    · obtain ⟨k, hk, hkc⟩ := mem_corner.1 (hS hmem)
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hkc
      refine ⟨k.isLt, ?_, ?_⟩
      · rw [Fin.eta, HJO.Dyck.flipCorners_of_mem hmem]
      · have := h.le_index k
        have := hk.pos_apply
        omega

end HJO.Dyck
