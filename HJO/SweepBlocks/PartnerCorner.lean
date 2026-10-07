/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepRankOrder
public import HJO.SweepBlocks.MarkedAttack
public meta import HJO.Attr

/-! # A marked pair is a corner of the square partner

`HJO.Paths.attackPartner_stepIndex_and_mem_corner_of_mem_sweepMarked`: for `(i, j) ∈ S(P̂)` the
entry `x'_j` of the square partner is `i + 1`, and the cell `(i, j)` is a corner of `P̂'`.

Everything follows from one computation of the `j`-th column of the attack set. A marked pair has
`rk̂(u_j) = rk̂(u_i) + ω` exactly (see `stepRank_eq_add_attackWindow_of_mem_sweepMarked`), so
the window clause of `HJO.Paths.sweepAttack` at `(r, j)` reads `rk̂(u_i) + ω < rk̂(u_r) + ω`, i.e.
`rk̂(u_i) < rk̂(u_r)`, that is `i < r` in the rank order. The column is therefore exactly the open
interval of positions strictly between `i` and `j` — `HJO.Paths.mem_attackPositions_column_marked`
— and its minimum, taken together with `{j}` as `HJO.Dyck.attackPartner` does, is `i + 1` whether
the interval is empty (`j = i + 1`) or not.

## Main results

* `HJO.Paths.mem_attackPositions_column_marked`: the column of `𝒜(P̂)` above a marked pair is the
  open interval of positions between the two members of the pair.
* `HJO.Paths.attackPartner_stepIndex_and_mem_corner_of_mem_sweepMarked`:
  `HJO.Paths.attackPartner_stepIndex_and_mem_corner_of_mem_sweepMarked`, both conclusions.

## Implementation notes

**The indexing.** `HJO.Paths.stepIndex` is `0`-based, while the `i`, `j` and `x'_j` are
`1`-based; `HJO.Dyck.attackPartner A k` is the `0`-based reading, for which the `x'_j`
is `attackPartner A (j - 1) + 1` (see the module docstring of `HJO/Shuffle/SweepRankOrder.lean`
and the consistency check in `HJO.Paths.wordPosition_stepFoot`). So the `x'_j = i + 1`
becomes `attackPartner (attackPositions y) k = p + 1` with `p := stepIndex y s` and
`k := stepIndex y t` — **not** `= p + 2`.

Likewise the corner cell `(i, j)` is `HJO.Dyck.corner`'s `(x k - 1, k) = (p, k)`, the
`0`-based coordinates of `HJO.Dyck.corner` being the usual `1`-based coordinates shifted down by
one in both coordinates.

`0 < a` and `0 < N` are not hypotheses: `HJO.Paths.mul_pos_of_isAboveDiagonal` extracts `0 < a * N`
from `IsAboveDiagonal` and the existence of the north step `s`, which is what the positivity of the
window needs.

## References

This file proves `HJO.Paths.attackPartner_stepIndex_and_mem_corner_of_mem_sweepMarked`, using
`HJO.Paths.IsAboveDiagonal`, `HJO.Dyck.corner`, `HJO.Paths.sweepAttack`, `HJO.Paths.sweepMarked` and
`HJO.Dyck.attackPartner`. A. Mellit, *Toric braids and `(m, n)`-parking functions*, section "The
sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-- **The column of the attack set above a marked pair is an interval of positions.** For
`(s, t) ∈ S(P̂)` the position `m` attacks the position of `t` exactly when it lies strictly between
the positions of `s` and of `t`.

The window clause of `HJO.Paths.sweepAttack` at `(r, t)` is `rk̂(u_t) < rk̂(u_r) + ω`, and
`rk̂(u_t) = rk̂(u_s) + ω` turns it into `rk̂(u_s) < rk̂(u_r)`; the rank order is the position order
(`HJO.Paths.stepIndex_lt_stepIndex_iff`), so the two clauses become `p < m` and `m < k`. -/
theorem mem_attackPositions_column_marked {y : Heights a b N} (hy : IsAboveDiagonal y)
    {s t : Fin (b * N)} (h : (s, t) ∈ sweepMarked y) (m : ℕ) :
    (m, (stepIndex y t : ℕ)) ∈ attackPositions y ↔
      (stepIndex y s : ℕ) < m ∧ m < (stepIndex y t : ℕ) := by
  have hrk := stepRank_eq_add_attackWindow_of_mem_sweepMarked h
  constructor
  · intro hmem
    obtain ⟨hm, hn, hatt⟩ := (mem_attackPositions_iff hy).1 hmem
    have ht : stepAt hy ⟨(stepIndex y t : ℕ), hn⟩ = t := by
      rw [show (⟨(stepIndex y t : ℕ), hn⟩ : Fin (b * N)) = stepIndex y t from Fin.val_injective rfl,
        stepAt_stepIndex]
    rw [ht] at hatt
    simp only [sweepAttack, mem_filter, mem_univ, true_and] at hatt
    obtain ⟨h1, h2⟩ := hatt
    refine ⟨?_, ?_⟩
    · have : stepRank y s < stepRank y (stepAt hy ⟨m, hm⟩) := by rw [hrk] at h2; omega
      have hpos := (stepIndex_lt_stepIndex_iff y s (stepAt hy ⟨m, hm⟩)).2 this
      rw [stepIndex_stepAt] at hpos
      exact hpos
    · have hpos := (stepIndex_lt_stepIndex_iff y (stepAt hy ⟨m, hm⟩) t).2 h1
      rw [stepIndex_stepAt] at hpos
      exact hpos
  · rintro ⟨hpm, hmk⟩
    have hm : m < b * N := hmk.trans (stepIndex y t).isLt
    refine (mem_attackPositions_iff hy).2 ⟨hm, (stepIndex y t).isLt, ?_⟩
    have ht : stepAt hy ⟨(stepIndex y t : ℕ), (stepIndex y t).isLt⟩ = t := by
      rw [show (⟨(stepIndex y t : ℕ), (stepIndex y t).isLt⟩ : Fin (b * N)) = stepIndex y t from
        Fin.val_injective rfl, stepAt_stepIndex]
    rw [ht]
    have hsr : stepRank y s < stepRank y (stepAt hy ⟨m, hm⟩) := by
      refine (stepIndex_lt_stepIndex_iff y s (stepAt hy ⟨m, hm⟩)).1 ?_
      rw [stepIndex_stepAt]
      exact hpm
    have hrt : stepRank y (stepAt hy ⟨m, hm⟩) < stepRank y t := by
      refine (stepIndex_lt_stepIndex_iff y (stepAt hy ⟨m, hm⟩) t).1 ?_
      rw [stepIndex_stepAt]
      exact hmk
    simp only [sweepAttack, mem_filter, mem_univ, true_and]
    exact ⟨hrt, by rw [hrk] at hrt ⊢; omega⟩

/-- The position of the lower member of a marked pair is strictly below that of the upper member:
the rank rises by the window along the pair, and the window is positive because the path has a
north step. -/
theorem stepIndex_lt_stepIndex_of_mem_sweepMarked {y : Heights a b N} (hy : IsAboveDiagonal y)
    {s t : Fin (b * N)} (h : (s, t) ∈ sweepMarked y) :
    (stepIndex y s : ℕ) < (stepIndex y t : ℕ) := by
  have hω : (0 : ℤ) < attackWindow a N := by
    exact_mod_cast attackWindow_pos_iff.2 (mul_pos_of_isAboveDiagonal hy s)
  have hrk := stepRank_eq_add_attackWindow_of_mem_sweepMarked h
  exact (stepIndex_lt_stepIndex_iff y s t).2 (by omega)

/-- **A marked pair determines the partner entry, and is a corner of the partner.** This is
`HJO.Paths.attackPartner_stepIndex_and_mem_corner_of_mem_sweepMarked`, in `0`-based coordinates:
with `p` and `k` the rank-order positions of the two members of a marked pair, the square partner
has `x_k = p + 1` and the cell `(p, k)` is a corner of it.

The partner entry is the minimum of the column `{m : p < m < k}` together with `{k}`, and that is
`p + 1` either way: if `k > p + 1` the column has least element `p + 1`, and if `k = p + 1` the
column is empty and the minimum is `k = p + 1`.

For the corner, the position below `k` is `k - 1`, which exists because `p < k`. If `k = p + 1`
then `x_{k-1} = x_p ≤ p < p + 1 = x_k` by `HJO.Dyck.attackPartner_le`; if `k > p + 1` then
`p < k - 1 < k`, so `(p, k-1)` is in the attack set and `x_{k-1} ≤ p < x_k`. -/
@[hjo "lem_sweep_partner_not_corner"]
theorem attackPartner_stepIndex_and_mem_corner_of_mem_sweepMarked {y : Heights a b N}
    (hy : IsAboveDiagonal y) {s t : Fin (b * N)} (h : (s, t) ∈ sweepMarked y) :
    Dyck.attackPartner (attackPositions y) (stepIndex y t) = (stepIndex y s : ℕ) + 1 ∧
      ((stepIndex y s : ℕ), (stepIndex y t : ℕ)) ∈
        Dyck.corner fun k : Fin (b * N) => Dyck.attackPartner (attackPositions y) (k : ℕ) := by
  set p : ℕ := (stepIndex y s : ℕ) with hp
  set k : ℕ := (stepIndex y t : ℕ) with hk
  have hpk : p < k := stepIndex_lt_stepIndex_of_mem_sweepMarked hy h
  have hcol := mem_attackPositions_column_marked hy h
  -- the partner entry at `k` is `p + 1`
  have hkey : Dyck.attackPartner (attackPositions y) k = p + 1 := by
    refine le_antisymm ?_ ?_
    · rcases Nat.lt_or_ge (p + 1) k with hlt | hge
      · exact Nat.sInf_le (Or.inl ((hcol (p + 1)).2 ⟨Nat.lt_succ_self p, hlt⟩))
      · have : p + 1 = k := by omega
        exact Nat.sInf_le (Or.inr this)
    · rcases Dyck.attackPartner_spec (attackPositions y) k with hmem | heq
      · exact (hcol _).1 hmem |>.1
      · omega
  refine ⟨hkey, ?_⟩
  -- the cell `(p, k)` is a corner: the entry at the position below `k` is at most `p`
  have hklt : k < b * N := (stepIndex y t).isLt
  have hk1lt : k - 1 < b * N := by omega
  have hrk := stepRank_eq_add_attackWindow_of_mem_sweepMarked h
  have hpred : Dyck.attackPartner (attackPositions y) (k - 1) ≤ p := by
    rcases Nat.lt_or_ge (p + 1) k with hlt | hge
    · -- `p < k - 1 < k`, so the position `p` attacks the position `k - 1`
      set r : Fin (b * N) := stepAt hy ⟨k - 1, hk1lt⟩ with hr
      have hir : (stepIndex y r : ℕ) = k - 1 := by rw [hr, stepIndex_stepAt]
      have hsr : stepRank y s < stepRank y r :=
        (stepIndex_lt_stepIndex_iff y s r).1 (by rw [← hp] at *; omega)
      have hrt : stepRank y r < stepRank y t :=
        (stepIndex_lt_stepIndex_iff y r t).1 (by rw [← hk] at *; omega)
      have hmem : (p, k - 1) ∈ attackPositions y := by
        rw [← hir, hp]
        refine (mem_attackPositions hy s r).2 ?_
        simp only [sweepAttack, mem_filter, mem_univ, true_and]
        exact ⟨hsr, by rw [hrk] at hrt; omega⟩
      exact Dyck.attackPartner_le_of_mem hmem
    · have hkp : k - 1 = p := by omega
      rw [hkp]
      exact Dyck.attackPartner_le _ _
  refine Dyck.mem_corner.2 ⟨⟨k, hklt⟩, ⟨⟨k - 1, hk1lt⟩, by simp only; omega, ?_⟩, by simp [hkey]⟩
  simp only
  rw [hkey]
  omega

end HJO.Paths
