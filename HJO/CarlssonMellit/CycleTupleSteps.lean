/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.Tuples
public meta import HJO.Attr

/-! # The interpolating tuples as permutations, and the single step between them

The raising recursion of Carlsson and Mellit is read off a chain of `k + 1` tuples
`σ^{(1)}, …, σ^{(k+1)}` — the family `HJO.Dyck.cycleTuple` — running from the identity tuple to the
cyclic shift, and its induction needs exactly three facts about that chain: each member is a listing
of the labels of the level `k + 1` without repetition, so that the characteristic series
`ν_{σ^{(i)}}` is the one the swapping operators act on; the label `i` sits at the first position of
`σ^{(i)}` and the label `i + 1` at the position `i + 1`, so that the transposition `τ_i` may be
applied to it; and one application of `τ_i` passes from `σ^{(i)}` to `σ^{(i+1)}`, which is the step
of the induction. This file proves those three facts from the `Fin.cycleRange` description of the
family.

## Main results

* `HJO.Dyck.cycleTuple_lt_and_injective`: the entries of `σ^{(i)}` are the labels of the level
  `k + 1`, each exactly once; `HJO.Dyck.cycleTuple_existsUnique_eq` is the same statement read
  literally, one label at a time.
* `HJO.Dyck.cycleTuple_castSucc_eq_self_iff` and `HJO.Dyck.cycleTuple_castSucc_eq_succ_iff`: the two
  labels the transposition moves sit at the positions `0` and `i + 1`, and nowhere else; the order
  between those positions is `HJO.Dyck.cycleTuple_castSucc_lt_of_eq`.
* `HJO.Dyck.transposeTuple_cycleTuple_castSucc`: `τ_i(σ^{(i)}) = σ^{(i+1)}`.

## Implementation notes

*Positions and labels are both indexed from `0`*, as in `HJO/CarlssonMellit/Tuples.lean`, so
`HJO.Dyck.cycleTuple i` is the paper's `σ^{(i+1)}`, its label `i` is the paper's `i + 1` and its
position `j` is the paper's `j + 1`. In particular the paper's `{1, …, k+1}` is `{0, …, k}` here,
and the paper's "the position of the entry `i` is `1`" reads "the position of the label `i` is
`0`".

*A listing of the labels of a level without repetition is recorded as the pair of conditions "every
entry is a label" and "the entries are pairwise distinct"*, which is the form
`HJO.Dyck.transposeTuple_lt_and_injective` already uses for the same phrase, and
the form the consumers of `HJO.Dyck.partialCharSeries` carry. For a tuple of `k + 1` entries those
two conditions are equivalent to listing all of `{0, …, k}` each exactly once, and
`HJO.Dyck.cycleTuple_existsUnique_eq` is that equivalence made explicit.

*The paper's range `1 ≤ i ≤ k` for the last two groups of results is carried by the index type*:
the moving label is `i : Fin k`, appearing as the tuple index `i.castSucc` on the left of a step and
`i.succ` on the right, so no side condition is a binder and the paper's `k ≥ 1` comes free, `Fin 0`
being empty. The first group, the `1 ≤ i ≤ k+1`, is stated for every `i : Fin (k + 1)`.

## References

E. Carlsson and A. Mellit, *A
proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 5.
-/

@[expose] public section

namespace HJO.Dyck

variable {k : ℕ}

/-! ### The interpolating tuples are permutations -/

/-- **The interpolating tuples are permutations**: the entries of `σ^{(i)}` are the labels
`0, …, k` of the level `k + 1`, each exactly once. As in
`HJO.Dyck.transposeTuple_lt_and_injective` that is recorded as the pair of conditions "every entry
is a label of the level" and "the entries are pairwise distinct", which for `k + 1` entries taken
from `k + 1` labels is equivalent to listing each of them once; the literal reading is
`HJO.Dyck.cycleTuple_existsUnique_eq`. It is this pair that lets `HJO.Dyck.partialCharSeries` be
read at `σ^{(i)}` as the `ν_{σ^{(i)}}` at the level `k + 1`. -/
@[hjo "lem_cm_sigmaseq_perm"]
theorem cycleTuple_lt_and_injective (i : Fin (k + 1)) :
    (∀ j, cycleTuple i j < k + 1) ∧ Function.Injective (cycleTuple i) :=
  ⟨cycleTuple_lt i, cycleTuple_injective i⟩

/-- Each label of the level `k + 1` occurs at exactly one position of `σ^{(i)}`: the literal
reading of "the entries are the labels `0, …, k`, each exactly once". -/
theorem cycleTuple_existsUnique_eq (i : Fin (k + 1)) {a : ℕ} (ha : a < k + 1) :
    ∃! j : Fin (k + 1), cycleTuple i j = a := by
  refine ⟨i.cycleRange ⟨a, ha⟩, ?_, fun j hj => cycleTuple_injective i (hj.trans ?_)⟩
  · simp [cycleTuple]
  · simp [cycleTuple]

/-! ### The positions of the two labels a transposition moves -/

/-- **The first entry of `σ^{(i)}` is the label `i`, and no other entry is**: the position of the
label `i` in `σ^{(i)}` is `0`, the paper's position `1`. -/
@[hjo "lem_cm_sigmaseq_order"]
theorem cycleTuple_castSucc_eq_self_iff (i : Fin k) (j : Fin (k + 1)) :
    cycleTuple i.castSucc j = (i : ℕ) ↔ j = 0 := by
  refine ⟨fun h => cycleTuple_injective i.castSucc ?_, fun h => by subst h; simp⟩
  rw [h, cycleTuple_zero, Fin.val_castSucc]

/-- **The entry at the position `i + 1` of `σ^{(i)}` is the label `i + 1`, and no other entry
is**: the position of the label `i + 1` in `σ^{(i)}` is `i + 1`, which is the paper's position
`i + 1` shifted, the paper's label `i + 2` being the label `i + 1` here. -/
@[hjo "lem_cm_sigmaseq_order"]
theorem cycleTuple_castSucc_eq_succ_iff (i : Fin k) (j : Fin (k + 1)) :
    cycleTuple i.castSucc j = (i : ℕ) + 1 ↔ j = i.succ := by
  have hi : cycleTuple i.castSucc i.succ = (i : ℕ) + 1 := by
    rw [cycleTuple_of_lt Fin.castSucc_lt_succ, Fin.val_succ]
  exact ⟨fun h => cycleTuple_injective i.castSucc (h.trans hi.symm), fun h => h ▸ hi⟩

/-- **The first entry realises the smallest position**: the position of the label `i` in `σ^{(i)}`
comes before the position of the label `i + 1`, that is
`(σ^{(i)})^{-1}(i) < (σ^{(i)})^{-1}(i+1)`. It is stated at a pair of positions rather than through
an inverse function, which is the form the swapping lemma
`HJO.Dyck.auxToFrac_partialCharSeries_transposeTuple` carries the hypothesis in: the two positions
are `0` and `i + 1` by `HJO.Dyck.cycleTuple_castSucc_eq_self_iff` and
`HJO.Dyck.cycleTuple_castSucc_eq_succ_iff`. -/
@[hjo "lem_cm_sigmaseq_order"]
theorem cycleTuple_castSucc_lt_of_eq (i : Fin k) {j j' : Fin (k + 1)}
    (hj : cycleTuple i.castSucc j = (i : ℕ)) (hj' : cycleTuple i.castSucc j' = (i : ℕ) + 1) :
    j < j' := by
  rw [(cycleTuple_castSucc_eq_self_iff i j).1 hj, (cycleTuple_castSucc_eq_succ_iff i j').1 hj']
  exact i.succ_pos

/-! ### One transposition passes from one tuple to the next -/

/-- **One transposition passes from one tuple to the next**: `τ_i(σ^{(i)}) = σ^{(i+1)}`, the step
of the induction the raising recursion is proved by. Interchanging the labels `i` and `i + 1`
throughout `σ^{(i)}` moves the label `i` from the first position to the position `i + 1` and the
label `i + 1` the other way, and fixes the labels `0, …, i-1` at the positions `1, …, i` and the
labels `i + 2, …, k` at their own positions; that is the description of `σ^{(i+1)}`. -/
@[hjo "lem_cm_sigmaseq_step"]
theorem transposeTuple_cycleTuple_castSucc (i : Fin k) :
    transposeTuple (i : ℕ) (cycleTuple i.castSucc) = cycleTuple i.succ := by
  refine funext fun j => ?_
  induction j using Fin.cases with
  | zero => simp [transposeTuple]
  | succ j =>
    simp only [transposeTuple, Function.comp_apply, cycleTuple_succ]
    rcases lt_trichotomy (j : ℕ) (i : ℕ) with h | h | h
    · have h1 : i.castSucc.succAbove j = j.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)
      have h2 : i.succ.succAbove j = j.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _
          (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)
      rw [h1, h2, Fin.val_castSucc, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
    · have h1 : i.castSucc.succAbove j = j.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp only [Fin.le_def, Fin.val_castSucc]; omega)
      have h2 : i.succ.succAbove j = j.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _
          (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)
      rw [h1, h2, Fin.val_castSucc, Fin.val_succ, h, Equiv.swap_apply_right]
    · have h1 : i.castSucc.succAbove j = j.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp only [Fin.le_def, Fin.val_castSucc]; omega)
      have h2 : i.succ.succAbove j = j.succ :=
        Fin.succAbove_of_le_castSucc _ _
          (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
      rw [h1, h2, Fin.val_succ, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

end HJO.Dyck
