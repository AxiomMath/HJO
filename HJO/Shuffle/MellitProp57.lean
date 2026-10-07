/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidInsertPoint
public meta import HJO.Attr

/-! # Mellit's Proposition 5.7: inserting a fixed point at the start

`HJO.Braid.specialBraid_mul_trainDown_one`. For special-braid data `(w, β)` of rank `k + 1` carrying
an index `j` with `w_j = 1 - θ` and `β_j = 1` — a point at the *start*, which performs no
move — the braid of `(w, β)` is the braid of the deleted data `(w ∘ j.succAbove, β ∘ j.succAbove)`
with every index raised by one, conjugated so as to carry the inserted strand past the others:
`B_{s,w,β}·T_{i↘1} = T_{i'↘1}·φ*₊(B_{s,v,α})`, where `i` is the inserted point's rank in the initial
position tuple and `i'` its rank in the final one.

## Main results

* `HJO.Braid.moveTuple_apply_eq_iterate` — the entry a sequence of moves leaves at `t` is the
  `count`-th iterate of `nx_θ`, which is what identifies the stages of `HJO.Braid.moveStage` with
  the iterates that `HJO.Braid.IsSpecialBraidData` controls.
* `HJO.Braid.specialMoveList_eq_map_succAbove` — the move sequence of `HJO.Braid.specialBraid` for
  `(w, β)` is the move sequence for the deleted data read in the larger tuple, the multiplicity at
  the inserted index being `1`.
* `HJO.Braid.specialBraid_mul_trainDown_one`.

## Implementation notes

### The move sequences match because the insertion is order preserving

`HJO.Braid.specialBraid` lists the moves in increasing order of index, so the identification of the
two sequences is a statement about *lists* and not multisets: `HJO.Braid.flatMap_finRange_succAbove`
is the fact that `Fin.succAbove` enumerates `Fin (k+1) ∖ {j}` in order. It is an induction on `k`
splitting `j` into `0` and `j'.succ`, since `Fin.succAbove` commutes with `Fin.succ`. Mellit's own
Lemma 5.6 — that the braid depends only on how many times each index is used — would make the
ordering irrelevant, and is not needed.

### Which hypotheses are not needed

One could also require `(v, α)` to be special-braid data of rank `k` at slope `s`. That is a
consequence of the same for `(w, β)`, every clause of `HJO.Braid.IsSpecialBraidData` restricting
along `j.succAbove`, so it is not assumed, and the resulting statement is stronger. The
slope `s` survives only inside `HJO.Braid.IsSpecialBraidData`, which is where `θ(s+1) = 1` and
`s > 0` live; what the proof uses of them is `0 < θ < 1`.

## References

On creation operators: the lemma `HJO.Braid.specialBraid_mul_trainDown_one`, using
`HJO.Braid.trainDown`, `HJO.Braid.BraidMonoid`, `HJO.Braid.positionPair`, `HJO.Braid.entryRank`,
`HJO.Braid.IsSpecialBraidData`, `HJO.Braid.specialBraid`, `HJO.Braid.phiPlusStar`. Transcribing A.
Mellit, *Toric braids and `(m, n)`-parking functions*, Proposition 5.7.
-/

@[expose] public section

namespace HJO.Braid

variable {θ : ℚ} {k : ℕ}

/-! ### The stages of a sequence of moves are iterates -/

/-- **The entry a sequence of moves leaves at `t` is an iterate of `nx_θ`**, the exponent being the
number of times the sequence moves `t`. -/
theorem moveTuple_apply_eq_iterate {K : ℕ} (w : Fin K → ℚ) (l : List (Fin K)) (t : Fin K) :
    moveTuple θ w l t = (nextCrossing θ)^[l.count t] (w t) := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    rw [moveTuple_cons]
    by_cases h : t = m
    · subst h
      rw [moveOne_self, ih, List.count_cons_self, Function.iterate_succ_apply']
    · rw [moveOne_of_ne _ _ h, ih, List.count_cons_of_ne (Ne.symm h)]

/-- **The final position tuple of `HJO.Braid.positionPair` is the tuple after all the moves of
`HJO.Braid.specialBraid`.** -/
theorem moveTuple_specialMoveList (w : Fin k → ℚ) (β : Fin k → ℕ) :
    moveTuple θ w (specialMoveList β) = (positionPair θ w β).2 := by
  funext t
  rw [moveTuple_apply_eq_iterate, count_specialMoveList, positionPair_snd]

/-! ### The move sequence of the inserted data -/

/-- **`Fin.succAbove` enumerates `Fin (k+1) ∖ {j}` in order**, in the form the move sequence needs:
a list-valued function that is empty at `j` may be summed over the smaller index set.

Induction on `k`, splitting `j` into `0` — where `j.succAbove` is `Fin.succ` — and `j'.succ`, where
it fixes `0` and commutes with `Fin.succ`. -/
theorem flatMap_finRange_succAbove {γ : Type*} :
    ∀ (k : ℕ) (j : Fin (k + 1)) (g : Fin (k + 1) → List γ), g j = [] →
      (List.finRange (k + 1)).flatMap g
        = (List.finRange k).flatMap fun t => g (j.succAbove t)
  | 0, j, g, hg => by
    rw [show j = 0 from Fin.eq_zero j] at hg
    simp [hg]
  | (k + 1), j, g, hg => by
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · rw [List.finRange_succ, List.flatMap_cons, hg, List.nil_append, List.flatMap_map]
      rfl
    · have hL : (List.finRange (k + 1 + 1)).flatMap g
          = g 0 ++ (List.finRange (k + 1)).flatMap fun t => g t.succ := by
        rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
      have hR : ((List.finRange (k + 1)).flatMap fun t => g (j'.succ.succAbove t))
          = g (j'.succ.succAbove 0)
            ++ (List.finRange k).flatMap fun t => g (j'.succ.succAbove t.succ) := by
        rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
      rw [hL, hR, Fin.succ_succAbove_zero,
        flatMap_finRange_succAbove k j' (fun t => g t.succ) hg]
      simp only [Fin.succ_succAbove_succ]

/-- **The move sequence of `HJO.Braid.specialBraid` for the inserted data.** The inserted index has
multiplicity `1`, so it contributes no move, and the remaining moves are those of the deleted data
read in the larger tuple. -/
theorem specialMoveList_eq_map_succAbove (j : Fin (k + 1)) (β : Fin (k + 1) → ℕ) (hβj : β j = 1) :
    specialMoveList β = (specialMoveList (β ∘ j.succAbove)).map j.succAbove := by
  rw [specialMoveList, specialMoveList,
    flatMap_finRange_succAbove k j (fun i => List.replicate (β i - 1) i) (by simp [hβj]),
    List.map_flatMap]
  simp only [List.map_replicate, Function.comp_apply]

/-! ### The hypotheses from `HJO.Braid.IsSpecialBraidData` -/

/-- The antidiagonal coordinate of special-braid data lies in `(0,1)`: `θ(s+1) = 1` with `s > 0`. -/
theorem IsSpecialBraidData.theta_mem_Ioo {s θ : ℚ} {K : ℕ} {w : Fin K → ℚ} {β : Fin K → ℕ}
    (h : IsSpecialBraidData s θ K w β) : θ ∈ Set.Ioo (0 : ℚ) 1 := by
  have hs := h.slope_pos
  have hθ := h.theta_spec
  constructor
  · nlinarith
  · nlinarith

/-- **Every iterate the data controls lies in `(0,1)`.** The initial position does, and `nx_θ` keeps
a point of `(0,1)` in `(0,1)` as long as it is not the puncture, which is the `ne_theta` clause of
`HJO.Braid.IsSpecialBraidData`. -/
theorem IsSpecialBraidData.iterate_mem_Ioo {s θ : ℚ} {K : ℕ} {w : Fin K → ℚ} {β : Fin K → ℕ}
    (h : IsSpecialBraidData s θ K w β) (t : Fin K) :
    ∀ r, r < β t → (nextCrossing θ)^[r] (w t) ∈ Set.Ioo (0 : ℚ) 1 := by
  intro r
  induction r with
  | zero => intro _; exact h.mem_Ioo t
  | succ r ih =>
    intro hr
    have hprev := ih (by omega)
    rw [Function.iterate_succ_apply']
    exact nextCrossing_mem_Ioo h.theta_mem_Ioo.1 h.theta_mem_Ioo.2 hprev.1 hprev.2
      (h.ne_theta t r (by omega))

/-! ### Proposition 5.7 -/

/-- **Mellit's Proposition 5.7**, `HJO.Braid.specialBraid_mul_trainDown_one`: let `(w, β)` be
special-braid data of rank `k + 1` at slope `s`, and let `j` be an index with `w_j = 1 - θ` and
`β_j = 1` — a point at the
*start*, which performs no move. Write `v = w ∘ j.succAbove` and `α = β ∘ j.succAbove` for the data
with the `j`-th entry deleted, `i` for the rank of `w_j` in the initial position tuple and `i'` for
the rank of the `j`-th entry of the final position tuple of `HJO.Braid.positionPair`. Then, in
`𝔹_{k+1}^+(𝕋_0)`,
`B_{s,w,β}·T_{i↘1} = T_{i'↘1}·φ*₊(B_{s,v,α})`.

The proof is the induction of `HJO.Braid.braidWord_map_succAbove_mul_trainDown_one` on the sequence
of moves, whose per-move step is the four braid identities of
`HJO/Shuffle/BraidPhiInsert.lean`; what this adds is the identification of the two move
sequences (`HJO.Braid.specialMoveList_eq_map_succAbove`) and of the final position tuple with the
last stage of the sequence (`HJO.Braid.moveTuple_specialMoveList`). -/
@[hjo "lem_mellit_prop57"]
theorem specialBraid_mul_trainDown_one {s : ℚ} (hk : 1 ≤ k) (w : Fin (k + 1) → ℚ)
    (β : Fin (k + 1) → ℕ) (hdata : IsSpecialBraidData s θ (k + 1) w β) (j : Fin (k + 1))
    (hwj : w j = 1 - θ) (hβj : β j = 1) :
    specialBraid θ w β * braidTrainDown (k + 1) (entryRank w j) 1
      = braidTrainDown (k + 1) (entryRank (positionPair θ w β).2 j) 1 *
        phiPlusStar k hk (specialBraid θ (w ∘ j.succAbove) (β ∘ j.succAbove)) := by
  have hlist := specialMoveList_eq_map_succAbove j β hβj
  -- every move of every suffix is one of the iterates `HJO.Braid.IsSpecialBraidData` controls
  have hcount : ∀ l' : List (Fin k), l' <:+ specialMoveList (β ∘ j.succAbove) →
      ∀ t : Fin (k + 1), (l'.map j.succAbove).count t < β t := by
    intro l' hl' t
    obtain ⟨pre, hpre⟩ := hl'
    have hsub : List.Sublist (l'.map j.succAbove) (specialMoveList β) :=
      List.IsSuffix.sublist ⟨pre.map j.succAbove, by rw [← List.map_append, hpre, hlist]⟩
    have hle := hsub.count_le t
    rw [count_specialMoveList] at hle
    have := hdata.one_le_mult t
    omega
  have hiter : ∀ l' : List (Fin k), l' <:+ specialMoveList (β ∘ j.succAbove) →
      ∀ t : Fin (k + 1), moveTuple θ w (l'.map j.succAbove) t
        = (nextCrossing θ)^[(l'.map j.succAbove).count t] (w t) :=
    fun l' _ t => moveTuple_apply_eq_iterate w _ t
  rw [specialBraid, specialBraid, hlist,
    braidWord_map_succAbove_mul_trainDown_one hk j w hwj _
      (fun l' hl' t t' htt => by
        rw [hiter l' hl' t, hiter l' hl' t'] at htt
        exact (hdata.injective t t' _ _ (hcount l' hl' t) (hcount l' hl' t') htt).1)
      (fun l' hl' t => by
        rw [hiter l' hl' t]
        exact hdata.iterate_mem_Ioo t _ (hcount l' hl' t))
      fun t₀ l' hl' => by
        rw [hiter l' ((List.suffix_cons t₀ l').trans hl') (j.succAbove t₀)]
        exact hdata.ne_theta _ _ (hcount l' ((List.suffix_cons t₀ l').trans hl') (j.succAbove t₀)),
    ← hlist, moveTuple_specialMoveList]

end HJO.Braid

end
