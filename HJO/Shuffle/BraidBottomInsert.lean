/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidInversions
public import HJO.Shuffle.MellitProp57

/-! # Inserting a fixed point at the BOTTOM

`HJO/Shuffle/BraidInsertPoint.lean` inserts a point that never moves at the *top* of the
position tuple, at or just under the start `1 - θ`, and carries the inserted strand past
the others by the conjugating train `T_{i↘1}`. This file does the opposite insertion: a point that
never moves and is the **strict minimum** of the tuple, at every stage of the sequence of moves.

That is the geometry of a type-`A` event of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`. A
type-`A` event inserts the lattice point `P` of *least* rank above the lower level
(`HJO.Mellit.Isolates.levelPosition_le_braidDataOfColouring_fst`), and its component has
multiplicity `1` (`HJO.Mellit.totalCrossings_of_eventType_A`), so the inserted entry performs no
move. The two facts together are exactly the hypotheses below.

## Main results

* `HJO.Braid.entryRank_eq_one_of_forall_lt` — an inserted minimum has rank `1`, so the conjugating
  train `T_{rk↘1}` of `HJO.Braid.specialBraid_mul_trainDown_one` is **empty**.
* `HJO.Braid.entryRank_succAbove_of_forall_lt` — every other entry's rank is its rank in the deleted
  tuple raised by one.
* `HJO.Braid.braidStep_succAbove_of_forall_lt` — **the mechanism at one move.** The letter of a
  retained entry's move against an inserted minimum is the letter of the same move in the deleted
  tuple with *every* index — both indices of the descending train and the index of the `z` or `ỹ` —
  raised by one. Nothing else changes and no conjugation appears.
* `HJO.Braid.tupleInversions_of_forall_lt` — **the inversion-count half.** Inserting a strict
  minimum at the index `j` adds `#\{t < j\}` inversions, whatever the values are. Applied to the
  initial and the final position tuple of `HJO.Braid.positionPair` it says that
  `inv_fin - inv_ini`, hence the prefactor `q^{(inv_fin - inv_ini)/2}` of the braid value, is
  **unchanged** by the insertion; `HJO.Braid.invFin_sub_invIni_of_forall_lt` is that corollary,
  stated for the two counts of `HJO.Braid.invIni` and `HJO.Braid.invFin` themselves.
* `HJO.Braid.braidStep_succAbove_eq_phiPlusStar_of_lt` and
  `HJO.Braid.braidWord_map_succAbove_eq_phiPlusStar_of_lt`,
  `HJO.Braid.specialBraid_eq_phiPlusStar_of_lt` — **below the puncture the raise IS
  `HJO.Braid.phiPlusStar`.** When every moving stage position is below `θ` every letter is a `z`,
  and `HJO.Braid.phiPlusStar_z` raises the index of a `z` on the nose, so the whole special braid of
  the inserted data is `φ^*_+` of the deleted one, with no conjugating train at either end.

## Implementation notes

### Above the puncture the raise is *not* `φ^*_+`, and that is not a defect of the proof

`HJO.Braid.phiPlusStar_braidYtilde` records that `φ^*_+(ỹ_a) = T_{a+1↘2}T̄_1ỹ_1T_{1↗a+1}` while
`HJO.Braid.braidYtilde_succ_eq` records `ỹ_{a+1} = T_{a+1↘2}T_1ỹ_1T_{1↗a+1}`: the two differ by the
middle letter, that is by `T_1^2`. So at a move *above* the puncture — the `ỹ` branch of
`HJO.Braid.braidStep`, which is the branch the only decided type-`A` instance
(`HJO.Mellit.braidValueColouring_gap_typeA`) takes — the letter of the inserted tuple is `ỹ_{a+1}`
and is **not** `φ^*_+(ỹ_a)`. `HJO.Braid.braidStep_succAbove_ytilde_of_forall_lt` and
`HJO.Braid.phiPlusStar_braidStep_ytilde` below write the two words out side by side, so the
discrepancy is a theorem and not a remark.

This is why the statement here is at one move and at the `z` branch, and not a monoid homomorphism
carrying `ỹ_a` to `ỹ_{a+1}`: `HJO.Braid.phiPlusStar` is the only such homomorphism the
library has, and it is not that map.

### The hypotheses are read at every stage, and the "after" condition is free

The minimality hypothesis is quantified over the suffixes of the sequence of moves, which is what
the induction of `HJO.Braid.braidWord_map_succAbove_eq_phiPlusStar_of_lt` consumes; the tuple after
a move is the stage tuple of a longer suffix, so no separate "the inserted point is still the
minimum after the move" clause is needed.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5. -/

@[expose] public section

open Finset

namespace HJO.Braid

variable {θ : ℚ} {k : ℕ}

/-! ### The two ranks of a bottom insertion -/

/-- **An inserted strict minimum has rank `1`.** So the conjugating train `T_{rk_w(j)↘1}` of
`HJO.Braid.specialBraid_mul_trainDown_one` is the identity at a bottom insertion, which is the whole
reason the insertion at the bottom is simpler than the insertion at the start. -/
theorem entryRank_eq_one_of_forall_lt {u : Fin (k + 1) → ℚ} {j : Fin (k + 1)}
    (h : ∀ t : Fin k, u j < u (j.succAbove t)) : entryRank u j = 1 := by
  rw [entryRank_self_succAbove u j, Finset.card_eq_zero.2 ?_, Nat.zero_add]
  rw [Finset.filter_eq_empty_iff]
  exact fun t _ => not_le.2 (h t)

/-- **Every other entry's rank rises by exactly one.** -/
theorem entryRank_succAbove_of_forall_lt {u : Fin (k + 1) → ℚ} {j : Fin (k + 1)}
    (h : ∀ t : Fin k, u j < u (j.succAbove t)) (t₀ : Fin k) :
    entryRank u (j.succAbove t₀) = entryRank (u ∘ j.succAbove) t₀ + 1 := by
  rw [entryRank_succAbove u j t₀, ite_eq_left_of_eq_true _ _ (eq_true (h t₀).le)]

/-- One move keeps an inserted minimum minimal, given that the moving entry does not drop below
it. -/
theorem forall_lt_moveOne_of_forall_lt {u : Fin (k + 1) → ℚ} {j : Fin (k + 1)} {t₀ : Fin k}
    (h : ∀ t : Fin k, u j < u (j.succAbove t))
    (h' : u j < nextCrossing θ (u (j.succAbove t₀))) (t : Fin k) :
    moveOne θ u (j.succAbove t₀) j < moveOne θ u (j.succAbove t₀) (j.succAbove t) := by
  rw [moveOne_of_ne θ u (Ne.symm (j.succAbove_ne t₀))]
  by_cases ht : t = t₀
  · subst ht
    rwa [moveOne_self]
  · rw [moveOne_of_ne θ u fun hc => ht (j.succAbove_right_injective hc)]
    exact h t

/-! ### One move against an inserted minimum -/

/-- **THE MECHANISM AT ONE MOVE.** Against an inserted entry that is the strict minimum before the
move and still below the moving entry after it, the letter of `HJO.Braid.braidStep` is the letter of
the same move in the deleted tuple with **every index raised by one**: both indices of the
descending train, and the index of the `z` or the `ỹ`. No conjugating train appears, the inserted
entry's rank being `1` throughout (`HJO.Braid.entryRank_eq_one_of_forall_lt`).

This is the formal content of "the inserted component contributes no letter to the special braid,
while the retained component's letter is untouched". It is untouched *up to the uniform raise*, and
that qualification is not idle: see `HJO.Braid.phiPlusStar_braidStep_ytilde`. -/
theorem braidStep_succAbove_of_forall_lt {u : Fin (k + 1) → ℚ} {j : Fin (k + 1)} {t₀ : Fin k}
    (h : ∀ t : Fin k, u j < u (j.succAbove t))
    (h' : u j < nextCrossing θ (u (j.succAbove t₀))) :
    braidStep θ u (j.succAbove t₀)
      = braidTrainDown (k + 1) (entryRank (moveOne θ (u ∘ j.succAbove) t₀) t₀ + 1)
            (entryRank (u ∘ j.succAbove) t₀ + 1) *
          (if (u ∘ j.succAbove) t₀ < θ then
              braidGenZ (k + 1) (entryRank (u ∘ j.succAbove) t₀ + 1)
            else braidYtilde (k + 1) (entryRank (u ∘ j.succAbove) t₀ + 1)) := by
  have hrank := entryRank_succAbove_of_forall_lt h t₀
  have hrank' : entryRank (moveOne θ u (j.succAbove t₀)) (j.succAbove t₀)
      = entryRank (moveOne θ (u ∘ j.succAbove) t₀) t₀ + 1 := by
    rw [entryRank_succAbove_of_forall_lt (forall_lt_moveOne_of_forall_lt h h') t₀,
      moveOne_comp_succAbove u j t₀]
  rw [braidStep, hrank, hrank']
  rfl

/-! ### The `ỹ` branch is *not* `φ^*_+` -/

/-- **The letter of a retained move above the puncture, written out.** The `ỹ` branch of
`HJO.Braid.braidStep_succAbove_of_forall_lt` with `HJO.Braid.braidYtilde_succ_eq` substituted, so
that it can be compared letter by letter with `HJO.Braid.phiPlusStar_braidStep_ytilde`. -/
theorem braidStep_succAbove_ytilde_of_forall_lt {u : Fin (k + 1) → ℚ} {j : Fin (k + 1)}
    {t₀ : Fin k} (h : ∀ t : Fin k, u j < u (j.succAbove t))
    (h' : u j < nextCrossing θ (u (j.succAbove t₀)))
    (hθ : ¬ (u ∘ j.succAbove) t₀ < θ) (hk : entryRank (u ∘ j.succAbove) t₀ ≤ k) :
    braidStep θ u (j.succAbove t₀)
      = braidTrainDown (k + 1) (entryRank (moveOne θ (u ∘ j.succAbove) t₀) t₀ + 1)
            (entryRank (u ∘ j.succAbove) t₀ + 1) *
          (braidTrainDown (k + 1) (entryRank (u ∘ j.succAbove) t₀ + 1) 2 *
            braidGenT (k + 1) 1 * braidYtilde (k + 1) 1 *
            braidTrainUp (k + 1) 1 (entryRank (u ∘ j.succAbove) t₀ + 1)) := by
  rw [braidStep_succAbove_of_forall_lt h h', ite_eq_right_of_eq_false _ _ (eq_false hθ),
    braidYtilde_succ_eq (entryRank_pos _ _) (by omega)]

/-- **`φ^*_+` of the same move, written out** — and the two words differ in exactly one letter,
`T̄_1` here against the `T_1` of `HJO.Braid.braidStep_succAbove_ytilde_of_forall_lt`. That is the
`T_1^2` of `HJO.Braid.phiPlusStar_braidYtilde`, and it is why a bottom insertion above the puncture
is **not** `HJO.Braid.phiPlusStar` of the deleted move. -/
theorem phiPlusStar_braidStep_ytilde (hk1 : 1 ≤ k) {v : Fin k → ℚ} {t₀ : Fin k}
    (hθ : ¬ v t₀ < θ) (hk : entryRank v t₀ ≤ k) :
    phiPlusStar k hk1 (braidStep θ v t₀)
      = braidTrainDown (k + 1) (entryRank (moveOne θ v t₀) t₀ + 1) (entryRank v t₀ + 1) *
          (braidTrainDown (k + 1) (entryRank v t₀ + 1) 2 *
            braidGenTinv (k + 1) 1 * braidYtilde (k + 1) 1 *
            braidTrainUp (k + 1) 1 (entryRank v t₀ + 1)) := by
  rw [braidStep, ite_eq_right_of_eq_false _ _ (eq_false hθ), map_mul,
    phiPlusStar_braidTrainDown hk1 (entryRank_pos _ _) (entryRank_pos _ _),
    phiPlusStar_braidYtilde hk1 (entryRank_pos _ _) hk]

/-! ### Below the puncture the raise IS `φ^*_+` -/

/-- **One move below the puncture is `φ^*_+` of the deleted move.** The letter is a `z`, and
`HJO.Braid.phiPlusStar_z` raises the index of a `z` on the nose. -/
theorem braidStep_succAbove_eq_phiPlusStar_of_lt (hk1 : 1 ≤ k) {u : Fin (k + 1) → ℚ}
    {j : Fin (k + 1)} {t₀ : Fin k} (h : ∀ t : Fin k, u j < u (j.succAbove t))
    (h' : u j < nextCrossing θ (u (j.succAbove t₀))) (hθ : (u ∘ j.succAbove) t₀ < θ) :
    braidStep θ u (j.succAbove t₀) = phiPlusStar k hk1 (braidStep θ (u ∘ j.succAbove) t₀) := by
  rw [braidStep_succAbove_of_forall_lt h h', ite_eq_left_of_eq_true _ _ (eq_true hθ), braidStep,
    ite_eq_left_of_eq_true _ _ (eq_true hθ), map_mul,
    phiPlusStar_braidTrainDown hk1 (entryRank_pos _ _) (entryRank_pos _ _),
    phiPlusStar_z hk1 (entryRank_pos _ _)]

/-- **A whole sequence of moves below the puncture is `φ^*_+` of the deleted sequence.** The
hypotheses are read at every suffix, which is what the induction consumes; the inserted entry is
never moved (`HJO.Braid.moveTuple_map_succAbove_self`), so the minimality clause at the suffix
`t₀ :: l'` is exactly the statement that the move at `t₀` leaves the inserted entry minimal. -/
theorem braidWord_map_succAbove_eq_phiPlusStar_of_lt (hk1 : 1 ≤ k) (j : Fin (k + 1))
    (w : Fin (k + 1) → ℚ) :
    ∀ l : List (Fin k),
      (∀ l', l' <:+ l → ∀ t : Fin k, moveTuple θ w (l'.map j.succAbove) j
          < moveTuple θ w (l'.map j.succAbove) (j.succAbove t)) →
      (∀ (t₀ : Fin k) (l' : List (Fin k)), t₀ :: l' <:+ l →
        moveTuple θ w (l'.map j.succAbove) (j.succAbove t₀) < θ) →
      braidWord θ w (l.map j.succAbove) = phiPlusStar k hk1 (braidWord θ (w ∘ j.succAbove) l) := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons t₀ l ih =>
    intro hmin hlt
    have hsuf : l <:+ t₀ :: l := List.suffix_cons t₀ l
    have ihl := ih (fun l' hl' => hmin l' (hl'.trans hsuf))
      fun s l' hl' => hlt s l' (hl'.trans hsuf)
    have hafter : moveTuple θ w (l.map j.succAbove) j
        < nextCrossing θ (moveTuple θ w (l.map j.succAbove) (j.succAbove t₀)) := by
      have h := hmin (t₀ :: l) (List.suffix_refl _) t₀
      rw [List.map_cons, moveTuple_cons, moveOne_of_ne θ _ (Ne.symm (j.succAbove_ne t₀)),
        moveOne_self] at h
      exact h
    have hstep := braidStep_succAbove_eq_phiPlusStar_of_lt hk1
      (u := moveTuple θ w (l.map j.succAbove)) (j := j) (t₀ := t₀) (hmin l hsuf) hafter
      (by rw [Function.comp_apply]; exact hlt t₀ l (List.suffix_refl _))
    rw [moveTuple_comp_succAbove] at hstep
    rw [List.map_cons, braidWord_cons, braidWord_cons, map_mul, hstep, ihl]

/-- **The special braid of a bottom insertion below the puncture.** The inserted index has
multiplicity `1`, so `HJO.Braid.specialMoveList_eq_map_succAbove` identifies the two sequences of
moves, and every letter is a `z`: the whole braid is `φ^*_+` of the deleted one, with **no**
conjugating train at either end — against `HJO.Braid.specialBraid_mul_trainDown_one`, which is the
same statement at a *top* insertion and carries `T_{i↘1}` on both sides. -/
theorem specialBraid_eq_phiPlusStar_of_lt (hk1 : 1 ≤ k) (j : Fin (k + 1)) (w : Fin (k + 1) → ℚ)
    (β : Fin (k + 1) → ℕ) (hβj : β j = 1)
    (hmin : ∀ l', l' <:+ specialMoveList (β ∘ j.succAbove) → ∀ t : Fin k,
      moveTuple θ w (l'.map j.succAbove) j
        < moveTuple θ w (l'.map j.succAbove) (j.succAbove t))
    (hlt : ∀ (t₀ : Fin k) (l' : List (Fin k)), t₀ :: l' <:+ specialMoveList (β ∘ j.succAbove) →
      moveTuple θ w (l'.map j.succAbove) (j.succAbove t₀) < θ) :
    specialBraid θ w β
      = phiPlusStar k hk1 (specialBraid θ (w ∘ j.succAbove) (β ∘ j.succAbove)) := by
  rw [specialBraid, specialBraid, specialMoveList_eq_map_succAbove j β hβj,
    braidWord_map_succAbove_eq_phiPlusStar_of_lt hk1 j w _ hmin hlt]

/-! ### The inversion count of a bottom insertion -/

/-- **Inserting a strict minimum adds `#\{t < j\}` inversions.** An inversion is a pair of indices
in increasing order whose entries are in decreasing order; the inserted entry being the least, it is
in inversion with exactly the entries *before* it, whatever the values are, and the remaining
inversions are those of the deleted tuple read through the order-preserving `Fin.succAbove`.

Read at the initial and the final position tuple of `HJO.Braid.positionPair` — the inserted entry
having multiplicity `1`, so that it is still the minimum at the end — this says that
`inv_fin - inv_ini` is **unchanged** by a type-`A` insertion, and with it the prefactor
`q^{(inv_fin - inv_ini)/2}` of `HJO.Mellit.braidValueOfData`. -/
theorem tupleInversions_of_forall_lt {u : Fin (k + 1) → ℚ} {j : Fin (k + 1)}
    (h : ∀ t : Fin k, u j < u (j.succAbove t)) :
    tupleInversions u = tupleInversions (u ∘ j.succAbove) + #{t : Fin (k + 1) | t < j} := by
  classical
  have hmono := Fin.strictMono_succAbove j
  have hsplit : {p ∈ (univ : Finset (Fin (k + 1) × Fin (k + 1))) | p.1 < p.2 ∧ u p.2 < u p.1}
      = ({p ∈ (univ : Finset (Fin k × Fin k)) |
            p.1 < p.2 ∧ (u ∘ j.succAbove) p.2 < (u ∘ j.succAbove) p.1}.image
          fun p => (j.succAbove p.1, j.succAbove p.2))
        ∪ ({t ∈ (univ : Finset (Fin (k + 1))) | t < j}.image fun t => (t, j)) := by
    ext ⟨p1, p2⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image,
      Function.comp_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨h12, hu⟩
      by_cases h2 : p2 = j
      · subst h2
        exact Or.inr ⟨p1, h12, rfl, rfl⟩
      · have h1 : p1 ≠ j := by
          rintro rfl
          obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq h2
          exact absurd hu (not_lt.2 (ht ▸ h t).le)
        obtain ⟨t1, ht1⟩ := Fin.exists_succAbove_eq h1
        obtain ⟨t2, ht2⟩ := Fin.exists_succAbove_eq h2
        refine Or.inl ⟨(t1, t2), ⟨?_, ?_⟩, ht1, ht2⟩
        · exact hmono.lt_iff_lt.1 (by rw [ht1, ht2]; exact h12)
        · rw [ht1, ht2]; exact hu
    · rintro (⟨⟨t1, t2⟩, ⟨h12, hu⟩, hp1, hp2⟩ | ⟨t, ht, hp1, hp2⟩)
      · subst hp1
        subst hp2
        exact ⟨hmono h12, hu⟩
      · subst hp1
        subst hp2
        obtain ⟨t', ht'⟩ := Fin.exists_succAbove_eq (ne_of_lt ht)
        exact ⟨ht, ht' ▸ h t'⟩
  have hdisj : Disjoint
      (({p ∈ (univ : Finset (Fin k × Fin k)) |
          p.1 < p.2 ∧ (u ∘ j.succAbove) p.2 < (u ∘ j.succAbove) p.1}.image
        fun p => (j.succAbove p.1, j.succAbove p.2)))
      (({t ∈ (univ : Finset (Fin (k + 1))) | t < j}.image fun t => (t, j))) := by
    rw [Finset.disjoint_left]
    rintro p hp hq
    obtain ⟨⟨t1, t2⟩, -, hp'⟩ := Finset.mem_image.1 hp
    obtain ⟨t, -, hq'⟩ := Finset.mem_image.1 hq
    rw [← hp'] at hq'
    exact j.succAbove_ne t2 (congrArg Prod.snd hq').symm
  rw [tupleInversions_eq_card_lt, tupleInversions_eq_card_lt, hsplit,
    Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ fun p p' hpp => Prod.ext
      (j.succAbove_right_injective (congrArg Prod.fst hpp))
      (j.succAbove_right_injective (congrArg Prod.snd hpp)),
    Finset.card_image_of_injective _ fun t t' htt => congrArg Prod.fst htt]

/-- **The prefactor of the braid value is unchanged by a bottom insertion of a fixed point.**
`inv_fin - inv_ini` is the same for the inserted data as for the deleted data: by
`HJO.Braid.tupleInversions_of_forall_lt` each of the two counts grows by the same `#\{t < j\}`, the
inserted entry being the strict minimum of the initial tuple by `hini` and of the final one by
`hfin` — where it is still its own initial position, its multiplicity being `1`.

This is the `hδ` hypothesis of `HJO.Mellit.braidValueOfData_eq_negYOneDPlusStar`, and it is the
"its inversion count is untouched" half of the type-`A` mechanism, in general. -/
theorem invFin_sub_invIni_of_forall_lt (j : Fin (k + 1)) (w : Fin (k + 1) → ℚ)
    (β : Fin (k + 1) → ℕ) (hβj : β j = 1) (hini : ∀ t : Fin k, w j < w (j.succAbove t))
    (hfin : ∀ t : Fin k,
      w j < (nextCrossing θ)^[β (j.succAbove t) - 1] (w (j.succAbove t))) :
    (invFin θ w β : ℤ) - (invIni θ w β : ℤ)
      = (invFin θ (w ∘ j.succAbove) (β ∘ j.succAbove) : ℤ)
        - (invIni θ (w ∘ j.succAbove) (β ∘ j.succAbove) : ℤ) := by
  have hcomp : ((fun i => (nextCrossing θ)^[β i - 1] (w i)) ∘ j.succAbove)
      = fun t => (nextCrossing θ)^[(β ∘ j.succAbove) t - 1] ((w ∘ j.succAbove) t) := rfl
  have hW : tupleInversions (fun i => (nextCrossing θ)^[β i - 1] (w i))
      = tupleInversions ((fun i => (nextCrossing θ)^[β i - 1] (w i)) ∘ j.succAbove)
          + #{t : Fin (k + 1) | t < j} := by
    refine tupleInversions_of_forall_lt fun t => ?_
    simp only [hβj, Nat.sub_self, Function.iterate_zero_apply]
    exact hfin t
  rw [invFin_eq_tupleInversions, invIni_eq_tupleInversions, invFin_eq_tupleInversions,
    invIni_eq_tupleInversions, hW, hcomp, tupleInversions_of_forall_lt hini]
  push_cast
  ring

end HJO.Braid

end
