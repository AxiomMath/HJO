/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidInversions
public import HJO.Shuffle.BraidSpecial
public import Mathlib.Tactic.Linarith

/-! # A rigid shift that crosses the puncture nowhere leaves the special braid alone

Every clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` owes the same bookkeeping: a
level drop moves the position tuple of `HJO.Mellit.braidDataOfColouring` by one common amount
(`HJO.Mellit.sweepTheta_eq_div`), and the clause has to say what that does to
`HJO.Braid.specialBraid` and to the two counts of `HJO.Braid.invIni` and `HJO.Braid.invFin`. The
answer is not "nothing": `HJO.Braid.exists_rotation_specialBraid_ne` exhibits a rigid rotation
across which the special braid changes, and `HJO.Braid.exists_rotation_invFin_sub_invIni_ne` one
across which the `q`-exponent changes. Both witnesses wrap — an entry passes `1` and re-enters at
`0`.

This file isolates what is true: **a shift under which no entry, at any stage of the move sequence,
changes which side of the puncture `θ` it is on, changes neither the braid nor either count.** Not a
rotation: the shift here is an honest addition, with no fractional part taken, which is the form a
level drop takes as long as the drop moves no entry past the wall
(`HJO.Mellit.braidDataOfColouring_fst_eq_add_of_notMem_sweptRegion`).

## Main results

* `HJO.Braid.SameSide` — `x` and `x + c` lie on the same side of `θ`. It is derived from `0 ≤ c`,
  the two values avoiding `θ`, and the one straddle being excluded, by
  `HJO.Braid.sameSide_of_not_straddle`.
* `HJO.Braid.entryRank_congr_add`, `HJO.Braid.tupleInversions_congr_add` — a rigid shift preserves
  the order of the entries, hence every rank of `HJO.Braid.entryRank` and every inversion count.
* `HJO.Braid.nextCrossing_add_of_sameSide`, `HJO.Braid.iterate_nextCrossing_add` — the walk of
  `HJO.Braid.nextCrossing` commutes with the shift as long as each iterate keeps its side.
* `HJO.Braid.braidStep_congr_add` — one letter of `HJO.Braid.braidStep` is unchanged: its train is
  determined by the two ranks and its generator by the side of the puncture, and the shift moves
  neither.
* `HJO.Braid.moveTuple_add_of_sameSide`, `HJO.Braid.braidWord_congr_add`,
  `HJO.Braid.specialBraid_congr_add` — the same for a whole move sequence, and for
  `HJO.Braid.specialBraid`.
* `HJO.Braid.invIni_congr_add`, `HJO.Braid.invFin_congr_add` — the two counts.

## Implementation notes

The hypothesis is quantified over the suffixes of the move list, `∀ l' <:+ l`, because that is what
the recursion of `HJO.Braid.braidWord` consumes: the head's letter is read at the tuple the tail has
already advanced. This is the same shape as the gap clause of
`HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le`. It is reduced to a hypothesis on the
iterates alone in `HJO.Mellit.specialBraid_congr_add_of_iterate`, using
`HJO.Braid.moveTuple_apply_eq_iterate` and `HJO.Braid.count_specialMoveList`.

`HJO.Braid.SameSide` is stated as a conjunction of two iffs rather than one, because `< θ` and
`θ <` are separately what `HJO.Braid.braidStep` and `HJO.Braid.nextCrossing` read, and at the
excluded value `x = θ` one iff does not imply the other. Nothing here assumes `0 ≤ c`; that
hypothesis appears only in `HJO.Braid.sameSide_of_not_straddle`, which is the convenient way to
produce `SameSide` for the upward shift a level drop performs.

## References

This file serves `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, using
`HJO.Mellit.sweepTheta_eq_div`, `HJO.Braid.tupleInversions_fract_add`, `HJO.Braid.zCount_mul`,
`HJO.Braid.specialBraid`, `HJO.Braid.braidStep`, `HJO.Braid.braidWord`, `HJO.Braid.entryRank`,
`HJO.Braid.nextCrossing`, `HJO.Braid.invIni` and `HJO.Braid.invFin`.
-/

@[expose] public section

open Finset

namespace HJO.Braid

/-! ### Being on the same side of the puncture before and after the shift -/

/-- `x` and `x + c` lie on the same side of the puncture `θ`. -/
def SameSide (θ c x : ℚ) : Prop := (x < θ ↔ x + c < θ) ∧ (θ < x ↔ θ < x + c)

theorem sameSide_of_not_straddle {θ c x : ℚ} (hc : 0 ≤ c) (hne : x ≠ θ) (hne' : x + c ≠ θ)
    (h : ¬ (x < θ ∧ θ < x + c)) : SameSide θ c x := by
  have hxc : x ≤ x + c := by linarith
  refine ⟨⟨fun hx => ?_, fun hx => lt_of_le_of_lt hxc hx⟩, ⟨fun hx => lt_of_lt_of_le hx hxc, ?_⟩⟩
  · rcases lt_trichotomy (x + c) θ with h1 | h1 | h1
    · exact h1
    · exact absurd h1 hne'
    · exact absurd ⟨hx, h1⟩ h
  · intro hx
    rcases lt_trichotomy x θ with h1 | h1 | h1
    · exact absurd ⟨h1, hx⟩ h
    · exact absurd h1 hne
    · exact h1

theorem nextCrossing_add_of_sameSide {θ c x : ℚ} (h : SameSide θ c x) :
    nextCrossing θ (x + c) = nextCrossing θ x + c := by
  unfold nextCrossing
  split_ifs with h1 h2 h2
  · ring
  · exact absurd (h.2.2 h1) h2
  · exact absurd (h.2.1 h2) h1
  · ring

theorem iterate_nextCrossing_add {θ c : ℚ} {x : ℚ} :
    ∀ m : ℕ, (∀ j < m, SameSide θ c ((nextCrossing θ)^[j] x)) →
      (nextCrossing θ)^[m] (x + c) = (nextCrossing θ)^[m] x + c
  | 0, _ => rfl
  | m + 1, h => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        iterate_nextCrossing_add m fun j hj => h j (by omega),
        nextCrossing_add_of_sameSide (h m (by omega))]

/-! ### The rank of an entry is a rigid-shift invariant -/

theorem entryRank_congr_add {k : ℕ} {w w' : Fin k → ℚ} {c : ℚ} (h : ∀ j, w' j = w j + c)
    (i : Fin k) : entryRank w' i = entryRank w i := by
  rw [entryRank, entryRank]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, add_le_add_iff_right]

/-! ### The move tuple and the braid word -/

theorem moveOne_add_of_sameSide {k : ℕ} {w w' : Fin k → ℚ} {c : ℚ} (θ : ℚ)
    (h : ∀ j, w' j = w j + c) {i : Fin k} (hs : SameSide θ c (w i)) (j : Fin k) :
    moveOne θ w' i j = moveOne θ w i j + c := by
  by_cases hj : j = i
  · subst hj
    rw [moveOne_self, moveOne_self, h, nextCrossing_add_of_sameSide hs]
  · rw [moveOne_of_ne _ _ hj, moveOne_of_ne _ _ hj, h]

theorem braidStep_congr_add {k : ℕ} {w w' : Fin k → ℚ} {c : ℚ} {θ : ℚ}
    (h : ∀ j, w' j = w j + c) {i : Fin k} (hs : SameSide θ c (w i)) :
    braidStep θ w' i = braidStep θ w i := by
  rw [braidStep, braidStep, entryRank_congr_add h i,
    entryRank_congr_add (moveOne_add_of_sameSide θ h hs) i]
  congr 1
  rw [h]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hs.1.2 h1) h2
  · exact absurd (hs.1.1 h2) h1
  · rfl

/-- **A rigid shift of the starting tuple is a rigid shift of every stage**, provided no entry
crosses the puncture at any stage. -/
theorem moveTuple_add_of_sameSide {k : ℕ} (θ c : ℚ) (w : Fin k → ℚ) :
    ∀ l : List (Fin k),
      (∀ l' : List (Fin k), l' <:+ l → ∀ i : Fin k, SameSide θ c (moveTuple θ w l' i)) →
      ∀ i : Fin k, moveTuple θ (fun j => w j + c) l i = moveTuple θ w l i + c
  | [], _, _ => rfl
  | i :: rest, h, j => by
      rw [moveTuple_cons, moveTuple_cons]
      exact moveOne_add_of_sameSide θ
        (moveTuple_add_of_sameSide θ c w rest
          (fun l' hl' => h l' (hl'.trans (List.suffix_cons i rest))))
        (h rest (List.suffix_cons i rest) i) j

/-- **The braid word is unchanged by a rigid shift that crosses no puncture.** -/
theorem braidWord_congr_add {k : ℕ} (θ c : ℚ) (w : Fin k → ℚ) :
    ∀ l : List (Fin k),
      (∀ l' : List (Fin k), l' <:+ l → ∀ i : Fin k, SameSide θ c (moveTuple θ w l' i)) →
      braidWord θ (fun j => w j + c) l = braidWord θ w l
  | [], _ => rfl
  | i :: rest, h => by
      rw [braidWord_cons, braidWord_cons,
        braidWord_congr_add θ c w rest
          (fun l' hl' => h l' (hl'.trans (List.suffix_cons i rest))),
        braidStep_congr_add
          (moveTuple_add_of_sameSide θ c w rest
            (fun l' hl' => h l' (hl'.trans (List.suffix_cons i rest))))
          (h rest (List.suffix_cons i rest) i)]

/-- **The special braid is unchanged by a rigid shift that crosses no puncture.** -/
theorem specialBraid_congr_add {k : ℕ} (θ c : ℚ) (v : Fin k → ℚ) (α : Fin k → ℕ)
    (h : ∀ l' : List (Fin k), l' <:+ specialMoveList α → ∀ i : Fin k,
      SameSide θ c (moveTuple θ v l' i)) :
    specialBraid θ (fun j => v j + c) α = specialBraid θ v α :=
  braidWord_congr_add θ c v (specialMoveList α) h

/-! ### The inversion counts are rigid-shift invariants -/

theorem tupleInversions_congr_add {k : ℕ} {w w' : Fin k → ℚ} {c : ℚ} (h : ∀ j, w' j = w j + c) :
    tupleInversions w' = tupleInversions w := by
  rw [tupleInversions_eq_card_lt, tupleInversions_eq_card_lt]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, add_lt_add_iff_right]

theorem invIni_congr_add {k : ℕ} (θ c : ℚ) (v : Fin k → ℚ) (α : Fin k → ℕ) :
    invIni θ (fun j => v j + c) α = invIni θ v α := by
  rw [invIni_eq_tupleInversions, invIni_eq_tupleInversions]
  exact tupleInversions_congr_add fun _ => rfl

theorem invFin_congr_add {k : ℕ} (θ c : ℚ) (v : Fin k → ℚ) (α : Fin k → ℕ)
    (h : ∀ (i : Fin k) (j : ℕ), j < α i - 1 → SameSide θ c ((nextCrossing θ)^[j] (v i))) :
    invFin θ (fun j => v j + c) α = invFin θ v α := by
  rw [invFin_eq_tupleInversions, invFin_eq_tupleInversions]
  exact tupleInversions_congr_add fun i =>
    iterate_nextCrossing_add (α i - 1) fun j hj => h i j hj

end HJO.Braid

end
