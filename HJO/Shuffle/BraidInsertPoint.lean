/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidPhiInsert
public import HJO.Shuffle.BraidSpecial
public import Mathlib.Tactic.Linarith
public meta import HJO.Attr

/-! # Inserting a fixed point at the start

The combinatorics of Mellit's Proposition 5.7: a point placed at `1 - θ` — Mellit's *start* —
never moves, and every other point's rank is its rank in the smaller tuple raised by one exactly
when it lies above the inserted point. This file turns the four braid identities of
`HJO/Shuffle/BraidPhiInsert.lean` into the statement about one elementary move of
`HJO.Braid.braidStep`, and then runs the induction on the sequence of moves.

## Main results

* `HJO.Braid.entryRank_self_succAbove`, `HJO.Braid.entryRank_succAbove` — the two ranks of
  `HJO.Braid.entryRank` after an insertion: the inserted point's rank counts the entries below it,
  and every other point's rank rises by one exactly when the inserted point is below it.
* `HJO.Braid.card_filter_moveOne_add` — one move changes the count of entries below the inserted
  point by the two indicator values, which is what makes the inserted point's rank change by at most
  one.
* `HJO.Braid.braidStep_succAbove_mul_trainDown_one_of_le` — **one move against the inserted point**:
  `b_m(u)·T_{i↘1} = T_{i'↘1}·φ*₊(b_{t₀}(p))`, the four cases of
  `HJO/Shuffle/BraidPhiInsert.lean` selected by the geometry, for an inserted point anywhere
  weakly below `1 - θ` that no other position separates from it.
* `HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le` — the induction on the length of the
  sequence, which is Proposition 5.7 for an arbitrary admissible sequence of moves.
* `HJO.Braid.braidStep_succAbove_mul_trainDown_one`,
  `HJO.Braid.braidWord_map_succAbove_mul_trainDown_one` — the two at the value `1 - θ`,
  where the extra hypothesis is free.

## Implementation notes

### The insertion is `Fin.succAbove`, and the deletion is composition with it

The smaller tuple `v` is obtained from `w` by deleting its `j`-th entry. That deletion is
`v = w ∘ j.succAbove`, which is the form every statement below reads, since it is the one that makes
`moveOne` and `moveTuple` commute with the insertion
(`HJO.Braid.moveOne_comp_succAbove`, `HJO.Braid.moveTuple_comp_succAbove`).

### What the geometry has to supply, and what it does not

Per move only five facts are used: `u j ≤ 1 - θ` together with `u m < u j + θ`, `0 < θ < 1`,
`0 < u m < 1`, `u m ≠ θ` and `u m ≠ u j`. The last is what makes the case split strict, and it comes
from the distinctness of the entries — the inserted point is *one of them*, so a moving point can
never land on it. At `u j = 1 - θ` the pair of positional hypotheses collapses to
nothing: `u j ≤ 1 - θ` is an equality and `u m < u j + θ` is `u m < 1`.
Nothing else about admissibility enters: the index ranges the four braid identities need are
`1 ≤ rk ≤ k`, which `HJO.Braid.entryRank_pos` and `HJO.Braid.entryRank_le` give for free.

The move never touches the inserted entry, `j` not being in the image of `j.succAbove`
(`HJO.Braid.moveTuple_apply_of_notMem`), which is the statement that the inserted point stays
fixed.

## References

This file proves `HJO.Braid.specialBraid_mul_trainDown_one`, using `HJO.Braid.trainDown`,
`HJO.Braid.BraidMonoid`, `HJO.Braid.positionPair`, `HJO.Braid.entryRank`,
`HJO.Braid.IsSpecialBraidData`, `HJO.Braid.specialBraid` and `HJO.Braid.phiPlusStar`. A. Mellit,
*Toric braids and `(m, n)`-parking functions*, Proposition 5.7.
-/

@[expose] public section

open Finset

namespace HJO.Braid

/-! ### The next crossing stays in the unit interval -/

/-- Below the puncture the trajectory wraps: `nx_θ(x) = x + 1 - θ`. -/
theorem nextCrossing_of_lt {θ x : ℚ} (h : x < θ) : nextCrossing θ x = x + 1 - θ := by
  simp only [nextCrossing, not_lt.2 h.le, ite_false]

/-- Above the puncture it does not: `nx_θ(x) = x - θ`. -/
theorem nextCrossing_of_gt {θ x : ℚ} (h : θ < x) : nextCrossing θ x = x - θ := by
  simp only [nextCrossing, h, ite_true]

/-- **`nx_θ` maps `(0,1) ∖ {θ}` into `(0,1)`.** Below `θ` the point jumps to `x + 1 - θ`, which is
above `1 - θ` and below `1`; above `θ` it drops to `x - θ`, which is positive and below `1 - θ`. At
the excluded `x = θ` the value is `1`, which is why the hypothesis is not decoration. -/
theorem nextCrossing_mem_Ioo {θ x : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hx0 : 0 < x) (hx1 : x < 1)
    (hne : x ≠ θ) : nextCrossing θ x ∈ Set.Ioo (0 : ℚ) 1 := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [nextCrossing_of_lt h]
    exact ⟨by linarith, by linarith⟩
  · rw [nextCrossing_of_gt h]
    exact ⟨by linarith, by linarith⟩

/-- Above the puncture the point drops below `1 - θ`: `θ < x < 1` gives `x - θ < 1 - θ`. -/
theorem nextCrossing_lt_of_lt {θ x : ℚ} (h : θ < x) (hx1 : x < 1) :
    nextCrossing θ x < 1 - θ := by
  rw [nextCrossing_of_gt h]
  linarith

/-- Below the puncture the point jumps above `1 - θ`: `0 < x < θ` gives `x + 1 - θ > 1 - θ`. -/
theorem lt_nextCrossing_of_lt {θ x : ℚ} (h : x < θ) (hx0 : 0 < x) : 1 - θ < nextCrossing θ x := by
  rw [nextCrossing_of_lt h]
  linarith

/-! ### Moves and the insertion -/

variable {θ : ℚ} {k : ℕ}

/-- An index the sequence does not move keeps its entry. -/
theorem moveTuple_apply_of_notMem {K : ℕ} (w : Fin K → ℚ) {l : List (Fin K)} {t : Fin K}
    (ht : t ∉ l) : moveTuple θ w l t = w t := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    rw [moveTuple_cons, moveOne_of_ne _ _ (by simpa using fun h => ht (by simp [h])),
      ih (fun h => ht (List.mem_cons_of_mem _ h))]

/-- **One move commutes with the insertion**: advancing the entry `j.succAbove t₀` of the larger
tuple and then deleting the `j`-th entry is advancing the entry `t₀` of the smaller one. -/
theorem moveOne_comp_succAbove (u : Fin (k + 1) → ℚ) (j : Fin (k + 1)) (t₀ : Fin k) :
    moveOne θ u (j.succAbove t₀) ∘ j.succAbove = moveOne θ (u ∘ j.succAbove) t₀ := by
  funext t
  by_cases h : t = t₀
  · subst h
    simp [moveOne]
  · rw [Function.comp_apply, moveOne_of_ne _ _ (fun hc => h (j.succAbove_right_injective hc)),
      moveOne_of_ne _ _ h, Function.comp_apply]

/-- **A sequence of moves commutes with the insertion.** -/
theorem moveTuple_comp_succAbove (u : Fin (k + 1) → ℚ) (j : Fin (k + 1)) (l : List (Fin k)) :
    moveTuple θ u (l.map j.succAbove) ∘ j.succAbove = moveTuple θ (u ∘ j.succAbove) l := by
  induction l with
  | nil => rfl
  | cons t₀ l ih =>
    rw [List.map_cons, moveTuple_cons, moveTuple_cons, ← ih, moveOne_comp_succAbove]

/-- The inserted index is never moved. -/
theorem moveTuple_map_succAbove_self (u : Fin (k + 1) → ℚ) (j : Fin (k + 1)) (l : List (Fin k)) :
    moveTuple θ u (l.map j.succAbove) j = u j :=
  moveTuple_apply_of_notMem u fun h => by
    obtain ⟨t, _, ht⟩ := List.mem_map.1 h
    exact (j.succAbove_ne t) ht

/-! ### The ranks of an insertion -/

/-- **The inserted point's rank counts the entries below it.** -/
theorem entryRank_self_succAbove (u : Fin (k + 1) → ℚ) (j : Fin (k + 1)) :
    entryRank u j = #{t : Fin k | (u ∘ j.succAbove) t ≤ u j} + 1 := by
  rw [entryRank, card_filter, Fin.sum_univ_succAbove _ j, card_filter]
  simp [Nat.add_comm]

/-- **Every other point's rank rises by one exactly when the inserted point is below it.** -/
theorem entryRank_succAbove (u : Fin (k + 1) → ℚ) (j : Fin (k + 1)) (t₀ : Fin k) :
    entryRank u (j.succAbove t₀)
      = entryRank (u ∘ j.succAbove) t₀ + (if u j ≤ u (j.succAbove t₀) then 1 else 0) := by
  rw [entryRank, card_filter, Fin.sum_univ_succAbove _ j, entryRank, card_filter, Nat.add_comm]
  rfl

/-- A point at or below the level has rank at most the number of entries at or below it. -/
theorem entryRank_le_card_filter {q : Fin k → ℚ} {t₀ : Fin k} {ζ : ℚ} (h : q t₀ ≤ ζ) :
    entryRank q t₀ ≤ #{t | q t ≤ ζ} :=
  card_le_card fun t ht => mem_filter.2 ⟨mem_univ t, (mem_filter.1 ht).2.trans h⟩

/-- A point above the level has rank greater than the number of entries at or below it. -/
theorem card_filter_lt_entryRank {q : Fin k → ℚ} {t₀ : Fin k} {ζ : ℚ} (h : ζ < q t₀) :
    #{t | q t ≤ ζ} + 1 ≤ entryRank q t₀ := by
  refine Nat.succ_le_of_lt (card_lt_card ⟨fun t ht => ?_, fun hsub => ?_⟩)
  · exact mem_filter.2 ⟨mem_univ t, (mem_filter.1 ht).2.trans h.le⟩
  · exact absurd (mem_filter.1 (hsub (mem_filter.2 ⟨mem_univ t₀, le_rfl⟩))).2 (not_le.2 h)

/-- **One move changes the count of entries at or below the level by the two indicators.** The
inserted point's rank is that count plus one, so this is what says the rank changes by at most one,
and in which direction. -/
theorem card_filter_moveOne_add (q : Fin k → ℚ) (t₀ : Fin k) (ζ : ℚ) :
    #{t | moveOne θ q t₀ t ≤ ζ} + (if q t₀ ≤ ζ then 1 else 0)
      = #{t | q t ≤ ζ} + (if nextCrossing θ (q t₀) ≤ ζ then 1 else 0) := by
  have hsplit : ∀ f : Fin k → ℕ, ∑ t : Fin k, f t = ∑ t ∈ univ.erase t₀, f t + f t₀ := fun f =>
    (sum_erase_add univ f (mem_univ t₀)).symm
  have hcongr : ∑ t ∈ univ.erase t₀, (if moveOne θ q t₀ t ≤ ζ then 1 else 0)
      = ∑ t ∈ univ.erase t₀, (if q t ≤ ζ then 1 else 0) :=
    sum_congr rfl fun t ht => by rw [moveOne_of_ne _ _ (mem_erase.1 ht).1]
  rw [card_filter, card_filter, hsplit (fun t => if moveOne θ q t₀ t ≤ ζ then 1 else 0),
    hsplit (fun t => if q t ≤ ζ then 1 else 0), hcongr, moveOne_self]
  omega

/-! ### One move against the inserted point -/

/-- **One elementary move against an inserted fixed point**, which is
`HJO.Braid.specialBraid_mul_trainDown_one` at `ℓ = 1`: for a tuple `u` of distinct points of `(0,1)`
with `u_j = 1 - θ`, and a move at an index `j.succAbove t₀` other than `j`,
`b_{j.succAbove t₀}(u)·T_{rk_u(j)↘1} = T_{rk_{u'}(j)↘1}·φ*₊(b_{t₀}(u ∘ j.succAbove))`.

Four cases, and the geometry chooses between them: which branch of `HJO.Braid.braidStep` fires is
the side of the puncture `θ` the moving point starts on, and which of the two index regimes fires is
the side of the inserted point `1 - θ` it starts on. A point below `θ` jumps *above* `1 - θ` and a
point above `θ` drops *below* it, so in two of the four cases the moving point crosses the inserted
one and the inserted point's rank changes by one.

No hypothesis on `θ` is needed here, not even `0 < θ < 1`: what the two branches use is that the
moving point lies in `(0,1)`, which is what puts `nx_θ` of it on the other side of `1 - θ`.

**The inserted point does not have to sit at `1 - θ`.** This is the isotopy clause at one move, and
it is what the whole file's generality rests on: the two branches read only the *side* of `u_j` the
moving point lands on, never the value of `u_j`. So `u_j = 1-θ` may be weakened to

* `u_j ≤ 1 - θ` — which with `u_m > 0` still puts `nx_θ(u_m) = u_m + 1 - θ` above `u_j` in the `z`
  branch; and
* `u_m < u_j + θ` — which is what puts `nx_θ(u_m) = u_m - θ` below `u_j` in the `ỹ` branch, and is
  the *only* place a lowered inserted point costs anything: at `u_j = 1 - θ` it is free, being
  `u_m < 1`.

The second hypothesis is sharp. If `u_m ∈ [u_j + θ, 1)` then `nx_θ(u_m)` lands in `[u_j, 1-θ)`, the
moving point does *not* cross the inserted one, and the inserted point's rank does not change: a
different braid, not this one. So "the braid depends on the entries only through the cell" is
exactly "no other point's position lies between the inserted point and `1-θ`", stated one move at a
time. -/
theorem braidStep_succAbove_mul_trainDown_one_of_le (hk : 1 ≤ k)
    (j : Fin (k + 1)) (u : Fin (k + 1) → ℚ) (t₀ : Fin k) (huj : u j ≤ 1 - θ)
    (hgap : u (j.succAbove t₀) < u j + θ) (hinj : Function.Injective u)
    (hIoo : ∀ t, u t ∈ Set.Ioo (0 : ℚ) 1) (hne : u (j.succAbove t₀) ≠ θ) :
    braidStep θ u (j.succAbove t₀) * braidTrainDown (k + 1) (entryRank u j) 1
      = braidTrainDown (k + 1) (entryRank (moveOne θ u (j.succAbove t₀)) j) 1 *
        phiPlusStar k hk (braidStep θ (u ∘ j.succAbove) t₀) := by
  have hmj : j.succAbove t₀ ≠ j := j.succAbove_ne t₀
  have hu'j : moveOne θ u (j.succAbove t₀) j = u j := moveOne_of_ne θ u (Ne.symm hmj)
  have hcomp : moveOne θ u (j.succAbove t₀) ∘ j.succAbove = moveOne θ (u ∘ j.succAbove) t₀ :=
    moveOne_comp_succAbove u j t₀
  have hx0 : 0 < u (j.succAbove t₀) := (hIoo _).1
  have hx1 : u (j.succAbove t₀) < 1 := (hIoo _).2
  have hxne : u (j.succAbove t₀) ≠ u j := fun h => hmj (hinj h)
  -- the rank of the moving point, before and after the move
  have hrm : entryRank u (j.succAbove t₀)
      = entryRank (u ∘ j.succAbove) t₀ + (if u j ≤ u (j.succAbove t₀) then 1 else 0) :=
    entryRank_succAbove u j t₀
  have hrm' : entryRank (moveOne θ u (j.succAbove t₀)) (j.succAbove t₀)
      = entryRank (moveOne θ (u ∘ j.succAbove) t₀) t₀
        + (if u j ≤ nextCrossing θ (u (j.succAbove t₀)) then 1 else 0) := by
    rw [entryRank_succAbove (moveOne θ u (j.succAbove t₀)) j t₀, hcomp, hu'j, moveOne_self]
  -- the rank of the inserted point, before and after the move
  have hij : entryRank u j = #{t | (u ∘ j.succAbove) t ≤ u j} + 1 := entryRank_self_succAbove u j
  have hij' : entryRank (moveOne θ u (j.succAbove t₀)) j
      = #{t | moveOne θ (u ∘ j.succAbove) t₀ t ≤ u j} + 1 := by
    rw [entryRank_self_succAbove (moveOne θ u (j.succAbove t₀)) j, hcomp, hu'j]
  have hcard := card_filter_moveOne_add (θ := θ) (u ∘ j.succAbove) t₀ (u j)
  -- the index bounds, all of them free
  have hA1 : 1 ≤ entryRank (u ∘ j.succAbove) t₀ := entryRank_pos _ _
  have hAk : entryRank (u ∘ j.succAbove) t₀ ≤ k := entryRank_le _ _
  have hA'1 : 1 ≤ entryRank (moveOne θ (u ∘ j.succAbove) t₀) t₀ := entryRank_pos _ _
  have hA'k : entryRank (moveOne θ (u ∘ j.succAbove) t₀) t₀ ≤ k := entryRank_le _ _
  have hCk : #{t | (u ∘ j.succAbove) t ≤ u j} ≤ k := by
    have h : #{t | (u ∘ j.succAbove) t ≤ u j} ≤ #(univ : Finset (Fin k)) := card_filter_le _ _
    simpa using h
  rcases lt_or_gt_of_ne hne with hxθ | hxθ
  · -- the `z` branch: the point jumps from below `θ` to above `1 - θ`
    have hx' : u j < nextCrossing θ (u (j.succAbove t₀)) := by
      rw [nextCrossing_of_lt hxθ]; linarith
    have hif' : (if u j ≤ nextCrossing θ (u (j.succAbove t₀)) then 1 else 0) = 1 :=
      ite_eq_left_of_eq_true _ _ (eq_true hx'.le)
    have hM2' : #{t | moveOne θ (u ∘ j.succAbove) t₀ t ≤ u j} + 1
        ≤ entryRank (moveOne θ (u ∘ j.succAbove) t₀) t₀ := by
      refine card_filter_lt_entryRank ?_
      rwa [moveOne_self]
    have hifc' : (if nextCrossing θ ((u ∘ j.succAbove) t₀) ≤ u j then 1 else 0) = 0 :=
      ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hx'))
    rw [braidStep_of_lt hxθ, braidStep_of_lt (show (u ∘ j.succAbove) t₀ < θ from hxθ), map_mul,
      phiPlusStar_braidTrainDown hk hA'1 hA1]
    rcases lt_or_gt_of_ne hxne with hxζ | hxζ
    · -- the moving point crosses the inserted one upwards, and `i` drops by one
      have hif : (if u j ≤ u (j.succAbove t₀) then 1 else 0) = 0 :=
        ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hxζ))
      have hifc : (if (u ∘ j.succAbove) t₀ ≤ u j then 1 else 0) = 1 :=
        ite_eq_left_of_eq_true _ _ (eq_true hxζ.le)
      have hM1 : entryRank (u ∘ j.succAbove) t₀ ≤ #{t | (u ∘ j.succAbove) t ≤ u j} :=
        entryRank_le_card_filter hxζ.le
      rw [hifc, hifc'] at hcard
      have heq : #{t | moveOne θ (u ∘ j.succAbove) t₀ t ≤ u j} + 1
          = #{t | (u ∘ j.succAbove) t ≤ u j} := by omega
      simp only [hrm, hrm', hif, hif', hij, hij', heq, Nat.add_zero]
      simpa only [mul_assoc] using trainDown_mul_braidGenZ_mul_trainDown_one_of_ge hk hA1
        (show entryRank (u ∘ j.succAbove) t₀ ≤ #{t | (u ∘ j.succAbove) t ≤ u j} from hM1)
        (show #{t | (u ∘ j.succAbove) t ≤ u j}
          ≤ entryRank (moveOne θ (u ∘ j.succAbove) t₀) t₀ from by omega) hAk hA'k
    · -- the moving point was already above the inserted one, and `i` is unchanged
      have hif : (if u j ≤ u (j.succAbove t₀) then 1 else 0) = 1 :=
        ite_eq_left_of_eq_true _ _ (eq_true hxζ.le)
      have hifc : (if (u ∘ j.succAbove) t₀ ≤ u j then 1 else 0) = 0 :=
        ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hxζ))
      have hM2 : #{t | (u ∘ j.succAbove) t ≤ u j} + 1 ≤ entryRank (u ∘ j.succAbove) t₀ :=
        card_filter_lt_entryRank hxζ
      rw [hifc, hifc'] at hcard
      have heq : #{t | moveOne θ (u ∘ j.succAbove) t₀ t ≤ u j}
          = #{t | (u ∘ j.succAbove) t ≤ u j} := by omega
      simp only [hrm, hrm', hif, hif', hij, hij', heq]
      simpa only [mul_assoc] using trainDown_mul_braidGenZ_mul_trainDown_one_of_le hk
        (show 1 ≤ #{t | (u ∘ j.succAbove) t ≤ u j} + 1 from by omega) hM2
        (show #{t | (u ∘ j.succAbove) t ≤ u j} + 1
          ≤ entryRank (moveOne θ (u ∘ j.succAbove) t₀) t₀ from by omega) hAk hA'k
  · -- the `ỹ` branch: the point drops from above `θ` to below `1 - θ`
    have hx' : nextCrossing θ (u (j.succAbove t₀)) < u j := by
      rw [nextCrossing_of_gt hxθ]; linarith
    have hif' : (if u j ≤ nextCrossing θ (u (j.succAbove t₀)) then 1 else 0) = 0 :=
      ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hx'))
    have hifc' : (if nextCrossing θ ((u ∘ j.succAbove) t₀) ≤ u j then 1 else 0) = 1 :=
      ite_eq_left_of_eq_true _ _ (eq_true hx'.le)
    have hM1' : entryRank (moveOne θ (u ∘ j.succAbove) t₀) t₀
        ≤ #{t | moveOne θ (u ∘ j.succAbove) t₀ t ≤ u j} := by
      refine entryRank_le_card_filter ?_
      rw [moveOne_self]
      exact hx'.le
    rw [braidStep_of_gt hxθ, braidStep_of_gt (show θ < (u ∘ j.succAbove) t₀ from hxθ), map_mul,
      phiPlusStar_braidTrainDown hk hA'1 hA1]
    rcases lt_or_gt_of_ne hxne with hxζ | hxζ
    · -- the moving point stays below the inserted one, and `i` is unchanged
      have hif : (if u j ≤ u (j.succAbove t₀) then 1 else 0) = 0 :=
        ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hxζ))
      have hifc : (if (u ∘ j.succAbove) t₀ ≤ u j then 1 else 0) = 1 :=
        ite_eq_left_of_eq_true _ _ (eq_true hxζ.le)
      have hM1 : entryRank (u ∘ j.succAbove) t₀ ≤ #{t | (u ∘ j.succAbove) t ≤ u j} :=
        entryRank_le_card_filter hxζ.le
      rw [hifc, hifc'] at hcard
      have heq : #{t | moveOne θ (u ∘ j.succAbove) t₀ t ≤ u j}
          = #{t | (u ∘ j.succAbove) t ≤ u j} := by omega
      simp only [hrm, hrm', hif, hif', hij, hij', heq, Nat.add_zero]
      simpa only [mul_assoc] using trainDown_mul_braidYtilde_mul_trainDown_one_of_le hk hA1
        (show entryRank (u ∘ j.succAbove) t₀ + 1 ≤ #{t | (u ∘ j.succAbove) t ≤ u j} + 1
          from by omega) hA'1
        (show entryRank (moveOne θ (u ∘ j.succAbove) t₀) t₀
          < #{t | (u ∘ j.succAbove) t ≤ u j} + 1 from by omega) hAk hA'k (by omega)
    · -- the moving point crosses the inserted one downwards, and `i` rises by one
      have hif : (if u j ≤ u (j.succAbove t₀) then 1 else 0) = 1 :=
        ite_eq_left_of_eq_true _ _ (eq_true hxζ.le)
      have hifc : (if (u ∘ j.succAbove) t₀ ≤ u j then 1 else 0) = 0 :=
        ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hxζ))
      have hM2 : #{t | (u ∘ j.succAbove) t ≤ u j} + 1 ≤ entryRank (u ∘ j.succAbove) t₀ :=
        card_filter_lt_entryRank hxζ
      rw [hifc, hifc'] at hcard
      have heq : #{t | moveOne θ (u ∘ j.succAbove) t₀ t ≤ u j}
          = #{t | (u ∘ j.succAbove) t ≤ u j} + 1 := by omega
      simp only [hrm, hrm', hif, hif', hij, hij', heq, Nat.add_zero]
      simpa only [mul_assoc] using trainDown_mul_braidYtilde_mul_trainDown_one_of_ge hk
        (show 1 ≤ #{t | (u ∘ j.succAbove) t ≤ u j} + 1 from by omega) hM2 hA'1
        (show entryRank (moveOne θ (u ∘ j.succAbove) t₀) t₀
          ≤ #{t | (u ∘ j.succAbove) t ≤ u j} + 1 from by omega) hAk hA'k

/-- **One elementary move against a point inserted at the start `1 - θ`**, the case
`HJO.Braid.specialBraid_mul_trainDown_one` reads: the `ỹ`-branch hypothesis of
`HJO.Braid.braidStep_succAbove_mul_trainDown_one_of_le` is then `u_m < 1`, which
`HJO.Braid.IsSpecialBraidData` supplies. -/
theorem braidStep_succAbove_mul_trainDown_one (hk : 1 ≤ k)
    (j : Fin (k + 1)) (u : Fin (k + 1) → ℚ) (huj : u j = 1 - θ) (hinj : Function.Injective u)
    (hIoo : ∀ t, u t ∈ Set.Ioo (0 : ℚ) 1) (t₀ : Fin k) (hne : u (j.succAbove t₀) ≠ θ) :
    braidStep θ u (j.succAbove t₀) * braidTrainDown (k + 1) (entryRank u j) 1
      = braidTrainDown (k + 1) (entryRank (moveOne θ u (j.succAbove t₀)) j) 1 *
        phiPlusStar k hk (braidStep θ (u ∘ j.succAbove) t₀) :=
  braidStep_succAbove_mul_trainDown_one_of_le hk j u t₀ huj.le
    (by rw [huj]; have := (hIoo (j.succAbove t₀)).2; linarith) hinj hIoo hne

/-! ### The induction on the sequence of moves -/

/-- **Proposition 5.7 for an arbitrary sequence of moves**: for every sequence `l` of moves of the
smaller tuple,
`b_{l·j}(w)·T_{rk_w(j)↘1} = T_{rk_{w^{(l)}}(j)↘1}·φ*₊(b_l(w ∘ j.succAbove))`,
where `l·j` is the sequence read in the larger tuple.

Induction on `l`, peeling the move that is performed *last*, which is the head of the list and the
leftmost factor of `HJO.Braid.braidWord`: the inductive hypothesis produces the descending train of
the inserted point's rank at the stage that move sees, and
`HJO.Braid.braidStep_succAbove_mul_trainDown_one` carries that move past it.

The four hypotheses are what every stage of the sequence needs — distinct entries, entries in
`(0,1)`, a moving entry different from `θ`, and the isotopy clause `u_m < w_j + θ` of
`HJO.Braid.braidStep_succAbove_mul_trainDown_one_of_le` — and they are stated over suffixes of `l`
because that is what the induction consumes. For the sequence of `HJO.Braid.specialBraid` they come
from `HJO.Braid.IsSpecialBraidData`, the last one excepted: at `w_j = 1-θ` it is `u_m < 1` and free
(`HJO.Braid.braidWord_map_succAbove_mul_trainDown_one`), and below `1-θ` it is a genuine hypothesis
saying that no other point's position lies between `w_j` and `1-θ`. -/
theorem braidWord_map_succAbove_mul_trainDown_one_of_le (hk : 1 ≤ k) (j : Fin (k + 1))
    (w : Fin (k + 1) → ℚ) (hwj : w j ≤ 1 - θ) :
    ∀ l : List (Fin k),
      (∀ l', l' <:+ l → Function.Injective (moveTuple θ w (l'.map j.succAbove))) →
      (∀ l', l' <:+ l → ∀ t, moveTuple θ w (l'.map j.succAbove) t ∈ Set.Ioo (0 : ℚ) 1) →
      (∀ (t₀ : Fin k) (l' : List (Fin k)), t₀ :: l' <:+ l →
        moveTuple θ w (l'.map j.succAbove) (j.succAbove t₀) ≠ θ) →
      (∀ (t₀ : Fin k) (l' : List (Fin k)), t₀ :: l' <:+ l →
        moveTuple θ w (l'.map j.succAbove) (j.succAbove t₀) < w j + θ) →
      braidWord θ w (l.map j.succAbove) * braidTrainDown (k + 1) (entryRank w j) 1
        = braidTrainDown (k + 1) (entryRank (moveTuple θ w (l.map j.succAbove)) j) 1 *
          phiPlusStar k hk (braidWord θ (w ∘ j.succAbove) l) := by
  intro l
  induction l with
  | nil => intro _ _ _ _; simp
  | cons t₀ l ih =>
    intro hinj hIoo hne hgap
    have hsuf : l <:+ t₀ :: l := List.suffix_cons t₀ l
    have ihl := ih (fun l' h => hinj l' (h.trans hsuf)) (fun l' h => hIoo l' (h.trans hsuf))
      (fun s l' h => hne s l' (h.trans hsuf)) fun s l' h => hgap s l' (h.trans hsuf)
    have hstep := braidStep_succAbove_mul_trainDown_one_of_le hk j
      (moveTuple θ w (l.map j.succAbove)) t₀
      (by rw [moveTuple_map_succAbove_self]; exact hwj)
      (by rw [moveTuple_map_succAbove_self]; exact hgap t₀ l (List.suffix_refl _))
      (hinj l hsuf) (hIoo l hsuf) (hne t₀ l (List.suffix_refl _))
    rw [moveTuple_comp_succAbove] at hstep
    rw [List.map_cons, braidWord_cons, braidWord_cons, moveTuple_cons, map_mul]
    calc braidStep θ (moveTuple θ w (l.map j.succAbove)) (j.succAbove t₀) *
          braidWord θ w (l.map j.succAbove) * braidTrainDown (k + 1) (entryRank w j) 1
        = braidStep θ (moveTuple θ w (l.map j.succAbove)) (j.succAbove t₀) *
            (braidWord θ w (l.map j.succAbove) * braidTrainDown (k + 1) (entryRank w j) 1) :=
          mul_assoc _ _ _
      _ = braidStep θ (moveTuple θ w (l.map j.succAbove)) (j.succAbove t₀) *
            (braidTrainDown (k + 1) (entryRank (moveTuple θ w (l.map j.succAbove)) j) 1 *
              phiPlusStar k hk (braidWord θ (w ∘ j.succAbove) l)) := by rw [ihl]
      _ = braidStep θ (moveTuple θ w (l.map j.succAbove)) (j.succAbove t₀) *
            braidTrainDown (k + 1) (entryRank (moveTuple θ w (l.map j.succAbove)) j) 1 *
              phiPlusStar k hk (braidWord θ (w ∘ j.succAbove) l) := (mul_assoc _ _ _).symm
      _ = braidTrainDown (k + 1)
            (entryRank (moveOne θ (moveTuple θ w (l.map j.succAbove)) (j.succAbove t₀)) j) 1 *
            phiPlusStar k hk (braidStep θ (moveTuple θ (w ∘ j.succAbove) l) t₀) *
              phiPlusStar k hk (braidWord θ (w ∘ j.succAbove) l) := by rw [hstep]
      _ = braidTrainDown (k + 1)
            (entryRank (moveOne θ (moveTuple θ w (l.map j.succAbove)) (j.succAbove t₀)) j) 1 *
            (phiPlusStar k hk (braidStep θ (moveTuple θ (w ∘ j.succAbove) l) t₀) *
              phiPlusStar k hk (braidWord θ (w ∘ j.succAbove) l)) := mul_assoc _ _ _

/-- **Proposition 5.7 for a point inserted at the start `1 - θ`**, which is the form
`HJO.Braid.specialBraid_mul_trainDown_one` states: the isotopy clause of
`HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le` reads `u_m < 1` there and is supplied by
`HJO.Braid.IsSpecialBraidData`, so the three original hypotheses suffice. -/
theorem braidWord_map_succAbove_mul_trainDown_one (hk : 1 ≤ k) (j : Fin (k + 1))
    (w : Fin (k + 1) → ℚ) (hwj : w j = 1 - θ) :
    ∀ l : List (Fin k),
      (∀ l', l' <:+ l → Function.Injective (moveTuple θ w (l'.map j.succAbove))) →
      (∀ l', l' <:+ l → ∀ t, moveTuple θ w (l'.map j.succAbove) t ∈ Set.Ioo (0 : ℚ) 1) →
      (∀ (t₀ : Fin k) (l' : List (Fin k)), t₀ :: l' <:+ l →
        moveTuple θ w (l'.map j.succAbove) (j.succAbove t₀) ≠ θ) →
      braidWord θ w (l.map j.succAbove) * braidTrainDown (k + 1) (entryRank w j) 1
        = braidTrainDown (k + 1) (entryRank (moveTuple θ w (l.map j.succAbove)) j) 1 *
          phiPlusStar k hk (braidWord θ (w ∘ j.succAbove) l) := by
  intro l hinj hIoo hne
  refine braidWord_map_succAbove_mul_trainDown_one_of_le hk j w hwj.le l hinj hIoo hne
    fun t₀ l' hl' => ?_
  have h := (hIoo l' ((List.suffix_cons t₀ l').trans hl') (j.succAbove t₀)).2
  rw [hwj]
  linarith

end HJO.Braid

end
