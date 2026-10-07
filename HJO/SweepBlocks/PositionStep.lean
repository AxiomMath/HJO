/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepEventTypes
public import HJO.Shuffle.SweepPositions
public meta import HJO.Attr

/-! # How the word position advances: one computation for both lemmas

The direct argument proves `HJO.Paths.wordPosition_of_rankAdjacent` at two rank-consecutive points
of `Sw(P̂)` and then gets `HJO.Paths.wordPosition_of_eventRankAdjacent` by *summing* the step lemma
over the type-`D` and type-`E` points lying between two consecutive events. **No summation is
needed.** Both are the same computation, and the weaker hypothesis suffices for it.

The difference `pos_{P̂}(P) - pos_{P̂}(Q)` counts the north steps whose foot has rank in
`(rk̂ Q, rk̂ P]` plus those whose head does. Every such foot and every such head is itself a swept
point of event type `A`, `B` or `C` — a foot by `HJO.Paths.mem_northSteps_iff_eventType`, a head by
`HJO.Paths.isSweepHead_iff_eventType`. So it is enough to know that **no swept point of type `A`,
`B` or `C`** has rank strictly between `rk̂ Q` and `rk̂ P`; the intervening `D` and `E` points are
never counted in the first place, so there is nothing to telescope through.

That hypothesis is `HJO.Paths.EventRankAdjacent`, and `HJO.Paths.RankAdjacent` implies it
(`HJO.Paths.RankAdjacent.eventRankAdjacent`). One computation therefore yields both lemmas.

## Main definitions

* `HJO.Paths.EventRankAdjacent`: `Q` and `P` are consecutive in the rank order **restricted to the
  events**, that is to the swept points of type `A`, `B` or `C`. This is being consecutive in the
  listing `Q_1, …, Q_L`.

## Main results

* `HJO.Paths.wordPosition_eq_of_eventRankAdjacent`: the position advances by the number of north
  steps with foot `P` plus the number with head `P`, each `0` or `1`. This is the computation.
* `HJO.Paths.wordPosition_of_rankAdjacent` — `2` at type `C`, `0` at
  types `D` and `E`, `1` otherwise.
* `HJO.Paths.wordPosition_of_eventRankAdjacent` — `2` at type `C` and `1`
  otherwise, between two consecutive *events*.

## Implementation notes

Both conclusions are stated in `ℕ` as `pos P = pos Q + δ` rather than as a subtraction: the
position is monotone in the rank, so nothing is truncated, but writing the difference in `ℕ` would
hide that. The `pos(P_r) - pos(P_{r+1})` has `P_r` the *upper* point, which is `P` here
and `Q` the lower one, matching `HJO.Paths.RankAdjacent`.

`HJO.Paths.wordPosition_of_eventRankAdjacent` is stated with `P` of event type `A`, `B` or `C` — the
`Q_l` lies in that list by construction. Type `D` or `E` at `P` is not excluded by
`EventRankAdjacent` itself, and there the advance is `0`; see
`wordPosition_eq_of_eventRankAdjacent`, which covers all five types at once.

## References

The lemmas `HJO.Paths.wordPosition_of_rankAdjacent` and
`HJO.Paths.wordPosition_of_eventRankAdjacent`, using `HJO.Paths.IsAboveDiagonal`,
`HJO.ParkingFunctions.abovePointRank`, `HJO.Paths.attackWindow`, `HJO.Paths.sweptRegion`,
`HJO.Paths.eventType` and `HJO.Paths.wordPosition`. Transcribing A. Mellit, *Toric braids and
`(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### Counting the feet and the heads at a point -/

/-- At a north step, exactly one north step has it for a foot. -/
theorem card_feet_of_mem {y : Heights a b N} {P : ℕ × ℕ} (h : P ∈ northSteps y) :
    #{u ∈ northSteps y | u = P} = 1 := by simp [filter_eq', h]

/-- Off the north steps, none has that point for a foot. -/
theorem card_feet_of_notMem {y : Heights a b N} {P : ℕ × ℕ} (h : P ∉ northSteps y) :
    #{u ∈ northSteps y | u = P} = 0 := by simp [filter_eq', h]

/-- At the head of a north step, exactly one north step has it for a head: the map `u ↦ u + (0,1)`
is injective, so there is at most one such step. -/
theorem card_heads_of_isSweepHead {y : Heights a b N} {P : ℕ × ℕ} (h : IsSweepHead y P) :
    #{u ∈ northSteps y | (u.1, u.2 + 1) = P} = 1 := by
  obtain ⟨w, hw, hwP⟩ := h
  have hsingle : {u ∈ northSteps y | (u.1, u.2 + 1) = P} = {w} := by
    ext v
    simp only [mem_filter, mem_singleton]
    refine ⟨fun hv => ?_, fun hv => hv ▸ ⟨hw, hwP⟩⟩
    have hvw := hv.2.trans hwP.symm
    rw [Prod.ext_iff] at hvw ⊢
    exact ⟨hvw.1, by omega⟩
  rw [hsingle, card_singleton]

/-- Off the heads of the north steps, none has that point for a head. -/
theorem card_heads_of_not_isSweepHead {y : Heights a b N} {P : ℕ × ℕ}
    (h : ¬IsSweepHead y P) : #{u ∈ northSteps y | (u.1, u.2 + 1) = P} = 0 := by
  rw [card_eq_zero]
  exact filter_eq_empty_iff.2 fun {v} hv hvP => h ⟨v, hv, hvP⟩

/-! ### Adjacency in the rank order restricted to the events -/

/-- Two points of the swept region are **adjacent in the event rank order**: `Q` is outranked by
`P` and no swept point of event type `A`, `B` or `C` is ranked strictly between them. This is being
consecutive in the listing `Q_1, …, Q_L` of the events by strictly decreasing rank,
with `P = Q_l` and `Q = Q_{l+1}`.

`HJO.Paths.RankAdjacent` excludes *every* swept point from the open interval and so implies this;
the point of the weaker form is that the computation of
`HJO.Paths.wordPosition_eq_of_eventRankAdjacent` only ever looks at feet and heads of north steps,
which are events. -/
def EventRankAdjacent (a b N : ℕ) (y : Heights a b N) (Q P : ℕ × ℕ) : Prop :=
  Q ∈ sweptRegion y ∧ P ∈ sweptRegion y ∧
    ParkingFunctions.abovePointRank a b N Q.1 Q.2 <
      ParkingFunctions.abovePointRank a b N P.1 P.2 ∧
    ∀ R ∈ sweptRegion y, eventType y R ≠ EventType.D → eventType y R ≠ EventType.E →
      ¬(ParkingFunctions.abovePointRank a b N Q.1 Q.2 <
          ParkingFunctions.abovePointRank a b N R.1 R.2 ∧
        ParkingFunctions.abovePointRank a b N R.1 R.2 <
          ParkingFunctions.abovePointRank a b N P.1 P.2)

/-- Rank-adjacent points are event-rank-adjacent: excluding every swept point from the open rank
interval excludes in particular the events. -/
theorem RankAdjacent.eventRankAdjacent {y : Heights a b N} {Q P : ℕ × ℕ}
    (hadj : RankAdjacent a b N y Q P) : EventRankAdjacent a b N y Q P :=
  ⟨hadj.1, hadj.2.1, hadj.2.2.1, fun R hR _ _ => hadj.2.2.2 R hR⟩

/-- A swept point of type `A`, `B` or `C` outranking the lower end of an event-rank-adjacent pair
is ranked at or above the upper end: the contrapositive form of the gap clause. -/
private theorem EventRankAdjacent.le_of_lt {y : Heights a b N} {Q P : ℕ × ℕ}
    (hadj : EventRankAdjacent a b N y Q P) {R : ℕ × ℕ} (hR : R ∈ sweptRegion y)
    (hD : eventType y R ≠ EventType.D) (hE : eventType y R ≠ EventType.E)
    (h : ParkingFunctions.abovePointRank a b N Q.1 Q.2 <
      ParkingFunctions.abovePointRank a b N R.1 R.2) :
    ParkingFunctions.abovePointRank a b N P.1 P.2 ≤
      ParkingFunctions.abovePointRank a b N R.1 R.2 :=
  not_lt.1 fun hcon => hadj.2.2.2 R hR hD hE ⟨h, hcon⟩

/-! ### The two half-open counts -/

/-- **The north steps whose foot is newly outranked are exactly those with foot `P`.** A north step
whose foot has rank in `(rk̂ Q, rk̂ P]` is a swept point of event type `B` or `C`
(`HJO.Paths.mem_northSteps_iff_eventType`), so the gap clause forbids its rank from being strictly
below `rk̂ P`; injectivity of the rank then identifies the foot with `P`. -/
private theorem sdiff_feet {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a) (hN : 0 < N)
    {Q P : ℕ × ℕ} (hadj : EventRankAdjacent a b N y Q P) :
    {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
        ParkingFunctions.abovePointRank a b N P.1 P.2} \
      {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
        ParkingFunctions.abovePointRank a b N Q.1 Q.2}
      = {u ∈ northSteps y | u = P} := by
  ext u
  simp only [mem_sdiff, mem_filter, not_and, not_le]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨⟨hu, huP⟩, hnot⟩ := h
    have hQu := hnot hu
    have hsw := (mem_sweptRegion_of_mem_northSteps hy hu).1
    have htype := (mem_northSteps_iff_eventType hsw).1 hu
    have hge := hadj.le_of_lt hsw (by rcases htype with h | h <;> simp [h])
      (by rcases htype with h | h <;> simp [h]) hQu
    obtain ⟨h1, h2⟩ := abovePointRank_injOn (b := b) ha hN
      (le_of_lt (mem_northSteps_iff.1 hu).1) (mem_sweptRegion.1 hadj.2.1).1
      (le_antisymm huP hge)
    exact ⟨hu, Prod.ext h1 h2⟩
  · obtain ⟨hu, rfl⟩ := h
    exact ⟨⟨hu, le_rfl⟩, fun _ => hadj.2.2.1⟩

/-- **The north steps whose head is newly outranked are exactly those with head `P`.** The head of a
north step is a swept point of event type `A` or `C` (`HJO.Paths.isSweepHead_iff_eventType`), and
its rank is that of the foot plus the window (`HJO.Paths.abovePointRank_succ`); the gap clause and
injectivity then identify that head with `P`. -/
private theorem sdiff_heads {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a) (hN : 0 < N)
    {Q P : ℕ × ℕ} (hadj : EventRankAdjacent a b N y Q P) :
    {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N ≤
        ParkingFunctions.abovePointRank a b N P.1 P.2} \
      {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N ≤
        ParkingFunctions.abovePointRank a b N Q.1 Q.2}
      = {u ∈ northSteps y | (u.1, u.2 + 1) = P} := by
  ext u
  simp only [mem_sdiff, mem_filter, not_and, not_le]
  have hsucc : ∀ v : ℕ × ℕ, ParkingFunctions.abovePointRank a b N v.1 (v.2 + 1) =
      ParkingFunctions.abovePointRank a b N v.1 v.2 + attackWindow a N :=
    fun v => abovePointRank_succ a b N v.1 v.2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨⟨hu, huP⟩, hnot⟩ := h
    have hQu := hnot hu
    have hsw := (mem_sweptRegion_of_mem_northSteps hy hu).2
    have htype := (isSweepHead_iff_eventType hy hsw).1 ⟨u, hu, rfl⟩
    have hge : ParkingFunctions.abovePointRank a b N P.1 P.2 ≤
        ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) :=
      hadj.le_of_lt hsw (by rcases htype with h | h <;> simp [h])
        (by rcases htype with h | h <;> simp [h]) (by rw [hsucc u]; exact hQu)
    have heq : ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) =
        ParkingFunctions.abovePointRank a b N P.1 P.2 := by
      rw [hsucc u] at hge ⊢
      omega
    obtain ⟨h1, h2⟩ := abovePointRank_injOn (b := b) ha hN
      (le_of_lt (mem_northSteps_iff.1 hu).1) (mem_sweptRegion.1 hadj.2.1).1 heq
    exact ⟨hu, Prod.ext h1 h2⟩
  · obtain ⟨hu, hhead⟩ := h
    have h1 : P.1 = u.1 := by rw [← hhead]
    have h2 : P.2 = u.2 + 1 := by rw [← hhead]
    have hP : ParkingFunctions.abovePointRank a b N P.1 P.2 =
        ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N := by
      rw [h1, h2, hsucc u]
    refine ⟨⟨hu, hP.ge⟩, fun _ => ?_⟩
    have h2 := hadj.2.2.1
    rwa [hP] at h2

/-! ### The computation -/

/-- **The word position advances by the number of north steps beginning at `P` plus the number
ending at `P`.** Both summands of `HJO.Paths.wordPosition` are monotone in the rank, and between
two event-rank-adjacent points each gains exactly the set computed by `sdiff_feet` and
`sdiff_heads`. The two indicators are `0` or `1`, and `HJO.Paths.mem_northSteps_iff_eventType`
and `HJO.Paths.isSweepHead_iff_eventType` read them off the event type at `P`, which is what the
two corollaries below do. -/
theorem wordPosition_eq_of_eventRankAdjacent {y : Heights a b N} (hy : IsAboveDiagonal y)
    (ha : 0 < a) (hN : 0 < N) {Q P : ℕ × ℕ} (hadj : EventRankAdjacent a b N y Q P) :
    wordPosition y P = wordPosition y Q + #{u ∈ northSteps y | u = P}
      + #{u ∈ northSteps y | (u.1, u.2 + 1) = P} := by
  have hlt := hadj.2.2.1
  have hsubF : {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
        ParkingFunctions.abovePointRank a b N Q.1 Q.2} ⊆
      {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
        ParkingFunctions.abovePointRank a b N P.1 P.2} :=
    monotone_filter_right _ fun u _ hu => hu.trans hlt.le
  have hsubH : {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 +
        attackWindow a N ≤ ParkingFunctions.abovePointRank a b N Q.1 Q.2} ⊆
      {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 +
        attackWindow a N ≤ ParkingFunctions.abovePointRank a b N P.1 P.2} :=
    monotone_filter_right _ fun u _ hu => hu.trans hlt.le
  have hF := card_sdiff_add_card_eq_card hsubF
  have hH := card_sdiff_add_card_eq_card hsubH
  rw [sdiff_feet hy ha hN hadj] at hF
  rw [sdiff_heads hy ha hN hadj] at hH
  simp only [wordPosition]
  omega

/-- **The word position entering an event.** `HJO.Paths.wordPosition_of_rankAdjacent`: between two
rank-consecutive points of `Sw(P̂)` the position advances by `2` at a type-`C` event, not at all at
types `D` and `E`, and by `1` at types `A` and `B`. -/
@[hjo "lem_sweep_position_step"]
theorem wordPosition_of_rankAdjacent {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a)
    (hN : 0 < N) {Q P : ℕ × ℕ} (hadj : RankAdjacent a b N y Q P) :
    wordPosition y P = wordPosition y Q +
      if eventType y P = EventType.C then 2
      else if eventType y P = EventType.D ∨ eventType y P = EventType.E then 0 else 1 := by
  have key := wordPosition_eq_of_eventRankAdjacent hy ha hN hadj.eventRankAdjacent
  have hfoot := mem_northSteps_iff_eventType (y := y) (P := P) hadj.2.1
  have hhead := isSweepHead_iff_eventType hy hadj.2.1
  cases hev : eventType y P with
  | A =>
    rw [card_feet_of_notMem fun h => by simpa [hev] using hfoot.1 h,
      card_heads_of_isSweepHead (hhead.2 (Or.inl hev))] at key
    simp only [reduceCtorEq, or_self, reduceIte]
    omega
  | B =>
    rw [card_feet_of_mem (hfoot.2 (Or.inl hev)),
      card_heads_of_not_isSweepHead fun h => by simpa [hev] using hhead.1 h] at key
    simp only [reduceCtorEq, or_self, reduceIte]
    omega
  | C =>
    rw [card_feet_of_mem (hfoot.2 (Or.inr hev)),
      card_heads_of_isSweepHead (hhead.2 (Or.inr hev))] at key
    simp only [reduceIte]
    omega
  | D =>
    rw [card_feet_of_notMem fun h => by simpa [hev] using hfoot.1 h,
      card_heads_of_not_isSweepHead fun h => by simpa [hev] using hhead.1 h] at key
    simp only [reduceCtorEq, true_or, reduceIte]
    omega
  | E =>
    rw [card_feet_of_notMem fun h => by simpa [hev] using hfoot.1 h,
      card_heads_of_not_isSweepHead fun h => by simpa [hev] using hhead.1 h] at key
    simp only [reduceCtorEq, or_true, reduceIte]
    omega

/-- **The word position between consecutive events.** `HJO.Paths.wordPosition_of_eventRankAdjacent`:
between two consecutive points of `Sw(P̂)` of event type `A`, `B` or `C` the position advances by
`2` at a type-`C` event and by `1` otherwise.

The direct argument sums `HJO.Paths.wordPosition_of_rankAdjacent` over the type-`D` and type-`E`
points in between; here the same computation runs once, because those points are never counted —
every foot and every head of a north step is an event. -/
@[hjo "lem_sweep_position_gap"]
theorem wordPosition_of_eventRankAdjacent {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a)
    (hN : 0 < N) {Q P : ℕ × ℕ} (hadj : EventRankAdjacent a b N y Q P)
    (hD : eventType y P ≠ EventType.D) (hE : eventType y P ≠ EventType.E) :
    wordPosition y P = wordPosition y Q + if eventType y P = EventType.C then 2 else 1 := by
  have key := wordPosition_eq_of_eventRankAdjacent hy ha hN hadj
  have hfoot := mem_northSteps_iff_eventType (y := y) (P := P) hadj.2.1
  have hhead := isSweepHead_iff_eventType hy hadj.2.1
  cases hev : eventType y P with
  | A =>
    rw [card_feet_of_notMem fun h => by simpa [hev] using hfoot.1 h,
      card_heads_of_isSweepHead (hhead.2 (Or.inl hev))] at key
    simp only [reduceCtorEq, reduceIte]
    omega
  | B =>
    rw [card_feet_of_mem (hfoot.2 (Or.inl hev)),
      card_heads_of_not_isSweepHead fun h => by simpa [hev] using hhead.1 h] at key
    simp only [reduceCtorEq, reduceIte]
    omega
  | C =>
    rw [card_feet_of_mem (hfoot.2 (Or.inr hev)),
      card_heads_of_isSweepHead (hhead.2 (Or.inr hev))] at key
    simp only [reduceIte]
    omega
  | D => exact absurd hev hD
  | E => exact absurd hev hE

end HJO.Paths
