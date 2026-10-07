/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepGeometry
public meta import HJO.Attr

/-! # What the sweep reads at a swept point: feet, heads, the area, and the width step

The sweep process descends a level line of the above-diagonal rank across the rectangle and
registers an event at every point of the swept region. This file identifies the five event types
geometrically and computes the two numbers `HJO.Mellit.sweepWord_mem_piece_zero` and
`HJO.Mellit.sweepComputes` read off that identification: how many points carry the event type `E`,
and how the width `k_{P̂}` changes between two swept points adjacent in the rank order.

## Main results

* `HJO.Paths.mem_northSteps_iff_eventType`: a swept point is the foot of a north step exactly at
  the event types `B` and `C` — `HJO.Paths.mem_northSteps_iff_eventType`.
* `HJO.Paths.isSweepHead_iff_eventType`: a swept point is the head of a north step exactly at the
  event types `A` and `C` — `HJO.Paths.isSweepHead_iff_eventType`.
* `HJO.Paths.card_filter_eventType_E`: the number of swept points of event type `E` is the area
  `â(P̂)` above the path — `HJO.Paths.card_filter_eventType_E`.
* `HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent`: between two swept points adjacent in the
  rank order the width rises by `1` at a type-`A` event, falls by `1` at a type-`B` event and is
  unchanged otherwise — `HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent`.
* `HJO.Paths.mem_northSteps_zero`, `HJO.Paths.abovePointRank_lt_of_mem_northSteps`: the origin is
  a north step and is strictly outranked by every other one, so it is the first north step in the
  rank-order listing — `HJO.Paths.abovePointRank_lt_of_mem_northSteps`.

## Implementation notes

### Adjacency in the rank order, instead of a listing

`HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent` is naturally stated about `P_1, …, P_M`, the
listing of `Sw(P̂)` in strictly decreasing rank, and about a consecutive pair `(P_r, P_{r+1})`.
Being consecutive in that
listing *is* the hypothesis `HJO.Paths.RankAdjacent` below: `rk̂(P_{r+1}) < rk̂(P_r)` with no point
of the swept region ranked strictly between. So the statement here quantifies over the pair directly
and never forms the listing, which is how every consumer holds it — `HJO.Mellit.sortByRank` sorts
increasingly and its consecutive pairs are exactly the rank-adjacent pairs of the set. Nothing is
lost: the listing is determined by the rank order, the rank being injective on the strip
(`HJO.Paths.abovePointRank_injOn`).

### The width as a difference of two counts

`k_{P̂}(P) = #{u : rk̂(u) ≤ rk̂(P) < rk̂(u) + ω}` is the number of feet the line has passed minus
the number of heads it has passed, the head of a north step outranking its foot by exactly `ω`
(`HJO.Paths.abovePointRank_succ`). The whole of
`HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent` is then the observation that between two
rank-adjacent swept points at most one foot and at most one head can be passed, because both ends of
a north step are themselves swept points (`HJO.Paths.mem_sweptRegion_of_mem_northSteps`) and the
rank is injective. That is carried out here as a pair of set differences of `HJO.Paths.liveSteps`,
which avoids truncated subtraction: the identity `#(s \ t) + #t = #(t \ s) + #s` is
`Finset.card_sdiff_add_card`, read twice.

### The area count

`HJO.Paths.card_filter_eventType_E` is a fibrewise count over the abscissa. Above a fixed `x` the
type-`E` points of `Sw(P̂)` are the ordinates `⌈bx/a⌉ ≤ k < ŷ_x`, of which there are `ŷ_x - ⌈bx/a⌉`;
summing over `0 ≤ x ≤ aN` and discarding the two vanishing end terms — `ŷ_0 = 0` at `x = 0` and
`ŷ_{aN} = bN = ⌈b·aN/a⌉` at `x = aN` — gives `HJO.Paths.aboveArea`. The constraint `k ≤ ŷ⁺_x` of
`HJO.Paths.sweptRegion` is implied by `k < ŷ_x` and the monotonicity of the heights, so it
contributes nothing.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section "The sweep process", for Lemmas
`HJO.Paths.mem_northSteps_iff_eventType`, `HJO.Paths.isSweepHead_iff_eventType`,
`HJO.Paths.card_filter_eventType_E`, `HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent` and
`HJO.Paths.abovePointRank_lt_of_mem_northSteps`, using `HJO.Paths.IsAboveDiagonal`,
`HJO.Paths.northSteps`, `HJO.Paths.aboveArea`, `HJO.ParkingFunctions.abovePointRank`,
`HJO.Paths.sweptRegion`, `HJO.Paths.liveSteps`, `HJO.Paths.sweepWidth` and `HJO.Paths.eventType`.
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### Feet and heads of north steps, read off the event type -/

/-- **A swept point is the foot of a north step exactly at the event types `B` and `C`.** Both of
those types ask the outgoing letter at `P` to be `N` together with `P` being on the path, and
`HJO.Paths.northSteps` asks for exactly that pair of conditions. -/
@[hjo "lem_sweep_event_foot"]
theorem mem_northSteps_iff_eventType {y : Heights a b N} {P : ℕ × ℕ} (hP : P ∈ sweptRegion y) :
    P ∈ northSteps y ↔ eventType y P = EventType.B ∨ eventType y P = EventType.C := by
  obtain ⟨hx, -, -⟩ := mem_sweptRegion.1 hP
  rw [mem_northSteps_iff, eventType]
  split_ifs <;> simp_all

/-- The swept point `P` is the head of a north step of the path: `P = u + (0,1)` for some north step
`u`, each north step being named by its foot. This is the condition
`HJO.Paths.isSweepHead_iff_eventType` reads off the event type, and the one the second count of
`HJO.Paths.sweepWidth` moves by. -/
def IsSweepHead (y : Heights a b N) (P : ℕ × ℕ) : Prop :=
  ∃ u ∈ northSteps y, (u.1, u.2 + 1) = P

instance {y : Heights a b N} {P : ℕ × ℕ} : Decidable (IsSweepHead y P) := by
  unfold IsSweepHead; infer_instance

/-- **A swept point is the head of a north step exactly at the event types `A` and `C`.** Both of
those types ask the incoming letter at `P` to be `N`, which on the swept region is `ŷ_x < y`.

The one place the hypotheses bite is the column `x = aN`, where `ŷ⁺_{aN} = bN = ŷ_{aN}`, so a swept
point there has `y ≤ ŷ_x` and is no head; that is where `HJO.Paths.IsAboveDiagonal` is read. -/
@[hjo "lem_sweep_event_head"]
theorem isSweepHead_iff_eventType {y : Heights a b N} (hy : IsAboveDiagonal y) {P : ℕ × ℕ}
    (hP : P ∈ sweptRegion y) :
    IsSweepHead y P ↔ eventType y P = EventType.A ∨ eventType y P = EventType.C := by
  obtain ⟨hx, -, hup⟩ := mem_sweptRegion.1 hP
  have hlt : ht y P.1 < P.2 ↔ eventType y P = EventType.A ∨ eventType y P = EventType.C := by
    rw [eventType]
    split_ifs <;> simp_all
    omega
  rw [← hlt]
  constructor
  · rintro ⟨u, hu, huP⟩
    obtain ⟨-, h2, -⟩ := mem_northSteps_iff.1 hu
    have h1 : u.1 = P.1 := by simpa using congrArg Prod.fst huP
    have h3 : u.2 + 1 = P.2 := by simpa using congrArg Prod.snd huP
    rw [← h1, ← h3]
    omega
  · intro h
    have hxlt : P.1 < a * N := by
      rcases Nat.lt_or_ge P.1 (a * N) with hlt' | hge
      · exact hlt'
      · have hx0 : P.1 = a * N := le_antisymm hx hge
        rw [hx0, ht_of_gt y (by omega)] at hup
        rw [hx0, hy.2.1] at h
        omega
    refine ⟨(P.1, P.2 - 1), mem_northSteps_iff.2 ⟨hxlt, ?_, ?_⟩, ?_⟩
    · change ht y P.1 ≤ P.2 - 1
      omega
    · change P.2 - 1 < ht y (P.1 + 1)
      omega
    · rw [Prod.ext_iff]
      exact ⟨rfl, by omega⟩

/-! ### The number of type-`E` events -/

/-- **The number of swept points of event type `E` is the area above the path.**
`#{P ∈ Sw(P̂) : ev_{P̂}(P) = E} = â(P̂)`.

The type-`E` points above a fixed abscissa `x` are the ordinates `⌈bx/a⌉ ≤ k < ŷ_x`, the upper
constraint `k ≤ ŷ⁺_x` of the swept region being implied by `k < ŷ_x` and monotonicity; the two end
columns contribute nothing, `ŷ_0 = 0` and `ŷ_{aN} = bN = ⌈b·aN/a⌉`, which is what leaves the sum
over `1 ≤ x < aN` that `HJO.Paths.aboveArea` is. -/
@[hjo "lem_sweep_event_area"]
theorem card_filter_eventType_E {y : Heights a b N} (hy : IsAboveDiagonal y) :
    #{P ∈ sweptRegion y | eventType y P = EventType.E} = aboveArea y := by
  rcases Nat.eq_zero_or_pos (a * N) with h0 | h0
  · have hempty : {P ∈ sweptRegion y | eventType y P = EventType.E} = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun {P} hP hev => ?_
      obtain ⟨hx, -, -⟩ := mem_sweptRegion.1 hP
      have hx0 : P.1 = 0 := by omega
      rw [eventType_eq_E_iff, hx0, hy.1] at hev
      omega
    rw [hempty, aboveArea, Finset.card_empty, h0]
    simp
  have ha : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have hfib : ∀ x ∈ range (a * N + 1),
      #{P ∈ {P ∈ sweptRegion y | eventType y P = EventType.E} | P.1 = x}
        = ht y x - b * x ⌈/⌉ a := by
    intro x hxr
    rw [mem_range] at hxr
    have hset : {P ∈ {P ∈ sweptRegion y | eventType y P = EventType.E} | P.1 = x}
        = (Finset.Ico (b * x ⌈/⌉ a) (ht y x)).image fun k => (x, k) := by
      ext P
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico, mem_sweptRegion,
        eventType_eq_E_iff]
      constructor
      · rintro ⟨⟨⟨-, hdiag, -⟩, hev⟩, hx⟩
        refine ⟨P.2, ⟨?_, ?_⟩, ?_⟩
        · rw [← hx]; exact (_root_.ceilDiv_le_iff_le_mul ha).2 hdiag
        · rw [← hx]; exact hev
        · rw [Prod.ext_iff]; exact ⟨hx.symm, rfl⟩
      · rintro ⟨k, ⟨hk1, hk2⟩, hP⟩
        have hP1 : P.1 = x := by simpa using (congrArg Prod.fst hP).symm
        have hP2 : P.2 = k := by simpa using (congrArg Prod.snd hP).symm
        rw [hP1, hP2]
        exact ⟨⟨⟨by omega, (_root_.ceilDiv_le_iff_le_mul ha).1 hk1,
          hk2.le.trans (ht_mono hy.2.2.1 (Nat.le_succ x))⟩, hk2⟩, rfl⟩
    rw [hset, Finset.card_image_of_injective _ (fun k k' h => by
      simpa using (congrArg Prod.snd h)), Nat.card_Ico]
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
      (t := range (a * N + 1)) (fun P hP => mem_range.2 (by
        have := (mem_sweptRegion.1 (Finset.mem_filter.1 hP).1).1; omega)),
    Finset.sum_congr rfl hfib]
  have hzero : ht y 0 - b * 0 ⌈/⌉ a = 0 := by rw [hy.1]; simp
  have htop : ht y (a * N) - b * (a * N) ⌈/⌉ a = 0 := by
    have := Nat.mul_sub_div_add_mul_ceilDiv (a := a) (b := b) (N := N) (r := a * N) ha le_rfl
    rw [hy.2.1]
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_div, Nat.zero_add] at this
    omega
  rw [Finset.range_eq_Ico, Finset.sum_Ico_succ_top (Nat.zero_le _), htop, Nat.add_zero,
    Finset.sum_eq_sum_Ico_succ_bot h0, hzero, Nat.zero_add, aboveArea]

/-! ### The width between two rank-adjacent swept points -/

/-- Two points of the swept region are **adjacent in the rank order**: `Q` is outranked by `P` and
no swept point is ranked strictly between them. This is being consecutive in the
listing `P_1, …, P_M` of `Sw(P̂)` by strictly decreasing rank, with `P = P_r` and `Q = P_{r+1}`; the
listing being determined by the rank order, nothing is lost by quantifying over the pair. -/
def RankAdjacent (a b N : ℕ) (y : Heights a b N) (Q P : ℕ × ℕ) : Prop :=
  Q ∈ sweptRegion y ∧ P ∈ sweptRegion y ∧
    ParkingFunctions.abovePointRank a b N Q.1 Q.2 <
      ParkingFunctions.abovePointRank a b N P.1 P.2 ∧
    ∀ R ∈ sweptRegion y,
      ¬(ParkingFunctions.abovePointRank a b N Q.1 Q.2 <
          ParkingFunctions.abovePointRank a b N R.1 R.2 ∧
        ParkingFunctions.abovePointRank a b N R.1 R.2 <
          ParkingFunctions.abovePointRank a b N P.1 P.2)

/-- A swept point ranked above the lower end of a rank-adjacent pair is ranked at or above the upper
end: the contrapositive form of the gap clause of `HJO.Paths.RankAdjacent`, which is how both
set-difference computations below read it. -/
private theorem RankAdjacent.le_of_lt {y : Heights a b N} {Q P : ℕ × ℕ}
    (hadj : RankAdjacent a b N y Q P) {R : ℕ × ℕ} (hR : R ∈ sweptRegion y)
    (h : ParkingFunctions.abovePointRank a b N Q.1 Q.2 <
      ParkingFunctions.abovePointRank a b N R.1 R.2) :
    ParkingFunctions.abovePointRank a b N P.1 P.2 ≤
      ParkingFunctions.abovePointRank a b N R.1 R.2 :=
  not_lt.1 fun hcon => hadj.2.2.2 R hR ⟨h, hcon⟩

/-- Passing from the lower to the upper point of a rank-adjacent pair, the live north steps that are
**lost** are exactly those whose foot is the upper point itself: a step live at `P` and not at `Q`
has its foot ranked in the half-open interval `(rk̂ Q, rk̂ P]`, which by rank-adjacency and
injectivity of the rank forces the foot to be `P`. -/
private theorem sdiff_liveSteps_left {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a)
    (hN : 0 < N) {Q P : ℕ × ℕ} (hadj : RankAdjacent a b N y Q P) :
    liveSteps y P \ liveSteps y Q = {u ∈ northSteps y | u = P} := by
  have hlt := hadj.2.2.1
  have hP := hadj.2.1
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
  have hωz : (0 : ℤ) < (attackWindow a N : ℤ) := by exact_mod_cast hω
  ext u
  simp only [Finset.mem_sdiff, liveSteps, Finset.mem_filter, not_and, not_lt]
  constructor
  · rintro ⟨⟨hu, hu1, hu2⟩, hnot⟩
    refine ⟨hu, ?_⟩
    have hQu : ParkingFunctions.abovePointRank a b N Q.1 Q.2 <
        ParkingFunctions.abovePointRank a b N u.1 u.2 := by
      by_contra hcon
      have := hnot hu (not_lt.1 hcon)
      omega
    have heq : ParkingFunctions.abovePointRank a b N u.1 u.2 =
        ParkingFunctions.abovePointRank a b N P.1 P.2 :=
      le_antisymm hu1 (hadj.le_of_lt (mem_sweptRegion_of_mem_northSteps hy hu).1 hQu)
    obtain ⟨h1, h2⟩ := abovePointRank_injOn (b := b) ha hN
      (le_of_lt (mem_northSteps_iff.1 hu).1) (mem_sweptRegion.1 hP).1 heq
    rw [Prod.ext_iff]
    exact ⟨h1, h2⟩
  · rintro ⟨hu, rfl⟩
    exact ⟨⟨hu, le_rfl, by omega⟩, fun _ h => absurd h (by omega)⟩

/-- Passing from the lower to the upper point of a rank-adjacent pair, the live north steps that are
**gained** are exactly those whose head is the upper point itself: a step live at `Q` and not at `P`
has its head ranked in `(rk̂ Q, rk̂ P]`, and `HJO.Paths.abovePointRank_succ` turns the window
condition of `HJO.Paths.liveSteps` into a statement about that head. -/
private theorem sdiff_liveSteps_right {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a)
    (hN : 0 < N) {Q P : ℕ × ℕ} (hadj : RankAdjacent a b N y Q P) :
    liveSteps y Q \ liveSteps y P = {u ∈ northSteps y | (u.1, u.2 + 1) = P} := by
  have hlt := hadj.2.2.1
  have hP := hadj.2.1
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
  have hωz : (0 : ℤ) < (attackWindow a N : ℤ) := by exact_mod_cast hω
  ext u
  simp only [Finset.mem_sdiff, liveSteps, Finset.mem_filter, not_and, not_lt]
  have hsucc : ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) =
      ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N :=
    abovePointRank_succ a b N u.1 u.2
  have hgapHead : ParkingFunctions.abovePointRank a b N Q.1 Q.2 <
        ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) →
      u ∈ northSteps y →
      ParkingFunctions.abovePointRank a b N P.1 P.2 ≤
        ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) := fun h hu =>
    hadj.le_of_lt (mem_sweptRegion_of_mem_northSteps hy hu).2 h
  constructor
  · rintro ⟨⟨hu, hu1, hu2⟩, hnot⟩
    refine ⟨hu, ?_⟩
    have hhead : ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N ≤
        ParkingFunctions.abovePointRank a b N P.1 P.2 := hnot hu (by omega)
    have hge := hgapHead (by omega) hu
    have heq : ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) =
        ParkingFunctions.abovePointRank a b N P.1 P.2 := by omega
    obtain ⟨h1, h2⟩ := abovePointRank_injOn (b := b) ha hN
      (le_of_lt (mem_northSteps_iff.1 hu).1) (mem_sweptRegion.1 hP).1 heq
    rw [Prod.ext_iff]
    exact ⟨h1, h2⟩
  · rintro ⟨hu, hhead⟩
    have hh1 : u.1 = P.1 := by simpa using congrArg Prod.fst hhead
    have hh2 : u.2 + 1 = P.2 := by simpa using congrArg Prod.snd hhead
    have hPh : ParkingFunctions.abovePointRank a b N P.1 P.2 =
        ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N := by
      rw [← hh1, ← hh2, ← hsucc]
    have hfoot : ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
        ParkingFunctions.abovePointRank a b N Q.1 Q.2 := by
      by_contra hcon
      have := hadj.le_of_lt (mem_sweptRegion_of_mem_northSteps hy hu).1 (not_le.1 hcon)
      omega
    exact ⟨⟨hu, hfoot, by omega⟩, fun _ _ => by omega⟩

/-- **The width changes by `+1`, `-1` or `0` between two rank-adjacent swept points.** With
`P = P_r` and `Q = P_{r+1}` consecutive in the listing of `Sw(P̂)` by decreasing rank,
`k_{P̂}(Q) - k_{P̂}(P)` is `1` at a type-`A` event at `P`, `-1` at a type-`B` event, and `0` at the
three remaining types.

The difference is the number of north steps whose head is `P` minus the number whose foot is `P`,
each of those being `0` or `1` by injectivity of the rank; `HJO.Paths.isSweepHead_iff_eventType` and
`HJO.Paths.mem_northSteps_iff_eventType` then read the two indicators off the event type. -/
@[hjo "lem_sweep_width_change"]
theorem sweepWidth_sub_sweepWidth_of_rankAdjacent {y : Heights a b N} (hy : IsAboveDiagonal y)
    (ha : 0 < a) (hN : 0 < N) {Q P : ℕ × ℕ} (hadj : RankAdjacent a b N y Q P) :
    (sweepWidth y Q : ℤ) - sweepWidth y P =
      if eventType y P = EventType.A then 1
      else if eventType y P = EventType.B then -1 else 0 := by
  have hP := hadj.2.1
  have hbal : #{u ∈ northSteps y | (u.1, u.2 + 1) = P} + sweepWidth y P
      = #{u ∈ northSteps y | u = P} + sweepWidth y Q := by
    rw [sweepWidth, sweepWidth, ← sdiff_liveSteps_left hy ha hN hadj,
      ← sdiff_liveSteps_right hy ha hN hadj, Finset.card_sdiff_add_card,
      Finset.card_sdiff_add_card, Finset.union_comm]
  have hfoot1 : P ∈ northSteps y → #{u ∈ northSteps y | u = P} = 1 := fun h => by
    simp [Finset.filter_eq', h]
  have hfoot0 : P ∉ northSteps y → #{u ∈ northSteps y | u = P} = 0 := fun h => by
    simp [Finset.filter_eq', h]
  have hhead1 : IsSweepHead y P → #{u ∈ northSteps y | (u.1, u.2 + 1) = P} = 1 := by
    rintro ⟨w, hw, hwP⟩
    have hsingle : {u ∈ northSteps y | (u.1, u.2 + 1) = P} = {w} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_singleton]
      refine ⟨fun hv => ?_, fun hv => ?_⟩
      · have hvw := hv.2.trans hwP.symm
        have h1 : v.1 = w.1 := by simpa using congrArg Prod.fst hvw
        have h2 : v.2 = w.2 := by
          have := congrArg Prod.snd hvw
          simp only at this
          omega
        rw [Prod.ext_iff]
        exact ⟨h1, h2⟩
      · rw [hv]; exact ⟨hw, hwP⟩
    rw [hsingle, Finset.card_singleton]
  have hhead0 : ¬IsSweepHead y P → #{u ∈ northSteps y | (u.1, u.2 + 1) = P} = 0 := fun h => by
    rw [Finset.card_eq_zero]
    exact Finset.filter_eq_empty_iff.2 fun {v} hv hvP => h ⟨v, hv, hvP⟩
  have hfoot' := mem_northSteps_iff_eventType (y := y) (P := P) hP
  have hhead' := isSweepHead_iff_eventType hy hP
  cases hev : eventType y P with
  | A =>
    rw [hfoot0 fun h => by simpa [hev] using hfoot'.1 h,
      hhead1 (hhead'.2 (Or.inl hev))] at hbal
    simp only [reduceIte]
    omega
  | B =>
    rw [hfoot1 (hfoot'.2 (Or.inl hev)), hhead0 fun h => by simpa [hev] using hhead'.1 h] at hbal
    simp only [reduceCtorEq, reduceIte]
    omega
  | C =>
    rw [hfoot1 (hfoot'.2 (Or.inr hev)), hhead1 (hhead'.2 (Or.inr hev))] at hbal
    simp only [reduceCtorEq, reduceIte]
    omega
  | D =>
    rw [hfoot0 fun h => by simpa [hev] using hfoot'.1 h,
      hhead0 fun h => by simpa [hev] using hhead'.1 h] at hbal
    simp only [reduceCtorEq, reduceIte]
    omega
  | E =>
    rw [hfoot0 fun h => by simpa [hev] using hfoot'.1 h,
      hhead0 fun h => by simpa [hev] using hhead'.1 h] at hbal
    simp only [reduceCtorEq, reduceIte]
    omega

/-! ### The first north step -/

/-- **The origin is a north step of an above-diagonal path.** The rectangle has a row, so
`ŷ_1 ≥ ⌈b/a⌉ ≥ 1 > 0 = ŷ_0`, and the north step at height `0` sits in column `0`. -/
theorem mem_northSteps_zero {y : Heights a b N} (hy : IsAboveDiagonal y) (hb : 0 < b)
    (hN : 0 < N) : ((0 : ℕ), (0 : ℕ)) ∈ northSteps y := by
  have hbN : 0 < b * N := Nat.mul_pos hb hN
  have haN : 0 < a * N := by
    by_contra hcon
    have h0 : a * N = 0 := by omega
    have htop := hy.2.1
    rw [h0, hy.1] at htop
    omega
  have h1 := hy.2.2.2 1 (by omega)
  refine mem_northSteps_iff.2 ⟨haN, ?_, ?_⟩
  · change ht y 0 ≤ 0
    rw [hy.1]
  · change (0 : ℕ) < ht y 1
    rcases Nat.eq_zero_or_pos (ht y 1) with h | h
    · rw [h, Nat.mul_zero] at h1
      omega
    · exact h

/-- **Every other north step strictly outranks the origin.** A north step `(x, i)` has
`a i ≥ a ŷ_x ≥ b x`, so its rank `(aN+1)N(ai - bx) + x` is nonnegative, and it vanishes only at
`x = 0` and `i = 0`. With `HJO.Paths.mem_northSteps_zero` this gives that the origin is a north
step, and it is the first one in the strictly increasing rank-order listing `u_1, …, u_{bN}`. -/
@[hjo "lem_sweep_first_north_step"]
theorem abovePointRank_lt_of_mem_northSteps {y : Heights a b N} (hy : IsAboveDiagonal y)
    {u : ℕ × ℕ} (hu : u ∈ northSteps y) (hne : u ≠ (0, 0)) :
    ParkingFunctions.abovePointRank a b N 0 0 <
      ParkingFunctions.abovePointRank a b N u.1 u.2 := by
  obtain ⟨h1, h2, -⟩ := mem_northSteps_iff.1 hu
  have ha : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at h1
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at h1
  have hdiag : b * u.1 ≤ a * u.2 :=
    (hy.2.2.2 u.1 (by omega)).trans (Nat.mul_le_mul_left a h2)
  have hdz : (0 : ℤ) ≤ (a : ℤ) * u.2 - (b : ℤ) * u.1 := by
    have hc : ((b * u.1 : ℕ) : ℤ) ≤ ((a * u.2 : ℕ) : ℤ) := Int.ofNat_le.2 hdiag
    push_cast at hc
    linarith
  have hM : (0 : ℤ) < ((a : ℤ) * N + 1) * N := by positivity
  have hX : (0 : ℤ) ≤ (u.1 : ℤ) := Int.natCast_nonneg _
  have hz : ParkingFunctions.abovePointRank a b N 0 0 = 0 := by
    simp [ParkingFunctions.abovePointRank]
  rw [hz, ParkingFunctions.abovePointRank]
  rcases Nat.eq_zero_or_pos u.1 with hx | hx
  · have hu2 : 0 < u.2 := by
      rcases Nat.eq_zero_or_pos u.2 with h | h
      · exact absurd (by rw [Prod.ext_iff]; exact ⟨hx, h⟩) hne
      · exact h
    have ha' : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
    have hu2' : (0 : ℤ) < (u.2 : ℤ) := by exact_mod_cast hu2
    have hx' : ((u.1 : ℕ) : ℤ) = 0 := by exact_mod_cast hx
    have hD : (0 : ℤ) < (a : ℤ) * u.2 - (b : ℤ) * u.1 := by
      rw [hx']
      nlinarith
    nlinarith [mul_pos hM hD]
  · have hx' : (0 : ℤ) < (u.1 : ℤ) := by exact_mod_cast hx
    nlinarith

end HJO.Paths
