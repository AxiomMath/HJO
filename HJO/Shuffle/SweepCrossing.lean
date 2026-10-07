/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepEventTypes
public meta import HJO.Attr

/-! # A pair of steps crossed by one level line: where it is seen, and that both are still there

The hook-counting half of
`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv` pairs an east
step with a north step whenever some level line crosses both, and reads the pair off at a single
swept point: the point revealing whichever of the two the sweep reaches *later*. Three facts make
that legitimate, and they are what this file carries.

* The two revealing points are distinct and both swept, so "the later step" is unambiguous, and the
  event type at each is one of two possibilities.
* The step revealed later does not lose the other one: the level line through the later revealing
  point still crosses the earlier-revealed step.
* In the case where the east step is revealed later, "still crossed" is membership in
  `HJO.Paths.liveSteps` at that point, which is the form every consumer wants.

## Main results

* `HJO.Paths.mem_liveSteps_eastLeft_of_levelCrosses`.
* `HJO.Paths.revealPoint_rank_ne_and_eventType`.
* `HJO.Paths.levelCrosses_other_of_reveal`.

## Implementation notes

### Crossing is an interval condition, and that is the whole mechanism

By `HJO.Paths.LevelCrosses` a step is crossed by the level lines of exactly the ranks in the
half-open interval between the ranks of its two endpoints, and by `HJO.Paths.revealPoint`
the *upper* end of that interval is the rank of the step's revealing point — the head for a north
step, the left endpoint for an east step, those being the ends the descending sweep meets first. Two
steps are crossed by a common line exactly when their intervals meet, and two meeting half-open
intervals with upper ends `α` and `β` contain every rank just below `min(α, β)`. So the
earlier-revealed step is still crossed at the later one's revealing rank. Both halves of
`HJO.Paths.levelCrosses_other_of_reveal` are that one observation, read once in each direction.

### Which hypotheses are not needed

`HJO.Paths.mem_liveSteps_eastLeft_of_levelCrosses` is usually stated with `0 ≤ s ≤ aN - 1`,
with the north
step to the right of the east step (`s + 1 ≤ c`), and with the path above-diagonal. None of the
three is used: the argument is four comparisons of ranks and does not know where the two segments
sit relative to one another, nor that the ambient path is above-diagonal — exactly as for
`HJO.Paths.levelCrosses_east_of_levelCrosses_head`, whose own docstring records the same three
droppings. What *is* needed is `u ∈ HJO.Paths.northSteps y`, which supplies `0 < a` and `0 < N`
through the column bound, and `0 < b`, which is what makes the rank *fall* along an east step so
that the left endpoint is the one of larger rank. At `b = 0` the rank rises along an east step, the
revealing point of `HJO.Paths.revealPoint` is the wrong end, and the statement is false; so `0 < b`
is live and is carried.

`HJO.Paths.revealPoint_rank_ne_and_eventType` does keep `s + 1 ≤ u.1`, because that is what forces
the two revealing points apart: without it the east step and the north step may share a column and
the two points can coincide, and then "the later of the two steps" names nothing.

### What "exactly one point" is here

Informally, there is exactly one `P ∈ Sw(P̂)` at which the later step is revealed.
`HJO.Paths.revealPoint` is a *function* of the step, so existence and uniqueness of that point are
carried by the type and nothing is left to prove; the content of the lemma is that both candidate
points are swept, that their ranks differ — so that "later" picks out one of them — and the event
type dichotomy at each. That is what is stated.

## References

A. Mellit, *Toric braids and
`(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### The rank falls along an east step -/

/-- **The rank falls along an east step.** Moving right by one changes the rank by
`1 - b(aN+1)N`, which is negative as soon as the rectangle has a column and a row: `(aN+1)N ≥ 2`
there, so `b(aN+1)N ≥ 2 > 1`. This is why `HJO.Paths.revealPoint` reveals an east step at its *left*
endpoint — that is the end of larger rank, hence the one the descending sweep meets first. -/
theorem abovePointRank_eastRight_lt_eastLeft (y : Heights a b N) (s : ℕ) (hb : 0 < b)
    (h0 : 0 < a * N) :
    ParkingFunctions.abovePointRank a b N (eastRight y s).1 (eastRight y s).2 <
      ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2 := by
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have h1 : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
  have h2 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have h3 : (1 : ℤ) ≤ (a : ℤ) * N := by exact_mod_cast h0
  have hM2 : (2 : ℤ) ≤ ((a : ℤ) * N + 1) * N := by nlinarith
  have hMb : (2 : ℤ) ≤ ((a : ℤ) * N + 1) * N * b := by nlinarith
  simp only [eastLeft, eastRight, ParkingFunctions.abovePointRank]
  push_cast
  nlinarith

/-! ### The north step stays live at the east step's revealing point -/

/-- **A north step crossed together with an east step is live at that step's left endpoint**, when
the left endpoint is outranked by the north step's head. This is
`HJO.Paths.mem_liveSteps_eastLeft_of_levelCrosses`.

The four comparisons: crossing the east step puts `η₀` strictly below the left endpoint, because the
rank falls along an east step (`HJO.Paths.abovePointRank_eastRight_lt_eastLeft`); crossing the north
step puts its foot weakly below `η₀`; so the foot is weakly below the left endpoint, which the
hypothesis puts strictly below the head. That is the half-open window of `HJO.Paths.liveSteps`, read
through `HJO.Paths.mem_liveSteps_iff_levelCrosses`.

Three of the hypotheses are not carried — `s ≤ aN - 1`, `s + 1 ≤ c`, and the path being
above-diagonal — because none is used; see the module docstring. `0 < b` is carried and is not
decoration: it is what makes the rank fall along an east step at all. -/
@[hjo "lem_sweep_crossing_north_live"]
theorem mem_liveSteps_eastLeft_of_levelCrosses {y : Heights a b N} (hb : 0 < b) {s : ℕ}
    {u : ℕ × ℕ} (hu : u ∈ northSteps y) {η₀ : ℤ}
    (hE : LevelCrosses a b N η₀ (eastLeft y s) (eastRight y s))
    (hU : LevelCrosses a b N η₀ u (u.1, u.2 + 1))
    (hlt : ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2 <
      ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1)) :
    u ∈ liveSteps y (eastLeft y s) := by
  have h0 : 0 < a * N := lt_of_le_of_lt (Nat.zero_le _) (mem_northSteps_iff.1 hu).1
  have ha : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have hrkR := abovePointRank_eastRight_lt_eastLeft y s hb h0
  have hηL : η₀ < ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2 := by
    have h := hE.2
    rwa [max_eq_left hrkR.le] at h
  have hFη : ParkingFunctions.abovePointRank a b N u.1 u.2 ≤ η₀ :=
    ((levelCrosses_north_iff ha hN).1 hU).1
  refine (mem_liveSteps_iff_levelCrosses hu).2 ((levelCrosses_north_iff ha hN).2 ⟨?_, ?_⟩)
  · omega
  · rw [← abovePointRank_succ]
    exact hlt

/-! ### Where the pair is read off -/

/-- **The two revealing points are distinct and swept, and each carries one of two event types.**
`HJO.Paths.revealPoint_rank_ne_and_eventType`: for an east step at `s` and a north step `u` to its
right, the sweep reveals the east step at `HJO.Paths.eastLeft y s` and the north step at its head,
both of those points are swept, their ranks differ — so the sweep meets one strictly before the
other and "the later of the two steps" names exactly one of them — and the event type is `A` or `D`
at the east step's point and `A` or `C` at the north step's.

Existence and uniqueness of the revealing point need no proof here, `HJO.Paths.revealPoint` being a
function of the step; the two membership halves are `HJO.Paths.eventType_top_of_column` and
`HJO.Paths.eventType_head_of_mem_northSteps`, and the distinctness is rank injectivity on the strip
together with `s < u.1`. -/
@[hjo "lem_sweep_crossing_event"]
theorem revealPoint_rank_ne_and_eventType {y : Heights a b N} (hy : IsAboveDiagonal y) {s : ℕ}
    (hs : s < a * N) {u : ℕ × ℕ} (hu : u ∈ northSteps y) (hsu : s + 1 ≤ u.1) :
    ((s, ht y (s + 1)) ∈ sweptRegion y ∧ (u.1, u.2 + 1) ∈ sweptRegion y) ∧
      ParkingFunctions.abovePointRank a b N s (ht y (s + 1)) ≠
        ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) ∧
      (eventType y (s, ht y (s + 1)) = EventType.A ∨
        eventType y (s, ht y (s + 1)) = EventType.D) ∧
      (eventType y (u.1, u.2 + 1) = EventType.A ∨
        eventType y (u.1, u.2 + 1) = EventType.C) := by
  have ha : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at hs
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at hs
  obtain ⟨hc, -, -⟩ := mem_northSteps_iff.1 hu
  obtain ⟨hmemE, htypeE⟩ := eventType_top_of_column hy hs
  obtain ⟨hmemN, htypeN⟩ := eventType_head_of_mem_northSteps hy hu
  refine ⟨⟨hmemE, hmemN⟩, ?_, ?_, ?_⟩
  · intro hEq
    obtain ⟨e1, -⟩ := abovePointRank_injOn (b := b) ha hN (le_of_lt hs) (le_of_lt hc) hEq
    omega
  · rw [htypeE]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [htypeN]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl

/-! ### The other step is still crossed there -/

/-- **The step revealed earlier is still crossed at the later one's revealing rank.** This is
`HJO.Paths.levelCrosses_other_of_reveal`, as the pair of implications the case split produces.

If the east step is revealed later — its left endpoint outranked by the north step's head — the
north step is still crossed there, and being a north step that reads as membership in
`HJO.Paths.liveSteps`: this is `HJO.Paths.mem_liveSteps_eastLeft_of_levelCrosses`. If the north step
is revealed later, the east step is still crossed at the head's rank: this is
`HJO.Paths.levelCrosses_east_of_levelCrosses_head`. Both are the interval observation of the module
docstring, and neither needs the path to be above-diagonal. -/
@[hjo "lem_sweep_crossing_transport"]
theorem levelCrosses_other_of_reveal {y : Heights a b N} (hb : 0 < b) {s : ℕ} {u : ℕ × ℕ}
    (hu : u ∈ northSteps y) {η₀ : ℤ}
    (hE : LevelCrosses a b N η₀ (eastLeft y s) (eastRight y s))
    (hU : LevelCrosses a b N η₀ u (u.1, u.2 + 1)) :
    (ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2 <
        ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) →
      u ∈ liveSteps y (eastLeft y s)) ∧
    (ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) <
        ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2 →
      LevelCrosses a b N (ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1))
        (eastLeft y s) (eastRight y s)) :=
  ⟨fun hlt => mem_liveSteps_eastLeft_of_levelCrosses hb hu hE hU hlt,
    fun hlt => levelCrosses_east_of_levelCrosses_head hu hE hU hlt⟩

end HJO.Paths
