/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepCrossing
public import HJO.Shuffle.SweepEventIndex
public import HJO.Shuffle.SweepWidth
public meta import HJO.Attr

/-! # The hook count grouped by sweep events

By `HJO.Paths.aboveHookCount_eq_card_crossingPairs` the above-diagonal hook count `ĥ(P̂)` is the
number of crossed pairs `(e, u)` of an east step and a north step, `e` strictly to the left of `u`,
that some one level line crosses both of — `HJO.Paths.crossingPairs`, each pair named by the
abscissa `s` of its east step and the height `i` of its north step's foot. This file regroups that
count by the swept point at which the sweep *reveals* the later of the two steps, and so proves
`HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount`: `ĥ(P̂)` is the sum of the live
north-step count to the right `a_{P̂}` over the points of type `A` or `D` plus the sum of the live
east-step count to the left `a*_{P̂}` over those of type `A` or `C`.

## Main results

* `HJO.Paths.levelCrosses_eastStep_iff`: a level line crosses an east step exactly on the half-open
  rank interval `[rk̂(R_e), rk̂(L_e))`, the rank falling along an east step.
* `HJO.Paths.exists_levelCrosses_iff_mem_liveSteps`: when the sweep reveals the east step later,
  the pair is crossed exactly when the north step is live at the east step's reveal point — the
  condition `HJO.Paths.sweepRight` counts there.
* `HJO.Paths.exists_levelCrosses_iff_levelCrosses_head`: when it reveals the north step later, the
  pair is crossed exactly when the level line through the north step's head still crosses the east
  step — the condition `HJO.Paths.leftEastCount` counts there.
* `HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount`: the display of
  `HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount`.

## Implementation notes

*The dichotomy is an ordering of two integers and nothing else.* The two reveal points of a crossed
pair are `L_e = HJO.Paths.eastLeft y s` for the east step and the head `(c, i+1)` for the north
step, and their ranks are distinct by `HJO.Paths.revealPoint_rank_ne_and_eventType`, the two points
having distinct abscissas and the rank being injective on the strip. The sweep descends, so the
step revealed *later* is the one whose reveal point has the *smaller* rank, and the pairs split in
two by that comparison — which is what the two `Finset.filter`s below are. A common level line
exists exactly when `max(rk̂(R_e), rk̂(u)) < min(rk̂(L_e), rk̂(u) + ω)`, and splitting on
`rk̂(L_e)` against `rk̂(u) + ω = rk̂(u + (0,1))` collapses that to `u ∈ HJO.Paths.liveSteps y L_e`
in the first case and to `HJO.Paths.LevelCrosses` at the head's rank in the second. So
`HJO.Paths.revealPoint_rank_ne_and_eventType`, `HJO.Paths.levelCrosses_other_of_reveal`,
`HJO.Paths.mem_liveSteps_eastLeft_of_levelCrosses` and
`HJO.Paths.levelCrosses_east_of_levelCrosses_head` are spent here as two `iff`s, and no separate
transport step is needed: the transported step's availability *is* the surviving inequality.

*The first sum is not a sum over the east steps.* Its index set is the type-`A`-or-`D` points,
which by `HJO.Paths.eventType_eq_A_or_D_iff` are the column tops `HJO.Paths.eastLeft y s` for
`s < aN` **and also the corner** `(aN, bN)`, whose outgoing letter is `E` because the guard
`x + 1 ≤ aN` fails there. Rather than reindex the sum to `∑_{s < aN}` and carry the corner as a
correction term, the fibre lemma below is proved at every type-`A`-or-`D` point: over a column top
the fibre is in bijection with what `a_{P̂}` counts, and over the corner both sides are `0` — the
fibre because every crossed pair has `s < aN`, and `a_{P̂}(aN, bN)` by
`HJO.Paths.sweepRight_corner`, no north step having column `≥ aN`. That is the one place where an
off-by-one-term reindexing could hide, and a misstated form of this identity fails by exactly
such a count discrepancy.

*`HJO.Paths.leftEastCount` spells its crossing condition as two rank inequalities*, not through
`HJO.Paths.LevelCrosses`, because along a horizontal segment the rank decreases and the
`min` and `max` change places. `HJO.Paths.levelCrosses_eastStep_iff` is the bridge, and
`HJO.Paths.exists_mem_inter_Ico` is what produces a witnessing level from the two intervals.

*Two hypotheses beyond the path.* `0 < a` and `0 < b` are carried because
`HJO.Paths.aboveHookCount_eq_card_crossingPairs`, this lemma's only other input, carries them; the
degenerate rectangles they exclude have no cell and no step, so both sides vanish there. `N = 0` is
*not* excluded and needs no separate branch: the swept region is then the single point `(0, 0)`,
which is the corner, and the corner branch of the fibre lemma covers it.

## References

The lemma `HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount`, with Definitions
`HJO.Paths.IsAboveDiagonal`, `HJO.Paths.aboveHookCount`, `HJO.Paths.sweptRegion`,
`HJO.Paths.sweepRight`, `HJO.Paths.eventType` and `HJO.Paths.leftEastCount`, and Lemmas
`HJO.Paths.aboveHookCount_eq_card_crossingPairs`, `HJO.Paths.revealPoint_rank_ne_and_eventType`,
`HJO.Paths.levelCrosses_other_of_reveal`, `HJO.Paths.eventType_top_of_column`,
`HJO.Paths.eventType_head_of_mem_northSteps`, `HJO.Paths.mem_liveSteps_eastLeft_of_levelCrosses` and
`HJO.Paths.levelCrosses_east_of_levelCrosses_head`. Transcribing A. Mellit, *Toric braids and
`(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### The crossing interval of an east step -/

/-- The ordinate of the left endpoint of the east step at `s`, as the height function. -/
theorem eastLeft_snd (y : Heights a b N) (s : ℕ) : (eastLeft y s).2 = ht y (s + 1) := rfl

/-- The ordinate of the right endpoint of the east step at `s`, as the height function. -/
theorem eastRight_snd (y : Heights a b N) (s : ℕ) : (eastRight y s).2 = ht y (s + 1) := rfl

/-- **A level line crosses an east step exactly on the half-open interval `[rk̂(R_e), rk̂(L_e))`.**
The rank falls along an east step (`HJO.Paths.abovePointRank_eastRight_lt_eastLeft`), so the `min`
of `HJO.Paths.LevelCrosses` sits at the right endpoint and its `max` at the left — the opposite
orientation to a north step, and the reason `HJO.Paths.leftEastCount` writes this inequality out
instead of going through `HJO.Paths.LevelCrosses`. -/
theorem levelCrosses_eastStep_iff {y : Heights a b N} {s : ℕ} {η : ℤ} (hb : 0 < b)
    (h0 : 0 < a * N) :
    LevelCrosses a b N η (eastLeft y s) (eastRight y s) ↔
      ParkingFunctions.abovePointRank a b N (eastRight y s).1 (eastRight y s).2 ≤ η ∧
        η < ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2 := by
  have h := abovePointRank_eastRight_lt_eastLeft y s hb h0
  rw [LevelCrosses, min_eq_right h.le, max_eq_left h.le]

/-! ### The dichotomy: which of the two steps the sweep reveals later -/

/-- **When the sweep reveals the east step later, the pair is crossed exactly when the north step
is live at the east step's reveal point.** "Later" is `rk̂(L_e) < rk̂(u + (0,1))`, the sweep
descending; the conclusion is the condition `HJO.Paths.sweepRight` counts at `L_e`.

Forwards this is `HJO.Paths.mem_liveSteps_eastLeft_of_levelCrosses`. Backwards, the live window
`rk̂(u) ≤ rk̂(L_e) < rk̂(u) + ω` already places `rk̂(R_e) < rk̂(u) + ω`, and `rk̂(u) < rk̂(L_e)` is
the live window's first half sharpened by rank injectivity: equality would put the north step's
foot at `L_e`, whose abscissa `s` is strictly left of the step's column. -/
theorem exists_levelCrosses_iff_mem_liveSteps {y : Heights a b N} (hb : 0 < b) {s : ℕ}
    (hs : s < a * N) {u : ℕ × ℕ} (hu : u ∈ northSteps y) (hsu : s + 1 ≤ u.1)
    (hlt : ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2 <
      ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1)) :
    (∃ η : ℤ, LevelCrosses a b N η (eastLeft y s) (eastRight y s) ∧
        LevelCrosses a b N η u (u.1, u.2 + 1)) ↔ u ∈ liveSteps y (eastLeft y s) := by
  have h0 : 0 < a * N := lt_of_le_of_lt (Nat.zero_le s) hs
  have ha : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  refine ⟨fun hex => ?_, fun hlive => ?_⟩
  · obtain ⟨η, hE, hU⟩ := hex
    exact mem_liveSteps_eastLeft_of_levelCrosses hb hu hE hU hlt
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 h0
  have hωZ : (0 : ℤ) < (attackWindow a N : ℤ) := by exact_mod_cast hω
  have hrkR := abovePointRank_eastRight_lt_eastLeft y s hb h0
  rw [liveSteps, mem_filter] at hlive
  obtain ⟨-, hlow, hhigh⟩ := hlive
  have hne : ParkingFunctions.abovePointRank a b N u.1 u.2 ≠
      ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2 := by
    intro hEq
    obtain ⟨h1, -⟩ := abovePointRank_injOn ha hN (le_of_lt (mem_northSteps_iff.1 hu).1)
      (by rw [eastLeft_fst]; exact le_of_lt hs) hEq
    rw [eastLeft_fst] at h1
    omega
  obtain ⟨η, hE, hU⟩ :
      ∃ η : ℤ,
        (ParkingFunctions.abovePointRank a b N (eastRight y s).1 (eastRight y s).2 ≤ η ∧
          η < ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2) ∧
        (ParkingFunctions.abovePointRank a b N u.1 u.2 ≤ η ∧
          η < ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N) :=
    (exists_mem_inter_Ico hrkR (by omega)).2 ⟨by omega, by omega⟩
  exact ⟨η, (levelCrosses_eastStep_iff hb h0).2 hE, (levelCrosses_north_iff ha hN).2 hU⟩

/-- **When the sweep reveals the north step later, the pair is crossed exactly when the level line
through the north step's head still crosses the east step.** "Later" is
`rk̂(u + (0,1)) < rk̂(L_e)`; the conclusion is the condition `HJO.Paths.leftEastCount` counts at the
head, read through `HJO.Paths.levelCrosses_eastStep_iff`.

Forwards this is `HJO.Paths.levelCrosses_east_of_levelCrosses_head`. Backwards the interval of the
north step is `[rk̂(u + (0,1)) - ω, rk̂(u + (0,1)))`, so a common level exists as soon as
`rk̂(R_e) < rk̂(u + (0,1))`; the hypothesis gives `≤`, and the two points are distinct because
`R_e = (s+1, ŷ_{s+1})` and `u + (0,1) = (c, i+1)` can share an abscissa but not an ordinate, the
step's foot lying weakly above `ŷ_c`. -/
theorem exists_levelCrosses_iff_levelCrosses_head {y : Heights a b N} (hb : 0 < b) {s : ℕ}
    (hs : s < a * N) {u : ℕ × ℕ} (hu : u ∈ northSteps y)
    (hlt : ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) <
      ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2) :
    (∃ η : ℤ, LevelCrosses a b N η (eastLeft y s) (eastRight y s) ∧
        LevelCrosses a b N η u (u.1, u.2 + 1)) ↔
      LevelCrosses a b N (ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1))
        (eastLeft y s) (eastRight y s) := by
  have h0 : 0 < a * N := lt_of_le_of_lt (Nat.zero_le s) hs
  have ha : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  obtain ⟨hu1, hu2, -⟩ := mem_northSteps_iff.1 hu
  refine ⟨fun hex => ?_, fun hC => ?_⟩
  · obtain ⟨η, hE, hU⟩ := hex
    exact levelCrosses_east_of_levelCrosses_head hu hE hU hlt
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 h0
  have hωZ : (0 : ℤ) < (attackWindow a N : ℤ) := by exact_mod_cast hω
  have hrkR := abovePointRank_eastRight_lt_eastLeft y s hb h0
  have hsucc := abovePointRank_succ a b N u.1 u.2
  rw [levelCrosses_eastStep_iff hb h0] at hC
  obtain ⟨hC1, hC2⟩ := hC
  have hne : ParkingFunctions.abovePointRank a b N (eastRight y s).1 (eastRight y s).2 ≠
      ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) := by
    intro hEq
    obtain ⟨h1, h2⟩ := abovePointRank_injOn ha hN
      (by rw [eastRight_fst]; omega) (le_of_lt hu1) hEq
    rw [eastRight_fst] at h1
    rw [eastRight_snd] at h2
    rw [← h1] at hu2
    omega
  obtain ⟨η, hE, hU⟩ :
      ∃ η : ℤ,
        (ParkingFunctions.abovePointRank a b N (eastRight y s).1 (eastRight y s).2 ≤ η ∧
          η < ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2) ∧
        (ParkingFunctions.abovePointRank a b N u.1 u.2 ≤ η ∧
          η < ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N) :=
    (exists_mem_inter_Ico hrkR (by omega)).2 ⟨by omega, by omega⟩
  exact ⟨η, (levelCrosses_eastStep_iff hb h0).2 hE, (levelCrosses_north_iff ha hN).2 hU⟩

/-! ### The two halves of the partition -/

/-- The crossed pairs whose east step the sweep reveals later: those whose east reveal rank
`rk̂(L_e)` is the smaller of the two, the sweep descending. -/
private noncomputable def eastLaterPairs (y : Heights a b N) : Finset (ℕ × ℕ) :=
  {p ∈ crossingPairs y | ParkingFunctions.abovePointRank a b N p.1 (ht y (p.1 + 1)) <
    ParkingFunctions.abovePointRank a b N (ParkingFunctions.aboveColumn y p.2) (p.2 + 1)}

/-- The crossed pairs whose north step the sweep reveals later: those whose north reveal rank
`rk̂(u + (0,1))` is the smaller of the two. -/
private noncomputable def northLaterPairs (y : Heights a b N) : Finset (ℕ × ℕ) :=
  {p ∈ crossingPairs y |
    ParkingFunctions.abovePointRank a b N (ParkingFunctions.aboveColumn y p.2) (p.2 + 1) <
      ParkingFunctions.abovePointRank a b N p.1 (ht y (p.1 + 1))}

private theorem mem_eastLaterPairs {y : Heights a b N} {p : ℕ × ℕ} :
    p ∈ eastLaterPairs y ↔ p ∈ crossingPairs y ∧
      ParkingFunctions.abovePointRank a b N p.1 (ht y (p.1 + 1)) <
        ParkingFunctions.abovePointRank a b N (ParkingFunctions.aboveColumn y p.2) (p.2 + 1) :=
  mem_filter

private theorem mem_northLaterPairs {y : Heights a b N} {p : ℕ × ℕ} :
    p ∈ northLaterPairs y ↔ p ∈ crossingPairs y ∧
      ParkingFunctions.abovePointRank a b N (ParkingFunctions.aboveColumn y p.2) (p.2 + 1) <
        ParkingFunctions.abovePointRank a b N p.1 (ht y (p.1 + 1)) :=
  mem_filter

/-- The north step of a crossed pair is the one at the height naming it. -/
private theorem northStep_mem_northSteps {y : Heights a b N} (hy : IsAboveDiagonal y) {p : ℕ × ℕ}
    (hp : p ∈ crossingPairs y) :
    ((ParkingFunctions.aboveColumn y p.2, p.2) : ℕ × ℕ) ∈ northSteps y :=
  (ParkingFunctions.mem_northSteps_iff_eq_aboveColumn hy).2
    ⟨(mem_crossingPairs.1 (show (p.1, p.2) ∈ crossingPairs y from hp)).1.2, rfl⟩

/-- The two reveal ranks of a crossed pair are distinct, so each pair is revealed at exactly one of
its two steps. This is the half of `HJO.Paths.revealPoint_rank_ne_and_eventType` that makes the
split below total and disjoint. -/
private theorem reveal_rank_ne {y : Heights a b N} (hy : IsAboveDiagonal y) {p : ℕ × ℕ}
    (hp : p ∈ crossingPairs y) :
    ParkingFunctions.abovePointRank a b N p.1 (ht y (p.1 + 1)) ≠
      ParkingFunctions.abovePointRank a b N (ParkingFunctions.aboveColumn y p.2) (p.2 + 1) := by
  have hp' := mem_crossingPairs.1 (show (p.1, p.2) ∈ crossingPairs y from hp)
  exact (revealPoint_rank_ne_and_eventType hy hp'.1.1 (northStep_mem_northSteps hy hp)
    hp'.2.1).2.1

/-- **The two halves exhaust the crossed pairs.** -/
private theorem card_eastLater_add_card_northLater {y : Heights a b N} (hy : IsAboveDiagonal y) :
    #(eastLaterPairs y) + #(northLaterPairs y) = #(crossingPairs y) := by
  have hcongr : northLaterPairs y =
      {p ∈ crossingPairs y | ¬ ParkingFunctions.abovePointRank a b N p.1 (ht y (p.1 + 1)) <
        ParkingFunctions.abovePointRank a b N (ParkingFunctions.aboveColumn y p.2) (p.2 + 1)} := by
    rw [northLaterPairs]
    refine filter_congr fun p hp => ?_
    have hne := reveal_rank_ne hy hp
    omega
  rw [eastLaterPairs, hcongr]
  exact card_filter_add_card_filter_not _

/-! ### The fibre over a point of type `A` or `D` -/

/-- **The fibre of the east-later pairs over a type-`A`-or-`D` point is what `a_{P̂}` counts.**
Over a column top `P = L_e` the pair `(s, i)` in the fibre has `s = x(P)`, and
`HJO.Paths.mem_liveSteps_eastLeft_of_levelCrosses` sends it to the live north step at height `i`,
whose column is strictly right of `P`; over the corner both sides are `0`, the fibre because every
crossed pair has `s < aN` and the count by `HJO.Paths.sweepRight_corner`. -/
private theorem card_fiber_eastLater {y : Heights a b N} (hy : IsAboveDiagonal y) (hb : 0 < b)
    {P : ℕ × ℕ} (hP : P ∈ sweptRegion y)
    (hev : eventType y P = EventType.A ∨ eventType y P = EventType.D) :
    #{p ∈ eastLaterPairs y | eastLeft y p.1 = P} = sweepRight y P := by
  rcases (eventType_eq_A_or_D_iff hy hP).1 hev with ⟨hs, hP2⟩ | ⟨hP1, hP2⟩
  · have hPe : eastLeft y P.1 = P := Prod.ext rfl hP2.symm
    rw [sweepRight]
    refine Finset.card_nbij' (fun p => (ParkingFunctions.aboveColumn y p.2, p.2))
      (fun u => (P.1, u.2)) ?_ ?_ ?_ ?_
    · intro p hp
      rw [mem_coe, mem_filter] at hp
      obtain ⟨hpE, hpP⟩ := hp
      obtain ⟨hpc, hpQ⟩ := mem_eastLaterPairs.1 hpE
      obtain ⟨-, h3, η, hE, hU⟩ :=
        mem_crossingPairs.1 (show (p.1, p.2) ∈ crossingPairs y from hpc)
      have hlive : ((ParkingFunctions.aboveColumn y p.2, p.2) : ℕ × ℕ) ∈
          liveSteps y (eastLeft y p.1) :=
        mem_liveSteps_eastLeft_of_levelCrosses hb (northStep_mem_northSteps hy hpc) hE hU hpQ
      have hp1 : p.1 = P.1 := by
        have h := congrArg Prod.fst hpP
        rw [eastLeft_fst] at h
        exact h
      refine mem_coe.2 (mem_filter.2 ⟨?_, ?_⟩)
      · rw [← hpP]; exact hlive
      · change P.1 < ParkingFunctions.aboveColumn y p.2
        omega
    · intro u hu
      rw [mem_coe, mem_filter] at hu
      obtain ⟨hulive, hugt⟩ := hu
      have hu' : u ∈ northSteps y := liveSteps_subset y P hulive
      obtain ⟨hlt1, hcol⟩ :=
        (ParkingFunctions.mem_northSteps_iff_eq_aboveColumn hy (x := u.1) (i := u.2)).1 hu'
      have hwin := hulive
      rw [liveSteps, mem_filter] at hwin
      have hlt : ParkingFunctions.abovePointRank a b N (eastLeft y P.1).1 (eastLeft y P.1).2 <
          ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) := by
        rw [hPe, abovePointRank_succ]
        exact hwin.2.2
      have hcross := (exists_levelCrosses_iff_mem_liveSteps hb hs hu'
        (by omega) hlt).2 (by rw [hPe]; exact hulive)
      refine mem_coe.2 (mem_filter.2 ⟨mem_eastLaterPairs.2 ⟨?_, ?_⟩, ?_⟩)
      · refine mem_crossingPairs.2 ⟨⟨hs, hlt1⟩, ?_, ?_⟩
        · rw [← hcol]; omega
        · rw [← hcol]; exact hcross
      · change ParkingFunctions.abovePointRank a b N P.1 (ht y (P.1 + 1)) <
          ParkingFunctions.abovePointRank a b N (ParkingFunctions.aboveColumn y u.2) (u.2 + 1)
        rw [← hcol]
        exact hlt
      · exact hPe
    · intro p hp
      rw [mem_coe, mem_filter] at hp
      obtain ⟨-, hpP⟩ := hp
      have hp1 : p.1 = P.1 := by
        have h := congrArg Prod.fst hpP
        rw [eastLeft_fst] at h
        exact h
      exact Prod.ext hp1.symm rfl
    · intro u hu
      rw [mem_coe, mem_filter] at hu
      obtain ⟨-, hcol⟩ := (ParkingFunctions.mem_northSteps_iff_eq_aboveColumn hy
        (x := u.1) (i := u.2)).1 (liveSteps_subset y P hu.1)
      exact Prod.ext hcol.symm rfl
  · have hPc : P = ((a * N, b * N) : ℕ × ℕ) := Prod.ext hP1 hP2
    rw [hPc, sweepRight_corner, card_eq_zero, filter_eq_empty_iff]
    intro p hp hcon
    have h1 := (mem_crossingPairs.1 (show (p.1, p.2) ∈ crossingPairs y from
      (mem_eastLaterPairs.1 hp).1)).1.1
    have h2 : p.1 = a * N := by
      have h := congrArg Prod.fst hcon
      rw [eastLeft_fst] at h
      exact h
    omega

/-! ### The fibre over a point of type `A` or `C` -/

/-- **The fibre of the north-later pairs over a type-`A`-or-`C` point is what `a*_{P̂}` counts.**
A type-`A`-or-`C` point is the head `u + (0,1)` of a north step (`isSweepHead_iff_eventType`), so
the fibre over it is indexed by the abscissa `s` of the pair's east step alone, and
`HJO.Paths.levelCrosses_east_of_levelCrosses_head` turns the pair's crossing condition into the
crossing of that east step by the level line through `P` — which with `s < x(P)` is exactly the
condition `HJO.Paths.leftEastCount` counts. -/
private theorem card_fiber_northLater {y : Heights a b N} (hy : IsAboveDiagonal y) (hb : 0 < b)
    {P : ℕ × ℕ} (hP : P ∈ sweptRegion y)
    (hev : eventType y P = EventType.A ∨ eventType y P = EventType.C) :
    #{p ∈ northLaterPairs y | (ParkingFunctions.aboveColumn y p.2, p.2 + 1) = P} =
      leftEastCount y P := by
  obtain ⟨u, hu, huP⟩ := (isSweepHead_iff_eventType hy hP).2 hev
  have hu1 : u.1 = P.1 := by rw [← huP]
  have hu2 : u.2 + 1 = P.2 := by rw [← huP]
  obtain ⟨hlt1, hcol⟩ :=
    (ParkingFunctions.mem_northSteps_iff_eq_aboveColumn hy (x := u.1) (i := u.2)).1 hu
  obtain ⟨hs1, -, -⟩ := mem_northSteps_iff.1 hu
  have h0 : 0 < a * N := lt_of_le_of_lt (Nat.zero_le _) hs1
  have hrkP : ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) =
      ParkingFunctions.abovePointRank a b N P.1 P.2 := by rw [hu1, hu2]
  rw [leftEastCount]
  refine Finset.card_nbij' (fun p => p.1) (fun s => (s, u.2)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_coe, mem_filter] at hp
    obtain ⟨hpN, hpP⟩ := hp
    obtain ⟨hpc, hpQ⟩ := mem_northLaterPairs.1 hpN
    obtain ⟨⟨h1, -⟩, h3, η, hE, hU⟩ :=
      mem_crossingPairs.1 (show (p.1, p.2) ∈ crossingPairs y from hpc)
    have hc : ParkingFunctions.aboveColumn y p.2 = P.1 := by rw [← hpP]
    have hi : p.2 + 1 = P.2 := by rw [← hpP]
    have hrk : ParkingFunctions.abovePointRank a b N
        (ParkingFunctions.aboveColumn y p.2) (p.2 + 1) =
        ParkingFunctions.abovePointRank a b N P.1 P.2 := by rw [hc, hi]
    have hcr : LevelCrosses a b N (ParkingFunctions.abovePointRank a b N
        (ParkingFunctions.aboveColumn y p.2) (p.2 + 1)) (eastLeft y p.1) (eastRight y p.1) :=
      levelCrosses_east_of_levelCrosses_head (northStep_mem_northSteps hy hpc) hE hU hpQ
    rw [levelCrosses_eastStep_iff hb h0, hrk] at hcr
    refine mem_coe.2 (mem_filter.2 ⟨mem_range.2 h1, hcr.1, hcr.2, ?_⟩)
    change p.1 < P.1
    omega
  · intro s hs
    rw [mem_coe, mem_filter, mem_range] at hs
    obtain ⟨hs2, hc1, hc2, hc3⟩ := hs
    have hcross : ∃ η : ℤ, LevelCrosses a b N η (eastLeft y s) (eastRight y s) ∧
        LevelCrosses a b N η u (u.1, u.2 + 1) := by
      refine (exists_levelCrosses_iff_levelCrosses_head hb hs2 hu ?_).2 ?_
      · rw [hrkP]; exact hc2
      · rw [hrkP]; exact (levelCrosses_eastStep_iff hb h0).2 ⟨hc1, hc2⟩
    refine mem_coe.2 (mem_filter.2 ⟨mem_northLaterPairs.2 ⟨?_, ?_⟩, ?_⟩)
    · refine mem_crossingPairs.2 ⟨⟨hs2, hlt1⟩, ?_, ?_⟩
      · rw [← hcol, hu1]; omega
      · rw [← hcol]; exact hcross
    · change ParkingFunctions.abovePointRank a b N (ParkingFunctions.aboveColumn y u.2) (u.2 + 1) <
        ParkingFunctions.abovePointRank a b N s (ht y (s + 1))
      rw [← hcol, hrkP]
      exact hc2
    · change ((ParkingFunctions.aboveColumn y u.2, u.2 + 1) : ℕ × ℕ) = P
      rw [← hcol]
      exact huP
  · intro p hp
    rw [mem_coe, mem_filter] at hp
    obtain ⟨-, hpP⟩ := hp
    have hi : p.2 + 1 = P.2 := by rw [← hpP]
    exact Prod.ext rfl (show u.2 = p.2 by omega)
  · intro s _
    rfl

/-! ### The display -/

/-- **The hook count grouped by events.** For an above-diagonal `(aN, bN)`-path the above-diagonal
hook count `ĥ(P̂)` is the sum of the live north-step count to the right `a_{P̂}(P)` over the points
`P` of the swept region whose event type is `A` or `D`, plus the sum of the live east-step count to
the left `a*_{P̂}(P)` over those whose event type is `A` or `C`.

The crossed pairs of `HJO.Paths.aboveHookCount_eq_card_crossingPairs` are grouped by the point at
which the sweep reveals the later of the pair's two steps, which is the reveal point of smaller
rank; the two index sets are the type-`A`-or-`D` points and the type-`A`-or-`C` points, and the
corner — a type-`D` point that is the top of no column — contributes nothing. -/
@[hjo "lem_sweep_hook_events"]
theorem aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount {y : Heights a b N}
    (hy : IsAboveDiagonal y) (ha : 0 < a) (hb : 0 < b) :
    aboveHookCount y =
      ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.A ∨ eventType y P = EventType.D},
          sweepRight y P +
        ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.A ∨ eventType y P = EventType.C},
          leftEastCount y P := by
  have hmapsAD : ∀ p ∈ eastLaterPairs y, eastLeft y p.1 ∈
      {P ∈ sweptRegion y | eventType y P = EventType.A ∨ eventType y P = EventType.D} := by
    intro p hp
    obtain ⟨⟨h1, -⟩, -, -⟩ := mem_crossingPairs.1
      (show (p.1, p.2) ∈ crossingPairs y from (mem_eastLaterPairs.1 hp).1)
    have hmem : ((p.1, ht y (p.1 + 1)) : ℕ × ℕ) ∈ sweptRegion y :=
      hy.mem_sweptRegion (le_of_lt h1) (ht_mono hy.2.2.1 (Nat.le_succ _)) le_rfl
    exact mem_filter.2 ⟨hmem, (eventType_eq_A_or_D_iff hy hmem).2 (Or.inl ⟨h1, rfl⟩)⟩
  have hmapsAC : ∀ p ∈ northLaterPairs y,
      ((ParkingFunctions.aboveColumn y p.2, p.2 + 1) : ℕ × ℕ) ∈
        {P ∈ sweptRegion y | eventType y P = EventType.A ∨ eventType y P = EventType.C} := by
    intro p hp
    have hv := northStep_mem_northSteps hy (mem_northLaterPairs.1 hp).1
    have hmem : ((ParkingFunctions.aboveColumn y p.2, p.2 + 1) : ℕ × ℕ) ∈ sweptRegion y :=
      (mem_sweptRegion_of_mem_northSteps hy hv).2
    exact mem_filter.2 ⟨hmem, (isSweepHead_iff_eventType hy hmem).1 ⟨_, hv, rfl⟩⟩
  rw [aboveHookCount_eq_card_crossingPairs hy ha hb, ← card_eastLater_add_card_northLater hy,
    Finset.card_eq_sum_card_fiberwise hmapsAD, Finset.card_eq_sum_card_fiberwise hmapsAC]
  exact congrArg₂ (· + ·)
    (Finset.sum_congr rfl fun P hP =>
      card_fiber_eastLater hy hb (mem_filter.1 hP).1 (mem_filter.1 hP).2)
    (Finset.sum_congr rfl fun P hP =>
      card_fiber_northLater hy hb (mem_filter.1 hP).1 (mem_filter.1 hP).2)

end HJO.Paths
