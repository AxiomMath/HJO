/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.Sweep
public meta import HJO.Attr

/-! # The geometry the sweep reads: crossings, reveal points, word positions and left east steps

The sweep moves a level line of the above-diagonal rank downwards across the rectangle. Four pieces
of data it reads off the path are fixed here, all of them functions of the rank
`HJO.ParkingFunctions.abovePointRank` and none of them part of the sweep word itself:

* when the level line of a given rank crosses a unit segment of the path;
* the point at which the sweep reveals a given step;
* the position, in the step word, of a point of the swept region;
* the number of live east steps lying to the left of a point.

## Main definitions

* `HJO.Paths.PathStep`: a step of the path, either the east step at a given abscissa or the north
  step with a given foot.
* `HJO.Paths.eastLeft`, `HJO.Paths.eastRight`: the left and right endpoints `L_e`, `R_e` of the
  east step at an abscissa.
* `HJO.Paths.LevelCrosses`: the level line of rank `η` crosses the unit segment `QQ'`.
* `HJO.Paths.revealPoint`: the point at which the sweep reveals a step.
* `HJO.Paths.wordPosition`: the word position `pos_{P̂}(P)` of a point of the swept region.
* `HJO.Paths.leftEastCount`: the live east-step count to the left, `a*_{P̂}(P)`.

## Main results

* `HJO.Paths.levelCrosses_comm`: crossing does not depend on which endpoint is named first — the
  segment is unoriented, which the `min`/`max` of the formula is there to say.
* `HJO.Paths.levelCrosses_north_iff`: for a north step, crossing is exactly the half-open window
  `rk̂(u) ≤ η < rk̂(u) + ω` of `HJO.Paths.liveSteps`. So `HJO.Paths.LevelCrosses` and
  `HJO.Paths.liveSteps` agree on north steps, which is what makes the width a count of crossings.
* `HJO.Paths.revealPoint_east`, `HJO.Paths.revealPoint_north`: the two clauses of
  `HJO.Paths.revealPoint` read off the definition; the east step is revealed at its left endpoint
  and the north step at its head.
* `HJO.Paths.mem_liveSteps_iff_levelCrosses`: being live is being crossed, so the width
  `k_{P̂}(P)` is a count of crossings (`HJO.Paths.sweepWidth_eq_card_crossed`).
* `HJO.Paths.mem_sweptRegion_revealPoint_north`,
  `HJO.Paths.mem_sweptRegion_of_mem_northSteps`: the point revealing a north step of an
  above-diagonal path is swept, and so is the step's foot, so the reveal points lie in the
  swept region.
* `HJO.Paths.abovePointRank_injOn`: the rank is injective on the strip `0 ≤ x ≤ aN`, which is what
  makes the rank order a total order on the swept region.
* `HJO.Paths.levelCrosses_east_of_levelCrosses_head`: an east step crossed together with a north
  step is still crossed at the rank of that north step's head.

## Implementation notes

### Crossing

`LevelCrosses` takes the two endpoints of the segment as separate arguments and is symmetric in
them (`levelCrosses_comm`); the `min` and `max` are there for exactly that reason. The
rank `η` is an integer, as `HJO.ParkingFunctions.abovePointRank` is. Nothing requires the two points
to be at distance one: the condition is stated for any pair, and `levelCrosses_north_iff` is where
being a unit segment in the vertical direction is used, through
`HJO.Paths.abovePointRank_succ`. A unit *horizontal* segment does not admit the same rewriting,
`rk̂` decreasing along it as soon as `b(aN+1)N > 1`, and `HJO.Paths.leftEastCount` writes the
inequality out for that reason rather than calling it a crossing.

### Reveal points and steps

`PathStep` names an east step by its abscissa `s` and a north step by its foot `u`, matching
`HJO.Paths.northSteps`, whose elements are feet. The natural bounds — `0 ≤ s ≤ aN - 1` for
an east step, `u ∈ northSteps y` for a north step — are not carried in the type: `revealPoint` is
total, in the house style of `HJO.Paths.liveSteps`, and the bounds enter in the lemmas. `aN - 1` is
never written: `s < a * N` is the same condition and truncates nothing.

### Word position

`wordPosition` counts north steps twice over, once by foot and once by head: the two
summands are `#{u : rk̂(u) ≤ rk̂(P)}` and `#{u : rk̂(u) + ω ≤ rk̂(P)}`, and by
`HJO.Paths.abovePointRank_succ` the second is `#{u : rk̂(head u) ≤ rk̂(P)}`. So the position of `P`
is the number of step endpoints of the path the sweep has passed, which is what a position in the
step word is. Both counts are over `HJO.Paths.northSteps`, the feet of the north steps, following
the convention that a north step is named by its foot.

### The left east count

The count is over the abscissas `s < aN`, one east step to each, rather than over a `Finset` of
segments: an east step of an `(aN, bN)`-path is determined by its abscissa, and `eastLeft`,
`eastRight` are its endpoints. The three clauses are those of the definition, written out and not
folded into `LevelCrosses`, for the reason given above.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section "The sweep process", with his `ε`
replaced throughout by the integer rank `HJO.ParkingFunctions.abovePointRank`. -/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### The east steps of a path -/

/-- The left endpoint `L_e = (s, ŷ_{s+1})` of the east step of the path `y` at abscissa `s`: the
east step runs from there to `(s + 1, ŷ_{s+1})`, at the top of the column at `s`. -/
def eastLeft (y : Heights a b N) (s : ℕ) : ℕ × ℕ := (s, ht y (s + 1))

/-- The right endpoint `R_e = (s + 1, ŷ_{s+1})` of the east step of the path `y` at abscissa `s`. -/
def eastRight (y : Heights a b N) (s : ℕ) : ℕ × ℕ := (s + 1, ht y (s + 1))

@[simp]
theorem eastLeft_fst (y : Heights a b N) (s : ℕ) : (eastLeft y s).1 = s := rfl

@[simp]
theorem eastRight_fst (y : Heights a b N) (s : ℕ) : (eastRight y s).1 = s + 1 := rfl

/-- The two endpoints of an east step have the same ordinate: the step is horizontal. -/
theorem eastLeft_snd_eq_eastRight_snd (y : Heights a b N) (s : ℕ) :
    (eastLeft y s).2 = (eastRight y s).2 := rfl

/-! ### A level line crossing a unit segment -/

/-- **The level line of rank `η` crosses the unit segment with lattice endpoints `Q` and `Q'`**:
`min(rk̂(Q), rk̂(Q')) ≤ η < max(rk̂(Q), rk̂(Q'))`, the rank being the above-diagonal rank
`HJO.ParkingFunctions.abovePointRank`.

Symmetric in the two endpoints (`levelCrosses_comm`), which is what the `min` and `max` are for: a
segment of the path is unoriented, and the condition must not depend on which end is named first.
The half-open interval breaks the tie at a lattice point in favour of the lower endpoint, which is
the tie-breaking Mellit's `ε` performs. -/
@[hjo "def_sweep_crosses"]
def LevelCrosses (a b N : ℕ) (η : ℤ) (Q Q' : ℕ × ℕ) : Prop :=
  min (ParkingFunctions.abovePointRank a b N Q.1 Q.2)
      (ParkingFunctions.abovePointRank a b N Q'.1 Q'.2) ≤ η ∧
    η < max (ParkingFunctions.abovePointRank a b N Q.1 Q.2)
      (ParkingFunctions.abovePointRank a b N Q'.1 Q'.2)

/-- Crossing is decidable, being a conjunction of two comparisons of integers. -/
instance (a b N : ℕ) (η : ℤ) (Q Q' : ℕ × ℕ) : Decidable (LevelCrosses a b N η Q Q') := by
  unfold LevelCrosses; infer_instance

/-- Crossing does not depend on which endpoint is named first. -/
theorem levelCrosses_comm {η : ℤ} {Q Q' : ℕ × ℕ} :
    LevelCrosses a b N η Q Q' ↔ LevelCrosses a b N η Q' Q := by
  simp only [LevelCrosses, min_comm, max_comm]

/-- No level line crosses a degenerate segment. -/
@[simp]
theorem not_levelCrosses_self {η : ℤ} {Q : ℕ × ℕ} : ¬LevelCrosses a b N η Q Q := by
  simp only [LevelCrosses, min_self, max_self, not_and, not_lt]
  exact fun h => h

/-- **Crossing a north step is the half-open window of `HJO.Paths.liveSteps`.** For the north step
with foot `u`, whose head is `(u.1, u.2 + 1)`, the level line of rank `η` crosses it exactly when
`rk̂(u) ≤ η < rk̂(u) + ω`. This is why the width `k_{P̂}(P)` counts crossings:
`HJO.Paths.LevelCrosses` and `HJO.Paths.liveSteps` say the same thing about a north step.

The head always outranks the foot, by exactly the window `ω`, so the `min` is the foot and the
`max` the head; the argument is `HJO.Paths.abovePointRank_succ` together with the positivity of the
window, which needs the rectangle to have a column. -/
theorem levelCrosses_north_iff {η : ℤ} {u : ℕ × ℕ} (ha : 0 < a) (hN : 0 < N) :
    LevelCrosses a b N η u (u.1, u.2 + 1) ↔
      ParkingFunctions.abovePointRank a b N u.1 u.2 ≤ η ∧
        η < ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N := by
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
  have hsucc : ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) =
      ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N :=
    abovePointRank_succ a b N u.1 u.2
  have hlt : ParkingFunctions.abovePointRank a b N u.1 u.2 <
      ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) := by
    rw [hsucc]; exact lt_add_of_pos_right _ (by exact_mod_cast hω)
  rw [LevelCrosses, min_eq_left hlt.le, max_eq_right hlt.le, hsucc]

/-- **Being live is being crossed.** A north step `u` of the path is live at `P` exactly when the
level line of rank `rk̂(P)` crosses it. This is `HJO.Paths.mem_liveSteps_iff_levelCrosses`, and it
lets the width `k_{P̂}(P)` of `HJO.Paths.sweepWidth` be read as a number of crossings: Mellit's
"the number of connected components of the intersection of the line with the figure".

The hypotheses that the path is above-diagonal and that `P` is swept are not needed —
neither `liveSteps` nor `LevelCrosses` reads either — and the positivity of the window comes from
`hu` alone: a north step has abscissa below `aN`, so the rectangle has a column. At `a * N = 0`
there are no north steps and the statement is vacuous rather than false. -/
@[hjo "lem_sweep_live_crossing"]
theorem mem_liveSteps_iff_levelCrosses {y : Heights a b N} {P u : ℕ × ℕ}
    (hu : u ∈ northSteps y) :
    u ∈ liveSteps y P ↔
      LevelCrosses a b N (ParkingFunctions.abovePointRank a b N P.1 P.2) u (u.1, u.2 + 1) := by
  have h0 : 0 < a * N := lt_of_le_of_lt (Nat.zero_le _) (mem_northSteps_iff.1 hu).1
  have ha : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  rw [levelCrosses_north_iff ha hN, liveSteps, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩

/-- The width at a point counts the north steps the level line through it crosses: `sweepWidth` read
through `mem_liveSteps_iff_levelCrosses`. -/
theorem sweepWidth_eq_card_crossed (y : Heights a b N) (P : ℕ × ℕ) :
    sweepWidth y P =
      #{u ∈ northSteps y |
        LevelCrosses a b N (ParkingFunctions.abovePointRank a b N P.1 P.2) u (u.1, u.2 + 1)} := by
  rw [sweepWidth]
  refine card_nbij id (fun u hu => ?_) (fun u _ v _ h => h) (fun u hu => ⟨u, ?_, rfl⟩)
  · exact mem_filter.2 ⟨liveSteps_subset y P hu,
      (mem_liveSteps_iff_levelCrosses (liveSteps_subset y P hu)).1 hu⟩
  · exact (mem_liveSteps_iff_levelCrosses (mem_filter.1 hu).1).2 (mem_filter.1 hu).2

/-- **The east step is still crossed when the north step is revealed.** Suppose some level line, of
rank `η₀`, crosses both the east step at abscissa `s` and the north step with foot `u`. If the head
of that north step is outranked by the left endpoint of the east step, then the level line *of the
head's rank* still crosses the east step.

This is `HJO.Paths.levelCrosses_east_of_levelCrosses_head`, and it is the step that keeps an east
step live while the sweep descends from `η₀` to the point revealing the north step. The whole
argument is a chain of four ranks: the crossing of the north step puts `η₀` strictly below the head,
that of the east step puts the lower endpoint weakly below `η₀`, and the hypothesis puts the head
strictly below the left endpoint, which is weakly below the larger endpoint.

Three of the hypotheses are therefore not needed and are not carried: that the path is
above-diagonal, that `s ≤ aN - 1`, and that `s + 1 ≤ c`. None of them is used — the inequalities do
not know where the two segments sit relative to one another — and dropping them generalises the
statement rather than weakening it. What *is* needed is `u ∈ northSteps y`, and only for the
positivity of the window inside `levelCrosses_north_iff`. The "some level line crosses
both" is read as a named `η₀` with the two crossings as hypotheses, which is the skolemised form
every consumer holds. -/
@[hjo "lem_sweep_crossing_east_live"]
theorem levelCrosses_east_of_levelCrosses_head {y : Heights a b N} {u : ℕ × ℕ} {s : ℕ} {η₀ : ℤ}
    (hu : u ∈ northSteps y)
    (hE : LevelCrosses a b N η₀ (eastLeft y s) (eastRight y s))
    (hU : LevelCrosses a b N η₀ u (u.1, u.2 + 1))
    (hlt : ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) <
      ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2) :
    LevelCrosses a b N (ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1))
      (eastLeft y s) (eastRight y s) := by
  have h0 : 0 < a * N := lt_of_le_of_lt (Nat.zero_le _) (mem_northSteps_iff.1 hu).1
  have ha : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  obtain ⟨-, hhead⟩ := (levelCrosses_north_iff ha hN).1 hU
  rw [← abovePointRank_succ a b N u.1 u.2] at hhead
  exact ⟨hE.1.trans hhead.le, hlt.trans_le (le_max_left _ _)⟩

/-! ### The point at which the sweep reveals a step -/

/-- A step of an `(aN, bN)`-path: the east step at abscissa `s`, running from `(s, ŷ_{s+1})` to
`(s + 1, ŷ_{s+1})`, or the north step with foot `u`, running from `u` to `u + (0,1)`. North steps
are named by their feet, as the elements of `HJO.Paths.northSteps` are. -/
inductive PathStep : Type
  /-- The east step at abscissa `s`. -/
  | east (s : ℕ) : PathStep
  /-- The north step with foot `u`. -/
  | north (u : ℕ × ℕ) : PathStep
  deriving DecidableEq

/-- **The point at which the sweep reveals a step.** The east step running from `(s, ŷ_{s+1})` to
`(s + 1, ŷ_{s+1})` is revealed at `(s, ŷ_{s+1})` — its left endpoint, the point of the swept region
lying at the top of the column at `s`; and the north step with foot `(c, i)` is revealed at
`(c, i + 1)` — its head.

So each step is revealed at whichever of its two endpoints the level line reaches first, the level
line descending: for a north step that is the head, which outranks the foot by `ω`, and for an east
step the left endpoint, which outranks the right as soon as the rectangle has a column. Total in the
step, the bounds `0 ≤ s ≤ aN - 1` and `u ∈ northSteps y` entering in the lemmas. -/
@[hjo "def_sweep_revealed"]
def revealPoint (y : Heights a b N) : PathStep → ℕ × ℕ
  | .east s => (s, ht y (s + 1))
  | .north u => (u.1, u.2 + 1)

/-- The east step at abscissa `s` is revealed at its left endpoint. -/
@[simp]
theorem revealPoint_east (y : Heights a b N) (s : ℕ) :
    revealPoint y (.east s) = eastLeft y s := rfl

/-- The north step with foot `(c, i)` is revealed at `(c, i + 1)`, its head. -/
@[simp]
theorem revealPoint_north (y : Heights a b N) (u : ℕ × ℕ) :
    revealPoint y (.north u) = (u.1, u.2 + 1) := rfl

/-- The point revealing a north step of an above-diagonal path lies in the swept region: the head
of a north step at height `i` in column `c` has ordinate `i + 1 ≤ ŷ_{c+1}`, and the column of the
path is swept. So the reveal points are points at which the sweep registers an event, which is what
`HJO.Paths.revealPoint` is for. -/
theorem mem_sweptRegion_revealPoint_north {y : Heights a b N} (hy : IsAboveDiagonal y)
    {u : ℕ × ℕ} (hu : u ∈ northSteps y) : revealPoint y (.north u) ∈ sweptRegion y := by
  obtain ⟨h1, h2, h3⟩ := mem_northSteps_iff.1 hu
  exact hy.mem_sweptRegion (by omega) (by omega) (by omega)

/-- The point revealing the east step at an abscissa inside the rectangle lies in the swept region:
it is the top of the column there. -/
theorem mem_sweptRegion_revealPoint_east {y : Heights a b N} (hy : IsAboveDiagonal y) {s : ℕ}
    (hs : s ≤ a * N) : revealPoint y (.east s) ∈ sweptRegion y :=
  hy.mem_sweptRegion hs (ht_mono hy.2.2.1 (Nat.le_succ s)) le_rfl

/-- **Both ends of a north step lie in the swept region.** For a north step `u` of an above-diagonal
path, `u` and `u + (0,1)` are both points at which the sweep registers an event: the foot because
the column of the path at `u.1` is swept, the head because its ordinate `u.2 + 1` is still at most
`ŷ_{u.1+1}`.

This is `HJO.Paths.mem_sweptRegion_of_mem_northSteps`, stated as the conjunction rather than as a
`Finset` inclusion — the `{u, u + (0,1)} ⊆ Sw(P̂)` — because the halves are used
separately: the foot in `HJO.Paths.wordPosition`, read at a foot, and the head in
`HJO.Paths.revealPoint`, which reveals the step there. -/
@[hjo "lem_sweep_north_step_ends"]
theorem mem_sweptRegion_of_mem_northSteps {y : Heights a b N} (hy : IsAboveDiagonal y)
    {u : ℕ × ℕ} (hu : u ∈ northSteps y) :
    u ∈ sweptRegion y ∧ (u.1, u.2 + 1) ∈ sweptRegion y := by
  obtain ⟨h1, h2, h3⟩ := mem_northSteps_iff.1 hu
  exact ⟨hy.mem_sweptRegion (by omega) h2 (by omega),
    hy.mem_sweptRegion (by omega) (by omega) (by omega)⟩

/-- **The rank is injective on the strip `0 ≤ x ≤ aN`.** This is
`HJO.Paths.abovePointRank_injOn`, which is what makes the rank order a total order on the swept
region and the rank-order listing of its points well defined.

The rank is `M(ay - bx) + x` with `M = (aN+1)N`, so two points of equal rank have abscissas
congruent modulo `M`; on the strip the difference of abscissas is at most `aN < M`, hence zero, and
then `a(y - y') = 0` gives the ordinates. Both steps need the rectangle to have a column: at
`a * N = 0` the factor `M` is `0` and the rank is constant in the ordinate, so the hypotheses
`0 < a` and `0 < N` are live and not decoration. -/
@[hjo "lem_sweep_rank_injective"]
theorem abovePointRank_injOn (ha : 0 < a) (hN : 0 < N) {x y x' y' : ℕ}
    (hx : x ≤ a * N) (hx' : x' ≤ a * N)
    (h : ParkingFunctions.abovePointRank a b N x y =
      ParkingFunctions.abovePointRank a b N x' y') : x = x' ∧ y = y' := by
  have hM : (a * N + 1) * N ≠ 0 := by positivity
  simp only [ParkingFunctions.abovePointRank] at h
  have hdvd : ((a : ℤ) * N + 1) * N ∣ ((x : ℤ) - x') :=
    ⟨(a : ℤ) * y' - b * x' - (a * y - b * x), by linarith⟩
  have hxx : (x : ℤ) = x' := by
    have hb : |(x : ℤ) - x'| < ((a : ℤ) * N + 1) * N := by
      have h1 : (x : ℤ) ≤ a * N := by exact_mod_cast hx
      have h2 : (x' : ℤ) ≤ a * N := by exact_mod_cast hx'
      have h3 : (1 : ℤ) ≤ N := by exact_mod_cast hN
      have h4 : (0 : ℤ) ≤ (a : ℤ) * N := by positivity
      rw [abs_lt]; constructor <;> nlinarith
    have := Int.eq_zero_of_abs_lt_dvd hdvd hb
    omega
  refine ⟨by exact_mod_cast hxx, ?_⟩
  have hay : (a : ℤ) * y = a * y' := by
    have hMpos : (0 : ℤ) < ((a : ℤ) * N + 1) * N := by positivity
    have : ((a : ℤ) * N + 1) * N * ((a : ℤ) * y - b * x) =
        ((a : ℤ) * N + 1) * N * ((a : ℤ) * y' - b * x') := by linarith
    have h2 := mul_left_cancel₀ (ne_of_gt hMpos) this
    rw [hxx] at h2
    linarith
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have : (y : ℤ) = y' := by
    have := mul_left_cancel₀ (ne_of_gt ha') hay
    exact this
  exact_mod_cast this

/-! ### The word position of a point -/

/-- **The word position `pos_{P̂}(P)` of a point of the swept region**:
`#{u : rk̂(u) ≤ rk̂(P)} + #{u : rk̂(u) + ω ≤ rk̂(P)}`, both counts over the north steps `u` of the
path, each named by its foot.

By `HJO.Paths.abovePointRank_succ` the second count is the number of north steps whose *head* is
outranked by `P`, so the position of `P` is the number of endpoints of north steps the sweep has
already passed — a position in the step word. Total in `P`, although only `P ∈ Sw(P̂)` is ever
read. -/
@[hjo "def_sweep_position"]
def wordPosition (y : Heights a b N) (P : ℕ × ℕ) : ℕ :=
  #{u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
      ParkingFunctions.abovePointRank a b N P.1 P.2} +
    #{u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N ≤
      ParkingFunctions.abovePointRank a b N P.1 P.2}

/-- **The second summand counts the heads.** `rk̂(u) + ω ≤ rk̂(P)` says that the head of the north
step with foot `u` is outranked by `P`, so `pos_{P̂}(P)` counts feet and heads separately and adds
them. -/
theorem wordPosition_eq_add_card_heads (y : Heights a b N) (P : ℕ × ℕ) :
    wordPosition y P =
      #{u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
          ParkingFunctions.abovePointRank a b N P.1 P.2} +
        #{u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) ≤
          ParkingFunctions.abovePointRank a b N P.1 P.2} := by
  rw [wordPosition]
  congr 1
  exact card_nbij id (fun u hu => by
      simpa only [id, abovePointRank_succ] using hu)
    (fun u _ v _ h => h) (fun u hu => ⟨u, by simpa only [abovePointRank_succ] using hu, rfl⟩)

/-- The second count never exceeds the first, the head of a north step outranking its foot. So the
word position is at most twice the number of north steps, which is the length of the step word. -/
theorem wordPosition_le (y : Heights a b N) (P : ℕ × ℕ) :
    wordPosition y P ≤ 2 * #(northSteps y) := by
  have h1 : #{u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
      ParkingFunctions.abovePointRank a b N P.1 P.2} ≤ #(northSteps y) := card_filter_le _ _
  have h2 : #{u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 +
      attackWindow a N ≤ ParkingFunctions.abovePointRank a b N P.1 P.2} ≤
      #(northSteps y) := card_filter_le _ _
  rw [wordPosition]; omega

/-! ### The live east-step count to the left -/

/-- **The live east-step count to the left, `a*_{P̂}(P)`**: the number of east steps `e` of the path
such that the level line through `P` crosses `e` — that is,
`rk̂(R_e) ≤ rk̂(P) < rk̂(L_e)` for the left and right endpoints `L_e`, `R_e` of `e` — and
`x(L_e) < x(P)`.

East steps are indexed by their abscissa `s < aN`, one to each, with endpoints
`HJO.Paths.eastLeft y s` and `HJO.Paths.eastRight y s`; the third clause is then `s < x(P)`.
The crossing inequality is written out rather than expressed through
`HJO.Paths.LevelCrosses`, because along a horizontal segment the rank *decreases*, so the
`min` of the formula would be at the right endpoint and the `max` at the left — the opposite of the
vertical case, and only when `b(aN+1)N > 1`. Writing the inequality out directly avoids
making the definition depend on that. Total in `P`, although only `P ∈ Sw(P̂)` is ever
read. -/
@[hjo "def_sweep_left_east"]
def leftEastCount (y : Heights a b N) (P : ℕ × ℕ) : ℕ :=
  #{s ∈ range (a * N) |
    ParkingFunctions.abovePointRank a b N (eastRight y s).1 (eastRight y s).2 ≤
        ParkingFunctions.abovePointRank a b N P.1 P.2 ∧
      ParkingFunctions.abovePointRank a b N P.1 P.2 <
        ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2 ∧
      s < P.1}

/-- Every east step counted lies strictly to the left of `P`, so the count is at most `x(P)`: this
is the bound the count is read against. -/
theorem leftEastCount_le_fst (y : Heights a b N) (P : ℕ × ℕ) : leftEastCount y P ≤ P.1 := by
  have hsub : ∀ s ∈ {s ∈ range (a * N) |
      ParkingFunctions.abovePointRank a b N (eastRight y s).1 (eastRight y s).2 ≤
          ParkingFunctions.abovePointRank a b N P.1 P.2 ∧
        ParkingFunctions.abovePointRank a b N P.1 P.2 <
          ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2 ∧
        s < P.1}, s ∈ range P.1 := fun s hs => mem_range.2 (mem_filter.1 hs).2.2.2
  calc leftEastCount y P ≤ #(range P.1) := card_le_card hsub
    _ = P.1 := card_range P.1

/-- The count is at most the number of east steps of the path. -/
theorem leftEastCount_le (y : Heights a b N) (P : ℕ × ℕ) : leftEastCount y P ≤ a * N := by
  calc leftEastCount y P ≤ #(range (a * N)) := card_filter_le _ _
    _ = a * N := card_range (a * N)

end HJO.Paths
