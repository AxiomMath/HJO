/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepCrossing
public meta import HJO.Attr

/-! # The cell a crossed pair marks, and the two rank comparisons that pin its hook

`HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount` matches the swept points at which
a crossed (east, north) pair is read off against the cells of the diagram passing Macdonald's hook
condition. The correspondence sends the pair "east step at `s`, north step `(c,i)`" to the cell
`(s+1, i+1)`, and it is a correspondence because the two rank comparisons that decide whether the
pair is crossed at all are *exactly* the two hook inequalities on that cell's arm and leg. This file
carries the cell and the two comparisons.

Write `α = c - s - 1` and `λ = i - ŷ_{s+1}`. Then:

* the arm of the cell `(s+1, i+1)` is `Â_{i+1} - (s+1) = c - s - 1 = α`, by
  `HJO.Paths.lastBelow_succ_of_mem_northSteps`;
* its leg is `i + 1 - 1 - ŷ_{s+1} = λ`, immediately from `HJO.Paths.aboveLeg`;
* the north step is outranked by the east step's left endpoint exactly when `aλ < b(α+1)`;
* the east step's right endpoint is outranked by the north step's head exactly when `bα ≤ a(λ+1)`.

The last two are the hook inequalities `b·arm ≤ a(leg+1)` and `a·leg < b(arm+1)` of
`HJO.Paths.aboveHookCount`, on the nose.

## Main results

* `HJO.Paths.mem_aboveCells_of_mem_northSteps`.
* `HJO.Paths.lastBelow_succ_of_mem_northSteps`.
* `HJO.Paths.abovePointRank_lt_top_of_column_iff`.
* `HJO.Paths.abovePointRank_eastRight_lt_head_iff`.

## Implementation notes

### `α` and `λ` are parameters, not subtractions

The differences `α = c - s - 1` and `λ = i - ŷ_{s+1}` are both genuine differences
under the hypotheses — `c ≥ s + 1`, and `i ≥ ŷ_c ≥ ŷ_{s+1}` by monotonicity. Rather than write them
as `ℕ` subtractions and then prove they do not truncate, the two rank comparisons are stated at the
north step `(s + 1 + α, ŷ_{s+1} + λ)`, with `α` and `λ` free natural numbers. That is the same pair
of points, it removes truncation from the statement entirely, and it is the form the consumer holds:
`HJO.Paths.hook_slope_iff_exists_levelCrosses` ranges over the cells of a row and has the arm and
the leg in hand before it names the step. `c ≥ s + 1` and `i ≥ ŷ_{s+1}` are then not hypotheses but
consequences of the shape.

### Where the positivity hypotheses go

Both comparisons go through `HJO.Paths.abovePointRank_lt_iff`, which needs
`0 < N` and both abscissae inside the strip. `HJO.Paths.abovePointRank_eastRight_lt_head_iff` needs
`0 < a` on top of that, and the proof is where it is used: in the boundary case `bα = a(λ+1)` the
rank comparison is decided by the abscissa tie-break, which needs `α ≥ 1`, and that follows only
because `a(λ+1) ≥ a ≥ 1` forces `bα > 0`. (Asking `≥ a > 1` is too much; `> 0` is what the argument
needs and what `0 < a` gives.)

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### The cell a crossed pair marks -/

/-- **The pair marks a cell.** `HJO.Paths.mem_aboveCells_of_mem_northSteps`: for `s < aN` and a
north step `(c,i)` with `s + 1 ≤ c`, the pair `(s+1, i+1)` is a cell of the diagram above the path.

The four conditions of `HJO.Paths.aboveCells` come out as: `1 ≤ s+1` is free; `s + 1 ≤ c < aN`;
`ŷ_{s+1} ≤ ŷ_c ≤ i < i+1` by monotonicity and the north-step bound; and `i + 1 ≤ ŷ_{c+1} ≤ bN`. -/
@[hjo "lem_sweep_cell_spanned"]
theorem mem_aboveCells_of_mem_northSteps {y : Heights a b N} (hy : IsAboveDiagonal y) {s : ℕ}
    {u : ℕ × ℕ} (hu : u ∈ northSteps y) (hsu : s + 1 ≤ u.1) :
    (s + 1, u.2 + 1) ∈ aboveCells y := by
  obtain ⟨h1, h2, h3⟩ := mem_northSteps_iff.1 hu
  have hmono : ht y (s + 1) ≤ ht y u.1 := ht_mono hy.2.2.1 hsu
  have htop : ht y (u.1 + 1) ≤ b * N := ht_le_mul y _
  refine mem_aboveCells.2 ⟨?_, ?_, ?_, ?_⟩
  · change 1 ≤ s + 1
    omega
  · change s + 1 < a * N
    omega
  · change ht y (s + 1) < u.2 + 1
    omega
  · change u.2 + 1 ≤ b * N
    omega

/-- **The arm of that cell is read off the north step's column.** This is
`HJO.Paths.lastBelow_succ_of_mem_northSteps`: for a north step `(c,i)`, the last abscissa at which
the path is still strictly below height `i+1` is `c` itself. So the arm `Â_{i+1} - (s+1)` of the
cell `(s+1, i+1)` is `c - s - 1`, the `α` of the two comparisons below.

`ŷ_c ≤ i` puts `c` in the set, and `ŷ_{c+1} > i` keeps every larger abscissa out, the heights being
nondecreasing. -/
@[hjo "lem_sweep_cell_arm_head"]
theorem lastBelow_succ_of_mem_northSteps {y : Heights a b N} (hy : IsAboveDiagonal y) {u : ℕ × ℕ}
    (hu : u ∈ northSteps y) : lastBelow y (u.2 + 1) = u.1 := by
  obtain ⟨h1, h2, h3⟩ := mem_northSteps_iff.1 hu
  refine le_antisymm ?_ (le_lastBelow (by omega) (by omega))
  by_contra hcon
  have hgt : u.1 + 1 ≤ lastBelow y (u.2 + 1) := by omega
  have hmono : ht y (u.1 + 1) ≤ ht y (lastBelow y (u.2 + 1)) := ht_mono hy.2.2.1 hgt
  have hlt := hy.ht_lastBelow_lt (j := u.2 + 1) (by omega)
  omega

/-! ### The two rank comparisons -/

/-- **The lower hook inequality is a rank comparison.**
`HJO.Paths.abovePointRank_lt_top_of_column_iff`: for the north step `(s + 1 + α, ŷ_{s+1} + λ)`, its
foot is outranked by the top of the column at `s` exactly when `aλ < b(α+1)`.

The two diagonal excesses differ by `aλ - b(α+1)`, and the abscissa tie-break of
`HJO.Paths.abovePointRank_lt_iff` cannot fire: the step's column `s + 1 + α` exceeds `s`, so the
alternative that lemma offers is unavailable and the excess decides alone. -/
@[hjo "lem_sweep_crossing_lower"]
theorem abovePointRank_lt_top_of_column_iff {y : Heights a b N} {s : ℕ} (hs : s < a * N)
    {α l : ℕ} (hu : (s + 1 + α, ht y (s + 1) + l) ∈ northSteps y) :
    ParkingFunctions.abovePointRank a b N (s + 1 + α) (ht y (s + 1) + l) <
        ParkingFunctions.abovePointRank a b N s (ht y (s + 1)) ↔ a * l < b * (α + 1) := by
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at hs
  have h1 : s + 1 + α < a * N := (mem_northSteps_iff.1 hu).1
  rw [abovePointRank_lt_iff (b := b) hN (le_of_lt h1) (le_of_lt hs)]
  constructor
  · rintro (h | ⟨-, hbad⟩)
    · have hz : (a : ℤ) * l < (b : ℤ) * (α + 1) := by push_cast at h; linarith
      exact_mod_cast hz
    · omega
  · intro h
    have hz : (a : ℤ) * l < (b : ℤ) * (α + 1) := by exact_mod_cast h
    refine Or.inl ?_
    push_cast
    linarith

/-- **The upper hook inequality is a rank comparison.**
`HJO.Paths.abovePointRank_eastRight_lt_head_iff`: for the north step `(s + 1 + α, ŷ_{s+1} + λ)`, the
right endpoint of the east step at `s` is outranked by that step's head exactly when `bα ≤ a(λ+1)`.

Here the excesses differ by `a(λ+1) - bα` and the tie-break *does* fire, which is why this
inequality is weak where the previous one is strict: the abscissae are `s+1` and `s+1+α`, so the
tie-break is available exactly when `α ≥ 1`, and in the boundary case `bα = a(λ+1)` that holds
because `a(λ+1) ≥ a ≥ 1` forces `bα > 0`. This is the one use of `0 < a`. -/
@[hjo "lem_sweep_crossing_upper"]
theorem abovePointRank_eastRight_lt_head_iff {y : Heights a b N} (ha : 0 < a) {s : ℕ}
    (hs : s < a * N) {α l : ℕ} (hu : (s + 1 + α, ht y (s + 1) + l) ∈ northSteps y) :
    ParkingFunctions.abovePointRank a b N (s + 1) (ht y (s + 1)) <
        ParkingFunctions.abovePointRank a b N (s + 1 + α) (ht y (s + 1) + l + 1) ↔
      b * α ≤ a * (l + 1) := by
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at hs
  have h1 : s + 1 + α < a * N := (mem_northSteps_iff.1 hu).1
  have haz : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  have hlz : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg _
  rw [abovePointRank_lt_iff (b := b) hN (by omega) (le_of_lt h1)]
  constructor
  · rintro (h | ⟨heq, -⟩)
    · have hz : (b : ℤ) * α < (a : ℤ) * (l + 1) := by push_cast at h; linarith
      exact_mod_cast hz.le
    · have hz : (b : ℤ) * α = (a : ℤ) * (l + 1) := by push_cast at heq; linarith
      exact_mod_cast hz.le
  · intro h
    have hz : (b : ℤ) * α ≤ (a : ℤ) * (l + 1) := by exact_mod_cast h
    rcases lt_or_eq_of_le hz with hlt | heq
    · refine Or.inl ?_
      push_cast
      linarith
    · have hαpos : 0 < α := by
        rcases Nat.eq_zero_or_pos α with h0 | h0
        · rw [h0] at heq
          simp only [Nat.cast_zero, mul_zero] at heq
          nlinarith
        · exact h0
      refine Or.inr ⟨?_, by omega⟩
      push_cast
      linarith

end HJO.Paths
