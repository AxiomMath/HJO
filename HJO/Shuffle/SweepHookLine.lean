/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepHookSlope
public meta import HJO.Attr

/-! # A level line crosses both steps exactly when the cell they span passes the hook condition

This is the hinge of
`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv`'s hook count.
An east step and a north step to its right span a cell; the cell has an arm `α` and a leg `λ`; and
the assertion is that some level line crosses both steps **exactly when** that cell passes
Macdonald's hook condition, `α/(λ+1) ≤ a/b < (α+1)/λ`.

Both sides are now available in cleared integer form. The hook condition is
`bα ≤ a(λ+1) ∧ aλ < b(α+1)` by `HJO.Paths.div_le_div_iff_mul_le_mul` and
`HJO.Paths.lt_div_iff_mul_lt_mul`. The crossing condition is an overlap of two half-open rank
intervals, and `HJO.Paths.abovePointRank_eastRight_lt_head_iff` and
`HJO.Paths.abovePointRank_lt_top_of_column_iff` say that the two overlap inequalities are those
same two integer inequalities. So the lemma is: clear the denominators on one side, resolve the
overlap on the other, and observe that what is left is the same pair.

## Main results

* `HJO.Paths.exists_levelCrosses_iff_hook`: the cleared form — some level line crosses both steps
  iff `bα ≤ a(λ+1)` and `aλ < b(α+1)`.
* `HJO.Paths.hook_slope_iff_exists_levelCrosses`,
  with the rational display on the left.

## Implementation notes

### The overlap criterion

`HJO.Paths.exists_mem_inter_Ico` is the one piece of new mathematics: two **nonempty** half-open
integer intervals `[p,q)` and `[r,t)` meet iff `p < t` and `r < q`. Mathlib has the set-level
route — `Set.Ico_inter_Ico : Ico a₁ b₁ ∩ Ico a₂ b₂ = Ico (a₁ ⊔ a₂) (b₁ ⊓ b₂)` together with
`Set.nonempty_Ico` — and it reduces to exactly the `max_lt` and `le_max_left`/`le_max_right`
facts used here. It is written directly rather than routed through `Set.Ico` because the statement
this file needs is an existential over `ℤ` with the two membership conditions spelled out, which is
the
shape `HJO.Paths.LevelCrosses` presents; going through `Set` would add a coercion in each direction
and prove nothing extra. The witness in the backward direction is `max p r`, which is the `a₁ ⊔ a₂`
of the Mathlib lemma.

### Why one overlap inequality is weak

`rk(R) < rk(H)` is the weak one, `bα ≤ a(λ+1)`, and that traces all the way back to the abscissa
tie-break of `HJO.Paths.abovePointRank_lt_iff`: see
`HJO.Paths.abovePointRank_eastRight_lt_head_iff`, where the boundary case `bα = a(λ+1)` is settled
by the tie-break in favour of the crossing surviving. Nothing new happens here; the asymmetry is
inherited.

### The `λ = 0` convention is not collapsed

The display reads `(α+1)/λ` as `+∞` at `λ = 0`, and Lean's `ℚ` division gives `0`
instead, so the right half of the display cannot be written as a bare `ℚ` inequality; see
`HJO.Paths.lt_div_iff_mul_lt_mul` and its module docstring. The rational form below therefore
carries the right half as `0 < λ → a/b < (α+1)/λ`, which is what the convention abbreviates.
**The two cases must not be collapsed back into one**: the collapsed statement is false at
`λ = 0`.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### Two half-open integer intervals meet -/

/-- **Two nonempty half-open integer intervals meet iff each starts before the other ends.** The
witness in the backward direction is `max p r`, which lies in both. This is the set-level
`Set.Ico_inter_Ico` together with `Set.nonempty_Ico`, written out for the existential form
`HJO.Paths.LevelCrosses` presents. -/
theorem exists_mem_inter_Ico {p q r t : ℤ} (hpq : p < q) (hrt : r < t) :
    (∃ η : ℤ, (p ≤ η ∧ η < q) ∧ (r ≤ η ∧ η < t)) ↔ p < t ∧ r < q := by
  constructor
  · rintro ⟨η, ⟨hp, hq⟩, hr, ht⟩
    exact ⟨lt_of_le_of_lt hp ht, lt_of_le_of_lt hr hq⟩
  · rintro ⟨hpt, hrq⟩
    exact ⟨max p r, ⟨le_max_left _ _, max_lt hpq hrq⟩, le_max_right _ _, max_lt hpt hrt⟩

/-! ### The crossing condition, cleared -/

/-- **Some level line crosses both steps exactly when the cleared hook inequalities hold.** The
integer form of `HJO.Paths.hook_slope_iff_exists_levelCrosses`, and the whole of its content.

Each step is crossed by exactly the ranks in a half-open interval: the east step at `s` by
`[rk(R), rk(L))`, since the rank falls along an east step
(`HJO.Paths.abovePointRank_eastRight_lt_eastLeft`), and the north step by `[rk(F), rk(H))`, since
the head outranks the foot by the window. Both are nonempty, so by
`HJO.Paths.exists_mem_inter_Ico` a common line exists iff `rk(R) < rk(H)` and `rk(F) < rk(L)` —
which are `bα ≤ a(λ+1)` and `aλ < b(α+1)` by the two comparisons of `SweepHookCells.lean`. -/
theorem exists_levelCrosses_iff_hook {y : Heights a b N} (ha : 0 < a) (hb : 0 < b) {s : ℕ}
    (hs : s < a * N) {u : ℕ × ℕ} (hu : u ∈ northSteps y) {α l : ℕ} (hα : u.1 = s + 1 + α)
    (hl : u.2 = ht y (s + 1) + l) :
    (∃ η : ℤ, LevelCrosses a b N η (eastLeft y s) (eastRight y s) ∧
        LevelCrosses a b N η u (u.1, u.2 + 1)) ↔
      b * α ≤ a * (l + 1) ∧ a * l < b * (α + 1) := by
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at hs
  have h0 : 0 < a * N := lt_of_le_of_lt (Nat.zero_le s) hs
  have hω : (0 : ℤ) < (attackWindow a N : ℤ) := by
    exact_mod_cast attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
  have hue : (s + 1 + α, ht y (s + 1) + l) ∈ northSteps y := by rw [← hα, ← hl]; exact hu
  -- the two points of the north step, spelled the way the earlier comparisons spell them
  have hrF : ParkingFunctions.abovePointRank a b N u.1 u.2
      = ParkingFunctions.abovePointRank a b N (s + 1 + α) (ht y (s + 1) + l) := by rw [hα, hl]
  have hrH : ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1)
      = ParkingFunctions.abovePointRank a b N (s + 1 + α) (ht y (s + 1) + l + 1) := by rw [hα, hl]
  -- the rank falls along the east step, so its crossing interval is `[rk R, rk L)`
  have hrkR := abovePointRank_eastRight_lt_eastLeft y s hb h0
  have hEiff : ∀ η : ℤ, LevelCrosses a b N η (eastLeft y s) (eastRight y s) ↔
      (ParkingFunctions.abovePointRank a b N (eastRight y s).1 (eastRight y s).2 ≤ η ∧
        η < ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2) := fun η => by
    rw [LevelCrosses, min_eq_right hrkR.le, max_eq_left hrkR.le]
  -- the head outranks the foot, so the north step's interval is `[rk F, rk H)`
  have hsucc : ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1) =
      ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N :=
    abovePointRank_succ a b N u.1 u.2
  have hUiff : ∀ η : ℤ, LevelCrosses a b N η u (u.1, u.2 + 1) ↔
      (ParkingFunctions.abovePointRank a b N u.1 u.2 ≤ η ∧
        η < ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1)) := fun η => by
    rw [levelCrosses_north_iff ha hN, hsucc]
  rw [show (∃ η : ℤ, LevelCrosses a b N η (eastLeft y s) (eastRight y s) ∧
      LevelCrosses a b N η u (u.1, u.2 + 1)) ↔
    (∃ η : ℤ, (ParkingFunctions.abovePointRank a b N (eastRight y s).1 (eastRight y s).2 ≤ η ∧
        η < ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2) ∧
      (ParkingFunctions.abovePointRank a b N u.1 u.2 ≤ η ∧
        η < ParkingFunctions.abovePointRank a b N u.1 (u.2 + 1))) from
      exists_congr fun η => and_congr (hEiff η) (hUiff η)]
  rw [exists_mem_inter_Ico hrkR (by omega)]
  rw [hrH, hrF]
  rw [show ParkingFunctions.abovePointRank a b N (eastRight y s).1 (eastRight y s).2
      = ParkingFunctions.abovePointRank a b N (s + 1) (ht y (s + 1)) from rfl,
    show ParkingFunctions.abovePointRank a b N (eastLeft y s).1 (eastLeft y s).2
      = ParkingFunctions.abovePointRank a b N s (ht y (s + 1)) from rfl,
    abovePointRank_eastRight_lt_head_iff ha hs hue,
    abovePointRank_lt_top_of_column_iff hs hue]

/-! ### The rational display -/

/-- **`HJO.Paths.hook_slope_iff_exists_levelCrosses`.** For an east step at `s` and a north step to
its right, with `α` and `λ` the arm and leg of the cell they span, the hook comparison
`α/(λ+1) ≤ a/b < (α+1)/λ` holds exactly when some level line crosses both steps.

The right half is carried as `0 < λ → a/b < (α+1)/λ`, which is what the `+∞` reading of
`(α+1)/λ` at `λ = 0` abbreviates; Lean's `ℚ` division sends `(α+1)/0` to `0`, so the collapsed
single inequality is *false* there. See the module docstring, and do not collapse the cases.

That `α` and `λ` really are the arm and the leg of a cell is
`HJO.Paths.mem_aboveCells_of_mem_northSteps`, `HJO.Paths.aboveArm_succ_succ` and
`HJO.Paths.aboveLeg_succ_succ`; this statement takes them as the
two offsets directly, which is how they arise. -/
@[hjo "lem_sweep_hook_crossing_line"]
theorem hook_slope_iff_exists_levelCrosses {y : Heights a b N} (ha : 0 < a) (hb : 0 < b) {s : ℕ}
    (hs : s < a * N) {u : ℕ × ℕ} (hu : u ∈ northSteps y) {α l : ℕ} (hα : u.1 = s + 1 + α)
    (hl : u.2 = ht y (s + 1) + l) :
    ((α : ℚ) / ((l : ℚ) + 1) ≤ (a : ℚ) / (b : ℚ) ∧
        (0 < l → (a : ℚ) / (b : ℚ) < ((α : ℚ) + 1) / (l : ℚ))) ↔
      ∃ η : ℤ, LevelCrosses a b N η (eastLeft y s) (eastRight y s) ∧
        LevelCrosses a b N η u (u.1, u.2 + 1) := by
  rw [exists_levelCrosses_iff_hook ha hb hs hu hα hl, div_le_div_iff_mul_le_mul (a := a) hb]
  obtain ⟨hup, hzero⟩ := lt_div_iff_mul_lt_mul (a := a) (b := b) hb α l
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · exact hzero h0
    · exact (hup h0).1 (h h0)
  · intro h h0
    exact (hup h0).2 h

end HJO.Paths
