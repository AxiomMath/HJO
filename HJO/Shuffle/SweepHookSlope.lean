/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import HJO.Shuffle.SweepHookCells
public meta import HJO.Attr

/-! # The arm and leg of the marked cell, and the two slope comparisons cleared of denominators

`HJO.Paths.hook_slope_iff_exists_levelCrosses` compares the slope `b/a` of the level line against
the two slopes a cell's hook offers, `arm/(leg+1)` and `(arm+1)/leg`. Those are comparisons of
rationals; the rank comparisons of `HJO.Paths.abovePointRank_lt_top_of_column_iff` and
`HJO.Paths.abovePointRank_eastRight_lt_head_iff` are comparisons of integers with the denominators
already cleared. This file supplies the two clearings, and — completing
`HJO/Shuffle/SweepHookCells.lean` — the arm and the leg of the cell a crossed pair marks.

## Main results

* `HJO.Paths.aboveArm_succ_succ`, `arm(s+1, i+1) = c - s - 1`.
* `HJO.Paths.aboveLeg_succ_succ`,
  `leg(s+1, i+1) = i - ŷ_{s+1}`.
* `HJO.Paths.div_le_div_iff_mul_le_mul`.
* `HJO.Paths.lt_div_iff_mul_lt_mul`.

## Implementation notes

### `HJO.Paths.lt_div_iff_mul_lt_mul` and the `+∞` convention

The hook condition is usually written with `(α+1)/λ` read as `+∞` when `λ = 0`, so that it is a
single iff. Lean's `ℚ` division does the opposite — `(α+1)/0 = 0` — so the iff, transcribed
literally with `ℚ` division, would be *false* at `λ = 0`: its left side would read `a/b < 0`, which
fails, while the right side `aλ < b(α+1)` holds. Rather than introduce an extended rational line
for one lemma, the statement is the two cases the convention encodes: for `λ ≥ 1` the rational
comparison and the cleared one are equivalent, and at `λ = 0` the cleared one holds outright. That
is exactly what the standard argument establishes, one case at a time, and it is what
`HJO.Paths.hook_slope_iff_exists_levelCrosses` needs — it reads the cleared form.

### `0 < b`, not `1 < b`

The standard arguments for both assume `b > 1`: `HJO.Paths.div_le_div_iff_mul_le_mul` to make
`b(λ+1)` a positive rational and
`HJO.Paths.lt_div_iff_mul_lt_mul` to make `b(α+1) ≥ b > 1 > 0 = aλ` at `λ = 0`. Positivity is all
either argument uses, so `0 < b` is what is carried. (The same over-strong `> 1` appears in the
proof of `HJO.Paths.abovePointRank_eastRight_lt_head_iff`; see
`HJO.Paths.abovePointRank_eastRight_lt_head_iff`.)

### Which hypotheses the arm and leg lemmas need

`HJO.Paths.aboveLeg_succ_succ` needs none of the three: `leg(r, j) = j - 1 - ŷ_r` by definition,
so at `j = i+1` the value is `i - ŷ_{s+1}` as an identity of truncated subtractions, whatever
`s`, `i` and the path do. The standard argument invokes `HJO.Paths.mem_aboveCells_of_mem_northSteps`
there only to justify calling the pair a cell, which the equation does not read.
`HJO.Paths.aboveArm_succ_succ` does need the path
above-diagonal and `(c,i)` to be a north step, because its content is `Â_{i+1} = c`
(`HJO.Paths.lastBelow_succ_of_mem_northSteps`); it does *not* need `s + 1 ≤ c`, the conclusion
being a truncated subtraction either way.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section "The sweep process", for Lemmas
`HJO.Paths.aboveArm_succ_succ`, `HJO.Paths.aboveLeg_succ_succ`,
`HJO.Paths.div_le_div_iff_mul_le_mul` and `HJO.Paths.lt_div_iff_mul_lt_mul`, using
`HJO.Paths.IsAboveDiagonal`, `HJO.Paths.northSteps` and `HJO.Paths.aboveCells`.
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### The arm and the leg of the marked cell -/

/-- **The arm of the marked cell is the column gap.** `HJO.Paths.aboveArm_succ_succ`: for a
north step `(c,i)`, the arm of the cell `(s+1, i+1)` is `c - s - 1`.

`HJO.Paths.aboveArm` is `Â_j - r` by definition, so the whole content is `Â_{i+1} = c`, which is
`HJO.Paths.lastBelow_succ_of_mem_northSteps`. The `s + 1 ≤ c` is not needed: the
conclusion is a truncated subtraction on either side of that bound. -/
@[hjo "lem_sweep_cell_arm"]
theorem aboveArm_succ_succ {y : Heights a b N} (hy : IsAboveDiagonal y) (s : ℕ) {u : ℕ × ℕ}
    (hu : u ∈ northSteps y) : aboveArm y (s + 1) (u.2 + 1) = u.1 - (s + 1) := by
  rw [aboveArm, lastBelow_succ_of_mem_northSteps hy hu]

/-- **The leg of the marked cell is the height gap.** `HJO.Paths.aboveLeg_succ_succ`: the leg
of the cell `(s+1, i+1)` is `i - ŷ_{s+1}`.

`HJO.Paths.aboveLeg` is `j - 1 - ŷ_r` by definition, so at `j = i + 1` this is an identity of
truncated subtractions and needs no hypothesis at all — neither the path being above-diagonal, nor
`(c,i)` being a north step, nor `s + 1 ≤ c`. The standard argument invokes
`HJO.Paths.mem_aboveCells_of_mem_northSteps` here only to justify calling `(s+1, i+1)` a cell, which
the equation does not read. -/
@[hjo "lem_sweep_cell_leg"]
theorem aboveLeg_succ_succ (y : Heights a b N) (s i : ℕ) :
    aboveLeg y (s + 1) (i + 1) = i - ht y (s + 1) := by
  rw [aboveLeg, Nat.add_sub_cancel]

/-! ### Clearing the denominators -/

/-- **The lower slope comparison, cleared.** `HJO.Paths.div_le_div_iff_mul_le_mul`:
`α/(λ+1) ≤ a/b` exactly when `bα ≤ a(λ+1)`.

Both denominators are positive — `λ + 1 ≥ 1` always and `b ≥ 1` by hypothesis — so this is
`div_le_div_iff₀` and a cast. The standard argument assumes `b > 1`; positivity is all it
uses. -/
@[hjo "lem_sweep_clear_lower"]
theorem div_le_div_iff_mul_le_mul (hb : 0 < b) (α l : ℕ) :
    (α : ℚ) / ((l : ℚ) + 1) ≤ (a : ℚ) / (b : ℚ) ↔ b * α ≤ a * (l + 1) := by
  have hl : (0 : ℚ) < (l : ℚ) + 1 := by positivity
  have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  rw [div_le_div_iff₀ hl hbq]
  constructor
  · intro h
    have hz : (b : ℚ) * α ≤ (a : ℚ) * ((l : ℚ) + 1) := by linarith
    have : ((b * α : ℕ) : ℚ) ≤ ((a * (l + 1) : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have hz : ((b * α : ℕ) : ℚ) ≤ ((a * (l + 1) : ℕ) : ℚ) := by exact_mod_cast h
    push_cast at hz
    linarith

/-- **The upper slope comparison, cleared.** `HJO.Paths.lt_div_iff_mul_lt_mul`:
`a/b < (α+1)/λ` exactly when `aλ < b(α+1)`, reading `(α+1)/λ` as `+∞` at `λ = 0`.

Stated as the two cases that convention encodes, because Lean's `ℚ` division sends `(α+1)/0` to `0`
rather than to `+∞` and a literal transcription would therefore be false there; see the module
docstring. The `λ = 0` half is where the `b > 1` appears, and `0 < b` is all it uses:
`aλ = 0 < b ≤ b(α+1)`. -/
@[hjo "lem_sweep_clear_upper"]
theorem lt_div_iff_mul_lt_mul (hb : 0 < b) (α l : ℕ) :
    (0 < l → ((a : ℚ) / (b : ℚ) < ((α : ℚ) + 1) / (l : ℚ) ↔ a * l < b * (α + 1))) ∧
      (l = 0 → a * l < b * (α + 1)) := by
  have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  refine ⟨fun hlpos => ?_, fun hl0 => ?_⟩
  · have hlq : (0 : ℚ) < (l : ℚ) := by exact_mod_cast hlpos
    rw [div_lt_div_iff₀ hbq hlq]
    constructor
    · intro h
      have hz : ((a * l : ℕ) : ℚ) < ((b * (α + 1) : ℕ) : ℚ) := by push_cast; linarith
      exact_mod_cast hz
    · intro h
      have hz : ((a * l : ℕ) : ℚ) < ((b * (α + 1) : ℕ) : ℚ) := by exact_mod_cast h
      push_cast at hz
      linarith
  · rw [hl0, Nat.mul_zero]
    calc 0 < b := hb
      _ = b * 1 := by rw [Nat.mul_one]
      _ ≤ b * (α + 1) := Nat.mul_le_mul_left b (by omega)

end HJO.Paths
