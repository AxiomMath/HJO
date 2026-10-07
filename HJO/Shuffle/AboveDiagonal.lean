/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Nat.Find
public import HJO.Paths.Basic
public meta import HJO.Attr

/-! # Above-diagonal rational paths and their statistics

The compositional rational shuffle identity is usually stated over the *above-diagonal*
parking functions of the `aN × bN` rectangle, while every consumer in this library wants the
*below-diagonal* ones of `HJO.Paths` and `HJO.ParkingFunctions`. This file carries the
above-diagonal path vocabulary, on the same height-vector encoding the below-diagonal side uses,
so that the half turn `(x, y) ↦ (aN - x, bN - y)` of the rectangle is a map of height vectors
rather than a change of representation.

Above and below diagonal are literally the two orientations of one inequality: `IsBelowDiagonal`
writes `y_r ≤ ⌊br/a⌋` as `a y_r ≤ b r`, and `IsAboveDiagonal` writes `ŷ_r ≥ ⌈br/a⌉` as
`b r ≤ a ŷ_r`. No floor or ceiling enters either predicate; the ceiling appears only in the area,
where `Nat.mul_sub_div_add_mul_ceilDiv` is what makes the two areas agree under the half turn.

## Main definitions

* `HJO.Paths.IsAboveDiagonal`: the above-diagonal `(aN, bN)`-paths inside `HJO.Paths.Heights`.
* `HJO.Paths.northSteps`: the north steps of a rational path, each named by its foot.
* `HJO.Paths.aboveArea`: `∑_{r=1}^{aN-1}(ŷ_r - ⌈br/a⌉)`, the area above the diagonal.
* `HJO.Paths.aboveCells`, `HJO.Paths.aboveArm`, `HJO.Paths.aboveLeg`,
  `HJO.Paths.aboveHookCount`: the diagram above the path and Macdonald's hook condition on it.
* `HJO.Paths.HasAboveReturns`: the above-diagonal analogue of `HJO.Paths.HasReturns`.

## Main results

* `HJO.Paths.mem_northSteps_iff`: the north step `(c, i)` has `c < aN` and `ŷ_c ≤ i < ŷ_{c+1}`,
  which is how every consumer reads `HJO.Paths.northSteps` without unfolding its `biUnion`.
* `HJO.Paths.aboveHookCount_eq_card_filter`: `ĥ(P̂)` as one filter on the raw cell window, the
  shape the half turn of the rectangle reindexes.
* `HJO.Paths.aboveHookCount_le_card_aboveCells`: `ĥ(P̂)` is at most the number of cells above the
  path.
* `HJO.Paths.lastBelow_eq_zero_iff`: `Â_j = 0` exactly when the path is at height `≥ j` at every
  positive abscissa, which inside the cell window `1 ≤ j ≤ bN` says that row `j` of the diagram is
  empty.

## Implementation notes

`HJO.Paths.IsAboveDiagonal`, `HJO.Paths.northSteps`, `HJO.Paths.aboveArea`, `HJO.Paths.aboveCells`,
`HJO.Paths.lastBelow`, `HJO.Paths.aboveArm`, `HJO.Paths.aboveLeg`, `HJO.Paths.HasAboveReturns` and
`Nat.mul_sub_div_add_mul_ceilDiv` all live in this file, together with
`HJO.Paths.lastBelow_eq_zero_iff`.

`HJO.Paths.aboveHookCount` is defined here too, with its two API lemmas
`HJO.Paths.aboveHookCount_eq_card_filter` and `HJO.Paths.aboveHookCount_le_card_aboveCells`, which
let `ĥ` be bounded and reindexed without unfolding it.

## References

This file formalises the definitions `HJO.Paths.IsAboveDiagonal`, `HJO.Paths.northSteps`,
`HJO.Paths.aboveArea`, `HJO.Paths.aboveCells`, `HJO.Paths.aboveHookCount` and
`HJO.Paths.HasAboveReturns`, and the lemma `Nat.mul_sub_div_add_mul_ceilDiv`.
-/

@[expose] public section

open Finset

/-! ### Complementing a floor -/

/-- Splitting an exact quotient at an arbitrary point: if `a ∣ m` and `k ≤ m`, the floor of the
lower part `m - k` and the ceiling of the upper part `k` add up to `m / a`. This is the `ℕ` form
of `⌊-x⌋ = -⌈x⌉`; it is not in Mathlib. -/
private theorem Nat.sub_div_add_ceilDiv_of_dvd {a m k : ℕ} (hm : a ∣ m) (hk : k ≤ m) :
    (m - k) / a + k ⌈/⌉ a = m / a := by
  obtain rfl | ha := Nat.eq_zero_or_pos a
  · obtain rfl := Nat.zero_dvd.1 hm
    simp [Nat.le_zero.1 hk]
  obtain ⟨M, rfl⟩ := hm
  rw [Nat.mul_div_cancel_left _ ha]
  have hk' : k ≤ a * (k ⌈/⌉ a) := (_root_.ceilDiv_le_iff_le_mul ha).1 le_rfl
  have hcM : k ⌈/⌉ a ≤ M := (_root_.ceilDiv_le_iff_le_mul ha).2 hk
  have hmul : a * (k ⌈/⌉ a) ≤ a * M := Nat.mul_le_mul_left _ hcM
  have hlt : a * (k ⌈/⌉ a) < k + a := by
    rcases Nat.eq_zero_or_pos (k ⌈/⌉ a) with h | h
    · rw [h]; omega
    · have h2 : a * (k ⌈/⌉ a - 1) < k :=
        Nat.lt_of_not_le fun hh => absurd ((_root_.ceilDiv_le_iff_le_mul ha).2 hh) (by omega)
      rw [Nat.mul_sub, Nat.mul_one] at h2
      have h3 : a ≤ a * (k ⌈/⌉ a) := Nat.le_mul_of_pos_right a h
      omega
  have key : a * M - k = a * (M - k ⌈/⌉ a) + (a * (k ⌈/⌉ a) - k) := by
    rw [Nat.mul_sub]; omega
  rw [key, Nat.mul_add_div ha, Nat.div_eq_of_lt (by omega)]
  omega

/-- Complementing a floor: for `0 < a` and `r ≤ aN`, the floor `⌊b(aN - r)/a⌋` of the reflected
coordinate and the ceiling `⌈br/a⌉` of the original one add up to `bN`. Equivalently
`⌊b(aN - r)/a⌋ = bN - ⌈br/a⌉`, by `Nat.eq_sub_of_add_eq`. -/
@[hjo "lem_floor_ceil_complement"]
theorem Nat.mul_sub_div_add_mul_ceilDiv {a b N r : ℕ} (ha : 0 < a) (hr : r ≤ a * N) :
    b * (a * N - r) / a + b * r ⌈/⌉ a = b * N := by
  have hsub : b * (a * N - r) = a * (b * N) - b * r := by rw [Nat.mul_sub, mul_left_comm]
  have hle : b * r ≤ a * (b * N) := by
    rw [mul_left_comm]; exact Nat.mul_le_mul_left _ hr
  rw [hsub, Nat.sub_div_add_ceilDiv_of_dvd (Dvd.intro _ rfl) hle, Nat.mul_div_cancel_left _ ha]

namespace HJO.Paths

/-! ### The above-diagonal paths -/

/-- `y` is an above-diagonal `(aN, bN)`-path: `0 = ŷ_0 ≤ ŷ_1 ≤ ⋯ ≤ ŷ_{aN} = bN` with
`ŷ_r ≥ ⌈br/a⌉`, the last condition written multiplicatively as `b r ≤ a ŷ_r`. This is
`IsBelowDiagonal` with the diagonal inequality reversed, the two being exchanged by the half turn
of the rectangle. -/
@[hjo "def_above_path"]
def IsAboveDiagonal {a b N : ℕ} (y : Heights a b N) : Prop :=
  ht y 0 = 0 ∧ ht y (a * N) = b * N ∧ (∀ r < a * N, ht y r ≤ ht y (r + 1)) ∧
    ∀ r ≤ a * N, b * r ≤ a * ht y r

instance instDecidableIsAboveDiagonal {a b N : ℕ} (y : Heights a b N) :
    Decidable (IsAboveDiagonal y) := by
  unfold IsAboveDiagonal; infer_instance

/-- The north steps of the rational path with height vector `y`, each named by its foot: the
lattice points `(s, i)` with `s < aN` and `ŷ_s ≤ i < ŷ_{s+1}`, the point `(s, i)` standing for the
unit segment from `(s, i)` to `(s, i + 1)`. The column of a north step is its first coordinate,
and column `s` contributes `ŷ_{s+1} - ŷ_s` of them, so an above-diagonal or below-diagonal
`(aN, bN)`-path has `bN` north steps in all. -/
@[hjo "def_above_north_steps"]
def northSteps {a b N : ℕ} (y : Heights a b N) : Finset (ℕ × ℕ) :=
  (Finset.range (a * N)).biUnion fun s => {s} ×ˢ Finset.Ico (ht y s) (ht y (s + 1))

/-- Membership in `HJO.Paths.northSteps`, read off the `biUnion`: the lattice point `P` is a north
step of `y` exactly when its column is inside the rectangle and its ordinate is one of the heights
that column climbs through. -/
theorem mem_northSteps_iff {a b N : ℕ} {y : Heights a b N} {P : ℕ × ℕ} :
    P ∈ northSteps y ↔ P.1 < a * N ∧ ht y P.1 ≤ P.2 ∧ P.2 < ht y (P.1 + 1) := by
  simp [northSteps, and_assoc, Prod.ext_iff]

/-- The area of the above-diagonal path with height vector `y`: the number
`∑_{r=1}^{aN-1} (ŷ_r - ⌈br/a⌉)` of full lattice squares between the path and the diagonal. On
paths satisfying `IsAboveDiagonal` the column bounds make every difference nonnegative before the
truncated subtraction of `ℕ` is applied. This is the mirror of `HJO.Paths.area` under the half turn
of the rectangle. -/
@[hjo "def_above_area"]
def aboveArea {a b N : ℕ} (y : Heights a b N) : ℕ :=
  ∑ r ∈ Finset.Ico 1 (a * N), (ht y r - b * r ⌈/⌉ a)

/-! ### The diagram above a path -/

/-- The cells of the above-diagonal path with height vector `y`: the pairs `(r, j)` with
`1 ≤ r < aN` and `ŷ_r < j ≤ bN`, the pair `(r, j)` standing for the unit square of the column of
abscissa `r` lying between the ordinates `j - 1` and `j`, that is for a square of that column
strictly above the path. This is the mirror under the half turn of the rectangle of the cells
`1 ≤ i ≤ y_r` of a below-diagonal path, which `hookCount` filters out of the same window. -/
@[hjo "def_above_arm_leg"]
def aboveCells {a b N : ℕ} (y : Heights a b N) : Finset (ℕ × ℕ) :=
  {p ∈ Finset.Ico 1 (a * N) ×ˢ Finset.Icc 1 (b * N) | ht y p.1 < p.2}

@[simp]
theorem mem_aboveCells {a b N : ℕ} {y : Heights a b N} {p : ℕ × ℕ} :
    p ∈ aboveCells y ↔ 1 ≤ p.1 ∧ p.1 < a * N ∧ ht y p.1 < p.2 ∧ p.2 ≤ b * N := by
  simp only [aboveCells, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc]
  omega

/-- `Â_j = max {r : 0 ≤ r ≤ aN and ŷ_r < j}`, the last abscissa at which the path with height
vector `y` is still strictly below height `j`, taken to be `0` when no abscissa is — on an
above-diagonal path only for `j = 0`, where there is no cell, since `ŷ_0 = 0` puts `r = 0` in the
set for every `j ≥ 1`. By monotonicity of the heights, row `j` of the diagram of an
above-diagonal path is the segment `1 ≤ r ≤ Â_j` of columns, so `Â_j` is the length of that row and
the arm of a cell `(r, j)` is `Â_j - r`. This is the mirror of the minimum `firstReach` of the
below-diagonal side. -/
def lastBelow {a b N : ℕ} (y : Heights a b N) (j : ℕ) : ℕ :=
  Nat.findGreatest (fun r => ht y r < j) (a * N)

theorem lastBelow_le {a b N : ℕ} (y : Heights a b N) (j : ℕ) : lastBelow y j ≤ a * N :=
  Nat.findGreatest_le _

theorem le_lastBelow {a b N : ℕ} {y : Heights a b N} {r j : ℕ} (hr : r ≤ a * N)
    (h : ht y r < j) : r ≤ lastBelow y j :=
  Nat.le_findGreatest hr h

/-- On an above-diagonal path the maximum defining `Â_j` is attained for every `j ≥ 1`: the set
contains `r = 0`, since `ŷ_0 = 0 < j`. -/
theorem IsAboveDiagonal.ht_lastBelow_lt {a b N : ℕ} {y : Heights a b N} (hy : IsAboveDiagonal y)
    {j : ℕ} (hj : 0 < j) : ht y (lastBelow y j) < j :=
  Nat.findGreatest_spec (P := fun r => ht y r < j) (m := 0) (Nat.zero_le _)
    (by rw [hy.1]; exact hj)

/-- `Â_j` is `0` exactly when no positive abscissa `r ≤ aN` has the path below height `j`. The
maximum is over a set that always contains `r = 0`, so this is an empty *row* and not a failure of
the maximum to be attained, and it is not confined to `j = 0`: it holds at `j = 1` on the
above-diagonal staircase `(ŷ_0, …, ŷ_3) = (0, 1, 2, 3)` of `a = b = 1`, `N = 3`. Inside the window
`1 ≤ j ≤ bN` that a cell of `aboveCells` lives in, the condition is exactly the emptiness of row
`j` of the diagram: `ŷ_{aN} = bN ≥ j` keeps `r = aN` out of the set, so the abscissae left are the
`1 ≤ r < aN` of the cells. Off that window the two part company, and the abscissa `aN` is why —
on that same staircase row `4` of the diagram is empty while `Â_4 = 3`, so the bound `r ≤ aN` in
the statement is not cosmetic. -/
theorem lastBelow_eq_zero_iff {a b N : ℕ} {y : Heights a b N} {j : ℕ} :
    lastBelow y j = 0 ↔ ∀ r, 0 < r → r ≤ a * N → j ≤ ht y r := by
  rw [lastBelow, Nat.findGreatest_eq_zero_iff]
  exact ⟨fun h r hr hra => Nat.le_of_not_lt (h hr hra),
    fun h _ hr hra => Nat.not_lt.2 (h _ hr hra)⟩

/-- The arm `Â_j - r` of the cell `(r, j)` of the above-diagonal path with height vector `y`, the
number of cells strictly to its right in its row of the diagram cut out by the path. The
subtraction is truncated, which is harmless on a cell: there `ŷ_r < j`, so `r ≤ Â_j`. -/
@[hjo "def_above_arm_leg"]
def aboveArm {a b N : ℕ} (y : Heights a b N) (r j : ℕ) : ℕ := lastBelow y j - r

/-- The leg `j - 1 - ŷ_r` of the cell `(r, j)` of the above-diagonal path with height vector `y`,
the number of cells strictly below it in its column of the diagram cut out by the path. The
subtraction is truncated, which is harmless on a cell: there `ŷ_r < j`. -/
@[hjo "def_above_arm_leg"]
def aboveLeg {a b N : ℕ} (y : Heights a b N) (r j : ℕ) : ℕ := j - 1 - ht y r

/-- The above-diagonal hook count `ĥ(P̂)`: the number of cells `(r, j)` of the above-diagonal path
with height vector `y` whose arm and leg satisfy `b⋅arm ≤ a(leg + 1)` and `a⋅leg < b(arm + 1)`.
The first inequality is weak and the second strict, exactly as in `hookCount`; the two definitions
impose literally the same pair of conditions, on the arm and leg of their own side. -/
@[hjo "def_above_hook"]
def aboveHookCount {a b N : ℕ} (y : Heights a b N) : ℕ :=
  #{p ∈ aboveCells y | b * aboveArm y p.1 p.2 ≤ a * (aboveLeg y p.1 p.2 + 1) ∧
      a * aboveLeg y p.1 p.2 < b * (aboveArm y p.1 p.2 + 1)}

/-- `ĥ(P̂)` as a count over the raw cell window `1 ≤ r < aN`, `1 ≤ j ≤ bN`, the shape in which the
below-diagonal `hookCount` is written: the two hook counts are then two filters on one product,
which is what lets the half turn of the rectangle be a reindexing of it. -/
theorem aboveHookCount_eq_card_filter {a b N : ℕ} (y : Heights a b N) :
    aboveHookCount y = #{p ∈ Finset.Ico 1 (a * N) ×ˢ Finset.Icc 1 (b * N) | ht y p.1 < p.2 ∧
      b * aboveArm y p.1 p.2 ≤ a * (aboveLeg y p.1 p.2 + 1) ∧
        a * aboveLeg y p.1 p.2 < b * (aboveArm y p.1 p.2 + 1)} := by
  rw [aboveHookCount, aboveCells, Finset.filter_filter]

/-- At most every cell of the diagram above the path passes the hook condition. -/
theorem aboveHookCount_le_card_aboveCells {a b N : ℕ} (y : Heights a b N) :
    aboveHookCount y ≤ #(aboveCells y) :=
  Finset.card_filter_le _ _

/-! ### The return composition of an above-diagonal path -/

/-- `y` is an above-diagonal `(aN, bN)`-path whose return composition is `α`: the parts of `α` are
positive and sum to `N`, and the ranks `0 = k_0 < k_1 < ⋯ < k_ℓ = N` with `ŷ_{ka} = kb` are
*exactly* the partial sums of `α`, so a path with an unrequested return is excluded. This is
`HJO.Paths.HasReturns` with the diagonal inequality reversed, the two being exchanged, at the
reversed composition, by the half turn of the rectangle. -/
@[hjo "def_above_returns"]
def HasAboveReturns {a b N : ℕ} (α : List ℕ) (y : Heights a b N) : Prop :=
  IsAboveDiagonal y ∧ (∀ x ∈ α, 0 < x) ∧ α.sum = N ∧
    ∀ k ≤ N, (ht y (a * k) = b * k ↔ k ∈ α.scanl (· + ·) 0)

instance instDecidableHasAboveReturns {a b N : ℕ} (α : List ℕ) (y : Heights a b N) :
    Decidable (HasAboveReturns α y) := by
  unfold HasAboveReturns; infer_instance

end HJO.Paths
