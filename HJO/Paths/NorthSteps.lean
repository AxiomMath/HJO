/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Defs
public import HJO.Paths.ReturnPath
public import HJO.Shuffle.AboveDiagonal
public meta import HJO.Attr

/-! # The north steps of a below-diagonal path

A below-diagonal `(aN, bN)`-path enters the column of abscissa `r` at height `y_{r-1}` and climbs
to `y_r` there, so its north steps are the `y_r - y_{r-1}` unit segments from `(r, j)` to
`(r, j + 1)` with `y_{r-1} ≤ j ≤ y_r - 1`, one family for each `1 ≤ r ≤ aN`. Naming such a segment
by its foot `(r, j)` puts it on the *right*-hand edge of the column it climbs. An above-diagonal
path climbs first and goes east afterwards, so `HJO.Paths.northSteps` carries the same segments on
the *left*-hand edge: there the feet are the `(s, i)` with `s < aN` and `ŷ_s ≤ i ≤ ŷ_{s+1} - 1`.
That shift of one in the abscissa is the whole difference between the two notions, and it is what
makes the half turn `(x, y) ↦ (aN - x, bN - y - 1)` of the rectangle carry the north steps of a
path to the north steps of its half turn.

Naming a north step by its foot and naming it by the *height* of that foot are two indexings of one
set: on a below-diagonal path every height `j < bN` is the foot of exactly one north step, the one
in the column `A_{j+1} = min {r : y_r > j}` that `HJO.ParkingFunctions.column` records, and that
indexing by `Fin (bN)` is the one a parking function labels.

## Main definitions

* `HJO.Paths.belowNorthSteps`: the north steps of a below-diagonal path, each named by its foot.

## Main results

* `HJO.Paths.mem_belowNorthSteps`: the point `(r, j)` is a north step exactly when `1 ≤ r ≤ aN` and
  `y_{r-1} ≤ j < y_r`, which is how a consumer reads the definition without unfolding its `biUnion`.
* `HJO.Paths.belowNorthSteps_eq_image_northSteps`: the north steps of a below-diagonal path are
  those of `HJO.Paths.northSteps` shifted one step east.
* `HJO.Paths.IsBelowDiagonal.card_belowNorthSteps`: a below-diagonal path has exactly `bN` north
  steps, one for each height it climbs through.
* `HJO.ParkingFunctions.mem_belowNorthSteps_iff_eq_column`,
  `HJO.ParkingFunctions.belowNorthSteps_eq_image_column`: the north steps are exactly the points
  `(A_{j+1}, j)` for `j < bN`, so indexing them by the height of their feet is bijective.

## Implementation notes

The definition is total on `HJO.Paths.Heights`, as every path statistic of this library is: the
geometric reading needs `HJO.Paths.IsBelowDiagonal`, but forming the set does not, and the
cardinality already holds for a merely monotone height function
(`HJO.Paths.card_belowNorthSteps`). It is written over the columns `s < aN` as the pairs
`(s + 1, j)` with `y_s ≤ j < y_{s+1}`, which avoids the truncated subtraction of `ℕ` inside the
definition;
`HJO.Paths.mem_belowNorthSteps` then reads it back in the `1`-based indexing of the columns, where
`y_{r-1}` is harmless because `1 ≤ r`.

The below-diagonal statistics of this library are the unprefixed ones and the above-diagonal
ones carry `above`, but `HJO.Paths.northSteps` was given to the above-diagonal set of feet; hence
the prefix on this one rather than on that one.

The half turn is recorded in the foot-height indexing, as
`HJO.ParkingFunctions.aboveColumn_halfTurn`, since that is the indexing a parking function labels;
`HJO.ParkingFunctions.mem_belowNorthSteps_iff_eq_column` and
`HJO.ParkingFunctions.mem_northSteps_iff_eq_aboveColumn` are what turn it into a statement about
the two sets of feet.

## References

Part of the proof of the compositional rational shuffle identity: the definition
`HJO.Paths.belowNorthSteps`.
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-- The north steps of the below-diagonal path with height vector `y`, each named by its foot: the
lattice points `(r, j)` with `1 ≤ r ≤ aN` and `y_{r-1} ≤ j ≤ y_r - 1`, the point `(r, j)` standing
for the unit segment from `(r, j)` to `(r, j + 1)`. The column of a north step is its first
coordinate, so column `r` carries `y_r - y_{r-1}` of them and a below-diagonal path has `bN` in
all. The abscissa of a north step is the right-hand edge of the column it climbs, a below-diagonal
path going east before it climbs; `HJO.Paths.northSteps` is the same set of segments named by the
left-hand edge, which is where an above-diagonal path climbs. -/
@[hjo "def_north_steps"]
def belowNorthSteps (y : Heights a b N) : Finset (ℕ × ℕ) :=
  (range (a * N)).biUnion fun s => {s + 1} ×ˢ Ico (ht y s) (ht y (s + 1))

/-- Membership in `HJO.Paths.belowNorthSteps`, in the `1`-based indexing of the columns: the
lattice point `P` is a north step of `y` exactly when its column is one of `1, …, aN` and its
ordinate is one of the heights that column climbs through. -/
theorem mem_belowNorthSteps {y : Heights a b N} {P : ℕ × ℕ} :
    P ∈ belowNorthSteps y ↔
      0 < P.1 ∧ P.1 ≤ a * N ∧ ht y (P.1 - 1) ≤ P.2 ∧ P.2 < ht y P.1 := by
  obtain ⟨r, j⟩ := P
  simp only [belowNorthSteps, mem_biUnion, mem_range, mem_product, mem_singleton, mem_Ico]
  constructor
  · rintro ⟨s, hs, rfl, h1, h2⟩
    simpa using ⟨by omega, h1, h2⟩
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨r - 1, by omega, by omega, h2, ?_⟩
    rwa [show r - 1 + 1 = r by omega]

/-- Membership in `HJO.Paths.belowNorthSteps` at the column `s + 1`, the column whose left-hand
edge is the abscissa `s`: this is the form in which `HJO.Paths.northSteps` names the same
segments. -/
theorem mem_belowNorthSteps_succ {y : Heights a b N} {s j : ℕ} :
    (s + 1, j) ∈ belowNorthSteps y ↔ s < a * N ∧ ht y s ≤ j ∧ j < ht y (s + 1) := by
  simp only [mem_belowNorthSteps, Nat.add_sub_cancel]
  omega

/-- The north steps of a path named by the right-hand edge of their columns are those named by the
left-hand edge shifted one step east: `belowNorthSteps` and `HJO.Paths.northSteps` are the two
namings of one set of segments. -/
theorem belowNorthSteps_eq_image_northSteps (y : Heights a b N) :
    belowNorthSteps y = (northSteps y).image fun P => (P.1 + 1, P.2) := by
  ext P
  obtain ⟨r, j⟩ := P
  simp only [mem_belowNorthSteps, mem_image, mem_northSteps_iff, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨r - 1, j, ⟨by omega, h2, ?_⟩, by omega, rfl⟩
    rwa [show r - 1 + 1 = r by omega]
  · rintro ⟨s, i, ⟨hs, h1, h2⟩, rfl, rfl⟩
    simpa using ⟨by omega, h1, h2⟩

/-- A path with monotone heights has one north step for each height between its two endpoints: the
columns climb through disjoint intervals of heights whose lengths telescope. -/
theorem card_belowNorthSteps {y : Heights a b N} (hmono : Monotone (ht y)) :
    #(belowNorthSteps y) = ht y (a * N) - ht y 0 := by
  rw [belowNorthSteps, card_biUnion fun s _ t _ hst => ?_]
  · rw [Finset.sum_congr rfl fun s _ => card_product _ _, ← Finset.sum_range_tsub hmono]
    exact Finset.sum_congr rfl fun s _ => by simp
  · simp only [Finset.disjoint_left, mem_product, mem_singleton]
    rintro ⟨u, v⟩ ⟨h1, -⟩ ⟨h2, -⟩
    exact hst (by omega)

/-- **A below-diagonal `(aN, bN)`-path has exactly `bN` north steps.** The heights rise from `0` to
`bN`, so each height below `bN` is the foot of exactly one north step. -/
@[simp]
theorem IsBelowDiagonal.card_belowNorthSteps {y : Heights a b N} (hy : IsBelowDiagonal y) :
    #(belowNorthSteps y) = b * N := by
  rw [_root_.HJO.Paths.card_belowNorthSteps hy.ht_mono, hy.1, hy.2.1, Nat.sub_zero]

end HJO.Paths

namespace HJO.ParkingFunctions

variable {a b N : ℕ}

/-- On a below-diagonal path the north steps are named by the height of their feet: `(r, j)` is a
north step exactly when `j < bN` and `r` is the column `A_{j+1}` of the step whose foot is at
height `j`. This is the mirror of `HJO.ParkingFunctions.mem_northSteps_iff_eq_aboveColumn` under the
half turn of the rectangle. -/
theorem mem_belowNorthSteps_iff_eq_column {y : Paths.Heights a b N}
    (hy : Paths.IsBelowDiagonal y) {r j : ℕ} :
    (r, j) ∈ Paths.belowNorthSteps y ↔ j < b * N ∧ r = column y j := by
  rw [Paths.mem_belowNorthSteps]
  dsimp only
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨?_, ?_⟩
    · have hle := hy.ht_mono h1
      rw [hy.2.1] at hle
      omega
    · refine (ReturnPath.firstReach_eq y h1 (by omega) fun r' hr' => ?_).symm
      have := hy.ht_mono (show r' ≤ r - 1 by omega)
      omega
  · rintro ⟨hj, rfl⟩
    have hreach : j + 1 ≤ Paths.ht y (column y j) :=
      ReturnPath.le_ht_firstReach y (by rw [hy.2.1]; omega)
    have hcol : column y j ≤ a * N := by
      have := ReturnPath.firstReach_lt y (j + 1)
      rw [column]
      omega
    have h0 : 0 < column y j := by
      rcases Nat.eq_zero_or_pos (column y j) with h | h
      · rw [h, hy.1] at hreach; omega
      · exact h
    have hprev := ReturnPath.ht_lt_of_lt_firstReach y (i := j + 1) (j := column y j - 1)
      (show column y j - 1 < Paths.firstReach y (j + 1) by rw [← column]; omega)
    exact ⟨h0, hcol, by omega, by omega⟩

/-- The `bN` north steps of a below-diagonal path are exactly the points `(A_{j+1}, j)` for
`j < bN`: indexing a north step by the height of its foot is a bijective indexing of
`HJO.Paths.belowNorthSteps` by `Fin (bN)`, which is what makes a labelling of `Fin (bN)` a
labelling of the north steps. -/
theorem belowNorthSteps_eq_image_column {y : Paths.Heights a b N}
    (hy : Paths.IsBelowDiagonal y) :
    Paths.belowNorthSteps y = (range (b * N)).image fun j => (column y j, j) := by
  ext q
  obtain ⟨r, j⟩ := q
  simp only [mem_image, mem_range, Prod.mk.injEq, mem_belowNorthSteps_iff_eq_column hy]
  constructor
  · rintro ⟨h1, rfl⟩
    exact ⟨j, h1, rfl, rfl⟩
  · rintro ⟨i, hi, rfl, rfl⟩
    exact ⟨hi, rfl⟩

end HJO.ParkingFunctions
