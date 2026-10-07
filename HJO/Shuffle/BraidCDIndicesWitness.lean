/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidCDIndices
public meta import HJO.Attr

/-! # The type-`C` and type-`D` index dictionary, re-derived at two decided witnesses

`HJO/Shuffle/BraidCDIndices.lean` proves the geometric input of the type-`C` and type-`D`
clauses of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` in general. A general theorem with
a sign, an index, a multiplicity, a shift or a width wrong can still look right, so — exactly as
`HJO.Mellit.gap_typeA_uncond` does for the type-`A` clause — this file runs a **decided instance
through the general theorems** and checks that every number agrees with the value obtained
independently from the decided colourings.

## The two witnesses

Both live on the `(2, 3)`-rectangle with `N = 1`, where `rk̂(x, y) = 6y - 8x`, `ω = 6`,
`θ = 3/7 = 12/28` and `D = 14`, and both take the canonical isolating pair `rk̂(P) ∓ 1/2` of
`HJO.Mellit.isolates_sub_half_add_half`.

* **Type `C`, rank `2`.** The path `HJO.Mellit.cdPathC = (0, 2, 3)` and the point `P = (0, 1)` of
  rank `6`, levels `11/2` and `13/2`. Both components survive the drop, so the witness exercises
  **both** branches of the dictionary: the index `i₀ = 0` where the bottom index falls, and the
  index `1` where nothing moves.
* **Type `D`, rank `1`.** The path `HJO.Mellit.cdPathD = (0, 3, 3)` — flat over the last column, so
  that `(1, 3)` is two consecutive east steps — and the point `P = (1, 3)` of rank `10`, levels
  `19/2` and `21/2`. The corner `(aN, bN)` is *not* usable here: a type-`D` event there has
  `rk̂ = aN` exactly, so no admissible level above `aN` can sit below it and
  `HJO.Mellit.Isolates.fst_lt` fails. A flat stretch strictly inside the rectangle is the smallest
  configuration that works, and it has rank `1`, so the `i ≠ i₀` branch of the type-`D` dictionary
  is **vacuous at this witness** and is not tested here.

## What is checked

| quantity | type `C` (`i = 0`, `i = 1`) | type `D` (`i = 0`) |
|---|---|---|
| top index at `η₊` | `2`, `4` | `3 = n_P - 1` |
| top index at `η₋` | `2`, `4` (unchanged) | `4 = n_P` |
| bottom index at `η₊` | `2 = n_P + 1`, `4` | `2` |
| bottom index at `η₋` | `1 = n_P`, `4` (unchanged) | `2` (unchanged) |
| multiplicity at `η₊` | `1` | `2` |
| multiplicity at `η₋` | `2`, `1` | `3` |
| position at `η₊` | `11/28`, `7/28` | `15/28` |
| position at `η₋` | `13/28`, `9/28` | `1/28` |
| `ζ` | `0` at both levels | `0` at `η₊`, `1` at `η₋` |

The rigid rotation is `1/14 = 2/28` at both witnesses, and at type `C` the positions rise by exactly
that with no wrap. At type `D` the single position rises by `2/28 + θ = 14/28`, from `15/28` to
`29/28`, and **wraps**: `1/28`. That wrap is what carries the extra `z` letter, and it is the reason
the type-`D` prediction is `+1` while the type-`C` one is `0` — the two predictions are checked
against braids computed letter by letter, `ỹ_2` at type `C` and `T_{·} z_1 · ỹ` at type `D`.

## References

This file concerns `HJO.Mellit.floor_crossingAbscissa_antidiag_lo`,
`HJO.Mellit.Isolates.notMem_colouringNorth_lo`, `HJO.Mellit.card_componentCrossingIndices_eq`,
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`. Transcribing A. Mellit, *Toric braids and
`(m, n)`-parking functions*, section 5.
-/

@[expose] public section

namespace HJO.Mellit

open Braid Finset ParkingFunctions Paths Sweep

/-! ### The arithmetic of the `(2, 3)`-rectangle -/

/-- **`rk̂(x, y) = 6y - 8x`** at `a = 2`, `b = 3`, `N = 1`: `(aN+1)N = 3` and `3·(2y - 3x) + x`. -/
theorem pointRank_cd (x y : ℕ) : pointRank 2 3 1 (x, y) = 6 * (y : ℤ) - 8 * (x : ℤ) := by
  rw [pointRank, abovePointRank]
  push_cast
  ring

/-- The attack window of the `(2, 3)`-rectangle is `6`, the rank gap of one north step. -/
theorem attackWindow_cd : attackWindow 2 1 = 6 := by decide

/-- `θ = 3/7` on the `(2, 3)`-rectangle. -/
theorem sweepTheta_cd : sweepTheta 2 3 1 = 3 / 7 := by
  rw [sweepTheta, sweepSlope]
  norm_num

/-- **The rigid rotation of a drop by one on the `(2, 3)`-rectangle is `1/14`**, whichever pair of
levels a distance `1` apart is taken. -/
theorem levelDropShift_cd (ηlo : ℚ) : levelDropShift 2 3 1 ηlo (ηlo + 1) = 1 / 14 := by
  rw [levelDropShift, sweepTheta_cd]
  norm_num

/-! ### The listing of a pinned two-point set -/

/-- The column listing of a pinned colouring half, read off the counting characterisation
`HJO.Mellit.colStep_card_filter_fst_lt` rather than off the sorted list. -/
theorem colStep_of_pinned {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) {P : ℕ × ℕ}
    (hP : P ∈ S) {i : ℕ} (hcount : #({R ∈ S | R.1 < P.1}) = i) : colStep S i = P := by
  rw [← hcount]; exact colStep_card_filter_fst_lt hcol hP

/-! ### The type-`C` witness -/

/-- The type-`C` witness path: the above-diagonal `(2, 3)`-path with heights `(0, 2, 3)`. It turns
north twice in the first column, so `(0, 1)` is two consecutive north steps. -/
def cdPathC : Heights 2 3 1 := ![0, 2, 3]

/-- The lower level of the type-`C` witness pair, `rk̂(0,1) - 1/2 = 11/2`. -/
def cdLoC : ℚ := 11 / 2

/-- The upper level of the type-`C` witness pair, `rk̂(0,1) + 1/2 = 13/2`. -/
def cdHiC : ℚ := 13 / 2

theorem isAboveDiagonal_cdPathC : IsAboveDiagonal cdPathC := by decide

/-- `(0, 1)` is a type-`C` event of the witness: `ŷ_0 = 0 < 1 < 2 = ŷ_1`. -/
theorem eventType_cdPathC : eventType cdPathC (0, 1) = EventType.C := by decide

theorem mem_sweptRegion_cdPathC : ((0, 1) : ℕ × ℕ) ∈ sweptRegion cdPathC := by decide

theorem northSteps_cdPathC : northSteps cdPathC = {(0, 0), (0, 1), (1, 2)} := by decide

theorem eastSteps_cdPathC : eastSteps cdPathC = {(0, 2), (1, 3)} := by decide

theorem isAdmissibleLevel_cdLoC : IsAdmissibleLevel cdLoC := ⟨5, by norm_num [cdLoC]⟩

theorem isAdmissibleLevel_cdHiC : IsAdmissibleLevel cdHiC := ⟨6, by norm_num [cdHiC]⟩

theorem cdLoC_lt_cdHiC : cdHiC = cdLoC + 1 := by norm_num [cdLoC, cdHiC]

theorem lt_cdLoC : ((2 * 1 : ℕ) : ℚ) < cdLoC := by norm_num [cdLoC]

/-- The isolating pair of the type-`C` witness, `rk̂(0,1) ∓ 1/2` with `rk̂(0,1) = 6`. -/
theorem isolates_cdPathC : Isolates 2 3 1 0 1 cdLoC cdHiC := by
  have h := isolates_sub_half_add_half 2 3 1 (X := 0) (Y := 1) (by norm_num) (by norm_num)
  rw [show ((pointRank 2 3 1 (0, 1) : ℤ) : ℚ) = 6 by rw [pointRank_cd]; norm_num] at h
  rw [show (6 : ℚ) - 1 / 2 = cdLoC by norm_num [cdLoC],
    show (6 : ℚ) + 1 / 2 = cdHiC by norm_num [cdHiC]] at h
  exact h

/-- **Both crossed north steps at `η₊ = 13/2`**: `(0, 1)` with `6 < 13/2 < 12` and `(1, 2)` with
`4 < 13/2 < 10`. -/
theorem colouringNorth_cdPathC_hi :
    colouringNorth cdPathC cdHiC = {((0 : ℕ), (1 : ℕ)), ((1 : ℕ), (2 : ℕ))} := by
  ext P
  rw [colouringNorth, Finset.mem_filter, northSteps_cdPathC]
  constructor
  · rintro ⟨hP, h⟩
    revert h
    fin_cases hP <;> norm_num [cdHiC, pointRank_cd, attackWindow_cd]
  · intro hP
    rcases Finset.mem_insert.1 hP with rfl | hP'
    · exact ⟨by decide, by norm_num [cdHiC, pointRank_cd, attackWindow_cd]⟩
    · rw [Finset.mem_singleton] at hP'
      subst hP'
      exact ⟨by decide, by norm_num [cdHiC, pointRank_cd, attackWindow_cd]⟩

/-- **Both crossed north steps at `η₋ = 11/2`**: the one of the first column has dropped to
`(0, 0)`, `0 < 11/2 < 6`, and `(1, 2)` is unchanged. -/
theorem colouringNorth_cdPathC_lo :
    colouringNorth cdPathC cdLoC = {((0 : ℕ), (0 : ℕ)), ((1 : ℕ), (2 : ℕ))} := by
  ext P
  rw [colouringNorth, Finset.mem_filter, northSteps_cdPathC]
  constructor
  · rintro ⟨hP, h⟩
    revert h
    fin_cases hP <;> norm_num [cdLoC, pointRank_cd, attackWindow_cd]
  · intro hP
    rcases Finset.mem_insert.1 hP with rfl | hP'
    · exact ⟨by decide, by norm_num [cdLoC, pointRank_cd, attackWindow_cd]⟩
    · rw [Finset.mem_singleton] at hP'
      subst hP'
      exact ⟨by decide, by norm_num [cdLoC, pointRank_cd, attackWindow_cd]⟩

/-- **The crossed east steps stand still at the type-`C` drop**, both of them: `(0, 2)` with
`4 < η < 12` and `(1, 3)` with `2 < η < 10`, at `η = 11/2` and at `η = 13/2` alike. -/
theorem colouringEast_cdPathC (η : ℚ) (h1 : (4 : ℚ) < η) (h2 : η < 10) :
    colouringEast cdPathC η = {((0 : ℕ), (2 : ℕ)), ((1 : ℕ), (3 : ℕ))} := by
  ext P
  rw [colouringEast, Finset.mem_filter, eastSteps_cdPathC]
  constructor
  · rintro ⟨hP, h⟩
    revert h
    fin_cases hP <;> norm_num [pointRank_cd]
  · intro hP
    rcases Finset.mem_insert.1 hP with rfl | hP'
    · refine ⟨by decide, ?_⟩
      norm_num [pointRank_cd]
      constructor <;> linarith
    · rw [Finset.mem_singleton] at hP'
      subst hP'
      refine ⟨by decide, ?_⟩
      norm_num [pointRank_cd]
      constructor <;> linarith

theorem colouringEast_cdPathC_hi :
    colouringEast cdPathC cdHiC = {((0 : ℕ), (2 : ℕ)), ((1 : ℕ), (3 : ℕ))} :=
  colouringEast_cdPathC cdHiC (by norm_num [cdHiC]) (by norm_num [cdHiC])

theorem colouringEast_cdPathC_lo :
    colouringEast cdPathC cdLoC = {((0 : ℕ), (2 : ℕ)), ((1 : ℕ), (3 : ℕ))} :=
  colouringEast_cdPathC cdLoC (by norm_num [cdLoC]) (by norm_num [cdLoC])

theorem card_colouringNorth_cdPathC_hi : #(colouringNorth cdPathC cdHiC) = 2 := by
  rw [colouringNorth_cdPathC_hi]; decide

theorem card_colouringNorth_cdPathC_lo : #(colouringNorth cdPathC cdLoC) = 2 := by
  rw [colouringNorth_cdPathC_lo]; decide

theorem card_colouringEast_cdPathC_hi : #(colouringEast cdPathC cdHiC) = 2 := by
  rw [colouringEast_cdPathC_hi]; decide

theorem card_colouringEast_cdPathC_lo : #(colouringEast cdPathC cdLoC) = 2 := by
  rw [colouringEast_cdPathC_lo]; decide

/-! ### The column listings of the type-`C` witness -/

theorem colStep_colouringEast_cdPathC_hi_zero :
    colStep (colouringEast cdPathC cdHiC) 0 = (0, 2) :=
  colStep_of_pinned (columnInjective_colouringEast (by norm_num) (by norm_num)
      isAdmissibleLevel_cdHiC cdPathC)
    (by rw [colouringEast_cdPathC_hi]; decide) (by rw [colouringEast_cdPathC_hi]; decide)

theorem colStep_colouringEast_cdPathC_hi_one :
    colStep (colouringEast cdPathC cdHiC) 1 = (1, 3) :=
  colStep_of_pinned (columnInjective_colouringEast (by norm_num) (by norm_num)
      isAdmissibleLevel_cdHiC cdPathC)
    (by rw [colouringEast_cdPathC_hi]; decide) (by rw [colouringEast_cdPathC_hi]; decide)

theorem colStep_colouringEast_cdPathC_lo_zero :
    colStep (colouringEast cdPathC cdLoC) 0 = (0, 2) :=
  colStep_of_pinned (columnInjective_colouringEast (by norm_num) (by norm_num)
      isAdmissibleLevel_cdLoC cdPathC)
    (by rw [colouringEast_cdPathC_lo]; decide) (by rw [colouringEast_cdPathC_lo]; decide)

theorem colStep_colouringEast_cdPathC_lo_one :
    colStep (colouringEast cdPathC cdLoC) 1 = (1, 3) :=
  colStep_of_pinned (columnInjective_colouringEast (by norm_num) (by norm_num)
      isAdmissibleLevel_cdLoC cdPathC)
    (by rw [colouringEast_cdPathC_lo]; decide) (by rw [colouringEast_cdPathC_lo]; decide)

theorem colStep_colouringNorth_cdPathC_hi_zero :
    colStep (colouringNorth cdPathC cdHiC) 0 = (0, 1) :=
  colStep_of_pinned (columnInjective_colouringNorth (by norm_num) (by norm_num)
      isAdmissibleLevel_cdHiC cdPathC)
    (by rw [colouringNorth_cdPathC_hi]; decide) (by rw [colouringNorth_cdPathC_hi]; decide)

theorem colStep_colouringNorth_cdPathC_hi_one :
    colStep (colouringNorth cdPathC cdHiC) 1 = (1, 2) :=
  colStep_of_pinned (columnInjective_colouringNorth (by norm_num) (by norm_num)
      isAdmissibleLevel_cdHiC cdPathC)
    (by rw [colouringNorth_cdPathC_hi]; decide) (by rw [colouringNorth_cdPathC_hi]; decide)

theorem colStep_colouringNorth_cdPathC_lo_zero :
    colStep (colouringNorth cdPathC cdLoC) 0 = (0, 0) :=
  colStep_of_pinned (columnInjective_colouringNorth (by norm_num) (by norm_num)
      isAdmissibleLevel_cdLoC cdPathC)
    (by rw [colouringNorth_cdPathC_lo]; decide) (by rw [colouringNorth_cdPathC_lo]; decide)

theorem colStep_colouringNorth_cdPathC_lo_one :
    colStep (colouringNorth cdPathC cdLoC) 1 = (1, 2) :=
  colStep_of_pinned (columnInjective_colouringNorth (by norm_num) (by norm_num)
      isAdmissibleLevel_cdLoC cdPathC)
    (by rw [colouringNorth_cdPathC_lo]; decide) (by rw [colouringNorth_cdPathC_lo]; decide)

/-! ### The endpoint indices of the type-`C` witness, read directly off the decided colourings -/

theorem componentTopIndex_cdPathC_hi_zero : componentTopIndex 2 3 1 cdPathC cdHiC 0 = 2 := by
  rw [componentTopIndex_eq (by norm_num) (by norm_num) (by norm_num) isAdmissibleLevel_cdHiC
      (by norm_num [cdHiC]) (show (0 : ℕ) < #(colouringEast cdPathC cdHiC) by
        rw [card_colouringEast_cdPathC_hi]; norm_num),
    colStep_colouringEast_cdPathC_hi_zero]
  norm_num

theorem componentTopIndex_cdPathC_hi_one : componentTopIndex 2 3 1 cdPathC cdHiC 1 = 4 := by
  rw [componentTopIndex_eq (by norm_num) (by norm_num) (by norm_num) isAdmissibleLevel_cdHiC
      (by norm_num [cdHiC]) (show (1 : ℕ) < #(colouringEast cdPathC cdHiC) by
        rw [card_colouringEast_cdPathC_hi]; norm_num),
    colStep_colouringEast_cdPathC_hi_one]
  norm_num

theorem componentTopIndex_cdPathC_lo_zero : componentTopIndex 2 3 1 cdPathC cdLoC 0 = 2 := by
  rw [componentTopIndex_eq (by norm_num) (by norm_num) (by norm_num) isAdmissibleLevel_cdLoC
      (by norm_num [cdLoC]) (show (0 : ℕ) < #(colouringEast cdPathC cdLoC) by
        rw [card_colouringEast_cdPathC_lo]; norm_num),
    colStep_colouringEast_cdPathC_lo_zero]
  norm_num

theorem componentTopIndex_cdPathC_lo_one : componentTopIndex 2 3 1 cdPathC cdLoC 1 = 4 := by
  rw [componentTopIndex_eq (by norm_num) (by norm_num) (by norm_num) isAdmissibleLevel_cdLoC
      (by norm_num [cdLoC]) (show (1 : ℕ) < #(colouringEast cdPathC cdLoC) by
        rw [card_colouringEast_cdPathC_lo]; norm_num),
    colStep_colouringEast_cdPathC_lo_one]
  norm_num

theorem componentBotIndex_cdPathC_hi_zero : componentBotIndex 2 3 1 cdPathC cdHiC 0 = 2 := by
  rw [componentBotIndex_eq_add_snd (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_cdHiC (by norm_num [cdHiC]) cdPathC
      (show (0 : ℕ) < #(colouringNorth cdPathC cdHiC) by
        rw [card_colouringNorth_cdPathC_hi]; norm_num),
    colStep_colouringNorth_cdPathC_hi_zero]
  norm_num

theorem componentBotIndex_cdPathC_hi_one : componentBotIndex 2 3 1 cdPathC cdHiC 1 = 4 := by
  rw [componentBotIndex_eq_add_snd (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_cdHiC (by norm_num [cdHiC]) cdPathC
      (show (1 : ℕ) < #(colouringNorth cdPathC cdHiC) by
        rw [card_colouringNorth_cdPathC_hi]; norm_num),
    colStep_colouringNorth_cdPathC_hi_one]
  norm_num

theorem componentBotIndex_cdPathC_lo_zero : componentBotIndex 2 3 1 cdPathC cdLoC 0 = 1 := by
  rw [componentBotIndex_eq_add_snd (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_cdLoC (by norm_num [cdLoC]) cdPathC
      (show (0 : ℕ) < #(colouringNorth cdPathC cdLoC) by
        rw [card_colouringNorth_cdPathC_lo]; norm_num),
    colStep_colouringNorth_cdPathC_lo_zero]
  norm_num

theorem componentBotIndex_cdPathC_lo_one : componentBotIndex 2 3 1 cdPathC cdLoC 1 = 4 := by
  rw [componentBotIndex_eq_add_snd (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_cdLoC (by norm_num [cdLoC]) cdPathC
      (show (1 : ℕ) < #(colouringNorth cdPathC cdLoC) by
        rw [card_colouringNorth_cdPathC_lo]; norm_num),
    colStep_colouringNorth_cdPathC_lo_one]
  norm_num

/-! ### The consistency check at the type-`C` witness

Every number below is produced by the **general** theorems of
`HJO/Shuffle/BraidCDIndices.lean` from the event type alone, and is checked against the value
read directly off the decided colourings above. The hypotheses the general theorems need at this
instance are the isolation, the path, the swept-region membership, the event type, and the one index
`i₀ = 0`, identified by `HJO.Mellit.colStep_colouringNorth_cdPathC_hi_zero`. -/

/-- **The type-`C` top indices, through the general theorem.** Both stand still, and both agree with
`HJO.Mellit.componentTopIndex_cdPathC_hi_zero` and `HJO.Mellit.componentTopIndex_cdPathC_hi_one`. -/
theorem cdC_top_via_general :
    componentTopIndex 2 3 1 cdPathC cdLoC 0 = 2 ∧ componentTopIndex 2 3 1 cdPathC cdLoC 1 = 4 := by
  refine ⟨?_, ?_⟩
  · rw [isolates_cdPathC.componentTopIndex_eq_of_eventType_C (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [cdLoC]) (by norm_num [cdHiC]) eventType_cdPathC
      (show (0 : ℕ) < #(colouringEast cdPathC cdHiC) by
        rw [card_colouringEast_cdPathC_hi]; norm_num)]
    exact componentTopIndex_cdPathC_hi_zero
  · rw [isolates_cdPathC.componentTopIndex_eq_of_eventType_C (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [cdLoC]) (by norm_num [cdHiC]) eventType_cdPathC
      (show (1 : ℕ) < #(colouringEast cdPathC cdHiC) by
        rw [card_colouringEast_cdPathC_hi]; norm_num)]
    exact componentTopIndex_cdPathC_hi_one

/-- **The type-`C` bottom indices, through the general theorem.** The general statement predicts
`n_P + 1 = 2` above the drop and `n_P = 1` below it at the index `i₀ = 0`, and no change at the
index `1`; the decided colourings give `2`, `1` and `4` (twice). -/
theorem cdC_bot_via_general :
    componentBotIndex 2 3 1 cdPathC cdHiC 0 = 2 ∧ componentBotIndex 2 3 1 cdPathC cdLoC 0 = 1 ∧
      componentBotIndex 2 3 1 cdPathC cdLoC 1 = 4 := by
  obtain ⟨hne, hhi, hlo⟩ := isolates_cdPathC.componentBotIndex_of_eventType_C (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [cdLoC]) (by norm_num [cdHiC]) eventType_cdPathC
    (show (0 : ℕ) < #(colouringNorth cdPathC cdHiC) by
      rw [card_colouringNorth_cdPathC_hi]; norm_num)
    colStep_colouringNorth_cdPathC_hi_zero
  refine ⟨by rw [hhi]; norm_num, by rw [hlo]; norm_num, ?_⟩
  rw [hne 1 (by rw [card_colouringNorth_cdPathC_hi]; norm_num) (by norm_num)]
  exact componentBotIndex_cdPathC_hi_one

/-! ### The multiplicities and positions of the type-`C` witness -/

/-- `HJO.Mellit.levelPosition` on the `(2, 3)`-rectangle: a rank `r` sits at `(3/7)(r - η)/6`. -/
theorem levelPosition_cd (η r : ℚ) : levelPosition 2 3 1 η r = 3 / 7 * ((r - η) / 6) := by
  rw [levelPosition, sweepTheta_cd]
  norm_num

theorem braidData_cdPathC_hi_snd_zero : (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 0 = 1 := by
  rw [braidDataOfColouring_snd_eq_toNat, show ((0 : Fin 2) : ℕ) = 0 from rfl,
    componentTopIndex_cdPathC_hi_zero, componentBotIndex_cdPathC_hi_zero]
  decide

theorem braidData_cdPathC_hi_snd_one : (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 1 = 1 := by
  rw [braidDataOfColouring_snd_eq_toNat, show ((1 : Fin 2) : ℕ) = 1 from rfl,
    componentTopIndex_cdPathC_hi_one, componentBotIndex_cdPathC_hi_one]
  decide

theorem braidData_cdPathC_lo_snd_zero : (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).2 0 = 2 := by
  rw [braidDataOfColouring_snd_eq_toNat, show ((0 : Fin 2) : ℕ) = 0 from rfl,
    componentTopIndex_cdPathC_lo_zero, componentBotIndex_cdPathC_lo_zero]
  decide

theorem braidData_cdPathC_lo_snd_one : (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).2 1 = 1 := by
  rw [braidDataOfColouring_snd_eq_toNat, show ((1 : Fin 2) : ℕ) = 1 from rfl,
    componentTopIndex_cdPathC_lo_one, componentBotIndex_cdPathC_lo_one]
  decide

theorem braidData_cdPathC_hi_fst_zero :
    (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).1 0 = 11 / 28 := by
  rw [braidDataOfColouring_fst_eq_levelPosition (a := 2) (b := 3) (N := 1) (by norm_num)
      (by norm_num) (by norm_num) isAdmissibleLevel_cdHiC (by norm_num [cdHiC]) (0 : Fin 2)
      (show ((0 : Fin 2) : ℕ) < #(colouringEast cdPathC cdHiC) by
        rw [card_colouringEast_cdPathC_hi]; norm_num),
    show ((0 : Fin 2) : ℕ) = 0 from rfl, colStep_colouringEast_cdPathC_hi_zero, pointRank_cd,
    levelPosition_cd, cdHiC]
  norm_num

theorem braidData_cdPathC_hi_fst_one :
    (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).1 1 = 7 / 28 := by
  rw [braidDataOfColouring_fst_eq_levelPosition (a := 2) (b := 3) (N := 1) (by norm_num)
      (by norm_num) (by norm_num) isAdmissibleLevel_cdHiC (by norm_num [cdHiC]) (1 : Fin 2)
      (show ((1 : Fin 2) : ℕ) < #(colouringEast cdPathC cdHiC) by
        rw [card_colouringEast_cdPathC_hi]; norm_num),
    show ((1 : Fin 2) : ℕ) = 1 from rfl, colStep_colouringEast_cdPathC_hi_one, pointRank_cd,
    levelPosition_cd, cdHiC]
  norm_num

theorem braidData_cdPathC_lo_fst_zero :
    (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 0 = 13 / 28 := by
  rw [braidDataOfColouring_fst_eq_levelPosition (a := 2) (b := 3) (N := 1) (by norm_num)
      (by norm_num) (by norm_num) isAdmissibleLevel_cdLoC (by norm_num [cdLoC]) (0 : Fin 2)
      (show ((0 : Fin 2) : ℕ) < #(colouringEast cdPathC cdLoC) by
        rw [card_colouringEast_cdPathC_lo]; norm_num),
    show ((0 : Fin 2) : ℕ) = 0 from rfl, colStep_colouringEast_cdPathC_lo_zero, pointRank_cd,
    levelPosition_cd, cdLoC]
  norm_num

theorem braidData_cdPathC_lo_fst_one :
    (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 1 = 9 / 28 := by
  rw [braidDataOfColouring_fst_eq_levelPosition (a := 2) (b := 3) (N := 1) (by norm_num)
      (by norm_num) (by norm_num) isAdmissibleLevel_cdLoC (by norm_num [cdLoC]) (1 : Fin 2)
      (show ((1 : Fin 2) : ℕ) < #(colouringEast cdPathC cdLoC) by
        rw [card_colouringEast_cdPathC_lo]; norm_num),
    show ((1 : Fin 2) : ℕ) = 1 from rfl, colStep_colouringEast_cdPathC_lo_one, pointRank_cd,
    levelPosition_cd, cdLoC]
  norm_num

/-- **The type-`C` multiplicity increment, through the general theorems.** The index `i₀ = 0` gains
a move and the index `1` does not, and both agree with the values read off the decided colourings:
`2 = 1 + 1` and `1`. -/
theorem cdC_snd_via_general :
    (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).2 0 = 2 ∧
      (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).2 1 = 1 := by
  refine ⟨?_, ?_⟩
  · rw [isolates_cdPathC.braidData_snd_succ_of_eventType_C (by norm_num) (by norm_num)
      (by norm_num) lt_cdLoC isAboveDiagonal_cdPathC eventType_cdPathC
      (show (0 : ℕ) < #(colouringNorth cdPathC cdHiC) by
        rw [card_colouringNorth_cdPathC_hi]; norm_num)
      colStep_colouringNorth_cdPathC_hi_zero (0 : Fin 2) rfl,
      braidData_cdPathC_hi_snd_zero]
  · rw [isolates_cdPathC.braidData_snd_of_eventType_C_of_ne (by norm_num) (by norm_num)
      (by norm_num) lt_cdLoC isAboveDiagonal_cdPathC eventType_cdPathC
      (show (0 : ℕ) < #(colouringNorth cdPathC cdHiC) by
        rw [card_colouringNorth_cdPathC_hi]; norm_num)
      colStep_colouringNorth_cdPathC_hi_zero (1 : Fin 2)
      (by rw [card_colouringNorth_cdPathC_hi]; norm_num) (by norm_num)]
    exact braidData_cdPathC_hi_snd_one

/-- **The type-`C` rigid rotation, through the general theorem.** Both positions rise by exactly
`HJO.Mellit.levelDropShift = 1/14 = 2/28`, with no fractional part taken, and agree with `13/28`
and `9/28`. -/
theorem cdC_fst_via_general :
    (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 0 = 13 / 28 ∧
      (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 1 = 9 / 28 := by
  have hshift : levelDropShift 2 3 1 cdLoC cdHiC = 1 / 14 := by
    rw [show cdHiC = cdLoC + 1 from cdLoC_lt_cdHiC]; exact levelDropShift_cd cdLoC
  refine ⟨?_, ?_⟩
  · rw [isolates_cdPathC.braidData_fst_eq_add_of_eventType_C (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [cdLoC]) eventType_cdPathC (0 : Fin 2)
      (show ((0 : Fin 2) : ℕ) < #(colouringEast cdPathC cdHiC) by
        rw [card_colouringEast_cdPathC_hi]; norm_num),
      braidData_cdPathC_hi_fst_zero, hshift]
    norm_num
  · rw [isolates_cdPathC.braidData_fst_eq_add_of_eventType_C (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [cdLoC]) eventType_cdPathC (1 : Fin 2)
      (show ((1 : Fin 2) : ℕ) < #(colouringEast cdPathC cdHiC) by
        rw [card_colouringEast_cdPathC_hi]; norm_num),
      braidData_cdPathC_hi_fst_one, hshift]
    norm_num

/-! ### The `z`-count of the type-`C` witness, letter by letter -/

/-- Above the drop every multiplicity is `1`, so the braid is the identity and `ζ = 0`. -/
theorem zCount_cdPathC_hi :
    zCount 2 (by norm_num) (specialBraid (sweepTheta 2 3 1)
        (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).1
        (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2) = 0 := by
  rw [specialBraid_of_forall_eq_one (fun i => by
    fin_cases i
    · exact braidData_cdPathC_hi_snd_zero
    · exact braidData_cdPathC_hi_snd_one), zCount_one]

theorem specialMoveList_cdPathC_lo :
    specialMoveList (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).2 = [(0 : Fin 2)] := by
  rw [specialMoveList, show List.finRange 2 = [(0 : Fin 2), 1] from rfl]
  simp [braidData_cdPathC_lo_snd_zero, braidData_cdPathC_lo_snd_one]

/-- **Below the drop the one added move is a `ỹ` letter, so `ζ` is still `0`.** The moving position
is `13/28`, strictly **above** the puncture `θ = 12/28`, so `HJO.Braid.braidStep` takes its `ỹ`
branch. This is the type-`C` prediction of
`HJO.Mellit.Isolates.zCount_sub_eq_zero_of_eventType_C`, recomputed from the letters. -/
theorem zCount_cdPathC_lo :
    zCount 2 (by norm_num) (specialBraid (sweepTheta 2 3 1)
        (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1
        (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).2) = 0 := by
  rw [specialBraid, specialMoveList_cdPathC_lo, braidWord_singleton, zCount_braidStep,
    braidData_cdPathC_lo_fst_zero, sweepTheta_cd]
  norm_num

/-- **The type-`C` prediction at the witness, through the general theorem.** Non-vacuity as well as
agreement: every hypothesis of `HJO.Mellit.Isolates.zCount_sub_eq_zero_of_eventType_C` is discharged
at this instance, and by `HJO.Mellit.card_colouringNorth_cdPathC_lo` and its upper twin the two
`ζ`'s here are the ones `HJO.Mellit.zCount_cdPathC_lo` and `HJO.Mellit.zCount_cdPathC_hi` compute
letter by letter as `0` and `0`. -/
theorem zCount_sub_cdPathC (hklo : 1 ≤ #(colouringNorth cdPathC cdLoC))
    (hkhi : 1 ≤ #(colouringNorth cdPathC cdHiC)) :
    (zCount #(colouringNorth cdPathC cdLoC) hklo (specialBraid (sweepTheta 2 3 1)
        (braidDataOfColouring 2 3 1 cdPathC cdLoC #(colouringNorth cdPathC cdLoC)).1
        (braidDataOfColouring 2 3 1 cdPathC cdLoC #(colouringNorth cdPathC cdLoC)).2) : ℤ)
      - (zCount #(colouringNorth cdPathC cdHiC) hkhi (specialBraid (sweepTheta 2 3 1)
          (braidDataOfColouring 2 3 1 cdPathC cdHiC #(colouringNorth cdPathC cdHiC)).1
          (braidDataOfColouring 2 3 1 cdPathC cdHiC #(colouringNorth cdPathC cdHiC)).2) : ℤ)
      = 0 :=
  isolates_cdPathC.zCount_sub_eq_zero_of_eventType_C (by norm_num) (by norm_num) (by norm_num)
    lt_cdLoC cdLoC_lt_cdHiC isAboveDiagonal_cdPathC eventType_cdPathC hklo hkhi

/-! ### The type-`D` witness -/

/-- The type-`D` witness path: the above-diagonal `(2, 3)`-path with heights `(0, 3, 3)`. It is flat
over the second column, so `(1, 3)` is two consecutive east steps. -/
def cdPathD : Heights 2 3 1 := ![0, 3, 3]

/-- The lower level of the type-`D` witness pair, `rk̂(1,3) - 1/2 = 19/2`. -/
def cdLoD : ℚ := 19 / 2

/-- The upper level of the type-`D` witness pair, `rk̂(1,3) + 1/2 = 21/2`. -/
def cdHiD : ℚ := 21 / 2

theorem isAboveDiagonal_cdPathD : IsAboveDiagonal cdPathD := by decide

/-- `(1, 3)` is a type-`D` event of the witness: `ŷ_1 = 3 = Y` and `ŷ_2 = 3` is not above it. -/
theorem eventType_cdPathD : eventType cdPathD (1, 3) = EventType.D := by decide

theorem mem_sweptRegion_cdPathD : ((1, 3) : ℕ × ℕ) ∈ sweptRegion cdPathD := by decide

theorem northSteps_cdPathD : northSteps cdPathD = {(0, 0), (0, 1), (0, 2)} := by decide

theorem eastSteps_cdPathD : eastSteps cdPathD = {(0, 3), (1, 3)} := by decide

theorem isAdmissibleLevel_cdLoD : IsAdmissibleLevel cdLoD := ⟨9, by norm_num [cdLoD]⟩

theorem isAdmissibleLevel_cdHiD : IsAdmissibleLevel cdHiD := ⟨10, by norm_num [cdHiD]⟩

theorem cdLoD_lt_cdHiD : cdHiD = cdLoD + 1 := by norm_num [cdLoD, cdHiD]

theorem lt_cdLoD : ((2 * 1 : ℕ) : ℚ) < cdLoD := by norm_num [cdLoD]

/-- The isolating pair of the type-`D` witness, `rk̂(1,3) ∓ 1/2` with `rk̂(1,3) = 10`. -/
theorem isolates_cdPathD : Isolates 2 3 1 1 3 cdLoD cdHiD := by
  have h := isolates_sub_half_add_half 2 3 1 (X := 1) (Y := 3) (by norm_num) (by norm_num)
  rw [show ((pointRank 2 3 1 (1, 3) : ℤ) : ℚ) = 10 by rw [pointRank_cd]; norm_num] at h
  rw [show (10 : ℚ) - 1 / 2 = cdLoD by norm_num [cdLoD],
    show (10 : ℚ) + 1 / 2 = cdHiD by norm_num [cdHiD]] at h
  exact h

/-- **The crossed north step stands still at the type-`D` drop**: `(0, 1)`, with `6 < η < 12` at
`η = 19/2` and at `η = 21/2` alike. -/
theorem colouringNorth_cdPathD (η : ℚ) (h1 : (6 : ℚ) < η) (h2 : η < 12) :
    colouringNorth cdPathD η = {((0 : ℕ), (1 : ℕ))} := by
  ext P
  rw [colouringNorth, Finset.mem_filter, northSteps_cdPathD]
  constructor
  · rintro ⟨hP, h⟩
    fin_cases hP
    · rw [pointRank_cd, attackWindow_cd] at h
      push_cast at h
      exact absurd h.2 (by linarith)
    · decide
    · rw [pointRank_cd, attackWindow_cd] at h
      push_cast at h
      exact absurd h.1 (by linarith)
  · intro hP
    rw [Finset.mem_singleton] at hP
    subst hP
    refine ⟨by decide, ?_⟩
    rw [pointRank_cd, attackWindow_cd]
    push_cast
    constructor <;> linarith

theorem colouringNorth_cdPathD_hi : colouringNorth cdPathD cdHiD = {((0 : ℕ), (1 : ℕ))} :=
  colouringNorth_cdPathD cdHiD (by norm_num [cdHiD]) (by norm_num [cdHiD])

theorem colouringNorth_cdPathD_lo : colouringNorth cdPathD cdLoD = {((0 : ℕ), (1 : ℕ))} :=
  colouringNorth_cdPathD cdLoD (by norm_num [cdLoD]) (by norm_num [cdLoD])

/-- **The crossed east step at `η₊ = 21/2` is `(0, 3)`**: `rk̂(1,3) = 10 < 21/2 < 18 = rk̂(0,3)`,
while `(1, 3)` needs `21/2 < 10` and fails. -/
theorem colouringEast_cdPathD_hi : colouringEast cdPathD cdHiD = {((0 : ℕ), (3 : ℕ))} := by
  ext P
  rw [colouringEast, Finset.mem_filter, eastSteps_cdPathD]
  constructor
  · rintro ⟨hP, h⟩
    revert h
    fin_cases hP <;> norm_num [cdHiD, pointRank_cd]
  · intro hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact ⟨by decide, by norm_num [cdHiD, pointRank_cd]⟩

/-- **The crossed east step at `η₋ = 19/2` is `(1, 3)`**, one column to the right: the level has
dropped past `rk̂(1,3) = 10`, so the step of ordinate `3` is now crossed in column `1`. -/
theorem colouringEast_cdPathD_lo : colouringEast cdPathD cdLoD = {((1 : ℕ), (3 : ℕ))} := by
  ext P
  rw [colouringEast, Finset.mem_filter, eastSteps_cdPathD]
  constructor
  · rintro ⟨hP, h⟩
    revert h
    fin_cases hP <;> norm_num [cdLoD, pointRank_cd]
  · intro hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact ⟨by decide, by norm_num [cdLoD, pointRank_cd]⟩

theorem card_colouringNorth_cdPathD_hi : #(colouringNorth cdPathD cdHiD) = 1 := by
  rw [colouringNorth_cdPathD_hi]; decide

theorem card_colouringNorth_cdPathD_lo : #(colouringNorth cdPathD cdLoD) = 1 := by
  rw [colouringNorth_cdPathD_lo]; decide

theorem card_colouringEast_cdPathD_hi : #(colouringEast cdPathD cdHiD) = 1 := by
  rw [colouringEast_cdPathD_hi]; decide

theorem card_colouringEast_cdPathD_lo : #(colouringEast cdPathD cdLoD) = 1 := by
  rw [colouringEast_cdPathD_lo]; decide

theorem colStep_colouringEast_cdPathD_hi :
    colStep (colouringEast cdPathD cdHiD) 0 = (1 - 1, 3) :=
  colStep_of_pinned (columnInjective_colouringEast (by norm_num) (by norm_num)
      isAdmissibleLevel_cdHiD cdPathD)
    (by rw [colouringEast_cdPathD_hi]; decide) (by rw [colouringEast_cdPathD_hi]; decide)

theorem colStep_colouringEast_cdPathD_lo :
    colStep (colouringEast cdPathD cdLoD) 0 = (1, 3) :=
  colStep_of_pinned (columnInjective_colouringEast (by norm_num) (by norm_num)
      isAdmissibleLevel_cdLoD cdPathD)
    (by rw [colouringEast_cdPathD_lo]; decide) (by rw [colouringEast_cdPathD_lo]; decide)

theorem colStep_colouringNorth_cdPathD_hi :
    colStep (colouringNorth cdPathD cdHiD) 0 = (0, 1) :=
  colStep_of_pinned (columnInjective_colouringNorth (by norm_num) (by norm_num)
      isAdmissibleLevel_cdHiD cdPathD)
    (by rw [colouringNorth_cdPathD_hi]; decide) (by rw [colouringNorth_cdPathD_hi]; decide)

theorem colStep_colouringNorth_cdPathD_lo :
    colStep (colouringNorth cdPathD cdLoD) 0 = (0, 1) :=
  colStep_of_pinned (columnInjective_colouringNorth (by norm_num) (by norm_num)
      isAdmissibleLevel_cdLoD cdPathD)
    (by rw [colouringNorth_cdPathD_lo]; decide) (by rw [colouringNorth_cdPathD_lo]; decide)

/-! ### The endpoint indices of the type-`D` witness, read directly off the decided colourings -/

theorem componentTopIndex_cdPathD_hi : componentTopIndex 2 3 1 cdPathD cdHiD 0 = 3 := by
  rw [componentTopIndex_eq (by norm_num) (by norm_num) (by norm_num) isAdmissibleLevel_cdHiD
      (by norm_num [cdHiD]) (show (0 : ℕ) < #(colouringEast cdPathD cdHiD) by
        rw [card_colouringEast_cdPathD_hi]; norm_num),
    colStep_colouringEast_cdPathD_hi]
  norm_num

theorem componentTopIndex_cdPathD_lo : componentTopIndex 2 3 1 cdPathD cdLoD 0 = 4 := by
  rw [componentTopIndex_eq (by norm_num) (by norm_num) (by norm_num) isAdmissibleLevel_cdLoD
      (by norm_num [cdLoD]) (show (0 : ℕ) < #(colouringEast cdPathD cdLoD) by
        rw [card_colouringEast_cdPathD_lo]; norm_num),
    colStep_colouringEast_cdPathD_lo]
  norm_num

theorem componentBotIndex_cdPathD_hi : componentBotIndex 2 3 1 cdPathD cdHiD 0 = 2 := by
  rw [componentBotIndex_eq_add_snd (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_cdHiD (by norm_num [cdHiD]) cdPathD
      (show (0 : ℕ) < #(colouringNorth cdPathD cdHiD) by
        rw [card_colouringNorth_cdPathD_hi]; norm_num),
    colStep_colouringNorth_cdPathD_hi]
  norm_num

theorem componentBotIndex_cdPathD_lo : componentBotIndex 2 3 1 cdPathD cdLoD 0 = 2 := by
  rw [componentBotIndex_eq_add_snd (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_cdLoD (by norm_num [cdLoD]) cdPathD
      (show (0 : ℕ) < #(colouringNorth cdPathD cdLoD) by
        rw [card_colouringNorth_cdPathD_lo]; norm_num),
    colStep_colouringNorth_cdPathD_lo]
  norm_num

/-! ### The consistency check at the type-`D` witness -/

/-- **The type-`D` index dictionary, through the general theorems.** The bottom index stands still
and the top index rises from `n_P - 1 = 3` to `n_P = 4`; the decided colourings give `2`, `3`
and `4`. -/
theorem cdD_indices_via_general :
    componentBotIndex 2 3 1 cdPathD cdLoD 0 = 2 ∧
      componentTopIndex 2 3 1 cdPathD cdHiD 0 = 3 ∧
      componentTopIndex 2 3 1 cdPathD cdLoD 0 = 4 := by
  obtain ⟨-, htophi, htoplo⟩ := isolates_cdPathD.componentTopIndex_of_eventType_D (by norm_num)
    (by norm_num) (by norm_num) lt_cdLoD (by norm_num [cdHiD]) (by norm_num)
    isAboveDiagonal_cdPathD eventType_cdPathD
    (show (0 : ℕ) < #(colouringEast cdPathD cdHiD) by
      rw [card_colouringEast_cdPathD_hi]; norm_num)
    colStep_colouringEast_cdPathD_hi
  refine ⟨?_, by rw [htophi]; norm_num, by rw [htoplo]; norm_num⟩
  rw [isolates_cdPathD.componentBotIndex_eq_of_eventType_D (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [cdLoD]) (by norm_num [cdHiD]) (by norm_num) eventType_cdPathD
    (show (0 : ℕ) < #(colouringNorth cdPathD cdHiD) by
      rw [card_colouringNorth_cdPathD_hi]; norm_num)]
  exact componentBotIndex_cdPathD_hi

/-! ### The multiplicities, positions and `z`-count of the type-`D` witness -/

theorem braidData_cdPathD_hi_snd : (braidDataOfColouring 2 3 1 cdPathD cdHiD 1).2 0 = 2 := by
  rw [braidDataOfColouring_snd_eq_toNat, show ((0 : Fin 1) : ℕ) = 0 from rfl,
    componentTopIndex_cdPathD_hi, componentBotIndex_cdPathD_hi]
  decide

theorem braidData_cdPathD_lo_snd : (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).2 0 = 3 := by
  rw [braidDataOfColouring_snd_eq_toNat, show ((0 : Fin 1) : ℕ) = 0 from rfl,
    componentTopIndex_cdPathD_lo, componentBotIndex_cdPathD_lo]
  decide

theorem braidData_cdPathD_hi_fst : (braidDataOfColouring 2 3 1 cdPathD cdHiD 1).1 0 = 15 / 28 := by
  rw [braidDataOfColouring_fst_eq_levelPosition (a := 2) (b := 3) (N := 1) (by norm_num)
      (by norm_num) (by norm_num) isAdmissibleLevel_cdHiD (by norm_num [cdHiD]) (0 : Fin 1)
      (show ((0 : Fin 1) : ℕ) < #(colouringEast cdPathD cdHiD) by
        rw [card_colouringEast_cdPathD_hi]; norm_num),
    show ((0 : Fin 1) : ℕ) = 0 from rfl, colStep_colouringEast_cdPathD_hi, pointRank_cd,
    levelPosition_cd, cdHiD]
  norm_num

theorem braidData_cdPathD_lo_fst : (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1 0 = 1 / 28 := by
  rw [braidDataOfColouring_fst_eq_levelPosition (a := 2) (b := 3) (N := 1) (by norm_num)
      (by norm_num) (by norm_num) isAdmissibleLevel_cdLoD (by norm_num [cdLoD]) (0 : Fin 1)
      (show ((0 : Fin 1) : ℕ) < #(colouringEast cdPathD cdLoD) by
        rw [card_colouringEast_cdPathD_lo]; norm_num),
    show ((0 : Fin 1) : ℕ) = 0 from rfl, colStep_colouringEast_cdPathD_lo, pointRank_cd,
    levelPosition_cd, cdLoD]
  norm_num

/-- **The type-`D` multiplicity increment and the wrapping position, through the general
theorems.** The multiplicity rises from `2` to `3`, and the position moves from `15/28` by
`levelDropShift + θ = 2/28 + 12/28`, wrapping to `1/28` — both agreeing with the values read off the
decided colourings. The wrap is the content: without the fractional part the value would be
`29/28`. -/
theorem cdD_data_via_general :
    (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).2 0 = 3 ∧
      (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1 0 = 1 / 28 := by
  have hshift : levelDropShift 2 3 1 cdLoD cdHiD = 1 / 14 := by
    rw [show cdHiD = cdLoD + 1 from cdLoD_lt_cdHiD]; exact levelDropShift_cd cdLoD
  refine ⟨?_, ?_⟩
  · rw [isolates_cdPathD.braidData_snd_succ_of_eventType_D (by norm_num) (by norm_num)
      (by norm_num) lt_cdLoD isAboveDiagonal_cdPathD eventType_cdPathD
      (show (0 : ℕ) < #(colouringEast cdPathD cdHiD) by
        rw [card_colouringEast_cdPathD_hi]; norm_num)
      colStep_colouringEast_cdPathD_hi (0 : Fin 1) rfl,
      braidData_cdPathD_hi_snd]
  · rw [isolates_cdPathD.braidData_fst_succ_of_eventType_D (by norm_num) (by norm_num)
      (by norm_num) lt_cdLoD isAboveDiagonal_cdPathD eventType_cdPathD
      (show (0 : ℕ) < #(colouringEast cdPathD cdHiD) by
        rw [card_colouringEast_cdPathD_hi]; norm_num)
      colStep_colouringEast_cdPathD_hi (0 : Fin 1) rfl,
      braidData_cdPathD_hi_fst, hshift, sweepTheta_cd]
    rw [show (15 : ℚ) / 28 + 1 / 14 + 3 / 7 = 1 + 1 / 28 by norm_num, Int.fract_one_add]
    rw [Int.fract_eq_self.2 ⟨by norm_num, by norm_num⟩]

theorem specialMoveList_cdPathD_hi :
    specialMoveList (braidDataOfColouring 2 3 1 cdPathD cdHiD 1).2 = [(0 : Fin 1)] := by
  rw [specialMoveList, show List.finRange 1 = [(0 : Fin 1)] from rfl]
  simp [braidData_cdPathD_hi_snd]

theorem specialMoveList_cdPathD_lo :
    specialMoveList (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).2 = [(0 : Fin 1), 0] := by
  rw [specialMoveList, show List.finRange 1 = [(0 : Fin 1)] from rfl]
  simp [braidData_cdPathD_lo_snd]

/-- **Above the drop the one move is a `ỹ` letter**: the position `15/28` is above the puncture
`12/28`, so `ζ = 0`. -/
theorem zCount_cdPathD_hi :
    zCount 1 (by norm_num) (specialBraid (sweepTheta 2 3 1)
        (braidDataOfColouring 2 3 1 cdPathD cdHiD 1).1
        (braidDataOfColouring 2 3 1 cdPathD cdHiD 1).2) = 0 := by
  rw [specialBraid, specialMoveList_cdPathD_hi, braidWord_singleton, zCount_braidStep,
    braidData_cdPathD_hi_fst, sweepTheta_cd]
  norm_num

/-- **Below the drop the added move is a `z` letter, so `ζ` is `1`.** The wrapped position `1/28` is
**below** the puncture `12/28`, so the first move takes `HJO.Braid.braidStep`'s `z` branch; the
second move starts from `HJO.Braid.nextCrossing (3/7) (1/28) = 17/28`, above the puncture, and
contributes a `ỹ`. This is the type-`D` prediction of
`HJO.Mellit.Isolates.zCount_sub_eq_one_of_eventType_D`, recomputed from the letters. -/
theorem zCount_cdPathD_lo :
    zCount 1 (by norm_num) (specialBraid (sweepTheta 2 3 1)
        (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1
        (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).2) = 1 := by
  rw [specialBraid, specialMoveList_cdPathD_lo, braidWord_pair, zCount_mul, zCount_braidStep,
    zCount_braidStep, moveOne_self, braidData_cdPathD_lo_fst, sweepTheta_cd, nextCrossing]
  norm_num

/-- **The type-`D` prediction at the witness, through the general theorem.** By
`HJO.Mellit.card_colouringNorth_cdPathD_lo` and its upper twin the two `ζ`'s here are the ones
`HJO.Mellit.zCount_cdPathD_lo` and `HJO.Mellit.zCount_cdPathD_hi` compute letter by letter as `1`
and `0`, so the general theorem's `+1` is the value the letters give. -/
theorem zCount_sub_cdPathD (hklo : 1 ≤ #(colouringNorth cdPathD cdLoD))
    (hkhi : 1 ≤ #(colouringNorth cdPathD cdHiD)) :
    (zCount #(colouringNorth cdPathD cdLoD) hklo (specialBraid (sweepTheta 2 3 1)
        (braidDataOfColouring 2 3 1 cdPathD cdLoD #(colouringNorth cdPathD cdLoD)).1
        (braidDataOfColouring 2 3 1 cdPathD cdLoD #(colouringNorth cdPathD cdLoD)).2) : ℤ)
      - (zCount #(colouringNorth cdPathD cdHiD) hkhi (specialBraid (sweepTheta 2 3 1)
          (braidDataOfColouring 2 3 1 cdPathD cdHiD #(colouringNorth cdPathD cdHiD)).1
          (braidDataOfColouring 2 3 1 cdPathD cdHiD #(colouringNorth cdPathD cdHiD)).2) : ℤ)
      = 1 :=
  isolates_cdPathD.zCount_sub_eq_one_of_eventType_D (by norm_num) (by norm_num) (by norm_num)
    lt_cdLoD cdLoD_lt_cdHiD isAboveDiagonal_cdPathD eventType_cdPathD hklo hkhi

end HJO.Mellit

end
