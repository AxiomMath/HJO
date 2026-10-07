/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidCDIndicesWitness
public import HJO.Shuffle.BraidCDLetterResidual
public meta import HJO.Attr

/-! # The equal-rank raise and the exponent, re-derived at the two decided witnesses

`HJO/Shuffle/BraidEqualRankRaise.lean` and `HJO/Shuffle/BraidSweepRightData.lean` prove in
general what raising one multiplicity does to `HJO.Braid.specialBraid` and what
`HJO.Paths.sweepRight` is in terms of the data. A general theorem with the letter on the wrong side,
the tuple at the wrong stage or the index off by one can still look right, so each is re-derived
here *through* the general statement at the two witnesses of
`HJO/Shuffle/BraidCDIndicesWitness.lean` and checked against the independently computed value.

Every pair below is closed by the `rfl` check on the two proof terms, which by proof irrelevance
typechecks **only if the two statements are literally the same `Prop`** — stronger than comparing
printed values by eye.

## What is checked

* `HJO.Mellit.sweepRight_cdPathC_via_general` against `HJO.Mellit.sweepRight_cdPathC_decided`:
  `a_{P̂}(0,1) = 1` on the type-`C` witness, the general formula reading `k - 1 - j = 2 - 1 - 0`.
* `HJO.Mellit.sweepRight_cdPathD_via_general` against `HJO.Mellit.sweepRight_cdPathD_decided`:
  `a_{P̂}(1,3) = 0` on the type-`D` witness, `k - 1 - j = 1 - 1 - 0`. This one tests the
  east-listing route, a different argument from the north-listing one.
* `HJO.Mellit.specialBraid_cdPathC_lo_via_general` against
  `HJO.Mellit.specialBraid_cdPathC_lo_decided`: the lower special braid of the type-`C` witness is
  the single letter `HJO.Braid.braidStep θ v 0`, which the decided route reads off
  `HJO.Mellit.specialMoveList_cdPathC_lo`. This pins that the general left form puts the letter on
  the **left** and reads it at the final tuple of the **unraised** multiplicities: every upper
  multiplicity here is `1`, so that tuple is `v` itself and the letter is the one whose `z`-count
  `HJO.Mellit.zCount_cdPathC_lo` computes as `0`.
* `HJO.Mellit.specialBraid_cdPathD_lo_via_general` against
  `HJO.Mellit.specialBraid_cdPathD_lo_decided`: the lower special braid of the type-`D` witness is
  two letters, and the general right form splits it with the added letter **rightmost**, read at `v`
  itself — which is the `z` letter `HJO.Mellit.zCount_cdPathD_lo` counts.
* `HJO.Mellit.moveOne_cdPathD_via_general` against `HJO.Mellit.moveOne_cdPathD_decided`: the tuple
  the rest of the type-`D` braid is read at is `17/28`, both as `nx_θ` of the wrapped lower position
  `1/28` and as the rigidly rotated upper position `15/28 + 1/14`.

## References

This file concerns `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, using
`HJO.Braid.specialBraid`, `HJO.Braid.braidStep`, `HJO.Paths.sweepRight`,
`HJO.Mellit.braidDataOfColouring`, `HJO.Braid.positionPair` and `HJO.Braid.nextCrossing`.
-/

@[expose] public section

namespace HJO.Mellit

open Braid Finset ParkingFunctions Paths Sweep

/-! ### The exponent at the type-`C` witness -/

/-- `a_{P̂}(0,1) = 1` on the type-`C` witness, read straight off `HJO.Paths.sweepRight`: the level
line crosses the two north steps `(0,1)` and `(1,2)`, and exactly one of them is strictly right of
column `0`. -/
theorem sweepRight_cdPathC_decided : sweepRight cdPathC ((0 : ℕ), (1 : ℕ)) = 1 := by decide

/-- The same through `HJO.Mellit.Isolates.sweepRight_eq_of_colStep_colouringNorth`: the event is the
`0`-th crossed north step of a rank-`2` colouring, so the formula gives `2 - 1 - 0`. -/
theorem sweepRight_cdPathC_via_general : sweepRight cdPathC ((0 : ℕ), (1 : ℕ)) = 1 := by
  rw [isolates_cdPathC.sweepRight_eq_of_colStep_colouringNorth (by norm_num) (by norm_num) cdPathC
      (j := 0) (by rw [card_colouringNorth_cdPathC_hi]; norm_num)
      colStep_colouringNorth_cdPathC_hi_zero,
    card_colouringNorth_cdPathC_hi]

/-- The two readings are the same statement, hence the same value. -/
example : sweepRight_cdPathC_decided = sweepRight_cdPathC_via_general := rfl

/-! ### The exponent at the type-`D` witness -/

/-- `a_{P̂}(1,3) = 0` on the type-`D` witness: the only crossed north step is `(0,1)`, sitting in
column `0`, which is not strictly right of column `1`. -/
theorem sweepRight_cdPathD_decided : sweepRight cdPathD ((1 : ℕ), (3 : ℕ)) = 0 := by decide

/-- The same through `HJO.Mellit.Isolates.sweepRight_eq_of_eventType_D`, whose index is read off the
**east** listing: the moved east step is the `0`-th of a rank-`1` colouring, so `1 - 1 - 0`. -/
theorem sweepRight_cdPathD_via_general : sweepRight cdPathD ((1 : ℕ), (3 : ℕ)) = 0 := by
  rw [isolates_cdPathD.sweepRight_eq_of_eventType_D (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [cdHiD]) isAboveDiagonal_cdPathD eventType_cdPathD (by norm_num) (j := 0)
      (by rw [card_colouringEast_cdPathD_hi]; norm_num) colStep_colouringEast_cdPathD_hi,
    card_colouringEast_cdPathD_hi]

/-- The two readings are the same statement, hence the same value. -/
example : sweepRight_cdPathD_decided = sweepRight_cdPathD_via_general := rfl

/-! ### The equal-rank raise at the type-`C` witness -/

/-- Every multiplicity of the upper type-`C` colouring is `1`. -/
theorem braidData_cdPathC_hi_snd_eq_one (i : Fin 2) :
    (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 i = 1 := by
  by_cases h : i = 0
  · subst h; exact braidData_cdPathC_hi_snd_zero
  · have h1 : i = 1 := by
      refine Fin.ext ?_
      change (i : ℕ) = 1
      have h2 : (i : ℕ) ≠ 0 := fun hc => h (Fin.ext hc)
      have h3 := i.isLt
      omega
    subst h1; exact braidData_cdPathC_hi_snd_one

/-- The lower multiplicities of the type-`C` witness are the upper ones with the index `0` raised by
one, which is the shape `HJO.Braid.specialBraid_update_succ_left` consumes. -/
theorem braidData_cdPathC_lo_snd_eq_update :
    (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).2
      = Function.update (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 0
          ((braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 0 + 1) := by
  funext i
  by_cases h : i = 0
  · subst h
    rw [Function.update_self, braidData_cdPathC_hi_snd_zero, braidData_cdPathC_lo_snd_zero]
  · have h1 : i = 1 := by
      refine Fin.ext ?_
      change (i : ℕ) = 1
      have h2 : (i : ℕ) ≠ 0 := fun hc => h (Fin.ext hc)
      have h3 := i.isLt
      omega
    subst h1
    rw [Function.update_of_ne (by decide), braidData_cdPathC_hi_snd_one,
      braidData_cdPathC_lo_snd_one]

/-- **The lower special braid of the type-`C` witness is one letter**, read straight off
`HJO.Mellit.specialMoveList_cdPathC_lo`: the move sequence is `[0]`, so `HJO.Braid.braidWord` is a
single `HJO.Braid.braidStep`. -/
theorem specialBraid_cdPathC_lo_decided :
    specialBraid (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1
        (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).2
      = braidStep (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 0 := by
  rw [specialBraid, specialMoveList_cdPathC_lo, braidWord_singleton]

/-- The same through `HJO.Braid.specialBraid_update_succ_left`: the unraised special braid is the
identity (every upper multiplicity is `1`) and the final position tuple of the unraised data is the
initial one, so the general left form collapses to the same single letter. -/
theorem specialBraid_cdPathC_lo_via_general :
    specialBraid (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1
        (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).2
      = braidStep (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 0 := by
  have hdata : IsSpecialBraidData (sweepSlope 2 3 1) (sweepTheta 2 3 1) 2
      (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1
      (Function.update (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 0
        ((braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 0 + 1)) := by
    rw [← braidData_cdPathC_lo_snd_eq_update]
    exact isSpecialBraidData_braidDataOfColouring_of_card (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_cdLoC (by norm_num [cdLoC]) isAboveDiagonal_cdPathC
      card_colouringNorth_cdPathC_lo
  rw [braidData_cdPathC_lo_snd_eq_update,
    specialBraid_update_succ_left 0 (by rw [braidData_cdPathC_hi_snd_eq_one]) hdata,
    specialBraid_of_forall_eq_one braidData_cdPathC_hi_snd_eq_one, mul_one]
  congr 1
  funext t
  exact positionPair_snd_of_mult_eq_one (braidData_cdPathC_hi_snd_eq_one t)

/-- The two readings are the same statement, so the general left form lands on the decided
letter. -/
example : specialBraid_cdPathC_lo_decided = specialBraid_cdPathC_lo_via_general := rfl

/-! ### The equal-rank raise at the type-`D` witness -/

/-- The lower multiplicity of the type-`D` witness is the upper one raised by one. -/
theorem braidData_cdPathD_lo_snd_eq_update :
    (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).2
      = Function.update (braidDataOfColouring 2 3 1 cdPathD cdHiD 1).2 0
          ((braidDataOfColouring 2 3 1 cdPathD cdHiD 1).2 0 + 1) := by
  funext i
  rw [show i = 0 from Fin.eq_zero i, Function.update_self, braidData_cdPathD_hi_snd,
    braidData_cdPathD_lo_snd]

/-- **The lower special braid of the type-`D` witness is two letters**, read straight off
`HJO.Mellit.specialMoveList_cdPathD_lo`: the move sequence is `[0, 0]`, the head being the move
performed last. -/
theorem specialBraid_cdPathD_lo_decided :
    specialBraid (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1
        (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).2
      = braidStep (sweepTheta 2 3 1)
            (moveOne (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1 0) 0
          * braidStep (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1 0 := by
  rw [specialBraid, specialMoveList_cdPathD_lo, braidWord_pair]

/-- The same through `HJO.Braid.specialBraid_update_succ_right`: the added letter stands
**rightmost** and is read at `v` itself, the unraised braid being the one move of the upper data at
the once-moved tuple. -/
theorem specialBraid_cdPathD_lo_via_general :
    specialBraid (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1
        (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).2
      = braidStep (sweepTheta 2 3 1)
            (moveOne (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1 0) 0
          * braidStep (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1 0 := by
  have hdata : IsSpecialBraidData (sweepSlope 2 3 1) (sweepTheta 2 3 1) 1
      (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1
      (Function.update (braidDataOfColouring 2 3 1 cdPathD cdHiD 1).2 0
        ((braidDataOfColouring 2 3 1 cdPathD cdHiD 1).2 0 + 1)) := by
    rw [← braidData_cdPathD_lo_snd_eq_update]
    exact isSpecialBraidData_braidDataOfColouring_of_card (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_cdLoD (by norm_num [cdLoD]) isAboveDiagonal_cdPathD
      card_colouringNorth_cdPathD_lo
  rw [braidData_cdPathD_lo_snd_eq_update,
    specialBraid_update_succ_right 0 (by rw [braidData_cdPathD_hi_snd]; norm_num) hdata,
    specialBraid, specialMoveList_cdPathD_hi, braidWord_singleton]

/-- The two readings are the same statement, so the general right form lands on the decided pair of
letters. -/
example : specialBraid_cdPathD_lo_decided = specialBraid_cdPathD_lo_via_general := rfl

/-! ### The once-moved type-`D` tuple -/

/-- The wrapped lower position `1/28` advances to `17/28`, read straight off
`HJO.Braid.nextCrossing`: it lies below the puncture `12/28`, so `nx_θ` adds `1 - θ = 16/28`. -/
theorem moveOne_cdPathD_decided :
    moveOne (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1 0 0 = 17 / 28 := by
  rw [moveOne_self, braidData_cdPathD_lo_fst, sweepTheta_cd, nextCrossing]
  norm_num

/-- The same through `HJO.Mellit.Isolates.moveOne_braidData_fst_of_eventType_D`: `17/28` is the
upper position `15/28` rigidly rotated by `HJO.Mellit.levelDropShift = 1/14`. The side conditions
are discharged at this witness — `15/28 + 1/14 = 17/28` is in `[0, 1)`, and the lower position
`1/28` is not the puncture `12/28`. -/
theorem moveOne_cdPathD_via_general :
    moveOne (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1 0 0 = 17 / 28 := by
  have hshift : levelDropShift 2 3 1 cdLoD cdHiD = 1 / 14 := by
    rw [show cdHiD = cdLoD + 1 from cdLoD_lt_cdHiD]; exact levelDropShift_cd cdLoD
  rw [isolates_cdPathD.moveOne_braidData_fst_of_eventType_D (by norm_num) (by norm_num)
      (by norm_num) lt_cdLoD isAboveDiagonal_cdPathD eventType_cdPathD
      card_colouringEast_cdPathD_hi 0 colStep_colouringEast_cdPathD_hi
      (by rw [sweepTheta_cd]; norm_num) (by rw [sweepTheta_cd]; norm_num)
      (by rw [braidData_cdPathD_lo_fst, sweepTheta_cd]; norm_num)
      (by rw [braidData_cdPathD_hi_fst, hshift]; norm_num)
      (by rw [braidData_cdPathD_hi_fst, hshift]; norm_num)]
  change (braidDataOfColouring 2 3 1 cdPathD cdHiD 1).1 0 + levelDropShift 2 3 1 cdLoD cdHiD
    = 17 / 28
  rw [braidData_cdPathD_hi_fst, hshift]
  norm_num

/-- The two readings are the same statement, hence the same value. -/
example : moveOne_cdPathD_decided = moveOne_cdPathD_via_general := rfl

/-! ### Which letter the type-`C` residual is about

The letter the general left form produces at the type-`C` witness is written out here, because
*which index it carries* is what decides whether the residual can match `HJO.Sweep.corner` at all:
`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` reads `Δ^{(k)}F = -T_{1↑k}(y_kF)`, whose `y` is at
the **top** index `k`. At this witness the moving position `13/28` is the largest of the two, so its
rank in the final tuple is `2 = k` and the letter is `ỹ_2` — the top index, as the corner's closed
form needs — and after the move it drops to `1/28`, the smallest, so the train is `T_{1↘2}`,
matching the `T_{1↑2}` of the closed form up to direction.

That the rank is `k` and the train is the full `T_{1↘k}` is **not** proved in general anywhere; it
is exactly the geometric input the type-`C` residual still needs, and this witness is one instance
of it. -/
theorem braidStep_cdPathC_lo :
    braidStep (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 0
      = braidTrainDown 2 1 2 * braidYtilde 2 2 := by
  have hle : ∀ j : Fin 2, (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 j
      ≤ (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 0 := by
    intro j
    by_cases h : j = 0
    · subst h; exact le_rfl
    · have h1 : j = 1 := by
        refine Fin.ext ?_
        change (j : ℕ) = 1
        have h2 : (j : ℕ) ≠ 0 := fun hc => h (Fin.ext hc)
        have h3 := j.isLt
        omega
      subst h1
      rw [braidData_cdPathC_lo_fst_zero, braidData_cdPathC_lo_fst_one]
      norm_num
  have hrk : entryRank (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 0 = 2 := by
    rw [entryRank, Finset.filter_true_of_mem fun j _ => hle j, Finset.card_univ,
      Fintype.card_fin]
  have hrk' : entryRank
      (moveOne (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 0) 0 = 1 := by
    rw [entryRank]
    refine Finset.card_eq_one.2 ⟨0, Finset.eq_singleton_iff_unique_mem.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩, fun j hj => ?_⟩⟩
    have hj' := (Finset.mem_filter.1 hj).2
    by_contra h
    have h1 : j = 1 := by
      refine Fin.ext ?_
      change (j : ℕ) = 1
      have h2 : (j : ℕ) ≠ 0 := fun hc => h (Fin.ext hc)
      have h3 := j.isLt
      omega
    subst h1
    rw [moveOne_of_ne _ _ (by decide), moveOne_self, braidData_cdPathC_lo_fst_zero,
      braidData_cdPathC_lo_fst_one, sweepTheta_cd, nextCrossing] at hj'
    norm_num at hj'
  rw [braidStep_of_gt (w := (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1) (i := 0)
      (by rw [braidData_cdPathC_lo_fst_zero, sweepTheta_cd]; norm_num), hrk, hrk']

end HJO.Mellit
