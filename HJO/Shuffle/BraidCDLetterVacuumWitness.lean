/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidCDLetterVacuum
public import HJO.Shuffle.BraidCDLetterWitness
public import HJO.Shuffle.MellitStarVertex
public import HJO.Shuffle.MellitStraightMonomial
public meta import HJO.Attr

/-! # Consistency checks for the type-`D` clause

Four computations go into the type-`D` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, and each of them would move a `q`-power
silently if it were off by one. So each is re-derived here against a value obtained without it.

* **`z_1` on the vacuum.** `HJO.Sweep.zopOneStar_auxVarProd` computes
  `z_1(y_1⋯y_k) = q^{k}u·y_1⋯y_k` by evaluating both halves of `HJO.Sweep.zop` on the monomial. At
  `k = 1`
  `HJO.Sweep.zopOneStar_one_auxVar_mul_of_mem_piece` gives the same value by a route that never
  touches `HJO.Sweep.bopExt`: it moves one letter `y_1` out of `z_1` at the cost of the
  `d^*_+d_-` term, which vanishes on the unit. Both give `qu·y_1`, so the factor `u` and the power
  of `q` are confirmed independently — and they are exactly what the clause's `q^{a}` needs.
* **The letter.** `HJO.Mellit.Isolates.braidStep_braidData_fst_of_eventType_D` reads the added
  letter as `T_{k↘1}z_1`. At the witness that is `z_1` with no train, and the same letter comes off
  `HJO.Braid.braidStep` directly from the wrapped position `1/28` being below the puncture `3/7`.
  **The `z`-count is a second, free check**: `HJO.Mellit.zCount_cdPathD_lo` computes the `z`-count
  of the lower braid as `1` against the upper `0`, and a `z` is exactly what this letter is. Had the
  general evaluation produced a `ỹ` the two would disagree.
* **`hlt`.** `HJO.Mellit.Isolates.braidData_fst_add_levelDropShift_lt_one_of_eventType_D` discharges
  in general the side condition that `HJO.Mellit.moveOne_cdPathD_via_general` had to supply by hand;
  the rotated tuple still lands on `17/28`.
* **The clause.** `HJO.Mellit.sweep_typeD_cdPathD` is the type-`D` clause at the witness with every
  hypothesis discharged by `norm_num` or `decide`, the counterpart of
  `HJO.Mellit.sweep_typeC_cdPathC`.

Each pair is closed by `example : decided = via_general := rfl`, which typechecks only if the two
statements are literally the same `Prop`.

## References

The file tests the type-`D` clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`
against `HJO.Braid.braidStep`, `HJO.Sweep.zop`, `HJO.Sweep.braidRep` and
`HJO.Mellit.sweepOperator`.
-/

@[expose] public section

open Finset

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### `z_1` on the rank-one vacuum, twice -/

/-- **`z_1(y_1) = qu·y_1`, by moving the letter out of `z_1`.** This is
`HJO.Sweep.zopOneStar_one_auxVar_mul_of_mem_piece` at `G = 1`: `z_1` annihilates the unit
(`HJO.Sweep.zopOneStar_one_one`) and `d^*_+{}^{(0)}d_-^{(1)}` fixes it
(`HJO.Sweep.dminus_one`), so the whole value is the cost `quy_1` of moving the letter. This route
evaluates no `d_-` on a monomial and never mentions `HJO.Sweep.bopExt`. -/
theorem zopOneStar_one_auxVar_decided (q u : L) (hq1 : q ≠ 1) :
    zopOneStar q u 1 (auxVarProd L 1) = (q ^ 1 * u) • auxVarProd L 1 := by
  have hmem : (1 : Total L) ∈ piece L 1 := one_mem _
  have hprod : auxVarProd L 1 = (auxVar 1 : Total L) := by
    rw [auxVarProd_succ, auxVarProd_zero, one_mul]
  rw [hprod, show (auxVar 1 : Total L) = (auxVar 1 : Total L) * 1 from (mul_one _).symm,
    zopOneStar_one_auxVar_mul_of_mem_piece hq1 hmem, zopOneStar_one_one, dminus_one,
    show dplusStar q u 0 (1 : Total L) = 1 from by rw [dplusStar_apply, map_one, map_one],
    zero_add, mul_one, Algebra.smul_def, ← scal_eq_algebraMap, pow_one]
  ring

/-- **The same through `HJO.Sweep.zopOneStar_auxVarProd`**, which computes both halves of
`HJO.Sweep.zop` on the monomial `y_1⋯y_k` at every rank and never moves a letter. -/
theorem zopOneStar_one_auxVar_via_general (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) :
    zopOneStar q u 1 (auxVarProd L 1) = (q ^ 1 * u) • auxVarProd L 1 :=
  zopOneStar_auxVarProd q u hq hq1 0

end HJO.Sweep

namespace HJO.Mellit

open Braid Finset ParkingFunctions Paths Sweep

/-- The two readings of `z_1` on the rank-one vacuum are the same statement, so the general
evaluation gives the independently computed value. -/
example {L : Type*} [Field L] [Algebra ℚ L] (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) :
    zopOneStar_one_auxVar_decided (L := L) q u hq1
      = zopOneStar_one_auxVar_via_general (L := L) q u hq hq1 := rfl

/-- **`π_1(z_1)` FIXES the vacuum.** The rank-one case of
`HJO.Sweep.braidRepMellit_braidTrainDown_top_mul_braidGenZ_one_dplusIterPiece`, where the train is
empty and the exponent `r^{k-1}` is `1`: the type-`D` clause at rank `1` asserts `R_- = R_+` with no
scalar at all, so the letter must fix the vector on the nose, and it does. `u ≠ 0` is still spent —
the `(qu)^{-1}` of `HJO.Sweep.braidRep` against the `qu` of
`HJO.Sweep.zopOneStar_one_auxVar_via_general`. -/
theorem braidRepMellit_braidGenZ_one_dplusIterPiece_one {L : Type*} [Field L] [Algebra ℚ L]
    (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) {r : L} (hr : r * r = q) (hu : u ≠ 0) :
    braidRepMellit q u hq hq1 hqp hr 1 (braidTrainDown 1 1 1 * braidGenZ 1 1)
        (dplusIterPiece q 1)
      = dplusIterPiece q 1 := by
  rw [braidRepMellit_braidTrainDown_top_mul_braidGenZ_one_dplusIterPiece q u hq hq1 hqp hr hu
    le_rfl]
  norm_num

/-! ### The type-`D` letter at the decided witness -/

/-- **The letter of the type-`D` witness, read straight off `HJO.Braid.braidStep`.** The wrapped
position `1/28` lies below the puncture `12/28`, so the generator is a `z`; the rank is `1` at both
ends because the tuple has one entry, so the train is empty. -/
theorem braidStep_cdPathD_lo_decided :
    braidStep (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1 0
      = braidTrainDown 1 1 1 * braidGenZ 1 1 := by
  rw [braidStep_of_lt (w := (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1) (i := 0)
      (by rw [braidData_cdPathD_lo_fst, sweepTheta_cd]; norm_num),
    entryRank_fin_one _ 0, entryRank_fin_one _ 0]

/-- **The same through the general evaluation.**
`HJO.Mellit.Isolates.braidStep_braidData_fst_of_eventType_D` produces `T_{k↘1}z_1` from the event
type alone, with the positions never mentioned — the `z` branch coming from the moving position
lying below the whole rigid rotation, and the two ranks from the strict extremality proved in
general. -/
theorem braidStep_cdPathD_lo_via_general :
    braidStep (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1 0
      = braidTrainDown 1 1 1 * braidGenZ 1 1 :=
  isolates_cdPathD.braidStep_braidData_fst_of_eventType_D (by norm_num) (by norm_num) (by norm_num)
    lt_cdLoD (by rw [cdLoD_lt_cdHiD]) isAboveDiagonal_cdPathD eventType_cdPathD
    card_colouringEast_cdPathD_hi 0 colStep_colouringEast_cdPathD_hi

/-- The two readings are the same statement, so the general evaluation gives the decided
letter — a `z`, which is what `HJO.Mellit.zCount_cdPathD_lo` counts. -/
example : braidStep_cdPathD_lo_decided = braidStep_cdPathD_lo_via_general := rfl

/-! ### The rotated tuple, with `hlt` discharged in general -/

/-- **`HJO.Mellit.moveOne_cdPathD_via_general` with no side condition supplied by hand.** There the
check `15/28 + 1/14 < 1` had to be made at the witness;
`HJO.Mellit.Isolates.braidData_fst_add_levelDropShift_lt_one_of_eventType_D` supplies it from
`η₊ ≤ η₋ + 1` at every witness, so the identification of the once-moved lower tuple with the rigidly
rotated upper one is unconditional in that range. -/
theorem moveOne_cdPathD_via_general_uncond :
    moveOne (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1 0 0 = 17 / 28 := by
  have hshift : levelDropShift 2 3 1 cdLoD cdHiD = 1 / 14 := by
    rw [show cdHiD = cdLoD + 1 from cdLoD_lt_cdHiD]; exact levelDropShift_cd cdLoD
  rw [isolates_cdPathD.moveOne_braidData_fst_eq_of_eventType_D (by norm_num) (by norm_num)
      (by norm_num) lt_cdLoD (by rw [cdLoD_lt_cdHiD]) isAboveDiagonal_cdPathD eventType_cdPathD
      card_colouringEast_cdPathD_hi 0 colStep_colouringEast_cdPathD_hi]
  change (braidDataOfColouring 2 3 1 cdPathD cdHiD 1).1 0 + levelDropShift 2 3 1 cdLoD cdHiD
    = 17 / 28
  rw [braidData_cdPathD_hi_fst, hshift]
  norm_num

/-- The unconditional reading is the same statement as the hand-computed one, hence the same
value. -/
example : moveOne_cdPathD_decided = moveOne_cdPathD_via_general_uncond := rfl

/-! ### The clause at the decided witness -/

/-- **THE TYPE-`D` CLAUSE OF `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` AT THE DECIDED
WITNESS.** The counterpart of `HJO.Mellit.sweep_typeC_cdPathC` and `HJO.Mellit.gap_typeA_uncond`:
every hypothesis of
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_D_of_step` is discharged by
`norm_num` or `decide` on the witness, the level-gap bound being the witness's own
`HJO.Mellit.cdLoD_lt_cdHiD`.

`u ≠ 0` is carried, and at `u = 0` the statement is false rather than vacuous: the letter
`π_1(z_1)` is the zero map there. -/
theorem sweep_typeD_cdPathD {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) :
    braidValueColouring q u hq hq1 hqp hr 2 3 1 cdLoD (colouring cdPathD cdLoD)
      = sweepOperator q u cdPathD (1, 3)
          (braidValueColouring q u hq hq1 hqp hr 2 3 1 cdHiD (colouring cdPathD cdHiD)) :=
  isolates_cdPathD.braidValueColouring_eq_sweepOperator_of_eventType_D_of_step q u hq hq1 hqp hr hu
    (by norm_num) (by norm_num) (by norm_num) lt_cdLoD (by rw [cdLoD_lt_cdHiD])
    isAboveDiagonal_cdPathD eventType_cdPathD

end HJO.Mellit

end
