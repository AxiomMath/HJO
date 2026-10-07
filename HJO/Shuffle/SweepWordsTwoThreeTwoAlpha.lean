/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWordsTwoThreeTwo

/-! # The nineteen sweep words of the `4 × 6` rectangle at `c_{(2)}`

`HJO.Mellit.card_aboveDiagonal_compColouring_two_three_two` counts nineteen above-diagonal
`(4,6)`-paths whose colouring at the level `9/2` is `c_{(2)}`. This file names them and peels each
of their partial sweep words into an explicit product of event operators of
`HJO.Mellit.sweepOperator`, by the same two steps `HJO/Shuffle/SweepWordsTwoThreeTwo.lean` uses at
`c_{(1,1)}`: `HJO.Mellit.partialSweepWord_step_two` past a swept rank and
`HJO.Mellit.partialSweepWord_skip` past a lattice rank the path does not sweep.

## The shape of the nineteen

Every one of the nineteen has `hat y_2 >= 4`, which is what distinguishes `c_{(2)}` from
`c_{(1,1)}`: the level `9/2` picks up the extra cells `(1,3)` and `(2,3)` exactly when
`hat y_2 = 3`. The words run from nine to sixteen events. Two of them reach width `4` — the paths
`(0,2,4,5,6)` and `(0,3,4,5,6)` — seven reach width `3`, nine stop at width `2`, and the staircase
`(0,6,6,6,6)` never leaves width `1`.

The skips matter more here than at `c_{(1,1)}`: the rectangle has sixteen lattice ranks above
`9/2` and a path sweeps between nine and sixteen of them, so all but the longest words cross a
rank at which they have no event.

## References

Builds on `HJO.Mellit.sweepOperator`, `HJO.Mellit.partialSweepWord`,
`HJO.Mellit.partialSweepWord_eq_sweepOperator_mul` and `HJO.Mellit.dsc`.
-/

@[expose] public section

namespace HJO.Mellit

open Finset HJO.Paths HJO.Sweep

section Words

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The above-diagonal `(4,6)`-path `(0,2,4,5,6)`. -/
def alphaTwoPath245 : Paths.Heights 2 3 2 := ![0, 2, 4, 5, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,2,4,5,6)`**, 9 events, widths up to `4`. -/
theorem partialSweepWord_alphaTwoPath245 (q u : L) :
    partialSweepWord q u alphaTwoPath245 (sepLevel 2 2)
      = (dminus q 2) * ((dminus q 3) * ((((q : L) ^ (-2 : ℤ)) • corner q 3) * ((dminus q 4) *
          ((((q : L) ^ (-2 : ℤ)) • corner q 4) * ((dplus q 3) * ((dplus q 2) * ((dplus q 1) *
          ((dplus q 0) * ((1 : Module.End L (Total L))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath245 ((1, 2) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath245 ((1, 2) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath245 ((1, 2) : ℕ × ℕ) = 2 from by decide]
  have op1 : sweepOperator q u alphaTwoPath245 ((3, 5) : ℕ × ℕ) = dminus q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath245 ((3, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath245 ((3, 5) : ℕ × ℕ) = 3 from by decide]
  have op2 : sweepOperator q u alphaTwoPath245 ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-2 : ℤ)) • corner q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath245 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath245 ((0, 1) : ℕ × ℕ) = 3 from by decide,
      show sweepRight alphaTwoPath245 ((0, 1) : ℕ × ℕ) = 2 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath245 ((2, 4) : ℕ × ℕ) = dminus q 4 := by
    rw [sweepOperator,
      show eventType alphaTwoPath245 ((2, 4) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath245 ((2, 4) : ℕ × ℕ) = 4 from by decide]
  have op4 : sweepOperator q u alphaTwoPath245 ((1, 3) : ℕ × ℕ)
      = ((q : L) ^ (-2 : ℤ)) • corner q 4 := by
    rw [sweepOperator,
      show eventType alphaTwoPath245 ((1, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath245 ((1, 3) : ℕ × ℕ) = 4 from by decide,
      show sweepRight alphaTwoPath245 ((1, 3) : ℕ × ℕ) = 2 from by decide]
    norm_num
  have op5 : sweepOperator q u alphaTwoPath245 ((3, 6) : ℕ × ℕ) = dplus q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath245 ((3, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath245 ((3, 6) : ℕ × ℕ) = 3 from by decide]
  have op6 : sweepOperator q u alphaTwoPath245 ((0, 2) : ℕ × ℕ) = dplus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath245 ((0, 2) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath245 ((0, 2) : ℕ × ℕ) = 2 from by decide]
  have op7 : sweepOperator q u alphaTwoPath245 ((2, 5) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath245 ((2, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath245 ((2, 5) : ℕ × ℕ) = 1 from by decide]
  have op8 : sweepOperator q u alphaTwoPath245 ((1, 4) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath245 ((1, 4) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath245 ((1, 4) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 51) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8]

/-- The above-diagonal `(4,6)`-path `(0,2,4,6,6)`. -/
def alphaTwoPath246 : Paths.Heights 2 3 2 := ![0, 2, 4, 6, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,2,4,6,6)`**, 10 events, widths up to `3`. -/
theorem partialSweepWord_alphaTwoPath246 (q u : L) :
    partialSweepWord q u alphaTwoPath246 (sepLevel 2 2)
      = (dminus q 2) * ((u • (1 : Module.End L (Total L))) * ((((q : L) ^ (-1 : ℤ)) • corner q 2)
          * ((dminus q 3) * ((((q : L) ^ (-1 : ℤ)) • corner q 3) * (((1 : Module.End L (Total L)))
          * ((dplus q 2) * ((corner q 2) * ((dplus q 1) * ((dplus q 0) * ((1 : Module.End L (Total
          L)))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath246 ((1, 2) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath246 ((1, 2) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath246 ((1, 2) : ℕ × ℕ) = 2 from by decide]
  have op1 : sweepOperator q u alphaTwoPath246 ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath246 ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op2 : sweepOperator q u alphaTwoPath246 ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath246 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath246 ((0, 1) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath246 ((0, 1) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath246 ((2, 4) : ℕ × ℕ) = dminus q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath246 ((2, 4) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath246 ((2, 4) : ℕ × ℕ) = 3 from by decide]
  have op4 : sweepOperator q u alphaTwoPath246 ((1, 3) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath246 ((1, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath246 ((1, 3) : ℕ × ℕ) = 3 from by decide,
      show sweepRight alphaTwoPath246 ((1, 3) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op5 : sweepOperator q u alphaTwoPath246 ((3, 6) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath246 ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath246 ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op6 : sweepOperator q u alphaTwoPath246 ((0, 2) : ℕ × ℕ) = dplus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath246 ((0, 2) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath246 ((0, 2) : ℕ × ℕ) = 2 from by decide]
  have op7 : sweepOperator q u alphaTwoPath246 ((2, 5) : ℕ × ℕ) = corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath246 ((2, 5) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath246 ((2, 5) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath246 ((2, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op8 : sweepOperator q u alphaTwoPath246 ((1, 4) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath246 ((1, 4) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath246 ((1, 4) : ℕ × ℕ) = 1 from by decide]
  have op9 : sweepOperator q u alphaTwoPath246 ((2, 6) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath246 ((2, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath246 ((2, 6) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 51) (n := 60) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 62) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9]

/-- The above-diagonal `(4,6)`-path `(0,2,5,5,6)`. -/
def alphaTwoPath255 : Paths.Heights 2 3 2 := ![0, 2, 5, 5, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,2,5,5,6)`**, 10 events, widths up to `3`. -/
theorem partialSweepWord_alphaTwoPath255 (q u : L) :
    partialSweepWord q u alphaTwoPath255 (sepLevel 2 2)
      = (dminus q 2) * ((dminus q 3) * ((((q : L) ^ (-2 : ℤ)) • corner q 3) * ((u • (1 :
          Module.End L (Total L))) * ((((q : L) ^ (-1 : ℤ)) • corner q 3) * ((dplus q 2) * ((dplus
          q 1) * (((1 : Module.End L (Total L))) * ((corner q 1) * ((dplus q 0) * ((1 : Module.End
          L (Total L)))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath255 ((1, 2) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath255 ((1, 2) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath255 ((1, 2) : ℕ × ℕ) = 2 from by decide]
  have op1 : sweepOperator q u alphaTwoPath255 ((3, 5) : ℕ × ℕ) = dminus q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath255 ((3, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath255 ((3, 5) : ℕ × ℕ) = 3 from by decide]
  have op2 : sweepOperator q u alphaTwoPath255 ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-2 : ℤ)) • corner q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath255 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath255 ((0, 1) : ℕ × ℕ) = 3 from by decide,
      show sweepRight alphaTwoPath255 ((0, 1) : ℕ × ℕ) = 2 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath255 ((2, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath255 ((2, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op4 : sweepOperator q u alphaTwoPath255 ((1, 3) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath255 ((1, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath255 ((1, 3) : ℕ × ℕ) = 3 from by decide,
      show sweepRight alphaTwoPath255 ((1, 3) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op5 : sweepOperator q u alphaTwoPath255 ((3, 6) : ℕ × ℕ) = dplus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath255 ((3, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath255 ((3, 6) : ℕ × ℕ) = 2 from by decide]
  have op6 : sweepOperator q u alphaTwoPath255 ((0, 2) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath255 ((0, 2) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath255 ((0, 2) : ℕ × ℕ) = 1 from by decide]
  have op7 : sweepOperator q u alphaTwoPath255 ((2, 5) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath255 ((2, 5) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath255 ((2, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op8 : sweepOperator q u alphaTwoPath255 ((1, 4) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath255 ((1, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath255 ((1, 4) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath255 ((1, 4) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op9 : sweepOperator q u alphaTwoPath255 ((1, 5) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath255 ((1, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath255 ((1, 5) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 51) (n := 60) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 60) (n := 62) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 5)) (m := 62) (n := 71) (r := 71)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 71) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9]

/-- The above-diagonal `(4,6)`-path `(0,2,5,6,6)`. -/
def alphaTwoPath256 : Paths.Heights 2 3 2 := ![0, 2, 5, 6, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,2,5,6,6)`**, 11 events, widths up to `2`. -/
theorem partialSweepWord_alphaTwoPath256 (q u : L) :
    partialSweepWord q u alphaTwoPath256 (sepLevel 2 2)
      = (dminus q 2) * ((u • (1 : Module.End L (Total L))) * ((((q : L) ^ (-1 : ℤ)) • corner q 2)
          * ((u • (1 : Module.End L (Total L))) * ((corner q 2) * (((1 : Module.End L (Total L)))
          * ((dplus q 1) * ((dminus q 2) * ((((q : L) ^ (-1 : ℤ)) • corner q 2) * ((dplus q 1) *
          ((dplus q 0) * ((1 : Module.End L (Total L))))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath256 ((1, 2) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath256 ((1, 2) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath256 ((1, 2) : ℕ × ℕ) = 2 from by decide]
  have op1 : sweepOperator q u alphaTwoPath256 ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath256 ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op2 : sweepOperator q u alphaTwoPath256 ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath256 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath256 ((0, 1) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath256 ((0, 1) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath256 ((2, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath256 ((2, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op4 : sweepOperator q u alphaTwoPath256 ((1, 3) : ℕ × ℕ) = corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath256 ((1, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath256 ((1, 3) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath256 ((1, 3) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op5 : sweepOperator q u alphaTwoPath256 ((3, 6) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath256 ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath256 ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op6 : sweepOperator q u alphaTwoPath256 ((0, 2) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath256 ((0, 2) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath256 ((0, 2) : ℕ × ℕ) = 1 from by decide]
  have op7 : sweepOperator q u alphaTwoPath256 ((2, 5) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath256 ((2, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath256 ((2, 5) : ℕ × ℕ) = 2 from by decide]
  have op8 : sweepOperator q u alphaTwoPath256 ((1, 4) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath256 ((1, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath256 ((1, 4) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath256 ((1, 4) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op9 : sweepOperator q u alphaTwoPath256 ((2, 6) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath256 ((2, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath256 ((2, 6) : ℕ × ℕ) = 1 from by decide]
  have op10 : sweepOperator q u alphaTwoPath256 ((1, 5) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath256 ((1, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath256 ((1, 5) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 51) (n := 60) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 5)) (m := 62) (n := 71) (r := 71)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 71) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10]

/-- The above-diagonal `(4,6)`-path `(0,2,6,6,6)`. -/
def alphaTwoPath266 : Paths.Heights 2 3 2 := ![0, 2, 6, 6, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,2,6,6,6)`**, 12 events, widths up to `2`. -/
theorem partialSweepWord_alphaTwoPath266 (q u : L) :
    partialSweepWord q u alphaTwoPath266 (sepLevel 2 2)
      = (dminus q 2) * ((u • (1 : Module.End L (Total L))) * ((((q : L) ^ (-1 : ℤ)) • corner q 2)
          * ((u • (1 : Module.End L (Total L))) * ((corner q 2) * (((1 : Module.End L (Total L)))
          * ((dplus q 1) * ((u • (1 : Module.End L (Total L))) * ((corner q 1) * (((1 : Module.End
          L (Total L))) * ((corner q 1) * ((dplus q 0) * ((1 : Module.End L (Total L))))))))))))))
      := by
  have op0 : sweepOperator q u alphaTwoPath266 ((1, 2) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath266 ((1, 2) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath266 ((1, 2) : ℕ × ℕ) = 2 from by decide]
  have op1 : sweepOperator q u alphaTwoPath266 ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath266 ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op2 : sweepOperator q u alphaTwoPath266 ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath266 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath266 ((0, 1) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath266 ((0, 1) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath266 ((2, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath266 ((2, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op4 : sweepOperator q u alphaTwoPath266 ((1, 3) : ℕ × ℕ) = corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath266 ((1, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath266 ((1, 3) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath266 ((1, 3) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op5 : sweepOperator q u alphaTwoPath266 ((3, 6) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath266 ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath266 ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op6 : sweepOperator q u alphaTwoPath266 ((0, 2) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath266 ((0, 2) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath266 ((0, 2) : ℕ × ℕ) = 1 from by decide]
  have op7 : sweepOperator q u alphaTwoPath266 ((2, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath266 ((2, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op8 : sweepOperator q u alphaTwoPath266 ((1, 4) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath266 ((1, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath266 ((1, 4) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath266 ((1, 4) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op9 : sweepOperator q u alphaTwoPath266 ((2, 6) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath266 ((2, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath266 ((2, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op10 : sweepOperator q u alphaTwoPath266 ((1, 5) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath266 ((1, 5) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath266 ((1, 5) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath266 ((1, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op11 : sweepOperator q u alphaTwoPath266 ((1, 6) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath266 ((1, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath266 ((1, 6) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 51) (n := 60) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 5)) (m := 62) (n := 71) (r := 71)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 71) (n := 80) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 6)) (m := 80) (n := 91) (r := 91)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 91) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10, op11]

/-- The above-diagonal `(4,6)`-path `(0,3,4,5,6)`. -/
def alphaTwoPath345 : Paths.Heights 2 3 2 := ![0, 3, 4, 5, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,3,4,5,6)`**, 10 events, widths up to `4`. -/
theorem partialSweepWord_alphaTwoPath345 (q u : L) :
    partialSweepWord q u alphaTwoPath345 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((dminus q 2) * ((((q : L) ^ (-1 : ℤ)) • corner q 2)
          * ((dminus q 3) * ((dminus q 4) * ((dplus q 3) * ((((q : L) ^ (-2 : ℤ)) • corner q 3) *
          ((dplus q 2) * ((dplus q 1) * ((dplus q 0) * ((1 : Module.End L (Total L)))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath345 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath345 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath345 ((3, 5) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath345 ((3, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath345 ((3, 5) : ℕ × ℕ) = 2 from by decide]
  have op2 : sweepOperator q u alphaTwoPath345 ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath345 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath345 ((0, 1) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath345 ((0, 1) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath345 ((2, 4) : ℕ × ℕ) = dminus q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath345 ((2, 4) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath345 ((2, 4) : ℕ × ℕ) = 3 from by decide]
  have op4 : sweepOperator q u alphaTwoPath345 ((1, 3) : ℕ × ℕ) = dminus q 4 := by
    rw [sweepOperator,
      show eventType alphaTwoPath345 ((1, 3) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath345 ((1, 3) : ℕ × ℕ) = 4 from by decide]
  have op5 : sweepOperator q u alphaTwoPath345 ((3, 6) : ℕ × ℕ) = dplus q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath345 ((3, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath345 ((3, 6) : ℕ × ℕ) = 3 from by decide]
  have op6 : sweepOperator q u alphaTwoPath345 ((0, 2) : ℕ × ℕ)
      = ((q : L) ^ (-2 : ℤ)) • corner q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath345 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath345 ((0, 2) : ℕ × ℕ) = 3 from by decide,
      show sweepRight alphaTwoPath345 ((0, 2) : ℕ × ℕ) = 2 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath345 ((2, 5) : ℕ × ℕ) = dplus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath345 ((2, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath345 ((2, 5) : ℕ × ℕ) = 2 from by decide]
  have op8 : sweepOperator q u alphaTwoPath345 ((1, 4) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath345 ((1, 4) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath345 ((1, 4) : ℕ × ℕ) = 1 from by decide]
  have op9 : sweepOperator q u alphaTwoPath345 ((0, 3) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath345 ((0, 3) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath345 ((0, 3) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 60) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9]

/-- The above-diagonal `(4,6)`-path `(0,3,4,6,6)`. -/
def alphaTwoPath346 : Paths.Heights 2 3 2 := ![0, 3, 4, 6, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,3,4,6,6)`**, 11 events, widths up to `3`. -/
theorem partialSweepWord_alphaTwoPath346 (q u : L) :
    partialSweepWord q u alphaTwoPath346 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * ((corner q 1) *
          ((dminus q 2) * ((dminus q 3) * (((1 : Module.End L (Total L))) * ((((q : L) ^ (-2 : ℤ))
          • corner q 3) * ((corner q 3) * ((dplus q 2) * ((dplus q 1) * ((dplus q 0) * ((1 :
          Module.End L (Total L))))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath346 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath346 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath346 ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath346 ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op2 : sweepOperator q u alphaTwoPath346 ((0, 1) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath346 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath346 ((0, 1) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath346 ((0, 1) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath346 ((2, 4) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath346 ((2, 4) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath346 ((2, 4) : ℕ × ℕ) = 2 from by decide]
  have op4 : sweepOperator q u alphaTwoPath346 ((1, 3) : ℕ × ℕ) = dminus q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath346 ((1, 3) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath346 ((1, 3) : ℕ × ℕ) = 3 from by decide]
  have op5 : sweepOperator q u alphaTwoPath346 ((3, 6) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath346 ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath346 ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op6 : sweepOperator q u alphaTwoPath346 ((0, 2) : ℕ × ℕ)
      = ((q : L) ^ (-2 : ℤ)) • corner q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath346 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath346 ((0, 2) : ℕ × ℕ) = 3 from by decide,
      show sweepRight alphaTwoPath346 ((0, 2) : ℕ × ℕ) = 2 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath346 ((2, 5) : ℕ × ℕ) = corner q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath346 ((2, 5) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath346 ((2, 5) : ℕ × ℕ) = 3 from by decide,
      show sweepRight alphaTwoPath346 ((2, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op8 : sweepOperator q u alphaTwoPath346 ((1, 4) : ℕ × ℕ) = dplus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath346 ((1, 4) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath346 ((1, 4) : ℕ × ℕ) = 2 from by decide]
  have op9 : sweepOperator q u alphaTwoPath346 ((0, 3) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath346 ((0, 3) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath346 ((0, 3) : ℕ × ℕ) = 1 from by decide]
  have op10 : sweepOperator q u alphaTwoPath346 ((2, 6) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath346 ((2, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath346 ((2, 6) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 62) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10]

/-- The above-diagonal `(4,6)`-path `(0,3,5,5,6)`. -/
def alphaTwoPath355 : Paths.Heights 2 3 2 := ![0, 3, 5, 5, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,3,5,5,6)`**, 11 events, widths up to `3`. -/
theorem partialSweepWord_alphaTwoPath355 (q u : L) :
    partialSweepWord q u alphaTwoPath355 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((dminus q 2) * ((((q : L) ^ (-1 : ℤ)) • corner q 2)
          * ((u • (1 : Module.End L (Total L))) * ((dminus q 3) * ((dplus q 2) * ((((q : L) ^ (-1
          : ℤ)) • corner q 2) * (((1 : Module.End L (Total L))) * ((corner q 2) * ((dplus q 1) *
          ((dplus q 0) * ((1 : Module.End L (Total L))))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath355 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath355 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath355 ((3, 5) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath355 ((3, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath355 ((3, 5) : ℕ × ℕ) = 2 from by decide]
  have op2 : sweepOperator q u alphaTwoPath355 ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath355 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath355 ((0, 1) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath355 ((0, 1) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath355 ((2, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath355 ((2, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op4 : sweepOperator q u alphaTwoPath355 ((1, 3) : ℕ × ℕ) = dminus q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath355 ((1, 3) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath355 ((1, 3) : ℕ × ℕ) = 3 from by decide]
  have op5 : sweepOperator q u alphaTwoPath355 ((3, 6) : ℕ × ℕ) = dplus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath355 ((3, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath355 ((3, 6) : ℕ × ℕ) = 2 from by decide]
  have op6 : sweepOperator q u alphaTwoPath355 ((0, 2) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath355 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath355 ((0, 2) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath355 ((0, 2) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath355 ((2, 5) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath355 ((2, 5) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath355 ((2, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op8 : sweepOperator q u alphaTwoPath355 ((1, 4) : ℕ × ℕ) = corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath355 ((1, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath355 ((1, 4) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath355 ((1, 4) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op9 : sweepOperator q u alphaTwoPath355 ((0, 3) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath355 ((0, 3) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath355 ((0, 3) : ℕ × ℕ) = 1 from by decide]
  have op10 : sweepOperator q u alphaTwoPath355 ((1, 5) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath355 ((1, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath355 ((1, 5) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 60) (n := 62) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 5)) (m := 62) (n := 71) (r := 71)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 71) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10]

/-- The above-diagonal `(4,6)`-path `(0,3,5,6,6)`. -/
def alphaTwoPath356 : Paths.Heights 2 3 2 := ![0, 3, 5, 6, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,3,5,6,6)`**, 12 events, widths up to `3`. -/
theorem partialSweepWord_alphaTwoPath356 (q u : L) :
    partialSweepWord q u alphaTwoPath356 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * ((corner q 1) *
          ((u • (1 : Module.End L (Total L))) * ((dminus q 2) * (((1 : Module.End L (Total L))) *
          ((((q : L) ^ (-1 : ℤ)) • corner q 2) * ((dminus q 3) * ((((q : L) ^ (-1 : ℤ)) • corner q
          3) * ((dplus q 2) * ((dplus q 1) * ((dplus q 0) * ((1 : Module.End L (Total
          L)))))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath356 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath356 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath356 ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath356 ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op2 : sweepOperator q u alphaTwoPath356 ((0, 1) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath356 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath356 ((0, 1) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath356 ((0, 1) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath356 ((2, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath356 ((2, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op4 : sweepOperator q u alphaTwoPath356 ((1, 3) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath356 ((1, 3) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath356 ((1, 3) : ℕ × ℕ) = 2 from by decide]
  have op5 : sweepOperator q u alphaTwoPath356 ((3, 6) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath356 ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath356 ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op6 : sweepOperator q u alphaTwoPath356 ((0, 2) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath356 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath356 ((0, 2) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath356 ((0, 2) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath356 ((2, 5) : ℕ × ℕ) = dminus q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath356 ((2, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath356 ((2, 5) : ℕ × ℕ) = 3 from by decide]
  have op8 : sweepOperator q u alphaTwoPath356 ((1, 4) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath356 ((1, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath356 ((1, 4) : ℕ × ℕ) = 3 from by decide,
      show sweepRight alphaTwoPath356 ((1, 4) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op9 : sweepOperator q u alphaTwoPath356 ((0, 3) : ℕ × ℕ) = dplus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath356 ((0, 3) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath356 ((0, 3) : ℕ × ℕ) = 2 from by decide]
  have op10 : sweepOperator q u alphaTwoPath356 ((2, 6) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath356 ((2, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath356 ((2, 6) : ℕ × ℕ) = 1 from by decide]
  have op11 : sweepOperator q u alphaTwoPath356 ((1, 5) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath356 ((1, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath356 ((1, 5) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 5)) (m := 62) (n := 71) (r := 71)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 71) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10, op11]

/-- The above-diagonal `(4,6)`-path `(0,3,6,6,6)`. -/
def alphaTwoPath366 : Paths.Heights 2 3 2 := ![0, 3, 6, 6, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,3,6,6,6)`**, 13 events, widths up to `2`. -/
theorem partialSweepWord_alphaTwoPath366 (q u : L) :
    partialSweepWord q u alphaTwoPath366 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * ((corner q 1) *
          ((u • (1 : Module.End L (Total L))) * ((dminus q 2) * (((1 : Module.End L (Total L))) *
          ((((q : L) ^ (-1 : ℤ)) • corner q 2) * ((u • (1 : Module.End L (Total L))) * ((corner q
          2) * ((dplus q 1) * (((1 : Module.End L (Total L))) * ((corner q 1) * ((dplus q 0) * ((1
          : Module.End L (Total L))))))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath366 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath366 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath366 ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath366 ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op2 : sweepOperator q u alphaTwoPath366 ((0, 1) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath366 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath366 ((0, 1) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath366 ((0, 1) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath366 ((2, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath366 ((2, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op4 : sweepOperator q u alphaTwoPath366 ((1, 3) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath366 ((1, 3) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath366 ((1, 3) : ℕ × ℕ) = 2 from by decide]
  have op5 : sweepOperator q u alphaTwoPath366 ((3, 6) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath366 ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath366 ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op6 : sweepOperator q u alphaTwoPath366 ((0, 2) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath366 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath366 ((0, 2) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath366 ((0, 2) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath366 ((2, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath366 ((2, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op8 : sweepOperator q u alphaTwoPath366 ((1, 4) : ℕ × ℕ) = corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath366 ((1, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath366 ((1, 4) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath366 ((1, 4) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op9 : sweepOperator q u alphaTwoPath366 ((0, 3) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath366 ((0, 3) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath366 ((0, 3) : ℕ × ℕ) = 1 from by decide]
  have op10 : sweepOperator q u alphaTwoPath366 ((2, 6) : ℕ × ℕ)
      = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath366 ((2, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath366 ((2, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op11 : sweepOperator q u alphaTwoPath366 ((1, 5) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath366 ((1, 5) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath366 ((1, 5) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath366 ((1, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op12 : sweepOperator q u alphaTwoPath366 ((1, 6) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath366 ((1, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath366 ((1, 6) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 5)) (m := 62) (n := 71) (r := 71)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 71) (n := 80) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 6)) (m := 80) (n := 91) (r := 91)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 91) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10, op11, op12]

/-- The above-diagonal `(4,6)`-path `(0,4,4,5,6)`. -/
def alphaTwoPath445 : Paths.Heights 2 3 2 := ![0, 4, 4, 5, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,4,4,5,6)`**, 11 events, widths up to `3`. -/
theorem partialSweepWord_alphaTwoPath445 (q u : L) :
    partialSweepWord q u alphaTwoPath445 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((dminus q 2) * ((((q : L) ^ (-1 : ℤ)) • corner q 2)
          * ((dminus q 3) * ((u • (1 : Module.End L (Total L))) * ((dplus q 2) * ((((q : L) ^ (-1
          : ℤ)) • corner q 2) * ((dplus q 1) * (((1 : Module.End L (Total L))) * ((corner q 1) *
          ((dplus q 0) * ((1 : Module.End L (Total L))))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath445 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath445 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath445 ((3, 5) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath445 ((3, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath445 ((3, 5) : ℕ × ℕ) = 2 from by decide]
  have op2 : sweepOperator q u alphaTwoPath445 ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath445 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath445 ((0, 1) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath445 ((0, 1) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath445 ((2, 4) : ℕ × ℕ) = dminus q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath445 ((2, 4) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath445 ((2, 4) : ℕ × ℕ) = 3 from by decide]
  have op4 : sweepOperator q u alphaTwoPath445 ((1, 3) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath445 ((1, 3) : ℕ × ℕ) = EventType.E from by decide]
  have op5 : sweepOperator q u alphaTwoPath445 ((3, 6) : ℕ × ℕ) = dplus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath445 ((3, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath445 ((3, 6) : ℕ × ℕ) = 2 from by decide]
  have op6 : sweepOperator q u alphaTwoPath445 ((0, 2) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath445 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath445 ((0, 2) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath445 ((0, 2) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath445 ((2, 5) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath445 ((2, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath445 ((2, 5) : ℕ × ℕ) = 1 from by decide]
  have op8 : sweepOperator q u alphaTwoPath445 ((1, 4) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath445 ((1, 4) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath445 ((1, 4) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op9 : sweepOperator q u alphaTwoPath445 ((0, 3) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath445 ((0, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath445 ((0, 3) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath445 ((0, 3) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op10 : sweepOperator q u alphaTwoPath445 ((0, 4) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath445 ((0, 4) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath445 ((0, 4) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 60) (n := 62) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 62) (n := 71) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 4)) (m := 71) (n := 80) (r := 80)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 80) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10]

/-- The above-diagonal `(4,6)`-path `(0,4,4,6,6)`. -/
def alphaTwoPath446 : Paths.Heights 2 3 2 := ![0, 4, 4, 6, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,4,4,6,6)`**, 12 events, widths up to `2`. -/
theorem partialSweepWord_alphaTwoPath446 (q u : L) :
    partialSweepWord q u alphaTwoPath446 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * ((corner q 1) *
          ((dminus q 2) * ((u • (1 : Module.End L (Total L))) * (((1 : Module.End L (Total L))) *
          ((((q : L) ^ (-1 : ℤ)) • corner q 2) * ((corner q 2) * ((q • (1 : Module.End L (Total
          L))) * ((((q : L) ^ (-1 : ℤ)) • corner q 2) * ((dplus q 1) * ((dplus q 0) * ((1 :
          Module.End L (Total L)))))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath446 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath446 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath446 ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath446 ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op2 : sweepOperator q u alphaTwoPath446 ((0, 1) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath446 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath446 ((0, 1) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath446 ((0, 1) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath446 ((2, 4) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath446 ((2, 4) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath446 ((2, 4) : ℕ × ℕ) = 2 from by decide]
  have op4 : sweepOperator q u alphaTwoPath446 ((1, 3) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath446 ((1, 3) : ℕ × ℕ) = EventType.E from by decide]
  have op5 : sweepOperator q u alphaTwoPath446 ((3, 6) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath446 ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath446 ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op6 : sweepOperator q u alphaTwoPath446 ((0, 2) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath446 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath446 ((0, 2) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath446 ((0, 2) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath446 ((2, 5) : ℕ × ℕ) = corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath446 ((2, 5) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath446 ((2, 5) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath446 ((2, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op8 : sweepOperator q u alphaTwoPath446 ((1, 4) : ℕ × ℕ)
      = q • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath446 ((1, 4) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath446 ((1, 4) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op9 : sweepOperator q u alphaTwoPath446 ((0, 3) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath446 ((0, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath446 ((0, 3) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath446 ((0, 3) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op10 : sweepOperator q u alphaTwoPath446 ((2, 6) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath446 ((2, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath446 ((2, 6) : ℕ × ℕ) = 1 from by decide]
  have op11 : sweepOperator q u alphaTwoPath446 ((0, 4) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath446 ((0, 4) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath446 ((0, 4) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 62) (n := 71) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 4)) (m := 71) (n := 80) (r := 80)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 80) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10, op11]

/-- The above-diagonal `(4,6)`-path `(0,4,5,5,6)`. -/
def alphaTwoPath455 : Paths.Heights 2 3 2 := ![0, 4, 5, 5, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,4,5,5,6)`**, 12 events, widths up to `2`. -/
theorem partialSweepWord_alphaTwoPath455 (q u : L) :
    partialSweepWord q u alphaTwoPath455 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((dminus q 2) * ((((q : L) ^ (-1 : ℤ)) • corner q 2)
          * ((u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * ((dplus q
          1) * ((corner q 1) * (((1 : Module.End L (Total L))) * ((dminus q 2) * ((((q : L) ^ (-1
          : ℤ)) • corner q 2) * ((dplus q 1) * ((dplus q 0) * ((1 : Module.End L (Total
          L)))))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath455 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath455 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath455 ((3, 5) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath455 ((3, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath455 ((3, 5) : ℕ × ℕ) = 2 from by decide]
  have op2 : sweepOperator q u alphaTwoPath455 ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath455 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath455 ((0, 1) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath455 ((0, 1) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath455 ((2, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath455 ((2, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op4 : sweepOperator q u alphaTwoPath455 ((1, 3) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath455 ((1, 3) : ℕ × ℕ) = EventType.E from by decide]
  have op5 : sweepOperator q u alphaTwoPath455 ((3, 6) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath455 ((3, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath455 ((3, 6) : ℕ × ℕ) = 1 from by decide]
  have op6 : sweepOperator q u alphaTwoPath455 ((0, 2) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath455 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath455 ((0, 2) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath455 ((0, 2) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath455 ((2, 5) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath455 ((2, 5) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath455 ((2, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op8 : sweepOperator q u alphaTwoPath455 ((1, 4) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath455 ((1, 4) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath455 ((1, 4) : ℕ × ℕ) = 2 from by decide]
  have op9 : sweepOperator q u alphaTwoPath455 ((0, 3) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath455 ((0, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath455 ((0, 3) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath455 ((0, 3) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op10 : sweepOperator q u alphaTwoPath455 ((1, 5) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath455 ((1, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath455 ((1, 5) : ℕ × ℕ) = 1 from by decide]
  have op11 : sweepOperator q u alphaTwoPath455 ((0, 4) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath455 ((0, 4) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath455 ((0, 4) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 60) (n := 62) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 5)) (m := 62) (n := 71) (r := 71)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 4)) (m := 71) (n := 80) (r := 80)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 80) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10, op11]

/-- The above-diagonal `(4,6)`-path `(0,4,5,6,6)`. -/
def alphaTwoPath456 : Paths.Heights 2 3 2 := ![0, 4, 5, 6, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,4,5,6,6)`**, 13 events, widths up to `3`. -/
theorem partialSweepWord_alphaTwoPath456 (q u : L) :
    partialSweepWord q u alphaTwoPath456 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * ((corner q 1) *
          ((u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * (((1 :
          Module.End L (Total L))) * ((corner q 1) * ((dminus q 2) * ((dminus q 3) * ((((q : L) ^
          (-2 : ℤ)) • corner q 3) * ((dplus q 2) * ((dplus q 1) * ((dplus q 0) * ((1 : Module.End
          L (Total L))))))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath456 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath456 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath456 ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath456 ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op2 : sweepOperator q u alphaTwoPath456 ((0, 1) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath456 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath456 ((0, 1) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath456 ((0, 1) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath456 ((2, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath456 ((2, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op4 : sweepOperator q u alphaTwoPath456 ((1, 3) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath456 ((1, 3) : ℕ × ℕ) = EventType.E from by decide]
  have op5 : sweepOperator q u alphaTwoPath456 ((3, 6) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath456 ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath456 ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op6 : sweepOperator q u alphaTwoPath456 ((0, 2) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath456 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath456 ((0, 2) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath456 ((0, 2) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath456 ((2, 5) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath456 ((2, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath456 ((2, 5) : ℕ × ℕ) = 2 from by decide]
  have op8 : sweepOperator q u alphaTwoPath456 ((1, 4) : ℕ × ℕ) = dminus q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath456 ((1, 4) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath456 ((1, 4) : ℕ × ℕ) = 3 from by decide]
  have op9 : sweepOperator q u alphaTwoPath456 ((0, 3) : ℕ × ℕ)
      = ((q : L) ^ (-2 : ℤ)) • corner q 3 := by
    rw [sweepOperator,
      show eventType alphaTwoPath456 ((0, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath456 ((0, 3) : ℕ × ℕ) = 3 from by decide,
      show sweepRight alphaTwoPath456 ((0, 3) : ℕ × ℕ) = 2 from by decide]
    norm_num
  have op10 : sweepOperator q u alphaTwoPath456 ((2, 6) : ℕ × ℕ) = dplus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath456 ((2, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath456 ((2, 6) : ℕ × ℕ) = 2 from by decide]
  have op11 : sweepOperator q u alphaTwoPath456 ((1, 5) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath456 ((1, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath456 ((1, 5) : ℕ × ℕ) = 1 from by decide]
  have op12 : sweepOperator q u alphaTwoPath456 ((0, 4) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath456 ((0, 4) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath456 ((0, 4) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 5)) (m := 62) (n := 71) (r := 71)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 4)) (m := 71) (n := 80) (r := 80)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 80) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10, op11, op12]

/-- The above-diagonal `(4,6)`-path `(0,4,6,6,6)`. -/
def alphaTwoPath466 : Paths.Heights 2 3 2 := ![0, 4, 6, 6, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,4,6,6,6)`**, 14 events, widths up to `2`. -/
theorem partialSweepWord_alphaTwoPath466 (q u : L) :
    partialSweepWord q u alphaTwoPath466 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * ((corner q 1) *
          ((u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * (((1 :
          Module.End L (Total L))) * ((corner q 1) * ((u • (1 : Module.End L (Total L))) *
          ((dminus q 2) * ((((q : L) ^ (-1 : ℤ)) • corner q 2) * (((1 : Module.End L (Total L))) *
          ((corner q 2) * ((dplus q 1) * ((dplus q 0) * ((1 : Module.End L (Total
          L)))))))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath466 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath466 ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op2 : sweepOperator q u alphaTwoPath466 ((0, 1) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath466 ((0, 1) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath466 ((0, 1) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath466 ((2, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((2, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op4 : sweepOperator q u alphaTwoPath466 ((1, 3) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((1, 3) : ℕ × ℕ) = EventType.E from by decide]
  have op5 : sweepOperator q u alphaTwoPath466 ((3, 6) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath466 ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op6 : sweepOperator q u alphaTwoPath466 ((0, 2) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath466 ((0, 2) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath466 ((0, 2) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath466 ((2, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((2, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op8 : sweepOperator q u alphaTwoPath466 ((1, 4) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((1, 4) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath466 ((1, 4) : ℕ × ℕ) = 2 from by decide]
  have op9 : sweepOperator q u alphaTwoPath466 ((0, 3) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((0, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath466 ((0, 3) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath466 ((0, 3) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op10 : sweepOperator q u alphaTwoPath466 ((2, 6) : ℕ × ℕ)
      = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((2, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath466 ((2, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op11 : sweepOperator q u alphaTwoPath466 ((1, 5) : ℕ × ℕ) = corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((1, 5) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath466 ((1, 5) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath466 ((1, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op12 : sweepOperator q u alphaTwoPath466 ((0, 4) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((0, 4) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath466 ((0, 4) : ℕ × ℕ) = 1 from by decide]
  have op13 : sweepOperator q u alphaTwoPath466 ((1, 6) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath466 ((1, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath466 ((1, 6) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 5)) (m := 62) (n := 71) (r := 71)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 4)) (m := 71) (n := 80) (r := 80)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 6)) (m := 80) (n := 91) (r := 91)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 91) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10, op11, op12, op13]

/-- The above-diagonal `(4,6)`-path `(0,5,5,5,6)`. -/
def alphaTwoPath555 : Paths.Heights 2 3 2 := ![0, 5, 5, 5, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,5,5,5,6)`**, 13 events, widths up to `2`. -/
theorem partialSweepWord_alphaTwoPath555 (q u : L) :
    partialSweepWord q u alphaTwoPath555 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((dminus q 2) * ((((q : L) ^ (-1 : ℤ)) • corner q 2)
          * ((u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * ((dplus q
          1) * ((corner q 1) * (((1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total
          L))) * ((corner q 1) * (((1 : Module.End L (Total L))) * ((corner q 1) * ((dplus q 0) *
          ((1 : Module.End L (Total L))))))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath555 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath555 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath555 ((3, 5) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath555 ((3, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath555 ((3, 5) : ℕ × ℕ) = 2 from by decide]
  have op2 : sweepOperator q u alphaTwoPath555 ((0, 1) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath555 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath555 ((0, 1) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath555 ((0, 1) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath555 ((2, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath555 ((2, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op4 : sweepOperator q u alphaTwoPath555 ((1, 3) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath555 ((1, 3) : ℕ × ℕ) = EventType.E from by decide]
  have op5 : sweepOperator q u alphaTwoPath555 ((3, 6) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath555 ((3, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath555 ((3, 6) : ℕ × ℕ) = 1 from by decide]
  have op6 : sweepOperator q u alphaTwoPath555 ((0, 2) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath555 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath555 ((0, 2) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath555 ((0, 2) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath555 ((2, 5) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath555 ((2, 5) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath555 ((2, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op8 : sweepOperator q u alphaTwoPath555 ((1, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath555 ((1, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op9 : sweepOperator q u alphaTwoPath555 ((0, 3) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath555 ((0, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath555 ((0, 3) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath555 ((0, 3) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op10 : sweepOperator q u alphaTwoPath555 ((1, 5) : ℕ × ℕ)
      = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath555 ((1, 5) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath555 ((1, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op11 : sweepOperator q u alphaTwoPath555 ((0, 4) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath555 ((0, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath555 ((0, 4) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath555 ((0, 4) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op12 : sweepOperator q u alphaTwoPath555 ((0, 5) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath555 ((0, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath555 ((0, 5) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 60) (n := 62) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 5)) (m := 62) (n := 71) (r := 71)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 4)) (m := 71) (n := 80) (r := 80)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 80) (n := 91) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 5)) (m := 91) (n := 100) (r := 100)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 100) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10, op11, op12]

/-- The above-diagonal `(4,6)`-path `(0,5,5,6,6)`. -/
def alphaTwoPath556 : Paths.Heights 2 3 2 := ![0, 5, 5, 6, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,5,5,6,6)`**, 14 events, widths up to `2`. -/
theorem partialSweepWord_alphaTwoPath556 (q u : L) :
    partialSweepWord q u alphaTwoPath556 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * ((corner q 1) *
          ((u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * (((1 :
          Module.End L (Total L))) * ((corner q 1) * ((dminus q 2) * ((u • (1 : Module.End L
          (Total L))) * ((((q : L) ^ (-1 : ℤ)) • corner q 2) * ((dplus q 1) * (((1 : Module.End L
          (Total L))) * ((corner q 1) * ((dplus q 0) * ((1 : Module.End L (Total L))))))))))))))))
      := by
  have op0 : sweepOperator q u alphaTwoPath556 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath556 ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op2 : sweepOperator q u alphaTwoPath556 ((0, 1) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath556 ((0, 1) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath556 ((0, 1) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath556 ((2, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((2, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op4 : sweepOperator q u alphaTwoPath556 ((1, 3) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((1, 3) : ℕ × ℕ) = EventType.E from by decide]
  have op5 : sweepOperator q u alphaTwoPath556 ((3, 6) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath556 ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op6 : sweepOperator q u alphaTwoPath556 ((0, 2) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath556 ((0, 2) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath556 ((0, 2) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath556 ((2, 5) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((2, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath556 ((2, 5) : ℕ × ℕ) = 2 from by decide]
  have op8 : sweepOperator q u alphaTwoPath556 ((1, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((1, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op9 : sweepOperator q u alphaTwoPath556 ((0, 3) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((0, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath556 ((0, 3) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath556 ((0, 3) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op10 : sweepOperator q u alphaTwoPath556 ((2, 6) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((2, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath556 ((2, 6) : ℕ × ℕ) = 1 from by decide]
  have op11 : sweepOperator q u alphaTwoPath556 ((1, 5) : ℕ × ℕ)
      = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((1, 5) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath556 ((1, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op12 : sweepOperator q u alphaTwoPath556 ((0, 4) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((0, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath556 ((0, 4) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath556 ((0, 4) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op13 : sweepOperator q u alphaTwoPath556 ((0, 5) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath556 ((0, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath556 ((0, 5) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 5)) (m := 62) (n := 71) (r := 71)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 4)) (m := 71) (n := 80) (r := 80)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_skip q u (m := 80) (n := 91) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 5)) (m := 91) (n := 100) (r := 100)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 100) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10, op11, op12, op13]

/-- The above-diagonal `(4,6)`-path `(0,5,6,6,6)`. -/
def alphaTwoPath566 : Paths.Heights 2 3 2 := ![0, 5, 6, 6, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,5,6,6,6)`**, 15 events, widths up to `2`. -/
theorem partialSweepWord_alphaTwoPath566 (q u : L) :
    partialSweepWord q u alphaTwoPath566 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * ((corner q 1) *
          ((u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * (((1 :
          Module.End L (Total L))) * ((corner q 1) * ((u • (1 : Module.End L (Total L))) * ((u •
          (1 : Module.End L (Total L))) * ((corner q 1) * (((1 : Module.End L (Total L))) *
          ((dminus q 2) * ((((q : L) ^ (-1 : ℤ)) • corner q 2) * ((dplus q 1) * ((dplus q 0) * ((1
          : Module.End L (Total L))))))))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath566 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath566 ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op2 : sweepOperator q u alphaTwoPath566 ((0, 1) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath566 ((0, 1) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath566 ((0, 1) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath566 ((2, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((2, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op4 : sweepOperator q u alphaTwoPath566 ((1, 3) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((1, 3) : ℕ × ℕ) = EventType.E from by decide]
  have op5 : sweepOperator q u alphaTwoPath566 ((3, 6) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath566 ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op6 : sweepOperator q u alphaTwoPath566 ((0, 2) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath566 ((0, 2) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath566 ((0, 2) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath566 ((2, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((2, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op8 : sweepOperator q u alphaTwoPath566 ((1, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((1, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op9 : sweepOperator q u alphaTwoPath566 ((0, 3) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((0, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath566 ((0, 3) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath566 ((0, 3) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op10 : sweepOperator q u alphaTwoPath566 ((2, 6) : ℕ × ℕ)
      = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((2, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath566 ((2, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op11 : sweepOperator q u alphaTwoPath566 ((1, 5) : ℕ × ℕ) = dminus q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((1, 5) : ℕ × ℕ) = EventType.B from by decide,
      show sweepWidth alphaTwoPath566 ((1, 5) : ℕ × ℕ) = 2 from by decide]
  have op12 : sweepOperator q u alphaTwoPath566 ((0, 4) : ℕ × ℕ)
      = ((q : L) ^ (-1 : ℤ)) • corner q 2 := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((0, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath566 ((0, 4) : ℕ × ℕ) = 2 from by decide,
      show sweepRight alphaTwoPath566 ((0, 4) : ℕ × ℕ) = 1 from by decide]
    norm_num
  have op13 : sweepOperator q u alphaTwoPath566 ((1, 6) : ℕ × ℕ) = dplus q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((1, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath566 ((1, 6) : ℕ × ℕ) = 1 from by decide]
  have op14 : sweepOperator q u alphaTwoPath566 ((0, 5) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath566 ((0, 5) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath566 ((0, 5) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 5)) (m := 62) (n := 71) (r := 71)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 4)) (m := 71) (n := 80) (r := 80)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 6)) (m := 80) (n := 91) (r := 91)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 5)) (m := 91) (n := 100) (r := 100)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 100) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10, op11, op12, op13, op14]

/-- The above-diagonal `(4,6)`-path `(0,6,6,6,6)`. -/
def alphaTwoPath666 : Paths.Heights 2 3 2 := ![0, 6, 6, 6, 6]

set_option maxRecDepth 100000 in
/-- **The sweep word of `(0,6,6,6,6)`**, 16 events, widths up to `1`. -/
theorem partialSweepWord_alphaTwoPath666 (q u : L) :
    partialSweepWord q u alphaTwoPath666 (sepLevel 2 2)
      = (u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * ((corner q 1) *
          ((u • (1 : Module.End L (Total L))) * ((u • (1 : Module.End L (Total L))) * (((1 :
          Module.End L (Total L))) * ((corner q 1) * ((u • (1 : Module.End L (Total L))) * ((u •
          (1 : Module.End L (Total L))) * ((corner q 1) * (((1 : Module.End L (Total L))) * ((u •
          (1 : Module.End L (Total L))) * ((corner q 1) * (((1 : Module.End L (Total L))) *
          ((corner q 1) * ((dplus q 0) * ((1 : Module.End L (Total L)))))))))))))))))) := by
  have op0 : sweepOperator q u alphaTwoPath666 ((1, 2) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((1, 2) : ℕ × ℕ) = EventType.E from by decide]
  have op1 : sweepOperator q u alphaTwoPath666 ((3, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((3, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op2 : sweepOperator q u alphaTwoPath666 ((0, 1) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((0, 1) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath666 ((0, 1) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath666 ((0, 1) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op3 : sweepOperator q u alphaTwoPath666 ((2, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((2, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op4 : sweepOperator q u alphaTwoPath666 ((1, 3) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((1, 3) : ℕ × ℕ) = EventType.E from by decide]
  have op5 : sweepOperator q u alphaTwoPath666 ((3, 6) : ℕ × ℕ) = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((3, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath666 ((3, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op6 : sweepOperator q u alphaTwoPath666 ((0, 2) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((0, 2) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath666 ((0, 2) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath666 ((0, 2) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op7 : sweepOperator q u alphaTwoPath666 ((2, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((2, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op8 : sweepOperator q u alphaTwoPath666 ((1, 4) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((1, 4) : ℕ × ℕ) = EventType.E from by decide]
  have op9 : sweepOperator q u alphaTwoPath666 ((0, 3) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((0, 3) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath666 ((0, 3) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath666 ((0, 3) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op10 : sweepOperator q u alphaTwoPath666 ((2, 6) : ℕ × ℕ)
      = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((2, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath666 ((2, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op11 : sweepOperator q u alphaTwoPath666 ((1, 5) : ℕ × ℕ)
      = u • (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((1, 5) : ℕ × ℕ) = EventType.E from by decide]
  have op12 : sweepOperator q u alphaTwoPath666 ((0, 4) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((0, 4) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath666 ((0, 4) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath666 ((0, 4) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op13 : sweepOperator q u alphaTwoPath666 ((1, 6) : ℕ × ℕ)
      = (1 : Module.End L (Total L)) := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((1, 6) : ℕ × ℕ) = EventType.D from by decide,
      show sweepRight alphaTwoPath666 ((1, 6) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op14 : sweepOperator q u alphaTwoPath666 ((0, 5) : ℕ × ℕ) = corner q 1 := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((0, 5) : ℕ × ℕ) = EventType.C from by decide,
      show sweepWidth alphaTwoPath666 ((0, 5) : ℕ × ℕ) = 1 from by decide,
      show sweepRight alphaTwoPath666 ((0, 5) : ℕ × ℕ) = 0 from by decide]
    norm_num
  have op15 : sweepOperator q u alphaTwoPath666 ((0, 6) : ℕ × ℕ) = dplus q 0 := by
    rw [sweepOperator,
      show eventType alphaTwoPath666 ((0, 6) : ℕ × ℕ) = EventType.A from by decide,
      show sweepWidth alphaTwoPath666 ((0, 6) : ℕ × ℕ) = 0 from by decide]
  rw [sepLevel_two_two,
    partialSweepWord_step_two q u (P := (1, 2)) (m := 4) (n := 11) (r := 11)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 5)) (m := 11) (n := 13) (r := 13)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 1)) (m := 13) (n := 20) (r := 20)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 4)) (m := 20) (n := 22) (r := 22)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 3)) (m := 22) (n := 31) (r := 31)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (3, 6)) (m := 31) (n := 33) (r := 33)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 2)) (m := 33) (n := 40) (r := 40)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 5)) (m := 40) (n := 42) (r := 42)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 4)) (m := 42) (n := 51) (r := 51)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 3)) (m := 51) (n := 60) (r := 60)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (2, 6)) (m := 60) (n := 62) (r := 62)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 5)) (m := 62) (n := 71) (r := 71)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 4)) (m := 71) (n := 80) (r := 80)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (1, 6)) (m := 80) (n := 91) (r := 91)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 5)) (m := 91) (n := 100) (r := 100)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_step_two q u (P := (0, 6)) (m := 100) (n := 120) (r := 120)
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide),
    partialSweepWord_top_two q u (m := 120) (by decide),
    op0, op1, op2, op3, op4, op5, op6, op7, op8, op9, op10, op11, op12, op13, op14, op15]

end Words

end HJO.Mellit

end
