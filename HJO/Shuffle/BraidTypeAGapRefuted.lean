/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidPositionWindow
public meta import HJO.Attr

/-! # The type-`A` rank squeeze is FALSE

`HJO/Shuffle/BraidPositionWindow.lean` settles what the type-`A` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` actually owes. Its repair route is
`HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le`, whose hypothesis
`w_j \le 1 - \theta` is free at every index
(`HJO.Mellit.braidDataOfColouring_fst_lt_one_sub_sweepTheta`) but whose **gap clause**
`u_m < w_j + \theta` is not; and since a type-`A` event inserts the point of *least* rank
above `\eta_-` (`HJO.Mellit.Isolates.levelPosition_le_braidDataOfColouring_fst`),
`HJO.Mellit.Isolates.not_lt_levelPosition_add_sweepTheta` turns the gap clause into a **squeeze**:

> every crossing that the move sequence advances has rank within `a(aN+1)N` of `rk̂(P)`.

**This file refutes it, at a single explicit configuration, with `a`, `b` coprime and `1 < a < b` —
that is, inside the parameter range the shuffle route's induction hypothesis quantifies over.**

## The witness

`a = 2`, `b = 5`, `N = 1`, so the rectangle is `2 × 5`, `rk̂(x, y) = 6y - 14x`, the rank denominator
and the attack window are both `a(aN+1)N = 6`, the slope is `s = 7/3` and `\theta = 3/10`. Take the
above-diagonal path `HJO.Mellit.gapPath` with heights `(0, 4, 5)`, the type-`A` point
`P = (1, 5)`, of rank `16`, and the isolating admissible pair `\eta_- = 31/2`, `\eta_+ = 33/2` — the
ranks of the rectangle nearest `16` being `12` below and `18` above, so nothing else lies between
the two levels. Then:

* `HJO.Mellit.colouringEast_gapPath`: the crossed east steps at `\eta_-` are `(0, 4)` and `(1, 5)`,
  of ranks `24` and `16`;
* `HJO.Mellit.colouringNorth_gapPath`: the crossed north steps are `(0, 2)` and `(1, 4)`, so the
  colouring has two components;
* `HJO.Mellit.braidData_gap_snd_zero`, `HJO.Mellit.braidData_gap_snd_one`: the multiplicities are
  `\alpha_0 = 2` and `\alpha_1 = 1`, so `HJO.Braid.specialMoveList` **advances the index `0`**,
  once, at its initial position;
* `HJO.Mellit.braidData_gap_fst_zero`, `HJO.Mellit.braidData_gap_fst_one`: the positions are
  `v_0 = 17/40` and `v_1 = 1/40`, and the type-`A` point is the index `1`.

So `v_1 + \theta = 1/40 + 12/40 = 13/40 \le 17/40 = v_0`
(`HJO.Mellit.gap_clause_false_gapPath`): the gap clause fails at the very first move of the
sequence. In ranks, `rk̂(0,4) - rk̂(P) = 24 - 16 = 8 > 6 = a(aN+1)N`
(`HJO.Mellit.pointRank_gap_not_squeezed`).

## What is refuted, and what is not

`HJO.Mellit.not_forall_pointRank_le_add_rankDen` and
`HJO.Mellit.not_forall_braidDataOfColouring_fst_lt_add_sweepTheta` are the two forms of the verdict,
the first in ranks and the second in positions. Both are stated with `1 < a`, `a < b`,
`Nat.Coprime a b` and `aN < \eta_-` among the hypotheses of the refuted universal, so the escape
`b \le a` — under which every position is below `\theta` for free — is not what is being exploited:
`HJO.Mellit.sweepTheta_lt_one_sub_sweepTheta` already showed that escape is closed on the parameters
this project needs, and this file shows the squeeze is false there.

**What is refuted is the squeeze, hence the only stated route to the type-`A` clause.** With
`HJO.Braid.specialBraid_mul_trainDown_one` unavailable
(`HJO.Mellit.not_exists_braidDataOfColouring_fst_eq_one_sub_sweepTheta`) and the gap clause of the
general lemma now false at a genuine type-`A` event, the type-`A` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` has no route left. It is **not** refuted as a
braid identity: the hypotheses of `HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le` are
sufficient, not necessary, and deciding the identity itself at this witness would be a computation
in `HJO.Braid.BraidMonoid`, which nothing here performs.

The counting sketch recorded under `HJO.Mellit.sweepTheta_lt_one_sub_sweepTheta` — "two crossings of
one component in the same column differ by `\theta`" — is **not** what happens here, and is checked
and dropped: a path has one east step per column and the level line meets one north step per column,
so each half of a colouring is column-injective (`HJO.Mellit.columnInjective_colouringEast`). The
failure is between *different* components: two crossed east steps of one colouring whose ranks
differ by more than `a(aN+1)N`.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

/-! ### The witness configuration -/

/-- The witness path: the above-diagonal `(2, 5)`-path with heights `(0, 4, 5)`. Its two east steps
are `(0, 4)` and `(1, 5)`, and it turns north before each of them, so both are type-`A` points. -/
def gapPath : Heights 2 5 1 := ![0, 4, 5]

/-- The lower level of the witness pair. The ranks of the `2 × 5` rectangle nearest `rk̂(1,5) = 16`
are `12` and `18`, so `31/2` and `33/2` isolate it. -/
def gapLo : ℚ := 31 / 2

/-- The upper level of the witness pair. -/
def gapHi : ℚ := 33 / 2

/-- The witness path is above the diagonal: `2ŷ_1 = 8 \ge 5` and `2ŷ_2 = 10 \ge 10`. -/
theorem isAboveDiagonal_gapPath : IsAboveDiagonal gapPath := by decide

/-- The witness point is a type-`A` event: the path arrives at `(1, 5)` going north, `ŷ_1 = 4 < 5`,
and leaves it going east, `ŷ_2 = 5`. -/
theorem eventType_gapPath : eventType gapPath (1, 5) = EventType.A := by decide

/-- The witness point is in the swept region, which is what the type-`A` descent lemmas of
`HJO/Shuffle/BraidLevelDrop.lean` read. -/
theorem mem_sweptRegion_gapPath : ((1, 5) : ℕ × ℕ) ∈ sweptRegion gapPath := by decide

/-- **`rk̂(x, y) = 6y - 14x`** at `a = 2`, `b = 5`, `N = 1`: the above-diagonal rank with
`(aN+1)N = 3` and `b(aN+1)N - 1 = 14`. -/
theorem pointRank_gap (x y : ℕ) : pointRank 2 5 1 (x, y) = 6 * (y : ℤ) - 14 * (x : ℤ) := by
  simp only [pointRank, abovePointRank]
  push_cast
  ring

/-- The attack window is `6`, which is also the rank denominator `a(aN+1)N`: one step up a column
raises the rank by exactly this. -/
theorem attackWindow_gap : attackWindow 2 1 = 6 := by decide

/-- The two east steps of the witness path. -/
theorem eastSteps_gapPath : eastSteps gapPath = {((0 : ℕ), (4 : ℕ)), (1, 5)} := by decide

/-- The five north steps of the witness path. -/
theorem northSteps_gapPath :
    northSteps gapPath = {((0 : ℕ), (0 : ℕ)), (0, 1), (0, 2), (0, 3), (1, 4)} := by decide

/-- **Both east steps are crossed at `\eta_-`**: `rk̂(1,4) = 10 < 31/2 < 24 = rk̂(0,4)` and
`rk̂(2,5) = 2 < 31/2 < 16 = rk̂(1,5)`. -/
theorem colouringEast_gapPath :
    colouringEast gapPath gapLo = {((0 : ℕ), (4 : ℕ)), (1, 5)} := by
  ext P
  rw [colouringEast, Finset.mem_filter, eastSteps_gapPath]
  refine ⟨fun h => h.1, fun hP => ⟨hP, ?_⟩⟩
  fin_cases hP <;> norm_num [gapLo, pointRank_gap]

/-- **Both crossed north steps at `\eta_-`**: `(0, 2)` has `rk̂ = 12 < 31/2 < 18 = 12 + \omega`,
and `(1, 4)` has `rk̂ = 10 < 31/2 < 16 = 10 + \omega`. The other three north steps of the path miss
the window. So the colouring has two components, matching the two crossed east steps. -/
theorem colouringNorth_gapPath :
    colouringNorth gapPath gapLo = {((0 : ℕ), (2 : ℕ)), (1, 4)} := by
  ext P
  rw [colouringNorth, Finset.mem_filter, northSteps_gapPath]
  constructor
  · rintro ⟨hP, h⟩
    revert h
    fin_cases hP <;> norm_num [gapLo, pointRank_gap, attackWindow_gap]
  · intro hP
    refine ⟨?_, ?_⟩
    · fin_cases hP <;> decide
    · fin_cases hP <;> norm_num [gapLo, pointRank_gap, attackWindow_gap]

/-- `\eta_- = 15 + 1/2` is admissible. -/
theorem isAdmissibleLevel_gapLo : IsAdmissibleLevel gapLo := ⟨15, by norm_num [gapLo]⟩

/-- `\eta_+ = 16 + 1/2` is admissible. -/
theorem isAdmissibleLevel_gapHi : IsAdmissibleLevel gapHi := ⟨16, by norm_num [gapHi]⟩

/-- The lower level is positive, which is what the position closed forms read. -/
theorem gapLo_pos : (0 : ℚ) < gapLo := by norm_num [gapLo]

/-- **The witness pair isolates `P = (1, 5)`.** The isolation clause needs no enumeration of the
rectangle: `rk̂` is an integer, and the only integer strictly between `31/2` and `33/2` is `16`,
which is `rk̂(1, 5)`. -/
theorem isolates_gapPath : Isolates 2 5 1 1 5 gapLo gapHi where
  lo := isAdmissibleLevel_gapLo
  hi := isAdmissibleLevel_gapHi
  ltP := by rw [pointRank_gap]; norm_num [gapLo]
  Plt := by rw [pointRank_gap]; norm_num [gapHi]
  iso := by
    rintro ⟨x, y⟩ - - h1 h2
    simp only [pointRank_gap] at h1 h2 ⊢
    rw [gapLo] at h1
    rw [gapHi] at h2
    have k1 : (15 : ℤ) < 6 * (y : ℤ) - 14 * (x : ℤ) := by
      have : ((15 : ℤ) : ℚ) < ((6 * (y : ℤ) - 14 * (x : ℤ) : ℤ) : ℚ) := by
        push_cast at h1 ⊢; linarith
      exact_mod_cast this
    have k2 : 6 * (y : ℤ) - 14 * (x : ℤ) < (17 : ℤ) := by
      have : ((6 * (y : ℤ) - 14 * (x : ℤ) : ℤ) : ℚ) < ((17 : ℤ) : ℚ) := by
        push_cast at h2 ⊢; linarith
      exact_mod_cast this
    push_cast
    omega
  xle := by norm_num
  yle := by norm_num

/-- The colouring has two crossed east steps, hence rank `k = 2`. -/
theorem card_colouringEast_gapPath : #(colouringEast gapPath gapLo) = 2 := by
  rw [colouringEast_gapPath]; decide

/-- The colouring has two crossed north steps, matching `HJO.Mellit.card_colouringEast_gapPath`. -/
theorem card_colouringNorth_gapPath : #(colouringNorth gapPath gapLo) = 2 := by
  rw [colouringNorth_gapPath]; decide

/-- A two-element column-injective set is listed in the order of its two columns. Only
`HJO.Mellit.colStep_mem` and `HJO.Mellit.colStep_fst_lt` are needed: the listing lands in the set
and increases strictly in the column, which at two elements pins both values. -/
private theorem colStep_pair {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) {P Q : ℕ × ℕ}
    (hS : S = {P, Q}) (hcard : #S = 2) (hPQ : P.1 < Q.1) :
    colStep S 0 = P ∧ colStep S 1 = Q := by
  subst hS
  have h0 := colStep_mem (S := ({P, Q} : Finset (ℕ × ℕ))) (i := 0) (by omega)
  have h1 := colStep_mem (S := ({P, Q} : Finset (ℕ × ℕ))) (i := 1) (by omega)
  have hlt := colStep_fst_lt hcol (i := 0) (j := 1) (by omega) (by omega)
  rw [Finset.mem_insert, Finset.mem_singleton] at h0 h1
  rcases h0 with h0 | h0
  · rcases h1 with h1 | h1
    · rw [h0, h1] at hlt; omega
    · exact ⟨h0, h1⟩
  · rcases h1 with h1 | h1 <;> rw [h0, h1] at hlt <;> omega

/-- **The column listing of the crossed east steps**: `w_0 = (0, 4)`, of rank `24`, and
`w_1 = (1, 5) = P`, of rank `16`. -/
theorem colStep_colouringEast_gapPath :
    colStep (colouringEast gapPath gapLo) 0 = (0, 4) ∧
      colStep (colouringEast gapPath gapLo) 1 = (1, 5) :=
  colStep_pair
    (columnInjective_colouringEast (a := 2) (b := 5) (N := 1) (by norm_num) (by norm_num)
      isAdmissibleLevel_gapLo gapPath)
    colouringEast_gapPath card_colouringEast_gapPath (by norm_num)

/-- **The column listing of the crossed north steps**: `u_0 = (0, 2)` and `u_1 = (1, 4)`. The second
is `(X, Y - 1)`, the north step the type-`A` event creates. -/
theorem colStep_colouringNorth_gapPath :
    colStep (colouringNorth gapPath gapLo) 0 = (0, 2) ∧
      colStep (colouringNorth gapPath gapLo) 1 = (1, 4) :=
  colStep_pair
    (columnInjective_colouringNorth (a := 2) (b := 5) (N := 1) (by norm_num) (by norm_num)
      isAdmissibleLevel_gapLo gapPath)
    colouringNorth_gapPath card_colouringNorth_gapPath (by norm_num)

/-! ### The scalars of the witness -/

/-- `s = (b(aN+1)N - 1)/(a(aN+1)N) = 14/6 = 7/3 > 1`, so the witness sits where the escape
`b \le a` of `HJO.Mellit.sweepTheta_lt_one_sub_sweepTheta` is unavailable. -/
theorem sweepSlope_gap : sweepSlope 2 5 1 = 7 / 3 := by rw [sweepSlope]; norm_num

/-- `\theta = 1/(1+s) = 3/10`, so `1 - \theta = 7/10` and the gap window `(0, \theta)` is strictly
narrower than the range `(0, 1-\theta)` the positions occupy. -/
theorem sweepTheta_gap : sweepTheta 2 5 1 = 3 / 10 := by rw [sweepTheta, sweepSlope_gap]; norm_num

/-- `HJO.Mellit.levelPosition` at the witness: a rank `r` sits at `(3/10)(r - 31/2)/6`. -/
theorem levelPosition_gap (r : ℚ) : levelPosition 2 5 1 gapLo r = 3 / 10 * ((r - 31 / 2) / 6) := by
  rw [levelPosition, sweepTheta_gap, gapLo]; norm_num

/-- The level index of the column `0` is `2`: `rk̂(0, 2) = 12 < 31/2 < 18 = rk̂(0, 3)`. -/
theorem levelIndex_gap_zero : levelIndex 2 5 1 gapLo 0 = 2 := by
  rw [levelIndex, gapLo]; norm_num [Int.floor_eq_iff]

/-- The level index of the column `1` is `4`: `rk̂(1, 4) = 10 < 31/2 < 16 = rk̂(1, 5)`. -/
theorem levelIndex_gap_one : levelIndex 2 5 1 gapLo 1 = 4 := by
  rw [levelIndex, gapLo]; norm_num [Int.floor_eq_iff]

/-! ### The braid data of the witness -/

/-- **The position of the component that gets moved is `17/40`**, the normalised rank of its crossed
east step `(0, 4)`: `(3/10)(24 - 31/2)/6 = 17/40`. It is above `\theta = 12/40`, which is exactly
the hypothesis of `HJO.Mellit.Isolates.not_lt_levelPosition_add_sweepTheta`. -/
theorem braidData_gap_fst_zero : (braidDataOfColouring 2 5 1 gapPath gapLo 2).1 0 = 17 / 40 := by
  have hi : ((0 : Fin 2) : ℕ) < #(colouringEast gapPath gapLo) := by
    rw [card_colouringEast_gapPath]; norm_num
  rw [braidDataOfColouring_fst_eq_levelPosition (a := 2) (b := 5) (N := 1) (by norm_num)
      (by norm_num) (by norm_num) isAdmissibleLevel_gapLo gapLo_pos (0 : Fin 2) hi,
    show ((0 : Fin 2) : ℕ) = 0 from rfl, colStep_colouringEast_gapPath.1, pointRank_gap,
    levelPosition_gap]
  norm_num

/-- **The position the type-`A` event inserts is `1/40`**, the normalised rank of `P = (1, 5)`:
`(3/10)(16 - 31/2)/6 = 1/40`. It is the least of the two, as
`HJO.Mellit.Isolates.levelPosition_le_braidDataOfColouring_fst` requires. -/
theorem braidData_gap_fst_one : (braidDataOfColouring 2 5 1 gapPath gapLo 2).1 1 = 1 / 40 := by
  have hi : ((1 : Fin 2) : ℕ) < #(colouringEast gapPath gapLo) := by
    rw [card_colouringEast_gapPath]; norm_num
  rw [braidDataOfColouring_fst_eq_levelPosition (a := 2) (b := 5) (N := 1) (by norm_num)
      (by norm_num) (by norm_num) isAdmissibleLevel_gapLo gapLo_pos (1 : Fin 2) hi,
    show ((1 : Fin 2) : ℕ) = 1 from rfl, colStep_colouringEast_gapPath.2, pointRank_gap,
    levelPosition_gap]
  norm_num

/-- **The multiplicity of the component at `17/40` is `2`**, so `HJO.Braid.specialMoveList` contains
its index once and the move sequence *does* advance it, at its initial position. The count is
`(x(w_0) + y(w_0)) - (x(u_0) + I_{x(u_0)} + 1) + 1 = 4 - 3 + 1 = 2`. -/
theorem braidData_gap_snd_zero : (braidDataOfColouring 2 5 1 gapPath gapLo 2).2 0 = 2 := by
  have hi : (0 : ℕ) < #(colouringEast gapPath gapLo) := by
    rw [card_colouringEast_gapPath]; norm_num
  rw [braidDataOfColouring_snd, show ((0 : Fin 2) : ℕ) = 0 from rfl,
    componentCrossingIndices_eq_Icc, Int.card_Icc,
    componentBotIndex_eq (a := 2) (b := 5) (N := 1) (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_gapLo gapLo_pos gapPath 0,
    componentTopIndex_eq (a := 2) (b := 5) (N := 1) (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_gapLo gapLo_pos hi,
    colStep_colouringEast_gapPath.1, colStep_colouringNorth_gapPath.1]
  norm_num [levelIndex_gap_zero]
  rfl

/-- The multiplicity of the inserted component is `1`, as `HJO.Mellit.totalCrossings_of_eventType_A`
predicts at a type-`A` event: `6 - 6 + 1 = 1`. So the move sequence never advances it. -/
theorem braidData_gap_snd_one : (braidDataOfColouring 2 5 1 gapPath gapLo 2).2 1 = 1 := by
  have hi : (1 : ℕ) < #(colouringEast gapPath gapLo) := by
    rw [card_colouringEast_gapPath]; norm_num
  rw [braidDataOfColouring_snd, show ((1 : Fin 2) : ℕ) = 1 from rfl,
    componentCrossingIndices_eq_Icc, Int.card_Icc,
    componentBotIndex_eq (a := 2) (b := 5) (N := 1) (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_gapLo gapLo_pos gapPath 1,
    componentTopIndex_eq (a := 2) (b := 5) (N := 1) (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_gapLo gapLo_pos hi,
    colStep_colouringEast_gapPath.2, colStep_colouringNorth_gapPath.2]
  norm_num [levelIndex_gap_one]

/-! ### The refutation -/

/-- **THE REFUTATION IN RANKS.** The crossed east step `(0, 4)` that the move sequence advances has
rank `24`, while `rk̂(P) = 16` and `a(aN+1)N = 6`: the rank is `8` above `rk̂(P)`, not within `6` of
it. -/
theorem pointRank_gap_not_squeezed :
    (pointRank 2 5 1 (1, 5) : ℤ) + ((2 * (2 * 1 + 1) * 1 : ℕ) : ℤ) < pointRank 2 5 1 (0, 4) := by
  simp only [pointRank_gap]
  norm_num

/-- **THE REFUTATION IN POSITIONS.** `v_1 + \theta = 1/40 + 12/40 = 13/40 \le 17/40 = v_0`: the gap
clause `u_m < w_j + \theta` of `HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le` is false
at the first move of the sequence, the entry `0` being advanced while still at its initial position
and the inserted entry `1` carrying `w_j`. -/
theorem gap_clause_false_gapPath :
    (braidDataOfColouring 2 5 1 gapPath gapLo 2).1 1 + sweepTheta 2 5 1
      ≤ (braidDataOfColouring 2 5 1 gapPath gapLo 2).1 0 := by
  rw [braidData_gap_fst_zero, braidData_gap_fst_one, sweepTheta_gap]
  norm_num

/-- **THE TYPE-`A` RANK SQUEEZE IS FALSE.** There is no theorem saying that at a type-`A` event
every crossing the move sequence advances has rank within `a(aN+1)N` of `rk̂(P)` — not even with
`1 < a < b`, `a` and `b` coprime and the level above `aN`, which is everything the shuffle route
supplies. `HJO.Mellit.gapPath` at `\eta_- = 31/2` is a counterexample:
`rk̂(0, 4) = 24 > 16 + 6 = rk̂(P) + a(aN+1)N`, and the component at `(0, 4)` has multiplicity `2`.

This was the obligation `HJO.Mellit.Isolates.not_lt_levelPosition_add_sweepTheta` identified as the
real content of the type-`A` clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, after
`HJO.Braid.specialBraid_mul_trainDown_one` had been shown inapplicable. -/
@[hjo "lem_braid_typea_squeeze_refuted"]
theorem not_forall_pointRank_le_add_rankDen :
    ¬ ∀ (a b N X Y k : ℕ) (ηlo ηhi : ℚ) (y : Heights a b N) (i : Fin k),
        1 < a → a < b → 0 < N → Nat.Coprime a b → ((a * N : ℕ) : ℚ) < ηlo →
        Isolates a b N X Y ηlo ηhi → IsAboveDiagonal y →
        ((X, Y) : ℕ × ℕ) ∈ sweptRegion y → eventType y (X, Y) = EventType.A →
        (i : ℕ) < #(colouringEast y ηlo) →
        2 ≤ (braidDataOfColouring a b N y ηlo k).2 i →
        (pointRank a b N (colStep (colouringEast y ηlo) (i : ℕ)) : ℤ)
          ≤ pointRank a b N (X, Y) + ((a * (a * N + 1) * N : ℕ) : ℤ) := by
  intro h
  have hcon := h 2 5 1 1 5 2 gapLo gapHi gapPath 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [gapLo]) isolates_gapPath isAboveDiagonal_gapPath
    mem_sweptRegion_gapPath eventType_gapPath
    (by rw [card_colouringEast_gapPath]; norm_num) (by rw [braidData_gap_snd_zero])
  rw [show ((0 : Fin 2) : ℕ) = 0 from rfl, colStep_colouringEast_gapPath.1] at hcon
  simp only [pointRank_gap] at hcon
  norm_num at hcon

/-- **The same verdict as the gap clause the repair route asks for.** The hypothesis
`u_m < w_j + \theta` of `HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le`, read at the
initial tuple and the index the move sequence advances first, is false at a genuine type-`A` event
with `1 < a < b` and `a`, `b` coprime.

So the type-`A` clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` has **no** route
left: `HJO.Braid.specialBraid_mul_trainDown_one` cannot serve it
(`HJO.Mellit.not_exists_braidDataOfColouring_fst_eq_one_sub_sweepTheta`) and neither can the general
lemma behind it. What is *not* shown is that the clause is false as a braid identity: those
hypotheses are sufficient, not necessary, and settling the identity at this witness would be a
computation in `HJO.Braid.BraidMonoid`. -/
@[hjo "lem_braid_typea_squeeze_refuted"]
theorem not_forall_braidDataOfColouring_fst_lt_add_sweepTheta :
    ¬ ∀ (a b N X Y k : ℕ) (ηlo ηhi : ℚ) (y : Heights a b N) (i j : Fin k),
        1 < a → a < b → 0 < N → Nat.Coprime a b → ((a * N : ℕ) : ℚ) < ηlo →
        Isolates a b N X Y ηlo ηhi → IsAboveDiagonal y →
        ((X, Y) : ℕ × ℕ) ∈ sweptRegion y → eventType y (X, Y) = EventType.A →
        (i : ℕ) < #(colouringEast y ηlo) → (j : ℕ) < #(colouringEast y ηlo) →
        colStep (colouringEast y ηlo) (j : ℕ) = (X, Y) →
        2 ≤ (braidDataOfColouring a b N y ηlo k).2 i →
        (braidDataOfColouring a b N y ηlo k).1 i
          < (braidDataOfColouring a b N y ηlo k).1 j + sweepTheta a b N := by
  intro h
  have hcon := h 2 5 1 1 5 2 gapLo gapHi gapPath 0 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [gapLo]) isolates_gapPath isAboveDiagonal_gapPath
    mem_sweptRegion_gapPath eventType_gapPath
    (by rw [card_colouringEast_gapPath]; norm_num)
    (by rw [card_colouringEast_gapPath]; norm_num)
    (by rw [show ((1 : Fin 2) : ℕ) = 1 from rfl]; exact colStep_colouringEast_gapPath.2)
    (by rw [braidData_gap_snd_zero])
  exact absurd hcon (not_lt.2 gap_clause_false_gapPath)

end HJO.Mellit

end
