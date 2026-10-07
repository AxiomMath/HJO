/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitThm58Floor

/-! # The level drops of the iteration are not consecutive

One might expect, of the type-`C` window hypothesis of `HJO/Shuffle/BraidCDWindowFree.lean`, that
consecutive admissible levels are what the sweep actually presents. Read as a statement about the
pairs of levels `HJO.Mellit.agreesWithDsc_of_recursions` and
`HJO.Mellit.agreesWithDsc_of_recursions_floor` hand to the clauses, **that is false**, and this file
computes a counterexample rather than arguing about it.

## The computation

At `(a, b, N) = (2, 3, 1)` the above-diagonal rank is `rk̂(X, Y) = 6Y - 8X`
(`HJO.Mellit.pointRank_two_three_one`), so **every rank of the rectangle is even**
(`HJO.Mellit.two_dvd_pointRank_two_three_one`). No lattice point has rank `5`. Hence at the
admissible level `9/2`:

* `9/2` is admissible and lies above the floor `aN = 2`, so the floored iteration visits it;
* ranks of the rectangle lie above `9/2` — the point `(1, 3)` has rank `10` — so the base case of
  the iteration does not settle it;
* every bracketing `HJO.Mellit.Isolates 2 3 1 X Y (9/2) ηhi` has `ηhi > 9/2 + 1`
  (`HJO.Mellit.one_add_lt_of_isolates_two_three_one`), because the bracketed rank is an even
  integer above `9/2` and so is at least `6`.

`HJO.Mellit.consecutive_levels_unavailable_two_three_one` is those three facts in one statement.

And `9/2` is exactly the level the iteration reaches first from the worked instance's level
`7/2`: the least rank of the rectangle above `7/2` is `4`
(`HJO.Mellit.first_drop_from_seven_halves_two_three_one`), and the upper level the induction of
`HJO.Mellit.agreesWithDsc_of_recursions_floor` builds is that rank plus `1/2`.

## What this does and does not say

It says that a recursion clause restricted to `ηhi = ηlo + 1` — `HJO.Mellit.SweepRecursionACDFloor`
plus that restriction, i.e. `HJO.Mellit.SweepRecursionACDFloorStep` — is **vacuous at the level
`9/2`** on the `2 × 3` rectangle, so it cannot supply the drop the iteration needs there. That is
the gap between the clause `HJO.Mellit.braidValueColouring` discharges
(`HJO.Mellit.braidValueColouring_sweepRecursionACDFloorStep`) and the clause
`HJO.Mellit.agreesWithDsc_of_recursions_floor` consumes.

It does **not** say the braid route is refuted. Two ways around the gap are left untouched here:
the proved type-`D` clause
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_D_of_step` might hold without
its `ηhi ≤ ηlo + 1`, or the iteration might be rebuilt on consecutive levels with a further clause
covering the drops that cross no rank at all. Neither is decided here, and no theorem below asserts
a falsity.
-/

@[expose] public section

namespace HJO.Mellit

open Finset ParkingFunctions Paths Sweep

/-! ### Every rank of the `2 × 3` rectangle is even -/

/-- **The above-diagonal rank on the `2 × 3` rectangle at `N = 1`.**
`HJO.ParkingFunctions.abovePointRank` reads `(aN+1)N(aY - bX) + X = 3(2Y - 3X) + X = 6Y - 8X`
there. -/
theorem pointRank_two_three_one (X Y : ℕ) : pointRank 2 3 1 (X, Y) = 6 * Y - 8 * X := by
  simp only [pointRank, abovePointRank]
  push_cast
  ring

/-- **Every rank of the `2 × 3` rectangle at `N = 1` is even.** Both coefficients of
`HJO.Mellit.pointRank_two_three_one` are, so no lattice point of that rectangle has an odd rank —
in particular none has rank `5`. -/
theorem two_dvd_pointRank_two_three_one (X Y : ℕ) : (2 : ℤ) ∣ pointRank 2 3 1 (X, Y) := by
  rw [pointRank_two_three_one]
  omega

/-! ### The level `9/2` is visited, and no bracketing of it is consecutive -/

/-- The level `9/2` is admissible: it is `4 + 1/2`. -/
theorem isAdmissibleLevel_nine_halves : IsAdmissibleLevel ((9 : ℚ) / 2) := ⟨4, by norm_num⟩

/-- **The base case does not settle the level `9/2` on the `2 × 3` rectangle.** The point `(1, 3)`
has rank `10`, so `HJO.Mellit.ranksAbove` is nonempty there and the iteration must take a drop. -/
theorem mem_ranksAbove_two_three_one_nine_halves :
    ((1 : ℕ), (3 : ℕ)) ∈ ranksAbove 2 3 1 ((9 : ℚ) / 2) := by
  refine mem_ranksAbove.2 ⟨by norm_num, by norm_num, ?_⟩
  rw [pointRank_two_three_one]
  norm_num

/-- `HJO.Mellit.mem_ranksAbove_two_three_one_nine_halves` in the shape the base case of the
iteration tests. -/
theorem ranksAbove_two_three_one_nine_halves_ne_empty :
    ranksAbove 2 3 1 ((9 : ℚ) / 2) ≠ ∅ :=
  Finset.ne_empty_of_mem mem_ranksAbove_two_three_one_nine_halves

/-- **No bracketing of the level `9/2` on the `2 × 3` rectangle is consecutive.** The bracketed rank
is an integer strictly above `9/2`, hence at least `5`; being even
(`HJO.Mellit.two_dvd_pointRank_two_three_one`) it is at least `6`; and the upper level is above it,
so it exceeds `9/2 + 1 = 11/2`.

This is the obstruction to a recursion clause restricted to `ηhi = ηlo + 1`: at this level such a
clause has no instance at all. -/
theorem one_add_lt_of_isolates_two_three_one {X Y : ℕ} {ηhi : ℚ}
    (hI : Isolates 2 3 1 X Y ((9 : ℚ) / 2) ηhi) : (9 : ℚ) / 2 + 1 < ηhi := by
  have hdvd := two_dvd_pointRank_two_three_one X Y
  have hlt : (9 : ℚ) / 2 < ((pointRank 2 3 1 (X, Y) : ℤ) : ℚ) := hI.ltP
  have h5 : (5 : ℤ) ≤ pointRank 2 3 1 (X, Y) := by
    by_contra hcon
    have h4 : pointRank 2 3 1 (X, Y) ≤ (4 : ℤ) := by omega
    have h4' : ((pointRank 2 3 1 (X, Y) : ℤ) : ℚ) ≤ (4 : ℚ) := by exact_mod_cast h4
    linarith
  have h6 : (6 : ℤ) ≤ pointRank 2 3 1 (X, Y) := by omega
  have h6' : (6 : ℚ) ≤ ((pointRank 2 3 1 (X, Y) : ℤ) : ℚ) := by exact_mod_cast h6
  have := hI.Plt
  linarith

/-- **The three facts about the level `9/2` in one statement.** It is admissible; it is above the
floor `aN = 2` of `HJO.Mellit.agreesWithDsc_of_recursions_floor`, so the floored iteration visits
it; the base case does not settle it; and every bracketing of it has level gap strictly greater than
`1`.

Read together: `HJO.Mellit.SweepRecursionACDFloorStep` is vacuous at this level, and the floored
iteration needs a drop here. -/
theorem consecutive_levels_unavailable_two_three_one :
    IsAdmissibleLevel ((9 : ℚ) / 2) ∧ ((2 * 1 : ℕ) : ℚ) < (9 : ℚ) / 2 ∧
      ranksAbove 2 3 1 ((9 : ℚ) / 2) ≠ ∅ ∧
      ∀ (X Y : ℕ) (ηhi : ℚ), Isolates 2 3 1 X Y ((9 : ℚ) / 2) ηhi → (9 : ℚ) / 2 + 1 < ηhi :=
  ⟨isAdmissibleLevel_nine_halves, by norm_num, ranksAbove_two_three_one_nine_halves_ne_empty,
    fun _ _ _ hI => one_add_lt_of_isolates_two_three_one hI⟩

/-! ### The level `9/2` is where the worked instance's chain goes first -/

/-- **From the level `7/2` the iteration's first drop is to `9/2`.** The least rank of the `2 × 3`
rectangle above `7/2` is `4`: every rank above `7/2` is an even integer and so at least `4`, and the
point `(1, 2)` attains it. The induction of `HJO.Mellit.agreesWithDsc_of_recursions_floor` takes the
least such rank and passes to that rank plus `1/2`, which is `9/2`.

So the obstruction of `HJO.Mellit.consecutive_levels_unavailable_two_three_one` sits on the chain of
the worked instance `HJO.Mellit.eq_dsc_of_recursions_example_floor`, at its second step. -/
theorem first_drop_from_seven_halves_two_three_one :
    (∀ X Y : ℕ, (7 : ℚ) / 2 < ((pointRank 2 3 1 (X, Y) : ℤ) : ℚ) →
        (4 : ℤ) ≤ pointRank 2 3 1 (X, Y)) ∧ pointRank 2 3 1 (1, 2) = 4 := by
  refine ⟨fun X Y hlt => ?_, by rw [pointRank_two_three_one]; norm_num⟩
  have hdvd := two_dvd_pointRank_two_three_one X Y
  have h4 : (4 : ℤ) ≤ pointRank 2 3 1 (X, Y) := by
    by_contra hcon
    have h3 : pointRank 2 3 1 (X, Y) ≤ (3 : ℤ) := by omega
    have h3' : ((pointRank 2 3 1 (X, Y) : ℤ) : ℚ) ≤ (3 : ℚ) := by exact_mod_cast h3
    linarith
  exact h4

end HJO.Mellit

end
