/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitFloorStepGap
public import HJO.Shuffle.BraidTypeAUnconditional
public import HJO.Shuffle.BraidCDLetterVacuum

/-! # Assembling the `A`/`C`/`D` clause for the braid candidate, above the floor

Three per-event clauses of the level recursion are proved for `HJO.Mellit.braidValueColouring`, each
with a level floor `aN < ηlo`:

* type `A`, `HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_A_uncond`, with
  no further hypothesis;
* type `C`, `HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_lt` at
  `a < b` and `..._of_succ` at `ηhi = ηlo + 1`;
* type `D`, `HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_D_of_step`, with
  `ηhi ≤ ηlo + 1` and `u ≠ 0`.

This file assembles them into the `Prop` the iteration reads, and the assembly is
what makes the price of each hypothesis visible.

## The one bridge the assembly needs

`HJO.Mellit.SweepRecursionACD` and its floored variants state the event condition as the disjunction
`ŷ_X < Y ∨ ŷ_{X+1} = Y`, which is what `HJO.Mellit.dsc_lo_eq_sweepOperator_dsc_hi` takes; the braid
clauses are stated at an event *type*. `HJO.Mellit.ht_lt_or_ht_succ_eq_of_eventType` goes from the
type to the disjunction, and the converse is what is needed here:
`HJO.Mellit.eventType_ACD_of_ht_lt_or_ht_succ_eq`, which reads the disjunction as excluding the
types `B` and `E`. Monotonicity of the height function — the adjacent-step clause of
`HJO.Paths.IsAboveDiagonal` — is the whole content: it is what rules out `E`.

## What is discharged, and at what price

`HJO.Mellit.braidValueColouring_sweepRecursionACDFloorStep` is the clause **above the floor and at
consecutive levels**, discharged outright from the three clauses above at `q ∉ {0, 1, -1}` with a
square root, `u ≠ 0`, and `0 < a`, `0 < b`, `0 < N`. It needs **no relation between `a` and `b`**:
at `ηhi = ηlo + 1` the type-`C` window comes from `..._of_succ`
(`HJO/Shuffle/BraidCDWindowFree.lean`) rather than from `a < b`.

`u ≠ 0` is genuinely spent, and only by type `D`. Its letter is a `z`, and `HJO.Sweep.braidRep`
sends `z_1 ↦ (qu)⁻¹ z_1`; at `u = 0` that letter is the zero map and the clause would be **false**,
not vacuous. Types `A` and `C` do not evaluate it, which is why
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_ne_eventType_D` below does not carry
it.

## The clause the iteration wants is the one without the step restriction

`HJO.Mellit.agreesWithDsc_of_recursions_floor` consumes `HJO.Mellit.SweepRecursionACDFloor`, whose
level pairs are unrestricted above the floor, and
`HJO.Mellit.consecutive_levels_unavailable_two_three_one` shows the two are not interchangeable: at
`(a, b, N) = (2, 3, 1)` the admissible above-floor level `9/2` has no consecutive bracketing at all,
and the iteration needs a drop there.

So the residual is exactly one thing, and it is named in Lean:
`HJO.Mellit.SweepRecursionTypeDFloor`, the type-`D` clause above the floor **at an unrestricted
gap**. `HJO.Mellit.braidValueColouring_sweepRecursionACDFloor_of_typeDFloor` discharges the full
floored `A`/`C`/`D` clause from it together with `a < b`, and
`HJO.Mellit.braidValueColouring_eq_dsc_of_typeDFloor` puts that into the floored iteration, leaving
the three obligations `HJO.Mellit.SweepRecursionTypeDFloor`, `HJO.Mellit.SweepRecursionBEFloor` and
`HJO.Mellit.SweepRecursionUnsweptFloor` and nothing else — the initial condition being proved
as `HJO.Mellit.braidValueColouring_sweepInitialCondition`.

`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` has four clauses and six recursions; this file
assembles three per-event clauses of one of them into a `Prop` and names what is left.
-/

@[expose] public section

namespace HJO.Mellit

open Finset ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### From the disjunction to the event type -/

/-- **The event condition of `HJO.Mellit.SweepRecursionACD` says the event is of type `A`, `C` or
`D`.** This is the converse of `HJO.Mellit.ht_lt_or_ht_succ_eq_of_eventType`, and it is what lets
the per-event braid clauses discharge a clause stated at the disjunction.

Type `B` asks `Y = ŷ_X` together with `Y < ŷ_{X+1}`, which both disjuncts refute; type `E` asks
`Y < ŷ_X`, refuted by the first disjunct outright and by the second through monotonicity of the
height function, `ŷ_X ≤ ŷ_{X+1} = Y`. Monotonicity is the adjacent-step clause of
`HJO.Paths.IsAboveDiagonal` and is the only thing the path is used for. -/
theorem eventType_ACD_of_ht_lt_or_ht_succ_eq {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hAB : ht y X < Y ∨ ht y (X + 1) = Y) :
    eventType y (X, Y) = EventType.A ∨ eventType y (X, Y) = EventType.C ∨
      eventType y (X, Y) = EventType.D := by
  have hmono : ht y X ≤ ht y (X + 1) := Paths.ht_mono hy.2.2.1 (Nat.le_succ X)
  have hnE : eventType y (X, Y) ≠ EventType.E := by
    rw [ne_eq, eventType_eq_E_iff]
    simp only
    omega
  have hnB : eventType y (X, Y) ≠ EventType.B := by
    rw [ne_eq, eventType_eq_B_iff]
    simp only
    omega
  cases hev : eventType y (X, Y) with
  | A => exact Or.inl rfl
  | B => exact absurd hev hnB
  | C => exact Or.inr (Or.inl rfl)
  | D => exact Or.inr (Or.inr rfl)
  | E => exact absurd hev hnE

/-! ### The clause above the floor, at consecutive levels -/

/-- **THE `A`/`C`/`D` CLAUSE OF THE LEVEL RECURSION FOR `HJO.Mellit.braidValueColouring`, above the
floor and at consecutive levels.** The three per-event clauses assembled into
`HJO.Mellit.SweepRecursionACDFloorStep`: type `A` from
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_A_uncond`, type `C` from
`..._of_eventType_C_of_succ` — so no relation between `a` and `b` is needed — and type `D` from
`..._of_eventType_D_of_step`, whose `ηhi ≤ ηlo + 1` is the equality read weakly.

`u ≠ 0` is spent by type `D` alone and is not optional: the type-`D` letter is a `z` and
`HJO.Sweep.braidRep` sends `z_1 ↦ (q u)⁻¹ z_1`, so at `u = 0` that letter is the zero map and the
identity is false rather than vacuous.

**This is not the clause `HJO.Mellit.agreesWithDsc_of_recursions_floor` consumes.** That one is
`HJO.Mellit.SweepRecursionACDFloor`, without `ηhi = ηlo + 1`, and
`HJO.Mellit.consecutive_levels_unavailable_two_three_one` shows the restriction bites: the pairs the
iteration builds are in general not consecutive. -/
theorem braidValueColouring_sweepRecursionACDFloorStep (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    SweepRecursionACDFloorStep q u a b N (braidValueColouring q u hq hq1 hqp hr a b N) := by
  intro X Y ηlo ηhi hfl hstep hI y hy hPsw hAB
  rcases eventType_ACD_of_ht_lt_or_ht_succ_eq hy hAB with hev | hev | hev
  · exact hI.braidValueColouring_eq_sweepOperator_of_eventType_A_uncond q u hq hq1 hqp hr ha hb hN
      hfl hy hPsw hev
  · exact hI.braidValueColouring_eq_sweepOperator_of_eventType_C_of_succ q u hq hq1 hqp hr ha hb hN
      hstep hfl hy hev
  · exact hI.braidValueColouring_eq_sweepOperator_of_eventType_D_of_step q u hq hq1 hqp hr hu ha hb
      hN hfl hstep.le hy hev

/-! ### The clause above the floor, away from type `D` -/

namespace Isolates

/-- **The `A`/`C`/`D` identity for `HJO.Mellit.braidValueColouring` at every event but type `D`**,
above the floor, at an **unrestricted** level gap. Types `A` and `C` are what the per-event clauses
give without any bound on the gap — `C` at the price of `a < b`, the relation
`HJO.Mellit.shuffle_of_lhs_and_induction` quantifies over — and neither spends `u ≠ 0`.

This is the exact shape of the residual: the floored clause the iteration wants differs from this
one only in admitting `eventType y (X, Y) = EventType.D`. -/
theorem braidValueColouring_eq_sweepOperator_of_ne_eventType_D (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : a < b) (hI : Isolates a b N X Y ηlo ηhi) (hfl : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y)
    (hAB : ht y X < Y ∨ ht y (X + 1) = Y) (hD : eventType y (X, Y) ≠ EventType.D) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  rcases eventType_ACD_of_ht_lt_or_ht_succ_eq hy hAB with hev | hev | hev
  · exact hI.braidValueColouring_eq_sweepOperator_of_eventType_A_uncond q u hq hq1 hqp hr ha hb hN
      hfl hy hPsw hev
  · exact hI.braidValueColouring_eq_sweepOperator_of_eventType_C_of_lt q u hq hq1 hqp hr ha hb hN
      hab hfl hy hev
  · exact absurd hev hD

end Isolates

/-! ### The residual, named -/

/-- **The type-`D` clause of the level recursion above the floor, at an unrestricted level gap,
asked of a candidate.** The braid clause
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_D_of_step` is this at
`ηhi ≤ ηlo + 1`, and `HJO.Mellit.consecutive_levels_unavailable_two_three_one` says that restriction
excludes level pairs the iteration builds. So this `Prop` is the residual of the `A`/`C`/`D` clause
for the braid candidate, stated so it can be discharged or refuted rather than described.

`HJO.Mellit.dsc` satisfies it (`HJO.Mellit.dsc_sweepRecursionTypeDFloor`), so it is not a
self-contradictory ask. -/
def SweepRecursionTypeDFloor (q u : L) (a b N : ℕ) (R : ℚ → Finset (ℕ × ℕ) → Total L) : Prop :=
  ∀ (X Y : ℕ) (ηlo ηhi : ℚ), ((a * N : ℕ) : ℚ) < ηlo → Isolates a b N X Y ηlo ηhi →
    ∀ y : Heights a b N, IsAboveDiagonal y → (X, Y) ∈ sweptRegion y →
      eventType y (X, Y) = EventType.D →
        R ηlo (colouring y ηlo) = sweepOperator q u y (X, Y) (R ηhi (colouring y ηhi))

/-- **`HJO.Mellit.dsc` satisfies the residual**, from `HJO.Mellit.dsc_lo_eq_sweepOperator_dsc_hi`
through `HJO.Mellit.ht_lt_or_ht_succ_eq_of_eventType`. So the residual is a statement about the
braid side alone, not an impossible demand. -/
theorem dsc_sweepRecursionTypeDFloor (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    SweepRecursionTypeDFloor q u a b N (dsc q u a b N) :=
  fun _ _ _ _ _ hI _ hy hPsw hev => dsc_lo_eq_sweepOperator_dsc_hi q u ha hb hN hI hy hPsw
    (ht_lt_or_ht_succ_eq_of_eventType ha hPsw (Or.inr (Or.inr hev)))

/-- **The floored `A`/`C`/`D` clause for the braid candidate, modulo the type-`D` residual.** With
`a < b` the types `A` and `C` are proved at an unrestricted gap
(`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_ne_eventType_D`), so the whole clause
`HJO.Mellit.SweepRecursionACDFloor` follows from `HJO.Mellit.SweepRecursionTypeDFloor`.

Note what is *not* spent here: `u ≠ 0` sits inside the hypothesis, because only type `D` needs
it. -/
theorem braidValueColouring_sweepRecursionACDFloor_of_typeDFloor (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : a < b)
    (hD : SweepRecursionTypeDFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N)) :
    SweepRecursionACDFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N) := by
  intro X Y ηlo ηhi hfl hI y hy hPsw hAB
  by_cases hev : eventType y (X, Y) = EventType.D
  · exact hD X Y ηlo ηhi hfl hI y hy hPsw hev
  · exact hI.braidValueColouring_eq_sweepOperator_of_ne_eventType_D q u hq hq1 hqp hr ha hb hN hab
      hfl hy hPsw hAB hev

/-! ### What the braid candidate still owes, exactly -/

/-- **The braid candidate agrees with `HJO.Mellit.dsc` above the floor, given three clauses.** The
initial condition is *not* among them: it is proved as
`HJO.Mellit.braidValueColouring_sweepInitialCondition`. So on the floored route the braid side owes
the `A`/`C`/`D` clause, the `BE` clause and the unswept clause, and nothing else. -/
theorem braidValueColouring_eq_dsc_of_recursions_floor (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hACD : SweepRecursionACDFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N))
    (hBE : SweepRecursionBEFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N))
    (hUn : SweepRecursionUnsweptFloor a b N (braidValueColouring q u hq hq1 hqp hr a b N))
    {η : ℚ} (hη : IsAdmissibleLevel η) (hfl : ((a * N : ℕ) : ℚ) < η) {c : Finset (ℕ × ℕ)}
    (hc : IsAdmissibleColouring a b N η c) :
    braidValueColouring q u hq hq1 hqp hr a b N η c = dsc q u a b N η c :=
  eq_dsc_of_recursions_floor q u ha hb hN hACD hBE hUn
    (braidValueColouring_sweepInitialCondition q u hq hq1 hqp hr ha) hη hfl hc

/-- **The braid candidate agrees with `HJO.Mellit.dsc` above the floor, given the three residuals
this file names.** `HJO.Mellit.SweepRecursionTypeDFloor` in place of the whole `A`/`C`/`D` clause —
types `A` and `C` being proved — together with the floored `BE` and unswept clauses, at `a < b`.

This is the precise state of the braid route given the counterexample
`HJO.Mellit.not_braid_recursions_two_three_one`: the level floor is *not* an obstruction to the
iteration (`HJO.Mellit.agreesWithDsc_of_recursions_floor` runs above it and
`HJO.Mellit.eq_dsc_sepLevel_floor` reaches the separating level), and what remains is these three
clauses, of which the type-`D` one is proved only at `ηhi ≤ ηlo + 1` — a restriction
`HJO.Mellit.consecutive_levels_unavailable_two_three_one` shows the iteration's own level pairs do
not meet. -/
theorem braidValueColouring_eq_dsc_of_typeDFloor (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : a < b)
    (hD : SweepRecursionTypeDFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N))
    (hBE : SweepRecursionBEFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N))
    (hUn : SweepRecursionUnsweptFloor a b N (braidValueColouring q u hq hq1 hqp hr a b N))
    {η : ℚ} (hη : IsAdmissibleLevel η) (hfl : ((a * N : ℕ) : ℚ) < η) {c : Finset (ℕ × ℕ)}
    (hc : IsAdmissibleColouring a b N η c) :
    braidValueColouring q u hq hq1 hqp hr a b N η c = dsc q u a b N η c :=
  braidValueColouring_eq_dsc_of_recursions_floor q u hq hq1 hqp hr ha hb hN
    (braidValueColouring_sweepRecursionACDFloor_of_typeDFloor q u hq hq1 hqp hr ha hb hN hab hD)
    hBE hUn hη hfl hc

end HJO.Mellit

end
