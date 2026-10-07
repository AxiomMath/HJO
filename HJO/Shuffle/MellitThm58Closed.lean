/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidBECut
public import HJO.Shuffle.BraidUnsweptFloor
public import HJO.Shuffle.MellitInductionBaseChange
public import HJO.Shuffle.MellitLhsEquivAbove
public import HJO.Shuffle.SweepComputesClosed
public meta import HJO.Attr

/-! # Mellit's Theorem 5.8 above the floor, and the closed form of the invariant

The three floored clauses of the level recursion are now theorems for the braid candidate
`HJO.Mellit.braidValueColouring`:

* `A`, `C`, `D`: `HJO.Mellit.braidValueColouring_sweepRecursionACDFloor`;
* `B`/`E`: `HJO.Mellit.braidValueColouring_sweepRecursionBEFloor`;
* the unswept clause: `HJO.Mellit.braidValueColouring_sweepRecursionUnsweptFloor`.

This file bundles them as `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, runs the floored
iteration to get `HJO.Mellit.braidValueColouring_eq_dsc_floor` at every admissible level above `aN`,
and discharges the last hypothesis of
`HJO.Mellit.mellitInduction_sweepWitness_of_sweepRecursionBEFloor'`, which is
`HJO.Mellit.mellitInduction_sweepWitness`: the `hind` binder of
`HJO.Mellit.shuffle_of_lhs_and_induction`.

## Main statements

* `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`: the three floored clauses.
* `HJO.Mellit.braidValueColouring_eq_dsc_floor`: the braid candidate is `HJO.Mellit.dsc` at every
  admissible level above `aN`.
* `HJO.Mellit.mellitInduction_sweepWitness`: `MellitInduction` at the sweep witness, for
  algebraically independent `q`, `u` and coprime `1 < a < b`.

## Implementation notes

The floor `aN < η` is the domain of `HJO.Mellit.braidDataOfColouring`; it is part of the statement,
and every consumer reads the invariant at a level separating the diagonal, which is above the floor
by `HJO.Mellit.lt_of_separatesDiagonal`.
-/

@[expose] public section

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

/-- **Above the floor `aN`**: the braid candidate satisfies the
floored `A`/`C`/`D` clause, the floored `B`/`E` clause and the floored unswept clause. -/
@[hjo "lem_braid_sweep_recursions"]
theorem braidValueColouring_sweepRecursionsFloor {L : Type*} [Field L] [Algebra ℚ L] (q u : L)
    {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0)
    {a b N : ℕ} (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : a < b) :
    SweepRecursionACDFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N) ∧
      SweepRecursionBEFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N) ∧
        SweepRecursionUnsweptFloor a b N (braidValueColouring q u hq hq1 hqp hr a b N) :=
  ⟨braidValueColouring_sweepRecursionACDFloor q u hq hq1 hqp hr hu ha hb hN hab,
    braidValueColouring_sweepRecursionBEFloor q u hq hq1 hqp hr hu ha hb hN hab,
    braidValueColouring_sweepRecursionUnsweptFloor q u hq hq1 hqp hr ha hb hN hab⟩

/-- **Mellit's Theorem 5.8 above the floor**: at every admissible level
`η > aN` and every admissible colouring `c` there, the normalised braid value
`r^{inv_fin - inv_ini} π_k(B_{s,v,α}) d_+^k(1)` is the invariant `D_{η,c}`. -/
@[hjo "lem_mellit_thm58"]
theorem braidValueColouring_eq_dsc_floor {L : Type*} [Field L] [Algebra ℚ L] (q u : L)
    {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0)
    {a b N : ℕ} (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : a < b) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hfl : ((a * N : ℕ) : ℚ) < η) {c : Finset (ℕ × ℕ)}
    (hc : IsAdmissibleColouring a b N η c) :
    braidValueColouring q u hq hq1 hqp hr a b N η c = dsc q u a b N η c :=
  braidValueColouring_eq_dsc_of_BEUnsweptFloor q u hq hq1 hqp hr hu ha hb hN hab
    (braidValueColouring_sweepRecursionBEFloor q u hq hq1 hqp hr hu ha hb hN hab)
    (braidValueColouring_sweepRecursionUnsweptFloor q u hq hq1 hqp hr ha hb hN hab) hη hfl hc

/-- **The closed form of the invariant of a composition**, at the sweep
witness, for algebraically independent `q`, `u` and coprime `1 < a < b`. This is the `hind` binder
of `HJO.Mellit.shuffle_of_lhs_and_induction`. -/
@[hjo "lem_mellit_induction"]
theorem mellitInduction_sweepWitness {L : Type*} [Field L] [Algebra ℚ L] :
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
      MellitInduction (sweepWitness q u a b) a b :=
  mellitInduction_sweepWitness_of_sweepRecursionBEFloor'
    fun _ _ _ _ _ hqu _ hr hq hq1 hqp _ _ _ _ ha hlt hN =>
      braidValueColouring_sweepRecursionBEFloor _ _ hq hq1 hqp hr
        (ne_zero_of_algebraicIndependent_snd hqu) (by omega) (by omega) hN hlt

/-- **`HJO.External.Shuffle` from the left-hand side alone.**
`HJO.Mellit.shuffle_of_lhs_and_induction` with its `hind` binder discharged by
`HJO.Mellit.mellitInduction_sweepWitness`: what remains of the shuffle side of this library is
`HJO.Mellit.LhsComputes`, the binder of `HJO.Mellit.lhsRewrite_sweepWitness`. -/
theorem shuffle_of_lhs {L : Type*} [Field L] [Algebra ℚ L]
    (hlhs : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a →
      a < b → LhsComputes q u a b) :
    HJO.External.Shuffle L :=
  shuffle_of_lhs_and_induction hlhs mellitInduction_sweepWitness

end HJO.Mellit

end
