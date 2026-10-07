/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidPositionWindow
public import HJO.Shuffle.MellitAppend
public import HJO.Shuffle.MellitThm58Iteration
public import HJO.CMStructure.MellitBraidRep

/-! # The braid side of Theorem 5.8, written down as a candidate for the level recursion

`HJO.Mellit.braidValueColouring_eq_dsc_floor` reads
`D_{η,c} = q^{(inv_fin − inv_ini)/2} π_k(B_{s,c}) d_+^k(1)`, and
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` is the assertion that the right-hand side
satisfies the clauses of the level recursion that the left-hand side is known to satisfy. Those
clauses are stated here as properties of an abstract candidate
`R : ℚ → Finset (ℕ × ℕ) → Total L` — `HJO.Mellit.SweepRecursionACD`, `HJO.Mellit.SweepRecursionBE`,
`HJO.Mellit.SweepRecursionBOrigin`, `HJO.Mellit.SweepRecursionUnswept` and
`HJO.Mellit.SweepInitialCondition`. `HJO.Mellit.dsc` is one instance (`HJO.Mellit.dsc_recursions`);
this file supplies the other, **the instance built from the braid**, which is the one
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` is about.

## Main results

* `HJO.Mellit.braidValueOfData` — the braid value of special-braid data `(v, α)`:
  `r^{inv_fin − inv_ini} • π_k(B_{θ,v,α}) d_+^k(1)`, with `r` the square root of `q` that
  `HJO.Sweep.braidRepMellit` already carries, so that the half-integer exponent is an
  integer power of `r`.
* `HJO.Mellit.braidValueOfPath` — that value at the special-braid data of a path's colouring,
  `HJO.Mellit.braidDataOfColouring`, at rank `k = #(colouringEast y η)`.
* `HJO.Mellit.braidValueColouring` — the candidate `R`: the same value read off a bare colouring
  through a representative path, exactly as `HJO.Mellit.dsc` reads a bare colouring through
  `HJO.Mellit.traceRep`. That the representative does not matter is
  `HJO.Mellit.braidValueColouring_colouring`, in `HJO/Shuffle/BraidValueUnswept.lean`.
* `HJO.Mellit.braidValueColouring_sweepInitialCondition` — **the braid value satisfies the initial
  condition of the level recursion**, the fifth of the five hypotheses of
  `HJO.Mellit.agreesWithDsc_of_recursions`. Above every rank of the rectangle the colouring is
  empty, so `k = 0`: the braid is the empty word, both inversion counts vanish, and the value is
  `d_+^0(1) = 1`.

## Implementation notes

**The exponent is carried as a power of `r`, not of `q`.** `HJO.Braid.invFin` and
`HJO.Braid.invIni` land in `ℕ`, their difference is taken in `ℤ`, and `r` is raised to it by `zpow`;
`r ≠ 0` follows from `hq : q ≠ 0` through `hr : r * r = q`, so the negative exponents are honest.
This is the same device the append recursion uses for the trains' `q^{∓k/2}`
(`HJO.Sweep.representedBy_braidTrainDown_top`), and it is why no extension of scalars appears: the
square root is a hypothesis, not a construction.

**Genericity.** The definition carries `q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0` and `r * r = q`, which is
exactly the hypothesis list of `HJO.Sweep.braidRepMellit` — `π_k` does not exist without them, so
they are not decoration and cannot be dropped. Nothing further is spent here: the initial condition
is proved at rank `0`, where no letter of `HJO.Sweep.braidRep` is evaluated, so the inverses
`(q−1)^{-1}` and `(qu)^{-1}` inside `HJO.Sweep.corner` and `HJO.Sweep.zop` — and with them the
exclusion `u ≠ 0` that `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` records — do not enter.
They will enter at any clause whose braid carries a `z` letter.

**Off the admissible locus the value is junk rather than `0`.** `HJO.Mellit.colouringRep` falls
back on `default`, so at a colouring no above-diagonal path realizes the candidate takes the braid
value of the junk path, where `HJO.Mellit.dsc` takes `0`. Nothing below reads that branch: all five
clauses evaluate `R` only at `colouring y η` for an above-diagonal `y`, and the initial condition
only at `∅`, which `HJO.Mellit.maxAbovePath` realizes.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, Section 5. -/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-- The braid value of special-braid data. -/
noncomputable def braidValueOfData (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) (a b N : ℕ) {k : ℕ} (v : Fin k → ℚ) (α : Fin k → ℕ) : Total L :=
  r ^ ((invFin (sweepTheta a b N) v α : ℤ) - (invIni (sweepTheta a b N) v α : ℤ)) •
    ((braidRepMellit q u hq hq1 hqp hr k (specialBraid (sweepTheta a b N) v α)
      (dplusIterPiece q k) : pieceSub L k) : Total L)

/-- The braid value of a path at a level. -/
noncomputable def braidValueOfPath (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) {a b N : ℕ} (y : Heights a b N) (η : ℚ) : Total L :=
  braidValueOfData q u hq hq1 hqp hr a b N
    (braidDataOfColouring a b N y η #(colouringEast y η)).1
    (braidDataOfColouring a b N y η #(colouringEast y η)).2

/-- A representative above-diagonal path of a colouring. -/
noncomputable def colouringRep (a b N : ℕ) (η : ℚ) (c : Finset (ℕ × ℕ)) : Heights a b N :=
  if h : ∃ y : Heights a b N, IsAboveDiagonal y ∧ colouring y η = c then h.choose else default

theorem colouringRep_spec {η : ℚ} {c : Finset (ℕ × ℕ)} (h : IsAdmissibleColouring a b N η c) :
    IsAboveDiagonal (colouringRep a b N η c) ∧ colouring (colouringRep a b N η c) η = c := by
  have h' : ∃ y : Heights a b N, IsAboveDiagonal y ∧ colouring y η = c := h
  rw [colouringRep]
  split_ifs
  exact h'.choose_spec

/-- **The braid value of a colouring.** -/
noncomputable def braidValueColouring (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) (a b N : ℕ) (η : ℚ) (c : Finset (ℕ × ℕ)) : Total L :=
  braidValueOfPath q u hq hq1 hqp hr (colouringRep a b N η c) η

/-! ### The value at rank zero -/

/-- At rank `0` the braid value is the vacuum. -/
theorem braidValueOfData_of_isEmpty (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) (a b N : ℕ) (v : Fin 0 → ℚ) (α : Fin 0 → ℕ) :
    braidValueOfData q u hq hq1 hqp hr a b N v α = (1 : Total L) := by
  rw [braidValueOfData, specialBraid_zero, map_one]
  simp only [invIni, invFin, tupleInversions_zero, Nat.cast_zero, sub_zero, zpow_zero,
    one_smul, Module.End.one_apply, coe_dplusIterPiece]
  rfl

theorem card_colouringEast_eq_zero_of_colouring_eq_empty {y : Heights a b N} {η : ℚ}
    (hc : colouring y η = ∅) : #(colouringEast y η) = 0 := by
  rw [Finset.card_eq_zero, ← Finset.subset_empty, ← hc, colouring_eq_union]
  exact Finset.subset_union_right

/-- **The braid value of a path with empty colouring is the vacuum.** -/
theorem braidValueOfPath_of_colouring_eq_empty (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) {y : Heights a b N} {η : ℚ} (hc : colouring y η = ∅) :
    braidValueOfPath q u hq hq1 hqp hr y η = (1 : Total L) := by
  rw [braidValueOfPath]
  rw [card_colouringEast_eq_zero_of_colouring_eq_empty hc]
  exact braidValueOfData_of_isEmpty q u hq hq1 hqp hr a b N _ _

/-- **The braid value satisfies the initial condition of the level recursion.** -/
theorem braidValueColouring_sweepInitialCondition (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) :
    SweepInitialCondition a b N (braidValueColouring q u hq hq1 hqp hr a b N) := by
  intro η _ hlt
  have hadm : IsAdmissibleColouring a b N η (∅ : Finset (ℕ × ℕ)) :=
    ⟨maxAbovePath a b N, isAboveDiagonal_maxAbovePath ha,
      colouring_eq_empty_of_forall_lt hlt _⟩
  exact braidValueOfPath_of_colouring_eq_empty q u hq hq1 hqp hr
    (colouringRep_spec hadm).2

end HJO.Mellit

end
