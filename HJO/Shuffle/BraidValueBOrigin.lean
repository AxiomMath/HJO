/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidValueUnswept

/-! # The origin clause of the level recursion, for the braid candidate

`HJO.Mellit.SweepRecursionBOrigin` is the third of the five properties
`HJO.Mellit.agreesWithDsc_of_recursions` asks of a candidate `R`, and its other proved instance is
`HJO.Mellit.dsc` itself (`HJO.Mellit.dsc_sweepRecursionBOrigin`). This file supplies the
instance for the braid candidate `HJO.Mellit.braidValueColouring`, so that clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` is closed.

## The computation, and why it is short

The clause sits at the one lattice point `(0, 0)`, whose rank is `0`
(`HJO.Mellit.pointRank_origin`). So a bracketing pair has `ηlo < 0 < ηhi`, and that is decisive on
both sides of the identity:

* **Below the origin the colouring is empty.** Every point the two halves of
  `HJO.Mellit.colouring` test lies weakly above the diagonal — a north step's foot by
  `HJO.Paths.IsAboveDiagonal` at its own column, and for an east step the point one step to its
  *right*, which is on the path — so its rank is nonnegative
  (`HJO.Mellit.pointRank_nonneg`), and both halves ask that rank to be `< ηlo < 0`. Hence
  `HJO.Mellit.colouring_eq_empty_of_lt_zero`, and the lower value is the vacuum.

* **Above the origin the east half of the colouring is empty**, though the colouring itself is
  not: at `η` just above `0` the level line crosses the north step with foot `(0,0)` and leaves the
  region at the far corner `(aN, bN)`, which is not an east step of the path. Formally, an east step
  `v` of `HJO.Mellit.colouringEast` at `ηhi` needs `rk̂(v + (1,0)) < ηhi`, and `v + (1,0)` is a
  lattice point of the rectangle on the path with abscissa `≥ 1`, so
  `HJO.Mellit.le_pointRank_of_diag` gives `rk̂(v + (1,0)) ≥ 1 > 0 > ηlo`; the isolation clause then
  forces that rank to be `rk̂(0,0) = 0`, a contradiction. This is
  `HJO.Mellit.Isolates.colouringEast_eq_empty_of_origin`.

  `HJO.Mellit.braidValueOfPath` reads its rank off the *east* half, so the upper value is the vacuum
  too, by `HJO.Mellit.braidValueOfPath_of_card_colouringEast_eq_zero`.

What is left is `d_-(1) = 1`, at every index — `HJO.Sweep.dminus_apply_one`. The lowering operator
is a coefficient extraction against `∑_n (-1)^n e_n y_k^{-n}` and on the constant `1` only the
`n = 0` term survives, contributing `e_0 = 1`. So the clause is an identity between two copies of
the vacuum, and `HJO.Mellit.braidValueColouring_origin_collapse` records that reading separately,
because it is the whole content: the assertion is `1 = d_-(1)`.

## The grading mismatch at the origin, recorded

`HJO.Mellit.Isolates.sweepWidth_eq_card_colouringEast` identifies the width the clause's `d_-` is
indexed by with the braid rank — but it costs `aN < ηlo`, and at the origin `ηlo < 0`, so it is
unavailable here and *false* here: the width at `(0,0)` is `1` for every above-diagonal path (the
one live north step is the one with foot `(0,0)`) while the braid rank above the origin is `0`.
`HJO.Mellit.sweepWidth_origin_ne_card_colouringEast_example` exhibits the two numbers at the
`2 × 3` witness. The clause is nevertheless true as stated, because `HJO.Sweep.dminus` is a total
endomorphism and `d_-(1) = 1` whatever index it carries; but nothing here should be read as saying
that `HJO.Mellit.braidValueColouring` is correctly graded below the level `aN`.

## What the three remaining clauses would then force

Below the level `0` every colouring is empty, so the braid candidate is the vacuum there
(`HJO.Mellit.braidValueColouring_eq_one_of_lt_zero`) — and `HJO.Mellit.eq_dsc_of_recursions` reaches
those levels, its induction climbing up from them. With the origin clause and the initial condition
both proved, the other three clauses would therefore buy
`HJO.Mellit.dsc q u a b N η ∅ = 1` at every admissible `η < 0`:
`HJO.Mellit.dsc_eq_one_of_lt_zero_of_braid_recursions`. At such a level
`HJO.Mellit.levelTrace` is the whole swept region, so that value is the full sweep word on the
vacuum summed over traces — the invariant under study. Nothing here proves it is not `1`, so this
is a conditional and not a refutation; but it says where to look, and the place it points at is the
region every proved braid clause excludes by `aN < ηlo`.

## Genericity

Only the four exclusions `HJO.Mellit.braidValueColouring` itself carries — `q ≠ 0`, `q ≠ 1`,
`q + 1 ≠ 0`, `r * r = q`, which are `HJO.Sweep.braidRepMellit`'s own. In particular **no `u ≠ 0`**:
both braid ranks are `0`, so no letter of `HJO.Sweep.braidRep` is evaluated and neither `(q-1)⁻¹`
nor `(qu)⁻¹` enters. Nor are `0 < a`, `0 < b`, `0 < N` needed — the argument is about ranks and the
isolation hypothesis alone.

## What is *not* claimed

`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` covers the whole level recursion, and of its
five properties this file closes one; `HJO.Mellit.SweepRecursionBE`,
`HJO.Mellit.SweepRecursionUnswept` and the assembly of `HJO.Mellit.SweepRecursionACD` are untouched
here.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, Section 5.
-/

@[expose] public section

open Finset

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The lowering operator fixes the vacuum -/

/-- **`d_-(1) = 1`, at every index.** `HJO.Sweep.qshiftNeg` is an algebra map, so it fixes `1`, and
`HJO.Sweep.lowerCoeff_one` — the coefficient extraction fixes the unit, `e_0` being `1` —
finishes. No hypothesis on `q` and none on the index: the index only chooses which variable the
coefficient is extracted in, and `1` involves none of them. -/
theorem dminus_apply_one (q : L) (k : ℕ) : dminus q k (1 : Total L) = 1 := by
  rw [dminus, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_one,
    LinearMap.restrictScalars_apply, lowerCoeff_one]

end HJO.Sweep

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-! ### The rank at and above the origin -/

/-- **The origin has rank `0`.** -/
theorem pointRank_origin (a b N : ℕ) : pointRank a b N ((0 : ℕ), (0 : ℕ)) = 0 := by
  simp [pointRank, ParkingFunctions.abovePointRank]

/-- **The rank of a lattice point weakly above the diagonal is at least its abscissa.** The
sharpening of `HJO.Mellit.pointRank_nonneg` that the origin clause needs: it is the `+ x` of
`rk̂(x,y) = M(ay - bx) + x` read off, and it is what makes a rank forced to be `0` force the
abscissa to be `0`. -/
theorem le_pointRank_of_diag {P : ℕ × ℕ} (h : b * P.1 ≤ a * P.2) :
    (P.1 : ℤ) ≤ pointRank a b N P := by
  have h' : (b : ℤ) * P.1 ≤ (a : ℤ) * P.2 := by exact_mod_cast h
  have hW : (0 : ℤ) ≤ ((a : ℤ) * N + 1) * N := by positivity
  have hp := mul_nonneg hW (by linarith : (0 : ℤ) ≤ (a : ℤ) * P.2 - (b : ℤ) * P.1)
  simp only [pointRank, ParkingFunctions.abovePointRank]
  linarith

/-! ### Below the origin every colouring is empty -/

/-- **Below the level `0` the colouring of an above-diagonal path is empty.** The dual of
`HJO.Mellit.colouring_eq_empty_of_forall_lt`, which empties the colouring above every rank: here the
level is below every rank that either half of `HJO.Mellit.colouring` tests. For a crossed north step
that rank is the step's own foot, weakly above the diagonal; for a crossed east step `v` it is
`v + (1,0)`, the *right* end of the step, which lies on the path and so is weakly above the diagonal
too. Both are therefore nonnegative, and both halves ask them to be `< η`. -/
theorem colouring_eq_empty_of_lt_zero {y : Heights a b N} (hy : IsAboveDiagonal y) {η : ℚ}
    (hη : η < 0) : colouring y η = ∅ := by
  rw [colouring, Finset.union_eq_empty]
  refine ⟨Finset.filter_eq_empty_iff.2 fun {P} hP => ?_,
    Finset.filter_eq_empty_iff.2 fun {P} hP => ?_⟩
  · obtain ⟨h1, h2, -⟩ := mem_northSteps_iff.1 hP
    have hd : b * P.1 ≤ a * P.2 := (hy.2.2.2 P.1 h1.le).trans (Nat.mul_le_mul_left a h2)
    have hnn : (0 : ℚ) ≤ ((pointRank a b N P : ℤ) : ℚ) := by
      exact_mod_cast pointRank_nonneg (N := N) hd
    rintro ⟨hlt, -⟩
    linarith
  · obtain ⟨h1, h2⟩ := mem_eastSteps_iff.1 hP
    have hd : b * (P.1 + 1, P.2).1 ≤ a * (P.1 + 1, P.2).2 := by
      simpa [h2] using hy.2.2.2 (P.1 + 1) (by omega)
    have hnn : (0 : ℚ) ≤ ((pointRank a b N (P.1 + 1, P.2) : ℤ) : ℚ) := by
      exact_mod_cast pointRank_nonneg (N := N) hd
    rintro ⟨hlt, -⟩
    linarith

/-! ### Above the origin the east half of the colouring is empty -/

namespace Isolates

variable {ηlo ηhi : ℚ}

/-- **At a bracketing pair of the origin the upper level crosses no east step.** The point one step
right of a crossed east step lies on the path, so its rank is at least its abscissa
(`HJO.Mellit.le_pointRank_of_diag`), which is at least `1`; it is a point of the rectangle with rank
above `ηlo` and, by the crossing condition, below `ηhi`, so the isolation clause forces its rank to
be `rk̂(0,0) = 0`.

The colouring itself is *not* empty here — the north step with foot `(0,0)` is crossed whenever the
event at the origin is of type `B`, which for an above-diagonal path is always
(`HJO.Mellit.eventType_origin_eq_B`). It is only the east half that is empty, the level line leaving
the region at the far corner `(aN, bN)`, which no east step of the path reaches. -/
theorem colouringEast_eq_empty_of_origin (hI : Isolates a b N 0 0 ηlo ηhi) {y : Heights a b N}
    (hy : IsAboveDiagonal y) : colouringEast y ηhi = ∅ := by
  have h0 : ηlo < 0 := by
    have := hI.ltP
    rw [pointRank_origin] at this
    exact_mod_cast this
  refine Finset.filter_eq_empty_iff.2 fun {P} hP => ?_
  obtain ⟨h1, h2⟩ := mem_eastSteps_iff.1 hP
  rintro ⟨hlt, -⟩
  have hd : b * (P.1 + 1, P.2).1 ≤ a * (P.1 + 1, P.2).2 := by
    simpa [h2] using hy.2.2.2 (P.1 + 1) (by omega)
  have hge : ((P.1 + 1 : ℕ) : ℤ) ≤ pointRank a b N (P.1 + 1, P.2) := le_pointRank_of_diag hd
  have hlo : ηlo < ((pointRank a b N (P.1 + 1, P.2) : ℤ) : ℚ) := by
    have : (0 : ℚ) ≤ ((pointRank a b N (P.1 + 1, P.2) : ℤ) : ℚ) := by
      exact_mod_cast pointRank_nonneg (N := N) hd
    linarith
  have hQ2 : (P.1 + 1, P.2).2 ≤ b * N := by simpa [h2] using ht_le_mul y (P.1 + 1)
  have := hI.iso (P.1 + 1, P.2) (by omega) hQ2 hlo hlt
  rw [pointRank_origin] at this
  omega

end Isolates

/-! ### The braid value at rank zero, read off the east half alone -/

/-- **A path whose crossed east steps are none has the vacuum for its braid value.** The rank of
`HJO.Mellit.braidValueOfPath` is `#(colouringEast y η)`, so at `0` the special-braid data is indexed
by `Fin 0` and `HJO.Mellit.braidValueOfData_of_isEmpty` applies. This is
`HJO.Mellit.braidValueOfPath_of_colouring_eq_empty` with the hypothesis weakened from the whole
colouring to its east half, which is what the origin supplies at the *upper* level. -/
theorem braidValueOfPath_of_card_colouringEast_eq_zero (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) {y : Heights a b N} {η : ℚ}
    (hc : #(colouringEast y η) = 0) :
    braidValueOfPath q u hq hq1 hqp hr y η = (1 : Total L) := by
  rw [braidValueOfPath, hc]
  exact braidValueOfData_of_isEmpty q u hq hq1 hqp hr a b N _ _

/-! ### The origin clause -/

namespace Isolates

variable {ηlo ηhi : ℚ}

/-- **At a bracketing pair of the origin both braid values are the vacuum.** This is the content of
the origin clause for `HJO.Mellit.braidValueColouring`, before the operator is applied: the lower
colouring is empty outright, and the upper one has an empty east half, which is all the braid rank
reads. -/
theorem braidValueColouring_origin_collapse (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (hI : Isolates a b N 0 0 ηlo ηhi) {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo) = (1 : Total L) ∧
      braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi) = (1 : Total L) := by
  have h0 : ηlo < 0 := by
    have := hI.ltP
    rw [pointRank_origin] at this
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · rw [braidValueColouring_colouring q u hq hq1 hqp hr hy]
    exact braidValueOfPath_of_colouring_eq_empty q u hq hq1 hqp hr
      (colouring_eq_empty_of_lt_zero hy h0)
  · rw [braidValueColouring_colouring q u hq hq1 hqp hr hy]
    exact braidValueOfPath_of_card_colouringEast_eq_zero q u hq hq1 hqp hr
      (by rw [hI.colouringEast_eq_empty_of_origin hy]; exact Finset.card_empty)

/-- **The origin clause of the level recursion, for the braid value of a colouring.** Verbatim the
shape of `HJO.Mellit.SweepRecursionBOrigin` at one bracketing pair, and hence at the one point
`HJO.Mellit.SweepRecursionACD` cannot reach and `HJO.Mellit.SweepRecursionBE` is vacuous at.

Both values collapse to the vacuum
(`HJO.Mellit.Isolates.braidValueColouring_origin_collapse`) and `HJO.Sweep.dminus_apply_one` fixes
it, at whatever width the event carries. Nothing beyond the four exclusions
`HJO.Mellit.braidValueColouring` already carries is spent: no `u ≠ 0`, and no positivity of `a`, `b`
or `N`. -/
theorem braidValueColouring_eq_dminus_of_origin (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (hI : Isolates a b N 0 0 ηlo ηhi) {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = dminus q (sweepWidth y ((0 : ℕ), (0 : ℕ)))
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  obtain ⟨hlo, hhi⟩ := hI.braidValueColouring_origin_collapse q u hq hq1 hqp hr hy
  rw [hlo, hhi, dminus_apply_one]

/-- **The origin clause read with the event's own operator**, which is the form the type-`A` and
type-`C` clauses take. The origin is a type-`B` event of every above-diagonal path
(`HJO.Mellit.eventType_origin_eq_B`), and `HJO.Mellit.sweepOperator` at a type-`B` event *is* `d_-`
at the width, so this says the same thing as
`HJO.Mellit.Isolates.braidValueColouring_eq_dminus_of_origin`. It is recorded because it is the
reading in which the index the clause carries is visible, and that index is the one thing the
collapse to the vacuum hides. Here `0 < a`, `0 < b`, `0 < N` are spent — on the event type, not on
the identity. -/
theorem braidValueColouring_eq_sweepOperator_of_origin (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N 0 0 ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y ((0 : ℕ), (0 : ℕ))
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  rw [sweepOperator_of_eventType_B y (eventType_origin_eq_B ha hb hN hy)]
  exact hI.braidValueColouring_eq_dminus_of_origin q u hq hq1 hqp hr hy

end Isolates

/-- **The braid candidate satisfies the origin clause of the level recursion.** The third of the
five properties `HJO.Mellit.agreesWithDsc_of_recursions` asks, now inhabited by the braid side and
not only by `HJO.Mellit.dsc` (`HJO.Mellit.dsc_sweepRecursionBOrigin`). -/
theorem braidValueColouring_sweepRecursionBOrigin (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) :
    SweepRecursionBOrigin q a b N (braidValueColouring q u hq hq1 hqp hr a b N) :=
  fun _ _ hI _ hy => hI.braidValueColouring_eq_dminus_of_origin q u hq hq1 hqp hr hy

/-- **The packaged clause and the pointwise theorem state the same thing.** The `Prop`
`HJO.Mellit.SweepRecursionBOrigin` is discharged by applying the pointwise identity, so nothing can
have been weakened in the packaging — an extra hypothesis or a reversed equation would make this
`rfl` fail to typecheck. -/
example (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q)
    {ηlo ηhi : ℚ} (hI : Isolates a b N 0 0 ηlo ηhi) {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    braidValueColouring_sweepRecursionBOrigin (a := a) (b := b) (N := N) q u hq hq1 hqp hr
        ηlo ηhi hI y hy
      = hI.braidValueColouring_eq_dminus_of_origin q u hq hq1 hqp hr hy := rfl

/-! ### Consistency check -/

/-- **The origin clause is not vacuous, and in range.** The same configuration
`HJO.Mellit.dsc_lo_eq_dminus_dsc_hi_origin_example` checks the `dsc` side at: the `2 × 3` rectangle,
coprime with `1 < a < b`, the above-diagonal path `(0, 2, 3)`, and a bracketing pair of admissible
levels at the origin, which `HJO.Mellit.exists_isolates` produces. Derived through the general
clause, with no ad-hoc route. -/
theorem braidValueColouring_origin_example {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) :
    ∃ ηlo ηhi : ℚ, ηlo < ηhi ∧
      braidValueColouring q u hq hq1 hqp hr 2 3 1 ηlo
          (colouring (![0, 2, 3] : Heights 2 3 1) ηlo)
        = dminus q (sweepWidth (![0, 2, 3] : Heights 2 3 1) ((0 : ℕ), (0 : ℕ)))
            (braidValueColouring q u hq hq1 hqp hr 2 3 1 ηhi
              (colouring (![0, 2, 3] : Heights 2 3 1) ηhi)) := by
  obtain ⟨ηlo, ηhi, hI⟩ := exists_isolates 2 3 1 0 0 (by norm_num) (by norm_num)
  exact ⟨ηlo, ηhi, hI.ltP.trans hI.Plt,
    hI.braidValueColouring_eq_dminus_of_origin q u hq hq1 hqp hr (by decide)⟩

/-! ### What the three remaining clauses would force

The origin clause is one of five, and the region it lives in — the levels below `0` — is where the
braid candidate is most degenerate. The two statements below say what the other three clauses would
have to buy there, and they are recorded because the answer is a fact about `HJO.Mellit.dsc` that
can be tested. -/

/-- **The empty colouring is admissible at every level below `0`**: every above-diagonal path is
coloured `∅` there, so in particular `HJO.Mellit.maxAbovePath` witnesses it. -/
theorem isAdmissibleColouring_empty_of_lt_zero (ha : 0 < a) {η : ℚ} (hη : η < 0) :
    IsAdmissibleColouring a b N η (∅ : Finset (ℕ × ℕ)) :=
  ⟨maxAbovePath a b N, isAboveDiagonal_maxAbovePath ha,
    colouring_eq_empty_of_lt_zero (isAboveDiagonal_maxAbovePath ha) hη⟩

/-- **Below the level `0` the braid candidate is the vacuum, at the only colouring there is.** Every
above-diagonal path is coloured `∅` (`HJO.Mellit.colouring_eq_empty_of_lt_zero`) and the braid value
of an empty colouring is `d_+^0(1) = 1`. Nothing is asked of `q` or `u` beyond the four exclusions
the candidate carries, and nothing of `b` or `N`. -/
theorem braidValueColouring_eq_one_of_lt_zero (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) {η : ℚ} (hη : η < 0) :
    braidValueColouring q u hq hq1 hqp hr a b N η (∅ : Finset (ℕ × ℕ)) = (1 : Total L) :=
  braidValueOfPath_of_colouring_eq_empty q u hq hq1 hqp hr
    (colouringRep_spec (isAdmissibleColouring_empty_of_lt_zero (b := b) (N := N) ha hη)).2

/-- **If the braid candidate satisfies the other three clauses, then `HJO.Mellit.dsc` is the vacuum
at every admissible level below `0`.** This is `HJO.Mellit.eq_dsc_of_recursions` run with the origin
clause and the initial condition supplied — `HJO.Mellit.braidValueColouring_sweepRecursionBOrigin`
and `HJO.Mellit.braidValueColouring_sweepInitialCondition` — against
`HJO.Mellit.braidValueColouring_eq_one_of_lt_zero`.

It is stated as a conditional, and it is **not** a proof that the antecedent fails. But the
consequent is a determinate claim about `HJO.Mellit.dsc` at a level the whole sweep sits above:
there `HJO.Mellit.levelTrace` is the entire swept region, so `HJO.Mellit.dsc` is the full sweep word
on the vacuum, summed over traces — the invariant under study, not `1`. This file proves neither
that it is `1` nor that it is not; `HJO.Mellit.dsc_empty_eq_zero` is about a *separating* level,
where `∅` is inadmissible instead, and settles nothing here. (At `(a, b, N) = (2, 3, 1)`,
`HJO.Mellit.dsc_two_three_one_below_zero_ne_one` of `HJO/Shuffle/DscBelowZeroTwoThree.lean` shows it
is not `1`.)

So: **either `dsc` is the vacuum below every rank as well as above every rank,
or at least one of `HJO.Mellit.SweepRecursionACD`, `HJO.Mellit.SweepRecursionBE`,
`HJO.Mellit.SweepRecursionUnswept` is false for `HJO.Mellit.braidValueColouring` as those `Prop`s
stand.** The place to look is the region the proved braid clauses exclude: the type-`A`, `C` and `D`
clauses are proved only under `aN < ηlo` and the unswept one under `0 < ηlo`, while none of the
three `Prop`s carries any such bound, and below `aN` the braid rank `#(colouringEast · ηhi)`
undercounts the components the width counts — the grading anomaly this file's docstring records at
the origin. -/
theorem dsc_eq_one_of_lt_zero_of_braid_recursions (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hACD : SweepRecursionACD q u a b N (braidValueColouring q u hq hq1 hqp hr a b N))
    (hBE : SweepRecursionBE q u a b N (braidValueColouring q u hq hq1 hqp hr a b N))
    (hUn : SweepRecursionUnswept a b N (braidValueColouring q u hq hq1 hqp hr a b N))
    {η : ℚ} (hη : IsAdmissibleLevel η) (hneg : η < 0) :
    dsc q u a b N η (∅ : Finset (ℕ × ℕ)) = (1 : Total L) := by
  rw [← eq_dsc_of_recursions q u ha hb hN hACD hBE
      (braidValueColouring_sweepRecursionBOrigin q u hq hq1 hqp hr) hUn
      (braidValueColouring_sweepInitialCondition q u hq hq1 hqp hr ha) hη
      (isAdmissibleColouring_empty_of_lt_zero (b := b) (N := N) ha hneg)]
  exact braidValueColouring_eq_one_of_lt_zero q u hq hq1 hqp hr ha hneg

/-- **The width at the origin is `1`, at the witness.** The number the clause's `d_-` is indexed by,
computed. Together with `HJO.Mellit.Isolates.colouringEast_eq_empty_of_origin`, which makes the
braid rank above the origin `0`, this is the grading mismatch the module docstring records: at the
origin `HJO.Mellit.Isolates.sweepWidth_eq_card_colouringEast` is unavailable — it costs `aN < ηlo`
— and false. The clause survives it only because `HJO.Sweep.dminus_apply_one` holds at every
index. -/
theorem sweepWidth_origin_ne_card_colouringEast_example :
    sweepWidth (![0, 2, 3] : Heights 2 3 1) ((0 : ℕ), (0 : ℕ)) = 1 := by decide

end HJO.Mellit

end
