/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidCDIndices
public meta import HJO.Attr

/-! # The exponent `a_{P̂}(P)` of the type-`C` and type-`D` rules, read off the data

`HJO.Paths.sweepRight` counts the live north steps strictly right of the event, and the two rules
`HJO.Mellit.sweepOperator` raises `q` to are `q^{-a}Δ` at type `C` and `q^{a}` at type `D`. Every
reduction of those clauses carries that integer along unevaluated — the `hmove` hypothesis of
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_move` reads it off the
path, and nothing anywhere computes it from the special-braid data. This file computes it.

## The answer

`HJO.Mellit.liveSteps_eq_colouringNorth` identifies the live north steps at the event with the
crossed north steps of the **upper** colouring, and `HJO.Mellit.colStep` lists those in strictly
increasing order of column (`HJO.Mellit.colStep_fst_lt`). So if the event sits at the `j`-th listed
component of a rank-`k` colouring, the components strictly to its right are exactly those of index
`j + 1, …, k - 1`, and

`a_{P̂}(P) = k - 1 - j`.

**The same formula at both event types**, and at `D` the index is read off the *east* listing:

* `HJO.Mellit.Isolates.sweepRight_eq_of_colStep_colouringNorth` — the type-`C` shape, where `(X, Y)`
  *is* the `j`-th crossed north step. No event hypothesis at all: the identity of the point with the
  `j`-th north step is what does the work, and that is exactly the `hj` every type-`C` lemma of
  `HJO/Shuffle/BraidCDIndices.lean` already carries.
* `HJO.Mellit.Isolates.sweepRight_eq_of_eventType_D` — the type-`D` shape, where the `j`-th crossed
  **east** step is `(X - 1, Y)`. Two extra ingredients are needed: the interleaving
  `HJO.Mellit.northCol_le_eastCol` and `HJO.Mellit.eastCol_lt_northCol_succ`, and the fact that a
  type-`D` column carries **no** north step at all
  (`HJO.Paths.fst_ne_of_mem_northSteps_of_eventType_D`), which is what upgrades
  `X - 1 < (colStep north (j+1)).1` to `X < (colStep north (j+1)).1`.

## Genericity

Everything here is `ℕ`, `ℤ` and `ℚ`. No field, no `q`, hence no bad parameter and no letter that
degenerates: the `(q-1)⁻¹` of `HJO.Sweep.corner` and the `q^{-a_{P̂}}` of `HJO.Mellit.sweepOperator`
are the consumers' business, not this file's. The subtraction `k - 1 - j` is `ℕ`-subtraction and is
honest, `j < k` being a hypothesis everywhere it appears.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5, for `HJO.Paths.sweepRight`,
`HJO.Mellit.sweepOperator`, `HJO.Paths.liveSteps`, `HJO.Paths.eventType`,
`HJO.Mellit.braidDataOfColouring` and `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`.
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-- **A type-`D` column carries no north step.** At a type-`D` event `Y = ŷ_X` and the outgoing
letter is east, so either the column is outside the rectangle or the path does not climb over it;
either way `HJO.Paths.mem_northSteps_iff`'s interval `[ŷ_X, ŷ_{X+1})` is empty.

This is what separates the type-`D` reading of `HJO.Paths.sweepRight` from the type-`C` one: at `C`
the event column *does* carry a live north step, namely the event itself, and
`HJO.Paths.sweepRight`'s strict inequality excludes it by hand; at `D` there is nothing in that
column to exclude. -/
theorem fst_ne_of_mem_northSteps_of_eventType_D {y : Heights a b N} {X Y : ℕ}
    (hev : eventType y (X, Y) = EventType.D) {P : ℕ × ℕ} (hP : P ∈ northSteps y) : P.1 ≠ X := by
  obtain ⟨hY, hout⟩ := eventType_eq_D_iff.1 hev
  have hY' : Y = ht y X := hY
  have hout' : ¬ (X < a * N ∧ Y < ht y (X + 1)) := hout
  intro hPX
  obtain ⟨h1, h2, h3⟩ := mem_northSteps_iff.1 hP
  rw [hPX] at h1 h2 h3
  exact hout' ⟨h1, by omega⟩

end HJO.Paths

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### Counting the members of a column-injective set to the right of one of them -/

/-- **Strictly right of the `i`-th column there are `#S - 1 - i` members.** The complement of
`HJO.Mellit.card_filter_fst_lt_colStep` and `HJO.Mellit.card_filter_fst_eq_colStep`: of the `#S`
members, `i` lie strictly left of the `i`-th, exactly one lies in its column, and the rest lie
strictly right. -/
theorem card_filter_colStep_fst_lt {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) {i : ℕ}
    (hi : i < #S) : #({P ∈ S | (colStep S i).1 < P.1}) = #S - 1 - i := by
  classical
  have hsucc : #({P ∈ S | P.1 < (colStep S i).1 + 1}) = i + 1 := by
    rw [card_filter_fst_lt_succ, card_filter_fst_lt_colStep hcol hi,
      card_filter_fst_eq_colStep hcol hi]
  have hsplit :=
    Finset.card_filter_add_card_filter_not (s := S)
      (fun P : ℕ × ℕ => (colStep S i).1 < P.1)
  have hneg : {P ∈ S | ¬ ((colStep S i).1 < P.1)} = {P ∈ S | P.1 < (colStep S i).1 + 1} := by
    ext P
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ => by omega
  rw [hneg, hsucc] at hsplit
  omega

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The exponent at a type-`C` event -/

/-- **The live count to the right, from the index of the event in the upper colouring.** If the
event point is the `j`-th crossed north step at the upper level of an isolating pair, then
`a_{P̂}(P) = k - 1 - j` with `k` the rank.

This is the type-`C` shape — `HJO.Mellit.Isolates.mem_colouringNorth_hi_of_eventType_C` says that
at a type-`C` event `(X, Y)` *is* a crossed north step of the upper colouring — but no event
hypothesis is used: the hypothesis `hj` is the whole input, and it is the hypothesis every type-`C`
lemma of `HJO/Shuffle/BraidCDIndices.lean` already carries. -/
theorem sweepRight_eq_of_colStep_colouringNorth (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) {j : ℕ}
    (hjlt : j < #(colouringNorth y ηhi)) (hj : colStep (colouringNorth y ηhi) j = (X, Y)) :
    sweepRight y (X, Y) = #(colouringNorth y ηhi) - 1 - j := by
  rw [sweepRight, liveSteps_eq_colouringNorth hI y]
  have hcol : ColumnInjective (colouringNorth y ηhi) :=
    columnInjective_colouringNorth ha hN hI.hi y
  have h := card_filter_colStep_fst_lt hcol hjlt
  rw [hj] at h
  exact h

/-! ### The exponent at a type-`D` event -/

/-- **The live count to the right at a type-`D` event, from the index of the moved east step.** The
`j`-th crossed east step of the upper colouring is `(X - 1, Y)`, and then `a_{P̂}(P) = k - 1 - j`
— the same formula as at type `C`, with the index read off the east listing rather than the north
one.

The two inequalities that place the north listing against the east one are
`HJO.Mellit.northCol_le_eastCol` (`x(u_i) ≤ x(w_i)`, so the first `j + 1` north steps are weakly
left of `X - 1`, hence strictly left of `X`) and `HJO.Mellit.eastCol_lt_northCol_succ`
(`x(w_j) < x(u_{j+1})`, so the rest are strictly right of `X - 1`). The second gives only
`X - 1 < x(u_{j+1})`, i.e. `X ≤ x(u_{j+1})`; the strictness `HJO.Paths.sweepRight` counts with is
supplied by `HJO.Paths.fst_ne_of_mem_northSteps_of_eventType_D`, no north step of a type-`D` column
existing at all. -/
theorem sweepRight_eq_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηhi : ((a * N : ℕ) : ℚ) < ηhi) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) (hX : 0 < X) {j : ℕ}
    (hjlt : j < #(colouringEast y ηhi)) (hj : colStep (colouringEast y ηhi) j = (X - 1, Y)) :
    sweepRight y (X, Y) = #(colouringEast y ηhi) - 1 - j := by
  classical
  have hcolN : ColumnInjective (colouringNorth y ηhi) :=
    columnInjective_colouringNorth ha hN hI.hi y
  have hk : #(colouringNorth y ηhi) = #(colouringEast y ηhi) :=
    card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy
  have hjN : j < #(colouringNorth y ηhi) := by omega
  -- the `j`-th north step is weakly left of the `j`-th east step, hence strictly left of `X`
  have hleft : (colStep (colouringNorth y ηhi) j).1 < X := by
    have h := northCol_le_eastCol ha hb hN hI.hi hηhi hy hjN
    rw [hj] at h
    omega
  -- the count strictly right of the `j`-th north step is the count strictly right of `X`
  have hfilter : {P ∈ colouringNorth y ηhi | X < P.1}
      = {P ∈ colouringNorth y ηhi | (colStep (colouringNorth y ηhi) j).1 < P.1} := by
    ext P
    simp only [Finset.mem_filter]
    refine and_congr_right fun hP => ?_
    refine ⟨fun h => by omega, fun h => ?_⟩
    -- from `hP` the point is one of the listed north steps; the ones past `j` clear `X - 1`,
    -- and a type-`D` column carries no north step, so they clear `X`
    obtain ⟨i, hi, hie⟩ := exists_colStep hP
    have hij : j < i := by
      by_contra hcon
      have : (colStep (colouringNorth y ηhi) i).1 ≤ (colStep (colouringNorth y ηhi) j).1 :=
        colStep_fst_le hcolN hjN (by omega)
      rw [hie] at this
      omega
    have hgt : X - 1 < P.1 := by
      have h2 := eastCol_lt_northCol_succ ha hb hN hI.hi hηhi hy
        (show j + 1 < #(colouringNorth y ηhi) by omega)
      rw [hj] at h2
      have h3 : (colStep (colouringNorth y ηhi) (j + 1)).1 ≤ P.1 := by
        rw [← hie]
        exact colStep_fst_le hcolN hi (by omega)
      omega
    have hne : P.1 ≠ X :=
      fst_ne_of_mem_northSteps_of_eventType_D hev (Finset.mem_filter.1 hP).1
    omega
  rw [sweepRight, liveSteps_eq_colouringNorth hI y, hfilter,
    card_filter_colStep_fst_lt hcolN hjN, hk]

end Isolates

end HJO.Mellit
