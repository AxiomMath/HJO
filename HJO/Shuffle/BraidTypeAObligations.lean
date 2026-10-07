/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidTypeATransfer
public import HJO.Shuffle.BraidTypeAWitness

/-! # The two obligations of the type-`A` clause, reduced to one technical step — and discharged at
the witness

`HJO.Mellit.braidValueColouring_eq_sweepOperator_of_eventType_A` proves the type-`A` clause for
`HJO.Mellit.braidValueColouring` from two hypotheses about the orbit of
`HJO.Braid.nextCrossing`: `hbot`, that the inserted position stays below every retained stage
position, and `hside`, that the rigid shift `HJO.Mellit.levelDropShift` carries no upper stage
position across the puncture. This file says **what those two obligations actually are**, and
verifies the whole route at the one configuration where it is independently decided.

## Both obligations are consequences of the same missing step

A stage position of a component is `nx_θ^m(v_i)`, which by
`HJO.Mellit.iterate_nextCrossing_fract_crossingAbscissa` is the fractional part of the crossing
abscissa `m` indices below the component's top one. **Suppose that crossing is realised by a lattice
point `Q` of the rectangle** — that is, suppose its fractional part is `levelPosition η (rk̂ Q)`,
which is what `HJO.Mellit.fract_crossingAbscissa_eq_levelPosition` asserts of a crossing sitting
strictly inside the column of `Q`. Then both obligations follow from the bracketing alone:

* `HJO.Mellit.lt_levelPosition_of_ne` — **`hbot` holds unless `Q = (X, Y)`.** A stage crossing of
  the *lower* data lies above the lower level, so `η₋ < rk̂ Q`; if also `rk̂ Q < η₊` then
  `HJO.Mellit.Isolates.iso` and `HJO.Mellit.pointRank_inj_of_le` force `Q = (X, Y)`, and otherwise
  `η₊ ≤ rk̂ Q` while `rk̂(X, Y) < η₊`, so the event point's position is strictly below `Q`'s. And
  `Q = (X, Y)` is the *inserted* component's own single crossing, which no retained component
  shares: distinct components share no crossing index
  (`HJO.Mellit.componentTopIndex_lt_componentBotIndex`) and a crossing's index is `x(Q) + y(Q)`.
* `HJO.Mellit.sameSide_levelDropShift_of_ne` — **`hside` holds unless `Q = (X, Y + 1)`**, the
  lattice point directly *above* the event point. `HJO.Braid.SameSide` fails only if `rk̂ Q` lies in
  the half-open window `[η₋ + ω, η₊ + ω]`, and `ω = HJO.Paths.attackWindow` is exactly the rank
  increment of one north step (`HJO.Mellit.Isolates.cast_pointRank_pred_add_attackWindow`), so that
  window says `rk̂(x(Q), y(Q) − 1)` is bracketed — which by isolation makes that point `(X, Y)`.

So the remaining work on the type-`A` clause is neither algebra nor bracketing: it is the single
step **"the crossing of index `n` of a component is realised by a lattice point of the rectangle"**,
for every `n` between a component's two endpoint indices. The endpoints themselves are realised —
`HJO.Mellit.componentTopIndex_eq` reads the top one off the crossed east step and
`HJO.Mellit.componentBotIndex_eq` reads the bottom one off the crossed north step — and what is
missing is the intermediate ones, whose column is not identified here.

## Consistency check

`HJO.Mellit.gap_typeA_via_transfer` derives the conclusion of
`HJO.Mellit.braidValueColouring_gap_typeA` — the type-`A` clause at `a = 2`, `b = 5`, `N = 1`,
`(X, Y) = (1, 5)`, `η₋ = 31/2`, the exact configuration at which the gap-clause route to the clause
fails (`HJO.Mellit.not_forall_braidDataOfColouring_fst_lt_add_sweepTheta`) — **through the general
theorem**, with both obligations discharged by explicit computation (`HJO.Mellit.hbot_gap`,
`HJO.Mellit.hside_gap`). So the general theorem is not vacuous, its two hypotheses are satisfiable
at a genuine type-`A` event with a mixed component, and the route reproduces the one instance that
is independently known.

The numbers, for the record: `θ = 12/40`, lower data `v = (17/40, 1/40)` and `α = (2, 1)`, upper
data `v = (15/40)` and `α = (2)`, shift `c = 2/40`. The insertion index is `j = 1`
(`HJO.Mellit.typeAIndex_gap`), the inserted entry is `1/40` with multiplicity `1`, the single
retained move carries `17/40` to `5/40` — still above `1/40` — and the shift carries `15/40` and
`3/40` to `17/40` and `5/40`, neither crossing `12/40`.

## What is still not proved

The type-`A` clause in general, and therefore no part of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`.

## References

Declarations involved: `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`,
`HJO.Mellit.Isolates.pointRank_le`, `HJO.Mellit.not_forall_pointRank_le_add_rankDen`,
`HJO.Mellit.fract_crossingAbscissa_eq_levelPosition`, `HJO.Mellit.braidDataOfColouring`,
`HJO.Paths.attackWindow`, `HJO.Paths.abovePointRank_injOn`. Transcribing A. Mellit, *Toric braids
and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {a b N X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The attack window is the denominator of a position -/

/-- **The attack window, over `ℚ`, is the rank denominator `a(aN+1)N`.** So "one attack window above
the level" and "one full turn of the circle" are the same statement, which is what makes the two
reductions below comparisons of ranks. -/
theorem cast_attackWindow_eq (a N : ℕ) :
    ((attackWindow a N : ℕ) : ℚ) = (a : ℚ) * ((a : ℚ) * N + 1) * N := by
  rw [attackWindow]; push_cast; ring

/-- A position is below the puncture exactly when its rank is less than one attack window above the
level. -/
theorem levelPosition_lt_sweepTheta_iff (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η r : ℚ) :
    levelPosition a b N η r < sweepTheta a b N ↔ r < η + ((attackWindow a N : ℕ) : ℚ) := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hθ := (sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN).1
  rw [levelPosition, cast_attackWindow_eq]
  constructor
  · intro h
    have h1 : (r - η) / ((a : ℚ) * ((a : ℚ) * N + 1) * N) < 1 := by
      by_contra hc
      have h2 := mul_le_mul_of_nonneg_left (not_lt.1 hc) hθ.le
      rw [mul_one] at h2
      linarith
    have h3 := (div_lt_one hM).1 h1
    linarith
  · intro h
    have h1 : (r - η) / ((a : ℚ) * ((a : ℚ) * N + 1) * N) < 1 := (div_lt_one hM).2 (by linarith)
    nlinarith [mul_lt_mul_of_pos_left h1 hθ]

/-- A position is above the puncture exactly when its rank exceeds one attack window above the
level. -/
theorem sweepTheta_lt_levelPosition_iff (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η r : ℚ) :
    sweepTheta a b N < levelPosition a b N η r ↔ η + ((attackWindow a N : ℕ) : ℚ) < r := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hθ := (sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN).1
  rw [levelPosition, cast_attackWindow_eq]
  constructor
  · intro h
    have h1 : 1 < (r - η) / ((a : ℚ) * ((a : ℚ) * N + 1) * N) := by
      by_contra hc
      have h2 := mul_le_mul_of_nonneg_left (not_lt.1 hc) hθ.le
      rw [mul_one] at h2
      linarith
    have h3 := (one_lt_div hM).1 h1
    linarith
  · intro h
    have h1 : 1 < (r - η) / ((a : ℚ) * ((a : ℚ) * N + 1) * N) := (one_lt_div hM).2 (by linarith)
    nlinarith [mul_lt_mul_of_pos_left h1 hθ]

/-! ### `hbot`, reduced to the event point itself -/

/-- **The `hbot` obligation, for a stage position realised by a lattice point.** If a position of
the *lower* data is the normalised rank of a lattice point `Q` of the rectangle above the lower
level, and `Q` is not the event point, then the event point's own position is strictly below it.

The proof is the bracketing and nothing else: either `rk̂ Q` is below `η₊`, and then
`HJO.Mellit.Isolates.iso` with `HJO.Mellit.pointRank_inj_of_le` makes `Q` the event point, or
`η₊ ≤ rk̂ Q` while `rk̂(X, Y) < η₊`. So at a type-`A` event the *only* lattice point that can tie
the inserted position is the event point, whose crossing belongs to the inserted component alone. -/
theorem lt_levelPosition_of_ne (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {x yy : ℕ} (hx : x ≤ a * N) (hyy : yy ≤ b * N)
    (hgt : ηlo < ((pointRank a b N (x, yy) : ℤ) : ℚ)) (hne : (x, yy) ≠ (X, Y)) :
    levelPosition a b N ηlo ((pointRank a b N (X, Y) : ℤ) : ℚ)
      < levelPosition a b N ηlo ((pointRank a b N (x, yy) : ℤ) : ℚ) := by
  refine levelPosition_lt_levelPosition ha hb hN ηlo (hI.Plt.trans_le ?_)
  by_contra hc
  exact hne (pointRank_inj_of_le ha hN hx hI.xle (hI.iso (x, yy) hx hyy hgt (not_le.1 hc)))

/-! ### `hside`, reduced to the lattice point above the event point -/

/-- **The `hside` obligation, for a stage position realised by a lattice point.** If a position of
the *upper* data is the normalised rank of a lattice point `(x, y)` with `y ≥ 1` whose downward
neighbour `(x, y - 1)` lies in the rectangle, and `(x, y) ≠ (X, Y + 1)`, then the rigid shift
`HJO.Mellit.levelDropShift` does not carry that position across the puncture.

`HJO.Braid.SameSide` can only fail inside the window `η₋ + ω ≤ rk̂(x, y) ≤ η₊ + ω`; since
`ω = HJO.Paths.attackWindow` is the rank increment of one north step, that window says exactly that
`rk̂(x, y - 1)` is bracketed by the two levels — and the two levels are not integers, so it is
bracketed strictly, and `HJO.Mellit.Isolates.iso` makes `(x, y - 1)` the event point. -/
theorem sameSide_levelDropShift_of_ne (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {x yy : ℕ} (hx : x ≤ a * N) (hyb : yy ≤ b * N + 1)
    (hy0 : 0 < yy) (hne : (x, yy) ≠ (X, Y + 1)) :
    SameSide (sweepTheta a b N) (levelDropShift a b N ηlo ηhi)
      (levelPosition a b N ηhi ((pointRank a b N (x, yy) : ℤ) : ℚ)) := by
  have hlolt : ηlo < ηhi := hI.ltP.trans hI.Plt
  have hshift : levelPosition a b N ηhi ((pointRank a b N (x, yy) : ℤ) : ℚ)
      + levelDropShift a b N ηlo ηhi
      = levelPosition a b N ηlo ((pointRank a b N (x, yy) : ℤ) : ℚ) :=
    (levelPosition_eq_add_levelDropShift ηlo ηhi _).symm
  have hpred : ((pointRank a b N (x, yy - 1) : ℤ) : ℚ)
      = ((pointRank a b N (x, yy) : ℤ) : ℚ) - ((attackWindow a N : ℕ) : ℚ) := by
    have h := Isolates.cast_pointRank_pred_add_attackWindow a b N x hy0
    linarith
  have hbad : ¬ (ηlo ≤ ((pointRank a b N (x, yy) : ℤ) : ℚ) - ((attackWindow a N : ℕ) : ℚ)
      ∧ ((pointRank a b N (x, yy) : ℤ) : ℚ) - ((attackWindow a N : ℕ) : ℚ) ≤ ηhi) := by
    rintro ⟨h1, h2⟩
    rw [← hpred] at h1 h2
    have h1' : ηlo < ((pointRank a b N (x, yy - 1) : ℤ) : ℚ) :=
      lt_of_le_of_ne h1 (intCast_ne_of_isAdmissibleLevel hI.lo _).symm
    have h2' : ((pointRank a b N (x, yy - 1) : ℤ) : ℚ) < ηhi :=
      lt_of_le_of_ne h2 (intCast_ne_of_isAdmissibleLevel hI.hi _)
    have hpt := pointRank_inj_of_le ha hN (P := (x, yy - 1)) (Q := (X, Y)) hx hI.xle
      (hI.iso (x, yy - 1) hx (by omega) h1' h2')
    have h3 : x = X := congrArg Prod.fst hpt
    have h4 : yy - 1 = Y := congrArg Prod.snd hpt
    exact hne (by subst h3; rw [show yy = Y + 1 by omega])
  have hlo1 := levelPosition_lt_sweepTheta_iff (a := a) (b := b) (N := N) ha hb hN ηlo
    ((pointRank a b N (x, yy) : ℤ) : ℚ)
  have hhi1 := levelPosition_lt_sweepTheta_iff (a := a) (b := b) (N := N) ha hb hN ηhi
    ((pointRank a b N (x, yy) : ℤ) : ℚ)
  have hlo2 := sweepTheta_lt_levelPosition_iff (a := a) (b := b) (N := N) ha hb hN ηlo
    ((pointRank a b N (x, yy) : ℤ) : ℚ)
  have hhi2 := sweepTheta_lt_levelPosition_iff (a := a) (b := b) (N := N) ha hb hN ηhi
    ((pointRank a b N (x, yy) : ℤ) : ℚ)
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hshift, hlo1]
    rw [hhi1] at h
    by_contra hc
    exact hbad ⟨by linarith, by linarith⟩
  · rw [hshift, hlo1] at h
    rw [hhi1]
    linarith
  · rw [hshift, hlo2]
    rw [hhi2] at h
    linarith
  · rw [hshift, hlo2] at h
    rw [hhi2]
    by_contra hc
    exact hbad ⟨by linarith, by linarith⟩

/-! ### The two obligations at the witness -/

/-- The insertion index at the witness is `1`: the one crossed east step above the drop, `(0, 4)`,
lies left of the event's column `X = 1`. -/
theorem typeAIndex_gap : typeAIndex gapPath gapHi 1 = 1 := by
  rw [typeAIndex, colouringEast_gapPath_hi]
  decide

/-- The rigid shift at the witness is `1/20 = 2/40`. -/
theorem levelDropShift_gap : levelDropShift 2 5 1 gapLo gapHi = 1 / 20 := by
  rw [levelDropShift, sweepTheta_gap, gapLo, gapHi]
  norm_num

/-- At the witness the insertion index is the *last* one, so the single retained entry keeps index
`0`. -/
theorem succAbove_gap : (1 : Fin 2).succAbove (0 : Fin 1) = 0 := by decide

/-- **`hbot` at the witness.** The inserted entry is `1/40`; the retained entry starts at `17/40`
and its single move carries it to `5/40`, both above `1/40`. -/
theorem hbot_gap (t : Fin 1) (m : ℕ)
    (hm : m ≤ (braidDataOfColouring 2 5 1 gapPath gapHi 1).2 t - 1) :
    (braidDataOfColouring 2 5 1 gapPath gapLo 2).1 1
      < (nextCrossing (sweepTheta 2 5 1))^[m]
          ((braidDataOfColouring 2 5 1 gapPath gapLo 2).1 ((1 : Fin 2).succAbove t)) := by
  have ht0 : t = 0 := Subsingleton.elim _ _
  subst ht0
  rw [braidData_gap_hi_snd] at hm
  simp only [Matrix.cons_val_fin_one] at hm
  rw [braidData_gap_lo_fst, succAbove_gap, sweepTheta_gap]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  interval_cases m
  · norm_num
  · rw [Function.iterate_one, nextCrossing]
    norm_num

/-- **`hside` at the witness.** The upper entry is `15/40` and its single move carries it to `3/40`;
the shift `2/40` carries those to `17/40` and `5/40`, and neither pair straddles `θ = 12/40`. -/
theorem hside_gap (t : Fin 1) (m : ℕ)
    (hm : m ≤ (braidDataOfColouring 2 5 1 gapPath gapHi 1).2 t - 1) :
    SameSide (sweepTheta 2 5 1) (levelDropShift 2 5 1 gapLo gapHi)
      ((nextCrossing (sweepTheta 2 5 1))^[m]
        ((braidDataOfColouring 2 5 1 gapPath gapHi 1).1 t)) := by
  have ht0 : t = 0 := Subsingleton.elim _ _
  subst ht0
  rw [braidData_gap_hi_snd] at hm
  simp only [Matrix.cons_val_fin_one] at hm
  rw [braidData_gap_hi_fst, levelDropShift_gap, sweepTheta_gap]
  simp only [Matrix.cons_val_fin_one]
  interval_cases m
  · norm_num [SameSide]
  · rw [Function.iterate_one, nextCrossing]
    norm_num [SameSide]

/-! ### Consistency check -/

/-- **The decided instance of the type-`A` clause, derived through the general route.** This is
verbatim the statement of `HJO.Mellit.braidValueColouring_gap_typeA`, whose own proof is an explicit
computation in `HJO.Braid.BraidMonoid`; here it comes out of
`HJO.Mellit.braidValueColouring_eq_sweepOperator_of_eventType_A` with every hypothesis discharged —
the geometry from `HJO/Shuffle/BraidTypeADictionary.lean`, and the two orbit obligations from
`HJO.Mellit.hbot_gap` and `HJO.Mellit.hside_gap`.

Two things this settles. The general theorem is **not vacuous**: its hypotheses are satisfiable at a
genuine type-`A` event whose component is mixed, so carries a `z` letter, and at which the
gap-clause route to the clause fails
(`HJO.Mellit.not_forall_braidDataOfColouring_fst_lt_add_sweepTheta`). And the dictionary is **not
wrong**: an error in the insertion index, the multiplicities, the shift or the width would make this
derivation fail, since the right-hand side is pinned independently. -/
theorem gap_typeA_via_transfer {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) :
    braidValueColouring q u hq hq1 hqp hr 2 5 1 gapLo (colouring gapPath gapLo)
      = sweepOperator q u gapPath (1, 5)
          (braidValueColouring q u hq hq1 hqp hr 2 5 1 gapHi (colouring gapPath gapHi)) :=
  braidValueColouring_eq_sweepOperator_of_eventType_A q u hq hq1 hqp hr (by norm_num) (by norm_num)
    (by norm_num) isolates_gapPath (by norm_num [gapLo]) isAboveDiagonal_gapPath
    mem_sweptRegion_gapPath eventType_gapPath card_colouringEast_gapPath_hi le_rfl 1
    typeAIndex_gap.symm hbot_gap hside_gap

end HJO.Mellit

end
