/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidSweepACDFloor
public import HJO.Shuffle.BraidCDLetterVacuumWitness
public meta import HJO.Attr

/-! # The type-`D` clause at an unrestricted level gap

`HJO/Shuffle/BraidCDLetterVacuum.lean` closes the type-`D` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` under `η₊ ≤ η₋ + 1`, and its proof uses that
hypothesis at three points, the third — strict maximality of the moving entry at the upper level —
in a way that *genuinely* needs a gap of one there.
`HJO.Mellit.consecutive_levels_unavailable_two_three_one` shows the iteration's own level pairs do
not meet that restriction, so the restriction must be removed.

**It can be removed, and the hypothesis that replaces it is already in the bundle.** All three
points are consequences of the isolation clause `HJO.Mellit.Isolates.iso` — no lattice point of the
rectangle has its rank strictly between the two levels — which the step-restricted type-`D`
evaluation does not use.

## The two readings of the isolation clause

`HJO.Mellit.Isolates.pointRank_le` reads it downwards: `rk̂(P)` is the *least* rank of the rectangle
above `η₋`. This file adds the two other readings.

* `HJO.Mellit.Isolates.le_pointRank`: `rk̂(P)` is the **greatest** rank of the rectangle below `η₊`.
* `HJO.Mellit.Isolates.pointRank_lt_lo_add_attackWindow`: `rk̂(P) < η₋ + ω`. The point one row
  below `P` is a rectangle point of rank `rk̂(P) - ω` (`HJO.Braid.entryRank`'s own row step), so the
  isolation clause pushes it under `η₋`. **This bounds the level gap where the geometry needs it
  bounded** — and it is a consequence of isolation, not a hypothesis.

## What each of the three points becomes

* **Strict maximality at the upper level** (`HJO.Mellit.Isolates.lt_braidData_fst_of_eventType_D`,
  the third point). A competing crossed east step `Q` of `c_{η₊}` carries `rk̂(Q⁺) < η₊` for its own
  right end `Q⁺` (`HJO.Mellit.pointRank_lt_of_mem_colouringEast`), and the moving entry's right end
  is `P` itself. So `rk̂(Q⁺) ≤ rk̂(P)` by `HJO.Mellit.Isolates.le_pointRank`, and one east step
  lowers every rank by the same `b(aN+1)N - 1` — so `rk̂(Q) ≤ rk̂(X - 1, Y)`. Ranks are compared,
  not positions, and no level gap appears
  (`HJO.Mellit.Isolates.pointRank_colStep_le_of_eventType_D`).
  **The argument of `HJO/Shuffle/BraidCDLetterVacuum.lean` compared one rank step against the
  rotation and therefore needed `η₊ - η₋ ≤ 1`; the statement does not.**
* **`hlt`, the rotation not wrapping** (the second point). At the moving index the rotated position
  is `levelPosition η₋ (rk̂(X - 1, Y))`, and `rk̂(X - 1, Y) = rk̂(P) + (b(aN+1)N - 1)`, so
  `HJO.Mellit.levelPosition_add_bMN_sub_one` splits it as `levelPosition η₋ (rk̂(P)) + (1 - θ)`.
  The first summand is below `θ` by `rk̂(P) < η₋ + ω`, so the sum is below `1`
  (`HJO.Mellit.Isolates.braidData_fst_add_levelDropShift_lt_one_of_eventType_D_gapFree`).
* **`levelDropShift ≤ θ`** (the first point) is not needed at all. It entered only to place the
  moving position below the puncture and to bound the wrap, and
  `HJO.Mellit.Isolates.braidData_fst_lo_lt_sweepTheta_of_eventType_D` gives the first directly from
  `rk̂(P) < η₋ + ω`. Its true scope — `η₊ - η₋ ≤ ω` — is recorded as
  `HJO.Mellit.levelDropShift_le_sweepTheta_of_le_attackWindow`, but nothing below consumes it.

## What this closes

`HJO.Mellit.braidValueColouring_sweepRecursionTypeDFloor` discharges
`HJO.Mellit.SweepRecursionTypeDFloor` — the residual `HJO/Shuffle/BraidSweepACDFloor.lean`
named — at `q ∉ {0, 1, -1}` with a square root, `u ≠ 0` and `0 < a`, `0 < b`, `0 < N`, with **no
relation between the levels beyond the floor**. With it
`HJO.Mellit.braidValueColouring_sweepRecursionACDFloor` is the floored `A`/`C`/`D` clause outright
at `a < b`, and `HJO.Mellit.braidValueColouring_eq_dsc_of_BEUnsweptFloor` puts the braid candidate
into the floored iteration leaving **two** obligations, `HJO.Mellit.SweepRecursionBEFloor` and
`HJO.Mellit.SweepRecursionUnsweptFloor`.

**`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` is not proved in full here**: the `BE`
clause, the unswept clause and the six recursions are untouched.

## Genericity

`u ≠ 0` is spent exactly where it was: the type-`D` letter is a `z` and `HJO.Sweep.braidRep` sends
`z_1 ↦ (qu)^{-1}z_1`, so at `u = 0` that letter is the zero map and the clause would be **false**,
not vacuous. Nothing here weakens that.

## Consistency checks at a wide gap

`HJO.Mellit.sweep_typeD_cdPathD_gapFree` re-derives the decided witness — `(a, b, N) = (2, 3, 1)`,
`HJO.Mellit.cdPathD`, `P = (1, 3)`, levels `19/2` and `21/2` — through the unrestricted clause, and
`HJO.Mellit.sweep_typeD_cdPathD_wide` instantiates it at the levels `13/2` and `23/2`, a gap of
**five**, where the step-restricted clause has nothing to say. Both colourings are unchanged
by the widening (`HJO.Mellit.colouringEast_cdPathD_wideLo`, and its three companions), so the wide
instance is the same geometry read at a wide gap rather than a different configuration.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open Braid Finset ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The rotation against `θ`, at its true scope -/

/-- **The rigid rotation is below `θ` exactly when the level gap is within one attack window.**
`HJO.Mellit.levelDropShift_le_sweepTheta` asks `η₊ ≤ η₋ + 1`; the rotation is `θ(η₊ - η₋)/ω`, so
what it needs is `η₊ - η₋ ≤ ω`, and `ω = a(aN+1)N ≥ 2` on a rectangle with a row and a column.

Recorded because the narrower form was the first of the three places the type-`D` evaluation spent
its level-gap hypothesis; **nothing below consumes even this one**, the two remaining places being
discharged from the isolation clause instead. -/
theorem levelDropShift_le_sweepTheta_of_le_attackWindow (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {ηlo ηhi : ℚ} (hgap : ηhi - ηlo ≤ ((attackWindow a N : ℕ) : ℚ)) :
    levelDropShift a b N ηlo ηhi ≤ sweepTheta a b N := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hθ := (sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN).1
  have hω : ((attackWindow a N : ℕ) : ℚ) = (a : ℚ) * ((a : ℚ) * N + 1) * N := by
    rw [cast_attackWindow]; ring
  rw [hω] at hgap
  rw [levelDropShift]
  have h1 : (ηhi - ηlo) / ((a : ℚ) * ((a : ℚ) * N + 1) * N) ≤ 1 := by
    rw [div_le_one hM]; linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hθ.le]

/-! ### Two pieces of position algebra -/

/-- **A rank `b(aN+1)N - 1` higher sits exactly `1 - θ` higher on the circle.** One step west raises
the rank by that amount (`HJO.Mellit.cast_pointRank_succ_fst`), and `θ s = 1 - θ` with
`ω s = b(aN+1)N - 1` turns the rank step into the position step. The mirror of
`HJO.Mellit.levelPosition_sub`, which does the same for the row step `ω` and `θ`. -/
theorem levelPosition_add_bMN_sub_one (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η r : ℚ) :
    levelPosition a b N η (r + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1))
      = levelPosition a b N η r + (1 - sweepTheta a b N) := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hs := rankDen_mul_sweepSlope (a := a) (b := b) (N := N) ha hN
  have hθ := sweepTheta_mul_sweepSlope (a := a) (b := b) (N := N) ha hb hN
  rw [← hs, ← hθ, levelPosition, levelPosition]
  field_simp
  ring

/-- **A rank less than one attack window above the level is a position below `θ`.** Positions are
`θ(r - η)/ω`, so this is the inequality `r - η < ω` rescaled. -/
theorem levelPosition_lt_sweepTheta (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η r : ℚ}
    (h : r < η + ((attackWindow a N : ℕ) : ℚ)) :
    levelPosition a b N η r < sweepTheta a b N := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hθ := (sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN).1
  have hω : ((attackWindow a N : ℕ) : ℚ) = (a : ℚ) * ((a : ℚ) * N + 1) * N := by
    rw [cast_attackWindow]; ring
  rw [hω] at h
  have h1 : (r - η) / ((a : ℚ) * ((a : ℚ) * N + 1) * N) < 1 := by
    rw [div_lt_one hM]; linarith
  calc levelPosition a b N η r
      = sweepTheta a b N * ((r - η) / ((a : ℚ) * ((a : ℚ) * N + 1) * N)) := rfl
    _ < sweepTheta a b N * 1 := by exact mul_lt_mul_of_pos_left h1 hθ
    _ = sweepTheta a b N := mul_one _

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The two new readings of the isolation clause -/

/-- **`rk̂(P)` is the greatest rank of the rectangle below the upper level.** The mirror of
`HJO.Mellit.Isolates.pointRank_le`, and read the only way the isolation clause can be read: a
rectangle point whose rank is below `η₊` either has rank above `η₋`, and then its rank *is*
`rk̂(P)`, or has rank below `η₋ < rk̂(P)`. -/
theorem le_pointRank (hI : Isolates a b N X Y ηlo ηhi) {Q : ℕ × ℕ} (hx : Q.1 ≤ a * N)
    (hy : Q.2 ≤ b * N) (h : ((pointRank a b N Q : ℤ) : ℚ) < ηhi) :
    ((pointRank a b N Q : ℤ) : ℚ) ≤ ((pointRank a b N (X, Y) : ℤ) : ℚ) := by
  by_cases hQ : ηlo < ((pointRank a b N Q : ℤ) : ℚ)
  · rw [hI.iso Q hx hy hQ h]
  · linarith [hI.ltP, not_lt.1 hQ]

/-- **THE LEVEL GAP THE GEOMETRY ACTUALLY BOUNDS: `rk̂(P) < η₋ + ω`.** The point one row below `P`
is a lattice point of the rectangle of rank `rk̂(P) - ω`
(`HJO.Mellit.cast_pointRank_pred_add_attackWindow`), and its rank is below `rk̂(P) < η₊`; so the
isolation clause forbids it to be above `η₋`, and a rank is never *equal* to an admissible level
(`HJO.Mellit.cast_pointRank_ne_of_isAdmissibleLevel`).

`0 < Y` is `HJO.Mellit.Isolates.pos_snd`, which the floor supplies: on the bottom row every rank is
at most `0`.

**This is what replaces `η₊ ≤ η₋ + 1` in the type-`D` evaluation.** It is not a hypothesis: the
isolating pair cannot be wide *below* `rk̂(P)`, however wide it is above. -/
theorem pointRank_lt_lo_add_attackWindow (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hlopos : (0 : ℚ) ≤ ηlo) :
    ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηlo + ((attackWindow a N : ℕ) : ℚ) := by
  have hY : 0 < Y := hI.pos_snd hb hN hlopos
  have hstep := cast_pointRank_pred_add_attackWindow a b N X (Y := Y) hY
  have hωpos : (0 : ℚ) < ((attackWindow a N : ℕ) : ℚ) := by
    have : 0 < attackWindow a N := attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
    exact_mod_cast this
  have hne : ((pointRank a b N (X, Y - 1) : ℤ) : ℚ) ≠ ηlo :=
    cast_pointRank_ne_of_isAdmissibleLevel hI.lo a b N (X, Y - 1)
  have hle : ((pointRank a b N (X, Y - 1) : ℤ) : ℚ) ≤ ηlo := by
    by_contra hcon
    have hlt : ((pointRank a b N (X, Y - 1) : ℤ) : ℚ) < ηhi := by
      have := hI.Plt
      linarith
    have := hI.iso (X, Y - 1) hI.xle (by have := hI.yle; omega) (not_le.1 hcon) hlt
    rw [← pointRank_pred_add_attackWindow a b N X hY] at this
    have hω : 0 < attackWindow a N := by exact_mod_cast hωpos
    omega
  have hlt : ((pointRank a b N (X, Y - 1) : ℤ) : ℚ) < ηlo := lt_of_le_of_ne hle hne
  linarith

/-! ### The moving entry at the lower level, in closed form -/

/-- **At a type-`D` drop the moving position of the LOWER data is the normalised rank of the event
point itself.** The `j`-th crossed east step of the lower colouring is `P = (X, Y)`
(`HJO.Mellit.Isolates.colStep_colouringEast_of_eventType_D`), so the position is
`levelPosition η₋ (rk̂(P))` — the step
`HJO.Mellit.Isolates.braidData_fst_lo_lt_levelDropShift_of_eventType_D` takes before it bounds. -/
theorem braidData_fst_lo_eq_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    (braidDataOfColouring a b N y ηlo k).1 j
      = levelPosition a b N ηlo ((pointRank a b N (X, Y) : ℤ) : ℚ) := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  have hcardE : #(colouringEast y ηlo) = #(colouringEast y ηhi) :=
    hI.card_colouringEast_eq_of_eventType_D ha hb hN hηlo hy hev
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.lo hlopos j
      (by rw [hcardE, hk]; exact j.isLt),
    hI.colStep_colouringEast_of_eventType_D ha hb hN hηlo hX hy hev hjlt hj hjlt,
    Function.update_self]

/-- **At a type-`D` drop the moving position of the LOWER data is below the puncture `θ`, with no
hypothesis on the level gap.** This is `HJO.Mellit.Isolates.pointRank_lt_lo_add_attackWindow` read
as a position, and it is the branch condition of `HJO.Braid.braidStep`: the added letter is a `z`.

The step-restricted route to the same conclusion went through
`HJO.Mellit.Isolates.braidData_fst_lo_lt_levelDropShift_of_eventType_D` and
`HJO.Mellit.levelDropShift_le_sweepTheta`, and so needed `η₊ ≤ η₋ + 1`. -/
theorem braidData_fst_lo_lt_sweepTheta_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    (braidDataOfColouring a b N y ηlo k).1 j < sweepTheta a b N := by
  have hlopos : (0 : ℚ) ≤ ηlo := le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg _) hηlo)
  rw [hI.braidData_fst_lo_eq_of_eventType_D ha hb hN hηlo hy hev hk j hj]
  exact levelPosition_lt_sweepTheta ha hb hN
    (hI.pointRank_lt_lo_add_attackWindow ha hb hN hlopos)

/-! ### Strict maximality at the upper level, from the isolation clause -/

/-- **THE RANK COMPARISON BEHIND MAXIMALITY.** Every crossed east step of the upper colouring has
rank at most that of `(X - 1, Y)`, the moving one.

The argument is two rank facts and the isolation clause. A crossed east step `Q` of `c_{η₊}` carries
`rk̂(Q.1 + 1, Q.2) < η₊` (`HJO.Mellit.pointRank_lt_of_mem_colouringEast`), so
`HJO.Mellit.Isolates.le_pointRank` bounds `rk̂(Q.1 + 1, Q.2) ≤ rk̂(P)`; and one step east lowers
every rank by the same `b(aN+1)N - 1` (`HJO.Mellit.cast_pointRank_succ_fst`), while
`(X - 1) + 1 = X`. So `rk̂(Q) ≤ rk̂(X - 1, Y)`.

**No level gap enters, and no position is compared.** This replaces the argument at the third of
the three places `HJO/Shuffle/BraidCDLetterVacuum.lean` spent `η₊ ≤ η₋ + 1`: its argument bounded
one rank step below the rotation, which does need a gap of one; the rank comparison does not. -/
theorem pointRank_colStep_le_of_eventType_D (hI : Isolates a b N X Y ηlo ηhi) (hX0 : 0 < X)
    {y : Heights a b N} {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (i : Fin k) :
    ((pointRank a b N (colStep (colouringEast y ηhi) (i : ℕ)) : ℤ) : ℚ)
      ≤ ((pointRank a b N (X - 1, Y) : ℤ) : ℚ) := by
  have hi : (i : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact i.isLt
  have hmem : colStep (colouringEast y ηhi) (i : ℕ) ∈ colouringEast y ηhi := colStep_mem hi
  obtain ⟨x, w, hxw⟩ : ∃ x w, colStep (colouringEast y ηhi) (i : ℕ) = (x, w) := ⟨_, _, rfl⟩
  rw [hxw] at hmem ⊢
  obtain ⟨hltη, -⟩ := pointRank_lt_of_mem_colouringEast (a := a) (b := b) (N := N) hmem
  obtain ⟨hxlt, hwht⟩ := mem_eastSteps_iff.1 (Finset.mem_filter.1 hmem).1
  simp only at hltη hxlt hwht
  have hwle : w ≤ b * N := by rw [hwht]; exact ht_le_mul y _
  have hle := hI.le_pointRank (Q := (x + 1, w)) (by omega) hwle hltη
  have h1 := cast_pointRank_succ_fst a b N x w
  have h2 := cast_pointRank_succ_fst a b N (X - 1) Y
  rw [show X - 1 + 1 = X from by omega] at h2
  linarith

/-- **THE ENTRY IS THE STRICT MAXIMUM AT THE UPPER LEVEL, AT ANY LEVEL GAP.** The ranks are ordered
by `HJO.Mellit.Isolates.pointRank_colStep_le_of_eventType_D`, `HJO.Mellit.levelPosition` is monotone
in the rank, and the entries of a colouring's braid data are distinct at stage `0` by
`HJO.Braid.IsSpecialBraidData.injective` — which is what upgrades `≤` to `<`.

This is `HJO.Mellit.Isolates.lt_braidData_fst_of_eventType_D` **without** its `η₊ ≤ η₋ + 1`. -/
theorem lt_braidData_fst_of_eventType_D_gapFree (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) (i : Fin k) (hne : i ≠ j) :
    (braidDataOfColouring a b N y ηhi k).1 i < (braidDataOfColouring a b N y ηhi k).1 j := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_D hηlo hy hev
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hi : (i : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact i.isLt
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hdatahi := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hy hkN
  have hdist : (braidDataOfColouring a b N y ηhi k).1 i
      ≠ (braidDataOfColouring a b N y ηhi k).1 j := fun hc =>
    hne (hdatahi.injective i j 0 0 (hdatahi.one_le_mult i) (hdatahi.one_le_mult j) hc).1
  refine lt_of_le_of_ne ?_ hdist
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos i hi,
    braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos j hjlt, hj]
  exact levelPosition_le_levelPosition ha hb hN ηhi
    (hI.pointRank_colStep_le_of_eventType_D hX0 hk i)

/-- `HJO.Mellit.Isolates.lt_braidData_fst_of_eventType_D_gapFree` as the entry rank
`HJO.Braid.braidStep` reads, at any level gap. -/
theorem entryRank_braidData_fst_hi_of_eventType_D_gapFree (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    entryRank (braidDataOfColouring a b N y ηhi k).1 j = k := by
  refine entryRank_eq_card_of_forall_le _ _ fun i => ?_
  by_cases h : i = j
  · rw [h]
  · exact (hI.lt_braidData_fst_of_eventType_D_gapFree ha hb hN hηlo hy hev hk j hj i h).le

/-! ### The rotation does not wrap, at any level gap -/

/-- **`hlt` of `HJO.Mellit.Isolates.moveOne_braidData_fst_of_eventType_D`, DISCHARGED at any level
gap.** The rotated position at the moving index is `levelPosition η₋ (rk̂(X - 1, Y))`; the rank
`rk̂(X - 1, Y)` is `rk̂(P) + (b(aN+1)N - 1)`, so
`HJO.Mellit.levelPosition_add_bMN_sub_one` splits the position as
`levelPosition η₋ (rk̂(P)) + (1 - θ)`, and the first summand is below `θ`
(`HJO.Mellit.Isolates.pointRank_lt_lo_add_attackWindow`). So the sum is below `1` — the isolation
clause, not the level gap, is what stops the wrap.

`HJO.Mellit.Isolates.braidData_fst_add_levelDropShift_lt_one_of_eventType_D` is the same bound from
`η₊ ≤ η₋ + 1`, and at every index rather than at the moving one; the moving index is the only one
the type-`D` clause reads. -/
theorem braidData_fst_add_levelDropShift_lt_one_of_eventType_D_gapFree (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    (hX0 : 0 < X) {y : Heights a b N} {k : ℕ} (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    (braidDataOfColouring a b N y ηhi k).1 j + levelDropShift a b N ηlo ηhi < 1 := by
  have hlopos : (0 : ℚ) ≤ ηlo := le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg _) hηlo)
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  have hrk : ((pointRank a b N (X - 1, Y) : ℤ) : ℚ)
      = ((pointRank a b N (X, Y) : ℤ) : ℚ) + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
    have h2 := cast_pointRank_succ_fst a b N (X - 1) Y
    rw [show X - 1 + 1 = X from by omega] at h2
    linarith
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos j hjlt, hj,
    ← levelPosition_eq_add_levelDropShift (a := a) (b := b) (N := N) ηlo ηhi, hrk,
    levelPosition_add_bMN_sub_one ha hb hN]
  have := levelPosition_lt_sweepTheta (a := a) (b := b) (N := N) ha hb hN
    (hI.pointRank_lt_lo_add_attackWindow ha hb hN hlopos)
  linarith

/-! ### The moving position advances onto the rotated upper tuple, at any level gap -/

/-- **`HJO.Mellit.Isolates.moveOne_braidData_fst_of_eventType_D` with both side conditions
discharged, at any level gap.** `hlt` is
`HJO.Mellit.Isolates.braidData_fst_add_levelDropShift_lt_one_of_eventType_D_gapFree` and `hne` is
`HJO.Braid.IsSpecialBraidData.ne_theta` of the lower data. -/
theorem moveOne_braidData_fst_eq_of_eventType_D_gapFree (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    moveOne (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1 j
      = fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hX0 : 0 < X := hI.pos_fst_of_eventType_D hηlo hy hev
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hθ := sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN
  have hkNlo : #(colouringNorth y ηlo) = k := by
    rw [hI.colouringNorth_eq_of_eventType_D ha hN hX hev,
      card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]
    exact hk
  have hdatalo := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.lo hηlo hy hkNlo
  refine hI.moveOne_braidData_fst_of_eventType_D ha hb hN hηlo hy hev hk j hj hθ.1 hθ.2
    (hdatalo.ne_theta j 0 (hdatalo.one_le_mult j)) ?_
    (hI.braidData_fst_add_levelDropShift_lt_one_of_eventType_D_gapFree ha hb hN hηlo hX0 hk j hj)
  have hpos := (isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hy
    (by rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk)).mem_Ioo j
  have hclo : (0 : ℚ) ≤ levelDropShift a b N ηlo ηhi := by
    rw [levelDropShift_eq_levelPosition]
    have : levelPosition a b N ηlo ηlo ≤ levelPosition a b N ηlo ηhi :=
      levelPosition_le_levelPosition ha hb hN ηlo (hI.ltP.trans hI.Plt).le
    rwa [show levelPosition a b N ηlo ηlo = 0 from by rw [levelPosition]; ring] at this
  linarith [hpos.1]

/-! ### The type-`D` letter, in closed form, at any level gap -/

/-- **THE TYPE-`D` LETTER, EVALUATED AT ANY LEVEL GAP: `T_{k↘1}z_1`.** The generator is a `z`
because the moving position of the lower data is below the puncture
(`HJO.Mellit.Isolates.braidData_fst_lo_lt_sweepTheta_of_eventType_D`), which is the letter-level
reading of `HJO.Mellit.Isolates.zCount_sub_eq_one_of_eventType_D`. The train is the full descending
one because the ranks are `1` before the move
(`HJO.Mellit.Isolates.entryRank_braidData_fst_lo_of_eventType_D`, which never needed a level gap)
and `k` after (`HJO.Mellit.Isolates.entryRank_braidData_fst_hi_of_eventType_D_gapFree`, read through
the rotated tuple by `HJO.Braid.entryRank_congr_add`). -/
theorem braidStep_braidData_fst_of_eventType_D_gapFree (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    braidStep (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1 j
      = braidTrainDown k k 1 * braidGenZ k 1 := by
  have hlo := hI.braidData_fst_lo_lt_sweepTheta_of_eventType_D ha hb hN hηlo hy hev hk j hj
  have hrank1 := hI.entryRank_braidData_fst_lo_of_eventType_D ha hb hN hηlo hy hev hk j hj
  have hmove := hI.moveOne_braidData_fst_eq_of_eventType_D_gapFree ha hb hN hηlo hy hev hk j hj
  have hrankk : entryRank
      (moveOne (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1 j) j = k := by
    rw [hmove, entryRank_congr_add (c := levelDropShift a b N ηlo ηhi) (fun _ => rfl) j]
    exact hI.entryRank_braidData_fst_hi_of_eventType_D_gapFree ha hb hN hηlo hy hev hk j hj
  rw [braidStep_of_lt hlo, hrank1, hrankk]

/-! ### The inversion count, at any level gap -/

/-- **`HJO.Mellit.Isolates.positionPair_snd_eq_of_eventType_D` at any level gap.** The two final
position tuples are rigid shifts of one another: away from the moving index the tuples differ by the
rotation, and at the moving index one `HJO.Braid.nextCrossing` step absorbs the extra
multiplicity. -/
theorem positionPair_snd_eq_of_eventType_D_gapFree (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
        (Function.update (braidDataOfColouring a b N y ηhi k).2 j
          ((braidDataOfColouring a b N y ηhi k).2 j + 1))).2
      = (positionPair (sweepTheta a b N)
          (fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi)
          (braidDataOfColouring a b N y ηhi k).2).2 := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hdatahi := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hy hkN
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  have hmove := hI.moveOne_braidData_fst_eq_of_eventType_D_gapFree ha hb hN hηlo hy hev hk j hj
  funext i
  rw [positionPair_snd, positionPair_snd]
  by_cases h : i = j
  · subst h
    rw [Function.update_self, show (braidDataOfColouring a b N y ηhi k).2 i + 1 - 1
        = ((braidDataOfColouring a b N y ηhi k).2 i - 1) + 1 from by
      have := hdatahi.one_le_mult i; omega, Function.iterate_succ_apply]
    congr 1
    have := congrFun hmove i
    rwa [moveOne_self] at this
  · rw [Function.update_of_ne h]
    congr 1
    have hi : (i : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact i.isLt
    exact hI.braidData_fst_of_eventType_D ha hb hN hηlo hy hev hjlt hj i hi
      (fun hc => h (Fin.ext hc))

/-- **`HJO.Braid.invFin` is the SAME at the two levels of a type-`D` drop, at any level gap.**
`HJO.Braid.invFin_congr_add` removes the rotation, its hypothesis being
`HJO.Mellit.Isolates.sameSide_iterate_of_eventType_D` — which never needed a level gap: at type `D`
no stage crosses the puncture. -/
theorem invFin_eq_of_eventType_D_gapFree (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
        (Function.update (braidDataOfColouring a b N y ηhi k).2 j
          ((braidDataOfColouring a b N y ηhi k).2 j + 1))
      = invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηhi k).1
          (braidDataOfColouring a b N y ηhi k).2 := by
  rw [invFin, hI.positionPair_snd_eq_of_eventType_D_gapFree ha hb hN hηlo hy hev hk j hj, ← invFin,
    invFin_congr_add _ (levelDropShift a b N ηlo ηhi) _ _
      fun t m hm => hI.sameSide_iterate_of_eventType_D ha hb hN hηlo hy hev hk t m (by omega)]

/-- **THE INVERSION COUNT AT ANY LEVEL GAP: `HJO.Braid.invIni` changes by `j - (k-1-j)`.** The
moving entry of the upper tuple is the strict maximum
(`HJO.Mellit.Isolates.lt_braidData_fst_of_eventType_D_gapFree`) and the wrapped entry of the lower
one is the strict minimum
(`HJO.Mellit.Isolates.braidData_fst_lo_lt_levelDropShift_of_eventType_D`, which needs no level gap),
and away from that index the two tuples differ by the rigid rotation. So
`HJO.Braid.tupleInversions_sub_tupleInversions_of_top_bot` applies verbatim. -/
theorem invIni_sub_invIni_of_eventType_D_gapFree (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    ((invIni (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
          (braidDataOfColouring a b N y ηhi k).2 : ℤ)
        - (invIni (sweepTheta a b N) (braidDataOfColouring a b N y ηhi k).1
            (braidDataOfColouring a b N y ηhi k).2 : ℤ))
      = ((j : ℕ) : ℤ) - ((k - 1 - (j : ℕ) : ℕ) : ℤ) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  have hlo := hI.braidData_fst_lo_lt_levelDropShift_of_eventType_D ha hb hN hηlo hy hev hk j hj
  have hagree : ∀ i : Fin k, i ≠ j → (braidDataOfColouring a b N y ηlo k).1 i
      = (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi := fun i hne =>
    hI.braidData_fst_of_eventType_D ha hb hN hηlo hy hev hjlt hj i (by rw [hk]; exact i.isLt)
      (fun hc => hne (Fin.ext hc))
  rw [invIni_eq_tupleInversions, invIni_eq_tupleInversions,
    ← tupleInversions_congr_add (c := levelDropShift a b N ηlo ηhi)
      (w := (braidDataOfColouring a b N y ηhi k).1)
      (w' := fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi)
      (fun _ => rfl)]
  refine tupleInversions_sub_tupleInversions_of_top_bot hagree
    (fun i hne => by
      have := hI.lt_braidData_fst_of_eventType_D_gapFree ha hb hN hηlo hy hev hk j hj i hne
      simpa using this) (fun i hne => ?_)
  rw [hagree i hne]
  have hpos : (0 : ℚ) < (braidDataOfColouring a b N y ηhi k).1 i := by
    rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos i
      (by rw [hk]; exact i.isLt)]
    have hmem := (Finset.mem_filter.1 (colStep_mem (show (i : ℕ) < #(colouringEast y ηhi) by
      rw [hk]; exact i.isLt))).2.2
    have := levelPosition_lt_levelPosition ha hb hN ηhi hmem
    rwa [show levelPosition a b N ηhi ηhi = 0 from by rw [levelPosition]; ring] at this
  linarith

end Isolates

/-! ### The type-`D` clause, at an unrestricted level gap -/

section Value

variable {L : Type*} [Field L] [Algebra ℚ L]

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-- **THE TYPE-`D` CLAUSE OF `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` AT AN
UNRESTRICTED LEVEL GAP, with the moving index given.** The proof is that of
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_D_of_index` with each of its
three level-gap-restricted inputs replaced by its gap-free form: the letter
(`HJO.Mellit.Isolates.braidStep_braidData_fst_of_eventType_D_gapFree`), the rotated tuple
(`HJO.Mellit.Isolates.moveOne_braidData_fst_eq_of_eventType_D_gapFree`) and the inversion count
(`HJO.Mellit.Isolates.invFin_eq_of_eventType_D_gapFree`,
`HJO.Mellit.Isolates.invIni_sub_invIni_of_eventType_D_gapFree`). The scalar action of the letter on
the vacuum (`HJO.Sweep.braidRepMellit_braidTrainDown_top_mul_braidGenZ_one_dplusIterPiece`) never
mentioned the levels.

`u ≠ 0` is spent exactly as before, and for the same reason. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_D_of_index_gapFree (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) (ha : 0 < a)
    (hb : 0 < b) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  have hr0 : r ≠ 0 := ne_zero_of_sq_eq hq hr
  have hk1 : 1 ≤ k := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hjk : (j : ℕ) < k := j.isLt
  refine hI.braidValueColouring_eq_sweepOperator_of_eventType_D_of_letter q u hq hq1 hqp hr ha hb hN
    hηlo hy hev hk j hj ?_
  rw [hI.braidStep_braidData_fst_of_eventType_D_gapFree ha hb hN hηlo hy hev hk j hj,
    braidRepMellit_braidTrainDown_top_mul_braidGenZ_one_dplusIterPiece q u hq hq1 hqp hr hu hk1,
    map_smul, Submodule.coe_smul,
    hI.moveOne_braidData_fst_eq_of_eventType_D_gapFree ha hb hN hηlo hy hev hk j hj,
    specialBraid_congr_add_of_iterate _ (levelDropShift a b N ηlo ηhi) _ _
      (fun t m hm => hI.sameSide_iterate_of_eventType_D ha hb hN hηlo hy hev hk t m hm),
    braidValueOfData, smul_smul, smul_smul,
    hI.invFin_eq_of_eventType_D_gapFree ha hb hN hηlo hy hev hk j hj]
  congr 1
  have hini := hI.invIni_sub_invIni_of_eventType_D_gapFree ha hb hN hηlo hy hev hk j hj
  have hq2 : (q : L) ^ (k - 1 - (j : ℕ)) = r ^ (2 * ((k - 1 - (j : ℕ) : ℕ) : ℤ)) := by
    rw [two_mul, zpow_add₀ hr0, zpow_natCast, ← hr, mul_pow]
  rw [hq2, ← zpow_natCast r (k - 1), ← zpow_add₀ hr0, ← zpow_add₀ hr0]
  congr 1
  omega

/-- **THE TYPE-`D` CLAUSE AT AN UNRESTRICTED LEVEL GAP.** The moving index is constructed rather
than assumed, by `HJO.Mellit.Isolates.mem_colouringEast_pred_hi_of_eventType_D` and
`HJO.Mellit.exists_colStep`.

Compared with `HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_D_of_step`
this drops `η₊ ≤ η₋ + 1` and keeps every other hypothesis unchanged. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_D_gapFree (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.D) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_D hηlo hy hev
  obtain ⟨i, hi, hie⟩ :=
    exists_colStep (hI.mem_colouringEast_pred_hi_of_eventType_D ha hb hN hX0 hev)
  exact hI.braidValueColouring_eq_sweepOperator_of_eventType_D_of_index_gapFree q u hq hq1 hqp hr hu
    ha hb hN hηlo hy hev rfl (⟨i, hi⟩ : Fin #(colouringEast y ηhi)) hie

end Isolates

/-! ### The residual, discharged -/

/-- **THE RESIDUAL `HJO.Mellit.SweepRecursionTypeDFloor`, DISCHARGED FOR THE BRAID CANDIDATE.** This
is what `HJO/Shuffle/BraidSweepACDFloor.lean` left open: the type-`D` clause of the level
recursion above the floor `aN < η₋`, at an **unrestricted** level gap.

The hypotheses are `HJO.Sweep.braidRep`'s own exclusions `q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0` with a square
root `r`, together with `u ≠ 0` and `0 < a`, `0 < b`, `0 < N`. No relation between the levels
beyond the floor, and no relation between `a` and `b`. -/
theorem braidValueColouring_sweepRecursionTypeDFloor (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    SweepRecursionTypeDFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N) :=
  fun _ _ _ _ hfl hI _ hy _ hev =>
    hI.braidValueColouring_eq_sweepOperator_of_eventType_D_gapFree q u hq hq1 hqp hr hu ha hb hN
      hfl hy hev

/-- **THE FLOORED `A`/`C`/`D` CLAUSE FOR THE BRAID CANDIDATE, OUTRIGHT.**
`HJO.Mellit.braidValueColouring_sweepRecursionACDFloor_of_typeDFloor` with its hypothesis
discharged: `HJO.Mellit.SweepRecursionACDFloor` — the clause
`HJO.Mellit.agreesWithDsc_of_recursions_floor` actually consumes, with unrestricted level pairs
above the floor — holds for `HJO.Mellit.braidValueColouring` at `a < b`.

`a < b` is spent by type `C` alone, through
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_lt`, and lies inside
the range `HJO.Mellit.shuffle_of_lhs_and_induction` quantifies over. Compare
`HJO.Mellit.braidValueColouring_sweepRecursionACDFloorStep`, which needs no relation between `a`
and `b` but only covers `η₊ = η₋ + 1` — the pairs
`HJO.Mellit.consecutive_levels_unavailable_two_three_one` shows the iteration does not present. -/
theorem braidValueColouring_sweepRecursionACDFloor (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : a < b) :
    SweepRecursionACDFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N) :=
  braidValueColouring_sweepRecursionACDFloor_of_typeDFloor q u hq hq1 hqp hr ha hb hN hab
    (braidValueColouring_sweepRecursionTypeDFloor q u hq hq1 hqp hr hu ha hb hN)

/-- **The braid candidate agrees with `HJO.Mellit.dsc` above the floor, given the `BE` clause and
the unswept clause and nothing else.** The `A`/`C`/`D` clause and the initial condition are proved;
these two are what the braid route still needs.

So the braid route stands as follows: the level floor is free
(`HJO.Mellit.agreesWithDsc_of_recursions_floor`), the `A`/`C`/`D` clause is discharged at the
unrestricted level gaps the iteration presents, and two clauses remain. -/
theorem braidValueColouring_eq_dsc_of_BEUnsweptFloor (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : a < b)
    (hBE : SweepRecursionBEFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N))
    (hUn : SweepRecursionUnsweptFloor a b N (braidValueColouring q u hq hq1 hqp hr a b N))
    {η : ℚ} (hη : IsAdmissibleLevel η) (hfl : ((a * N : ℕ) : ℚ) < η) {c : Finset (ℕ × ℕ)}
    (hc : IsAdmissibleColouring a b N η c) :
    braidValueColouring q u hq hq1 hqp hr a b N η c = dsc q u a b N η c :=
  braidValueColouring_eq_dsc_of_recursions_floor q u hq hq1 hqp hr ha hb hN
    (braidValueColouring_sweepRecursionACDFloor q u hq hq1 hqp hr hu ha hb hN hab) hBE hUn hη hfl hc

end Value

/-! ### Consistency checks: the decided witness, and one at a level gap of five

The decided type-`D` witness of `HJO/Shuffle/BraidCDIndicesWitness.lean` — `(a, b, N) = (2, 3, 1)`,
the path `HJO.Mellit.cdPathD = (0, 3, 3)`, the event `P = (1, 3)` of rank `10`, levels `19/2` and
`21/2` — is re-derived through the unrestricted clause, and then the **same** path and event are
read at the levels `13/2` and `23/2`, a gap of five. Nothing but the levels changes: the ranks of
the `2 × 3` rectangle are `{-16, -10, -8, -4, -2, 0, 2, 4, 6, 10, 12, 18}`, so `10` is
still the only one between them, and both colourings are the ones the narrow pair reads. -/

section Witness

/-- **The decided type-`D` witness through the unrestricted clause.** The counterpart of
`HJO.Mellit.sweep_typeD_cdPathD`, with the level-gap hypothesis `HJO.Mellit.cdLoD_lt_cdHiD` that
theorem supplies **not supplied**. -/
theorem sweep_typeD_cdPathD_gapFree {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) :
    braidValueColouring q u hq hq1 hqp hr 2 3 1 cdLoD (colouring cdPathD cdLoD)
      = sweepOperator q u cdPathD (1, 3)
          (braidValueColouring q u hq hq1 hqp hr 2 3 1 cdHiD (colouring cdPathD cdHiD)) :=
  isolates_cdPathD.braidValueColouring_eq_sweepOperator_of_eventType_D_gapFree q u hq hq1 hqp hr hu
    (by norm_num) (by norm_num) (by norm_num) lt_cdLoD isAboveDiagonal_cdPathD eventType_cdPathD

/-- The unrestricted clause gives the **same statement** as the step-restricted one at the decided
witness, so no `q`-power has moved. -/
example {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) :
    sweep_typeD_cdPathD q u hq hq1 hqp hr hu = sweep_typeD_cdPathD_gapFree q u hq hq1 hqp hr hu :=
  rfl

/-- **The type-`D` letter at the decided witness through the unrestricted evaluation.** The `z`
branch comes from `HJO.Mellit.Isolates.braidData_fst_lo_lt_sweepTheta_of_eventType_D` — the moving
position below the puncture read off `rk̂(P) < η₋ + ω` — rather than from the rotation being small;
the two entry ranks from the isolation clause. -/
theorem braidStep_cdPathD_lo_via_gapFree :
    braidStep (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathD cdLoD 1).1 0
      = braidTrainDown 1 1 1 * braidGenZ 1 1 :=
  isolates_cdPathD.braidStep_braidData_fst_of_eventType_D_gapFree (by norm_num) (by norm_num)
    (by norm_num) lt_cdLoD isAboveDiagonal_cdPathD eventType_cdPathD
    card_colouringEast_cdPathD_hi 0 colStep_colouringEast_cdPathD_hi

/-- The unrestricted evaluation produces the letter `HJO.Braid.braidStep` reads off the positions, a
`z` — which is what `HJO.Mellit.zCount_cdPathD_lo` counts letter by letter as `1` against
`HJO.Mellit.zCount_cdPathD_hi`'s `0`. A `ỹ` would have disagreed with that count. -/
example : braidStep_cdPathD_lo_decided = braidStep_cdPathD_lo_via_gapFree := rfl

/-- The lower level of the wide type-`D` pair, `13/2` — three units below `HJO.Mellit.cdLoD` and
still above the floor `aN = 2`. No rank of the rectangle lies in between, which is why the wider
pair still isolates. -/
def wideLoD : ℚ := 13 / 2

/-- The upper level of the wide type-`D` pair, `23/2`. The gap `wideHiD - wideLoD = 5` exceeds `1`,
so `HJO.Mellit.SweepRecursionACDFloorStep` and every clause carrying `η₊ ≤ η₋ + 1` says nothing
here. -/
def wideHiD : ℚ := 23 / 2

theorem isAdmissibleLevel_wideLoD : IsAdmissibleLevel wideLoD := ⟨6, by norm_num [wideLoD]⟩

theorem isAdmissibleLevel_wideHiD : IsAdmissibleLevel wideHiD := ⟨11, by norm_num [wideHiD]⟩

/-- **The gap of the wide pair is five**, not one. -/
theorem one_add_wideLoD_lt_wideHiD : wideLoD + 1 < wideHiD := by norm_num [wideLoD, wideHiD]

theorem lt_wideLoD : ((2 * 1 : ℕ) : ℚ) < wideLoD := by norm_num [wideLoD]

/-- **The wide pair still isolates `(1, 3)`.** Its rank is `10`, and on the `2 × 3` rectangle
`rk̂(x, w) = 6w - 8x` takes no other value in `(13/2, 23/2)`: the values are
`{-16, -10, -8, -4, -2, 0, 2, 4, 6, 10, 12, 18}`, and `omega` checks that `7 ≤ 6w - 8x ≤ 11` with
`x ≤ 2`, `w ≤ 3` forces `6w - 8x = 10`. -/
theorem isolates_cdPathD_wide : Isolates 2 3 1 1 3 wideLoD wideHiD where
  lo := isAdmissibleLevel_wideLoD
  hi := isAdmissibleLevel_wideHiD
  ltP := by rw [pointRank_cd]; norm_num [wideLoD]
  Plt := by rw [pointRank_cd]; norm_num [wideHiD]
  iso := by
    intro Q hx hy h1 h2
    obtain ⟨x, w⟩ := Q
    simp only at hx hy
    rw [pointRank_cd] at h1 h2 ⊢
    rw [pointRank_cd]
    have h1' : (7 : ℤ) ≤ 6 * (w : ℤ) - 8 * (x : ℤ) := by
      by_contra hc
      have h6 : 6 * (w : ℤ) - 8 * (x : ℤ) ≤ 6 := by omega
      have : ((6 * (w : ℤ) - 8 * (x : ℤ) : ℤ) : ℚ) ≤ (6 : ℚ) := by exact_mod_cast h6
      rw [wideLoD] at h1
      push_cast at this h1
      linarith
    have h2' : 6 * (w : ℤ) - 8 * (x : ℤ) ≤ (11 : ℤ) := by
      by_contra hc
      have h12 : (12 : ℤ) ≤ 6 * (w : ℤ) - 8 * (x : ℤ) := by omega
      have : (12 : ℚ) ≤ ((6 * (w : ℤ) - 8 * (x : ℤ) : ℤ) : ℚ) := by exact_mod_cast h12
      rw [wideHiD] at h2
      push_cast at this h2
      linarith
    omega
  xle := by norm_num
  yle := by norm_num

/-- **The crossed east step at the wide upper level is `(0, 3)`** — the one the narrow upper level
`21/2` reads. -/
theorem colouringEast_cdPathD_wideHi : colouringEast cdPathD wideHiD = {((0 : ℕ), (3 : ℕ))} := by
  ext P
  rw [colouringEast, Finset.mem_filter, eastSteps_cdPathD]
  constructor
  · rintro ⟨hP, h⟩
    revert h
    fin_cases hP <;> norm_num [wideHiD, pointRank_cd]
  · intro hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact ⟨by decide, by norm_num [wideHiD, pointRank_cd]⟩

/-- **The crossed east step at the wide lower level is `(1, 3)`** — the one the narrow lower level
`19/2` reads. -/
theorem colouringEast_cdPathD_wideLo : colouringEast cdPathD wideLoD = {((1 : ℕ), (3 : ℕ))} := by
  ext P
  rw [colouringEast, Finset.mem_filter, eastSteps_cdPathD]
  constructor
  · rintro ⟨hP, h⟩
    revert h
    fin_cases hP <;> norm_num [wideLoD, pointRank_cd]
  · intro hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact ⟨by decide, by norm_num [wideLoD, pointRank_cd]⟩

theorem colouringNorth_cdPathD_wideHi : colouringNorth cdPathD wideHiD = {((0 : ℕ), (1 : ℕ))} :=
  colouringNorth_cdPathD wideHiD (by norm_num [wideHiD]) (by norm_num [wideHiD])

theorem colouringNorth_cdPathD_wideLo : colouringNorth cdPathD wideLoD = {((0 : ℕ), (1 : ℕ))} :=
  colouringNorth_cdPathD wideLoD (by norm_num [wideLoD]) (by norm_num [wideLoD])

/-- **The wide pair reads the same two colourings as the narrow one.** So the wide instance below is
the decided configuration — one crossed north step `(0, 1)`, one crossed east step moving from
`(0, 3)` to `(1, 3)`, rank `k = 1` — read at a level gap of five, not a different configuration. -/
theorem colouring_cdPathD_wide_eq :
    colouring cdPathD wideLoD = colouring cdPathD cdLoD ∧
      colouring cdPathD wideHiD = colouring cdPathD cdHiD := by
  refine ⟨?_, ?_⟩
  · rw [colouring_eq_union, colouring_eq_union, colouringNorth_cdPathD_wideLo,
      colouringEast_cdPathD_wideLo, colouringNorth_cdPathD_lo, colouringEast_cdPathD_lo]
  · rw [colouring_eq_union, colouring_eq_union, colouringNorth_cdPathD_wideHi,
      colouringEast_cdPathD_wideHi, colouringNorth_cdPathD_hi, colouringEast_cdPathD_hi]

theorem card_colouringEast_cdPathD_wideHi : #(colouringEast cdPathD wideHiD) = 1 := by
  rw [colouringEast_cdPathD_wideHi]; decide

theorem colStep_colouringEast_cdPathD_wideHi :
    colStep (colouringEast cdPathD wideHiD) 0 = (1 - 1, 3) :=
  colStep_of_pinned (columnInjective_colouringEast (by norm_num) (by norm_num)
      isAdmissibleLevel_wideHiD cdPathD)
    (by rw [colouringEast_cdPathD_wideHi]; decide) (by rw [colouringEast_cdPathD_wideHi]; decide)

/-- **THE TYPE-`D` LETTER AT A LEVEL GAP OF FIVE is the same `z` with the same empty train.** The
evaluation fires where the step-restricted one is silent, and the letter it produces agrees with the
one the narrow pair reads (`HJO.Mellit.braidStep_cdPathD_lo_via_gapFree`). -/
theorem braidStep_cdPathD_wideLo :
    braidStep (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathD wideLoD 1).1 0
      = braidTrainDown 1 1 1 * braidGenZ 1 1 :=
  isolates_cdPathD_wide.braidStep_braidData_fst_of_eventType_D_gapFree (by norm_num) (by norm_num)
    (by norm_num) lt_wideLoD isAboveDiagonal_cdPathD eventType_cdPathD
    card_colouringEast_cdPathD_wideHi 0 colStep_colouringEast_cdPathD_wideHi

/-- **THE TYPE-`D` CLAUSE AT A LEVEL GAP OF FIVE.** The same path, the same event and — by
`HJO.Mellit.colouring_cdPathD_wide_eq` — the same two colourings as the decided witness, at the
levels `13/2` and `23/2`.

**This is the instance the step-restricted clause cannot supply.**
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_D_of_step` asks
`η₊ ≤ η₋ + 1`, which `HJO.Mellit.one_add_wideLoD_lt_wideHiD` refutes here; and by
`HJO.Mellit.consecutive_levels_unavailable_two_three_one` it is pairs of exactly this kind that the
floored iteration presents on this very rectangle. -/
theorem sweep_typeD_cdPathD_wide {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) :
    braidValueColouring q u hq hq1 hqp hr 2 3 1 wideLoD (colouring cdPathD wideLoD)
      = sweepOperator q u cdPathD (1, 3)
          (braidValueColouring q u hq hq1 hqp hr 2 3 1 wideHiD (colouring cdPathD wideHiD)) :=
  isolates_cdPathD_wide.braidValueColouring_eq_sweepOperator_of_eventType_D_gapFree q u hq hq1 hqp
    hr hu (by norm_num) (by norm_num) (by norm_num) lt_wideLoD isAboveDiagonal_cdPathD
    eventType_cdPathD

end Witness

end HJO.Mellit

end
