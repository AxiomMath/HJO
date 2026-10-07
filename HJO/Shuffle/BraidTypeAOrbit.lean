/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidCrossingLattice
public import HJO.Shuffle.BraidTypeAObligations

/-! # The two orbit obligations of a type-`A` event, discharged

`HJO.Mellit.braidValueColouring_eq_sweepOperator_of_eventType_A` proves the type-`A` clause from two
hypotheses about the orbit of `HJO.Braid.nextCrossing`, `hbot` and `hside`, and
`HJO/Shuffle/BraidTypeAObligations.lean` reduces each of them to a single missing step: that
the stage crossing in question is realised by a lattice point of the rectangle, with one excluded
point each. `HJO/Shuffle/BraidCrossingLattice.lean` supplies the realisation. This file joins
the two and removes both hypotheses.

## The two exclusions

* **`hbot` needs `Q ≠ (X, Y)`.** The event point's crossing index is `X + Y`, which is both endpoint
  index of the *inserted* component — `HJO.Mellit.Isolates.componentBotIndex_lo_typeAIndex` and
  `HJO.Mellit.Isolates.componentTopIndex_lo_typeAIndex`. A retained component is a different
  component, and distinct components share no crossing index
  (`HJO.Mellit.componentTopIndex_lt_componentBotIndex`), so no crossing of a retained component has
  index `X + Y`. Since a realising point has `x + yy` equal to the index it realises, `Q = (X, Y)`
  is impossible. `HJO/Shuffle/BraidTypeAObligations.lean` states this in prose; here it is
  `HJO.Mellit.Isolates.lt_iterate_of_eventType_A`.

* **`hside` needs `Q ≠ (X, Y + 1)`.** This is where the *sharp* ordinate bound of
  `HJO.Mellit.exists_pointRank_of_le_componentTopIndex` earns its keep. That bound is not merely
  `yy ≤ bN` but `yy ≤ ŷ_{x+1}`: the realising point lies weakly below the path, because inside a
  component the level line does. At a type-`A` event `ŷ_{X+1} ≤ Y` — type `A` is a north step
  followed by an east step, so the path does not rise past `Y` in the next column
  (`HJO.Paths.ht_lt_of_eventType_A`). A realising point `(X, Y + 1)` would need `Y + 1 ≤ ŷ_{X+1}`,
  and that is the contradiction.

The second exclusion is the one that would fail on the weaker bound, and it is not a formality: if
`(X, Y + 1)` *did* realise a stage crossing of a retained component then `hside` would be **false**
there, since `HJO.Mellit.levelPosition` of `rk̂ (X, Y + 1)` sits one `θ` above a position the level
drop moves across the puncture. So the sharp bound is not an optimisation; it is the statement.

## What is left to the next file

`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_A_of_card` below keeps the
hypothesis `1 ≤ k`, which is not geometry: `HJO.Sweep.dplusIntertwines_specialBraid` starts its
induction at rank `1`. `HJO/Shuffle/BraidTypeAUnconditional.lean` settles the rank-`0` case and
removes it.

**Only the type-`A` clause is proved here.** It is one clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`; the types `C` and `D` are untouched.

## References

Transcribing A. Mellit,
*Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {a b N X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### Every stage position of a component is the normalised rank of a lattice point -/

/-- **Every stage position of a component is the normalised rank of a lattice point of the
rectangle.** The `m`-th iterate of `HJO.Braid.nextCrossing` at `v_i` is the position of the crossing
`m` indices below the top one (`HJO.Mellit.iterate_nextCrossing_fract_crossingAbscissa`), the bound
on `m` puts that index inside the component's range, and
`HJO.Mellit.exists_pointRank_of_le_componentTopIndex` realises it. The bracketing of the index is
returned along with the point, since it is what the two exclusions below argue with. -/
theorem exists_pointRank_iterate_nextCrossing (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {k : ℕ} (hk : #(colouringEast y η) = k) (i : Fin k) {m : ℕ}
    (hm : m ≤ (braidDataOfColouring a b N y η k).2 i - 1) :
    ∃ x yy : ℕ, x < a * N ∧ 0 < yy ∧ yy ≤ ht y (x + 1) ∧
      componentBotIndex a b N y η (i : ℕ) ≤ (x : ℤ) + (yy : ℤ) ∧
      (x : ℤ) + (yy : ℤ) ≤ componentTopIndex a b N y η (i : ℕ) ∧
      η < ((pointRank a b N (x, yy) : ℤ) : ℚ) ∧
      (nextCrossing (sweepTheta a b N))^[m] ((braidDataOfColouring a b N y η k).1 i)
        = levelPosition a b N η ((pointRank a b N (x, yy) : ℤ) : ℚ) := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηa
  have hiN : (i : ℕ) < #(colouringNorth y η) := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hη hηa hy, hk]; exact i.isLt
  have hle := componentBotIndex_le_componentTopIndex ha hb hN hη hηa hy hiN
  have hcard : (braidDataOfColouring a b N y η k).2 i
      = (componentTopIndex a b N y η (i : ℕ) + 1
          - componentBotIndex a b N y η (i : ℕ)).toNat := by
    rw [braidDataOfColouring_snd, componentCrossingIndices_eq_Icc, Int.card_Icc]
  rw [hcard] at hm
  have hmle : componentBotIndex a b N y η (i : ℕ)
      ≤ componentTopIndex a b N y η (i : ℕ) - (m : ℤ) := by omega
  obtain ⟨x, yy, hsum, hx, hyy0, hyyle, hrk, hfr⟩ :=
    exists_pointRank_of_le_componentTopIndex ha hb hN hη hηa hy hiN hmle (by omega)
  refine ⟨x, yy, hx, hyy0, hyyle, by omega, by omega, hrk, ?_⟩
  rw [braidDataOfColouring_fst,
    iterate_nextCrossing_fract_crossingAbscissa ha hb hN hη hηpos y (i : ℕ) hmle]
  exact hfr

namespace Isolates

/-! ### `hbot`: the event point's index belongs to the inserted component alone -/

/-- **The `hbot` obligation of a type-`A` event, in general.** The inserted position is the
normalised rank of the event point and each stage position of a retained component is the normalised
rank of some lattice point `Q` of the rectangle above the lower level, so
`HJO.Mellit.lt_levelPosition_of_ne` applies as soon as `Q ≠ (X, Y)`.

And `Q ≠ (X, Y)`, because `x(Q) + y(Q)` is the crossing index `Q` realises: the index `X + Y` is
*both* endpoint indices of the inserted component, a retained component is a different component of
the same colouring, and distinct components share no crossing index. -/
theorem lt_iterate_of_eventType_A (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.A) {k : ℕ} (hk : #(colouringEast y ηhi) = k)
    (j : Fin (k + 1)) (hj : (j : ℕ) = typeAIndex y ηhi X) (t : Fin k) (m : ℕ)
    (hm : m ≤ (braidDataOfColouring a b N y ηhi k).2 t - 1) :
    (braidDataOfColouring a b N y ηlo (k + 1)).1 j
      < (nextCrossing (sweepTheta a b N))^[m]
          ((braidDataOfColouring a b N y ηlo (k + 1)).1 (j.succAbove t)) := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hklo : #(colouringEast y ηlo) = k + 1 := by
    rw [hI.card_colouringEast_of_eventType_A ha hb hN hX hPsw hev, hk]
  have hmlo : m ≤ (braidDataOfColouring a b N y ηlo (k + 1)).2 (j.succAbove t) - 1 := by
    rw [hI.braidDataOfColouring_snd_succAbove ha hb hN hηlo hy hPsw hev hk j hj t]; exact hm
  obtain ⟨x, yy, hx, hyy0, hyyle, hbotle, htople, hrk, hfr⟩ :=
    exists_pointRank_iterate_nextCrossing ha hb hN hI.lo hηlo hy hklo (j.succAbove t) hmlo
  rw [hI.braidDataOfColouring_fst_typeAIndex ha hb hN hηlo hPsw hev j hj, hfr]
  refine lt_levelPosition_of_ne ha hb hN hI hx.le (hyyle.trans (ht_le_mul y _)) hrk ?_
  intro hQ
  have hx1 : x = X := congrArg Prod.fst hQ
  have hy1 : yy = Y := congrArg Prod.snd hQ
  subst hx1 hy1
  -- the index `x + yy = X + Y` is both endpoint indices of the inserted component
  have hbotj : componentBotIndex a b N y ηlo (j : ℕ) = (x : ℤ) + (yy : ℤ) := by
    rw [hj, hI.componentBotIndex_lo_typeAIndex ha hb hN hηlo hy hPsw hev]
  have htopj : componentTopIndex a b N y ηlo (j : ℕ) = (x : ℤ) + (yy : ℤ) := by
    rw [hj, hI.componentTopIndex_lo_typeAIndex ha hb hN hηlo hPsw hev]
  have hcard : #(colouringNorth y ηlo) = k + 1 := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.lo hηlo hy, hklo]
  have hjN : (j : ℕ) < #(colouringNorth y ηlo) := by rw [hcard]; exact j.isLt
  have hi'N : ((j.succAbove t : Fin (k + 1)) : ℕ) < #(colouringNorth y ηlo) := by
    rw [hcard]; exact (j.succAbove t).isLt
  have hne : ((j.succAbove t : Fin (k + 1)) : ℕ) ≠ (j : ℕ) :=
    fun h => Fin.succAbove_ne j t (Fin.val_injective h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := componentTopIndex_lt_componentBotIndex ha hb hN hI.lo hηlo hy hjN hlt
    omega
  · have := componentTopIndex_lt_componentBotIndex ha hb hN hI.lo hηlo hy hi'N hgt
    omega

/-! ### `hside`: the point above the event point lies above the path -/

/-- **The `hside` obligation of a type-`A` event, in general.** Each stage position of a retained
component is the normalised rank of a lattice point `Q` of the rectangle, weakly below the path, so
`HJO.Mellit.sameSide_levelDropShift_of_ne` applies as soon as `Q ≠ (X, Y + 1)`.

And `Q ≠ (X, Y + 1)`: at a type-`A` event the path does not rise past `Y` in the column right of
`X`, so `ŷ_{X+1} ≤ Y`, while the realising point satisfies `y(Q) ≤ ŷ_{x(Q)+1}`. This is the one
place where the *sharp* ordinate bound of
`HJO.Mellit.exists_pointRank_of_le_componentTopIndex` is used;
`y(Q) ≤ bN` would not do, and the obligation is genuinely false at `(X, Y + 1)`. -/
theorem sameSide_iterate_of_eventType_A (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.A) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (t : Fin k) (m : ℕ)
    (hm : m ≤ (braidDataOfColouring a b N y ηhi k).2 t - 1) :
    SameSide (sweepTheta a b N) (levelDropShift a b N ηlo ηhi)
      ((nextCrossing (sweepTheta a b N))^[m] ((braidDataOfColouring a b N y ηhi k).1 t)) := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  obtain ⟨x, yy, hx, hyy0, hyyle, -, -, hrk, hfr⟩ :=
    exists_pointRank_iterate_nextCrossing ha hb hN hI.hi hηhi hy hk t hm
  rw [hfr]
  refine sameSide_levelDropShift_of_ne ha hb hN hI hx.le
    (le_trans (hyyle.trans (ht_le_mul y _)) (by omega)) hyy0 ?_
  intro hQ
  have hx1 : x = X := congrArg Prod.fst hQ
  have hy1 : yy = Y + 1 := congrArg Prod.snd hQ
  subst hx1
  have hA : ht y (x + 1) ≤ Y := by
    by_contra hc
    exact (ht_lt_of_eventType_A hev).2 ⟨hX, by omega⟩
  omega

/-! ### The type-`A` clause, with no orbit hypothesis -/

/-- **The type-`A` clause of the sweep recursion for `HJO.Mellit.braidValueColouring`, with both
orbit hypotheses discharged.** This is
`HJO.Mellit.braidValueColouring_eq_sweepOperator_of_eventType_A` with `hbot` and `hside` supplied by
`HJO.Mellit.Isolates.lt_iterate_of_eventType_A` and
`HJO.Mellit.Isolates.sameSide_iterate_of_eventType_A`, and with the insertion index constructed
rather than assumed.

The remaining hypothesis `1 ≤ k` is not geometry: the rank-raise intertwiner
`HJO.Sweep.dplusIntertwines_specialBraid` begins its induction at rank `1`. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_A_of_card {L : Type*} [Field L]
    [Algebra ℚ L] (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A)
    (hk1 : 1 ≤ #(colouringEast y ηhi)) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  have hjlt : typeAIndex y ηhi X < #(colouringEast y ηhi) + 1 := by
    have := typeAIndex_le y ηhi X; omega
  refine braidValueColouring_eq_sweepOperator_of_eventType_A q u hq hq1 hqp hr ha hb hN hI hηlo hy
    hPsw hev rfl hk1 ⟨typeAIndex y ηhi X, hjlt⟩ rfl
    (hI.lt_iterate_of_eventType_A ha hb hN hηlo hy hPsw hev rfl _ rfl)
    (hI.sameSide_iterate_of_eventType_A ha hb hN hηlo hy hev rfl)

end Isolates

/-! ### Consistency check: the decided witness, through the unconditional route -/

/-- **The decided instance of the type-`A` clause, derived with no orbit hypothesis at all.** This
is verbatim the statement of `HJO.Mellit.braidValueColouring_gap_typeA` and of
`HJO.Mellit.gap_typeA_via_transfer`, but where the latter discharges `hbot` and `hside` by explicit
computation at `a = 2`, `b = 5`, `N = 1` (`HJO.Mellit.hbot_gap`, `HJO.Mellit.hside_gap`), this one
takes them from the general lemmas above. The only remaining input is `1 ≤ k`.

So the general route reproduces the one configuration that is independently decided: `θ = 12/40`,
lower data `v = (17/40, 1/40)` and `α = (2, 1)`, upper data `v = (15/40)` and `α = (2)`, shift
`2/40`, insertion index `j = 1`. An error in the realising point, in its two bounds, or in either
exclusion would make this derivation fail, the right-hand side being pinned independently. -/
theorem gap_typeA_via_orbit {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) :
    braidValueColouring q u hq hq1 hqp hr 2 5 1 gapLo (colouring gapPath gapLo)
      = sweepOperator q u gapPath (1, 5)
          (braidValueColouring q u hq hq1 hqp hr 2 5 1 gapHi (colouring gapPath gapHi)) :=
  isolates_gapPath.braidValueColouring_eq_sweepOperator_of_eventType_A_of_card q u hq hq1 hqp hr
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [gapLo]) isAboveDiagonal_gapPath
    mem_sweptRegion_gapPath eventType_gapPath (by rw [card_colouringEast_gapPath_hi])

end HJO.Mellit

end
