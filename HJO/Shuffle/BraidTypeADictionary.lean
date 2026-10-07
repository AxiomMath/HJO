/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidColStepInsert
public import HJO.Shuffle.BraidLevelDrop
public import HJO.Shuffle.BraidValueUnswept

/-! # The dictionary of a type-`A` event: a bottom insertion of a fixed point

`HJO.Mellit.braidValueOfData_succAbove_eq_dplus` proves the type-`A` identity at the level of
special-braid data: at a *bottom insertion of a fixed point* — an index `j` of multiplicity `1`
whose position lies below every other position, at every stage of the move sequence — the value of
the inserted data is `d^♭_+` of the braid value of the deleted data. **Nothing in that theorem knows
about colourings.** This file supplies the missing dictionary: it identifies the two colourings of a
type-`A` event as exactly such a pair.

## What is established

Fix a bracketing `HJO.Mellit.Isolates` of the event point `(X, Y)`, an above-diagonal path `y`
sweeping it whose event there is of type `A`, and write `k = #(colouringEast y ηhi)`. Then, with

`j = HJO.Mellit.typeAIndex y ηhi X`

the number of crossed east steps strictly left of the event's column:

* **The rank rises by one.** `HJO.Mellit.Isolates.card_colouringEast_of_eventType_A`:
  `#(colouringEast y ηlo) = k + 1`.
* **`j` is a single insertion index for both halves.**
  `HJO.Mellit.Isolates.typeAIndex_eq_card_filter_colouringNorth` says the count of crossed *north*
  steps left of the column is the same number — this is the only place the geometry of the event is
  really used, through `HJO.Mellit.card_colouringNorth_filter_lt` and the fact that at a type-`A`
  event the upper level runs at or above the path at the event's column
  (`HJO.Mellit.Isolates.ht_le_levelIndex_hi_of_eventType_A`). With that,
  `HJO.Mellit.Isolates.colStep_colouringNorth_lo_typeAIndex`,
  `HJO.Mellit.Isolates.colStep_colouringEast_lo_typeAIndex` place the two new steps `(X, Y-1)` and
  `(X, Y)` at index `j` of the lower listings, and
  `HJO.Mellit.Isolates.colStep_colouringNorth_lo_succAbove`,
  `HJO.Mellit.Isolates.colStep_colouringEast_lo_succAbove` say the old ones are listed along
  `j.succAbove`.
* **The multiplicities.** `HJO.Mellit.Isolates.braidDataOfColouring_snd_typeAIndex`: `α_lo j = 1`,
  the inserted component having its two endpoints at the same crossing index `X + Y`; and
  `HJO.Mellit.Isolates.braidDataOfColouring_snd_succAbove`: `α_lo ∘ j.succAbove = α_hi`. Only the
  *sum* of these was previously available, as
  `HJO.Mellit.Isolates.totalCrossings_of_eventType_A`.
* **The positions.** `HJO.Mellit.Isolates.braidDataOfColouring_fst_succAbove`: the retained
  positions all rise by the one amount `HJO.Mellit.levelDropShift`, and
  `HJO.Mellit.Isolates.braidDataOfColouring_fst_typeAIndex_lt`: the inserted position is **strictly
  below** every retained one, which is the `hini` hypothesis of the data-level identity. That second
  one is free: the event point's rank is below `ηhi` and every crossed east step of the upper
  colouring has rank above `ηhi`, and `HJO.Mellit.levelPosition` is strictly increasing in the rank.
* **The width.** `HJO.Mellit.Isolates.sweepWidth_eq_card_colouringEast`: `k_{P̂}(P) = k`, so the
  event operator `HJO.Sweep.sweepOperator` at a type-`A` event is `dplus q k` — the very `d^♭_+` the
  data-level identity produces. This is `HJO.Mellit.liveSteps_eq_colouringNorth` combined with
  `HJO.Mellit.card_colouringNorth_eq_card_colouringEast`.

## What is *not* established here

Two hypotheses of `HJO.Mellit.braidValueOfData_succAbove_eq_dplus` are about the *stages* of the
move sequence rather than the starting positions, and are not settled in this file; see
`HJO/Shuffle/BraidTypeATransfer.lean`, which carries them as named hypotheses and proves the
clause from them. They are the `hmin`/`hfin` pair — the inserted position stays below every retained
entry after each move — and, separately, the `HJO.Braid.SameSide` obligation that turns the rigid
shift of the positions into an equality of braid values. Neither is a statement about the colouring:
both are statements about the orbit of `HJO.Braid.nextCrossing`, which is where the remaining work
on the type-`A` clause lies.

## Genericity

None is spent: every statement here is about `ℕ`, `ℤ` and `ℚ` — colourings, crossing indices,
positions and counts. No braid, no representation, no field.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {a b N X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The two halves have the same count to the left of a column the level runs above -/

/-- **Where the level line runs at or above the path, the two halves of the colouring have the same
count to the left.** This is `HJO.Mellit.card_colouringNorth_filter_lt` with its indicator
discharged: the balance term is `1` exactly when the level line is *below* the path at the vertical
lattice line in question. -/
theorem card_filter_colouringNorth_eq_card_filter_colouringEast
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η) (hηpos : 0 < η)
    {y : Heights a b N} (hy : IsAboveDiagonal y) {t : ℕ} (htN : t ≤ a * N)
    (hle : (ht y t : ℤ) ≤ levelIndex a b N η t) :
    #({P ∈ colouringNorth y η | P.1 < t}) = #({P ∈ colouringEast y η | P.1 < t}) := by
  have h := card_colouringNorth_filter_lt ha hb hN hη hηpos hy htN
  rw [ite_eq_right_of_eq_false _ _
    (eq_false (by omega : ¬ levelIndex a b N η t < (ht y t : ℤ)))] at h
  omega

/-! ### The positions are strictly ordered by rank -/

/-- **`HJO.Mellit.levelPosition` is strictly increasing in the rank.** The strict companion of
`HJO.Mellit.levelPosition_le_levelPosition`, and what makes a rank comparison between the event
point and a crossed east step a comparison of the braid data's positions. -/
theorem levelPosition_lt_levelPosition (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) {r r' : ℚ}
    (h : r < r') : levelPosition a b N η r < levelPosition a b N η r' := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hθ := (sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN).1
  rw [levelPosition, levelPosition]
  gcongr

/-! ### The insertion index -/

/-- **The insertion index of a type-`A` event at the column `X`**: the number of crossed east steps
of the upper colouring strictly left of that column. By
`HJO.Mellit.Isolates.typeAIndex_eq_card_filter_colouringNorth` it is also the count in the north
half, so it is one index serving both listings. -/
noncomputable def typeAIndex (y : Heights a b N) (η : ℚ) (X : ℕ) : ℕ :=
  #({Q ∈ colouringEast y η | Q.1 < X})

/-- The insertion index does not exceed the upper rank. -/
theorem typeAIndex_le (y : Heights a b N) (η : ℚ) (X : ℕ) :
    typeAIndex y η X ≤ #(colouringEast y η) :=
  Finset.card_filter_le _ _

namespace Isolates

/-! ### No step of the upper colouring sits in the event's column -/

/-- **The upper colouring has no crossed north step in the event's column.** The lower one has
`(X, Y-1)` there, and a colouring meets each column once. -/
theorem forall_fst_ne_of_eventType_A_north (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X < a * N) (hY : 0 < Y) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A) :
    ∀ Q ∈ colouringNorth y ηhi, Q.1 ≠ X := by
  intro Q hQ hQX
  have hins := hI.colouringNorth_eq_of_eventType_A ha hN hX hPsw hev
  have hQlo : Q ∈ colouringNorth y ηlo := by rw [hins]; exact Finset.mem_insert_of_mem hQ
  have hplo : ((X, Y - 1) : ℕ × ℕ) ∈ colouringNorth y ηlo := by
    rw [hins]; exact Finset.mem_insert_self _ _
  have heq := columnInjective_colouringNorth ha hN hI.lo y Q hQlo _ hplo hQX
  exact hI.notMem_colouringNorth_pred_hi hY y (heq ▸ hQ)

/-- **The upper colouring has no crossed east step in the event's column.** The lower one has
`(X, Y)` there. -/
theorem forall_fst_ne_of_eventType_A_east (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X < a * N) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A) :
    ∀ Q ∈ colouringEast y ηhi, Q.1 ≠ X := by
  intro Q hQ hQX
  have hins := hI.colouringEast_eq_of_eventType_A ha hb hN hX hPsw hev
  have hQlo : Q ∈ colouringEast y ηlo := by rw [hins]; exact Finset.mem_insert_of_mem hQ
  have hplo : ((X, Y) : ℕ × ℕ) ∈ colouringEast y ηlo := by
    rw [hins]; exact Finset.mem_insert_self _ _
  have heq := columnInjective_colouringEast ha hN hI.lo y Q hQlo _ hplo hQX
  exact hI.notMem_colouringEast_hi y (heq ▸ hQ)

/-! ### The rank rises by one -/

/-- **The lower colouring has exactly one more component.** The first of the five identifications:
`k_lo = k_hi + 1`. -/
theorem card_colouringEast_of_eventType_A (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X < a * N) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A) :
    #(colouringEast y ηlo) = #(colouringEast y ηhi) + 1 := by
  rw [hI.colouringEast_eq_of_eventType_A ha hb hN hX hPsw hev,
    Finset.card_insert_of_notMem (hI.notMem_colouringEast_hi y)]

/-! ### At the event's column the upper level runs at or above the path -/

/-- **At a type-`A` event the upper level's index at the event's column is at least the path height
there.** The lower level's index at that column is `Y - 1`, which is already at least `ht y X`
because `(X, Y-1)` is a crossed north step below; and away from `(X, Y)` the two levels cut the
rectangle in the same place, by `HJO.Mellit.Isolates.le_levelIndex_iff_of_ne`. -/
theorem ht_le_levelIndex_hi_of_eventType_A (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X < a * N) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A) :
    (ht y X : ℤ) ≤ levelIndex a b N ηhi X := by
  have hins := hI.colouringNorth_eq_of_eventType_A ha hN hX hPsw hev
  have hplo : ((X, Y - 1) : ℕ × ℕ) ∈ colouringNorth y ηlo := by
    rw [hins]; exact Finset.mem_insert_self _ _
  obtain ⟨-, h2, -, -⟩ := mem_colouringNorth_spec ha hN hI.lo y hplo
  have hht : ht y X < Y := (ht_lt_of_eventType_A hev).1
  have hne : ((X, ht y X) : ℕ × ℕ) ≠ (X, Y) := fun h =>
    absurd (congrArg Prod.snd h) (by omega)
  exact (hI.le_levelIndex_iff_of_ne ha hN hI.xle (ht_le_mul y X) hne).1 (by simpa using h2)

/-! ### One index serves both halves -/

/-- **The insertion index is the same in the two halves of the colouring.** At a type-`A` event the
upper level runs at or above the path at the event's column, so the balance term of
`HJO.Mellit.card_colouringNorth_filter_lt` vanishes there and the two counts agree. This is the
second identification: the new crossed north step and the new crossed east step are inserted at the
*same* position of their respective listings, which is what lets one `j : Fin (k+1)` describe the
whole event. -/
theorem typeAIndex_eq_card_filter_colouringNorth (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.A) :
    typeAIndex y ηhi X = #({Q ∈ colouringNorth y ηhi | Q.1 < X}) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hpos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  exact (card_filter_colouringNorth_eq_card_filter_colouringEast ha hb hN hI.hi hpos hy hI.xle
    (hI.ht_le_levelIndex_hi_of_eventType_A ha hN (hI.fst_lt hηlo) hPsw hev)).symm

/-! ### The listings of the lower colouring, along the insertion index -/

/-- **The new crossed east step is the `j`-th member of the lower east listing.** -/
theorem colStep_colouringEast_lo_typeAIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X < a * N) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A) :
    colStep (colouringEast y ηlo) (typeAIndex y ηhi X) = (X, Y) := by
  rw [typeAIndex, hI.colouringEast_eq_of_eventType_A ha hb hN hX hPsw hev]
  exact colStep_insert_self (columnInjective_colouringEast ha hN hI.hi y)
    (hI.forall_fst_ne_of_eventType_A_east ha hb hN hX hPsw hev)

/-- **The new crossed north step is the `j`-th member of the lower north listing**, for the *same*
`j`. -/
theorem colStep_colouringNorth_lo_typeAIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.A) :
    colStep (colouringNorth y ηlo) (typeAIndex y ηhi X) = (X, Y - 1) := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hY : 0 < Y := by have := (ht_lt_of_eventType_A hev).1; omega
  rw [hI.typeAIndex_eq_card_filter_colouringNorth ha hb hN hηlo hy hPsw hev,
    hI.colouringNorth_eq_of_eventType_A ha hN hX hPsw hev]
  exact colStep_insert_self (columnInjective_colouringNorth ha hN hI.hi y)
    (hI.forall_fst_ne_of_eventType_A_north ha hN hX hY hPsw hev)

/-- **Away from the insertion index the lower east listing is the upper one, read along
`Fin.succAbove`.** -/
theorem colStep_colouringEast_lo_succAbove (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X < a * N) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin (k + 1)) (hj : (j : ℕ) = typeAIndex y ηhi X)
    (i : Fin k) :
    colStep (colouringEast y ηlo) ((j.succAbove i : Fin (k + 1)) : ℕ)
      = colStep (colouringEast y ηhi) (i : ℕ) := by
  rw [hI.colouringEast_eq_of_eventType_A ha hb hN hX hPsw hev]
  exact colStep_insert_succAbove (columnInjective_colouringEast ha hN hI.hi y)
    (hI.notMem_colouringEast_hi y) (hI.forall_fst_ne_of_eventType_A_east ha hb hN hX hPsw hev)
    hk j (hj.trans rfl) i

/-- **Away from the insertion index the lower north listing is the upper one, read along
`Fin.succAbove`.** -/
theorem colStep_colouringNorth_lo_succAbove (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.A) {k : ℕ} (hk : #(colouringNorth y ηhi) = k)
    (j : Fin (k + 1)) (hj : (j : ℕ) = typeAIndex y ηhi X) (i : Fin k) :
    colStep (colouringNorth y ηlo) ((j.succAbove i : Fin (k + 1)) : ℕ)
      = colStep (colouringNorth y ηhi) (i : ℕ) := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hY : 0 < Y := by have := (ht_lt_of_eventType_A hev).1; omega
  rw [hI.colouringNorth_eq_of_eventType_A ha hN hX hPsw hev]
  refine colStep_insert_succAbove (columnInjective_colouringNorth ha hN hI.hi y)
    (hI.notMem_colouringNorth_pred_hi hY y)
    (hI.forall_fst_ne_of_eventType_A_north ha hN hX hY hPsw hev) hk j ?_ i
  rw [hj, hI.typeAIndex_eq_card_filter_colouringNorth ha hb hN hηlo hy hPsw hev]

/-! ### The level index at a retained column does not move -/

/-- **A crossed north step of the upper colouring pins the level index of its column at both
levels.** It is a crossed north step of the lower colouring too, and the ordinate of a crossed north
step *is* the level index of its column; so the two indices agree there. This is what makes the
retained components' bottom crossing indices the same on the two sides. -/
theorem levelIndex_lo_eq_hi_of_mem_colouringNorth_hi (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X < a * N) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A)
    {Q : ℕ × ℕ} (hQ : Q ∈ colouringNorth y ηhi) :
    levelIndex a b N ηlo Q.1 = levelIndex a b N ηhi Q.1 := by
  have hQlo : Q ∈ colouringNorth y ηlo := by
    rw [hI.colouringNorth_eq_of_eventType_A ha hN hX hPsw hev]; exact Finset.mem_insert_of_mem hQ
  obtain ⟨-, -, -, h4⟩ := mem_colouringNorth_spec ha hN hI.lo y hQlo
  obtain ⟨-, -, -, h4'⟩ := mem_colouringNorth_spec ha hN hI.hi y hQ
  rw [← h4, ← h4']

/-! ### The two endpoints of the inserted component coincide -/

/-- **The inserted component's bottom crossing index is `X + Y`.** Its crossed north step is
`(X, Y-1)`, whose ordinate is the lower level's index in the column `X`, so the first crossing at or
above the component's left end is the one of index `X + (Y-1) + 1`. -/
theorem componentBotIndex_lo_typeAIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.A) :
    componentBotIndex a b N y ηlo (typeAIndex y ηhi X) = (X : ℤ) + (Y : ℤ) := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hY : 0 < Y := by have := (ht_lt_of_eventType_A hev).1; omega
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hplo : ((X, Y - 1) : ℕ × ℕ) ∈ colouringNorth y ηlo := by
    rw [hI.colouringNorth_eq_of_eventType_A ha hN hX hPsw hev]; exact Finset.mem_insert_self _ _
  obtain ⟨-, -, -, h4⟩ := mem_colouringNorth_spec ha hN hI.lo y hplo
  have h4' : ((Y - 1 : ℕ) : ℤ) = levelIndex a b N ηlo X := h4
  rw [componentBotIndex_eq ha hb hN hI.lo hlopos,
    hI.colStep_colouringNorth_lo_typeAIndex ha hb hN hηlo hy hPsw hev]
  omega

/-- **The inserted component's top crossing index is also `X + Y`**, its crossed east step being the
event point itself. -/
theorem componentTopIndex_lo_typeAIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A) :
    componentTopIndex a b N y ηlo (typeAIndex y ηhi X) = (X : ℤ) + (Y : ℤ) := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hlt : typeAIndex y ηhi X < #(colouringEast y ηlo) := by
    have h1 := typeAIndex_le y ηhi X
    have h2 := hI.card_colouringEast_of_eventType_A ha hb hN hX hPsw hev
    omega
  rw [componentTopIndex_eq ha hb hN hI.lo hlopos hlt,
    hI.colStep_colouringEast_lo_typeAIndex ha hb hN hX hPsw hev]

/-! ### The multiplicities -/

/-- **The inserted component has multiplicity `1`.** Its two endpoint crossing indices are both
`X + Y`, so it carries exactly one crossing and `HJO.Braid.specialMoveList` contributes nothing for
it: the third identification, and the `hβj` hypothesis of
`HJO.Mellit.braidValueOfData_succAbove_eq_dplus`.

Only the *sum* statement `HJO.Mellit.Isolates.totalCrossings_of_eventType_A` was previously
available. -/
theorem braidDataOfColouring_snd_typeAIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.A) {k : ℕ} (j : Fin (k + 1))
    (hj : (j : ℕ) = typeAIndex y ηhi X) :
    (braidDataOfColouring a b N y ηlo (k + 1)).2 j = 1 := by
  rw [braidDataOfColouring_snd, componentCrossingIndices_eq_Icc, hj,
    hI.componentBotIndex_lo_typeAIndex ha hb hN hηlo hy hPsw hev,
    hI.componentTopIndex_lo_typeAIndex ha hb hN hηlo hPsw hev, Finset.Icc_self,
    Finset.card_singleton]

/-- **The retained components keep their multiplicities.** Both endpoint indices are unchanged: the
top index reads only the crossed east step, which is the same point, and the bottom index reads the
crossed north step's column together with the level index there, which
`HJO.Mellit.Isolates.levelIndex_lo_eq_hi_of_mem_colouringNorth_hi` pins. The second half of the
third identification, `α_lo ∘ j.succAbove = α_hi`. -/
theorem braidDataOfColouring_snd_succAbove (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.A) {k : ℕ} (hk : #(colouringEast y ηhi) = k)
    (j : Fin (k + 1)) (hj : (j : ℕ) = typeAIndex y ηhi X) (i : Fin k) :
    (braidDataOfColouring a b N y ηlo (k + 1)).2 (j.succAbove i)
      = (braidDataOfColouring a b N y ηhi k).2 i := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hY : 0 < Y := by have := (ht_lt_of_eventType_A hev).1; omega
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy, hk]
  have hiN : (i : ℕ) < #(colouringNorth y ηhi) := by rw [hkN]; exact i.isLt
  have hiE : (i : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact i.isLt
  have hEle : typeAIndex y ηhi X ≤ k := by
    have := typeAIndex_le y ηhi X; omega
  have hltlo : ((j.succAbove i : Fin (k + 1)) : ℕ) < #(colouringEast y ηlo) := by
    have h2 := hI.card_colouringEast_of_eventType_A ha hb hN hX hPsw hev
    have := (j.succAbove i).isLt
    omega
  have hbot : componentBotIndex a b N y ηlo ((j.succAbove i : Fin (k + 1)) : ℕ)
      = componentBotIndex a b N y ηhi (i : ℕ) := by
    rw [componentBotIndex_eq ha hb hN hI.lo hlopos, componentBotIndex_eq ha hb hN hI.hi hhipos,
      hI.colStep_colouringNorth_lo_succAbove ha hb hN hηlo hy hPsw hev hkN j hj i,
      hI.levelIndex_lo_eq_hi_of_mem_colouringNorth_hi ha hN hX hPsw hev (colStep_mem hiN)]
  have htop : componentTopIndex a b N y ηlo ((j.succAbove i : Fin (k + 1)) : ℕ)
      = componentTopIndex a b N y ηhi (i : ℕ) := by
    rw [componentTopIndex_eq ha hb hN hI.lo hlopos hltlo,
      componentTopIndex_eq ha hb hN hI.hi hhipos hiE,
      hI.colStep_colouringEast_lo_succAbove ha hb hN hX hPsw hev hk j hj i]
  rw [braidDataOfColouring_snd, braidDataOfColouring_snd, componentCrossingIndices_eq_Icc,
    componentCrossingIndices_eq_Icc, hbot, htop]

/-! ### The positions -/

/-- **The inserted position is the normalised rank of the event point.** -/
theorem braidDataOfColouring_fst_typeAIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A) {k : ℕ}
    (j : Fin (k + 1)) (hj : (j : ℕ) = typeAIndex y ηhi X) :
    (braidDataOfColouring a b N y ηlo (k + 1)).1 j
      = levelPosition a b N ηlo ((pointRank a b N (X, Y) : ℤ) : ℚ) := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hlt : (j : ℕ) < #(colouringEast y ηlo) := by
    have h1 := typeAIndex_le y ηhi X
    have h2 := hI.card_colouringEast_of_eventType_A ha hb hN hX hPsw hev
    omega
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.lo hlopos j hlt, hj,
    hI.colStep_colouringEast_lo_typeAIndex ha hb hN hX hPsw hev]

/-- **The retained positions all rise by the one amount `HJO.Mellit.levelDropShift`.** They are the
normalised ranks of the same crossed east steps, read from the lower level instead of the upper one,
and `HJO.Mellit.levelPosition_eq_add_levelDropShift` is that change of level. The rigid-shift half
of the fourth identification. -/
theorem braidDataOfColouring_fst_succAbove (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin (k + 1)) (hj : (j : ℕ) = typeAIndex y ηhi X)
    (i : Fin k) :
    (braidDataOfColouring a b N y ηlo (k + 1)).1 (j.succAbove i)
      = (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hiE : (i : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact i.isLt
  have hltlo : ((j.succAbove i : Fin (k + 1)) : ℕ) < #(colouringEast y ηlo) := by
    have h2 := hI.card_colouringEast_of_eventType_A ha hb hN hX hPsw hev
    have := (j.succAbove i).isLt
    omega
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.lo hlopos _ hltlo,
    braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos i hiE,
    hI.colStep_colouringEast_lo_succAbove ha hb hN hX hPsw hev hk j hj i,
    levelPosition_eq_add_levelDropShift]

/-- **The inserted position lies strictly below every retained one.** This is the `hini` hypothesis
of `HJO.Mellit.braidValueOfData_succAbove_eq_dplus`, and it is free: the event point's rank is below
`ηhi` while every crossed east step of the *upper* colouring has rank above `ηhi`, and
`HJO.Mellit.levelPosition` is strictly increasing in the rank. So the insertion a type-`A` event
performs is a **bottom** insertion. -/
theorem braidDataOfColouring_fst_typeAIndex_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin (k + 1)) (hj : (j : ℕ) = typeAIndex y ηhi X)
    (i : Fin k) :
    (braidDataOfColouring a b N y ηlo (k + 1)).1 j
      < (braidDataOfColouring a b N y ηlo (k + 1)).1 (j.succAbove i) := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hiE : (i : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact i.isLt
  have hltlo : ((j.succAbove i : Fin (k + 1)) : ℕ) < #(colouringEast y ηlo) := by
    have h2 := hI.card_colouringEast_of_eventType_A ha hb hN hX hPsw hev
    have := (j.succAbove i).isLt
    omega
  have hrk : ηhi < ((pointRank a b N (colStep (colouringEast y ηhi) (i : ℕ)) : ℤ) : ℚ) :=
    (pointRank_lt_of_mem_colouringEast (a := a) (b := b) (N := N) (colStep_mem hiE)).2
  rw [hI.braidDataOfColouring_fst_typeAIndex ha hb hN hηlo hPsw hev j hj,
    braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.lo hlopos _ hltlo,
    hI.colStep_colouringEast_lo_succAbove ha hb hN hX hPsw hev hk j hj i]
  exact levelPosition_lt_levelPosition ha hb hN ηlo (hI.Plt.trans hrk)

/-! ### The width -/

/-- **The width at the event point is the upper rank.** `HJO.Mellit.liveSteps_eq_colouringNorth`
identifies the live north steps at a bracketed point with the upper colouring's north half, and
`HJO.Mellit.card_colouringNorth_eq_card_colouringEast` counts that half by the east one. So the
event operator of a type-`A` event, `dplus q (sweepWidth y P)`, is `dplus q k_hi` — exactly the
`d^♭_+` that `HJO.Mellit.braidValueOfData_succAbove_eq_dplus` produces. The fifth identification.

Nothing about the event type enters: the statement holds at every bracketed point of an
above-diagonal path. -/
theorem sweepWidth_eq_card_colouringEast (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) : sweepWidth y (X, Y) = #(colouringEast y ηhi) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  rw [sweepWidth, liveSteps_eq_colouringNorth hI y,
    card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]

end Isolates

end HJO.Mellit

end
