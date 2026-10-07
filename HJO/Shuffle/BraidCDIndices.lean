/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidColStepInsert
public import HJO.Shuffle.BraidCompParts
public import HJO.Shuffle.BraidTypeATransfer
public import HJO.Shuffle.BraidValueUnswept
public import HJO.Shuffle.BraidZCountDrop
public meta import HJO.Attr

/-! # The component endpoints across a type-`C` and a type-`D` level drop

`HJO/Shuffle/BraidZCountDrop.lean` proves the bookkeeping identity of a level drop — the change of
`HJO.Braid.zCount` is carried entirely by the component endpoint indices — and then states its
three predictions with those index families as **hypotheses**:

* `HJO.Mellit.zCount_eq_of_componentIndex_eq` (type `E`),
* `HJO.Mellit.zCount_sub_eq_zero_of_componentBotIndex_descends` (type `C`),
* `HJO.Mellit.zCount_sub_eq_one_of_componentTopIndex_ascends` (type `D`).

Deriving them means transporting `HJO.Mellit.Isolates.erase_colouringNorth` and
`HJO.Mellit.Isolates.erase_colouringEast` through the column listing `HJO.Mellit.colStep`, which is
not done there. The same holds of `HJO.Mellit.floor_crossingAbscissa_antidiag_lo`: the last sentence
of its clause (v) is read off `HJO.Mellit.Isolates.notMem_colouringNorth_lo` and is *not* formalized
there, having been checked outside Lean by enumeration for `a, b ≤ 4` and `N ≤ 3`.

**This file carries out that derivation.** It is the geometric input the type-`C` and the
type-`D` clauses of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` share, and the two clauses
read it in opposite halves of the colouring.

## One lemma does both halves

The two descent identities are single-point replacements of a column-injective set, and
`HJO.Mellit.colStep_replace` is the statement that such a replacement changes the column listing at
exactly one index — provided the new point sits in the same *place* in the column order, which is
the hypothesis `hord`. That hypothesis is discharged differently in the two cases and it is the
whole difference between them:

* at type `C` the north half replaces `(X, Y)` by `(X, Y - 1)` — the **same column**, so `hord` is
  `Iff.rfl`, and the listing changes only in the ordinate;
* at type `D` the east half replaces `(X - 1, Y)` by `(X, Y)` — the column **moves right by one**,
  and `hord` needs that no crossed east step of the upper level sits in column `X`. That is not an
  extra hypothesis: it follows from column-injectivity of the *lower* colouring, in which `(X, Y)`
  and any such step would share a column.

Both endpoint indices are then read off the listed point itself rather than through the level:
`HJO.Mellit.componentBotIndex_eq_add_snd` replaces the `levelIndex` of
`HJO.Mellit.componentBotIndex_eq` by the ordinate of the crossed north step, which
`HJO.Mellit.mem_colouringNorth_spec` says is the same integer, and
`HJO.Mellit.componentTopIndex_eq` is already in that form. So the four numbers
`HJO.Mellit.floor_crossingAbscissa_antidiag_lo` asks for come out as `X + Y ± 1` and `X + Y` by
arithmetic on the two listed points.

## What this closes and what it does not

It closes the geometric hypotheses of the two bookkeeping theorems, giving
`HJO.Mellit.zCount_sub_eq_zero_of_eventType_C` and `HJO.Mellit.zCount_sub_eq_one_of_eventType_D`
with **no hypothesis on the index families**: at a type-`C` drop the `z`-count is unchanged, at a
type-`D` drop it rises by exactly one. Read against `HJO.Mellit.card_componentCrossingIndices_eq` —
`HJO.Mellit.Isolates.totalCrossings_of_eventType_C` and its type-`D` twin, both `+1` — this is the
braid-side separation of `C` from `D`, now unconditional: **the move type `C` adds is a `ỹ` letter
and the move type `D` adds is a `z` letter.**

It does **not** close either clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`. What a
clause needs past this is the *value* of the added move under `HJO.Sweep.braidRep`, which is the
analogue of `HJO.Sweep.DplusIntertwines` at equal rank. The last section carries the geometry all
the way into the shape `HJO.Mellit.SweepRecursionACD` asks for and leaves each clause hanging
on **one** hypothesis, a braid-value identity with no geometry in it:
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_move` and
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_D_of_move`. Those `hmove`s
are the precise residuals, as Lean statements rather than prose.

## Genericity

None. Every statement here is about `ℕ`, `ℤ` and `ℚ` — the column listing, the level index and the
crossing indices — and no coefficient field appears. `0 < a`, `0 < b`, `0 < N` are the standing
nondegeneracy of the rectangle, and admissibility of the two levels is what makes the ordinate of a
crossed north step equal to its column's level index.

## References

Declarations involved: `HJO.Mellit.floor_crossingAbscissa_antidiag_lo` clause (v),
`HJO.Mellit.Isolates.notMem_colouringNorth_lo`, `HJO.Mellit.card_componentCrossingIndices_eq`,
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, `HJO.Mellit.braidDataOfColouring`,
`HJO.Mellit.colouring`, `HJO.Paths.eventType`. Transcribing A. Mellit, *Toric braids and
`(m, n)`-parking functions*, section 5.
-/

@[expose] public section

namespace HJO.Mellit

open Braid Finset ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### Replacing one point of a column-injective set -/

/-- **A single-point replacement changes the column listing at exactly one index.** Let `S` be
column-injective, `P ∈ S`, and let `P'` be a point outside `S.erase P` which sits in the same place
in the column order — `hord`: a retained point is left of `P` exactly when it is left of `P'`. Then
the listing of `insert P' (S.erase P)` agrees with that of `S` away from the index `i₀` of `P`, and
is `P'` there.

This is the transport `HJO.Mellit.floor_crossingAbscissa_antidiag_lo` needs: both descent identities
of `HJO.Mellit.Isolates.notMem_colouringNorth_lo` are of this shape, and `hord` is the only thing
that distinguishes the type-`C` replacement from the type-`D` one. -/
theorem colStep_replace {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) {P P' : ℕ × ℕ}
    (hP : P ∈ S) (hP' : P' ∉ S.erase P)
    (hcol' : ColumnInjective (insert P' (S.erase P)))
    (hord : ∀ Q ∈ S.erase P, (Q.1 < P.1 ↔ Q.1 < P'.1))
    {i₀ : ℕ} (hi₀ : i₀ < #S) (hPi₀ : colStep S i₀ = P) {i : ℕ} (hi : i < #S) :
    colStep (insert P' (S.erase P)) i = Function.update (colStep S) i₀ P' i := by
  classical
  have hcard : #(insert P' (S.erase P)) = #S := by
    have hpos : 0 < #S := Finset.card_pos.2 ⟨P, hP⟩
    rw [Finset.card_insert_of_notMem hP', Finset.card_erase_of_mem hP]
    omega
  -- no retained point shares a column with `P'`
  have hnew : ∀ Q ∈ S.erase P, Q.1 ≠ P'.1 := fun Q hQ hQ' =>
    hP' (hcol' Q (Finset.mem_insert_of_mem hQ) P' (Finset.mem_insert_self _ _) hQ' ▸ hQ)
  -- away from `i₀` the listing of `S` lands in the erased set
  have hmemT : ∀ j, j < #S → j ≠ i₀ → colStep S j ∈ S.erase P := by
    intro j hj hjne
    refine Finset.mem_erase.2 ⟨fun hc => hjne ?_, colStep_mem hj⟩
    refine colStep_injOn hcol ?_ ?_ (by rw [hc, hPi₀])
    · simp only [Finset.coe_range, Set.mem_Iio]; exact hj
    · simp only [Finset.coe_range, Set.mem_Iio]; exact hi₀
  refine colStep_eq_of_strictMono hcol' (g := Function.update (colStep S) i₀ P')
    (fun j hj => ?_) (fun j j' hjj' hj' => ?_) (by rw [hcard]; exact hi)
  · rw [hcard] at hj
    by_cases h : j = i₀
    · subst h; rw [Function.update_self]; exact Finset.mem_insert_self _ _
    · rw [Function.update_of_ne h]; exact Finset.mem_insert_of_mem (hmemT j hj h)
  · rw [hcard] at hj'
    have hj : j < #S := by omega
    by_cases h' : j' = i₀
    · -- the replaced point is on the right: `colStep S j` is left of `P`, hence left of `P'`
      subst h'
      have hne : j ≠ j' := by omega
      rw [Function.update_of_ne hne, Function.update_self]
      have hlt : (colStep S j).1 < P.1 := by
        rw [← hPi₀]; exact colStep_fst_lt hcol hj' hjj'
      exact (hord _ (hmemT j hj hne)).1 hlt
    · by_cases h : j = i₀
      · -- the replaced point is on the left: `colStep S j'` is right of `P`, hence right of `P'`
        subst h
        rw [Function.update_self, Function.update_of_ne h']
        have hlt : P.1 < (colStep S j').1 := by
          rw [← hPi₀]; exact colStep_fst_lt hcol hj' hjj'
        have hnotlt : ¬ (colStep S j').1 < P'.1 := fun hc =>
          absurd ((hord _ (hmemT j' hj' h')).2 hc) (by omega)
        have hne := hnew _ (hmemT j' hj' h')
        omega
      · rw [Function.update_of_ne h, Function.update_of_ne h']
        exact colStep_fst_lt hcol hj' hjj'

/-- The replaced point sits at the index the old one occupied. -/
theorem colStep_replace_self {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) {P P' : ℕ × ℕ}
    (hP : P ∈ S) (hP' : P' ∉ S.erase P)
    (hcol' : ColumnInjective (insert P' (S.erase P)))
    (hord : ∀ Q ∈ S.erase P, (Q.1 < P.1 ↔ Q.1 < P'.1))
    {i₀ : ℕ} (hi₀ : i₀ < #S) (hPi₀ : colStep S i₀ = P) :
    colStep (insert P' (S.erase P)) i₀ = P' := by
  rw [colStep_replace hcol hP hP' hcol' hord hi₀ hPi₀ hi₀, Function.update_self]

/-- Away from that index the listing is unchanged. -/
theorem colStep_replace_of_ne {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) {P P' : ℕ × ℕ}
    (hP : P ∈ S) (hP' : P' ∉ S.erase P)
    (hcol' : ColumnInjective (insert P' (S.erase P)))
    (hord : ∀ Q ∈ S.erase P, (Q.1 < P.1 ↔ Q.1 < P'.1))
    {i₀ : ℕ} (hi₀ : i₀ < #S) (hPi₀ : colStep S i₀ = P) {i : ℕ} (hi : i < #S) (hne : i ≠ i₀) :
    colStep (insert P' (S.erase P)) i = colStep S i := by
  rw [colStep_replace hcol hP hP' hcol' hord hi₀ hPi₀ hi, Function.update_of_ne hne]

/-! ### The bottom index read off the listed point -/

/-- **The bottom index of a component is `x(u_i) + y(u_i) + 1`**, the sum of the coordinates of its
crossed north step plus one — the same shape `HJO.Mellit.componentTopIndex_eq` gives the top index.
`HJO.Mellit.componentBotIndex_eq` states it with the column's level index in place of the ordinate,
and `HJO.Mellit.mem_colouringNorth_spec` says those are the same integer. In this form the level has
disappeared from the right-hand side, so two levels with the same listed point have the same bottom
index. -/
theorem componentBotIndex_eq_add_snd (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) (y : Heights a b N) {i : ℕ}
    (hi : i < #(colouringNorth y η)) :
    componentBotIndex a b N y η i =
      ((colStep (colouringNorth y η) i).1 : ℤ) + ((colStep (colouringNorth y η) i).2 : ℤ) + 1 := by
  rw [componentBotIndex_eq ha hb hN hη hηpos y i,
    ← (mem_colouringNorth_spec ha hN hη y (colStep_mem hi)).2.2.2]

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### Type `C`: every top index stands still and one bottom index falls -/

/-- **At an event of type `C` every top index stands still.** The crossed east steps are literally
the same set at the two levels (`HJO.Mellit.Isolates.colouringEast_eq_of_eventType_C`), so the
column listing is the same and `HJO.Mellit.componentTopIndex_eq` reads the same integer off it. -/
theorem componentTopIndex_eq_of_eventType_C (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hlopos : 0 < ηlo) (hhipos : 0 < ηhi)
    {y : Heights a b N} (hev : eventType y (X, Y) = EventType.C) {i : ℕ}
    (hi : i < #(colouringEast y ηhi)) :
    componentTopIndex a b N y ηlo i = componentTopIndex a b N y ηhi i := by
  have hE := hI.colouringEast_eq_of_eventType_C ha hN hev
  have hilo : i < #(colouringEast y ηlo) := by rw [hE]; exact hi
  rw [componentTopIndex_eq ha hb hN hI.lo hlopos hilo,
    componentTopIndex_eq ha hb hN hI.hi hhipos hi, hE]

/-- **The listing of the crossed north steps at a type-`C` drop**: it is the upper one with the
point of column `X` dropped one lattice point, and unchanged at every other index. The replacement
is within one column, so `HJO.Mellit.colStep_replace` applies with `hord` trivial. -/
theorem colStep_colouringNorth_of_eventType_C (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.C) {i₀ : ℕ} (hi₀ : i₀ < #(colouringNorth y ηhi))
    (hPi₀ : colStep (colouringNorth y ηhi) i₀ = (X, Y)) {i : ℕ}
    (hi : i < #(colouringNorth y ηhi)) :
    colStep (colouringNorth y ηlo) i =
      Function.update (colStep (colouringNorth y ηhi)) i₀ ((X, Y - 1) : ℕ × ℕ) i := by
  obtain ⟨hht, hX, hht'⟩ := ht_lt_of_eventType_C hev
  have hY : 0 < Y := by omega
  have hset := hI.colouringNorth_eq_of_eventType_C ha hN hev
  have hP' : ((X, Y - 1) : ℕ × ℕ) ∉ (colouringNorth y ηhi).erase (X, Y) := fun h =>
    (hI.notMem_colouringNorth_pred_hi hY y) (Finset.mem_of_mem_erase h)
  have hcol' : ColumnInjective (insert ((X, Y - 1) : ℕ × ℕ)
      ((colouringNorth y ηhi).erase (X, Y))) := by
    rw [← hset]; exact columnInjective_colouringNorth ha hN hI.lo y
  rw [hset]
  exact colStep_replace (columnInjective_colouringNorth ha hN hI.hi y)
    (hI.mem_colouringNorth_hi_of_eventType_C ha hN hev) hP' hcol'
    (fun Q _ => Iff.rfl) hi₀ hPi₀ hi

/-- **The three bottom-index facts a type-`C` drop supplies**, which are exactly the hypotheses
`hbot`, `hbothi`, `hbotlo` of
`HJO.Mellit.zCount_sub_eq_zero_of_componentBotIndex_descends`: away from the one index the bottom
index is unchanged, and at that index it falls from `n_P + 1` to `n_P`. -/
theorem componentBotIndex_of_eventType_C (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hlopos : 0 < ηlo) (hhipos : 0 < ηhi)
    {y : Heights a b N} (hev : eventType y (X, Y) = EventType.C) {i₀ : ℕ}
    (hi₀ : i₀ < #(colouringNorth y ηhi))
    (hPi₀ : colStep (colouringNorth y ηhi) i₀ = (X, Y)) :
    (∀ i < #(colouringNorth y ηhi), i ≠ i₀ →
        componentBotIndex a b N y ηlo i = componentBotIndex a b N y ηhi i) ∧
      componentBotIndex a b N y ηhi i₀ = (X : ℤ) + (Y : ℤ) + 1 ∧
      componentBotIndex a b N y ηlo i₀ = (X : ℤ) + (Y : ℤ) := by
  obtain ⟨hht, hX, hht'⟩ := ht_lt_of_eventType_C hev
  have hY : 0 < Y := by omega
  have hcardN := hI.card_colouringNorth_of_eventType_C ha hN hev
  refine ⟨fun i hi hne => ?_, ?_, ?_⟩
  · have hilo : i < #(colouringNorth y ηlo) := by rw [hcardN]; exact hi
    rw [componentBotIndex_eq_add_snd ha hb hN hI.lo hlopos y hilo,
      componentBotIndex_eq_add_snd ha hb hN hI.hi hhipos y hi,
      hI.colStep_colouringNorth_of_eventType_C ha hN hev hi₀ hPi₀ hi,
      Function.update_of_ne hne]
  · rw [componentBotIndex_eq_add_snd ha hb hN hI.hi hhipos y hi₀, hPi₀]
  · have hi₀lo : i₀ < #(colouringNorth y ηlo) := by rw [hcardN]; exact hi₀
    rw [componentBotIndex_eq_add_snd ha hb hN hI.lo hlopos y hi₀lo,
      hI.colStep_colouringNorth_of_eventType_C ha hN hev hi₀ hPi₀ hi₀, Function.update_self]
    have : ((Y - 1 : ℕ) : ℤ) = (Y : ℤ) - 1 := by omega
    simp only
    rw [this]
    ring

/-! ### Type `D`: every bottom index stands still and one top index rises -/

/-- **At an event of type `D` every bottom index stands still.** The crossed north steps are
literally the same set at the two levels
(`HJO.Mellit.Isolates.colouringNorth_eq_of_eventType_D`), and
`HJO.Mellit.componentBotIndex_eq_add_snd` reads the bottom index off the listed point alone — the
level having been eliminated there, which is why the level index needed no comparison. -/
theorem componentBotIndex_eq_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hlopos : 0 < ηlo) (hhipos : 0 < ηhi) (hX : X < a * N)
    {y : Heights a b N} (hev : eventType y (X, Y) = EventType.D) {i : ℕ}
    (hi : i < #(colouringNorth y ηhi)) :
    componentBotIndex a b N y ηlo i = componentBotIndex a b N y ηhi i := by
  have hset := hI.colouringNorth_eq_of_eventType_D ha hN hX hev
  have hilo : i < #(colouringNorth y ηlo) := by rw [hset]; exact hi
  rw [componentBotIndex_eq_add_snd ha hb hN hI.lo hlopos y hilo,
    componentBotIndex_eq_add_snd ha hb hN hI.hi hhipos y hi, hset]

/-- **The listing of the crossed east steps at a type-`D` drop**: it is the upper one with the point
of ordinate `Y` moved one column right, and unchanged at every other index.

The order hypothesis of `HJO.Mellit.colStep_replace` is the only work. It asks that a retained
crossed east step be left of column `X - 1` exactly when it is left of column `X`, that is that none
of them sits in column `X - 1` — which is column-injectivity of the upper colouring — or in column
`X`, which is column-injectivity of the **lower** one, where `(X, Y)` already sits there. -/
theorem colStep_colouringEast_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hX : X < a * N)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D)
    {i₀ : ℕ} (hi₀ : i₀ < #(colouringEast y ηhi))
    (hPi₀ : colStep (colouringEast y ηhi) i₀ = (X - 1, Y)) {i : ℕ}
    (hi : i < #(colouringEast y ηhi)) :
    colStep (colouringEast y ηlo) i =
      Function.update (colStep (colouringEast y ηhi)) i₀ ((X, Y) : ℕ × ℕ) i := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_D hηlo hy hev
  have hset := hI.colouringEast_eq_of_eventType_D ha hb hN hX hy hev
  have hP' : ((X, Y) : ℕ × ℕ) ∉ (colouringEast y ηhi).erase (X - 1, Y) := fun h =>
    (hI.notMem_colouringEast_hi y) (Finset.mem_of_mem_erase h)
  have hcol' : ColumnInjective (insert ((X, Y) : ℕ × ℕ)
      ((colouringEast y ηhi).erase (X - 1, Y))) := by
    rw [← hset]; exact columnInjective_colouringEast ha hN hI.lo y
  have hcolhi := columnInjective_colouringEast ha hN hI.hi y
  have hord : ∀ Q ∈ (colouringEast y ηhi).erase (X - 1, Y),
      (Q.1 < (((X - 1, Y) : ℕ × ℕ)).1 ↔ Q.1 < (((X, Y) : ℕ × ℕ)).1) := by
    intro Q hQ
    -- `Q` is not in column `X - 1`: that is where the erased point sits
    have hne1 : Q.1 ≠ X - 1 := fun hc =>
      (Finset.mem_erase.1 hQ).1 (hcolhi Q (Finset.mem_of_mem_erase hQ) (X - 1, Y)
        (hPi₀ ▸ colStep_mem hi₀) hc)
    -- `Q` is not in column `X`: that is where the inserted point sits
    have hne2 : Q.1 ≠ X := fun hc =>
      hP' (hcol' Q (Finset.mem_insert_of_mem hQ) (X, Y) (Finset.mem_insert_self _ _) hc ▸ hQ)
    simp only
    omega
  rw [hset]
  exact colStep_replace hcolhi (hPi₀ ▸ colStep_mem hi₀) hP' hcol' hord hi₀ hPi₀ hi

/-- **The three top-index facts a type-`D` drop supplies**, which are exactly the hypotheses `htop`,
`htophi`, `htoplo` of `HJO.Mellit.zCount_sub_eq_one_of_componentTopIndex_ascends`: away from the one
index the top index is unchanged, and at that index it rises from `n_P - 1` to `n_P`. -/
theorem componentTopIndex_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hhipos : 0 < ηhi)
    (hX : X < a * N) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.D) {i₀ : ℕ} (hi₀ : i₀ < #(colouringEast y ηhi))
    (hPi₀ : colStep (colouringEast y ηhi) i₀ = (X - 1, Y)) :
    (∀ i < #(colouringEast y ηhi), i ≠ i₀ →
        componentTopIndex a b N y ηlo i = componentTopIndex a b N y ηhi i) ∧
      componentTopIndex a b N y ηhi i₀ = (X : ℤ) + (Y : ℤ) - 1 ∧
      componentTopIndex a b N y ηlo i₀ = (X : ℤ) + (Y : ℤ) := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_D hηlo hy hev
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hcardE : #(colouringEast y ηlo) = #(colouringEast y ηhi) := by
    rw [hI.colouringEast_eq_of_eventType_D ha hb hN hX hy hev,
      Finset.card_insert_of_notMem (fun h =>
        (hI.notMem_colouringEast_hi y) (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem (hPi₀ ▸ colStep_mem hi₀)]
    have hpos : 0 < #(colouringEast y ηhi) := by omega
    omega
  refine ⟨fun i hi hne => ?_, ?_, ?_⟩
  · have hilo : i < #(colouringEast y ηlo) := by rw [hcardE]; exact hi
    rw [componentTopIndex_eq ha hb hN hI.lo hlopos hilo,
      componentTopIndex_eq ha hb hN hI.hi hhipos hi,
      hI.colStep_colouringEast_of_eventType_D ha hb hN hηlo hX hy hev hi₀ hPi₀ hi,
      Function.update_of_ne hne]
  · rw [componentTopIndex_eq ha hb hN hI.hi hhipos hi₀, hPi₀]
    have : ((X - 1 : ℕ) : ℤ) = (X : ℤ) - 1 := by omega
    simp only
    rw [this]
    ring
  · have hi₀lo : i₀ < #(colouringEast y ηlo) := by rw [hcardE]; exact hi₀
    rw [componentTopIndex_eq ha hb hN hI.lo hlopos hi₀lo,
      hI.colStep_colouringEast_of_eventType_D ha hb hN hηlo hX hy hev hi₀ hPi₀ hi₀,
      Function.update_self]

end Isolates

/-! ### The multiplicity of a component, from its two endpoint indices -/

/-- The multiplicity `α_i` of `HJO.Mellit.braidDataOfColouring` is `T_i - B_i + 1`: the crossings of
a component are the integers of `Finset.Icc B_i T_i`. -/
theorem braidDataOfColouring_snd_eq_toNat (a b N : ℕ) (y : Heights a b N) (η : ℚ) (k : ℕ)
    (i : Fin k) :
    (braidDataOfColouring a b N y η k).2 i
      = (componentTopIndex a b N y η i + 1 - componentBotIndex a b N y η i).toNat := by
  rw [braidDataOfColouring_snd, componentCrossingIndices_eq_Icc, Int.card_Icc]

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The data-level dictionary of a type-`C` drop -/

/-- **At a type-`C` drop the multiplicity rises by one at the one index and nowhere else.** Only the
*sum* of the multiplicities was known before (`HJO.Mellit.Isolates.totalCrossings_of_eventType_C`);
this is the index-by-index statement, which is what `HJO.Braid.specialBraid` reads. The component
whose multiplicity rises is the one whose crossed north step dropped a lattice point, and it gains
its crossing at the **bottom** of its interval, the top index standing still. -/
theorem braidData_snd_of_eventType_C_of_ne (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {i₀ : ℕ}
    (hi₀ : i₀ < #(colouringNorth y ηhi))
    (hPi₀ : colStep (colouringNorth y ηhi) i₀ = (X, Y)) {k : ℕ} (i : Fin k)
    (hik : (i : ℕ) < #(colouringNorth y ηhi)) (hne : (i : ℕ) ≠ i₀) :
    (braidDataOfColouring a b N y ηlo k).2 i = (braidDataOfColouring a b N y ηhi k).2 i := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hiE : (i : ℕ) < #(colouringEast y ηhi) := by
    rw [← card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hik
  have htop := hI.componentTopIndex_eq_of_eventType_C ha hb hN hlopos hhipos hev hiE
  obtain ⟨hbotne, -, -⟩ :=
    hI.componentBotIndex_of_eventType_C ha hb hN hlopos hhipos hev hi₀ hPi₀
  rw [braidDataOfColouring_snd_eq_toNat, braidDataOfColouring_snd_eq_toNat, htop,
    hbotne (i : ℕ) hik hne]

/-- **At the one index of a type-`C` drop the multiplicity rises by exactly one.** The top index
stands still and the bottom index falls by one, so the component gains a crossing at the bottom of
its interval. -/
theorem braidData_snd_succ_of_eventType_C (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {i₀ : ℕ}
    (hi₀ : i₀ < #(colouringNorth y ηhi))
    (hPi₀ : colStep (colouringNorth y ηhi) i₀ = (X, Y)) {k : ℕ} (i : Fin k)
    (heq : (i : ℕ) = i₀) :
    (braidDataOfColouring a b N y ηlo k).2 i = (braidDataOfColouring a b N y ηhi k).2 i + 1 := by
  subst heq
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hcardN := hI.card_colouringNorth_of_eventType_C ha hN hev
  have hiE : (i : ℕ) < #(colouringEast y ηhi) := by
    rw [← card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hi₀
  have htop := hI.componentTopIndex_eq_of_eventType_C ha hb hN hlopos hhipos hev hiE
  obtain ⟨-, hbothi, hbotlo⟩ :=
    hI.componentBotIndex_of_eventType_C ha hb hN hlopos hhipos hev hi₀ hPi₀
  have hle : componentBotIndex a b N y ηlo (i : ℕ) ≤ componentTopIndex a b N y ηlo (i : ℕ) :=
    componentBotIndex_le_componentTopIndex ha hb hN hI.lo hηlo hy (by rw [hcardN]; exact hi₀)
  rw [hbotlo, htop] at hle
  rw [braidDataOfColouring_snd_eq_toNat, braidDataOfColouring_snd_eq_toNat, htop, hbothi, hbotlo]
  omega

/-- **At a type-`C` drop every position rises by the one common amount
`HJO.Mellit.levelDropShift`, with no fractional part taken.** The crossed east steps stand still, so
the position is the same function of the same point at the two levels, and
`HJO.Mellit.levelPosition_eq_add_levelDropShift` is an honest addition. This is the form
`HJO.Mellit.braidValueOfData_congr_add` consumes; `HJO.Mellit.Isolates.braidData_fst_of_eventType_C`
is the same fact with a `Int.fract` around it. -/
theorem braidData_fst_eq_add_of_eventType_C (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hlopos : 0 < ηlo) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.C) {k : ℕ} (i : Fin k)
    (hi : (i : ℕ) < #(colouringEast y ηhi)) :
    (braidDataOfColouring a b N y ηlo k).1 i
      = (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi := by
  have hE := hI.colouringEast_eq_of_eventType_C ha hN hev
  have hhipos : 0 < ηhi := hlopos.trans (hI.ltP.trans hI.Plt)
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.lo hlopos i (by rwa [hE]),
    braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos i hi, hE,
    levelPosition_eq_add_levelDropShift]

/-! ### The data-level dictionary of a type-`D` drop -/

/-- **At a type-`D` drop the multiplicity rises by one at the one index and nowhere else**, the
component gaining its crossing at the **top** of its interval. The index-by-index companion of
`HJO.Mellit.Isolates.totalCrossings_of_eventType_D`. -/
theorem braidData_snd_of_eventType_D_of_ne (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {i₀ : ℕ}
    (hi₀ : i₀ < #(colouringEast y ηhi))
    (hPi₀ : colStep (colouringEast y ηhi) i₀ = (X - 1, Y)) {k : ℕ} (i : Fin k)
    (hik : (i : ℕ) < #(colouringEast y ηhi)) (hne : (i : ℕ) ≠ i₀) :
    (braidDataOfColouring a b N y ηlo k).2 i = (braidDataOfColouring a b N y ηhi k).2 i := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hikN : (i : ℕ) < #(colouringNorth y ηhi) := by
    rwa [← card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy] at hik
  have hbot := hI.componentBotIndex_eq_of_eventType_D ha hb hN hlopos hhipos hX hev hikN
  obtain ⟨htopne, -, -⟩ :=
    hI.componentTopIndex_of_eventType_D ha hb hN hηlo hhipos hX hy hev hi₀ hPi₀
  rw [braidDataOfColouring_snd_eq_toNat, braidDataOfColouring_snd_eq_toNat, hbot,
    htopne (i : ℕ) hik hne]

/-- **At the one index of a type-`D` drop the multiplicity rises by exactly one.** The bottom index
stands still and the top index rises by one, so the component gains a crossing at the top of its
interval — the opposite end from type `C`. -/
theorem braidData_snd_succ_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {i₀ : ℕ}
    (hi₀ : i₀ < #(colouringEast y ηhi))
    (hPi₀ : colStep (colouringEast y ηhi) i₀ = (X - 1, Y)) {k : ℕ} (i : Fin k)
    (heq : (i : ℕ) = i₀) :
    (braidDataOfColouring a b N y ηlo k).2 i = (braidDataOfColouring a b N y ηhi k).2 i + 1 := by
  subst heq
  have hX : X < a * N := hI.fst_lt hηlo
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hikN : (i : ℕ) < #(colouringNorth y ηhi) := by
    rwa [← card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy] at hi₀
  have hbot := hI.componentBotIndex_eq_of_eventType_D ha hb hN hlopos hhipos hX hev hikN
  obtain ⟨-, htophi, htoplo⟩ :=
    hI.componentTopIndex_of_eventType_D ha hb hN hηlo hhipos hX hy hev hi₀ hPi₀
  have hle : componentBotIndex a b N y ηhi (i : ℕ) ≤ componentTopIndex a b N y ηhi (i : ℕ) :=
    componentBotIndex_le_componentTopIndex ha hb hN hI.hi hηhi hy hikN
  rw [htophi] at hle
  rw [braidDataOfColouring_snd_eq_toNat, braidDataOfColouring_snd_eq_toNat, hbot, htophi, htoplo]
  omega

/-- **A type-`D` drop leaves the rank alone**: the crossed north steps stand still, and the two
halves of a colouring have the same cardinality. -/
theorem card_colouringEast_eq_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) :
    #(colouringEast y ηlo) = #(colouringEast y ηhi) := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  rw [← card_colouringNorth_eq_card_colouringEast hb hN hI.lo hηlo hy,
    ← card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy,
    hI.colouringNorth_eq_of_eventType_D ha hN hX hev]

/-- **At a type-`D` drop the one moving position advances by a further `θ`.** Away from the index
`i₀` the position rises by the common `HJO.Mellit.levelDropShift` alone; at `i₀` the component's top
crossing index rises by one (`HJO.Mellit.Isolates.componentTopIndex_of_eventType_D`), so by
`HJO.Mellit.crossingAbscissa_succ_eq_add` its abscissa moves a further step `θ`. This is the
asymmetry the left side records as the bare `q^{a}` against type `C`'s `q^{-a}Δ`. -/
theorem braidData_fst_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {i₀ : ℕ}
    (hi₀ : i₀ < #(colouringEast y ηhi))
    (hPi₀ : colStep (colouringEast y ηhi) i₀ = (X - 1, Y)) {k : ℕ} (i : Fin k)
    (hik : (i : ℕ) < #(colouringEast y ηhi)) (hne : (i : ℕ) ≠ i₀) :
    (braidDataOfColouring a b N y ηlo k).1 i
      = (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hcardE : #(colouringEast y ηlo) = #(colouringEast y ηhi) := by
    rw [← card_colouringNorth_eq_card_colouringEast hb hN hI.lo hηlo hy,
      ← card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy,
      hI.colouringNorth_eq_of_eventType_D ha hN hX hev]
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.lo hlopos i
      (by rw [hcardE]; exact hik),
    braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos i hik,
    hI.colStep_colouringEast_of_eventType_D ha hb hN hηlo hX hy hev hi₀ hPi₀ hik,
    Function.update_of_ne hne, levelPosition_eq_add_levelDropShift]

/-- **The rigid rotation of a level drop, with every fraction cleared**: `(η₊ − η₋)/D`. This is
`HJO.Mellit.crossingAbscissa_sub_crossingAbscissa` read as a statement about
`HJO.Mellit.levelDropShift`, which is the same number written through `θ`. -/
theorem levelDropShift_eq_div (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (ηlo ηhi : ℚ) :
    levelDropShift a b N ηlo ηhi = (ηhi - ηlo) / crossingDen a b N := by
  have hD := (crossingDen_pos ha hb hN).ne'
  have haM : ((a : ℚ) * ((a : ℚ) * N + 1) * N) ≠ 0 := by
    have ha' : (0 : ℚ) < a := by exact_mod_cast ha
    have hN' : (0 : ℚ) < N := by exact_mod_cast hN
    positivity
  rw [levelDropShift, sweepTheta_eq_div ha hb hN]
  push_cast at haM ⊢
  field_simp

/-- **At the one index of a type-`D` drop the position advances by `θ` beyond the rotation.** The
component's top crossing index rises by one, so its abscissa moves by `θ` on top of the common shift
— and the fractional part is what `HJO.Mellit.braidDataOfColouring` reads, so the value **wraps**
when that carries it past `1`. That wrap is exactly the extra `z` letter of
`HJO.Mellit.Isolates.zCount_sub_eq_one_of_eventType_D`. -/
theorem braidData_fst_succ_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {i₀ : ℕ}
    (hi₀ : i₀ < #(colouringEast y ηhi))
    (hPi₀ : colStep (colouringEast y ηhi) i₀ = (X - 1, Y)) {k : ℕ} (i : Fin k)
    (heq : (i : ℕ) = i₀) :
    (braidDataOfColouring a b N y ηlo k).1 i
      = Int.fract ((braidDataOfColouring a b N y ηhi k).1 i
          + levelDropShift a b N ηlo ηhi + sweepTheta a b N) := by
  subst heq
  have hX : X < a * N := hI.fst_lt hηlo
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  obtain ⟨-, htophi, htoplo⟩ :=
    hI.componentTopIndex_of_eventType_D ha hb hN hηlo hhipos hX hy hev hi₀ hPi₀
  have htoplo' : componentTopIndex a b N y ηlo (i : ℕ) = ((X : ℤ) + (Y : ℤ) - 1) + 1 := by
    rw [htoplo]; ring
  have hlhs : (braidDataOfColouring a b N y ηlo k).1 i
      = Int.fract (crossingAbscissa a b N ηhi ((X : ℤ) + (Y : ℤ) - 1) + sweepTheta a b N
          + (ηhi - ηlo) / crossingDen a b N) := by
    rw [braidDataOfColouring_fst, htoplo',
      crossingAbscissa_succ_eq_add ha hb hN ηlo ηhi ((X : ℤ) + (Y : ℤ) - 1)]
  have hrhs : (braidDataOfColouring a b N y ηhi k).1 i
      = Int.fract (crossingAbscissa a b N ηhi ((X : ℤ) + (Y : ℤ) - 1)) := by
    rw [braidDataOfColouring_fst, htophi]
  rw [hlhs, hrhs, levelDropShift_eq_div ha hb hN,
    show Int.fract (crossingAbscissa a b N ηhi ((X : ℤ) + (Y : ℤ) - 1))
          + (ηhi - ηlo) / crossingDen a b N + sweepTheta a b N
        = Int.fract (crossingAbscissa a b N ηhi ((X : ℤ) + (Y : ℤ) - 1))
          + ((ηhi - ηlo) / crossingDen a b N + sweepTheta a b N) by ring,
    fract_fract_add]
  ring_nf

/-! ### The two `z`-count predictions, with no hypothesis on the index families -/

/-- **At a type-`C` drop the `z`-count of the colouring's special braid is unchanged**, with the
event type as the only geometric hypothesis. This is
`HJO.Mellit.zCount_sub_eq_zero_of_componentBotIndex_descends` with its four index hypotheses
discharged by `HJO.Mellit.Isolates.componentTopIndex_eq_of_eventType_C` and
`HJO.Mellit.Isolates.componentBotIndex_of_eventType_C`.

Read against `HJO.Mellit.Isolates.totalCrossings_of_eventType_C`, whose type-`C` row is `+1` move:
**the move a type-`C` drop adds is a `ỹ` letter.** -/
theorem zCount_sub_eq_zero_of_eventType_C (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi = ηlo + 1)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C)
    (hklo : 1 ≤ #(colouringNorth y ηlo)) (hkhi : 1 ≤ #(colouringNorth y ηhi)) :
    (zCount #(colouringNorth y ηlo) hklo (specialBraid (sweepTheta a b N)
        (braidDataOfColouring a b N y ηlo #(colouringNorth y ηlo)).1
        (braidDataOfColouring a b N y ηlo #(colouringNorth y ηlo)).2) : ℤ)
      - (zCount #(colouringNorth y ηhi) hkhi (specialBraid (sweepTheta a b N)
          (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).1
          (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).2) : ℤ) = 0 := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  obtain ⟨i₀, hi₀, hPi₀⟩ := exists_colStep (hI.mem_colouringNorth_hi_of_eventType_C ha hN hev)
  obtain ⟨hbotne, hbothi, hbotlo⟩ :=
    hI.componentBotIndex_of_eventType_C ha hb hN hlopos hhipos hev hi₀ hPi₀
  exact zCount_sub_eq_zero_of_componentBotIndex_descends ha hb hN hI.lo hI.hi hηlo hstep hy
    (hI.card_colouringNorth_of_eventType_C ha hN hev) hklo hkhi hI.ltP hI.Plt
    (fun i hi => hI.componentTopIndex_eq_of_eventType_C ha hb hN hlopos hhipos hev
      (by rwa [← card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]))
    hbotne hbothi hbotlo

/-- **At a type-`D` drop the `z`-count of the colouring's special braid rises by exactly one**, with
the event type as the only geometric hypothesis. This is
`HJO.Mellit.zCount_sub_eq_one_of_componentTopIndex_ascends` with its four index hypotheses
discharged by `HJO.Mellit.Isolates.componentBotIndex_eq_of_eventType_D` and
`HJO.Mellit.Isolates.componentTopIndex_of_eventType_D`.

Read against `HJO.Mellit.Isolates.totalCrossings_of_eventType_D`, also `+1` move: **the move a
type-`D` drop adds is a `z` letter.** With the type-`C` twin this is the braid-side separation of
`C` from `D`, now carrying no hypothesis beyond the event. -/
theorem zCount_sub_eq_one_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi = ηlo + 1)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D)
    (hklo : 1 ≤ #(colouringNorth y ηlo)) (hkhi : 1 ≤ #(colouringNorth y ηhi)) :
    (zCount #(colouringNorth y ηlo) hklo (specialBraid (sweepTheta a b N)
        (braidDataOfColouring a b N y ηlo #(colouringNorth y ηlo)).1
        (braidDataOfColouring a b N y ηlo #(colouringNorth y ηlo)).2) : ℤ)
      - (zCount #(colouringNorth y ηhi) hkhi (specialBraid (sweepTheta a b N)
          (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).1
          (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).2) : ℤ) = 1 := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hX0 : 0 < X := hI.pos_fst_of_eventType_D hηlo hy hev
  have hcardEq := card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy
  obtain ⟨i₀, hi₀, hPi₀⟩ :=
    exists_colStep (hI.mem_colouringEast_pred_hi_of_eventType_D ha hb hN hX0 hev)
  obtain ⟨htopne, htophi, htoplo⟩ :=
    hI.componentTopIndex_of_eventType_D ha hb hN hηlo hhipos hX hy hev hi₀ hPi₀
  refine zCount_sub_eq_one_of_componentTopIndex_ascends ha hb hN hI.lo hI.hi hηlo hstep hy
    (by rw [hI.colouringNorth_eq_of_eventType_D ha hN hX hev]) hklo hkhi hI.ltP hI.Plt
    (by rw [hcardEq]; exact hi₀)
    (fun i hi => hI.componentBotIndex_eq_of_eventType_D ha hb hN hlopos hhipos hX hev hi)
    (fun i hi hne => htopne i (by rwa [← hcardEq]) hne) htophi htoplo

/-! ### The two clauses, each reduced to one named residual

Everything above is geometry: `ℕ`, `ℤ` and `ℚ`. The two theorems below carry that geometry into the
shape `HJO.Mellit.SweepRecursionACD` asks for, and what is left of each clause is the **single
hypothesis `hmove`** — a braid-value identity between two special-braid data, the upper one and the
upper one with a rigid rotation applied and one multiplicity raised by one.

**`hmove` is equivalent to the clause at each instance, not weaker than it**, the chain from one to
the other being a chain of equalities; nothing here claims to have made the clause easier. What the
reduction buys is that the *geometry is gone* from `hmove`: no colouring, no `HJO.Mellit.colStep`,
no event type and no crossing index appears in it. The only quantity it still reads off the path is
the
integer exponent `a_{P̂}(P)` of `HJO.Paths.sweepRight`, which the event operator of
`HJO.Mellit.sweepOperator` reads too.

So the residual of each clause is the analogue of `HJO.Sweep.DplusIntertwines` at **equal** rank:
at type `C` the added move must implement `q^{-a}Δ` and at type `D` the bare `q^{a}`. By
`HJO.Mellit.Isolates.zCount_sub_eq_zero_of_eventType_C` and
`HJO.Mellit.Isolates.zCount_sub_eq_one_of_eventType_D` the added letter is a `ỹ` in the first case
and a `z` in the second, which is the only braid-side separation of the two available. -/

section Residual

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The type-`C` clause, reduced to one braid-value identity.** Every geometric hypothesis of the
`A`/`C`/`D` clause of `HJO.Mellit.SweepRecursionACD` at a type-`C` event is discharged: the rank is
the same at the two levels, the positions are the upper ones rigidly rotated by
`HJO.Mellit.levelDropShift`, and the multiplicities are the upper ones with the single index `j`
raised by one — `j` being the component whose crossed north step dropped a lattice point.

What is left is `hmove`, and nothing else. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_C_of_move (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C)
    {k : ℕ} (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y))
    (hmove : braidValueOfData q u hq hq1 hqp hr a b N
        (fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi)
        (Function.update (braidDataOfColouring a b N y ηhi k).2 j
          ((braidDataOfColouring a b N y ηhi k).2 j + 1))
      = q ^ (-(sweepRight y (X, Y) : ℤ)) • corner q k
          (braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηhi k).1
            (braidDataOfColouring a b N y ηhi k).2)) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hklo : #(colouringEast y ηlo) = k := by
    rw [hI.colouringEast_eq_of_eventType_C ha hN hev]; exact hk
  have hjlt : (j : ℕ) < #(colouringNorth y ηhi) := by rw [hkN]; exact j.isLt
  have hfst : (braidDataOfColouring a b N y ηlo k).1
      = fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi :=
    funext fun i => hI.braidData_fst_eq_add_of_eventType_C ha hb hN hlopos hev i
      (by rw [hk]; exact i.isLt)
  have hsnd : (braidDataOfColouring a b N y ηlo k).2
      = Function.update (braidDataOfColouring a b N y ηhi k).2 j
          ((braidDataOfColouring a b N y ηhi k).2 j + 1) := by
    funext i
    by_cases h : i = j
    · subst h
      rw [Function.update_self]
      exact hI.braidData_snd_succ_of_eventType_C ha hb hN hηlo hy hev hjlt hj i rfl
    · rw [Function.update_of_ne h]
      exact hI.braidData_snd_of_eventType_C_of_ne ha hb hN hηlo hy hev hjlt hj i
        (by rw [hkN]; exact i.isLt) (fun hc => h (Fin.ext hc))
  rw [braidValueColouring_colouring q u hq hq1 hqp hr hy,
    braidValueColouring_colouring q u hq hq1 hqp hr hy, sweepOperator_of_eventType_C y hev,
    hI.sweepWidth_eq_card_colouringEast hb hN hηlo hy, hk,
    braidValueOfPath_eq_braidValueOfData q u hq hq1 hqp hr y ηlo hklo,
    braidValueOfPath_eq_braidValueOfData q u hq hq1 hqp hr y ηhi hk, hfst, hsnd]
  exact hmove

/-- **The type-`D` clause, reduced to one braid-value identity.** The same reduction as at type `C`,
with the two differences the geometry records: the index `j` is the component whose crossed **east**
step moved a column right, and its position advances by a further `θ` on top of the rotation — and
that value is a *fractional part*, so it wraps when the advance carries it past `1`.

What is left is `hmove`, and nothing else. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_D_of_move (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D)
    {k : ℕ} (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y))
    (hmove : braidValueOfData q u hq hq1 hqp hr a b N
        (Function.update
          (fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi) j
          (Int.fract ((braidDataOfColouring a b N y ηhi k).1 j
            + levelDropShift a b N ηlo ηhi + sweepTheta a b N)))
        (Function.update (braidDataOfColouring a b N y ηhi k).2 j
          ((braidDataOfColouring a b N y ηhi k).2 j + 1))
      = q ^ (sweepRight y (X, Y)) •
          braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηhi k).1
            (braidDataOfColouring a b N y ηhi k).2) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  have hklo : #(colouringEast y ηlo) = k := by
    rw [hI.card_colouringEast_eq_of_eventType_D ha hb hN hηlo hy hev]; exact hk
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  have hfst : (braidDataOfColouring a b N y ηlo k).1
      = Function.update
          (fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi) j
          (Int.fract ((braidDataOfColouring a b N y ηhi k).1 j
            + levelDropShift a b N ηlo ηhi + sweepTheta a b N)) := by
    funext i
    by_cases h : i = j
    · subst h
      rw [Function.update_self]
      exact hI.braidData_fst_succ_of_eventType_D ha hb hN hηlo hy hev hjlt hj i rfl
    · rw [Function.update_of_ne h]
      exact hI.braidData_fst_of_eventType_D ha hb hN hηlo hy hev hjlt hj i
        (by rw [hk]; exact i.isLt) (fun hc => h (Fin.ext hc))
  have hsnd : (braidDataOfColouring a b N y ηlo k).2
      = Function.update (braidDataOfColouring a b N y ηhi k).2 j
          ((braidDataOfColouring a b N y ηhi k).2 j + 1) := by
    funext i
    by_cases h : i = j
    · subst h
      rw [Function.update_self]
      exact hI.braidData_snd_succ_of_eventType_D ha hb hN hηlo hy hev hjlt hj i rfl
    · rw [Function.update_of_ne h]
      exact hI.braidData_snd_of_eventType_D_of_ne ha hb hN hηlo hy hev hjlt hj i
        (by rw [hk]; exact i.isLt) (fun hc => h (Fin.ext hc))
  rw [braidValueColouring_colouring q u hq hq1 hqp hr hy,
    braidValueColouring_colouring q u hq hq1 hqp hr hy, sweepOperator_of_eventType_D y hev,
    braidValueOfPath_eq_braidValueOfData q u hq hq1 hqp hr y ηlo hklo,
    braidValueOfPath_eq_braidValueOfData q u hq hq1 hqp hr y ηhi hk, hfst, hsnd]
  exact hmove

end Residual

end Isolates

end HJO.Mellit

end
