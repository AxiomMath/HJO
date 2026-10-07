/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidCDIndices
public import HJO.Shuffle.BraidTypeADictionary
public import HJO.Shuffle.BraidTypeBMoveCount
public meta import HJO.Attr

/-! # The type-`B` row of the position-and-multiplicity table

`HJO/Shuffle/BraidDataLevelDrop.lean` tabulates, for the event types `C`, `D` and `E`, *where*
in the two column listings of `HJO.Mellit.braidDataOfColouring` a level drop moves a point, and
hence which entry of the position tuple `v` and which entry of the multiplicity tuple `α` changes.
Type `A` has the same table in `HJO/Shuffle/BraidTypeADictionary.lean`. **Type `B` has no row in
either**, and without one the identity of the two extra moves of
`HJO.Mellit.Isolates.length_specialMoveList_of_eventType_B` is unknown — that theorem counts them
and says nothing about where they sit.

This file supplies that row.

## The statement of the row

Fix a bracketing `HJO.Mellit.Isolates` of `(X, Y)`, an above-diagonal path `y` whose event there is
of type `B`, the floor `aN < ηlo`, and write `k = #(colouringEast y ηlo)` — the rank `hmove` of
`HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_move` reads on the left, the upper
data being of rank `k + 1`. Put

`j = HJO.Mellit.typeBIndex y ηlo X`,

the number of crossed east steps of the **lower** colouring strictly left of the column `X - 1`.
Then:

| half | what the level rise does | at which index |
| ---- | ------------------------ | -------------- |
| east | gains `(X - 1, Y)` | `j` |
| north | gains `(X, Y)` | `j + 1` |

The two insertion indices **differ by exactly one**, north above east, and that is the whole content
of the row: `HJO.Mellit.Isolates.card_filter_colouringNorth_lo_eq_typeBIndex_succ`. It is the
statement that separates type `B` from type `A`, where
`HJO.Mellit.Isolates.typeAIndex_eq_card_filter_colouringNorth` makes the two indices **equal**
and so lets a single `j : Fin (k+1)` describe the whole event. Here it cannot: the balance term of
`HJO.Mellit.card_colouringNorth_filter_lt` at the column `X` is `1` at the lower level, because a
type-`B` event has `Y = ŷ_X` and the lower level's index in that column is below `Y`
(`HJO.Mellit.Isolates.levelIndex_lo_lt`) — the level line runs *below* the path exactly there.

## What that makes of the two tuples

The position tuple reads only the east half (`HJO.Mellit.braidDataOfColouring_fst_eq`), so it sees a
single insertion at `j` and nothing else:

* `HJO.Mellit.Isolates.braidData_fst_typeBIndex` — the new entry is the normalised rank of
  `(X - 1, Y)`;
* `HJO.Mellit.Isolates.braidData_fst_succAbove` — every old entry is the new tuple read along
  `j.succAbove`, rigidly rotated by `HJO.Mellit.levelDropShift`.

The multiplicity tuple reads both halves, one through `HJO.Mellit.componentTopIndex` and one through
`HJO.Mellit.componentBotIndex`, so the offset between the two insertion indices makes it behave
differently — and this is the part with no analogue at the other event types:

* `HJO.Mellit.Isolates.braidData_snd_succAbove_of_ne` — away from the one index `j` the upper
  multiplicities read along `j.succAbove` are the lower ones, exactly as at type `A`;
* `HJO.Mellit.Isolates.braidData_snd_typeBIndex_add_succ` — at `j` the single lower multiplicity
  is the **sum of two** upper ones plus one:

  `α_lo j = α_hi j + α_hi (j+1) + 1`.

`HJO.Mellit.Isolates.braidData_of_eventType_B` puts the two tuples together as one equation: the
lower data of rank `k` is the upper data of rank `k + 1` with the index `j` deleted from the
positions and the indices `j`, `j + 1` merged in the multiplicities, plus the one rotation. So the
data rule `BE` reads on the left is a *function* of the data it reads on the right.

The component `j` of the lower data is the one the level rise **splits in two**: its crossing
interval `[B_j, T_j]` is cut at the antidiagonal index `X + Y`, the upper data carrying
`[B_j, X + Y - 1]` at index `j` and `[X + Y + 1, T_j]` at index `j + 1`
(`HJO.Mellit.Isolates.componentTopIndex_hi_typeBIndex`,
`HJO.Mellit.Isolates.componentBotIndex_hi_typeBIndex_succ`). The cut index `X + Y` is the crossing
the level rise takes away.

## The identity of the two extra moves

`HJO.Braid.count_specialMoveList` makes the moves of the component `i` exactly `α_i - 1`, so the
row above locates the two extra moves of
`HJO.Mellit.Isolates.length_specialMoveList_of_eventType_B` outright:

* `HJO.Mellit.Isolates.count_specialMoveList_of_eventType_B_of_ne` — off the index `j` the lower
  braid has the same moves as the upper one, component by component;
* `HJO.Mellit.Isolates.count_specialMoveList_typeBIndex_of_eventType_B` —

  `count_lo j = count_hi j + count_hi (j+1) + 2`.

**Both extra moves sit on the one component `j`**, and neither is anywhere else. That is the fact
the letter-count row could not see, and it says what a proof of `hmove` has to produce: not two
letters distributed over the word, but two letters on a single strand — the strand of the component
the level rise splits at the crossing `X + Y`.

## What is *not* here

`hmove` is not discharged, at no point and for no `(a, b, N)`; nor is it reduced to anything. This
file adds no hypothesis-free braid identity and touches no braid value: every statement is about
`ℕ`, `ℤ` and `ℚ` — colourings, column listings, crossing indices, positions and counts. In
particular the *value* of the two extra letters under `HJO.Sweep.braidRep` is untouched, and so is
the question of which letters they are: `HJO.Mellit.Isolates.zCount_sub_eq_one_of_eventType_D` is
the type-`D` answer to that question and it has no type-`B` counterpart here.

`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` covers the whole level recursion and this file
closes none of its clauses; `HJO.Mellit.card_componentCrossingIndices_eq` names the four types `A`,
`C`, `D`, `E` and not this one.

## Genericity

None is spent. No coefficient field appears, so the degeneracies of
`HJO/Shuffle/BraidDataLevelDrop.lean`'s last section — `Δ = 0` at `q = 1`,
`π_k(z_1) = 0` at `qu = 0` — are not in play. `0 < a`, `0 < b`, `0 < N` are the nondegeneracy of the
rectangle, admissibility of the two levels comes from the bracketing, and the floor `aN < ηlo` is
what makes the two halves of a colouring equinumerous
(`HJO.Mellit.card_colouringNorth_eq_card_colouringEast`) and, by
`HJO.Mellit.Isolates.pos_fst_of_eventType_B_of_lt`, what makes `0 < X` free — so the origin, a
type-`B` event of every above-diagonal path, needs no separate hypothesis.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, Sections 4 and 5, for
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, `HJO.Mellit.dsc_eq_dminus_add_smul`,
`HJO.Mellit.Isolates.notMem_colouringNorth_lo`, `HJO.Mellit.card_componentCrossingIndices_eq`,
`HJO.Mellit.card_colouringNorth_eq_card_colouringEast`, `HJO.Mellit.braidDataOfColouring`,
`HJO.Braid.specialBraid` and `HJO.Paths.eventType`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {a b N X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The insertion index -/

/-- **The insertion index of a type-`B` event**: the number of crossed east steps of the **lower**
colouring strictly left of the column `X - 1`, that being the column of the east step `(X - 1, Y)`
which the level rise adds.

Unlike `HJO.Mellit.typeAIndex` this is *not* also the insertion index of the north half: by
`HJO.Mellit.Isolates.card_filter_colouringNorth_lo_eq_typeBIndex_succ` the north half inserts at
`j + 1`. -/
noncomputable def typeBIndex (y : Heights a b N) (η : ℚ) (X : ℕ) : ℕ :=
  #({Q ∈ colouringEast y η | Q.1 < X - 1})

/-- The insertion index does not exceed the lower rank. -/
theorem typeBIndex_le (y : Heights a b N) (η : ℚ) (X : ℕ) :
    typeBIndex y η X ≤ #(colouringEast y η) :=
  Finset.card_filter_le _ _

/-- `HJO.Mellit.colStep_card_filter_fst_lt` with the index supplied separately, which is the form a
concrete listing is computed in: to place `P` at the index `i` it is enough to count `i` members of
`S` left of it. -/
theorem colStep_eq_of_card_filter_fst_lt {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S)
    {P : ℕ × ℕ} (hP : P ∈ S) {i : ℕ} (hi : #({Q ∈ S | Q.1 < P.1}) = i) : colStep S i = P := by
  rw [← hi]; exact colStep_card_filter_fst_lt hcol hP

namespace Isolates

/-! ### No step of the lower colouring sits in either inserted column -/

/-- **The lower colouring has no crossed north step in the column `X`.** The upper one has `(X, Y)`
there, and a colouring meets each column once. -/
theorem forall_fst_ne_of_eventType_B_north (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.B) :
    ∀ Q ∈ colouringNorth y ηlo, Q.1 ≠ X := by
  intro Q hQ hQX
  have hins := hI.colouringNorth_eq_of_eventType_B ha hN hev
  have hQhi : Q ∈ colouringNorth y ηhi := by rw [hins]; exact Finset.mem_insert_of_mem hQ
  have hPhi : ((X, Y) : ℕ × ℕ) ∈ colouringNorth y ηhi := by
    rw [hins]; exact Finset.mem_insert_self _ _
  have heq := columnInjective_colouringNorth ha hN hI.hi y Q hQhi _ hPhi hQX
  exact hI.notMem_colouringNorth_lo y (heq ▸ hQ)

/-- **The lower colouring has no crossed east step in the column `X - 1`.** The upper one has
`(X - 1, Y)` there. -/
theorem forall_fst_ne_of_eventType_B_east (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX0 : 0 < X) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.B) :
    ∀ Q ∈ colouringEast y ηlo, Q.1 ≠ X - 1 := by
  intro Q hQ hQX
  have hins := hI.colouringEast_eq_of_eventType_B ha hb hN hX0 hev
  have hQhi : Q ∈ colouringEast y ηhi := by rw [hins]; exact Finset.mem_insert_of_mem hQ
  have hPhi : ((X - 1, Y) : ℕ × ℕ) ∈ colouringEast y ηhi := by
    rw [hins]; exact Finset.mem_insert_self _ _
  have heq := columnInjective_colouringEast ha hN hI.hi y Q hQhi _ hPhi hQX
  exact hI.notMem_colouringEast_pred_lo hX0 y (heq ▸ hQ)

/-! ### The two insertion indices differ by one -/

/-- **The column `X - 1` contributes nothing to the lower east count**, so the count left of `X` and
the count left of `X - 1` agree: the insertion index of the east half may be read at either
column. -/
theorem card_filter_colouringEast_lo_lt_fst (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX0 : 0 < X) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.B) :
    #({Q ∈ colouringEast y ηlo | Q.1 < X}) = typeBIndex y ηlo X := by
  have hzero : #({Q ∈ colouringEast y ηlo | Q.1 = X - 1}) = 0 :=
    Finset.card_eq_zero.2 (Finset.eq_empty_iff_forall_notMem.2 fun Q hQ =>
      hI.forall_fst_ne_of_eventType_B_east ha hb hN hX0 hev Q
        (Finset.mem_filter.1 hQ).1 (Finset.mem_filter.1 hQ).2)
  have hsucc := card_filter_fst_lt_succ (colouringEast y ηlo) (X - 1)
  rw [show X - 1 + 1 = X from by omega, hzero] at hsucc
  rw [hsucc, typeBIndex, Nat.add_zero]

/-- **The north half inserts one index above the east half.** This is the type-`B` row of the
position-and-multiplicity table, and the fact that separates type `B` from type `A`.

The balance lemma `HJO.Mellit.card_colouringNorth_filter_lt` compares the two counts left of a
column and charges `1` exactly when the level line runs below the path at that column. At a type-`B`
event `Y = ŷ_X`, and `HJO.Mellit.Isolates.levelIndex_lo_lt` puts the lower level's index in the
column `X` strictly below `Y`; so the balance term is `1` there and the north count exceeds the east
count by one. At type `A` the same term is `0`
(`HJO.Mellit.Isolates.typeAIndex_eq_card_filter_colouringNorth`), which is why a single index serves
both halves there and no index serves both here. -/
theorem card_filter_colouringNorth_lo_eq_typeBIndex_succ (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) :
    #({Q ∈ colouringNorth y ηlo | Q.1 < X}) = typeBIndex y ηlo X + 1 := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_B_of_lt hηlo hy hev
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  obtain ⟨hfoot, -, -⟩ := eventType_eq_B_iff.1 hev
  have hfoot' : Y = ht y X := hfoot
  have hbal := card_colouringNorth_filter_lt ha hb hN hI.lo hlopos hy (t := X) hI.xle
  have hlt : levelIndex a b N ηlo X < (ht y X : ℤ) := by
    have := hI.levelIndex_lo_lt ha hN
    omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true hlt)] at hbal
  rw [hbal, hI.card_filter_colouringEast_lo_lt_fst ha hb hN hX0 hev]

/-- **The split happens strictly inside the lower data.** The north insertion index `j + 1` is a
count of crossed north steps, so it is at most the lower rank; hence `j < k`, and in particular the
lower colouring has at least one component. -/
theorem typeBIndex_succ_le (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) :
    typeBIndex y ηlo X + 1 ≤ #(colouringEast y ηlo) := by
  have h := hI.card_filter_colouringNorth_lo_eq_typeBIndex_succ ha hb hN hηlo hy hev
  have hle : #({Q ∈ colouringNorth y ηlo | Q.1 < X}) ≤ #(colouringNorth y ηlo) :=
    Finset.card_filter_le _ _
  have hcard := card_colouringNorth_eq_card_colouringEast hb hN hI.lo hηlo hy (y := y)
  omega

/-! ### The east listing: a single insertion at `j` -/

/-- **The new crossed east step is the `j`-th member of the upper east listing.** -/
theorem colStep_colouringEast_hi_typeBIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX0 : 0 < X) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.B) :
    colStep (colouringEast y ηhi) (typeBIndex y ηlo X) = (X - 1, Y) := by
  rw [typeBIndex, hI.colouringEast_eq_of_eventType_B ha hb hN hX0 hev]
  exact colStep_insert_self (columnInjective_colouringEast ha hN hI.lo y)
    (hI.forall_fst_ne_of_eventType_B_east ha hb hN hX0 hev)

/-- **Below `j` the upper east listing is the lower one.** -/
theorem colStep_colouringEast_hi_of_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX0 : 0 < X) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.B) {i : ℕ} (hi : i < #(colouringEast y ηlo))
    (hij : i < typeBIndex y ηlo X) :
    colStep (colouringEast y ηhi) i = colStep (colouringEast y ηlo) i := by
  rw [hI.colouringEast_eq_of_eventType_B ha hb hN hX0 hev]
  exact colStep_insert_of_lt (columnInjective_colouringEast ha hN hI.lo y)
    (hI.forall_fst_ne_of_eventType_B_east ha hb hN hX0 hev) hi hij

/-- **At and above `j` the upper east listing is the lower one with its index raised by one.** -/
theorem colStep_colouringEast_hi_of_le (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX0 : 0 < X) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.B) {i : ℕ} (hi : i < #(colouringEast y ηlo))
    (hij : typeBIndex y ηlo X ≤ i) :
    colStep (colouringEast y ηhi) (i + 1) = colStep (colouringEast y ηlo) i := by
  rw [hI.colouringEast_eq_of_eventType_B ha hb hN hX0 hev]
  exact colStep_insert_of_le (columnInjective_colouringEast ha hN hI.lo y)
    (hI.notMem_colouringEast_pred_lo hX0 y)
    (hI.forall_fst_ne_of_eventType_B_east ha hb hN hX0 hev) hi hij

/-! ### The north listing: a single insertion at `j + 1` -/

/-- **The new crossed north step is the `(j+1)`-st member of the upper north listing** — one index
above where the east half inserts. -/
theorem colStep_colouringNorth_hi_typeBIndex_succ (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) :
    colStep (colouringNorth y ηhi) (typeBIndex y ηlo X + 1) = (X, Y) := by
  rw [← hI.card_filter_colouringNorth_lo_eq_typeBIndex_succ ha hb hN hηlo hy hev,
    hI.colouringNorth_eq_of_eventType_B ha hN hev]
  exact colStep_insert_self (columnInjective_colouringNorth ha hN hI.lo y)
    (hI.forall_fst_ne_of_eventType_B_north ha hN hev)

/-- **At and below `j` the upper north listing is the lower one.** -/
theorem colStep_colouringNorth_hi_of_le (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {i : ℕ}
    (hi : i < #(colouringNorth y ηlo)) (hij : i ≤ typeBIndex y ηlo X) :
    colStep (colouringNorth y ηhi) i = colStep (colouringNorth y ηlo) i := by
  rw [hI.colouringNorth_eq_of_eventType_B ha hN hev]
  refine colStep_insert_of_lt (columnInjective_colouringNorth ha hN hI.lo y)
    (hI.forall_fst_ne_of_eventType_B_north ha hN hev) hi ?_
  rw [hI.card_filter_colouringNorth_lo_eq_typeBIndex_succ ha hb hN hηlo hy hev]
  omega

/-- **Above `j` the upper north listing is the lower one with its index raised by one.** -/
theorem colStep_colouringNorth_hi_of_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {i : ℕ}
    (hi : i < #(colouringNorth y ηlo)) (hij : typeBIndex y ηlo X < i) :
    colStep (colouringNorth y ηhi) (i + 1) = colStep (colouringNorth y ηlo) i := by
  rw [hI.colouringNorth_eq_of_eventType_B ha hN hev]
  refine colStep_insert_of_le (columnInjective_colouringNorth ha hN hI.lo y)
    (hI.notMem_colouringNorth_lo y) (hI.forall_fst_ne_of_eventType_B_north ha hN hev) hi ?_
  rw [hI.card_filter_colouringNorth_lo_eq_typeBIndex_succ ha hb hN hηlo hy hev]
  omega

/-! ### The two listings read along `Fin.succAbove` -/

/-- **Away from `j` the upper east listing is the lower one, read along `Fin.succAbove`.** This is
the shape the rank-raise layer's `HJO.Braid.specialMoveList_eq_map_succAbove` takes an insertion
in. -/
theorem colStep_colouringEast_hi_succAbove (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX0 : 0 < X) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.B) {k : ℕ} (hk : #(colouringEast y ηlo) = k)
    (j : Fin (k + 1)) (hj : (j : ℕ) = typeBIndex y ηlo X) (i : Fin k) :
    colStep (colouringEast y ηhi) ((j.succAbove i : Fin (k + 1)) : ℕ)
      = colStep (colouringEast y ηlo) (i : ℕ) := by
  rw [hI.colouringEast_eq_of_eventType_B ha hb hN hX0 hev]
  exact colStep_insert_succAbove (columnInjective_colouringEast ha hN hI.lo y)
    (hI.notMem_colouringEast_pred_lo hX0 y)
    (hI.forall_fst_ne_of_eventType_B_east ha hb hN hX0 hev) hk j (hj.trans rfl) i

/-- **Away from `j + 1` the upper north listing is the lower one, read along `Fin.succAbove`** — the
same statement as for the east half but at the *shifted* index, which is the whole asymmetry of the
type-`B` row. -/
theorem colStep_colouringNorth_hi_succAbove (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {k : ℕ}
    (hk : #(colouringNorth y ηlo) = k) (j' : Fin (k + 1))
    (hj' : (j' : ℕ) = typeBIndex y ηlo X + 1) (i : Fin k) :
    colStep (colouringNorth y ηhi) ((j'.succAbove i : Fin (k + 1)) : ℕ)
      = colStep (colouringNorth y ηlo) (i : ℕ) := by
  rw [hI.colouringNorth_eq_of_eventType_B ha hN hev]
  refine colStep_insert_succAbove (columnInjective_colouringNorth ha hN hI.lo y)
    (hI.notMem_colouringNorth_lo y) (hI.forall_fst_ne_of_eventType_B_north ha hN hev) hk j' ?_ i
  rw [hj', hI.card_filter_colouringNorth_lo_eq_typeBIndex_succ ha hb hN hηlo hy hev]

/-! ### The endpoint indices: the level rise cuts one component at `X + Y` -/

/-- **The top crossing index of the upper component `j` is `X + Y - 1`**, its crossed east step
being the new one `(X - 1, Y)`. -/
theorem componentTopIndex_hi_typeBIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) :
    componentTopIndex a b N y ηhi (typeBIndex y ηlo X) = (X : ℤ) + (Y : ℤ) - 1 := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_B_of_lt hηlo hy hev
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hcard := hI.card_colouringEast_of_eventType_B ha hb hN hX0 hev (y := y)
  have hle := hI.typeBIndex_succ_le ha hb hN hηlo hy hev
  have hlt : typeBIndex y ηlo X < #(colouringEast y ηhi) := by omega
  rw [componentTopIndex_eq ha hb hN hI.hi hhipos hlt,
    hI.colStep_colouringEast_hi_typeBIndex ha hb hN hX0 hev]
  simp only
  omega

/-- **The bottom crossing index of the upper component `j + 1` is `X + Y + 1`**, its crossed north
step being the new one `(X, Y)`. Together with
`HJO.Mellit.Isolates.componentTopIndex_hi_typeBIndex` this is the cut: the level rise removes the
single crossing of index `X + Y` and separates what is below it from what is above. -/
theorem componentBotIndex_hi_typeBIndex_succ (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) :
    componentBotIndex a b N y ηhi (typeBIndex y ηlo X + 1) = (X : ℤ) + (Y : ℤ) + 1 := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_B_of_lt hηlo hy hev
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hcardN := hI.card_colouringNorth_of_eventType_B ha hN hev (y := y)
  have hcardlo := card_colouringNorth_eq_card_colouringEast hb hN hI.lo hηlo hy (y := y)
  have hle := hI.typeBIndex_succ_le ha hb hN hηlo hy hev
  have hlt : typeBIndex y ηlo X + 1 < #(colouringNorth y ηhi) := by omega
  rw [componentBotIndex_eq_add_snd ha hb hN hI.hi hhipos y hlt,
    hI.colStep_colouringNorth_hi_typeBIndex_succ ha hb hN hηlo hy hev]

/-- **The top crossing index of the upper component `j + 1` is the lower component `j`'s.** -/
theorem componentTopIndex_hi_typeBIndex_succ (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) :
    componentTopIndex a b N y ηhi (typeBIndex y ηlo X + 1)
      = componentTopIndex a b N y ηlo (typeBIndex y ηlo X) := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_B_of_lt hηlo hy hev
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hcard := hI.card_colouringEast_of_eventType_B ha hb hN hX0 hev (y := y)
  have hle := hI.typeBIndex_succ_le ha hb hN hηlo hy hev
  have hltlo : typeBIndex y ηlo X < #(colouringEast y ηlo) := by omega
  have hlt : typeBIndex y ηlo X + 1 < #(colouringEast y ηhi) := by omega
  rw [componentTopIndex_eq ha hb hN hI.hi hhipos hlt,
    componentTopIndex_eq ha hb hN hI.lo hlopos hltlo,
    hI.colStep_colouringEast_hi_of_le ha hb hN hX0 hev hltlo le_rfl]

/-- **Below `j` the top crossing indices are unchanged.** -/
theorem componentTopIndex_hi_of_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {i : ℕ}
    (hi : i < #(colouringEast y ηlo)) (hij : i < typeBIndex y ηlo X) :
    componentTopIndex a b N y ηhi i = componentTopIndex a b N y ηlo i := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_B_of_lt hηlo hy hev
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hcard := hI.card_colouringEast_of_eventType_B ha hb hN hX0 hev (y := y)
  rw [componentTopIndex_eq ha hb hN hI.hi hhipos (by omega),
    componentTopIndex_eq ha hb hN hI.lo hlopos hi,
    hI.colStep_colouringEast_hi_of_lt ha hb hN hX0 hev hi hij]

/-- **Above `j` the top crossing indices are unchanged, at the raised index.** -/
theorem componentTopIndex_hi_of_gt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {i : ℕ}
    (hi : i < #(colouringEast y ηlo)) (hij : typeBIndex y ηlo X < i) :
    componentTopIndex a b N y ηhi (i + 1) = componentTopIndex a b N y ηlo i := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_B_of_lt hηlo hy hev
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hcard := hI.card_colouringEast_of_eventType_B ha hb hN hX0 hev (y := y)
  rw [componentTopIndex_eq ha hb hN hI.hi hhipos (by omega),
    componentTopIndex_eq ha hb hN hI.lo hlopos hi,
    hI.colStep_colouringEast_hi_of_le ha hb hN hX0 hev hi hij.le]

/-- **At and below `j` the bottom crossing indices are unchanged.** -/
theorem componentBotIndex_hi_of_le (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {i : ℕ}
    (hi : i < #(colouringNorth y ηlo)) (hij : i ≤ typeBIndex y ηlo X) :
    componentBotIndex a b N y ηhi i = componentBotIndex a b N y ηlo i := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hcardN := hI.card_colouringNorth_of_eventType_B ha hN hev (y := y)
  rw [componentBotIndex_eq_add_snd ha hb hN hI.hi hhipos y (by omega),
    componentBotIndex_eq_add_snd ha hb hN hI.lo hlopos y hi,
    hI.colStep_colouringNorth_hi_of_le ha hb hN hηlo hy hev hi hij]

/-- **Above `j` the bottom crossing indices are unchanged, at the raised index.** -/
theorem componentBotIndex_hi_of_gt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {i : ℕ}
    (hi : i < #(colouringNorth y ηlo)) (hij : typeBIndex y ηlo X < i) :
    componentBotIndex a b N y ηhi (i + 1) = componentBotIndex a b N y ηlo i := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hcardN := hI.card_colouringNorth_of_eventType_B ha hN hev (y := y)
  rw [componentBotIndex_eq_add_snd ha hb hN hI.hi hhipos y (by omega),
    componentBotIndex_eq_add_snd ha hb hN hI.lo hlopos y hi,
    hI.colStep_colouringNorth_hi_of_lt ha hb hN hηlo hy hev hi hij]

/-! ### The position tuple: one insertion at `j`, and the rotation -/

/-- **The inserted position is the normalised rank of the new crossed east step `(X - 1, Y)`.**
The position tuple reads only the east half of the colouring, so the type-`B` row it sees is a
single insertion at `j` — the shifted north insertion is invisible to it. -/
theorem braidData_fst_typeBIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {k : ℕ}
    (hk : #(colouringEast y ηlo) = k) (j : Fin (k + 1)) (hj : (j : ℕ) = typeBIndex y ηlo X) :
    (braidDataOfColouring a b N y ηhi (k + 1)).1 j
      = levelPosition a b N ηhi ((pointRank a b N ((X - 1 : ℕ), Y) : ℤ) : ℚ) := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_B_of_lt hηlo hy hev
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hcard := hI.card_colouringEast_of_eventType_B ha hb hN hX0 hev (y := y)
  have hle := hI.typeBIndex_succ_le ha hb hN hηlo hy hev
  have hlt : (j : ℕ) < #(colouringEast y ηhi) := by omega
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos j hlt, hj,
    hI.colStep_colouringEast_hi_typeBIndex ha hb hN hX0 hev]

/-- **Every retained position is the upper one read along `j.succAbove`, rigidly rotated.** The one
common shift is `HJO.Mellit.levelDropShift`, as at every level drop. -/
theorem braidData_fst_succAbove (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {k : ℕ}
    (hk : #(colouringEast y ηlo) = k) (j : Fin (k + 1)) (hj : (j : ℕ) = typeBIndex y ηlo X)
    (i : Fin k) :
    (braidDataOfColouring a b N y ηlo k).1 i
      = (braidDataOfColouring a b N y ηhi (k + 1)).1 (j.succAbove i)
        + levelDropShift a b N ηlo ηhi := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_B_of_lt hηlo hy hev
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hcard := hI.card_colouringEast_of_eventType_B ha hb hN hX0 hev (y := y)
  have hilo : (i : ℕ) < #(colouringEast y ηlo) := by rw [hk]; exact i.isLt
  have hihi : ((j.succAbove i : Fin (k + 1)) : ℕ) < #(colouringEast y ηhi) := by
    have := (j.succAbove i).isLt; omega
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.lo hlopos i hilo,
    braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos _ hihi,
    hI.colStep_colouringEast_hi_succAbove ha hb hN hX0 hev hk j hj i,
    levelPosition_eq_add_levelDropShift]

/-! ### The multiplicity tuple: unchanged off `j`, split in two at `j` -/

/-- **Away from the one index `j` the upper multiplicities read along `j.succAbove` are the lower
ones.** Both endpoint indices are carried across: below `j` neither listing has moved, and above `j`
both have moved by one — the offset between the two insertion indices is invisible except at `j`
itself. -/
theorem braidData_snd_succAbove_of_ne (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {k : ℕ}
    (hk : #(colouringEast y ηlo) = k) (j : Fin (k + 1)) (hj : (j : ℕ) = typeBIndex y ηlo X)
    (i : Fin k) (hne : (i : ℕ) ≠ typeBIndex y ηlo X) :
    (braidDataOfColouring a b N y ηhi (k + 1)).2 (j.succAbove i)
      = (braidDataOfColouring a b N y ηlo k).2 i := by
  have hcardlo : #(colouringNorth y ηlo) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.lo hηlo hy, hk]
  have hiE : (i : ℕ) < #(colouringEast y ηlo) := by rw [hk]; exact i.isLt
  have hiN : (i : ℕ) < #(colouringNorth y ηlo) := by rw [hcardlo]; exact i.isLt
  rw [braidDataOfColouring_snd_eq_toNat, braidDataOfColouring_snd_eq_toNat]
  rcases lt_or_gt_of_ne hne with h | h
  · have hval : ((j.succAbove i : Fin (k + 1)) : ℕ) = (i : ℕ) := by
      rw [Fin.succAbove_of_castSucc_lt _ _
        (show i.castSucc < j from by rw [Fin.lt_def, Fin.val_castSucc, hj]; exact h),
        Fin.val_castSucc]
    rw [hval, hI.componentTopIndex_hi_of_lt ha hb hN hηlo hy hev hiE h,
      hI.componentBotIndex_hi_of_le ha hb hN hηlo hy hev hiN h.le]
  · have hval : ((j.succAbove i : Fin (k + 1)) : ℕ) = (i : ℕ) + 1 := by
      rw [Fin.succAbove_of_le_castSucc _ _
        (show j ≤ i.castSucc from by rw [Fin.le_def, Fin.val_castSucc, hj]; exact h.le),
        Fin.val_succ]
    rw [hval, hI.componentTopIndex_hi_of_gt ha hb hN hηlo hy hev hiE h,
      hI.componentBotIndex_hi_of_gt ha hb hN hηlo hy hev hiN h]

/-- **The multiplicity of the lower component `j` is the sum of two upper ones plus one.** This is
the row the table did not have and the reason type `B` is not a type-`A` insertion: the crossing
interval of the lower component `j` is cut by the level rise at the antidiagonal index `X + Y`, the
part below it becoming the upper component `j` and the part above it the upper component `j + 1`,
with the cut crossing itself lost.

Everything else being carried across unchanged
(`HJO.Mellit.Isolates.braidData_snd_succAbove_of_ne`), this single equation accounts for the whole
letter gap of `HJO.Mellit.Isolates.length_specialMoveList_of_eventType_B`. -/
theorem braidData_snd_typeBIndex_add_succ (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {k : ℕ}
    (hk : #(colouringEast y ηlo) = k) (j j' : Fin (k + 1)) (hj : (j : ℕ) = typeBIndex y ηlo X)
    (hj' : (j' : ℕ) = typeBIndex y ηlo X + 1) (i : Fin k) (hi : (i : ℕ) = typeBIndex y ηlo X) :
    (braidDataOfColouring a b N y ηhi (k + 1)).2 j
        + (braidDataOfColouring a b N y ηhi (k + 1)).2 j' + 1
      = (braidDataOfColouring a b N y ηlo k).2 i := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_B_of_lt hηlo hy hev
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hcardN := hI.card_colouringNorth_of_eventType_B ha hN hev (y := y)
  have hcardlo : #(colouringNorth y ηlo) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.lo hηlo hy, hk]
  have hle := hI.typeBIndex_succ_le ha hb hN hηlo hy hev
  have hiN : (i : ℕ) < #(colouringNorth y ηlo) := by rw [hcardlo]; exact i.isLt
  have htophi := hI.componentTopIndex_hi_typeBIndex ha hb hN hηlo hy hev (y := y)
  have hbothi := hI.componentBotIndex_hi_typeBIndex_succ ha hb hN hηlo hy hev (y := y)
  have htophi' := hI.componentTopIndex_hi_typeBIndex_succ ha hb hN hηlo hy hev (y := y)
  have hbothi' := hI.componentBotIndex_hi_of_le ha hb hN hηlo hy hev (i := typeBIndex y ηlo X)
    (by omega) le_rfl (y := y)
  -- the two upper components are nondegenerate, which is what makes the `toNat` arithmetic work
  have hnd : componentBotIndex a b N y ηhi (typeBIndex y ηlo X)
      ≤ componentTopIndex a b N y ηhi (typeBIndex y ηlo X) :=
    componentBotIndex_le_componentTopIndex ha hb hN hI.hi hηhi hy (by omega)
  have hnd' : componentBotIndex a b N y ηhi (typeBIndex y ηlo X + 1)
      ≤ componentTopIndex a b N y ηhi (typeBIndex y ηlo X + 1) :=
    componentBotIndex_le_componentTopIndex ha hb hN hI.hi hηhi hy (by omega)
  rw [braidDataOfColouring_snd_eq_toNat, braidDataOfColouring_snd_eq_toNat,
    braidDataOfColouring_snd_eq_toNat, hj, hj', hi, htophi, hbothi, htophi', hbothi']
  rw [htophi, hbothi'] at hnd
  rw [hbothi, htophi'] at hnd'
  omega

/-! ### Where the two extra moves sit -/

/-- **Off the index `j` the lower braid has the same moves as the upper one, component by
component.** `HJO.Braid.count_specialMoveList` counts the moves of a component as `α_i - 1`. -/
theorem count_specialMoveList_of_eventType_B_of_ne (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {k : ℕ}
    (hk : #(colouringEast y ηlo) = k) (j : Fin (k + 1)) (hj : (j : ℕ) = typeBIndex y ηlo X)
    (i : Fin k) (hne : (i : ℕ) ≠ typeBIndex y ηlo X) :
    (Braid.specialMoveList (braidDataOfColouring a b N y ηlo k).2).count i
      = (Braid.specialMoveList (braidDataOfColouring a b N y ηhi (k + 1)).2).count
          (j.succAbove i) := by
  rw [Braid.count_specialMoveList, Braid.count_specialMoveList,
    hI.braidData_snd_succAbove_of_ne ha hb hN hηlo hy hev hk j hj i hne]

/-- **Both extra moves sit on the one component `j`.** The lower component `j` carries exactly two
moves more than the two upper components it splits into carry between them:

`count_lo j = count_hi j + count_hi (j+1) + 2`.

One of the two is the crossing the level rise removes, the other is the join of the two upper
intervals. With `HJO.Mellit.Isolates.count_specialMoveList_of_eventType_B_of_ne` this locates the
whole letter gap of `HJO.Mellit.Isolates.length_specialMoveList_of_eventType_B`, which counts the
two extra moves and says nothing about where they are.

What it does **not** say is which letters they are: `HJO.Braid.braidStep` chooses between a `z` and
a `ỹ` by the position of the moving point relative to the puncture, and no such statement is proved
here for type `B`. -/
theorem count_specialMoveList_typeBIndex_of_eventType_B (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {k : ℕ}
    (hk : #(colouringEast y ηlo) = k) (j j' : Fin (k + 1)) (hj : (j : ℕ) = typeBIndex y ηlo X)
    (hj' : (j' : ℕ) = typeBIndex y ηlo X + 1) (i : Fin k) (hi : (i : ℕ) = typeBIndex y ηlo X) :
    (Braid.specialMoveList (braidDataOfColouring a b N y ηlo k).2).count i
      = (Braid.specialMoveList (braidDataOfColouring a b N y ηhi (k + 1)).2).count j
        + (Braid.specialMoveList (braidDataOfColouring a b N y ηhi (k + 1)).2).count j' + 2 := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hcardN := hI.card_colouringNorth_of_eventType_B ha hN hev (y := y)
  have hcardlo : #(colouringNorth y ηlo) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.lo hηlo hy, hk]
  have hle := hI.typeBIndex_succ_le ha hb hN hηlo hy hev
  have hsum := hI.braidData_snd_typeBIndex_add_succ ha hb hN hηlo hy hev hk j j' hj hj' i hi
  -- each upper component carries at least one crossing
  have h1 : 1 ≤ (braidDataOfColouring a b N y ηhi (k + 1)).2 j := by
    have hnd := componentBotIndex_le_componentTopIndex ha hb hN hI.hi hηhi hy
      (show (j : ℕ) < #(colouringNorth y ηhi) by omega)
    rw [braidDataOfColouring_snd_eq_toNat]
    omega
  have h2 : 1 ≤ (braidDataOfColouring a b N y ηhi (k + 1)).2 j' := by
    have hnd := componentBotIndex_le_componentTopIndex ha hb hN hI.hi hηhi hy
      (show (j' : ℕ) < #(colouringNorth y ηhi) by omega)
    rw [braidDataOfColouring_snd_eq_toNat]
    omega
  rw [Braid.count_specialMoveList, Braid.count_specialMoveList, Braid.count_specialMoveList]
  omega

/-! ### The row, as one equation -/

/-- **The whole type-`B` row in one equation: the lower special-braid data is the upper one with the
index `j` deleted from the positions and the indices `j`, `j + 1` merged in the multiplicities.**

Read off `HJO.Mellit.Isolates.braidData_fst_succAbove`,
`HJO.Mellit.Isolates.braidData_snd_succAbove_of_ne` and
`HJO.Mellit.Isolates.braidData_snd_typeBIndex_add_succ`. The point is that the right-hand side
mentions the lower level only through the one rotation `HJO.Mellit.levelDropShift`: the data of rank
`k` that rule `BE` reads on the left is a *function* of the data of rank `k + 1` it reads on the
right, the index `j` and that rotation, with no further geometry.

Compare the type-`A` row, where `HJO.Mellit.braidValueOfData_succAbove_eq_dplus` turns the analogous
description — one entry inserted, of multiplicity `1` — into a braid-value identity. Here the
description is a *merge* rather than an insertion, so no such identity is available and none is
claimed: this is geometry, and `hmove` of
`HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_move` is untouched. -/
theorem braidData_of_eventType_B (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.B) {k : ℕ}
    (hk : #(colouringEast y ηlo) = k) (j j' : Fin (k + 1)) (hj : (j : ℕ) = typeBIndex y ηlo X)
    (hj' : (j' : ℕ) = typeBIndex y ηlo X + 1) (i₀ : Fin k)
    (hi₀ : (i₀ : ℕ) = typeBIndex y ηlo X) :
    braidDataOfColouring a b N y ηlo k
      = ((fun i => (braidDataOfColouring a b N y ηhi (k + 1)).1 (j.succAbove i)
            + levelDropShift a b N ηlo ηhi),
        Function.update
          (fun i => (braidDataOfColouring a b N y ηhi (k + 1)).2 (j.succAbove i)) i₀
          ((braidDataOfColouring a b N y ηhi (k + 1)).2 j
            + (braidDataOfColouring a b N y ηhi (k + 1)).2 j' + 1)) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact hI.braidData_fst_succAbove ha hb hN hηlo hy hev hk j hj i
  · dsimp only
    by_cases h : i = i₀
    · subst h
      rw [Function.update_self]
      exact (hI.braidData_snd_typeBIndex_add_succ ha hb hN hηlo hy hev hk j j' hj hj' i hi₀).symm
    · rw [Function.update_of_ne h]
      exact (hI.braidData_snd_succAbove_of_ne ha hb hN hηlo hy hev hk j hj i
        (fun hc => h (Fin.ext (hc.trans hi₀.symm)))).symm

end Isolates

/-! ### Consistency check at the decided configuration

Everything below is read at the `2 × 3` configuration `HJO.Mellit.dsc_eq_dminus_add_smul_example` is
stated at and `HJO.Mellit.Isolates.bePair_ranks` and
`HJO.Mellit.Isolates.length_specialMoveList_of_bePair` were both checked at: the paths `(0,2,3)`
and `(0,3,3)`, the point `P = (1, 2)` of rank `4`, the levels `7/2` and `9/2`. There `k = 1`, so the
lower data has one component and the upper data two, and the insertion index is `j = 0` — the east
half inserts at `0` and the north half at `1`, the offset the general row asserts.

The check is the last theorem and its `rfl`. The two special-braid letter counts of the
configuration are already computed in `HJO.Mellit.length_specialMoveList_be_witness_adhoc`, from the
two total crossing counts and the two widths, with no dictionary used. They are re-derived here from
the type-`B` row instead: the **upper** multiplicities `2` and `1` are computed outright, the
**lower** one is obtained from them by `HJO.Mellit.Isolates.braidData_snd_typeBIndex_add_succ`
alone, and the two lengths follow. A `+2` in place of the `+1` of the split, an insertion placed at
the wrong index in either half, or the two insertion indices taken equal (the type-`A` row) all give
a different lower multiplicity and fail here. -/

/-- The insertion index at the witness is `0`: the lower colouring has no crossed east step left of
the column `X - 1 = 0`. -/
theorem typeBIndex_be_witness : typeBIndex (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1 = 0 := by
  rw [typeBIndex, colouringEast_be_witness.1]
  decide

/-- **The two insertion positions at the witness, computed outright** from the explicit colouring
sets through `HJO.Mellit.colStep_eq_of_card_filter_fst_lt`: the new crossed east step `(0, 2)` is
listed at index `0` and the new crossed north step `(1, 2)` at index `1`. -/
theorem colStep_be_witness_adhoc :
    colStep (colouringEast (![0, 2, 3] : Heights 2 3 1) (9 / 2)) 0 = (0, 2) ∧
      colStep (colouringNorth (![0, 2, 3] : Heights 2 3 1) (9 / 2)) 1 = (1, 2) := by
  obtain ⟨-, hE', -⟩ := colouringEast_be_witness
  obtain ⟨-, hN2⟩ := colouringNorth_be_witness
  exact ⟨colStep_eq_of_card_filter_fst_lt
      (columnInjective_colouringEast (by norm_num) (by norm_num) isolates_be_witness.hi
        (![0, 2, 3] : Heights 2 3 1)) (by rw [hE']; decide) (by rw [hE']; decide),
    colStep_eq_of_card_filter_fst_lt
      (columnInjective_colouringNorth (by norm_num) (by norm_num) isolates_be_witness.hi
        (![0, 2, 3] : Heights 2 3 1)) (by rw [hN2]; decide) (by rw [hN2]; decide)⟩

/-- **The two insertion positions at the witness, through the general row.** The offset is visible
here: the east half inserts at `HJO.Mellit.typeBIndex = 0` and the north half at `1`. -/
theorem colStep_be_witness :
    colStep (colouringEast (![0, 2, 3] : Heights 2 3 1) (9 / 2)) 0 = (0, 2) ∧
      colStep (colouringNorth (![0, 2, 3] : Heights 2 3 1) (9 / 2)) 1 = (1, 2) := by
  have hev : eventType (![0, 2, 3] : Heights 2 3 1) (1, 2) = EventType.B := by decide
  have hE := isolates_be_witness.colStep_colouringEast_hi_typeBIndex (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hev
  have hN := isolates_be_witness.colStep_colouringNorth_hi_typeBIndex_succ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide) hev
  rw [typeBIndex_be_witness] at hE hN
  exact ⟨hE, hN⟩

/-- **The two routes place the two new steps at the same two indices.** -/
example : colStep_be_witness = colStep_be_witness_adhoc := rfl

/-- **The two upper multiplicities at the witness, computed outright**: the component the level rise
cuts below the crossing `X + Y = 3` carries the crossings `1, 2` and the one above it carries the
single crossing `4`. -/
theorem braidData_snd_hi_be_witness_adhoc :
    (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2 0 = 2 ∧
      (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2 1 = 1 := by
  obtain ⟨-, hE', -⟩ := colouringEast_be_witness
  obtain ⟨-, hN2⟩ := colouringNorth_be_witness
  have hcE : #(colouringEast (![0, 2, 3] : Heights 2 3 1) (9 / 2)) = 2 := by rw [hE']; decide
  have hcN : #(colouringNorth (![0, 2, 3] : Heights 2 3 1) (9 / 2)) = 2 := by rw [hN2]; decide
  have hcolE := columnInjective_colouringEast (b := 3) (by norm_num) (by norm_num)
    isolates_be_witness.hi (![0, 2, 3] : Heights 2 3 1)
  have hcolN := columnInjective_colouringNorth (b := 3) (by norm_num) (by norm_num)
    isolates_be_witness.hi (![0, 2, 3] : Heights 2 3 1)
  have hE0 : colStep (colouringEast (![0, 2, 3] : Heights 2 3 1) (9 / 2)) 0 = (0, 2) :=
    colStep_eq_of_card_filter_fst_lt hcolE (by rw [hE']; decide) (by rw [hE']; decide)
  have hE1 : colStep (colouringEast (![0, 2, 3] : Heights 2 3 1) (9 / 2)) 1 = (1, 3) :=
    colStep_eq_of_card_filter_fst_lt hcolE (by rw [hE']; decide) (by rw [hE']; decide)
  have hN0 : colStep (colouringNorth (![0, 2, 3] : Heights 2 3 1) (9 / 2)) 0 = (0, 0) :=
    colStep_eq_of_card_filter_fst_lt hcolN (by rw [hN2]; decide) (by rw [hN2]; decide)
  have hN1 : colStep (colouringNorth (![0, 2, 3] : Heights 2 3 1) (9 / 2)) 1 = (1, 2) :=
    colStep_eq_of_card_filter_fst_lt hcolN (by rw [hN2]; decide) (by rw [hN2]; decide)
  have htop : ∀ i : ℕ, i < 2 → componentTopIndex 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) i
      = ((colStep (colouringEast (![0, 2, 3] : Heights 2 3 1) (9 / 2)) i).1 : ℤ)
        + ((colStep (colouringEast (![0, 2, 3] : Heights 2 3 1) (9 / 2)) i).2 : ℤ) :=
    fun i hi => componentTopIndex_eq (by norm_num) (by norm_num) (by norm_num)
      isolates_be_witness.hi (by norm_num) (by rw [hcE]; exact hi)
  have hbot : ∀ i : ℕ, i < 2 → componentBotIndex 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) i
      = ((colStep (colouringNorth (![0, 2, 3] : Heights 2 3 1) (9 / 2)) i).1 : ℤ)
        + ((colStep (colouringNorth (![0, 2, 3] : Heights 2 3 1) (9 / 2)) i).2 : ℤ) + 1 :=
    fun i hi => componentBotIndex_eq_add_snd (by norm_num) (by norm_num) (by norm_num)
      isolates_be_witness.hi (by norm_num) _ (by rw [hcN]; exact hi)
  refine ⟨?_, ?_⟩
  · rw [braidDataOfColouring_snd_eq_toNat, Fin.val_zero, htop 0 (by norm_num),
      hbot 0 (by norm_num), hE0, hN0]
    decide
  · rw [braidDataOfColouring_snd_eq_toNat, Fin.val_one, htop 1 (by norm_num),
      hbot 1 (by norm_num), hE1, hN1]
    decide

/-- **The multiplicity split at the witness, through the general result**: `4 = 2 + 1 + 1`. Every
hypothesis of `HJO.Mellit.Isolates.braidData_snd_typeBIndex_add_succ` is discharged by computation,
so the statement is about a configuration that occurs. -/
theorem braidData_snd_add_succ_be_witness :
    (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2 0
        + (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2 1 + 1
      = (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).2 0 :=
  isolates_be_witness.braidData_snd_typeBIndex_add_succ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide)
    (show #(colouringEast (![0, 2, 3] : Heights 2 3 1) (7 / 2)) = 1 by
      rw [colouringEast_be_witness.1]; decide)
    0 1 (by simp [typeBIndex_be_witness]) (by simp [typeBIndex_be_witness]) 0
    (by simp [typeBIndex_be_witness])

/-- **The two letter counts at the witness, re-derived from the type-`B` row.** The upper
multiplicities are the computed `2` and `1`; the lower one is *not* computed — it comes from
`HJO.Mellit.Isolates.braidData_snd_typeBIndex_add_succ`, which is the whole content of the row. -/
theorem length_specialMoveList_be_witness_of_dictionary :
    (Braid.specialMoveList
        (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2).length = 1 ∧
      (Braid.specialMoveList
        (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).2).length = 3 := by
  obtain ⟨h0, h1⟩ := braidData_snd_hi_be_witness_adhoc
  have hsplit := braidData_snd_add_succ_be_witness
  rw [h0, h1] at hsplit
  refine ⟨?_, ?_⟩
  · rw [Braid.length_specialMoveList, Fin.sum_univ_two, h0, h1]
  · rw [Braid.length_specialMoveList, Fin.sum_univ_one, ← hsplit]

/-- **The check.** The two letter counts of the decided configuration, from the type-`B` row and
from the independent computation of `HJO.Mellit.length_specialMoveList_be_witness_adhoc`, are the
same two equations. -/
example : length_specialMoveList_be_witness_of_dictionary
    = length_specialMoveList_be_witness_adhoc := rfl

end HJO.Mellit

end
