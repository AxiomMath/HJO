/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidValueBERanks
public meta import HJO.Attr

/-! # The type-`B` row of the letter-count table, and what it rules out

`HJO/Shuffle/BraidLevelDrop.lean` tabulates how the number of letters of the special braid
`B_{s,v,α}` of `HJO.Mellit.braidDataOfColouring` changes across one level drop, for the event types
`A`, `C`, `D` and `E`:

| event | `k` | `∑ α` | moves |
| ----- | --- | ----- | ----- |
| `A`   | `+1`| `+1`  | `0` |
| `C`   | `0` | `+1`  | `+1` |
| `D`   | `0` | `+1`  | `+1` |
| `E`   | `0` | `0`   | `0` |

(each entry the change from the upper level to the lower one). **Type `B` is absent**, and the
lemma `HJO.Mellit.card_componentCrossingIndices_eq` does not state it either: it names exactly
those four types. This file adds the row, from the type-`B` descent identities of
`HJO/Shuffle/BraidValueBERanks.lean`:

| event | `k` | `∑ α` | moves |
| ----- | --- | ----- | ----- |
| `B`   | `-1`| `+1`  | `+2` |

## Why the arithmetic comes out this way, and why it is decisive

`HJO.Mellit.cast_totalCrossings` makes `∑_i α_i` the difference of two sums of antidiagonal indices,
with the pairing between the two halves of the colouring gone. Raising the level past a type-`B`
point adds `(X, Y)` to the crossed north steps and `(X - 1, Y)` to the crossed east steps
(`HJO.Mellit.Isolates.colouringNorth_eq_of_eventType_B`,
`HJO.Mellit.Isolates.colouringEast_eq_of_eventType_B`), and the antidiagonal index of the point
added on the east side is *one less* than that of the point added on the north side. So `∑ α` drops
by one as the level rises, i.e. rises by one as it falls — the same sign as at `A`, `C` and `D`. But
the width also rises by one as the level rises, where at `A` it *fell*. The two effects add rather
than cancel, and the lower special braid comes out with **two more moves** than the upper one:
`HJO.Mellit.Isolates.length_specialMoveList_of_eventType_B`.

That is the fact that settles the shape of rule `BE`'s braid-side obligation. The identity `hmove`
of `HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_move` applies `d^♭_-` to the braid
value of the *upper* data and asks for the braid value of the lower data (plus the `u`-term). At
type `A` the corresponding obligation was discharged by
`HJO.Sweep.dplusIntertwines_specialBraid`, a letter-by-letter intertwining — available exactly
because type `A` inserts an entry of multiplicity `1`, which contributes no letter, so the two
special braids have the *same* moves. Here they do not:
`HJO.Mellit.Isolates.length_specialMoveList_of_bePair` states the gap at precisely the two ranks
`hmove` reads, `k + 1` and `k`. Whatever closes `hmove`, it is not the type-`A` mechanism, and no
lowering-side analogue of `dplusIntertwines_specialBraid`, however complete, is enough on its own.
The companion file `HJO/Shuffle/BraidRankLower.lean` builds that analogue as far as it exists
and reports the same conclusion from the other side.

## What is not here

The *identity* of the two extra moves — which components they sit on and which letters they
contribute — is not determined here. That needs the type-`B` row of the position-and-multiplicity
table (where the new north step and the new east step are inserted into the two column listings),
which `HJO/Shuffle/BraidDataLevelDrop.lean` supplies for `C`, `D` and `E` and
`HJO/Shuffle/BraidTypeBDictionary.lean` supplies for `B`. Nothing here bears on whether `hmove` is
true.

## Hypotheses

`HJO.Mellit.Isolates` is the bracketing bundle, `0 < a`, `0 < b`, `0 < N` are carried as everywhere
in this layer, and `aN < ηlo` is the floor that `HJO.Mellit.lt_of_separatesDiagonal` derives from
`HJO.Mellit.SeparatesDiagonal`. The floor is what makes `0 < X` free: at `X = 0` a type-`B` event
forces `Y = 0` and `rk̂(0, 0) = 0`, which no level above `aN` lies below
(`HJO.Mellit.Isolates.pos_fst_of_eventType_B_of_lt`). So the origin, which is a
type-`B` event of every above-diagonal path, is excluded by the floor rather than by hypothesis.

**This is not that lemma.** `HJO.Mellit.card_componentCrossingIndices_eq` states the four increments
`A`, `C`, `D`, `E` and not this one, and `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` is
untouched.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, Sections 4 and 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {a b N X Y : ℕ} {ηlo ηhi : ℚ}

namespace Isolates

/-! ### The floor makes the origin impossible -/

/-- **A type-`B` event above the floor `aN` has positive abscissa.** Type `B` reads `Y = ŷ_X`, so
`X = 0` forces `Y = ŷ_0 = 0` on an above-diagonal path, and then `rk̂(X, Y) = 0`; but the lower
level is below that rank and above `aN ≥ 0`.

This is `HJO.Mellit.Isolates.pos_fst_of_eventType_B` with the hypothesis `(X, Y) ≠ (0, 0)` traded
for the floor — the same trade `HJO.Mellit.Isolates.pos_fst_of_eventType_D` makes at type `D`, and
by the same argument. It is why no clause below carries an origin hypothesis. -/
theorem pos_fst_of_eventType_B_of_lt (hI : Isolates a b N X Y ηlo ηhi)
    (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.B) : 0 < X := by
  rcases Nat.eq_zero_or_pos X with hX0 | hX0
  · exfalso
    obtain ⟨hfoot, -, -⟩ := eventType_eq_B_iff.1 hev
    have hY : Y = 0 := by rw [hX0, hy.1] at hfoot; exact hfoot
    have hrk : ((pointRank a b N (X, Y) : ℤ) : ℚ) = 0 := by
      rw [hX0, hY, cast_pointRank_eq a b N 0 0]
      push_cast
      ring
    have hnn : (0 : ℚ) ≤ ((a * N : ℕ) : ℚ) := Nat.cast_nonneg _
    have hlt := hI.ltP
    rw [hrk] at hlt
    linarith
  · exact hX0

/-! ### The total crossing count -/

/-- **At an event of type `B` the total crossing count rises by exactly one when the level falls.**
The east half gains the point `(X - 1, Y)` and the north half gains `(X, Y)` as the level rises, and
`HJO.Mellit.cast_totalCrossings` subtracts the second sum from the first, so the count changes by
`(X - 1 + Y) - (X + Y) = -1` upwards.

The sign is the same as at `A`, `C` and `D`; what distinguishes type `B` is the width, which rises
with the level here and falls at `A`. -/
theorem totalCrossings_of_eventType_B (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.B) :
    totalCrossings a b N y ηlo = totalCrossings a b N y ηhi + 1 := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_B_of_lt hηlo hy hev
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlo := cast_totalCrossings ha hb hN hI.lo hηlo hy (y := y)
  have hhi := cast_totalCrossings ha hb hN hI.hi hηhi hy (y := y)
  have hXcast : ((X - 1 : ℕ) : ℤ) = (X : ℤ) - 1 := by omega
  rw [hI.colouringNorth_eq_of_eventType_B ha hN hev,
    hI.colouringEast_eq_of_eventType_B ha hb hN hX0 hev,
    Finset.sum_insert (hI.notMem_colouringNorth_lo y),
    Finset.sum_insert (hI.notMem_colouringEast_pred_lo hX0 y)] at hhi
  push_cast at hhi
  rw [hXcast] at hhi
  omega

/-! ### The letter count -/

/-- **At an event of type `B` the lower special braid carries exactly two more moves than the upper
one.** The count of moves is `∑ α - k` (`HJO.Mellit.length_specialMoveList_braidDataOfColouring`,
stated without subtraction), `∑ α` rises by one as the level falls
(`HJO.Mellit.Isolates.totalCrossings_of_eventType_B`) and the width falls by one
(`HJO.Mellit.Isolates.card_colouringNorth_of_eventType_B`), so the two contributions add.

This is the row the table did not have, and it is the one that says rule `BE` is not a letterwise
intertwining: at type `A` the two special braids have the same moves, which is what makes
`HJO.Sweep.dplusIntertwines_specialBraid` applicable there. -/
theorem length_specialMoveList_of_eventType_B (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.B) :
    (Braid.specialMoveList
          (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).2).length + 2
      = (Braid.specialMoveList
          (braidDataOfColouring a b N y ηlo #(colouringNorth y ηlo)).2).length := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlo := length_specialMoveList_braidDataOfColouring ha hb hN hI.lo hηlo hy (y := y)
  have hhi := length_specialMoveList_braidDataOfColouring ha hb hN hI.hi hηhi hy (y := y)
  have hcard := hI.card_colouringNorth_of_eventType_B ha hN hev (y := y)
  have htot := hI.totalCrossings_of_eventType_B ha hb hN hηlo hy hev
  omega

/-- **The letter gap at the two ranks rule `BE` reads.** `hmove` of
`HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_move` compares
`HJO.Mellit.braidValueOfData` at the upper data of rank `k + 1` with the lower data of rank `k`,
where `k = #(colouringEast yB ηlo)`; at those two ranks the special braid of the lower data has two
more moves.

So the braid `d^♭_-` is applied to is *shorter*, by two letters, than the braid on the left-hand
side of `hmove`. -/
theorem length_specialMoveList_of_bePair (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {yB : Heights a b N} (hyB : IsAboveDiagonal yB)
    (hevB : eventType yB (X, Y) = EventType.B) {k : ℕ}
    (hk : #(colouringEast yB ηlo) = k) :
    (Braid.specialMoveList (braidDataOfColouring a b N yB ηhi (k + 1)).2).length + 2
      = (Braid.specialMoveList (braidDataOfColouring a b N yB ηlo k).2).length := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hNlo : #(colouringNorth yB ηlo) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.lo hηlo hyB, hk]
  have hNhi : #(colouringNorth yB ηhi) = k + 1 := by
    rw [hI.card_colouringNorth_of_eventType_B ha hN hevB, hNlo]
  have h := hI.length_specialMoveList_of_eventType_B ha hb hN hηlo hyB hevB
  rwa [hNlo, hNhi] at h

end Isolates

/-! ### Consistency check at the decided configuration

Everything below is read at the `2 × 3` configuration
`HJO.Mellit.dsc_eq_dminus_add_smul_example` is stated at and
`HJO.Mellit.Isolates.bePair_ranks` was checked at: the paths `(0,2,3)` and `(0,3,3)`, the point
`P = (1, 2)` of rank `4`, the levels `7/2` and `9/2`. The two crossed east steps are already
computed in `HJO.Mellit.colouringEast_be_witness`; the crossed north steps are computed here, the
two total crossing counts are read off both halves, and the two letter counts come out as `1` above
the drop and `3` below it.

The gap is then produced twice — once by `HJO.Mellit.Isolates.length_specialMoveList_of_bePair` from
the event type alone, and once from those two numbers — and the final `rfl` typechecks only if the
two routes state the same equation. What it checks is the sign and the size of the gap: a `+1`
instead of `+2`, a reversed direction, or a wrong insertion point in either descent identity fails
here. -/

/-- The crossed north steps of the type-`B` witness path at the two witness levels, computed
outright. The attack window of the `2 × 3` rectangle is `6`, so at `7/2` only the north step of rank
`0` is crossed, and at `9/2` the isolated point `(1, 2)` of rank `4` joins it. -/
theorem colouringNorth_be_witness :
    colouringNorth (![0, 2, 3] : Heights 2 3 1) (7 / 2) = {(0, 0)} ∧
      colouringNorth (![0, 2, 3] : Heights 2 3 1) (9 / 2) = {(0, 0), (1, 2)} := by
  have hn : northSteps (![0, 2, 3] : Heights 2 3 1) = {(0, 0), (0, 1), (1, 2)} := by decide
  refine ⟨?_, ?_⟩
  · rw [colouringNorth, hn]
    norm_num [pointRank, ParkingFunctions.abovePointRank, attackWindow, Finset.filter_insert,
      Finset.filter_singleton]
  · rw [colouringNorth, hn]
    norm_num [pointRank, ParkingFunctions.abovePointRank, attackWindow, Finset.filter_insert,
      Finset.filter_singleton]

/-- **The two total crossing counts at the witness, computed outright** from the two halves of the
colouring by `HJO.Mellit.cast_totalCrossings`, with no descent identity used: `(4) - (0) = 4` below
the drop and `(2 + 4) - (0 + 3) = 3` above it. -/
theorem totalCrossings_be_witness_adhoc :
    (totalCrossings 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) : ℤ) = 4 ∧
      (totalCrossings 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) : ℤ) = 3 := by
  have hy : IsAboveDiagonal (![0, 2, 3] : Heights 2 3 1) := by decide
  obtain ⟨hE, hE', -⟩ := colouringEast_be_witness
  obtain ⟨hN1, hN2⟩ := colouringNorth_be_witness
  refine ⟨?_, ?_⟩
  · rw [cast_totalCrossings (by norm_num) (by norm_num) (by norm_num) isolates_be_witness.lo
      (by norm_num) hy, hE, hN1]
    decide
  · rw [cast_totalCrossings (by norm_num) (by norm_num) (by norm_num) isolates_be_witness.hi
      (by norm_num) hy, hE', hN2]
    decide

/-- **The two letter counts at the witness**: the special braid above the drop carries one move and
the one below it carries three. Read from `HJO.Mellit.totalCrossings_be_witness_adhoc` and the two
widths `2` and `1`. -/
theorem length_specialMoveList_be_witness_adhoc :
    (Braid.specialMoveList
        (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2).length = 1 ∧
      (Braid.specialMoveList
        (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).2).length = 3 := by
  have hy : IsAboveDiagonal (![0, 2, 3] : Heights 2 3 1) := by decide
  obtain ⟨hN1, hN2⟩ := colouringNorth_be_witness
  obtain ⟨hT1, hT2⟩ := totalCrossings_be_witness_adhoc
  have hc1 : #(colouringNorth (![0, 2, 3] : Heights 2 3 1) (7 / 2)) = 1 := by rw [hN1]; decide
  have hc2 : #(colouringNorth (![0, 2, 3] : Heights 2 3 1) (9 / 2)) = 2 := by rw [hN2]; decide
  have hlo := length_specialMoveList_braidDataOfColouring (a := 2) (b := 3) (N := 1)
    (by norm_num) (by norm_num) (by norm_num) isolates_be_witness.lo (by norm_num) hy
  have hhi := length_specialMoveList_braidDataOfColouring (a := 2) (b := 3) (N := 1)
    (by norm_num) (by norm_num) (by norm_num) isolates_be_witness.hi (by norm_num) hy
  rw [hc1] at hlo
  rw [hc2] at hhi
  omega

/-- **The letter gap at the witness, ad hoc**: `1 + 2 = 3`, from the two computed counts. -/
theorem length_specialMoveList_gap_be_witness_adhoc :
    (Braid.specialMoveList
          (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2).length + 2
      = (Braid.specialMoveList
          (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).2).length := by
  obtain ⟨h1, h2⟩ := length_specialMoveList_be_witness_adhoc
  rw [h1, h2]

/-- **The letter gap at the witness, through the general result.** Every hypothesis of
`HJO.Mellit.Isolates.length_specialMoveList_of_bePair` is discharged by computation, so the
statement is about a configuration that occurs. -/
theorem length_specialMoveList_gap_be_witness :
    (Braid.specialMoveList
          (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2).length + 2
      = (Braid.specialMoveList
          (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).2).length :=
  isolates_be_witness.length_specialMoveList_of_bePair (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide)
    (show #(colouringEast (![0, 2, 3] : Heights 2 3 1) (7 / 2)) = 1 by
      rw [colouringEast_be_witness.1]; decide)

/-- **The two routes state the same equation.** -/
example : length_specialMoveList_gap_be_witness = length_specialMoveList_gap_be_witness_adhoc := rfl

end HJO.Mellit

end
