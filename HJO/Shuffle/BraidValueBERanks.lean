/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidValueBOrigin
public import HJO.Shuffle.BraidTypeATransfer
public import HJO.Shuffle.BraidDataLevelDrop

/-! # The type-`B` row of the descent table, and what rule `BE` asks of the braid value

`HJO.Mellit.SweepRecursionBE` is the fourth of the five properties
`HJO.Mellit.agreesWithDsc_of_recursions` asks of a candidate, and it is the only clause of Mellit's
Theorem 4.2 with *two* upper terms: the type-`B` path carrying `d_-` and the type-`E` path carrying
`u`. This file does not close it. It supplies the bookkeeping that any braid-side proof must start
from, and it states the residual the geometry reduces to.

## The type-`B` row of the descent table

`HJO/Shuffle/BraidLevelDrop.lean` tabulates, for each of `A`, `C`, `D`, `E`, how the two halves of
the colouring move when the level drops past the isolated point. **Type `B` is absent from that
table**, and the two statements of it that do exist
(`HJO.Mellit.Isolated.colouring_hi_eq_of_eventType_B` and
`HJO.Mellit.Isolated.sweepWidth_eq_of_eventType_B`) speak of the *combined* colouring, are phrased
against a second copy of the bracketing hypothesis (`HJO.Mellit.Isolated`, not
`HJO.Mellit.Isolates`), and carry the geometry as `ht y X = Y` rather than as an event type. So they
do not apply in the braid-side setting.

The row is: raising the level past a type-`B` point adds `(X, Y)` to the crossed north steps — the
north step the path takes out of `P` — and `(X - 1, Y)` to the crossed east steps, the east step the
path takes into `P`. Both halves grow by exactly one. Everything here comes from the general descent
lemmas `HJO.Mellit.Isolates.erase_colouringNorth` and `HJO.Mellit.Isolates.erase_colouringEast` with
the four memberships evaluated, exactly as the type-`A` row is; the event type does nothing else.

## Where `0 < X` comes from, and why the origin is not an exception to be assumed away

The east half's row needs `0 < X`, and at a type-`B` event that is *equivalent* to the point not
being the origin: type `B` says `Y = ŷ_X`, so `X = 0` forces `Y = ŷ_0 = 0`
(`HJO.Mellit.Isolates.pos_fst_of_eventType_B`). At the origin the two points the level drop would
add coincide — `X - 1 = 0 = X` in `ℕ` — so the colouring grows by *one*, not two, and the east half
does not grow at all. That is exactly the collapse
`HJO.Mellit.Isolates.colouringEast_eq_empty_of_origin` records, and it is why the origin is a
separate clause rather than an instance of this one.

## The `u`-term is the left-hand side's own braid data, rigidly rotated

At a type-`E` event both halves of the colouring stand still
(`HJO.Mellit.Isolates.colouringNorth_eq_of_eventType_E`,
`HJO.Mellit.Isolates.colouringEast_eq_of_eventType_E`), so the type-`E` path's colouring at the
*upper* level is its colouring at the lower level, which rule `BE` requires to be the type-`B`
path's. Hence `HJO.Mellit.Isolates.colouring_hi_eq_of_bePair`: the `u`-term of rule `BE` is the
candidate evaluated at the **lower** colouring, read at the upper level. For the braid value that
pins the term down completely up to a rotation: its multiplicities are those of the left-hand side
(`HJO.Mellit.Isolates.braidData_bePair_snd`) and its positions are the left-hand side's rotated by
the one common shift (`HJO.Mellit.Isolates.braidData_bePair_fst`). So the braid-side content of the
`u`-term is rotation behaviour and nothing else — the reading
`HJO.Mellit.Isolates.braidData_of_eventType_E` already records for a single path, transported to the
pair rule `BE` actually asks about.

## The grading, and the anomaly below the level `aN`

With `k := #(colouringEast yB ηlo)` the clause reads, rank by rank: the left side at rank `k`, the
`d_-` term at index `sweepWidth yB P` applied to a value of rank `k + 1`, the `u` term at rank `k`.
`HJO.Mellit.Isolates.bePair_ranks` proves all three numbers, and they match — `d_-` really does
lower `k + 1` to `k` — **but only above the level `aN`**. The width is
`#(colouringNorth yB ηhi)` at every bracketed point
(`HJO.Mellit.Isolates.sweepWidth_eq_card_colouringNorth`, unconditional), and
`#(colouringNorth y η) = #(colouringEast y η)` is
`HJO.Mellit.card_colouringNorth_eq_card_colouringEast`, which costs `aN < η` and is false below it:
at a level in `(0, aN)` the level line leaves the region at the far corner rather than at an east
step, so there is one crossed north step with no crossed east step to pair with.
`HJO.Mellit.Isolates.sweepWidth_eq_card_colouringEast_of_lt_hi` is the sharpest form the identity
has — it asks `aN < ηhi` where `HJO.Mellit.Isolates.sweepWidth_eq_card_colouringEast`
asks `aN < ηlo`, which is a gain only at the points of rank exactly `aN` — and below that there is
no form of it.

`HJO.Mellit.SweepRecursionBE` quantifies over *every* bracketed point of the rectangle, so it
includes type-`B` events of rank `< aN`, where the braid rank and the width differ by one and the
clause is not a graded identity at all. Nothing here closes those, and no result proved elsewhere
does.

## What remains, precisely

`HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_move` is the clause at one bracketed
point given **one** hypothesis, `hmove`, which mentions no colouring, no path, no event type and no
width: an identity between `HJO.Mellit.braidValueOfData` at three explicit special-braid data
tuples. That is the shape the type-`C` clause was reduced to before it was closed, and it is all the
geometry is worth here. The braid combinatorics behind `hmove` is untouched, and no proved result
supports it: there is no `d_-` analogue of `HJO.Sweep.dplusIntertwines_specialBraid` here, and no
braid-monoid map for one to be stated against.

`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` covers the whole level recursion and this file
closes none of its clauses.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, Sections 4 and 5, for
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, `HJO.Mellit.dsc_eq_dminus_add_smul`,
`HJO.Mellit.Isolates.notMem_colouringNorth_lo`,
`HJO.Mellit.card_colouringNorth_eq_card_colouringEast`, `HJO.Mellit.braidDataOfColouring`,
`HJO.Paths.eventType` and `HJO.Paths.sweepWidth`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {a b N X Y : ℕ} {ηlo ηhi : ℚ}

namespace Isolates

/-! ### The origin is the only type-`B` event in the leftmost column -/

/-- **A type-`B` event away from the origin has positive abscissa.** Type `B` reads `Y = ŷ_X`, and
an above-diagonal path has `ŷ_0 = 0`, so `X = 0` forces `Y = 0`. The converse is
`HJO.Mellit.eventType_origin_eq_B`: the origin *is* a type-`B` event of every above-diagonal path.
So on an above-diagonal path "type `B` and not the origin" is exactly "type `B` and `0 < X`". -/
theorem pos_fst_of_eventType_B {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.B) (hne : ((X, Y) : ℕ × ℕ) ≠ ((0 : ℕ), (0 : ℕ))) :
    0 < X := by
  obtain ⟨hfoot, -, -⟩ := eventType_eq_B_iff.1 hev
  rcases Nat.eq_zero_or_pos X with hX0 | hX0
  · subst hX0
    have hY : Y = 0 := by simpa [hy.1] using hfoot
    subst hY
    simp at hne
  · exact hX0

/-! ### The type-`B` row of the descent table -/

/-- **At an event of type `B` the crossed north steps gain `(X, Y)` when the level is raised**: it
is the north step the path takes out of `P`, and the point below it in the column is no north step
at all, the path arriving at `P` from the left.

The mirror of `HJO.Mellit.Isolates.colouringNorth_eq_of_eventType_A`, and the row the descent table
did not have. At `Y = 0` the erased point `(X, Y - 1)` is `(X, 0) = (X, Y)` itself, which is kept
out of the lower colouring by its rank rather than by not being a north step
(`HJO.Mellit.Isolates.notMem_colouringNorth_lo`); both cases are handled. -/
theorem colouringNorth_eq_of_eventType_B (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.B) :
    colouringNorth y ηhi = insert (X, Y) (colouringNorth y ηlo) := by
  obtain ⟨hfoot, hX, htop⟩ := eventType_eq_B_iff.1 hev
  have hfoot' : Y = ht y X := hfoot
  have htop' : Y < ht y (X + 1) := htop
  have hmem : ((X, Y) : ℕ × ℕ) ∈ colouringNorth y ηhi := by
    rw [hI.mem_colouringNorth_hi_iff ha hN y]
    exact mem_northSteps_iff.2 ⟨hX, by omega, htop⟩
  have hlo : ((X, Y - 1) : ℕ × ℕ) ∉ colouringNorth y ηlo := by
    rcases Nat.eq_zero_or_pos Y with hY | hY
    · subst hY
      simpa using hI.notMem_colouringNorth_lo y
    · exact notMem_colouringNorth_of_notMem_northSteps fun h => by
        have h2 : X < a * N ∧ ht y X ≤ Y - 1 ∧ Y - 1 < ht y (X + 1) := mem_northSteps_iff.1 h
        omega
  have h := hI.erase_colouringNorth ha hN y
  rw [Finset.erase_eq_self.2 hlo] at h
  rw [h, Finset.insert_erase hmem]

/-- **At an event of type `B` the crossed east steps gain `(X - 1, Y)` when the level is raised**:
it is the east step the path takes into `P`. The point `(X, Y)` is no east step of the path, which
leaves `P` upwards.

`0 < X` is needed and is no restriction beyond excluding the origin, by
`HJO.Mellit.Isolates.pos_fst_of_eventType_B`. -/
theorem colouringEast_eq_of_eventType_B (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX0 : 0 < X) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.B) :
    colouringEast y ηhi = insert (X - 1, Y) (colouringEast y ηlo) := by
  obtain ⟨hfoot, hX, htop⟩ := eventType_eq_B_iff.1 hev
  have hfoot' : Y = ht y X := hfoot
  have htop' : Y < ht y (X + 1) := htop
  have hmem : ((X - 1, Y) : ℕ × ℕ) ∈ colouringEast y ηhi := by
    rw [hI.mem_colouringEast_pred_hi_iff ha hb hN hX0 y]
    exact mem_eastSteps_iff.2 ⟨by omega,
      by simpa [show X - 1 + 1 = X from by omega] using hfoot'⟩
  have hlo : ((X, Y) : ℕ × ℕ) ∉ colouringEast y ηlo := by
    rw [hI.mem_colouringEast_lo_iff ha hb hN y]
    intro h
    have h2 := mem_eastSteps_iff.1 h
    omega
  have h := hI.erase_colouringEast ha hN y
  rw [Finset.erase_eq_self.2 hlo] at h
  rw [h, Finset.insert_erase hmem]

/-- **At an event of type `B` the width rises by exactly one when the level is raised**, matching
the `d_-` of rule `B`. -/
theorem card_colouringNorth_of_eventType_B (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.B) :
    #(colouringNorth y ηhi) = #(colouringNorth y ηlo) + 1 := by
  rw [hI.colouringNorth_eq_of_eventType_B ha hN hev,
    Finset.card_insert_of_notMem (hI.notMem_colouringNorth_lo y)]

/-- **At an event of type `B` the number of crossed east steps rises by exactly one when the level
is raised.** This is the row missing from the descent table: `A` has it
(`HJO.Mellit.Isolates.card_colouringEast_of_eventType_A`), `D` has it
(`HJO.Mellit.Isolates.card_colouringEast_eq_of_eventType_D`), `C` and `E` have the sets equal, and
`B` has none. It is what fixes the braid rank on the two sides of the `d_-` of rule `BE`. -/
theorem card_colouringEast_of_eventType_B (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX0 : 0 < X) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.B) :
    #(colouringEast y ηhi) = #(colouringEast y ηlo) + 1 := by
  rw [hI.colouringEast_eq_of_eventType_B ha hb hN hX0 hev,
    Finset.card_insert_of_notMem (hI.notMem_colouringEast_pred_lo hX0 y)]

/-! ### The width, as far as it is the braid rank -/

/-- **The width at the isolated point is the number of crossed north steps at the upper level**, at
every bracketed point, with no hypothesis at all beyond the bracketing: it is
`HJO.Mellit.liveSteps_eq_colouringNorth` counted. -/
theorem sweepWidth_eq_card_colouringNorth (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) :
    sweepWidth y (X, Y) = #(colouringNorth y ηhi) := by
  rw [sweepWidth, liveSteps_eq_colouringNorth hI y]

/-- **The width is the braid rank at the upper level**, which is what makes the operator of an event
act between the graded pieces the two braid values live in.
`HJO.Mellit.Isolates.sweepWidth_eq_card_colouringEast` asks `aN < ηlo`; this asks `aN < ηhi`, which
is the weakest the `HJO.Mellit.card_colouringNorth_eq_card_colouringEast` route allows, and the
difference is exactly the points of rank `aN`.

Below `aN` there is no such identity: `HJO.Mellit.card_colouringNorth_eq_card_colouringEast` is
false there — one component of the level line ends at the far corner of the rectangle rather than at
an east step of the path — and `HJO.Mellit.sweepWidth_origin_ne_card_colouringEast_example` exhibits
the two numbers differing. -/
theorem sweepWidth_eq_card_colouringEast_of_lt_hi (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηhi : ((a * N : ℕ) : ℚ) < ηhi) {y : Heights a b N}
    (hy : IsAboveDiagonal y) : sweepWidth y (X, Y) = #(colouringEast y ηhi) := by
  rw [hI.sweepWidth_eq_card_colouringNorth y,
    card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]

/-! ### The type-`E` half of rule `BE` -/

/-- **At an event of type `E` the colouring does not move.** Both halves stand still, so the union
does. -/
theorem colouring_eq_of_eventType_E (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.E) : colouring y ηlo = colouring y ηhi := by
  rw [colouring_eq_union, colouring_eq_union, hI.colouringNorth_eq_of_eventType_E ha hN hev,
    hI.colouringEast_eq_of_eventType_E ha hN hy hev]

/-- **The `u`-term of rule `BE` is the candidate at the lower colouring, read at the upper level.**
The type-`E` path's colouring does not move across the drop, and rule `BE` asks it to agree with the
type-`B` path's at the lower level; so the second summand of the rule is not a new value at all but
the left-hand side's own argument, evaluated at the other level. -/
theorem colouring_hi_eq_of_bePair (ha : 0 < a) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    {yB yE : Heights a b N} (hyE : IsAboveDiagonal yE)
    (hevE : eventType yE (X, Y) = EventType.E) (hcol : colouring yB ηlo = colouring yE ηlo) :
    colouring yE ηhi = colouring yB ηlo := by
  rw [← hI.colouring_eq_of_eventType_E ha hN hyE hevE]
  exact hcol.symm

/-- **The `u`-term has the braid rank of the left-hand side.** -/
theorem colouringEast_eq_of_bePair (ha : 0 < a) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    {yB yE : Heights a b N} (hyE : IsAboveDiagonal yE)
    (hevE : eventType yE (X, Y) = EventType.E) (hcol : colouring yB ηlo = colouring yE ηlo) :
    colouringEast yE ηhi = colouringEast yB ηlo := by
  rw [← hI.colouringEast_eq_of_eventType_E ha hN hyE hevE]
  exact colouringEast_congr hcol.symm

/-! ### The three ranks of rule `BE` -/

/-- **The grading of rule `BE`, at a type-`B`/`E` pair above the level `aN`.** The left-hand side
has braid rank `k`; the `d_-` term is indexed by `k + 1` and applied to a value of braid rank
`k + 1`; the `u` term has braid rank `k`. So the clause is an identity in `V_k`, which is the first
thing a braid-side proof of it needs and the first thing that fails below `aN`. -/
theorem bePair_ranks (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    (hηhi : ((a * N : ℕ) : ℚ) < ηhi) {yB yE : Heights a b N} (hyB : IsAboveDiagonal yB)
    (hyE : IsAboveDiagonal yE) (hevB : eventType yB (X, Y) = EventType.B)
    (hevE : eventType yE (X, Y) = EventType.E) (hcol : colouring yB ηlo = colouring yE ηlo)
    (hne : ((X, Y) : ℕ × ℕ) ≠ ((0 : ℕ), (0 : ℕ))) :
    #(colouringEast yB ηhi) = #(colouringEast yB ηlo) + 1 ∧
      sweepWidth yB (X, Y) = #(colouringEast yB ηlo) + 1 ∧
        #(colouringEast yE ηhi) = #(colouringEast yB ηlo) := by
  have hX0 : 0 < X := pos_fst_of_eventType_B hyB hevB hne
  have hcard := hI.card_colouringEast_of_eventType_B ha hb hN hX0 hevB (y := yB)
  refine ⟨hcard, ?_, by rw [hI.colouringEast_eq_of_bePair ha hN hyE hevE hcol]⟩
  rw [hI.sweepWidth_eq_card_colouringEast_of_lt_hi hb hN hηhi hyB, hcard]

/-! ### The braid data of the `u`-term -/

/-- **The `u`-term's multiplicities are those of the left-hand side.** Entry by entry: the type-`E`
path's data does not move across the drop
(`HJO.Mellit.Isolates.braidData_snd_of_eventType_E`) and at the lower level it is the type-`B`
path's, the two colourings agreeing there. -/
theorem braidData_bePair_snd (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {yB yE : Heights a b N} (hyE : IsAboveDiagonal yE)
    (hevE : eventType yE (X, Y) = EventType.E) (hcol : colouring yB ηlo = colouring yE ηlo)
    {k : ℕ} (hk : #(colouringEast yB ηlo) = k) (i : Fin k) :
    (braidDataOfColouring a b N yE ηhi k).2 i = (braidDataOfColouring a b N yB ηlo k).2 i := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hcongr : braidDataOfColouring a b N yB ηlo k = braidDataOfColouring a b N yE ηlo k :=
    braidDataOfColouring_congr k (colouringNorth_congr hcol) (colouringEast_congr hcol)
  have hiN : (i : ℕ) < #(colouringNorth yE ηhi) := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hyE,
      hI.colouringEast_eq_of_bePair ha hN hyE hevE hcol, hk]
    exact i.isLt
  rw [hcongr]
  exact (braidData_snd_of_eventType_E ha hb hN hI hηlo hyE i hevE hiN).symm

/-- **The `u`-term's positions are those of the left-hand side, rigidly rotated.** The one common
shift is `θ · (c(ηhi) − c(ηlo))`, the same for every index, as at every drop. With
`HJO.Mellit.Isolates.braidData_bePair_snd` this says that the braid-side content of the `u`-term of
rule `BE` is the rotation behaviour of `HJO.Braid.specialBraid` and nothing else — and that
behaviour is not invariance: `HJO.Braid.exists_rotation_specialBraid_ne` refutes the general form of
it. -/
theorem braidData_bePair_fst (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {yB yE : Heights a b N} (hyE : IsAboveDiagonal yE)
    (hevE : eventType yE (X, Y) = EventType.E) (hcol : colouring yB ηlo = colouring yE ηlo)
    {k : ℕ} (hk : #(colouringEast yB ηlo) = k) (i : Fin k) :
    (braidDataOfColouring a b N yB ηlo k).1 i
      = Int.fract ((braidDataOfColouring a b N yE ηhi k).1 i
          + sweepTheta a b N * (levelIntercept a N ηhi - levelIntercept a N ηlo)) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (by positivity) hηlo
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (by positivity) hηhi
  have hcongr : braidDataOfColouring a b N yB ηlo k = braidDataOfColouring a b N yE ηlo k :=
    braidDataOfColouring_congr k (colouringNorth_congr hcol) (colouringEast_congr hcol)
  have hiE : (i : ℕ) < #(colouringEast yE ηhi) := by
    rw [hI.colouringEast_eq_of_bePair ha hN hyE hevE hcol, hk]
    exact i.isLt
  rw [hcongr]
  exact braidData_fst_of_eventType_E ha hb hN hI hlopos hhipos hyE i hevE hiE

/-! ### The clause, reduced to one identity of braid values -/

/-- **Rule `BE` for `HJO.Mellit.braidValueColouring`, given one identity of braid values.** Every
piece of geometry is discharged: the representative `HJO.Mellit.colouringRep` chooses is irrelevant
(`HJO.Mellit.braidValueColouring_colouring`), the three braid ranks are `k`, `k + 1` and `k`
(`HJO.Mellit.Isolates.bePair_ranks`), and the width the `d_-` carries is `k + 1`. What is left is
`hmove`, which mentions no path, no colouring, no event type and no width — an identity between
`HJO.Mellit.braidValueOfData` at three explicit special-braid data tuples.

This is the shape the type-`C` clause was reduced to before it was closed
(`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_move`), and it is as
far as the geometry goes. It is *not* progress on the braid combinatorics: `hmove` has nothing to
stand on, there being no `d_-` counterpart of `HJO.Sweep.dplusIntertwines_specialBraid` here. -/
theorem braidValueColouring_eq_dminus_add_smul_of_move {L : Type*} [Field L] [Algebra ℚ L]
    (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a)
    (hb : 0 < b) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    (hηhi : ((a * N : ℕ) : ℚ) < ηhi) {yB yE : Heights a b N} (hyB : IsAboveDiagonal yB)
    (hyE : IsAboveDiagonal yE) (hevB : eventType yB (X, Y) = EventType.B)
    (hevE : eventType yE (X, Y) = EventType.E) (hcol : colouring yB ηlo = colouring yE ηlo)
    (hne : ((X, Y) : ℕ × ℕ) ≠ ((0 : ℕ), (0 : ℕ))) {k : ℕ} (hk : #(colouringEast yB ηlo) = k)
    (hmove : braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N yB ηlo k).1
          (braidDataOfColouring a b N yB ηlo k).2
        = dminus q (k + 1) (braidValueOfData q u hq hq1 hqp hr a b N
              (braidDataOfColouring a b N yB ηhi (k + 1)).1
              (braidDataOfColouring a b N yB ηhi (k + 1)).2)
          + u • braidValueOfData q u hq hq1 hqp hr a b N
              (braidDataOfColouring a b N yE ηhi k).1
              (braidDataOfColouring a b N yE ηhi k).2) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring yB ηlo)
      = dminus q (sweepWidth yB (X, Y))
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring yB ηhi))
        + u • braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring yE ηhi) := by
  obtain ⟨hBhi, hwid, hEhi⟩ :=
    hI.bePair_ranks ha hb hN hηhi hyB hyE hevB hevE hcol hne
  rw [braidValueColouring_colouring q u hq hq1 hqp hr hyB,
    braidValueColouring_colouring q u hq hq1 hqp hr hyB,
    braidValueColouring_colouring q u hq hq1 hqp hr hyE,
    braidValueOfPath_eq_braidValueOfData q u hq hq1 hqp hr yB ηlo hk,
    braidValueOfPath_eq_braidValueOfData q u hq hq1 hqp hr yB ηhi (by rw [hBhi, hk]),
    braidValueOfPath_eq_braidValueOfData q u hq hq1 hqp hr yE ηhi (by rw [hEhi, hk]),
    show sweepWidth yB (X, Y) = k + 1 from by rw [hwid, hk]]
  exact hmove

end Isolates

/-! ### Consistency check

The three rank equations are re-derived at the decided configuration
`HJO.Mellit.dsc_eq_dminus_add_smul_example` is stated at — the `2 × 3` rectangle, the paths
`(0,2,3)` and `(0,3,3)`, the point `(1, 2)` of rank `4`, the levels `7/2` and `9/2` — once through
`HJO.Mellit.Isolates.bePair_ranks` and once ad hoc from the three crossed-east-step sets computed
outright. The final `rfl` is what makes it a check: it typechecks only if the two routes state
literally the same three equations, so a reversed direction or an off-by-one in the general result
would fail it here. -/

/-- The crossed east steps of the two witness paths at the two witness levels, computed outright.
The rational level is outside the kernel's arithmetic, so this goes by `norm_num` on the explicit
`Finset`s, as `HJO.Mellit.colouring_thm42_be_witness` does. -/
theorem colouringEast_be_witness :
    colouringEast (![0, 2, 3] : Heights 2 3 1) (7 / 2) = {(1, 3)} ∧
      colouringEast (![0, 2, 3] : Heights 2 3 1) (9 / 2) = {(0, 2), (1, 3)} ∧
        colouringEast (![0, 3, 3] : Heights 2 3 1) (9 / 2) = {(1, 3)} := by
  have he : eastSteps (![0, 2, 3] : Heights 2 3 1) = {(0, 2), (1, 3)} := by decide
  have he' : eastSteps (![0, 3, 3] : Heights 2 3 1) = {(0, 3), (1, 3)} := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [colouringEast, he]
    norm_num [pointRank, ParkingFunctions.abovePointRank, Finset.filter_insert,
      Finset.filter_singleton]
  · rw [colouringEast, he]
    norm_num [pointRank, ParkingFunctions.abovePointRank, Finset.filter_insert,
      Finset.filter_singleton]
  · rw [colouringEast, he']
    norm_num [pointRank, ParkingFunctions.abovePointRank, Finset.filter_insert,
      Finset.filter_singleton]

/-- The bracketing hypothesis at the decided configuration: `7/2 < rk̂(1,2) = 4 < 9/2`, and no other
rank of the `2 × 3` rectangle lies between the two levels. -/
theorem isolates_be_witness : Isolates 2 3 1 1 2 (7 / 2) (9 / 2) := by
  have hrank : pointRank 2 3 1 (1, 2) = 4 := by
    norm_num [pointRank, ParkingFunctions.abovePointRank]
  refine ⟨⟨3, by norm_num⟩, ⟨4, by norm_num⟩, ?_, ?_, ?_, by norm_num, by norm_num⟩
  · rw [hrank]; norm_num
  · rw [hrank]; norm_num
  · intro Q _ _ h1 h2
    rw [hrank] at *
    have hr1 : (3 : ℤ) < pointRank 2 3 1 Q := by
      have h : ((3 : ℤ) : ℚ) < ((pointRank 2 3 1 Q : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast h
    have hr2 : pointRank 2 3 1 Q < 5 := by
      have h : ((pointRank 2 3 1 Q : ℤ) : ℚ) < ((5 : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast h
    omega

/-- **The three rank equations at the witness, ad hoc**: read off
`HJO.Mellit.colouringEast_be_witness` and the kernel's own evaluation of the width, with
`HJO.Mellit.Isolates.bePair_ranks` unused. -/
theorem bePair_ranks_be_witness_adhoc :
    #(colouringEast (![0, 2, 3] : Heights 2 3 1) (9 / 2))
        = #(colouringEast (![0, 2, 3] : Heights 2 3 1) (7 / 2)) + 1 ∧
      sweepWidth (![0, 2, 3] : Heights 2 3 1) (1, 2)
          = #(colouringEast (![0, 2, 3] : Heights 2 3 1) (7 / 2)) + 1 ∧
        #(colouringEast (![0, 3, 3] : Heights 2 3 1) (9 / 2))
          = #(colouringEast (![0, 2, 3] : Heights 2 3 1) (7 / 2)) := by
  obtain ⟨e1, e2, e3⟩ := colouringEast_be_witness
  have hw : sweepWidth (![0, 2, 3] : Heights 2 3 1) (1, 2) = 2 := by decide
  rw [e1, e2, e3, hw]
  exact ⟨by decide, by decide, by decide⟩

/-- **The three rank equations at the witness, through the general result.** Every hypothesis of
`HJO.Mellit.Isolates.bePair_ranks` is discharged by computation, so the statement is about a
configuration that occurs. -/
theorem bePair_ranks_be_witness :
    #(colouringEast (![0, 2, 3] : Heights 2 3 1) (9 / 2))
        = #(colouringEast (![0, 2, 3] : Heights 2 3 1) (7 / 2)) + 1 ∧
      sweepWidth (![0, 2, 3] : Heights 2 3 1) (1, 2)
          = #(colouringEast (![0, 2, 3] : Heights 2 3 1) (7 / 2)) + 1 ∧
        #(colouringEast (![0, 3, 3] : Heights 2 3 1) (9 / 2))
          = #(colouringEast (![0, 2, 3] : Heights 2 3 1) (7 / 2)) :=
  isolates_be_witness.bePair_ranks (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [colouring_thm42_be_witness.1, colouring_thm42_be_witness.2]) (by decide)

/-- **The two routes state the same three equations.** -/
example : bePair_ranks_be_witness = bePair_ranks_be_witness_adhoc := rfl

end HJO.Mellit

end
