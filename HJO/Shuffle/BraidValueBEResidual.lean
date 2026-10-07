/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidRankLower
public import HJO.Shuffle.BraidTypeBMoveCount
public import HJO.Shuffle.MellitThm58Floor
public meta import HJO.Attr

/-! # Rule `BE` with the `d^♭_-` eliminated: the residual the lowering intertwiner leaves

`HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_move` reduces rule `BE` at one
bracketed point to `hmove`, an identity between `HJO.Mellit.braidValueOfData` at three explicit data
tuples with a `d^♭_-` in it. This file removes the `d^♭_-` in favour of the lowering intertwiner
`HJO.Sweep.DminusIntertwines` of `HJO/Shuffle/BraidRankLower.lean`, and what is left is
`HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_intertwines`:

*given* a rank-`k` braid `Z` intertwined with the special braid of the upper data, rule `BE` at the
point follows from an identity between three rank-`k` values and **no operator at all** —

`D(lower) = D^{e_1}(Z, upper) + u·D(type-E upper)`,

where `D^{e_1}` is `HJO.Sweep.braidValueElemSymmOfData`: the same prefactor and the same
representation as `HJO.Mellit.braidValueOfData`, applied to `e_1·d_+^k(1)` instead of to
`d_+^k(1)`, because `HJO.Sweep.dminus_dplusIter` says that is what `d^♭_-` does to the vacuum tower.

## What the reduction is worth, and what it is not

It is worth exactly one thing: it shows where the remaining content sits. The `d^♭_-`, the width,
the event types and the colourings are all gone; what is left is a statement about three braid words
at one rank, a rigid rotation (`HJO.Mellit.Isolates.braidData_bePair_fst`) and one factor `e_1`.

It is **not** progress on the braid combinatorics, and the two hypotheses it asks for are not close
to being met.

* `hXY` is not available. `HJO/Shuffle/BraidRankLower.lean` intertwines the `T`, `T̄` and `y_1`
  letters at indices below `k` and **no move-letter at all**: the `z` letter is conditional on an
  unproved operator identity and the `ỹ` letter's loop reaches the one index `d^♭_-` does not
  commute with. So for a special braid with at least one move, `hXY` has no proved route.
* `hres` cannot be the type-`A` identity in disguise.
  `HJO.Mellit.Isolates.length_specialMoveList_of_bePair` shows the lower special braid carries
  **two more moves** than the upper one at exactly these ranks, so `Z` — which any letterwise
  intertwining would give the upper braid's shape — is not the lower special braid, and `hres` is a
  genuine identity between differently-shaped words rather than a rewriting.

## The whole floored clause is the per-point identity, and nothing else

`HJO.Mellit.braidValueColouring_sweepRecursionBEFloor_of_move` closes the loop on the geometry:
`HJO.Mellit.SweepRecursionBEFloor` for `HJO.Mellit.braidValueColouring` follows from `hmove`
supplied at every bracketed point, with **every** other hypothesis of
`HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_move` derived from the clause's own:
the bracketing bundle `HJO.Mellit.Isolates` is assembled from the clause's seven hypotheses, the
upper floor `aN < ηhi` follows from the lower one, and the origin exclusion `(X, Y) ≠ (0, 0)` is
free — `HJO.Mellit.Isolates.pos_fst_of_eventType_B_of_lt` gets `0 < X` out of the floor, so no
origin clause is needed and `HJO.Mellit.SweepRecursionBOrigin` does not enter.

So the *only* thing between the braid value and `HJO.Mellit.SweepRecursionBEFloor` is `hmove` at
every bracketed point of every rectangle: one identity between three `HJO.Mellit.braidValueOfData`
at explicit data tuples, mentioning no colouring, path, event type or width. It is not proved at any
point.

## Genericity

Nothing new is excluded: `q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0`, `r * r = q` are `HJO.Sweep.braidRepMellit`'s
and are what `HJO.Mellit.braidValueColouring` already needs. `u ≠ 0` is not spent and no inverse in
`u` is evaluated. The floor `aN < ηlo` is not asked for here — the per-point clause asks `aN < ηhi`
and `(X, Y) ≠ (0, 0)`, and both are available wherever it is applied, the second because a level
above `aN` cannot lie below the rank of the origin
(`HJO.Mellit.Isolates.pos_fst_of_eventType_B_of_lt`).

`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` covers the whole level recursion; this file
closes none of its clauses. `HJO.Mellit.SweepRecursionBEFloor` itself is proved by a different
route: `HJO.Mellit.braidValueColouring_sweepRecursionBEFloor` (`HJO/Shuffle/BraidBECut.lean`), from
the `hmove` route via `HJO.Mellit.braidValueColouring_sweepRecursionBEFloor_of_cut`.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, Sections 4 and 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N X Y : ℕ} {ηlo ηhi : ℚ}

namespace Isolates

/-- **Rule `BE` for `HJO.Mellit.braidValueColouring` from the lowering intertwiner and one
operator-free identity.** The hypothesis `hmove` of
`HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_move` is replaced by two: a rank-`k`
braid `Z` intertwined with the special braid of the upper data (`hXY`), and the identity `hres`
between three rank-`k` values in which no operator occurs — the `d^♭_-` having been absorbed into
`Z` and into the one factor `e_1` that `HJO.Sweep.dminus_dplusIter` puts on the vacuum tower.

Neither hypothesis is discharged anywhere. See the module docstring for why `hXY` has no proved
route at a braid with a move, and `HJO.Mellit.Isolates.length_specialMoveList_of_bePair` for why
`hres` is not a rewriting. -/
theorem braidValueColouring_eq_dminus_add_smul_of_intertwines
    (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a)
    (hb : 0 < b) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    (hηhi : ((a * N : ℕ) : ℚ) < ηhi) {yB yE : Heights a b N} (hyB : IsAboveDiagonal yB)
    (hyE : IsAboveDiagonal yE) (hevB : eventType yB (X, Y) = EventType.B)
    (hevE : eventType yE (X, Y) = EventType.E) (hcol : colouring yB ηlo = colouring yE ηlo)
    (hne : ((X, Y) : ℕ × ℕ) ≠ ((0 : ℕ), (0 : ℕ))) {k : ℕ} (hk : #(colouringEast yB ηlo) = k)
    {Z : Braid.BraidMonoid k}
    (hXY : DminusIntertwines q u hq hq1 hqp hr k
      (specialBraid (sweepTheta a b N) (braidDataOfColouring a b N yB ηhi (k + 1)).1
        (braidDataOfColouring a b N yB ηhi (k + 1)).2) Z)
    (hres : braidValueOfData q u hq hq1 hqp hr a b N
          (braidDataOfColouring a b N yB ηlo k).1
          (braidDataOfColouring a b N yB ηlo k).2
        = braidValueElemSymmOfData q u hq hq1 hqp hr a b N Z
            (braidDataOfColouring a b N yB ηhi (k + 1)).1
            (braidDataOfColouring a b N yB ηhi (k + 1)).2
          + u • braidValueOfData q u hq hq1 hqp hr a b N
              (braidDataOfColouring a b N yE ηhi k).1
              (braidDataOfColouring a b N yE ηhi k).2) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring yB ηlo)
      = dminus q (sweepWidth yB (X, Y))
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring yB ηhi))
        + u • braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring yE ηhi) :=
  hI.braidValueColouring_eq_dminus_add_smul_of_move q u hq hq1 hqp hr ha hb hN hηhi hyB hyE
    hevB hevE hcol hne hk
    (by rw [hres, ← dminus_braidValueOfData_of_dminusIntertwines a b N hXY])

end Isolates

/-! ### The floored clause, reduced to the per-point identity -/

/-- **`HJO.Mellit.SweepRecursionBEFloor` for `HJO.Mellit.braidValueColouring`, given `hmove` at
every bracketed point.** The one hypothesis is the data identity, quantified over the two levels,
the point and the two paths, with the rank taken to be `#(colouringEast yB ηlo)`; everything else
the per-point clause `HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_move` asks for
is derived from the clause's own hypotheses.

Three things are discharged here and worth naming. The bracketing bundle `HJO.Mellit.Isolates` is
exactly the clause's seven hypotheses repackaged. The upper floor `aN < ηhi` follows from the lower
floor through `ηlo < rk̂(P) < ηhi`, so the sharp width identity
`HJO.Mellit.Isolates.sweepWidth_eq_card_colouringEast_of_lt_hi` is available. And the origin is
excluded by the floor alone (`HJO.Mellit.Isolates.pos_fst_of_eventType_B_of_lt`), so this needs no
origin clause and `HJO.Mellit.SweepRecursionBOrigin` never appears — the origin is a type-`B` event
of every above-diagonal path, and it is the floor rather than a side condition that keeps it out.

`hmove` is proved nowhere, at no point and for no `(a, b, N)`. -/
theorem braidValueColouring_sweepRecursionBEFloor_of_move
    (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a)
    (hb : 0 < b) (hN : 0 < N)
    (hmove : ∀ (X Y : ℕ) (ηlo ηhi : ℚ), ((a * N : ℕ) : ℚ) < ηlo →
      Isolates a b N X Y ηlo ηhi → ∀ yB yE : Heights a b N, IsAboveDiagonal yB →
        IsAboveDiagonal yE → eventType yB (X, Y) = EventType.B →
          eventType yE (X, Y) = EventType.E → colouring yB ηlo = colouring yE ηlo →
            braidValueOfData q u hq hq1 hqp hr a b N
                (braidDataOfColouring a b N yB ηlo #(colouringEast yB ηlo)).1
                (braidDataOfColouring a b N yB ηlo #(colouringEast yB ηlo)).2
              = dminus q (#(colouringEast yB ηlo) + 1)
                  (braidValueOfData q u hq hq1 hqp hr a b N
                    (braidDataOfColouring a b N yB ηhi (#(colouringEast yB ηlo) + 1)).1
                    (braidDataOfColouring a b N yB ηhi (#(colouringEast yB ηlo) + 1)).2)
                + u • braidValueOfData q u hq hq1 hqp hr a b N
                    (braidDataOfColouring a b N yE ηhi #(colouringEast yB ηlo)).1
                    (braidDataOfColouring a b N yE ηhi #(colouringEast yB ηlo)).2) :
    SweepRecursionBEFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N) := by
  intro P ηlo ηhi hfloor hlo hhi hP1 hP2 hltP hPlt hiso yB yE hyB hyE _ hevB hevE hcol
  obtain ⟨X, Y⟩ := P
  have hI : Isolates a b N X Y ηlo ηhi := ⟨hlo, hhi, hltP, hPlt, hiso, hP1, hP2⟩
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hfloor.trans (hltP.trans hPlt)
  have hX0 : 0 < X := hI.pos_fst_of_eventType_B_of_lt hfloor hyB hevB
  have hne : ((X, Y) : ℕ × ℕ) ≠ ((0 : ℕ), (0 : ℕ)) := by
    intro h
    rw [Prod.mk.injEq] at h
    omega
  exact hI.braidValueColouring_eq_dminus_add_smul_of_move q u hq hq1 hqp hr ha hb hN hηhi
    hyB hyE hevB hevE hcol hne rfl
    (hmove X Y ηlo ηhi hfloor hI yB yE hyB hyE hevB hevE hcol)

end HJO.Mellit

end
