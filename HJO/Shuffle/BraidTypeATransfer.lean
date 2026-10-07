/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidRankRaise
public import HJO.Shuffle.BraidTypeADictionary
public import HJO.Shuffle.BraidValueColouring

/-! # The type-`A` clause of the braid recursion, reduced to two obligations on the crossing orbit

`HJO.Mellit.braidValueOfData_succAbove_eq_dplus` is the type-`A` identity for special-braid data and
`HJO/Shuffle/BraidTypeADictionary.lean` identifies the two colourings of a type-`A` event as
such a pair. This file performs the assembly; the point of it is the **exact list of what is left**.

## The result

`HJO.Mellit.braidValueColouring_eq_sweepOperator_of_eventType_A` is the conclusion of
`HJO.Mellit.SweepRecursionACD` for `HJO.Mellit.braidValueColouring` at a type-`A` event:

`R η₋ (c₋) = Φ_{P̂}(P) (R η₊ (c₊))`.

It carries, past the geometry the dictionary settles, exactly three hypotheses:

* `1 ≤ k` — the upper rank is positive. This is not geometry but a limitation of
  `HJO.Sweep.dplusIntertwines_specialBraid`, whose induction starts at rank `1`.
* `hbot` — **the inserted position stays below every retained entry at every stage of the move
  sequence.** This is `hmin`/`hfin` of the data-level identity, contracted into one statement by
  `HJO.Mellit.hmin_of_forall_iterate`: the inserted index is never moved, so the entry at `j` is
  constant at `v_lo j` through the whole word, while the entry at `j.succAbove t` after some moves
  is an iterate `nx_θ^m(v_lo (j.succAbove t))` with `m ≤ α_hi t − 1`.
* `hside` — **the rigid shift `HJO.Mellit.levelDropShift` moves no stage position of the *upper*
  data across the puncture `θ`.** This is what turns `HJO.Mellit.braidValueOfData_congr_add` into
  the statement that the deleted data has the upper level's braid value; it is the same obligation
  the unswept clause already carries in
  `HJO.Mellit.braidValueOfPath_eq_of_notMem_sweptRegion`.

Both `hbot` and `hside` are statements about the orbit of `HJO.Braid.nextCrossing` on the circle,
about *stages* rather than starting positions. Neither is a statement about colourings, and neither
is proved in this file; both are proved in `HJO/Shuffle/BraidTypeAOrbit.lean`, and
`HJO/Shuffle/BraidTypeAUnconditional.lean` assembles the clause without them. **So this file does
not close `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, not even its type-`A` clause.**

## Why the obligations are not decoration

`hbot` is not implied by the inserted position being below every *starting* position, which
`HJO.Mellit.Isolates.braidDataOfColouring_fst_typeAIndex_lt` does prove: the iterates of
`HJO.Braid.nextCrossing` walk down the circle and wrap past the puncture, so a retained entry can in
principle descend below the inserted one. And `hside` is not implied by the shift being small, for
the same reason: `HJO.Braid.SameSide` fails exactly when an entry starts below `θ` and the shift
carries it above.

What *is* known is that both hold at the decided witness. At `a = 2`, `b = 5`, `N = 1`,
`(X, Y) = (1, 5)`, `η₋ = 31/2` — the configuration of `HJO.Mellit.braidValueColouring_gap_typeA`,
where the rank-squeeze hypothesis of `HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le`
fails — the lower data is
`v = (17/40, 1/40)`, `α = (2, 1)` with `θ = 12/40`, so the inserted entry is `1/40` and the single
retained move takes `17/40` to `5/40`, still above it; and the shift is `2/40`, which moves `15/40`
and `3/40` to `17/40` and `5/40` without either crossing `12/40`.

## Genericity

`q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0` and `r * r = q` — the hypothesis list of
`HJO.Sweep.braidRepMellit`, without which `π_k` does not exist. Nothing further: `u ≠ 0` is not
spent, no inverse is evaluated, and the two obligations are hypotheses rather than computations.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

/-! ### Contracting the two stage hypotheses of the data-level identity into one -/

/-- **The `hmin` hypothesis of `HJO.Sweep.dplusIntertwines_specialBraid` follows from a bound on the
iterates.** The inserted index `j` occurs in no move of the word — every move is a `j.succAbove t` —
so the entry there never moves, and the entry at `j.succAbove t` after a prefix of moves is the
`m`-th iterate of `nx_θ` for some `m` bounded by that index's own multiplicity minus one. -/
theorem hmin_of_forall_iterate {θ : ℚ} {k : ℕ} (j : Fin (k + 1)) (w : Fin (k + 1) → ℚ)
    (β : Fin (k + 1) → ℕ)
    (h : ∀ (t : Fin k) (m : ℕ), m ≤ β (j.succAbove t) - 1 →
      w j < (nextCrossing θ)^[m] (w (j.succAbove t))) :
    ∀ lt, lt <:+ specialMoveList (β ∘ j.succAbove) → ∀ t : Fin k,
      moveTuple θ w (lt.map j.succAbove) j
        < moveTuple θ w (lt.map j.succAbove) (j.succAbove t) := by
  intro lt hlt t
  rw [moveTuple_apply_eq_iterate, moveTuple_apply_eq_iterate,
    List.count_eq_zero.2 (fun hc => by
      obtain ⟨t', -, ht'⟩ := List.mem_map.1 hc
      exact (j.succAbove_ne t') ht'),
    List.count_map_of_injective lt j.succAbove Fin.succAbove_right_injective t]
  exact h t _ ((hlt.sublist.count_le t).trans (count_specialMoveList (β ∘ j.succAbove) t).le)

/-! ### The braid value of a path at a fixed rank -/

/-- `HJO.Mellit.braidValueOfPath` with the rank named, so that the two ranks of a level drop can be
compared as `k + 1` and `k`. -/
theorem braidValueOfPath_eq_braidValueOfData {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) {a b N : ℕ}
    (y : Heights a b N) (η : ℚ) {k : ℕ} (hk : #(colouringEast y η) = k) :
    braidValueOfPath q u hq hq1 hqp hr y η
      = braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y η k).1
          (braidDataOfColouring a b N y η k).2 := by
  subst hk
  rfl

/-! ### The type-`A` clause, modulo the two obligations -/

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N X Y : ℕ} {ηlo ηhi : ℚ}

/-- **The type-`A` clause for the braid value of a path**, given the two obligations on the crossing
orbit. Every piece of geometry is discharged from
`HJO/Shuffle/BraidTypeADictionary.lean`: the rank rises by one, one index `j` inserts into both
halves, the inserted multiplicity is `1` and the retained ones are unchanged, the retained positions
rise by the single shift `HJO.Mellit.levelDropShift`, the inserted position is below every retained
one, and the width is the upper rank. What is assumed is `hbot` and `hside`, both about the orbit of
`HJO.Braid.nextCrossing`; see the module docstring. -/
theorem braidValueOfPath_eq_dplus_of_eventType_A (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.A) {k : ℕ} (hk : #(colouringEast y ηhi) = k)
    (hk1 : 1 ≤ k) (j : Fin (k + 1)) (hj : (j : ℕ) = typeAIndex y ηhi X)
    (hbot : ∀ (t : Fin k) (m : ℕ), m ≤ (braidDataOfColouring a b N y ηhi k).2 t - 1 →
      (braidDataOfColouring a b N y ηlo (k + 1)).1 j
        < (nextCrossing (sweepTheta a b N))^[m]
            ((braidDataOfColouring a b N y ηlo (k + 1)).1 (j.succAbove t)))
    (hside : ∀ (t : Fin k) (m : ℕ), m ≤ (braidDataOfColouring a b N y ηhi k).2 t - 1 →
      SameSide (sweepTheta a b N) (levelDropShift a b N ηlo ηhi)
        ((nextCrossing (sweepTheta a b N))^[m] ((braidDataOfColouring a b N y ηhi k).1 t))) :
    braidValueOfPath q u hq hq1 hqp hr y ηlo
      = dplus q k (braidValueOfPath q u hq hq1 hqp hr y ηhi) := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hklo : #(colouringEast y ηlo) = k + 1 := by
    rw [hI.card_colouringEast_of_eventType_A ha hb hN hX hPsw hev, hk]
  -- the multiplicities transported along the insertion
  have hmult' : ∀ i : Fin k, (braidDataOfColouring a b N y ηlo (k + 1)).2 (j.succAbove i)
      = (braidDataOfColouring a b N y ηhi k).2 i := fun i =>
    hI.braidDataOfColouring_snd_succAbove ha hb hN hηlo hy hPsw hev hk j hj i
  have hmult : (braidDataOfColouring a b N y ηlo (k + 1)).2 ∘ j.succAbove
      = (braidDataOfColouring a b N y ηhi k).2 := funext hmult'
  -- the positions transported along the insertion
  have hpos : (braidDataOfColouring a b N y ηlo (k + 1)).1 ∘ j.succAbove
      = fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi :=
    funext fun i =>
      hI.braidDataOfColouring_fst_succAbove ha hb hN hηlo hPsw hev hk j hj i
  rw [braidValueOfPath_eq_braidValueOfData q u hq hq1 hqp hr y ηlo hklo,
    braidValueOfPath_eq_braidValueOfData q u hq hq1 hqp hr y ηhi hk,
    braidValueOfData_succAbove_eq_dplus hk1 a b N j _ _
      (hI.braidDataOfColouring_snd_typeAIndex ha hb hN hηlo hy hPsw hev j hj)
      (fun t => hI.braidDataOfColouring_fst_typeAIndex_lt ha hb hN hηlo hPsw hev hk j hj t)
      (fun t => hbot t _ (by rw [hmult' t]))
      (hmin_of_forall_iterate j _ _ fun t m hm => hbot t m (by rwa [hmult' t] at hm)),
    hmult, hpos]
  exact congrArg _ (braidValueOfData_congr_add q u hq hq1 hqp hr a b N _ _ _ hside)

/-- **The type-`A` clause for the candidate `HJO.Mellit.braidValueColouring`**, in the shape the
`A`/`C`/`D` clause of `HJO.Mellit.SweepRecursionACD` asks for, and subject to the same two
obligations. `HJO.Mellit.braidValueColouring_colouring` removes the representative on both sides,
`HJO.Sweep.sweepOperator_of_eventType_A` names the event operator `d_+`, and
`HJO.Mellit.Isolates.sweepWidth_eq_card_colouringEast` says its rank is the upper one.

This is the clause at *one* event type. `HJO.Mellit.SweepRecursionACD` asks for `A`, `C` and `D`
together and takes its event hypothesis as the disjunction `ht y X < Y ∨ ht y (X+1) = Y`, which
`HJO.Mellit.ht_lt_or_ht_succ_eq_of_eventType` produces from any of the three; the types `C` and `D`
are untouched here. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_A (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.A) {k : ℕ} (hk : #(colouringEast y ηhi) = k)
    (hk1 : 1 ≤ k) (j : Fin (k + 1)) (hj : (j : ℕ) = typeAIndex y ηhi X)
    (hbot : ∀ (t : Fin k) (m : ℕ), m ≤ (braidDataOfColouring a b N y ηhi k).2 t - 1 →
      (braidDataOfColouring a b N y ηlo (k + 1)).1 j
        < (nextCrossing (sweepTheta a b N))^[m]
            ((braidDataOfColouring a b N y ηlo (k + 1)).1 (j.succAbove t)))
    (hside : ∀ (t : Fin k) (m : ℕ), m ≤ (braidDataOfColouring a b N y ηhi k).2 t - 1 →
      SameSide (sweepTheta a b N) (levelDropShift a b N ηlo ηhi)
        ((nextCrossing (sweepTheta a b N))^[m] ((braidDataOfColouring a b N y ηhi k).1 t))) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  rw [braidValueColouring_colouring q u hq hq1 hqp hr hy, braidValueColouring_colouring
      q u hq hq1 hqp hr hy, sweepOperator_of_eventType_A y hev,
    hI.sweepWidth_eq_card_colouringEast hb hN hηlo hy, hk]
  exact braidValueOfPath_eq_dplus_of_eventType_A q u hq hq1 hqp hr ha hb hN hI hηlo hy hPsw hev
    hk hk1 j hj hbot hside

end HJO.Mellit

end
