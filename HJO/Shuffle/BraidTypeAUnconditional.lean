/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidTypeAOrbit

/-! # The type-`A` clause with no hypothesis on the upper rank

`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_A_of_card` still carries
`1 ≤ #(colouringEast y ηhi)`, inherited from `HJO.Sweep.dplusIntertwines_specialBraid`, whose
induction starts at rank `1` because the `y_1` generator needs a strand to act on
(`HJO.Sweep.dplusIntertwines_braidGenY`). That hypothesis is not geometry, and `k = 0` really does
occur — the last event of a sweep can leave the upper colouring empty.

At `k = 0` there is nothing to intertwine. The move sequence of the deleted data is a list over
`Fin 0`, hence empty, so the deleted braid is the identity — `HJO.Braid.specialBraid_zero` — and the
inserted one is too, its only index having multiplicity `1`. So
`HJO.Sweep.DplusIntertwines.one` settles the rank-`0` case outright, and
`HJO.Mellit.braidValueOfData_succAbove_eq_dplus_of_card` is the two cases together.

Above that the argument is the one of `HJO/Shuffle/BraidTypeATransfer.lean` unchanged: the same
dictionary, the same two obligations — now `HJO.Mellit.Isolates.lt_iterate_of_eventType_A` and
`HJO.Mellit.Isolates.sameSide_iterate_of_eventType_A` rather than hypotheses — and the same
`HJO.Mellit.braidValueOfData_congr_add` at the end. It is stated separately because the two
statements differ only in a hypothesis, and the conditional one is what
`HJO.Mellit.gap_typeA_via_transfer` is written against.

**This is not the whole of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`.** That statement
covers four clauses, and the types `C` and `D` are untouched.

## References

This file concerns `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`,
`HJO.Mellit.Isolates.pointRank_le`, `HJO.Braid.specialBraid`, `HJO.Braid.BraidMonoid`. Transcribing
A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Sweep

open Braid

variable {L : Type*} [Field L] [Algebra ℚ L]
variable {q u : L} {hq : q ≠ 0} {hq1 : q ≠ 1} {hqp : q + 1 ≠ 0} {r : L} {hr : r * r = q}

/-- **At rank `0` both special braids of a bottom insertion of a fixed point are the identity.** The
deleted data is indexed by `Fin 0`, so its move sequence is empty; the inserted index has
multiplicity `1`, so `HJO.Braid.specialMoveList_eq_map_succAbove` makes the inserted sequence empty
too. This is the base case `HJO.Sweep.dplusIntertwines_specialBraid` excludes. -/
theorem dplusIntertwines_specialBraid_of_zero {θ : ℚ} (j : Fin (0 + 1)) (w : Fin (0 + 1) → ℚ)
    (β : Fin (0 + 1) → ℕ) (hβj : β j = 1) :
    DplusIntertwines q u hq hq1 hqp hr 0 (specialBraid θ (w ∘ j.succAbove) (β ∘ j.succAbove))
      (specialBraid θ w β) := by
  have hnil : specialMoveList (β ∘ j.succAbove) = [] := by simp [specialMoveList]
  have h1 : specialBraid θ w β = 1 := by
    rw [specialBraid, specialMoveList_eq_map_succAbove j β hβj, hnil, List.map_nil, braidWord_nil]
  rw [h1, specialBraid_zero]
  exact DplusIntertwines.one

end HJO.Sweep

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

section Data

variable {L : Type*} [Field L] [Algebra ℚ L]
variable {q u : L} {hq : q ≠ 0} {hq1 : q ≠ 1} {hqp : q + 1 ≠ 0} {r : L} {hr : r * r = q} {k : ℕ}

/-- **The type-`A` identity at the level of the data, at rank `0`.** The same proof as
`HJO.Mellit.braidValueOfData_succAbove_eq_dplus` with the rank-`0` intertwiner in place of the
inductive one; the inversion prefactor and the vacuum recursion need no hypothesis on the rank. -/
theorem braidValueOfData_succAbove_eq_dplus_of_zero (a b N : ℕ) (j : Fin (0 + 1))
    (w : Fin (0 + 1) → ℚ) (β : Fin (0 + 1) → ℕ) (hβj : β j = 1)
    (hini : ∀ t : Fin 0, w j < w (j.succAbove t))
    (hfin : ∀ t : Fin 0, w j < (nextCrossing (sweepTheta a b N))^[β (j.succAbove t) - 1]
      (w (j.succAbove t))) :
    braidValueOfData q u hq hq1 hqp hr a b N w β
      = dplus q 0 (braidValueOfData q u hq hq1 hqp hr a b N (w ∘ j.succAbove)
          (β ∘ j.succAbove)) := by
  have hvac : (dplusIterPiece q (0 + 1) : pieceSub L (0 + 1))
      = ⟨dplus q 0 ((dplusIterPiece q 0 : pieceSub L 0) : Total L),
          dplus_mem_piece q 0 (dplusIterPiece q 0).2⟩ := Subtype.ext rfl
  have hkey := dplusIntertwines_specialBraid_of_zero (q := q) (u := u) (hq := hq) (hq1 := hq1)
    (hqp := hqp) (hr := hr) (θ := sweepTheta a b N) j w β hβj (dplusIterPiece q 0)
  rw [braidValueOfData, braidValueOfData,
    invFin_sub_invIni_of_forall_lt j w β hβj hini hfin, map_smul, hvac, hkey]

/-- **The type-`A` identity at the level of the data, at every rank.** `1 ≤ k` was the only thing
`HJO.Mellit.braidValueOfData_succAbove_eq_dplus` asked beyond the bottom-insertion data, and
`HJO.Mellit.braidValueOfData_succAbove_eq_dplus_of_zero` supplies the missing rank. -/
theorem braidValueOfData_succAbove_eq_dplus_of_card (a b N : ℕ) (j : Fin (k + 1))
    (w : Fin (k + 1) → ℚ) (β : Fin (k + 1) → ℕ) (hβj : β j = 1)
    (hini : ∀ t : Fin k, w j < w (j.succAbove t))
    (hfin : ∀ t : Fin k, w j < (nextCrossing (sweepTheta a b N))^[β (j.succAbove t) - 1]
      (w (j.succAbove t)))
    (hmin : ∀ lt, lt <:+ specialMoveList (β ∘ j.succAbove) → ∀ t : Fin k,
      moveTuple (sweepTheta a b N) w (lt.map j.succAbove) j
        < moveTuple (sweepTheta a b N) w (lt.map j.succAbove) (j.succAbove t)) :
    braidValueOfData q u hq hq1 hqp hr a b N w β
      = dplus q k (braidValueOfData q u hq hq1 hqp hr a b N (w ∘ j.succAbove)
          (β ∘ j.succAbove)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact braidValueOfData_succAbove_eq_dplus_of_zero a b N j w β hβj hini hfin
  · exact braidValueOfData_succAbove_eq_dplus hk a b N j w β hβj hini hfin hmin

end Data

namespace Isolates

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N X Y : ℕ} {ηlo ηhi : ℚ}

/-- **The type-`A` clause for the braid value of a path, with no hypothesis left.** Both orbit
obligations come from `HJO/Shuffle/BraidTypeAOrbit.lean` and the rank restriction from
`HJO.Mellit.braidValueOfData_succAbove_eq_dplus_of_card`; the rest is the dictionary of
`HJO/Shuffle/BraidTypeADictionary.lean`, exactly as in
`HJO.Mellit.braidValueOfPath_eq_dplus_of_eventType_A`. -/
theorem braidValueOfPath_eq_dplus_of_eventType_A_of_card (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.A) {k : ℕ} (hk : #(colouringEast y ηhi) = k)
    (j : Fin (k + 1)) (hj : (j : ℕ) = typeAIndex y ηhi X) :
    braidValueOfPath q u hq hq1 hqp hr y ηlo
      = dplus q k (braidValueOfPath q u hq hq1 hqp hr y ηhi) := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hklo : #(colouringEast y ηlo) = k + 1 := by
    rw [hI.card_colouringEast_of_eventType_A ha hb hN hX hPsw hev, hk]
  have hbot := hI.lt_iterate_of_eventType_A ha hb hN hηlo hy hPsw hev hk j hj
  have hside := hI.sameSide_iterate_of_eventType_A ha hb hN hηlo hy hev hk
  have hmult' : ∀ i : Fin k, (braidDataOfColouring a b N y ηlo (k + 1)).2 (j.succAbove i)
      = (braidDataOfColouring a b N y ηhi k).2 i := fun i =>
    hI.braidDataOfColouring_snd_succAbove ha hb hN hηlo hy hPsw hev hk j hj i
  have hmult : (braidDataOfColouring a b N y ηlo (k + 1)).2 ∘ j.succAbove
      = (braidDataOfColouring a b N y ηhi k).2 := funext hmult'
  have hpos : (braidDataOfColouring a b N y ηlo (k + 1)).1 ∘ j.succAbove
      = fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi :=
    funext fun i =>
      hI.braidDataOfColouring_fst_succAbove ha hb hN hηlo hPsw hev hk j hj i
  rw [braidValueOfPath_eq_braidValueOfData q u hq hq1 hqp hr y ηlo hklo,
    braidValueOfPath_eq_braidValueOfData q u hq hq1 hqp hr y ηhi hk,
    braidValueOfData_succAbove_eq_dplus_of_card a b N j _ _
      (hI.braidDataOfColouring_snd_typeAIndex ha hb hN hηlo hy hPsw hev j hj)
      (fun t => hI.braidDataOfColouring_fst_typeAIndex_lt ha hb hN hηlo hPsw hev hk j hj t)
      (fun t => hbot t _ (by rw [hmult' t]))
      (hmin_of_forall_iterate j _ _ fun t m hm => hbot t m (by rwa [hmult' t] at hm)),
    hmult, hpos]
  exact congrArg _ (braidValueOfData_congr_add q u hq hq1 hqp hr a b N _ _ _ hside)

/-- **The type-`A` clause of the sweep recursion for `HJO.Mellit.braidValueColouring`,
unconditional.** Every hypothesis is about the event: the two levels isolate the point, the path is
above the diagonal, the point is in the swept region, and the event type is `A`. Nothing about the
orbit of `HJO.Braid.nextCrossing` and nothing about the upper rank.

This is the type-`A` clause. The types `C` and `D` of `HJO.Mellit.SweepRecursionACD` are untouched,
so no part of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` is claimed. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_A_uncond (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.A) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  have hjlt : typeAIndex y ηhi X < #(colouringEast y ηhi) + 1 := by
    have := typeAIndex_le y ηhi X; omega
  rw [braidValueColouring_colouring q u hq hq1 hqp hr hy, braidValueColouring_colouring
      q u hq hq1 hqp hr hy, sweepOperator_of_eventType_A y hev,
    hI.sweepWidth_eq_card_colouringEast hb hN hηlo hy]
  exact hI.braidValueOfPath_eq_dplus_of_eventType_A_of_card q u hq hq1 hqp hr ha hb hN hηlo hy
    hPsw hev rfl ⟨typeAIndex y ηhi X, hjlt⟩ rfl

end Isolates

/-! ### Consistency check -/

/-- **The decided witness, through the unconditional clause.** Verbatim
`HJO.Mellit.braidValueColouring_gap_typeA` again, now with no orbit hypothesis and no rank
hypothesis: only the isolation, the path, the swept-region membership and the event type. -/
theorem gap_typeA_uncond {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) :
    braidValueColouring q u hq hq1 hqp hr 2 5 1 gapLo (colouring gapPath gapLo)
      = sweepOperator q u gapPath (1, 5)
          (braidValueColouring q u hq hq1 hqp hr 2 5 1 gapHi (colouring gapPath gapHi)) :=
  isolates_gapPath.braidValueColouring_eq_sweepOperator_of_eventType_A_uncond q u hq hq1 hqp hr
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [gapLo]) isAboveDiagonal_gapPath
    mem_sweptRegion_gapPath eventType_gapPath

end HJO.Mellit

end
