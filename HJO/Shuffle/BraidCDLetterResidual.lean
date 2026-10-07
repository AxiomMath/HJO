/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidEqualRankRaise
public import HJO.Shuffle.BraidSweepRightData
public meta import HJO.Attr

/-! # The type-`C` and type-`D` clauses, reduced to one **letter** each

`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_move` and its type-`D`
twin reduce each clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` to one hypothesis
`hmove`, a braid-value identity between two special-braid data. Two things in `hmove` were still
unresolved, and this file resolves both:

1. **The raised multiplicity.** `hmove` compares `B_{s,v',α'}` with `B_{s,v,α}` where `α'` is `α`
   with one entry raised by one, and nothing said what that does to the braid.
   `HJO.Braid.specialBraid_update_succ_left` and `HJO.Braid.specialBraid_update_succ_right` say: it
   multiplies by **one letter** of `HJO.Braid.braidStep`. So the residual is an identity about that
   one letter's image under `HJO.Sweep.braidRep`, not about two unrelated braids.
2. **The exponent.** `hmove` still read `a_{P̂}(P)` off the path.
   `HJO.Mellit.Isolates.sweepRight_eq_of_colStep_colouringNorth` and
   `HJO.Mellit.Isolates.sweepRight_eq_of_eventType_D` evaluate it from the data as `k - 1 - j`, with
   `k` the rank and `j` the index of the moving component. So the residual carries a **number**.

## The two residuals, and what is still open in each

* Type `C`: `HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_letter`. The
  residual `hletter` says that `π_k` of **one `ỹ`-letter** — read at the final position tuple of the
  *rotated upper* data, which is where
  `HJO.Mellit.Isolates.zCount_sub_eq_zero_of_eventType_C` puts a `ỹ` rather than a `z` — together
  with the `r`-power the two `HJO.Braid.invFin` counts differ by, acts on the rotated upper braid
  value as `q^{-(k-1-j)}Δ` acts on the upper one.
* Type `D`: `HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_D_of_letter`. The
  residual `hletter` says that **one `z`-letter** applied to the vacuum, then carried through the
  rotated upper braid, is `q^{k-1-j}` times the upper braid value. The letter stands on the *right*
  because at type `D` the added crossing is the new top one and the old `v` is one
  `HJO.Braid.nextCrossing` step **below** it —
  `HJO.Mellit.Isolates.moveOne_braidData_fst_of_eventType_D` is that reading, and it identifies the
  tuple the rest of the braid is read at with the rigidly rotated upper tuple.

Neither residual is weaker than its clause: each chain from `hletter` to the clause is a chain of
**equalities** (the equal-rank raise is an identity in `HJO.Braid.BraidMonoid k`, and the exponent
identity is an identity of naturals), so `hletter` is equivalent to `hmove` and hence to the clause.
Nothing here closes either clause. What is open, with the quantifier named, is stated in
`HJO/Shuffle/BraidCDLetterResidual.lean`'s two `hletter` hypotheses: for every rank `k`, every
above-diagonal path, every isolating pair and every index `j`, the displayed letter identity.

## Genericity

`q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0`, `r * r = q` and nothing else — `HJO.Sweep.braidRep`'s own exclusions.
`q` appears inverted in `q^{-(k-1-j)}` on the type-`C` side, which is `HJO.Mellit.sweepOperator`'s
own `q^{-a_{P̂}}` and needs `q ≠ 0`; the `(q-1)⁻¹` inside `HJO.Sweep.corner` needs `q ≠ 1`. Both are
hypotheses of the clause being reduced, so no letter here is a zero map that the unreduced clause
was not.

## References

Transcribing
A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open Braid ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-- `HJO.Mellit.isSpecialBraidData_braidDataOfColouring` at a rank named by an equation rather than
by the cardinality itself, which is the shape every consumer reads it in. -/
theorem isSpecialBraidData_braidDataOfColouring_of_card (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {η : ℚ} (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {k : ℕ} (hk : #(colouringNorth y η) = k) :
    IsSpecialBraidData (sweepSlope a b N) (sweepTheta a b N) k
      (braidDataOfColouring a b N y η k).1 (braidDataOfColouring a b N y η k).2 := by
  subst hk
  exact isSpecialBraidData_braidDataOfColouring ha hb hN hη hηa hy

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}
variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The type-`C` clause, reduced to one letter -/

/-- **The type-`C` clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, reduced to one
letter of `HJO.Braid.braidStep`.** Every hypothesis of
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_move` is carried
unchanged, and `hmove` is replaced by `hletter`, in which

* the raised multiplicity has become a single letter, by
  `HJO.Braid.specialBraid_update_succ_left` and `HJO.Mellit.braidValueOfData_update_succ_left`; and
* `HJO.Paths.sweepRight` has been evaluated as `k - 1 - j`, by
  `HJO.Mellit.Isolates.sweepRight_eq_of_colStep_colouringNorth`.

The letter is read at the final position tuple of `HJO.Braid.positionPair` for the **lower positions
with the upper multiplicities** — the rotated upper data. By
`HJO.Mellit.Isolates.zCount_sub_eq_zero_of_eventType_C` that position lies above the puncture, so
the letter is a `ỹ`; that is not assumed here and is not needed, the statement being about
`HJO.Braid.braidStep` whichever branch it takes. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_C_of_letter (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C)
    {k : ℕ} (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y))
    (hletter : r ^ ((invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
            (Function.update (braidDataOfColouring a b N y ηhi k).2 j
              ((braidDataOfColouring a b N y ηhi k).2 j + 1)) : ℤ)
          - (invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
              (braidDataOfColouring a b N y ηhi k).2 : ℤ)) •
        ((braidRepMellit q u hq hq1 hqp hr k
            (braidStep (sweepTheta a b N)
              (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
                (braidDataOfColouring a b N y ηhi k).2).2 j)
            ⟨braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηlo k).1
                (braidDataOfColouring a b N y ηhi k).2,
              braidValueOfData_mem_pieceSub q u hq hq1 hqp hr a b N _ _⟩ : pieceSub L k)
          : Total L)
      = q ^ (-((k - 1 - (j : ℕ) : ℕ) : ℤ)) • corner q k
          (braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηhi k).1
            (braidDataOfColouring a b N y ηhi k).2)) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hkNlo : #(colouringNorth y ηlo) = k := by
    rw [hI.card_colouringNorth_of_eventType_C ha hN hev]; exact hkN
  have hjlt : (j : ℕ) < #(colouringNorth y ηhi) := by rw [hkN]; exact j.isLt
  have hdatahi := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hy hkN
  have hdatalo := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.lo hηlo hy hkNlo
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
  have hdata : IsSpecialBraidData (sweepSlope a b N) (sweepTheta a b N) k
      (braidDataOfColouring a b N y ηlo k).1
      (Function.update (braidDataOfColouring a b N y ηhi k).2 j
        ((braidDataOfColouring a b N y ηhi k).2 j + 1)) := by
    rw [← hsnd]; exact hdatalo
  have hsweep : sweepRight y (X, Y) = k - 1 - (j : ℕ) := by
    rw [hI.sweepRight_eq_of_colStep_colouringNorth ha hN y hjlt hj, hkN]
  refine hI.braidValueColouring_eq_sweepOperator_of_eventType_C_of_move q u hq hq1 hqp hr ha hb hN
    hηlo hy hev hk j hj ?_
  rw [← hfst, hsweep,
    braidValueOfData_update_succ_left q u hq hq1 hqp hr a b N j (hdatahi.one_le_mult j) hdata]
  exact hletter

/-! ### The type-`D` clause, reduced to one letter -/

/-- **At a type-`D` drop the lower position tuple, advanced once at the moving index, is the upper
tuple rigidly rotated.** The added crossing is the new *top* one and the old top crossing is one
`HJO.Braid.nextCrossing` step below it: that is
`HJO.Mellit.Isolates.braidData_fst_succ_of_eventType_D`'s fractional part read backwards, through
`HJO.Mellit.nextCrossing_fract`.

The two hypotheses are exactly the two places the fractional part can bite. `hlt` says the rigid
rotation alone does not carry the moving position past `1` — the wrap in
`HJO.Mellit.Isolates.braidData_fst_succ_of_eventType_D` is produced by the further `θ`, not by the
rotation — and `hne` that the lower position is not the puncture, where `HJO.Braid.nextCrossing` is
meaningless. `hne` is `HJO.Braid.IsSpecialBraidData.ne_theta` of the lower data at `j`; `hlt` is
**not** discharged here, and is the one place a type-`D` witness with a large rotation could fail
this identification. -/
theorem moveOne_braidData_fst_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y))
    (hθ0 : 0 < sweepTheta a b N) (hθ1 : sweepTheta a b N < 1)
    (hne : (braidDataOfColouring a b N y ηlo k).1 j ≠ sweepTheta a b N)
    (hlo : 0 ≤ (braidDataOfColouring a b N y ηhi k).1 j + levelDropShift a b N ηlo ηhi)
    (hlt : (braidDataOfColouring a b N y ηhi k).1 j + levelDropShift a b N ηlo ηhi < 1) :
    moveOne (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1 j
      = fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi := by
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  have hfj : (braidDataOfColouring a b N y ηlo k).1 j
      = Int.fract ((braidDataOfColouring a b N y ηhi k).1 j + levelDropShift a b N ηlo ηhi
          + sweepTheta a b N) :=
    hI.braidData_fst_succ_of_eventType_D ha hb hN hηlo hy hev hjlt hj j rfl
  have hstep : nextCrossing (sweepTheta a b N) ((braidDataOfColouring a b N y ηlo k).1 j)
      = (braidDataOfColouring a b N y ηhi k).1 j + levelDropShift a b N ηlo ηhi := by
    rw [hfj] at hne ⊢
    rw [nextCrossing_fract hθ0 hθ1 hne, add_sub_cancel_right,
      Int.fract_eq_self.2 ⟨hlo, hlt⟩]
  funext i
  rw [moveOne]
  by_cases h : i = j
  · subst h; rw [Function.update_self, hstep]
  · rw [Function.update_of_ne h]
    exact hI.braidData_fst_of_eventType_D ha hb hN hηlo hy hev hjlt hj i
      (by rw [hk]; exact i.isLt) (fun hc => h (Fin.ext hc))

/-- **The type-`D` clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, reduced to one
letter of `HJO.Braid.braidStep`.** Every hypothesis of
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_D_of_move` is carried
unchanged, and `hmove` is replaced by `hletter`, in which

* the raised multiplicity has become a single letter applied to the **vacuum**, by
  `HJO.Braid.specialBraid_update_succ_right` and
  `HJO.Mellit.braidValueOfData_update_succ_right` — the letter stands rightmost because at type `D`
  the added crossing is the new top one, so the added move is the one performed *first*; and
* `HJO.Paths.sweepRight` has been evaluated as `k - 1 - j`, by
  `HJO.Mellit.Isolates.sweepRight_eq_of_eventType_D`.

By `HJO.Mellit.Isolates.zCount_sub_eq_one_of_eventType_D` the letter is a `z`, the lower position
at `j` lying below the puncture; that is not assumed here. The tuple the rest of the braid is read
at is `HJO.Braid.moveOne` of the lower tuple, which
`HJO.Mellit.Isolates.moveOne_braidData_fst_of_eventType_D` identifies with the rigidly rotated
upper tuple under two named side conditions; it is left unsimplified here so that this reduction
carries no hypothesis its clause does not. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_D_of_letter (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D)
    {k : ℕ} (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y))
    (hletter : r ^ ((invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
            (Function.update (braidDataOfColouring a b N y ηhi k).2 j
              ((braidDataOfColouring a b N y ηhi k).2 j + 1)) : ℤ)
          - (invIni (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
              (braidDataOfColouring a b N y ηhi k).2 : ℤ)) •
        ((braidRepMellit q u hq hq1 hqp hr k
            (specialBraid (sweepTheta a b N)
              (moveOne (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1 j)
              (braidDataOfColouring a b N y ηhi k).2)
            (braidRepMellit q u hq hq1 hqp hr k
              (braidStep (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1 j)
              (dplusIterPiece q k)) : pieceSub L k) : Total L)
      = q ^ (k - 1 - (j : ℕ)) •
          braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηhi k).1
            (braidDataOfColouring a b N y ηhi k).2) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hX : X < a * N := hI.fst_lt hηlo
  have hX0 : 0 < X := hI.pos_fst_of_eventType_D hηlo hy hev
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hkNlo : #(colouringNorth y ηlo) = k := by
    rw [hI.colouringNorth_eq_of_eventType_D ha hN hX hev]; exact hkN
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  have hdatahi := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hy hkN
  have hdatalo := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.lo hηlo hy hkNlo
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
  have hdata : IsSpecialBraidData (sweepSlope a b N) (sweepTheta a b N) k
      (braidDataOfColouring a b N y ηlo k).1
      (Function.update (braidDataOfColouring a b N y ηhi k).2 j
        ((braidDataOfColouring a b N y ηhi k).2 j + 1)) := by
    rw [← hsnd]; exact hdatalo
  have hsweep : sweepRight y (X, Y) = k - 1 - (j : ℕ) := by
    rw [hI.sweepRight_eq_of_eventType_D ha hb hN hηhi hy hev hX0 hjlt hj, hk]
  refine hI.braidValueColouring_eq_sweepOperator_of_eventType_D_of_move q u hq hq1 hqp hr ha hb hN
    hηlo hy hev hk j hj ?_
  rw [← hfst, hsweep,
    braidValueOfData_update_succ_right q u hq hq1 hqp hr a b N j (hdatahi.one_le_mult j) hdata]
  exact hletter

end Isolates

end HJO.Mellit
