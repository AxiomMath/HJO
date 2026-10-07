/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidBottomInsert
public import HJO.Shuffle.BraidTypeAWitness
public import HJO.Shuffle.MellitShiftLoc

/-! # The below-`θ` case of the type-`A` clause is an operator identity, and it is the wrong one

`HJO/Shuffle/BraidTypeAWitness.lean` decides the type-`A` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` at one instance, where both positions
sit *above* the puncture `θ` and every letter of both special braids is a `ỹ`. The case left
untested there is a type-`A` event whose retained component sits *below* `θ`, so that its moves emit
`z` letters. This file settles what that case comes to.

## The finding

Below `θ` the braid side is completely determined, and by the *wrong* operator.

`HJO.Braid.specialBraid_eq_phiPlusStar_of_lt` says that at a bottom insertion all of whose moving
stage positions are below `θ`, the lower special braid is exactly `φ^*_+` of the upper one — no
conjugating train, the inserted entry having rank `1`. Feeding that into
`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`
(`HJO.Sweep.braidRep_phiPlusStar_comp_mellit`) and `HJO.Sweep.dplus_dplusIter`
(`HJO.Mellit.dplusIterPiece_succ`) gives `HJO.Mellit.braidValueOfData_eq_negYOneDPlusStar`:

> the lower braid value is `(-y_1d^*_+)` of the upper one.

But rule `A` of `HJO.Mellit.dsc_lo_eq_dplus_dsc_hi` applies `d_+` (`HJO.Mellit.sweepOperator` at
`HJO.Sweep.EventType.A` is `HJO.Sweep.dplus`), and **`d_+` and `-y_1d^*_+` are different maps
`V_k → V_{k+1}`.** They agree on the vacuum tower — that is exactly what
`HJO.Sweep.dplus_dplusIter` says — and they disagree already on `V_1`, at the very vector the
decided instance produces as its upper value: `HJO.Mellit.dplus_ne_negYOneDPlusStar_auxVar_one_sq`
shows

`d_+(y_1^2) - (-y_1d^*_+)(y_1^2) = (q-1)y_1^2y_2 ≠ 0` for every `q ≠ 1`,

and `q ≠ 1` is one of `HJO.Sweep.braidRepMellit`'s standing exclusions, so this is not a degenerate
`0 = 0`: the monomial `y_1^2y_2` has coefficient `q - 1`, which is nonzero throughout the clause's
range.

`HJO.Mellit.braidValueOfData_eq_dplus_iff_of_specialBraid_eq_phiPlusStar` is the consequence, stated
as the equivalence it is: at a bottom insertion whose special braid is `φ^*_+` of the deleted one
and whose two inversion counts are balanced, **the type-`A` identity holds if and only if the two
insertions agree at the upper value.** So a below-`θ` type-`A` event does not merely leave the
clause untested: it reduces it to an equation between two operators that are unequal on the ambient
space, and the clause can survive there only because the upper value happens to lie in the locus
where they agree.

## What this settles and what it does not

It settles that the type-`A` clause is **not** an instance of
`HJO.Braid.specialBraid_mul_trainDown_one` in any form, at either end of the tuple. The refutation
in `HJO/Shuffle/BraidTypeAGapRefuted.lean` shows the gap clause of the general insertion lemma is
false at a genuine type-`A` event; this shows that even where that lemma *does* apply — the
below-`θ` regime, where its hypotheses are free and its conclusion is exact, with the conjugating
trains empty — its conclusion computes `-y_1d^*_+` and rule `A` demands `d_+`. The difference is the
`T_1^2` of `HJO.Braid.phiPlusStar_braidYtilde`, and the reason the decided instance holds is that
its letter is a `ỹ_{a+1}` and *not* `φ^*_+(ỹ_a)`.

It does **not** exhibit a type-`A` event whose moves are all below `θ`: that needs a lattice search,
and the two statements here are about special-braid data, not about a path. Whether the upper braid
value of such an event lies in the agreement locus of the two insertions is therefore open, and it
is the one question a refutation of the type-`A` clause now has to answer. Note that a stage
position below `θ` is exactly a crossing whose rank is within `a(aN+1)N` of the level, by
`HJO.Mellit.Isolates.not_lt_levelPosition_add_sweepTheta` — so the below-`θ` condition *is* the rank
squeeze, and `HJO.Mellit.not_forall_pointRank_le_add_rankDen` refutes only that it holds
universally. Whether it holds at some type-`A` event with at least one move is not settled here, and
nothing below asserts that it does.

## Genericity

`q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0` and `r * r = q`, which is `HJO.Sweep.braidRepMellit`'s list. **`u`
enters here** — `HJO.Sweep.dplusStar` carries `HJO.Sweep.cycleShift`, whose corner value is `uy_1` —
but no inverse of `u` is evaluated: the two computations below read `d^*_+` only at `y_1`, where
`HJO.Sweep.dplusStarAlg_auxVar` gives `y_2` for every `u`, and the inequality holds at every `u`
including `u = 0`. The `(qu)^{-1}` of `HJO.Sweep.zop` would enter only when a `z` letter of
`HJO.Sweep.braidRep` is evaluated, and nothing here evaluates one: the `z` letters are transported
by `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` rather than computed.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*,
section 5.
-/

@[expose] public section

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The braid value of a bottom insertion below the puncture -/

/-- **The lower braid value of a bottom insertion below the puncture is `-y_1d^*_+` of the upper
one.** The two hypotheses are what `HJO/Shuffle/BraidBottomInsert.lean` supplies in that
regime: the special braid is `φ^*_+` of the deleted one
(`HJO.Braid.specialBraid_eq_phiPlusStar_of_lt`) and the exponent
`inv_fin - inv_ini` is unchanged (`HJO.Braid.tupleInversions_of_forall_lt`).

Then `HJO.Sweep.dplus_dplusIter` writes the vacuum tower of rank `k+1` as `-y_1d^*_+` of the one of
rank `k`, and `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` carries
`π_{k+1}(φ^*_+(B))` past it. -/
theorem braidValueOfData_eq_negYOneDPlusStar (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (a b N : ℕ) {k : ℕ} (hk : 1 ≤ k) (j : Fin (k + 1))
    (w : Fin (k + 1) → ℚ) (β : Fin (k + 1) → ℕ)
    (hB : specialBraid (sweepTheta a b N) w β
      = phiPlusStar k hk (specialBraid (sweepTheta a b N) (w ∘ j.succAbove) (β ∘ j.succAbove)))
    (hδ : (invFin (sweepTheta a b N) w β : ℤ) - (invIni (sweepTheta a b N) w β : ℤ)
      = (invFin (sweepTheta a b N) (w ∘ j.succAbove) (β ∘ j.succAbove) : ℤ)
        - (invIni (sweepTheta a b N) (w ∘ j.succAbove) (β ∘ j.succAbove) : ℤ)) :
    braidValueOfData q u hq hq1 hqp hr a b N w β
      = negYOneDPlusStar q u k
          (braidValueOfData q u hq hq1 hqp hr a b N (w ∘ j.succAbove) (β ∘ j.succAbove)) := by
  have hint := LinearMap.congr_fun
    (braidRep_phiPlusStar_comp_mellit q u hq hq1 hqp hr hk
      (specialBraid (sweepTheta a b N) (w ∘ j.succAbove) (β ∘ j.succAbove)))
    (dplusIterPiece q k)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hint
  rw [braidValueOfData, braidValueOfData, hB, hδ, dplusIterPiece_succ q u k, hint,
    coe_negYOneDPlusStarPiece, map_smul]

/-! ### The two insertions, at the vector the decided instance produces -/

omit [Algebra ℚ L] in
/-- **`d_+(y_1^2) = -T_1(y_1^2y_2)`.** The raising operator of `HJO.Sweep.dplus` adds the letter
`y_{k+1}` at the *top* and carries it down by the ascending train `T_{1↗k+1}`, which at `k = 1` is
the single operator `T_1`. -/
theorem dplus_one_auxVar_one_sq (q : L) :
    dplus q 1 ((auxVar 1 : Total L) * auxVar 1)
      = -braidEnd q 1 ((auxVar 1 : Total L) * auxVar 1 * auxVar 2) := by
  have hax : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have htop : (auxVar (1 + 1) : Total L) = auxVar 2 := rfl
  have hqs : qshift q (1 + 1) ((auxVar 1 : Total L) * (auxVar 1 : Total L))
      = (auxVar 1 : Total L) * (auxVar 1 : Total L) := by
    rw [hax, map_mul, qshift_auxVar]
  rw [dplus_apply, trainUpEnd_one_two, hqs]
  congr 2
  rw [htop]
  ring

/-- **`(-y_1d^*_+)(y_1^2) = -y_1y_2^2`.** The conjugate raising operator adds its letter at the
*bottom*, shifting every variable up by one; `HJO.Sweep.dplusStarAlg_auxVar` is that shift and it is
the same for every `u`. -/
theorem negYOneDPlusStar_one_auxVar_one_sq (q u : L) :
    negYOneDPlusStar q u 1 ((auxVar 1 : Total L) * auxVar 1)
      = -((auxVar 1 : Total L) * (auxVar 2 * auxVar 2)) := by
  have h : dplusStar q u 1 ((auxVar 1 : Total L) * auxVar 1)
      = (auxVar 2 : Total L) * auxVar 2 := by
    rw [← dplusStarAlg_eq_dplusStar, map_mul, dplusStarAlg_auxVar q u le_rfl le_rfl]
  rw [negYOneDPlusStar_apply, h]

omit [Algebra ℚ L] in
/-- A nonzero scalar times a monomial is nonzero, which is what says the discrepancy below is not
the degenerate `0 = 0` of a letter that became the zero map. -/
theorem scal_mul_auxVar_one_sq_mul_auxVar_two_ne_zero {c : L} (hc : c ≠ 0) :
    scal c * ((auxVar 1 : Total L) * auxVar 1 * auxVar 2) ≠ 0 := by
  have hax1 : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hax2 : (auxVar 2 : Total L) = MvPolynomial.X 1 := rfl
  rw [hax1, hax2]
  refine mul_ne_zero ?_ (mul_ne_zero (mul_ne_zero (MvPolynomial.X_ne_zero 0)
    (MvPolynomial.X_ne_zero 0)) (MvPolynomial.X_ne_zero 1))
  rw [scal, Ne, MvPolynomial.C_eq_zero, MvPolynomial.C_eq_zero]
  exact hc

/-- **THE TWO INSERTIONS DISAGREE ON `V_1`, AT THE UPPER VALUE OF THE DECIDED INSTANCE.**
`d_+(y_1^2) - (-y_1d^*_+)(y_1^2) = (q-1)y_1^2y_2`, which is nonzero for every `q ≠ 1` — and `q ≠ 1`
is one of `HJO.Sweep.braidRepMellit`'s exclusions, so the discrepancy is present throughout the
range of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`. The vector `y_1^2` is exactly
`HJO.Mellit.braidValueOfPath_gap_hi`, the upper braid value of the one decided type-`A` instance.

By `HJO.Mellit.braidValueOfData_eq_negYOneDPlusStar` this is what stops the `φ^*_+` route — the
route the below-`θ` regime makes exact — from proving the type-`A` clause. -/
theorem dplus_ne_negYOneDPlusStar_auxVar_one_sq (q u : L) (hq1 : q ≠ 1) :
    dplus q 1 ((auxVar 1 : Total L) * auxVar 1)
      ≠ negYOneDPlusStar q u 1 ((auxVar 1 : Total L) * auxVar 1) := by
  have hax1 : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hax2 : (auxVar 2 : Total L) = MvPolynomial.X 1 := rfl
  intro hcon
  rw [dplus_one_auxVar_one_sq, negYOneDPlusStar_one_auxVar_one_sq, braidEnd_gap_value, hax1,
    hax2] at hcon
  refine scal_mul_auxVar_one_sq_mul_auxVar_two_ne_zero (sub_ne_zero_of_ne hq1) ?_
  rw [hax1, hax2]
  linear_combination hcon

/-! ### What the below-`θ` case of the clause reduces to -/

/-- **The type-`A` identity at a bottom insertion below the puncture, as the equivalence it is.**
Given that the special braid is `φ^*_+` of the deleted one and the inversion counts are balanced —
the two things `HJO/Shuffle/BraidBottomInsert.lean` supplies in the below-`θ` regime — the
identity rule `A` asks for holds **if and only if** the two insertions `d_+` and `-y_1d^*_+` agree
at the upper braid value.

`HJO.Mellit.dplus_ne_negYOneDPlusStar_auxVar_one_sq` shows they do not agree on `V_1`, so this is a
genuine obligation and not a restatement: a below-`θ` type-`A` event can satisfy the clause only if
its upper value lies in the locus where the two insertions agree. -/
theorem braidValueOfData_eq_dplus_iff_of_specialBraid_eq_phiPlusStar (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (a b N : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (j : Fin (k + 1)) (w : Fin (k + 1) → ℚ) (β : Fin (k + 1) → ℕ)
    (hB : specialBraid (sweepTheta a b N) w β
      = phiPlusStar k hk (specialBraid (sweepTheta a b N) (w ∘ j.succAbove) (β ∘ j.succAbove)))
    (hδ : (invFin (sweepTheta a b N) w β : ℤ) - (invIni (sweepTheta a b N) w β : ℤ)
      = (invFin (sweepTheta a b N) (w ∘ j.succAbove) (β ∘ j.succAbove) : ℤ)
        - (invIni (sweepTheta a b N) (w ∘ j.succAbove) (β ∘ j.succAbove) : ℤ)) :
    braidValueOfData q u hq hq1 hqp hr a b N w β
        = dplus q k (braidValueOfData q u hq hq1 hqp hr a b N (w ∘ j.succAbove) (β ∘ j.succAbove))
      ↔ negYOneDPlusStar q u k
            (braidValueOfData q u hq hq1 hqp hr a b N (w ∘ j.succAbove) (β ∘ j.succAbove))
          = dplus q k
              (braidValueOfData q u hq hq1 hqp hr a b N (w ∘ j.succAbove) (β ∘ j.succAbove)) := by
  rw [braidValueOfData_eq_negYOneDPlusStar q u hq hq1 hqp hr a b N hk j w β hB hδ]

end HJO.Mellit

end
