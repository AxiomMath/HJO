/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidRankRaise
public import HJO.Shuffle.BraidTypeABelowTheta
public meta import HJO.Attr

/-! # The rank-raise intertwiner is not a pair of zero maps, and it settles the below-`θ` question

Two consequences of `HJO/Shuffle/BraidRankRaise.lean` that need the computations of
`HJO/Shuffle/BraidTypeAWitness.lean` and `HJO/Shuffle/BraidTypeABelowTheta.lean`.

## Non-degeneracy

`HJO.Sweep.dplusIntertwines_braidYtilde` at `k = 1`, `a = 1`, evaluated at the vacuum
`d_+^1(1) = -y_1`, computes `d^♭_+(y_1^2) = -T_1(y_1^2y_2)`, and
`HJO.Sweep.dplus_braidRepMellit_braidYtilde_one_dplusIterPiece_ne_zero` shows that is nonzero over
every field: `T_1` is invertible for `q ≠ 0` and `y_1^2y_2` is a nonzero monomial. So the `ỹ` case
of the intertwiner is not the degenerate `0 = 0` that a letter carrying an inverse would produce.
`HJO.Mellit.braidEnd_gap_value` gives the value in closed form, `y_1y_2^2 - (q-1)y_1^2y_2` up to
sign, whose leading monomial has coefficient `1` whatever `q` is.

This is the same vector as `HJO.Mellit.braidValueOfPath_gap_hi` — the upper braid value of the one
decided type-`A` instance — so what is checked here is exactly the instance
`HJO.Mellit.braidValueColouring_gap_typeA` decides.

## The below-`θ` question, answered

`HJO/Shuffle/BraidTypeABelowTheta.lean` reduces the below-`θ` case of the type-`A` clause to
whether `d_+` and `-y_1d^*_+` — which are different maps `V_1 → V_2`,
`HJO.Mellit.dplus_ne_negYOneDPlusStar_auxVar_one_sq` — agree at the upper braid value, and leaves
that open, calling it "the one question a refutation of the type-`A` clause now has to answer".

`HJO.Mellit.dplus_eq_negYOneDPlusStar_braidValueOfData` answers it **for the special-braid data**:
they agree. The same braid is reached by two routes —
`HJO.Braid.specialBraid_eq_phiPlusStar_of_lt` through `HJO.Braid.phiPlusStar`, and
`HJO.Sweep.dplusIntertwines_specialBraid` through the rank raise, whose `z` letters agree with
`φ^*_+`'s — so the two operators take the same value there, and no refutation of the type-`A` clause
comes from the below-`θ` regime.

`HJO.Mellit.not_exists_eventType_A_forall_move_lt_sweepTheta`
(`HJO/Shuffle/BraidTypeABelowThetaVacuous.lean`) reaches the same conclusion about the clause
by the opposite route, showing that no type-`A` event realizes those hypotheses at all. The two are
independent: that one says the regime is empty at an event, this one says the identity holds on the
data whether or not an event realizes it. Neither dispatches the case that does occur, a component
with moves on **both** sides of `θ`; that is what
`HJO.Mellit.braidValueOfData_succAbove_eq_dplus` covers, and it carries no condition on `θ`.

## Genericity

`HJO.Sweep.braidRepMellit`'s list, and no more: `q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0`, `r * r = q`. `u` is
carried but never inverted; the nonzero value below holds at every `u`, including `u = 0`.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

namespace HJO.Sweep

open Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- At rank `1` every train is empty and `ỹ_1 = y_1` (`HJO.Braid.braidYtilde_one_one`), so
`π_1(ỹ_1)` is multiplication by `-y_1`. -/
theorem coe_braidRepMellit_braidYtilde_one_one (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) {r : L} (hr : r * r = q) (x : pieceSub L 1) :
    ((braidRepMellit q u hq hq1 hqp hr 1 (braidYtilde 1 1) x : pieceSub L 1) : Total L)
      = -((auxVar 1 : Total L) * x) := by
  rw [braidYtilde_one_one, braidRepMellit, (representedBy_braidGenY (le_refl 1)).apply]
  rfl

omit [Algebra ℚ L] in
/-- `d_+^1(1) = -y_1`, the rank-one case of `HJO.Sweep.dplusIter_eq_smul_auxVarProd`. -/
theorem coe_dplusIterPiece_one (q : L) :
    ((dplusIterPiece q 1 : pieceSub L 1) : Total L) = -(auxVar 1 : Total L) := by
  rw [coe_dplusIterPiece, dplusIter_eq_smul_auxVarProd, auxVarProd_succ, auxVarProd_zero, one_mul,
    pow_one, neg_one_smul]

/-- `π_1(ỹ_1)(d_+^1(1)) = y_1^2`, the upper value of the decided type-`A` instance. -/
theorem braidRepMellit_braidYtilde_one_dplusIterPiece (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) {r : L} (hr : r * r = q) :
    ((braidRepMellit q u hq hq1 hqp hr 1 (braidYtilde 1 1) (dplusIterPiece q 1) :
        pieceSub L 1) : Total L) = (auxVar 1 : Total L) * auxVar 1 := by
  rw [coe_braidRepMellit_braidYtilde_one_one, coe_dplusIterPiece_one]
  ring

/-- `d^♭_+(π_1(ỹ_1)(d_+^1(1))) = -T_1(y_1^2y_2)`: the common value of the two sides of the `ỹ`
intertwiner at the smallest instance. -/
theorem dplus_braidRepMellit_braidYtilde_one_dplusIterPiece (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) {r : L} (hr : r * r = q) :
    dplus q 1 ((braidRepMellit q u hq hq1 hqp hr 1 (braidYtilde 1 1) (dplusIterPiece q 1) :
        pieceSub L 1) : Total L)
      = -braidEnd q 1 ((auxVar 1 : Total L) * auxVar 1 * auxVar 2) := by
  rw [braidRepMellit_braidYtilde_one_dplusIterPiece, Mellit.dplus_one_auxVar_one_sq]

/-- **The common value is nonzero over every field**, so the `ỹ` case of the intertwiner is not an
identity between two zero maps. `T_1` is invertible for `q ≠ 0`
(`HJO.Sweep.braidInvEnd_mul_braidEnd`) and `y_1^2y_2` is a nonzero monomial, so no hypothesis on `q`
beyond `q ≠ 0` and no hypothesis on `u` is read. -/
theorem dplus_braidRepMellit_braidYtilde_one_dplusIterPiece_ne_zero (q u : L) (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) {r : L} (hr : r * r = q) :
    dplus q 1 ((braidRepMellit q u hq hq1 hqp hr 1 (braidYtilde 1 1) (dplusIterPiece q 1) :
        pieceSub L 1) : Total L) ≠ 0 := by
  have hax1 : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hax2 : (auxVar 2 : Total L) = MvPolynomial.X 1 := rfl
  have hZ : ((auxVar 1 : Total L) * auxVar 1 * auxVar 2) ≠ 0 := by
    rw [hax1, hax2]
    exact mul_ne_zero (mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 0))
      (MvPolynomial.X_ne_zero 1)
  rw [dplus_braidRepMellit_braidYtilde_one_dplusIterPiece, neg_ne_zero]
  intro hcon
  refine hZ ?_
  have h := LinearMap.congr_fun (braidInvEnd_mul_braidEnd q hq 1)
    ((auxVar 1 : Total L) * auxVar 1 * auxVar 2)
  rw [Module.End.mul_apply, Module.End.one_apply, hcon, map_zero] at h
  exact h.symm

end HJO.Sweep

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **THE TWO INSERTIONS DO AGREE AT A BELOW-`θ` BRAID VALUE.** At a bottom insertion of a fixed
point all of whose retained moves are below the puncture, `d_+` and `-y_1d^*_+` take the same value
on the deleted data's braid value — even though
`HJO.Mellit.dplus_ne_negYOneDPlusStar_auxVar_one_sq` shows the two operators are different maps
`V_1 → V_2`.

This is what the module docstring of `HJO/Shuffle/BraidTypeABelowTheta.lean` calls "the one
question a refutation of the type-`A` clause now has to answer": that file reduces the below-`θ`
case of the clause, through
`HJO.Mellit.braidValueOfData_eq_dplus_iff_of_specialBraid_eq_phiPlusStar`, to exactly this
agreement and leaves it open. The answer is that it holds, and the reason is that the same braid is
reached by two different routes — `HJO.Braid.specialBraid_eq_phiPlusStar_of_lt`
through `HJO.Braid.phiPlusStar`, and `HJO.Sweep.dplusIntertwines_specialBraid` through the rank
raise, whose `z` letters agree with `φ^*_+`'s.

So no refutation of the type-`A` clause comes from the below-`θ` regime. -/
theorem dplus_eq_negYOneDPlusStar_braidValueOfData (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (a b N : ℕ) {k : ℕ} (hk : 1 ≤ k) (j : Fin (k + 1))
    (w : Fin (k + 1) → ℚ) (β : Fin (k + 1) → ℕ) (hβj : β j = 1)
    (hini : ∀ t : Fin k, w j < w (j.succAbove t))
    (hfin : ∀ t : Fin k, w j < (nextCrossing (sweepTheta a b N))^[β (j.succAbove t) - 1]
      (w (j.succAbove t)))
    (hmin : ∀ lt, lt <:+ specialMoveList (β ∘ j.succAbove) → ∀ t : Fin k,
      moveTuple (sweepTheta a b N) w (lt.map j.succAbove) j
        < moveTuple (sweepTheta a b N) w (lt.map j.succAbove) (j.succAbove t))
    (hlt : ∀ (t₀ : Fin k) (lt : List (Fin k)), t₀ :: lt <:+ specialMoveList (β ∘ j.succAbove) →
      moveTuple (sweepTheta a b N) w (lt.map j.succAbove) (j.succAbove t₀) < sweepTheta a b N) :
    dplus q k (braidValueOfData q u hq hq1 hqp hr a b N (w ∘ j.succAbove) (β ∘ j.succAbove))
      = negYOneDPlusStar q u k
          (braidValueOfData q u hq hq1 hqp hr a b N (w ∘ j.succAbove) (β ∘ j.succAbove)) := by
  rw [← braidValueOfData_succAbove_eq_dplus (u := u) (hq := hq) (hq1 := hq1) (hqp := hqp)
      (hr := hr) hk a b N j w β hβj hini hfin hmin,
    braidValueOfData_eq_negYOneDPlusStar q u hq hq1 hqp hr a b N hk j w β
      (specialBraid_eq_phiPlusStar_of_lt hk j w β hβj hmin hlt)
      (invFin_sub_invIni_of_forall_lt j w β hβj hini hfin)]

end HJO.Mellit

end
