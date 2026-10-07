/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.MellitDpaAction
public import HJO.CMStructure.MellitZLoops
public meta import HJO.Attr

/-! # `HJO.Sweep.braidRepRespects_mellit`: the assignment of `HJO.Sweep.braidRep` respects the
presentation

Mellit's Proposition 5.3. `HJO.Sweep.braidRepRespects_of_residual` discharges nine of the ten
relation families of `HJO.Braid.BraidRel` from the closed forms of the operators, leaving the single
clause `HJO.Sweep.BraidRepResidual.zRep_comm` — that Mellit's `z_i` commute with one another on
`V_k`; `HJO.Sweep.zop_comm_of_mellitAction` proves that clause from a Mellit-convention action of
the Dyck path algebra, and `HJO.Sweep.exists_isDpaAction_mellit` supplies one. This file is the
join.

## The three side conditions, and where each comes from

* `q ≠ 0` — the loops of the Mellit convention are the inverses `T_i^{-1}`, and `HJO.Sweep.zop`
  divides by `q`. Present in `HJO.Sweep.braidRepRespects_of_residual` already.
* `q ≠ 1` — `HJO.Dyck.Aq.yElt` divides by `q' - 1` at `q' = q^{-1}`, which is
  `HJO.Sweep.zop`'s own `q^k/(1-q)`; see `HJO.Sweep.invOf_inv_sub_one_eq`.
* `q + 1 ≠ 0` — from `HJO.Sweep.isDpaOperators_mellit`, and there from the first conjugation
  relation alone, whose reduced form is equivalent to the relation only up to a factor `1 + q`.

No condition on `u` appears: the normalising scalar `(qu)^{-1}` of `HJO.Sweep.braidRep`'s assignment
`z_1 ↦ (qu)^{-1}z_1` occurs once on each side of the commutation and is never cancelled, so the
`u ≠ 0` of `HJO.Sweep.braidResidual_iff_zop_comm` is not needed in this direction. Every use
instantiates it at parameters algebraically independent over `ℤ`, where all three conditions hold.

## What is NOT used, and why that matters

One might expect the residual clause to be a transport of `HJO.Sweep.map_yElt_low_comm` across
`HJO.Sweep.exists_slopeActions`. It is not
(`HJO.Sweep.mulLeft_auxVar_two_not_comm_trainUpEnd`,
`HJO/CMStructure/BraidRepNotTotal.lean`), and neither statement is used here. What is used is a
*fourth* instance of the abstract operator package, in the convention `HJO.Sweep.zop` is actually
written in — `(T_i^{-1}, d^♭_-, d^*_+)` at `q^{-1}` — whose four lowering-operator relations are
proved from scratch rather than inherited. The commutation itself is
`HJO.Dyck.Aq.yElt_comm`, a theorem of `HJO.Dyck.Aq` carrying no hypothesis beyond `1 ≤ i, j ≤ k`.

The total-space form of the clause is false at `k = 2`
(`HJO.Sweep.braidRepRespectsTotal_two_false`), so the statement is provable only at the typing
`HJO.Sweep.braidRep` carries, `Module.End L (pieceSub L k)`.

## Main results

* `HJO.Sweep.braidRepResidual_mellit` — the residual clause, unconditionally.
* `HJO.Sweep.braidRepRespects_mellit`: `π_k` exists.
* `HJO.Sweep.braidRep_mellit` — `π_k` itself, with no well-definedness argument to supply.

Uniqueness of `π_k`, the other half of the existence-and-uniqueness statement, is
`HJO.Sweep.braidRep_unique` (`HJO/Shuffle/BraidRep.lean`): a monoid homomorphism out of a presented
monoid is determined by its values on the generators.

## References

A. Mellit,
*Toric braids and `(m, n)`-parking functions*, Proposition 5.3.
-/

@[expose] public section

namespace HJO.Sweep

section Mellit

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The residual clause of Mellit's Proposition 5.3, unconditionally**: the operators `z_i` of
`HJO.Sweep.zop` commute with one another on `V_k`.

`HJO.Sweep.exists_isDpaAction_mellit` supplies the Mellit-convention action and
`HJO.Sweep.braidRepResidual_of_mellitAction` reads the clause off it. The two `Invertible`
instances are the ones `HJO.Dyck.Aq.yElt` needs to name the corner elements of the algebra at
`q^{-1}`. -/
theorem braidRepResidual_mellit (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) {r : L}
    (hr : r * r = q) (k : ℕ) : BraidRepResidual q u r k := by
  obtain ⟨ρ, hact, hT, hD, hU⟩ := exists_isDpaAction_mellit q u hq hqp
  have hqi : (q⁻¹ : L) ≠ 0 := inv_ne_zero hq
  have hqi1 : (q⁻¹ - 1 : L) ≠ 0 := fun h => hq1 (inv_eq_one.1 (sub_eq_zero.1 h))
  let _ : Invertible (q⁻¹ : L) := invertibleOfNonzero hqi
  let _ : Invertible (q⁻¹ - 1 : L) := invertibleOfNonzero hqi1
  exact braidRepResidual_of_mellitAction hact hT hD hU hq hq1 hr k

/-- **The assignment of `HJO.Sweep.braidRep` respects the presentation of `𝔹_k^+(𝕋_0)`**,
`HJO.Sweep.braidRepRespects_mellit` and Mellit's Proposition 5.3: `π_k` exists.

Nine of the ten relation families come from `HJO.Sweep.braidRepRespects_of_residual` — the two
cancellations, the braid relation and far commutation from `HJO.Sweep.isBraidSystem_braidEnd` with
`r^2 = q`, the out-of-rank family from the guard on the letter assignment, `y_iT_j = T_jy_i`,
`y_iy_j = y_jy_i` and `z_iT_j = T_jz_i` from the two closed forms, and the mixed relation from both
at once. The tenth is `HJO.Sweep.braidRepResidual_mellit`. -/
@[hjo "lem_braid_rep_respects"]
theorem braidRepRespects_mellit (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) {r : L}
    (hr : r * r = q) (k : ℕ) : BraidRepRespects q u r k :=
  braidRepRespects_of_residual q u hq hr k (braidRepResidual_mellit q u hq hq1 hqp hr k)

/-- **The braid representation `π_k`**, with no hypothesis left to supply: `HJO.Sweep.braidRep`
applied to `HJO.Sweep.braidRepRespects_mellit`. Its values on the generators are
`HJO.Sweep.braidRep_T`, `HJO.Sweep.braidRep_Tbar`, `HJO.Sweep.braidRep_y` and
`HJO.Sweep.braidRep_z`. -/
noncomputable def braidRepMellit (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) {r : L}
    (hr : r * r = q) (k : ℕ) : Braid.BraidMonoid k →* Module.End L (pieceSub L k) :=
  braidRep q u r k (braidRepRespects_mellit q u hq hq1 hqp hr k)

end Mellit

end HJO.Sweep

end
