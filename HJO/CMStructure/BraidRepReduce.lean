/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.YBraid
public import HJO.CMStructure.ZBraid
public import HJO.CMStructure.ZyMixed

/-! # What is left of `HJO.Sweep.braidRep`'s well-definedness

`HJO.Sweep.braidRep` — takes `HJO.Sweep.BraidRepRespects` as
an argument, because a homomorphism out of a presented monoid exists exactly when the assignment
respects the presentation, and that is Mellit's Proposition 5.3,
`HJO.Sweep.braidRepRespects_mellit`. This file reduces that hypothesis to a single clause, using the
closed forms of the operators.

Of the ten relation families of `HJO.Braid.BraidRel`, nine are discharged here:

* the two cancellations, the braid relation and far commutation, from
  `HJO.Sweep.isBraidSystem_braidEnd` together with `r^2 = q`;
* the out-of-rank family from the guard in `HJO.Sweep.braidRepLetterTotal`;
* `y_iT_j = T_jy_i` and `y_iy_j = y_jy_i` from `HJO.Sweep.yRepTotal_mul_braidEnd` and
  `HJO.Sweep.yRepTotal_mul_comm`, which come off the closed form "`y_i` is multiplication by
  `-y_i`" of `HJO/CMStructure/YBraid.lean`;
* `z_iT_j = T_jz_i` from `HJO.Sweep.zRepTotal_mul_braidEnd`, which comes off the closed form
  `z_{i+1} = q^{-i}T_{i+1↘1}z_1T_{1↗i+1}` of `HJO/CMStructure/ZBraid.lean`;
* the mixed relation `z_1T_1y_1T_1^{-1} = qT_1^{-1}y_1T_1^{-1}z_1` from
  `HJO.Sweep.zRepTotal_braidEnd_yRepTotal_braidInvEnd`, which reads both closed forms at once in
  `HJO/CMStructure/ZyMixed.lean`: the right-hand side is multiplication by `y_2`, and the
  commutator inside `z_1` raises the index of a multiplier just as it raises the index of a braid
  letter.

`HJO.Sweep.BraidRepResidual` is the one that is left: `z_iz_j = z_jz_i`, **on the graded piece**.

## The nine are proved on the total space and the tenth is asked on `V_k`

All nine closed forms are identities in `Module.End L (Total L)`, and
`HJO.Sweep.braidRepFreeTotal_rel_or_zWord` — the one induction this file runs — returns either
such an identity or the `zWord_comm` instance that produced the goal. Both reductions then read
that disjunction:

* `HJO.Sweep.braidRepRespectsTotal_of_residualTotal` answers the `zWord_comm` branch with the
  total-space clause `HJO.Sweep.BraidRepResidualTotal.zRepTotal_comm`, and so proves
  the total-space hypothesis from it. **That hypothesis is false at `k = 2`**
  (`HJO.Sweep.braidRepRespectsTotal_two_false`), so this reduction is kept for the refutation
  and for rank `1`, not as a route to `HJO.Sweep.braidRep`.
* `HJO.Sweep.braidRepRespects_of_residual` answers it with the *piece-level* clause
  `HJO.Sweep.BraidRepResidual.zRep_comm`, and pushes each of the nine down with
  `HJO.Sweep.braidRepFree_eq_of_total`. This is the reduction `HJO.Sweep.braidRep` runs on, and the
  residual clause it leaves is proved as `HJO.Sweep.braidRepResidual_mellit`
  (`HJO/CMStructure/MellitBraidRep.lean`).

The whole point of the split is that `z_1z_2 = z_2z_1` **is** refuted on the total space —
`HJO.Sweep.zop_two_not_comm` disagrees on `y_3`, outside `V_2` — and is not refuted on `V_2`,
where `HJO.Sweep.zop_mem_piece` says both operators live.

## The one clause, and why it is not free

`z_iz_j = z_jz_i` does not follow from the closed forms already in hand. Against
`HJO.Sweep.zop_eq_conj` it becomes an identity between two words in `z_1` and four trains, and
nothing cancels: `z_1` does not commute with `T_1`, which occurs in every train for `j ≥ 2`. Nor is
it a direct transport of `HJO.Sweep.map_yElt_low_comm` across `HJO.Sweep.exists_slopeActions`: that
would need `HJO.Dyck.Tilde.Atilde.zElt_one_eq_wordDownStar`, `HJO.Dyck.Tilde.Atilde.zElt_succ_eq`
(without which `ρ^*(y_i)` is not identified with `z_i` at all), and a bridge carrying
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul` through the commutator and both trains, the two sides
sitting in different `d_-` conventions — and that bridge fails at the train
(`HJO.Sweep.mulLeft_auxVar_two_not_comm_trainUpEnd`). The clause is proved instead as
`HJO.Sweep.braidRepResidual_mellit`, from an action of the Dyck path algebra in Mellit's convention;
the typing on `V_k` makes the clause a *statable* target, and this file does not prove it.

The mixed relation is proved by reading the index shifts on multipliers rather than on braid
letters, and it is *not* a consequence of the `y` closed form alone: the conjugate
`T_1y_1T_1^{-1}` is not a multiplication operator — `HJO.Sweep.braid_sub_self` makes it
`y_2 + (q-1)y_1T_1^{-1}` — so the clause is a genuine statement about `z_1`, discharged in
`HJO/CMStructure/ZyMixed.lean` and not by commutativity.

## Main results

* `HJO.Sweep.BraidRepResidual` — the one-clause residue of Mellit's Proposition 5.3, on `V_k`.
* `HJO.Sweep.BraidRepResidualTotal` — the same clause on the total space, which is what
  `HJO/CMStructure/BraidRepNotTotal.lean` refutes at `k = 2`.
* `HJO.Sweep.braidRepRespects_of_residual` — **the reduction**;
  `HJO.Sweep.braidRepRespectsTotal_of_residualTotal` — its total-space counterpart.
* `HJO.Sweep.braidResidual_iff_zop_comm` — the residual clause with the representation removed:
  `z_iz_j = z_jz_i` for the operators of `HJO.Sweep.zop`, *on `V_k`*. This is the target.
* `HJO.Sweep.braidRepResidual_one`, `HJO.Sweep.braidRepRespects_one` — at rank `1` the clause is
  an element with itself, so `π_1` exists outright; with
  `HJO.Sweep.braidRepRespectsTotal_one` it exists on the total space too, which is the typing
  `HJO.Sweep.slopeOperator` is written in.

## References

A. Mellit, *Toric braids and `(m, n)`-parking
functions*, Proposition 5.3.
-/

@[expose] public section

namespace HJO.Sweep

open Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- A product of two scaled endomorphisms scales by the product. -/
private theorem smul_mul_smul' (a b : L) (f g : Module.End L (Total L)) :
    (a • f) * (b • g) = (a * b) • (f * g) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

/-- **Nine of the ten relation families, discharged on the total space.** Given a relation
`BraidRel k x y`, either the two words already have the same image in `Module.End L (Total L)` —
which is what the nine closed forms give — or the relation is the `zWord_comm` instance at
some pair of indices, returned here so that each of the two reductions below can answer it in its
own codomain. -/
private theorem braidRepFreeTotal_rel_or_zWord (q u : L) {r : L} (hq : q ≠ 0) (hr : r * r = q)
    {k : ℕ} {x y : FreeMonoid Letter} (hrel : BraidRel k x y) :
    braidRepFreeTotal q u r k x = braidRepFreeTotal q u r k y
      ∨ ∃ i j : ℕ, (1 ≤ i ∧ i ≤ k ∧ 1 ≤ j ∧ j ≤ k)
          ∧ x = zWord i * zWord j ∧ y = zWord j * zWord i := by
  have hr0 : r ≠ 0 := fun h0 => hq (by rw [← hr, h0, mul_zero])
  have hbs := isBraidSystem_braidEnd q hq k
  induction hrel with
  | mul_inv i hi hik =>
    refine Or.inl ?_
    simp only [map_mul, map_one, braidRepFreeTotal_of, braidRepLetterTotal_T q u r hi hik,
      braidRepLetterTotal_Tbar q u r hi hik, smul_mul_smul', inv_mul_cancel₀ hr0,
      hbs.mul_inv i hi hik, one_smul]
  | inv_mul i hi hik =>
    refine Or.inl ?_
    simp only [map_mul, map_one, braidRepFreeTotal_of, braidRepLetterTotal_T q u r hi hik,
      braidRepLetterTotal_Tbar q u r hi hik, smul_mul_smul', mul_inv_cancel₀ hr0,
      hbs.inv_mul i hi hik, one_smul]
  | braid i hi hik =>
    refine Or.inl ?_
    simp only [map_mul, braidRepFreeTotal_of,
      braidRepLetterTotal_T q u r hi (show i + 1 ≤ k by omega),
      braidRepLetterTotal_T q u r (show 1 ≤ i + 1 by omega) (show i + 1 + 1 ≤ k by omega),
      smul_mul_smul', hbs.braid i hi hik]
  | far_comm i j hi hij hjk =>
    refine Or.inl ?_
    simp only [map_mul, braidRepFreeTotal_of,
      braidRepLetterTotal_T q u r hi (show i + 1 ≤ k by omega),
      braidRepLetterTotal_T q u r (show 1 ≤ j by omega) hjk, smul_mul_smul',
      hbs.far_comm i j hi hij hjk]
  | yWord_comm_T i j hi hik hj hjk hne hne' =>
    refine Or.inl ?_
    simp only [map_mul, braidRepFreeTotal_of, braidRepLetterTotal_T q u r hj hjk,
      ← yRepTotal_def, mul_smul_comm, smul_mul_assoc,
      yRepTotal_mul_braidEnd q u hq hr hi hik hne hne']
  | zWord_comm_T i j hi hik hj hjk hne hne' =>
    refine Or.inl ?_
    simp only [map_mul, braidRepFreeTotal_of, braidRepLetterTotal_T q u r hj hjk,
      ← zRepTotal_def, mul_smul_comm, smul_mul_assoc,
      zRepTotal_mul_braidEnd q u hq hr hi hik hj hjk hne hne']
  | yWord_comm i j hi hik hj hjk =>
    refine Or.inl ?_
    simpa only [map_mul, ← yRepTotal_def] using yRepTotal_mul_comm q u hq hr hi hik hj hjk
  | zWord_comm i j hi hik hj hjk =>
    exact Or.inr ⟨i, j, ⟨hi, hik, hj, hjk⟩, rfl, rfl⟩
  | zy hk =>
    refine Or.inl ?_
    have hz := zRepTotal_braidEnd_yRepTotal_braidInvEnd q u hq hr hk
    simp only [map_mul, braidRepFreeTotal_of,
      braidRepLetterTotal_T q u r le_rfl (show 1 + 1 ≤ k by omega),
      braidRepLetterTotal_Tbar q u r le_rfl (show 1 + 1 ≤ k by omega), ← yRepTotal_def,
      ← zRepTotal_def, mul_smul_comm, smul_mul_assoc, smul_smul]
    rw [show r * r⁻¹ = 1 from mul_inv_cancel₀ hr0, one_smul, hz, hr]
  | out_of_rank c hc =>
    refine Or.inl ?_
    simp only [map_one, braidRepFreeTotal_of, braidRepLetterTotal_of_not_inRank q u r hc]

/-- **What is left of `HJO.Sweep.braidRep`'s well-definedness after the closed forms have been
used.** Mellit's Proposition 5.3 has five clauses; four of them — `y_iT_j = T_jy_i`,
`y_iy_j = y_jy_i`, `z_iT_j = T_jz_i` and the mixed relation — are theorems
(`HJO.Sweep.yRepTotal_mul_braidEnd`, `HJO.Sweep.yRepTotal_mul_comm`,
`HJO.Sweep.zRepTotal_mul_braidEnd`,
`HJO.Sweep.zRepTotal_braidEnd_yRepTotal_braidInvEnd`), and this one is not.

The clause is asked **on the graded piece**, which is `HJO.Sweep.braidRep`'s own codomain. The same
clause on the total space is `HJO.Sweep.BraidRepResidualTotal`, and it is refuted at `k = 2` by
`HJO.Sweep.braidRepResidualTotal_two_false`. -/
structure BraidRepResidual (q u r : L) (k : ℕ) : Prop where
  /-- The `z` operators commute with one another, as endomorphisms of `V_k`. -/
  zRep_comm : ∀ i j, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k →
    zRep q u r k i * zRep q u r k j = zRep q u r k j * zRep q u r k i

/-- **The same clause on the total space, which is false at `k = 2`.** This is the total-space
variant of `HJO.Sweep.BraidRepResidual`; `HJO.Sweep.braidRepResidualTotal_two_false` refutes it,
and that refutation is the reason `HJO.Sweep.BraidRepResidual` asks the clause on `V_k` instead.
No result of this library assumes this; it is stated so that the negative result has a subject. -/
structure BraidRepResidualTotal (q u r : L) (k : ℕ) : Prop where
  /-- The `z` operators commute with one another, on the whole total space. -/
  zRepTotal_comm : ∀ i j, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k →
    zRepTotal q u r k i * zRepTotal q u r k j = zRepTotal q u r k j * zRepTotal q u r k i

/-- The total-space clause implies the one on the graded piece, by
`HJO.Sweep.braidRepFree_eq_of_total`. The converse fails — `HJO.Sweep.zop_two_not_comm`. -/
theorem braidRepResidual_of_total (q u r : L) (k : ℕ) (h : BraidRepResidualTotal q u r k) :
    BraidRepResidual q u r k where
  zRep_comm i j hi hik hj hjk := by
    have hd := braidRepFree_eq_of_total q u r k (x := zWord i * zWord j) (y := zWord j * zWord i)
      (by simpa only [map_mul, ← zRepTotal_def] using h.zRepTotal_comm i j hi hik hj hjk)
    simpa only [map_mul, ← zRep_def] using hd

/-- **The reduction.** Nine of the ten relation families of `HJO.Braid.BraidRel` are discharged
— the two cancellations, the braid relation and far commutation from
`HJO.Sweep.isBraidSystem_braidEnd` with `r^2 = q`, the out-of-rank family from the guard in
`HJO.Sweep.braidRepLetterTotal`, the three `y`- and `z`-commutations from the two closed forms, and
the mixed relation from both at once — so well-definedness of `HJO.Sweep.braidRep` is exactly the
one clause of `HJO.Sweep.BraidRepResidual`.

The nine are identities on the total space and descend by
`HJO.Sweep.braidRepFree_eq_of_total`; only the tenth is asked on `V_k`, and that is what makes
the hypothesis survivable at `k = 2` where its total-space form does not. -/
theorem braidRepRespects_of_residual (q u : L) {r : L} (hq : q ≠ 0) (hr : r * r = q) (k : ℕ)
    (h : BraidRepResidual q u r k) : BraidRepRespects q u r k := by
  intro x y hrel
  rcases braidRepFreeTotal_rel_or_zWord q u hq hr hrel with
    heq | ⟨i, j, ⟨hi, hik, hj, hjk⟩, rfl, rfl⟩
  · exact braidRepFree_eq_of_total q u r k heq
  · simpa only [map_mul, ← zRep_def] using h.zRep_comm i j hi hik hj hjk

/-- **The reduction on the total space.** The same nine families, with the tenth answered by the
total-space clause. Kept for two purposes only: `HJO/CMStructure/BraidRepNotTotal.lean`
refutes its conclusion at `k = 2` through it, and at rank `1` it is what puts
`HJO.Sweep.slopeOperator` in the typing it is written in. -/
theorem braidRepRespectsTotal_of_residualTotal (q u : L) {r : L} (hq : q ≠ 0) (hr : r * r = q)
    (k : ℕ) (h : BraidRepResidualTotal q u r k) : BraidRepRespectsTotal q u r k := by
  intro x y hrel
  rcases braidRepFreeTotal_rel_or_zWord q u hq hr hrel with
    heq | ⟨i, j, ⟨hi, hik, hj, hjk⟩, rfl, rfl⟩
  · exact heq
  · simpa only [map_mul, ← zRepTotal_def] using h.zRepTotal_comm i j hi hik hj hjk

/-! ### What the residual clause asks, in terms of the operators

The point of typing `HJO.Sweep.braidRep` at `HJO.Sweep.pieceSub L k` is that the one clause left
becomes a statement about `HJO.Sweep.zop`'s own operator — *restricted to `V_k`*, with no
representation and no braid monoid in it. `HJO.Sweep.braidResidual_iff_zop_comm` is that
translation, and it is the form a proof of the clause has to establish. -/

/-- **The residual clause, with the representation removed.** `HJO.Sweep.BraidRepResidual` holds
exactly when the operators `z_i` of `HJO.Sweep.zop` commute with one another *on `V_k`*, for
`1 ≤ i, j ≤ k`. The normalising scalar `(qu)^{-1}` of `HJO.Sweep.zRepTotal_eq_smul_zop` appears
squared on both sides and cancels, which is where `q ≠ 0` and `u ≠ 0` are spent.

Compare `HJO.Sweep.zop_two_not_comm`: the same commutation on the *whole* total space is false at
`k = 2`. The difference between the two statements is the membership hypothesis `F ∈ piece L k`,
and `HJO.Sweep.zop_mem_piece` is what makes the restricted one well posed. -/
theorem braidResidual_iff_zop_comm (q u : L) {r : L} (hq : q ≠ 0) (hu : u ≠ 0) (hr : r * r = q)
    (k : ℕ) :
    BraidRepResidual q u r k ↔
      ∀ i j : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → ∀ F ∈ piece L k,
        zop q u k i (zop q u k j F) = zop q u k j (zop q u k i F) := by
  have hqu : q * u ≠ 0 := mul_ne_zero hq hu
  have key : ∀ i j : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → ∀ x : pieceSub L k,
      ((zRep q u r k i * zRep q u r k j) x : Total L)
        = ((q * u)⁻¹ * (q * u)⁻¹) • zop q u k i (zop q u k j x) := by
    intro i j hi hik hj hjk x
    rw [Module.End.mul_apply, coe_zRep, zRepTotal_eq_smul_zop q u hr i hi hik,
      LinearMap.smul_apply, coe_zRep, zRepTotal_eq_smul_zop q u hr j hj hjk,
      LinearMap.smul_apply, map_smul, smul_smul]
  constructor
  · intro h i j hi hik hj hjk F hF
    have hx : ((zRep q u r k i * zRep q u r k j) (⟨F, hF⟩ : pieceSub L k) : Total L)
        = ((zRep q u r k j * zRep q u r k i) (⟨F, hF⟩ : pieceSub L k) : Total L) := by
      rw [h.zRep_comm i j hi hik hj hjk]
    rw [key i j hi hik hj hjk, key j i hj hjk hi hik] at hx
    have hA := congrArg (fun G : Total L => ((q * u) * (q * u)) • G) hx
    simp only [smul_smul] at hA
    rw [show (q * u) * (q * u) * ((q * u)⁻¹ * (q * u)⁻¹)
        = ((q * u) * (q * u)⁻¹) * ((q * u) * (q * u)⁻¹) from by ring,
      mul_inv_cancel₀ hqu, one_mul] at hA
    simpa only [one_smul] using hA
  · intro h
    refine ⟨fun i j hi hik hj hjk => ?_⟩
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [key i j hi hik hj hjk, key j i hj hjk hi hik, h i j hi hik hj hjk x x.2]

/-! ### Rank one, where the hypothesis is free -/

/-- **At rank `1` the residual clause is trivial**, so what is left of Mellit's Proposition 5.3
asks nothing there: the only letters in rank are `y_1` and `z_1`, there is no `T_j`, and the
commutation clause is an element with itself. This is the "`𝔹_1^+(𝕋_0)` is the free
monoid on `y_1` and `z_1`", read on the representation. -/
theorem braidRepResidual_one (q u r : L) : BraidRepResidual q u r 1 where
  zRep_comm i j hi hik hj hjk := by
    obtain rfl : i = 1 := by omega
    obtain rfl : j = 1 := by omega
    rfl

/-- **Rank `1` is not refuted**, and the total-space clause holds there for the same reason: the
commutation is an element with itself. `HJO.Sweep.braidRepResidualTotal_two_false` is about
rank `2`. -/
theorem braidRepResidualTotal_one (q u r : L) : BraidRepResidualTotal q u r 1 where
  zRepTotal_comm i j hi hik hj hjk := by
    obtain rfl : i = 1 := by omega
    obtain rfl : j = 1 := by omega
    rfl

/-- **`π_1` exists outright**, with no hypothesis, at `HJO.Sweep.braidRep`'s own codomain. -/
theorem braidRepRespects_one (q u : L) {r : L} (hq : q ≠ 0) (hr : r * r = q) :
    BraidRepRespects q u r 1 :=
  braidRepRespects_of_residual q u hq hr 1 (braidRepResidual_one q u r)

/-- **And on the total space too**: the rank-one representation is the one
`HJO.Sweep.slopeOperator` is already written in — "the image of `β_{m,n}` under the rank-one
case of `HJO.Sweep.braidRep`, in which no `T_i` occurs and no square root of `q` is needed" — and
`HJO.Sweep.braidRepTotal_one_y1`, `HJO.Sweep.braidRepTotal_one_z1` are its two letter values,
matching `HJO.Sweep.slopeOperator`'s on the nose. -/
theorem braidRepRespectsTotal_one (q u : L) {r : L} (hq : q ≠ 0) (hr : r * r = q) :
    BraidRepRespectsTotal q u r 1 :=
  braidRepRespectsTotal_of_residualTotal q u hq hr 1 (braidRepResidualTotal_one q u r)

end HJO.Sweep
