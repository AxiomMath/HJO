/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.MellitConjRel1
public import HJO.CMStructure.MellitConjRel2
public import HJO.CMStructure.StarAction
public import HJO.CMStructure.VmodActionMod
public meta import HJO.Attr

/-! # The Mellit-convention instance of the abstract Dyck-path operator package

`HJO.Sweep.IsDpaOperators` (`HJO/CMStructure/DpaActionBuild.lean`) is abstract in its operator
triple `(T, D, U)`, and three other instances of it are proved elsewhere:

* `HJO.Sweep.isDpaOperators_cm` -- `(T_i, d_-, d_+)` at `q`, i.e. `HJO.Sweep.exists_isDpaAction_cm`;
* `HJO.Sweep.isDpaOperators_mod` -- `(T_i, d^♭_-, d^♭_+)` at `q`, i.e.
  `HJO.Sweep.exists_isDpaAction_mod`;
* `HJO.Sweep.isDpaOperators_star` -- `(T_i^{-1}, d_-, d^*_+)` at `q^{-1}`, i.e. the action half of
  `HJO.Sweep.exists_isDpaAction_star`.

**None of the three is the convention Mellit's `z_i` live in**, and that is the reason this file
exists. `HJO.Sweep.zop` -- hence `HJO.Sweep.zopOneStar`, `HJO.Sweep.zRep` and the residual clause
`HJO.Sweep.BraidRepResidual.zRep_comm` -- is built on `HJO.Sweep.starComm`, the commutator of
`d^*_+` with the lowering operator `HJO.Sweep.dminus` (Mellit's `d^♭_-`, pairing `F_j` with
`e_j`). The starred instance is
all-Carlsson--Mellit: its lowering operator is `HJO.Sweep.dminusCM` (pairing
`F_j` with `e_{j+1}`), and its commutator is `HJO.Sweep.starCommCM`. So the triple this file
supplies is the fourth one, `(T_i^{-1}, d^♭_-, d^*_+)` at `q^{-1}`.

## Main results

* `HJO.Sweep.isDpaOperators_mellit` -- the instance.
* `HJO.Sweep.exists_isDpaAction_mellit` -- the action of `𝔸_{q^{-1}}` on `V_*` it builds, sending
  the loops to `T_i^{-1}`, the lowering arrow to `d^♭_-` and the raising arrow to `d^*_+`.

## The four `D`-relations are proved from scratch, and there is a proof that they must be

The tempting shortcut is to read the four relations off the starred instance through the bridge
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul`, which is
`d_-F = -d^♭_-(y_{k+1}F)`. It does not work, and the obstruction is not a gap in the argument:

* Substituting the bridge into a relation for `d_-` yields the corresponding relation for `d^♭_-`
  **at argument** `y_{k+1}F`. Multiplication by `y_{k+1}` is injective on `V_{k+1}` but not
  surjective -- the vacuum is not in its image -- so a relation known for `d_-` at every argument
  constrains `d^♭_-` only on the ideal `(y_{k+1})`.
* The same bridge does suffice *inside the commutator*, and that much is proved:
  `HJO.Sweep.starCommCM_eq_neg_starComm_auxVar_mul` (`HJO/CMStructure/StarZrelShift.lean`) is
  `[d^*_+, d_-] = -[d^*_+, d^♭_-] ∘ (y_k ·)` on `V_k`. What blocks is the train, and there is a
  witness: `HJO.Sweep.mulLeft_auxVar_two_not_comm_trainUpEnd`
  (`HJO/CMStructure/BraidRepNotTotal.lean`) shows multiplication by `y_2` does not commute with
  `T_{2↗1} = T_1^{-1}`, using only `q ≠ 0`.

So the four fields that read `D` -- `loop_lower`, `lower_sq`, `extra_lower`, `extra_raise` -- are
re-proved in this convention, and the two substantial ones are the contents of
`HJO/CMStructure/MellitConjRel1.lean` and `HJO/CMStructure/MellitConjRel2.lean`.

## What each of the ten fields costs

The six fields that do not mention `D` are exactly the starred instance's, since they involve only
`T_i^{-1}` and `d^*_+`: `HJO.Sweep.braidInv_braidInv_apply`, `HJO.Sweep.braidInv_braidInv_braid`,
`HJO.Sweep.braidInv_comm`, `HJO.Sweep.dplusStar_braidInv` and
`HJO.Sweep.braidInv_one_dplusStar_dplusStar`, plus the quiver-shape field
`HJO.Sweep.braidInvModPiece_of_le`. The four that do:

* `loop_lower` -- `HJO.Sweep.dminus_braidInv` (`HJO.Sweep.braid_dminus` in the inverted loops).
* `lower_sq` -- `HJO.Sweep.dminus_dminus_braidInv` (`HJO.Sweep.dminus_dminus_braid`, likewise).
* `extra_lower` -- `HJO.Sweep.dminus_starComm_braidInv`.
* `extra_raise` -- `HJO.Sweep.braidInv_starComm_dplusStar`.

`q ≠ 0` is unavoidable: the loops of the statement are the inverses `T_i^{-1}`, and the scalar
`q^{-1}` of the relations is `0` at `q = 0` in Lean rather than undefined. `q + 1 ≠ 0` is inherited
from `extra_lower` alone, for the reason recorded at `HJO.Sweep.dminusCM_starCommCM_braidInv`: the
reduced form is equivalent to the relation only up to a factor `1 + q`. Every use instantiates it
at parameters algebraically independent over `ℤ`, where both hold.

**The action this file builds is `HJO.Sweep.exists_isDpaAction_mellit`**: an action `ρ^{♭*}` of
`𝔸_{q^{-1}}` on `V_*` with `ρ^{♭*}(T_i) = T_i^{-1}`, `ρ^{♭*}(d_-) = d^♭_-` and
`ρ^{♭*}(d_+) = d^*_+`, the three operator families being `HJO.Sweep.braidInvModPiece`,
`HJO.Sweep.dminusModPiece` (`HJO.Sweep.dminus`) and `HJO.Sweep.dplusStarPiece`
(`HJO.Sweep.dplusStar`). The commutation clause `z_iz_j = z_jz_i`, discussed under
`HJO.Sweep.braidRepRespects_mellit`, is not part of it.

`q ≠ 0` and `q + 1 ≠ 0` are read and the statement as usually written displays neither; both are
inherited rather than chosen, exactly as at `HJO.Sweep.exists_isDpaAction_mod` (`q ≠ 0`) and
`HJO.Sweep.exists_isDpaAction_star` (both), and they are accounted for above. Every use
instantiates it at parameters algebraically independent over `ℤ`.

## A route via `HJO.Standing.exists_action_atilde_ker_eq_param` that is not taken

One could obtain this action from `HJO.Standing.exists_action_atilde_ker_eq_param` — proved in
`HJO/CMStructure/Thm73Closed.lean` — which gives the first three families and the two extra
relations in the lowering operator `d_-`, and then move to `d^♭_-` by the `[ϑ,-]` argument of
`HJO.Sweep.unitShiftTotal`. Nothing here uses either, and two remarks on that route are recorded.

* **`HJO.Standing.exists_action_atilde_ker_eq_param` is not needed.** The six fields that do not
  mention the lowering operator are the starred instance's, resting on
  `HJO.Sweep.braid_braid_apply`, `HJO.Sweep.braid_braid`, `HJO.Sweep.braid_comm` and
  `HJO.Sweep.dplusStar_braidInv`; the four that do are proved in this convention from
  `HJO.Sweep.dminusCM_starCommCM_braidInv` and `HJO.Sweep.braidInv_starCommCM_dplusStar`, read
  with `HJO.Sweep.starComm` in place of `HJO.Sweep.starCommCM`
  (`HJO/CMStructure/MellitConjRel1.lean`, `MellitConjRel2.lean`).
* **It is not true that passing from `d_-` to `d^♭_-` changes only the two families in which the
  lowering operator occurs together with a raising operator, namely the fourth and the fifth.** The
  *second* family is `T_id_- - d_-T_i` and `d_-^2T_{k-1} - d_-^2`, and both contain the lowering
  operator, so both change under the substitution and neither is supplied by
  `HJO.Standing.exists_action_atilde_ker_eq_param` in the `d^♭_-` reading. They are
  `HJO.Sweep.dminus_braidInv` and `HJO.Sweep.dminus_dminus_braidInv` here — the `loop_lower` and
  `lower_sq` fields — i.e. `HJO.Sweep.braid_dminus` and `HJO.Sweep.dminus_dminus_braid` read in the
  inverted loops. The `[ϑ,-]` argument would in fact cover them, applied once rather than twice, so
  the gap is in the case count, not in the mathematics.

## References

Lemma `HJO.Sweep.exists_isDpaAction_mellit`, on replication and the actions indexed by coprime
pairs, using `HJO.Sweep.dplusStar`, `HJO.Dyck.AqInv`, `HJO.Sweep.IsDpaAction` and
`HJO.Sweep.dminus`; also `HJO.Sweep.exists_isDpaAction_cm`, `HJO.Sweep.exists_isDpaAction_mod`,
`HJO.Sweep.exists_isDpaAction_star`, `HJO.Sweep.dminusCM_starCommCM_braidInv` and
`HJO.Sweep.braidInv_starCommCM_dplusStar`, and the remark on `z_iz_j = z_jz_i` at
`HJO.Sweep.braidRepRespects_mellit`. Transcribing A. Mellit, *Toric braids and `(m, n)`-parking
functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section Mellit

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The Mellit-convention operators satisfy the nine relations of `HJO.Dyck.Aq` at the scalar
`q^{-1}`.**

The triple is `(T_i^{-1}, d^♭_-, d^*_+)`: the inverted Demazure--Lusztig operators, the lowering
operator of `HJO.Sweep.dminus` and the starred raising operator of `HJO.Sweep.dplusStar`. This is
the convention `HJO.Sweep.starComm` and hence `HJO.Sweep.zop` are written in, and it is not the
convention of any of the three other instances -- `HJO.Sweep.isDpaOperators_star` has the same
loops and the same raising arrow but Carlsson and Mellit's own `d_-`.

Field by field. The six not mentioning the lowering operator are the starred instance's, read at the
same operators: `HJO.Sweep.braid_braid_apply`, `HJO.Sweep.braid_braid` and `HJO.Sweep.braid_comm`
in the inverted loops, and both clauses of `HJO.Sweep.dplusStar_braidInv` about the raising arrow.
The four that do are proved in this convention rather than transported -- see the module docstring,
and `HJO/CMStructure/BraidRepNotTotal.lean` for the proved half of the obstruction:
`HJO.Sweep.dminus_braidInv`, `HJO.Sweep.dminus_dminus_braidInv`,
`HJO.Sweep.dminus_starComm_braidInv` and `HJO.Sweep.braidInv_starComm_dplusStar`. -/
theorem isDpaOperators_mellit (q u : L) (hq : q ≠ 0) (hq1 : q + 1 ≠ 0) :
    IsDpaOperators q⁻¹ (braidInvModPiece q) (dminusModPiece q) (dplusStarPiece q u) where
  loop_eq_zero h := braidInvModPiece_of_le q h
  quadratic := by
    intro k i hik F
    refine Subtype.ext ?_
    simp only [AddMemClass.coe_add, SetLike.val_smul, coe_braidInvModPiece q hik,
      smul_eq_scal_mul]
    exact braidInv_braidInv_apply q hq (i + 1) _
  braid := by
    intro k i hik F
    refine Subtype.ext ?_
    simp only [coe_braidInvModPiece q (show i + 2 ≤ k from by omega),
      coe_braidInvModPiece q (show i + 1 + 2 ≤ k from by omega)]
    exact braidInv_braidInv_braid q hq (show 1 ≤ i + 1 from by omega) _
  comm := by
    intro k i j hi hj hij F
    refine Subtype.ext ?_
    simp only [coe_braidInvModPiece q hi, coe_braidInvModPiece q hj]
    exact braidInv_comm q (show 1 ≤ i + 1 from by omega)
      (show i + 1 + 2 ≤ j + 1 from by omega) _
  loop_lower := by
    intro m i him F
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    refine Subtype.ext ?_
    simp only [coe_braidInvModPiece q him, coe_dminusModPiece,
      coe_braidInvModPiece q (show i + 2 ≤ n + 2 + 1 from by omega)]
    exact (dminus_braidInv q (k := n + 1) (show i + 1 ≤ n + 1 from by omega) _).symm
  lower_sq := by
    intro m F
    refine Subtype.ext ?_
    simp only [coe_dminusModPiece, coe_braidInvModPiece q (show m + 2 ≤ m + 2 from le_rfl)]
    exact dminus_dminus_braidInv q hq m F.2
  raise_loop := by
    intro k i hik F
    refine Subtype.ext ?_
    simp only [coe_dplusStarPiece, coe_braidInvModPiece q hik,
      coe_braidInvModPiece q (show i + 1 + 2 ≤ k + 1 from by omega)]
    exact dplusStar_braidInv q u hq (show 1 ≤ i + 1 from by omega)
      (show i + 1 < k from by omega) _
  raise_sq := by
    intro k F
    refine Subtype.ext ?_
    simp only [coe_braidInvModPiece q (show 0 + 2 ≤ k + 2 from by omega), coe_dplusStarPiece]
    exact braidInv_one_dplusStar_dplusStar q u hq F.2
  extra_lower := by
    intro j F
    refine Subtype.ext ?_
    simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, coe_dminusModPiece, coe_dplusStarPiece,
      coe_braidInvModPiece q (show j + 2 ≤ j + 2 from le_rfl)]
    exact dminus_starComm_braidInv q u hq hq1 (k := j) F.2
  extra_raise := by
    intro m F
    refine Subtype.ext ?_
    simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, coe_dminusModPiece, coe_dplusStarPiece,
      coe_braidInvModPiece q (show 0 + 2 ≤ m + 2 from by omega)]
    have h := braidInv_starComm_dplusStar q u hq (k := m) F.2
    simp only [map_sub] at h ⊢
    exact h

/-! ### The action -/

/-- **Mellit, the conjugate modified action**, `HJO.Sweep.exists_isDpaAction_mellit`: there is an
action `ρ^{♭*}` of `𝔸_{q^{-1}}` on `V_*` with `ρ^{♭*}(T_i) = T_i^{-1}`, `ρ^{♭*}(d_-) = d^♭_-` and
`ρ^{♭*}(d_+) = d^*_+`. The operators `T_i^{-1}`, `d^♭_-`, `d^*_+` and the projections onto the
summands define an action of `𝔸_{q^{-1}}` on `V_*`.

`HJO.Dyck.Aq` being a presentation, that is the statement that the assignment of its generators to
those operators descends to an algebra homomorphism out of `HJO.Dyck.Aq L q⁻¹`, and here it is one
satisfying `HJO.Sweep.IsDpaAction` as well. Both halves are
`HJO.Sweep.IsDpaOperators.exists_isDpaAction`, and the input is
`HJO.Sweep.isDpaOperators_mellit`.

**Why this is a different action from `HJO.Sweep.exists_isDpaAction_star`**, which has the same
source algebra and the same images for the loops and the raising arrow: the lowering arrow goes to
`HJO.Sweep.dminus` here and to `HJO.Sweep.dminusCM` there, and those are different operators --
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul` relates them only after multiplication by the last
variable. The commutator of `d^*_+` with the lowering arrow is correspondingly
`HJO.Sweep.starComm` here and `HJO.Sweep.starCommCM` there, and it is the former that
`HJO.Sweep.zopOneStar`, `HJO.Sweep.zop` and `HJO.Sweep.zRep` are built on. That difference is why
this action, and not `HJO.Sweep.exists_isDpaAction_star`, is the one needed: it has
`ρ^{♭*}(d_-) = d^♭_-`, and that is also the second
condition of `HJO.Sweep.IsIntertwinedPair`, which the pair `(ρ^♭, ρ^{♭*})` of
`HJO.Sweep.exists_isIntertwinedPair_vmod` has to satisfy against `ρ^♭(d_-) = d^♭_-`. -/
@[hjo "lem_vmod_action_star"]
theorem exists_isDpaAction_mellit (q u : L) (hq : q ≠ 0) (hq1 : q + 1 ≠ 0) :
    ∃ ρ : Dyck.Aq L q⁻¹ →ₐ[L] Module.End L (Vstar L), IsDpaAction q⁻¹ ρ
      ∧ (∀ k i : ℕ, ρ (Dyck.Aq.Tg L q⁻¹ k i) = loopVstar (braidInvModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dMinus L q⁻¹ k) = lowerVstar (dminusModPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dPlus L q⁻¹ k) = raiseVstar (dplusStarPiece q u) k) :=
  (isDpaOperators_mellit q u hq hq1).exists_isDpaAction

/-- `HJO.Sweep.exists_isDpaAction_mellit` over `HJO.Dyck.AqInv L q`, which is `HJO.Dyck.Aq L ⅟q` by
`HJO.Dyck.AqInv`. This is the shape `HJO.Sweep.IsIntertwinedPair` reads,
`HJO.Sweep.IsIntertwinedPair` taking its second action out of that algebra; at the instance
`invertibleOfNonzero` the two statements are the same one, `⅟q` being `q⁻¹` there. The same step as
`HJO.Sweep.exists_isDpaAction_starInv`, one convention over. -/
theorem exists_isDpaAction_mellitInv (q u : L) [Invertible q] (hq1 : q + 1 ≠ 0) :
    ∃ ρ : Dyck.Aq L (⅟q) →ₐ[L] Module.End L (Vstar L), IsDpaAction (⅟q) ρ
      ∧ (∀ k i : ℕ, ρ (Dyck.Aq.Tg L (⅟q) k i) = loopVstar (braidInvModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dMinus L (⅟q) k) = lowerVstar (dminusModPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dPlus L (⅟q) k) = raiseVstar (dplusStarPiece q u) k) := by
  rw [invOf_eq_inv]
  exact exists_isDpaAction_mellit q u (Invertible.ne_zero q) hq1

end Mellit

end HJO.Sweep

end
