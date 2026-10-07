/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.DminusSqBraid
public import HJO.CMStructure.DpaActionBuild
public import HJO.CMStructure.VmodExtraMod
public meta import HJO.Attr

/-! # Mellit's modified action of the Dyck path algebra on `V_*`

`HJO.Sweep.exists_isDpaAction_mod`: there is an action `ρ^♭` of `𝔸_q` on `V_*` with
`ρ^♭(T_i) = T_i`, `ρ^♭(d_-) = d^♭_-` and `ρ^♭(d_+) = d^♭_+`, the modified operators being those of
`HJO.Sweep.dminus` and `HJO.Sweep.dplus_eq_ascWord`, that is, `HJO.Sweep.dminus` and
`HJO.Sweep.dplus`.

The construction is `HJO.Sweep.IsDpaOperators.exists_isDpaAction`, shared with
`HJO.Sweep.exists_isDpaAction_cm`: the assignment of the generators of `HJO.Dyck.Aq` to the
operators extends to the path algebra, and what has to be checked is the nine defining relations of
`HJO.Dyck.Aq`. This file supplies them for the modified operators, one field of
`HJO.Sweep.IsDpaOperators` per relation, each an earlier lemma.

## Main definitions

* `HJO.Sweep.dminusModPiece`, `HJO.Sweep.dplusModPiece` — the two modified operators as maps between
  the graded pieces, which is where the relations reading a membership live.

## Main results

* `HJO.Sweep.exists_isDpaAction_mod`.
* `HJO.Sweep.isDpaOperators_mod` — the nine relations, collected.

## Implementation notes

**The nine relations are nine earlier lemmas, in the order of the definition.** The first family is
`HJO.Sweep.braid_braid_apply`, `HJO.Sweep.braid_braid` and `HJO.Sweep.braid_comm`, read on the
summand in `HJO.Sweep.braidModPiece_quadratic` and its two companions — the operators `T_i` being
literally `HJO.Sweep.braid`, which is what it means for the operators `T_i` to be the
same as in `HJO.Sweep.exists_isDpaAction_cm`. The second family is `HJO.Sweep.braid_dminus`
and `HJO.Sweep.dminus_dminus_braid`, the third `HJO.Sweep.dplus_braid_succ` and
`HJO.Sweep.braid_one_dplus_sq`, the fourth `HJO.Sweep.dminus_commutator_braid` and the fifth
`HJO.Sweep.braid_one_commutator_dplus`.

**Two of them read the `F ∈ V_k`, and the summand supplies it.**
`HJO.Sweep.braid_one_dplus_sq` and `HJO.Sweep.dminus_dminus_braid` are false on the total space;
here they are applied to the underlying element of a term of `HJO.Sweep.pieceSub`, whose defining
property is exactly the membership, so `F.2` discharges the hypothesis and nothing has to be carried
into the statement.

**`q ≠ 0` is read, although the statement as usually given does not assume it.** This is a
narrowing, and it is
inherited rather than chosen: it is the hypothesis of `HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus`,
`HJO.Sweep.dminus_trainUpEnd_star_cmDPlus`, `HJO.Sweep.cmAscWord_auxVar_last_mul` and
`HJO.Sweep.braid_braidInv`, hence of `HJO.Sweep.dplus_dminus_sub_dminus_dplus` and of the two extra
relations that rest on it, and every lemma on the modified operators carries it. Every consumer
supplies it: the shuffle side is instantiated at parameters algebraically independent over `ℤ`,
which gives `q ≠ 0`. The unstarred instance `HJO.Sweep.exists_isDpaAction_cm` needs no such
hypothesis. No `q ≠ 1` appears anywhere: every relation is polynomial in `q`.

## References

The lemma `HJO.Sweep.exists_isDpaAction_mod`, on the modified operators, using `HJO.Dyck.Aq`,
`HJO.Sweep.braid`, `HJO.Sweep.IsDpaAction`, `HJO.Sweep.dminus`, `HJO.Sweep.dplus_eq_ascWord`,
`HJO.Sweep.braid_braid_apply`, `HJO.Sweep.braid_braid`, `HJO.Sweep.braid_comm`,
`HJO.Sweep.exists_isDpaAction_cm`, `HJO.Sweep.braid_dminus`, `HJO.Sweep.dminus_dminus_braid`,
`HJO.Sweep.dplus_braid_succ`, `HJO.Sweep.braid_one_dplus_sq`, `HJO.Sweep.dminus_commutator_braid`
and `HJO.Sweep.braid_one_commutator_dplus`. Following A. Mellit, *Toric braids and
`(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section Mod

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The two modified operators between the graded pieces -/

/-- `d^♭_-` as a map between the graded pieces, `V_{k+1} → V_k`, the codomain
`HJO.Sweep.dminus` gives it. -/
noncomputable def dminusModPiece (q : L) (k : ℕ) : pieceSub L (k + 1) →ₗ[L] pieceSub L k :=
  (dminus q (k + 1)).restrict fun _ hx => dminus_mem_piece q (k + 1) hx

/-- `d^♭_+` as a map between the graded pieces, `V_k → V_{k+1}`, the codomain
`HJO.Sweep.dplus_eq_ascWord` gives it. -/
noncomputable def dplusModPiece (q : L) (k : ℕ) : pieceSub L k →ₗ[L] pieceSub L (k + 1) :=
  (dplus q k).restrict fun _ hx => dplus_mem_piece q k hx

@[simp]
theorem coe_dminusModPiece (q : L) (k : ℕ) (F : pieceSub L (k + 1)) :
    (dminusModPiece q k F : Total L) = dminus q (k + 1) F := rfl

omit [Algebra ℚ L] in
@[simp]
theorem coe_dplusModPiece (q : L) (k : ℕ) (F : pieceSub L k) :
    (dplusModPiece q k F : Total L) = dplus q k F := rfl

/-! ### The nine relations -/

/-- **The modified operators satisfy the nine defining relations of `𝔸_q`.** Field by field, the
nine lemmas: the first family `HJO.Sweep.braid_braid_apply`, `HJO.Sweep.braid_braid` and
`HJO.Sweep.braid_comm`; the second `HJO.Sweep.braid_dminus` and `HJO.Sweep.dminus_dminus_braid`; the
third `HJO.Sweep.dplus_braid_succ` and `HJO.Sweep.braid_one_dplus_sq`; the fourth
`HJO.Sweep.dminus_commutator_braid` and the fifth `HJO.Sweep.braid_one_commutator_dplus`. -/
theorem isDpaOperators_mod (q : L) (hq : q ≠ 0) :
    IsDpaOperators q (braidModPiece q) (dminusModPiece q) (dplusModPiece q) where
  loop_eq_zero h := braidModPiece_of_le q h
  quadratic h F := braidModPiece_quadratic q h F
  braid h F := braidModPiece_braid q h F
  comm hi hj hij F := braidModPiece_comm q hi hj hij F
  loop_lower := by
    intro m i him F
    refine Subtype.ext ?_
    simp only [coe_braidModPiece q him, coe_dminusModPiece,
      coe_braidModPiece q (show i + 2 ≤ m + 1 from by omega)]
    exact braid_dminus q (show i + 1 + 2 ≤ m + 1 from by omega) _
  lower_sq := by
    intro m F
    refine Subtype.ext ?_
    simp only [coe_dminusModPiece, coe_braidModPiece q (show m + 2 ≤ m + 2 from le_rfl)]
    exact dminus_dminus_braid q m F.2
  raise_loop := by
    intro k i hik F
    refine Subtype.ext ?_
    simp only [coe_dplusModPiece, coe_braidModPiece q hik,
      coe_braidModPiece q (show i + 1 + 2 ≤ k + 1 from by omega)]
    exact dplus_braid_succ q (by omega) (by omega) _
  raise_sq := by
    intro k F
    refine Subtype.ext ?_
    simp only [coe_braidModPiece q (show 0 + 2 ≤ k + 2 from by omega), coe_dplusModPiece]
    exact braid_one_dplus_sq q F.2
  extra_lower := by
    intro j F
    refine Subtype.ext ?_
    simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, coe_dminusModPiece, coe_dplusModPiece,
      coe_braidModPiece q (show j + 2 ≤ j + 2 from le_rfl), smul_eq_scal_mul]
    exact dminus_commutator_braid q hq j F.2
  extra_raise := by
    intro m F
    refine Subtype.ext ?_
    simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, coe_dminusModPiece, coe_dplusModPiece,
      coe_braidModPiece q (show 0 + 2 ≤ m + 2 from by omega), smul_eq_scal_mul]
    exact braid_one_commutator_dplus q hq m F.2

/-! ### The action -/

/-- **Mellit, the modified action**, `HJO.Sweep.exists_isDpaAction_mod`: there is an action
`ρ^♭` of `𝔸_q` on `V_*` with `ρ^♭(T_i) = T_i`, `ρ^♭(d_-) = d^♭_-` and `ρ^♭(d_+) = d^♭_+`.

The proof. The assignment of the generators of `HJO.Dyck.Aq` to the operators, and of
`𝟏_k` to the projection onto `V_k`, extends uniquely to a `𝕜`-algebra homomorphism from the path
algebra, since a path algebra is free on its arrows subject only to composability and composability
is respected; by `HJO.Sweep.IsDpaAction` it then suffices that the images of the generators of the
defining ideal vanish. Both halves are `HJO.Sweep.IsDpaOperators.exists_isDpaAction`, and the input
is `HJO.Sweep.isDpaOperators_mod`, which collects the nine relations.

`ρ^♭(T_i)`, `ρ^♭(d_-)` and `ρ^♭(d_+)` are the three operators below read on the summands they act
between — `HJO.Sweep.braid` at the shifted index `i + 1` of `HJO.Dyck.Aq`, `HJO.Sweep.dminus` and
`HJO.Sweep.dplus` — and `HJO.Sweep.coe_braidModPiece`, `HJO.Sweep.coe_dminusModPiece` and
`HJO.Sweep.coe_dplusModPiece` read them off.

`q ≠ 0` is carried, which the statement as usually given does not assume; see the note in the file
header. -/
@[hjo "lem_vmod_action_mod"]
theorem exists_isDpaAction_mod (q : L) (hq : q ≠ 0) :
    ∃ ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L), IsDpaAction q ρ
      ∧ (∀ k i : ℕ, ρ (Dyck.Aq.Tg L q k i) = loopVstar (braidModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dMinus L q k) = lowerVstar (dminusModPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = raiseVstar (dplusModPiece q) k) :=
  (isDpaOperators_mod q hq).exists_isDpaAction

end Mod

end HJO.Sweep

end
