/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.DminusSqBraid
public import HJO.CMStructure.DpaActionBuild
public import HJO.CMStructure.RelExtra
public import HJO.CarlssonMellit.ConjugationOperator
public meta import HJO.Attr

/-! # Carlsson and Mellit's operators satisfy the relations

`HJO.Sweep.exists_isDpaAction_cm`: for every `k ≥ 0` the operators `T_i` on `V_k`,
`d_+ : V_k → V_{k+1}` and `d_- : V_{k+1} → V_k` satisfy every relation listed in `HJO.Dyck.Aq`.

`HJO.Dyck.Aq` is a *presented* algebra — a `RingQuot` of the free algebra on the arrows of the
quiver — so "the operators satisfy every relation listed there" is exactly the statement that the
assignment of the generators to the operators descends to `𝔸_q`, which is what is proved below: an
algebra homomorphism `𝔸_q → End_𝕜(V_*)` in the sense of `HJO.Sweep.IsDpaAction`, sending the loops
to the `T_i`, the lowering arrow to `d_-` and the raising arrow to `d_+`. Nothing weaker would be
checkable, and nothing stronger is claimed: the eighteen relations are the eighteen constructors of
`HJO.Dyck.Rel`, and the homomorphism exists if and only if all of them hold.

The construction is `HJO.Sweep.IsDpaOperators.exists_isDpaAction`, shared with
`HJO.Sweep.exists_isDpaAction_mod`: the plumbing and the nine path-algebra relations are done once
there, and this file supplies Carlsson and Mellit's nine for the unstarred operators.

## Main results

* `HJO.Sweep.exists_isDpaAction_cm`.
* `HJO.Sweep.isDpaOperators_cm` — Carlsson and Mellit's nine relations for the unstarred operators,
  collected.

## Implementation notes

**The nine relations are nine lemmas proved earlier, in the order of `HJO.Dyck.Aq`.** The first line
of `HJO.Dyck.Aq` is `HJO.Sweep.braid_braid_apply`, `HJO.Sweep.braid_braid` and
`HJO.Sweep.braid_comm`, read on the summand by `HJO.Sweep.braidModPiece_quadratic` and its two
companions. The second is `HJO.Sweep.dminusCM_braid`, `HJO.Sweep.cmDPlus_braid`,
`HJO.Sweep.braid_one_cmDPlus_cmDPlus` and `HJO.Sweep.dminusCM_dminusCM_braid`. The third is
`HJO.Sweep.dminusCM_commutator_braid` and `HJO.Sweep.braid_one_commutator_cmDPlus`.

**Two of them read the `F ∈ V_k`, and the summand supplies it.**
`HJO.Sweep.braid_one_cmDPlus_cmDPlus` and `HJO.Sweep.dminusCM_dminusCM_braid` are false on the total
space `HJO.Sweep.Total`; here they are applied to the underlying element of a term of
`HJO.Sweep.pieceSub`, whose defining property is exactly that membership. This is why the action has
to be built on the direct sum `V_*` of `HJO.Sweep.Vstar`.

**No `q ≠ 0` and no `q ≠ 1`.** Every one of the nine unstarred relations is proved without a side
condition on `q`, so this statement carries none — unlike its modified twin
`HJO.Sweep.exists_isDpaAction_mod`, whose relations pass through
`HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus` and so read `q ≠ 0`.

**The remark that `y_1, …, y_k` act by multiplication is not part of this statement** and is
not proved here: it is `HJO.Dyck.Aq.yElt_one_eq_wordDown` and
`HJO.Sweep.braid_auxVar_succ_mul_braid` read on the action, and the statement belongs in a remark
after the proof rather than in a clause of it.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*,
§3.
-/

@[expose] public section

namespace HJO.Sweep

section CM

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The nine relations -/

/-- **Carlsson and Mellit's operators satisfy Carlsson and Mellit's nine relations.** Field by
field, the nine lemmas: the first family `HJO.Sweep.braid_braid_apply`, `HJO.Sweep.braid_braid` and
`HJO.Sweep.braid_comm`; the second `HJO.Sweep.dminusCM_braid` and
`HJO.Sweep.dminusCM_dminusCM_braid`; the third `HJO.Sweep.cmDPlus_braid` and
`HJO.Sweep.braid_one_cmDPlus_cmDPlus`; and the pair `HJO.Sweep.dminusCM_commutator_braid`,
`HJO.Sweep.braid_one_commutator_cmDPlus`. -/
theorem isDpaOperators_cm (q : L) :
    IsDpaOperators q (braidModPiece q) (dminusPiece q) (cmDPlusPiece q) where
  loop_eq_zero h := braidModPiece_of_le q h
  quadratic h F := braidModPiece_quadratic q h F
  braid h F := braidModPiece_braid q h F
  comm hi hj hij F := braidModPiece_comm q hi hj hij F
  loop_lower := by
    intro m i him F
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    refine Subtype.ext ?_
    simp only [coe_braidModPiece q him, coe_dminusPiece,
      coe_braidModPiece q (show i + 2 ≤ n + 2 + 1 from by omega)]
    exact (dminusCM_braid q (k := n + 1) (show i + 1 ≤ n + 1 from by omega) _).symm
  lower_sq := by
    intro m F
    refine Subtype.ext ?_
    simp only [coe_dminusPiece, coe_braidModPiece q (show m + 2 ≤ m + 2 from le_rfl)]
    exact dminusCM_dminusCM_braid q m F.2
  raise_loop := by
    intro k i hik F
    refine Subtype.ext ?_
    simp only [coe_cmDPlusPiece, coe_braidModPiece q hik,
      coe_braidModPiece q (show i + 1 + 2 ≤ k + 1 from by omega)]
    exact cmDPlus_braid q (by omega) (by omega) _
  raise_sq := by
    intro k F
    refine Subtype.ext ?_
    simp only [coe_braidModPiece q (show 0 + 2 ≤ k + 2 from by omega), coe_cmDPlusPiece]
    exact braid_one_cmDPlus_cmDPlus q F.2
  extra_lower := by
    intro j F
    refine Subtype.ext ?_
    simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, coe_dminusPiece, coe_cmDPlusPiece,
      coe_braidModPiece q (show j + 2 ≤ j + 2 from le_rfl), smul_eq_scal_mul]
    exact dminusCM_commutator_braid q j F.2
  extra_raise := by
    intro m F
    refine Subtype.ext ?_
    simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, coe_dminusPiece, coe_cmDPlusPiece,
      coe_braidModPiece q (show 0 + 2 ≤ m + 2 from by omega), smul_eq_scal_mul]
    exact braid_one_commutator_cmDPlus q m F.2

/-! ### The action -/

/-- **Carlsson--Mellit, the operators satisfy the relations**, `HJO.Sweep.exists_isDpaAction_cm`:
for every `k ≥ 0` the operators `T_i` on `V_k`, `d_+ : V_k → V_{k+1}` and `d_- : V_{k+1} → V_k`
satisfy every relation listed in `HJO.Dyck.Aq`.

`HJO.Dyck.Aq` being a presentation, that is the statement that the assignment of its generators to
those operators descends to an algebra homomorphism out of `𝔸_q`, and here it is one satisfying
`HJO.Sweep.IsDpaAction` as well: `ρ(𝟏_k)` is the projection onto `V_k`, `ρ` sends the loop `Tg k i`
— Carlsson and Mellit's `T_{i+1}` at the vertex `k` — to the Demazure--Lusztig operator there, the
lowering arrow to `d_-` of `HJO.Sweep.dminusCM` and the raising arrow to `d_+` of
`HJO.Sweep.cmDPlus`.

The proof. The assignment extends to the path algebra, composability being respected;
by `HJO.Sweep.IsDpaAction` it then suffices that the images of the generators of the defining ideal
vanish, and that is `HJO.Sweep.isDpaOperators_cm` — the nine relations — fed to
`HJO.Sweep.IsDpaOperators.exists_isDpaAction`, which also discharges the nine relations of the
path-algebra structure.

`HJO.Sweep.coe_braidModPiece`, `HJO.Sweep.coe_dminusPiece` and `HJO.Sweep.coe_cmDPlusPiece` read
the three operator families off as `HJO.Sweep.braid`, `HJO.Sweep.dminusCM` and
`HJO.Sweep.cmDPlus`. -/
@[hjo "lem_cm_replemma"]
theorem exists_isDpaAction_cm (q : L) :
    ∃ ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L), IsDpaAction q ρ
      ∧ (∀ k i : ℕ, ρ (Dyck.Aq.Tg L q k i) = loopVstar (braidModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dMinus L q k) = lowerVstar (dminusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = raiseVstar (cmDPlusPiece q) k) :=
  (isDpaOperators_cm q).exists_isDpaAction

end CM

end HJO.Sweep

end
