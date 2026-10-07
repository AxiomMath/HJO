/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.AtildeBuild
public import HJO.CMStructure.VmodYMultiplication
public meta import HJO.Attr

/-! # The corner elements of `Ã`, read as operators on `V_*`

`HJO.Dyck.Tilde.Atilde` writes its two corner families by the same two formulas of
`HJO.Dyck.Aq.yElt` — `y_k = (q-1)^{-1}T̂_{k-1}⋯T̂_1(d₊d₋-d₋d₊)` and `y_i = q^{-1}T_iy_{i+1}T_i`, the
second read in the starred generators for `z_i`. This file computes what those formulas are once the
generators are Carlsson and Mellit's operators: the unstarred family is multiplication by the
variable, and the starred family is the starred commutator conjugated by two braid trains, which is
the shape `HJO.Sweep.starCommCM_cmDPlus` and `HJO.Sweep.zopOneStar_dplus` are stated in.

## Main results

* `HJO.Sweep.cornerAux_apply_eq_zero` — either corner family kills every summand but the one its
  vertex names.
* `HJO.Sweep.tinvWordOf_ofPiece` — the word of inverted loops undoes the ascending word
  `T_{[1,n]}` of `HJO.Sweep.cmAscWord`: the one cancellation that turns `HJO.Dyck.Aq.yElt`'s
  prefactor into the identity.
* `HJO.Sweep.yOpVstar_eq_loopVstar` — the unstarred corner family is multiplication by `y_i`. This
  is `HJO.Sweep.map_yElt_eq_auxMulPiece` for Carlsson and Mellit's own operators, and it is proved
  directly from `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` rather than through an action: no
  injectivity of `T_{1↑k}` is needed, because the prefactor `T̂_{k-1}⋯T̂_1` cancels the word the
  commutator produces letter by letter.
(The starred corner family is computed in `HJO.CMStructure.AtildeMixed`, where the trains it
is written with are available.)

## Implementation notes

**The unstarred family needs no action and no injectivity.** `HJO.Sweep.map_yElt_eq_auxMulPiece`
proves the corresponding statement for the modified operators by comparing `ρ^♭(y_k)` with
`HJO.Sweep.dplus_dminus_sub_dminus_dplus` and cancelling the word `T_{1↑k}` through
`HJO.Sweep.cmAscWord_one_injective`. Here the word is cancelled by the prefactor of
`HJO.Dyck.Aq.yElt` itself: the formula for `y_k` carries `T̂_{k-1}⋯T̂_1` in front of the commutator,
and `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` produces exactly `T_{[1,k-1]}`, so
`HJO.Sweep.tinvWordOf_ofPiece` finishes with `T̂_jT_j = 1`. That is why this file does not read
`HJO.Sweep.exists_isDpaAction_cm` at all, only the commutator.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §3 and §5. All of it serves the
action half of `HJO.Standing.exists_action_atilde_ker_eq_param`. -/

@[expose] public section

namespace HJO.Sweep

/-! ### A corner family kills every other summand -/

section Vanish

variable {L : Type*} [CommRing L]

/-- **A corner family kills every summand but the one its vertex names.** Both families of
`HJO.Dyck.Tilde.Atilde` are built from `HJO.Dyck.cornerAux`, whose innermost factor is the
idempotent at the vertex `k` and whose recursion multiplies by a loop there on the right; either
kills `V_l` for `l ≠ k`. -/
theorem cornerAux_apply_eq_zero {qq qi di : L}
    {U : ∀ k : ℕ, pieceSub L k →ₗ[L] pieceSub L (k + 1)}
    {D : ∀ k : ℕ, pieceSub L (k + 1) →ₗ[L] pieceSub L k}
    {T : ℕ → ℕ → Module.End L (Vstar L)} {k l : ℕ} (hl : l ≠ k) {F : pieceSub L l}
    (hT : ∀ i : ℕ, T k i (ofPiece L l F) = 0) :
    ∀ j : ℕ, Dyck.cornerAux qq qi di (pieceProj L) (raiseVstar U) (lowerVstar D) T k j
      (ofPiece L l F) = 0 := by
  intro j
  induction j with
  | zero =>
    rw [Dyck.cornerAux, LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply,
      pieceProj_ofPiece_of_ne hl, map_zero, map_zero, smul_zero]
  | succ j ih =>
    rw [Dyck.cornerAux, LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply, hT,
      map_zero, map_zero, smul_zero]

end Vanish

/-! ### The word of inverted loops undoes the ascending word -/

section Tinv

variable {L : Type*} [Field L] [Algebra ℚ L] (q : L) [Invertible q]

omit [Algebra ℚ L] in
/-- **The word of inverted loops undoes the ascending word.** `HJO.Dyck.Aq.yElt` puts
`T̂_{k-1}⋯T̂_1` in front of the commutator and `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`
produces `T_{[1,k-1]}`; this is the cancellation of the two, letter by letter, on `V_k`. -/
theorem tinvWordOf_ofPiece {k : ℕ} :
    ∀ (n : ℕ), n + 1 ≤ k → ∀ X Y : pieceSub L k, (Y : Total L) = cmAscWord q 1 n (X : Total L) →
      Dyck.tinvWordOf q ⅟q (pieceProj L) (loopVstar (braidModPiece q)) k n (ofPiece L k Y)
        = ofPiece L k X := by
  have hq : q ≠ 0 := Invertible.ne_zero q
  intro n
  induction n with
  | zero =>
    intro _ X Y hXY
    rw [Dyck.tinvWordOf, pieceProj_ofPiece]
    refine ofPiece_congr ?_
    rw [hXY, cmAscWord_self_pred q 0, Module.End.one_apply]
  | succ n ih =>
    intro hn X Y hXY
    have hmem : braid q (n + 1) (X : Total L) ∈ piece L k :=
      braid_mem_piece q (by omega) (by omega) X.2
    set X' : pieceSub L k := ⟨braid q (n + 1) (X : Total L), hmem⟩ with hX'
    have hstep : Dyck.tinvWordOf q ⅟q (pieceProj L) (loopVstar (braidModPiece q)) k n
        (ofPiece L k Y) = ofPiece L k X' := by
      refine ih (by omega) X' Y ?_
      rw [hXY, hX', cmAscWord_one_succ_apply]
    rw [Dyck.tinvWordOf, Module.End.mul_apply, hstep,
      show Dyck.tinvOf q ⅟q (loopVstar (braidModPiece q) k n) (pieceProj L k)
        = tinvVstar q k n from rfl, tinvVstar_eq_loopVstar q (show n + 2 ≤ k from by omega),
      loopVstar_ofPiece]
    refine ofPiece_congr ?_
    rw [coe_braidInvModPiece q (show n + 2 ≤ k from by omega), hX', braidInv_braid q hq]

end Tinv

/-! ### The unstarred corner family is multiplication by the variable -/

section YMul

variable {L : Type*} [Field L] [Algebra ℚ L] (q : L) [Invertible q] [Invertible (q - 1)]

/-- **The top unstarred corner element is multiplication by the top variable**, read on the summand:
`HJO.Dyck.Aq.yElt`'s formula for `y_k` at Carlsson and Mellit's operators.
`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` computes the commutator as
`(q-1)T_{[1,k-1]}(y_kF)` and the prefactor `T̂_{k-1}⋯T̂_1` of the formula cancels the word. -/
theorem yOpVstar_self_ofPiece (m : ℕ) (F : pieceSub L (m + 1)) :
    yOpVstar q (m + 1) (m + 1) (ofPiece L (m + 1) F)
      = ofPiece L (m + 1) (auxMulPiece L (m + 1) (m + 1) F) := by
  set X : pieceSub L (m + 1) := (q - 1) • auxMulPiece L (m + 1) (m + 1) F with hX
  set Y : pieceSub L (m + 1) :=
    cmDPlusPiece q m (dminusPiece q m F) - dminusPiece q (m + 1) (cmDPlusPiece q (m + 1) F) with hY
  have hXcoe : (X : Total L) = scal (q - 1) * ((auxVar (m + 1) : Total L) * F) := by
    rw [hX, SetLike.val_smul, coe_auxMulPiece (by omega) le_rfl, smul_eq_scal_mul]
  have hYX : (Y : Total L) = cmAscWord q 1 m (X : Total L) := by
    have h := dminusCM_cmDPlus_sub_cmDPlus_dminusCM q m F.2
    rw [hY, hXcoe, cmAscWord_scal_mul,
      show (scal (q - 1) : Total L) = -scal (1 - q) from by rw [← scal_neg, neg_sub]]
    simp only [AddSubgroupClass.coe_sub, coe_cmDPlusPiece, coe_dminusPiece]
    linear_combination -h
  have hword : Dyck.tinvWordOf q ⅟q (pieceProj L) (loopVstar (braidModPiece q)) (m + 1) m
      (ofPiece L (m + 1) Y) = ofPiece L (m + 1) X := tinvWordOf_ofPiece q m le_rfl X Y hYX
  rw [yOpVstar, Dyck.cornerOf, Nat.sub_self, Dyck.cornerAux, LinearMap.smul_apply,
    Module.End.mul_apply, Module.End.mul_apply, pieceProj_ofPiece,
    show Dyck.commOf (raiseVstar (cmDPlusPiece q)) (lowerVstar (dminusPiece q)) (m + 1 - 1)
      = deltaVstar (dminusPiece q) (cmDPlusPiece q) m from rfl,
    deltaVstar_ofPiece, ← hY]
  rw [Nat.add_sub_cancel, hword, hX, map_smul, smul_smul, invOf_mul_self, one_smul]

/-- **The unstarred corner family is multiplication by the variable**, read on the summand: the
downward recursion `y_i = q^{-1}T_iy_{i+1}T_i` of `HJO.Dyck.Aq.yElt` carries the top case down
through `HJO.Sweep.braid_auxVar_succ_mul_braid`. -/
theorem yOpVstar_ofPiece {k : ℕ} :
    ∀ (d i : ℕ), i + d = k → 1 ≤ i → ∀ F : pieceSub L k,
      yOpVstar q k i (ofPiece L k F) = ofPiece L k (auxMulPiece L k i F) := by
  intro d
  induction d with
  | zero =>
    intro i hik h1 F
    obtain rfl : i = k := by omega
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    exact yOpVstar_self_ofPiece q m F
  | succ d ih =>
    intro i hik h1 F
    have hlt : i < k := by omega
    have hik' : i - 1 + 2 ≤ k := by omega
    set F' : pieceSub L k := braidModPiece q k (i - 1) F with hF'
    have hF'coe : (F' : Total L) = braid q i (F : Total L) := by
      have h := coe_braidModPiece q hik' F
      rwa [show i - 1 + 1 = i from by omega] at h
    have hstep : yOpVstar q k (i + 1) (ofPiece L k F') = ofPiece L k (auxMulPiece L k (i + 1) F') :=
      ih (i + 1) (by omega) (by omega) F'
    have hrec : yOpVstar q k i
        = ⅟q • (loopVstar (braidModPiece q) k (i - 1) * yOpVstar q k (i + 1)
            * loopVstar (braidModPiece q) k (i - 1)) := by
      rw [yOpVstar, yOpVstar, Dyck.cornerOf, Dyck.cornerOf,
        show k - i = (k - (i + 1)) + 1 from by omega, Dyck.cornerAux,
        show k - (k - (i + 1)) - 2 = i - 1 from by omega]
    rw [hrec, LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply,
      show loopVstar (braidModPiece q) k (i - 1) (ofPiece L k F) = ofPiece L k F' from
        loopVstar_ofPiece k (i - 1) F, hstep, loopVstar_ofPiece, ← map_smul]
    refine ofPiece_congr ?_
    rw [SetLike.val_smul, coe_braidModPiece q hik', show i - 1 + 1 = i from by omega,
      coe_auxMulPiece (by omega) (by omega), hF'coe, braid_auxVar_succ_mul_braid q h1,
      coe_auxMulPiece h1 (by omega), ← smul_eq_scal_mul, smul_mul_assoc, smul_smul,
      invOf_mul_self, one_smul]

/-- **The unstarred corner family is multiplication by the variable**: for `1 ≤ i ≤ k` the operator
`HJO.Dyck.Aq.yElt`'s `y_i` becomes on `V_*` is multiplication by `y_i` on `V_k` and `0` on every
other summand. This is `HJO.Sweep.map_yElt_eq_auxMulPiece` for Carlsson and Mellit's own
operators. -/
theorem yOpVstar_eq_loopVstar {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    yOpVstar q k i = loopVstar (auxMulPiece L) k i := by
  refine vstar_ext fun l F => ?_
  rcases eq_or_ne l k with rfl | hl
  · rw [loopVstar_ofPiece]
    exact yOpVstar_ofPiece q (l - i) i (by omega) h1 F
  · rw [loopVstar_ofPiece_of_ne i hl, yOpVstar, Dyck.cornerOf]
    exact cornerAux_apply_eq_zero hl (fun j => loopVstar_ofPiece_of_ne j hl F) (k - i)

end YMul

end HJO.Sweep

end
