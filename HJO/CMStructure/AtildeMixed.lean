/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.AtildeCorner
public import HJO.CMStructure.StarZrelShift
public meta import HJO.Attr

/-! # The three mixed relations of `Ã`, for Carlsson and Mellit's operators

`HJO.Dyck.Tilde.Atilde` imposes three relations mixing the two raising arrows:
`z_{i+1}d_+ = d_+z_i`, `y_{i+1}d^*_+ = d^*_+y_i` and `z_1d_+ = -uq^{k+1}y_1d^*_+`. This file proves
all three for the operators, which with `HJO.Sweep.exists_action_atilde_of_mixed` gives the action
half of `HJO.Standing.exists_action_atilde_ker_eq_param`.

## Main results

* `HJO.Sweep.zOpVstar_ofPiece` — the starred corner element `z_i` of `HJO.Dyck.Tilde.Atilde`, read
  as an operator on `V_k`, is `q^{k-i}(q^{-1}-1)^{-1}T_{i↘1}(d^*_+d_--d_-d^*_+)T^*_{k↘1}T_{1↗i}`.
  This is the unwinding of the recursion `z_i = qT_i^{-1}z_{i+1}T_i^{-1}` that
  `HJO.Sweep.starCommCM_cmDPlus` describes in words and states its relation for.
* `HJO.Sweep.mixed_z_vstar`, `HJO.Sweep.mixed_y_vstar`, `HJO.Sweep.mixed_top_vstar` — the three
  mixed relations.
* `HJO.Sweep.exists_action_atilde` — **the action half of
  `HJO.Standing.exists_action_atilde_ker_eq_param`**: the operators `T_i`, `d_-`, `d_+`, `d^*_+` and
  the projections onto the summands define an action of `Ã` on `V_*`.

## Implementation notes

**The scalars are carried here and cancel only in two of the three relations.**
`HJO.Sweep.starCommCM_cmDPlus` and `HJO.Sweep.zopOneStar_dplus` are both stated with the common
prefactor of `z` removed. For the first mixed relation that is harmless — one `z` on each side, same
prefactor `q^{k-i}(q^{-1}-1)^{-1}` — and `HJO.Sweep.mixed_z_vstar` puts it back by linearity. For
the third it is not: `z_1d_+ = -uq^{k+1}y_1d^*_+` has one `z` and one `y`, and the identity is false
without the prefactor. `HJO.Sweep.mixed_top_vstar` is where the two are multiplied out:
`q^k(-q(q-1)^{-1})(q-1)u = -uq^{k+1}`, and `(q-1)^{-1}(q-1) = 1` is the only thing read of
`Invertible (q - 1)`.

**The three train identities are the whole of the unwinding.** `HJO.Dyck.Tilde.Atilde` writes `z_k`
with the *unstarred* descending word in front of the starred commutator — the substitution
`T_i ↦ T_i^{-1}` applied to `HJO.Dyck.Aq.yElt`'s `T̂_{k-1}⋯T̂_1` gives back `T_{k-1}⋯T_1`, which is
`HJO.Dyck.Tilde.tinvOf_tinvOf` — and the recursion conjugates by `T_i^{-1}`. So the closed form is
reached by three cancellations in the braid system of `HJO.Sweep.isBraidSystem_braidEnd`:
`T_i^{-1}T_{i+1↘1} = T_{i↘1}`, `T_{1↗i+1}T_i^{-1} = T_{1↗i}` and `T_{k↗1}T_{1↗k} = 1`, each an
instance of the gluing lemmas `HJO.Braid.trainDown_mul_trainDown` and
`HJO.Braid.trainUp_mul_trainUp`.

**What is proved elsewhere.** `HJO.Standing.exists_action_atilde_ker_eq_param` has a second
conclusion — that the kernel of `Ãe_0 → V_*` is `Ie_0` — which is
`HJO.Standing.atildeE0_inf_ker_evalOne_eq_param` and is not touched by this file. What is proved
here is the action half, which is what `HJO.Sweep.exists_isDpaAction_mellit` and
`HJO.Sweep.exists_isIntertwinedPair_vmod` read of it. The kernel half and the whole statement are
proved in `HJO/CMStructure/Thm73Closed.lean`, as `HJO.Sweep.atildeE0_inf_ker_evalOne_eq` and
`HJO.Sweep.exists_action_atilde_ker_eq`.

## References

E. Carlsson and A. Mellit,
*A proof of the shuffle conjecture*, §3 and §5, and A. Mellit, *Toric braids and
`(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### Three cancellations in the braid trains -/

section Trains

variable {L : Type*} [Field L] (q : L) (hq : q ≠ 0)

/-- The scalars of the base field pass the inverted braid operator, which is `Λ`-linear and not
`𝕜`-linear on the nose. -/
theorem braidInv_scal_mul_apply (i : ℕ) (x : L) (G : Total L) :
    braidInv q i (scal x * G) = scal x * braidInv q i G := by
  rw [braidInv_apply, braidInv_apply, braid_scal_mul]
  ring

include hq

/-- **A descending train grows by one letter**: `T_{n+2↘1} = T_{n+1}T_{n+1↘1}`. -/
theorem trainDownEnd_succ_apply (n : ℕ) (X : Total L) :
    braid q (n + 1) (trainDownEnd q (n + 1) 1 X) = trainDownEnd q (n + 2) 1 X := by
  have hglue := Braid.trainDown_mul_trainDown (isBraidSystem_braidEnd q hq (n + 2))
    (a := n + 2) (b := n + 1) (c := 1) (by omega) le_rfl (by omega) (by omega) le_rfl (by omega)
  rw [← trainDownEnd, ← trainDownEnd, ← trainDownEnd, trainDownEnd_succ_self q] at hglue
  have h := LinearMap.congr_fun hglue X
  rw [Module.End.mul_apply] at h
  simpa [braidEnd] using h

/-- **The first cancellation**: `T_i^{-1}T_{i+1↘1} = T_{i↘1}`, which is how the recursion
`z_i = qT_i^{-1}z_{i+1}T_i^{-1}` shortens the descending train in front of the commutator. -/
theorem braidInv_trainDownEnd {i : ℕ} (hi : 1 ≤ i) (X : Total L) :
    braidInv q i (trainDownEnd q (i + 1) 1 X) = trainDownEnd q i 1 X := by
  have hglue := Braid.trainDown_mul_trainDown (isBraidSystem_braidEnd q hq (i + 1))
    (a := i) (b := i + 1) (c := 1) hi (by omega) (by omega) le_rfl (by omega) (by omega)
  rw [← trainDownEnd, ← trainDownEnd, ← trainDownEnd,
    show trainDownEnd q i (i + 1) = braidInvEnd q i from Braid.trainDown_self_succ _ _ i] at hglue
  have h := LinearMap.congr_fun hglue X
  rw [Module.End.mul_apply] at h
  simpa [braidInvEnd] using h

/-- **The second cancellation**: `T_{1↗i+1}T_i^{-1} = T_{1↗i}`, the other half of the same
conjugation. -/
theorem trainUpEnd_one_braidInv {i : ℕ} (hi : 1 ≤ i) (X : Total L) :
    trainUpEnd q 1 (i + 1) (braidInv q i X) = trainUpEnd q 1 i X := by
  have hglue := Braid.trainUp_mul_trainUp (isBraidSystem_braidEnd q hq (i + 1))
    (a := 1) (b := i + 1) (c := i) (by omega) (by omega) (by omega) le_rfl hi (by omega)
  rw [← trainUpEnd, ← trainUpEnd, ← trainUpEnd,
    show trainUpEnd q (i + 1) i = braidInvEnd q i from Braid.trainUp_succ_self _ _ i] at hglue
  have h := LinearMap.congr_fun hglue X
  rw [Module.End.mul_apply] at h
  simpa [braidInvEnd] using h

/-- **The third cancellation**: `T_{k↗1}T_{1↗k} = 1`, which is what makes the two trains of
`HJO.Sweep.zOpVstar_ofPiece` a conjugation and collapses at the top index `i = k`. -/
theorem trainUpEnd_trainUpEnd_one {k : ℕ} (hk : 1 ≤ k) (X : Total L) :
    trainUpEnd q k 1 (trainUpEnd q 1 k X) = X := by
  have hglue := Braid.trainUp_mul_trainUp_self (isBraidSystem_braidEnd q hq k)
    (a := k) (b := 1) hk le_rfl le_rfl hk
  rw [← trainUpEnd, ← trainUpEnd] at hglue
  have h := LinearMap.congr_fun hglue X
  rw [Module.End.mul_apply, Module.End.one_apply] at h
  exact h

end Trains

/-! ### The starred corner family, in closed form -/

section ZOp

variable {L : Type*} [Field L] [Algebra ℚ L] (q u : L) [Invertible q] [Invertible (q - 1)]

omit [Algebra ℚ L] [Invertible (q - 1)] in
/-- **The substituted word of loops is the unstarred descending train.** `HJO.Dyck.Tilde.Atilde`
builds `z_k` from `HJO.Dyck.Aq.yElt`'s `T̂_{k-1}⋯T̂_1` read in the starred generators, and the
substitution is an involution on the loops (`HJO.Dyck.Tilde.tinvOf_tinvOf`), so what stands there is
the unstarred train `T_{k-1}⋯T_1` of `HJO.Braid.trainDown`. -/
theorem tinvWordOf_star_ofPiece {k : ℕ} :
    ∀ (n : ℕ), n + 1 ≤ k → ∀ X : pieceSub L k, ∃ Y : pieceSub L k,
      Dyck.tinvWordOf (⅟q) q (pieceProj L) (tinvVstar q) k n (ofPiece L k X) = ofPiece L k Y
        ∧ (Y : Total L) = trainDownEnd q (n + 1) 1 (X : Total L) := by
  have hq : q ≠ 0 := Invertible.ne_zero q
  intro n
  induction n with
  | zero =>
    intro _ X
    refine ⟨X, ?_, ?_⟩
    · rw [Dyck.tinvWordOf, pieceProj_ofPiece]
    · rw [trainDownEnd, Braid.trainDown_self, Module.End.one_apply]
  | succ n ih =>
    intro hn X
    obtain ⟨Y, hY1, hY2⟩ := ih (by omega) X
    refine ⟨braidModPiece q k n Y, ?_, ?_⟩
    · rw [Dyck.tinvWordOf, Module.End.mul_apply, hY1,
        show Dyck.tinvOf (⅟q) q (tinvVstar q k n) (pieceProj L k)
          = loopVstar (braidModPiece q) k n from
          Dyck.Tilde.tinvOf_tinvOf (loopVstar (braidModPiece q) k n) (pieceProj L k),
        loopVstar_ofPiece]
    · rw [coe_braidModPiece q (show n + 2 ≤ k from by omega), hY2,
        trainDownEnd_succ_apply q hq]

/-- **The top starred corner element**, read on the summand: `HJO.Dyck.Tilde.Atilde`'s formula for
`z_k` at Carlsson and Mellit's operators is `(q^{-1}-1)^{-1}T_{k↘1}(d^*_+d_--d_-d^*_+)` on `V_k`,
with `(q^{-1}-1)^{-1} = -q(q-1)^{-1}` the substituted scalar. -/
theorem zOpVstar_self_ofPiece (m : ℕ) (F : pieceSub L (m + 1)) :
    ∃ G : pieceSub L (m + 1),
      zOpVstar q u (m + 1) (m + 1) (ofPiece L (m + 1) F) = ofPiece L (m + 1) G
        ∧ (G : Total L) = scal (-(q * ⅟(q - 1)))
            * trainDownEnd q (m + 1) 1 (starCommCM q u (m + 1) (F : Total L)) := by
  set X : pieceSub L (m + 1) := dplusStarPiece q u m (dminusPiece q m F)
    - dminusPiece q (m + 1) (dplusStarPiece q u (m + 1) F) with hX
  have hXcoe : (X : Total L) = starCommCM q u (m + 1) (F : Total L) := by
    rw [hX, starCommCM_succ_apply]
    simp only [AddSubgroupClass.coe_sub, coe_dplusStarPiece, coe_dminusPiece]
  obtain ⟨Y, hY1, hY2⟩ := tinvWordOf_star_ofPiece q m le_rfl X
  refine ⟨(-(q * ⅟(q - 1))) • Y, ?_, ?_⟩
  · rw [zOpVstar, Dyck.cornerOf, Nat.sub_self, Dyck.cornerAux, LinearMap.smul_apply,
      Module.End.mul_apply, Module.End.mul_apply, pieceProj_ofPiece,
      show Dyck.commOf (raiseVstar (dplusStarPiece q u)) (lowerVstar (dminusPiece q)) (m + 1 - 1)
        = deltaVstar (dminusPiece q) (dplusStarPiece q u) m from rfl,
      deltaVstar_ofPiece, ← hX]
    rw [Nat.add_sub_cancel, hY1, ← map_smul]
  · rw [SetLike.val_smul, smul_eq_scal_mul, hY2, hXcoe]

/-- **The starred corner family in closed form**, read on the summand: for `1 ≤ i ≤ k`,

`z_i = q^{k-i}(q^{-1}-1)^{-1} T_{i↘1}(d^*_+d_--d_-d^*_+)T^*_{k↘1}T_{1↗i}` on `V_k`,

which is the operator `HJO.Sweep.starCommCM_cmDPlus` and `HJO.Sweep.zopOneStar_dplus` state their
relations for, with the prefactor they leave off put back. `T^*_{k↘1}` is `T_{k↗1}` by
`HJO.Braid.trainUp_inv_eq_trainDown`, which is what `HJO.Sweep.trainUpEnd` writes. -/
theorem zOpVstar_ofPiece {k : ℕ} :
    ∀ (d i : ℕ), i + d = k → 1 ≤ i → ∀ F : pieceSub L k, ∃ G : pieceSub L k,
      zOpVstar q u k i (ofPiece L k F) = ofPiece L k G
        ∧ (G : Total L) = scal (q ^ d * -(q * ⅟(q - 1))) * trainDownEnd q i 1 (starCommCM q u k
            (trainUpEnd q k 1 (trainUpEnd q 1 i (F : Total L)))) := by
  have hq : q ≠ 0 := Invertible.ne_zero q
  intro d
  induction d with
  | zero =>
    intro i hik h1 F
    obtain rfl : i = k := by omega
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    obtain ⟨G, hG1, hG2⟩ := zOpVstar_self_ofPiece q u m F
    refine ⟨G, hG1, ?_⟩
    rw [hG2, pow_zero, one_mul, trainUpEnd_trainUpEnd_one q hq (show 1 ≤ m + 1 from by omega)]
  | succ d ih =>
    intro i hik h1 F
    have hlt : i < k := by omega
    have hik' : i - 1 + 2 ≤ k := by omega
    set F' : pieceSub L k := braidInvModPiece q k (i - 1) F with hF'
    have hF'coe : (F' : Total L) = braidInv q i (F : Total L) := by
      have h := coe_braidInvModPiece q hik' F
      rwa [show i - 1 + 1 = i from by omega] at h
    obtain ⟨G, hG1, hG2⟩ := ih (i + 1) (by omega) (by omega) F'
    have htinv : tinvVstar q k (i - 1) = loopVstar (braidInvModPiece q) k (i - 1) :=
      tinvVstar_eq_loopVstar q hik'
    have hrec : zOpVstar q u k i
        = q • (tinvVstar q k (i - 1) * zOpVstar q u k (i + 1) * tinvVstar q k (i - 1)) := by
      rw [zOpVstar, zOpVstar, Dyck.cornerOf, Dyck.cornerOf,
        show k - i = (k - (i + 1)) + 1 from by omega, Dyck.cornerAux,
        show k - (k - (i + 1)) - 2 = i - 1 from by omega]
    refine ⟨q • braidInvModPiece q k (i - 1) G, ?_, ?_⟩
    · rw [hrec, LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply, htinv,
        loopVstar_ofPiece, ← hF', hG1, loopVstar_ofPiece, ← map_smul]
    · rw [SetLike.val_smul, smul_eq_scal_mul, coe_braidInvModPiece q hik',
        show i - 1 + 1 = i from by omega, hG2, braidInv_scal_mul_apply q,
        braidInv_trainDownEnd q hq h1, hF'coe, trainUpEnd_one_braidInv q hq h1,
        show q ^ (d + 1) * -(q * ⅟(q - 1)) = q * (q ^ d * -(q * ⅟(q - 1))) from by ring]
      simp only [scal_mul]
      ring

end ZOp

/-! ### The three mixed relations -/

section Mixed

variable {L : Type*} [Field L] [Algebra ℚ L] (q u : L) [Invertible q] [Invertible (q - 1)]

/-- **The first mixed relation** of `HJO.Dyck.Tilde.Atilde`, `z_{i+1}d_+ = d_+z_i`, for the
operators: `HJO.Sweep.starCommCM_cmDPlus` with the prefactor of `z` put back. The two sides carry
the same prefactor `q^{k-i}(q^{-1}-1)^{-1}`, so putting it back is linearity. -/
theorem mixed_z_vstar {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    zOpVstar q u (k + 1) (i + 1) * raiseVstar (cmDPlusPiece q) k
      = raiseVstar (cmDPlusPiece q) k * zOpVstar q u k i := by
  have hq : q ≠ 0 := Invertible.ne_zero q
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne k l with rfl | hl
  · obtain ⟨G, hG1, hG2⟩ := zOpVstar_ofPiece q u (k - i) i (by omega) h1 F
    obtain ⟨G', hG1', hG2'⟩ := zOpVstar_ofPiece q u (k - i) (i + 1) (by omega) (by omega)
      (cmDPlusPiece q k F)
    rw [raiseVstar_ofPiece, hG1', hG1, raiseVstar_ofPiece]
    refine ofPiece_congr ?_
    rw [hG2', coe_cmDPlusPiece, coe_cmDPlusPiece, hG2, cmDPlus_scal_mul,
      trainDown_starCommCM_trainUp_cmDPlus q u hq h1 hik F.2]
  · rw [raiseVstar_ofPiece_of_ne (Ne.symm hl), map_zero, zOpVstar, Dyck.cornerOf,
      cornerAux_apply_eq_zero (Ne.symm hl)
        (fun j => tinvVstar_apply_ofPiece_of_ne q (Ne.symm hl) j F) (k - i),
      map_zero]

/-- **The second mixed relation** of `HJO.Dyck.Tilde.Atilde`, `y_{i+1}d^*_+ = d^*_+y_i`, for the
operators: the unstarred corner family being multiplication by the variable
(`HJO.Sweep.yOpVstar_eq_loopVstar`), this is the third clause of `HJO.Sweep.dplusStar_braidInv` —
the cyclic shift inside `d^*_+` raising the index of the variable. -/
theorem mixed_y_vstar {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    yOpVstar q (k + 1) (i + 1) * raiseVstar (dplusStarPiece q u) k
      = raiseVstar (dplusStarPiece q u) k * yOpVstar q k i := by
  rw [yOpVstar_eq_loopVstar q (by omega) (show i + 1 ≤ k + 1 from by omega),
    yOpVstar_eq_loopVstar q h1 hik]
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne k l with rfl | hl
  · rw [raiseVstar_ofPiece, loopVstar_ofPiece, loopVstar_ofPiece, raiseVstar_ofPiece]
    refine ofPiece_congr ?_
    rw [coe_auxMulPiece (by omega) (show i + 1 ≤ k + 1 from by omega), coe_dplusStarPiece,
      coe_dplusStarPiece, coe_auxMulPiece h1 hik]
    exact (dplusStar_auxVar_mul q u h1 hik (F : Total L)).symm
  · rw [raiseVstar_ofPiece_of_ne (Ne.symm hl), map_zero,
      loopVstar_ofPiece_of_ne i (Ne.symm hl), map_zero]

/-- **The third mixed relation** of `HJO.Dyck.Tilde.Atilde`, `z_1d_+ = -uq^{k+1}y_1d^*_+`, for the
operators: `HJO.Sweep.zopOneStar_dplus` in its all-Carlsson--Mellit reading, with both prefactors
put back. Here they do not cancel — one side carries `z` and the other `y` — and the scalar identity
`q^k(-q(q-1)^{-1})(q-1)u = -uq^{k+1}` is the content of putting them back. -/
theorem mixed_top_vstar (k : ℕ) :
    zOpVstar q u (k + 1) 1 * raiseVstar (cmDPlusPiece q) k
      = (-(u * q ^ (k + 1)) : L) • (yOpVstar q (k + 1) 1 * raiseVstar (dplusStarPiece q u) k) := by
  have hq : q ≠ 0 := Invertible.ne_zero q
  have hscal : q ^ k * -(q * ⅟(q - 1)) * ((q - 1) * u) = -(u * q ^ (k + 1)) := by
    have hinv : ⅟(q - 1) * (q - 1) = 1 := invOf_mul_self (q - 1)
    linear_combination (-(q ^ k * q * u)) * hinv
  rw [yOpVstar_eq_loopVstar q (le_refl 1) (show 1 ≤ k + 1 from by omega)]
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply]
  rcases eq_or_ne k l with rfl | hl
  · obtain ⟨G, hG1, hG2⟩ := zOpVstar_ofPiece q u k 1 (by omega) (le_refl 1) (cmDPlusPiece q k F)
    rw [raiseVstar_ofPiece, hG1, raiseVstar_ofPiece, loopVstar_ofPiece, ← map_smul]
    refine ofPiece_congr ?_
    rw [hG2, SetLike.val_smul, smul_eq_scal_mul, coe_auxMulPiece (le_refl 1) (by omega),
      coe_dplusStarPiece, coe_cmDPlusPiece,
      show trainDownEnd q 1 1 = 1 from Braid.trainDown_self _ _ 1, Module.End.one_apply,
      show trainUpEnd q 1 1 = 1 from Braid.trainUp_self _ _ 1, Module.End.one_apply,
      starCommCM_succ_apply, starCommCM_trainUpEnd_star_cmDPlus q u hq F.2, ← mul_assoc,
      ← mul_assoc, ← scal_mul, hscal, mul_assoc]
  · rw [raiseVstar_ofPiece_of_ne (Ne.symm hl), map_zero,
      raiseVstar_ofPiece_of_ne (Ne.symm hl), map_zero, smul_zero]

/-! ### The action -/

/-- **The action half of `HJO.Standing.exists_action_atilde_ker_eq_param`**: the operators `T_i` of
`HJO.Sweep.braid`, `d_-` of `HJO.Sweep.dminusCM`, `d_+` of `HJO.Sweep.cmDPlus`, `d^*_+` of
`HJO.Sweep.dplusStar` and the projections onto the summands define an action of the extended Dyck
path algebra `Ã` of `HJO.Dyck.Tilde.Atilde` on `V_*`.

`HJO.Dyck.Tilde.Atilde` being a presentation, "the operators define an action" is the statement that
the assignment of its generators to them descends to an algebra homomorphism out of `Ã`, and
that is
`HJO.Sweep.exists_action_atilde_of_mixed` — the unstarred group of relations from
`HJO.Sweep.exists_isDpaAction_cm`, the starred group from the action half of
`HJO.Sweep.exists_isDpaAction_star`, and the three mixed relations from the three lemmas above.

**This is not the whole statement.** `HJO.Standing.exists_action_atilde_ker_eq_param` also asserts
that the kernel of `Ãe_0 → V_*` is `Ie_0`, which is
`HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`; that half is proved in
`HJO/CMStructure/Thm73Closed.lean` (`HJO.Sweep.atildeE0_inf_ker_evalOne_eq`), and the whole
statement there is `HJO.Sweep.exists_action_atilde_ker_eq`. The action half is what
`HJO.Sweep.exists_isDpaAction_mellit` and `HJO.Sweep.exists_isIntertwinedPair_vmod` read of it.

`q ≠ 0` and `q ≠ 1` are carried by `HJO.Dyck.Tilde.Atilde` itself, as `Invertible q` and
`Invertible (q - 1)`: its corner elements divide by `q` and by `q - 1`. `q + 1 ≠ 0` is inherited
from `HJO.Sweep.exists_isDpaAction_star`, which inherits it from
`HJO.Sweep.dminusCM_starCommCM_braidInv`. Every use instantiates it at parameters algebraically
independent over `ℤ`, where all three hold. -/
@[hjo "lem_cm_thm73_action"]
theorem exists_action_atilde (hq1 : q + 1 ≠ 0) :
    ∃ ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L),
      (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
      ∧ (∀ k i : ℕ, ρ (Dyck.Tilde.Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlusStar L q u k)
          = raiseVstar (dplusStarPiece q u) k) :=
  exists_action_atilde_of_mixed q u hq1 (fun _ _ h1 hik => mixed_z_vstar q u h1 hik)
    (fun _ _ h1 hik => mixed_y_vstar q u h1 hik) (mixed_top_vstar q u)

end Mixed

end HJO.Sweep

end
