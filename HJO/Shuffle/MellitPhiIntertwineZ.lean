/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.StarZrelShift
public import HJO.CMStructure.ZyMixed
public meta import HJO.Attr

/-! # The `z` letter of the index-raising diagram, reduced to a commutator identity

`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` says that `π_{k+1}(φ*₊(B))` and `π_k(B)`
are intertwined by the vertical arrow `-y_1d^*_+`. Its proof checks that on the four letters of
`HJO.Braid.braidGenT`; three of them are relations between `d^*_+` and a multiplication operator and
are discharged elsewhere, and the fourth is the `z` letter,

`z_2^{(k+1)}·(y_1d^*_+) = (y_1d^*_+)·z_1^{(k)}`,

the sign of the arrow cancelling. This file takes that clause apart. It strips the multiplication
operator, then the two braid trains of `HJO.Sweep.zop`, and leaves a single identity between `d^*_+`
and the commutator `[d^*_+, d^♭_-]` of `HJO.Sweep.starComm`, with no `y`, no train and no braid
monoid in it:

`q·[d^*_+,d^♭_-]_{k+1}·d^*_+ = T_1·d^*_+·[d^*_+,d^♭_-]_k`.

Every statement here is an implication *towards* the clause, and the clause is not proved here
(it is `HJO.Sweep.zRep_two_comp_negYOneDPlusStarPiece`, by another route); see "What this
reduction says about the `z` clause".

## Main results

* `HJO.Sweep.zop_two_mul_mulLeft_auxVar_one` — `z_2y_1 = y_1T_1^{-1}z_1T_1` on `V_k` for `k ≥ 2`.
  This is the whole of the `y`-side bookkeeping: the mixed relation of `HJO.Braid.BraidMonoid` and
  the `y`-recursion, and it is what removes multiplication by `y_1` from the clause.
* `HJO.Sweep.zop_two_mul_mulLeft_dplusStar` — the clause follows from
  `z_1^{(k+1)}T_1d^*_+ = T_1d^*_+z_1^{(k)}`, which carries no `y_1`.
* `HJO.Sweep.dplusStar_mul_trainUpEnd_one` — `d^*_+T^*_{k↘1} = T^*_{k+1↘2}d^*_+`: the starred arrow
  conjugates Mellit's train up by one index. This is the train half of the reduction.
* `HJO.Sweep.zopOneStar_braidEnd_dplusStar_of_starComm` — and with that, the clause follows from the
  commutator identity displayed above.

## What this reduction says about the `z` clause

The commutator identity is *equivalent* to the clause, not merely sufficient for it: multiplication
by `y_1` is injective and the trains are invertible, so every step above is reversible. And the
commutator identity is in turn equivalent to `[z_1, z_2]d^♭_+ = 0`: read
`HJO.Sweep.zopOneStar_dplus` to replace `y_1d^*_+` by `(uq^{k+1})^{-1}z_1d^♭_+`, and
`HJO.Sweep.starCommCM_cmDPlus` to move `d^♭_+` past `z_1`, and the two sides of the clause become
`z_2z_1d^♭_+` and `z_1z_2d^♭_+`.

That is the same statement whose *unrestricted* form `z_1z_2 = z_2z_1` on the total space is
refuted at rank `2` (`HJO.Sweep.zop_two_not_comm`, in `HJO/CMStructure/BraidRepNotTotal.lean`).
The clause here asks for it only on the image of `d^♭_+`, so the refutation does not settle it;
but the two questions are the same piece of mathematics, and the `z` letter of
`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` — although it looks like the two
`y`-relations — is the hardest of its inputs, not a fourth routine one. It is discharged in
`HJO/Shuffle/MellitPhiIntertwinePiece.lean` through the Mellit-convention action of the Dyck path
algebra rather than through the identity above.

## Why nothing here mentions `π_k`

The vertical arrow `-y_1d^*_+` is `HJO.Sweep.negYOneDPlusStar` and the clause is that file's
`HJO.Sweep.PhiIntertwineZ`, phrased through `HJO.Sweep.zRep`. Neither is used here: every statement
below is made at the level of `HJO.Sweep.zop`, the operator `z_i` itself, and of the bare
product `y_1d^*_+`. By `HJO.Sweep.braidRepRespects_two_false`, `HJO.Sweep.braidRep` has to take
values in the endomorphisms of `V_k ⊗ 𝕜[q^{1/2}]`, and phrasing the reduction below `zRep` keeps it
independent of that.

## References

A. Mellit, *Toric braids and `(m, n)`-parking
functions*, §5.5.
-/

@[expose] public section

namespace HJO.Sweep

open Braid

/-! ### The starred arrow against a braid letter and against Mellit's train -/

section Field

variable {L : Type*} [Field L]

/-- `d^*_+T_i^{-1} = T_{i+1}^{-1}d^*_+` on `V_k` for `1 ≤ i < k`, the operator form of
`HJO.Sweep.dplusStar_braidInv`'s first clause for the inverses (`HJO.Sweep.dplusStar_braidInv`). -/
theorem dplusStar_mul_braidInvEnd (q u : L) (hq : q ≠ 0) {i k : ℕ} (hi : 1 ≤ i) (hik : i < k) :
    dplusStar q u k * braidInvEnd q i = braidInvEnd q (i + 1) * dplusStar q u k :=
  LinearMap.ext fun F => dplusStar_braidInv q u hq hi hik F

/-- **The train absorbs the letter**: `T^*_{k↘1}T_1 = T^*_{k↘2}` for `2 ≤ k`. Mellit's train
`trainUpEnd q k 1` is `T_{k-1}^{-1} ⋯ T_1^{-1}`, and factoring its last letter off as
`trainUpEnd q 2 1` is `HJO.Braid.trainUp_mul_trainUp`. -/
theorem trainUpEnd_one_mul_braidEnd_one (q : L) (hq : q ≠ 0) {k : ℕ} (hk : 2 ≤ k) :
    trainUpEnd q k 1 * braidEnd q 1 = trainUpEnd q k 2 := by
  have hbs := isBraidSystem_braidEnd q hq k
  have hsplit : trainUpEnd q k 2 * braidInvEnd q 1 = trainUpEnd q k 1 := by
    rw [show braidInvEnd q 1 = trainUpEnd q 2 1 from
      (Braid.trainUp_succ_self (braidEnd q) (braidInvEnd q) 1).symm]
    exact Braid.trainUp_mul_trainUp hbs (by omega) le_rfl (by omega) hk le_rfl (by omega)
  rw [← hsplit, mul_assoc, braidInvEnd_mul_braidEnd q hq, mul_one]

/-- **The starred arrow conjugates Mellit's train up by one index**:
`d^*_+T^*_{k↘1} = T^*_{k+1↘2}d^*_+` on `V_k`.

Both trains are descending words in the *inverse* braid letters — `trainUpEnd q k 1` is
`T_{k-1}^{-1} ⋯ T_1^{-1}`, the second branch of `HJO.Braid.trainUp` — so this is
`HJO.Braid.mul_descendingWord` applied to `HJO.Sweep.dplusStar_mul_braidInvEnd`, whose range
`1 ≤ i < k` is exactly the set of letters the train contains. At `k = 1` both trains are empty and
there is nothing to move. -/
theorem dplusStar_mul_trainUpEnd_one (q u : L) (hq : q ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    dplusStar q u k * trainUpEnd q k 1 = trainUpEnd q (k + 1) 2 * dplusStar q u k := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · have hk1' : k = 1 := by omega
    subst hk1'
    rw [show trainUpEnd q 1 1 = 1 from by rw [trainUpEnd, Braid.trainUp_self],
      show trainUpEnd q (1 + 1) 2 = 1 from by rw [trainUpEnd, Braid.trainUp_self], mul_one,
      one_mul]
  · have hL : trainUpEnd q k 1 = Braid.descendingWord (braidInvEnd q) k 1 := by
      rw [trainUpEnd, Braid.trainUp]
      exact ite_eq_right_of_eq_false _ _ (eq_false (by omega))
    have hR : trainUpEnd q (k + 1) 2 = Braid.descendingWord (braidInvEnd q) (k + 1) 2 := by
      rw [trainUpEnd, Braid.trainUp]
      exact ite_eq_right_of_eq_false _ _ (eq_false (by omega))
    rw [hL, hR]
    exact Braid.mul_descendingWord fun i hi hik => dplusStar_mul_braidInvEnd q u hq hi hik

end Field

/-! ### The `y` letter is removable from the clause -/

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`z_2y_1 = y_1T_1^{-1}z_1T_1` on `V_k` for `k ≥ 2`**, the `y`-side of the `z` letter of
`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`.

`z_2 = q^{-1}T_1z_1T_1` is `HJO.Sweep.zop`'s recursion; the mixed relation of
`HJO.Braid.BraidMonoid` (`HJO.Sweep.zopOneStar_mul_braidEnd_mul_mulLeft_auxVar_one`) turns
`z_1T_1y_1` into `y_2z_1T_1`; and `y_2 = qT_1^{-1}y_1T_1^{-1}` (`HJO.Sweep.mulLeft_auxVar_succ_eq`)
cancels the leading `T_1` against the factor `q^{-1}`. -/
theorem zop_two_mul_mulLeft_auxVar_one (q u : L) (hq : q ≠ 0) {k : ℕ} (hk : 2 ≤ k) :
    zop q u k 2 * LinearMap.mulLeft L (auxVar 1 : Total L)
      = LinearMap.mulLeft L (auxVar 1 : Total L) *
        (braidInvEnd q 1 * zopOneStar q u k * braidEnd q 1) := by
  set Y : Module.End L (Total L) := LinearMap.mulLeft L (auxVar 1 : Total L) with hY
  set Z : Module.End L (Total L) := zopOneStar q u k with hZ
  have hTT : braidEnd q 1 * braidInvEnd q 1 = 1 := braidEnd_mul_braidInvEnd q hq 1
  have hTT' : braidInvEnd q 1 * braidEnd q 1 = 1 := braidInvEnd_mul_braidEnd q hq 1
  have hz2 : zop q u k 2 = q⁻¹ • (braidEnd q 1 * Z * braidEnd q 1) := rfl
  have hy2 : LinearMap.mulLeft L (auxVar 2 : Total L)
      = q • (braidInvEnd q 1 * Y * braidInvEnd q 1) := mulLeft_auxVar_succ_eq q hq le_rfl
  have hstep : Z * braidEnd q 1 * Y
      = LinearMap.mulLeft L (auxVar 2 : Total L) * Z * braidEnd q 1 := by
    have h := zopOneStar_mul_braidEnd_mul_mulLeft_auxVar_one q u hq hk
    calc Z * braidEnd q 1 * Y
        = Z * braidEnd q 1 * Y * (braidInvEnd q 1 * braidEnd q 1) := by rw [hTT', mul_one]
      _ = Z * braidEnd q 1 * Y * braidInvEnd q 1 * braidEnd q 1 := by simp only [mul_assoc]
      _ = LinearMap.mulLeft L (auxVar 2 : Total L) * Z * braidEnd q 1 := by rw [h]
  have key : braidEnd q 1 * Z * braidEnd q 1 * Y
      = q • (Y * (braidInvEnd q 1 * Z * braidEnd q 1)) := by
    calc braidEnd q 1 * Z * braidEnd q 1 * Y
        = braidEnd q 1 * (Z * braidEnd q 1 * Y) := by simp only [mul_assoc]
      _ = braidEnd q 1 * (LinearMap.mulLeft L (auxVar 2 : Total L) * Z * braidEnd q 1) := by
            rw [hstep]
      _ = braidEnd q 1 * (q • (braidInvEnd q 1 * Y * braidInvEnd q 1) * Z * braidEnd q 1) := by
            rw [hy2]
      _ = q • (braidEnd q 1 * braidInvEnd q 1 * (Y * (braidInvEnd q 1 * Z * braidEnd q 1))) := by
            simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
      _ = q • (Y * (braidInvEnd q 1 * Z * braidEnd q 1)) := by rw [hTT, one_mul]
  rw [hz2, smul_mul_assoc, key, smul_smul, inv_mul_cancel₀ hq, one_smul]

/-- **The `z` letter of `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` with the
multiplication operator removed.** Given `z_1^{(k+1)}T_1d^*_+ = T_1d^*_+z_1^{(k)}` — an identity in
`d^*_+` and `z_1` alone — the vertical arrow of the diagram intertwines the two `z`'s:

`z_2^{(k+1)}(y_1d^*_+) = (y_1d^*_+)z_1^{(k)}`.

The arrow of the diagram is `-y_1d^*_+` (`HJO.Sweep.negYOneDPlusStar`) and the sign cancels, so this
is that clause. `HJO.Sweep.zop_two_mul_mulLeft_auxVar_one` moves the factor `y_1` to the outside on
the left, leaving `T_1^{-1}z_1^{(k+1)}T_1d^*_+` against `d^*_+z_1^{(k)}`; the hypothesis is that
identity with the leading `T_1^{-1}` cleared. The scalars `(qu)^{-1}` that `HJO.Sweep.braidRep` puts
on both `z`'s cancel and are not part of this statement. -/
theorem zop_two_mul_mulLeft_dplusStar (q u : L) (hq : q ≠ 0) {k : ℕ} (hk : 1 ≤ k)
    (h : zopOneStar q u (k + 1) * braidEnd q 1 * dplusStar q u k
      = braidEnd q 1 * dplusStar q u k * zopOneStar q u k) :
    zop q u (k + 1) 2 * (LinearMap.mulLeft L (auxVar 1 : Total L) * dplusStar q u k)
      = LinearMap.mulLeft L (auxVar 1 : Total L) * dplusStar q u k * zop q u k 1 := by
  have hTT' : braidInvEnd q 1 * braidEnd q 1 = 1 := braidInvEnd_mul_braidEnd q hq 1
  rw [zop_one, ← mul_assoc,
    zop_two_mul_mulLeft_auxVar_one q u hq (show 2 ≤ k + 1 by omega)]
  calc LinearMap.mulLeft L (auxVar 1 : Total L) *
          (braidInvEnd q 1 * zopOneStar q u (k + 1) * braidEnd q 1) * dplusStar q u k
      = LinearMap.mulLeft L (auxVar 1 : Total L) * (braidInvEnd q 1 *
          (zopOneStar q u (k + 1) * braidEnd q 1 * dplusStar q u k)) := by
        simp only [mul_assoc]
    _ = LinearMap.mulLeft L (auxVar 1 : Total L) * (braidInvEnd q 1 * braidEnd q 1 *
          (dplusStar q u k * zopOneStar q u k)) := by rw [h]; simp only [mul_assoc]
    _ = LinearMap.mulLeft L (auxVar 1 : Total L) * dplusStar q u k * zopOneStar q u k := by
        rw [hTT', one_mul, mul_assoc]

/-- **The `z` letter reduced to a commutator identity.** Given

`q·[d^*_+,d^♭_-]_{k+1}·d^*_+ = T_1·d^*_+·[d^*_+,d^♭_-]_k`

on `V_k` — no `y`, no train, no braid monoid — the hypothesis of
`HJO.Sweep.zop_two_mul_mulLeft_dplusStar` holds, and with it the `z` letter of
`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`.

`HJO.Sweep.zop` writes `z_1^{(m)}` as `q^m/(1-q)` times the commutator followed by the train
`T^*_{m↘1}`. On the left the train absorbs the letter `T_1`
(`HJO.Sweep.trainUpEnd_one_mul_braidEnd_one`) and `d^*_+` then carries the shortened train back down
(`HJO.Sweep.dplusStar_mul_trainUpEnd_one`), so both sides end in the same factor `T^*_{k↘1}`; the
scalars differ by exactly the `q` the hypothesis carries, `q^{k+1}/(1-q)` being `q·q^k/(1-q)`. The
scalar is carried, never divided by, so `q = 1` is not excluded. -/
theorem zopOneStar_braidEnd_dplusStar_of_starComm (q u : L) (hq : q ≠ 0) {k : ℕ} (hk : 1 ≤ k)
    (h : q • (starComm q u (k + 1) * dplusStar q u k)
      = braidEnd q 1 * dplusStar q u k * starComm q u k) :
    zopOneStar q u (k + 1) * braidEnd q 1 * dplusStar q u k
      = braidEnd q 1 * dplusStar q u k * zopOneStar q u k := by
  have hscal : q ^ (k + 1) / (1 - q) = q ^ k / (1 - q) * q := by
    rw [pow_succ]
    ring
  calc zopOneStar q u (k + 1) * braidEnd q 1 * dplusStar q u k
      = (q ^ (k + 1) / (1 - q)) • (starComm q u (k + 1) *
          (trainUpEnd q (k + 1) 1 * braidEnd q 1) * dplusStar q u k) := by
        rw [zopOneStar_eq]
        simp only [smul_mul_assoc, mul_assoc]
    _ = (q ^ k / (1 - q)) • (q • (starComm q u (k + 1) * dplusStar q u k) *
          trainUpEnd q k 1) := by
        rw [trainUpEnd_one_mul_braidEnd_one q hq (show 2 ≤ k + 1 by omega), hscal, mul_assoc,
          ← dplusStar_mul_trainUpEnd_one q u hq hk]
        simp only [smul_mul_assoc, smul_smul, mul_assoc]
    _ = (q ^ k / (1 - q)) • (braidEnd q 1 * dplusStar q u k * starComm q u k *
          trainUpEnd q k 1) := by rw [h]
    _ = braidEnd q 1 * dplusStar q u k * zopOneStar q u k := by
        rw [zopOneStar_eq]
        simp only [mul_smul_comm, mul_assoc]

end Newton

end HJO.Sweep

end
