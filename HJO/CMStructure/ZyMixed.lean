/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.YBraid
public import HJO.CMStructure.ZBraid

/-! # The mixed relation of the braid representation

This file is the mixed clause of `HJO.Sweep.braidRepRespects_mellit`, one of the five relation
families of Mellit's Proposition 5.3, and the one not proved in the neighbouring files:

`z_1T_1y_1T_1^{-1} = qT_1^{-1}y_1T_1^{-1}z_1`, a hypothesis of
`HJO.Sweep.braidRepRespectsTotal_of_residualTotal`, proved here as
`HJO.Sweep.zRepTotal_braidEnd_yRepTotal_braidInvEnd`.

## The relation is one index shift, not a computation with `z_1`

Nothing about the internal structure of `d^*_+` or `d_-` is used beyond a single fact about each,
and no braid relation beyond the cancellation `T_1^{-1}T_1 = 1`. Read the two sides against the
closed forms already in hand:

* `y_1` is multiplication by `-y_1` (`HJO.Sweep.yRepTotal_eq_neg_mulLeft`), so the two signs
  cancel and the relation is about the multiplication operators.
* the right-hand side is *not* a conjugate to be expanded: `q(T_1^{-1}y_1T_1^{-1})` is precisely
  multiplication by `y_2`, which is `HJO.Sweep.mulLeft_auxVar_succ_eq`, the `y`-recursion of
  `HJO.Sweep.braidRep` satisfied by the multiplication operators. So the relation to prove is
  `z_1T_1y_1T_1^{-1} = y_2z_1`, with `y_2` a multiplier and no conjugation left anywhere.
* on the left `z_1 = q^k/(1-q) [d^*_+, d_-] T^*_{k↘1}` (`HJO.Sweep.zopOneStar_eq`) and the train
  absorbs the letter: `T^*_{k↘1}T_1 = T^*_{k↘2}` by `HJO.Braid.trainUp_mul_trainUp` and
  `HJO.Braid.trainUp_succ_self`, since `T^*_{k↘1} = T^*_{k↘2}T_1^{-1}`.

What is left is `[d^*_+, d_-] T^*_{k↘2} y_1 = y_2 [d^*_+, d_-] T^*_{k↘2}`, and both factors move the
index for a separate reason:

* `T^*_{k↘2}` is a word in the letters `T_2, \dots, T_{k-1}`, every one of which is linear over
  `y_1` (`HJO.Sweep.braid_symmetric_mul` against `HJO.Sweep.swapAux_auxVar_of_ne`), so the train
  passes `y_1` unchanged. Its inverted letters do too, a two-sided inverse of an operator commuting
  with a multiplier commuting with it as well.
* the commutator **raises** the index of a multiplier exactly as it raises the index of a braid
  letter: `HJO.Sweep.starComm_mul_mulLeft_auxVar_one` is `[d^*_+, d_-]y_1 = y_2[d^*_+, d_-]` on
  `V_k` for `k ≥ 2`, off `HJO.Sweep.dplusStar_auxVar_mul` (`d^*_+y_i = y_{i+1}d^*_+`) and the
  linearity of `d_-` over the earlier variables, one of the two summands needing the latter at `y_1`
  and the other at `y_2`.

The shift the commutator supplies and the shift the train `T^*_{k↘1}T_1` performs are the same two
shifts that cancel in `HJO.Sweep.zopOneStar_mul_braidEnd`; here they do not cancel, they compose,
and what comes out is the raised multiplier `y_2` — which is what the right-hand side is.

## `2 ≤ k` is exactly the field's hypothesis and it is load-bearing twice

`d_-` on `V_1` is the extraction at `y_1` itself and is *not* linear over `y_1`
(`HJO.Sweep.lowerCoeff_auxVar_mul` is what happens instead), so the commutator's shift needs
`k ≥ 2`; and `T^*_{k↘2}` is a word in letters of index `≥ 2` only when `k ≥ 2`. Nothing else here
constrains `k`, and `q ≠ 0` is spent only on the two cancellations `T_1^{-1}T_1 = 1` and on
`HJO.Sweep.mulLeft_auxVar_succ_eq`. The scalar `q^k/(1-q)` is never divided by: it is carried
through, so `q = 1` — where it is `0` and both sides collapse — needs no separate treatment.

## Main results

* `HJO.Sweep.starComm_mul_mulLeft_auxVar_one`: the commutator raises the index of a multiplier.
* `HJO.Sweep.zopOneStar_mul_braidEnd_mul_mulLeft_auxVar_one`: the relation on
  `HJO.Sweep.zopOneStar`, in the form `z_1T_1y_1T_1^{-1} = y_2z_1`.
* `HJO.Sweep.zRepTotal_braidEnd_yRepTotal_braidInvEnd`: the clause on the representation, which
  discharges the corresponding hypothesis of the reductions of
  `HJO/CMStructure/BraidRepReduce.lean`.

## References

The lemma `HJO.Sweep.braidRepRespects_mellit` and definitions `HJO.Sweep.braidRep`,
`HJO.Sweep.zop`, `HJO.Braid.BraidMonoid`, `HJO.Braid.trainUp`. Following A. Mellit,
*Toric braids and `(m,n)`-parking functions*, Proposition 5.3, whose displayed reduction of the
mixed relation is the operator identity
`[d^*_+, d_-]T^*_{k↘2}y_1T_1^{-1} = y_2[d^*_+, d_-]T^*_{k↘1}`.
-/

@[expose] public section

namespace HJO.Sweep

open Braid

section Field

variable {L : Type*} [Field L]

/-- Multiplication by `y_1` commutes with a braid operator of index `≥ 2`: the operator form of
`HJO.Sweep.braid_symmetric_mul` at the multiplier `y_1`, which `s_j` fixes for `j ≥ 2` by
`HJO.Sweep.swapAux_auxVar_of_ne`. -/
private theorem mulLeft_auxVar_one_comm_braidEnd' (q : L) {j : ℕ} (hj : 2 ≤ j) :
    LinearMap.mulLeft L (auxVar 1 : Total L) * braidEnd q j
      = braidEnd q j * LinearMap.mulLeft L (auxVar 1 : Total L) := by
  refine LinearMap.ext fun F => ?_
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, braidEnd,
    LinearMap.restrictScalars_apply]
  exact (braid_symmetric_mul q
    (swapAux_auxVar_of_ne (L := L) le_rfl (by omega) (by omega)) F).symm

/-- The same for the inverted letter: an operator with a two-sided inverse commutes with a
multiplier exactly when its inverse does. -/
private theorem mulLeft_auxVar_one_comm_braidInvEnd' (q : L) (hq : q ≠ 0) {j : ℕ} (hj : 2 ≤ j) :
    LinearMap.mulLeft L (auxVar 1 : Total L) * braidInvEnd q j
      = braidInvEnd q j * LinearMap.mulLeft L (auxVar 1 : Total L) := by
  have hL := braidInvEnd_mul_braidEnd q hq j
  have hR := braidEnd_mul_braidInvEnd q hq j
  calc LinearMap.mulLeft L (auxVar 1 : Total L) * braidInvEnd q j
      = braidInvEnd q j * braidEnd q j
          * (LinearMap.mulLeft L (auxVar 1 : Total L) * braidInvEnd q j) := by
        rw [hL, one_mul]
    _ = braidInvEnd q j * (braidEnd q j * LinearMap.mulLeft L (auxVar 1 : Total L))
          * braidInvEnd q j := by simp only [mul_assoc]
    _ = braidInvEnd q j * LinearMap.mulLeft L (auxVar 1 : Total L)
          * (braidEnd q j * braidInvEnd q j) := by
        rw [← mulLeft_auxVar_one_comm_braidEnd' q hj]; simp only [mul_assoc]
    _ = braidInvEnd q j * LinearMap.mulLeft L (auxVar 1 : Total L) := by rw [hR, mul_one]

/-- **The train `T^*_{k↘2}` is linear over `y_1`**: it is a word in the inverted letters
`T_2^{-1}, \dots, T_{k-1}^{-1}`, each of which commutes with multiplication by `y_1`, so the whole
word does by `HJO.Braid.mul_prod_comm`. At `k = 2` the train is empty. -/
private theorem mulLeft_auxVar_one_comm_trainUpEnd' (q : L) (hq : q ≠ 0) {k : ℕ} (hk : 2 ≤ k) :
    LinearMap.mulLeft L (auxVar 1 : Total L) * trainUpEnd q k 2
      = trainUpEnd q k 2 * LinearMap.mulLeft L (auxVar 1 : Total L) := by
  rw [trainUpEnd, Braid.trainUp]
  split_ifs with h
  · obtain rfl : k = 2 := by omega
    rw [Braid.ascendingWord, show (2 : ℕ) - 2 = 0 from rfl]
    simp
  · rw [Braid.descendingWord]
    refine Braid.mul_prod_comm fun y hy => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_reverse, List.mem_range'_1] at hj
    exact mulLeft_auxVar_one_comm_braidInvEnd' q hq (by omega)

/-- **The train factors as `T^*_{k↘1} = T^*_{k↘2}T_1^{-1}`**, by `HJO.Braid.trainUp_mul_trainUp` and
`HJO.Braid.trainUp_succ_self`, which reads the single-letter train `T^*_{2↘1}` as `T_1^{-1}`. -/
private theorem trainUpEnd_two_mul_braidInvEnd_one' (q : L) (hq : q ≠ 0) {k : ℕ} (hk : 2 ≤ k) :
    trainUpEnd q k 2 * braidInvEnd q 1 = trainUpEnd q k 1 := by
  have hbs := isBraidSystem_braidEnd q hq k
  rw [show braidInvEnd q 1 = trainUpEnd q 2 1 from
    (Braid.trainUp_succ_self (braidEnd q) (braidInvEnd q) 1).symm]
  exact Braid.trainUp_mul_trainUp hbs (by omega) le_rfl (by omega) hk le_rfl (by omega)

/-- **The train absorbs the letter**: `T^*_{k↘1}T_1 = T^*_{k↘2}` for `2 ≤ k`, the factorisation
`HJO.Sweep.trainUpEnd_two_mul_braidInvEnd_one'` read against `T_1^{-1}T_1 = 1`. -/
private theorem trainUpEnd_one_mul_braidEnd_one' (q : L) (hq : q ≠ 0) {k : ℕ} (hk : 2 ≤ k) :
    trainUpEnd q k 1 * braidEnd q 1 = trainUpEnd q k 2 := by
  rw [← trainUpEnd_two_mul_braidInvEnd_one' q hq hk, mul_assoc,
    braidInvEnd_mul_braidEnd q hq, mul_one]

end Field

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The lowering operator is linear over the earlier variables: `d_-(y_jF) = y_jd_-F` on `V_{k+1}`
for `1 ≤ j ≤ k`. This is `HJO.Sweep.dminusCM_auxVar_mul` for the modified
operator `d^♭_-` of `HJO.Sweep.dminus`, which is the one `HJO.Sweep.zopOneStar` is written with;
the proof is the same, `HJO.Sweep.lowerCoeff_mul_of_mem_piece` replacing its shifted twin. -/
private theorem dminus_auxVar_mul' (q : L) {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (F : Total L) :
    dminus q (k + 1) ((auxVar j : Total L) * F) = auxVar j * dminus q (k + 1) F := by
  rw [dminus_succ_apply, dminus_succ_apply, map_mul, qshiftNeg_auxVar_apply,
    lowerCoeff_mul_of_mem_piece (auxVar_mem_piece hj hjk)]

/-- `HJO.Sweep.dminus_auxVar_mul'` in the endomorphism monoid. -/
private theorem dminus_mul_mulLeft_auxVar' (q : L) {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    dminus q (k + 1) * LinearMap.mulLeft L (auxVar j : Total L)
      = LinearMap.mulLeft L (auxVar j : Total L) * dminus q (k + 1) :=
  LinearMap.ext fun F => dminus_auxVar_mul' q hj hjk F

omit [Algebra ℚ L] in
/-- `HJO.Sweep.dplusStar_auxVar_mul` in the endomorphism monoid: `d^*_+y_i = y_{i+1}d^*_+`. -/
private theorem dplusStar_mul_mulLeft_auxVar' (q u : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    dplusStar q u k * LinearMap.mulLeft L (auxVar i : Total L)
      = LinearMap.mulLeft L (auxVar (i + 1) : Total L) * dplusStar q u k :=
  LinearMap.ext fun F => dplusStar_auxVar_mul q u hi hik F

/-- **The commutator of the starred arrow with the lowering operator raises the index of a
multiplier**: `[d^*_+, d_-]y_1 = y_2[d^*_+, d_-]` on `V_k` for `k ≥ 2`, written at `k = m + 2` so
that no subtraction is truncated. This is the exact analogue for multipliers of
`HJO.Sweep.starComm_mul_braidEnd`, which raises the index of a braid letter.

Each summand shifts on its own. In `d^*_+d_-` the lowering operator passes `y_1` unchanged and the
starred arrow then raises it (`HJO.Sweep.dplusStar_auxVar_mul`); in `d_-d^*_+` the starred arrow
raises first and the lowering operator then passes `y_2`. The binding constraint is that `d_-` be
linear over the variable it meets, which on `V_{j+1}` holds for `y_1, \dots, y_j` — so the first
summand needs `1 ≤ m + 1` and the second `2 ≤ m + 2`, both free, and what `k ≥ 2` buys is that
`d_-` is never asked about `y_1` on `V_1`, where it is the extraction at `y_1` itself. -/
theorem starComm_mul_mulLeft_auxVar_one (q u : L) (m : ℕ) :
    starComm q u (m + 2) * LinearMap.mulLeft L (auxVar 1 : Total L)
      = LinearMap.mulLeft L (auxVar 2 : Total L) * starComm q u (m + 2) := by
  have hA : dplusStar q u (m + 1) * dminus q (m + 2) * LinearMap.mulLeft L (auxVar 1 : Total L)
      = LinearMap.mulLeft L (auxVar 2 : Total L) * (dplusStar q u (m + 1) * dminus q (m + 2)) := by
    rw [mul_assoc, dminus_mul_mulLeft_auxVar' (k := m + 1) q le_rfl (by omega), ← mul_assoc,
      dplusStar_mul_mulLeft_auxVar' q u (i := 1) le_rfl (by omega), mul_assoc]
  have hB : dminus q (m + 3) * dplusStar q u (m + 2) * LinearMap.mulLeft L (auxVar 1 : Total L)
      = LinearMap.mulLeft L (auxVar 2 : Total L) * (dminus q (m + 3) * dplusStar q u (m + 2)) := by
    rw [mul_assoc, dplusStar_mul_mulLeft_auxVar' q u (i := 1) le_rfl (by omega), ← mul_assoc,
      dminus_mul_mulLeft_auxVar' (k := m + 2) q (by omega) (by omega), mul_assoc]
  rw [starComm_add_two, sub_mul, mul_sub, hA, hB]

/-- **The mixed relation on `HJO.Sweep.zopOneStar`**: `z_1T_1y_1T_1^{-1} = y_2z_1` on `V_k` for
`k ≥ 2`, the `y`'s being the multiplication operators.

The train absorbs the letter, `T^*_{k↘1}T_1` being `T^*_{k↘2}` by `HJO.Braid.trainUp_mul_trainUp`;
the shortened train passes the multiplier `y_1` because every letter in it has index `≥ 2`; the
commutator raises it to `y_2` (`HJO.Sweep.starComm_mul_mulLeft_auxVar_one`), and the letter
`T_1^{-1}` put back on the right rebuilds `T^*_{k↘1}`. The scalar `q^k/(1-q)` is carried, never
divided by. -/
theorem zopOneStar_mul_braidEnd_mul_mulLeft_auxVar_one (q u : L) (hq : q ≠ 0) {k : ℕ}
    (hk : 2 ≤ k) :
    zopOneStar q u k * braidEnd q 1 * LinearMap.mulLeft L (auxVar 1 : Total L)
        * braidInvEnd q 1
      = LinearMap.mulLeft L (auxVar 2 : Total L) * zopOneStar q u k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [zopOneStar_eq]
  simp only [smul_mul_assoc, mul_smul_comm]
  refine congrArg _ ?_
  calc starComm q u (m + 2) * trainUpEnd q (m + 2) 1 * braidEnd q 1
          * LinearMap.mulLeft L (auxVar 1 : Total L) * braidInvEnd q 1
      = starComm q u (m + 2) * (trainUpEnd q (m + 2) 1 * braidEnd q 1)
          * LinearMap.mulLeft L (auxVar 1 : Total L) * braidInvEnd q 1 := by
        simp only [mul_assoc]
    _ = starComm q u (m + 2)
          * (trainUpEnd q (m + 2) 2 * LinearMap.mulLeft L (auxVar 1 : Total L))
          * braidInvEnd q 1 := by
        rw [trainUpEnd_one_mul_braidEnd_one' q hq hk]; simp only [mul_assoc]
    _ = starComm q u (m + 2) * LinearMap.mulLeft L (auxVar 1 : Total L)
          * (trainUpEnd q (m + 2) 2 * braidInvEnd q 1) := by
        rw [← mulLeft_auxVar_one_comm_trainUpEnd' q hq hk]; simp only [mul_assoc]
    _ = LinearMap.mulLeft L (auxVar 2 : Total L) * starComm q u (m + 2)
          * (trainUpEnd q (m + 2) 2 * braidInvEnd q 1) := by
        rw [starComm_mul_mulLeft_auxVar_one]
    _ = LinearMap.mulLeft L (auxVar 2 : Total L)
          * (starComm q u (m + 2) * trainUpEnd q (m + 2) 1) := by
        rw [trainUpEnd_two_mul_braidInvEnd_one' q hq hk]; simp only [mul_assoc]

/-- **`HJO.Sweep.braidRepRespects_mellit`'s mixed clause**, the last hypothesis
`HJO.Sweep.braidRepRespectsTotal_of_residualTotal` needed beyond `z_iz_j = z_jz_i`: for `k ≥ 2`,
`z_1T_1y_1T_1^{-1} = q(T_1^{-1}y_1T_1^{-1}z_1)` on the representation.

The two closed forms turn this into `HJO.Sweep.zopOneStar_mul_braidEnd_mul_mulLeft_auxVar_one`: the
`y`'s become multiplication by `-y_1` (`HJO.Sweep.yRepTotal_eq_neg_mulLeft`) and the two signs
cancel;
`q(T_1^{-1}y_1T_1^{-1})` on the right is multiplication by `y_2`
(`HJO.Sweep.mulLeft_auxVar_succ_eq`), which is where the factor `q` of the half-integral
normalisation goes; and the `z`'s are `(qu)^{-1}z_1` on both sides
(`HJO.Sweep.zRepTotal_eq_smul_zop`), so that scalar cancels too. -/
theorem zRepTotal_braidEnd_yRepTotal_braidInvEnd (q u : L) {r : L} (hq : q ≠ 0)
    (hr : r * r = q) {k : ℕ} (hk : 2 ≤ k) :
    zRepTotal q u r k 1 * braidEnd q 1 * yRepTotal q u r k 1 * braidInvEnd q 1
      = q • (braidInvEnd q 1 * yRepTotal q u r k 1 * braidInvEnd q 1 * zRepTotal q u r k 1) := by
  have hy2 : LinearMap.mulLeft L (auxVar 2 : Total L)
      = q • (braidInvEnd q 1 * LinearMap.mulLeft L (auxVar 1 : Total L) * braidInvEnd q 1) :=
    mulLeft_auxVar_succ_eq q hq le_rfl
  have key : zopOneStar q u k * braidEnd q 1 * LinearMap.mulLeft L (auxVar 1 : Total L)
        * braidInvEnd q 1
      = q • (braidInvEnd q 1 * LinearMap.mulLeft L (auxVar 1 : Total L) * braidInvEnd q 1
        * zopOneStar q u k) := by
    rw [zopOneStar_mul_braidEnd_mul_mulLeft_auxVar_one q u hq hk, hy2, smul_mul_assoc]
  have hz : zRepTotal q u r k 1 = (q * u)⁻¹ • zopOneStar q u k := by
    rw [zRepTotal_eq_smul_zop q u hr 1 le_rfl (by omega), zop_one]
  have hyv : yRepTotal q u r k 1 = -LinearMap.mulLeft L (auxVar 1 : Total L) :=
    yRepTotal_eq_neg_mulLeft q u hq hr le_rfl (by omega)
  rw [hz, hyv]
  have e1 : ((q * u)⁻¹ • zopOneStar q u k) * braidEnd q 1
        * (-LinearMap.mulLeft L (auxVar 1 : Total L)) * braidInvEnd q 1
      = -((q * u)⁻¹ • (zopOneStar q u k * braidEnd q 1
        * LinearMap.mulLeft L (auxVar 1 : Total L) * braidInvEnd q 1)) := by
    simp only [smul_mul_assoc, neg_mul, mul_neg]
  have e2 : q • (braidInvEnd q 1 * (-LinearMap.mulLeft L (auxVar 1 : Total L)) * braidInvEnd q 1
        * ((q * u)⁻¹ • zopOneStar q u k))
      = -((q * u)⁻¹ • (q • (braidInvEnd q 1 * LinearMap.mulLeft L (auxVar 1 : Total L)
        * braidInvEnd q 1 * zopOneStar q u k))) := by
    simp only [neg_mul, mul_neg, smul_neg, mul_smul_comm, smul_smul, mul_comm]
  rw [e1, e2, key]

end Newton

end HJO.Sweep
