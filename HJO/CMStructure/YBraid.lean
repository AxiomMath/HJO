/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.DemazureIdentities
public import HJO.Shuffle.BraidRep
public import HJO.Shuffle.MellitShiftGenerators

/-! # The `y` operators of the braid representation are multiplication operators

This file is the `y`-half of `HJO.Sweep.braidRepRespects_mellit`, an instance of
Mellit's Proposition 5.3. Of its five clauses — the five relation families
`HJO.Braid.BraidMonoid` imposes beyond the braid system itself — two are settled here,
`y_iT_j = T_jy_i` and `y_iy_j = y_jy_i`, and both come out of one closed form.

## The closed form: `y_i` is multiplication by `-y_i`

The word `𝗒_i` of `HJO.Braid.yWord` is built by the recursion `𝗒_{i+1} = T̄_i𝗒_iT̄_i`, and on the
operators that reads `y_{i+1} = qT_i^{-1}y_iT_i^{-1}` (`HJO.Sweep.yRepTotal_succ`, the factor `q`
being the price of the half-integral normalisation of the braid letters). The claim is that the
whole family is the multiplication operators: `y_i` is multiplication by `-y_i`, the sign coming
from the assignment `y_1 ↦ -y_1` of `HJO.Sweep.braidRep` and passing through the recursion
untouched.

That is one proved identity away. `HJO.Sweep.braid_auxVar_succ_mul_braid`
is `T_i(y_{i+1}T_iF) = qy_iF`, i.e. `T_i ∘ y_{i+1} ∘ T_i = q · y_i` on multiplication operators;
conjugating both sides by `T_i^{-1}` turns it into `y_{i+1} = qT_i^{-1}y_iT_i^{-1}`
(`HJO.Sweep.mulLeft_auxVar_succ_eq`), which is the operator recursion on the nose. So the induction
is one step wide and closes: `HJO.Sweep.yRepTotal_eq_neg_mulLeft`.

The recursion is available only for `i ≤ k` — beyond the rank the letter `T̄_i` is out of rank and
`HJO.Sweep.braidRepLetterTotal` sends it to the identity, so `y_{k+1} = y_k` there and the closed
form fails. `1 ≤ i ≤ k` is therefore not slack, and it is exactly the range `HJO.Braid.BraidMonoid`
imposes the two relations on.

## Both clauses are then immediate, and one range is redundant

* `y_iT_j = T_jy_i` is `HJO.Sweep.braid_symmetric_mul` — `T_j` is
  linear over a multiplier `s_j` fixes — applied to `y_i`, which `s_j` fixes for `i ∉ {j, j+1}` by
  `HJO.Sweep.swapAux_auxVar_of_ne`. **The presentation's `1 ≤ j` and `j + 1 ≤ k` are not needed**:
  `HJO.Sweep.yRepTotal_mul_braidEnd` holds at every `j`, because `T_j` is an endomorphism of the
  whole total space and the only thing the argument asks of `j` is that `s_j` miss `y_i`. At
  `j = 0` both operators are the identity (`HJO.Sweep.braid_zero_index`) and the statement is
  trivially true, so nothing is being smuggled in. The two hypotheses are therefore dropped.
* `y_iy_j = y_jy_i` is then commutativity of `HJO.Sweep.Total`, the two operators being
  multiplication by `y_i` and by `y_j`. Here both ranges are live, one per closed form.

What is left of Mellit's Proposition 5.3 after this file, `HJO/CMStructure/ZBraid.lean` and
`HJO/CMStructure/ZyMixed.lean` is one clause of the five: `z_iz_j = z_jz_i`. The mixed relation
is *not* free from the closed form here — `T_1y_1T_1^{-1}` is `y_2 + (q-1)y_1T_1^{-1}`, not a
multiplication operator — and needs the index shift `ZyMixed` reads off `z_1`; what the closed form
does give it is that the relation's right-hand side is multiplication by `y_2`.

## Main results

* `HJO.Sweep.braidEnd_mul_mulLeft_auxVar_succ_mul_braidEnd`,
  `HJO.Sweep.mulLeft_auxVar_succ_eq`: `HJO.Sweep.braid_auxVar_succ_mul_braid` in the endomorphism
  monoid, and the form the recursion reads it in.
* `HJO.Sweep.yRepTotal_eq_neg_mulLeft`: the closed form, for `1 ≤ i ≤ k`.
* `HJO.Sweep.yRepTotal_mul_braidEnd`: the clause `y_iT_j = T_jy_i`, which is the field
  `HJO.Sweep.BraidRepResidualTotal.yRepTotal_comm_T`.
* `HJO.Sweep.yRepTotal_mul_comm`: the clause `y_iy_j = y_jy_i`, which is the field
  `HJO.Sweep.BraidRepResidualTotal.yRepTotal_comm`.

## References

Following A. Mellit, *Toric braids and `(m, n)`-parking
functions*, Proposition 5.3.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-- **`HJO.Sweep.braid_auxVar_succ_mul_braid` in the endomorphism monoid**:
`T_i ∘ y_{i+1} ∘ T_i = q · y_i`, the multiplication operators being written `LinearMap.mulLeft`.
This is `HJO.Sweep.braid_auxVar_succ_mul_braid` with the application unbundled; `1 ≤ i` is live
there because at `i = 0` the variable `y_0` is read as `y_1` and both sides degenerate. -/
theorem braidEnd_mul_mulLeft_auxVar_succ_mul_braidEnd (q : L) {i : ℕ} (hi : 1 ≤ i) :
    braidEnd q i * LinearMap.mulLeft L (auxVar (i + 1) : Total L) * braidEnd q i
      = q • LinearMap.mulLeft L (auxVar i : Total L) := by
  refine LinearMap.ext fun F => ?_
  have h := braid_auxVar_succ_mul_braid q hi F
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply,
    braidEnd, LinearMap.restrictScalars_apply]
  rw [h, scal_eq_algebraMap, ← Algebra.smul_def, smul_mul_assoc]

/-- **The multiplication operators satisfy the `y`-recursion of `HJO.Sweep.braidRep`**:
`y_{i+1} = qT_i^{-1}y_iT_i^{-1}` for `1 ≤ i`. This is
`HJO.Sweep.braidEnd_mul_mulLeft_auxVar_succ_mul_braidEnd` conjugated by `T_i^{-1}`, which is where
`q ≠ 0` is spent — it is what makes `T_i` invertible
(`HJO.Sweep.braidEnd_mul_braidInvEnd`). No division by `q` happens, the factor `q` staying on the
same side throughout. -/
theorem mulLeft_auxVar_succ_eq (q : L) (hq : q ≠ 0) {i : ℕ} (hi : 1 ≤ i) :
    LinearMap.mulLeft L (auxVar (i + 1) : Total L)
      = q • (braidInvEnd q i * LinearMap.mulLeft L (auxVar i : Total L) * braidInvEnd q i) := by
  have hL := braidInvEnd_mul_braidEnd q hq i
  have hR := braidEnd_mul_braidInvEnd q hq i
  have hsandwich : braidInvEnd q i
        * (braidEnd q i * LinearMap.mulLeft L (auxVar (i + 1) : Total L) * braidEnd q i)
        * braidInvEnd q i
      = LinearMap.mulLeft L (auxVar (i + 1) : Total L) := by
    rw [← mul_assoc (braidInvEnd q i), ← mul_assoc (braidInvEnd q i), hL, one_mul, mul_assoc,
      hR, mul_one]
  rw [← hsandwich, braidEnd_mul_mulLeft_auxVar_succ_mul_braidEnd q hi]
  simp only [mul_smul_comm, smul_mul_assoc]

end Field

section Rat

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The closed form of the `y` operators: `y_i` is multiplication by `-y_i`**, for `1 ≤ i ≤ k`.

The assignment of `HJO.Sweep.braidRep` sends `y_1` to multiplication by `-y_1`, and the recursion
`HJO.Sweep.yRepTotal_succ` — `y_{i+1} = qT_i^{-1}y_iT_i^{-1}` — is satisfied by the multiplication
operators, which is `HJO.Sweep.mulLeft_auxVar_succ_eq`. So the induction is one step wide.

**`i ≤ k` is not slack.** Above the rank the letter `T̄_i` of `𝗒_{i+1}` is out of rank and
`HJO.Sweep.braidRepLetterTotal` sends it to the identity, so `y_{k+1}` is `y_k` again rather than
multiplication by `-y_{k+1}`. -/
theorem yRepTotal_eq_neg_mulLeft (q u : L) {r : L} (hq : q ≠ 0) (hr : r * r = q) {k i : ℕ}
    (hi : 1 ≤ i) (hik : i ≤ k) :
    yRepTotal q u r k i = -LinearMap.mulLeft L (auxVar i : Total L) := by
  induction i with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [yRepTotal_one q u r hik]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [show m + 1 + 1 = m + 2 from rfl, yRepTotal_succ q u hr (show m + 2 ≤ k by omega),
        ih (by omega) (by omega), mulLeft_auxVar_succ_eq q hq (show 1 ≤ m + 1 by omega)]
      refine LinearMap.ext fun F => ?_
      simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.smul_apply, map_neg,
        smul_neg]

/-- **`y_iT_j = T_jy_i` for `i ∉ {j, j+1}`**, one of the five clauses of Mellit's
Proposition 5.3, and one of the nine families
`HJO.Sweep.braidRepRespects_of_residual` discharges.

By `HJO.Sweep.yRepTotal_eq_neg_mulLeft` the operator `y_i` is multiplication by `-y_i`, and
`HJO.Sweep.braid_symmetric_mul` says `T_j` is linear over any
multiplier `s_j` fixes. `s_j` fixes `y_i` exactly outside `{y_j, y_{j+1}}`
(`HJO.Sweep.swapAux_auxVar_of_ne`), and that is the side condition.

**The presentation's `1 ≤ j` and `j + 1 ≤ k` are redundant and are dropped**: the braid operators
are endomorphisms of the whole total space and the argument asks nothing of `j` beyond `s_j` missing
`y_i`. At `j = 0` the statement is true for a second reason, `T_0` being the identity by
`HJO.Sweep.braid_zero_index`. `1 ≤ i ≤ k` stays, being what the closed form needs. -/
theorem yRepTotal_mul_braidEnd (q u : L) {r : L} (hq : q ≠ 0) (hr : r * r = q) {k i j : ℕ}
    (hi : 1 ≤ i) (hik : i ≤ k) (hij : i ≠ j) (hij' : i ≠ j + 1) :
    yRepTotal q u r k i * braidEnd q j = braidEnd q j * yRepTotal q u r k i := by
  rw [yRepTotal_eq_neg_mulLeft q u hq hr hi hik]
  refine LinearMap.ext fun F => ?_
  simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply, braidEnd,
    LinearMap.restrictScalars_apply, map_neg]
  rw [braid_symmetric_mul q (swapAux_auxVar_of_ne hi hij hij') F]

/-- **`y_iy_j = y_jy_i`**, a second of the five clauses of Mellit's Proposition 5.3. Both
operators are multiplication operators by `HJO.Sweep.yRepTotal_eq_neg_mulLeft`, and
`HJO.Sweep.Total` is commutative. Both index ranges are live, one for each closed form. -/
theorem yRepTotal_mul_comm (q u : L) {r : L} (hq : q ≠ 0) (hr : r * r = q) {k i j : ℕ}
    (hi : 1 ≤ i) (hik : i ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    yRepTotal q u r k i * yRepTotal q u r k j = yRepTotal q u r k j * yRepTotal q u r k i := by
  rw [yRepTotal_eq_neg_mulLeft q u hq hr hi hik, yRepTotal_eq_neg_mulLeft q u hq hr hj hjk]
  refine LinearMap.ext fun F => ?_
  simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply, map_neg, neg_neg]
  rw [← mul_assoc, ← mul_assoc, mul_comm (auxVar i : Total L)]

end Rat

end HJO.Sweep
