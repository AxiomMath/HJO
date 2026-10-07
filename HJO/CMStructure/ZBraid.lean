/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.DminusBraid
public import HJO.CMStructure.StarEasy
public import HJO.Shuffle.BraidRep
public import HJO.Shuffle.BraidTrainRelations

/-! # The `z` operators against the braid letters

This file is the `z`-half of `HJO.Sweep.braidRepRespects_mellit`, which is
Mellit's Proposition 5.3. Of its five clauses — the five relation families
`HJO.Braid.BraidMonoid` imposes beyond the braid system itself — the one settled here is
`z_iT_j = T_jz_i`, at the exact index range
`HJO.Braid.BraidMonoid` imposes it on: `1 ≤ i ≤ k`, `1 ≤ j ≤ k-1`, `i \notin \{j, j+1\}`.
`HJO.Sweep.zRepTotal_mul_braidEnd` is that clause on the representation, so the field
`BraidRepResidualTotal.zRepTotal_comm_T` holds outright.

## The mechanism at `i = 1`: two index shifts that cancel

`d^*_+` raises the index of a braid letter and `d_-` leaves it alone, so their commutator raises:

* `HJO.Sweep.dplusStar_braid`: `d^*_+T_i = T_{i+1}d^*_+` for `1 ≤ i < k`.
* `HJO.Sweep.dminus_braid` (`HJO.Sweep.dminusCM_braid`): `d_-T_i = T_id_-` for `1 ≤ i ≤ k-2`.
* Hence `HJO.Sweep.starComm_mul_braidEnd`: `[d^*_+, d_-]T_j = T_{j+1}[d^*_+, d_-]` for
  `1 ≤ j ≤ k-2`, that range being the intersection of the two above and not slack at either end.

`z_1` is that commutator followed by a train of braid letters, and the train has to undo the shift.
The word that undoes it is the one whose conjugation *lowers*, and that is the inverse of the
**ascending** train `T_1T_2 \cdots T_{k-1}`: `HJO.Braid.trainUp_mul_gen` says
`T_{1↗k}T_i = T_{i+1}T_{1↗k}`, so its inverse `T_{k↗1}` satisfies `T_{k↗1}T_{i+1} = T_iT_{k↗1}`.
That word is Mellit's `T^*_{k↘1}`, and composing the two shifts gives commutation at `2 ≤ j ≤ k-1`
— exactly the range `1 \notin \{j, j+1\}`, `1 ≤ j ≤ k-1` of `HJO.Braid.BraidMonoid`.

## The word in `HJO.Sweep.zop` is load-bearing, and the wrong one is kept as the witness

`HJO.Sweep.zopOneStar` — the operator `HJO.Sweep.zop` is built on — carries the train
`T^*_{k↘1} = T_{k-1}^{-1}T_{k-2}^{-1} \cdots T_1^{-1}`, which is `HJO.Sweep.trainUpEnd q k 1` under
the translation rule `HJO.Braid.trainUp_inv_eq_trainDown` records: a starred
Mellit symbol is the *other* train, not the inverse of the same one. Reading the train of
`HJO.Sweep.zop` instead as `T^{-1}_{k↘1}`, the reverse word `T_1^{-1} \cdots T_{k-1}^{-1}`, gives
`HJO.Sweep.zopOne`. That is not a variant spelling:

* `HJO.Sweep.trainDownEnd_mul_braidEnd` says the reverse word *raises* the index, as the commutator
  does, so with it the two shifts add: `HJO.Sweep.zopOne_mul_braidEnd` is `z_1T_j = T_{j+2}z_1`, and
  the relation `HJO.Braid.BraidMonoid` demands of `z_1` is not what comes out.
* `HJO.Sweep.trainUpEnd_mul_braidEnd` says Mellit's word lowers it, and the shifts cancel.

`HJO.Sweep.zopOne` exists for exactly that one theorem; nothing else uses it.

There is a second, independent check that Mellit's reading is the intended one, and it does not
depend on any of this. His `z_1` is Carlsson and Mellit's own `y_1` — their
`y_1 = 1/(q^{k-1}(q-1)) (d_+d_- - d_-d_+) T_{k↘1}` — read in the conjugate algebra, where
`q` becomes `q^{-1}`, `d_+` becomes `d^*_+` and each `T_i` becomes `T_i^{-1}`. Substituting
`q^{-1}` for `q` in the scalar gives `q^k/(1-q)`, which is Mellit's prefactor on the nose. And the
train `T_{k↘1} = T_{k-1} \cdots T_1` of the *conjugate* braid system is
`T_{k-1}^{-1} \cdots T_1^{-1}` — the descending train of the inverted letters, not the inverse of
the descending train. That is Mellit's `T^*_{k↘1}` again. The unstarred formula is the sanity check
on the direction: there `T_{k↘1}` is the lowering word, and `y_1` — multiplication by `y_1`, which
commutes with every `T_j` for `j ≥ 2` — comes out commuting for the same reason `z_1` does here.

## From `i = 1` to general `i`

`HJO.Sweep.zop`'s recursion is `z_{i+1} = q^{-1}T_iz_iT_i`, and unwinding it gives the closed form
`HJO.Sweep.zop_eq_conj`: `z_{i+1} = q^{-i}T_{i+1↘1}z_1T_{1↗i+1}`, a conjugation of `z_1` by a pair
of trains in the letters `T_1, \dots, T_i`. Against that form the relation splits into the two
halves the presentation's side condition leaves open, and *neither* is an induction on the recursion
— a direct induction cannot work, because the step from `i` to `i+1` needs the relation at `j = i-1`
and the hypothesis forbids exactly that index:

* `j > i`: the letter is far from every letter of both trains, so it commutes with them
  (`HJO.Braid.trainUp_far_comm`, `HJO.Braid.trainDown_far_comm`), and with `z_1` because `j ≥ 2`.
* `j + 1 < i`: the ascending train raises the letter's index (`HJO.Braid.trainUp_mul_gen`), `z_1`
  passes `T_{j+1}` because `j + 1 ≥ 2`, and the descending train lowers it back
  (`HJO.Sweep.trainDownEnd_pos_mul_braidEnd`). The two shifts cancel here too.

Together they cover `j \ne i` and `j + 1 \ne i`, which is the side condition exactly — the case
`j = i` and the case `j = i - 1` are the two the relation does not claim.

## Main results

* `HJO.Sweep.starComm`, `HJO.Sweep.starComm_mul_braidEnd`: the commutator and its index shift.
* `HJO.Sweep.trainUpEnd_mul_braidEnd`, `HJO.Sweep.trainDownEnd_mul_braidEnd`,
  `HJO.Sweep.trainDownEnd_pos_mul_braidEnd`: the trains against a braid letter.
* `HJO.Sweep.zopOneStar_mul_braidEnd`: `z_1T_j = T_jz_1` for `2 ≤ j ≤ k-1`.
* `HJO.Sweep.zop_eq_conj`, `HJO.Sweep.zop_mul_braidEnd`: the closed form and the full clause
  `z_iT_j = T_jz_i` of `HJO.Braid.BraidMonoid`.
* `HJO.Sweep.zRepTotal_eq_smul_zop`, `HJO.Sweep.zRepTotal_mul_braidEnd`: the clause on the
  representation, one of the nine families `HJO.Sweep.braidRepRespects_of_residual` discharges.
* `HJO.Sweep.zopOne_mul_braidEnd`: what the other word gives instead.

## References

A. Mellit, *Toric braids and `(m,n)`-parking functions*, §3.6 and §5.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-- `HJO.Sweep.dplusStar_braid` in the endomorphism monoid: `d^*_+T_i = T_{i+1}d^*_+` for
`1 ≤ i < k`. -/
theorem dplusStar_mul_braidEnd (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i < k) :
    dplusStar q u k * braidEnd q i = braidEnd q (i + 1) * dplusStar q u k :=
  LinearMap.ext fun F => dplusStar_braid q u hi hik F

/-! ### Single-letter trains

The two boundary readings of `HJO.Braid.trainUp` and `HJO.Braid.trainDown` at which a train is one
letter of the *uninverted* system. They are what turns the recursion `z_{i+1} = q^{-1}T_iz_iT_i`
into a statement about trains, through the gluing lemmas `HJO.Braid.trainUp_mul_trainUp` and
`HJO.Braid.trainDown_mul_trainDown`. -/

/-- `T_{a↗a+1}` is the single letter `T_a`. -/
theorem trainUpEnd_self_succ (q : L) (a : ℕ) : trainUpEnd q a (a + 1) = braidEnd q a := by
  simp [trainUpEnd, Braid.trainUp, Braid.ascendingWord]

/-- `T_{a+1↘a}` is the single letter `T_a`. -/
theorem trainDownEnd_succ_self (q : L) (a : ℕ) : trainDownEnd q (a + 1) a = braidEnd q a := by
  simp [trainDownEnd, Braid.trainDown, Braid.descendingWord]

/-! ### The trains against a braid letter -/

/-- **The inverse of the ascending train lowers the index of a braid letter**:
`T_{k↗1}T_{i+1} = T_iT_{k↗1}` for `1 ≤ i` and `i + 1 < k`.

`HJO.Braid.trainUp_mul_gen` is `T_{1↗k}T_i = T_{i+1}T_{1↗k}`, and
`HJO.Braid.conj_swap` reads that conjugation from the other side, `T_{k↗1}` being the inverse of
`T_{1↗k}` by `HJO.Braid.trainUp_mul_trainUp_self`. -/
theorem trainUpEnd_mul_braidEnd (q : L) (hq : q ≠ 0) {i k : ℕ} (hi : 1 ≤ i) (hik : i + 1 < k) :
    trainUpEnd q k 1 * braidEnd q (i + 1) = braidEnd q i * trainUpEnd q k 1 := by
  have hbs := isBraidSystem_braidEnd q hq k
  refine (Braid.conj_swap (w := trainUpEnd q 1 k) (w' := trainUpEnd q k 1) ?_ ?_ ?_).symm
  · exact Braid.trainUp_mul_trainUp_self hbs le_rfl (by omega) (by omega) le_rfl
  · exact Braid.trainUp_mul_trainUp_self hbs (by omega) le_rfl le_rfl (by omega)
  · exact Braid.trainUp_mul_gen hbs le_rfl hi hik le_rfl

/-- **The inverse of the descending train raises the index of a braid letter**:
`T_{1↘k}T_i = T_{i+1}T_{1↘k}` for `1 ≤ i` and `i + 1 < k`.

`HJO.Sweep.trainDownEnd q 1 k` is the ascending train of the *inverted* braid system by
`HJO.Braid.trainUp_inv_eq_trainDown`, and the inverted pair is a braid system by
`HJO.Braid.IsBraidSystem.inverses`, so `HJO.Braid.trainUp_mul_gen_inv` applies to it and shifts the
uninverted letter upwards. -/
theorem trainDownEnd_mul_braidEnd (q : L) (hq : q ≠ 0) {i k : ℕ} (hi : 1 ≤ i) (hik : i + 1 < k) :
    trainDownEnd q 1 k * braidEnd q i = braidEnd q (i + 1) * trainDownEnd q 1 k := by
  have hbs := (isBraidSystem_braidEnd q hq k).inverses
  have hdual : trainDownEnd q 1 k = Braid.trainUp (braidInvEnd q) (braidEnd q) 1 k :=
    (Braid.trainUp_inv_eq_trainDown (braidEnd q) (braidInvEnd q) 1 k).symm
  rw [hdual]
  exact Braid.trainUp_mul_gen_inv hbs le_rfl hi hik le_rfl

/-- **The descending train in the uninverted letters lowers the index of a braid letter**:
`T_{k↘1}T_{i+1} = T_iT_{k↘1}` for `1 ≤ i` and `i + 1 < k`.

`T_{k↘1} = T_{k-1} \cdots T_1` is the two-sided inverse of `T_{1↘k}` by
`HJO.Braid.trainDown_mul_trainDown_self`, so this is
`HJO.Sweep.trainDownEnd_mul_braidEnd` read from the other side through `HJO.Braid.conj_swap` — the
one train that appears in `HJO.Sweep.zop_eq_conj` and in none of the operators above it. -/
theorem trainDownEnd_pos_mul_braidEnd (q : L) (hq : q ≠ 0) {i k : ℕ} (hi : 1 ≤ i)
    (hik : i + 1 < k) :
    trainDownEnd q k 1 * braidEnd q (i + 1) = braidEnd q i * trainDownEnd q k 1 := by
  have hbs := isBraidSystem_braidEnd q hq k
  refine (Braid.conj_swap (w := trainDownEnd q 1 k) (w' := trainDownEnd q k 1) ?_ ?_ ?_).symm
  · exact Braid.trainDown_mul_trainDown_self hbs le_rfl (by omega) (by omega) le_rfl
  · exact Braid.trainDown_mul_trainDown_self hbs (by omega) le_rfl le_rfl (by omega)
  · exact trainDownEnd_mul_braidEnd q hq hi hik

end Field

/-! ### The commutator and its index shift -/

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The commutator `d^*_+d_- - d_-d^*_+` on `V_k`, the operator that `HJO.Sweep.zop` scales by
`q^k/(1-q)` before appending the train. It is named
only so that its index shift can be stated once and used by both `HJO.Sweep.zopOneStar` and
`HJO.Sweep.zopOne`. The indices record the graded piece each factor is read on, exactly as in
`HJO.Sweep.zopOneStar`. -/
noncomputable def starComm (q u : L) (k : ℕ) : Module.End L (Total L) :=
  dplusStar q u (k - 1) * dminus q k - dminus q (k + 1) * dplusStar q u k

/-- `HJO.Sweep.zopOneStar` is the commutator followed by Mellit's train, scaled. -/
theorem zopOneStar_eq (q u : L) (k : ℕ) :
    zopOneStar q u k = (q ^ k / (1 - q)) • (starComm q u k * trainUpEnd q k 1) := rfl

/-- `HJO.Sweep.zopOne` is the commutator followed by the reverse train, scaled. -/
theorem zopOne_eq (q u : L) (k : ℕ) :
    zopOne q u k = (q ^ k / (1 - q)) • (starComm q u k * trainDownEnd q 1 k) := rfl

/-- The commutator at a successor index, with no truncated subtraction. -/
theorem starComm_add_two (q u : L) (m : ℕ) :
    starComm q u (m + 2)
      = dplusStar q u (m + 1) * dminus q (m + 2) - dminus q (m + 3) * dplusStar q u (m + 2) := rfl

/-- **The commutator of the starred arrow with the lowering operator raises the index of a braid
letter**: `[d^*_+, d_-]T_j = T_{j+1}[d^*_+, d_-]` on `V_{k}` for `1 ≤ j ≤ k-2`, written here at
`k = m + 2` so that the range reads `1 ≤ j ≤ m`.

Each of the two summands shifts on its own. In `d^*_+d_-` the lowering operator passes `T_j`
unchanged (`HJO.Sweep.dminus_braid`, needing `j ≤ k-2`) and the starred arrow then raises it
(`HJO.Sweep.dplusStar_braid`, needing `j < k-1`); in `d_-d^*_+` the starred arrow raises first
(needing `j < k`) and the lowering operator passes `T_{j+1}` unchanged (needing `j+1 ≤ k-2`). The
binding constraint is `j ≤ k-2` and it appears twice, once from each summand. -/
theorem starComm_mul_braidEnd (q u : L) {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) :
    starComm q u (m + 2) * braidEnd q j = braidEnd q (j + 1) * starComm q u (m + 2) := by
  have hA : dplusStar q u (m + 1) * dminus q (m + 2) * braidEnd q j
      = braidEnd q (j + 1) * (dplusStar q u (m + 1) * dminus q (m + 2)) := by
    rw [mul_assoc, dminus_mul_braidEnd q hjm, ← mul_assoc,
      dplusStar_mul_braidEnd q u hj (by omega), mul_assoc]
  have hB : dminus q (m + 3) * dplusStar q u (m + 2) * braidEnd q j
      = braidEnd q (j + 1) * (dminus q (m + 3) * dplusStar q u (m + 2)) := by
    rw [mul_assoc, dplusStar_mul_braidEnd q u hj (by omega), ← mul_assoc,
      dminus_mul_braidEnd q (show j + 1 ≤ m + 1 by omega), mul_assoc]
  rw [starComm_add_two, sub_mul, mul_sub, hA, hB]

/-! ### `z_1` against a braid letter, with each of the two candidate trains -/

/-- **`z_1T_j = T_jz_1` for `2 ≤ j ≤ k-1`.** This is the clause `z_iT_j = T_jz_i` of
`HJO.Braid.BraidMonoid` at `i = 1`, where the side condition `1 \notin \{j, j+1\}` together with
`1 ≤ j ≤ k-1` is exactly `2 ≤ j ≤ k-1`.

The train lowers the index (`HJO.Sweep.trainUpEnd_mul_braidEnd`) by precisely the one step the
commutator raises it (`HJO.Sweep.starComm_mul_braidEnd`), and the two cancel. -/
theorem zopOneStar_mul_braidEnd (q u : L) (hq : q ≠ 0) {k j : ℕ} (hj : 2 ≤ j) (hjk : j + 1 ≤ k) :
    zopOneStar q u k * braidEnd q j = braidEnd q j * zopOneStar q u k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [zopOneStar_eq, smul_mul_assoc, mul_smul_comm, mul_assoc,
    trainUpEnd_mul_braidEnd q hq (by omega) (by omega), ← mul_assoc,
    starComm_mul_braidEnd q u (by omega) (by omega), mul_assoc]

/-- **What the other word gives instead: `z_1T_j = T_{j+2}z_1`.** With
`T^{-1}_{k↘1} = T_1^{-1} \cdots T_{k-1}^{-1}` the train *raises* the index
(`HJO.Sweep.trainDownEnd_mul_braidEnd`) and so does the commutator, so the two shifts add rather
than cancel and the relation `z_1T_j = T_jz_1` of `HJO.Braid.BraidMonoid` is not what comes out.

Stated at `k = m + 2` with `1 ≤ j` and `j + 1 ≤ m`, the range on which both shifts are available.
This shows that reading the train of `HJO.Sweep.zop` as the reverse word is not a harmless variant
spelling, and it is the only use of `HJO.Sweep.zopOne`. -/
theorem zopOne_mul_braidEnd (q u : L) (hq : q ≠ 0) {m j : ℕ} (hj : 1 ≤ j) (hjm : j + 1 ≤ m) :
    zopOne q u (m + 2) * braidEnd q j = braidEnd q (j + 2) * zopOne q u (m + 2) := by
  rw [zopOne_eq, smul_mul_assoc, mul_smul_comm, mul_assoc,
    trainDownEnd_mul_braidEnd q hq hj (by omega), ← mul_assoc,
    starComm_mul_braidEnd q u (show 1 ≤ j + 1 by omega) hjm, mul_assoc]

/-! ### General `i`: the closed form and the relation -/

/-- **`z_{i+1}` is `z_1` conjugated by a pair of trains**: unwinding `HJO.Sweep.zop`'s recursion
`z_{i+1} = q^{-1}T_iz_iT_i` gives `z_{i+1} = q^{-i}T_{i+1↘1}z_1T_{1↗i+1}` on `V_k`, for
`i + 1 ≤ k`.

The step is the two gluing lemmas read backwards: `T_{i+2↘1} = T_{i+1}T_{i+1↘1}` by
`HJO.Braid.trainDown_mul_trainDown` and `T_{1↗i+2} = T_{1↗i+1}T_{i+1}` by
`HJO.Braid.trainUp_mul_trainUp`, the single-letter trains being `HJO.Sweep.trainDownEnd_succ_self`
and `HJO.Sweep.trainUpEnd_self_succ`. -/
theorem zop_eq_conj (q u : L) (hq : q ≠ 0) {k : ℕ} : ∀ i, i + 1 ≤ k →
    zop q u k (i + 1)
      = (q ^ i)⁻¹ • (trainDownEnd q (i + 1) 1 * zopOneStar q u k * trainUpEnd q 1 (i + 1)) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [zop_one, trainDownEnd, trainUpEnd, Braid.trainDown_self, Braid.trainUp_self]
  | succ i ih =>
    intro hik
    have hbs := isBraidSystem_braidEnd q hq k
    have hD : trainDownEnd q (i + 2) 1 = braidEnd q (i + 1) * trainDownEnd q (i + 1) 1 := by
      rw [← trainDownEnd_succ_self q (i + 1)]
      exact (Braid.trainDown_mul_trainDown hbs (show 1 ≤ i + 2 by omega) (by omega)
        (show 1 ≤ i + 1 by omega) (by omega) le_rfl (by omega)).symm
    have hU : trainUpEnd q 1 (i + 2) = trainUpEnd q 1 (i + 1) * braidEnd q (i + 1) := by
      rw [← trainUpEnd_self_succ q (i + 1)]
      exact (Braid.trainUp_mul_trainUp hbs le_rfl (by omega) (show 1 ≤ i + 1 by omega) (by omega)
        (show 1 ≤ i + 2 by omega) (by omega)).symm
    have hscal : (q ^ (i + 1))⁻¹ = q⁻¹ * (q ^ i)⁻¹ := by rw [pow_succ, mul_inv, mul_comm]
    rw [show i + 1 + 1 = i + 2 from rfl, zop_succ, ih (by omega), hD, hU, hscal]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]

/-- **`z_iT_j = T_jz_i`**, the clause of `HJO.Braid.BraidMonoid` in full: for `1 ≤ i ≤ k`,
`1 ≤ j ≤ k-1` and `i \notin \{j, j+1\}`, the operator `z_i` of `HJO.Sweep.zop` commutes with the
braid operator `T_j` of `HJO.Sweep.braid`.

Read on the closed form `HJO.Sweep.zop_eq_conj`, the side condition splits into the two halves the
module docstring describes, and the excluded indices `j = i` and `j = i - 1` are the two on which
the argument — and the relation — say nothing. -/
theorem zop_mul_braidEnd (q u : L) (hq : q ≠ 0) {k i j : ℕ} (hi : 1 ≤ i) (hik : i ≤ k)
    (hj : 1 ≤ j) (hjk : j + 1 ≤ k) (hne : i ≠ j) (hne' : i ≠ j + 1) :
    zop q u k i * braidEnd q j = braidEnd q j * zop q u k i := by
  have hbs := isBraidSystem_braidEnd q hq k
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [zop_eq_conj q u hq i (by omega), smul_mul_assoc, mul_smul_comm]
  refine congrArg _ ?_
  set D := trainDownEnd q (i + 1) 1
  set U := trainUpEnd q 1 (i + 1)
  set Z := zopOneStar q u k
  rcases show i + 1 < j ∨ j + 1 < i + 1 by omega with hlt | hlt
  · have hU : U * braidEnd q j = braidEnd q j * U :=
      (Braid.trainUp_far_comm hbs hj hjk le_rfl (by omega) (by omega) (by omega) (by omega)).symm
    have hD : D * braidEnd q j = braidEnd q j * D :=
      (Braid.trainDown_far_comm hbs hj hjk (by omega) (by omega) le_rfl (by omega)
        (by omega)).symm
    have hZ : Z * braidEnd q j = braidEnd q j * Z :=
      zopOneStar_mul_braidEnd q u hq (by omega) hjk
    calc D * Z * U * braidEnd q j = D * Z * (U * braidEnd q j) := mul_assoc _ _ _
      _ = D * (Z * braidEnd q j) * U := by rw [hU]; simp only [mul_assoc]
      _ = D * braidEnd q j * (Z * U) := by rw [hZ]; simp only [mul_assoc]
      _ = braidEnd q j * (D * Z * U) := by rw [hD]; simp only [mul_assoc]
  · have hU : U * braidEnd q j = braidEnd q (j + 1) * U :=
      Braid.trainUp_mul_gen hbs le_rfl hj (by omega) (by omega)
    have hD : D * braidEnd q (j + 1) = braidEnd q j * D :=
      trainDownEnd_pos_mul_braidEnd q hq hj (by omega)
    have hZ : Z * braidEnd q (j + 1) = braidEnd q (j + 1) * Z :=
      zopOneStar_mul_braidEnd q u hq (by omega) (by omega)
    calc D * Z * U * braidEnd q j = D * Z * (U * braidEnd q j) := mul_assoc _ _ _
      _ = D * (Z * braidEnd q (j + 1)) * U := by rw [hU]; simp only [mul_assoc]
      _ = D * braidEnd q (j + 1) * (Z * U) := by rw [hZ]; simp only [mul_assoc]
      _ = braidEnd q j * (D * Z * U) := by rw [hD]; simp only [mul_assoc]

/-! ### The clause on the representation -/

/-- **`π_k` sends the generator `z_i` to `(qu)^{-1}z_i`, for `1 ≤ i ≤ k`.** At `i = 1` this is the
assignment `HJO.Sweep.braidRepLetterTotal` makes; the induction is that
`HJO.Sweep.zRepTotal_succ` — the recursion the word `𝗓_{i+1} = T_i𝗓_iT_i` forces on the
operators — is `HJO.Sweep.zop`'s own recursion `z_{i+1} = q^{-1}T_iz_iT_i`, with the same scalar,
so the two families differ by the constant `(qu)^{-1}` at every index. -/
theorem zRepTotal_eq_smul_zop (q u : L) {r : L} (hr : r * r = q) {k : ℕ} (i : ℕ) (hi : 1 ≤ i)
    (hik : i ≤ k) : zRepTotal q u r k i = (q * u)⁻¹ • zop q u k i := by
  induction i with
  | zero => omega
  | succ i ih =>
    rcases i with _ | i
    · exact zRepTotal_one q u r (by omega)
    · rw [zRepTotal_succ q u hr (show i + 1 + 1 ≤ k by omega), ih (by omega) (by omega),
        show i + 1 + 1 = i + 2 from rfl, zop_succ]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

/-- **`HJO.Sweep.braidRepRespects_mellit`'s `z`-commutation clause**, one of the nine families
`HJO.Sweep.braidRepRespects_of_residual` discharges: the image of `z_i` commutes with the image of
`T_j` for `1 ≤ i ≤ k`, `1 ≤ j ≤ k-1` and `i \notin \{j, j+1\}`. The `q^{1/2}` normalisation
cancels — both images are scalar multiples of `HJO.Sweep.zop` and `HJO.Sweep.braidEnd` — so this is
`HJO.Sweep.zop_mul_braidEnd` with the scalars pulled through. -/
theorem zRepTotal_mul_braidEnd (q u : L) {r : L} (hq : q ≠ 0) (hr : r * r = q) {k i j : ℕ}
    (hi : 1 ≤ i) (hik : i ≤ k) (hj : 1 ≤ j) (hjk : j + 1 ≤ k) (hne : i ≠ j) (hne' : i ≠ j + 1) :
    zRepTotal q u r k i * braidEnd q j = braidEnd q j * zRepTotal q u r k i := by
  rw [zRepTotal_eq_smul_zop q u hr i hi hik, smul_mul_assoc, mul_smul_comm,
    zop_mul_braidEnd q u hq hi hik hj hjk hne hne']

end Newton

end HJO.Sweep
