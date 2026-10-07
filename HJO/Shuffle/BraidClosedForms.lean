/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidMonoid
public import HJO.Shuffle.BraidTrainRelations
public meta import HJO.Attr

/-! # The closed forms of the generators `y_i` and `z_i`

`HJO.Braid.yWord` and `HJO.Braid.zWord` name `y_i` and `z_i` by a recursion that wraps one letter
around each end, `y_{i+1} = T̄_i y_i T̄_i` and `z_{i+1} = T_i z_i T_i`. The lemmas
`HJO.Braid.braidGenY_eq_trainUp_mul_mul_trainDown` and
`HJO.Braid.braidGenZ_eq_trainDown_mul_mul_trainUp` read the resulting palindromes as conjugates of
the rank-one generators by the two trains of `HJO.Braid.trainUp` and `HJO.Braid.trainDown`:

* `y_i = T_{i↗1} y_1 T_{1↘i}`,
* `z_i = T_{i↘1} z_1 T_{1↗i}`.

Both are an induction whose step is one gluing at each end, `HJO.Braid.trainUp_mul_trainUp` and
`HJO.Braid.trainDown_mul_trainDown` applied to the braid system `HJO.Braid.isBraidSystem_braidGenT`
of the images of the `T_i`. They are what makes `HJO.Braid.phiPlusStar` — the homomorphism raising
the index of every `T_i`, `y_i` and `z_i` — determined by its values on `T_i` and `y_1`, `z_1`,
which is the step `HJO.Braid.specialBraid_mul_trainDown_one` needs.

## Main results

* `HJO.Braid.braidGenY_eq_trainUp_mul_mul_trainDown`.
* `HJO.Braid.braidGenZ_eq_trainDown_mul_mul_trainUp`.
* `HJO.Braid.trainUp_self_succ`, `HJO.Braid.trainDown_succ_self` — the two one-letter trains in the
  *forward* direction, `T_{a↗a+1} = T_a` and `T_{a+1↘a} = T_a`. `HJO.Braid.trainUp_succ_self` and
  `HJO.Braid.trainDown_self_succ` are the two that name `Tinv a`; the four together pin the
  boundary of the empty-product convention in both branches of each train.

## Implementation notes

The bound `i ≤ k` is spent only through the gluing lemmas, which need every index of the train
inside the rank; `1 ≤ i` is what makes the recursion of `HJO.Braid.yWord` apply, `y_0` being the
junk empty word. Neither bound is an extra hypothesis.

The trains are the ones formed inside `𝔹_k^+(𝕋_0)` from the images of `HJO.Braid.braidGenT`, which
is `HJO.Braid.braidTrainUp` and `HJO.Braid.braidTrainDown`; the "the trains being those of
the braid system of `HJO.Braid.isBraidSystem_braidGenT`" says exactly that.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*,
Section 5.
-/

@[expose] public section

namespace HJO.Braid

variable {M : Type*} [Monoid M]

/-! ### The one-letter trains in the forward direction -/

/-- `T_{a↗a+1} = T_a`: the first branch of `HJO.Braid.trainUp` at its shortest nonempty range. The
companion `HJO.Braid.trainUp_succ_self` is the second branch, which names `Tinv a`. -/
theorem trainUp_self_succ (T Tinv : ℕ → M) (a : ℕ) : trainUp T Tinv a (a + 1) = T a := by
  simp [trainUp, ascendingWord]

/-- `T_{a+1↘a} = T_a`: the first branch of `HJO.Braid.trainDown` at its shortest nonempty range. The
companion `HJO.Braid.trainDown_self_succ` is the second branch, which names `Tinv a`. -/
theorem trainDown_succ_self (T Tinv : ℕ → M) (a : ℕ) : trainDown T Tinv (a + 1) a = T a := by
  simp [trainDown, descendingWord]

/-! ### The closed forms -/

/-- **Closed form of `z_i`**, `HJO.Braid.braidGenZ_eq_trainDown_mul_mul_trainUp`:
`z_i = T_{i↘1} z_1 T_{1↗i}` in `𝔹_k^+(𝕋_0)` for `1 ≤ i ≤ k`.

Induction on `i`. At `i = 1` both trains are empty. The step reads `z_{i+1} = T_i z_i T_i` off
`HJO.Braid.zWord`, and glues `T_i = T_{i+1↘i}` onto the descending train at the left end and
`T_i = T_{i↗i+1}` onto the ascending train at the right end, by `HJO.Braid.trainDown_mul_trainDown`
and `HJO.Braid.trainUp_mul_trainUp` for the braid system of `HJO.Braid.isBraidSystem_braidGenT`. -/
@[hjo "lem_braid_z_closed"]
theorem braidGenZ_eq_trainDown_mul_mul_trainUp (k : ℕ) :
    ∀ i, 1 ≤ i → i ≤ k →
      braidGenZ k i = braidTrainDown k i 1 * braidGenZ k 1 * braidTrainUp k 1 i := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => intro _; simp
  | succ i hi ih =>
    intro hik
    have ihi := ih (by omega)
    have h := isBraidSystem_braidGenT k
    have hD : braidGenT k i * braidTrainDown k i 1 = braidTrainDown k (i + 1) 1 := by
      have hglue := trainDown_mul_trainDown (T := braidGenT k) (Tinv := braidGenTinv k) h
        (a := i + 1) (b := i) (c := 1) (by omega) hik (by omega) (by omega) (by omega) (by omega)
      rwa [trainDown_succ_self] at hglue
    have hU : braidTrainUp k 1 i * braidGenT k i = braidTrainUp k 1 (i + 1) := by
      have hglue := trainUp_mul_trainUp (T := braidGenT k) (Tinv := braidGenTinv k) h
        (a := 1) (b := i) (c := i + 1) (by omega) (by omega) (by omega) (by omega) (by omega) hik
      rwa [trainUp_self_succ] at hglue
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [braidGenZ_succ, ihi, ← hD, ← hU]
    simp only [mul_assoc]

/-- **Closed form of `y_i`**, `HJO.Braid.braidGenY_eq_trainUp_mul_mul_trainDown`:
`y_i = T_{i↗1} y_1 T_{1↘i}` in `𝔹_k^+(𝕋_0)` for `1 ≤ i ≤ k`.

The same induction as `HJO.Braid.braidGenZ_eq_trainDown_mul_mul_trainUp`, with the two trains
exchanged: `HJO.Braid.yWord` conjugates by `T̄_i` rather than `T_i`, and `T̄_i` is
`T_{i+1↗i}` and `T_{i↘i+1}` — the *second* branch of each train, which is why the ascending train
runs downwards here. -/
@[hjo "lem_braid_y_closed"]
theorem braidGenY_eq_trainUp_mul_mul_trainDown (k : ℕ) :
    ∀ i, 1 ≤ i → i ≤ k →
      braidGenY k i = braidTrainUp k i 1 * braidGenY k 1 * braidTrainDown k 1 i := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => intro _; simp
  | succ i hi ih =>
    intro hik
    have ihi := ih (by omega)
    have h := isBraidSystem_braidGenT k
    have hU : braidGenTinv k i * braidTrainUp k i 1 = braidTrainUp k (i + 1) 1 := by
      have hglue := trainUp_mul_trainUp (T := braidGenT k) (Tinv := braidGenTinv k) h
        (a := i + 1) (b := i) (c := 1) (by omega) hik (by omega) (by omega) (by omega) (by omega)
      rwa [trainUp_succ_self] at hglue
    have hD : braidTrainDown k 1 i * braidGenTinv k i = braidTrainDown k 1 (i + 1) := by
      have hglue := trainDown_mul_trainDown (T := braidGenT k) (Tinv := braidGenTinv k) h
        (a := 1) (b := i) (c := i + 1) (by omega) (by omega) (by omega) (by omega) (by omega) hik
      rwa [trainDown_self_succ] at hglue
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [braidGenY_succ, ihi, ← hU, ← hD]
    simp only [mul_assoc]

/-! ### The orientation of the two trains

The two closed forms differ only by which train stands on which side, and exchanging them would
make each statement false rather than ill-typed. These two check the orientation at `i = 4` against
the words `HJO.Braid.zWord` and `HJO.Braid.yWord` write out by hand: `𝗓_4 = T_3T_2T_1 z_1 T_1T_2T_3`
and `𝗒_4 = T̄_3T̄_2T̄_1 y_1 T̄_1T̄_2T̄_3`, the letters in the order the recursion produces them. -/

/-- `z_4 = T_3T_2T_1 z_1 T_1T_2T_3`: the closed form with both trains written out. -/
theorem braidGenZ_four (k : ℕ) (hk : 4 ≤ k) :
    braidGenZ k 4 = braidGenT k 3 * braidGenT k 2 * braidGenT k 1 * braidGenZ k 1 *
      (braidGenT k 1 * (braidGenT k 2 * braidGenT k 3)) := by
  rw [braidGenZ_eq_trainDown_mul_mul_trainUp k 4 (by omega) hk,
    show braidTrainDown k 4 1 = braidGenT k 3 * braidGenT k 2 * braidGenT k 1 from
      trainDown_four_one _ _,
    show braidTrainUp k 1 4 = braidGenT k 1 * braidGenT k 2 * braidGenT k 3 from
      trainUp_one_four _ _]
  simp only [mul_assoc]

/-- `y_4 = T̄_3T̄_2T̄_1 y_1 T̄_1T̄_2T̄_3`: the closed form with both trains written out. The
trains are the *second* branch of each definition here, so `T_{4↗1}` descends through the inverses
and `T_{1↘4}` ascends through them. -/
theorem braidGenY_four (k : ℕ) (hk : 4 ≤ k) :
    braidGenY k 4 = braidGenTinv k 3 * braidGenTinv k 2 * braidGenTinv k 1 * braidGenY k 1 *
      (braidGenTinv k 1 * (braidGenTinv k 2 * braidGenTinv k 3)) := by
  rw [braidGenY_eq_trainUp_mul_mul_trainDown k 4 (by omega) hk,
    show braidTrainUp k 4 1 = braidGenTinv k 3 * braidGenTinv k 2 * braidGenTinv k 1 by
      simp [trainUp, descendingWord, List.range', mul_assoc],
    show braidTrainDown k 1 4 = braidGenTinv k 1 * braidGenTinv k 2 * braidGenTinv k 3 by
      simp [trainDown, ascendingWord, List.range', mul_assoc]]
  simp only [mul_assoc]

end HJO.Braid
