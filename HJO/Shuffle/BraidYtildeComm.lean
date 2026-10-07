/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidMoveComm
public import HJO.Shuffle.BraidPhiInsert
public meta import HJO.Attr

/-! # The commuting lifts against the braid generators

`HJO.Braid.BraidMonoid` carries `𝗓_i T_j = T_j 𝗓_i` for `i ∉ {j, j + 1}` as a relation, and
`HJO.Braid.braidYtilde`'s `ỹ_i` has no such relation. This file proves the `ỹ`-form as a theorem, in
full generality, from the relations.

## Main results

* `HJO.Braid.braidYtilde_comm_T` — `ỹ_a T_j = T_j ỹ_a` for `1 ≤ a ≤ k`, `1 ≤ j ≤ k - 1` and
  `a ∉ {j, j + 1}`: the `ỹ`-analogue of `HJO.Braid.braidGenZ_comm_T`, with exactly the hypotheses
  that relation carries.
* `HJO.Braid.braidYtilde_comm_trainDown`, `HJO.Braid.braidYtilde_comm_trainUp` — the same against a
  whole train whose letters are all far from `a`, the `ỹ`-analogues of
  `HJO.Braid.braidGenZ_comm_trainDown` and `HJO.Braid.braidGenZ_comm_trainUp`.

## Implementation notes

### Two configurations, and only the far one is a far commutation

`HJO.Braid.braidTrainDown_mul_braidYtilde` puts `ỹ_a` in the form `T_{a↘1} ỹ_1 T_{1↗a}`
(`HJO.Braid.braidYtilde_eq_trainDown_one_mul`), whose two trains read the indices `1, …, a - 1`,
and `HJO.Braid.braidYtilde_one_comm_gen` already commutes `ỹ_1` past every `T_j` with `j ≥ 2`. The
hypothesis `a ∉ {j, j + 1}` leaves two cases.

*Above.* `a < j`. Every letter of both trains is at distance at least two from `T_j`, so
`HJO.Braid.trainDown_far_comm` and `HJO.Braid.trainUp_far_comm` carry `T_j` across each train
untouched, and `HJO.Braid.braidYtilde_one_comm_gen` carries it across the middle factor. Three
commutations.

*Below.* `j + 2 ≤ a`. Here `T_j` is **not** far from the trains — `T_{1↗a}` reads `T_j` itself —
and no commutation is available. What happens instead is a shift: `HJO.Braid.trainUp_mul_gen` turns
`T_{1↗a} T_j` into `T_{j+1} T_{1↗a}`, the raised letter is still at index `≥ 2` so
`HJO.Braid.braidYtilde_one_comm_gen` applies to it, and
`HJO.Braid.trainDown_one_mul_gen` lowers it back to `T_j` on the far side of `T_{a↘1}`. The
letter that comes out is the one that went in, which is why the statement is a commutation and not
a shift, but the proof passes through `T_{j+1}`.

The case `a = j` and the case `a = j + 1` are both genuinely excluded: at those indices the
hypothesis of `HJO.Braid.trainUp_mul_gen` fails and `T_j` is adjacent to the top letter of the
trains.

### No hypothesis beyond the rank bounds

Everything here lives in `BraidMonoid k`; no field, no representation, and no condition on the
data of `HJO.Braid.specialBraid`. The bounds are the ones `HJO.Braid.braidGenZ_comm_T` carries.

## References

This file concerns `HJO.Braid.BraidMonoid`, `HJO.Braid.braidGenT`, `HJO.Braid.braidYtilde`,
`HJO.Braid.braidTrainDown_mul_braidYtilde`, `HJO.Braid.trainUp_mul_gen`,
`HJO.Braid.trainUp_far_comm`, `HJO.Braid.trainDown_far_comm` and
`HJO.Braid.braidGenY_eq_trainUp_mul_mul_trainDown`. A. Mellit, *Toric braids and `(m, n)`-parking
functions*, section 5 (the braid monoid).
-/

@[expose] public section

namespace HJO.Braid

variable {k : ℕ}

/-! ### `ỹ_a` against one generator -/

/-- **`ỹ_a T_j = T_j ỹ_a` for `a ∉ {j, j + 1}`**, the `ỹ`-analogue of `HJO.Braid.BraidMonoid`'s
`𝗓_i T_j = T_j 𝗓_i`. It is not a relation of the presentation and it is proved here from the
relations; see the module docstring for the two configurations. -/
@[hjo "lem_braid_ytilde_comm_T"]
theorem braidYtilde_comm_T {a j : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hj : 1 ≤ j) (hjk : j + 1 ≤ k)
    (hne : a ≠ j) (hne' : a ≠ j + 1) :
    braidYtilde k a * braidGenT k j = braidGenT k j * braidYtilde k a := by
  have hsys := isBraidSystem_braidGenT k
  rw [braidYtilde_eq_trainDown_one_mul ha hak]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `a < j`: `T_j` is far from every letter of both trains.
    have hD : braidTrainDown k a 1 * braidGenT k j = braidGenT k j * braidTrainDown k a 1 :=
      (trainDown_far_comm hsys hj hjk ha hak le_rfl (by omega) (by right; omega)).symm
    have hU : braidTrainUp k 1 a * braidGenT k j = braidGenT k j * braidTrainUp k 1 a :=
      (trainUp_far_comm hsys hj hjk le_rfl (by omega) ha hak (by right; omega)).symm
    have hY : braidYtilde k 1 * braidGenT k j = braidGenT k j * braidYtilde k 1 := by
      obtain ⟨r, rfl⟩ : ∃ r, j = r + 1 := ⟨j - 1, by omega⟩
      exact braidYtilde_one_comm_gen (by omega) (by omega)
    calc braidTrainDown k a 1 * braidYtilde k 1 * braidTrainUp k 1 a * braidGenT k j
        = braidTrainDown k a 1 * braidYtilde k 1 * (braidTrainUp k 1 a * braidGenT k j) := by
          simp only [mul_assoc]
      _ = braidTrainDown k a 1 * (braidYtilde k 1 * braidGenT k j) * braidTrainUp k 1 a := by
          rw [hU]; simp only [mul_assoc]
      _ = braidTrainDown k a 1 * braidGenT k j * (braidYtilde k 1 * braidTrainUp k 1 a) := by
          rw [hY]; simp only [mul_assoc]
      _ = braidGenT k j * (braidTrainDown k a 1 * braidYtilde k 1 * braidTrainUp k 1 a) := by
          rw [hD]; simp only [mul_assoc]
  · -- `j + 2 ≤ a`: the letter shifts up through the ascending train and back down through the
    -- descending one.
    have hja : j + 2 ≤ a := by omega
    have hU : braidTrainUp k 1 a * braidGenT k j = braidGenT k (j + 1) * braidTrainUp k 1 a :=
      trainUp_mul_gen hsys le_rfl hj (by omega) hak
    have hY : braidYtilde k 1 * braidGenT k (j + 1) = braidGenT k (j + 1) * braidYtilde k 1 :=
      braidYtilde_one_comm_gen hj (by omega)
    have hD : braidTrainDown k a 1 * braidGenT k (j + 1) = braidGenT k j * braidTrainDown k a 1 :=
      trainDown_one_mul_gen hsys hj hja hak
    calc braidTrainDown k a 1 * braidYtilde k 1 * braidTrainUp k 1 a * braidGenT k j
        = braidTrainDown k a 1 * braidYtilde k 1 * (braidTrainUp k 1 a * braidGenT k j) := by
          simp only [mul_assoc]
      _ = braidTrainDown k a 1 * (braidYtilde k 1 * braidGenT k (j + 1)) * braidTrainUp k 1 a := by
          rw [hU]; simp only [mul_assoc]
      _ = braidTrainDown k a 1 * braidGenT k (j + 1) * (braidYtilde k 1 * braidTrainUp k 1 a) := by
          rw [hY]; simp only [mul_assoc]
      _ = braidGenT k j * (braidTrainDown k a 1 * braidYtilde k 1 * braidTrainUp k 1 a) := by
          rw [hD]; simp only [mul_assoc]

/-! ### `ỹ_a` against a whole train -/

/-- `ỹ_a` commutes with a descending train all of whose letters are far from `a`, the `ỹ`-analogue
of `HJO.Braid.braidGenZ_comm_trainDown`. -/
theorem braidYtilde_comm_trainDown {a c d : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hc : 1 ≤ c)
    (hck : c ≤ k) (hd : 1 ≤ d) (hdk : d ≤ k) (hfar : a + 1 ≤ min c d ∨ max c d + 1 ≤ a) :
    braidYtilde k a * braidTrainDown k c d = braidTrainDown k c d * braidYtilde k a :=
  (isBraidSystem_braidGenT k).comm_trainDown hc hck hd hdk fun j _ _ =>
    braidYtilde_comm_T ha hak (by omega) (by omega) (by omega) (by omega)

/-- `ỹ_a` commutes with an ascending train all of whose letters are far from `a`, the `ỹ`-analogue
of `HJO.Braid.braidGenZ_comm_trainUp`. -/
theorem braidYtilde_comm_trainUp {a c d : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hc : 1 ≤ c)
    (hck : c ≤ k) (hd : 1 ≤ d) (hdk : d ≤ k) (hfar : a + 1 ≤ min c d ∨ max c d + 1 ≤ a) :
    braidYtilde k a * braidTrainUp k c d = braidTrainUp k c d * braidYtilde k a :=
  (isBraidSystem_braidGenT k).comm_trainUp hc hck hd hdk fun j _ _ =>
    braidYtilde_comm_T ha hak (by omega) (by omega) (by omega) (by omega)

end HJO.Braid
