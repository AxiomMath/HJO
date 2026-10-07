/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidClosedForms
public meta import HJO.Attr

/-! # The two train rules

Mellit's Section 5 moves a train past a generator by *changing the generator's index to the train's
own upper index*: for every `1 ≤ a, b ≤ k`,

* `T_{a↘b} z_b = z_a T_{a↗b}`, the `T`–`z` rule,
* `T_{a↘b} ỹ_b = ỹ_a T_{a↗b}`, the `T`–`ỹ` rule.

Both are the same two-line calculation, and neither reads a relation of `HJO.Braid.BraidMonoid`
beyond the gluing of trains. The descending train on the left glues onto the descending train inside
the generator and the ascending train on the right glues onto the ascending train inside it, so both
sides collapse to `T_{a↘1} (…) T_{1↗b}` with the same middle factor. What makes that work is that
`z_i` and `ỹ_i` are *conjugates of one index-independent element by a pair of trains based at `1`* —
`HJO.Braid.braidGenZ_eq_trainDown_mul_mul_trainUp` for `z_i` and `HJO.Braid.braidYtilde` for `ỹ_i` —
which is why Mellit introduces `ỹ_i` rather than working with `y_i`: the closed form of `y_i`
(`HJO.Braid.braidGenY_eq_trainUp_mul_mul_trainDown`) has the
*ascending* train on the left and the descending one on the right, the orientation in which this
calculation does not close.

## Main results

* `HJO.Braid.braidTrainDown_mul_braidGenZ`.
* `HJO.Braid.braidTrainDown_mul_braidYtilde`.

## Implementation notes

The gluing lemmas `HJO.Braid.trainUp_mul_trainUp` and `HJO.Braid.trainDown_mul_trainDown` need every
index they read to lie in `[1, k]`, which is where the `1 ≤ a, b ≤ k` is spent; `1 ≤ k`
follows from `1 ≤ a ≤ k` and is not a separate hypothesis. The braid system is the one
`HJO.Braid.isBraidSystem_braidGenT` supplies inside the quotient,
`HJO.Braid.isBraidSystem_braidGenT`.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §5. -/

@[expose] public section

namespace HJO.Braid

variable {k a b : ℕ}

/-- **The `T`–`z` rule**, `HJO.Braid.braidTrainDown_mul_braidGenZ`: `T_{a↘b} z_b = z_a T_{a↗b}` in
`𝔹_k^+(𝕋_0)` for `1 ≤ a, b ≤ k`.

By `HJO.Braid.braidGenZ_eq_trainDown_mul_mul_trainUp` both sides are `T_{a↘1} z_1 T_{1↗b}`: on the
left the outer descending train glues onto the one inside `z_b`
(`HJO.Braid.trainDown_mul_trainDown`), and on the right the ascending train inside `z_a` glues onto
the outer one (`HJO.Braid.trainUp_mul_trainUp`). -/
@[hjo "lem_train_z_rule"]
theorem braidTrainDown_mul_braidGenZ (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k) :
    braidTrainDown k a b * braidGenZ k b = braidGenZ k a * braidTrainUp k a b := by
  have hsys := isBraidSystem_braidGenT k
  have hD : braidTrainDown k a b * braidTrainDown k b 1 = braidTrainDown k a 1 :=
    trainDown_mul_trainDown hsys ha hak hb hbk le_rfl (by omega)
  have hU : braidTrainUp k 1 a * braidTrainUp k a b = braidTrainUp k 1 b :=
    trainUp_mul_trainUp hsys le_rfl (by omega) ha hak hb hbk
  rw [braidGenZ_eq_trainDown_mul_mul_trainUp k b hb hbk,
    braidGenZ_eq_trainDown_mul_mul_trainUp k a ha hak]
  simp only [mul_assoc]
  rw [hU, ← hD]
  simp only [mul_assoc]

/-- **The `T`–`ỹ` rule**, `HJO.Braid.braidTrainDown_mul_braidYtilde`:
`T_{a↘b} ỹ_b = ỹ_a T_{a↗b}` in `𝔹_k^+(𝕋_0)` for `1 ≤ a, b ≤ k`.

The same calculation as `HJO.Braid.braidTrainDown_mul_braidGenZ`, with the middle factor
`T_{1↗k} y_k` in place of `z_1`: `HJO.Braid.braidYtilde` already presents `ỹ_i` as
`T_{i↘1} (T_{1↗k} y_k) T_{k↗i}`, so nothing has to be computed before the two gluings. -/
@[hjo "lem_train_ytilde_rule"]
theorem braidTrainDown_mul_braidYtilde (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k) :
    braidTrainDown k a b * braidYtilde k b = braidYtilde k a * braidTrainUp k a b := by
  have hsys := isBraidSystem_braidGenT k
  have hD : braidTrainDown k a b * braidTrainDown k b 1 = braidTrainDown k a 1 :=
    trainDown_mul_trainDown hsys ha hak hb hbk le_rfl (by omega)
  have hU : braidTrainUp k k a * braidTrainUp k a b = braidTrainUp k k b :=
    trainUp_mul_trainUp hsys (by omega) le_rfl ha hak hb hbk
  rw [braidYtilde, braidYtilde]
  simp only [mul_assoc]
  rw [hU, ← hD]
  simp only [mul_assoc]

end HJO.Braid
