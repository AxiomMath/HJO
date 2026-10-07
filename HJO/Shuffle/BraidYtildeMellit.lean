/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidYtildeComm
public meta import HJO.Attr

/-! # Mellit's relations for the commuting lifts

`HJO.Braid.BraidMonoid` presents `𝔹_k^+(𝕋_0)` on `T_i`, `T̄_i`, `y_1`, `z_1`. Mellit records that
those relations "can be translated" to a second list, in the commuting lifts `ỹ_i` of
`HJO.Braid.braidYtilde`, and gives no proof. This file proves that list.

## Main results

* `HJO.Braid.braidYtilde_succ` — `ỹ_{a+1} = T_a ỹ_a T_a`, which is
  `HJO.Braid.braidTrainDown_mul_braidYtilde` at adjacent indices read as a recursion.
* `HJO.Braid.braidYtilde_comm` — **`ỹ_a ỹ_b = ỹ_b ỹ_a` for `1 ≤ a, b ≤ k`.** Not a relation of
  `HJO.Braid.BraidMonoid`.
* `HJO.Braid.braidYtilde_zy` — **`ỹ_1 T_1 z_1 = T_1 z_1 T_1 ỹ_1 T_1`**, Mellit's one mixed relation
  in the `ỹ`-family. Not a relation of `HJO.Braid.BraidMonoid` either.
* `HJO.Braid.braidLoop`, `HJO.Braid.braidLoopInv` — the pure braid `T_{a↗k} T_{k↘a}` in which the
  whole argument is carried, and its inverse.

Together with `HJO.Braid.braidYtilde_comm_T` these are Mellit's two displayed lists.

## Implementation notes

### `ỹ_1` is `y_1` times one pure braid

`HJO.Braid.braidGenY_eq_trainUp_mul_mul_trainDown` turns `HJO.Braid.braidYtilde` at index `1` into
`ỹ_1 = y_1 · T_{1↘k} T_{k↗1}` (`HJO.Braid.braidYtilde_one_eq`): the ascending train of
`HJO.Braid.braidYtilde` cancels the one inside `y_k`, and what survives is `y_1` followed by the
inverse of `HJO.Braid.braidLoop k 1`, the pure braid in which strand `1` loops around all the
others. That single factor is where every remaining difficulty sits, and the two facts about it are:

* it commutes with `T_j` for `2 ≤ j ≤ k - 1` (`HJO.Braid.braidLoop_one_comm_T`) — two applications
  of `HJO.Braid.trainUp_mul_gen` and `HJO.Braid.trainDown_one_mul_gen`, the letter going down
  through the ascending train and back up through the descending one;
* hence it commutes with `HJO.Braid.braidLoop k 2`, which is a word in exactly those letters
  (`HJO.Braid.braidLoop_one_comm_two`).

`HJO.Braid.braidLoop k 1 = T_1 · (HJO.Braid.braidLoop k 2) · T_1` is a gluing, and those three
facts give `T_1 (Λ_1 Λ_2) = (Λ_1 Λ_2) T_1` with no braid-group theory beyond the presentation:
**no full twist and no centrality theorem is needed**, which is what a first reading of this problem
expects.

### The commutation is an induction on the index, by the braid relation alone

Write `X_a = ỹ_a T_a ỹ_a`. Then `ỹ_a ỹ_{a+1} = X_a T_a` and `ỹ_{a+1} ỹ_a = T_a X_a`, so the
adjacent case at `a` says exactly that `T_a` commutes with `X_a`. Two steps:

* At `a = 1`, `X_1 = y_1 y_2 · T_1 · Λ̄_2 Λ̄_1` — the computation above — and `T_1` commutes with
  both halves. That `T_1` commutes with `y_1 y_2` is `𝗒_1 𝗒_2 = 𝗒_2 𝗒_1` together with
  `y_2 = T̄_1 y_1 T̄_1`, and is the only place a relation of the `y`-family enters.
* `X_{a+1} = T_a T_{a+1} X_a T_{a+1} T_a`, because `ỹ_a` commutes with `T_{a+1}`
  (`HJO.Braid.braidYtilde_comm_T`) and `T_a T_{a+1} T_a = T_{a+1} T_a T_{a+1}`. From that the
  commutation propagates upwards using the braid relation and nothing else
  (`HJO.Braid.conj_swap_pair`, `HJO.Braid.conj_swap_step`).

Non-adjacent indices reduce to adjacent ones without any cancellation: for `a + 1 ≤ b`,
`HJO.Braid.braidTrainDown_mul_braidYtilde` gives `ỹ_b = T_{b↘a+1} ỹ_{a+1} T_{a+1↗b}`, and `ỹ_a`
commutes with both of those trains, so both products are the same two trains around `ỹ_a ỹ_{a+1}`
and `ỹ_{a+1} ỹ_a`.

### The mixed relation is two cancellations

`ỹ_1 T_1 z_1` and `T_1 z_1 T_1 ỹ_1 T_1` both reduce, by `HJO.Braid.braidYtilde_one_eq` and the fact
that `z_1` commutes with `HJO.Braid.braidLoopInv k 2`, to `(y_1 T̄_1 z_1) Λ̄_2` and
`(T_1 z_1 T_1 y_1 T̄_1) Λ̄_2`; and `HJO.Braid.BraidMonoid`'s `𝗓_1 T_1 𝗒_1 T̄_1 = T̄_1 𝗒_1 T̄_1 𝗓_1`
multiplied on the left by `T_1` is exactly the equality of the two heads. Nothing else is used.

### No hypothesis beyond the rank bounds

As in `HJO.Braid.braidYtilde_comm_T`: everything is in `BraidMonoid k`, with no field, no
representation and no condition on the data of `HJO.Braid.specialBraid`.

## References

A. Mellit,
*Toric braids and `(m, n)`-parking functions*, the two displays following his `ỹ_i`.
-/

@[expose] public section

namespace HJO.Braid

/-! ### Two rearrangements in a monoid -/

section Monoid

variable {M : Type*} [Monoid M]

/-- **The shape of the induction step.** If `g` commutes with `s` and `t s t = s t s`, then
`t g t · s · t g t = t s · (g t g) · s t`: the two conjugates of `g` by `t` around an `s` are the
conjugate by `t s` of `g t g`. With `g = ỹ_a`, `t = T_a`, `s = T_{a+1}` this says
`X_{a+1} = T_a T_{a+1} X_a T_{a+1} T_a`. -/
theorem conj_swap_pair {g s t : M} (hgs : g * s = s * g) (hb : t * s * t = s * t * s) :
    t * g * t * s * (t * g * t) = t * s * (g * t * g) * (s * t) := by
  calc t * g * t * s * (t * g * t)
      = t * g * (t * s * t) * (g * t) := by simp only [mul_assoc]
    _ = t * g * (s * t * s) * (g * t) := by rw [hb]
    _ = t * (g * s) * (t * s * g * t) := by simp only [mul_assoc]
    _ = t * (s * g) * (t * s * g * t) := by rw [hgs]
    _ = t * s * g * t * (s * g) * t := by simp only [mul_assoc]
    _ = t * s * g * t * (g * s) * t := by rw [← hgs]
    _ = t * s * (g * t * g) * (s * t) := by simp only [mul_assoc]

/-- **The induction step itself.** If `t s t = s t s` and `t` commutes with `X`, then `s` commutes
with `t s X s t`: the braid relation carries the commutation from one generator to the next. -/
theorem conj_swap_step {X s t : M} (hb : t * s * t = s * t * s) (hX : t * X = X * t) :
    s * (t * s * X * (s * t)) = t * s * X * (s * t) * s := by
  calc s * (t * s * X * (s * t))
      = s * t * s * X * (s * t) := by simp only [mul_assoc]
    _ = t * s * t * X * (s * t) := by rw [← hb]
    _ = t * s * (t * X) * (s * t) := by simp only [mul_assoc]
    _ = t * s * (X * t) * (s * t) := by rw [hX]
    _ = t * s * X * (t * s * t) := by simp only [mul_assoc]
    _ = t * s * X * (s * t * s) := by rw [hb]
    _ = t * s * X * (s * t) * s := by simp only [mul_assoc]

end Monoid

variable {k : ℕ}

/-! ### The pure braid of one strand against the strands above it -/

/-- **The loop of strand `a` around the strands above it**: `Λ_a = T_{a↗k} T_{k↘a}` in
`𝔹_k^+(𝕋_0)`. Total in `a`; at `a = k` both trains are empty and `Λ_k = 1`. -/
@[hjo "def_braid_loop"]
def braidLoop (k a : ℕ) : BraidMonoid k := braidTrainUp k a k * braidTrainDown k k a

/-- **The inverse loop** `Λ̄_a = T_{a↘k} T_{k↗a}`, the two-sided inverse of
`HJO.Braid.braidLoop` by `HJO.Braid.braidLoop_mul_inv` and
`HJO.Braid.braidLoopInv_mul_self`. -/
@[hjo "def_braid_loop"]
def braidLoopInv (k a : ℕ) : BraidMonoid k := braidTrainDown k a k * braidTrainUp k k a

theorem braidLoop_mul_inv {a : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) :
    braidLoop k a * braidLoopInv k a = 1 := by
  have hsys := isBraidSystem_braidGenT k
  have hD : braidTrainDown k k a * braidTrainDown k a k = 1 :=
    trainDown_mul_trainDown_self hsys (by omega) le_rfl ha hak
  have hU : braidTrainUp k a k * braidTrainUp k k a = 1 :=
    trainUp_mul_trainUp_self hsys ha hak (by omega) le_rfl
  rw [braidLoop, braidLoopInv]
  simp only [mul_assoc]
  rw [mul_mul_cancel_of_mul_eq_one hD, hU]

theorem braidLoopInv_mul_self {a : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) :
    braidLoopInv k a * braidLoop k a = 1 := by
  have hsys := isBraidSystem_braidGenT k
  have hU : braidTrainUp k k a * braidTrainUp k a k = 1 :=
    trainUp_mul_trainUp_self hsys (by omega) le_rfl ha hak
  have hD : braidTrainDown k a k * braidTrainDown k k a = 1 :=
    trainDown_mul_trainDown_self hsys ha hak (by omega) le_rfl
  rw [braidLoop, braidLoopInv]
  simp only [mul_assoc]
  rw [mul_mul_cancel_of_mul_eq_one hU, hD]

/-- **`Λ_1 = T_1 Λ_2 T_1`**: splitting the bottom letter off each of the two trains of `Λ_1`, by
`HJO.Braid.trainUp_mul_trainUp` and `HJO.Braid.trainDown_mul_trainDown`. -/
theorem braidLoop_one_eq (hk : 2 ≤ k) :
    braidLoop k 1 = braidGenT k 1 * braidLoop k 2 * braidGenT k 1 := by
  have hsys := isBraidSystem_braidGenT k
  have hU : braidGenT k 1 * braidTrainUp k 2 k = braidTrainUp k 1 k := by
    have hglue : braidTrainUp k 1 2 * braidTrainUp k 2 k = braidTrainUp k 1 k :=
      trainUp_mul_trainUp hsys (by omega) (by omega) (by omega) hk (by omega) le_rfl
    rwa [show braidTrainUp k 1 2 = braidGenT k 1 from trainUp_self_succ _ _ 1] at hglue
  have hD : braidTrainDown k k 2 * braidGenT k 1 = braidTrainDown k k 1 := by
    have hglue : braidTrainDown k k 2 * braidTrainDown k 2 1 = braidTrainDown k k 1 :=
      trainDown_mul_trainDown hsys (by omega) le_rfl (by omega) hk (by omega) (by omega)
    rwa [show braidTrainDown k 2 1 = braidGenT k 1 from trainDown_succ_self _ _ 1] at hglue
  rw [braidLoop, braidLoop, ← hU, ← hD]
  simp only [mul_assoc]

/-- **`Λ̄_1 = T̄_1 Λ̄_2 T̄_1`**, the inverted form of `HJO.Braid.braidLoop_one_eq`; the two bottom
letters are the *second* branch of each train, so they are `T̄_1`. -/
theorem braidLoopInv_one_eq (hk : 2 ≤ k) :
    braidLoopInv k 1 = braidGenTinv k 1 * braidLoopInv k 2 * braidGenTinv k 1 := by
  have hsys := isBraidSystem_braidGenT k
  have hD : braidGenTinv k 1 * braidTrainDown k 2 k = braidTrainDown k 1 k := by
    have hglue : braidTrainDown k 1 2 * braidTrainDown k 2 k = braidTrainDown k 1 k :=
      trainDown_mul_trainDown hsys (by omega) (by omega) (by omega) hk (by omega) le_rfl
    rwa [show braidTrainDown k 1 2 = braidGenTinv k 1 from trainDown_self_succ _ _ 1] at hglue
  have hU : braidTrainUp k k 2 * braidGenTinv k 1 = braidTrainUp k k 1 := by
    have hglue : braidTrainUp k k 2 * braidTrainUp k 2 1 = braidTrainUp k k 1 :=
      trainUp_mul_trainUp hsys (by omega) le_rfl (by omega) hk (by omega) (by omega)
    rwa [show braidTrainUp k 2 1 = braidGenTinv k 1 from trainUp_succ_self _ _ 1] at hglue
  rw [braidLoopInv, braidLoopInv, ← hD, ← hU]
  simp only [mul_assoc]

/-- **`Λ̄_1 T_1 = T̄_1 Λ̄_2`**, one cancellation in `HJO.Braid.braidLoopInv_one_eq`. This is the
form in which the loop meets the generator in every computation below. -/
theorem braidLoopInv_one_mul_gen (hk : 2 ≤ k) :
    braidLoopInv k 1 * braidGenT k 1 = braidGenTinv k 1 * braidLoopInv k 2 := by
  have hT : braidGenTinv k 1 * braidGenT k 1 = 1 := braidGenT_inv_mul le_rfl hk
  rw [braidLoopInv_one_eq hk]
  simp only [mul_assoc]
  rw [hT, mul_one]

/-- **`Λ_1` commutes with `T_j` for `2 ≤ j ≤ k - 1`.** `HJO.Braid.trainUp_mul_gen` lowers the letter
to `T_{j-1}` as it passes the ascending train, and `HJO.Braid.trainDown_one_mul_gen` raises it back
to `T_j` as it passes the descending one. This is the one genuinely braid-theoretic fact the
`ỹ`-relations need, and it is two shifts. -/
@[hjo "lem_braid_loop_comm"]
theorem braidLoop_one_comm_T {j : ℕ} (hj : 2 ≤ j) (hjk : j + 1 ≤ k) :
    braidLoop k 1 * braidGenT k j = braidGenT k j * braidLoop k 1 := by
  have hsys := isBraidSystem_braidGenT k
  obtain ⟨r, rfl⟩ : ∃ r, j = r + 1 := ⟨j - 1, by omega⟩
  have hD : braidTrainDown k k 1 * braidGenT k (r + 1) = braidGenT k r * braidTrainDown k k 1 :=
    trainDown_one_mul_gen hsys (by omega) (by omega) le_rfl
  have hU : braidTrainUp k 1 k * braidGenT k r = braidGenT k (r + 1) * braidTrainUp k 1 k :=
    trainUp_mul_gen hsys (by omega) (by omega) (by omega) le_rfl
  rw [braidLoop]
  calc braidTrainUp k 1 k * braidTrainDown k k 1 * braidGenT k (r + 1)
      = braidTrainUp k 1 k * (braidTrainDown k k 1 * braidGenT k (r + 1)) := mul_assoc _ _ _
    _ = braidTrainUp k 1 k * braidGenT k r * braidTrainDown k k 1 := by
        rw [hD]; simp only [mul_assoc]
    _ = braidGenT k (r + 1) * (braidTrainUp k 1 k * braidTrainDown k k 1) := by
        rw [hU]; simp only [mul_assoc]

/-- **`Λ_1` commutes with `Λ_2`**: every letter of `Λ_2` is a `T_j` with `2 ≤ j ≤ k - 1`, and
`HJO.Braid.braidLoop_one_comm_T` commutes `Λ_1` past each of them. -/
@[hjo "lem_braid_loop_comm"]
theorem braidLoop_one_comm_two (hk : 2 ≤ k) :
    braidLoop k 1 * braidLoop k 2 = braidLoop k 2 * braidLoop k 1 := by
  have hsys := isBraidSystem_braidGenT k
  have hU : braidLoop k 1 * braidTrainUp k 2 k = braidTrainUp k 2 k * braidLoop k 1 :=
    hsys.comm_trainUp (by omega) hk (by omega) le_rfl fun j _ _ =>
      braidLoop_one_comm_T (by omega) (by omega)
  have hD : braidLoop k 1 * braidTrainDown k k 2 = braidTrainDown k k 2 * braidLoop k 1 :=
    hsys.comm_trainDown (by omega) le_rfl (by omega) hk fun j _ _ =>
      braidLoop_one_comm_T (by omega) (by omega)
  rw [show braidLoop k 2 = braidTrainUp k 2 k * braidTrainDown k k 2 from rfl]
  calc braidLoop k 1 * (braidTrainUp k 2 k * braidTrainDown k k 2)
      = braidLoop k 1 * braidTrainUp k 2 k * braidTrainDown k k 2 := (mul_assoc _ _ _).symm
    _ = braidTrainUp k 2 k * (braidLoop k 1 * braidTrainDown k k 2) := by
        rw [hU]; simp only [mul_assoc]
    _ = braidTrainUp k 2 k * braidTrainDown k k 2 * braidLoop k 1 := by
        rw [hD]; simp only [mul_assoc]

/-- **`T_1` commutes with `Λ_1 Λ_2`.** `HJO.Braid.braidLoop_one_comm_two` turns `Λ_1 Λ_2` into
`Λ_2 Λ_1`, and `HJO.Braid.braidLoop_one_eq` then makes both sides the same word. -/
@[hjo "lem_braid_loop_comm"]
theorem braidGenT_one_comm_braidLoop (hk : 2 ≤ k) :
    braidGenT k 1 * (braidLoop k 1 * braidLoop k 2)
      = braidLoop k 1 * braidLoop k 2 * braidGenT k 1 := by
  have h1 : braidLoop k 1 = braidGenT k 1 * braidLoop k 2 * braidGenT k 1 := braidLoop_one_eq hk
  calc braidGenT k 1 * (braidLoop k 1 * braidLoop k 2)
      = braidGenT k 1 * (braidLoop k 2 * braidLoop k 1) := by rw [braidLoop_one_comm_two hk]
    _ = braidLoop k 1 * braidLoop k 2 * braidGenT k 1 := by rw [h1]; simp only [mul_assoc]

/-- **`T_1` commutes with `Λ̄_2 Λ̄_1`**, the inverse form of
`HJO.Braid.braidGenT_one_comm_braidLoop`. -/
theorem braidGenT_one_comm_braidLoopInv (hk : 2 ≤ k) :
    braidGenT k 1 * (braidLoopInv k 2 * braidLoopInv k 1)
      = braidLoopInv k 2 * braidLoopInv k 1 * braidGenT k 1 := by
  have h1 : braidLoop k 1 * braidLoopInv k 1 = 1 := braidLoop_mul_inv (by omega) (by omega)
  have h1' : braidLoopInv k 1 * braidLoop k 1 = 1 := braidLoopInv_mul_self (by omega) (by omega)
  have h2 : braidLoop k 2 * braidLoopInv k 2 = 1 := braidLoop_mul_inv (by omega) hk
  have h2' : braidLoopInv k 2 * braidLoop k 2 = 1 := braidLoopInv_mul_self (by omega) hk
  refine comm_inv_right (y := braidLoop k 1 * braidLoop k 2) ?_ ?_
    (braidGenT_one_comm_braidLoop hk)
  · simp only [mul_assoc]
    rw [mul_mul_cancel_of_mul_eq_one h2, h1]
  · simp only [mul_assoc]
    rw [mul_mul_cancel_of_mul_eq_one h1', h2']

/-! ### `y_1` and `z_1` against a train -/

/-- `y_a` commutes with a descending train all of whose letters are far from `a`, the `y`-analogue
of `HJO.Braid.braidGenZ_comm_trainDown`. -/
theorem braidGenY_comm_trainDown {a c d : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hc : 1 ≤ c)
    (hck : c ≤ k) (hd : 1 ≤ d) (hdk : d ≤ k) (hfar : a + 1 ≤ min c d ∨ max c d + 1 ≤ a) :
    braidGenY k a * braidTrainDown k c d = braidTrainDown k c d * braidGenY k a :=
  (isBraidSystem_braidGenT k).comm_trainDown hc hck hd hdk fun j _ _ =>
    braidGenY_comm_T ha hak (by omega) (by omega) (by omega) (by omega)

/-- `y_a` commutes with an ascending train all of whose letters are far from `a`. -/
theorem braidGenY_comm_trainUp {a c d : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hc : 1 ≤ c)
    (hck : c ≤ k) (hd : 1 ≤ d) (hdk : d ≤ k) (hfar : a + 1 ≤ min c d ∨ max c d + 1 ≤ a) :
    braidGenY k a * braidTrainUp k c d = braidTrainUp k c d * braidGenY k a :=
  (isBraidSystem_braidGenT k).comm_trainUp hc hck hd hdk fun j _ _ =>
    braidGenY_comm_T ha hak (by omega) (by omega) (by omega) (by omega)

/-- `y_1` commutes with `Λ̄_2`, whose letters are the `T_j` with `2 ≤ j ≤ k - 1`. -/
theorem braidGenY_one_comm_braidLoopInv_two (hk : 2 ≤ k) :
    braidGenY k 1 * braidLoopInv k 2 = braidLoopInv k 2 * braidGenY k 1 := by
  have hD : braidGenY k 1 * braidTrainDown k 2 k = braidTrainDown k 2 k * braidGenY k 1 :=
    braidGenY_comm_trainDown (c := 2) (d := k) (by omega) (by omega) (by omega) hk (by omega)
      le_rfl (by omega)
  have hU : braidGenY k 1 * braidTrainUp k k 2 = braidTrainUp k k 2 * braidGenY k 1 :=
    braidGenY_comm_trainUp (c := k) (d := 2) (by omega) (by omega) (by omega) le_rfl (by omega)
      hk (by omega)
  rw [braidLoopInv]
  calc braidGenY k 1 * (braidTrainDown k 2 k * braidTrainUp k k 2)
      = braidGenY k 1 * braidTrainDown k 2 k * braidTrainUp k k 2 := (mul_assoc _ _ _).symm
    _ = braidTrainDown k 2 k * (braidGenY k 1 * braidTrainUp k k 2) := by
        rw [hD]; simp only [mul_assoc]
    _ = braidTrainDown k 2 k * braidTrainUp k k 2 * braidGenY k 1 := by
        rw [hU]; simp only [mul_assoc]

/-- `z_1` commutes with `Λ̄_2`. -/
theorem braidGenZ_one_comm_braidLoopInv_two (hk : 2 ≤ k) :
    braidGenZ k 1 * braidLoopInv k 2 = braidLoopInv k 2 * braidGenZ k 1 := by
  have hD : braidGenZ k 1 * braidTrainDown k 2 k = braidTrainDown k 2 k * braidGenZ k 1 :=
    braidGenZ_comm_trainDown (c := 2) (d := k) (by omega) (by omega) (by omega) hk (by omega)
      le_rfl (by omega)
  have hU : braidGenZ k 1 * braidTrainUp k k 2 = braidTrainUp k k 2 * braidGenZ k 1 :=
    braidGenZ_comm_trainUp (c := k) (d := 2) (by omega) (by omega) (by omega) le_rfl (by omega)
      hk (by omega)
  rw [braidLoopInv]
  calc braidGenZ k 1 * (braidTrainDown k 2 k * braidTrainUp k k 2)
      = braidGenZ k 1 * braidTrainDown k 2 k * braidTrainUp k k 2 := (mul_assoc _ _ _).symm
    _ = braidTrainDown k 2 k * (braidGenZ k 1 * braidTrainUp k k 2) := by
        rw [hD]; simp only [mul_assoc]
    _ = braidTrainDown k 2 k * braidTrainUp k k 2 * braidGenZ k 1 := by
        rw [hU]; simp only [mul_assoc]

/-! ### `ỹ_1` is `y_1` times one pure braid -/

/-- **`ỹ_1 = y_1 Λ̄_1`.** `HJO.Braid.braidGenY_eq_trainUp_mul_mul_trainDown` writes
`y_k = T_{k↗1} y_1 T_{1↘k}`, whose ascending train cancels the one `HJO.Braid.braidYtilde` puts in
front of it by `HJO.Braid.trainUp_mul_trainUp_self`; what is left is `y_1` followed by
`T_{1↘k} T_{k↗1}`. -/
theorem braidYtilde_one_eq (hk : 1 ≤ k) :
    braidYtilde k 1 = braidGenY k 1 * braidLoopInv k 1 := by
  have hsys := isBraidSystem_braidGenT k
  have hyk : braidGenY k k = braidTrainUp k k 1 * braidGenY k 1 * braidTrainDown k 1 k :=
    braidGenY_eq_trainUp_mul_mul_trainDown k k hk le_rfl
  have hcancel : braidTrainUp k 1 k * braidTrainUp k k 1 = 1 :=
    trainUp_mul_trainUp_self hsys le_rfl hk hk le_rfl
  rw [braidYtilde, braidTrainDown_self, one_mul, hyk, braidLoopInv]
  simp only [mul_assoc]
  rw [mul_mul_cancel_of_mul_eq_one hcancel]

/-! ### The recursion and the general conjugation form -/

/-- **`ỹ_{a+1} = T_a ỹ_a T_a`**, Mellit's second display: `HJO.Braid.braidTrainDown_mul_braidYtilde`
at the adjacent pair `(a + 1, a)` reads `T_a ỹ_a = ỹ_{a+1} T̄_a`, and one cancellation turns it into
the recursion. -/
theorem braidYtilde_succ {a : ℕ} (ha : 1 ≤ a) (hak : a + 1 ≤ k) :
    braidYtilde k (a + 1) = braidGenT k a * braidYtilde k a * braidGenT k a := by
  have h := braidTrainDown_mul_braidYtilde (k := k) (a := a + 1) (b := a) (by omega) hak ha
    (by omega)
  rw [show braidTrainDown k (a + 1) a = braidGenT k a from trainDown_succ_self _ _ a,
    show braidTrainUp k (a + 1) a = braidGenTinv k a from trainUp_succ_self _ _ a] at h
  calc braidYtilde k (a + 1)
      = braidYtilde k (a + 1) * (braidGenTinv k a * braidGenT k a) := by
        rw [braidGenT_inv_mul ha hak, mul_one]
    _ = braidGenT k a * braidYtilde k a * braidGenT k a := by rw [← mul_assoc, ← h]

/-- **`ỹ_b = T_{b↘a} ỹ_a T_{a↗b}`**, `HJO.Braid.braidTrainDown_mul_braidYtilde` with the ascending
train moved to the other side by `HJO.Braid.trainUp_mul_trainUp_self`. -/
theorem braidYtilde_eq_trainDown_mul_mul_trainUp {a b : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b)
    (hbk : b ≤ k) :
    braidYtilde k b = braidTrainDown k b a * braidYtilde k a * braidTrainUp k a b := by
  have hsys := isBraidSystem_braidGenT k
  have h := braidTrainDown_mul_braidYtilde (k := k) (a := b) (b := a) hb hbk ha hak
  have hcancel : braidTrainUp k b a * braidTrainUp k a b = 1 :=
    trainUp_mul_trainUp_self hsys hb hbk ha hak
  calc braidYtilde k b = braidYtilde k b * (braidTrainUp k b a * braidTrainUp k a b) := by
        rw [hcancel, mul_one]
    _ = braidTrainDown k b a * braidYtilde k a * braidTrainUp k a b := by
        rw [← mul_assoc, ← h]

/-! ### `T_1` commutes with `ỹ_1 T_1 ỹ_1` -/

/-- **`T_1` commutes with `y_1 y_2`.** This is the only place a relation of the `y`-family other
than `HJO.Braid.braidGenY_eq_trainUp_mul_mul_trainDown` is spent: `y_2 = T̄_1 y_1 T̄_1` turns
`T_1 (y_2 y_1) T̄_1` into `y_1 y_2`, and `𝗒_1 𝗒_2 = 𝗒_2 𝗒_1` is what lets the product be read in the
other order. -/
theorem braidGenT_one_comm_braidGenY_mul (hk : 2 ≤ k) :
    braidGenT k 1 * (braidGenY k 1 * braidGenY k 2)
      = braidGenY k 1 * braidGenY k 2 * braidGenT k 1 := by
  have hT : braidGenT k 1 * braidGenTinv k 1 = 1 := braidGenT_mul_inv le_rfl hk
  have hy2 : braidGenY k 2 = braidGenTinv k 1 * braidGenY k 1 * braidGenTinv k 1 := by
    simpa using braidGenY_succ k 0
  have hcomm : braidGenY k 1 * braidGenY k 2 = braidGenY k 2 * braidGenY k 1 :=
    braidGenY_comm (by omega) (by omega) (by omega) hk
  have key : braidGenT k 1 * (braidGenY k 2 * braidGenY k 1) * braidGenTinv k 1
      = braidGenY k 1 * braidGenY k 2 := by
    rw [hy2]
    simp only [mul_assoc]
    rw [mul_mul_cancel_of_mul_eq_one hT]
  calc braidGenT k 1 * (braidGenY k 1 * braidGenY k 2)
      = braidGenT k 1 * (braidGenY k 2 * braidGenY k 1)
          * (braidGenTinv k 1 * braidGenT k 1) := by
        rw [braidGenT_inv_mul le_rfl hk, mul_one, hcomm]
    _ = braidGenY k 1 * braidGenY k 2 * braidGenT k 1 := by rw [← mul_assoc, key]

/-- **`ỹ_1 T_1 ỹ_1 = y_1 y_2 · T_1 · Λ̄_2 Λ̄_1`.** Substituting `ỹ_1 = y_1 Λ̄_1` and using
`Λ̄_1 T_1 = T̄_1 Λ̄_2`, the factor `Λ̄_2` commutes past the second `y_1`, and `y_1 T̄_1 y_1` is
`y_1 y_2 T_1`. -/
theorem braidYtilde_one_conj_eq (hk : 2 ≤ k) :
    braidYtilde k 1 * braidGenT k 1 * braidYtilde k 1
      = braidGenY k 1 * braidGenY k 2 * braidGenT k 1
        * (braidLoopInv k 2 * braidLoopInv k 1) := by
  have hT : braidGenTinv k 1 * braidGenT k 1 = 1 := braidGenT_inv_mul le_rfl hk
  have hy1 : braidYtilde k 1 = braidGenY k 1 * braidLoopInv k 1 := braidYtilde_one_eq (by omega)
  have hLT : braidLoopInv k 1 * braidGenT k 1 = braidGenTinv k 1 * braidLoopInv k 2 :=
    braidLoopInv_one_mul_gen hk
  have hy2 : braidGenY k 2 = braidGenTinv k 1 * braidGenY k 1 * braidGenTinv k 1 := by
    simpa using braidGenY_succ k 0
  have hyy : braidGenY k 1 * braidGenTinv k 1 * braidGenY k 1
      = braidGenY k 1 * braidGenY k 2 * braidGenT k 1 := by
    rw [hy2]
    simp only [mul_assoc]
    rw [hT, mul_one]
  have hcomm := braidGenY_one_comm_braidLoopInv_two hk
  have hcomm2 : braidLoopInv k 2 * (braidGenY k 1 * braidLoopInv k 1)
      = braidGenY k 1 * (braidLoopInv k 2 * braidLoopInv k 1) := by
    rw [← mul_assoc, ← hcomm, mul_assoc]
  calc braidYtilde k 1 * braidGenT k 1 * braidYtilde k 1
      = braidGenY k 1 * (braidLoopInv k 1 * braidGenT k 1)
          * (braidGenY k 1 * braidLoopInv k 1) := by rw [hy1]; simp only [mul_assoc]
    _ = braidGenY k 1 * braidGenTinv k 1
          * (braidLoopInv k 2 * (braidGenY k 1 * braidLoopInv k 1)) := by
        rw [hLT]; simp only [mul_assoc]
    _ = braidGenY k 1 * braidGenTinv k 1
          * (braidGenY k 1 * (braidLoopInv k 2 * braidLoopInv k 1)) := by rw [hcomm2]
    _ = braidGenY k 1 * braidGenTinv k 1 * braidGenY k 1
          * (braidLoopInv k 2 * braidLoopInv k 1) := by simp only [mul_assoc]
    _ = braidGenY k 1 * braidGenY k 2 * braidGenT k 1
          * (braidLoopInv k 2 * braidLoopInv k 1) := by rw [hyy]

/-- **`T_1` commutes with `ỹ_1 T_1 ỹ_1`**, the base of the induction: by
`HJO.Braid.braidYtilde_one_conj_eq` the element is `y_1 y_2 · T_1 · Λ̄_2 Λ̄_1`, and `T_1` commutes
with each of the two outer factors. -/
theorem braidGenT_one_comm_braidYtilde_conj (hk : 2 ≤ k) :
    braidGenT k 1 * (braidYtilde k 1 * braidGenT k 1 * braidYtilde k 1)
      = braidYtilde k 1 * braidGenT k 1 * braidYtilde k 1 * braidGenT k 1 := by
  have hY := braidGenT_one_comm_braidGenY_mul hk
  have hL := braidGenT_one_comm_braidLoopInv hk
  rw [braidYtilde_one_conj_eq hk]
  calc braidGenT k 1 * (braidGenY k 1 * braidGenY k 2 * braidGenT k 1
          * (braidLoopInv k 2 * braidLoopInv k 1))
      = braidGenT k 1 * (braidGenY k 1 * braidGenY k 2)
          * (braidGenT k 1 * (braidLoopInv k 2 * braidLoopInv k 1)) := by simp only [mul_assoc]
    _ = braidGenY k 1 * braidGenY k 2 * braidGenT k 1
          * (braidLoopInv k 2 * braidLoopInv k 1 * braidGenT k 1) := by rw [hY, hL]
    _ = braidGenY k 1 * braidGenY k 2 * braidGenT k 1
          * (braidLoopInv k 2 * braidLoopInv k 1) * braidGenT k 1 := by simp only [mul_assoc]

/-- **`T_a` commutes with `ỹ_a T_a ỹ_a`, for every `1 ≤ a ≤ k - 1`.** Induction on `a`. The base is
`HJO.Braid.braidGenT_one_comm_braidYtilde_conj`. The step is `HJO.Braid.conj_swap_pair`, which
rewrites `X_{a+1}` as `T_a T_{a+1} X_a T_{a+1} T_a` using that `ỹ_a` commutes with `T_{a+1}`, and
then `HJO.Braid.conj_swap_step`, which propagates the commutation by the braid relation alone. -/
theorem braidGenT_comm_braidYtilde_conj : ∀ a, 1 ≤ a → a + 1 ≤ k →
    braidGenT k a * (braidYtilde k a * braidGenT k a * braidYtilde k a)
      = braidYtilde k a * braidGenT k a * braidYtilde k a * braidGenT k a := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => intro hk; exact braidGenT_one_comm_braidYtilde_conj hk
  | succ a ha ih =>
    intro hak
    have ihh := ih (by omega)
    have hbraid : braidGenT k a * braidGenT k (a + 1) * braidGenT k a
        = braidGenT k (a + 1) * braidGenT k a * braidGenT k (a + 1) :=
      braidGenT_braid ha hak
    have hyc : braidYtilde k a * braidGenT k (a + 1) = braidGenT k (a + 1) * braidYtilde k a :=
      braidYtilde_comm_T ha (by omega) (by omega) hak (by omega) (by omega)
    have hstep : braidYtilde k (a + 1) * braidGenT k (a + 1) * braidYtilde k (a + 1)
        = braidGenT k a * braidGenT k (a + 1)
          * (braidYtilde k a * braidGenT k a * braidYtilde k a)
          * (braidGenT k (a + 1) * braidGenT k a) := by
      rw [braidYtilde_succ ha (by omega)]
      exact conj_swap_pair hyc hbraid
    rw [hstep]
    exact conj_swap_step hbraid ihh

/-! ### The commutation of the lifts -/

/-- **`ỹ_a ỹ_{a+1} = ỹ_{a+1} ỹ_a`**: by `HJO.Braid.braidYtilde_succ` the two products are
`X_a T_a` and `T_a X_a` for `X_a = ỹ_a T_a ỹ_a`, so this is
`HJO.Braid.braidGenT_comm_braidYtilde_conj`. -/
theorem braidYtilde_comm_succ {a : ℕ} (ha : 1 ≤ a) (hak : a + 1 ≤ k) :
    braidYtilde k a * braidYtilde k (a + 1) = braidYtilde k (a + 1) * braidYtilde k a := by
  have hX := braidGenT_comm_braidYtilde_conj a ha hak
  rw [braidYtilde_succ ha hak]
  calc braidYtilde k a * (braidGenT k a * braidYtilde k a * braidGenT k a)
      = braidYtilde k a * braidGenT k a * braidYtilde k a * braidGenT k a := by
        simp only [mul_assoc]
    _ = braidGenT k a * (braidYtilde k a * braidGenT k a * braidYtilde k a) := hX.symm
    _ = braidGenT k a * braidYtilde k a * braidGenT k a * braidYtilde k a := by
        simp only [mul_assoc]

/-- The ordered case of `HJO.Braid.braidYtilde_comm`: for `a < b` the identity reduces to the
adjacent pair `(a, a + 1)` with no cancellation. `HJO.Braid.braidTrainDown_mul_braidYtilde` writes
`ỹ_b = T_{b↘a+1} ỹ_{a+1} T_{a+1↗b}`, and `ỹ_a` commutes with both of those trains by
`HJO.Braid.braidYtilde_comm_trainDown` and `HJO.Braid.braidYtilde_comm_trainUp`, so both products
become the same two trains around `ỹ_a ỹ_{a+1}` and `ỹ_{a+1} ỹ_a`. -/
theorem braidYtilde_comm_of_lt {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hbk : b ≤ k) :
    braidYtilde k a * braidYtilde k b = braidYtilde k b * braidYtilde k a := by
  have hsplit : braidYtilde k b
      = braidTrainDown k b (a + 1) * braidYtilde k (a + 1) * braidTrainUp k (a + 1) b :=
    braidYtilde_eq_trainDown_mul_mul_trainUp (a := a + 1) (b := b) (by omega) (by omega)
      (by omega) hbk
  have hD : braidYtilde k a * braidTrainDown k b (a + 1)
      = braidTrainDown k b (a + 1) * braidYtilde k a :=
    braidYtilde_comm_trainDown (c := b) (d := a + 1) ha (by omega) (by omega) hbk (by omega)
      (by omega) (by left; omega)
  have hU : braidYtilde k a * braidTrainUp k (a + 1) b
      = braidTrainUp k (a + 1) b * braidYtilde k a :=
    braidYtilde_comm_trainUp (c := a + 1) (d := b) ha (by omega) (by omega) (by omega) (by omega)
      hbk (by left; omega)
  have hadj : braidYtilde k a * braidYtilde k (a + 1)
      = braidYtilde k (a + 1) * braidYtilde k a := braidYtilde_comm_succ ha (by omega)
  rw [hsplit]
  calc braidYtilde k a * (braidTrainDown k b (a + 1) * braidYtilde k (a + 1)
          * braidTrainUp k (a + 1) b)
      = braidYtilde k a * braidTrainDown k b (a + 1) * (braidYtilde k (a + 1)
          * braidTrainUp k (a + 1) b) := by simp only [mul_assoc]
    _ = braidTrainDown k b (a + 1) * (braidYtilde k a * braidYtilde k (a + 1))
          * braidTrainUp k (a + 1) b := by rw [hD]; simp only [mul_assoc]
    _ = braidTrainDown k b (a + 1) * (braidYtilde k (a + 1) * braidYtilde k a)
          * braidTrainUp k (a + 1) b := by rw [hadj]
    _ = braidTrainDown k b (a + 1) * braidYtilde k (a + 1)
          * (braidYtilde k a * braidTrainUp k (a + 1) b) := by simp only [mul_assoc]
    _ = braidTrainDown k b (a + 1) * braidYtilde k (a + 1) * braidTrainUp k (a + 1) b
          * braidYtilde k a := by rw [hU]; simp only [mul_assoc]

/-- **`ỹ_a ỹ_b = ỹ_b ỹ_a` for `1 ≤ a, b ≤ k`**, Mellit's third display. It is not a relation of
`HJO.Braid.BraidMonoid`; see the module docstring for what it is proved from. -/
@[hjo "lem_braid_ytilde_comm"]
theorem braidYtilde_comm {a b : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k) :
    braidYtilde k a * braidYtilde k b = braidYtilde k b * braidYtilde k a := by
  rcases lt_trichotomy a b with h | rfl | h
  · exact braidYtilde_comm_of_lt ha h hbk
  · rfl
  · exact (braidYtilde_comm_of_lt hb h hak).symm

/-! ### The mixed relation -/

/-- **`ỹ_1 T_1 z_1 = T_1 z_1 T_1 ỹ_1 T_1`**, Mellit's fourth display and the `ỹ`-form of
`HJO.Braid.BraidMonoid`'s one mixed relation. Both sides reduce to `y_1 T̄_1 z_1 Λ̄_2` by
`HJO.Braid.braidYtilde_one_eq`, and the heads agree because `𝗓_1 T_1 𝗒_1 T̄_1 = T̄_1 𝗒_1 T̄_1 𝗓_1`
multiplied on the left by `T_1` says exactly `T_1 z_1 T_1 y_1 T̄_1 = y_1 T̄_1 z_1`. -/
@[hjo "lem_braid_ytilde_zy"]
theorem braidYtilde_zy (hk : 2 ≤ k) :
    braidYtilde k 1 * braidGenT k 1 * braidGenZ k 1
      = braidGenT k 1 * braidGenZ k 1 * braidGenT k 1 * braidYtilde k 1 * braidGenT k 1 := by
  have hT' : braidGenT k 1 * braidGenTinv k 1 = 1 := braidGenT_mul_inv le_rfl hk
  have hy1 : braidYtilde k 1 = braidGenY k 1 * braidLoopInv k 1 := braidYtilde_one_eq (by omega)
  have hLT : braidLoopInv k 1 * braidGenT k 1 = braidGenTinv k 1 * braidLoopInv k 2 :=
    braidLoopInv_one_mul_gen hk
  have hz := braidGenZ_one_comm_braidLoopInv_two hk
  have hhead : braidGenT k 1 * braidGenZ k 1 * braidGenT k 1 * braidGenY k 1 * braidGenTinv k 1
      = braidGenY k 1 * braidGenTinv k 1 * braidGenZ k 1 := by
    have h := braidGen_zy (k := k) hk
    calc braidGenT k 1 * braidGenZ k 1 * braidGenT k 1 * braidGenY k 1 * braidGenTinv k 1
        = braidGenT k 1 * (braidGenZ k 1 * braidGenT k 1 * braidGenY k 1
            * braidGenTinv k 1) := by simp only [mul_assoc]
      _ = braidGenT k 1 * (braidGenTinv k 1 * braidGenY k 1 * braidGenTinv k 1
            * braidGenZ k 1) := by rw [h]
      _ = braidGenY k 1 * braidGenTinv k 1 * braidGenZ k 1 := by
          simp only [mul_assoc]
          rw [mul_mul_cancel_of_mul_eq_one hT']
  calc braidYtilde k 1 * braidGenT k 1 * braidGenZ k 1
      = braidGenY k 1 * (braidLoopInv k 1 * braidGenT k 1) * braidGenZ k 1 := by
        rw [hy1]; simp only [mul_assoc]
    _ = braidGenY k 1 * braidGenTinv k 1 * (braidLoopInv k 2 * braidGenZ k 1) := by
        rw [hLT]; simp only [mul_assoc]
    _ = braidGenY k 1 * braidGenTinv k 1 * (braidGenZ k 1 * braidLoopInv k 2) := by rw [hz]
    _ = braidGenT k 1 * braidGenZ k 1 * braidGenT k 1 * braidGenY k 1 * braidGenTinv k 1
          * braidLoopInv k 2 := by rw [hhead]; simp only [mul_assoc]
    _ = braidGenT k 1 * braidGenZ k 1 * braidGenT k 1 * (braidGenY k 1
          * (braidLoopInv k 1 * braidGenT k 1)) := by rw [hLT]; simp only [mul_assoc]
    _ = braidGenT k 1 * braidGenZ k 1 * braidGenT k 1 * braidYtilde k 1 * braidGenT k 1 := by
        rw [hy1]; simp only [mul_assoc]

end HJO.Braid
