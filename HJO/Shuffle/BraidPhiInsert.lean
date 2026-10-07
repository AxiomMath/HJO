/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidPhiPlus
public import HJO.Shuffle.BraidTrainInsert
public import HJO.Shuffle.BraidTrainRules
public meta import HJO.Attr

/-! # One elementary move against an inserted fixed point

This is the braid algebra of Mellit's Proposition 5.7 (`HJO.Braid.specialBraid_mul_trainDown_one`):
what happens to the letter of one elementary move of `HJO.Braid.braidStep` when a point that never
moves is inserted into the tuple, and the inserted strand is carried past the others by the
descending train `T_{i↘1}`.

## Main results

* `HJO.Braid.phiPlusStar_braidTrainDown`, `HJO.Braid.phiPlusStar_braidTrainUp` — `φ*₊` raises both
  indices of a train.
* `HJO.Braid.phiPlusStar_braidYtilde` — **the absorption**:
  `φ*₊(ỹ_a) = T_{a+1↘2}T̄_1ỹ_1T_{1↗a+1}`, against
  `HJO.Braid.braidYtilde_succ_eq` : `ỹ_{a+1} = T_{a+1↘2}T_1ỹ_1T_{1↗a+1}`. The two words differ by
  `T_1²` in the middle, so `φ*₊` does **not** carry `ỹ_a` to `ỹ_{a+1}`; see the implementation note.
* `HJO.Braid.trainDown_mul_braidGenZ_mul_trainDown_one_of_le`,
  `HJO.Braid.trainDown_mul_braidGenZ_mul_trainDown_one_of_ge`,
  `HJO.Braid.trainDown_mul_braidYtilde_mul_trainDown_one_of_le`,
  `HJO.Braid.trainDown_mul_braidYtilde_mul_trainDown_one_of_ge` — **the four one-move identities**,
  the two branches of `HJO.Braid.braidStep` against the two positions the inserted point can take.
  Each says `b'·T_{i↘1} = T_{i'↘1}·φ*₊(b)` for one elementary move, which is Proposition 5.7 at
  `ℓ = 1`.

## Implementation notes

### `φ*₊(ỹ_a) ≠ ỹ_{a+1}`, and what absorbs the difference

`HJO.Braid.braidStep` contributes `ỹ_a` and not `y_a`, while `HJO.Braid.phiPlusStar` raises the
index of `T_i`, `y_i` and `z_i`. On `y` and `z` that is what it says; on `ỹ` it is not, and the
discrepancy is exactly a factor `T_1²`:

* `ỹ_{a+1} = T_{a+1↘2}·T_1·ỹ_1·T_{1↗a+1}`,
* `φ*₊(ỹ_a) = T_{a+1↘2}·T̄_1·ỹ_1·T_{1↗a+1}`.

That `y_i` and `ỹ_i` are different elements of the monoid is clear, but not this
consequence; Mellit states it only at `a = 1` (as `φ*₊(ỹ_1) = T_1^{-1}ỹ_1T_1`) inside the
proof. What absorbs the difference is the outer conjugation of the statement: the `T̄_1` is
swallowed by `T_{i'↘1}` coming from the left, since `T_{i'↘1} = T_{i'↘2}T_1`. That is the step
`T_{i'↘1}T_{a'+1↘2}T̄_1 = T_{a'↘1}T_{i'↘2}` inside
`HJO.Braid.trainDown_one_mul_trainDown_mul_phiPlusStar_braidYtilde`, and it is the reason
Proposition 5.7 is a conjugation identity rather than `B' = φ*₊(B)`.

### Which regime of the index arithmetic fires

Both `ỹ` identities and both `z` identities come from *one* normal form each — the `ỹ` one ending
`ỹ_1T_{i'↘2}T_{1↗a+1}` and the `z` one ending `z_1T_{i'+1↘2}T_{1↗a+1}` — followed by a single
application of `HJO.Braid.trainDown_two_mul_trainUp_one_of_le` or
`HJO.Braid.trainDown_two_mul_trainUp_one_of_ge`. Which of the two fires is which side of the
inserted point the moving point ends on, and it is the *only* thing that distinguishes the cases:
the inserted point's rank is unchanged in one and shifted by one in the other.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, Proposition 5.7.
-/

@[expose] public section

namespace HJO.Braid

variable {M : Type*} [Monoid M]

/-! ### A homomorphism that raises the index of every letter -/

/-- An ascending word maps to the ascending word one index up, for a homomorphism that raises the
index of every letter it reads. -/
theorem map_ascendingWord {N : Type*} [Monoid N] (f : M →* N) (T : ℕ → M) (T' : ℕ → N) {a b : ℕ}
    (hT : ∀ j, a ≤ j → j < b → f (T j) = T' (j + 1)) :
    f (ascendingWord T a b) = ascendingWord T' (a + 1) (b + 1) := by
  rw [ascendingWord, ascendingWord, f.map_list_prod, List.map_map,
    show b + 1 - (a + 1) = b - a from by omega, ← map_range'_succ a (b - a), List.map_map]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range'_1] at hj
  exact hT j (by omega) (by omega)

/-- A descending word maps to the descending word one index up. -/
theorem map_descendingWord {N : Type*} [Monoid N] (f : M →* N) (T : ℕ → M) (T' : ℕ → N) {a b : ℕ}
    (hT : ∀ j, b ≤ j → j < a → f (T j) = T' (j + 1)) :
    f (descendingWord T a b) = descendingWord T' (a + 1) (b + 1) := by
  rw [descendingWord, descendingWord, f.map_list_prod, List.map_map,
    show a + 1 - (b + 1) = a - b from by omega, ← map_range'_succ b (a - b), ← List.map_reverse,
    List.map_map]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_reverse, List.mem_range'_1] at hj
  exact hT j (by omega) (by omega)

/-- **A homomorphism raising every index carries a descending train to the train one index up.**
Both indices of the train are raised; the hypothesis is needed only at the letters the train reads,
all of which have index at least `min a b ≥ 1`. -/
theorem map_trainDown {N : Type*} [Monoid N] (f : M →* N) {T Tinv : ℕ → M} {T' Tinv' : ℕ → N}
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hT : ∀ j, 1 ≤ j → f (T j) = T' (j + 1))
    (hTinv : ∀ j, 1 ≤ j → f (Tinv j) = Tinv' (j + 1)) :
    f (trainDown T Tinv a b) = trainDown T' Tinv' (a + 1) (b + 1) := by
  unfold trainDown
  split_ifs with h h' h'
  · exact map_descendingWord f T T' fun j hj _ => hT j (by omega)
  · omega
  · omega
  · exact map_ascendingWord f Tinv Tinv' fun j hj _ => hTinv j (by omega)

/-- **A homomorphism raising every index carries an ascending train to the train one index up.** -/
theorem map_trainUp {N : Type*} [Monoid N] (f : M →* N) {T Tinv : ℕ → M} {T' Tinv' : ℕ → N}
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hT : ∀ j, 1 ≤ j → f (T j) = T' (j + 1))
    (hTinv : ∀ j, 1 ≤ j → f (Tinv j) = Tinv' (j + 1)) :
    f (trainUp T Tinv a b) = trainUp T' Tinv' (a + 1) (b + 1) := by
  unfold trainUp
  split_ifs with h h' h'
  · exact map_ascendingWord f T T' fun j hj _ => hT j (by omega)
  · omega
  · omega
  · exact map_descendingWord f Tinv Tinv' fun j hj _ => hTinv j (by omega)

/-! ### `φ*₊` on the trains and on `ỹ` -/

variable {k : ℕ}

/-- **`φ*₊` raises both indices of a descending train**: `φ*₊(T_{a↘b}) = T_{a+1↘b+1}`. -/
theorem phiPlusStar_braidTrainDown (hk : 1 ≤ k) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    phiPlusStar k hk (braidTrainDown k a b) = braidTrainDown (k + 1) (a + 1) (b + 1) :=
  map_trainDown _ ha hb (fun _ hj => phiPlusStar_T hk hj) fun _ hj => phiPlusStar_Tbar hk hj

/-- **`φ*₊` raises both indices of an ascending train**: `φ*₊(T_{a↗b}) = T_{a+1↗b+1}`. -/
theorem phiPlusStar_braidTrainUp (hk : 1 ≤ k) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    phiPlusStar k hk (braidTrainUp k a b) = braidTrainUp (k + 1) (a + 1) (b + 1) :=
  map_trainUp _ ha hb (fun _ hj => phiPlusStar_T hk hj) fun _ hj => phiPlusStar_Tbar hk hj

/-- **The closed form of `ỹ_a` based at `1`**: `ỹ_a = T_{a↘1}ỹ_1T_{1↗a}` for `1 ≤ a ≤ k`. This is
`HJO.Braid.braidTrainDown_mul_braidYtilde` at `b = 1`, with the ascending train it produces
cancelled by `HJO.Braid.trainUp_mul_trainUp_self`. -/
theorem braidYtilde_eq_trainDown_one_mul {a : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) :
    braidYtilde k a = braidTrainDown k a 1 * braidYtilde k 1 * braidTrainUp k 1 a := by
  have hsys := isBraidSystem_braidGenT k
  rw [braidTrainDown_mul_braidYtilde ha hak le_rfl (by omega), mul_assoc,
    trainUp_mul_trainUp_self hsys ha hak le_rfl (by omega), mul_one]

/-- **The closed form of `z_a` based at `1`** in the shape the insertion uses. -/
theorem braidGenZ_eq_trainDown_one_mul {a : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) :
    braidGenZ k a = braidTrainDown k a 1 * braidGenZ k 1 * braidTrainUp k 1 a :=
  braidGenZ_eq_trainDown_mul_mul_trainUp k a ha hak

/-- **The `T_1²` discrepancy, half one**: `ỹ_{a+1} = T_{a+1↘2}·T_1·ỹ_1·T_{1↗a+1}`. -/
theorem braidYtilde_succ_eq {a : ℕ} (ha : 1 ≤ a) (hak : a + 1 ≤ k) :
    braidYtilde k (a + 1)
      = braidTrainDown k (a + 1) 2 * braidGenT k 1 * braidYtilde k 1 *
        braidTrainUp k 1 (a + 1) := by
  have hbot : braidTrainDown k (a + 1) 2 * braidGenT k 1 = braidTrainDown k (a + 1) 1 :=
    trainDown_two_mul_gen (isBraidSystem_braidGenT k) (by omega) hak
  rw [braidYtilde_eq_trainDown_one_mul (by omega) hak, ← hbot]

/-- **`φ*₊` on `ỹ_1`**: `φ*₊(ỹ_1) = T̄_1ỹ_1T_1`, Mellit's own formula. The image is the
conjugate of `ỹ_1` at the *same* index by `T_1`, and not `ỹ_2`. -/
theorem phiPlusStar_braidYtilde_one (hk : 1 ≤ k) :
    phiPlusStar k hk (braidYtilde k 1)
      = braidGenTinv (k + 1) 1 * braidYtilde (k + 1) 1 * braidGenT (k + 1) 1 := by
  have hsys := isBraidSystem_braidGenT (k + 1)
  have hsplit : braidTrainUp (k + 1) 1 (k + 1)
      = braidGenT (k + 1) 1 * braidTrainUp (k + 1) 2 (k + 1) := by
    have hglue : braidTrainUp (k + 1) 1 2 * braidTrainUp (k + 1) 2 (k + 1)
        = braidTrainUp (k + 1) 1 (k + 1) :=
      trainUp_mul_trainUp hsys (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [show braidTrainUp (k + 1) 1 2 = braidGenT (k + 1) 1 from
      trainUp_self_succ _ _ 1] at hglue
    exact hglue.symm
  have hsplit' : braidTrainUp (k + 1) (k + 1) 1
      = braidTrainUp (k + 1) (k + 1) 2 * braidGenTinv (k + 1) 1 := by
    have hglue : braidTrainUp (k + 1) (k + 1) 2 * braidTrainUp (k + 1) 2 1
        = braidTrainUp (k + 1) (k + 1) 1 :=
      trainUp_mul_trainUp hsys (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [show braidTrainUp (k + 1) 2 1 = braidGenTinv (k + 1) 1 from
      trainUp_succ_self _ _ 1] at hglue
    exact hglue.symm
  have h11 : braidGenTinv (k + 1) 1 * braidGenT (k + 1) 1 = 1 :=
    braidGenT_inv_mul le_rfl (by omega)
  have h11' : braidGenT (k + 1) 1 * braidGenTinv (k + 1) 1 = 1 :=
    braidGenT_mul_inv le_rfl (by omega)
  rw [braidYtilde, braidTrainDown_self, one_mul, map_mul, map_mul,
    phiPlusStar_braidTrainUp hk (by omega) (by omega),
    phiPlusStar_braidTrainUp hk (by omega) (by omega), phiPlusStar_y hk (by omega),
    braidYtilde, braidTrainDown_self, one_mul, hsplit, hsplit']
  simp only [mul_assoc]
  rw [mul_mul_cancel_of_mul_eq_one h11]
  simp only [← mul_assoc]
  rw [mul_assoc _ (braidGenTinv (k + 1) 1) (braidGenT (k + 1) 1), h11, mul_one]

/-- **The `T_1²` discrepancy, half two — the absorption**:
`φ*₊(ỹ_a) = T_{a+1↘2}·T̄_1·ỹ_1·T_{1↗a+1}` for `1 ≤ a ≤ k`.

Against `HJO.Braid.braidYtilde_succ_eq` this says `φ*₊(ỹ_a)` and `ỹ_{a+1}` differ exactly by the
middle letter, `T̄_1` against `T_1`, that is by `T_1²`. See the module docstring. -/
theorem phiPlusStar_braidYtilde (hk : 1 ≤ k) {a : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) :
    phiPlusStar k hk (braidYtilde k a)
      = braidTrainDown (k + 1) (a + 1) 2 * braidGenTinv (k + 1) 1 * braidYtilde (k + 1) 1 *
        braidTrainUp (k + 1) 1 (a + 1) := by
  have hsys := isBraidSystem_braidGenT (k + 1)
  have hsplit : braidGenT (k + 1) 1 * braidTrainUp (k + 1) 2 (a + 1)
      = braidTrainUp (k + 1) 1 (a + 1) := by
    have hglue : braidTrainUp (k + 1) 1 2 * braidTrainUp (k + 1) 2 (a + 1)
        = braidTrainUp (k + 1) 1 (a + 1) :=
      trainUp_mul_trainUp hsys (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rwa [show braidTrainUp (k + 1) 1 2 = braidGenT (k + 1) 1 from trainUp_self_succ _ _ 1] at hglue
  rw [braidYtilde_eq_trainDown_one_mul ha hak, map_mul, map_mul,
    phiPlusStar_braidTrainDown hk ha (by omega), phiPlusStar_braidTrainUp hk (by omega) ha,
    phiPlusStar_braidYtilde_one hk]
  simp only [mul_assoc]
  rw [hsplit]

/-! ### `z_1` and `ỹ_1` against a descending train -/

/-- **`z_1` commutes with `T_{c↘2}`**: every letter of that train is `T_j` with `j ≥ 2`, and the
fifth family of `HJO.Braid.BraidMonoid` commutes `z_1` past each of them. -/
theorem braidGenZ_one_comm_trainDown {c : ℕ} (hc : 2 ≤ c) (hck : c ≤ k) :
    braidGenZ k 1 * braidTrainDown k c 2 = braidTrainDown k c 2 * braidGenZ k 1 :=
  comm_trainDown hc fun j hj hj' =>
    braidGenZ_comm_T le_rfl (by omega) (by omega) (by omega) (by omega) (by omega)

/-- **`ỹ_1` commutes with `T_{r+1}` for `r ≥ 1`**: writing `ỹ_1 = T_{1↗k}y_kT_{k↗1}` and using
`HJO.Braid.trainUp_mul_gen`, the letter `T_{r+1}` becomes `T_r` inside the conjugation, where the
fourth family of `HJO.Braid.BraidMonoid` commutes it past `y_k`. -/
theorem braidYtilde_one_comm_gen {r : ℕ} (hr : 1 ≤ r) (hrk : r + 2 ≤ k) :
    braidYtilde k 1 * braidGenT k (r + 1) = braidGenT k (r + 1) * braidYtilde k 1 := by
  have hsys := isBraidSystem_braidGenT k
  have hshift : braidTrainUp k 1 k * braidGenT k r = braidGenT k (r + 1) * braidTrainUp k 1 k :=
    trainUp_mul_gen hsys (by omega) (by omega) (by omega) le_rfl
  have hshift' : braidGenT k r * braidTrainUp k k 1 = braidTrainUp k k 1 * braidGenT k (r + 1) :=
    conj_swap (trainUp_mul_trainUp_self hsys (by omega) (by omega) (by omega) (by omega))
      (trainUp_mul_trainUp_self hsys (by omega) (by omega) (by omega) (by omega)) hshift
  have hy : braidGenY k k * braidGenT k r = braidGenT k r * braidGenY k k :=
    braidGenY_comm_T (by omega) le_rfl (by omega) (by omega) (by omega) (by omega)
  rw [braidYtilde, braidTrainDown_self, one_mul]
  calc braidTrainUp k 1 k * braidGenY k k * braidTrainUp k k 1 * braidGenT k (r + 1)
      = braidTrainUp k 1 k * braidGenY k k * (braidTrainUp k k 1 * braidGenT k (r + 1)) :=
        mul_assoc _ _ _
    _ = braidTrainUp k 1 k * braidGenY k k * (braidGenT k r * braidTrainUp k k 1) := by
        rw [← hshift']
    _ = braidTrainUp k 1 k * (braidGenY k k * braidGenT k r) * braidTrainUp k k 1 := by
        simp only [mul_assoc]
    _ = braidTrainUp k 1 k * (braidGenT k r * braidGenY k k) * braidTrainUp k k 1 := by rw [hy]
    _ = braidTrainUp k 1 k * braidGenT k r * (braidGenY k k * braidTrainUp k k 1) := by
        simp only [mul_assoc]
    _ = braidGenT k (r + 1) * braidTrainUp k 1 k * (braidGenY k k * braidTrainUp k k 1) := by
        rw [hshift]
    _ = braidGenT k (r + 1) * (braidTrainUp k 1 k * braidGenY k k * braidTrainUp k k 1) := by
        simp only [mul_assoc]

/-- **`ỹ_1` commutes with `T_{c↘2}`**, by `HJO.Braid.braidYtilde_one_comm_gen` at each letter. -/
theorem braidYtilde_one_comm_trainDown {c : ℕ} (hc : 2 ≤ c) (hck : c ≤ k) :
    braidYtilde k 1 * braidTrainDown k c 2 = braidTrainDown k c 2 * braidYtilde k 1 := by
  refine comm_trainDown hc fun j hj hj' => ?_
  obtain ⟨r, rfl⟩ : ∃ r, j = r + 1 := ⟨j - 1, by omega⟩
  exact braidYtilde_one_comm_gen (by omega) (by omega)

/-! ### The normal forms -/

/-- **The normal form of the `ỹ` branch.** For `1 ≤ a ≤ k` and `1 ≤ a' < i' ≤ k + 1`,
`T_{i'↘1}·T_{a'+1↘a+1}·φ*₊(ỹ_a) = T_{a'↘1}·ỹ_1·T_{i'↘2}·T_{1↗a+1}` in `𝔹_{k+1}^+(𝕋_0)`.

This is where the `T_1²` of `HJO.Braid.phiPlusStar_braidYtilde` is absorbed: the `T̄_1` it carries
meets the bottom letter of `T_{i'↘1}`, which the overtaking of
`HJO.Braid.trainDown_one_mul_trainDown_one` has brought to the right of the shorter train. -/
theorem trainDown_one_mul_trainDown_mul_phiPlusStar_braidYtilde (hk : 1 ≤ k) {a a' i' : ℕ}
    (ha : 1 ≤ a) (hak : a ≤ k) (ha' : 1 ≤ a') (ha'i : a' < i') (hik : i' ≤ k + 1) :
    braidTrainDown (k + 1) i' 1 * braidTrainDown (k + 1) (a' + 1) (a + 1) *
        phiPlusStar k hk (braidYtilde k a)
      = braidTrainDown (k + 1) a' 1 * braidYtilde (k + 1) 1 * braidTrainDown (k + 1) i' 2 *
        braidTrainUp (k + 1) 1 (a + 1) := by
  have hsys := isBraidSystem_braidGenT (k + 1)
  have hglue : braidTrainDown (k + 1) (a' + 1) (a + 1) * braidTrainDown (k + 1) (a + 1) 2
      = braidTrainDown (k + 1) (a' + 1) 2 :=
    trainDown_mul_trainDown hsys (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hover : braidTrainDown (k + 1) a' 1 * braidTrainDown (k + 1) i' 1
      = braidTrainDown (k + 1) i' 1 * braidTrainDown (k + 1) (a' + 1) 2 :=
    trainDown_one_mul_trainDown_one hsys ha' ha'i hik
  have hbot : braidTrainDown (k + 1) i' 2 * braidGenT (k + 1) 1 = braidTrainDown (k + 1) i' 1 :=
    trainDown_two_mul_gen hsys (by omega) hik
  have h11 : braidGenT (k + 1) 1 * braidGenTinv (k + 1) 1 = 1 :=
    braidGenT_mul_inv le_rfl (by omega)
  have hcomm : braidYtilde (k + 1) 1 * braidTrainDown (k + 1) i' 2
      = braidTrainDown (k + 1) i' 2 * braidYtilde (k + 1) 1 :=
    braidYtilde_one_comm_trainDown (by omega) hik
  have e1 : ∀ X, braidTrainDown (k + 1) (a' + 1) (a + 1) * (braidTrainDown (k + 1) (a + 1) 2 * X)
      = braidTrainDown (k + 1) (a' + 1) 2 * X := fun X => by
    simp only [← mul_assoc]; rw [hglue]
  have e2 : ∀ X, braidTrainDown (k + 1) i' 1 * (braidTrainDown (k + 1) (a' + 1) 2 * X)
      = braidTrainDown (k + 1) a' 1 * (braidTrainDown (k + 1) i' 1 * X) := fun X => by
    simp only [← mul_assoc]; rw [← hover]
  have e3 : ∀ X, braidTrainDown (k + 1) i' 1 * (braidGenTinv (k + 1) 1 * X)
      = braidTrainDown (k + 1) i' 2 * X := fun X => by
    simp only [← mul_assoc]
    rw [← hbot]
    simp only [mul_assoc]
    rw [mul_mul_cancel_of_mul_eq_one h11]
  have e4 : ∀ X, braidTrainDown (k + 1) i' 2 * (braidYtilde (k + 1) 1 * X)
      = braidYtilde (k + 1) 1 * (braidTrainDown (k + 1) i' 2 * X) := fun X => by
    simp only [← mul_assoc]; rw [← hcomm]
  rw [phiPlusStar_braidYtilde hk ha hak]
  simp only [mul_assoc]
  rw [e1, e2, e3, e4]

/-- **The normal form of the `z` branch.** For `1 ≤ a ≤ k`, `1 ≤ i' ≤ a' ≤ k`,
`T_{i'↘1}·T_{a'+1↘a+1}·z_{a+1} = T_{a'+1↘1}·z_1·T_{i'+1↘2}·T_{1↗a+1}` in `𝔹_{k+1}^+(𝕋_0)`.

Here `z_{a+1}` is `φ*₊(z_a)` outright — the `z` half of `HJO.Braid.phiPlusStar` needs no
absorption — so the only work is the overtaking, which raises `i'` to `i'+1` as it passes. -/
theorem trainDown_one_mul_trainDown_mul_braidGenZ (hk : 1 ≤ k) {a a' i' : ℕ} (ha : 1 ≤ a)
    (hak : a ≤ k) (hi' : 1 ≤ i') (hia' : i' ≤ a') (ha'k : a' ≤ k) :
    braidTrainDown (k + 1) i' 1 * braidTrainDown (k + 1) (a' + 1) (a + 1) *
        braidGenZ (k + 1) (a + 1)
      = braidTrainDown (k + 1) (a' + 1) 1 * braidGenZ (k + 1) 1 *
        braidTrainDown (k + 1) (i' + 1) 2 * braidTrainUp (k + 1) 1 (a + 1) := by
  have hsys := isBraidSystem_braidGenT (k + 1)
  have hglue : braidTrainDown (k + 1) (a' + 1) (a + 1) * braidTrainDown (k + 1) (a + 1) 1
      = braidTrainDown (k + 1) (a' + 1) 1 :=
    trainDown_mul_trainDown hsys (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hover : braidTrainDown (k + 1) i' 1 * braidTrainDown (k + 1) (a' + 1) 1
      = braidTrainDown (k + 1) (a' + 1) 1 * braidTrainDown (k + 1) (i' + 1) 2 :=
    trainDown_one_mul_trainDown_one hsys hi' (by omega) (by omega)
  have hcomm : braidGenZ (k + 1) 1 * braidTrainDown (k + 1) (i' + 1) 2
      = braidTrainDown (k + 1) (i' + 1) 2 * braidGenZ (k + 1) 1 :=
    braidGenZ_one_comm_trainDown (by omega) (by omega)
  have e1 : ∀ X, braidTrainDown (k + 1) (a' + 1) (a + 1) * (braidTrainDown (k + 1) (a + 1) 1 * X)
      = braidTrainDown (k + 1) (a' + 1) 1 * X := fun X => by
    simp only [← mul_assoc]; rw [hglue]
  have e2 : ∀ X, braidTrainDown (k + 1) i' 1 * (braidTrainDown (k + 1) (a' + 1) 1 * X)
      = braidTrainDown (k + 1) (a' + 1) 1 * (braidTrainDown (k + 1) (i' + 1) 2 * X) :=
    fun X => by simp only [← mul_assoc]; rw [hover]
  have e3 : ∀ X, braidTrainDown (k + 1) (i' + 1) 2 * (braidGenZ (k + 1) 1 * X)
      = braidGenZ (k + 1) 1 * (braidTrainDown (k + 1) (i' + 1) 2 * X) := fun X => by
    simp only [← mul_assoc]; rw [← hcomm]
  rw [braidGenZ_eq_trainDown_one_mul (a := a + 1) (by omega) (by omega)]
  simp only [mul_assoc]
  rw [e1, e2, e3]

/-! ### The four one-move identities -/

/-- **One move, `ỹ` branch, the inserted point's rank unchanged.** For `1 ≤ a`, `a + 1 ≤ i`,
`1 ≤ a' < i`, `a ≤ k`, `a' ≤ k`, `i ≤ k + 1`:
`T_{a'↘a}ỹ_a·T_{i↘1} = T_{i↘1}·T_{a'+1↘a+1}·φ*₊(ỹ_a)`.

The moving point stays on the same side of the inserted one, so both of its ranks in the larger
tuple are the ranks in the smaller one, and the inserted point keeps its rank `i`. -/
theorem trainDown_mul_braidYtilde_mul_trainDown_one_of_le (hk : 1 ≤ k) {a a' i : ℕ} (ha : 1 ≤ a)
    (hai : a + 1 ≤ i) (ha' : 1 ≤ a') (ha'i : a' < i) (hak : a ≤ k) (ha'k : a' ≤ k)
    (hik : i ≤ k + 1) :
    braidTrainDown (k + 1) a' a * braidYtilde (k + 1) a * braidTrainDown (k + 1) i 1
      = braidTrainDown (k + 1) i 1 * braidTrainDown (k + 1) (a' + 1) (a + 1) *
        phiPlusStar k hk (braidYtilde k a) := by
  have hsys := isBraidSystem_braidGenT (k + 1)
  have hglue : braidTrainDown (k + 1) a' a * braidTrainDown (k + 1) a 1
      = braidTrainDown (k + 1) a' 1 :=
    trainDown_mul_trainDown hsys (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hreg : braidTrainDown (k + 1) i 2 * braidTrainUp (k + 1) 1 (a + 1)
      = braidTrainUp (k + 1) 1 a * braidTrainDown (k + 1) i 1 :=
    trainDown_two_mul_trainUp_one_of_le hsys a ha (by omega) hik
  have e1 : ∀ X, braidTrainDown (k + 1) a' a * (braidTrainDown (k + 1) a 1 * X)
      = braidTrainDown (k + 1) a' 1 * X := fun X => by simp only [← mul_assoc]; rw [hglue]
  rw [trainDown_one_mul_trainDown_mul_phiPlusStar_braidYtilde hk ha hak ha' ha'i hik,
    braidYtilde_eq_trainDown_one_mul (k := k + 1) ha (by omega)]
  simp only [mul_assoc]
  rw [e1, hreg]

/-- **One move, `ỹ` branch, the inserted point overtaken.** For `1 ≤ i ≤ a`, `1 ≤ a' ≤ i`,
`a ≤ k`, `a' ≤ k`, `i + 1 ≤ k + 1`:
`T_{a'↘a+1}ỹ_{a+1}·T_{i↘1} = T_{i+1↘1}·T_{a'+1↘a+1}·φ*₊(ỹ_a)`.

The moving point crosses the inserted one downwards, so its rank before the move is one more than
in the smaller tuple and the inserted point's rank rises from `i` to `i + 1`. -/
theorem trainDown_mul_braidYtilde_mul_trainDown_one_of_ge (hk : 1 ≤ k) {a a' i : ℕ} (hi : 1 ≤ i)
    (hia : i ≤ a) (ha' : 1 ≤ a') (ha'i : a' ≤ i) (hak : a ≤ k) (ha'k : a' ≤ k) :
    braidTrainDown (k + 1) a' (a + 1) * braidYtilde (k + 1) (a + 1) *
        braidTrainDown (k + 1) i 1
      = braidTrainDown (k + 1) (i + 1) 1 * braidTrainDown (k + 1) (a' + 1) (a + 1) *
        phiPlusStar k hk (braidYtilde k a) := by
  have hsys := isBraidSystem_braidGenT (k + 1)
  have hglue : braidTrainDown (k + 1) a' (a + 1) * braidTrainDown (k + 1) (a + 1) 1
      = braidTrainDown (k + 1) a' 1 :=
    trainDown_mul_trainDown hsys (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hreg : braidTrainDown (k + 1) (i + 1) 2 * braidTrainUp (k + 1) 1 (a + 1)
      = braidTrainUp (k + 1) 1 (a + 1) * braidTrainDown (k + 1) i 1 :=
    trainDown_two_mul_trainUp_one_of_ge hsys hi a hia (by omega)
  have e1 : ∀ X, braidTrainDown (k + 1) a' (a + 1) * (braidTrainDown (k + 1) (a + 1) 1 * X)
      = braidTrainDown (k + 1) a' 1 * X := fun X => by simp only [← mul_assoc]; rw [hglue]
  rw [trainDown_one_mul_trainDown_mul_phiPlusStar_braidYtilde hk (by omega) hak ha' (by omega)
      (by omega),
    braidYtilde_eq_trainDown_one_mul (k := k + 1) (a := a + 1) (by omega) (by omega)]
  simp only [mul_assoc]
  rw [e1, hreg]

/-- **One move, `z` branch, the inserted point's rank unchanged.** For `1 ≤ i ≤ a`, `i ≤ a'`,
`a ≤ k`, `a' ≤ k`:
`T_{a'+1↘a+1}z_{a+1}·T_{i↘1} = T_{i↘1}·T_{a'+1↘a+1}·φ*₊(z_a)`.

Both ranks of the moving point are one more than in the smaller tuple — it is above the inserted
point before the move and stays above it — so the whole letter commutes with the inserted train. -/
theorem trainDown_mul_braidGenZ_mul_trainDown_one_of_le (hk : 1 ≤ k) {a a' i : ℕ} (hi : 1 ≤ i)
    (hia : i ≤ a) (hia' : i ≤ a') (hak : a ≤ k) (ha'k : a' ≤ k) :
    braidTrainDown (k + 1) (a' + 1) (a + 1) * braidGenZ (k + 1) (a + 1) *
        braidTrainDown (k + 1) i 1
      = braidTrainDown (k + 1) i 1 * braidTrainDown (k + 1) (a' + 1) (a + 1) *
        phiPlusStar k hk (braidGenZ k a) := by
  have hsys := isBraidSystem_braidGenT (k + 1)
  have hreg : braidTrainDown (k + 1) (i + 1) 2 * braidTrainUp (k + 1) 1 (a + 1)
      = braidTrainUp (k + 1) 1 (a + 1) * braidTrainDown (k + 1) i 1 :=
    trainDown_two_mul_trainUp_one_of_ge hsys hi a hia (by omega)
  have hglue : braidTrainDown (k + 1) (a' + 1) (a + 1) * braidTrainDown (k + 1) (a + 1) 1
      = braidTrainDown (k + 1) (a' + 1) 1 :=
    trainDown_mul_trainDown hsys (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have e1 : ∀ X, braidTrainDown (k + 1) (a' + 1) (a + 1) * (braidTrainDown (k + 1) (a + 1) 1 * X)
      = braidTrainDown (k + 1) (a' + 1) 1 * X := fun X => by simp only [← mul_assoc]; rw [hglue]
  rw [phiPlusStar_z hk (by omega),
    trainDown_one_mul_trainDown_mul_braidGenZ hk (by omega) hak hi hia' ha'k,
    braidGenZ_eq_trainDown_one_mul (k := k + 1) (a := a + 1) (by omega) (by omega)]
  simp only [mul_assoc]
  rw [e1, hreg]

/-- **One move, `z` branch, the inserted point overtaken.** For `1 ≤ a ≤ e ≤ a'`, `a ≤ k`,
`a' ≤ k`:
`T_{a'+1↘a}z_a·T_{e+1↘1} = T_{e↘1}·T_{a'+1↘a+1}·φ*₊(z_a)`.

The moving point crosses the inserted one upwards, so its rank before the move is the rank in the
smaller tuple while its rank after is one more, and the inserted point's rank falls from `e + 1` to
`e`. -/
theorem trainDown_mul_braidGenZ_mul_trainDown_one_of_ge (hk : 1 ≤ k) {a a' e : ℕ} (ha : 1 ≤ a)
    (hae : a ≤ e) (hea' : e ≤ a') (hak : a ≤ k) (ha'k : a' ≤ k) :
    braidTrainDown (k + 1) (a' + 1) a * braidGenZ (k + 1) a *
        braidTrainDown (k + 1) (e + 1) 1
      = braidTrainDown (k + 1) e 1 * braidTrainDown (k + 1) (a' + 1) (a + 1) *
        phiPlusStar k hk (braidGenZ k a) := by
  have hsys := isBraidSystem_braidGenT (k + 1)
  have hglue : braidTrainDown (k + 1) (a' + 1) a * braidTrainDown (k + 1) a 1
      = braidTrainDown (k + 1) (a' + 1) 1 :=
    trainDown_mul_trainDown hsys (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hreg : braidTrainDown (k + 1) (e + 1) 2 * braidTrainUp (k + 1) 1 (a + 1)
      = braidTrainUp (k + 1) 1 a * braidTrainDown (k + 1) (e + 1) 1 :=
    trainDown_two_mul_trainUp_one_of_le hsys a ha (by omega) (by omega)
  have e1 : ∀ X, braidTrainDown (k + 1) (a' + 1) a * (braidTrainDown (k + 1) a 1 * X)
      = braidTrainDown (k + 1) (a' + 1) 1 * X := fun X => by simp only [← mul_assoc]; rw [hglue]
  rw [phiPlusStar_z hk (by omega),
    trainDown_one_mul_trainDown_mul_braidGenZ hk ha hak (by omega) hea' ha'k,
    braidGenZ_eq_trainDown_one_mul (k := k + 1) (a := a) ha (by omega)]
  simp only [mul_assoc]
  rw [e1, hreg]

end HJO.Braid

end
