/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidLetterCount
public import HJO.Shuffle.ColouringBraidData
public meta import HJO.Attr

/-! # What a rigid rotation of the position tuple does to the special braid

`HJO.Mellit.sweepTheta_eq_div` shows that a level drop acts on the positions `v` of
`HJO.Mellit.braidDataOfColouring` as a **rigid rotation** of `ℝ/ℤ`, by `m/D` with `m ≥ 1`, leaving
the rank and — at an event of type `E` — every multiplicity alone. The type-`C`, type-`D` and
type-`E` clauses of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` therefore all need to know
how `HJO.Braid.specialBraid` responds to such a rotation, and no such statement is available.

This file answers that question, and the answer is **not** an invariance and not a conjugation. It
is an exact count of `z` letters against `ỹ` letters.

## The invariant that sees the rotation

`HJO.Braid.letterCount` counts `y` and `z` letters together, so it cannot see the rotation at all:
by `HJO.Braid.letterCount_specialBraid` it is `∑_i (α_i - 1)`, which reads only the multiplicities.
But every relation of `HJO.Braid.BraidMonoid` preserves the number of `z_1` letters **separately** —
the one mixed relation `𝗓_1T_1𝗒_1T̄_1 = T̄_1𝗒_1T̄_1𝗓_1` has one of each on both sides — so there is
a second homomorphism `𝔹_k^+(𝕋_0) → (ℕ, +)`, `HJO.Braid.zCount`, and `HJO.Braid.braidStep`
contributes to it exactly when the moving point is *below* the puncture.

## Main definitions

* `HJO.Braid.zWeightHom`, `HJO.Braid.zCount` — the `z`-counting homomorphism and its additive
  reading.
* `HJO.Braid.belowCount` — how many of the first `n` iterates of `nx_θ` at `x` lie below `θ`.

## Main results

* `HJO.Braid.zCount_braidStep` — one move contributes a `z` exactly when the moving entry is below
  the puncture, whatever the two ranks are.
* `HJO.Braid.zCount_specialBraid` — `ζ(B_{s,v,α}) = ∑_i` (the number of moves of the `i`-th point
  made from below the puncture).
* `HJO.Braid.belowCount_eq_neg_floor` — **the closed form**: that number is `-⌊v_i - (α_i-1)θ⌋`. So
  the number of `z` letters a point contributes is the number of integers its *unwrapped* trajectory
  crosses, which is what a `z` letter means geometrically.
* `HJO.Braid.zCount_specialBraid_rotate_sub` — **the rotation lemma.** If `v'_i = {v_i + c}` for one
  common `c`, with the same multiplicities and both tuples special-braid data, then
  `ζ(B_{s,v',α}) - ζ(B_{s,v,α}) = ∑_i (⌊v_i + c⌋ - ⌊f_i + c⌋)` with `f_i` the final position
  `nx_θ^{α_i-1}(v_i)` of `HJO.Braid.positionPair`.
* `HJO.Braid.zCount_specialBraid_rotate_sub_card` — the same read as a count, for `0 ≤ c < 1`: the
  rotation **gains** one `z` for each *initial* position it carries past `0` and **loses** one for
  each *final* position it carries past `0`.
* `HJO.Braid.exists_rotation_specialBraid_ne` — **a rigid rotation is visible**: there are
  special-braid data and a rotation for which the two special braids are different elements of
  `𝔹_k^+(𝕋_0)`. So no rotation-invariance statement is available to
  `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, and the conditional recorded under
  `HJO.Mellit.sweepTheta_eq_div` — that an invisible rotation would force `D_{η_-,c} = D_{η_+,c}` —
  has no hypothesis left to run on. It does **not** decide the rotations that actually occur: the
  witness has `k = 1` and `c = 1/5`, not a rotation of the form `m/D` coming from a level drop.

## What this settles about `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, and what not

It settles the *shape* of the missing move, and it is a bookkeeping identity rather than a braid
relation: the rotation neither fixes `B_{s,v,α}` nor conjugates it, and the two braids need not even
have the same number of `z` letters. Since `HJO.Sweep.braidRep` sends `z_1` to `(qu)^{-1}z_1` while
the `ỹ` letters go to `y`-multiplications carrying no explicit `u`, that difference is the sort of
thing the `u` of rule `E` and the `Δ` of rule `C` would have to come from. It is *not* a proof that
the `u`-degree of `R_±` is the `z`-count: `HJO.Sweep.zopOneStar` itself reads `u`, through
`HJO.Sweep.cycleShift`, so the `u`-degree of the image is not a function of the `z`-count alone.

It does **not** determine `B_{s,v',α}` from `B_{s,v,α}`. `HJO.Braid.zCount` is one functional on a
monoid presented on `2k` letters, and two braids with equal `z`-count and equal letter count can
still differ. What is proved here is that the *first* invariant one reaches already separates them,
so the missing clauses cannot be closed by any invariance argument: a clause must predict the
change in `z`-count, and `HJO.Braid.zCount_specialBraid_rotate_sub_card` is what it must predict.

## References

The file concerns `HJO.Braid.zCount_mul`, used by
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, together with `HJO.Mellit.sweepTheta_eq_div`,
`HJO.Braid.BraidMonoid`, `HJO.Braid.braidStep`, `HJO.Braid.specialBraid`,
`HJO.Braid.IsSpecialBraidData`, `HJO.Braid.positionPair`, `HJO.Sweep.braidRep`. Transcribing
A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Braid

/-! ### The `z`-weight of a letter -/

/-- **The `z`-weight of a letter**: `z_1` weighs one, and every other letter — the braid letters and
`y_1` — weighs nothing. This is `HJO.Braid.weightLetter` with the `y` half removed, and the point of
removing it is that the difference between a `z` letter and a `ỹ` letter is exactly what a rigid
rotation of the position tuple changes. -/
def zWeightLetter : Letter → Multiplicative ℕ
  | Letter.T _ => 1
  | Letter.Tbar _ => 1
  | Letter.y1 => 1
  | Letter.z1 => Multiplicative.ofAdd 1

/-- The `z`-weight of a word of `F_k`: the number of `z_1` letters in it. -/
def zWeightWord : FreeMonoid Letter →* Multiplicative ℕ := FreeMonoid.lift zWeightLetter

@[simp]
theorem zWeightLetter_T (i : ℕ) : zWeightLetter (Letter.T i) = 1 := rfl

@[simp]
theorem zWeightLetter_Tbar (i : ℕ) : zWeightLetter (Letter.Tbar i) = 1 := rfl

@[simp]
theorem zWeightLetter_y1 : zWeightLetter Letter.y1 = 1 := rfl

theorem zWeightLetter_z1 : zWeightLetter Letter.z1 = Multiplicative.ofAdd 1 := rfl

@[simp]
theorem zWeightWord_of (c : Letter) : zWeightWord (FreeMonoid.of c) = zWeightLetter c := rfl

@[simp]
theorem zWeightWord_T (i : ℕ) : zWeightWord (FreeMonoid.of (Letter.T i)) = 1 := rfl

@[simp]
theorem zWeightWord_Tbar (i : ℕ) : zWeightWord (FreeMonoid.of (Letter.Tbar i)) = 1 := rfl

@[simp]
theorem zWeightWord_y1 : zWeightWord (FreeMonoid.of Letter.y1) = 1 := rfl

/-- **`𝗒_i` carries no `z`**, at every index: `HJO.Braid.yWord` is a word in `T̄` and `y_1`. -/
@[simp]
theorem zWeightWord_yWord : ∀ i, zWeightWord (yWord i) = 1
  | 0 => by rw [show yWord 0 = 1 from rfl, map_one]
  | 1 => rfl
  | (i + 2) => by
    rw [yWord_succ, map_mul, map_mul, zWeightWord_yWord (i + 1), zWeightWord_Tbar]
    simp

/-- **`𝗓_i` carries exactly one `z`**, for `i ≥ 1`. -/
theorem zWeightWord_zWord : ∀ i, 1 ≤ i → zWeightWord (zWord i) = Multiplicative.ofAdd 1
  | 1, _ => rfl
  | (i + 2), _ => by
    rw [zWord_succ, map_mul, map_mul, zWeightWord_zWord (i + 1) (by omega), zWeightWord_T,
      one_mul, mul_one]

/-! ### The `z`-weight descends to the quotient -/

/-- **Every relation of `HJO.Braid.BraidMonoid` preserves the number of `z` letters**, at every rank
`k ≥ 1`.

The only relation that mixes the two loop families is `𝗓_1T_1𝗒_1T̄_1 = T̄_1𝗒_1T̄_1𝗓_1`, and it has
one `z` on each side; every other family either lives in the braid letters or moves one loop word
past letters of `z`-weight zero. As for `HJO.Braid.weightWord_respects`, `1 ≤ k` is what keeps
`HJO.Braid.BraidRel.out_of_rank` from firing on `z_1`. -/
theorem zWeightWord_respects {k : ℕ} (hk : 1 ≤ k) {x y : FreeMonoid Letter} (h : BraidRel k x y) :
    zWeightWord x = zWeightWord y := by
  cases h with
  | mul_inv i _ _ => simp
  | inv_mul i _ _ => simp
  | braid i _ _ => simp
  | far_comm i j _ _ _ => simp
  | yWord_comm_T i j hi _ _ _ _ _ => simp
  | zWord_comm_T i j hi _ _ _ _ _ =>
    rw [map_mul, map_mul, zWeightWord_zWord i hi, zWeightWord_T, one_mul, mul_one]
  | yWord_comm i j hi _ hj _ => simp
  | zWord_comm i j hi _ hj _ =>
    rw [map_mul, map_mul, zWeightWord_zWord i hi, zWeightWord_zWord j hj]
  | zy _ =>
    simp only [map_mul, zWeightWord_T, zWeightWord_Tbar, zWeightWord_yWord,
      zWeightWord_zWord 1 le_rfl, one_mul, mul_one]
  | out_of_rank c hc =>
    cases c with
    | T i => simp
    | Tbar i => simp
    | y1 => exact absurd hk hc
    | z1 => exact absurd hk hc

/-- **The `z`-counting homomorphism of `HJO.Braid.BraidMonoid`**, `𝔹_k^+(𝕋_0) →* Multiplicative ℕ`,
for `k ≥ 1`. -/
def zWeightHom (k : ℕ) (hk : 1 ≤ k) : BraidMonoid k →* Multiplicative ℕ :=
  Con.lift _ zWeightWord
    (Con.conGen_le.2 fun _x _y hxy => (Con.ker_rel _).2 (zWeightWord_respects hk hxy))

@[simp]
theorem zWeightHom_apply (k : ℕ) (hk : 1 ≤ k) (x : FreeMonoid Letter) :
    zWeightHom k hk (toBraidMonoid k x) = zWeightWord x :=
  Con.lift_coe _ _

/-- **The `z`-count `ζ` of an element of `𝔹_k^+(𝕋_0)`**: the number of `z_1` letters in any word
naming it, which the relations make well defined. -/
def zCount (k : ℕ) (hk : 1 ≤ k) (x : BraidMonoid k) : ℕ :=
  Multiplicative.toAdd (zWeightHom k hk x)

@[simp]
theorem zCount_one (k : ℕ) (hk : 1 ≤ k) : zCount k hk 1 = 0 := by
  rw [zCount, map_one]
  rfl

@[hjo "lem_braid_rotation_zcount"]
theorem zCount_mul {k : ℕ} (hk : 1 ≤ k) (x y : BraidMonoid k) :
    zCount k hk (x * y) = zCount k hk x + zCount k hk y := by
  rw [zCount, zCount, zCount, map_mul]
  rfl

/-! ### The `z`-count of each named element -/

@[simp, hjo "lem_braid_rotation_zcount"]
theorem zCount_braidGenT {k : ℕ} (hk : 1 ≤ k) (i : ℕ) : zCount k hk (braidGenT k i) = 0 := by
  rw [zCount, braidGenT, zWeightHom_apply, zWeightWord_T]
  rfl

@[simp, hjo "lem_braid_rotation_zcount"]
theorem zCount_braidGenTinv {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    zCount k hk (braidGenTinv k i) = 0 := by
  rw [zCount, braidGenTinv, zWeightHom_apply, zWeightWord_Tbar]
  rfl

/-- **`ζ(y_i) = 0`**: a `y` letter is not a `z` letter, which is the whole content of this
homomorphism. -/
@[simp, hjo "lem_braid_rotation_zcount"]
theorem zCount_braidGenY {k : ℕ} (hk : 1 ≤ k) (i : ℕ) : zCount k hk (braidGenY k i) = 0 := by
  rw [zCount, braidGenY, zWeightHom_apply, zWeightWord_yWord i]
  rfl

/-- **`ζ(z_i) = 1`** for `i ≥ 1`. -/
@[simp, hjo "lem_braid_rotation_zcount"]
theorem zCount_braidGenZ {k : ℕ} (hk : 1 ≤ k) {i : ℕ} (hi : 1 ≤ i) :
    zCount k hk (braidGenZ k i) = 1 := by
  rw [zCount, braidGenZ, zWeightHom_apply, zWeightWord_zWord i hi]
  rfl

theorem zCount_prod_eq_zero {k : ℕ} (hk : 1 ≤ k) {α : Type*} (l : List α)
    (f : α → BraidMonoid k) (hf : ∀ x, zCount k hk (f x) = 0) :
    zCount k hk ((l.map f).prod) = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.prod_cons, zCount_mul, hf a, ih]

/-- **A train carries no `z`**: `HJO.Braid.trainUp` is a word in the braid letters alone. -/
@[simp]
theorem zCount_braidTrainUp {k : ℕ} (hk : 1 ≤ k) (a b : ℕ) :
    zCount k hk (braidTrainUp k a b) = 0 := by
  rw [braidTrainUp, trainUp]
  split
  · rw [ascendingWord]
    exact zCount_prod_eq_zero hk _ _ (zCount_braidGenT hk)
  · rw [descendingWord]
    exact zCount_prod_eq_zero hk _ _ (zCount_braidGenTinv hk)

/-- **A train carries no `z`**: `HJO.Braid.trainDown` is a word in the braid letters alone. -/
@[simp]
theorem zCount_braidTrainDown {k : ℕ} (hk : 1 ≤ k) (a b : ℕ) :
    zCount k hk (braidTrainDown k a b) = 0 := by
  rw [braidTrainDown, trainDown]
  split
  · rw [descendingWord]
    exact zCount_prod_eq_zero hk _ _ (zCount_braidGenT hk)
  · rw [ascendingWord]
    exact zCount_prod_eq_zero hk _ _ (zCount_braidGenTinv hk)

/-- **`ζ(ỹ_i) = 0`**: `HJO.Braid.braidYtilde` conjugates `y_k` by trains, and neither the trains nor
`y_k` carries a `z`. This is the asymmetry `HJO.Braid.letterCount` cannot see — there
`ℓ(ỹ_i) = ℓ(z_i) = 1`. -/
@[simp, hjo "lem_braid_rotation_zcount"]
theorem zCount_braidYtilde {k : ℕ} (hk : 1 ≤ k) (i : ℕ) : zCount k hk (braidYtilde k i) = 0 := by
  rw [braidYtilde, zCount_mul, zCount_mul, zCount_mul, zCount_braidTrainDown,
    zCount_braidTrainUp, zCount_braidTrainUp, zCount_braidGenY hk]

/-! ### The `z`-count of a braid of moves -/

/-- **A move contributes a `z` exactly when the moving entry is below the puncture.** The two
branches of `HJO.Braid.braidStep` are a `z_a` and a `ỹ_a`, and the descending train in front of
either carries no `z`; so the rank does not enter, only the side of `θ` the entry is on. -/
@[simp, hjo "lem_braid_rotation_zcount"]
theorem zCount_braidStep {θ : ℚ} {k : ℕ} (hk : 1 ≤ k) (w : Fin k → ℚ) (i : Fin k) :
    zCount k hk (braidStep θ w i) = if w i < θ then 1 else 0 := by
  rw [braidStep, zCount_mul, zCount_braidTrainDown, zero_add]
  split
  · exact zCount_braidGenZ hk (entryRank_pos w i)
  · exact zCount_braidYtilde hk _

/-- **How many of the first `n` iterates of `nx_θ` at `x` lie below the puncture.** By
`HJO.Braid.zCount_braidStep` this is the number of `z` letters the point `x` contributes over `n`
moves. -/
def belowCount (θ x : ℚ) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if (nextCrossing θ)^[j] x < θ then 1 else 0

@[simp]
theorem belowCount_zero (θ x : ℚ) : belowCount θ x 0 = 0 := by
  rw [belowCount, Finset.range_zero, Finset.sum_empty]

theorem belowCount_succ (θ x : ℚ) (n : ℕ) :
    belowCount θ x (n + 1) =
      belowCount θ x n + if (nextCrossing θ)^[n] x < θ then 1 else 0 := by
  rw [belowCount, belowCount, Finset.sum_range_succ]

/-- **The `z`-count of a braid of moves**, resolved point by point: the `j`-th move of the point `t`
sees `t` at the iterate `nx_θ^j(w_t)`, the other points' moves not touching that entry, so the
number of `z` letters the sequence contributes is `HJO.Braid.belowCount` at each entry, evaluated at
the number of times the sequence moves it. -/
theorem zCount_braidWord {θ : ℚ} {k : ℕ} (hk : 1 ≤ k) (w : Fin k → ℚ) :
    ∀ l : List (Fin k),
      zCount k hk (braidWord θ w l) = ∑ t : Fin k, belowCount θ (w t) (l.count t)
  | [] => by simp
  | (m :: l) => by
    have hcount : ∀ t ∈ Finset.univ.erase m,
        belowCount θ (w t) ((m :: l).count t) = belowCount θ (w t) (l.count t) := by
      intro t ht
      rw [List.count_cons_of_ne ((Finset.mem_erase.1 ht).1.symm)]
    rw [braidWord_cons, zCount_mul, zCount_braidStep, zCount_braidWord hk w l,
      moveTuple_apply_eq_iterate, ← Finset.sum_erase_add _ _ (Finset.mem_univ m),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ m), Finset.sum_congr rfl hcount,
      List.count_cons_self, belowCount_succ]
    omega

/-- **The `z`-count of the special braid**: `ζ(B_{s,v,α}) = ∑_i` (the number of the `i`-th point's
`α_i - 1` moves that are made from below the puncture). -/
@[hjo "lem_braid_rotation_zcount"]
theorem zCount_specialBraid {θ : ℚ} {k : ℕ} (hk : 1 ≤ k) (v : Fin k → ℚ) (α : Fin k → ℕ) :
    zCount k hk (specialBraid θ v α) = ∑ i : Fin k, belowCount θ (v i) (α i - 1) := by
  rw [specialBraid, zCount_braidWord hk]
  exact Finset.sum_congr rfl fun i _ => by rw [count_specialMoveList]

/-! ### The closed form: a `z` letter is an integer crossed -/

/-- **`nx_θ` is `x ↦ {x - θ}`** on the interval where `HJO.Braid.IsSpecialBraidData` reads it.
`HJO.Braid.nextCrossing` is the rotation of `ℝ/ℤ` by `-θ`, written on the
representatives `(0,1)`. -/
theorem nextCrossing_eq_fract_sub {θ x : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hx0 : 0 < x) (hx1 : x < 1)
    (hne : x ≠ θ) : nextCrossing θ x = Int.fract (x - θ) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [nextCrossing_of_lt h,
      show x - θ = x + 1 - θ + ((-1 : ℤ) : ℚ) by push_cast; ring, Int.fract_add_intCast]
    exact (Int.fract_eq_self.2 ⟨by linarith, by linarith⟩).symm
  · rw [nextCrossing_of_gt h]
    exact (Int.fract_eq_self.2 ⟨by linarith, by linarith⟩).symm

/-- Every iterate `nx_θ^j(x)` that `HJO.Braid.IsSpecialBraidData` controls lies in `(0,1)`: the
hypothesis is the `ne_theta` clause, read directly rather than through the data. -/
theorem iterate_nextCrossing_mem_Ioo {θ x : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hx0 : 0 < x)
    (hx1 : x < 1) : ∀ n : ℕ, (∀ j, j < n → (nextCrossing θ)^[j] x ≠ θ) →
      (nextCrossing θ)^[n] x ∈ Set.Ioo (0 : ℚ) 1 := by
  intro n
  induction n with
  | zero => intro _; exact ⟨hx0, hx1⟩
  | succ n ih =>
    intro hne
    have hprev := ih fun j hj => hne j (by omega)
    rw [Function.iterate_succ_apply']
    exact nextCrossing_mem_Ioo hθ0 hθ1 hprev.1 hprev.2 (hne n (by omega))

/-- **The `j`-th iterate of `nx_θ` is `{x - jθ}`.** Iterating the rotation is subtracting `jθ`, and
the fractional part is where the representative in `(0,1)` comes from. -/
theorem iterate_nextCrossing_eq_fract {θ x : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hx0 : 0 < x)
    (hx1 : x < 1) : ∀ n : ℕ, (∀ j, j < n → (nextCrossing θ)^[j] x ≠ θ) →
      (nextCrossing θ)^[n] x = Int.fract (x - (n : ℚ) * θ) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, sub_zero]
    exact (Int.fract_eq_self.2 ⟨hx0.le, hx1⟩).symm
  | succ n ih =>
    intro hne
    have hprev := ih fun j hj => hne j (by omega)
    have hmem := iterate_nextCrossing_mem_Ioo hθ0 hθ1 hx0 hx1 n fun j hj => hne j (by omega)
    rw [Function.iterate_succ_apply',
      nextCrossing_eq_fract_sub hθ0 hθ1 hmem.1 hmem.2 (hne n (by omega)), hprev,
      show Int.fract (x - (n : ℚ) * θ) - θ
          = (x - ((n + 1 : ℕ) : ℚ) * θ) + ((-⌊x - (n : ℚ) * θ⌋ : ℤ) : ℚ) from by
        rw [Int.fract]; push_cast; ring,
      Int.fract_add_intCast]

/-- **One step of the floor count.** Lowering a rational by `θ ∈ (0,1)` drops its floor by one
exactly when its fractional part is below `θ` — which by `HJO.Braid.nextCrossing_eq_fract_sub` is
exactly when `HJO.Braid.braidStep` reads a `z`. -/
theorem floor_sub_floor_sub (θ y : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ⌊y⌋ - ⌊y - θ⌋ = if Int.fract y < θ then 1 else 0 := by
  have h0 := Int.fract_nonneg y
  have h1 := Int.fract_lt_one y
  rw [show y - θ = (Int.fract y - θ) + ((⌊y⌋ : ℤ) : ℚ) from by rw [Int.fract]; ring,
    Int.floor_add_intCast]
  split_ifs with h
  · rw [show ⌊Int.fract y - θ⌋ = -1 from by
      rw [Int.floor_eq_iff]
      push_cast
      exact ⟨by linarith, by linarith⟩]
    omega
  · rw [show ⌊Int.fract y - θ⌋ = 0 from by
      rw [Int.floor_eq_iff]
      push_cast
      exact ⟨by linarith [not_lt.1 h], by linarith⟩]
    omega

/-- **The closed form for the number of `z` letters a point contributes.** Over `n` moves from
`x ∈ (0,1)`, none of them at the puncture, the point crosses `0` exactly `-⌊x - nθ⌋` times: its
unwrapped trajectory falls from `x` to `x - nθ`, and each `z` letter of `HJO.Braid.braidStep` is one
integer passed on the way. -/
@[hjo "lem_braid_rotation_zcount"]
theorem belowCount_eq_neg_floor {θ x : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hx0 : 0 < x) (hx1 : x < 1) :
    ∀ n : ℕ, (∀ j, j < n → (nextCrossing θ)^[j] x ≠ θ) →
      (belowCount θ x n : ℤ) = -⌊x - (n : ℚ) * θ⌋ := by
  intro n
  induction n with
  | zero =>
    intro _
    have hfl : ⌊x - ((0 : ℕ) : ℚ) * θ⌋ = 0 := by
      rw [Nat.cast_zero, zero_mul, sub_zero]
      exact Int.floor_eq_zero_iff.2 (Set.mem_Ico.2 ⟨hx0.le, hx1⟩)
    rw [belowCount_zero, hfl]
    norm_num
  | succ n ih =>
    intro hne
    have hprev := ih fun j hj => hne j (by omega)
    have hiter := iterate_nextCrossing_eq_fract hθ0 hθ1 hx0 hx1 n fun j hj => hne j (by omega)
    have hstep := floor_sub_floor_sub θ (x - (n : ℚ) * θ) hθ0 hθ1
    have hsub : x - ((n + 1 : ℕ) : ℚ) * θ = x - (n : ℚ) * θ - θ := by push_cast; ring
    rw [belowCount_succ, hsub, Nat.cast_add, hprev, hiter]
    split_ifs at hstep ⊢ <;> push_cast <;> omega

/-- **The `z`-count of the special braid in closed form.** Every `z` letter is an integer the
corresponding point's unwrapped trajectory passes, so `ζ(B_{s,v,α}) = -∑_i ⌊v_i - (α_i-1)θ⌋`. -/
@[hjo "lem_braid_rotation_zcount"]
theorem zCount_specialBraid_eq {s θ : ℚ} {k : ℕ} (hk : 1 ≤ k) {v : Fin k → ℚ} {α : Fin k → ℕ}
    (hdata : IsSpecialBraidData s θ k v α) :
    (zCount k hk (specialBraid θ v α) : ℤ) =
      -∑ i : Fin k, ⌊v i - ((α i - 1 : ℕ) : ℚ) * θ⌋ := by
  have hθ := hdata.theta_mem_Ioo
  rw [zCount_specialBraid, Nat.cast_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact belowCount_eq_neg_floor hθ.1 hθ.2 (hdata.mem_Ioo i).1 (hdata.mem_Ioo i).2 (α i - 1)
    fun j hj => hdata.ne_theta i j (by have := hdata.one_le_mult i; omega)

/-! ### The rotation lemma -/

/-- **What a rigid rotation does to the special braid: an exact count of `z` letters.**

Let `(v, α)` and `(v', α)` be special-braid data at the same `θ` with `v'_i = {v_i + c}` for one
common `c` — the situation `HJO.Mellit.sweepTheta_eq_div` puts the type-`C`, type-`D` and type-`E`
clauses of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` in. Then

`ζ(B_{s,v',α}) - ζ(B_{s,v,α}) = ∑_i (⌊v_i + c⌋ - ⌊f_i + c⌋)`,

where `f_i = nx_θ^{α_i-1}(v_i)` is the final position of `HJO.Braid.positionPair`. In words: the
rotation **gains** a `z` letter for each *initial* position it carries past `0`, and **loses** one
for each *final* position it carries past `0`. Nothing else about the configuration enters — not the
ranks, not the multiplicities, not `θ` itself.

This is the obligation common to the three clauses, and it is not an invariance: see
`HJO.Braid.exists_rotation_specialBraid_ne`. -/
@[hjo "lem_braid_rotation_zcount"]
theorem zCount_specialBraid_rotate_sub {s θ : ℚ} {k : ℕ} (hk : 1 ≤ k) {v v' : Fin k → ℚ}
    {α : Fin k → ℕ} (c : ℚ) (hdata : IsSpecialBraidData s θ k v α)
    (hdata' : IsSpecialBraidData s θ k v' α) (hrot : ∀ i, v' i = Int.fract (v i + c)) :
    (zCount k hk (specialBraid θ v' α) : ℤ) - (zCount k hk (specialBraid θ v α) : ℤ)
      = ∑ i : Fin k, (⌊v i + c⌋ - ⌊(nextCrossing θ)^[α i - 1] (v i) + c⌋) := by
  have hθ := hdata.theta_mem_Ioo
  rw [zCount_specialBraid_eq hk hdata', zCount_specialBraid_eq hk hdata, neg_sub_neg,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  set m : ℕ := α i - 1 with hm
  have hfin := iterate_nextCrossing_eq_fract hθ.1 hθ.2 (hdata.mem_Ioo i).1 (hdata.mem_Ioo i).2 m
    fun j hj => hdata.ne_theta i j (by have := hdata.one_le_mult i; omega)
  have hkey : ⌊v' i - (m : ℚ) * θ⌋ = ⌊v i + c - (m : ℚ) * θ⌋ - ⌊v i + c⌋ := by
    rw [show v' i - (m : ℚ) * θ
        = (v i + c - (m : ℚ) * θ) + ((-⌊v i + c⌋ : ℤ) : ℚ) from by
      rw [hrot i, Int.fract]; push_cast; ring, Int.floor_add_intCast]
    omega
  have hfloor : ⌊(nextCrossing θ)^[m] (v i) + c⌋
      = ⌊v i + c - (m : ℚ) * θ⌋ - ⌊v i - (m : ℚ) * θ⌋ := by
    rw [show (nextCrossing θ)^[m] (v i) + c
        = (v i + c - (m : ℚ) * θ) + ((-⌊v i - (m : ℚ) * θ⌋ : ℤ) : ℚ) from by
      rw [hfin, Int.fract]; push_cast; ring, Int.floor_add_intCast]
    omega
  rw [hkey, hfloor]
  omega

/-- **The `z`-count difference read as a count of positions**, for a rotation by `c ∈ [0,1)`: the
rotation gains a `z` for each initial position in `[1-c, 1)` and loses one for each final position
there. A position of `(0,1)` is carried past `0` by the rotation exactly when it is at least
`1 - c`, and then by exactly one whole turn.

This is the form in which a clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` has to
predict the change: at an event of type `E`, where `HJO.Mellit.Isolates.braidData_of_eventType_E`
makes the rank and every multiplicity equal, this integer is the whole braid-side difference between
`R_-` and `R_+^{\widehat Q}` that the `u` of rule `E` must account for. -/
@[hjo "lem_braid_rotation_zcount"]
theorem zCount_specialBraid_rotate_sub_card {s θ : ℚ} {k : ℕ} (hk : 1 ≤ k) {v v' : Fin k → ℚ}
    {α : Fin k → ℕ} {c : ℚ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hdata : IsSpecialBraidData s θ k v α)
    (hdata' : IsSpecialBraidData s θ k v' α) (hrot : ∀ i, v' i = Int.fract (v i + c)) :
    (zCount k hk (specialBraid θ v' α) : ℤ) - (zCount k hk (specialBraid θ v α) : ℤ)
      = (#{i : Fin k | 1 - c ≤ v i} : ℤ)
        - (#{i : Fin k | 1 - c ≤ (nextCrossing θ)^[α i - 1] (v i)} : ℤ) := by
  have hfl : ∀ x : ℚ, 0 < x → x < 1 → ⌊x + c⌋ = if 1 - c ≤ x then 1 else 0 := by
    intro x hx0 hx1
    split_ifs with h
    · exact Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
    · exact Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith [not_le.1 h]⟩
  rw [zCount_specialBraid_rotate_sub hk c hdata hdata' hrot, Finset.card_filter,
    Finset.card_filter, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfin := hdata.iterate_mem_Ioo i (α i - 1) (by have := hdata.one_le_mult i; omega)
  rw [hfl (v i) (hdata.mem_Ioo i).1 (hdata.mem_Ioo i).2, hfl _ hfin.1 hfin.2]
  split_ifs <;> norm_num

/-! ### A rigid rotation is visible -/

/-- Two special braids with different `z`-counts are different elements of `𝔹_k^+(𝕋_0)`. -/
theorem specialBraid_ne_specialBraid_of_zCount_ne {θ : ℚ} {k : ℕ} (hk : 1 ≤ k)
    {v v' : Fin k → ℚ} {α α' : Fin k → ℕ}
    (h : zCount k hk (specialBraid θ v α) ≠ zCount k hk (specialBraid θ v' α')) :
    specialBraid θ v α ≠ specialBraid θ v' α' := fun heq => h (by rw [heq])

/-- The witness's data at the upper level: one point at `9/10`, one move, puncture `θ = 1/3`,
slope `s = 2`. The two iterates are `9/10` and `9/10 - 1/3`, both away from the puncture. -/
theorem isSpecialBraidData_witness :
    IsSpecialBraidData 2 (1 / 3) 1 (fun _ => 9 / 10) (fun _ => 2) where
  slope_pos := by norm_num
  theta_spec := by norm_num
  mem_Ioo i := by norm_num
  one_le_mult i := by norm_num
  ne_theta i j hj := by
    have hj' : j < 2 := hj
    interval_cases j <;> norm_num [nextCrossing]
  injective i i' j j' hj hj' h := by
    refine ⟨Subsingleton.elim _ _, ?_⟩
    have hj1 : j < 2 := hj
    have hj2 : j' < 2 := hj'
    interval_cases j <;> interval_cases j' <;>
      first
        | rfl
        | (exfalso; norm_num [nextCrossing] at h)

/-- The same data rotated by `c = 1/5`: the point stands at `{9/10 + 1/5} = 1/10`, which is now
**below** the puncture, so its single move contributes a `z` where before it contributed a `ỹ`. -/
theorem isSpecialBraidData_witness_rotate :
    IsSpecialBraidData 2 (1 / 3) 1 (fun _ => 1 / 10) (fun _ => 2) where
  slope_pos := by norm_num
  theta_spec := by norm_num
  mem_Ioo i := by norm_num
  one_le_mult i := by norm_num
  ne_theta i j hj := by
    have hj' : j < 2 := hj
    interval_cases j <;> norm_num [nextCrossing]
  injective i i' j j' hj hj' h := by
    refine ⟨Subsingleton.elim _ _, ?_⟩
    have hj1 : j < 2 := hj
    have hj2 : j' < 2 := hj'
    interval_cases j <;> interval_cases j' <;>
      first
        | rfl
        | (exfalso; norm_num [nextCrossing] at h)

theorem zCount_witness :
    zCount 1 le_rfl (specialBraid (1 / 3 : ℚ) (fun _ => 9 / 10) (fun _ => 2)) = 0 := by
  rw [zCount_specialBraid, Fin.sum_univ_one,
    show ((fun _ => 2 : Fin 1 → ℕ) 0) - 1 = 1 from rfl, belowCount_succ, belowCount_zero,
    Function.iterate_zero_apply]
  norm_num

theorem zCount_witness_rotate :
    zCount 1 le_rfl (specialBraid (1 / 3 : ℚ) (fun _ => 1 / 10) (fun _ => 2)) = 1 := by
  rw [zCount_specialBraid, Fin.sum_univ_one,
    show ((fun _ => 2 : Fin 1 → ℕ) 0) - 1 = 1 from rfl, belowCount_succ, belowCount_zero,
    Function.iterate_zero_apply]
  norm_num

/-- **A rigid rotation of the position tuple changes the special braid.** At `θ = 1/3`, one point,
one move: from `9/10` the point is above the puncture and the move contributes a `ỹ`, so `ζ = 0`;
rotated by `1/5` it stands at `1/10`, below the puncture, and the move contributes a `z`, so
`ζ = 1`. The two elements of `𝔹_1^+(𝕋_0)` are therefore distinct, and both tuples are genuine
special-braid data — the rotation is not an artefact of a degenerate configuration.

So **there is no rotation-invariance lemma** for
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` to use, and the conditional recorded under
`HJO.Mellit.sweepTheta_eq_div` — that an invisible rotation would force `D_{η_-,c} = D_{η_+,c}` at
every type-`E` colouring — has no hypothesis left to run on. What replaces invariance is
`HJO.Braid.zCount_specialBraid_rotate_sub_card`.

**The scope of this witness.** It refutes the *general* invariance statement, the one a clause would
have to invoke. It does not decide whether a *particular* level drop moves the braid: `c = 1/5` here
is not of the form `m/D`, and `k = 1`. That question is the criterion stated after
`HJO.Braid.zCount_mul`, and it is not proved. -/
@[hjo "lem_braid_rotation_zcount"]
theorem exists_rotation_specialBraid_ne :
    ∃ (s θ : ℚ) (k : ℕ) (hk : 1 ≤ k) (v v' : Fin k → ℚ) (α : Fin k → ℕ) (c : ℚ),
      0 ≤ c ∧ c < 1 ∧ IsSpecialBraidData s θ k v α ∧ IsSpecialBraidData s θ k v' α ∧
        (∀ i, v' i = Int.fract (v i + c)) ∧
        zCount k hk (specialBraid θ v α) ≠ zCount k hk (specialBraid θ v' α) ∧
        specialBraid θ v α ≠ specialBraid θ v' α := by
  refine ⟨2, 1 / 3, 1, le_rfl, fun _ => 9 / 10, fun _ => 1 / 10, fun _ => 2, 1 / 5, by norm_num,
    by norm_num, isSpecialBraidData_witness, isSpecialBraidData_witness_rotate, fun i => ?_, ?_,
    ?_⟩
  · rw [show (9 : ℚ) / 10 + 1 / 5 = 1 / 10 + ((1 : ℤ) : ℚ) from by push_cast; ring,
      Int.fract_add_intCast]
    exact (Int.fract_eq_self.2 ⟨by norm_num, by norm_num⟩).symm
  · rw [zCount_witness, zCount_witness_rotate]
    omega
  · exact specialBraid_ne_specialBraid_of_zCount_ne le_rfl (by
      rw [zCount_witness, zCount_witness_rotate]; omega)

end HJO.Braid

/-! ### What the `z`-count of a colouring's special braid measures

For the data of `HJO.Mellit.braidDataOfColouring` the closed form becomes a lattice count: the
`i`-th component contributes one `z` for each integer its crossing abscissa passes between the
bottom crossing and the top one. That is what makes the identity
`HJO.Braid.zCount_specialBraid_rotate_sub` readable on the sweep: a level drop moves every crossing
abscissa right by `(η_+ - η_-)/D`, and a `z` is gained or lost exactly when an endpoint's abscissa
passes a lattice point of its antidiagonal — which, the drop isolating one lattice point, is a
condition on that point alone. -/

namespace HJO.Mellit

open Braid Finset ParkingFunctions Paths

variable {a b N : ℕ}

/-- **Lowering the index by `m` lowers the crossing abscissa by `mθ`**, the integer form of
`HJO.Mellit.crossingAbscissa_sub_sweepTheta`. -/
theorem crossingAbscissa_sub_mul_sweepTheta (hs : 1 + sweepSlope a b N ≠ 0) (η : ℚ) (n m : ℤ) :
    crossingAbscissa a b N η n - (m : ℚ) * sweepTheta a b N
      = crossingAbscissa a b N η (n - m) := by
  rw [crossingAbscissa, crossingAbscissa, sweepTheta]
  field_simp
  push_cast
  ring

/-- **The contribution of one component to the `z`-count is the number of integers its abscissa
passes.** The component's positions are the fractional parts of the crossing abscissae from the
bottom index to the top one, so `HJO.Braid.belowCount_eq_neg_floor` reads off the difference of the
two floors. -/
theorem neg_floor_fract_crossingAbscissa_sub (hs : 1 + sweepSlope a b N ≠ 0) (η : ℚ) {bot top : ℤ}
    (hle : bot ≤ top) :
    -⌊Int.fract (crossingAbscissa a b N η top)
        - (((top + 1 - bot).toNat - 1 : ℕ) : ℚ) * sweepTheta a b N⌋
      = ⌊crossingAbscissa a b N η top⌋ - ⌊crossingAbscissa a b N η bot⌋ := by
  have hm : ((top + 1 - bot).toNat - 1 : ℕ) = (top - bot).toNat := by omega
  have hcast : (((top - bot).toNat : ℕ) : ℚ) = ((top - bot : ℤ) : ℚ) := by
    rw [show (((top - bot).toNat : ℕ) : ℚ) = ((((top - bot).toNat : ℕ) : ℤ) : ℚ) from by
      push_cast; ring, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ top - bot)]
  have hstep := crossingAbscissa_sub_mul_sweepTheta hs η top (top - bot)
  rw [show top - (top - bot) = bot from by ring] at hstep
  push_cast at hstep
  rw [hm, hcast,
    show Int.fract (crossingAbscissa a b N η top) - ((top - bot : ℤ) : ℚ) * sweepTheta a b N
        = crossingAbscissa a b N η bot
          + ((-⌊crossingAbscissa a b N η top⌋ : ℤ) : ℚ) from by
      rw [Int.fract]
      push_cast
      linarith,
    Int.floor_add_intCast]
  omega

/-- **The `z`-count of a colouring's special braid counts lattice lines.** For the data of
`HJO.Mellit.braidDataOfColouring` at an admissible level `η > aN` on an above-diagonal path,

`ζ(B_{s,v,α}) = ∑_i (⌊x_i^{top}⌋ - ⌊x_i^{bot}⌋)`,

the `i`-th summand being the number of integers the `i`-th component's crossing abscissa passes
between its bottom crossing and its top one. Together with
`HJO.Braid.zCount_specialBraid_rotate_sub` this is what makes the type-`C`, type-`D` and type-`E`
clauses of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` into a condition on the one lattice
point the level drop isolates: a `z` letter is created or destroyed exactly when an endpoint's
abscissa passes a lattice point of its antidiagonal.

The total letter count `ℓ(B_{s,v,α}) = ∑_i (α_i - 1)` of
`HJO.Mellit.card_componentCrossingIndices_eq` says nothing about this split; `HJO.Braid.zCount` is a
second, independent functional. -/
@[hjo "lem_braid_rotation_zcount"]
theorem zCount_specialBraid_braidDataOfColouring (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hk : 1 ≤ #(colouringNorth y η)) :
    (zCount #(colouringNorth y η) hk (specialBraid (sweepTheta a b N)
        (braidDataOfColouring a b N y η #(colouringNorth y η)).1
        (braidDataOfColouring a b N y η #(colouringNorth y η)).2) : ℤ)
      = ∑ i : Fin #(colouringNorth y η),
          (⌊crossingAbscissa a b N η (componentTopIndex a b N y η i)⌋
            - ⌊crossingAbscissa a b N η (componentBotIndex a b N y η i)⌋) := by
  have hs := one_add_sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  rw [zCount_specialBraid_eq hk (isSpecialBraidData_braidDataOfColouring ha hb hN hη hηa hy),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [braidDataOfColouring_fst, braidDataOfColouring_snd, componentCrossingIndices_eq_Icc,
    Int.card_Icc]
  exact neg_floor_fract_crossingAbscissa_sub hs.ne' η
    (componentBotIndex_le_componentTopIndex ha hb hN hη hηa hy i.isLt)

end HJO.Mellit

end
