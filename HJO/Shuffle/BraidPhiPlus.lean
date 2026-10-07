/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidMonoid
public import HJO.Shuffle.BraidTrainRelations
public meta import HJO.Attr

/-! # The index-raising homomorphism `φ*₊`

`HJO.Braid.phiPlusStar` is the monoid homomorphism
`φ*₊ : 𝔹_k^+(𝕋_0) → 𝔹_{k+1}^+(𝕋_0)` induced by `T_i ↦ T_{i+1}`, `T̄_i ↦ T̄_{i+1}`, `y_1 ↦ y_2`,
`z_1 ↦ z_2` on the generators. As with `HJO.Sweep.braidRep`, "induced by" is a claim: the assignment
has to respect the ten relation families of `HJO.Braid.BraidMonoid`, and unlike `HJO.Sweep.braidRep`
that claim is discharged here, so this file gives a bare `def` (taking the `k ≥ 1` as its
hypothesis).

## Main definitions

* `HJO.Braid.phiPlusLetter`, `HJO.Braid.phiPlusFree` — the assignment on letters and the
  homomorphism it induces on the free monoid.
* `HJO.Braid.phiPlusStar`.

## Main results

* `HJO.Braid.braidGen_zy_two` — **the mixed relation at index 2**,
  `z_2T_2y_2T̄_2 = T̄_2y_2T̄_2z_2`, in `𝔹_K^+(𝕋_0)` for `K ≥ 3`. This is the one family whose image
  under the assignment is not another instance of itself, and it is what makes `φ*₊` exist at all;
  see the implementation note.
* `HJO.Braid.phiPlusFree_yWord`, `HJO.Braid.phiPlusFree_zWord` — the assignment carries the word
  `𝗒_i` to `𝗒_{i+1}` and `𝗓_i` to `𝗓_{i+1}`, so `φ*₊` raises the index of *every* `y_i` and `z_i`
  and not only of `y_1` and `z_1`. This is the step `HJO.Braid.specialBraid_mul_trainDown_one`
  needs; it can be derived from `HJO.Braid.braidGenY_eq_trainUp_mul_mul_trainDown` and
  `HJO.Braid.braidGenZ_eq_trainDown_mul_mul_trainUp`, but on the words it is a two-line induction
  and needs neither.
* `HJO.Braid.phiPlusStar_T`, `HJO.Braid.phiPlusStar_Tbar`, `HJO.Braid.phiPlusStar_y`,
  `HJO.Braid.phiPlusStar_z` — the values on the generators.
* `HJO.Braid.phiPlusStar_unique` — uniqueness, by `HJO.Braid.monoidHom_ext`.

## Implementation notes

### The mixed relation is imposed at index 1 only, and its image sits at index 2

Nine of the ten families of `HJO.Braid.BraidRel` are stable under raising every index by one: the
image of an instance is another instance of the same family at the shifted index, whose side
conditions hold because the rank has grown by one too. The tenth, `HJO.Braid.BraidRel.zy`, is
imposed at index `1` alone, and its image is the same equation at index `2`, which the presentation
does **not** list. So `φ*₊` exists only if that equation is a *consequence* of the presentation, and
`HJO.Braid.braidGen_zy_two` is the proof that it is. The derivation is short but not formal: writing
`z_2 = T_1z_1T_1` and `y_2 = T̄_1y_1T̄_1`, both sides reduce to `y_3z_2` — the left one using the
braid relation twice, the commutations of `y_1` and `z_1` with `T_2`, the index-1 mixed relation and
finally `y_3T_1 = T_1y_3`, which is the fourth family at `i = 3`, `j = 1` and needs `K ≥ 3`. That
`K ≥ 3` is available exactly because the presentation imposes `zy` only for `k ≥ 2`.

Had the relation been listed at every index the map would be immediate; had `y_3` not commuted with
`T_1` it would not exist.

### The letter `T_0` needs a guard, and `y_1` needs the hypothesis `k ≥ 1`

`HJO.Braid.Letter` carries `T_i` and `T̄_i` for every natural `i`, and
`HJO.Braid.BraidRel.out_of_rank` kills the ones outside `[1, k - 1]`; the assignment must therefore
kill them too. For `i ≥ 1` outside the rank this is automatic — `T_{i+1}` is then outside the rank
of `k + 1` and `HJO.Braid.braidGenT_of_lt` sends it to `1` — but `T_0` is out of rank at every `k`
while `T_1` is a genuine generator of `𝔹_{k+1}^+(𝕋_0)` as soon as `k ≥ 1`. So the two braid clauses
of `HJO.Braid.phiPlusLetter` carry the guard `i = 0`, and without it the assignment would not
descend.

The letters `y_1` and `z_1` are out of rank only at `k = 0`, where `𝔹_0^+(𝕋_0)` is trivial and the
map is not needed: `HJO.Braid.phiPlusStar` takes `k ≥ 1` as a hypothesis, and that
hypothesis is what discharges the out-of-rank family at those two letters. At `k = 0` the assignment
genuinely fails to respect the presentation — `y_1` is killed by `out_of_rank` there, while its
image `y_2 = T̄_1y_1T̄_1 = y_1` in `𝔹_1^+(𝕋_0)` is not the identity — so the hypothesis is not
bookkeeping.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, Section 5, the braid monoid. This file
defines `HJO.Braid.phiPlusStar`, using `HJO.Braid.BraidMonoid` and `HJO.Braid.braidGenT`.
-/

@[expose] public section

namespace HJO.Braid

/-! ### The mixed relation at index two -/

/-- **The mixed relation at index `2`**: `z_2T_2y_2T̄_2 = T̄_2y_2T̄_2z_2` in `𝔹_K^+(𝕋_0)` for
`K ≥ 3`.

`HJO.Braid.BraidMonoid` imposes the mixed relation at index `1` only. This is the same equation one
index up, and it is a consequence rather than a relation: with `z_2 = T_1z_1T_1` and
`y_2 = T̄_1y_1T̄_1` both sides equal `y_3z_2`. The left side gets there through
`T_1T_2T̄_1 = T̄_2T_1T_2` and `T_2T̄_1T̄_2 = T̄_1T̄_2T_1` (the braid relation and its inverse), the
commutations `z_1T_2 = T_2z_1` and `y_1T_2 = T_2y_1`, the index-`1` mixed relation, and
`y_3T_1 = T_1y_3` — the last being the fourth family at `i = 3`, `j = 1`, which is what spends the
hypothesis `K ≥ 3`.

This is what makes `HJO.Braid.phiPlusStar` a definition: the image of the one relation of
`HJO.Braid.BraidMonoid` that is not stable under raising the index is exactly this equation. -/
theorem braidGen_zy_two {K : ℕ} (hK : 3 ≤ K) :
    braidGenZ K 2 * braidGenT K 2 * braidGenY K 2 * braidGenTinv K 2
      = braidGenTinv K 2 * braidGenY K 2 * braidGenTinv K 2 * braidGenZ K 2 := by
  have hy2 : braidGenY K 2 = braidGenTinv K 1 * braidGenY K 1 * braidGenTinv K 1 :=
    braidGenY_succ K 0
  have hz2 : braidGenZ K 2 = braidGenT K 1 * braidGenZ K 1 * braidGenT K 1 :=
    braidGenZ_succ K 0
  have hy3 : braidGenY K 3 = braidGenTinv K 2 * braidGenY K 2 * braidGenTinv K 2 :=
    braidGenY_succ K 1
  have h11 : braidGenT K 1 * braidGenTinv K 1 = 1 := braidGenT_mul_inv le_rfl (by omega)
  have h11' : braidGenTinv K 1 * braidGenT K 1 = 1 := braidGenT_inv_mul le_rfl (by omega)
  have h22 : braidGenT K 2 * braidGenTinv K 2 = 1 := braidGenT_mul_inv (by omega) (by omega)
  have h22' : braidGenTinv K 2 * braidGenT K 2 = 1 := braidGenT_inv_mul (by omega) (by omega)
  have hb : braidGenT K 1 * braidGenT K 2 * braidGenT K 1
      = braidGenT K 2 * braidGenT K 1 * braidGenT K 2 := braidGenT_braid le_rfl (by omega)
  have hb' : braidGenTinv K 1 * braidGenTinv K 2 * braidGenTinv K 1
      = braidGenTinv K 2 * braidGenTinv K 1 * braidGenTinv K 2 :=
    (isBraidSystem_braidGenT K).inverses.braid 1 le_rfl (by omega)
  -- The two consequences of the braid relation that move a letter across an inverted pair.
  have e1base : braidGenT K 1 * braidGenT K 2 * braidGenTinv K 1
      = braidGenTinv K 2 * braidGenT K 1 * braidGenT K 2 :=
    calc braidGenT K 1 * braidGenT K 2 * braidGenTinv K 1
        = braidGenTinv K 2 * braidGenT K 2 *
            (braidGenT K 1 * braidGenT K 2 * braidGenTinv K 1) := by rw [h22', one_mul]
      _ = braidGenTinv K 2 * (braidGenT K 2 * braidGenT K 1 * braidGenT K 2)
            * braidGenTinv K 1 := by simp only [mul_assoc]
      _ = braidGenTinv K 2 * (braidGenT K 1 * braidGenT K 2 * braidGenT K 1)
            * braidGenTinv K 1 := by rw [hb]
      _ = braidGenTinv K 2 * braidGenT K 1 * braidGenT K 2 *
            (braidGenT K 1 * braidGenTinv K 1) := by simp only [mul_assoc]
      _ = braidGenTinv K 2 * braidGenT K 1 * braidGenT K 2 := by rw [h11, mul_one]
  have e4base : braidGenT K 2 * braidGenTinv K 1 * braidGenTinv K 2
      = braidGenTinv K 1 * braidGenTinv K 2 * braidGenT K 1 :=
    calc braidGenT K 2 * braidGenTinv K 1 * braidGenTinv K 2
        = braidGenT K 2 * (braidGenTinv K 1 * braidGenTinv K 2 * braidGenTinv K 1)
            * braidGenT K 1 := by
          simp only [mul_assoc]
          rw [h11', mul_one]
      _ = braidGenT K 2 * (braidGenTinv K 2 * braidGenTinv K 1 * braidGenTinv K 2)
            * braidGenT K 1 := by rw [hb']
      _ = braidGenT K 2 * braidGenTinv K 2 *
            (braidGenTinv K 1 * braidGenTinv K 2 * braidGenT K 1) := by simp only [mul_assoc]
      _ = braidGenTinv K 1 * braidGenTinv K 2 * braidGenT K 1 := by rw [h22, one_mul]
  -- The commutations, and the index-one mixed relation.
  have hzt2 : braidGenZ K 1 * braidGenT K 2 = braidGenT K 2 * braidGenZ K 1 :=
    braidGenZ_comm_T (i := 1) (j := 2) le_rfl (by omega) (by omega) (by omega) (by omega) (by omega)
  have hzt2' : braidGenZ K 1 * braidGenTinv K 2 = braidGenTinv K 2 * braidGenZ K 1 :=
    comm_inv_right h22 h22' hzt2
  have hyt2 : braidGenY K 1 * braidGenT K 2 = braidGenT K 2 * braidGenY K 1 :=
    braidGenY_comm_T (i := 1) (j := 2) le_rfl (by omega) (by omega) (by omega) (by omega) (by omega)
  have hy3t1 : braidGenT K 1 * braidGenY K 3 = braidGenY K 3 * braidGenT K 1 :=
    (braidGenY_comm_T (i := 3) (j := 1) (by omega) hK le_rfl (by omega) (by omega)
      (by omega)).symm
  have hzy : braidGenZ K 1 * braidGenT K 1 * braidGenY K 1 * braidGenTinv K 1
      = braidGenTinv K 1 * braidGenY K 1 * braidGenTinv K 1 * braidGenZ K 1 :=
    braidGen_zy (by omega)
  rw [hy3, hy2] at hy3t1
  -- The six rewriting steps, each the corresponding identity with a trailing factor.
  have e1 : ∀ X, braidGenT K 1 * (braidGenT K 2 * (braidGenTinv K 1 * X))
      = braidGenTinv K 2 * (braidGenT K 1 * (braidGenT K 2 * X)) := fun X => by
    simp only [← mul_assoc]; rw [e1base]
  have e2 : ∀ X, braidGenZ K 1 * (braidGenTinv K 2 * X)
      = braidGenTinv K 2 * (braidGenZ K 1 * X) := fun X => by
    simp only [← mul_assoc]; rw [hzt2']
  have e3 : ∀ X, braidGenT K 2 * (braidGenY K 1 * X)
      = braidGenY K 1 * (braidGenT K 2 * X) := fun X => by
    simp only [← mul_assoc]; rw [hyt2]
  have e4 : braidGenT K 2 * (braidGenTinv K 1 * braidGenTinv K 2)
      = braidGenTinv K 1 * (braidGenTinv K 2 * braidGenT K 1) := by
    simp only [← mul_assoc]; rw [e4base]
  have e5 : ∀ X, braidGenZ K 1 * (braidGenT K 1 * (braidGenY K 1 * (braidGenTinv K 1 * X)))
      = braidGenTinv K 1 * (braidGenY K 1 * (braidGenTinv K 1 * (braidGenZ K 1 * X))) :=
    fun X => by simp only [← mul_assoc]; rw [hzy]
  have e6 : ∀ X, braidGenT K 1 * (braidGenTinv K 2 * (braidGenTinv K 1 * (braidGenY K 1 *
        (braidGenTinv K 1 * (braidGenTinv K 2 * X)))))
      = braidGenTinv K 2 * (braidGenTinv K 1 * (braidGenY K 1 * (braidGenTinv K 1 *
        (braidGenTinv K 2 * (braidGenT K 1 * X))))) := fun X => by
    simp only [← mul_assoc] at hy3t1 ⊢
    rw [hy3t1]
  rw [hy2, hz2]
  simp only [mul_assoc]
  rw [e1, e2, e3, e4, e5, e2, e6]

/-! ### The assignment on letters -/

/-- **The assignment of `HJO.Braid.phiPlusStar` on the letters**: `T_i ↦ T_{i+1}`,
`T̄_i ↦ T̄_{i+1}`, `y_1 ↦ y_2`, `z_1 ↦ z_2`.

The guard `i = 0` on the two braid clauses is what matches `HJO.Braid.BraidRel.out_of_rank` at the
one letter where raising the index would turn something the monoid kills into a generator; see the
module docstring. -/
def phiPlusLetter (k : ℕ) : Letter → BraidMonoid (k + 1)
  | Letter.T i => if i = 0 then 1 else braidGenT (k + 1) (i + 1)
  | Letter.Tbar i => if i = 0 then 1 else braidGenTinv (k + 1) (i + 1)
  | Letter.y1 => braidGenY (k + 1) 2
  | Letter.z1 => braidGenZ (k + 1) 2

theorem phiPlusLetter_T {k i : ℕ} (hi : 1 ≤ i) :
    phiPlusLetter k (Letter.T i) = braidGenT (k + 1) (i + 1) := by
  have h0 : i ≠ 0 := by omega
  simp [phiPlusLetter, h0]

theorem phiPlusLetter_Tbar {k i : ℕ} (hi : 1 ≤ i) :
    phiPlusLetter k (Letter.Tbar i) = braidGenTinv (k + 1) (i + 1) := by
  have h0 : i ≠ 0 := by omega
  simp [phiPlusLetter, h0]

/-- The guarded letters: `T_0` and `T̄_0` are out of rank at every `k` and go to the identity. -/
theorem phiPlusLetter_T_zero (k : ℕ) : phiPlusLetter k (Letter.T 0) = 1 := by
  simp [phiPlusLetter]

theorem phiPlusLetter_Tbar_zero (k : ℕ) : phiPlusLetter k (Letter.Tbar 0) = 1 := by
  simp [phiPlusLetter]

/-- **The assignment on the free monoid**, which needs no relation. -/
def phiPlusFree (k : ℕ) : FreeMonoid Letter →* BraidMonoid (k + 1) :=
  FreeMonoid.lift (phiPlusLetter k)

@[simp]
theorem phiPlusFree_of (k : ℕ) (c : Letter) :
    phiPlusFree k (FreeMonoid.of c) = phiPlusLetter k c := rfl

/-! ### The images of the `y`- and `z`-words -/

/-- **The assignment raises the index of every `y`-word**: `𝗒_i ↦ 𝗒_{i+1}`, for `1 ≤ i`.

The recursion `𝗒_{i+1} = T̄_i𝗒_iT̄_i` of `HJO.Braid.yWord` becomes
`𝗒_{i+2} = T̄_{i+1}𝗒_{i+1}T̄_{i+1}` under the assignment, which is the same
recursion one index up; so the claim is an induction with `y_1 ↦ y_2` as its
base. This is the fact `HJO.Braid.specialBraid_mul_trainDown_one` needs — that `φ*₊` raises the
index of `y_i` and not merely of `y_1`. -/
theorem phiPlusFree_yWord (k : ℕ) :
    ∀ i, 1 ≤ i → phiPlusFree k (yWord i) = braidGenY (k + 1) (i + 1)
  | 1, _ => rfl
  | (i + 2), _ => by
    rw [yWord_succ, map_mul, map_mul, phiPlusFree_of,
      phiPlusLetter_Tbar (show 1 ≤ i + 1 by omega),
      phiPlusFree_yWord k (i + 1) (by omega), braidGenY_succ (k + 1) (i + 1)]

/-- **The assignment raises the index of every `z`-word**: `𝗓_i ↦ 𝗓_{i+1}`, for `1 ≤ i`; the mirror
of `HJO.Braid.phiPlusFree_yWord` under `T̄_i ↦ T_i`, `y_1 ↦ z_1`. -/
theorem phiPlusFree_zWord (k : ℕ) :
    ∀ i, 1 ≤ i → phiPlusFree k (zWord i) = braidGenZ (k + 1) (i + 1)
  | 1, _ => rfl
  | (i + 2), _ => by
    rw [zWord_succ, map_mul, map_mul, phiPlusFree_of,
      phiPlusLetter_T (show 1 ≤ i + 1 by omega),
      phiPlusFree_zWord k (i + 1) (by omega), braidGenZ_succ (k + 1) (i + 1)]

/-! ### Well-definedness -/

/-- **The assignment respects the presentation of `HJO.Braid.BraidMonoid`.** Nine of the ten
families go to an instance of themselves at the raised index; the tenth, the mixed relation, goes to
`HJO.Braid.braidGen_zy_two`. The hypothesis `1 ≤ k` is spent only on the out-of-rank family at the
letters `y_1` and `z_1`, which are out of rank exactly at `k = 0`. -/
theorem phiPlusFree_respects {k : ℕ} (hk : 1 ≤ k) {x y : FreeMonoid Letter}
    (hrel : BraidRel k x y) : phiPlusFree k x = phiPlusFree k y := by
  induction hrel with
  | mul_inv i hi hik =>
    rw [map_mul, map_one, phiPlusFree_of, phiPlusFree_of, phiPlusLetter_T hi,
      phiPlusLetter_Tbar hi]
    exact braidGenT_mul_inv (by omega) (by omega)
  | inv_mul i hi hik =>
    rw [map_mul, map_one, phiPlusFree_of, phiPlusFree_of, phiPlusLetter_T hi,
      phiPlusLetter_Tbar hi]
    exact braidGenT_inv_mul (by omega) (by omega)
  | braid i hi hik =>
    simp only [map_mul, phiPlusFree_of, phiPlusLetter_T hi,
      phiPlusLetter_T (show 1 ≤ i + 1 by omega)]
    exact braidGenT_braid (by omega) (by omega)
  | far_comm i j hi hij hjk =>
    simp only [map_mul, phiPlusFree_of, phiPlusLetter_T hi,
      phiPlusLetter_T (show 1 ≤ j by omega)]
    exact braidGenT_far_comm (by omega) (by omega) (by omega)
  | yWord_comm_T i j hi hik hj hjk hne hne' =>
    rw [map_mul, map_mul, phiPlusFree_of, phiPlusLetter_T hj, phiPlusFree_yWord k i hi]
    exact braidGenY_comm_T (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  | zWord_comm_T i j hi hik hj hjk hne hne' =>
    rw [map_mul, map_mul, phiPlusFree_of, phiPlusLetter_T hj, phiPlusFree_zWord k i hi]
    exact braidGenZ_comm_T (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  | yWord_comm i j hi hik hj hjk =>
    rw [map_mul, map_mul, phiPlusFree_yWord k i hi, phiPlusFree_yWord k j hj]
    exact braidGenY_comm (by omega) (by omega) (by omega) (by omega)
  | zWord_comm i j hi hik hj hjk =>
    rw [map_mul, map_mul, phiPlusFree_zWord k i hi, phiPlusFree_zWord k j hj]
    exact braidGenZ_comm (by omega) (by omega) (by omega) (by omega)
  | zy hk2 =>
    simp only [map_mul, phiPlusFree_of, phiPlusLetter_T le_rfl, phiPlusLetter_Tbar le_rfl,
      phiPlusFree_yWord k 1 le_rfl, phiPlusFree_zWord k 1 le_rfl]
    exact braidGen_zy_two (by omega)
  | out_of_rank c hc =>
    rw [map_one, phiPlusFree_of]
    match c with
    | Letter.T i =>
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact phiPlusLetter_T_zero k
      · rw [phiPlusLetter_T hi]
        exact braidGenT_of_lt (by simp only [Letter.InRank] at hc; omega)
    | Letter.Tbar i =>
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact phiPlusLetter_Tbar_zero k
      · rw [phiPlusLetter_Tbar hi]
        exact braidGenTinv_of_not_inRank (by simp only [Letter.InRank] at hc ⊢; omega)
    | Letter.y1 => exact absurd hk (by simpa only [Letter.InRank] using hc)
    | Letter.z1 => exact absurd hk (by simpa only [Letter.InRank] using hc)

/-! ### The homomorphism -/

/-- **The index-raising homomorphism `φ*₊`**, `HJO.Braid.phiPlusStar`: the monoid
homomorphism `𝔹_k^+(𝕋_0) → 𝔹_{k+1}^+(𝕋_0)` induced by `T_i ↦ T_{i+1}`, `T̄_i ↦ T̄_{i+1}`,
`y_1 ↦ y_2` and `z_1 ↦ z_2`.

Unlike `HJO.Sweep.braidRep` this is a bare definition and not a definition with a hypothesis: the
assignment does respect the presentation, which is `HJO.Braid.phiPlusFree_respects`, and its one
nontrivial step is `HJO.Braid.braidGen_zy_two`. The `k ≥ 1` is the hypothesis `hk`, and
it is needed: at `k = 0` the assignment does not descend. -/
@[hjo "def_braid_phi_plus_star"]
def phiPlusStar (k : ℕ) (hk : 1 ≤ k) : BraidMonoid k →* BraidMonoid (k + 1) :=
  Con.lift _ (phiPlusFree k)
    (Con.conGen_le.2 fun _x _y hxy => (Con.ker_rel _).2 (phiPlusFree_respects hk hxy))

@[simp]
theorem phiPlusStar_apply (k : ℕ) (hk : 1 ≤ k) (x : FreeMonoid Letter) :
    phiPlusStar k hk (toBraidMonoid k x) = phiPlusFree k x :=
  Con.lift_coe _ _

/-- `φ*₊(T_i) = T_{i+1}`. -/
theorem phiPlusStar_T {k i : ℕ} (hk : 1 ≤ k) (hi : 1 ≤ i) :
    phiPlusStar k hk (braidGenT k i) = braidGenT (k + 1) (i + 1) := by
  rw [braidGenT, phiPlusStar_apply, phiPlusFree_of, phiPlusLetter_T hi]

/-- `φ*₊(T̄_i) = T̄_{i+1}`. -/
theorem phiPlusStar_Tbar {k i : ℕ} (hk : 1 ≤ k) (hi : 1 ≤ i) :
    phiPlusStar k hk (braidGenTinv k i) = braidGenTinv (k + 1) (i + 1) := by
  rw [braidGenTinv, phiPlusStar_apply, phiPlusFree_of, phiPlusLetter_Tbar hi]

/-- **`φ*₊(y_i) = y_{i+1}` for every `i ≥ 1`**, and not only at `i = 1`. -/
theorem phiPlusStar_y {k i : ℕ} (hk : 1 ≤ k) (hi : 1 ≤ i) :
    phiPlusStar k hk (braidGenY k i) = braidGenY (k + 1) (i + 1) := by
  rw [braidGenY, phiPlusStar_apply, phiPlusFree_yWord k i hi]

/-- **`φ*₊(z_i) = z_{i+1}` for every `i ≥ 1`.** -/
theorem phiPlusStar_z {k i : ℕ} (hk : 1 ≤ k) (hi : 1 ≤ i) :
    phiPlusStar k hk (braidGenZ k i) = braidGenZ (k + 1) (i + 1) := by
  rw [braidGenZ, phiPlusStar_apply, phiPlusFree_zWord k i hi]

/-- **`φ*₊` is the only homomorphism with these values on the letters**, which is what "induced by
the assignment on the generators" asserts. -/
theorem phiPlusStar_unique {k : ℕ} (hk : 1 ≤ k) {f : BraidMonoid k →* BraidMonoid (k + 1)}
    (hf : ∀ c : Letter, f (toBraidMonoid k (FreeMonoid.of c)) = phiPlusLetter k c) :
    f = phiPlusStar k hk :=
  monoidHom_ext fun c => by rw [hf c, phiPlusStar_apply, phiPlusFree_of]

end HJO.Braid
