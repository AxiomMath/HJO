/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.VmodGenerators
public import HJO.CMStructure.VmodRaising
public import HJO.Shuffle.BraidTrainRelations
public meta import HJO.Attr

/-! # The relations of the modified raising operator

Four statements of Mellit's §3 about the modified raising operator `d^♭_+` of
`HJO.Sweep.dplus_eq_ascWord`, which is `HJO.Sweep.dplus` — `HJO.Sweep.dplus_eq_ascWord` exhibits
it as the displayed composite that defines `d^♭_+`, so no second operator is introduced here.

* `HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus` compares `d^♭_+` with the Dyck path algebra's
  unmodified `d_+` of `HJO.Sweep.cmDPlus`: `d^♭_+F = -T_{1↑k+1}(y_{k+1}T^*_{k+1↓1}(d_+F))`. The
  starred descending word undoes the ascending word inside `d_+`, leaving `τ_{k+1,k+1}(F)`, which is
  exactly the argument `d^♭_+` multiplies by `y_{k+1}`.
* `HJO.Sweep.dplus_braid_succ` shifts the braid index, `d^♭_+(T_iF) = T_{i+1}(d^♭_+F)`.
* `HJO.Sweep.braid_one_dplus_sq` says `T_1` fixes the double image,
  `T_1(d^♭_+d^♭_+F) = d^♭_+d^♭_+F`.
* `HJO.Sweep.dplus_auxVar_one_mul` moves the first variable across,
  `d^♭_+(y_1F) = T_1(y_1T_1^{-1}(d^♭_+F))`.

## Main results

* `HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus`.
* `HJO.Sweep.dplus_braid_succ`.
* `HJO.Sweep.braid_one_dplus_sq`.
* `HJO.Sweep.dplus_auxVar_one_mul`.

## Implementation notes

**Mellit's `T^*_{k+1↓1}` is `HJO.Sweep.trainUpEnd q (k+1) 1`.** The starred descending word of
`HJO.Braid.wordDownStar` is the descending word `T_k^{-1}⋯T_1^{-1}` in the *inverted* letters, and
above its turning point the ascending train of `HJO.Braid.trainUp` takes precisely that branch;
`HJO.Sweep.trainUpEnd_eq_descendingWord` records it, including the boundary `k = 0` where the two
branches differ and both words are empty. This is the mirror of the reading `VmodRaising.lean`
takes for `T^*_{1↑k+1}`. The unstarred `T_{1↑k+1}` is `HJO.Sweep.cmAscWord q 1 k`, which is
`trainUpEnd q 1 (k+1)` by `HJO.Sweep.cmAscWord`; the cancellation the comparison needs is then
`HJO.Braid.trainUp_mul_trainUp_self` at the braid system of rank `k+1`.

**Two of the four are earlier lemmas, restated at the indices used here.**
`HJO.Sweep.dplus_braid` is `HJO.Sweep.dplus_braid_succ` and `HJO.Sweep.braid_one_dplus_dplus` is
`HJO.Sweep.braid_one_dplus_sq`; both are proved for `HJO.Sweep.dplus` as the two ingredients of
`HJO.Sweep.braid_dplusIter`. The declarations below restate those two lemmas rather than giving a
second proof.

**Hypotheses dropped.** `HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus`, `HJO.Sweep.dplus_braid_succ` and
`HJO.Sweep.dplus_auxVar_one_mul` do not read the `F ∈ V_k`: every step is an identity between
operators on the whole total space. `HJO.Sweep.braid_one_dplus_sq` *does* read it, and it is carried
— the argument needs `s_{k+1}` to fix `τ_{k+2,k+2}τ_{k+1,k+1}(F)`, which fails as soon as `F`
involves `y_{k+1}`. The `k ≥ 2` in `HJO.Sweep.dplus_braid_succ` is implied by `1 ≤ i` and
`i + 1 ≤ k`, its reading of `1 ≤ i ≤ k-1` without truncated subtraction, and `1 ≤ i` is not
droppable: at the unread index `0` the left side loses its braid operator while the right side
keeps `T_1`. The `k ≥ 1` of `HJO.Sweep.dplus_auxVar_one_mul` is carried, the proof splitting the
head letter `T_1` off a word that is empty at `k = 0`.

`q ≠ 0` appears in the two statements that read an inverse, `HJO.Sweep.braid_braidInv` being
available only then; the arguments as usually written assume it too.

## References

Following A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-! ### The starred descending word, and the cancellation it performs -/

/-- An ascending train above its turning point is the descending word in the *inverted* letters,
which is Mellit's starred descending word `T^*_{b↓1}`. Stated at `b = k + 1` because at `b = 0` the
branch of `HJO.Braid.trainUp` is the other one and reads the unread letter `T_0`; at `b = 1` the two
branches are both the empty product, which is the case the proof splits off. -/
theorem trainUpEnd_eq_descendingWord (q : L) (k : ℕ) :
    trainUpEnd q (k + 1) 1 = Braid.descendingWord (braidInvEnd q) (k + 1) 1 := by
  rw [trainUpEnd, Braid.trainUp]
  split_ifs with h
  · obtain rfl : k = 0 := by omega
    simp [Braid.ascendingWord, Braid.descendingWord]
  · rfl

/-- **The starred descending word undoes the ascending one**: `T^*_{k+1↓1}T_{1↑k+1} = 1`. This is
`HJO.Braid.wordDownStar_mul_wordUp` for the braid operators on the total space, read through the
trains: both words are trains of the braid system of rank `k + 1` based at the two ends `1` and
`k + 1`, and `HJO.Braid.trainUp_mul_trainUp_self` is the cancellation. -/
theorem trainUpEnd_star_mul_cmAscWord (q : L) (hq : q ≠ 0) (k : ℕ) :
    trainUpEnd q (k + 1) 1 * cmAscWord q 1 k = 1 := by
  rw [cmAscWord]
  exact Braid.trainUp_mul_trainUp_self (isBraidSystem_braidEnd q hq (k + 1)) (by omega) le_rfl
    (by omega) (by omega)

/-- **The starred descending word recovers the substitution inside `d_+`**:
`T^*_{k+1↓1}(d_+F) = τ_{k+1,k+1}(F)`, the one computation the comparison of the two raising
operators rests on. -/
theorem trainUpEnd_star_cmDPlus (q : L) (hq : q ≠ 0) (k : ℕ) (F : Total L) :
    trainUpEnd q (k + 1) 1 (cmDPlus q k F) = qshift q (k + 1) F := by
  have hcancel := LinearMap.congr_fun (trainUpEnd_star_mul_cmAscWord q hq k)
    (qshift q (k + 1) F)
  rw [Module.End.mul_apply, Module.End.one_apply] at hcancel
  rw [cmDPlus_apply, hcancel]

/-! ### The two raising operators -/

/-- **The two raising operators**, `HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus`: for `k ≥ 0` and
`F ∈ V_k`,
`d^♭_+F = -T_{1↑k+1}(y_{k+1}T^*_{k+1↓1}(d_+F))`,
with `d_+` the unmodified operator of `HJO.Sweep.cmDPlus` and the two words those of
`HJO.Braid.wordUp` and `HJO.Braid.wordDownStar` in the invertible `T_1, …, T_k`.

`HJO.Sweep.trainUpEnd_star_cmDPlus` turns `T^*_{k+1↓1}(d_+F)` into `τ_{k+1,k+1}(F)`, and the
right-hand side is then the defining formula `HJO.Sweep.dplus_eq_ascWord` of `d^♭_+` verbatim. The
hypothesis `F ∈ V_k` is not read: the cancellation is an identity of operators on the whole total
space. -/
@[hjo "lem_vmod_dplus_compare"]
theorem dplus_eq_neg_cmAscWord_cmDPlus (q : L) (hq : q ≠ 0) (k : ℕ) (F : Total L) :
    dplus q k F
      = -cmAscWord q 1 k
          ((auxVar (k + 1) : Total L) * trainUpEnd q (k + 1) 1 (cmDPlus q k F)) := by
  rw [trainUpEnd_star_cmDPlus q hq, dplus_eq_ascWord]

/-! ### The braid index shifts -/

/-- **The modified raising operator shifts the braid index**,
`HJO.Sweep.dplus_braid_succ`: for `k ≥ 2`, `1 ≤ i ≤ k-1` and `F ∈ V_k`,
`d^♭_+(T_iF) = T_{i+1}(d^♭_+F)`.

This is `HJO.Sweep.dplus_braid` at the indices used here: `1 ≤ i` and
`i + 1 ≤ k` are `1 ≤ i ≤ k-1` without truncated subtraction, and together they force `k ≥ 2`. The
hypothesis `F ∈ V_k` is not read — the letter `y_{k+1}` that `d^♭_+` carries is `s_i`-symmetric for
those indices, so it passes `T_i` on the whole total space, and what remains is
`HJO.Sweep.cmDPlus_braid`. -/
@[hjo "lem_vmod_dplus_braid_mod"]
theorem dplus_braid_succ (q : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) (F : Total L) :
    dplus q k (braid q i F) = braid q (i + 1) (dplus q k F) :=
  dplus_braid q hi hik F

/-- `HJO.Sweep.dplus_braid_succ` in the endomorphism monoid, `d^♭_+T_i = T_{i+1}d^♭_+`. -/
theorem dplus_mul_braidEnd_succ (q : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    dplus q k * braidEnd q i = braidEnd q (i + 1) * dplus q k :=
  LinearMap.ext fun F => dplus_braid_succ q hi hik F

/-! ### The double image is braid invariant -/

/-- **The modified raising operator squared is braid invariant**,
`HJO.Sweep.braid_one_dplus_sq`: for `k ≥ 0` and `F ∈ V_k`,
`T_1(d^♭_+d^♭_+F) = d^♭_+d^♭_+F`.

This is `HJO.Sweep.braid_one_dplus_dplus`, whose proof is the argument: the two
ascending words merge by the braid identity `T_{1↑k+2}T_{1↑k+1} = T_{2↑k+2}T_{1↑k+2}`
(`HJO.Sweep.cmAscWord_word_shift`), the merged argument
`y_{k+1}y_{k+2}τ_{k+2,k+2}τ_{k+1,k+1}(F)` is symmetric in `y_{k+1}` and `y_{k+2}`
(`HJO.Sweep.swapAux_qshift_qshift`) so `T_{k+1}` fixes it, and `T_1` may then be prefixed because
`T_1T_{2↑k+2} = T_{1↑k+2}`.

**The `F ∈ V_k` is load-bearing and is carried.** It is what makes the merged argument
symmetric: as soon as `F` involves `y_{k+1}`, `s_{k+1}` no longer fixes
`τ_{k+2,k+2}τ_{k+1,k+1}(F)` and the conclusion fails. -/
@[hjo "lem_vmod_dplus_sq_mod"]
theorem braid_one_dplus_sq (q : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    braid q 1 (dplus q (k + 1) (dplus q k F)) = dplus q (k + 1) (dplus q k F) :=
  braid_one_dplus_dplus q hF

/-! ### The first variable -/

/-- **The modified raising operator and the first variable**, `HJO.Sweep.dplus_auxVar_one_mul`:
for `k ≥ 1` and `F ∈ V_k`,
`d^♭_+(y_1F) = T_1(y_1T_1^{-1}(d^♭_+F))`.

The proof. `τ_{k+1,k+1}` fixes `y_1` (`HJO.Sweep.qshift_auxVar_apply`), so
`d^♭_+(y_1F) = -T_{1↑k+1}(y_1y_{k+1}τ_{k+1,k+1}F)`; splitting the head letter
`T_{1↑k+1} = T_1T_{2↑k+1}` and letting `y_1` pass `T_{2↑k+1}`, which every `s_i` with `i ≥ 2`
fixes (`HJO.Sweep.cmAscWord_mul_of_swapAux_eq`), gives
`-T_1(y_1T_{2↑k+1}(y_{k+1}τ_{k+1,k+1}F))`. On the other side the same split identifies
`T_1^{-1}(d^♭_+F)` with `-T_{2↑k+1}(y_{k+1}τ_{k+1,k+1}F)`, the inverse existing by
`HJO.Sweep.braid_braidInv`.

The `F ∈ V_k` is not read; its `k ≥ 1` is, the head letter being absent from the empty
word at `k = 0`. -/
@[hjo "lem_vmod_dplus_y1"]
theorem dplus_auxVar_one_mul (q : L) (hq : q ≠ 0) {k : ℕ} (hk : 1 ≤ k) (F : Total L) :
    dplus q k ((auxVar 1 : Total L) * F)
      = braid q 1 ((auxVar 1 : Total L) * braidInv q 1 (dplus q k F)) := by
  have hinv : braidInv q 1 (dplus q k F)
      = -cmAscWord q 2 k ((auxVar (k + 1) : Total L) * qshift q (k + 1) F) := by
    rw [dplus_apply_head q hk, map_neg, braidInv_braid q hq]
  have hpass : cmAscWord q 2 k
        ((auxVar 1 : Total L) * ((auxVar (k + 1) : Total L) * qshift q (k + 1) F))
      = (auxVar 1 : Total L)
        * cmAscWord q 2 k ((auxVar (k + 1) : Total L) * qshift q (k + 1) F) :=
    cmAscWord_mul_of_swapAux_eq q (a := 2) (b := k) (by omega)
      (fun j hj _ => swapAux_auxVar_of_ne (by omega) (by omega) (by omega)) _
  have hmove : (auxVar (k + 1) : Total L) * ((auxVar 1 : Total L) * qshift q (k + 1) F)
      = (auxVar 1 : Total L) * ((auxVar (k + 1) : Total L) * qshift q (k + 1) F) := by
    ring
  have hfix : qshift q (k + 1) ((auxVar 1 : Total L) * F)
      = (auxVar 1 : Total L) * qshift q (k + 1) F := by
    rw [map_mul, qshift_auxVar_apply]
  rw [hinv, dplus_eq_ascWord, hfix, hmove, cmAscWord_apply_succ_left q hk, hpass, mul_neg,
    map_neg]

end Field

end HJO.Sweep
