/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.DemazureIdentities
public import HJO.Shuffle.CMRaising
public import HJO.Shuffle.QShiftInverse
public meta import HJO.Attr

/-! # The ascending word on the last variable, and the unit shift past the raising operator

Two statements of Mellit's `V`-module subsection that the existing layer already has all the
pieces for.

`HJO.Sweep.cmAscWord_auxVar_last_mul` moves the whole ascending word `T_{1↗k+1}` past the *last*
variable at once: `T_{1↗k+1}(y_{k+1}G) = q^ky_1T^*_{1↗k+1}G`. Each letter contributes one
conjugation `T_i(y_{i+1}H) = qy_iT_i^{-1}H` — `HJO.Sweep.braid_auxVar_succ_mul_braid` — and the `k`
factors of `q` accumulate while the inverted
letters accumulate into the starred word. It is what turns the modified raising operator's value on
the unit into `-q^ky_1`, which is the second generator of Mellit's kernel ideal.

`HJO.Sweep.unitShiftTotal_cmDPlus` is the raising half of the unit-shift calculus: `ϑ` commutes with
`d_+`. Its two ingredients are already proved — `HJO.Sweep.unitShiftTotal_qshift` and
`HJO.Sweep.unitShiftTotal_braid` — and all that is added here is
that a map commuting with every letter commutes with the word.

## Main results

* `HJO.Sweep.cmAscWord_auxVar_last_mul`.
* `HJO.Sweep.unitShiftTotal_cmDPlus`.

## Implementation notes

**Mellit's `T^*_{1↗k+1}` is `HJO.Sweep.trainDownEnd q 1 (k+1)`.** The starred ascending word of
`HJO.Braid.wordUpStar` is the ascending word in the *inverted* letters, and by
`HJO.Braid.trainUp_inv_eq_trainDown` that is the descending train of the uninverted family; on the
total space the descending train at `a = 1 < b` is by definition
`ascendingWord (braidInvEnd q) 1 b`. `HJO.Sweep.trainDownEnd_eq_ascendingWord` records the one
boundary case, `b = 1`, where the branch of `HJO.Braid.trainDown` is the other one and both words
are empty. The unstarred word is written `HJO.Sweep.cmAscWord q 1 k`, which is
`trainUpEnd q 1 (k+1)` by `HJO.Sweep.cmAscWord`.

**The `G ∈ V_{k+1}` is dropped.** Every step of the induction — the conjugation
`HJO.Sweep.braid_auxVar_succ_mul_braid`, the splitting of the word, the scalar coming out — holds
for an arbitrary element of the total space, so the membership hypothesis carries no content and the
statement is proved in that generality. That also disposes of
the warning, in the argument as usually written, about the inductive hypothesis having to be "read
inside `V_{k+1}` with
the variable `y_k` in place of `y_{k+1}`": on the total space the inductive statement at `k-1` *is*
the statement at `k-1`, with no relocation.

`q ≠ 0` appears because the conjugation is applied to `T_i^{-1}G`, and `T_i^{-1}` is a two-sided
inverse only then (`HJO.Sweep.braid_braidInv`). The argument as usually written assumes it too.

## References

Lemmas `HJO.Sweep.cmAscWord_auxVar_last_mul` and `HJO.Sweep.unitShiftTotal_cmDPlus`, on the modified
generators, using `HJO.Sweep.piece`, `HJO.Sweep.braid`, `HJO.Braid.wordUp`, `HJO.Braid.wordUpStar`,
`HJO.Sweep.cmDPlus` and `HJO.Sweep.unitShiftTotal`. Following A. Mellit, *Toric braids and
`(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-- A descending train above its turning point is the plain ascending word in the inverted letters,
which is Mellit's starred ascending word `T^*_{a↗b}`. The hypothesis `1 ≤ b` is needed only at
`b = 0`, where `HJO.Braid.trainDown` takes its other branch and reads a letter the word does not
have. -/
theorem trainDownEnd_eq_ascendingWord (q : L) {b : ℕ} (hb : 1 ≤ b) :
    trainDownEnd q 1 b = Braid.ascendingWord (braidInvEnd q) 1 b := by
  rw [trainDownEnd, Braid.trainDown]
  split_ifs with h
  · obtain rfl : b = 1 := by omega
    simp [Braid.descendingWord, Braid.ascendingWord]
  · rfl

/-- The starred ascending word absorbs one more inverted letter on the right:
`T^*_{1↗b+1} = T^*_{1↗b}T_b^{-1}`. -/
theorem trainDownEnd_succ (q : L) {b : ℕ} (hb : 1 ≤ b) :
    trainDownEnd q 1 (b + 1) = trainDownEnd q 1 b * braidInvEnd q b := by
  rw [trainDownEnd_eq_ascendingWord q (by omega), trainDownEnd_eq_ascendingWord q hb,
    ← Braid.ascendingWord_succ_self (braidInvEnd q) b,
    Braid.ascendingWord_mul (braidInvEnd q) (by omega) (by omega)]

/-- **The ascending word on the last variable**, `HJO.Sweep.cmAscWord_auxVar_last_mul`:
`T_{1↗k+1}(y_{k+1}G) = q^{k}\,y_1\,T^*_{1↗k+1}G`.

Induction on `k`. At `k = 0` both words are empty and both sides are `y_1G`. The step splits
`T_{1↗k+2} = T_{1↗k+1}T_{k+1}`, applies `HJO.Sweep.braid_auxVar_succ_mul_braid` at `i = k+1` to
`T_{k+1}(y_{k+2}G) = qy_{k+1}T_{k+1}^{-1}G`, pulls the scalar out through the word, and finishes
with the inductive hypothesis at `T_{k+1}^{-1}G` — the one extra inverted letter being exactly what
`HJO.Sweep.trainDownEnd_succ` appends to the starred word. -/
@[hjo "lem_vmod_top_y_word"]
theorem cmAscWord_auxVar_last_mul (q : L) (hq : q ≠ 0) (k : ℕ) (G : Total L) :
    cmAscWord q 1 k ((auxVar (k + 1) : Total L) * G)
      = scal (q ^ k) * auxVar 1 * trainDownEnd q 1 (k + 1) G := by
  induction k generalizing G with
  | zero =>
    rw [cmAscWord_self_pred, pow_zero, scal_one, one_mul]
    have h1 : trainDownEnd q 1 1 = 1 := by
      rw [trainDownEnd, Braid.trainDown_self]
    rw [h1]
    rfl
  | succ k ih =>
    have hsplit : cmAscWord q 1 (k + 1) = cmAscWord q 1 k * braidEnd q (k + 1) := by
      rw [cmAscWord_split q (c := k) (by omega) (by omega), cmAscWord_self]
    have hconj : braid q (k + 1) ((auxVar (k + 2) : Total L) * G)
        = scal q * auxVar (k + 1) * braidInv q (k + 1) G := by
      have h := braid_auxVar_succ_mul_braid q (i := k + 1) (by omega) (braidInv q (k + 1) G)
      rwa [braid_braidInv q hq (k + 1) G] at h
    have hstep : cmAscWord q 1 (k + 1) ((auxVar (k + 2) : Total L) * G)
        = cmAscWord q 1 k (braid q (k + 1) ((auxVar (k + 2) : Total L) * G)) := by
      rw [hsplit]
      rfl
    rw [hstep, hconj, mul_assoc,
      cmAscWord_mul_of_swapAux_eq q (a := 1) (b := k) (by omega)
        (fun _ _ _ => swapAux_scal _ _), ih, trainDownEnd_succ q (b := k + 1) (by omega)]
    have hlast : (trainDownEnd q 1 (k + 1) * braidInvEnd q (k + 1)) G
        = trainDownEnd q 1 (k + 1) (braidInv q (k + 1) G) := rfl
    rw [hlast, pow_succ, scal_mul]
    ring

/-! ### The unit shift past the raising operator -/

/-- **`ϑ` commutes with the ascending word**, letter by letter: `HJO.Sweep.unitShiftTotal_braid`
gives the commutation with each `T_j`, and an element commuting with every entry of a list commutes
with the list's product (`HJO.Braid.mul_prod_comm`). -/
theorem unitShiftTotal_mul_cmAscWord (q : L) {a b : ℕ} (hab : a ≤ b + 1) :
    (unitShiftTotal L).toLinearMap.restrictScalars L * cmAscWord q a b
      = cmAscWord q a b * (unitShiftTotal L).toLinearMap.restrictScalars L := by
  rw [cmAscWord, trainUpEnd_eq_ascendingWord q hab, Braid.ascendingWord]
  refine Braid.mul_prod_comm fun y hy => ?_
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hy
  exact LinearMap.ext fun F => unitShiftTotal_braid q j F

/-- **`ϑ(T_{[a,b]}F) = T_{[a,b]}(ϑF)`**, the applied form. -/
theorem unitShiftTotal_cmAscWord (q : L) {a b : ℕ} (hab : a ≤ b + 1) (F : Total L) :
    unitShiftTotal L (cmAscWord q a b F) = cmAscWord q a b (unitShiftTotal L F) :=
  LinearMap.congr_fun (unitShiftTotal_mul_cmAscWord q hab) F

/-- **The unit shift commutes with the raising operator**, `HJO.Sweep.unitShiftTotal_cmDPlus`:
`ϑ_{k+1}(d_+F) = d_+(ϑ_kF)`, with `d_+` the operator of `HJO.Sweep.cmDPlus`.

`d_+F = T_{[1,k]}(τ_{k+1,k+1}F)`, and `ϑ` commutes with `τ_{k+1,k+1}`
(`HJO.Sweep.unitShiftTotal_qshift`) and with the word
(`HJO.Sweep.unitShiftTotal_cmAscWord`). On the total space `ϑ` does not depend on the width, so the
maps `ϑ_{k+1}` and `ϑ_k` — which one identifies by noting that the restriction of one to
`V_k ⊆ V_{k+1}` is the other — are the same map here and nothing has to be said. -/
@[hjo "lem_vmod_tau_dplus"]
theorem unitShiftTotal_cmDPlus (q : L) (k : ℕ) (F : Total L) :
    unitShiftTotal L (cmDPlus q k F) = cmDPlus q k (unitShiftTotal L F) := by
  rw [cmDPlus_apply, cmDPlus_apply, unitShiftTotal_cmAscWord q (a := 1) (b := k) (by omega),
    unitShiftTotal_qshift]

/-- **The unit shift commutes with the sweep process's raising operator too**, the same statement
for `HJO.Sweep.dplus`: the extra letter `y_{k+1}` that `HJO.Sweep.dplus` carries is fixed by `ϑ`,
which is a `𝕜[y]`-algebra map, so the sign and the letter pass unchanged. -/
theorem unitShiftTotal_dplus (q : L) (k : ℕ) (F : Total L) :
    unitShiftTotal L (dplus q k F) = dplus q k (unitShiftTotal L F) := by
  have hd : ∀ G : Total L, dplus q k G = -cmDPlus q k (auxVar (k + 1) * G) := by
    intro G
    rw [dplus_eq_neg_cmDPlus]
    rfl
  rw [hd, hd, map_neg, unitShiftTotal_cmDPlus, map_mul, unitShiftTotal_auxVar]

end Field

end HJO.Sweep
