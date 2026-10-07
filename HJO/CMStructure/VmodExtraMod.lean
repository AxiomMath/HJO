/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.VmodCommutatorMod
public import HJO.Shuffle.SweepWordV0
public meta import HJO.Attr

/-! # The two extra relations for the modified operators

The fourth and fifth relation families of Mellit's Dyck path algebra, read on the modified operators
`d^♭_±` of `HJO.Sweep.dplus_eq_ascWord` and `HJO.Sweep.dminus`. Writing `C_k` for the commutator
`d^♭_+d^♭_- - d^♭_-d^♭_+` on `V_k`, which `HJO.Sweep.dplus_dminus_sub_dminus_dplus` evaluates to
`(q-1)T_{1↑k}(y_k\cdot)`:

* `HJO.Sweep.dminus_commutator_braid`: `d^♭_-\big(C_k(T_{k-1}F)\big) = q\,C_{k-1}(d^♭_-F)` for
  `k ≥ 2`;
* `HJO.Sweep.braid_one_commutator_dplus`: `T_1\big(C_{k+1}(d^♭_+F)\big) = q\,d^♭_+\big(C_kF\big)`
  for `k ≥ 1`.

Both are pure consequences of `HJO.Sweep.dplus_dminus_sub_dminus_dplus`: each side becomes a word
applied to a variable times something, and the two words are identified by one conjugation:
`HJO.Sweep.braid_auxVar_succ_mul_braid` for the first relation,
`HJO.Sweep.cmAscWord_auxVar_last_mul` together with `HJO.Sweep.dplus_auxVar_one_mul` for the second.

## Main results

* `HJO.Sweep.dminus_commutator_braid`.
* `HJO.Sweep.braid_one_commutator_dplus`.

## Implementation notes

**The commutator is written out rather than named.** It occurs at three different vertices across
the two statements, and it is never needed as an operator; spelling it out keeps each
statement's four operator indices visible, which is what the reader has to check.

**Indices.** `HJO.Sweep.dminus_commutator_braid` is read at `k = m + 2`: it needs `k ≥ 2`, for the
braid operator `T_{k-1}` to be one of `V_k`'s own and for `HJO.Sweep.dplus_dminus_sub_dminus_dplus`
to be available at the vertex `k-1`. `HJO.Sweep.braid_one_commutator_dplus` is read at `k = m + 1`,
its `k ≥ 1` being what `HJO.Sweep.dplus_auxVar_one_mul` reads. No subtraction is truncated in
either.

**The second relation's `q^k` and `q^{k-1}` are not compared as truncated exponents.** The argument
as usually written applies `HJO.Sweep.cmAscWord_auxVar_last_mul` at `k` on one side and "with `k-1`
in place of `k`" on the other; here those are the two instances at `m + 1` and at `m`, and the
identity `(q-1)q^{m+1} = q\big((q-1)q^m\big)` is closed by `ring` in the base field rather than by
any exponent bookkeeping.

**The starred ascending word `T^*_{1↑k}` is `HJO.Sweep.trainDownEnd q 1 k`**, as `VmodRaising.lean`
records. Splitting off its head letter (`HJO.Sweep.trainDownEnd_eq_ascendingWord` and
`HJO.Braid.ascendingWord_mul`) and moving `d^♭_+` through the tail
(`HJO.Braid.mul_ascendingWord`, whose per-letter hypothesis is `HJO.Sweep.dplus_braid_succ`
inverted by `HJO.Braid.comm_shift_inv`) is the identity
`T^*_{2↑k+1}d^♭_+ = d^♭_+T^*_{1↑k}`.

`q ≠ 0` is read throughout, the starred words and the inverse `T_1^{-1}` existing only then
(`HJO.Sweep.braid_braidInv`).

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-- **`d^♭_+` commutes with a scalar**, being `𝕜`-linear. -/
theorem dplus_scal_mul (q : L) (k : ℕ) (x : L) (F : Total L) :
    dplus q k (scal x * F) = scal x * dplus q k F := by
  rw [scal_eq_algebraMap, ← Algebra.smul_def, map_smul, Algebra.smul_def, ← scal_eq_algebraMap]

/-- **`d^♭_+` shifts an inverted braid letter too**: `d^♭_+T_i^{-1} = T_{i+1}^{-1}d^♭_+` for
`1 ≤ i ≤ k-1`. This is `HJO.Sweep.dplus_braid_succ` composed with the two inverses, which exist by
`HJO.Sweep.braid_braidInv` — the usual derivation. -/
theorem dplus_mul_braidInvEnd_succ (q : L) (hq : q ≠ 0) {k i : ℕ} (hi : 1 ≤ i)
    (hik : i + 1 ≤ k) :
    dplus q k * braidInvEnd q i = braidInvEnd q (i + 1) * dplus q k :=
  Braid.comm_shift_inv (braidEnd_mul_braidInvEnd q hq i)
    (braidInvEnd_mul_braidEnd q hq (i + 1)) (dplus_mul_braidEnd_succ q hi hik)

/-- **`T^*_{2↑k+1}d^♭_+ = d^♭_+T^*_{1↑k}`**, the word-level form of
`HJO.Sweep.dplus_mul_braidInvEnd_succ`: every letter of the starred word moves up one index as
`d^♭_+` passes it, and shifting an index range by one turns `T^*_{1↑k}` into `T^*_{2↑k+1}`. -/
theorem dplus_mul_ascendingWord_braidInvEnd (q : L) (hq : q ≠ 0) (m : ℕ) :
    dplus q (m + 1) * Braid.ascendingWord (braidInvEnd q) 1 (m + 1)
      = Braid.ascendingWord (braidInvEnd q) 2 (m + 2) * dplus q (m + 1) :=
  Braid.mul_ascendingWord (T := braidInvEnd q) (W := dplus q (m + 1)) (by omega)
    fun i hi him => dplus_mul_braidInvEnd_succ q hq hi (by omega)

/-- **The starred ascending word gives up its head letter**: `T^*_{1↑m+2} = T_1^{-1}T^*_{2↑m+2}`,
the concatenation of two adjacent index ranges in the inverted letters. -/
theorem trainDownEnd_one_split (q : L) (m : ℕ) :
    trainDownEnd q 1 (m + 2)
      = braidInvEnd q 1 * Braid.ascendingWord (braidInvEnd q) 2 (m + 2) := by
  have h1 : Braid.ascendingWord (braidInvEnd q) 1 2 = braidInvEnd q 1 :=
    Braid.ascendingWord_succ_self (braidInvEnd q) 1
  rw [trainDownEnd_eq_ascendingWord q (b := m + 2) (by omega), ← h1,
    Braid.ascendingWord_mul (braidInvEnd q) (by omega) (by omega)]

end Field

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The first extra relation -/

/-- **The first extra relation for the modified operators**,
`HJO.Sweep.dminus_commutator_braid`: for `k ≥ 2` and `F ∈ V_k`,
`d^♭_-\big((d^♭_+d^♭_- - d^♭_-d^♭_+)(T_{k-1}F)\big) = q\,(d^♭_+d^♭_- - d^♭_-d^♭_+)(d^♭_-F)`,
read at `k = m + 2`.

The proof. `HJO.Sweep.dplus_dminus_sub_dminus_dplus` at the vertex `m+2` turns the left-hand side
into `(q-1)d^♭_-T_{1↑m+2}(y_{m+2}T_{m+1}F)`; splitting the last letter off the word
(`HJO.Sweep.cmAscWord_one_succ_apply`) exposes `T_{m+1}(y_{m+2}T_{m+1}F)`, which is `qy_{m+1}F` by
`HJO.Sweep.braid_auxVar_succ_mul_braid`; and `d^♭_-` then passes the shorter word
(`HJO.Sweep.dminus_cmAscWord`, off `HJO.Sweep.braid_dminus`) and the variable `y_{m+1}`
(`HJO.Sweep.dminus_succ_auxVar_mul`), leaving `q(q-1)T_{1↑m+1}(y_{m+1}d^♭_-F)` — which is
`HJO.Sweep.dplus_dminus_sub_dminus_dplus` at the vertex `m+1`, applied to `d^♭_-F`. -/
@[hjo "lem_vmod_extra_one_mod"]
theorem dminus_commutator_braid (q : L) (hq : q ≠ 0) (m : ℕ) {F : Total L}
    (hF : F ∈ piece L (m + 2)) :
    dminus q (m + 2) (dplus q (m + 1) (dminus q (m + 2) (braid q (m + 1) F))
        - dminus q (m + 3) (dplus q (m + 2) (braid q (m + 1) F)))
      = scal q * (dplus q m (dminus q (m + 1) (dminus q (m + 2) F))
        - dminus q (m + 2) (dplus q (m + 1) (dminus q (m + 2) F))) := by
  have hc2 : ∀ X : Total L, X ∈ piece L (m + 2) →
      dplus q (m + 1) (dminus q (m + 2) X) - dminus q (m + 3) (dplus q (m + 2) X)
        = scal (q - 1) * cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) * X) :=
    fun X hX => dplus_dminus_sub_dminus_dplus q hq (m + 1) hX
  have hc1 : ∀ X : Total L, X ∈ piece L (m + 1) →
      dplus q m (dminus q (m + 1) X) - dminus q (m + 2) (dplus q (m + 1) X)
        = scal (q - 1) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * X) :=
    fun X hX => dplus_dminus_sub_dminus_dplus q hq m hX
  have hTF : braid q (m + 1) F ∈ piece L (m + 2) :=
    braid_mem_piece q (by omega) (by omega) hF
  have hdF : dminus q (m + 2) F ∈ piece L (m + 1) := dminus_mem_piece q (m + 2) hF
  have hconj : braid q (m + 1) ((auxVar (m + 2) : Total L) * braid q (m + 1) F)
      = scal q * auxVar (m + 1) * F :=
    braid_auxVar_succ_mul_braid q (i := m + 1) (by omega) F
  rw [hc2 _ hTF, hc1 _ hdF, cmAscWord_one_succ_apply q m, hconj,
    show (scal q : Total L) * auxVar (m + 1) * F
      = scal q * ((auxVar (m + 1) : Total L) * F) from by ring,
    cmAscWord_scal_mul, dminus_scal_mul, dminus_scal_mul, dminus_cmAscWord q (le_refl m),
    dminus_succ_auxVar_mul q m]
  ring

/-! ### The second extra relation -/

/-- **The second extra relation for the modified operators**,
`HJO.Sweep.braid_one_commutator_dplus`: for `k ≥ 1` and `F ∈ V_k`,
`T_1\big((d^♭_+d^♭_- - d^♭_-d^♭_+)(d^♭_+F)\big) = q\,d^♭_+\big((d^♭_+d^♭_- - d^♭_-d^♭_+)F\big)`,
read at `k = m + 1`.

The proof. `HJO.Sweep.dplus_dminus_sub_dminus_dplus` at the vertex `m+2` makes the left-hand side
`(q-1)T_1T_{1↑m+2}(y_{m+2}d^♭_+F)`, and `HJO.Sweep.cmAscWord_auxVar_last_mul` rewrites the word on
the last variable as `q^{m+1}y_1T^*_{1↑m+2}`. Splitting the head letter off the starred word
(`HJO.Sweep.trainDownEnd_one_split`) and moving `d^♭_+` through the tail
(`HJO.Sweep.dplus_mul_ascendingWord_braidInvEnd`) puts the expression in the shape
`T_1(y_1T_1^{-1}(d^♭_+G))` with `G = T^*_{1↑m+1}F`, which `HJO.Sweep.dplus_auxVar_one_mul` turns
into `d^♭_+(y_1G)`. The right-hand side is the same, `HJO.Sweep.dplus_dminus_sub_dminus_dplus` at
the vertex `m+1` followed by `HJO.Sweep.cmAscWord_auxVar_last_mul` at `m` producing `q\cdot(q-1)q^m`
in place of `(q-1)q^{m+1}`. -/
@[hjo "lem_vmod_extra_two_mod"]
theorem braid_one_commutator_dplus (q : L) (hq : q ≠ 0) (m : ℕ) {F : Total L}
    (hF : F ∈ piece L (m + 1)) :
    braid q 1 (dplus q (m + 1) (dminus q (m + 2) (dplus q (m + 1) F))
        - dminus q (m + 3) (dplus q (m + 2) (dplus q (m + 1) F)))
      = scal q * dplus q (m + 1) (dplus q m (dminus q (m + 1) F)
        - dminus q (m + 2) (dplus q (m + 1) F)) := by
  have hc2 : ∀ X : Total L, X ∈ piece L (m + 2) →
      dplus q (m + 1) (dminus q (m + 2) X) - dminus q (m + 3) (dplus q (m + 2) X)
        = scal (q - 1) * cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) * X) :=
    fun X hX => dplus_dminus_sub_dminus_dplus q hq (m + 1) hX
  have hX : dplus q (m + 1) F ∈ piece L (m + 2) := dplus_mem_piece q (m + 1) hF
  have htop2 : cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) * dplus q (m + 1) F)
      = scal (q ^ (m + 1)) * auxVar 1 * trainDownEnd q 1 (m + 2) (dplus q (m + 1) F) :=
    cmAscWord_auxVar_last_mul q hq (m + 1) (dplus q (m + 1) F)
  have htop1 : cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F)
      = scal (q ^ m) * auxVar 1 * trainDownEnd q 1 (m + 1) F :=
    cmAscWord_auxVar_last_mul q hq m F
  have hinner : trainDownEnd q 1 (m + 2) (dplus q (m + 1) F)
      = braidInv q 1 (dplus q (m + 1) (trainDownEnd q 1 (m + 1) F)) := by
    have h2 : Braid.ascendingWord (braidInvEnd q) 2 (m + 2) (dplus q (m + 1) F)
        = dplus q (m + 1) (Braid.ascendingWord (braidInvEnd q) 1 (m + 1) F) :=
      (LinearMap.congr_fun (dplus_mul_ascendingWord_braidInvEnd q hq m) F).symm
    have h3 : Braid.ascendingWord (braidInvEnd q) 1 (m + 1) = trainDownEnd q 1 (m + 1) :=
      (trainDownEnd_eq_ascendingWord q (by omega)).symm
    rw [trainDownEnd_one_split q m, Module.End.mul_apply, h2, h3]
    rfl
  have hy1 : braid q 1 ((auxVar 1 : Total L)
        * braidInv q 1 (dplus q (m + 1) (trainDownEnd q 1 (m + 1) F)))
      = dplus q (m + 1) ((auxVar 1 : Total L) * trainDownEnd q 1 (m + 1) F) :=
    (dplus_auxVar_one_mul q hq (by omega) (trainDownEnd q 1 (m + 1) F)).symm
  have hL : braid q 1 (dplus q (m + 1) (dminus q (m + 2) (dplus q (m + 1) F))
        - dminus q (m + 3) (dplus q (m + 2) (dplus q (m + 1) F)))
      = scal ((q - 1) * q ^ (m + 1))
        * dplus q (m + 1) ((auxVar 1 : Total L) * trainDownEnd q 1 (m + 1) F) := by
    rw [hc2 _ hX, htop2, hinner,
      show (scal (q - 1) : Total L) * (scal (q ^ (m + 1)) * auxVar 1
            * braidInv q 1 (dplus q (m + 1) (trainDownEnd q 1 (m + 1) F)))
          = scal ((q - 1) * q ^ (m + 1)) * ((auxVar 1 : Total L)
            * braidInv q 1 (dplus q (m + 1) (trainDownEnd q 1 (m + 1) F)))
        from by rw [scal_mul]; ring,
      braid_scal_mul, hy1]
  have hR : scal q * dplus q (m + 1) (dplus q m (dminus q (m + 1) F)
        - dminus q (m + 2) (dplus q (m + 1) F))
      = scal (q * ((q - 1) * q ^ m))
        * dplus q (m + 1) ((auxVar 1 : Total L) * trainDownEnd q 1 (m + 1) F) := by
    rw [dplus_dminus_sub_dminus_dplus q hq m hF, htop1,
      show (scal (q - 1) : Total L)
            * (scal (q ^ m) * auxVar 1 * trainDownEnd q 1 (m + 1) F)
          = scal ((q - 1) * q ^ m)
            * ((auxVar 1 : Total L) * trainDownEnd q 1 (m + 1) F)
        from by rw [scal_mul]; ring,
      dplus_scal_mul, ← mul_assoc, ← scal_mul]
  rw [hL, hR, show (q - 1) * q ^ (m + 1) = q * ((q - 1) * q ^ m) from by ring]

end Newton

end HJO.Sweep

end
