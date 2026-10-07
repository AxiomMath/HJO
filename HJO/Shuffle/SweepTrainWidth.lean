/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepBraidMonomial
public import HJO.Shuffle.CornerClosedForm
public import HJO.Shuffle.MellitDplusVacuum
public import HJO.CMStructure.VmodRaising
public import HJO.CarlssonMellit.AmbientBrackets

/-! # The ascending train on the staircase, and `d_+` and `Δ` at every width

The three operators of `HJO.Mellit.sweepOperator` are, at every width, a braid word applied to a
monomial: `HJO.Sweep.dplus_apply` and `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` both put the
whole computation inside the ascending train `T_{1↗k+1}`, and `HJO.Sweep.dminus_auxVar_pow_mul`
already evaluates `d_-` at every width. This file evaluates that train on the shapes the sweep
meets, using the closed form of one letter from `HJO/Shuffle/SweepBraidMonomial.lean`. Everything is
stated at general width; widths `3` and `4` are instances.

## What the train does

Two shapes, and they are the only two the train handles without branching.

* **Symmetric.** `T_{1↗k+1}S = S` when `S` is symmetric in `y_1, …, y_{k+1}`
  (`HJO.Sweep.cmAscWord_one_eq_self_of_swapAux_eq`), each letter being the identity by
  `HJO.Sweep.braid_eq_self_of_swapAux_eq`. Consequently `Δ^{(k+1)}S = -q^ky_1S` on such an `S`
  (`HJO.Sweep.corner_of_swapAux_eq`); at the list level this is
  `HJO.Sweep.prod_map_braidEnd_apply_of_swapAux_eq`, which is where
  `HJO.Sweep.dplus_auxVarProd` gets `d_+^{(k)}(y_1⋯y_k) = -y_1⋯y_{k+1}` from.
* **Symmetric times the last variable.** `T_{1↗k+1}(Sy_{k+1}) = q^kSy_1`
  (`HJO.Sweep.cmAscWord_one_mul_auxVar_last`), which is the `k`-fold cascade of the single letter
  `T_i(y_i^by_{i+1}^{b+1}) = qy_i^{b+1}y_{i+1}^b`: each letter moves the extra power down one index
  and emits one `q`. The bare case `S = 1` is `HJO.Sweep.cmAscWord_one_auxVar_last`,
  `T_{1↗k+1}(y_{k+1}) = q^ky_1`.

## The two closed forms for `d_+` and `Δ` at every width

`HJO.Sweep.cmAscWord_auxVar_last_mul` already trades the ascending train for
the *descending* one, so both operators have a closed form on the whole space for `q ≠ 0`:

* `HJO.Sweep.corner_eq_neg_auxVar_mul_trainDownEnd`: `Δ^{(k+1)}F = -q^ky_1T^*_{1↗k+1}F` on
  `V_{k+1}`;
* `HJO.Sweep.dplus_eq_neg_auxVar_mul_trainDownEnd`:
  `d_+^{(k)}F = -q^ky_1T^*_{1↗k+1}(τ_{k+1,k+1}F)`.

These are the statements to reach for when the argument is *not* symmetric: they move the whole
problem to the inverted letters, where `HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow` and
`HJO.Sweep.braidInv_eq_self_of_swapAux_eq` apply.

## The one place a power of `q` appears, and where it does not

The earlier `HJO.Sweep.dplus_auxVarProd` carries **no** power of `q` at any width, and
`HJO.Sweep.corner_auxVarProd` carries exactly `q^k`. The difference is the symmetric case: `d_+`
applied to `y_1⋯y_k` produces `y_1⋯y_{k+1}`, symmetric in all `k+1` variables, on which every letter
of the train is the identity; the corner inserts a *second* copy of `y_{k+1}`, and it is that extra
copy which walks down the train emitting one `q` per letter. Reading `T_i` as multiplication by `q`
on the symmetric vector instead would put `q^k` into both, and is wrong in the first.

## Genericity

`q ≠ 0` is spent wherever `T_i^{-1}` occurs and wherever the corner's general closed form is quoted
(`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` reads it through
`HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus`); `q ≠ 1` is spent by every statement about
`HJO.Sweep.corner`, since `HJO.Sweep.corner` carries the literal `(q-1)^{-1}` and at `q = 1` a
field's `0^{-1} = 0` makes the operator the zero map — so those statements are *false* at `q = 1`,
not vacuous. The statements about the train itself and
`HJO.Sweep.dplus_eq_neg_auxVar_mul_trainDownEnd` spend nothing beyond what is written: no inverse of
`q` occurs in the train statements. `u` occurs nowhere: neither `HJO.Sweep.dplus` nor
`HJO.Sweep.corner` reads it.

## References

Transcribing A. Mellit, *Toric braids and
`(m,n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

section Field

variable {L : Type*} [Field L] {q : L}

/-! ### The ascending train on the two shapes it evaluates in closed form -/

/-- **`T_{1↗k+1}S = S` for `S` symmetric in `y_1, …, y_{k+1}`.** Every letter of the train is the
identity on such an `S` (`HJO.Sweep.braid_eq_self_of_swapAux_eq`); read here off
`HJO.Sweep.cmAscWord_mul_of_swapAux_eq` at `F = 1`, together with `T_{[1,k]}1 = 1`. -/
theorem cmAscWord_one_eq_self_of_swapAux_eq (q : L) (k : ℕ) {S : Total L}
    (hS : ∀ j, 1 ≤ j → j ≤ k → swapAux L j S = S) : cmAscWord q 1 k S = S := by
  have h := cmAscWord_mul_of_swapAux_eq q (a := 1) (b := k) (by omega) hS 1
  rwa [mul_one, cmAscWord_map_one q (by omega), mul_one] at h

/-- **`T_{1↗k+1}(y_{k+1}) = q^ky_1`**, at every width and for every `q`.

The cascade: `T_k` sends `y_{k+1}` to `qy_k` (`HJO.Sweep.braid_auxVar_pow_mul_auxVar_pow_succ` at
`b = 0`), then `T_{k-1}` sends `y_k` to `qy_{k-1}`, and so on down to `y_1`, one factor of `q` per
letter. Nothing is inverted, so no hypothesis on `q` is needed: the `q` comes from the braid letter,
not from a normalisation. -/
theorem cmAscWord_one_auxVar_last (q : L) (k : ℕ) :
    cmAscWord q 1 k (auxVar (k + 1) : Total L) = scal (q ^ k) * auxVar 1 := by
  induction k with
  | zero =>
    have h0 : cmAscWord q 1 0 = (1 : Module.End L (Total L)) := cmAscWord_self_pred q 0
    rw [h0, Module.End.one_apply, pow_zero, scal_one, one_mul]
  | succ k ih =>
    have hstep : braid q (k + 1) (auxVar (k + 1 + 1) : Total L)
        = scal q * (auxVar (k + 1) : Total L) := by
      have h := braid_auxVar_pow_mul_auxVar_pow_succ q (i := k + 1) (L := L) (by omega) 0
      simpa using h
    rw [cmAscWord_one_succ_apply, hstep, cmAscWord_scal_mul, ih, pow_succ, scal_mul]
    ring

/-- **`T_{1↗k+1}(Sy_{k+1}) = q^kSy_1`** for `S` symmetric in `y_1, …, y_{k+1}`: the train is linear
over what every one of its letters fixes (`HJO.Sweep.cmAscWord_mul_of_swapAux_eq`), and
`HJO.Sweep.cmAscWord_one_auxVar_last` evaluates it on the remaining `y_{k+1}`.

This is the shape `HJO.Sweep.corner` presents to the train whenever the vector it is applied to is
symmetric: the extra power of the last variable walks down to `y_1`, emitting `q` at each of the `k`
letters. -/
theorem cmAscWord_one_mul_auxVar_last (q : L) (k : ℕ) {S : Total L}
    (hS : ∀ j, 1 ≤ j → j ≤ k → swapAux L j S = S) :
    cmAscWord q 1 k (S * (auxVar (k + 1) : Total L)) = scal (q ^ k) * (S * auxVar 1) := by
  rw [cmAscWord_mul_of_swapAux_eq q (by omega) hS, cmAscWord_one_auxVar_last]
  ring

/-! ### `d_+` at every width -/

/-- **`d_+^{(k)}F = -q^ky_1T^*_{1↗k+1}(τ_{k+1,k+1}F)`** at every width, for `q ≠ 0`: the closed form
of `HJO.Sweep.dplus` in the *inverted* letters.

`HJO.Sweep.dplus_apply` puts `y_{k+1}τ_{k+1,k+1}F` inside the ascending train, and
`HJO.Sweep.cmAscWord_auxVar_last_mul` trades that train for the descending
one at the cost of `q^ky_1` outside. No condition on `F` is read: the identity holds on the whole
total space. -/
theorem dplus_eq_neg_auxVar_mul_trainDownEnd (hq : q ≠ 0) (k : ℕ) (F : Total L) :
    dplus q k F
      = -(scal (q ^ k) * (auxVar 1 * trainDownEnd q 1 (k + 1) (qshift q (k + 1) F))) := by
  have hw : ∀ G : Total L, trainUpEnd q 1 (k + 1) G = cmAscWord q 1 k G := fun _ => rfl
  rw [dplus_apply, hw, cmAscWord_auxVar_last_mul q hq k _]
  ring

end Field

/-! ### `Δ` at every width -/

section Corner

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

/-- **`Δ^{(k+1)}F = -q^ky_1T^*_{1↗k+1}F`** for every `k`, every `F ∈ V_{k+1}` and every
`q ∉ {0, 1}`: the closed form of `HJO.Sweep.corner` in the *inverted* letters.

`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` already puts the corner inside the ascending train;
`HJO.Sweep.cmAscWord_auxVar_last_mul` trades that train for the descending one. Both exclusions are
irreducible — `q ≠ 1` because `HJO.Sweep.corner` carries `(q-1)^{-1}`, `q ≠ 0` because the
right-hand side names inverted braid letters. -/
theorem corner_eq_neg_auxVar_mul_trainDownEnd (hq0 : q ≠ 0) (hq1 : q ≠ 1) (m : ℕ) {F : Total L}
    (hF : F ∈ piece L (m + 1)) :
    corner q (m + 1) F = -(scal (q ^ m) * (auxVar 1 * trainDownEnd q 1 (m + 1) F)) := by
  rw [corner_eq_neg_cmAscWord_auxVar_mul hq0 hq1 m hF, cmAscWord_auxVar_last_mul q hq0 m F]
  ring

/-- **`Δ^{(k+1)}S = -q^ky_1S`** for every `S ∈ V_{k+1}` symmetric in `y_1, …, y_{k+1}`, whenever
`q ∉ {0, 1}`.

The corner on a symmetric vector is multiplication by `-q^ky_1` and nothing more: the train is the
identity on the symmetric part, and the single `y_{k+1}` that `HJO.Sweep.corner` inserts walks down
to `y_1` emitting one `q` per letter. At `k = 1`, `S = y_1y_2` this is
`HJO.Sweep.corner_two_X_zero_mul_X_one`. -/
theorem corner_of_swapAux_eq (hq0 : q ≠ 0) (hq1 : q ≠ 1) (m : ℕ) {S : Total L}
    (hS : S ∈ piece L (m + 1)) (hsym : ∀ j, 1 ≤ j → j ≤ m → swapAux L j S = S) :
    corner q (m + 1) S = -(scal (q ^ m) * ((auxVar 1 : Total L) * S)) := by
  rw [corner_eq_neg_cmAscWord_auxVar_mul hq0 hq1 m hS,
    show (auxVar (m + 1) : Total L) * S = S * auxVar (m + 1) from mul_comm _ _,
    cmAscWord_one_mul_auxVar_last q m hsym]
  ring

/-- **`Δ^{(k+1)}(y_1⋯y_{k+1}) = -q^ky_1^2y_2⋯y_{k+1}`** at every width, for `q ∉ {0, 1}`.
`HJO.Sweep.corner_of_swapAux_eq` at the staircase monomial. At `k = 1` this is
`HJO.Sweep.corner_two_X_zero_mul_X_one`; the widths `3` and `4` are `m = 2` and `m = 3`. -/
theorem corner_auxVarProd (hq0 : q ≠ 0) (hq1 : q ≠ 1) (m : ℕ) :
    corner q (m + 1) (auxVarProd L (m + 1))
      = -(scal (q ^ m) * ((auxVar 1 : Total L) * auxVarProd L (m + 1))) :=
  corner_of_swapAux_eq hq0 hq1 m (auxVarProd_mem_piece L (m + 1))
    fun _ _ hj2 => swapAux_auxVarProd hj2

/-- **`Δ^{(k+1)}(f·(y_1⋯y_{k+1})^b) = -q^ky_1·f·(y_1⋯y_{k+1})^b`** for every symmetric function `f`,
every `b` and every width, whenever `q ∉ {0, 1}`: a `Λ`-multiple of a power of the staircase is
symmetric, so `HJO.Sweep.corner_of_swapAux_eq` applies. -/
theorem corner_C_mul_auxVarProd_pow (hq0 : q ≠ 0) (hq1 : q ≠ 1) (m b : ℕ) (f : Sym.Lambda L) :
    corner q (m + 1) (MvPolynomial.C f * auxVarProd L (m + 1) ^ b)
      = -(scal (q ^ m) * ((auxVar 1 : Total L)
          * (MvPolynomial.C f * auxVarProd L (m + 1) ^ b))) := by
  refine corner_of_swapAux_eq hq0 hq1 m ?_ fun _ _ hj2 => ?_
  · exact mul_mem (Subalgebra.algebraMap_mem _ f) (pow_mem (auxVarProd_mem_piece L (m + 1)) b)
  · rw [map_mul, map_pow, swapAux_C, swapAux_auxVarProd hj2]

end Corner

end HJO.Sweep

end
