/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepTrainWidth
public import HJO.Shuffle.SweepBraidMonomial
public import HJO.Shuffle.SweepWidthThreeFour

/-! # The ascending train on a monomial the closed form does not reach

`HJO/Shuffle/SweepTrainMonomialClosed.lean` evaluates `T_{1↗k+1}` on `Sy_{k+1}^{n+1}` with `S`
symmetric in `y_1, …, y_{k+1}`. That shape spans exactly the vectors symmetric in `y_1, …, y_k` —
the invariants of the subgroup fixing the top variable — so a monomial whose *lower* exponents are
not constant across `y_1, …, y_k` is outside its reach, and the sweep words of the `4 × 6` rectangle
present such monomials at width `2` and above. This file evaluates the train on them directly.

## The workhorse

`HJO.Sweep.braid_eq_of` is one braid letter, presented as a *check*: to evaluate `T_iF` it suffices
to exhibit the swapped vector `H` and a vector `G` with `(y_{i+1} - y_i)G = F - H`, the second being
a polynomial identity that `ring` discharges. This is `HJO.Sweep.braid` together with
`HJO.Sweep.dividedDiff_unique`, and it turns each letter on a concrete monomial into one `ring`
call rather than a case analysis on which of the two exponents is the larger.

`HJO.Sweep.braid_mul_of_swapAux_eq` then lets the variables the letter does not move ride outside
it, so the train on a monomial in `y_1, …, y_n` is `n - 1` such checks.

## The one general statement

`HJO.Sweep.cmAscWord_one_auxVar_one_mul_auxVar_last`: `T_{1↗k+2}(y_1y_{k+2}) = q^ky_1y_2`, at every
width. The cascade of `HJO.Sweep.cmAscWord_one_auxVar_last` runs down from `y_{k+2}` emitting one
`q` per letter and **stops one step early**, at `y_2`, because the last letter `T_1` meets `y_1y_2`,
which is symmetric. One factor of `q` fewer than the bare cascade is the whole content, and it is
what the width-`4` corner of the `(0,2,3,5,6)` word needs.

## Genericity

Nothing here reads a hypothesis on `q` and nothing mentions `u`: every statement is a polynomial
identity in `q`, holding at `q = 0` and at `q = 1` alike. The corner values that consume them do
carry `q ≠ 0`, `q ≠ 1`, but those come from `HJO.Sweep.corner`'s own `(q-1)^{-1}` and not from
anything here.

## References

Transcribing A. Mellit, *Toric braids and `(m,n)`-parking functions*, §3.2.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

section Field

variable {L : Type*} [Field L] {q : L}

/-! ### One braid letter, presented as a check -/

/-- **`T_iF = H + (q-1)y_iG`** whenever `H` is `s_iF` and `G` solves `(y_{i+1} - y_i)G = F - H`.

This is `HJO.Sweep.braid` with `HJO.Sweep.dividedDiff_unique` supplying `∂_iF = G`: the divided
difference is pinned by that one divisibility, so a candidate quotient checked by `ring` is the
value. On a concrete monomial both hypotheses are polynomial identities, which is what makes this
the practical form of the letter. -/
theorem braid_eq_of (q : L) {i : ℕ} (hi : 1 ≤ i) {F H G : Total L}
    (hs : swapAux L i F = H)
    (hd : ((auxVar (i + 1) : Total L) - auxVar i) * G = F - H) :
    braid q i F = H + scal (q - 1) * (auxVar i * G) := by
  have hx : (MvPolynomial.X i : Total L) = auxVar (i + 1) := by
    rw [auxVar, Nat.add_sub_cancel]
  have hy : (MvPolynomial.X (i - 1) : Total L) = auxVar i := rfl
  have hdd : dividedDiff i F = G :=
    (dividedDiff_unique hi (by rw [hx, hy, hd, hs])).symm
  rw [braid_apply, hs, hdd, mul_assoc]

/-- **`T_i` fixes a vector symmetric in `y_i, y_{i+1}`**, read as a check with `G = 0`: the
`i = 0` clause of `HJO.Sweep.braid_eq_self_of_swapAux_eq`, restated here so the two shapes a train
letter can meet — fixed, or moved by an explicit divided difference — are named side by side. -/
theorem braid_eq_of_swap (q : L) {i : ℕ} {F : Total L} (hs : swapAux L i F = F) :
    braid q i F = F := braid_eq_self_of_swapAux_eq q hs

/-! ### The bottom variable paired with the top one -/

/-- **`T_{1↗k+2}(y_1y_{k+2}) = q^ky_1y_2`**, at every width and for every `q`.

The cascade of `HJO.Sweep.cmAscWord_one_auxVar_last` with the bottom variable sitting alongside:
`T_{k+1}` sends `y_{k+2}` to `qy_{k+1}` and `y_1` rides outside it, and so on down — but the last
letter `T_1` meets `y_1y_2`, which is *symmetric*, and therefore emits nothing. So the answer
carries `q^k` and not `q^{k+1}`: exactly one factor fewer than
`HJO.Sweep.cmAscWord_one_auxVar_last` at the same width.

This is the shape `HJO.Sweep.corner` presents at a monomial whose bottom exponent exceeds the rest,
which is where the collected closed form of `HJO/Shuffle/SweepTrainMonomialClosed.lean` does
not apply: `y_1y_{k+2}` is not `Sy_{k+2}^{n+1}` for any `S` symmetric in `y_1, …, y_{k+2}`. -/
theorem cmAscWord_one_auxVar_one_mul_auxVar_last (q : L) (k : ℕ) :
    cmAscWord q 1 (k + 1) ((auxVar 1 : Total L) * auxVar (k + 2))
      = scal (q ^ k) * ((auxVar 1 : Total L) * auxVar 2) := by
  induction k with
  | zero =>
    have hsym : ∀ j, 1 ≤ j → j ≤ 1 →
        swapAux L j ((auxVar 1 : Total L) * auxVar 2) = (auxVar 1 : Total L) * auxVar 2 := by
      intro j hj1 hj2
      have hj : j = 1 := by omega
      subst hj
      rw [map_mul, swapAux_auxVar_self (by omega), swapAux_auxVar_succ (by omega)]
      ring
    rw [show (0 : ℕ) + 2 = 2 from rfl, cmAscWord_one_eq_self_of_swapAux_eq q 1 hsym, pow_zero,
      scal_one, one_mul]
  | succ m ih =>
    have hfix : swapAux L (m + 2) (auxVar 1 : Total L) = auxVar 1 :=
      swapAux_auxVar_of_ne (by omega) (by omega) (by omega)
    have hstep : braid q (m + 2) (auxVar (m + 3) : Total L)
        = scal q * (auxVar (m + 2) : Total L) := by
      have h := braid_auxVar_pow_mul_auxVar_pow_succ q (i := m + 2) (L := L) (by omega) 0
      simpa using h
    rw [show (m + 1) + 2 = (m + 2) + 1 from rfl, cmAscWord_one_succ_apply,
      show (m + 2) + 1 = m + 3 from rfl, braid_mul_of_swapAux_eq q hfix, hstep,
      show (auxVar 1 : Total L) * (scal q * auxVar (m + 2))
        = scal q * ((auxVar 1 : Total L) * auxVar (m + 2)) from by ring,
      cmAscWord_scal_mul, ih, pow_succ, scal_mul]
    ring

/-! ### The corner on the staircase with a doubled bottom variable -/

end Field

section Corner

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

/-- **`Δ^{(k+2)}(y_1·y_1⋯y_{k+2}) = -q^k(y_1y_2)(y_1⋯y_{k+2})`**, for `q ∉ {0, 1}`.

`HJO.Sweep.corner` hands the train `y_{k+2}·y_1·(y_1⋯y_{k+2})`; the staircase is symmetric and
rides outside (`HJO.Sweep.cmAscWord_mul_of_swapAux_eq`), leaving
`HJO.Sweep.cmAscWord_one_auxVar_one_mul_auxVar_last` on `y_1y_{k+2}`.

The exponent is `q^k` and not `q^{k+1}`: the doubled bottom variable costs the cascade its last
step, which is the one respect in which this differs from `HJO.Sweep.corner_auxVarProd`. Both
exclusions are `HJO.Sweep.corner`'s own — `q ≠ 1` for its `(q-1)^{-1}`, `q ≠ 0` for the inverted
letters of the train identity it is proved through. -/
theorem corner_auxVar_one_mul_auxVarProd (hq0 : q ≠ 0) (hq1 : q ≠ 1) (k : ℕ) :
    corner q (k + 2) ((auxVar 1 : Total L) * auxVarProd L (k + 2))
      = -(scal (q ^ k) * (auxVarProd L (k + 2) * ((auxVar 1 : Total L) * auxVar 2))) := by
  have hmem : (auxVar 1 : Total L) * auxVarProd L (k + 2) ∈ piece L (k + 1 + 1) :=
    mul_mem (auxVar_mem_piece (by omega) (by omega)) (auxVarProd_mem_piece L (k + 2))
  have hsym : ∀ j, 1 ≤ j → j ≤ k + 1 →
      swapAux L j (auxVarProd L (k + 2)) = auxVarProd L (k + 2) :=
    fun _ _ hj2 => swapAux_auxVarProd (by omega)
  rw [show k + 2 = (k + 1) + 1 from rfl, corner_eq_neg_cmAscWord_auxVar_mul hq0 hq1 (k + 1) hmem,
    show (auxVar ((k + 1) + 1) : Total L) * ((auxVar 1 : Total L) * auxVarProd L (k + 2))
      = auxVarProd L (k + 2) * ((auxVar 1 : Total L) * auxVar (k + 2)) from by
      rw [show (k + 1) + 1 = k + 2 from rfl]; ring,
    cmAscWord_mul_of_swapAux_eq q (by omega) hsym,
    cmAscWord_one_auxVar_one_mul_auxVar_last q k]
  ring

end Corner

end HJO.Sweep

end
