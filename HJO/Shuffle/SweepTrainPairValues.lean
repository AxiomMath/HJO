/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepTrainMonomialWidthTwo

/-! # The braid letter on an adjacent pair, and the trains of widths `1` and `2`

`HJO/Shuffle/SweepBraidMonomial.lean` gives `T_i(y_i^by_{i+1}^{b+c})` and its mirror as a
geometric sum. This file reads off the individual exponent pairs the sweep words of the `4 × 6`
rectangle actually present, and assembles the trains `T_{1↗2} = T_1` and `T_{1↗3} = T_1T_2` on the
monomials those words hand them.

## Why the pairs and not a closed form

`T_i` moves only `y_i` and `y_{i+1}`, so the whole content of a monomial for one letter is the pair
of exponents there; `HJO.Sweep.braid_mul_of_swapAux_eq` lets the other variables ride outside. The
train on a monomial in `y_1, …, y_n` is therefore `n-1` readings of the pair table, and the table
entries are what `HJO.Sweep.braid_eq_of` checks in one `ring` call apiece. Two entries are new —
`(1,3)` and `(3,1)`, where the exponents differ by two and the divided difference is a two-term sum
— and the rest are the adjacent cases computed earlier.

## The two symmetric shapes

`(b,b)` is fixed by the letter (`HJO.Sweep.braid_auxVar_pow_mul_auxVar_pow_self`) and `(b,b+1)`
emits a bare `q`; those two are where every power of `q` in a train value comes from, and a value
with a `q-1` in it has passed through one of the unbalanced pairs.

## Genericity

Every statement here is a polynomial identity in `q`, with no inverse and no hypothesis: they hold
at `q = 0` and at `q = 1`. `u` does not occur.

## References

Built on `HJO.Sweep.braid`, `HJO.Sweep.dividedDiffₗ` and `HJO.Sweep.cmAscWord`. -/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

section Field

variable {L : Type*} [Field L] {q : L}

/-! ### The balanced pair -/

/-- **`T_i(y_i^by_{i+1}^b) = y_i^by_{i+1}^b`**: the balanced pair is `s_i`-symmetric, so the letter
is the identity on it — the trap of this layer, `T_i` being the identity and not multiplication by
`q` on what it fixes. -/
theorem braid_auxVar_pow_mul_auxVar_pow_self (q : L) {i : ℕ} (hi : 1 ≤ i) (b : ℕ) :
    braid q i ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b)
      = (auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b := by
  refine braid_eq_of_swap q ?_
  rw [map_mul, map_pow, map_pow, swapAux_auxVar_self hi, swapAux_auxVar_succ hi]
  ring

/-! ### The two pairs whose exponents differ by two -/

/-- **`T_i(y_iy_{i+1}^3) = (q-1)y_i^2y_{i+1}^2 + qy_i^3y_{i+1}`.**

The divided difference is `y_iy_{i+1}(y_i + y_{i+1})`, a two-term sum rather than the single
monomial the adjacent pairs give, which is why this value has *two* monomials with a `q-1` between
them. Unconditional in `q`. -/
theorem braid_auxVar_mul_auxVar_pow_three (q : L) {i : ℕ} (hi : 1 ≤ i) :
    braid q i ((auxVar i : Total L) * (auxVar (i + 1) : Total L) ^ 3)
      = scal (q - 1) * ((auxVar i : Total L) ^ 2 * (auxVar (i + 1) : Total L) ^ 2)
        + scal q * ((auxVar i : Total L) ^ 3 * (auxVar (i + 1) : Total L)) := by
  have hs : swapAux L i ((auxVar i : Total L) * (auxVar (i + 1) : Total L) ^ 3)
      = (auxVar i : Total L) ^ 3 * (auxVar (i + 1) : Total L) := by
    rw [map_mul, map_pow, swapAux_auxVar_self hi, swapAux_auxVar_succ hi]
    ring
  rw [braid_eq_of q hi hs
    (G := (auxVar i : Total L) * (auxVar (i + 1) : Total L)
      * ((auxVar i : Total L) + (auxVar (i + 1) : Total L))) (by ring)]
  simp only [scal_eq_algebraMap, map_sub, map_one]
  ring

/-- **`T_i(y_i^3y_{i+1}) = y_iy_{i+1}^3 - (q-1)(y_i^2y_{i+1}^2 + y_i^3y_{i+1})`**, the mirror of
`HJO.Sweep.braid_auxVar_mul_auxVar_pow_three`: the same two-term divided difference with the
opposite sign. -/
theorem braid_auxVar_pow_three_mul_auxVar (q : L) {i : ℕ} (hi : 1 ≤ i) :
    braid q i ((auxVar i : Total L) ^ 3 * (auxVar (i + 1) : Total L))
      = (auxVar i : Total L) * (auxVar (i + 1) : Total L) ^ 3
        - scal (q - 1) * ((auxVar i : Total L) ^ 2 * (auxVar (i + 1) : Total L) ^ 2)
        - scal (q - 1) * ((auxVar i : Total L) ^ 3 * (auxVar (i + 1) : Total L)) := by
  have hs : swapAux L i ((auxVar i : Total L) ^ 3 * (auxVar (i + 1) : Total L))
      = (auxVar i : Total L) * (auxVar (i + 1) : Total L) ^ 3 := by
    rw [map_mul, map_pow, swapAux_auxVar_self hi, swapAux_auxVar_succ hi]
    ring
  rw [braid_eq_of q hi hs
    (G := -((auxVar i : Total L) * (auxVar (i + 1) : Total L)
      * ((auxVar i : Total L) + (auxVar (i + 1) : Total L)))) (by ring)]
  ring

/-! ### The two trains the `4 × 6` words read -/

/-- `T_{1↗2} = T_1`: the width-`1` train is its single letter. -/
theorem cmAscWord_one_one_apply (q : L) (F : Total L) :
    cmAscWord q 1 1 F = braid q 1 F := by
  have h0 : cmAscWord q 1 0 = (1 : Module.End L (Total L)) := cmAscWord_self_pred q 0
  rw [show (1 : ℕ) = 0 + 1 from rfl, cmAscWord_one_succ_apply, h0, Module.End.one_apply]

/-- `T_{1↗3} = T_1T_2`: the width-`2` train, letters applied right to left. -/
theorem cmAscWord_one_two_apply (q : L) (F : Total L) :
    cmAscWord q 1 2 F = braid q 1 (braid q 2 F) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, cmAscWord_one_succ_apply, cmAscWord_one_one_apply]

/-! ### The variables a letter does not move -/

/-- `s_1` fixes `y_3`. -/
theorem swapAux_one_auxVar_three : swapAux L 1 (auxVar 3 : Total L) = auxVar 3 :=
  swapAux_auxVar_of_ne (by omega) (by omega) (by omega)

/-- `s_2` fixes `y_1`. -/
theorem swapAux_two_auxVar_one : swapAux L 2 (auxVar 1 : Total L) = auxVar 1 :=
  swapAux_auxVar_of_ne (by omega) (by omega) (by omega)

/-- `s_1` fixes `y_3^c`. -/
theorem swapAux_one_auxVar_three_pow (c : ℕ) :
    swapAux L 1 ((auxVar 3 : Total L) ^ c) = (auxVar 3 : Total L) ^ c := by
  rw [map_pow, swapAux_one_auxVar_three]

/-- `s_2` fixes `y_1^a`. -/
theorem swapAux_two_auxVar_one_pow (a : ℕ) :
    swapAux L 2 ((auxVar 1 : Total L) ^ a) = (auxVar 1 : Total L) ^ a := by
  rw [map_pow, swapAux_two_auxVar_one]

/-! ### `T_1T_2` factorised into its two letters on a monomial

Each of the two letters meets a monomial in the pair it moves, times a power of the variable it does
not, which `HJO.Sweep.braid_mul_of_swapAux_eq` carries outside. -/

/-- **`T_2(y_1^ay_2^by_3^c) = y_1^aT_2(y_2^by_3^c)`**: the bottom variable rides outside the second
letter. -/
theorem braid_two_auxVar_one_pow_mul (q : L) (a : ℕ) (G : Total L) :
    braid q 2 ((auxVar 1 : Total L) ^ a * G) = (auxVar 1 : Total L) ^ a * braid q 2 G :=
  braid_mul_of_swapAux_eq q (swapAux_two_auxVar_one_pow a) G

/-- **`T_1(y_1^ay_2^by_3^c) = y_3^cT_1(y_1^ay_2^b)`**: the top variable rides outside the first
letter. -/
theorem braid_one_auxVar_three_pow_mul (q : L) (c : ℕ) (G : Total L) :
    braid q 1 ((auxVar 3 : Total L) ^ c * G) = (auxVar 3 : Total L) ^ c * braid q 1 G :=
  braid_mul_of_swapAux_eq q (swapAux_one_auxVar_three_pow c) G

end Field

end HJO.Sweep

end
