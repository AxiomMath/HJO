/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitPhiIntertwine
public import Mathlib.Algebra.Ring.GeomSum

/-! # The braid letter on a monomial pair, at every index and every pair of exponents

Every operator of the sweep is, after `HJO.Sweep.dplus_apply` and
`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul`, a *braid word* applied to a monomial. The lowering
operator is already general (`HJO.Sweep.dminus_auxVar_pow_mul`) and so is the corner's reduction
to a word, so what stops a sweep word from being evaluated at width `3` or `4` is not any of the
three operators: it is that the braid letter `T_i` had only been computed on individual monomials,
one `theorem` per monomial, at `i ∈ {1, 2}` and exponents at most `2`.

This file replaces that list by the closed form. `T_i` moves only `y_i` and `y_{i+1}`, so on a
monomial it is determined by the pair of exponents there; writing the larger exponent as `b + c` and
the smaller as `b`, the divided difference is a single geometric sum:

`∂_i(y_i^{b+c} y_{i+1}^b) = -y_i^b y_{i+1}^b ∑_{j<c} y_i^j y_{i+1}^{c-1-j}`

(`HJO.Sweep.dividedDiff_auxVar_pow_mul_auxVar_pow`), and `HJO.Sweep.braid` then gives `T_i` on both
orderings of the pair. Everything is stated at a general index `i ≥ 1` and general exponents, so
widths `3` and `4` are instances rather than new work.

## The two boundary cases, which are the ones the sweep actually meets

* `c = 0`, the **symmetric** pair. Then the sum is empty, `∂_i` vanishes and **`T_i` is the
  identity** — `HJO.Sweep.braid_eq_self_of_swapAux_eq`, stated for any `s_i`-invariant argument.
  This is the trap of the descending train: on a vector symmetric in `y_i, y_{i+1}` the letter `T_i`
  acts as `1`, *not* as multiplication by `q`, and a hand computation that assumes the latter gets
  the wrong answer. With `HJO.Sweep.braid` read as `s_i + (q-1)y_i∂_i` it is immediate.
* `c = 1`, the **adjacent** pair, which is the step the ascending train takes. There the geometric
  sum is `1` and the two orderings are
  `T_i(y_i^b y_{i+1}^{b+1}) = q y_i^{b+1} y_{i+1}^b`
  (`HJO.Sweep.braid_auxVar_pow_mul_auxVar_pow_succ`) and
  `T_i(y_i^{b+1} y_{i+1}^b) = y_i^b y_{i+1}^{b+1} - (q-1) y_i^{b+1} y_{i+1}^b`
  (`HJO.Sweep.braid_auxVar_pow_succ_mul_auxVar_pow`). The first is the letter that produces the
  powers of `q` in every closed form of `HJO/Shuffle/SweepTrainWidth.lean`; at `b = 1` it is
  `HJO.Sweep.braid_one_X_zero_mul_X_one_sq`.

## Genericity

Nothing before `HJO.Sweep.braidInv_eq_self_of_swapAux_eq` reads a hypothesis on `q`: the divided
difference is a quotient by `y_{i+1} - y_i`, which is a non-zero-divisor in the polynomial ring for
`i ≥ 1` (`HJO.Sweep.auxVar_sub_ne_zero`), and `T_i` is a polynomial in `q`. The two statements about
`T_i^{-1}` spend `q ≠ 0`, and spend it irreducibly: `HJO.Sweep.braid`'s inverse is
`(T_i + (q-1))/q`, which at `q = 0` is the zero map in a field, so those statements are *false* at
`q = 0` rather than unproved. No statement here mentions `u`, and none mentions `q = 1`: the braid
letter is defined for every `q`.

The index hypothesis `1 ≤ i` is the range condition of the definitions of `s_i` and `∂_i`. At the
unread index `0` the convention `y_0 = y_1` of `HJO.Sweep.auxVar` makes `s_0` the identity and `∂_0`
the zero map, so `T_0 = 1`; that is why `HJO.Sweep.braid_eq_self_of_swapAux_eq` needs no hypothesis
on `i` at all.

## References

Declarations involved: `HJO.Sweep.swapAux`, `HJO.Sweep.dividedDiffₗ`, `HJO.Sweep.braid`,
`HJO.Sweep.dividedDiff_mem_piece`, `HJO.Sweep.braid_braidInv`. Transcribing A. Mellit, *Toric braids
and `(m,n)`-parking functions*, §3.2.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

section Field

variable {L : Type*} [Field L] {q : L}

/-! ### The symmetric case: `∂_i` kills it and `T_i` fixes it -/

/-- **`∂_i F = 0` whenever `s_iF = F`.** `HJO.Sweep.dividedDiffₗ` is the quotient of `F - s_iF` by
`y_{i+1} - y_i`, and that numerator vanishes. -/
theorem dividedDiff_eq_zero_of_swapAux_eq {i : ℕ} {F : Total L} (h : swapAux L i F = F) :
    dividedDiff i F = 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact dividedDiff_zero_index F
  · exact (dividedDiff_unique hi (by rw [mul_zero, h, sub_self])).symm

/-- **`T_i` is the identity on anything symmetric in `y_i` and `y_{i+1}`.**

This is the one place where a hand computation of a sweep word goes wrong: on an `s_i`-invariant
vector the letter `T_i` acts as `1`, not as multiplication by `q`. With `HJO.Sweep.braid` read as
`T_i = s_i + (q-1)y_i∂_i` both summands are visible — the first returns `F`, the second vanishes by
`HJO.Sweep.dividedDiff_eq_zero_of_swapAux_eq`.

Unconditional in `q` and in `i`: at the unread index `0` the hypothesis holds for every `F` by
`HJO.Sweep.swapAux_zero`, and the conclusion is `T_0 = 1`. -/
theorem braid_eq_self_of_swapAux_eq (q : L) {i : ℕ} {F : Total L} (h : swapAux L i F = F) :
    braid q i F = F := by
  rw [braid_apply, h, dividedDiff_eq_zero_of_swapAux_eq h, mul_zero, add_zero]

/-- **`T_i^{-1}` is the identity on anything symmetric in `y_i` and `y_{i+1}`**, for `q ≠ 0`.
`HJO.Sweep.braid`'s inverse is `(T_i + (q-1))/q`, which on such a vector is `(1 + q - 1)/q`.

`q ≠ 0` is irreducible: at `q = 0` a field's `0⁻¹ = 0` makes `HJO.Sweep.braidInv 0 i` the zero map,
so the statement is false there and not merely unproved. -/
theorem braidInv_eq_self_of_swapAux_eq (hq : q ≠ 0) {i : ℕ} {F : Total L}
    (h : swapAux L i F = F) : braidInv q i F = F := by
  have hq' : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq, scal_one]
  have hqs : (scal q : Total L) = 1 + scal (q - 1) := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  rw [braidInv_apply, braid_eq_self_of_swapAux_eq q h]
  linear_combination F * hq' - (scal q⁻¹ * F : Total L) * hqs

/-! ### The divided difference on a monomial pair -/

/-- **`∂_i(y_i^{b+c} y_{i+1}^b) = -y_i^b y_{i+1}^b ∑_{j<c} y_i^j y_{i+1}^{c-1-j}`**, at every index
`i ≥ 1` and all exponents.

This is the closed form of `HJO.Sweep.dividedDiffₗ` on a monomial: `T_i` and `∂_i` move only `y_i`
and `y_{i+1}`, so a monomial's whole content for them is the pair of exponents there, and writing
the larger as `b + c` makes the quotient the geometric sum `Mathlib`'s `geom_sum₂_mul` names. At
`c = 0` the sum is empty and `∂_i` vanishes, which is `HJO.Sweep.dividedDiff_eq_zero_of_swapAux_eq`
for this argument. -/
theorem dividedDiff_auxVar_pow_mul_auxVar_pow {i : ℕ} (hi : 1 ≤ i) (b c : ℕ) :
    dividedDiff i ((auxVar i : Total L) ^ (b + c) * (auxVar (i + 1) : Total L) ^ b)
      = -((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b *
          ∑ j ∈ Finset.range c,
            (auxVar i : Total L) ^ j * (auxVar (i + 1) : Total L) ^ (c - 1 - j)) := by
  have hx : (MvPolynomial.X (i - 1) : Total L) = auxVar i := rfl
  have hy : (MvPolynomial.X i : Total L) = auxVar (i + 1) := by
    rw [auxVar, Nat.add_sub_cancel]
  have hgeom := geom_sum₂_mul (auxVar i : Total L) (auxVar (i + 1)) c
  refine (dividedDiff_unique hi ?_).symm
  rw [map_mul, map_pow, map_pow, swapAux_auxVar_self hi, swapAux_auxVar_succ hi, hx, hy]
  linear_combination ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b) * hgeom

/-- **`∂_i(y_i^b y_{i+1}^{b+c}) = y_i^b y_{i+1}^b ∑_{j<c} y_i^j y_{i+1}^{c-1-j}`**, the other
ordering of the pair: `HJO.Sweep.dividedDiff_auxVar_pow_mul_auxVar_pow` and the antisymmetry
`HJO.Sweep.dividedDiff_swapAux`. -/
theorem dividedDiff_auxVar_pow_mul_auxVar_pow' {i : ℕ} (hi : 1 ≤ i) (b c : ℕ) :
    dividedDiff i ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + c))
      = (auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b *
          ∑ j ∈ Finset.range c,
            (auxVar i : Total L) ^ j * (auxVar (i + 1) : Total L) ^ (c - 1 - j) := by
  have hsw : swapAux L i ((auxVar i : Total L) ^ (b + c) * (auxVar (i + 1) : Total L) ^ b)
      = (auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + c) := by
    rw [map_mul, map_pow, map_pow, swapAux_auxVar_self hi, swapAux_auxVar_succ hi]
    ring
  rw [← hsw, dividedDiff_swapAux, dividedDiff_auxVar_pow_mul_auxVar_pow hi, neg_neg]

/-! ### The braid letter on a monomial pair -/

/-- **`T_i(y_i^{b+c} y_{i+1}^b)`**, the descending ordering: `HJO.Sweep.braid` evaluated with
`HJO.Sweep.dividedDiff_auxVar_pow_mul_auxVar_pow`. -/
theorem braid_auxVar_pow_mul_auxVar_pow (q : L) {i : ℕ} (hi : 1 ≤ i) (b c : ℕ) :
    braid q i ((auxVar i : Total L) ^ (b + c) * (auxVar (i + 1) : Total L) ^ b)
      = (auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + c)
        - scal (q - 1) * ((auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b *
            ∑ j ∈ Finset.range c,
              (auxVar i : Total L) ^ j * (auxVar (i + 1) : Total L) ^ (c - 1 - j)) := by
  rw [braid_apply, dividedDiff_auxVar_pow_mul_auxVar_pow hi, map_mul, map_pow, map_pow,
    swapAux_auxVar_self hi, swapAux_auxVar_succ hi]
  ring

/-- **`T_i(y_i^b y_{i+1}^{b+c})`**, the ascending ordering: `HJO.Sweep.braid` evaluated with
`HJO.Sweep.dividedDiff_auxVar_pow_mul_auxVar_pow'`. -/
theorem braid_auxVar_pow_mul_auxVar_pow' (q : L) {i : ℕ} (hi : 1 ≤ i) (b c : ℕ) :
    braid q i ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + c))
      = (auxVar i : Total L) ^ (b + c) * (auxVar (i + 1) : Total L) ^ b
        + scal (q - 1) * ((auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b *
            ∑ j ∈ Finset.range c,
              (auxVar i : Total L) ^ j * (auxVar (i + 1) : Total L) ^ (c - 1 - j)) := by
  rw [braid_apply, dividedDiff_auxVar_pow_mul_auxVar_pow' hi, map_mul, map_pow, map_pow,
    swapAux_auxVar_self hi, swapAux_auxVar_succ hi]
  ring

/-! ### The adjacent pair, which is the step the trains take -/

/-- **`T_i(y_i^b y_{i+1}^{b+1}) = q y_i^{b+1} y_{i+1}^b`**, at every index `i ≥ 1` and every `b`.

This single letter is what produces every power of `q` in the closed forms of
`HJO/Shuffle/SweepTrainWidth.lean`: the ascending train meets exactly this shape at each of its
`k` letters. At `b = 1` and `i = 1` it is
`HJO.Sweep.braid_one_X_zero_mul_X_one_sq`. Unconditional in `q`. -/
theorem braid_auxVar_pow_mul_auxVar_pow_succ (q : L) {i : ℕ} (hi : 1 ≤ i) (b : ℕ) :
    braid q i ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + 1))
      = scal q * ((auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b) := by
  have hqs : (scal q : Total L) = 1 + scal (q - 1) := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  rw [braid_auxVar_pow_mul_auxVar_pow' q hi b 1, hqs]
  simp only [Finset.sum_range_one, show (1 : ℕ) - 1 - 0 = 0 from rfl, pow_zero, mul_one]
  ring

/-- **`T_i(y_i^{b+1} y_{i+1}^b) = y_i^b y_{i+1}^{b+1} - (q-1) y_i^{b+1} y_{i+1}^b`**, the reverse
adjacent pair. -/
theorem braid_auxVar_pow_succ_mul_auxVar_pow (q : L) {i : ℕ} (hi : 1 ≤ i) (b : ℕ) :
    braid q i ((auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b)
      = (auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + 1)
        - scal (q - 1) * ((auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b) := by
  rw [braid_auxVar_pow_mul_auxVar_pow q hi b 1]
  simp only [Finset.sum_range_one, show (1 : ℕ) - 1 - 0 = 0 from rfl, pow_zero, mul_one]

/-- **`T_i^{-1}(y_i^{b+1} y_{i+1}^b) = q^{-1} y_i^b y_{i+1}^{b+1}`**, for `q ≠ 0`: the inverse of
`HJO.Sweep.braid_auxVar_pow_mul_auxVar_pow_succ`, and the step the *descending* train of
`HJO.Sweep.corner_eq_neg_auxVar_mul_trainDownEnd` takes.

`q ≠ 0` is spent twice over and irreducibly — once for `T_i^{-1}` to exist at all, once for the
`q^{-1}` on the right to be the inverse of the `q` the forward letter produced. -/
theorem braidInv_auxVar_pow_succ_mul_auxVar_pow (hq : q ≠ 0) {i : ℕ} (hi : 1 ≤ i) (b : ℕ) :
    braidInv q i ((auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b)
      = scal q⁻¹ * ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + 1)) := by
  have hq' : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq, scal_one]
  have hfwd := braid_auxVar_pow_mul_auxVar_pow_succ q hi b
  have hback : braidInv q i (scal q * ((auxVar i : Total L) ^ (b + 1)
        * (auxVar (i + 1) : Total L) ^ b))
      = (auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + 1) := by
    rw [← hfwd, braidInv_braid q hq i]
  rw [braidInv_scal_mul] at hback
  linear_combination (scal q⁻¹ : Total L) * hback
    - braidInv q i ((auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b) * hq'

/-- **`T_i^{-1}(y_i^b y_{i+1}^{b+1}) = y_i^{b+1}y_{i+1}^b + (q-1)q^{-1}y_i^by_{i+1}^{b+1}`**, for
`q ≠ 0`: the *other* ordering of the adjacent pair under the inverted letter, and the one the
descending train meets whenever the exponent it is walking past is the larger of the two.

Unlike `HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow`, this value is **not** a single monomial:
`HJO.Sweep.braid`'s inverse is `(T_i + (q-1))/q`, and on this argument the `T_i` half contributes
the swapped monomial while the `(q-1)` half contributes the argument back. Both letters of the pair
are needed because the descending train of `HJO.Sweep.corner_eq_neg_auxVar_mul_trainDownEnd` meets
both orderings as it walks along a monomial. -/
theorem braidInv_auxVar_pow_mul_auxVar_pow_succ (hq : q ≠ 0) {i : ℕ} (hi : 1 ≤ i) (b : ℕ) :
    braidInv q i ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + 1))
      = (auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b
        + scal ((q - 1) * q⁻¹)
          * ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + 1)) := by
  have hq' : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq, scal_one]
  rw [braidInv_apply, braid_auxVar_pow_mul_auxVar_pow_succ q hi b, scal_mul]
  linear_combination
    ((auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b) * hq'

end Field

end HJO.Sweep

end
