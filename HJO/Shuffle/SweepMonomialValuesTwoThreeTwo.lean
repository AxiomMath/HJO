/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepTrainMonomialWidthTwo
public import HJO.Shuffle.SweepWordValuesTwoThreeTwo
public import HJO.Shuffle.SweepStageWordTwoThreeTwoValue

/-! # The event operators on the monomials the `c_{(2)}` words present

The nineteen sweep words of `HJO/Shuffle/SweepWordsTwoThreeTwoAlpha.lean` meet monomials that
the earlier operator tables do not reach: `HJO.Sweep.corner` at width `2` on `y_1^ay_2^b` with
`a < b + 1`, `HJO.Sweep.dplus` on a power of the bottom variable alone, and `HJO.Sweep.dminus` at a
variable whose exponent exceeds `1`. This file fills those in.

## The three uniform reductions

* **`HJO.Sweep.dminus`**: `HJO.Sweep.dminus_auxVar_pow_mul_auxSubalg_mul_C` is the whole of the
  lowering on the shape these words present — `d_-^{(k+1)}(y_{k+1}^i·Z·f) = Z·B_i(f)` for a
  `y`-monomial `Z` in the first `k` variables and a symmetric coefficient `f`. It is
  `HJO.Sweep.dminus_auxVar_pow_mul` composed with `HJO.Sweep.bopExt_auxSubalg_mul`, and the
  displacement `HJO.Sym.Bop q i` is where every symmetric function in the answers comes from.
* **`HJO.Sweep.corner`**: `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` turns the corner at width
  `m+1` into minus the ascending train on one more copy of the top variable, and each letter of that
  train is discharged by `HJO.Sweep.braid_eq_of` — exhibit the swapped monomial and a candidate
  divided difference, and `ring` does the rest.
* **`HJO.Sweep.dplus`**: `HJO.Sweep.dplus_of_mem_auxSubalg` does the same for the raising on a
  `y`-monomial, and `HJO.Sweep.dplus_apply` with `HJO.Sweep.qshift_C_elemSymm_one` for the two
  places where a raising meets a symmetric coefficient. There the `q`-shift contributes a term the
  `Λ`-linear reading would miss, and it is not a normalisation: it is what gives
  `HJO.Sweep.dplus_one_C_elemSymm_one_mul_auxVar_one_sq` a monomial with no `e_1` on it at all.

## Genericity

The `HJO.Sweep.dplus` and `HJO.Sweep.dminus` statements read no hypothesis on `q`: they are
polynomial identities, holding at `q = 0` and `q = 1` alike. The corner statements carry `q ≠ 0` and
`q ≠ 1`, both of them `HJO.Sweep.corner`'s own — `q ≠ 1` for its `(q-1)^{-1}` and `q ≠ 0` for the
inverted letters of the train identity it is proved through. Nothing here mentions `u`.

## References

The operators evaluated are `HJO.Sweep.corner`, `HJO.Sweep.dplus`, `HJO.Sweep.dminus` and
`HJO.Sweep.braid`, on the words of `HJO.Sweep.cmAscWord`.
-/

@[expose] public section

-- Every value below closes on a polynomial identity in the `y`-monomials and the `e`-monomials, and
-- each is normalised by the *same* rewrite set; which members of it fire depends on the
-- monomial, so some are unused in each individual proof. This is the arrangement of
-- `HJO/Shuffle/SweepStageWordTwoThreeTwoValue.lean`, and its linter exemption too.
set_option linter.unusedSimpArgs false

-- Every exponent written as a numeral in this file is a natural number. Saying so up front lets
-- each `x ^ n` resolve `HPow _ ℕ _` at once instead of retrying instance resolution for the
-- pending numeral type until defaulting, which dominated elaboration here. The elaborated terms
-- are the ones the default instance would produce.
local macro_rules | `($x ^ $n:num) => `(rightact% HPow.hPow $x ($n : ℕ))

namespace HJO.Sweep

open MvPolynomial HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

/-! ### The lowering on a monomial with a symmetric coefficient -/

/-- **`d_-^{(k+1)}(y_{k+1}^i·Z·f) = Z·B_i(f)`**, for `Z` a vector in the first `k` variables lying
in the `y`-subalgebra and `f` a symmetric function.

This is the whole of the lowering as the sweep words of the `4 × 6` rectangle present it: the
exponent `i` of the variable being lowered is read off, everything below it rides outside, and what
is left is the displacement `HJO.Sym.Bop q i` on the coefficient. `HJO.Sweep.dminus_auxVar_pow_mul`
supplies the first step and `HJO.Sweep.bopExt_auxSubalg_mul` the second; the `i = 1`, `f = 1` case
is `HJO.Sweep.dminus_auxVar_succ_mul` and the `i = 1`, `f = e_1` case
`HJO.Sweep.dminus_auxVar_succ_mul_C_elemSymm_one_mul`. No hypothesis on `q`. -/
theorem dminus_auxVar_pow_mul_auxSubalg_mul_C (q : L) (k i : ℕ) (f : Lambda L) {Z : Total L}
    (hZp : Z ∈ piece L k) (hZa : Z ∈ auxSubalg L) :
    dminus q (k + 1) ((auxVar (k + 1) : Total L) ^ i * (Z * C f))
      = Z * C ((Bop q (i : ℤ)) f) := by
  rw [dminus_auxVar_pow_mul q k i (mul_mem hZp (C_mem_piece f k)),
    bopExt_auxSubalg_mul q _ hZa, bopExt_C]

/-! ### The corner at width `1` on a monomial with a symmetric coefficient -/

/-- **`Δ^{(1)}(f·y_1^m) = -f·y_1^{m+1}`.** At width `1` the corner is multiplication by `-y_1`,
whatever symmetric coefficient rides along: `HJO.Sweep.corner_C_mul_auxVarProd_pow` at `m = 0`,
where the power of `q` it emits is `q^0 = 1`. -/
theorem corner_one_C_mul_auxVar_pow (hq0 : q ≠ 0) (hq1 : q ≠ 1) (f : Lambda L) (m : ℕ) :
    corner q 1 (C f * (auxVar 1 : Total L) ^ m) = -(C f * (auxVar 1 : Total L) ^ (m + 1)) := by
  have h := corner_C_mul_auxVarProd_pow (L := L) hq0 hq1 0 m f
  rw [show (0 : ℕ) + 1 = 1 from rfl, auxVarProd_one,
    show (X 0 : Total L) = auxVar 1 from rfl, pow_zero, scal_one, one_mul] at h
  rw [h]
  ring

/-! ### The corner at width `2` on the monomials the words present

The four with `a ≥ b + 1` are already proved (`HJO.Sweep.corner_two_prod`,
`HJO.Sweep.corner_two_auxVar_one_sq_mul_auxVar_two`,
`HJO.Sweep.corner_two_auxVar_one_sq_mul_auxVar_two_sq`,
`HJO.Sweep.corner_two_auxVar_one_cube_mul_auxVar_two_sq`); these are the six it does not have. Each
is `HJO.Sweep.corner_two_eq_neg_braid` followed by one `HJO.Sweep.braid_eq_of`. -/

omit [Algebra ℚ L] in
/-- The swap of a width-`2` monomial: `s_1(y_1^ay_2^b) = y_1^by_2^a`. -/
theorem swapAux_one_monoTwo (a b : ℕ) :
    swapAux L 1 ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b)
      = (auxVar 1 : Total L) ^ b * (auxVar 2 : Total L) ^ a := by
  rw [map_mul, map_pow, map_pow, swapAux_auxVar_self (i := 1) le_rfl,
    swapAux_auxVar_succ (i := 1) le_rfl, show (1 : ℕ) + 1 = 2 from rfl]
  ring

/-- **The corner at width `2`, presented as a check.** To evaluate `Δ^{(2)}F` it suffices to name
`y_2F`, its swap, and a candidate divided difference: `HJO.Sweep.corner_two_eq_neg_braid` turns the
corner into one braid letter and `HJO.Sweep.braid_eq_of` discharges that letter. -/
theorem corner_two_eq_of (hq0 : q ≠ 0) (hq1 : q ≠ 1) {F E H G : Total L} (hF : F ∈ piece L 2)
    (hE : (auxVar 2 : Total L) * F = E) (hs : swapAux L 1 E = H)
    (hd : ((auxVar 2 : Total L) - auxVar 1) * G = E - H) :
    corner q 2 F = -(H + scal (q - 1) * ((auxVar 1 : Total L) * G)) := by
  rw [corner_two_eq_neg_braid hq0 hq1 hF, hE, braid_eq_of q (i := 1) le_rfl hs hd]

/-- **`Δ^{(2)}(y_1y_2^2) = -qy_1^3y_2 - (q-1)y_1^2y_2^2`.** -/
theorem corner_two_auxVar_one_mul_auxVar_two_sq (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2)
      = -(scal q * ((auxVar 1 : Total L) ^ 3 * auxVar 2))
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) := by
  rw [corner_two_eq_of hq0 hq1 (F := (auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2)
      (E := (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3)
      (H := (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1)
      (G := (auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2
        + (auxVar 1 : Total L) ^ 2 * auxVar 2)
      (by simpa using monoTwo_mem_piece 1 2) (by ring) (swapAux_one_monoTwo 1 3) (by ring)]
  simp only [scal_eq_algebraMap, map_sub, map_one]
  ring

/-- **`Δ^{(2)}(y_1y_2^3) = -qy_1^4y_2 - (q-1)(y_1^3y_2^2 + y_1^2y_2^3)`.** -/
theorem corner_two_auxVar_one_mul_auxVar_two_cube (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 3)
      = -(scal q * ((auxVar 1 : Total L) ^ 4 * auxVar 2))
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3) := by
  rw [corner_two_eq_of hq0 hq1 (F := (auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 3)
      (E := (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 4)
      (H := (auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1)
      (G := (auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 3
        + (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
        + (auxVar 1 : Total L) ^ 3 * auxVar 2)
      (by simpa using monoTwo_mem_piece 1 3) (by ring) (swapAux_one_monoTwo 1 4) (by ring)]
  simp only [scal_eq_algebraMap, map_sub, map_one]
  ring

/-- **`Δ^{(2)}(y_1y_2^4) = -qy_1^5y_2 - (q-1)(y_1^4y_2^2 + y_1^3y_2^3 + y_1^2y_2^4)`.** -/
theorem corner_two_auxVar_one_mul_auxVar_two_pow_four (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 4)
      = -(scal q * ((auxVar 1 : Total L) ^ 5 * auxVar 2))
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2)
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3)
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 4) := by
  rw [corner_two_eq_of hq0 hq1 (F := (auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 4)
      (E := (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 5)
      (H := (auxVar 1 : Total L) ^ 5 * (auxVar 2 : Total L) ^ 1)
      (G := (auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 4
        + (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3
        + (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2
        + (auxVar 1 : Total L) ^ 4 * auxVar 2)
      (by simpa using monoTwo_mem_piece 1 4) (by ring) (swapAux_one_monoTwo 1 5) (by ring)]
  simp only [scal_eq_algebraMap, map_sub, map_one]
  ring

/-- **`Δ^{(2)}(y_1^2y_2^3) = -qy_1^4y_2^2 - (q-1)y_1^3y_2^3`.** -/
theorem corner_two_auxVar_one_sq_mul_auxVar_two_cube (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
      = -(scal q * ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2))
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) := by
  rw [corner_two_eq_of hq0 hq1 (F := (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
      (E := (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 4)
      (H := (auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2)
      (G := (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3
        + (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
      (monoTwo_mem_piece 2 3) (by ring) (swapAux_one_monoTwo 2 4) (by ring)]
  simp only [scal_eq_algebraMap, map_sub, map_one]
  ring

/-- **`Δ^{(2)}(y_1^3y_2) = -y_1^2y_2^3 + (q-1)y_1^3y_2^2`.** -/
theorem corner_two_auxVar_one_cube_mul_auxVar_two (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) ^ 3 * auxVar 2)
      = -((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
  rw [corner_two_eq_of hq0 hq1 (F := (auxVar 1 : Total L) ^ 3 * auxVar 2)
      (E := (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
      (H := (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
      (G := -((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
      (by simpa using monoTwo_mem_piece 3 1) (by ring) (swapAux_one_monoTwo 3 2) (by ring)]
  ring

/-- **`Δ^{(2)}(y_1^4y_2) = -y_1^2y_2^4 + (q-1)(y_1^4y_2^2 + y_1^3y_2^3)`.** -/
theorem corner_two_auxVar_one_pow_four_mul_auxVar_two (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) ^ 4 * auxVar 2)
      = -((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 4)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) := by
  rw [corner_two_eq_of hq0 hq1 (F := (auxVar 1 : Total L) ^ 4 * auxVar 2)
      (E := (auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2)
      (H := (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 4)
      (G := -((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        - (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
      (by simpa using monoTwo_mem_piece 4 1) (by ring) (swapAux_one_monoTwo 4 2) (by ring)]
  ring

/-! ### The corner at width `3` on `y_1y_2^2y_3^2` -/

/-- **`Δ^{(3)}(y_1y_2^2y_3^2) = -q^2y_1^3y_2y_3^2 - q(q-1)y_1^2y_2^2y_3^2`.**

The one width-`3` monomial of the nineteen words not already covered by an earlier lemma. The
train's second letter `T_2` meets `y_2^2y_3^3` and collapses it to `qy_2^3y_3^2` — the swapped
monomial and the divided-difference term add there rather than cancel — and the first letter `T_1`
then meets `y_1y_2^3` with `y_3^2` riding outside. -/
theorem corner_three_auxVar_one_mul_auxVar_two_sq_mul_auxVar_three_sq (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 3 ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 2)
      = -(scal (q ^ 2) * ((auxVar 1 : Total L) ^ 3 * auxVar 2 * (auxVar 3 : Total L) ^ 2))
        - scal (q * (q - 1)) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
            * (auxVar 3 : Total L) ^ 2) := by
  have hmem : ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 2)
      ∈ piece L 3 := by simpa using monoThree_mem_piece (L := L) 1 2 2
  have hb1 : braid q 1 ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3)
      = (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1
        + scal (q - 1) * ((auxVar 1 : Total L)
          * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2
            + (auxVar 1 : Total L) ^ 2 * auxVar 2)) :=
    braid_eq_of q (i := 1) le_rfl (swapAux_one_monoTwo 1 3) (by ring)
  have h2 : swapAux L 2 ((auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 3)
      = (auxVar 2 : Total L) ^ 3 * (auxVar 3 : Total L) ^ 2 := by
    rw [map_mul, map_pow, map_pow, swapAux_auxVar_self (i := 2) (by omega),
      swapAux_auxVar_succ (i := 2) (by omega), show (2 : ℕ) + 1 = 3 from rfl]
    ring
  have hb2 : braid q 2 ((auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 3)
      = scal q * ((auxVar 2 : Total L) ^ 3 * (auxVar 3 : Total L) ^ 2) := by
    rw [braid_eq_of q (i := 2) (by omega) h2
      (G := (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 2) (by ring)]
    simp only [scal_eq_algebraMap, map_sub, map_one]
    ring
  have hfix1 : swapAux L 2 (auxVar 1 : Total L) = auxVar 1 :=
    swapAux_auxVar_of_ne (by omega) (by omega) (by omega)
  have hfix3 : swapAux L 1 ((auxVar 3 : Total L) ^ 2) = (auxVar 3 : Total L) ^ 2 := by
    rw [map_pow, swapAux_auxVar_of_ne (i := 1) (m := 3) (by omega) (by omega) (by omega)]
  rw [show (3 : ℕ) = 2 + 1 from rfl,
    corner_eq_neg_cmAscWord_auxVar_mul hq0 hq1 2 hmem, cmAscWord_one_two_apply,
    show (auxVar (2 + 1) : Total L)
        * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 2)
      = (auxVar 1 : Total L) * ((auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 3) from by
      norm_num; ring,
    braid_mul_of_swapAux_eq q hfix1, hb2,
    show (auxVar 1 : Total L) * (scal q * ((auxVar 2 : Total L) ^ 3 * (auxVar 3 : Total L) ^ 2))
      = scal q * ((auxVar 3 : Total L) ^ 2
        * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3)) from by ring,
    braid_scal_mul, braid_mul_of_swapAux_eq q hfix3, hb1]
  simp only [scal_eq_algebraMap, map_sub, map_mul, map_one, map_pow]
  ring

/-! ### The raising on a power of the bottom variable

`HJO.Sweep.dplus_of_mem_auxSubalg` turns each of these into minus the ascending train on one more
variable, and the train is one letter at width `1`, two at width `2`, three at width `3`. -/

omit [Algebra ℚ L] in
/-- **`d_+^{(1)}(y_1^3) = -y_1y_2^3 + (q-1)(y_1^2y_2^2 + y_1^3y_2)`.** -/
theorem dplus_one_auxVar_one_cube (q : L) :
    dplus q 1 ((auxVar 1 : Total L) ^ 3)
      = -((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 3)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 3 * auxVar 2) := by
  rw [dplus_of_mem_auxSubalg q 1 (auxVar_pow_mem_auxSubalg 1 3), cmAscWord_one_one_apply,
    show (auxVar (1 + 1) : Total L) * (auxVar 1 : Total L) ^ 3
      = (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 from by norm_num; ring,
    braid_eq_of q (i := 1) le_rfl (swapAux_one_monoTwo 3 1)
      (G := -((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2)
        - (auxVar 1 : Total L) ^ 2 * auxVar 2) (by ring)]
  ring

omit [Algebra ℚ L] in
/-- **`d_+^{(1)}(y_1^4) = -y_1y_2^4 + (q-1)(y_1^2y_2^3 + y_1^3y_2^2 + y_1^4y_2)`.** -/
theorem dplus_one_auxVar_one_pow_four (q : L) :
    dplus q 1 ((auxVar 1 : Total L) ^ 4)
      = -((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 4)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 4 * auxVar 2) := by
  rw [dplus_of_mem_auxSubalg q 1 (auxVar_pow_mem_auxSubalg 1 4), cmAscWord_one_one_apply,
    show (auxVar (1 + 1) : Total L) * (auxVar 1 : Total L) ^ 4
      = (auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1 from by norm_num; ring,
    braid_eq_of q (i := 1) le_rfl (swapAux_one_monoTwo 4 1)
      (G := -((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 3)
        - (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
        - (auxVar 1 : Total L) ^ 3 * auxVar 2) (by ring)]
  ring

/-! ### The swaps of a width-`4` monomial -/

omit [Algebra ℚ L] in
/-- `s_1(y_1^ay_2^by_3^cy_4^d) = y_1^by_2^ay_3^cy_4^d`. -/
theorem swapAux_one_monoFour (a b c d : ℕ) :
    swapAux L 1 ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * (auxVar 3 : Total L) ^ c
        * (auxVar 4 : Total L) ^ d)
      = (auxVar 1 : Total L) ^ b * (auxVar 2 : Total L) ^ a * (auxVar 3 : Total L) ^ c
        * (auxVar 4 : Total L) ^ d := by
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    swapAux_auxVar_self (i := 1) le_rfl, swapAux_auxVar_succ (i := 1) le_rfl,
    swapAux_auxVar_of_ne (i := 1) (m := 3) (by omega) (by omega) (by omega),
    swapAux_auxVar_of_ne (i := 1) (m := 4) (by omega) (by omega) (by omega),
    show (1 : ℕ) + 1 = 2 from rfl]
  ring

omit [Algebra ℚ L] in
/-- `s_2(y_1^ay_2^by_3^cy_4^d) = y_1^ay_2^cy_3^by_4^d`. -/
theorem swapAux_two_monoFour (a b c d : ℕ) :
    swapAux L 2 ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * (auxVar 3 : Total L) ^ c
        * (auxVar 4 : Total L) ^ d)
      = (auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ c * (auxVar 3 : Total L) ^ b
        * (auxVar 4 : Total L) ^ d := by
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    swapAux_auxVar_self (i := 2) (by omega), swapAux_auxVar_succ (i := 2) (by omega),
    swapAux_auxVar_of_ne (i := 2) (m := 1) (by omega) (by omega) (by omega),
    swapAux_auxVar_of_ne (i := 2) (m := 4) (by omega) (by omega) (by omega),
    show (2 : ℕ) + 1 = 3 from rfl]
  ring

omit [Algebra ℚ L] in
/-- `s_3(y_1^ay_2^by_3^cy_4^d) = y_1^ay_2^by_3^dy_4^c`. -/
theorem swapAux_three_monoFour (a b c d : ℕ) :
    swapAux L 3 ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * (auxVar 3 : Total L) ^ c
        * (auxVar 4 : Total L) ^ d)
      = (auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * (auxVar 3 : Total L) ^ d
        * (auxVar 4 : Total L) ^ c := by
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    swapAux_auxVar_self (i := 3) (by omega), swapAux_auxVar_succ (i := 3) (by omega),
    swapAux_auxVar_of_ne (i := 3) (m := 1) (by omega) (by omega) (by omega),
    swapAux_auxVar_of_ne (i := 3) (m := 2) (by omega) (by omega) (by omega),
    show (3 : ℕ) + 1 = 4 from rfl]
  ring

/-! ### The corner at widths `3` and `4` on the staircase, in `HJO.Sweep.auxVar` form

`HJO.Sweep.corner_three_prod` and `HJO.Sweep.corner_four_prod` are stated in the `MvPolynomial.X`
spelling; the sweep words present the `HJO.Sweep.auxVar` one. -/

/-- **`Δ^{(3)}(y_1y_2y_3) = -q^2y_1^2y_2y_3`.** -/
theorem corner_three_auxVarProd (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 3 ((auxVar 1 : Total L) * auxVar 2 * auxVar 3)
      = -(scal (q ^ 2) * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3)) :=
  corner_three_prod hq0 hq1

/-- **`Δ^{(4)}(y_1y_2y_3y_4) = -q^3y_1^2y_2y_3y_4`.** -/
theorem corner_four_auxVarProd (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 4 ((auxVar 1 : Total L) * auxVar 2 * auxVar 3 * auxVar 4)
      = -(scal (q ^ 3) * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3 * auxVar 4)) :=
  corner_four_prod hq0 hq1

/-! ### The corner is `Λ`-linear on its graded piece

`HJO.Sweep.corner_two_eq_neg_braid` and `HJO.Sweep.corner_three_eq_neg_braid` write the corner as a
braid word, and `HJO.Sweep.braid_C_mul` says each letter is `Λ`-linear. So a symmetric coefficient
passes the corner untouched — which is *not* true of `HJO.Sweep.dplus` or `HJO.Sweep.dminus`,
both of which carry a `q`-shift that acts on the coefficient. -/

/-- **`Δ^{(2)}(f·F) = f·Δ^{(2)}F`** for `F` in the second graded piece. -/
theorem corner_two_C_mul (hq0 : q ≠ 0) (hq1 : q ≠ 1) (f : Lambda L) {F : Total L}
    (hF : F ∈ piece L 2) : corner q 2 (C f * F) = C f * corner q 2 F := by
  rw [corner_two_eq_neg_braid hq0 hq1 (mul_mem (C_mem_piece f 2) hF),
    corner_two_eq_neg_braid hq0 hq1 hF,
    show (auxVar 2 : Total L) * (C f * F) = C f * ((auxVar 2 : Total L) * F) from by ring,
    braid_C_mul]
  ring

/-- **`Δ^{(3)}(f·F) = f·Δ^{(3)}F`** for `F` in the third graded piece. -/
theorem corner_three_C_mul (hq0 : q ≠ 0) (hq1 : q ≠ 1) (f : Lambda L) {F : Total L}
    (hF : F ∈ piece L 3) : corner q 3 (C f * F) = C f * corner q 3 F := by
  rw [corner_three_eq_neg_braid hq0 hq1 (mul_mem (C_mem_piece f 3) hF),
    corner_three_eq_neg_braid hq0 hq1 hF,
    show (auxVar 3 : Total L) * (C f * F) = C f * ((auxVar 3 : Total L) * F) from by ring,
    braid_C_mul, braid_C_mul]
  ring

/-- `Δ^{(2)}(f·y_1y_2^2)`. -/
theorem corner_two_auxVar_one_mul_auxVar_two_sq_C (hq0 : q ≠ 0) (hq1 : q ≠ 1) (f : Lambda L) :
    corner q 2 (C f * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2))
      = C f * (-(scal q * ((auxVar 1 : Total L) ^ 3 * auxVar 2))
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)) := by
  rw [corner_two_C_mul hq0 hq1 f (by simpa using monoTwo_mem_piece 1 2),
    corner_two_auxVar_one_mul_auxVar_two_sq hq0 hq1]

/-- `Δ^{(2)}(f·y_1y_2^3)`. -/
theorem corner_two_auxVar_one_mul_auxVar_two_cube_C (hq0 : q ≠ 0) (hq1 : q ≠ 1) (f : Lambda L) :
    corner q 2 (C f * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 3))
      = C f * (-(scal q * ((auxVar 1 : Total L) ^ 4 * auxVar 2))
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)) := by
  rw [corner_two_C_mul hq0 hq1 f (by simpa using monoTwo_mem_piece 1 3),
    corner_two_auxVar_one_mul_auxVar_two_cube hq0 hq1]

/-- `Δ^{(2)}(f·y_1^2y_2)`. -/
theorem corner_two_auxVar_one_sq_mul_auxVar_two_C (hq0 : q ≠ 0) (hq1 : q ≠ 1) (f : Lambda L) :
    corner q 2 (C f * ((auxVar 1 : Total L) ^ 2 * auxVar 2))
      = C f * -((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) := by
  rw [corner_two_C_mul hq0 hq1 f (by simpa using monoTwo_mem_piece 2 1),
    corner_two_auxVar_one_sq_mul_auxVar_two hq0 hq1]

/-- `Δ^{(2)}(f·y_1^2y_2^2)`. -/
theorem corner_two_auxVar_one_sq_mul_auxVar_two_sq_C (hq0 : q ≠ 0) (hq1 : q ≠ 1) (f : Lambda L) :
    corner q 2 (C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
      = C f * -(scal q * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)) := by
  rw [corner_two_C_mul hq0 hq1 f (monoTwo_mem_piece 2 2),
    corner_two_auxVar_one_sq_mul_auxVar_two_sq hq0 hq1]

/-- `Δ^{(2)}(f·y_1^3y_2)`. -/
theorem corner_two_auxVar_one_cube_mul_auxVar_two_C (hq0 : q ≠ 0) (hq1 : q ≠ 1) (f : Lambda L) :
    corner q 2 (C f * ((auxVar 1 : Total L) ^ 3 * auxVar 2))
      = C f * (-((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)) := by
  rw [corner_two_C_mul hq0 hq1 f (by simpa using monoTwo_mem_piece 3 1),
    corner_two_auxVar_one_cube_mul_auxVar_two hq0 hq1]

/-- `Δ^{(3)}(f·y_1^2y_2y_3)`. -/
theorem corner_three_auxVar_one_sq_mul_auxVar_two_mul_auxVar_three_C (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (f : Lambda L) :
    corner q 3 (C f * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3))
      = C f * -(scal q * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * auxVar 3)) := by
  rw [corner_three_C_mul hq0 hq1 f (by simpa using monoThree_mem_piece 2 1 1),
    corner_three_auxVar_one_sq_mul_auxVar_two_mul_auxVar_three hq0 hq1]

/-! ### The lowering, at the three widths the words read it -/

omit [Algebra ℚ L] in
private theorem auxVar_one_pow_mem_piece_one (a : ℕ) : ((auxVar 1 : Total L)) ^ a ∈ piece L 1 :=
  pow_mem (auxVar_mem_piece (by omega) (by omega)) a

/-- **`d_-^{(2)}(y_1^ay_2^b) = y_1^a·B_b(1)`.** -/
theorem dminus_two_monoTwo (q : L) (a b : ℕ) :
    dminus q 2 ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b)
      = (auxVar 1 : Total L) ^ a * C ((Bop q ((b : ℕ) : ℤ)) (1 : Lambda L)) := by
  have h := dminus_auxVar_pow_mul_auxSubalg_mul_C q 1 b (1 : Lambda L)
    (auxVar_one_pow_mem_piece_one a) (auxVar_pow_mem_auxSubalg 1 a)
  rw [map_one, mul_one, show (1 : ℕ) + 1 = 2 from rfl] at h
  rw [show ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b)
    = (auxVar 2 : Total L) ^ b * (auxVar 1 : Total L) ^ a from by ring, h]

/-- **`d_-^{(2)}(f·y_1^ay_2^b) = y_1^a·B_b(f)`.** -/
theorem dminus_two_monoTwo_C (q : L) (a b : ℕ) (f : Lambda L) :
    dminus q 2 (C f * ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b))
      = (auxVar 1 : Total L) ^ a * C ((Bop q ((b : ℕ) : ℤ)) f) := by
  have h := dminus_auxVar_pow_mul_auxSubalg_mul_C q 1 b f
    (auxVar_one_pow_mem_piece_one a) (auxVar_pow_mem_auxSubalg 1 a)
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  rw [show (C f * ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b))
    = (auxVar 2 : Total L) ^ b * ((auxVar 1 : Total L) ^ a * C f) from by ring, h]

/-- **`d_-^{(3)}(y_1^ay_2^by_3^c) = y_1^ay_2^b·B_c(1)`.** -/
theorem dminus_three_monoThree (q : L) (a b c : ℕ) :
    dminus q 3 ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * (auxVar 3 : Total L) ^ c)
      = (auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b
        * C ((Bop q ((c : ℕ) : ℤ)) (1 : Lambda L)) := by
  have h := dminus_auxVar_pow_mul_auxSubalg_mul_C q 2 c (1 : Lambda L)
    (monoTwo_mem_piece a b) (monoTwo_mem_auxSubalg a b)
  rw [map_one, mul_one, show (2 : ℕ) + 1 = 3 from rfl] at h
  rw [show ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * (auxVar 3 : Total L) ^ c)
    = (auxVar 3 : Total L) ^ c * ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b) from by ring,
    h]

/-- **`d_-^{(3)}(f·y_1^ay_2^by_3^c) = y_1^ay_2^b·B_c(f)`.** -/
theorem dminus_three_monoThree_C (q : L) (a b c : ℕ) (f : Lambda L) :
    dminus q 3 (C f * ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b
        * (auxVar 3 : Total L) ^ c))
      = (auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * C ((Bop q ((c : ℕ) : ℤ)) f) := by
  have h := dminus_auxVar_pow_mul_auxSubalg_mul_C q 2 c f
    (monoTwo_mem_piece a b) (monoTwo_mem_auxSubalg a b)
  rw [show (2 : ℕ) + 1 = 3 from rfl] at h
  rw [show (C f * ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b
        * (auxVar 3 : Total L) ^ c))
    = (auxVar 3 : Total L) ^ c
      * ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * C f) from by ring, h]

/-- **`d_-^{(4)}(y_1^ay_2^by_3^cy_4^d) = y_1^ay_2^by_3^c·B_d(1)`.** -/
theorem dminus_four_monoFour (q : L) (a b c d : ℕ) :
    dminus q 4 ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * (auxVar 3 : Total L) ^ c
        * (auxVar 4 : Total L) ^ d)
      = (auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * (auxVar 3 : Total L) ^ c
        * C ((Bop q ((d : ℕ) : ℤ)) (1 : Lambda L)) := by
  have h := dminus_auxVar_pow_mul_auxSubalg_mul_C q 3 d (1 : Lambda L)
    (monoThree_mem_piece a b c) (monoThree_mem_auxSubalg a b c)
  rw [map_one, mul_one, show (3 : ℕ) + 1 = 4 from rfl] at h
  rw [show ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * (auxVar 3 : Total L) ^ c
        * (auxVar 4 : Total L) ^ d)
    = (auxVar 4 : Total L) ^ d * ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b
      * (auxVar 3 : Total L) ^ c) from by ring, h]

/-- **`d_-^{(4)}(f·y_1^ay_2^by_3^cy_4^d) = y_1^ay_2^by_3^c·B_d(f)`.** -/
theorem dminus_four_monoFour_C (q : L) (a b c d : ℕ) (f : Lambda L) :
    dminus q 4 (C f * ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b
        * (auxVar 3 : Total L) ^ c * (auxVar 4 : Total L) ^ d))
      = (auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * (auxVar 3 : Total L) ^ c
        * C ((Bop q ((d : ℕ) : ℤ)) f) := by
  have h := dminus_auxVar_pow_mul_auxSubalg_mul_C q 3 d f
    (monoThree_mem_piece a b c) (monoThree_mem_auxSubalg a b c)
  rw [show (3 : ℕ) + 1 = 4 from rfl] at h
  rw [show (C f * ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b
        * (auxVar 3 : Total L) ^ c * (auxVar 4 : Total L) ^ d))
    = (auxVar 4 : Total L) ^ d * ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b
      * (auxVar 3 : Total L) ^ c * C f) from by ring, h]

/-! ### The displacement values, at the natural-number index the lowering hands them

The eleven `HJO.Sym.Bop` values the nineteen words read, restated at the index
`((i : ℕ) : ℤ)` that `HJO.Sweep.dminus_two_monoTwo` and its siblings produce. -/

/-- `B_1(1) = -e_1`. -/
theorem bopNat_one_one (q : L) : Bop q ((1 : ℕ) : ℤ) (1 : Lambda L) = -elemSymm L 1 := by
  rw [bop_natCast_one]; norm_num

/-- `B_2(1) = e_2`. -/
theorem bopNat_two_one (q : L) : Bop q ((2 : ℕ) : ℤ) (1 : Lambda L) = elemSymm L 2 :=
  bop_two_one q

/-- `B_3(1) = -e_3`. -/
theorem bopNat_three_one (q : L) : Bop q ((3 : ℕ) : ℤ) (1 : Lambda L) = -elemSymm L 3 := by
  rw [bop_natCast_one]; norm_num

/-- `B_4(1) = e_4`. -/
theorem bopNat_four_one (q : L) : Bop q ((4 : ℕ) : ℤ) (1 : Lambda L) = elemSymm L 4 :=
  bop_four_one q

/-- `B_1(e_1) = -e_1^2 + (1-q)e_2`. -/
theorem bopNat_one_elemSymm_one (q : L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 1)
      = -(elemSymm L 1 * elemSymm L 1) + C (1 - q) * elemSymm L 2 := by
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl, bop_one_elemSymm_one]

/-- `B_2(e_1) = e_1e_2 - (1-q)e_3`. -/
theorem bopNat_two_elemSymm_one (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1)
      = elemSymm L 1 * elemSymm L 2 - C (1 - q) * elemSymm L 3 :=
  bop_two_elemSymm_one q

/-- `B_3(e_1) = -e_1e_3 + (1-q)e_4`. -/
theorem bopNat_three_elemSymm_one (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 1)
      = -(elemSymm L 1 * elemSymm L 3) + (1 - q) • elemSymm L 4 :=
  bop_three_elemSymm_one q

/-- `B_1(e_2) = -qe_1e_2 + q(1-q)e_3`. -/
theorem bopNat_one_elemSymm_two (q : L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 2)
      = -q • (elemSymm L 1 * elemSymm L 2) + (q * (1 - q)) • elemSymm L 3 :=
  bop_one_elemSymm_two q

/-- `B_2(e_2) = e_2^2 - (1-q)e_1e_3 - q(1-q)e_4`. -/
theorem bopNat_two_elemSymm_two (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 2)
      = elemSymm L 2 * elemSymm L 2 - (1 - q) • (elemSymm L 1 * elemSymm L 3)
        - (q * (1 - q)) • elemSymm L 4 :=
  bop_two_elemSymm_two' q

/-- `B_1(e_1^2) = -e_1^3 + 2(1-q)e_1e_2 - (1-q)^2e_3`. -/
theorem bopNat_one_elemSymm_one_sq (q : L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 1 ^ 2)
      = -(elemSymm L 1 * elemSymm L 1 * elemSymm L 1)
        + (2 * (1 - q)) • (elemSymm L 1 * elemSymm L 2) - (1 - q) ^ 2 • elemSymm L 3 := by
  rw [sq]
  exact bop_one_elemSymm_one_sq q

/-- `B_2(e_1^2) = e_1^2e_2 - 2(1-q)e_1e_3 + (1-q)^2e_4`. -/
theorem bopNat_two_elemSymm_one_sq (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 ^ 2)
      = elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)
        - (2 * (1 - q)) • (elemSymm L 1 * elemSymm L 3) + (1 - q) ^ 2 • elemSymm L 4 := by
  rw [sq]
  exact bop_two_elemSymm_one_sq q

/-! ### The raising as a braid word

`HJO.Sweep.dplus_of_mem_auxSubalg` on a `y`-monomial, with the ascending train spelled out letter by
letter. -/

omit [Algebra ℚ L] in
/-- `s_1(y_1^ay_2^by_3^c) = y_1^by_2^ay_3^c`. -/
theorem swapAux_one_monoThree (a b c : ℕ) :
    swapAux L 1 ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * (auxVar 3 : Total L) ^ c)
      = (auxVar 1 : Total L) ^ b * (auxVar 2 : Total L) ^ a * (auxVar 3 : Total L) ^ c := by
  have h := swapAux_one_monoFour (L := L) a b c 0
  rw [pow_zero, mul_one, mul_one] at h
  exact h

omit [Algebra ℚ L] in
/-- `s_2(y_1^ay_2^by_3^c) = y_1^ay_2^cy_3^b`. -/
theorem swapAux_two_monoThree (a b c : ℕ) :
    swapAux L 2 ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * (auxVar 3 : Total L) ^ c)
      = (auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ c * (auxVar 3 : Total L) ^ b := by
  have h := swapAux_two_monoFour (L := L) a b c 0
  rw [pow_zero, mul_one, mul_one] at h
  exact h

omit [Algebra ℚ L] in
/-- **`d_+^{(3)}F = -T_1T_2T_3(y_4F)`** on the `y`-subalgebra. -/
theorem dplus_three_eq_neg_braid (q : L) {F : Total L} (hF : F ∈ auxSubalg L) :
    dplus q 3 F = -(braid q 1) ((braid q 2) ((braid q 3) ((auxVar 4 : Total L) * F))) := by
  rw [dplus_of_mem_auxSubalg q 3 hF, cmAscWord_one_three_apply]

omit [Algebra ℚ L] in
/-- **`d_+^{(1)}y_1 = -y_1y_2`**, in `HJO.Sweep.auxVar` form. -/
theorem dplus_one_auxVar_one (q : L) :
    dplus q 1 (auxVar 1 : Total L) = -((auxVar 1 : Total L) * auxVar 2) := by
  have h := dplus_auxVarProd (L := L) q 1
  rw [auxVarProd_one, show (1 : ℕ) + 1 = 2 from rfl, auxVarProd_two',
    show (X 0 : Total L) = auxVar 1 from rfl] at h
  exact h

omit [Algebra ℚ L] in
/-- **`d_+^{(2)}(y_1y_2) = -y_1y_2y_3`**, in `HJO.Sweep.auxVar` form. -/
theorem dplus_two_auxVarProd_two (q : L) :
    dplus q 2 ((auxVar 1 : Total L) * auxVar 2) = -((auxVar 1 : Total L) * auxVar 2 * auxVar 3) :=
      by
  have h := dplus_auxVarProd (L := L) q 2
  rwa [show (2 : ℕ) + 1 = 3 from rfl, auxVarProd_two', auxVarProd_three'] at h

omit [Algebra ℚ L] in
/-- **`d_+^{(3)}(y_1y_2y_3) = -y_1y_2y_3y_4`**, in `HJO.Sweep.auxVar` form. -/
theorem dplus_three_auxVarProd_three (q : L) :
    dplus q 3 ((auxVar 1 : Total L) * auxVar 2 * auxVar 3)
      = -((auxVar 1 : Total L) * auxVar 2 * auxVar 3 * auxVar 4) := by
  have h := dplus_auxVarProd (L := L) q 3
  rwa [show (3 : ℕ) + 1 = 4 from rfl, auxVarProd_three', auxVarProd_four'] at h

omit [Algebra ℚ L] in
/-- **`d_+^{(2)}(y_1^2y_2^2) = -y_1y_2^2y_3^2 + (q-1)(y_1^2y_2y_3^2 + y_1^2y_2^2y_3)`.**

The train's second letter moves `y_2^2y_3` and its first meets `y_1^2y_2^2`, which is symmetric and
so survives untouched: the last term is the one the letter `T_1` does not see. -/
theorem dplus_two_auxVar_one_sq_mul_auxVar_two_sq (q : L) :
    dplus q 2 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
      = -((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 2)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * (auxVar 3 : Total L) ^ 2)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * auxVar 3) := by
  have hb2 : braid q 2 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
        * (auxVar 3 : Total L) ^ 1)
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 2
        + scal (q - 1) * ((auxVar 2 : Total L)
          * (-((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3))) :=
    braid_eq_of q (by omega) (swapAux_two_monoThree 2 2 1) (by ring)
  have hb1a : braid q 1 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1
        * (auxVar 3 : Total L) ^ 2)
      = (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 2
        + scal (q - 1) * ((auxVar 1 : Total L)
          * (-((auxVar 1 : Total L) * auxVar 2 * (auxVar 3 : Total L) ^ 2))) :=
    braid_eq_of q le_rfl (swapAux_one_monoThree 2 1 2) (by ring)
  have hb1b : braid q 1 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
        * (auxVar 3 : Total L) ^ 1)
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 1
        + scal (q - 1) * ((auxVar 1 : Total L) * 0) :=
    braid_eq_of q le_rfl (swapAux_one_monoThree 2 2 1) (by ring)
  rw [dplus_two_eq_neg_braid q (monoTwo_mem_auxSubalg 2 2),
    show (auxVar 3 : Total L) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 1 from by
      ring, hb2]
  rw [show ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 2
        + scal (q - 1) * ((auxVar 2 : Total L)
          * (-((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3))))
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 2
        + scal (-(q - 1)) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
          * (auxVar 3 : Total L) ^ 1) from by
      simp only [scal_eq_algebraMap, map_sub, map_neg, map_one]; ring,
    map_add, braid_scal_mul, hb1a, hb1b]
  simp only [scal_eq_algebraMap, map_sub, map_neg, map_one]
  ring

omit [Algebra ℚ L] in
/-- **`d_+^{(2)}(y_1^3y_2) = -y_1y_2^3y_3 + (q-1)(y_1^2y_2^2y_3 + y_1^3y_2y_3)`.**

The second letter meets `y_2y_3`, which is symmetric, so the whole of the answer comes from the
first letter on `y_1^3y_2`. -/
theorem dplus_two_auxVar_one_cube_mul_auxVar_two (q : L) :
    dplus q 2 ((auxVar 1 : Total L) ^ 3 * auxVar 2)
      = -((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 3 * auxVar 3)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * auxVar 3)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 3 * auxVar 2 * auxVar 3) := by
  have hb2 : braid q 2 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1
        * (auxVar 3 : Total L) ^ 1)
      = (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1
        + scal (q - 1) * ((auxVar 2 : Total L) * 0) :=
    braid_eq_of q (by omega) (swapAux_two_monoThree 3 1 1) (by ring)
  have hb1 : braid q 1 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1
        * (auxVar 3 : Total L) ^ 1)
      = (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3 * (auxVar 3 : Total L) ^ 1
        + scal (q - 1) * ((auxVar 1 : Total L)
          * (-((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 * auxVar 3)
            - (auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3)) :=
    braid_eq_of q le_rfl (swapAux_one_monoThree 3 1 1) (by ring)
  rw [dplus_two_eq_neg_braid q (by simpa using monoTwo_mem_auxSubalg 3 1),
    show (auxVar 3 : Total L) * ((auxVar 1 : Total L) ^ 3 * auxVar 2)
      = (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1 from by
      ring, hb2, mul_zero, mul_zero, add_zero, hb1]
  simp only [scal_eq_algebraMap, map_sub, map_one]
  ring

omit [Algebra ℚ L] in
/-- **`d_+^{(3)}(y_1^2y_2y_3) = -y_1y_2^2y_3y_4 + (q-1)y_1^2y_2y_3y_4`.**

Both of the train's upper letters meet a monomial symmetric in the pair they move, so only `T_1`
acts. -/
theorem dplus_three_auxVar_one_sq_mul_auxVar_two_mul_auxVar_three (q : L) :
    dplus q 3 ((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3)
      = -((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 * auxVar 3 * auxVar 4)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3 * auxVar 4) := by
  have hb3 : braid q 3 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1
        * (auxVar 3 : Total L) ^ 1 * (auxVar 4 : Total L) ^ 1)
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1
          * (auxVar 4 : Total L) ^ 1
        + scal (q - 1) * ((auxVar 3 : Total L) * 0) :=
    braid_eq_of q (by omega) (swapAux_three_monoFour 2 1 1 1) (by ring)
  have hb2 : braid q 2 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1
        * (auxVar 3 : Total L) ^ 1 * (auxVar 4 : Total L) ^ 1)
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1
          * (auxVar 4 : Total L) ^ 1
        + scal (q - 1) * ((auxVar 2 : Total L) * 0) :=
    braid_eq_of q (by omega) (swapAux_two_monoFour 2 1 1 1) (by ring)
  have hb1 : braid q 1 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1
        * (auxVar 3 : Total L) ^ 1 * (auxVar 4 : Total L) ^ 1)
      = (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 1
          * (auxVar 4 : Total L) ^ 1
        + scal (q - 1) * ((auxVar 1 : Total L)
          * (-((auxVar 1 : Total L) * auxVar 2 * auxVar 3 * auxVar 4))) :=
    braid_eq_of q le_rfl (swapAux_one_monoFour 2 1 1 1) (by ring)
  rw [dplus_three_eq_neg_braid q (by simpa using monoThree_mem_auxSubalg 2 1 1),
    show (auxVar 4 : Total L) * ((auxVar 1 : Total L) ^ 2 * auxVar 2 * auxVar 3)
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1
        * (auxVar 4 : Total L) ^ 1 from by ring,
    hb3, mul_zero, mul_zero, add_zero, hb2, mul_zero, mul_zero, add_zero, hb1]
  simp only [scal_eq_algebraMap, map_sub, map_one]
  ring

/-! ### The raising against a symmetric coefficient

The two places where a `HJO.Sweep.dplus` of the nineteen words meets a `Λ`-coefficient. Here the
`q`-shift of `HJO.Sweep.qshift` acts: `HJO.Sweep.qshift_C_elemSymm_one` adds `(q-1)y_2` to `e_1`,
and the extra monomial that letter produces carries **no** `e_1` at all. A `Λ`-linear reading of
`d_+` would miss it, and it does not cancel. -/

/-- `d_+^{(1)}(e_1y_1^m)` before either braid letter is read: the `q`-shift, written out. -/
theorem dplus_one_C_elemSymm_one_mul_auxVar_pow (q : L) (m : ℕ) :
    dplus q 1 (C (elemSymm L 1) * (auxVar 1 : Total L) ^ m)
      = -(braid q 1) ((auxVar 2 : Total L)
          * ((C (elemSymm L 1) + scal (q - 1) * auxVar 2) * (auxVar 1 : Total L) ^ m)) := by
  have hq : qshift q 2 (C (elemSymm L 1) * (auxVar 1 : Total L) ^ m)
      = (C (elemSymm L 1) + scal (q - 1) * auxVar 2) * (auxVar 1 : Total L) ^ m := by
    rw [map_mul, qshift_C_elemSymm_one,
      qshift_of_mem_auxSubalg q 2 (auxVar_pow_mem_auxSubalg 1 m)]
  rw [dplus_apply, show (1 : ℕ) + 1 = 2 from rfl, hq, trainUpEnd_one_two, braidEnd,
    LinearMap.restrictScalars_apply]

/-- **`d_+^{(1)}(e_1y_1^2) = -e_1y_1y_2^2 + (q-1)e_1y_1^2y_2 - (q-1)y_1^2y_2^2`.** -/
theorem dplus_one_C_elemSymm_one_mul_auxVar_one_sq (q : L) :
    dplus q 1 (C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2)
      = -(C (elemSymm L 1) * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2))
        + scal (q - 1) * (C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * auxVar 2))
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) := by
  have hb : braid q 1 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1)
      = (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2
        + scal (q - 1) * ((auxVar 1 : Total L) * (-((auxVar 1 : Total L) * auxVar 2))) :=
    braid_eq_of q le_rfl (swapAux_one_monoTwo 2 1) (by ring)
  have hsym : braid q 1 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 :=
    braid_auxVar_pow_mul_auxVar_pow_self q le_rfl 2
  rw [dplus_one_C_elemSymm_one_mul_auxVar_pow q 2,
    show (auxVar 2 : Total L) * ((C (elemSymm L 1) + scal (q - 1) * auxVar 2)
        * (auxVar 1 : Total L) ^ 2)
      = C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) from by ring,
    map_add, braid_C_mul, braid_scal_mul, hb, hsym]
  simp only [scal_eq_algebraMap, map_sub, map_one]
  ring

/-- **`d_+^{(1)}(e_1y_1^3) = -e_1y_1y_2^3 + (q-1)e_1(y_1^2y_2^2 + y_1^3y_2) - (q-1)y_1^2y_2^3
+ (q-1)^2y_1^3y_2^2`.** -/
theorem dplus_one_C_elemSymm_one_mul_auxVar_one_cube (q : L) :
    dplus q 1 (C (elemSymm L 1) * (auxVar 1 : Total L) ^ 3)
      = -(C (elemSymm L 1) * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 3))
        + scal (q - 1) * (C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2
          * (auxVar 2 : Total L) ^ 2))
        + scal (q - 1) * (C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * auxVar 2))
        - scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + scal ((q - 1) ^ 2) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
  have hb : braid q 1 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1)
      = (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3
        + scal (q - 1) * ((auxVar 1 : Total L)
          * (-((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2)
            - (auxVar 1 : Total L) ^ 2 * auxVar 2)) :=
    braid_eq_of q le_rfl (swapAux_one_monoTwo 3 1) (by ring)
  have hb2 : braid q 1 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3
        + scal (q - 1) * ((auxVar 1 : Total L)
          * (-((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))) :=
    braid_eq_of q le_rfl (swapAux_one_monoTwo 3 2) (by ring)
  rw [dplus_one_C_elemSymm_one_mul_auxVar_pow q 3,
    show (auxVar 2 : Total L) * ((C (elemSymm L 1) + scal (q - 1) * auxVar 2)
        * (auxVar 1 : Total L) ^ 3)
      = C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1)
        + scal (q - 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) from by ring,
    map_add, braid_C_mul, braid_scal_mul, hb, hb2]
  simp only [scal_eq_algebraMap, map_sub, map_add, map_mul, map_one, map_pow, map_ofNat]
  ring

/-! ### The tables, with every exponent written out

The nineteen words are evaluated by rewriting, and rewriting is syntactic: a value whose monomials
carry `y_2^1` does not meet a lemma stated at `y_2`. So each operator value the words read is
restated here in the one uniform shape the evaluation produces, every exponent explicit. The content
is the lemma above it; only the spelling differs. -/

/-- `Δ^{(2)}(y_1^1y_2^1)`, with every exponent written out. -/
theorem corner_two_monoTwo_one_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1)
      = (-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1
      = (auxVar 1 : Total L) * (auxVar 2 : Total L) from by ring, corner_two_prod hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(y_1^1y_2^2)`, with every exponent written out. -/
theorem corner_two_monoTwo_one_two (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2)
      = (1 - q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
        + (-q : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2
      = (auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 from by ring,
        corner_two_auxVar_one_mul_auxVar_two_sq hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(y_1^1y_2^3)`, with every exponent written out. -/
theorem corner_two_monoTwo_one_three (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3)
      = (1 - q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + (1 - q : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        + (-q : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3
      = (auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 3 from by ring,
        corner_two_auxVar_one_mul_auxVar_two_cube hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(y_1^1y_2^4)`, with every exponent written out. -/
theorem corner_two_monoTwo_one_four (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 4)
      = (1 - q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 4)
        + (1 - q : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3)
        + (1 - q : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2)
        + (-q : L) • ((auxVar 1 : Total L) ^ 5 * (auxVar 2 : Total L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 4
      = (auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 4 from by ring,
        corner_two_auxVar_one_mul_auxVar_two_pow_four hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(y_1^2y_2^1)`, with every exponent written out. -/
theorem corner_two_monoTwo_two_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) := by
  rw [show (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) from by ring,
        corner_two_auxVar_one_sq_mul_auxVar_two hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(y_1^2y_2^2)`, with every exponent written out. -/
theorem corner_two_monoTwo_two_two (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
      = (-q : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
  rw [show (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 from by ring,
        corner_two_auxVar_one_sq_mul_auxVar_two_sq hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(y_1^2y_2^3)`, with every exponent written out. -/
theorem corner_two_monoTwo_two_three (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
      = (1 - q : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3)
        + (-q : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2) := by
  rw [show (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3 from by ring,
        corner_two_auxVar_one_sq_mul_auxVar_two_cube hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(y_1^3y_2^1)`, with every exponent written out. -/
theorem corner_two_monoTwo_three_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
  rw [show (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1
      = (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) from by ring,
        corner_two_auxVar_one_cube_mul_auxVar_two hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(y_1^3y_2^2)`, with every exponent written out. -/
theorem corner_two_monoTwo_three_two (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) := by
  rw [show (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2
      = (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2 from by ring,
        corner_two_auxVar_one_cube_mul_auxVar_two_sq hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(y_1^4y_2^1)`, with every exponent written out. -/
theorem corner_two_monoTwo_four_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 4)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2) := by
  rw [show (auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1
      = (auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) from by ring,
        corner_two_auxVar_one_pow_four_mul_auxVar_two hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(f·y_1^1y_2^2)`: the corner is `Λ`-linear. -/
theorem corner_two_monoTwo_one_two_C (hq0 : q ≠ 0) (hq1 : q ≠ 1) (f : Lambda L) :
    corner q 2 (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2))
      = (1 - q : L) • (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
      + (-q : L) • (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1)) := by
  rw [show (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2))
      = MvPolynomial.C f * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2) from by ring,
    corner_two_C_mul hq0 hq1 f (by simpa using monoTwo_mem_piece 1 2),
      corner_two_auxVar_one_mul_auxVar_two_sq hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(f·y_1^1y_2^3)`: the corner is `Λ`-linear. -/
theorem corner_two_monoTwo_one_three_C (hq0 : q ≠ 0) (hq1 : q ≠ 1) (f : Lambda L) :
    corner q 2 (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3))
      = (1 - q : L) • (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3))
      + (1 - q : L) • (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
      + (-q : L) • (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1)) := by
  rw [show (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3))
      = MvPolynomial.C f * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 3) from by ring,
    corner_two_C_mul hq0 hq1 f (by simpa using monoTwo_mem_piece 1 3),
      corner_two_auxVar_one_mul_auxVar_two_cube hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(f·y_1^2y_2^1)`: the corner is `Λ`-linear. -/
theorem corner_two_monoTwo_two_one_C (hq0 : q ≠ 0) (hq1 : q ≠ 1) (f : Lambda L) :
    corner q 2 (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1))
      = (-1 : L) • (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)) := by
  rw [show (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1))
      = MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L)) from by ring,
    corner_two_C_mul hq0 hq1 f (by simpa using monoTwo_mem_piece 2 1),
      corner_two_auxVar_one_sq_mul_auxVar_two hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(f·y_1^2y_2^2)`: the corner is `Λ`-linear. -/
theorem corner_two_monoTwo_two_two_C (hq0 : q ≠ 0) (hq1 : q ≠ 1) (f : Lambda L) :
    corner q 2 (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
      = (-q : L) • (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)) := by
  rw [show (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
      = MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) from by ring,
    corner_two_C_mul hq0 hq1 f (by simpa using monoTwo_mem_piece 2 2),
      corner_two_auxVar_one_sq_mul_auxVar_two_sq hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(2)}(f·y_1^3y_2^1)`: the corner is `Λ`-linear. -/
theorem corner_two_monoTwo_three_one_C (hq0 : q ≠ 0) (hq1 : q ≠ 1) (f : Lambda L) :
    corner q 2 (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1))
      = (-1 : L) • (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3))
      + (q - 1 : L) • (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
        := by
  rw [show (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1))
      = MvPolynomial.C f * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L)) from by ring,
    corner_two_C_mul hq0 hq1 f (by simpa using monoTwo_mem_piece 3 1),
      corner_two_auxVar_one_cube_mul_auxVar_two hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(3)}(y_1^1y_2^1y_3^1)`, with every exponent written out. -/
theorem corner_three_monoThree_one_one_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 3 ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)
      = (-q ^ 2 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L)
        ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1
      = (auxVar 1 : Total L) * (auxVar 2 : Total L) * (auxVar 3 : Total L) from by ring,
        corner_three_auxVarProd hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(3)}(y_1^1y_2^1y_3^2)`, with every exponent written out. -/
theorem corner_three_monoThree_one_one_two (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 3 ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 2)
      = (-q*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 :
        Total L) ^ 2)
        + (-q*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 :
          Total L) ^ 1)
        + (-q ^ 2 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total
          L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 2
      = (auxVar 1 : Total L) * (auxVar 2 : Total L) * (auxVar 3 : Total L) ^ 2 from by ring,
        corner_three_prod_mul_auxVar_three hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(3)}(y_1^1y_2^2y_3^1)`, with every exponent written out. -/
theorem corner_three_monoThree_one_two_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 3 ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 1)
      = (-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^
        2) := by
  rw [show (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 1
      = (auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) from by ring,
        corner_three_auxVar_one_mul_auxVar_two_sq_mul_auxVar_three hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(3)}(y_1^2y_2^1y_3^1)`, with every exponent written out. -/
theorem corner_three_monoThree_two_one_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 3 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)
      = (-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^
        1) := by
  rw [show (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) * (auxVar 3 : Total L) from by ring,
        corner_three_auxVar_one_sq_mul_auxVar_two_mul_auxVar_three hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(3)}(y_1^3y_2^1y_3^1)`, with every exponent written out. -/
theorem corner_three_monoThree_three_one_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 3 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)
      = (-q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3 * (auxVar 3 : Total L) ^ 1)
        + (q*(q - 1) : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 :
          Total L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1
      = (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) * (auxVar 3 : Total L) from by ring,
        corner_three_auxVar_one_cube_mul_auxVar_two_mul_auxVar_three hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(3)}(f·y_1^2y_2^1y_3^1)`: the corner is `Λ`-linear. -/
theorem corner_three_monoThree_two_one_one_C (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (f : Lambda L) :
    corner q 3 (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar
      3 : Total L) ^ 1))
      = (-q : L) • (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 *
        (auxVar 3 : Total L) ^ 1)) := by
  rw [show (MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 :
    Total L) ^ 1))
      = MvPolynomial.C f * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) * (auxVar 3 : Total
        L)) from by ring,
    corner_three_C_mul hq0 hq1 f (by simpa using monoThree_mem_piece 2 1 1),
    corner_three_auxVar_one_sq_mul_auxVar_two_mul_auxVar_three hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `Δ^{(4)}(y_1y_2y_3y_4)`, with every exponent written out. -/
theorem corner_four_monoFour_one_one_one_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 4 ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1 *
      (auxVar 4 : Total L) ^ 1)
      = (-q ^ 3 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L)
        ^ 1 * (auxVar 4 : Total L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1 *
    (auxVar 4 : Total L) ^ 1
      = (auxVar 1 : Total L) * (auxVar 2 : Total L) * (auxVar 3 : Total L) * (auxVar 4 : Total L)
        from by ring, corner_four_auxVarProd hq0 hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

omit [Algebra ℚ L] in
/-- `d_+^{(0)}1 = -y_1`, with the exponent written out. -/
theorem dplus_zero_monoZero (q : L) :
    dplus q 0 (1 : Total L)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1) := by
  rw [dplus_zero_one q, show (MvPolynomial.X 0 : Total L) = auxVar 1 from rfl]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

omit [Algebra ℚ L] in
/-- `d_+^{(1)}(y_1^1)`, with every exponent written out. -/
theorem dplus_one_monoOne_one (q : L) :
    dplus q 1 ((auxVar 1 : Total L) ^ 1)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 1
      = (auxVar 1 : Total L) from by ring, dplus_one_auxVar_one q]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

omit [Algebra ℚ L] in
/-- `d_+^{(1)}(y_1^2)`, with every exponent written out. -/
theorem dplus_one_monoOne_two (q : L) :
    dplus q 1 ((auxVar 1 : Total L) ^ 2)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 2
      = (auxVar 1 : Total L) ^ 2 from by ring, dplus_one_auxVar_one_sq q]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

omit [Algebra ℚ L] in
/-- `d_+^{(1)}(y_1^3)`, with every exponent written out. -/
theorem dplus_one_monoOne_three (q : L) :
    dplus q 1 ((auxVar 1 : Total L) ^ 3)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 3
      = (auxVar 1 : Total L) ^ 3 from by ring, dplus_one_auxVar_one_cube q]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

omit [Algebra ℚ L] in
/-- `d_+^{(1)}(y_1^4)`, with every exponent written out. -/
theorem dplus_one_monoOne_four (q : L) :
    dplus q 1 ((auxVar 1 : Total L) ^ 4)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 4)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 4
      = (auxVar 1 : Total L) ^ 4 from by ring, dplus_one_auxVar_one_pow_four q]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

omit [Algebra ℚ L] in
/-- `d_+^{(2)}(y_1^1y_2^1)`, with every exponent written out. -/
theorem dplus_two_monoTwo_one_one (q : L) :
    dplus q 2 ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^
        1) := by
  rw [show (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1
      = (auxVar 1 : Total L) * (auxVar 2 : Total L) from by ring, dplus_two_auxVarProd_two q]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

omit [Algebra ℚ L] in
/-- `d_+^{(2)}(y_1^1y_2^2)`, with every exponent written out. -/
theorem dplus_two_monoTwo_one_two (q : L) :
    dplus q 2 ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 2)
        + (q*(q - 1) : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 :
          Total L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2
      = (auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 from by ring,
        dplus_two_auxVar_one_mul_auxVar_two_sq q]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

omit [Algebra ℚ L] in
/-- `d_+^{(2)}(y_1^2y_2^1)`, with every exponent written out. -/
theorem dplus_two_monoTwo_two_one (q : L) :
    dplus q 2 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 1)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total
          L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) from by ring,
        dplus_two_auxVar_one_sq_mul_auxVar_two q]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

omit [Algebra ℚ L] in
/-- `d_+^{(2)}(y_1^2y_2^2)`, with every exponent written out. -/
theorem dplus_two_monoTwo_two_two (q : L) :
    dplus q 2 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 2)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total
          L) ^ 2)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total
          L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 from by ring,
        dplus_two_auxVar_one_sq_mul_auxVar_two_sq q]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

omit [Algebra ℚ L] in
/-- `d_+^{(2)}(y_1^3y_2^1)`, with every exponent written out. -/
theorem dplus_two_monoTwo_three_one (q : L) :
    dplus q 2 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 3 * (auxVar 3 : Total L) ^ 1)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total
          L) ^ 1)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total
          L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1
      = (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) from by ring,
        dplus_two_auxVar_one_cube_mul_auxVar_two q]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

omit [Algebra ℚ L] in
/-- `d_+^{(3)}(y_1^1y_2^1y_3^1)`, with every exponent written out. -/
theorem dplus_three_monoThree_one_one_one (q : L) :
    dplus q 3 ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1
        * (auxVar 4 : Total L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1
      = (auxVar 1 : Total L) * (auxVar 2 : Total L) * (auxVar 3 : Total L) from by ring,
        dplus_three_auxVarProd_three q]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

omit [Algebra ℚ L] in
/-- `d_+^{(3)}(y_1^2y_2^1y_3^1)`, with every exponent written out. -/
theorem dplus_three_monoThree_two_one_one (q : L) :
    dplus q 3 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1)
      = (-1 : L) • ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2 * (auxVar 3 : Total L) ^ 1
        * (auxVar 4 : Total L) ^ 1)
        + (q - 1 : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total
          L) ^ 1 * (auxVar 4 : Total L) ^ 1) := by
  rw [show (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1 * (auxVar 3 : Total L) ^ 1
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) * (auxVar 3 : Total L) from by ring,
        dplus_three_auxVar_one_sq_mul_auxVar_two_mul_auxVar_three q]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `d_+^{(1)}(e_1y_1^2)`, with every exponent written out. -/
theorem dplus_one_monoOne_two_C_elemSymm_one (q : L) :
    dplus q 1 (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2))
      = (-1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total
        L) ^ 2))
        + (q - 1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
          Total L) ^ 1))
        + (1 - q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) := by
  rw [dplus_one_C_elemSymm_one_mul_auxVar_one_sq q]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- `d_+^{(1)}(e_1y_1^3)`, with every exponent written out. -/
theorem dplus_one_monoOne_three_C_elemSymm_one (q : L) :
    dplus q 1 (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3))
      = (-1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total
        L) ^ 3))
        + (q - 1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 :
          Total L) ^ 2))
        + (1 - q : L) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
        + (q - 1 : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 :
          Total L) ^ 1))
        + ((q - 1) ^ 2 : L) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
  rw [dplus_one_C_elemSymm_one_mul_auxVar_one_cube q]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

end HJO.Sweep

end
