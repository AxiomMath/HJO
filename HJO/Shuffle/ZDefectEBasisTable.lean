/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepStageWordTwoThreeTwoValue
public import HJO.Shuffle.BraidInvMonomialPair

/-! # The `e`-basis `B`-word table for `HJO.Sweep.zDefect`, and the three missing entries

`HJO/Shuffle/SweepPairIterate.lean` and `HJO/Shuffle/BraidInvMonomialPair.lean` both name
the same absent object: `HJO.Sweep.zDefect q u n A` at `(n,A) = (2, e_1^2)`, `(2, e_2)` and
`(3, e_1)`. The entries proved earlier are `HJO.Sweep.zDefect_one_one`, `zDefect_two_one`,
`zDefect_three_one`, `zDefect_one_elemSymm_one`, `zDefect_two_elemSymm_one`, and none of the three
is among them. This file builds the table **at every index**, evaluates the three entries, and
runs it into its first consumer.

Nothing here is an equivalence. Every result is a value, or a row of a table of values.

## The table

`HJO.Sweep.zDefect q u n A = d^*_+{}^{(0)}(C(B_nA)) - B_n(d^*_+{}^{(0)}(CA))` is the failure of
`HJO.Sym.Bop` to commute with the one-letter displacement `(q-1)uy_1`. Both halves are computable
once `A` is an `e`-monomial, and this is the split that does it:

* **`HJO.Sweep.bopExt_dplusStar_zero_C_elemSymm`** — the *second* half at an arbitrary `e_n` and an
  arbitrary integer index `r`. `HJO.Sweep.dplusStar_C_elemSymm` writes the displacement as a
  `Finset.range` sum of powers of the letter `uy_1` times constants, and every one of those powers
  lies in `HJO.Sweep.auxSubalg`, so `HJO.Sweep.bopExt_auxSubalg_mul` carries `B_r` past it onto the
  constant. No case split, no hypothesis, every `r : ℤ` including the negative ones.

* **`HJO.Sweep.zDefect_elemSymm`** — the whole defect at an arbitrary `e_n` and an arbitrary index,
  the first half left as `d^*_+(C(B_ne_n)) - C(B_ne_n)`. **The `Λ`-constant term cancels
  identically**, which is why this and every row below is divisible by `y_1`; at `n = 0` the sum is
  empty and the row degenerates to `HJO.Sweep.zDefect_one_of_table`, the vacuum row.

* The graded rows the two-part family actually reads, each at **every** index `r` and each in the
  form `∑_m x_m·y_1^m·C(B_r f_m)` that `HJO.Sweep.bopExt_smul_auxVar_pow_mul_C` consumes:
  `HJO.Sweep.zDefect_elemSymm_one_expand`, `zDefect_elemSymm_two_expand`,
  `zDefect_elemSymm_one_sq_expand`, `zDefect_elemSymm_one_cube_expand`,
  `zDefect_elemSymm_one_mul_two_expand`. That is every `e`-monomial of weight at most three, which
  covers every coefficient the two-part vectors carry.

* **`d^*_+` in graded form at the `e`-monomials of weight four**, the first half's input:
  `HJO.Sweep.dplusStar_C_elemSymm_three_expand`, `_four_expand`, `_one_mul_two_expand`,
  `_one_cube_expand`, `_one_mul_three_expand`, `_one_sq_mul_two_expand`, `_two_sq_expand`.
  Multiplicativity (`HJO.Sweep.dplusStar_C_mul`) does all the work; the earlier
  `HJO.Sweep.dplusStar_C_elemSymm_one_expand`, `_two_expand`, `_one_sq_expand` are the weight-two
  cases.

The `B_r`-values themselves are **not** new: the Pieri rules `HJO.Sym.bop_elemSymm_one_mul` and
`HJO.Sym.bop_elemSymm_two_mul` are proved at every index, with `HJO.Sym.bop_natCast_one` as the
base, so the `B`-side of the table already existed at every `e`-monomial. What was missing was the
`d^*_+`-side and the join, and that is what is above.

## The three entries

`HJO.Sweep.zDefect_two_elemSymm_one_sq`, `HJO.Sweep.zDefect_two_elemSymm_two`,
`HJO.Sweep.zDefect_three_elemSymm_one`, each an explicit element of `V_1` and each
**hypothesis-free**:

`zDefect_2(e_1^2) = (q-1)u·y_1e_1^3 + 2(q-1)^2u·y_1e_1e_2 + (q-1)^3u·y_1e_3
    - (q-1)u^2·y_1^2e_1^2 + (q-1)^3u^2·y_1^2e_2`,

`zDefect_2(e_2) = q(q-1)u·y_1e_1e_2 + q(q-1)^2u·y_1e_3 - q(q-1)u^2·y_1^2e_2`,

`zDefect_3(e_1) = -(q-1)u·y_1e_1e_2 - (q-1)^2u·y_1e_3 + (q-1)u^2·y_1^2e_1^2 - (q-1)u^3·y_1^3e_1`.

Each is homogeneous of the weight of `B_nA`, and in each the weight-four `Λ`-term and the top power
of the letter cancel identically — the `y_1^3` and `y_1^4` coefficients of the first two vanish, not
by a hypothesis but term by term.

## Consistency checks

All **five** earlier entries are re-derived *through* the table —
`HJO.Sweep.zDefect_one_one_of_table`, `zDefect_two_one_of_table`, `zDefect_three_one_of_table`,
`zDefect_one_elemSymm_one_of_table`, `zDefect_two_elemSymm_one_of_table` — and each is checked to be
literally the earlier `Prop` by `HJO.Sweep.zDefect_one_one_of_table_eq` and its four companions,
which typecheck only if the statements are identical. The earlier proofs ran on hand expansions
with no general machinery in them; three of the five are the sharp ones, because there the
cancellation is exact: `zDefect_one_elemSymm_one` has a single monomial left after the `y_1^2`
terms annihilate, and the two vacuum rows at `n = 2, 3` pin the alternating signs of the letter's
powers.

## The first consumer, and what it does NOT decide

`HJO.Sweep.zCommTwo_stageWordTotal_two_three_one_one` reads the single `z` letter on the `[1,1]`
stage word as five defects — `HJO.Sweep.zCommTwo_monomial'` at the five monomials of
`HJO.Sweep.stageWordTotal_two_three_one_one` — and **three of the five are exactly the entries
above**, the other two being `zDefect_two_elemSymm_one` and `zDefect_three_one`. Substituting gives
`HJO.Sweep.zCommValueOneOne`, a ten-monomial element of `V_2`
(`HJO.Sweep.zCommTwo_stageWordTotal_two_three_one_one_expand`), hence
`HJO.Sweep.zopOneStar_two_stageWordTotal_two_three_one_one_eq_value`.

Applying the outer letter on top of it, `HJO.Sweep.braidInvEnd_one_auxVar_sq_mul_zCommValueOneOne`
and `HJO.Sweep.pairArgSucc_one_zero_expand` make

`HJO.Sweep.pairArgSucc q u 1 0 = \frac{q}{1-q}·HJO.Sweep.pairArgSuccValueOneZero q u`,

a **twelve-monomial explicit element of `V_2` with no operator of the sweep and no braid letter left
in it** — the step vector the `B`-recursion of
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_succ` carries at its first step. The five
values of `T_1^{-1}` it runs on are `HJO.Sweep.braidInvEnd_one_cube_sq` (proved earlier) and
`HJO.Sweep.braidInvEnd_one_pow_four_sq`, `_pow_five_sq`, `_pow_four_cube`, `_pow_five_cube`, each
off `HJO.Sweep.braidInvEnd_one_auxVar_pow_mul_auxVar_pow_pair` with the block values
`HJO.Sweep.pairBlock_succ_self`, `pairBlock_add_two_self` and the new
`HJO.Sweep.pairBlock_add_three_self`.

**`(A,B) = (1,2)` is NOT decided here, and the three entries above are not enough to decide it.**
The engine at `(A,B) = (1,2)` is
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_succ` at `A = 1, B = 0`, whose right-hand
side applies `HJO.Sweep.zDefect q u (d 1)` to the **coefficients of
`HJO.Sweep.pairArgSucc q u 1 0`**, not to those of the stage word. Reading `(d 0, d 1)` and the
coefficients off `HJO.Sweep.pairArgSuccValueOneZero`, a *second* round of the table is needed, at
exactly these eleven arguments and no others:

* `zDefect_3` at `e_1^3`, `e_1e_2`, `e_3`, `e_1^2`, `e_2` (at `e_1` it is the
  `zDefect_three_elemSymm_one` above),
* `zDefect_4` at `e_1^2`, `e_2`, `e_1`, `1`,
* `zDefect_5` at `e_1`, `1`.

The rows above supply every one of these *shapes* at every index; what each still needs is `B_r` of
its argument as an `e`-polynomial of weight up to eight and `d^*_+` of that polynomial. Separately,
the engine sums over `(pairArgSucc q u 1 0).support`, and that `Finset` is not computed here either.
So the precise quantifier is: **for no pair `(A,B)` other than `(1,1)` is
`ct(d_-^{(1)}d_-^{(2)}(G_{2,B}G_{1,A}(1)))` an explicit element of `Λ` after this file**, and in
particular `(1,2)`, `(2,1)`, `(2,2)` are all still open.

Nothing here asserts a closed form in `A` or `B`, and the one-part family's `2, 9, 26` `e`-monomials
at `A = 1, 2, 3` remain the reason to expect none.

## Genericity

**The whole table and all three entries are unconditional** — no hypothesis on `q`, `u`, `n` or `r`,
and `r` may be any integer in `HJO.Sweep.bopExt_dplusStar_zero_C_elemSymm`. That is not bookkeeping:
`HJO.Sweep.zDefect` is built from `d^*_+{}^{(0)}` and `HJO.Sweep.bopExt`, both of which are
**polynomial** in `q` and `u`, so no letter of the table can become a zero map. In particular
`M = (1-q)(1-u) ≠ 0`, `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, `qu ≠ 1` are all *unused* by every row and by every
value.

The hypotheses appear only where a **consumer** needs them, and they are those of the `[1,1]` value,
never the table's:

* `q ≠ 0`, `u ≠ 0`, `q ≠ 1` on `HJO.Sweep.zCommTwo_stageWordTotal_two_three_one_one` and everything
  after it — inherited verbatim from `HJO.Sweep.stageWordTotal_two_three_one_one`, where the
  `(qu)^{-1}` of `HJO.Sweep.slopeOperator` and the `q^2/(1-q)` of `HJO.Sweep.zop` become the zero
  map in a field at `qu = 0` and at `q = 1`, so a clause asserting otherwise there is *false*, not
  vacuous;
* `q ≠ 0` alone on `HJO.Sweep.braidInvEnd_one_cube_cube`, which cancels a `q^{-1}·q` — the same
  phenomenon as in `HJO/Shuffle/BraidInvMonomialPair.lean`: the four other `T_1^{-1}` values
  here are hypothesis-free because their `(q-1)`-term is annihilated by the block instead;
* `q ≠ 0` and `q ≠ 1` again on `HJO.Sweep.pairArgSucc_one_zero_expand`, where
  `q^2/(1-q)·q^{-1} = q/(1-q)` is cancelled.
  `HJO.Sweep.braidInvEnd_one_auxVar_sq_mul_zCommValueOneOne`
  just above it keeps that `q^{-1}` symbolic and is therefore unconditional.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

-- Every exponent written as a numeral in this file is a natural number. Saying so up front lets
-- each `x ^ n` resolve `HPow _ ℕ _` at once instead of retrying instance resolution for the
-- pending numeral type until defaulting, which dominated elaboration here. The elaborated terms
-- are the ones the default instance would produce.
local macro_rules | `($x ^ $n:num) => `(rightact% HPow.hPow $x ($n : ℕ))

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### `B_r` on the displacement of an elementary function, at every pair of indices -/

/-- `B_r` applied coefficientwise to `d^*_+{}^{(0)}(Ce_n)`, at every `r` and every `n`. -/
theorem bopExt_dplusStar_zero_C_elemSymm (q u : L) (r : ℤ) (n : ℕ) :
    bopExt q r (dplusStar q u 0 (MvPolynomial.C (elemSymm L n) : Total L))
      = MvPolynomial.C (Bop q r (elemSymm L n))
        - scal (q - 1) * ∑ i ∈ Finset.range n,
            (-starLetter u) ^ (i + 1)
              * MvPolynomial.C (Bop q r (elemSymm L (n - 1 - i))) := by
  rw [dplusStar_C_elemSymm, map_sub, bopExt_C,
    bopExt_auxSubalg_mul q r (scal_mem_auxSubalg (q - 1)), map_sum]
  refine congrArg (fun S => MvPolynomial.C (Bop q r (elemSymm L n)) - scal (q - 1) * S) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bopExt_auxSubalg_mul q r (pow_mem (neg_mem (starLetter_mem_auxSubalg u)) (i + 1)), bopExt_C]

/-- **The defect at an arbitrary elementary function and an arbitrary index.** -/
theorem zDefect_elemSymm (q u : L) (r n : ℕ) :
    zDefect q u r (elemSymm L n)
      = (dplusStar q u 0 (MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L n)))
            - MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L n)))
        + scal (q - 1) * ∑ i ∈ Finset.range n,
            (-starLetter u) ^ (i + 1)
              * MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L (n - 1 - i))) := by
  rw [zDefect, bopExt_dplusStar_zero_C_elemSymm]
  ring

/-! ### The three graded rows of the table, at every index -/

/-- The `e_1` row of the table, at every index `r`: one power of the letter `uy_1`, and its
coefficient is `B_r(1)`. Unconditional — every scalar is polynomial in `q` and `u`. -/
theorem zDefect_elemSymm_one_expand (q u : L) (r : ℕ) :
    zDefect q u r (elemSymm L 1)
      = (dplusStar q u 0 (MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 1)))
            - MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 1)))
        - ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (1 : Lambda L))) := by
  rw [zDefect, dplusStar_C_elemSymm_one_expand, map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C]
  ring

/-- The `e_2` row of the table, at every index `r`. Unconditional. -/
theorem zDefect_elemSymm_two_expand (q u : L) (r : ℕ) :
    zDefect q u r (elemSymm L 2)
      = (dplusStar q u 0 (MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 2)))
            - MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 2)))
        - ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 1)))
        - ((1 - q) * u ^ 2) • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (1 : Lambda L))) := by
  rw [zDefect, dplusStar_C_elemSymm_two_expand, map_add, map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_smul_auxVar_pow_mul_C]
  ring

/-- The `e_1^2` row of the table, at every index `r`: the displacement of a square, so the
middle coefficient carries the binomial `2`. Unconditional. -/
theorem zDefect_elemSymm_one_sq_expand (q u : L) (r : ℕ) :
    zDefect q u r (elemSymm L 1 * elemSymm L 1)
      = (dplusStar q u 0 (MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1)))
            - MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1)))
        - (2 * ((q - 1) * u)) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 1)))
        - ((q - 1) ^ 2 * u ^ 2) • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (1 : Lambda L))) := by
  rw [zDefect, dplusStar_C_elemSymm_one_sq_expand, map_add, map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_smul_auxVar_pow_mul_C]
  ring

/-! ### `d^*_+` in graded form at the `e`-monomials of weight four -/

/-- `d^*_+(e_3)` in the graded form `∑_m x_m·y_1^m·Cf_m` that `HJO.Sweep.bopExt` reads.
Unconditional, and the level `k` is not read. -/
theorem dplusStar_C_elemSymm_three_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 3) : Total L)
      = MvPolynomial.C (elemSymm L 3)
        + ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2))
        + ((1 - q) * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1))
        + ((q - 1) * u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Lambda L)) := by
  rw [dplusStar_C_elemSymm_three]
  simp only [starLetter, smul_eq_scal_mul, scal, map_sub, map_mul, map_one,
    map_pow]
  ring

/-- `d^*_+(e_4)`, graded. Unconditional, at every level. -/
theorem dplusStar_C_elemSymm_four_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 4) : Total L)
      = MvPolynomial.C (elemSymm L 4)
        + ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 3))
        + ((1 - q) * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2))
        + ((q - 1) * u ^ 3) • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1))
        + ((1 - q) * u ^ 4) • ((auxVar 1 : Total L) ^ 4 * MvPolynomial.C (1 : Lambda L)) := by
  rw [dplusStar_C_elemSymm_four]
  simp only [starLetter, smul_eq_scal_mul, scal, map_sub, map_mul, map_one,
    map_pow]
  ring

/-- `d^*_+(e_1e_3)`, graded: the product of the `e_1` and `e_3` values off
`HJO.Sweep.dplusStar_C_mul`. The `y_1^3`-coefficient `(q-1)(2-q)` is where the two factors'
opposite signs meet. Unconditional. -/
theorem dplusStar_C_elemSymm_one_mul_three_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 1 * elemSymm L 3) : Total L)
      = MvPolynomial.C (elemSymm L 1 * elemSymm L 3)
        + ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 3))
        + ((1 - q) * u ^ 2) • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + ((q - 1) ^ 2 * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2))
        + ((q - 1) * (2 - q) * u ^ 3) • ((auxVar 1 : Total L) ^ 3
            * MvPolynomial.C (elemSymm L 1))
        + ((q - 1) ^ 2 * u ^ 4) • ((auxVar 1 : Total L) ^ 4
            * MvPolynomial.C (1 : Lambda L)) := by
  rw [dplusStar_C_mul, dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_three]
  simp only [starLetter, smul_eq_scal_mul, scal, map_sub, map_mul, map_one,
    map_pow, map_ofNat]
  ring

/-- `d^*_+(e_1^2e_2)`, graded, off two applications of `HJO.Sweep.dplusStar_C_mul`.
Unconditional. -/
theorem dplusStar_C_elemSymm_one_sq_mul_two_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)) : Total L)
      = MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))
        + ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
        + (2 * ((q - 1) * u)) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + ((2 * (q - 1) ^ 2 - (q - 1)) * u ^ 2) • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + ((q - 1) ^ 2 * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2))
        + (((q - 1) ^ 3 - 2 * (q - 1) ^ 2) * u ^ 3) • ((auxVar 1 : Total L) ^ 3
            * MvPolynomial.C (elemSymm L 1))
        + (-((q - 1) ^ 3) * u ^ 4) • ((auxVar 1 : Total L) ^ 4
            * MvPolynomial.C (1 : Lambda L)) := by
  rw [dplusStar_C_mul, dplusStar_C_mul, dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two]
  simp only [starLetter, smul_eq_scal_mul, scal, map_sub, map_neg, map_mul, map_one,
    map_pow, map_ofNat]
  ring

/-- `d^*_+(e_2^2)`, graded. Unconditional. -/
theorem dplusStar_C_elemSymm_two_sq_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 2 * elemSymm L 2) : Total L)
      = MvPolynomial.C (elemSymm L 2 * elemSymm L 2)
        + (2 * ((q - 1) * u)) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + ((q - 1) ^ 2 * u ^ 2) • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (-(2 * (q - 1)) * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2))
        + (-(2 * (q - 1) ^ 2) * u ^ 3) • ((auxVar 1 : Total L) ^ 3
            * MvPolynomial.C (elemSymm L 1))
        + ((q - 1) ^ 2 * u ^ 4) • ((auxVar 1 : Total L) ^ 4
            * MvPolynomial.C (1 : Lambda L)) := by
  rw [dplusStar_C_mul, dplusStar_C_elemSymm_two]
  simp only [starLetter, smul_eq_scal_mul, scal, map_sub, map_neg, map_mul, map_one,
    map_pow, map_ofNat]
  ring

/-- `d^*_+(e_1e_2)`, graded. Unconditional. -/
theorem dplusStar_C_elemSymm_one_mul_two_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) : Total L)
      = MvPolynomial.C (elemSymm L 1 * elemSymm L 2)
        + ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 2))
        + (((q - 1) ^ 2 - (q - 1)) * u ^ 2) • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 1))
        + (-((q - 1) ^ 2) * u ^ 3) • ((auxVar 1 : Total L) ^ 3
            * MvPolynomial.C (1 : Lambda L)) := by
  rw [dplusStar_C_mul, dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two]
  simp only [starLetter, smul_eq_scal_mul, scal, map_sub, map_neg, map_mul, map_one,
    map_pow]
  ring

/-- `d^*_+(e_1^3)`, graded: the cube of the `e_1` value, so the coefficients are the binomials
`3, 3, 1`. Unconditional. -/
theorem dplusStar_C_elemSymm_one_cube_expand (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)) : Total L)
      = MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))
        + (3 * ((q - 1) * u)) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (3 * (q - 1) ^ 2 * u ^ 2) • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 1))
        + ((q - 1) ^ 3 * u ^ 3) • ((auxVar 1 : Total L) ^ 3
            * MvPolynomial.C (1 : Lambda L)) := by
  rw [dplusStar_C_mul, dplusStar_C_mul, dplusStar_C_elemSymm_one]
  simp only [starLetter, smul_eq_scal_mul, scal, map_sub, map_mul, map_one,
    map_pow, map_ofNat]
  ring

/-- The `e_1^3` row of the table, at every index. -/
theorem zDefect_elemSymm_one_cube_expand (q u : L) (r : ℕ) :
    zDefect q u r (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))
      = (dplusStar q u 0 (MvPolynomial.C
              (Bop q ((r : ℕ) : ℤ) (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))))
            - MvPolynomial.C (Bop q ((r : ℕ) : ℤ)
                (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))))
        - (3 * ((q - 1) * u)) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1)))
        - (3 * (q - 1) ^ 2 * u ^ 2) • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 1)))
        - ((q - 1) ^ 3 * u ^ 3) • ((auxVar 1 : Total L) ^ 3
            * MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (1 : Lambda L))) := by
  rw [zDefect, dplusStar_C_elemSymm_one_cube_expand, map_add, map_add, map_add, bopExt_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_smul_auxVar_pow_mul_C, bopExt_smul_auxVar_pow_mul_C]
  ring

/-- The `e_1e_2` row of the table, at every index. -/
theorem zDefect_elemSymm_one_mul_two_expand (q u : L) (r : ℕ) :
    zDefect q u r (elemSymm L 1 * elemSymm L 2)
      = (dplusStar q u 0 (MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 2)))
            - MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 2)))
        - ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1)))
        - ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 2)))
        - (((q - 1) ^ 2 - (q - 1)) * u ^ 2) • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (elemSymm L 1)))
        - (-((q - 1) ^ 2) * u ^ 3) • ((auxVar 1 : Total L) ^ 3
            * MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (1 : Lambda L))) := by
  rw [zDefect, dplusStar_C_elemSymm_one_mul_two_expand, map_add, map_add, map_add, map_add,
    bopExt_C, bopExt_smul_auxVar_pow_mul_C, bopExt_smul_auxVar_pow_mul_C,
    bopExt_smul_auxVar_pow_mul_C, bopExt_smul_auxVar_pow_mul_C]
  ring

/-! ### The three missing entries of the table -/

/-- **FIRST MISSING ENTRY: `zDefect_2(e_1^2)`.**

`(q-1)u·y_1e_1^3 + 2(q-1)^2u·y_1e_1e_2 + (q-1)^3u·y_1e_3 - (q-1)u^2·y_1^2e_1^2
  + (q-1)^3u^2·y_1^2e_2`.

The `y_1^3`- and `y_1^4`-coefficients of the two halves cancel term by term, and so does the whole
weight-four `Λ`-part; nothing survives that is not divisible by `y_1`.

**Hypothesis-free.** `HJO.Sweep.zDefect` is polynomial in `q` and `u` — no inverse appears — so no
letter can become the zero map and no exclusion is needed. -/
theorem zDefect_two_elemSymm_one_sq (q u : L) :
    zDefect q u 2 (elemSymm L 1 * elemSymm L 1)
      = ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
        + (2 * (q - 1) ^ 2 * u) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + ((q - 1) ^ 3 * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 3))
        + (-((q - 1) * u ^ 2)) • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + ((q - 1) ^ 3 * u ^ 2) • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 2)) := by
  rw [zDefect_elemSymm_one_sq_expand, bop_two_elemSymm_one_sq, bop_two_elemSymm_one', bop_two_one]
  simp only [map_add, map_sub, C_smul, map_smul, dplusStar_C_elemSymm_one_sq_mul_two_expand,
    dplusStar_C_elemSymm_one_mul_three_expand, dplusStar_C_elemSymm_four_expand]
  simp only [smul_eq_scal_mul, scal, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- **SECOND MISSING ENTRY: `zDefect_2(e_2)`.**

`q(q-1)u·y_1e_1e_2 + q(q-1)^2u·y_1e_3 - q(q-1)u^2·y_1^2e_2`, which is
`q(q-1)u·y_1(B_2(e_1) - uy_1B_2(1))` — every coefficient carries a factor `q`, unlike the entry
above. **Hypothesis-free.** -/
theorem zDefect_two_elemSymm_two (q u : L) :
    zDefect q u 2 (elemSymm L 2)
      = (q * (q - 1) * u) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (q * (q - 1) ^ 2 * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 3))
        + (-(q * (q - 1) * u ^ 2)) • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 2)) := by
  rw [zDefect_elemSymm_two_expand, bop_two_elemSymm_two', bop_two_elemSymm_one', bop_two_one]
  simp only [map_sub, C_smul, map_smul, dplusStar_C_elemSymm_two_sq_expand,
    dplusStar_C_elemSymm_one_mul_three_expand, dplusStar_C_elemSymm_four_expand]
  simp only [smul_eq_scal_mul, scal, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- **THIRD MISSING ENTRY: `zDefect_3(e_1)`.**

`-(q-1)u·y_1e_1e_2 - (q-1)^2u·y_1e_3 + (q-1)u^2·y_1^2e_1^2 - (q-1)u^3·y_1^3e_1`.

This is the deepest of the three in the letter: the index `3` reaches `y_1^3`, whereas the two
index-`2` entries stop at `y_1^2`. **Hypothesis-free.** -/
theorem zDefect_three_elemSymm_one (q u : L) :
    zDefect q u 3 (elemSymm L 1)
      = (-((q - 1) * u)) • ((auxVar 1 : Total L) ^ 1
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
        + (-((q - 1) ^ 2 * u)) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (elemSymm L 3))
        + ((q - 1) * u ^ 2) • ((auxVar 1 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (-((q - 1) * u ^ 3)) • ((auxVar 1 : Total L) ^ 3
            * MvPolynomial.C (elemSymm L 1)) := by
  rw [zDefect_elemSymm_one_expand, bop_three_elemSymm_one, bop_three_one']
  simp only [map_add, map_neg, C_smul, map_smul,
    dplusStar_C_elemSymm_one_mul_three_expand, dplusStar_C_elemSymm_four_expand]
  simp only [smul_eq_scal_mul, scal, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-! ### Consistency checks: the five earlier entries, re-derived through the table -/

/-- The vacuum row of the table, at every index: the `Λ`-constant part of the defect cancels. -/
theorem zDefect_one_of_table (q u : L) (r : ℕ) :
    zDefect q u r (1 : Lambda L)
      = dplusStar q u 0 (MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (1 : Lambda L)))
        - MvPolynomial.C (Bop q ((r : ℕ) : ℤ) (1 : Lambda L)) := by
  have h := zDefect_elemSymm (L := L) q u r 0
  rw [elemSymm_zero L, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero] at h
  exact h

/-- **Check:** the earlier `HJO.Sweep.zDefect_one_one`, re-derived through the vacuum row. -/
theorem zDefect_one_one_of_table (q u : L) :
    zDefect q u 1 (1 : Sym.Lambda L) = -(scal ((q - 1) * u) * (auxVar 1 : Total L)) := by
  have hb0 : Bop q ((1 : ℕ) : ℤ) (1 : Lambda L) = -elemSymm L 1 := by
    rw [bop_natCast_one]; norm_num
  rw [zDefect_one_of_table, hb0, map_neg, map_neg, dplusStar_C_elemSymm_one_expand]
  simp only [smul_eq_scal_mul, scal, map_sub, map_mul, map_one]
  ring

/-- **Check:** the earlier `HJO.Sweep.zDefect_two_one`, re-derived through the vacuum row and
`HJO.Sweep.dplusStar_C_elemSymm_two_expand`. The alternating signs of the letter's powers are what
this pins. -/
theorem zDefect_two_one_of_table (q u : L) :
    zDefect q u 2 (1 : Sym.Lambda L)
      = scal ((q - 1) * u) * ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))
        - scal ((q - 1) * u ^ 2) * (auxVar 1 : Total L) ^ 2 := by
  rw [zDefect_one_of_table, bop_two_one, dplusStar_C_elemSymm_two_expand]
  simp only [smul_eq_scal_mul, scal, map_sub, map_mul, map_one, map_pow]
  ring

/-- **Check:** the earlier `HJO.Sweep.zDefect_three_one`, re-derived through the vacuum row.
Three powers of the letter, signs `-, +, -`. -/
theorem zDefect_three_one_of_table (q u : L) :
    zDefect q u 3 (1 : Sym.Lambda L)
      = -(scal ((q - 1) * u) * ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 2)))
        + scal ((q - 1) * u ^ 2)
            * ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (Sym.elemSymm L 1))
        - scal ((q - 1) * u ^ 3) * (auxVar 1 : Total L) ^ 3 := by
  rw [zDefect_one_of_table, bop_three_one', map_neg, map_neg,
    dplusStar_C_elemSymm_three_expand]
  simp only [smul_eq_scal_mul, scal, map_sub, map_mul, map_one, map_pow]
  ring

/-- **Check**, the sharp one: the earlier `HJO.Sweep.zDefect_one_elemSymm_one`, whose value is a
**single** monomial because the two `y_1^2e_1`-terms of the two halves annihilate. Re-derived
through `HJO.Sweep.zDefect_elemSymm_one_expand`. A wrong binomial in
`HJO.Sweep.dplusStar_C_elemSymm_one_sq_expand` would leave that term behind. -/
theorem zDefect_one_elemSymm_one_of_table (q u : L) :
    zDefect q u 1 (Sym.elemSymm L 1)
      = -(scal (q * (q - 1) * u)
          * ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))) := by
  have hb0 : Bop q ((1 : ℕ) : ℤ) (1 : Lambda L) = -elemSymm L 1 := by
    rw [bop_natCast_one]; norm_num
  rw [zDefect_elemSymm_one_expand, bop_one_elemSymm_one', hb0]
  simp only [map_add, map_neg, C_smul, map_smul, dplusStar_C_elemSymm_one_sq_expand,
    dplusStar_C_elemSymm_two_expand]
  simp only [smul_eq_scal_mul, scal, map_sub, 
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- **Check:** the earlier `HJO.Sweep.zDefect_two_elemSymm_one`, re-derived through
`HJO.Sweep.zDefect_elemSymm_one_expand` at `r = 2`. Its `(q-1)^2` coefficient is produced here as
`(q-1)q - (q-1)`, so the check tests the table's arithmetic and not just its shape. -/
theorem zDefect_two_elemSymm_one_of_table (q u : L) :
    zDefect q u 2 (Sym.elemSymm L 1)
      = scal ((q - 1) * u)
            * ((auxVar 1 : Total L) * (MvPolynomial.C (Sym.elemSymm L 1)
              * MvPolynomial.C (Sym.elemSymm L 1)))
        + scal ((q - 1) ^ 2 * u)
            * ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 2))
        - scal ((q - 1) * u ^ 2)
            * ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (Sym.elemSymm L 1)) := by
  rw [zDefect_elemSymm_one_expand, bop_two_elemSymm_one', bop_two_one]
  simp only [map_sub, C_smul, map_smul,
    dplusStar_C_elemSymm_one_mul_two_expand, dplusStar_C_elemSymm_three_expand,
]
  simp only [smul_eq_scal_mul, scal, map_sub, map_neg,
    map_mul, map_one, map_pow]
  ring

/-! ### The checks are the same `Prop`s as the earlier entries -/

/-- The check and the earlier entry are the same `Prop`, by `rfl`. -/
theorem zDefect_one_one_of_table_eq (q u : L) :
    zDefect_one_one_of_table (L := L) q u = zDefect_one_one (L := L) q u := rfl

/-- The check and the earlier entry are the same `Prop`, by `rfl`. -/
theorem zDefect_two_one_of_table_eq (q u : L) :
    zDefect_two_one_of_table (L := L) q u = zDefect_two_one (L := L) q u := rfl

/-- The check and the earlier entry are the same `Prop`, by `rfl`. -/
theorem zDefect_three_one_of_table_eq (q u : L) :
    zDefect_three_one_of_table (L := L) q u = zDefect_three_one (L := L) q u := rfl

/-- The check and the earlier entry are the same `Prop`, by `rfl`. -/
theorem zDefect_one_elemSymm_one_of_table_eq (q u : L) :
    zDefect_one_elemSymm_one_of_table (L := L) q u
      = zDefect_one_elemSymm_one (L := L) q u := rfl

/-- The check and the earlier entry are the same `Prop`, by `rfl`. -/
theorem zDefect_two_elemSymm_one_of_table_eq (q u : L) :
    zDefect_two_elemSymm_one_of_table (L := L) q u
      = zDefect_two_elemSymm_one (L := L) q u := rfl

/-! ### The first consumer: the vector the `B`-recursion carries at its first step -/

/-- **The single `z` letter on the `[1,1]` stage word, as five defects.**

`HJO.Sweep.zCommTwo_monomial'` at each of the five monomials of
`HJO.Sweep.stageWordTotal_two_three_one_one`: the `y_1`-exponent becomes a spectator power of `y_2`
and the `y_2`-exponent becomes the index of the defect. **Three of the five are exactly the entries
above** and the other two were proved earlier.

`q ≠ 0`, `u ≠ 0`, `q ≠ 1` are those of the `[1,1]` value and of nothing else — there the `(qu)^{-1}`
of `HJO.Sweep.slopeOperator` and the `q^2/(1-q)` of `HJO.Sweep.zop` are zero maps at `qu = 0` and
`q = 1`. -/
theorem zCommTwo_stageWordTotal_two_three_one_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    zCommTwo q u (Mellit.stageWordTotal q u 2 3 [1, 1])
      = q • ((auxVar 2 : Total L) ^ 2 * zDefect q u 2 (elemSymm L 1 * elemSymm L 1))
        + (q * (q - 1)) • ((auxVar 2 : Total L) ^ 2 * zDefect q u 2 (elemSymm L 2))
        - (q * u) • ((auxVar 2 : Total L) ^ 3 * zDefect q u 2 (elemSymm L 1))
        - (q * u) • ((auxVar 2 : Total L) ^ 2 * zDefect q u 3 (elemSymm L 1))
        + (q * u ^ 2) • ((auxVar 2 : Total L) ^ 3 * zDefect q u 3 (1 : Lambda L)) := by
  rw [stageWordTotal_two_three_one_one hq0 hu0 hq1,
    show ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3)
      = MvPolynomial.C (1 : Lambda L)
        * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3) from by rw [map_one, one_mul]]
  simp only [map_add, map_sub, map_smul, zCommTwo_monomial']

/-- **`z_1^{(2)}` on the `[1,1]` stage word**, `HJO.Sweep.zopOneStar_two_eq` with the train
letter deleted by `HJO.Sweep.braidInvEnd_one_stageWordTotal_two_three_one_one` — the word is
`s_1`-symmetric, so `T_1^{-1}` fixes it. Same three hypotheses, all those of the `[1,1]` value. -/
theorem zopOneStar_two_stageWordTotal_two_three_one_one (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    zopOneStar q u 2 (Mellit.stageWordTotal q u 2 3 [1, 1])
      = (q ^ 2 / (1 - q)) •
          (q • ((auxVar 2 : Total L) ^ 2 * zDefect q u 2 (elemSymm L 1 * elemSymm L 1))
            + (q * (q - 1)) • ((auxVar 2 : Total L) ^ 2 * zDefect q u 2 (elemSymm L 2))
            - (q * u) • ((auxVar 2 : Total L) ^ 3 * zDefect q u 2 (elemSymm L 1))
            - (q * u) • ((auxVar 2 : Total L) ^ 2 * zDefect q u 3 (elemSymm L 1))
            + (q * u ^ 2) • ((auxVar 2 : Total L) ^ 3 * zDefect q u 3 (1 : Lambda L))) := by
  rw [zopOneStar_two_eq]
  simp only [LinearMap.smul_apply, Module.End.mul_apply]
  rw [braidInvEnd_one_stageWordTotal_two_three_one_one hq0 hu0 hq1,
    zCommTwo_stageWordTotal_two_three_one_one hq0 hu0 hq1]

/-- The ten-monomial element of `V_2` that `zCommTwo` returns on the `[1,1]` stage word. -/
noncomputable def zCommValueOneOne (q u : L) : Total L :=
  (q * (q - 1) * u) • ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2
        * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
    + (2 * q * (q - 1) ^ 2 * u + q ^ 2 * (q - 1) ^ 2 * u + q * (q - 1) * u ^ 2) •
        ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2
          * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
    + (q * (q - 1) ^ 3 * u + q ^ 2 * (q - 1) ^ 3 * u + q * (q - 1) ^ 2 * u ^ 2) •
        ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 3))
    + (-(q * (q - 1) * u ^ 2) - q * (q - 1) * u ^ 3) •
        ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
          * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
    + (q * (q - 1) ^ 3 * u ^ 2 - q ^ 2 * (q - 1) ^ 2 * u ^ 2) •
        ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
          * MvPolynomial.C (elemSymm L 2))
    + (q * (q - 1) * u ^ 4) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2
          * MvPolynomial.C (elemSymm L 1))
    + (-(q * (q - 1) * u ^ 2)) • ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 3
          * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
    + (-(q * (q - 1) ^ 2 * u ^ 2) - q * (q - 1) * u ^ 3) •
        ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))
    + (q * (q - 1) * u ^ 3 + q * (q - 1) * u ^ 4) •
        ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3
          * MvPolynomial.C (elemSymm L 1))
    + (-(q * (q - 1) * u ^ 5)) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3
          * MvPolynomial.C (1 : Lambda L))

/-- **The value: `HJO.Sweep.zCommValueOneOne`, ten monomials.** The five defects of
`HJO.Sweep.zCommTwo_stageWordTotal_two_three_one_one` substituted from the table. This is the
consistency check on the three new entries at a real vector: a wrong coefficient in any of them,
or a misread index, would not collect into ten monomials of the stated weights. -/
theorem zCommTwo_stageWordTotal_two_three_one_one_expand (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    zCommTwo q u (Mellit.stageWordTotal q u 2 3 [1, 1]) = zCommValueOneOne q u := by
  rw [zCommTwo_stageWordTotal_two_three_one_one hq0 hu0 hq1, zDefect_two_elemSymm_one_sq,
    zDefect_two_elemSymm_two, zDefect_two_elemSymm_one, zDefect_three_elemSymm_one,
    zDefect_three_one, zCommValueOneOne]
  simp only [smul_eq_scal_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- `z_1^{(2)}` on the `[1,1]` stage word as an explicit element of `V_2`, up to the scalar
`q^2/(1-q)` of `HJO.Sweep.zop` which is carried symbolically. -/
theorem zopOneStar_two_stageWordTotal_two_three_one_one_eq_value (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    zopOneStar q u 2 (Mellit.stageWordTotal q u 2 3 [1, 1])
      = (q ^ 2 / (1 - q)) • zCommValueOneOne q u := by
  rw [zopOneStar_two_eq]
  simp only [LinearMap.smul_apply, Module.End.mul_apply]
  rw [braidInvEnd_one_stageWordTotal_two_three_one_one hq0 hu0 hq1,
    zCommTwo_stageWordTotal_two_three_one_one_expand hq0 hu0 hq1]

/-- `HJO.Sweep.pairArgSucc q u 1 0` with its inner `z` letter evaluated: `T_1^{-1}` on an
explicit element of `V_2`. The outer letter is removed just below. -/
theorem pairArgSucc_one_zero_eq_value (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    pairArgSucc q u 1 0
      = braidInvEnd q 1 ((auxVar 1 : Total L) ^ 2
          * ((q ^ 2 / (1 - q)) • zCommValueOneOne q u)) := by
  rw [pairArgSucc_one_zero hq0 hu0 hq1,
    zopOneStar_two_stageWordTotal_two_three_one_one_eq_value hq0 hu0 hq1]

/-! ### The offset-three block -/

omit [Algebra ℚ L] in
/-- `pairBlock i (b+3) b = -y_i^by_{i+1}^b(y_i^2 + y_iy_{i+1} + y_{i+1}^2)`: the offset-three
block, the one the earlier entries stopped short of. Proved straight off the definition, so it
holds at every index including `0`, and unconditionally in `q`. -/
theorem pairBlock_add_three_self (i b : ℕ) :
    pairBlock L i (b + 3) b
      = -((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b
          * ((auxVar i : Total L) ^ 2 + (auxVar i : Total L) * (auxVar (i + 1) : Total L)
            + (auxVar (i + 1) : Total L) ^ 2)) := by
  rw [pairBlock, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    show b + 3 + b - 1 - b = b + 2 from by omega,
    show b + 3 + b - 1 - (b + 1) = b + 1 from by omega,
    show b + 3 + b - 1 - (b + 2) = b from by omega]
  ring

/-! ### `T_1^{-1}` at the five monomials of `y_1^2·zCommValueOneOne` -/

omit [Algebra ℚ L] in
/-- `T_1^{-1}(y_1^4y_2^2) = q^{-1}(y_1^2y_2^4 - (q-1)y_1^3y_2^3)`, off the general pair formula
with `HJO.Sweep.pairBlock_add_two_self`. **Hypothesis-free**: the `q^{-1}` is the symbolic one
`HJO.Sweep.braidInv` carries, so at `q = 0` both sides are `0`. -/
theorem braidInvEnd_one_pow_four_sq (q : L) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2)
      = scal q⁻¹ * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 4
          - scal (q - 1) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3)) := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, braidInvEnd_one_auxVar_pow_mul_auxVar_pow_pair q (2 + 2) 2,
    pairBlock_add_two_self]
  ring

omit [Algebra ℚ L] in
/-- `T_1^{-1}(y_1^5y_2^2) = q^{-1}(y_1^2y_2^5 - (q-1)(y_1^4y_2^3 + y_1^3y_2^4))`, off
`HJO.Sweep.pairBlock_add_three_self`. **Hypothesis-free.** -/
theorem braidInvEnd_one_pow_five_sq (q : L) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 5 * (auxVar 2 : Total L) ^ 2)
      = scal q⁻¹ * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 5
          - scal (q - 1) * ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 3
              + (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 4)) := by
  rw [show (5 : ℕ) = 2 + 3 from rfl, braidInvEnd_one_auxVar_pow_mul_auxVar_pow_pair q (2 + 3) 2,
    pairBlock_add_three_self]
  ring

omit [Algebra ℚ L] in
/-- `T_1^{-1}` fixes `y_1^3y_2^3`: the block vanishes on a symmetric pair. This is the one of
the five that genuinely spends `q ≠ 0`, on the `q^{-1}·q` that clears the monomial — showing
that the hypothesis belongs to the cancellation, not to the evaluation. -/
theorem braidInvEnd_one_cube_cube (hq0 : q ≠ 0) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3)
      = (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3 := by
  have h := braidInv_auxVar_pow_mul_auxVar_pow_self_of_pair (L := L) hq0 (i := 1) le_rfl 3
  rwa [show (1 : ℕ) + 1 = 2 from rfl] at h

omit [Algebra ℚ L] in
/-- `T_1^{-1}(y_1^4y_2^3) = q^{-1}y_1^3y_2^4`: at offset one the `(q-1)`-term is annihilated by
the block exactly and a bare monomial survives. **Hypothesis-free.** -/
theorem braidInvEnd_one_pow_four_cube (q : L) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 3)
      = scal q⁻¹ * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 4) := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, braidInvEnd_one_auxVar_pow_mul_auxVar_pow_pair q (3 + 1) 3,
    pairBlock_succ_self]
  ring

omit [Algebra ℚ L] in
/-- `T_1^{-1}(y_1^5y_2^3) = q^{-1}(y_1^3y_2^5 - (q-1)y_1^4y_2^4)`. **Hypothesis-free.** -/
theorem braidInvEnd_one_pow_five_cube (q : L) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 5 * (auxVar 2 : Total L) ^ 3)
      = scal q⁻¹ * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 5
          - scal (q - 1) * ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 4)) := by
  rw [show (5 : ℕ) = 3 + 2 from rfl, braidInvEnd_one_auxVar_pow_mul_auxVar_pow_pair q (3 + 2) 3,
    pairBlock_add_two_self]
  ring

/-! ### The step vector of the `B`-recursion at its first step, with every operator gone -/

/-- The twelve-monomial element of `V_2` that `T_1^{-1}(y_1^2·zCommValueOneOne)` is. -/
noncomputable def pairArgSuccValueOneZero (q u : L) : Total L :=
  (q * (q - 1) * u) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3
        * MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1)))
    + (q * (q - 1) * u * (q ^ 2 + q - 2 + u)) • ((auxVar 1 : Total L) ^ 2
        * (auxVar 2 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 2))
    + (q * (q - 1) ^ 2 * u * (q ^ 2 - 1 + u)) • ((auxVar 1 : Total L) ^ 2
        * (auxVar 2 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 3))
    + (-(q * (q - 1) * u ^ 2 * (1 + u))) • ((auxVar 1 : Total L) ^ 2
        * (auxVar 2 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
    + (-(q * (q - 1) ^ 2 * u ^ 2)) • ((auxVar 1 : Total L) ^ 2
        * (auxVar 2 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 2))
    + (q * (q - 1) * u ^ 2 * (q * u - u - 1)) • ((auxVar 1 : Total L) ^ 3
        * (auxVar 2 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
    + (q * (q - 1) * u ^ 2 * (1 - q - q * u)) • ((auxVar 1 : Total L) ^ 3
        * (auxVar 2 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 2))
    + (q * (q - 1) * u ^ 4) • ((auxVar 1 : Total L) ^ 2
        * (auxVar 2 : Total L) ^ 5 * MvPolynomial.C (elemSymm L 1))
    + (-(q * (q - 1) ^ 2 * u ^ 4)) • ((auxVar 1 : Total L) ^ 4
        * (auxVar 2 : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1))
    + (q * (q - 1) * u ^ 3 * (1 + 2 * u - q * u)) • ((auxVar 1 : Total L) ^ 3
        * (auxVar 2 : Total L) ^ 4 * MvPolynomial.C (elemSymm L 1))
    + (-(q * (q - 1) * u ^ 5)) • ((auxVar 1 : Total L) ^ 3
        * (auxVar 2 : Total L) ^ 5 * MvPolynomial.C (1 : Lambda L))
    + (q * (q - 1) ^ 2 * u ^ 5) • ((auxVar 1 : Total L) ^ 4
        * (auxVar 2 : Total L) ^ 4 * MvPolynomial.C (1 : Lambda L))

/-- **The outer `T_1^{-1}` on `y_1^2·HJO.Sweep.zCommValueOneOne`, evaluated.**

Ten monomials in, twelve out: the five `T_1^{-1}`-values above applied termwise through
`HJO.Sweep.braidInvEnd_C_mul`, then collected. The two monomials `y_1^3y_2^3` and `y_1^2y_2^4` of
the input meet each other's images, which is where the coefficients `qu - u - 1` and `1 - q - qu`
of `HJO.Sweep.pairArgSuccValueOneZero` come from.

**Unconditional**: the `q^{-1}` of the train is kept on the left as a symbolic scalar and nothing is
cancelled against it. -/
theorem braidInvEnd_one_auxVar_sq_mul_zCommValueOneOne (q u : L) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 2 * zCommValueOneOne q u)
      = q⁻¹ • pairArgSuccValueOneZero q u := by
  have hrw : (auxVar 1 : Total L) ^ 2 * zCommValueOneOne q u
      = scal (q * (q - 1) * u)
            * (MvPolynomial.C (elemSymm L 1 * (elemSymm L 1 * elemSymm L 1))
              * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
        + scal (2 * q * (q - 1) ^ 2 * u + q ^ 2 * (q - 1) ^ 2 * u + q * (q - 1) * u ^ 2)
            * (MvPolynomial.C (elemSymm L 1 * elemSymm L 2)
              * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
        + scal (q * (q - 1) ^ 3 * u + q ^ 2 * (q - 1) ^ 3 * u + q * (q - 1) ^ 2 * u ^ 2)
            * (MvPolynomial.C (elemSymm L 3)
              * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
        + scal (-(q * (q - 1) * u ^ 2) - q * (q - 1) * u ^ 3)
            * (MvPolynomial.C (elemSymm L 1 * elemSymm L 1)
              * ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2))
        + scal (q * (q - 1) ^ 3 * u ^ 2 - q ^ 2 * (q - 1) ^ 2 * u ^ 2)
            * (MvPolynomial.C (elemSymm L 2)
              * ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 2))
        + scal (q * (q - 1) * u ^ 4)
            * (MvPolynomial.C (elemSymm L 1)
              * ((auxVar 1 : Total L) ^ 5 * (auxVar 2 : Total L) ^ 2))
        + scal (-(q * (q - 1) * u ^ 2))
            * (MvPolynomial.C (elemSymm L 1 * elemSymm L 1)
              * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3))
        + scal (-(q * (q - 1) ^ 2 * u ^ 2) - q * (q - 1) * u ^ 3)
            * (MvPolynomial.C (elemSymm L 2)
              * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3))
        + scal (q * (q - 1) * u ^ 3 + q * (q - 1) * u ^ 4)
            * (MvPolynomial.C (elemSymm L 1)
              * ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 3))
        + scal (-(q * (q - 1) * u ^ 5))
            * (MvPolynomial.C (1 : Lambda L)
              * ((auxVar 1 : Total L) ^ 5 * (auxVar 2 : Total L) ^ 3)) := by
    rw [zCommValueOneOne]
    simp only [smul_eq_scal_mul]
    ring
  rw [hrw, pairArgSuccValueOneZero]
  simp only [map_add, braidInvEnd_scal_mul, braidInvEnd_C_mul,
    braidInvEnd_one_cube_sq, braidInvEnd_one_pow_four_sq, braidInvEnd_one_pow_five_sq,
    braidInvEnd_one_pow_four_cube, braidInvEnd_one_pow_five_cube]
  rw [braidInvEnd_one_auxVar_pow_mul_auxVar_pow_pair q 3 3, pairBlock_self]
  simp only [smul_eq_scal_mul, scal, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- **`HJO.Sweep.pairArgSucc q u 1 0` as an explicit element of `V_2`: no operator of the sweep and
no braid letter survives.** -/
theorem pairArgSucc_one_zero_expand (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    pairArgSucc q u 1 0 = (q / (1 - q)) • pairArgSuccValueOneZero q u := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [pairArgSucc_one_zero_eq_value hq0 hu0 hq1, mul_smul_comm, map_smul,
    braidInvEnd_one_auxVar_sq_mul_zCommValueOneOne, smul_smul,
    show q ^ 2 / (1 - q) * q⁻¹ = q / (1 - q) from by field_simp]

end HJO.Sweep

end
