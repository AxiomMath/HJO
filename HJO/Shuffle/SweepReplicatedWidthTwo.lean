/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitLhsOnePartReplication

/-! # The replicated letter at `(2,3)` on the grading `0` is a word of width `≤ 2`

`HJO.Mellit.lhsAt_two_three_singleton_iff` reduces the `hlhs` clause at a one-part composition
`[A]` and `(a,b) = (2,3)` to one identity whose sweep half is
`ct(d_-^{(1)}((Z^{(1)}_{2,3})^{A-1}(-e_1y_1^2 + uy_1^3)))`. Its companion
`HJO.Mellit.stageWordTotal_singleton_mem_piece` records that the whole family stays in `V_1`, and
its docstring reads off from the definitions that the operator being iterated "reads `d_-` and
`d^*_+` at the indices `1` and `2` and no higher".

**This file turns that reading into a theorem.** `HJO.Sweep.replicatedTotal_two_three_zero_eq` is a
single equation exhibiting `Z^{(1)}_{2,3}` as an explicit word in

* `HJO.Sweep.dplusStar` at the indices `0` and `1`,
* `HJO.Sweep.dminus` at the indices `1` and `2`,
* multiplication by `y_1` and by `y_1^2`,

with no braid letter, no train, no slope operator and no `HJO.Sweep.zop` left in it — so the
largest index any factor carries is `2`, and that is now checked by the kernel rather than read off
by eye. `HJO.Sweep.lhsAt_two_three_singleton_iff_width` states the clause at `[A]` against that
word.

## Where the letters go

Three collapses do the work and each is already proved:

* `HJO.Mellit.replicatedTotal_zero` empties both conjugating trains of `HJO.Mellit.replicatedLetter`
  at the grading `0`, leaving `HJO.Mellit.replTwoTotal`;
* `HJO.Sweep.slopeOperator_two_three` reads `β_{2,3} = yzy`
  (`HJO.Mellit.slopeWord_two_three`) as `(-y_1)·(qu)^{-1}z_1·(-y_1)`, so the whole slope operator is
  two multiplications by `y_1` around one `z_1`;
* `HJO.Braid.trainUp_self` empties the train inside `HJO.Sweep.zop` at `k = 1`, which is what
  `HJO.Sweep.zopOneStar_one_eq` records.

The three signs — the `(-1)^{a-1}` of `HJO.Mellit.euclid` at `a = 2`, the `-y_1d^*_+`, and the two
`-y_1` of the slope word — multiply to `+1`, which is why the word below carries none.

## Genericity

`HJO.Sweep.zopOneStar_one_eq`, `HJO.Sweep.replicatedTotal_two_three_zero_eq` and their applied
forms: **none**. They are rewritings of one operator into another and hold at every `q` and `u`,
including the degenerate ones, where both sides become the zero map together: at `q = 0` and at
`u = 0` through the `(qu)^{-1}` the slope word carries, and at `q = 1` through the `q/(1-q)` of
`HJO.Sweep.zop`. That is exactly why they settle nothing by themselves and why the clause
restatement below still carries `q ≠ 0`, `u ≠ 0`, `q ≠ 1`.

`HJO.Sweep.lhsAt_two_three_singleton_iff_width`: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, all three inherited
verbatim from `HJO.Mellit.lhsAt_two_three_singleton_iff`. Each is the inverse-becomes-zero hazard
and not bookkeeping — in a field `0⁻¹ = 0`, so at `q = 0` or `u = 0` the letter `(qu)^{-1}z_1` is
the zero map and at `q = 1` the scalar `q/(1-q)` is undefined, and a clause asserting otherwise
there would be false rather than vacuous.

## References

This file works with `HJO.Mellit.replicatedLetter`, `HJO.Sweep.zop`, `HJO.Sweep.slopeOperator`,
`HJO.Braid.slopeBraid`, `HJO.Sweep.dplusStar`, `HJO.Sweep.dminus` and `HJO.Mellit.euclid`,
towards `HJO.Mellit.lhsRewrite_sweepWitness`.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym HJO.Mellit

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### `z_1` at the grading `1`, with the train gone -/

/-- **`z_1^{(1)} = \frac{q}{1-q}(d^{*(0)}_+d_-^{(1)} - d_-^{(2)}d^{*(1)}_+)`.** The train
`T^*_{1↘1}` of `HJO.Sweep.zop` is the empty word at `k = 1` (`HJO.Braid.trainUp_self`), so the only
operators left are `d^*_+` at the indices `0` and `1` and `d_-` at the indices `1` and `2`.

Unconditional: at `q = 1` both sides are the zero map, the scalar `q^k/(1-q)` of `HJO.Sweep.zop`
collapsing on each. -/
theorem zopOneStar_one_eq (q u : L) :
    zopOneStar q u 1
      = (q / (1 - q)) • (dplusStar q u 0 * dminus q 1 - dminus q 2 * dplusStar q u 1) := by
  rw [zopOneStar, show trainUpEnd q 1 1 = 1 from Braid.trainUp_self _ _ 1, mul_one, pow_one,
    Nat.sub_self]

/-- **`z_1^{(1)}` on an element**, the applied form of `HJO.Sweep.zopOneStar_one_eq`. -/
theorem zopOneStar_one_apply (q u : L) (F : Total L) :
    zopOneStar q u 1 F
      = (q / (1 - q)) • (dplusStar q u 0 (dminus q 1 F) - dminus q 2 (dplusStar q u 1 F)) := by
  rw [zopOneStar_one_eq]
  rfl

/-! ### The replicated letter at `(2,3)` on the grading `0` -/

/-- **`Z^{(1)}_{2,3} = (qu)^{-1}·y_1·z_1^{(1)}·y_1^2·z_1^{(1)}`.** Both conjugating trains of
`HJO.Mellit.replicatedLetter` are empty at the grading `0` (`HJO.Mellit.replicatedTotal_zero`) and
the slope word `β_{2,3} = yzy` is two multiplications by `-y_1` around one `(qu)^{-1}z_1`
(`HJO.Sweep.slopeOperator_two_three`). The three signs of `HJO.Mellit.replTwoTotal` at `a = 2` —
the `(-1)^{a-1}`, the `-y_1z_1` and the two `-y_1` of the word — cancel.

Unconditional. -/
theorem replicatedTotal_two_three_zero_eq (q u : L) :
    replicatedTotal q u 2 3 0
      = (q * u)⁻¹ • (LinearMap.mulLeft L (auxVar 1 : Total L) * zopOneStar q u 1 *
          LinearMap.mulLeft L ((auxVar 1 : Total L) ^ 2) * zopOneStar q u 1) := by
  refine LinearMap.ext fun F => ?_
  rw [replicatedTotal_zero, replTwoTotal, slopeOperator_two_three, zop_one]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.mulLeft_apply, neg_neg, mul_neg,
    neg_mul, smul_neg, neg_smul, Nat.add_one_sub_one, Nat.zero_add, pow_one, mul_smul_comm, sq,
    one_smul, mul_assoc]

/-- **`Z^{(1)}_{2,3}` on an element.** -/
theorem replicatedTotal_two_three_zero_apply (q u : L) (F : Total L) :
    replicatedTotal q u 2 3 0 F
      = (q * u)⁻¹ • ((auxVar 1 : Total L) *
          zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F)) := by
  rw [replicatedTotal_two_three_zero_eq]
  rfl

/-- **The width bound, as one equation.** `Z^{(1)}_{2,3}` is a word in `d^*_+` at the indices `0`
and `1`, `d_-` at the indices `1` and `2`, and multiplication by `y_1` and `y_1^2`. No factor
carries an index above `2`, and nothing of the braid representation, the trains, the slope operator
or `HJO.Sweep.zop` survives on the right.

Together with `HJO.Mellit.stageWordTotal_singleton_mem_piece` — the whole one-part family stays in
`V_1` — this is what makes evaluating the sweep side of the `hlhs` clause at *every* one-part
composition a width-`≤ 2` computation: the statement that the machinery of `V_3` and `V_4` is not
needed is now a theorem rather than a reading of the definitions.

Unconditional. -/
theorem replicatedTotal_two_three_zero_eq_width_two (q u : L) :
    replicatedTotal q u 2 3 0
      = ((q * u)⁻¹ * (q / (1 - q)) ^ 2) •
          (LinearMap.mulLeft L (auxVar 1 : Total L)
            * (dplusStar q u 0 * dminus q 1 - dminus q 2 * dplusStar q u 1)
            * LinearMap.mulLeft L ((auxVar 1 : Total L) ^ 2)
            * (dplusStar q u 0 * dminus q 1 - dminus q 2 * dplusStar q u 1)) := by
  rw [replicatedTotal_two_three_zero_eq, zopOneStar_one_eq]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [sq]
  ring_nf

/-! ### The clause at a one-part composition, against the width-`≤ 2` word -/

/-- **`HJO.Mellit.LhsAt` at `(a,b) = (2,3)` and a one-part composition `[A]`, with the sweep side a
power of one width-`≤ 2` word on one explicit polynomial.**

`HJO.Mellit.lhsAt_two_three_singleton_iff` with
`HJO.Sweep.replicatedTotal_two_three_zero_eq_width_two` substituted: the creation half is
`Θ(h_A)(1)` and the sweep half mentions only `d^*_+` at the indices `0` and `1`, `d_-` at the
indices `1` and `2`, and multiplication by `y_1`.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, all three
`HJO.Mellit.lhsAt_two_three_singleton_iff`'s own. -/
theorem lhsAt_two_three_singleton_iff_width (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (A : ℕ)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) :
    LhsAt q u 2 3 Θ [A] ↔
      Θ (completeHomog L A) 1
        = -MvPolynomial.constantCoeff (dminus q 1
            (((((q * u)⁻¹ * (q / (1 - q)) ^ 2) •
                (LinearMap.mulLeft L (auxVar 1 : Total L)
                  * (dplusStar q u 0 * dminus q 1 - dminus q 2 * dplusStar q u 1)
                  * LinearMap.mulLeft L ((auxVar 1 : Total L) ^ 2)
                  * (dplusStar q u 0 * dminus q 1 - dminus q 2 * dplusStar q u 1))) ^ (A - 1))
              (-(MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2)
                + u • (auxVar 1 : Total L) ^ 3))) := by
  rw [lhsAt_two_three_singleton_iff hq0 hu0 hq1, replicatedTotal_two_three_zero_eq_width_two]

end HJO.Sweep
