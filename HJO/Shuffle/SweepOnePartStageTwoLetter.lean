/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepOnePartStageTwoZ

/-! # The `z` letter on the one-part stage word at `[2]`, and the value `V_3`

`HJO/Shuffle/SweepOnePartDefectValues.lean` closed the one-part sweep step into
`HJO.Mellit.smul_onePartSweepValue_succ_of_letter`:

  `qu(1-q)^2·V_{A+2} = -(1-q)^2·x_{A+1}`,  `x_A = HJO.Mellit.onePartOuterValue q u A`,

and recorded that `x_2`, `w_2 = HJO.Mellit.onePartInnerValue q u 2`, `Δ¹_2` and `V_3` all wait on
**one** computation: `z_1` applied once more to the eleven-monomial one-part stage word
`HJO.Mellit.stageWordTotal q u 2 3 [2]`. **This file and the four before it do that computation
and the one after it**: the Hall--Littlewood table
(`HJO/Shuffle/SweepOnePartStageTwoTable.lean`), the `z_1` values at weight six and eight
(`HJO/Shuffle/SweepOnePartZOneWeightSix.lean`,
`HJO/Shuffle/SweepOnePartZOneWeightEight.lean`), the stage word `G_3`
(`HJO/Shuffle/SweepOnePartStageTwoZ.lean`), and here the value `V_3` read off it. They form one
computation, split along those lines because together they are far longer than a file should be.
Everything below is a value, with one exception labelled as such: the last declaration,
`HJO.Mellit.lhsAt_two_three_three_of_creation`, is an *implication* naming what the creation side
still owes. **Nothing here is an equivalence.**

## The route

`HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C` evaluates `z_1` on one monomial of `V_1`,

  `z_1(y_1^mCA) = q/(1-q)·(d^*_+{}^{(0)}(C(B_mA)) - B_m(d^*_+{}^{(0)}(CA)))`,

the second `B_m` coefficientwise in `y_1` (`HJO.Sweep.bopExt`). In every one of the twenty-nine
monomial values of the two `z_1` files the bracket is divisible by `1 - q`, so the value is `q`
times a polynomial — that is where `q ≠ 1` is spent and why no denominator survives. The first half
needs `d^*_+` at `e_n` up to `n = 8` (`HJO.Sweep.dplusStar_C_elemSymm_six`, `_seven`, `_eight`)
and the Hall--Littlewood value `B_mA` at weight up to nine; the second needs `d^*_+(CA)` in the
graded form `∑_j x_jy_1^jCf_j` that `HJO.Sweep.bopExt` reads, which is the seven
`HJO.Sweep.dplusStar_C_elemSymm_*_expand` rows.

The `B`-side is the Pieri rules `HJO.Sym.bop_elemSymm_one_mul`, `_two_mul`, `_three_mul`,
`_four_mul` — each holding at **every** index — run down to the vacuum `B_k(1) = (-1)^ke_k`
(`HJO.Sym.bop_natCast_one`), with the nine new base rows `B_m(e_n)` at `n ≥ 5` and at the indices
past the existing table. Those are the only rows the Pieri rules cannot reach, because they strip a
leading `e_n` only for `n ≤ 4`; the one composite row the existing table lacked,
`HJO.Sym.bop_two_elemSymm_one_cube`, is the Pieri rule itself.

The last step, `ct(d_-^{(1)}G_3)`, reads `B_j` at each of the forty-two `y_1`-coefficients of `G_3`,
and those thirty-five composite values are written out as a **weight-nine table**
(`HJO.Sym.bop_two_elemSymm_one_mul_six` and its thirty-four companions), each a Pieri reduction of
its own. With the table explicit, `module` proves the value: the twenty-six `e`-monomials of weight
nine are atoms and only their scalars are normalised. That normalisation — about two hundred and
fifty products of a `G_3` coefficient with a table scalar — is the largest single computation of
the one-part family, and the one declaration here that takes longer to check than the rest.

## What is proved

The first five are in `HJO/Shuffle/SweepOnePartStageTwoZ.lean`, the last three here.

* `HJO.Mellit.zopOneStar_one_stageWordTotal_two_three_two` — **`z_1(G_2)`**, eighteen monomials
  over the `y_1`-degrees `1` to `6`, common factor `q^2u^2`, homogeneous of total weight six. This
  is the single object the file's docstring in `SweepOnePartDefectValues.lean` named as missing.
* `HJO.Mellit.auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_two` — `y_1^2z_1(G_2)`, the
  vector `H_2` that `HJO.Mellit.onePartInnerValue` projects.
* `HJO.Mellit.onePartInnerValue_two` — **`w_2`**, sixteen `e`-monomials of weight eight,
  coefficients of `(q,u)`-degree up to sixteen.
* `HJO.Mellit.zopOneStar_one_auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_two` — the outer
  `z_1`, forty-two monomials over the `y_1`-degrees `1` to `8`, common factor `q^3u^3`.
* `HJO.Mellit.stageWordTotal_two_three_three_eq` — **`G_3`**, the one-part stage word at `[3]`:
  forty-two monomials over the `y_1`-degrees `2` to `9`, common factor `q^2u^2`.
* `HJO.Mellit.onePartSweepValue_three_eq` — **`V_3` in the `e`-basis**: twenty-six `e`-monomials of
  weight nine, coefficients of `q`-degree up to twenty-one and total degree twenty-three. The
  value that decides `A = 3` for the one-part family.
* `HJO.Mellit.onePartOuterValue_two` — **`x_2 = -quV_3`**, off
  `HJO.Mellit.smul_onePartSweepValue_succ_of_letter` at `A = 1`. The last datum the outer defect of
  the one-part step carried.
* `HJO.Mellit.lhsAt_two_three_three_of_creation` — the residual at `[3]` named exactly: an
  *implication*, not a decision. The clause holds as soon as `Θ(h_3)(1)` is the explicit element
  above, and nothing here evaluates `Θ(h_3)(1)`.

## The consistency check

`HJO.Sym.bop_hmz_two_seven_of_table` and `HJO.Sym.bop_hmz_two_seven_of_hmz` are **the same
`Prop`**, witnessed by `HJO.Sym.bop_hmz_two_seven_eq : ... = ... := rfl`, which typechecks only if
the two statements are literally identical. The `Prop` is the Haglund--Morse--Zabrocki relation
`HJO.Sym.bop_pair_antisymm_apply` at `(m, n) = (2, 7)` on the vacuum,

  `B_2(B_71) - qB_3(B_61) = qB_7(B_21) - B_6(B_31)`,

i.e. `-B_2(e_7) - qB_3(e_6) = qB_7(e_2) + B_6(e_3)`, and the four values in it are **four of the
new weight-nine base rows**, each read off the `HJO.Sym.dop_elemSymm` convolution against the
kernel table — `HJO.Sym.bop_two_elemSymm_seven` being the only place the new
`HJO.Bglx.paramPleth_elemSymm_seven_eq` is read at all. The two routes share no lemma:
`HJO.Sym.bop_hmz_two_seven_of_hmz` proves the relation from `HJO.Sym.bop_bop_sub_smul` with **no**
value of `B` in it, while `..._of_table` evaluates all four rows and closes on a polynomial
identity in the five weight-nine `e`-monomials `e_9`, `e_1e_8`, `e_2e_7`, `e_3e_6`, `e_4e_5`. A
dropped term, a lost sign or a misread index in any one of the four would separate them.

The rest of the chain is checked by construction: `HJO.Mellit.onePartOuterValue_two` is obtained
from `HJO.Mellit.onePartSweepValue_three_eq` through
`HJO.Mellit.smul_onePartSweepValue_succ_of_letter`, which is proved from
`HJO.Sweep.replicatedTotal_two_three_zero_apply` with no value in it, so the scalar
`qu(1-q)^2·(-(q^2u^2)) = -(1-q)^2·q^3u^3` is a constraint the two sides must meet.

## What is NOT proved, with the quantifier named

* **`HJO.Mellit.LhsAt q u 2 3 Θ [3]` is NOT decided, at any slope homomorphism.** What this file
  supplies is the *sweep* side: by `HJO.Mellit.lhsAt_two_three_singleton_iff_onePartSweepValue` the
  clause at `[3]` is `Θ(h_3)(1) = V_3`, and `V_3` is now an explicit element of `Λ`. The creation
  side is untouched and has no `Θ`-free reduction past `A = 2`:
  `HJO.Mellit.lhsAt_two_three_two_iff_qop` rests on
  `HJO.Mellit.theta_completeHomog_two_apply_one_smul`, and there is **no** `h_3` analogue of it.
  The recursion `HJO.Mellit.theta_completeHomog_apply_one_smul_eq_sum_qop` at `A = 3` leaves
  `Θ(h_2)(Q_{2,3}1)`, `Θ(h_1)(Q_{4,6}1)`, `Θ(h_0)(Q_{6,9}1)`, and the four weight-nine slope values
  a `Θ`-free `[3]` would need — `Q_{2,3}(Q_{2,3}(Q_{2,3}1))`, `Q_{4,6}(Q_{2,3}1)`,
  `Q_{2,3}(Q_{4,6}1)`, `Q_{6,9}(1)` — are **none of them evaluated in any form**. This is a *missing
  evaluation on the creation side*, not an obstruction.
* **The induction route to `[3]` is circular and this file does not change that.**
  `HJO.Mellit.creation_step_iff_lhsAt_succ` at `A = 1`, given the proved clause at `[2]`, makes the
  `hstep` hypothesis of `HJO.Mellit.forall_lhsAt_two_three_singleton_succ_of_creation_of_axis`
  *equivalent* to the clause at `[3]`. So `hstep` is discharged at **no** `A ≥ 1`.
* **`Δ¹_2 = HJO.Mellit.onePartDefectOne q u 2` is still not an explicit element of `Λ`.**
  `HJO.Mellit.onePartDefectOne_eq` at `A = 2` reads `Δ¹_2 = D_1(w_2) - ((1-q)/q)·x_2`; both `w_2`
  and `x_2` are evaluated here, and what is missing is `D_1(w_2)` — the `u`-full operator
  `HJO.Sym.Dop` on a weight-eight argument. The `HJO.Sym.dop_*` table stops at output weight
  six (`dop_one_elemSymm_five`, `dop_two_elemSymm_four`), so **no** `Dop` row of this file's weight
  exists. The same gap leaves `D_2(V_2)` unevaluated, hence `HJO.Mellit.onePartDefectTwo_two` is
  not re-derived from its closed form here.
* **No closed form in `A` is claimed.** The one-part values run `2, 9, 26` `e`-monomials at
  `A = 1, 2, 3` with coefficients of `q`-degree `1, 8, 21`; the stage words run `2, 11, 42`
  monomials. Nothing here suggests a formula, and the file's own values are the reason: each level
  is one further `z_1` and the support grows with the partitions of the weight.
* **No value here is shown to be nonzero as an element of `Λ`, and nothing here compares two
  computed values of different origin except the consistency check.**

## Genericity

`q ≠ 0`, `u ≠ 0`, `q ≠ 1` throughout, and nothing else. They are the seed's and the letter's, not
this file's: `q ≠ 1` is the `q/(1-q)` of `HJO.Sweep.zop`, which in a field is the **zero map** at
`q = 1` so a clause asserting otherwise there is false and not vacuous; `q ≠ 0` and `u ≠ 0` are the
`(qu)^{-1}` of `HJO.Sweep.slopeOperator`, the same way. `M = (1-q)(1-u) ≠ 0` is **not** needed
anywhere in this file — no value below spells `M^{-1}` — and neither is `qu ≠ 1` or `qu ≠ -1`,
which `HJO.Mellit.lhsAt_two_three_two_of_axis` needs only because `HJO.Sym.Qop` and
`HJO.Sym.axisGen` appear on its right-hand side.

The `B_k`, `d^*_+` and kernel tables need **no hypothesis at all**: they are identities of two
polynomial expressions in `q` and `u`.

## What the results are

These are values of `HJO.Sweep.zop`, `HJO.Sym.Bop`, `HJO.Sweep.dplusStar`
and `HJO.Mellit.stage`, not those definitions themselves.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

-- Every computation below closes on a polynomial identity in the `e`-monomials and the scalars
-- `C q`, `C u`, and each is normalised by the *same* rewrite set: which members of it fire depends
-- on the monomial, so some are unused in each individual proof.
set_option linter.unusedSimpArgs false

-- Every exponent written as a numeral in this file is a natural number. Saying so up front lets
-- each `x ^ n` resolve `HPow _ ℕ _` at once instead of retrying instance resolution for the
-- pending numeral type until defaulting, which dominated elaboration here. The elaborated terms
-- are the ones the default instance would produce.
local macro_rules | `($x ^ $n:num) => `(rightact% HPow.hPow $x ($n : ℕ))

namespace HJO.Mellit

open HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

set_option maxHeartbeats 1400000 in
-- A size, not a loop: the closing normalisation of this value — the largest of the family — needs
-- between three and four times the default budget, so it is given twice what it needs.
/-- **`V_3` in the `e`-basis** (module route). -/
theorem onePartSweepValue_three_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    onePartSweepValue q u 3 = (-(q ^ 2 * u ^ 2)) • (
          (-(q ^ 19) - q ^ 18 * u - q ^ 17 * u ^ 2 - q ^ 16 * u ^ 3 - q ^ 15 * u ^ 4
            - q ^ 14 * u ^ 5 - q ^ 13 * u ^ 6 - q ^ 12 * u ^ 7 - q ^ 11 * u ^ 8 - q ^ 10 * u ^ 9
            - q ^ 9 * u ^ 10 - q ^ 8 * u ^ 11 - q ^ 7 * u ^ 12 - q ^ 6 * u ^ 13 - q ^ 5 * u ^ 14
            - q ^ 4 * u ^ 15 - q ^ 3 * u ^ 16 - q ^ 2 * u ^ 17 - q * u ^ 18 - u ^ 19 + q ^ 18
            + u ^ 18 + q ^ 17 + q ^ 16 * u + q * u ^ 16 + u ^ 17 + q ^ 15 * u + q ^ 14 * u ^ 2
            + q ^ 2 * u ^ 14 + q * u ^ 15 + q ^ 14 * u + q ^ 13 * u ^ 2 + q ^ 12 * u ^ 3
            + q ^ 3 * u ^ 12 + q ^ 2 * u ^ 13 + q * u ^ 14 - q ^ 14 + q ^ 13 * u
            + 2 * q ^ 12 * u ^ 2 + 2 * q ^ 11 * u ^ 3 + 2 * q ^ 10 * u ^ 4 + q ^ 9 * u ^ 5
            + q ^ 8 * u ^ 6 + q ^ 7 * u ^ 7 + q ^ 6 * u ^ 8 + q ^ 5 * u ^ 9 + 2 * q ^ 4 * u ^ 10
            + 2 * q ^ 3 * u ^ 11 + 2 * q ^ 2 * u ^ 12 + q * u ^ 13 - u ^ 14 - q ^ 13 - q ^ 12 * u
            + 2 * q ^ 11 * u ^ 2 + 2 * q ^ 10 * u ^ 3 + 2 * q ^ 9 * u ^ 4 + 2 * q ^ 8 * u ^ 5
            + q ^ 7 * u ^ 6 + q ^ 6 * u ^ 7 + 2 * q ^ 5 * u ^ 8 + 2 * q ^ 4 * u ^ 9
            + 2 * q ^ 3 * u ^ 10 + 2 * q ^ 2 * u ^ 11 - q * u ^ 12 - u ^ 13 - q ^ 12
            - 4 * q ^ 11 * u - 2 * q ^ 10 * u ^ 2 + 2 * q ^ 9 * u ^ 3 + 2 * q ^ 8 * u ^ 4
            + 3 * q ^ 7 * u ^ 5 + 4 * q ^ 6 * u ^ 6 + 3 * q ^ 5 * u ^ 7 + 2 * q ^ 4 * u ^ 8
            + 2 * q ^ 3 * u ^ 9 - 2 * q ^ 2 * u ^ 10 - 4 * q * u ^ 11 - u ^ 12 + q ^ 11
            - 2 * q ^ 10 * u - 5 * q ^ 9 * u ^ 2 - 2 * q ^ 8 * u ^ 3 + 2 * q ^ 7 * u ^ 4
            + 2 * q ^ 6 * u ^ 5 + 2 * q ^ 5 * u ^ 6 + 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8
            - 5 * q ^ 2 * u ^ 9 - 2 * q * u ^ 10 + u ^ 11 + q ^ 10 - 5 * q ^ 8 * u ^ 2
            - 10 * q ^ 7 * u ^ 3 - 10 * q ^ 6 * u ^ 4 - 9 * q ^ 5 * u ^ 5 - 10 * q ^ 4 * u ^ 6
            - 10 * q ^ 3 * u ^ 7 - 5 * q ^ 2 * u ^ 8 + u ^ 10 + q ^ 9 + 3 * q ^ 8 * u
            + q ^ 7 * u ^ 2 - 3 * q ^ 6 * u ^ 3 - 6 * q ^ 5 * u ^ 4 - 6 * q ^ 4 * u ^ 5
            - 3 * q ^ 3 * u ^ 6 + q ^ 2 * u ^ 7 + 3 * q * u ^ 8 + u ^ 9 + 3 * q ^ 7 * u
            + 6 * q ^ 6 * u ^ 2 + 6 * q ^ 5 * u ^ 3 + 6 * q ^ 4 * u ^ 4 + 6 * q ^ 3 * u ^ 5
            + 6 * q ^ 2 * u ^ 6 + 3 * q * u ^ 7 + q ^ 6 * u + 4 * q ^ 5 * u ^ 2
            + 6 * q ^ 4 * u ^ 3 + 6 * q ^ 3 * u ^ 4 + 4 * q ^ 2 * u ^ 5 + q * u ^ 6 - q ^ 6
            - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 2 * u ^ 4 - q * u ^ 5 - u ^ 6 - q ^ 5
            - 3 * q ^ 4 * u - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3 - 3 * q * u ^ 4 - u ^ 5
            + q ^ 4 - q ^ 2 * u ^ 2 + u ^ 4 + q ^ 2 * u + q * u ^ 2) • elemSymm L 9
        + (-(q ^ 18) - q ^ 17 * u - q ^ 16 * u ^ 2 - q ^ 15 * u ^ 3 - q ^ 14 * u ^ 4
            - q ^ 13 * u ^ 5 - q ^ 12 * u ^ 6 - q ^ 11 * u ^ 7 - q ^ 10 * u ^ 8 - q ^ 9 * u ^ 9
            - q ^ 8 * u ^ 10 - q ^ 7 * u ^ 11 - q ^ 6 * u ^ 12 - q ^ 5 * u ^ 13 - q ^ 4 * u ^ 14
            - q ^ 3 * u ^ 15 - q ^ 2 * u ^ 16 - q * u ^ 17 - u ^ 18 - q ^ 16 * u - q ^ 15 * u ^ 2
            - q ^ 14 * u ^ 3 - q ^ 13 * u ^ 4 - q ^ 12 * u ^ 5 - q ^ 11 * u ^ 6 - q ^ 10 * u ^ 7
            - q ^ 9 * u ^ 8 - q ^ 8 * u ^ 9 - q ^ 7 * u ^ 10 - q ^ 6 * u ^ 11 - q ^ 5 * u ^ 12
            - q ^ 4 * u ^ 13 - q ^ 3 * u ^ 14 - q ^ 2 * u ^ 15 - q * u ^ 16 + q ^ 16
            - q ^ 14 * u ^ 2 - q ^ 13 * u ^ 3 - q ^ 12 * u ^ 4 - q ^ 11 * u ^ 5 - q ^ 10 * u ^ 6
            - q ^ 9 * u ^ 7 - q ^ 8 * u ^ 8 - q ^ 7 * u ^ 9 - q ^ 6 * u ^ 10 - q ^ 5 * u ^ 11
            - q ^ 4 * u ^ 12 - q ^ 3 * u ^ 13 - q ^ 2 * u ^ 14 + u ^ 16 + q ^ 15 + q ^ 14 * u
            - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4 - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7
            - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9 - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12
            + q * u ^ 14 + u ^ 15 + q ^ 14 + 2 * q ^ 13 * u + q ^ 12 * u ^ 2 - q ^ 10 * u ^ 4
            - q ^ 9 * u ^ 5 - q ^ 8 * u ^ 6 - q ^ 7 * u ^ 7 - q ^ 6 * u ^ 8 - q ^ 5 * u ^ 9
            - q ^ 4 * u ^ 10 + q ^ 2 * u ^ 12 + 2 * q * u ^ 13 + u ^ 14 + q ^ 13 + 4 * q ^ 12 * u
            + 4 * q ^ 11 * u ^ 2 + 3 * q ^ 10 * u ^ 3 + 2 * q ^ 9 * u ^ 4 + q ^ 8 * u ^ 5
            + q ^ 7 * u ^ 6 + q ^ 6 * u ^ 7 + q ^ 5 * u ^ 8 + 2 * q ^ 4 * u ^ 9
            + 3 * q ^ 3 * u ^ 10 + 4 * q ^ 2 * u ^ 11 + 4 * q * u ^ 12 + u ^ 13 - q ^ 12
            + 4 * q ^ 11 * u + 7 * q ^ 10 * u ^ 2 + 6 * q ^ 9 * u ^ 3 + 5 * q ^ 8 * u ^ 4
            + 4 * q ^ 7 * u ^ 5 + 3 * q ^ 6 * u ^ 6 + 4 * q ^ 5 * u ^ 7 + 5 * q ^ 4 * u ^ 8
            + 6 * q ^ 3 * u ^ 9 + 7 * q ^ 2 * u ^ 10 + 4 * q * u ^ 11 - u ^ 12 - 4 * q ^ 11
            - 3 * q ^ 10 * u + 5 * q ^ 9 * u ^ 2 + 8 * q ^ 8 * u ^ 3 + 8 * q ^ 7 * u ^ 4
            + 9 * q ^ 6 * u ^ 5 + 9 * q ^ 5 * u ^ 6 + 8 * q ^ 4 * u ^ 7 + 8 * q ^ 3 * u ^ 8
            + 5 * q ^ 2 * u ^ 9 - 3 * q * u ^ 10 - 4 * u ^ 11 - 2 * q ^ 10 - 8 * q ^ 9 * u
            - 4 * q ^ 8 * u ^ 2 + 6 * q ^ 7 * u ^ 3 + 10 * q ^ 6 * u ^ 4 + 10 * q ^ 5 * u ^ 5
            + 10 * q ^ 4 * u ^ 6 + 6 * q ^ 3 * u ^ 7 - 4 * q ^ 2 * u ^ 8 - 8 * q * u ^ 9
            - 2 * u ^ 10 - 8 * q ^ 8 * u - 16 * q ^ 7 * u ^ 2 - 16 * q ^ 6 * u ^ 3
            - 12 * q ^ 5 * u ^ 4 - 12 * q ^ 4 * u ^ 5 - 16 * q ^ 3 * u ^ 6 - 16 * q ^ 2 * u ^ 7
            - 8 * q * u ^ 8 + 3 * q ^ 8 - q ^ 7 * u - 12 * q ^ 6 * u ^ 2 - 20 * q ^ 5 * u ^ 3
            - 23 * q ^ 4 * u ^ 4 - 20 * q ^ 3 * u ^ 5 - 12 * q ^ 2 * u ^ 6 - q * u ^ 7 + 3 * u ^ 8
            + 3 * q ^ 7 + 9 * q ^ 6 * u + 7 * q ^ 5 * u ^ 2 + 3 * q ^ 4 * u ^ 3
            + 3 * q ^ 3 * u ^ 4 + 7 * q ^ 2 * u ^ 5 + 9 * q * u ^ 6 + 3 * u ^ 7 + q ^ 6
            + 7 * q ^ 5 * u + 14 * q ^ 4 * u ^ 2 + 15 * q ^ 3 * u ^ 3 + 14 * q ^ 2 * u ^ 4
            + 7 * q * u ^ 5 + u ^ 6 - q ^ 5 + q ^ 4 * u + 4 * q ^ 3 * u ^ 2 + 4 * q ^ 2 * u ^ 3
            + q * u ^ 4 - u ^ 5 - 3 * q ^ 4 - 5 * q ^ 3 * u - 5 * q ^ 2 * u ^ 2 - 5 * q * u ^ 3
            - 3 * u ^ 4 - 3 * q ^ 2 * u - 3 * q * u ^ 2 + q ^ 2 + 2 * q * u + u ^ 2)
              • (elemSymm L 1 * elemSymm L 8)
        + (-(q ^ 17) - q ^ 16 * u - q ^ 15 * u ^ 2 - q ^ 14 * u ^ 3 - q ^ 13 * u ^ 4
            - q ^ 12 * u ^ 5 - q ^ 11 * u ^ 6 - q ^ 10 * u ^ 7 - q ^ 9 * u ^ 8 - q ^ 8 * u ^ 9
            - q ^ 7 * u ^ 10 - q ^ 6 * u ^ 11 - q ^ 5 * u ^ 12 - q ^ 4 * u ^ 13 - q ^ 3 * u ^ 14
            - q ^ 2 * u ^ 15 - q * u ^ 16 - u ^ 17 + q ^ 16 + u ^ 16 - q ^ 13 * u ^ 2
            - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4 - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7
            - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9 - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12
            - q ^ 2 * u ^ 13 + q ^ 14 + q ^ 13 * u + q ^ 12 * u ^ 2 + q ^ 2 * u ^ 12 + q * u ^ 13
            + u ^ 14 + q ^ 12 * u - q ^ 9 * u ^ 4 - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7
            - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9 + q * u ^ 12 - q ^ 12 + q ^ 11 * u
            + 2 * q ^ 10 * u ^ 2 + q ^ 9 * u ^ 3 + q ^ 8 * u ^ 4 + q ^ 4 * u ^ 8 + q ^ 3 * u ^ 9
            + 2 * q ^ 2 * u ^ 10 + q * u ^ 11 - u ^ 12 + 2 * q ^ 9 * u ^ 2 + 2 * q ^ 8 * u ^ 3
            + q ^ 7 * u ^ 4 + q ^ 6 * u ^ 5 + q ^ 5 * u ^ 6 + q ^ 4 * u ^ 7 + 2 * q ^ 3 * u ^ 8
            + 2 * q ^ 2 * u ^ 9 + 2 * q ^ 8 * u ^ 2 + 6 * q ^ 7 * u ^ 3 + 7 * q ^ 6 * u ^ 4
            + 7 * q ^ 5 * u ^ 5 + 7 * q ^ 4 * u ^ 6 + 6 * q ^ 3 * u ^ 7 + 2 * q ^ 2 * u ^ 8
            - q ^ 8 * u + 2 * q ^ 6 * u ^ 3 + 5 * q ^ 5 * u ^ 4 + 5 * q ^ 4 * u ^ 5
            + 2 * q ^ 3 * u ^ 6 - q * u ^ 8 - q ^ 8 - 5 * q ^ 7 * u - 9 * q ^ 6 * u ^ 2
            - 12 * q ^ 5 * u ^ 3 - 14 * q ^ 4 * u ^ 4 - 12 * q ^ 3 * u ^ 5 - 9 * q ^ 2 * u ^ 6
            - 5 * q * u ^ 7 - u ^ 8 + q ^ 7 + 2 * q ^ 6 * u - q ^ 5 * u ^ 2 - 2 * q ^ 4 * u ^ 3
            - 2 * q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5 + 2 * q * u ^ 6 + u ^ 7 + 3 * q ^ 5 * u
            + 6 * q ^ 4 * u ^ 2 + 5 * q ^ 3 * u ^ 3 + 6 * q ^ 2 * u ^ 4 + 3 * q * u ^ 5
            + q ^ 3 * u ^ 2 + q ^ 2 * u ^ 3 - q ^ 4 - 2 * q ^ 3 * u - 3 * q ^ 2 * u ^ 2
            - 2 * q * u ^ 3 - u ^ 4 + q ^ 3 + u ^ 3 + q ^ 2 + 2 * q * u + u ^ 2 - q - u)
              • (elemSymm L 2 * elemSymm L 7)
        + (-(q ^ 16) - q ^ 15 * u - q ^ 14 * u ^ 2 - q ^ 13 * u ^ 3 - q ^ 12 * u ^ 4
            - q ^ 11 * u ^ 5 - q ^ 10 * u ^ 6 - q ^ 9 * u ^ 7 - q ^ 8 * u ^ 8 - q ^ 7 * u ^ 9
            - q ^ 6 * u ^ 10 - q ^ 5 * u ^ 11 - q ^ 4 * u ^ 12 - q ^ 3 * u ^ 13 - q ^ 2 * u ^ 14
            - q * u ^ 15 - u ^ 16 + q ^ 15 + u ^ 15 + q ^ 14 + q ^ 13 * u + q * u ^ 13 + u ^ 14
            - 2 * q ^ 13 - q ^ 12 * u - q ^ 11 * u ^ 2 - 2 * q ^ 10 * u ^ 3 - 2 * q ^ 9 * u ^ 4
            - 2 * q ^ 8 * u ^ 5 - 2 * q ^ 7 * u ^ 6 - 2 * q ^ 6 * u ^ 7 - 2 * q ^ 5 * u ^ 8
            - 2 * q ^ 4 * u ^ 9 - 2 * q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 - q * u ^ 12 - 2 * u ^ 13
            + 2 * q ^ 12 + q ^ 11 * u + q ^ 10 * u ^ 2 + q ^ 9 * u ^ 3 + q ^ 3 * u ^ 9
            + q ^ 2 * u ^ 10 + q * u ^ 11 + 2 * u ^ 12 + q ^ 11 + 3 * q ^ 10 * u
            + 2 * q ^ 9 * u ^ 2 + 2 * q ^ 8 * u ^ 3 + 2 * q ^ 7 * u ^ 4 + q ^ 6 * u ^ 5
            + q ^ 5 * u ^ 6 + 2 * q ^ 4 * u ^ 7 + 2 * q ^ 3 * u ^ 8 + 2 * q ^ 2 * u ^ 9
            + 3 * q * u ^ 10 + u ^ 11 - 2 * q ^ 10 + 3 * q ^ 8 * u ^ 2 + q ^ 7 * u ^ 3
            + q ^ 6 * u ^ 4 + 2 * q ^ 5 * u ^ 5 + q ^ 4 * u ^ 6 + q ^ 3 * u ^ 7
            + 3 * q ^ 2 * u ^ 8 - 2 * u ^ 10 - 2 * q ^ 8 * u + q ^ 7 * u ^ 2 + 6 * q ^ 6 * u ^ 3
            + 4 * q ^ 5 * u ^ 4 + 4 * q ^ 4 * u ^ 5 + 6 * q ^ 3 * u ^ 6 + q ^ 2 * u ^ 7
            - 2 * q * u ^ 8 + 2 * q ^ 7 * u + 3 * q ^ 5 * u ^ 3 + 8 * q ^ 4 * u ^ 4
            + 3 * q ^ 3 * u ^ 5 + 2 * q * u ^ 7 - 3 * q ^ 7 - 6 * q ^ 6 * u - 7 * q ^ 5 * u ^ 2
            - 13 * q ^ 4 * u ^ 3 - 13 * q ^ 3 * u ^ 4 - 7 * q ^ 2 * u ^ 5 - 6 * q * u ^ 6
            - 3 * u ^ 7 + q ^ 6 - 3 * q ^ 5 * u - 4 * q ^ 4 * u ^ 2 - 2 * q ^ 3 * u ^ 3
            - 4 * q ^ 2 * u ^ 4 - 3 * q * u ^ 5 + u ^ 6 + 3 * q ^ 5 + 4 * q ^ 4 * u
            + 2 * q ^ 3 * u ^ 2 + 2 * q ^ 2 * u ^ 3 + 4 * q * u ^ 4 + 3 * u ^ 5 + q ^ 4
            + 4 * q ^ 3 * u + 5 * q ^ 2 * u ^ 2 + 4 * q * u ^ 3 + u ^ 4 - q ^ 3 + q ^ 2 * u
            + q * u ^ 2 - u ^ 3 - 2 * q ^ 2 - 4 * q * u - 2 * u ^ 2 + q + u)
              • (elemSymm L 3 * elemSymm L 6)
        + (-(q ^ 15) - q ^ 14 * u - q ^ 13 * u ^ 2 - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4
            - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7 - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9
            - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12 - q ^ 2 * u ^ 13 - q * u ^ 14
            - u ^ 15 - q ^ 13 * u - q ^ 12 * u ^ 2 - q ^ 11 * u ^ 3 - q ^ 10 * u ^ 4
            - q ^ 9 * u ^ 5 - q ^ 8 * u ^ 6 - q ^ 7 * u ^ 7 - q ^ 6 * u ^ 8 - q ^ 5 * u ^ 9
            - q ^ 4 * u ^ 10 - q ^ 3 * u ^ 11 - q ^ 2 * u ^ 12 - q * u ^ 13 + 2 * q ^ 13
            + q ^ 12 * u + q * u ^ 12 + 2 * u ^ 13 + q ^ 12 + 2 * q ^ 11 * u + q ^ 10 * u ^ 2
            + q ^ 2 * u ^ 10 + 2 * q * u ^ 11 + u ^ 12 - q ^ 11 + q ^ 10 * u + q ^ 9 * u ^ 2
            - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5 - q ^ 5 * u ^ 6 - q ^ 4 * u ^ 7 + q ^ 2 * u ^ 9
            + q * u ^ 10 - u ^ 11 + 2 * q ^ 9 * u + 3 * q ^ 8 * u ^ 2 + 3 * q ^ 7 * u ^ 3
            + 2 * q ^ 6 * u ^ 4 + q ^ 5 * u ^ 5 + 2 * q ^ 4 * u ^ 6 + 3 * q ^ 3 * u ^ 7
            + 3 * q ^ 2 * u ^ 8 + 2 * q * u ^ 9 - 2 * q ^ 9 + 3 * q ^ 7 * u ^ 2
            + 3 * q ^ 6 * u ^ 3 + 4 * q ^ 5 * u ^ 4 + 4 * q ^ 4 * u ^ 5 + 3 * q ^ 3 * u ^ 6
            + 3 * q ^ 2 * u ^ 7 - 2 * u ^ 9 - q ^ 8 - 4 * q ^ 7 * u + q ^ 6 * u ^ 2
            + 5 * q ^ 5 * u ^ 3 + 4 * q ^ 4 * u ^ 4 + 5 * q ^ 3 * u ^ 5 + q ^ 2 * u ^ 6
            - 4 * q * u ^ 7 - u ^ 8 - 5 * q ^ 6 * u - 8 * q ^ 5 * u ^ 2 - 4 * q ^ 4 * u ^ 3
            - 4 * q ^ 3 * u ^ 4 - 8 * q ^ 2 * u ^ 5 - 5 * q * u ^ 6 + 2 * q ^ 6 - q ^ 5 * u
            - 8 * q ^ 4 * u ^ 2 - 13 * q ^ 3 * u ^ 3 - 8 * q ^ 2 * u ^ 4 - q * u ^ 5 + 2 * u ^ 6
            + 2 * q ^ 5 + 7 * q ^ 4 * u + 6 * q ^ 3 * u ^ 2 + 6 * q ^ 2 * u ^ 3 + 7 * q * u ^ 4
            + 2 * u ^ 5 - 2 * q ^ 4 + 2 * q ^ 3 * u + 6 * q ^ 2 * u ^ 2 + 2 * q * u ^ 3
            - 2 * u ^ 4 - 3 * q ^ 2 * u - 3 * q * u ^ 2) • (elemSymm L 4 * elemSymm L 5)
        + (-(q ^ 16) - q ^ 15 * u - q ^ 14 * u ^ 2 - q ^ 13 * u ^ 3 - q ^ 12 * u ^ 4
            - q ^ 11 * u ^ 5 - q ^ 10 * u ^ 6 - q ^ 9 * u ^ 7 - q ^ 8 * u ^ 8 - q ^ 7 * u ^ 9
            - q ^ 6 * u ^ 10 - q ^ 5 * u ^ 11 - q ^ 4 * u ^ 12 - q ^ 3 * u ^ 13 - q ^ 2 * u ^ 14
            - q * u ^ 15 - u ^ 16 - q ^ 14 * u - q ^ 13 * u ^ 2 - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4
            - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7 - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9
            - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12 - q ^ 2 * u ^ 13 - q * u ^ 14
            - q ^ 13 * u - 2 * q ^ 12 * u ^ 2 - 2 * q ^ 11 * u ^ 3 - 2 * q ^ 10 * u ^ 4
            - 2 * q ^ 9 * u ^ 5 - 2 * q ^ 8 * u ^ 6 - 2 * q ^ 7 * u ^ 7 - 2 * q ^ 6 * u ^ 8
            - 2 * q ^ 5 * u ^ 9 - 2 * q ^ 4 * u ^ 10 - 2 * q ^ 3 * u ^ 11 - 2 * q ^ 2 * u ^ 12
            - q * u ^ 13 + q ^ 13 - q ^ 11 * u ^ 2 - 2 * q ^ 10 * u ^ 3 - 2 * q ^ 9 * u ^ 4
            - 2 * q ^ 8 * u ^ 5 - 2 * q ^ 7 * u ^ 6 - 2 * q ^ 6 * u ^ 7 - 2 * q ^ 5 * u ^ 8
            - 2 * q ^ 4 * u ^ 9 - 2 * q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 + u ^ 13 + 2 * q ^ 12
            + 2 * q ^ 11 * u - q ^ 9 * u ^ 3 - 2 * q ^ 8 * u ^ 4 - 2 * q ^ 7 * u ^ 5
            - 2 * q ^ 6 * u ^ 6 - 2 * q ^ 5 * u ^ 7 - 2 * q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9
            + 2 * q * u ^ 11 + 2 * u ^ 12 + 2 * q ^ 11 + 6 * q ^ 10 * u + 5 * q ^ 9 * u ^ 2
            + 3 * q ^ 8 * u ^ 3 + 2 * q ^ 7 * u ^ 4 + q ^ 6 * u ^ 5 + q ^ 5 * u ^ 6
            + 2 * q ^ 4 * u ^ 7 + 3 * q ^ 3 * u ^ 8 + 5 * q ^ 2 * u ^ 9 + 6 * q * u ^ 10
            + 2 * u ^ 11 - q ^ 10 + 5 * q ^ 9 * u + 9 * q ^ 8 * u ^ 2 + 7 * q ^ 7 * u ^ 3
            + 6 * q ^ 6 * u ^ 4 + 6 * q ^ 5 * u ^ 5 + 6 * q ^ 4 * u ^ 6 + 7 * q ^ 3 * u ^ 7
            + 9 * q ^ 2 * u ^ 8 + 5 * q * u ^ 9 - u ^ 10 - 3 * q ^ 9 - q ^ 8 * u
            + 8 * q ^ 7 * u ^ 2 + 14 * q ^ 6 * u ^ 3 + 14 * q ^ 5 * u ^ 4 + 14 * q ^ 4 * u ^ 5
            + 14 * q ^ 3 * u ^ 6 + 8 * q ^ 2 * u ^ 7 - q * u ^ 8 - 3 * u ^ 9 - 3 * q ^ 8
            - 7 * q ^ 7 * u - 4 * q ^ 6 * u ^ 2 + 3 * q ^ 5 * u ^ 3 + 7 * q ^ 4 * u ^ 4
            + 3 * q ^ 3 * u ^ 5 - 4 * q ^ 2 * u ^ 6 - 7 * q * u ^ 7 - 3 * u ^ 8 - 2 * q ^ 7
            - 12 * q ^ 6 * u - 19 * q ^ 5 * u ^ 2 - 22 * q ^ 4 * u ^ 3 - 22 * q ^ 3 * u ^ 4
            - 19 * q ^ 2 * u ^ 5 - 12 * q * u ^ 6 - 2 * u ^ 7 + 3 * q ^ 6 - 9 * q ^ 4 * u ^ 2
            - 11 * q ^ 3 * u ^ 3 - 9 * q ^ 2 * u ^ 4 + 3 * u ^ 6 + 3 * q ^ 5 + 8 * q ^ 4 * u
            + 9 * q ^ 3 * u ^ 2 + 9 * q ^ 2 * u ^ 3 + 8 * q * u ^ 4 + 3 * u ^ 5 + 2 * q ^ 4
            + 6 * q ^ 3 * u + 9 * q ^ 2 * u ^ 2 + 6 * q * u ^ 3 + 2 * u ^ 4 - 2 * q ^ 3
            - q ^ 2 * u - q * u ^ 2 - 2 * u ^ 3 - 2 * q ^ 2 - 4 * q * u - 2 * u ^ 2 + q + u)
              • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
        + (-(q ^ 15) - q ^ 14 * u - q ^ 13 * u ^ 2 - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4
            - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7 - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9
            - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12 - q ^ 2 * u ^ 13 - q * u ^ 14
            - u ^ 15 - q ^ 14 - 2 * q ^ 13 * u - 2 * q ^ 12 * u ^ 2 - 2 * q ^ 11 * u ^ 3
            - 2 * q ^ 10 * u ^ 4 - 2 * q ^ 9 * u ^ 5 - 2 * q ^ 8 * u ^ 6 - 2 * q ^ 7 * u ^ 7
            - 2 * q ^ 6 * u ^ 8 - 2 * q ^ 5 * u ^ 9 - 2 * q ^ 4 * u ^ 10 - 2 * q ^ 3 * u ^ 11
            - 2 * q ^ 2 * u ^ 12 - 2 * q * u ^ 13 - u ^ 14 + 2 * q ^ 13 - q ^ 11 * u ^ 2
            - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4 - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7
            - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9 - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 + 2 * u ^ 13
            - 2 * q ^ 10 * u ^ 2 - 3 * q ^ 9 * u ^ 3 - 3 * q ^ 8 * u ^ 4 - 3 * q ^ 7 * u ^ 5
            - 3 * q ^ 6 * u ^ 6 - 3 * q ^ 5 * u ^ 7 - 3 * q ^ 4 * u ^ 8 - 3 * q ^ 3 * u ^ 9
            - 2 * q ^ 2 * u ^ 10 + q ^ 11 + q ^ 10 * u - 2 * q ^ 8 * u ^ 3 - 3 * q ^ 7 * u ^ 4
            - 3 * q ^ 6 * u ^ 5 - 3 * q ^ 5 * u ^ 6 - 3 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8
            + q * u ^ 10 + u ^ 11 + 2 * q ^ 10 + 5 * q ^ 9 * u + 3 * q ^ 8 * u ^ 2
            + 2 * q ^ 7 * u ^ 3 - q ^ 5 * u ^ 5 + 2 * q ^ 3 * u ^ 7 + 3 * q ^ 2 * u ^ 8
            + 5 * q * u ^ 9 + 2 * u ^ 10 - q ^ 9 + 5 * q ^ 8 * u + 9 * q ^ 7 * u ^ 2
            + 7 * q ^ 6 * u ^ 3 + 8 * q ^ 5 * u ^ 4 + 8 * q ^ 4 * u ^ 5 + 7 * q ^ 3 * u ^ 6
            + 9 * q ^ 2 * u ^ 7 + 5 * q * u ^ 8 - u ^ 9 - 2 * q ^ 8 - q ^ 7 * u
            + 9 * q ^ 6 * u ^ 2 + 14 * q ^ 5 * u ^ 3 + 13 * q ^ 4 * u ^ 4 + 14 * q ^ 3 * u ^ 5
            + 9 * q ^ 2 * u ^ 6 - q * u ^ 7 - 2 * u ^ 8 - 5 * q ^ 6 * u - 5 * q ^ 5 * u ^ 2
            + q ^ 4 * u ^ 3 + q ^ 3 * u ^ 4 - 5 * q ^ 2 * u ^ 5 - 5 * q * u ^ 6 - q ^ 6
            - 5 * q ^ 5 * u - 13 * q ^ 4 * u ^ 2 - 16 * q ^ 3 * u ^ 3 - 13 * q ^ 2 * u ^ 4
            - 5 * q * u ^ 5 - u ^ 6 - q ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3
            - q * u ^ 4 - u ^ 5 + 2 * q ^ 4 + 3 * q ^ 3 * u + 4 * q ^ 2 * u ^ 2 + 3 * q * u ^ 3
            + 2 * u ^ 4 + q ^ 2 * u + q * u ^ 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
        + (-(q ^ 14) - q ^ 13 * u - q ^ 12 * u ^ 2 - q ^ 11 * u ^ 3 - q ^ 10 * u ^ 4
            - q ^ 9 * u ^ 5 - q ^ 8 * u ^ 6 - q ^ 7 * u ^ 7 - q ^ 6 * u ^ 8 - q ^ 5 * u ^ 9
            - q ^ 4 * u ^ 10 - q ^ 3 * u ^ 11 - q ^ 2 * u ^ 12 - q * u ^ 13 - u ^ 14 - q ^ 12 * u
            - q ^ 11 * u ^ 2 - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4 - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6
            - q ^ 6 * u ^ 7 - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9 - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11
            - q * u ^ 12 - q ^ 12 - 2 * q ^ 11 * u - 3 * q ^ 10 * u ^ 2 - 3 * q ^ 9 * u ^ 3
            - 3 * q ^ 8 * u ^ 4 - 3 * q ^ 7 * u ^ 5 - 3 * q ^ 6 * u ^ 6 - 3 * q ^ 5 * u ^ 7
            - 3 * q ^ 4 * u ^ 8 - 3 * q ^ 3 * u ^ 9 - 3 * q ^ 2 * u ^ 10 - 2 * q * u ^ 11 - u ^ 12
            + 2 * q ^ 11 - q ^ 9 * u ^ 2 - 2 * q ^ 8 * u ^ 3 - 2 * q ^ 7 * u ^ 4
            - 2 * q ^ 6 * u ^ 5 - 2 * q ^ 5 * u ^ 6 - 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8
            - q ^ 2 * u ^ 9 + 2 * u ^ 11 + 3 * q ^ 10 + 3 * q ^ 9 * u - q ^ 7 * u ^ 3
            - 2 * q ^ 6 * u ^ 4 - 2 * q ^ 5 * u ^ 5 - 2 * q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7
            + 3 * q * u ^ 9 + 3 * u ^ 10 + 5 * q ^ 8 * u + 4 * q ^ 7 * u ^ 2 + q ^ 6 * u ^ 3
            + q ^ 3 * u ^ 6 + 4 * q ^ 2 * u ^ 7 + 5 * q * u ^ 8 - q ^ 8 + 3 * q ^ 7 * u
            + 8 * q ^ 6 * u ^ 2 + 7 * q ^ 5 * u ^ 3 + 6 * q ^ 4 * u ^ 4 + 7 * q ^ 3 * u ^ 5
            + 8 * q ^ 2 * u ^ 6 + 3 * q * u ^ 7 - u ^ 8 + q ^ 7 + 4 * q ^ 6 * u
            + 11 * q ^ 5 * u ^ 2 + 18 * q ^ 4 * u ^ 3 + 18 * q ^ 3 * u ^ 4 + 11 * q ^ 2 * u ^ 5
            + 4 * q * u ^ 6 + u ^ 7 - 5 * q ^ 6 - 6 * q ^ 5 * u - 5 * q ^ 4 * u ^ 2
            - 5 * q ^ 3 * u ^ 3 - 5 * q ^ 2 * u ^ 4 - 6 * q * u ^ 5 - 5 * u ^ 6 - 4 * q ^ 5
            - 14 * q ^ 4 * u - 17 * q ^ 3 * u ^ 2 - 17 * q ^ 2 * u ^ 3 - 14 * q * u ^ 4
            - 4 * u ^ 5 + 4 * q ^ 4 + q ^ 3 * u - 4 * q ^ 2 * u ^ 2 + q * u ^ 3 + 4 * u ^ 4
            + 3 * q ^ 3 + 8 * q ^ 2 * u + 8 * q * u ^ 2 + 3 * u ^ 3 + q ^ 2 + 2 * q * u + u ^ 2
            - 2 * q - 2 * u) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
        + (-(q ^ 13) - q ^ 12 * u - q ^ 11 * u ^ 2 - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4
            - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7 - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9
            - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 - q * u ^ 12 - u ^ 13 - q ^ 11 * u - q ^ 10 * u ^ 2
            - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5 - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7
            - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10 - q * u ^ 11 + q ^ 11 - q ^ 9 * u ^ 2
            - q ^ 8 * u ^ 3 - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5 - q ^ 5 * u ^ 6 - q ^ 4 * u ^ 7
            - q ^ 3 * u ^ 8 - q ^ 2 * u ^ 9 + u ^ 11 - q ^ 8 * u ^ 2 - 2 * q ^ 7 * u ^ 3
            - 2 * q ^ 6 * u ^ 4 - 2 * q ^ 5 * u ^ 5 - 2 * q ^ 4 * u ^ 6 - 2 * q ^ 3 * u ^ 7
            - q ^ 2 * u ^ 8 + 3 * q ^ 9 + 3 * q ^ 8 * u + 2 * q ^ 7 * u ^ 2 + q ^ 6 * u ^ 3
            + q ^ 3 * u ^ 6 + 2 * q ^ 2 * u ^ 7 + 3 * q * u ^ 8 + 3 * u ^ 9 + 5 * q ^ 7 * u
            + 4 * q ^ 6 * u ^ 2 + 3 * q ^ 5 * u ^ 3 + 3 * q ^ 4 * u ^ 4 + 3 * q ^ 3 * u ^ 5
            + 4 * q ^ 2 * u ^ 6 + 5 * q * u ^ 7 - 3 * q ^ 7 + q ^ 6 * u + 7 * q ^ 5 * u ^ 2
            + 6 * q ^ 4 * u ^ 3 + 6 * q ^ 3 * u ^ 4 + 7 * q ^ 2 * u ^ 5 + q * u ^ 6 - 3 * u ^ 7
            - 3 * q ^ 6 - 6 * q ^ 5 * u - q ^ 4 * u ^ 2 + 4 * q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4
            - 6 * q * u ^ 5 - 3 * u ^ 6 - 7 * q ^ 4 * u - 11 * q ^ 3 * u ^ 2 - 11 * q ^ 2 * u ^ 3
            - 7 * q * u ^ 4 + 4 * q ^ 4 + 2 * q ^ 3 * u - 2 * q ^ 2 * u ^ 2 + 2 * q * u ^ 3
            + 4 * u ^ 4 + 6 * q ^ 2 * u + 6 * q * u ^ 2 - q ^ 2 - 2 * q * u - u ^ 2)
              • (elemSymm L 1 * (elemSymm L 4 * elemSymm L 4))
        + (-(q ^ 13) - q ^ 12 * u - q ^ 11 * u ^ 2 - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4
            - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7 - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9
            - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 - q * u ^ 12 - u ^ 13 + q ^ 12 + u ^ 12
            - q ^ 9 * u ^ 2 - q ^ 8 * u ^ 3 - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5 - q ^ 5 * u ^ 6
            - q ^ 4 * u ^ 7 - q ^ 3 * u ^ 8 - q ^ 2 * u ^ 9 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4
            - q ^ 5 * u ^ 5 - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3
            - 2 * q ^ 5 * u ^ 4 - 2 * q ^ 4 * u ^ 5 - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7 + q ^ 8
            + 3 * q ^ 7 * u + 3 * q ^ 6 * u ^ 2 + 3 * q ^ 5 * u ^ 3 + 4 * q ^ 4 * u ^ 4
            + 3 * q ^ 3 * u ^ 5 + 3 * q ^ 2 * u ^ 6 + 3 * q * u ^ 7 + u ^ 8 - q ^ 7
            + 3 * q ^ 5 * u ^ 2 + 2 * q ^ 4 * u ^ 3 + 2 * q ^ 3 * u ^ 4 + 3 * q ^ 2 * u ^ 5
            - u ^ 7 - 3 * q ^ 5 * u - 3 * q ^ 4 * u ^ 2 - 3 * q ^ 2 * u ^ 4 - 3 * q * u ^ 5
            + q ^ 5 + 2 * q ^ 4 * u + 2 * q * u ^ 4 + u ^ 5 + q ^ 2 * u ^ 2 - q ^ 3 + q ^ 2 * u
            + q * u ^ 2 - u ^ 3 - 2 * q ^ 2 - 4 * q * u - 2 * u ^ 2 + 2 * q + 2 * u)
              • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
        + (-(q ^ 12) - q ^ 11 * u - q ^ 10 * u ^ 2 - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5
            - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7 - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10
            - q * u ^ 11 - u ^ 12 - q ^ 11 - 2 * q ^ 10 * u - 2 * q ^ 9 * u ^ 2
            - 2 * q ^ 8 * u ^ 3 - 2 * q ^ 7 * u ^ 4 - 2 * q ^ 6 * u ^ 5 - 2 * q ^ 5 * u ^ 6
            - 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8 - 2 * q ^ 2 * u ^ 9 - 2 * q * u ^ 10 - u ^ 11
            + 2 * q ^ 10 - q ^ 8 * u ^ 2 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4 - q ^ 5 * u ^ 5
            - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 + 2 * u ^ 10 - 2 * q ^ 7 * u ^ 2
            - 3 * q ^ 6 * u ^ 3 - 3 * q ^ 5 * u ^ 4 - 3 * q ^ 4 * u ^ 5 - 3 * q ^ 3 * u ^ 6
            - 2 * q ^ 2 * u ^ 7 + q ^ 8 + q ^ 7 * u - 2 * q ^ 5 * u ^ 3 - 3 * q ^ 4 * u ^ 4
            - 2 * q ^ 3 * u ^ 5 + q * u ^ 7 + u ^ 8 + 3 * q ^ 7 + 6 * q ^ 6 * u
            + 5 * q ^ 5 * u ^ 2 + 6 * q ^ 4 * u ^ 3 + 6 * q ^ 3 * u ^ 4 + 5 * q ^ 2 * u ^ 5
            + 6 * q * u ^ 6 + 3 * u ^ 7 - q ^ 6 + 7 * q ^ 5 * u + 11 * q ^ 4 * u ^ 2
            + 10 * q ^ 3 * u ^ 3 + 11 * q ^ 2 * u ^ 4 + 7 * q * u ^ 5 - u ^ 6 - 5 * q ^ 5
            - 9 * q ^ 4 * u - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3 - 9 * q * u ^ 4 - 5 * u ^ 5
            + q ^ 4 - 3 * q ^ 3 * u - 6 * q ^ 2 * u ^ 2 - 3 * q * u ^ 3 + u ^ 4 - q ^ 3
            - 3 * q ^ 2 * u - 3 * q * u ^ 2 - u ^ 3 + 2 * q ^ 2 + 4 * q * u + 2 * u ^ 2)
              • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 4))
        + (-(q ^ 10) - q ^ 9 * u - q ^ 8 * u ^ 2 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4 - q ^ 5 * u ^ 5
            - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 - q * u ^ 9 - u ^ 10 + q ^ 9 + u ^ 9
            + q ^ 8 + q ^ 7 * u + q * u ^ 7 + u ^ 8 - q ^ 7 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4
            - u ^ 7 + q ^ 6 + q ^ 5 * u + 2 * q ^ 4 * u ^ 2 + 3 * q ^ 3 * u ^ 3
            + 2 * q ^ 2 * u ^ 4 + q * u ^ 5 + u ^ 6 + 3 * q ^ 4 * u + 3 * q ^ 3 * u ^ 2
            + 3 * q ^ 2 * u ^ 3 + 3 * q * u ^ 4 - 3 * q ^ 4 - 5 * q ^ 3 * u - 4 * q ^ 2 * u ^ 2
            - 5 * q * u ^ 3 - 3 * u ^ 4 + q ^ 3 - 2 * q ^ 2 * u - 2 * q * u ^ 2 + u ^ 3
            + 2 * q ^ 2 + 4 * q * u + 2 * u ^ 2 - q - u)
              • (elemSymm L 3 * (elemSymm L 3 * elemSymm L 3))
        + (-(q ^ 13) - q ^ 12 * u - q ^ 11 * u ^ 2 - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4
            - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7 - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9
            - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 - q * u ^ 12 - u ^ 13 - q ^ 11 * u - q ^ 10 * u ^ 2
            - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5 - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7
            - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10 - q * u ^ 11 - q ^ 10 * u
            - 2 * q ^ 9 * u ^ 2 - 2 * q ^ 8 * u ^ 3 - 2 * q ^ 7 * u ^ 4 - 2 * q ^ 6 * u ^ 5
            - 2 * q ^ 5 * u ^ 6 - 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8 - 2 * q ^ 2 * u ^ 9
            - q * u ^ 10 + q ^ 10 - q ^ 8 * u ^ 2 - 2 * q ^ 7 * u ^ 3 - 2 * q ^ 6 * u ^ 4
            - 2 * q ^ 5 * u ^ 5 - 2 * q ^ 4 * u ^ 6 - 2 * q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 + u ^ 10
            + 2 * q ^ 9 + 3 * q ^ 8 * u + q ^ 7 * u ^ 2 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5
            + q ^ 2 * u ^ 7 + 3 * q * u ^ 8 + 2 * u ^ 9 + q ^ 8 + 5 * q ^ 7 * u
            + 6 * q ^ 6 * u ^ 2 + 5 * q ^ 5 * u ^ 3 + 5 * q ^ 4 * u ^ 4 + 5 * q ^ 3 * u ^ 5
            + 6 * q ^ 2 * u ^ 6 + 5 * q * u ^ 7 + u ^ 8 - q ^ 7 + 3 * q ^ 6 * u
            + 8 * q ^ 5 * u ^ 2 + 10 * q ^ 4 * u ^ 3 + 10 * q ^ 3 * u ^ 4 + 8 * q ^ 2 * u ^ 5
            + 3 * q * u ^ 6 - u ^ 7 - 3 * q ^ 6 - 5 * q ^ 5 * u - 2 * q ^ 4 * u ^ 2
            - q ^ 3 * u ^ 3 - 2 * q ^ 2 * u ^ 4 - 5 * q * u ^ 5 - 3 * u ^ 6 - q ^ 5
            - 6 * q ^ 4 * u - 9 * q ^ 3 * u ^ 2 - 9 * q ^ 2 * u ^ 3 - 6 * q * u ^ 4 - u ^ 5
            - q ^ 3 * u - 3 * q ^ 2 * u ^ 2 - q * u ^ 3 + 2 * q ^ 3 + 3 * q ^ 2 * u
            + 3 * q * u ^ 2 + 2 * u ^ 3 + q ^ 2 + 2 * q * u + u ^ 2 - q - u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
        + (-(q ^ 12) - q ^ 11 * u - q ^ 10 * u ^ 2 - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5
            - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7 - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10
            - q * u ^ 11 - u ^ 12 - q ^ 11 - 2 * q ^ 10 * u - 2 * q ^ 9 * u ^ 2
            - 2 * q ^ 8 * u ^ 3 - 2 * q ^ 7 * u ^ 4 - 2 * q ^ 6 * u ^ 5 - 2 * q ^ 5 * u ^ 6
            - 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8 - 2 * q ^ 2 * u ^ 9 - 2 * q * u ^ 10 - u ^ 11
            - q ^ 10 - 3 * q ^ 9 * u - 4 * q ^ 8 * u ^ 2 - 4 * q ^ 7 * u ^ 3 - 4 * q ^ 6 * u ^ 4
            - 4 * q ^ 5 * u ^ 5 - 4 * q ^ 4 * u ^ 6 - 4 * q ^ 3 * u ^ 7 - 4 * q ^ 2 * u ^ 8
            - 3 * q * u ^ 9 - u ^ 10 + 3 * q ^ 9 - 2 * q ^ 7 * u ^ 2 - 3 * q ^ 6 * u ^ 3
            - 3 * q ^ 5 * u ^ 4 - 3 * q ^ 4 * u ^ 5 - 3 * q ^ 3 * u ^ 6 - 2 * q ^ 2 * u ^ 7
            + 3 * u ^ 9 + 2 * q ^ 8 + 3 * q ^ 7 * u - q ^ 6 * u ^ 2 - 3 * q ^ 5 * u ^ 3
            - 4 * q ^ 4 * u ^ 4 - 3 * q ^ 3 * u ^ 5 - q ^ 2 * u ^ 6 + 3 * q * u ^ 7 + 2 * u ^ 8
            + 6 * q ^ 6 * u + 7 * q ^ 5 * u ^ 2 + 5 * q ^ 4 * u ^ 3 + 5 * q ^ 3 * u ^ 4
            + 7 * q ^ 2 * u ^ 5 + 6 * q * u ^ 6 + q ^ 6 + 6 * q ^ 5 * u + 14 * q ^ 4 * u ^ 2
            + 15 * q ^ 3 * u ^ 3 + 14 * q ^ 2 * u ^ 4 + 6 * q * u ^ 5 + u ^ 6 - q ^ 5
            - 2 * q ^ 4 * u - 2 * q * u ^ 4 - u ^ 5 - 4 * q ^ 4 - 7 * q ^ 3 * u
            - 9 * q ^ 2 * u ^ 2 - 7 * q * u ^ 3 - 4 * u ^ 4 - 5 * q ^ 2 * u - 5 * q * u ^ 2
            + 3 * q ^ 2 + 6 * q * u + 3 * u ^ 2 - q - u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
        + (-(q ^ 11) - q ^ 10 * u - q ^ 9 * u ^ 2 - q ^ 8 * u ^ 3 - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5
            - q ^ 5 * u ^ 6 - q ^ 4 * u ^ 7 - q ^ 3 * u ^ 8 - q ^ 2 * u ^ 9 - q * u ^ 10 - u ^ 11
            - q ^ 10 - 2 * q ^ 9 * u - 2 * q ^ 8 * u ^ 2 - 2 * q ^ 7 * u ^ 3 - 2 * q ^ 6 * u ^ 4
            - 2 * q ^ 5 * u ^ 5 - 2 * q ^ 4 * u ^ 6 - 2 * q ^ 3 * u ^ 7 - 2 * q ^ 2 * u ^ 8
            - 2 * q * u ^ 9 - u ^ 10 - q ^ 9 - 3 * q ^ 8 * u - 4 * q ^ 7 * u ^ 2
            - 4 * q ^ 6 * u ^ 3 - 4 * q ^ 5 * u ^ 4 - 4 * q ^ 4 * u ^ 5 - 4 * q ^ 3 * u ^ 6
            - 4 * q ^ 2 * u ^ 7 - 3 * q * u ^ 8 - u ^ 9 + 2 * q ^ 8 - q ^ 7 * u
            - 3 * q ^ 6 * u ^ 2 - 4 * q ^ 5 * u ^ 3 - 4 * q ^ 4 * u ^ 4 - 4 * q ^ 3 * u ^ 5
            - 3 * q ^ 2 * u ^ 6 - q * u ^ 7 + 2 * u ^ 8 + 3 * q ^ 7 + 3 * q ^ 6 * u
            - q ^ 5 * u ^ 2 - 3 * q ^ 4 * u ^ 3 - 3 * q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5
            + 3 * q * u ^ 6 + 3 * u ^ 7 + 4 * q ^ 6 + 9 * q ^ 5 * u + 9 * q ^ 4 * u ^ 2
            + 8 * q ^ 3 * u ^ 3 + 9 * q ^ 2 * u ^ 4 + 9 * q * u ^ 5 + 4 * u ^ 6 + 10 * q ^ 4 * u
            + 15 * q ^ 3 * u ^ 2 + 15 * q ^ 2 * u ^ 3 + 10 * q * u ^ 4 - 9 * q ^ 4
            - 10 * q ^ 3 * u - 5 * q ^ 2 * u ^ 2 - 10 * q * u ^ 3 - 9 * u ^ 4 - 10 * q ^ 2 * u
            - 10 * q * u ^ 2 + 2 * q ^ 2 + 4 * q * u + 2 * u ^ 2 + q + u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4)))
        + (-(q ^ 10) - q ^ 9 * u - q ^ 8 * u ^ 2 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4 - q ^ 5 * u ^ 5
            - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 - q * u ^ 9 - u ^ 10 - q ^ 9
            - 2 * q ^ 8 * u - 2 * q ^ 7 * u ^ 2 - 2 * q ^ 6 * u ^ 3 - 2 * q ^ 5 * u ^ 4
            - 2 * q ^ 4 * u ^ 5 - 2 * q ^ 3 * u ^ 6 - 2 * q ^ 2 * u ^ 7 - 2 * q * u ^ 8 - u ^ 9
            - 2 * q ^ 7 * u - 3 * q ^ 6 * u ^ 2 - 3 * q ^ 5 * u ^ 3 - 3 * q ^ 4 * u ^ 4
            - 3 * q ^ 3 * u ^ 5 - 3 * q ^ 2 * u ^ 6 - 2 * q * u ^ 7 + q ^ 7 - q ^ 6 * u
            - 3 * q ^ 5 * u ^ 2 - 4 * q ^ 4 * u ^ 3 - 4 * q ^ 3 * u ^ 4 - 3 * q ^ 2 * u ^ 5
            - q * u ^ 6 + u ^ 7 + 2 * q ^ 6 + 3 * q ^ 5 * u + q ^ 4 * u ^ 2 + q ^ 2 * u ^ 4
            + 3 * q * u ^ 5 + 2 * u ^ 6 + 2 * q ^ 5 + 7 * q ^ 4 * u + 8 * q ^ 3 * u ^ 2
            + 8 * q ^ 2 * u ^ 3 + 7 * q * u ^ 4 + 2 * u ^ 5 - 4 * q ^ 4 - 2 * q ^ 3 * u
            + q ^ 2 * u ^ 2 - 2 * q * u ^ 3 - 4 * u ^ 4 + 2 * q ^ 3 - 2 * q ^ 2 * u
            - 2 * q * u ^ 2 + 2 * u ^ 3 + q ^ 2 + 2 * q * u + u ^ 2 - 2 * q - 2 * u)
              • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4)))
        + (-(q ^ 9) - q ^ 8 * u - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5
            - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7 - q * u ^ 8 - u ^ 9 - 2 * q ^ 8 - 3 * q ^ 7 * u
            - 3 * q ^ 6 * u ^ 2 - 3 * q ^ 5 * u ^ 3 - 3 * q ^ 4 * u ^ 4 - 3 * q ^ 3 * u ^ 5
            - 3 * q ^ 2 * u ^ 6 - 3 * q * u ^ 7 - 2 * u ^ 8 + q ^ 7 - 2 * q ^ 6 * u
            - 3 * q ^ 5 * u ^ 2 - 3 * q ^ 4 * u ^ 3 - 3 * q ^ 3 * u ^ 4 - 3 * q ^ 2 * u ^ 5
            - 2 * q * u ^ 6 + u ^ 7 - 2 * q ^ 5 * u - 5 * q ^ 4 * u ^ 2 - 6 * q ^ 3 * u ^ 3
            - 5 * q ^ 2 * u ^ 4 - 2 * q * u ^ 5 + 4 * q ^ 5 + 4 * q ^ 4 * u + 3 * q ^ 3 * u ^ 2
            + 3 * q ^ 2 * u ^ 3 + 4 * q * u ^ 4 + 4 * u ^ 5 + 6 * q ^ 4 + 13 * q ^ 3 * u
            + 14 * q ^ 2 * u ^ 2 + 13 * q * u ^ 3 + 6 * u ^ 4 - 5 * q ^ 3 + 2 * q ^ 2 * u
            + 2 * q * u ^ 2 - 5 * u ^ 3 - 8 * q ^ 2 - 16 * q * u - 8 * u ^ 2 + 5 * q + 5 * u)
              • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3)))
        + (-(q ^ 7) - q ^ 6 * u - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5
            - q * u ^ 6 - u ^ 7 - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4
            - q * u ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3 - q * u ^ 4 + q ^ 4
            + q ^ 3 * u + q * u ^ 3 + u ^ 4 + q ^ 3 + 2 * q ^ 2 * u + 2 * q * u ^ 2 + u ^ 3
            + q ^ 2 + 2 * q * u + u ^ 2 - 2 * q - 2 * u)
              • (elemSymm L 2 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3)))
        + (-(q ^ 9) - q ^ 8 * u - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5
            - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7 - q * u ^ 8 - u ^ 9 - q ^ 7 * u - q ^ 6 * u ^ 2
            - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5 - q ^ 2 * u ^ 6 - q * u ^ 7 + q ^ 7
            - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5 + u ^ 7 + q ^ 6
            + 2 * q ^ 5 * u + q ^ 4 * u ^ 2 + q ^ 3 * u ^ 3 + q ^ 2 * u ^ 4 + 2 * q * u ^ 5
            + u ^ 6 + 2 * q ^ 4 * u + 3 * q ^ 3 * u ^ 2 + 3 * q ^ 2 * u ^ 3 + 2 * q * u ^ 4
            + q ^ 2 * u ^ 2 - q ^ 3 - q ^ 2 * u - q * u ^ 2 - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2
            + q + u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
        + (-(q ^ 8) - q ^ 7 * u - q ^ 6 * u ^ 2 - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5
            - q ^ 2 * u ^ 6 - q * u ^ 7 - u ^ 8 - q ^ 7 - 2 * q ^ 6 * u - 2 * q ^ 5 * u ^ 2
            - 2 * q ^ 4 * u ^ 3 - 2 * q ^ 3 * u ^ 4 - 2 * q ^ 2 * u ^ 5 - 2 * q * u ^ 6 - u ^ 7
            - q ^ 6 - 3 * q ^ 5 * u - 4 * q ^ 4 * u ^ 2 - 4 * q ^ 3 * u ^ 3 - 4 * q ^ 2 * u ^ 4
            - 3 * q * u ^ 5 - u ^ 6 + q ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3
            - q * u ^ 4 + u ^ 5 + 7 * q ^ 4 + 9 * q ^ 3 * u + 8 * q ^ 2 * u ^ 2 + 9 * q * u ^ 3
            + 7 * u ^ 4 - 3 * q ^ 3 + 4 * q ^ 2 * u + 4 * q * u ^ 2 - 3 * u ^ 3 - 4 * q ^ 2
            - 8 * q * u - 4 * u ^ 2 + 2 * q + 2 * u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4))))
        + (-(q ^ 7) - q ^ 6 * u - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5
            - q * u ^ 6 - u ^ 7 - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4
            - q * u ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3 - q * u ^ 4 + q ^ 4
            + q ^ 3 * u + q * u ^ 3 + u ^ 4 + q ^ 3 + 2 * q ^ 2 * u + 2 * q * u ^ 2 + u ^ 3
            + q ^ 2 + 2 * q * u + u ^ 2 - 2 * q - 2 * u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3))))
        + (-(q ^ 6) - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4 - q * u ^ 5
            - u ^ 6 - 2 * q ^ 5 - 3 * q ^ 4 * u - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3
            - 3 * q * u ^ 4 - 2 * u ^ 5 - 3 * q ^ 4 - 6 * q ^ 3 * u - 6 * q ^ 2 * u ^ 2
            - 6 * q * u ^ 3 - 3 * u ^ 4 + 4 * q ^ 3 + q ^ 2 * u + q * u ^ 2 + 4 * u ^ 3
            + 5 * q ^ 2 + 10 * q * u + 5 * u ^ 2 - 3 * q - 3 * u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3))))
        + (-(q ^ 3) - q ^ 2 * u - q * u ^ 2 - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2 + 2 * q + 2 * u)
              • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))))
        + (-(q ^ 4) - q ^ 3 * u - q ^ 2 * u ^ 2 - q * u ^ 3 - u ^ 4 + q ^ 3 + u ^ 3 + q ^ 2
            + 2 * q * u + u ^ 2 - q - u)
              • (elemSymm L 1
                  * (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))))
        + (-(q ^ 3) - q ^ 2 * u - q * u ^ 2 - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2 + 2 * q + 2 * u)
              • (elemSymm L 1
                  * (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))))
        + (-q - u)
              • (elemSymm L 1
                  * (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2)))))
      ) := by
  rw [onePartSweepValue_eq_neg_constantCoeff,
    stageWordTotal_two_three_three_eq hq0 hu0 hq1]
  simp only [map_smul, constantCoeff_smul, map_add, dminus_one_auxVar_pow_mul_C,
    MvPolynomial.constantCoeff_C,
    bop_two_elemSymm_seven, bop_two_elemSymm_one_mul_six, bop_two_elemSymm_two_mul_five,
    bop_two_elemSymm_three_mul_four, bop_two_elemSymm_one_sq_mul_five,
    bop_two_elemSymm_one_mul_two_mul_four, bop_two_elemSymm_one_mul_three_sq,
    bop_two_elemSymm_two_sq_mul_three, bop_two_elemSymm_one_cube_mul_four,
    bop_two_elemSymm_one_sq_mul_two_mul_three, bop_two_elemSymm_one_mul_two_cube,
    bop_two_elemSymm_one_pow_four_mul_three, bop_two_elemSymm_one_cube_mul_two_sq,
    bop_three_elemSymm_six, bop_three_elemSymm_one_mul_five, bop_three_elemSymm_two_mul_four,
    bop_three_elemSymm_three_sq, bop_three_elemSymm_one_sq_mul_four,
    bop_three_elemSymm_one_mul_two_mul_three, bop_three_elemSymm_two_cube,
    bop_three_elemSymm_one_cube_mul_three, bop_three_elemSymm_one_sq_mul_two_sq,
    bop_three_elemSymm_one_pow_four_mul_two, bop_four_elemSymm_five,
    bop_four_elemSymm_one_mul_four, bop_four_elemSymm_two_mul_three,
    bop_four_elemSymm_one_sq_mul_three, bop_four_elemSymm_one_mul_two_sq,
    bop_four_elemSymm_one_cube_mul_two, bop_four_elemSymm_one_pow_five, bop_five_elemSymm_four,
    bop_five_elemSymm_one_mul_three, bop_five_elemSymm_two_sq, bop_five_elemSymm_one_sq_mul_two,
    bop_five_elemSymm_one_pow_four, bop_six_elemSymm_three, bop_six_elemSymm_one_mul_two,
    bop_six_elemSymm_one_cube, bop_seven_elemSymm_two, bop_seven_elemSymm_one_sq,
    bop_eight_elemSymm_one, bop_nine_one]
  module

/-- **`x_2 = onePartOuterValue q u 2 = -quV_3`**, the whole replicated letter on `G_2` bar
its scalar, read off `HJO.Mellit.smul_onePartSweepValue_succ_of_letter` at `A = 1` and the
value above. This is the one datum the outer defect of the one-part step still carried. -/
theorem onePartOuterValue_two (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    onePartOuterValue q u 2 = (q ^ 3 * u ^ 3) • (
          (-(q ^ 19) - q ^ 18 * u - q ^ 17 * u ^ 2 - q ^ 16 * u ^ 3 - q ^ 15 * u ^ 4
            - q ^ 14 * u ^ 5 - q ^ 13 * u ^ 6 - q ^ 12 * u ^ 7 - q ^ 11 * u ^ 8 - q ^ 10 * u ^ 9
            - q ^ 9 * u ^ 10 - q ^ 8 * u ^ 11 - q ^ 7 * u ^ 12 - q ^ 6 * u ^ 13 - q ^ 5 * u ^ 14
            - q ^ 4 * u ^ 15 - q ^ 3 * u ^ 16 - q ^ 2 * u ^ 17 - q * u ^ 18 - u ^ 19 + q ^ 18
            + u ^ 18 + q ^ 17 + q ^ 16 * u + q * u ^ 16 + u ^ 17 + q ^ 15 * u + q ^ 14 * u ^ 2
            + q ^ 2 * u ^ 14 + q * u ^ 15 + q ^ 14 * u + q ^ 13 * u ^ 2 + q ^ 12 * u ^ 3
            + q ^ 3 * u ^ 12 + q ^ 2 * u ^ 13 + q * u ^ 14 - q ^ 14 + q ^ 13 * u
            + 2 * q ^ 12 * u ^ 2 + 2 * q ^ 11 * u ^ 3 + 2 * q ^ 10 * u ^ 4 + q ^ 9 * u ^ 5
            + q ^ 8 * u ^ 6 + q ^ 7 * u ^ 7 + q ^ 6 * u ^ 8 + q ^ 5 * u ^ 9 + 2 * q ^ 4 * u ^ 10
            + 2 * q ^ 3 * u ^ 11 + 2 * q ^ 2 * u ^ 12 + q * u ^ 13 - u ^ 14 - q ^ 13 - q ^ 12 * u
            + 2 * q ^ 11 * u ^ 2 + 2 * q ^ 10 * u ^ 3 + 2 * q ^ 9 * u ^ 4 + 2 * q ^ 8 * u ^ 5
            + q ^ 7 * u ^ 6 + q ^ 6 * u ^ 7 + 2 * q ^ 5 * u ^ 8 + 2 * q ^ 4 * u ^ 9
            + 2 * q ^ 3 * u ^ 10 + 2 * q ^ 2 * u ^ 11 - q * u ^ 12 - u ^ 13 - q ^ 12
            - 4 * q ^ 11 * u - 2 * q ^ 10 * u ^ 2 + 2 * q ^ 9 * u ^ 3 + 2 * q ^ 8 * u ^ 4
            + 3 * q ^ 7 * u ^ 5 + 4 * q ^ 6 * u ^ 6 + 3 * q ^ 5 * u ^ 7 + 2 * q ^ 4 * u ^ 8
            + 2 * q ^ 3 * u ^ 9 - 2 * q ^ 2 * u ^ 10 - 4 * q * u ^ 11 - u ^ 12 + q ^ 11
            - 2 * q ^ 10 * u - 5 * q ^ 9 * u ^ 2 - 2 * q ^ 8 * u ^ 3 + 2 * q ^ 7 * u ^ 4
            + 2 * q ^ 6 * u ^ 5 + 2 * q ^ 5 * u ^ 6 + 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8
            - 5 * q ^ 2 * u ^ 9 - 2 * q * u ^ 10 + u ^ 11 + q ^ 10 - 5 * q ^ 8 * u ^ 2
            - 10 * q ^ 7 * u ^ 3 - 10 * q ^ 6 * u ^ 4 - 9 * q ^ 5 * u ^ 5 - 10 * q ^ 4 * u ^ 6
            - 10 * q ^ 3 * u ^ 7 - 5 * q ^ 2 * u ^ 8 + u ^ 10 + q ^ 9 + 3 * q ^ 8 * u
            + q ^ 7 * u ^ 2 - 3 * q ^ 6 * u ^ 3 - 6 * q ^ 5 * u ^ 4 - 6 * q ^ 4 * u ^ 5
            - 3 * q ^ 3 * u ^ 6 + q ^ 2 * u ^ 7 + 3 * q * u ^ 8 + u ^ 9 + 3 * q ^ 7 * u
            + 6 * q ^ 6 * u ^ 2 + 6 * q ^ 5 * u ^ 3 + 6 * q ^ 4 * u ^ 4 + 6 * q ^ 3 * u ^ 5
            + 6 * q ^ 2 * u ^ 6 + 3 * q * u ^ 7 + q ^ 6 * u + 4 * q ^ 5 * u ^ 2
            + 6 * q ^ 4 * u ^ 3 + 6 * q ^ 3 * u ^ 4 + 4 * q ^ 2 * u ^ 5 + q * u ^ 6 - q ^ 6
            - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 2 * u ^ 4 - q * u ^ 5 - u ^ 6 - q ^ 5
            - 3 * q ^ 4 * u - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3 - 3 * q * u ^ 4 - u ^ 5
            + q ^ 4 - q ^ 2 * u ^ 2 + u ^ 4 + q ^ 2 * u + q * u ^ 2) • elemSymm L 9
        + (-(q ^ 18) - q ^ 17 * u - q ^ 16 * u ^ 2 - q ^ 15 * u ^ 3 - q ^ 14 * u ^ 4
            - q ^ 13 * u ^ 5 - q ^ 12 * u ^ 6 - q ^ 11 * u ^ 7 - q ^ 10 * u ^ 8 - q ^ 9 * u ^ 9
            - q ^ 8 * u ^ 10 - q ^ 7 * u ^ 11 - q ^ 6 * u ^ 12 - q ^ 5 * u ^ 13 - q ^ 4 * u ^ 14
            - q ^ 3 * u ^ 15 - q ^ 2 * u ^ 16 - q * u ^ 17 - u ^ 18 - q ^ 16 * u - q ^ 15 * u ^ 2
            - q ^ 14 * u ^ 3 - q ^ 13 * u ^ 4 - q ^ 12 * u ^ 5 - q ^ 11 * u ^ 6 - q ^ 10 * u ^ 7
            - q ^ 9 * u ^ 8 - q ^ 8 * u ^ 9 - q ^ 7 * u ^ 10 - q ^ 6 * u ^ 11 - q ^ 5 * u ^ 12
            - q ^ 4 * u ^ 13 - q ^ 3 * u ^ 14 - q ^ 2 * u ^ 15 - q * u ^ 16 + q ^ 16
            - q ^ 14 * u ^ 2 - q ^ 13 * u ^ 3 - q ^ 12 * u ^ 4 - q ^ 11 * u ^ 5 - q ^ 10 * u ^ 6
            - q ^ 9 * u ^ 7 - q ^ 8 * u ^ 8 - q ^ 7 * u ^ 9 - q ^ 6 * u ^ 10 - q ^ 5 * u ^ 11
            - q ^ 4 * u ^ 12 - q ^ 3 * u ^ 13 - q ^ 2 * u ^ 14 + u ^ 16 + q ^ 15 + q ^ 14 * u
            - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4 - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7
            - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9 - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12
            + q * u ^ 14 + u ^ 15 + q ^ 14 + 2 * q ^ 13 * u + q ^ 12 * u ^ 2 - q ^ 10 * u ^ 4
            - q ^ 9 * u ^ 5 - q ^ 8 * u ^ 6 - q ^ 7 * u ^ 7 - q ^ 6 * u ^ 8 - q ^ 5 * u ^ 9
            - q ^ 4 * u ^ 10 + q ^ 2 * u ^ 12 + 2 * q * u ^ 13 + u ^ 14 + q ^ 13 + 4 * q ^ 12 * u
            + 4 * q ^ 11 * u ^ 2 + 3 * q ^ 10 * u ^ 3 + 2 * q ^ 9 * u ^ 4 + q ^ 8 * u ^ 5
            + q ^ 7 * u ^ 6 + q ^ 6 * u ^ 7 + q ^ 5 * u ^ 8 + 2 * q ^ 4 * u ^ 9
            + 3 * q ^ 3 * u ^ 10 + 4 * q ^ 2 * u ^ 11 + 4 * q * u ^ 12 + u ^ 13 - q ^ 12
            + 4 * q ^ 11 * u + 7 * q ^ 10 * u ^ 2 + 6 * q ^ 9 * u ^ 3 + 5 * q ^ 8 * u ^ 4
            + 4 * q ^ 7 * u ^ 5 + 3 * q ^ 6 * u ^ 6 + 4 * q ^ 5 * u ^ 7 + 5 * q ^ 4 * u ^ 8
            + 6 * q ^ 3 * u ^ 9 + 7 * q ^ 2 * u ^ 10 + 4 * q * u ^ 11 - u ^ 12 - 4 * q ^ 11
            - 3 * q ^ 10 * u + 5 * q ^ 9 * u ^ 2 + 8 * q ^ 8 * u ^ 3 + 8 * q ^ 7 * u ^ 4
            + 9 * q ^ 6 * u ^ 5 + 9 * q ^ 5 * u ^ 6 + 8 * q ^ 4 * u ^ 7 + 8 * q ^ 3 * u ^ 8
            + 5 * q ^ 2 * u ^ 9 - 3 * q * u ^ 10 - 4 * u ^ 11 - 2 * q ^ 10 - 8 * q ^ 9 * u
            - 4 * q ^ 8 * u ^ 2 + 6 * q ^ 7 * u ^ 3 + 10 * q ^ 6 * u ^ 4 + 10 * q ^ 5 * u ^ 5
            + 10 * q ^ 4 * u ^ 6 + 6 * q ^ 3 * u ^ 7 - 4 * q ^ 2 * u ^ 8 - 8 * q * u ^ 9
            - 2 * u ^ 10 - 8 * q ^ 8 * u - 16 * q ^ 7 * u ^ 2 - 16 * q ^ 6 * u ^ 3
            - 12 * q ^ 5 * u ^ 4 - 12 * q ^ 4 * u ^ 5 - 16 * q ^ 3 * u ^ 6 - 16 * q ^ 2 * u ^ 7
            - 8 * q * u ^ 8 + 3 * q ^ 8 - q ^ 7 * u - 12 * q ^ 6 * u ^ 2 - 20 * q ^ 5 * u ^ 3
            - 23 * q ^ 4 * u ^ 4 - 20 * q ^ 3 * u ^ 5 - 12 * q ^ 2 * u ^ 6 - q * u ^ 7 + 3 * u ^ 8
            + 3 * q ^ 7 + 9 * q ^ 6 * u + 7 * q ^ 5 * u ^ 2 + 3 * q ^ 4 * u ^ 3
            + 3 * q ^ 3 * u ^ 4 + 7 * q ^ 2 * u ^ 5 + 9 * q * u ^ 6 + 3 * u ^ 7 + q ^ 6
            + 7 * q ^ 5 * u + 14 * q ^ 4 * u ^ 2 + 15 * q ^ 3 * u ^ 3 + 14 * q ^ 2 * u ^ 4
            + 7 * q * u ^ 5 + u ^ 6 - q ^ 5 + q ^ 4 * u + 4 * q ^ 3 * u ^ 2 + 4 * q ^ 2 * u ^ 3
            + q * u ^ 4 - u ^ 5 - 3 * q ^ 4 - 5 * q ^ 3 * u - 5 * q ^ 2 * u ^ 2 - 5 * q * u ^ 3
            - 3 * u ^ 4 - 3 * q ^ 2 * u - 3 * q * u ^ 2 + q ^ 2 + 2 * q * u + u ^ 2)
              • (elemSymm L 1 * elemSymm L 8)
        + (-(q ^ 17) - q ^ 16 * u - q ^ 15 * u ^ 2 - q ^ 14 * u ^ 3 - q ^ 13 * u ^ 4
            - q ^ 12 * u ^ 5 - q ^ 11 * u ^ 6 - q ^ 10 * u ^ 7 - q ^ 9 * u ^ 8 - q ^ 8 * u ^ 9
            - q ^ 7 * u ^ 10 - q ^ 6 * u ^ 11 - q ^ 5 * u ^ 12 - q ^ 4 * u ^ 13 - q ^ 3 * u ^ 14
            - q ^ 2 * u ^ 15 - q * u ^ 16 - u ^ 17 + q ^ 16 + u ^ 16 - q ^ 13 * u ^ 2
            - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4 - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7
            - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9 - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12
            - q ^ 2 * u ^ 13 + q ^ 14 + q ^ 13 * u + q ^ 12 * u ^ 2 + q ^ 2 * u ^ 12 + q * u ^ 13
            + u ^ 14 + q ^ 12 * u - q ^ 9 * u ^ 4 - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7
            - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9 + q * u ^ 12 - q ^ 12 + q ^ 11 * u
            + 2 * q ^ 10 * u ^ 2 + q ^ 9 * u ^ 3 + q ^ 8 * u ^ 4 + q ^ 4 * u ^ 8 + q ^ 3 * u ^ 9
            + 2 * q ^ 2 * u ^ 10 + q * u ^ 11 - u ^ 12 + 2 * q ^ 9 * u ^ 2 + 2 * q ^ 8 * u ^ 3
            + q ^ 7 * u ^ 4 + q ^ 6 * u ^ 5 + q ^ 5 * u ^ 6 + q ^ 4 * u ^ 7 + 2 * q ^ 3 * u ^ 8
            + 2 * q ^ 2 * u ^ 9 + 2 * q ^ 8 * u ^ 2 + 6 * q ^ 7 * u ^ 3 + 7 * q ^ 6 * u ^ 4
            + 7 * q ^ 5 * u ^ 5 + 7 * q ^ 4 * u ^ 6 + 6 * q ^ 3 * u ^ 7 + 2 * q ^ 2 * u ^ 8
            - q ^ 8 * u + 2 * q ^ 6 * u ^ 3 + 5 * q ^ 5 * u ^ 4 + 5 * q ^ 4 * u ^ 5
            + 2 * q ^ 3 * u ^ 6 - q * u ^ 8 - q ^ 8 - 5 * q ^ 7 * u - 9 * q ^ 6 * u ^ 2
            - 12 * q ^ 5 * u ^ 3 - 14 * q ^ 4 * u ^ 4 - 12 * q ^ 3 * u ^ 5 - 9 * q ^ 2 * u ^ 6
            - 5 * q * u ^ 7 - u ^ 8 + q ^ 7 + 2 * q ^ 6 * u - q ^ 5 * u ^ 2 - 2 * q ^ 4 * u ^ 3
            - 2 * q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5 + 2 * q * u ^ 6 + u ^ 7 + 3 * q ^ 5 * u
            + 6 * q ^ 4 * u ^ 2 + 5 * q ^ 3 * u ^ 3 + 6 * q ^ 2 * u ^ 4 + 3 * q * u ^ 5
            + q ^ 3 * u ^ 2 + q ^ 2 * u ^ 3 - q ^ 4 - 2 * q ^ 3 * u - 3 * q ^ 2 * u ^ 2
            - 2 * q * u ^ 3 - u ^ 4 + q ^ 3 + u ^ 3 + q ^ 2 + 2 * q * u + u ^ 2 - q - u)
              • (elemSymm L 2 * elemSymm L 7)
        + (-(q ^ 16) - q ^ 15 * u - q ^ 14 * u ^ 2 - q ^ 13 * u ^ 3 - q ^ 12 * u ^ 4
            - q ^ 11 * u ^ 5 - q ^ 10 * u ^ 6 - q ^ 9 * u ^ 7 - q ^ 8 * u ^ 8 - q ^ 7 * u ^ 9
            - q ^ 6 * u ^ 10 - q ^ 5 * u ^ 11 - q ^ 4 * u ^ 12 - q ^ 3 * u ^ 13 - q ^ 2 * u ^ 14
            - q * u ^ 15 - u ^ 16 + q ^ 15 + u ^ 15 + q ^ 14 + q ^ 13 * u + q * u ^ 13 + u ^ 14
            - 2 * q ^ 13 - q ^ 12 * u - q ^ 11 * u ^ 2 - 2 * q ^ 10 * u ^ 3 - 2 * q ^ 9 * u ^ 4
            - 2 * q ^ 8 * u ^ 5 - 2 * q ^ 7 * u ^ 6 - 2 * q ^ 6 * u ^ 7 - 2 * q ^ 5 * u ^ 8
            - 2 * q ^ 4 * u ^ 9 - 2 * q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 - q * u ^ 12 - 2 * u ^ 13
            + 2 * q ^ 12 + q ^ 11 * u + q ^ 10 * u ^ 2 + q ^ 9 * u ^ 3 + q ^ 3 * u ^ 9
            + q ^ 2 * u ^ 10 + q * u ^ 11 + 2 * u ^ 12 + q ^ 11 + 3 * q ^ 10 * u
            + 2 * q ^ 9 * u ^ 2 + 2 * q ^ 8 * u ^ 3 + 2 * q ^ 7 * u ^ 4 + q ^ 6 * u ^ 5
            + q ^ 5 * u ^ 6 + 2 * q ^ 4 * u ^ 7 + 2 * q ^ 3 * u ^ 8 + 2 * q ^ 2 * u ^ 9
            + 3 * q * u ^ 10 + u ^ 11 - 2 * q ^ 10 + 3 * q ^ 8 * u ^ 2 + q ^ 7 * u ^ 3
            + q ^ 6 * u ^ 4 + 2 * q ^ 5 * u ^ 5 + q ^ 4 * u ^ 6 + q ^ 3 * u ^ 7
            + 3 * q ^ 2 * u ^ 8 - 2 * u ^ 10 - 2 * q ^ 8 * u + q ^ 7 * u ^ 2 + 6 * q ^ 6 * u ^ 3
            + 4 * q ^ 5 * u ^ 4 + 4 * q ^ 4 * u ^ 5 + 6 * q ^ 3 * u ^ 6 + q ^ 2 * u ^ 7
            - 2 * q * u ^ 8 + 2 * q ^ 7 * u + 3 * q ^ 5 * u ^ 3 + 8 * q ^ 4 * u ^ 4
            + 3 * q ^ 3 * u ^ 5 + 2 * q * u ^ 7 - 3 * q ^ 7 - 6 * q ^ 6 * u - 7 * q ^ 5 * u ^ 2
            - 13 * q ^ 4 * u ^ 3 - 13 * q ^ 3 * u ^ 4 - 7 * q ^ 2 * u ^ 5 - 6 * q * u ^ 6
            - 3 * u ^ 7 + q ^ 6 - 3 * q ^ 5 * u - 4 * q ^ 4 * u ^ 2 - 2 * q ^ 3 * u ^ 3
            - 4 * q ^ 2 * u ^ 4 - 3 * q * u ^ 5 + u ^ 6 + 3 * q ^ 5 + 4 * q ^ 4 * u
            + 2 * q ^ 3 * u ^ 2 + 2 * q ^ 2 * u ^ 3 + 4 * q * u ^ 4 + 3 * u ^ 5 + q ^ 4
            + 4 * q ^ 3 * u + 5 * q ^ 2 * u ^ 2 + 4 * q * u ^ 3 + u ^ 4 - q ^ 3 + q ^ 2 * u
            + q * u ^ 2 - u ^ 3 - 2 * q ^ 2 - 4 * q * u - 2 * u ^ 2 + q + u)
              • (elemSymm L 3 * elemSymm L 6)
        + (-(q ^ 15) - q ^ 14 * u - q ^ 13 * u ^ 2 - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4
            - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7 - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9
            - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12 - q ^ 2 * u ^ 13 - q * u ^ 14
            - u ^ 15 - q ^ 13 * u - q ^ 12 * u ^ 2 - q ^ 11 * u ^ 3 - q ^ 10 * u ^ 4
            - q ^ 9 * u ^ 5 - q ^ 8 * u ^ 6 - q ^ 7 * u ^ 7 - q ^ 6 * u ^ 8 - q ^ 5 * u ^ 9
            - q ^ 4 * u ^ 10 - q ^ 3 * u ^ 11 - q ^ 2 * u ^ 12 - q * u ^ 13 + 2 * q ^ 13
            + q ^ 12 * u + q * u ^ 12 + 2 * u ^ 13 + q ^ 12 + 2 * q ^ 11 * u + q ^ 10 * u ^ 2
            + q ^ 2 * u ^ 10 + 2 * q * u ^ 11 + u ^ 12 - q ^ 11 + q ^ 10 * u + q ^ 9 * u ^ 2
            - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5 - q ^ 5 * u ^ 6 - q ^ 4 * u ^ 7 + q ^ 2 * u ^ 9
            + q * u ^ 10 - u ^ 11 + 2 * q ^ 9 * u + 3 * q ^ 8 * u ^ 2 + 3 * q ^ 7 * u ^ 3
            + 2 * q ^ 6 * u ^ 4 + q ^ 5 * u ^ 5 + 2 * q ^ 4 * u ^ 6 + 3 * q ^ 3 * u ^ 7
            + 3 * q ^ 2 * u ^ 8 + 2 * q * u ^ 9 - 2 * q ^ 9 + 3 * q ^ 7 * u ^ 2
            + 3 * q ^ 6 * u ^ 3 + 4 * q ^ 5 * u ^ 4 + 4 * q ^ 4 * u ^ 5 + 3 * q ^ 3 * u ^ 6
            + 3 * q ^ 2 * u ^ 7 - 2 * u ^ 9 - q ^ 8 - 4 * q ^ 7 * u + q ^ 6 * u ^ 2
            + 5 * q ^ 5 * u ^ 3 + 4 * q ^ 4 * u ^ 4 + 5 * q ^ 3 * u ^ 5 + q ^ 2 * u ^ 6
            - 4 * q * u ^ 7 - u ^ 8 - 5 * q ^ 6 * u - 8 * q ^ 5 * u ^ 2 - 4 * q ^ 4 * u ^ 3
            - 4 * q ^ 3 * u ^ 4 - 8 * q ^ 2 * u ^ 5 - 5 * q * u ^ 6 + 2 * q ^ 6 - q ^ 5 * u
            - 8 * q ^ 4 * u ^ 2 - 13 * q ^ 3 * u ^ 3 - 8 * q ^ 2 * u ^ 4 - q * u ^ 5 + 2 * u ^ 6
            + 2 * q ^ 5 + 7 * q ^ 4 * u + 6 * q ^ 3 * u ^ 2 + 6 * q ^ 2 * u ^ 3 + 7 * q * u ^ 4
            + 2 * u ^ 5 - 2 * q ^ 4 + 2 * q ^ 3 * u + 6 * q ^ 2 * u ^ 2 + 2 * q * u ^ 3
            - 2 * u ^ 4 - 3 * q ^ 2 * u - 3 * q * u ^ 2) • (elemSymm L 4 * elemSymm L 5)
        + (-(q ^ 16) - q ^ 15 * u - q ^ 14 * u ^ 2 - q ^ 13 * u ^ 3 - q ^ 12 * u ^ 4
            - q ^ 11 * u ^ 5 - q ^ 10 * u ^ 6 - q ^ 9 * u ^ 7 - q ^ 8 * u ^ 8 - q ^ 7 * u ^ 9
            - q ^ 6 * u ^ 10 - q ^ 5 * u ^ 11 - q ^ 4 * u ^ 12 - q ^ 3 * u ^ 13 - q ^ 2 * u ^ 14
            - q * u ^ 15 - u ^ 16 - q ^ 14 * u - q ^ 13 * u ^ 2 - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4
            - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7 - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9
            - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12 - q ^ 2 * u ^ 13 - q * u ^ 14
            - q ^ 13 * u - 2 * q ^ 12 * u ^ 2 - 2 * q ^ 11 * u ^ 3 - 2 * q ^ 10 * u ^ 4
            - 2 * q ^ 9 * u ^ 5 - 2 * q ^ 8 * u ^ 6 - 2 * q ^ 7 * u ^ 7 - 2 * q ^ 6 * u ^ 8
            - 2 * q ^ 5 * u ^ 9 - 2 * q ^ 4 * u ^ 10 - 2 * q ^ 3 * u ^ 11 - 2 * q ^ 2 * u ^ 12
            - q * u ^ 13 + q ^ 13 - q ^ 11 * u ^ 2 - 2 * q ^ 10 * u ^ 3 - 2 * q ^ 9 * u ^ 4
            - 2 * q ^ 8 * u ^ 5 - 2 * q ^ 7 * u ^ 6 - 2 * q ^ 6 * u ^ 7 - 2 * q ^ 5 * u ^ 8
            - 2 * q ^ 4 * u ^ 9 - 2 * q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 + u ^ 13 + 2 * q ^ 12
            + 2 * q ^ 11 * u - q ^ 9 * u ^ 3 - 2 * q ^ 8 * u ^ 4 - 2 * q ^ 7 * u ^ 5
            - 2 * q ^ 6 * u ^ 6 - 2 * q ^ 5 * u ^ 7 - 2 * q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9
            + 2 * q * u ^ 11 + 2 * u ^ 12 + 2 * q ^ 11 + 6 * q ^ 10 * u + 5 * q ^ 9 * u ^ 2
            + 3 * q ^ 8 * u ^ 3 + 2 * q ^ 7 * u ^ 4 + q ^ 6 * u ^ 5 + q ^ 5 * u ^ 6
            + 2 * q ^ 4 * u ^ 7 + 3 * q ^ 3 * u ^ 8 + 5 * q ^ 2 * u ^ 9 + 6 * q * u ^ 10
            + 2 * u ^ 11 - q ^ 10 + 5 * q ^ 9 * u + 9 * q ^ 8 * u ^ 2 + 7 * q ^ 7 * u ^ 3
            + 6 * q ^ 6 * u ^ 4 + 6 * q ^ 5 * u ^ 5 + 6 * q ^ 4 * u ^ 6 + 7 * q ^ 3 * u ^ 7
            + 9 * q ^ 2 * u ^ 8 + 5 * q * u ^ 9 - u ^ 10 - 3 * q ^ 9 - q ^ 8 * u
            + 8 * q ^ 7 * u ^ 2 + 14 * q ^ 6 * u ^ 3 + 14 * q ^ 5 * u ^ 4 + 14 * q ^ 4 * u ^ 5
            + 14 * q ^ 3 * u ^ 6 + 8 * q ^ 2 * u ^ 7 - q * u ^ 8 - 3 * u ^ 9 - 3 * q ^ 8
            - 7 * q ^ 7 * u - 4 * q ^ 6 * u ^ 2 + 3 * q ^ 5 * u ^ 3 + 7 * q ^ 4 * u ^ 4
            + 3 * q ^ 3 * u ^ 5 - 4 * q ^ 2 * u ^ 6 - 7 * q * u ^ 7 - 3 * u ^ 8 - 2 * q ^ 7
            - 12 * q ^ 6 * u - 19 * q ^ 5 * u ^ 2 - 22 * q ^ 4 * u ^ 3 - 22 * q ^ 3 * u ^ 4
            - 19 * q ^ 2 * u ^ 5 - 12 * q * u ^ 6 - 2 * u ^ 7 + 3 * q ^ 6 - 9 * q ^ 4 * u ^ 2
            - 11 * q ^ 3 * u ^ 3 - 9 * q ^ 2 * u ^ 4 + 3 * u ^ 6 + 3 * q ^ 5 + 8 * q ^ 4 * u
            + 9 * q ^ 3 * u ^ 2 + 9 * q ^ 2 * u ^ 3 + 8 * q * u ^ 4 + 3 * u ^ 5 + 2 * q ^ 4
            + 6 * q ^ 3 * u + 9 * q ^ 2 * u ^ 2 + 6 * q * u ^ 3 + 2 * u ^ 4 - 2 * q ^ 3
            - q ^ 2 * u - q * u ^ 2 - 2 * u ^ 3 - 2 * q ^ 2 - 4 * q * u - 2 * u ^ 2 + q + u)
              • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
        + (-(q ^ 15) - q ^ 14 * u - q ^ 13 * u ^ 2 - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4
            - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7 - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9
            - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12 - q ^ 2 * u ^ 13 - q * u ^ 14
            - u ^ 15 - q ^ 14 - 2 * q ^ 13 * u - 2 * q ^ 12 * u ^ 2 - 2 * q ^ 11 * u ^ 3
            - 2 * q ^ 10 * u ^ 4 - 2 * q ^ 9 * u ^ 5 - 2 * q ^ 8 * u ^ 6 - 2 * q ^ 7 * u ^ 7
            - 2 * q ^ 6 * u ^ 8 - 2 * q ^ 5 * u ^ 9 - 2 * q ^ 4 * u ^ 10 - 2 * q ^ 3 * u ^ 11
            - 2 * q ^ 2 * u ^ 12 - 2 * q * u ^ 13 - u ^ 14 + 2 * q ^ 13 - q ^ 11 * u ^ 2
            - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4 - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7
            - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9 - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 + 2 * u ^ 13
            - 2 * q ^ 10 * u ^ 2 - 3 * q ^ 9 * u ^ 3 - 3 * q ^ 8 * u ^ 4 - 3 * q ^ 7 * u ^ 5
            - 3 * q ^ 6 * u ^ 6 - 3 * q ^ 5 * u ^ 7 - 3 * q ^ 4 * u ^ 8 - 3 * q ^ 3 * u ^ 9
            - 2 * q ^ 2 * u ^ 10 + q ^ 11 + q ^ 10 * u - 2 * q ^ 8 * u ^ 3 - 3 * q ^ 7 * u ^ 4
            - 3 * q ^ 6 * u ^ 5 - 3 * q ^ 5 * u ^ 6 - 3 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8
            + q * u ^ 10 + u ^ 11 + 2 * q ^ 10 + 5 * q ^ 9 * u + 3 * q ^ 8 * u ^ 2
            + 2 * q ^ 7 * u ^ 3 - q ^ 5 * u ^ 5 + 2 * q ^ 3 * u ^ 7 + 3 * q ^ 2 * u ^ 8
            + 5 * q * u ^ 9 + 2 * u ^ 10 - q ^ 9 + 5 * q ^ 8 * u + 9 * q ^ 7 * u ^ 2
            + 7 * q ^ 6 * u ^ 3 + 8 * q ^ 5 * u ^ 4 + 8 * q ^ 4 * u ^ 5 + 7 * q ^ 3 * u ^ 6
            + 9 * q ^ 2 * u ^ 7 + 5 * q * u ^ 8 - u ^ 9 - 2 * q ^ 8 - q ^ 7 * u
            + 9 * q ^ 6 * u ^ 2 + 14 * q ^ 5 * u ^ 3 + 13 * q ^ 4 * u ^ 4 + 14 * q ^ 3 * u ^ 5
            + 9 * q ^ 2 * u ^ 6 - q * u ^ 7 - 2 * u ^ 8 - 5 * q ^ 6 * u - 5 * q ^ 5 * u ^ 2
            + q ^ 4 * u ^ 3 + q ^ 3 * u ^ 4 - 5 * q ^ 2 * u ^ 5 - 5 * q * u ^ 6 - q ^ 6
            - 5 * q ^ 5 * u - 13 * q ^ 4 * u ^ 2 - 16 * q ^ 3 * u ^ 3 - 13 * q ^ 2 * u ^ 4
            - 5 * q * u ^ 5 - u ^ 6 - q ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3
            - q * u ^ 4 - u ^ 5 + 2 * q ^ 4 + 3 * q ^ 3 * u + 4 * q ^ 2 * u ^ 2 + 3 * q * u ^ 3
            + 2 * u ^ 4 + q ^ 2 * u + q * u ^ 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
        + (-(q ^ 14) - q ^ 13 * u - q ^ 12 * u ^ 2 - q ^ 11 * u ^ 3 - q ^ 10 * u ^ 4
            - q ^ 9 * u ^ 5 - q ^ 8 * u ^ 6 - q ^ 7 * u ^ 7 - q ^ 6 * u ^ 8 - q ^ 5 * u ^ 9
            - q ^ 4 * u ^ 10 - q ^ 3 * u ^ 11 - q ^ 2 * u ^ 12 - q * u ^ 13 - u ^ 14 - q ^ 12 * u
            - q ^ 11 * u ^ 2 - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4 - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6
            - q ^ 6 * u ^ 7 - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9 - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11
            - q * u ^ 12 - q ^ 12 - 2 * q ^ 11 * u - 3 * q ^ 10 * u ^ 2 - 3 * q ^ 9 * u ^ 3
            - 3 * q ^ 8 * u ^ 4 - 3 * q ^ 7 * u ^ 5 - 3 * q ^ 6 * u ^ 6 - 3 * q ^ 5 * u ^ 7
            - 3 * q ^ 4 * u ^ 8 - 3 * q ^ 3 * u ^ 9 - 3 * q ^ 2 * u ^ 10 - 2 * q * u ^ 11 - u ^ 12
            + 2 * q ^ 11 - q ^ 9 * u ^ 2 - 2 * q ^ 8 * u ^ 3 - 2 * q ^ 7 * u ^ 4
            - 2 * q ^ 6 * u ^ 5 - 2 * q ^ 5 * u ^ 6 - 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8
            - q ^ 2 * u ^ 9 + 2 * u ^ 11 + 3 * q ^ 10 + 3 * q ^ 9 * u - q ^ 7 * u ^ 3
            - 2 * q ^ 6 * u ^ 4 - 2 * q ^ 5 * u ^ 5 - 2 * q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7
            + 3 * q * u ^ 9 + 3 * u ^ 10 + 5 * q ^ 8 * u + 4 * q ^ 7 * u ^ 2 + q ^ 6 * u ^ 3
            + q ^ 3 * u ^ 6 + 4 * q ^ 2 * u ^ 7 + 5 * q * u ^ 8 - q ^ 8 + 3 * q ^ 7 * u
            + 8 * q ^ 6 * u ^ 2 + 7 * q ^ 5 * u ^ 3 + 6 * q ^ 4 * u ^ 4 + 7 * q ^ 3 * u ^ 5
            + 8 * q ^ 2 * u ^ 6 + 3 * q * u ^ 7 - u ^ 8 + q ^ 7 + 4 * q ^ 6 * u
            + 11 * q ^ 5 * u ^ 2 + 18 * q ^ 4 * u ^ 3 + 18 * q ^ 3 * u ^ 4 + 11 * q ^ 2 * u ^ 5
            + 4 * q * u ^ 6 + u ^ 7 - 5 * q ^ 6 - 6 * q ^ 5 * u - 5 * q ^ 4 * u ^ 2
            - 5 * q ^ 3 * u ^ 3 - 5 * q ^ 2 * u ^ 4 - 6 * q * u ^ 5 - 5 * u ^ 6 - 4 * q ^ 5
            - 14 * q ^ 4 * u - 17 * q ^ 3 * u ^ 2 - 17 * q ^ 2 * u ^ 3 - 14 * q * u ^ 4
            - 4 * u ^ 5 + 4 * q ^ 4 + q ^ 3 * u - 4 * q ^ 2 * u ^ 2 + q * u ^ 3 + 4 * u ^ 4
            + 3 * q ^ 3 + 8 * q ^ 2 * u + 8 * q * u ^ 2 + 3 * u ^ 3 + q ^ 2 + 2 * q * u + u ^ 2
            - 2 * q - 2 * u) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
        + (-(q ^ 13) - q ^ 12 * u - q ^ 11 * u ^ 2 - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4
            - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7 - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9
            - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 - q * u ^ 12 - u ^ 13 - q ^ 11 * u - q ^ 10 * u ^ 2
            - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5 - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7
            - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10 - q * u ^ 11 + q ^ 11 - q ^ 9 * u ^ 2
            - q ^ 8 * u ^ 3 - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5 - q ^ 5 * u ^ 6 - q ^ 4 * u ^ 7
            - q ^ 3 * u ^ 8 - q ^ 2 * u ^ 9 + u ^ 11 - q ^ 8 * u ^ 2 - 2 * q ^ 7 * u ^ 3
            - 2 * q ^ 6 * u ^ 4 - 2 * q ^ 5 * u ^ 5 - 2 * q ^ 4 * u ^ 6 - 2 * q ^ 3 * u ^ 7
            - q ^ 2 * u ^ 8 + 3 * q ^ 9 + 3 * q ^ 8 * u + 2 * q ^ 7 * u ^ 2 + q ^ 6 * u ^ 3
            + q ^ 3 * u ^ 6 + 2 * q ^ 2 * u ^ 7 + 3 * q * u ^ 8 + 3 * u ^ 9 + 5 * q ^ 7 * u
            + 4 * q ^ 6 * u ^ 2 + 3 * q ^ 5 * u ^ 3 + 3 * q ^ 4 * u ^ 4 + 3 * q ^ 3 * u ^ 5
            + 4 * q ^ 2 * u ^ 6 + 5 * q * u ^ 7 - 3 * q ^ 7 + q ^ 6 * u + 7 * q ^ 5 * u ^ 2
            + 6 * q ^ 4 * u ^ 3 + 6 * q ^ 3 * u ^ 4 + 7 * q ^ 2 * u ^ 5 + q * u ^ 6 - 3 * u ^ 7
            - 3 * q ^ 6 - 6 * q ^ 5 * u - q ^ 4 * u ^ 2 + 4 * q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4
            - 6 * q * u ^ 5 - 3 * u ^ 6 - 7 * q ^ 4 * u - 11 * q ^ 3 * u ^ 2 - 11 * q ^ 2 * u ^ 3
            - 7 * q * u ^ 4 + 4 * q ^ 4 + 2 * q ^ 3 * u - 2 * q ^ 2 * u ^ 2 + 2 * q * u ^ 3
            + 4 * u ^ 4 + 6 * q ^ 2 * u + 6 * q * u ^ 2 - q ^ 2 - 2 * q * u - u ^ 2)
              • (elemSymm L 1 * (elemSymm L 4 * elemSymm L 4))
        + (-(q ^ 13) - q ^ 12 * u - q ^ 11 * u ^ 2 - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4
            - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7 - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9
            - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 - q * u ^ 12 - u ^ 13 + q ^ 12 + u ^ 12
            - q ^ 9 * u ^ 2 - q ^ 8 * u ^ 3 - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5 - q ^ 5 * u ^ 6
            - q ^ 4 * u ^ 7 - q ^ 3 * u ^ 8 - q ^ 2 * u ^ 9 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4
            - q ^ 5 * u ^ 5 - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3
            - 2 * q ^ 5 * u ^ 4 - 2 * q ^ 4 * u ^ 5 - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7 + q ^ 8
            + 3 * q ^ 7 * u + 3 * q ^ 6 * u ^ 2 + 3 * q ^ 5 * u ^ 3 + 4 * q ^ 4 * u ^ 4
            + 3 * q ^ 3 * u ^ 5 + 3 * q ^ 2 * u ^ 6 + 3 * q * u ^ 7 + u ^ 8 - q ^ 7
            + 3 * q ^ 5 * u ^ 2 + 2 * q ^ 4 * u ^ 3 + 2 * q ^ 3 * u ^ 4 + 3 * q ^ 2 * u ^ 5
            - u ^ 7 - 3 * q ^ 5 * u - 3 * q ^ 4 * u ^ 2 - 3 * q ^ 2 * u ^ 4 - 3 * q * u ^ 5
            + q ^ 5 + 2 * q ^ 4 * u + 2 * q * u ^ 4 + u ^ 5 + q ^ 2 * u ^ 2 - q ^ 3 + q ^ 2 * u
            + q * u ^ 2 - u ^ 3 - 2 * q ^ 2 - 4 * q * u - 2 * u ^ 2 + 2 * q + 2 * u)
              • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
        + (-(q ^ 12) - q ^ 11 * u - q ^ 10 * u ^ 2 - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5
            - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7 - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10
            - q * u ^ 11 - u ^ 12 - q ^ 11 - 2 * q ^ 10 * u - 2 * q ^ 9 * u ^ 2
            - 2 * q ^ 8 * u ^ 3 - 2 * q ^ 7 * u ^ 4 - 2 * q ^ 6 * u ^ 5 - 2 * q ^ 5 * u ^ 6
            - 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8 - 2 * q ^ 2 * u ^ 9 - 2 * q * u ^ 10 - u ^ 11
            + 2 * q ^ 10 - q ^ 8 * u ^ 2 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4 - q ^ 5 * u ^ 5
            - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 + 2 * u ^ 10 - 2 * q ^ 7 * u ^ 2
            - 3 * q ^ 6 * u ^ 3 - 3 * q ^ 5 * u ^ 4 - 3 * q ^ 4 * u ^ 5 - 3 * q ^ 3 * u ^ 6
            - 2 * q ^ 2 * u ^ 7 + q ^ 8 + q ^ 7 * u - 2 * q ^ 5 * u ^ 3 - 3 * q ^ 4 * u ^ 4
            - 2 * q ^ 3 * u ^ 5 + q * u ^ 7 + u ^ 8 + 3 * q ^ 7 + 6 * q ^ 6 * u
            + 5 * q ^ 5 * u ^ 2 + 6 * q ^ 4 * u ^ 3 + 6 * q ^ 3 * u ^ 4 + 5 * q ^ 2 * u ^ 5
            + 6 * q * u ^ 6 + 3 * u ^ 7 - q ^ 6 + 7 * q ^ 5 * u + 11 * q ^ 4 * u ^ 2
            + 10 * q ^ 3 * u ^ 3 + 11 * q ^ 2 * u ^ 4 + 7 * q * u ^ 5 - u ^ 6 - 5 * q ^ 5
            - 9 * q ^ 4 * u - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3 - 9 * q * u ^ 4 - 5 * u ^ 5
            + q ^ 4 - 3 * q ^ 3 * u - 6 * q ^ 2 * u ^ 2 - 3 * q * u ^ 3 + u ^ 4 - q ^ 3
            - 3 * q ^ 2 * u - 3 * q * u ^ 2 - u ^ 3 + 2 * q ^ 2 + 4 * q * u + 2 * u ^ 2)
              • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 4))
        + (-(q ^ 10) - q ^ 9 * u - q ^ 8 * u ^ 2 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4 - q ^ 5 * u ^ 5
            - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 - q * u ^ 9 - u ^ 10 + q ^ 9 + u ^ 9
            + q ^ 8 + q ^ 7 * u + q * u ^ 7 + u ^ 8 - q ^ 7 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4
            - u ^ 7 + q ^ 6 + q ^ 5 * u + 2 * q ^ 4 * u ^ 2 + 3 * q ^ 3 * u ^ 3
            + 2 * q ^ 2 * u ^ 4 + q * u ^ 5 + u ^ 6 + 3 * q ^ 4 * u + 3 * q ^ 3 * u ^ 2
            + 3 * q ^ 2 * u ^ 3 + 3 * q * u ^ 4 - 3 * q ^ 4 - 5 * q ^ 3 * u - 4 * q ^ 2 * u ^ 2
            - 5 * q * u ^ 3 - 3 * u ^ 4 + q ^ 3 - 2 * q ^ 2 * u - 2 * q * u ^ 2 + u ^ 3
            + 2 * q ^ 2 + 4 * q * u + 2 * u ^ 2 - q - u)
              • (elemSymm L 3 * (elemSymm L 3 * elemSymm L 3))
        + (-(q ^ 13) - q ^ 12 * u - q ^ 11 * u ^ 2 - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4
            - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7 - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9
            - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 - q * u ^ 12 - u ^ 13 - q ^ 11 * u - q ^ 10 * u ^ 2
            - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5 - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7
            - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10 - q * u ^ 11 - q ^ 10 * u
            - 2 * q ^ 9 * u ^ 2 - 2 * q ^ 8 * u ^ 3 - 2 * q ^ 7 * u ^ 4 - 2 * q ^ 6 * u ^ 5
            - 2 * q ^ 5 * u ^ 6 - 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8 - 2 * q ^ 2 * u ^ 9
            - q * u ^ 10 + q ^ 10 - q ^ 8 * u ^ 2 - 2 * q ^ 7 * u ^ 3 - 2 * q ^ 6 * u ^ 4
            - 2 * q ^ 5 * u ^ 5 - 2 * q ^ 4 * u ^ 6 - 2 * q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 + u ^ 10
            + 2 * q ^ 9 + 3 * q ^ 8 * u + q ^ 7 * u ^ 2 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5
            + q ^ 2 * u ^ 7 + 3 * q * u ^ 8 + 2 * u ^ 9 + q ^ 8 + 5 * q ^ 7 * u
            + 6 * q ^ 6 * u ^ 2 + 5 * q ^ 5 * u ^ 3 + 5 * q ^ 4 * u ^ 4 + 5 * q ^ 3 * u ^ 5
            + 6 * q ^ 2 * u ^ 6 + 5 * q * u ^ 7 + u ^ 8 - q ^ 7 + 3 * q ^ 6 * u
            + 8 * q ^ 5 * u ^ 2 + 10 * q ^ 4 * u ^ 3 + 10 * q ^ 3 * u ^ 4 + 8 * q ^ 2 * u ^ 5
            + 3 * q * u ^ 6 - u ^ 7 - 3 * q ^ 6 - 5 * q ^ 5 * u - 2 * q ^ 4 * u ^ 2
            - q ^ 3 * u ^ 3 - 2 * q ^ 2 * u ^ 4 - 5 * q * u ^ 5 - 3 * u ^ 6 - q ^ 5
            - 6 * q ^ 4 * u - 9 * q ^ 3 * u ^ 2 - 9 * q ^ 2 * u ^ 3 - 6 * q * u ^ 4 - u ^ 5
            - q ^ 3 * u - 3 * q ^ 2 * u ^ 2 - q * u ^ 3 + 2 * q ^ 3 + 3 * q ^ 2 * u
            + 3 * q * u ^ 2 + 2 * u ^ 3 + q ^ 2 + 2 * q * u + u ^ 2 - q - u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
        + (-(q ^ 12) - q ^ 11 * u - q ^ 10 * u ^ 2 - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5
            - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7 - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10
            - q * u ^ 11 - u ^ 12 - q ^ 11 - 2 * q ^ 10 * u - 2 * q ^ 9 * u ^ 2
            - 2 * q ^ 8 * u ^ 3 - 2 * q ^ 7 * u ^ 4 - 2 * q ^ 6 * u ^ 5 - 2 * q ^ 5 * u ^ 6
            - 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8 - 2 * q ^ 2 * u ^ 9 - 2 * q * u ^ 10 - u ^ 11
            - q ^ 10 - 3 * q ^ 9 * u - 4 * q ^ 8 * u ^ 2 - 4 * q ^ 7 * u ^ 3 - 4 * q ^ 6 * u ^ 4
            - 4 * q ^ 5 * u ^ 5 - 4 * q ^ 4 * u ^ 6 - 4 * q ^ 3 * u ^ 7 - 4 * q ^ 2 * u ^ 8
            - 3 * q * u ^ 9 - u ^ 10 + 3 * q ^ 9 - 2 * q ^ 7 * u ^ 2 - 3 * q ^ 6 * u ^ 3
            - 3 * q ^ 5 * u ^ 4 - 3 * q ^ 4 * u ^ 5 - 3 * q ^ 3 * u ^ 6 - 2 * q ^ 2 * u ^ 7
            + 3 * u ^ 9 + 2 * q ^ 8 + 3 * q ^ 7 * u - q ^ 6 * u ^ 2 - 3 * q ^ 5 * u ^ 3
            - 4 * q ^ 4 * u ^ 4 - 3 * q ^ 3 * u ^ 5 - q ^ 2 * u ^ 6 + 3 * q * u ^ 7 + 2 * u ^ 8
            + 6 * q ^ 6 * u + 7 * q ^ 5 * u ^ 2 + 5 * q ^ 4 * u ^ 3 + 5 * q ^ 3 * u ^ 4
            + 7 * q ^ 2 * u ^ 5 + 6 * q * u ^ 6 + q ^ 6 + 6 * q ^ 5 * u + 14 * q ^ 4 * u ^ 2
            + 15 * q ^ 3 * u ^ 3 + 14 * q ^ 2 * u ^ 4 + 6 * q * u ^ 5 + u ^ 6 - q ^ 5
            - 2 * q ^ 4 * u - 2 * q * u ^ 4 - u ^ 5 - 4 * q ^ 4 - 7 * q ^ 3 * u
            - 9 * q ^ 2 * u ^ 2 - 7 * q * u ^ 3 - 4 * u ^ 4 - 5 * q ^ 2 * u - 5 * q * u ^ 2
            + 3 * q ^ 2 + 6 * q * u + 3 * u ^ 2 - q - u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
        + (-(q ^ 11) - q ^ 10 * u - q ^ 9 * u ^ 2 - q ^ 8 * u ^ 3 - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5
            - q ^ 5 * u ^ 6 - q ^ 4 * u ^ 7 - q ^ 3 * u ^ 8 - q ^ 2 * u ^ 9 - q * u ^ 10 - u ^ 11
            - q ^ 10 - 2 * q ^ 9 * u - 2 * q ^ 8 * u ^ 2 - 2 * q ^ 7 * u ^ 3 - 2 * q ^ 6 * u ^ 4
            - 2 * q ^ 5 * u ^ 5 - 2 * q ^ 4 * u ^ 6 - 2 * q ^ 3 * u ^ 7 - 2 * q ^ 2 * u ^ 8
            - 2 * q * u ^ 9 - u ^ 10 - q ^ 9 - 3 * q ^ 8 * u - 4 * q ^ 7 * u ^ 2
            - 4 * q ^ 6 * u ^ 3 - 4 * q ^ 5 * u ^ 4 - 4 * q ^ 4 * u ^ 5 - 4 * q ^ 3 * u ^ 6
            - 4 * q ^ 2 * u ^ 7 - 3 * q * u ^ 8 - u ^ 9 + 2 * q ^ 8 - q ^ 7 * u
            - 3 * q ^ 6 * u ^ 2 - 4 * q ^ 5 * u ^ 3 - 4 * q ^ 4 * u ^ 4 - 4 * q ^ 3 * u ^ 5
            - 3 * q ^ 2 * u ^ 6 - q * u ^ 7 + 2 * u ^ 8 + 3 * q ^ 7 + 3 * q ^ 6 * u
            - q ^ 5 * u ^ 2 - 3 * q ^ 4 * u ^ 3 - 3 * q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5
            + 3 * q * u ^ 6 + 3 * u ^ 7 + 4 * q ^ 6 + 9 * q ^ 5 * u + 9 * q ^ 4 * u ^ 2
            + 8 * q ^ 3 * u ^ 3 + 9 * q ^ 2 * u ^ 4 + 9 * q * u ^ 5 + 4 * u ^ 6 + 10 * q ^ 4 * u
            + 15 * q ^ 3 * u ^ 2 + 15 * q ^ 2 * u ^ 3 + 10 * q * u ^ 4 - 9 * q ^ 4
            - 10 * q ^ 3 * u - 5 * q ^ 2 * u ^ 2 - 10 * q * u ^ 3 - 9 * u ^ 4 - 10 * q ^ 2 * u
            - 10 * q * u ^ 2 + 2 * q ^ 2 + 4 * q * u + 2 * u ^ 2 + q + u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4)))
        + (-(q ^ 10) - q ^ 9 * u - q ^ 8 * u ^ 2 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4 - q ^ 5 * u ^ 5
            - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 - q * u ^ 9 - u ^ 10 - q ^ 9
            - 2 * q ^ 8 * u - 2 * q ^ 7 * u ^ 2 - 2 * q ^ 6 * u ^ 3 - 2 * q ^ 5 * u ^ 4
            - 2 * q ^ 4 * u ^ 5 - 2 * q ^ 3 * u ^ 6 - 2 * q ^ 2 * u ^ 7 - 2 * q * u ^ 8 - u ^ 9
            - 2 * q ^ 7 * u - 3 * q ^ 6 * u ^ 2 - 3 * q ^ 5 * u ^ 3 - 3 * q ^ 4 * u ^ 4
            - 3 * q ^ 3 * u ^ 5 - 3 * q ^ 2 * u ^ 6 - 2 * q * u ^ 7 + q ^ 7 - q ^ 6 * u
            - 3 * q ^ 5 * u ^ 2 - 4 * q ^ 4 * u ^ 3 - 4 * q ^ 3 * u ^ 4 - 3 * q ^ 2 * u ^ 5
            - q * u ^ 6 + u ^ 7 + 2 * q ^ 6 + 3 * q ^ 5 * u + q ^ 4 * u ^ 2 + q ^ 2 * u ^ 4
            + 3 * q * u ^ 5 + 2 * u ^ 6 + 2 * q ^ 5 + 7 * q ^ 4 * u + 8 * q ^ 3 * u ^ 2
            + 8 * q ^ 2 * u ^ 3 + 7 * q * u ^ 4 + 2 * u ^ 5 - 4 * q ^ 4 - 2 * q ^ 3 * u
            + q ^ 2 * u ^ 2 - 2 * q * u ^ 3 - 4 * u ^ 4 + 2 * q ^ 3 - 2 * q ^ 2 * u
            - 2 * q * u ^ 2 + 2 * u ^ 3 + q ^ 2 + 2 * q * u + u ^ 2 - 2 * q - 2 * u)
              • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4)))
        + (-(q ^ 9) - q ^ 8 * u - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5
            - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7 - q * u ^ 8 - u ^ 9 - 2 * q ^ 8 - 3 * q ^ 7 * u
            - 3 * q ^ 6 * u ^ 2 - 3 * q ^ 5 * u ^ 3 - 3 * q ^ 4 * u ^ 4 - 3 * q ^ 3 * u ^ 5
            - 3 * q ^ 2 * u ^ 6 - 3 * q * u ^ 7 - 2 * u ^ 8 + q ^ 7 - 2 * q ^ 6 * u
            - 3 * q ^ 5 * u ^ 2 - 3 * q ^ 4 * u ^ 3 - 3 * q ^ 3 * u ^ 4 - 3 * q ^ 2 * u ^ 5
            - 2 * q * u ^ 6 + u ^ 7 - 2 * q ^ 5 * u - 5 * q ^ 4 * u ^ 2 - 6 * q ^ 3 * u ^ 3
            - 5 * q ^ 2 * u ^ 4 - 2 * q * u ^ 5 + 4 * q ^ 5 + 4 * q ^ 4 * u + 3 * q ^ 3 * u ^ 2
            + 3 * q ^ 2 * u ^ 3 + 4 * q * u ^ 4 + 4 * u ^ 5 + 6 * q ^ 4 + 13 * q ^ 3 * u
            + 14 * q ^ 2 * u ^ 2 + 13 * q * u ^ 3 + 6 * u ^ 4 - 5 * q ^ 3 + 2 * q ^ 2 * u
            + 2 * q * u ^ 2 - 5 * u ^ 3 - 8 * q ^ 2 - 16 * q * u - 8 * u ^ 2 + 5 * q + 5 * u)
              • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3)))
        + (-(q ^ 7) - q ^ 6 * u - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5
            - q * u ^ 6 - u ^ 7 - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4
            - q * u ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3 - q * u ^ 4 + q ^ 4
            + q ^ 3 * u + q * u ^ 3 + u ^ 4 + q ^ 3 + 2 * q ^ 2 * u + 2 * q * u ^ 2 + u ^ 3
            + q ^ 2 + 2 * q * u + u ^ 2 - 2 * q - 2 * u)
              • (elemSymm L 2 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3)))
        + (-(q ^ 9) - q ^ 8 * u - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5
            - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7 - q * u ^ 8 - u ^ 9 - q ^ 7 * u - q ^ 6 * u ^ 2
            - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5 - q ^ 2 * u ^ 6 - q * u ^ 7 + q ^ 7
            - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5 + u ^ 7 + q ^ 6
            + 2 * q ^ 5 * u + q ^ 4 * u ^ 2 + q ^ 3 * u ^ 3 + q ^ 2 * u ^ 4 + 2 * q * u ^ 5
            + u ^ 6 + 2 * q ^ 4 * u + 3 * q ^ 3 * u ^ 2 + 3 * q ^ 2 * u ^ 3 + 2 * q * u ^ 4
            + q ^ 2 * u ^ 2 - q ^ 3 - q ^ 2 * u - q * u ^ 2 - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2
            + q + u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
        + (-(q ^ 8) - q ^ 7 * u - q ^ 6 * u ^ 2 - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5
            - q ^ 2 * u ^ 6 - q * u ^ 7 - u ^ 8 - q ^ 7 - 2 * q ^ 6 * u - 2 * q ^ 5 * u ^ 2
            - 2 * q ^ 4 * u ^ 3 - 2 * q ^ 3 * u ^ 4 - 2 * q ^ 2 * u ^ 5 - 2 * q * u ^ 6 - u ^ 7
            - q ^ 6 - 3 * q ^ 5 * u - 4 * q ^ 4 * u ^ 2 - 4 * q ^ 3 * u ^ 3 - 4 * q ^ 2 * u ^ 4
            - 3 * q * u ^ 5 - u ^ 6 + q ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3
            - q * u ^ 4 + u ^ 5 + 7 * q ^ 4 + 9 * q ^ 3 * u + 8 * q ^ 2 * u ^ 2 + 9 * q * u ^ 3
            + 7 * u ^ 4 - 3 * q ^ 3 + 4 * q ^ 2 * u + 4 * q * u ^ 2 - 3 * u ^ 3 - 4 * q ^ 2
            - 8 * q * u - 4 * u ^ 2 + 2 * q + 2 * u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4))))
        + (-(q ^ 7) - q ^ 6 * u - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5
            - q * u ^ 6 - u ^ 7 - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4
            - q * u ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3 - q * u ^ 4 + q ^ 4
            + q ^ 3 * u + q * u ^ 3 + u ^ 4 + q ^ 3 + 2 * q ^ 2 * u + 2 * q * u ^ 2 + u ^ 3
            + q ^ 2 + 2 * q * u + u ^ 2 - 2 * q - 2 * u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3))))
        + (-(q ^ 6) - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4 - q * u ^ 5
            - u ^ 6 - 2 * q ^ 5 - 3 * q ^ 4 * u - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3
            - 3 * q * u ^ 4 - 2 * u ^ 5 - 3 * q ^ 4 - 6 * q ^ 3 * u - 6 * q ^ 2 * u ^ 2
            - 6 * q * u ^ 3 - 3 * u ^ 4 + 4 * q ^ 3 + q ^ 2 * u + q * u ^ 2 + 4 * u ^ 3
            + 5 * q ^ 2 + 10 * q * u + 5 * u ^ 2 - 3 * q - 3 * u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3))))
        + (-(q ^ 3) - q ^ 2 * u - q * u ^ 2 - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2 + 2 * q + 2 * u)
              • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))))
        + (-(q ^ 4) - q ^ 3 * u - q ^ 2 * u ^ 2 - q * u ^ 3 - u ^ 4 + q ^ 3 + u ^ 3 + q ^ 2
            + 2 * q * u + u ^ 2 - q - u)
              • (elemSymm L 1
                  * (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))))
        + (-(q ^ 3) - q ^ 2 * u - q * u ^ 2 - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2 + 2 * q + 2 * u)
              • (elemSymm L 1
                  * (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))))
        + (-q - u)
              • (elemSymm L 1
                  * (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2)))))
      ) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have hne : (-((1 - q) ^ 2) : L) ≠ 0 := neg_ne_zero.2 (pow_ne_zero 2 h1q)
  have h := smul_onePartSweepValue_succ_of_letter (L := L) hq0 hu0 hq1 1
  rw [show (1 : ℕ) + 2 = 3 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
    onePartSweepValue_three_eq hq0 hu0 hq1] at h
  refine smul_right_injective (Lambda L) hne ?_
  dsimp only
  rw [← h, smul_smul, smul_smul,
    show q * u * (1 - q) ^ 2 * -(q ^ 2 * u ^ 2)
      = -((1 - q) ^ 2) * (q ^ 3 * u ^ 3) from by ring]

/-- **THE RESIDUAL AT `[3]`, NAMED EXACTLY.** The `hlhs` clause at `(a,b) = (2,3)` and the
composition `[3]` holds as soon as the *creation* side takes this one explicit value:
`HJO.Mellit.lhsAt_two_three_singleton_iff_onePartSweepValue` at `A = 3` says the clause is
`Θ(h_3)(1) = V_3`, and `HJO.Mellit.onePartSweepValue_three_eq` is `V_3`.

**This is an implication and not a decision.** Nothing in this library evaluates
`Θ(h_3)(1)`: there is no `h_3` analogue of
`HJO.Mellit.theta_completeHomog_two_apply_one_smul`, and the four weight-nine slope values a
`Θ`-free `[3]` needs — `Q_{2,3}^3(1)`, `Q_{4,6}(Q_{2,3}1)`, `Q_{2,3}(Q_{4,6}1)`, `Q_{6,9}(1)`
— are none of them evaluated. So what this says is exactly: **the sweep side of `[3]` is
finished, and the obligation that remains is this equation in `Λ` and nothing else.** -/
theorem lhsAt_two_three_three_of_creation (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hcre : Θ (completeHomog L 3) 1 = (-(q ^ 2 * u ^ 2)) •
          ((-(q ^ 19) - q ^ 18 * u - q ^ 17 * u ^ 2 - q ^ 16 * u ^ 3 - q ^ 15 * u ^ 4
            - q ^ 14 * u ^ 5 - q ^ 13 * u ^ 6 - q ^ 12 * u ^ 7 - q ^ 11 * u ^ 8 - q ^ 10 * u ^ 9
            - q ^ 9 * u ^ 10 - q ^ 8 * u ^ 11 - q ^ 7 * u ^ 12 - q ^ 6 * u ^ 13 - q ^ 5 * u ^ 14
            - q ^ 4 * u ^ 15 - q ^ 3 * u ^ 16 - q ^ 2 * u ^ 17 - q * u ^ 18 - u ^ 19 + q ^ 18
            + u ^ 18 + q ^ 17 + q ^ 16 * u + q * u ^ 16 + u ^ 17 + q ^ 15 * u + q ^ 14 * u ^ 2
            + q ^ 2 * u ^ 14 + q * u ^ 15 + q ^ 14 * u + q ^ 13 * u ^ 2 + q ^ 12 * u ^ 3
            + q ^ 3 * u ^ 12 + q ^ 2 * u ^ 13 + q * u ^ 14 - q ^ 14 + q ^ 13 * u
            + 2 * q ^ 12 * u ^ 2 + 2 * q ^ 11 * u ^ 3 + 2 * q ^ 10 * u ^ 4 + q ^ 9 * u ^ 5
            + q ^ 8 * u ^ 6 + q ^ 7 * u ^ 7 + q ^ 6 * u ^ 8 + q ^ 5 * u ^ 9 + 2 * q ^ 4 * u ^ 10
            + 2 * q ^ 3 * u ^ 11 + 2 * q ^ 2 * u ^ 12 + q * u ^ 13 - u ^ 14 - q ^ 13 - q ^ 12 * u
            + 2 * q ^ 11 * u ^ 2 + 2 * q ^ 10 * u ^ 3 + 2 * q ^ 9 * u ^ 4 + 2 * q ^ 8 * u ^ 5
            + q ^ 7 * u ^ 6 + q ^ 6 * u ^ 7 + 2 * q ^ 5 * u ^ 8 + 2 * q ^ 4 * u ^ 9
            + 2 * q ^ 3 * u ^ 10 + 2 * q ^ 2 * u ^ 11 - q * u ^ 12 - u ^ 13 - q ^ 12
            - 4 * q ^ 11 * u - 2 * q ^ 10 * u ^ 2 + 2 * q ^ 9 * u ^ 3 + 2 * q ^ 8 * u ^ 4
            + 3 * q ^ 7 * u ^ 5 + 4 * q ^ 6 * u ^ 6 + 3 * q ^ 5 * u ^ 7 + 2 * q ^ 4 * u ^ 8
            + 2 * q ^ 3 * u ^ 9 - 2 * q ^ 2 * u ^ 10 - 4 * q * u ^ 11 - u ^ 12 + q ^ 11
            - 2 * q ^ 10 * u - 5 * q ^ 9 * u ^ 2 - 2 * q ^ 8 * u ^ 3 + 2 * q ^ 7 * u ^ 4
            + 2 * q ^ 6 * u ^ 5 + 2 * q ^ 5 * u ^ 6 + 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8
            - 5 * q ^ 2 * u ^ 9 - 2 * q * u ^ 10 + u ^ 11 + q ^ 10 - 5 * q ^ 8 * u ^ 2
            - 10 * q ^ 7 * u ^ 3 - 10 * q ^ 6 * u ^ 4 - 9 * q ^ 5 * u ^ 5 - 10 * q ^ 4 * u ^ 6
            - 10 * q ^ 3 * u ^ 7 - 5 * q ^ 2 * u ^ 8 + u ^ 10 + q ^ 9 + 3 * q ^ 8 * u
            + q ^ 7 * u ^ 2 - 3 * q ^ 6 * u ^ 3 - 6 * q ^ 5 * u ^ 4 - 6 * q ^ 4 * u ^ 5
            - 3 * q ^ 3 * u ^ 6 + q ^ 2 * u ^ 7 + 3 * q * u ^ 8 + u ^ 9 + 3 * q ^ 7 * u
            + 6 * q ^ 6 * u ^ 2 + 6 * q ^ 5 * u ^ 3 + 6 * q ^ 4 * u ^ 4 + 6 * q ^ 3 * u ^ 5
            + 6 * q ^ 2 * u ^ 6 + 3 * q * u ^ 7 + q ^ 6 * u + 4 * q ^ 5 * u ^ 2
            + 6 * q ^ 4 * u ^ 3 + 6 * q ^ 3 * u ^ 4 + 4 * q ^ 2 * u ^ 5 + q * u ^ 6 - q ^ 6
            - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 2 * u ^ 4 - q * u ^ 5 - u ^ 6 - q ^ 5
            - 3 * q ^ 4 * u - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3 - 3 * q * u ^ 4 - u ^ 5
            + q ^ 4 - q ^ 2 * u ^ 2 + u ^ 4 + q ^ 2 * u + q * u ^ 2) • elemSymm L 9
        + (-(q ^ 18) - q ^ 17 * u - q ^ 16 * u ^ 2 - q ^ 15 * u ^ 3 - q ^ 14 * u ^ 4
            - q ^ 13 * u ^ 5 - q ^ 12 * u ^ 6 - q ^ 11 * u ^ 7 - q ^ 10 * u ^ 8 - q ^ 9 * u ^ 9
            - q ^ 8 * u ^ 10 - q ^ 7 * u ^ 11 - q ^ 6 * u ^ 12 - q ^ 5 * u ^ 13 - q ^ 4 * u ^ 14
            - q ^ 3 * u ^ 15 - q ^ 2 * u ^ 16 - q * u ^ 17 - u ^ 18 - q ^ 16 * u - q ^ 15 * u ^ 2
            - q ^ 14 * u ^ 3 - q ^ 13 * u ^ 4 - q ^ 12 * u ^ 5 - q ^ 11 * u ^ 6 - q ^ 10 * u ^ 7
            - q ^ 9 * u ^ 8 - q ^ 8 * u ^ 9 - q ^ 7 * u ^ 10 - q ^ 6 * u ^ 11 - q ^ 5 * u ^ 12
            - q ^ 4 * u ^ 13 - q ^ 3 * u ^ 14 - q ^ 2 * u ^ 15 - q * u ^ 16 + q ^ 16
            - q ^ 14 * u ^ 2 - q ^ 13 * u ^ 3 - q ^ 12 * u ^ 4 - q ^ 11 * u ^ 5 - q ^ 10 * u ^ 6
            - q ^ 9 * u ^ 7 - q ^ 8 * u ^ 8 - q ^ 7 * u ^ 9 - q ^ 6 * u ^ 10 - q ^ 5 * u ^ 11
            - q ^ 4 * u ^ 12 - q ^ 3 * u ^ 13 - q ^ 2 * u ^ 14 + u ^ 16 + q ^ 15 + q ^ 14 * u
            - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4 - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7
            - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9 - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12
            + q * u ^ 14 + u ^ 15 + q ^ 14 + 2 * q ^ 13 * u + q ^ 12 * u ^ 2 - q ^ 10 * u ^ 4
            - q ^ 9 * u ^ 5 - q ^ 8 * u ^ 6 - q ^ 7 * u ^ 7 - q ^ 6 * u ^ 8 - q ^ 5 * u ^ 9
            - q ^ 4 * u ^ 10 + q ^ 2 * u ^ 12 + 2 * q * u ^ 13 + u ^ 14 + q ^ 13 + 4 * q ^ 12 * u
            + 4 * q ^ 11 * u ^ 2 + 3 * q ^ 10 * u ^ 3 + 2 * q ^ 9 * u ^ 4 + q ^ 8 * u ^ 5
            + q ^ 7 * u ^ 6 + q ^ 6 * u ^ 7 + q ^ 5 * u ^ 8 + 2 * q ^ 4 * u ^ 9
            + 3 * q ^ 3 * u ^ 10 + 4 * q ^ 2 * u ^ 11 + 4 * q * u ^ 12 + u ^ 13 - q ^ 12
            + 4 * q ^ 11 * u + 7 * q ^ 10 * u ^ 2 + 6 * q ^ 9 * u ^ 3 + 5 * q ^ 8 * u ^ 4
            + 4 * q ^ 7 * u ^ 5 + 3 * q ^ 6 * u ^ 6 + 4 * q ^ 5 * u ^ 7 + 5 * q ^ 4 * u ^ 8
            + 6 * q ^ 3 * u ^ 9 + 7 * q ^ 2 * u ^ 10 + 4 * q * u ^ 11 - u ^ 12 - 4 * q ^ 11
            - 3 * q ^ 10 * u + 5 * q ^ 9 * u ^ 2 + 8 * q ^ 8 * u ^ 3 + 8 * q ^ 7 * u ^ 4
            + 9 * q ^ 6 * u ^ 5 + 9 * q ^ 5 * u ^ 6 + 8 * q ^ 4 * u ^ 7 + 8 * q ^ 3 * u ^ 8
            + 5 * q ^ 2 * u ^ 9 - 3 * q * u ^ 10 - 4 * u ^ 11 - 2 * q ^ 10 - 8 * q ^ 9 * u
            - 4 * q ^ 8 * u ^ 2 + 6 * q ^ 7 * u ^ 3 + 10 * q ^ 6 * u ^ 4 + 10 * q ^ 5 * u ^ 5
            + 10 * q ^ 4 * u ^ 6 + 6 * q ^ 3 * u ^ 7 - 4 * q ^ 2 * u ^ 8 - 8 * q * u ^ 9
            - 2 * u ^ 10 - 8 * q ^ 8 * u - 16 * q ^ 7 * u ^ 2 - 16 * q ^ 6 * u ^ 3
            - 12 * q ^ 5 * u ^ 4 - 12 * q ^ 4 * u ^ 5 - 16 * q ^ 3 * u ^ 6 - 16 * q ^ 2 * u ^ 7
            - 8 * q * u ^ 8 + 3 * q ^ 8 - q ^ 7 * u - 12 * q ^ 6 * u ^ 2 - 20 * q ^ 5 * u ^ 3
            - 23 * q ^ 4 * u ^ 4 - 20 * q ^ 3 * u ^ 5 - 12 * q ^ 2 * u ^ 6 - q * u ^ 7 + 3 * u ^ 8
            + 3 * q ^ 7 + 9 * q ^ 6 * u + 7 * q ^ 5 * u ^ 2 + 3 * q ^ 4 * u ^ 3
            + 3 * q ^ 3 * u ^ 4 + 7 * q ^ 2 * u ^ 5 + 9 * q * u ^ 6 + 3 * u ^ 7 + q ^ 6
            + 7 * q ^ 5 * u + 14 * q ^ 4 * u ^ 2 + 15 * q ^ 3 * u ^ 3 + 14 * q ^ 2 * u ^ 4
            + 7 * q * u ^ 5 + u ^ 6 - q ^ 5 + q ^ 4 * u + 4 * q ^ 3 * u ^ 2 + 4 * q ^ 2 * u ^ 3
            + q * u ^ 4 - u ^ 5 - 3 * q ^ 4 - 5 * q ^ 3 * u - 5 * q ^ 2 * u ^ 2 - 5 * q * u ^ 3
            - 3 * u ^ 4 - 3 * q ^ 2 * u - 3 * q * u ^ 2 + q ^ 2 + 2 * q * u + u ^ 2)
              • (elemSymm L 1 * elemSymm L 8)
        + (-(q ^ 17) - q ^ 16 * u - q ^ 15 * u ^ 2 - q ^ 14 * u ^ 3 - q ^ 13 * u ^ 4
            - q ^ 12 * u ^ 5 - q ^ 11 * u ^ 6 - q ^ 10 * u ^ 7 - q ^ 9 * u ^ 8 - q ^ 8 * u ^ 9
            - q ^ 7 * u ^ 10 - q ^ 6 * u ^ 11 - q ^ 5 * u ^ 12 - q ^ 4 * u ^ 13 - q ^ 3 * u ^ 14
            - q ^ 2 * u ^ 15 - q * u ^ 16 - u ^ 17 + q ^ 16 + u ^ 16 - q ^ 13 * u ^ 2
            - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4 - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7
            - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9 - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12
            - q ^ 2 * u ^ 13 + q ^ 14 + q ^ 13 * u + q ^ 12 * u ^ 2 + q ^ 2 * u ^ 12 + q * u ^ 13
            + u ^ 14 + q ^ 12 * u - q ^ 9 * u ^ 4 - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7
            - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9 + q * u ^ 12 - q ^ 12 + q ^ 11 * u
            + 2 * q ^ 10 * u ^ 2 + q ^ 9 * u ^ 3 + q ^ 8 * u ^ 4 + q ^ 4 * u ^ 8 + q ^ 3 * u ^ 9
            + 2 * q ^ 2 * u ^ 10 + q * u ^ 11 - u ^ 12 + 2 * q ^ 9 * u ^ 2 + 2 * q ^ 8 * u ^ 3
            + q ^ 7 * u ^ 4 + q ^ 6 * u ^ 5 + q ^ 5 * u ^ 6 + q ^ 4 * u ^ 7 + 2 * q ^ 3 * u ^ 8
            + 2 * q ^ 2 * u ^ 9 + 2 * q ^ 8 * u ^ 2 + 6 * q ^ 7 * u ^ 3 + 7 * q ^ 6 * u ^ 4
            + 7 * q ^ 5 * u ^ 5 + 7 * q ^ 4 * u ^ 6 + 6 * q ^ 3 * u ^ 7 + 2 * q ^ 2 * u ^ 8
            - q ^ 8 * u + 2 * q ^ 6 * u ^ 3 + 5 * q ^ 5 * u ^ 4 + 5 * q ^ 4 * u ^ 5
            + 2 * q ^ 3 * u ^ 6 - q * u ^ 8 - q ^ 8 - 5 * q ^ 7 * u - 9 * q ^ 6 * u ^ 2
            - 12 * q ^ 5 * u ^ 3 - 14 * q ^ 4 * u ^ 4 - 12 * q ^ 3 * u ^ 5 - 9 * q ^ 2 * u ^ 6
            - 5 * q * u ^ 7 - u ^ 8 + q ^ 7 + 2 * q ^ 6 * u - q ^ 5 * u ^ 2 - 2 * q ^ 4 * u ^ 3
            - 2 * q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5 + 2 * q * u ^ 6 + u ^ 7 + 3 * q ^ 5 * u
            + 6 * q ^ 4 * u ^ 2 + 5 * q ^ 3 * u ^ 3 + 6 * q ^ 2 * u ^ 4 + 3 * q * u ^ 5
            + q ^ 3 * u ^ 2 + q ^ 2 * u ^ 3 - q ^ 4 - 2 * q ^ 3 * u - 3 * q ^ 2 * u ^ 2
            - 2 * q * u ^ 3 - u ^ 4 + q ^ 3 + u ^ 3 + q ^ 2 + 2 * q * u + u ^ 2 - q - u)
              • (elemSymm L 2 * elemSymm L 7)
        + (-(q ^ 16) - q ^ 15 * u - q ^ 14 * u ^ 2 - q ^ 13 * u ^ 3 - q ^ 12 * u ^ 4
            - q ^ 11 * u ^ 5 - q ^ 10 * u ^ 6 - q ^ 9 * u ^ 7 - q ^ 8 * u ^ 8 - q ^ 7 * u ^ 9
            - q ^ 6 * u ^ 10 - q ^ 5 * u ^ 11 - q ^ 4 * u ^ 12 - q ^ 3 * u ^ 13 - q ^ 2 * u ^ 14
            - q * u ^ 15 - u ^ 16 + q ^ 15 + u ^ 15 + q ^ 14 + q ^ 13 * u + q * u ^ 13 + u ^ 14
            - 2 * q ^ 13 - q ^ 12 * u - q ^ 11 * u ^ 2 - 2 * q ^ 10 * u ^ 3 - 2 * q ^ 9 * u ^ 4
            - 2 * q ^ 8 * u ^ 5 - 2 * q ^ 7 * u ^ 6 - 2 * q ^ 6 * u ^ 7 - 2 * q ^ 5 * u ^ 8
            - 2 * q ^ 4 * u ^ 9 - 2 * q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 - q * u ^ 12 - 2 * u ^ 13
            + 2 * q ^ 12 + q ^ 11 * u + q ^ 10 * u ^ 2 + q ^ 9 * u ^ 3 + q ^ 3 * u ^ 9
            + q ^ 2 * u ^ 10 + q * u ^ 11 + 2 * u ^ 12 + q ^ 11 + 3 * q ^ 10 * u
            + 2 * q ^ 9 * u ^ 2 + 2 * q ^ 8 * u ^ 3 + 2 * q ^ 7 * u ^ 4 + q ^ 6 * u ^ 5
            + q ^ 5 * u ^ 6 + 2 * q ^ 4 * u ^ 7 + 2 * q ^ 3 * u ^ 8 + 2 * q ^ 2 * u ^ 9
            + 3 * q * u ^ 10 + u ^ 11 - 2 * q ^ 10 + 3 * q ^ 8 * u ^ 2 + q ^ 7 * u ^ 3
            + q ^ 6 * u ^ 4 + 2 * q ^ 5 * u ^ 5 + q ^ 4 * u ^ 6 + q ^ 3 * u ^ 7
            + 3 * q ^ 2 * u ^ 8 - 2 * u ^ 10 - 2 * q ^ 8 * u + q ^ 7 * u ^ 2 + 6 * q ^ 6 * u ^ 3
            + 4 * q ^ 5 * u ^ 4 + 4 * q ^ 4 * u ^ 5 + 6 * q ^ 3 * u ^ 6 + q ^ 2 * u ^ 7
            - 2 * q * u ^ 8 + 2 * q ^ 7 * u + 3 * q ^ 5 * u ^ 3 + 8 * q ^ 4 * u ^ 4
            + 3 * q ^ 3 * u ^ 5 + 2 * q * u ^ 7 - 3 * q ^ 7 - 6 * q ^ 6 * u - 7 * q ^ 5 * u ^ 2
            - 13 * q ^ 4 * u ^ 3 - 13 * q ^ 3 * u ^ 4 - 7 * q ^ 2 * u ^ 5 - 6 * q * u ^ 6
            - 3 * u ^ 7 + q ^ 6 - 3 * q ^ 5 * u - 4 * q ^ 4 * u ^ 2 - 2 * q ^ 3 * u ^ 3
            - 4 * q ^ 2 * u ^ 4 - 3 * q * u ^ 5 + u ^ 6 + 3 * q ^ 5 + 4 * q ^ 4 * u
            + 2 * q ^ 3 * u ^ 2 + 2 * q ^ 2 * u ^ 3 + 4 * q * u ^ 4 + 3 * u ^ 5 + q ^ 4
            + 4 * q ^ 3 * u + 5 * q ^ 2 * u ^ 2 + 4 * q * u ^ 3 + u ^ 4 - q ^ 3 + q ^ 2 * u
            + q * u ^ 2 - u ^ 3 - 2 * q ^ 2 - 4 * q * u - 2 * u ^ 2 + q + u)
              • (elemSymm L 3 * elemSymm L 6)
        + (-(q ^ 15) - q ^ 14 * u - q ^ 13 * u ^ 2 - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4
            - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7 - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9
            - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12 - q ^ 2 * u ^ 13 - q * u ^ 14
            - u ^ 15 - q ^ 13 * u - q ^ 12 * u ^ 2 - q ^ 11 * u ^ 3 - q ^ 10 * u ^ 4
            - q ^ 9 * u ^ 5 - q ^ 8 * u ^ 6 - q ^ 7 * u ^ 7 - q ^ 6 * u ^ 8 - q ^ 5 * u ^ 9
            - q ^ 4 * u ^ 10 - q ^ 3 * u ^ 11 - q ^ 2 * u ^ 12 - q * u ^ 13 + 2 * q ^ 13
            + q ^ 12 * u + q * u ^ 12 + 2 * u ^ 13 + q ^ 12 + 2 * q ^ 11 * u + q ^ 10 * u ^ 2
            + q ^ 2 * u ^ 10 + 2 * q * u ^ 11 + u ^ 12 - q ^ 11 + q ^ 10 * u + q ^ 9 * u ^ 2
            - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5 - q ^ 5 * u ^ 6 - q ^ 4 * u ^ 7 + q ^ 2 * u ^ 9
            + q * u ^ 10 - u ^ 11 + 2 * q ^ 9 * u + 3 * q ^ 8 * u ^ 2 + 3 * q ^ 7 * u ^ 3
            + 2 * q ^ 6 * u ^ 4 + q ^ 5 * u ^ 5 + 2 * q ^ 4 * u ^ 6 + 3 * q ^ 3 * u ^ 7
            + 3 * q ^ 2 * u ^ 8 + 2 * q * u ^ 9 - 2 * q ^ 9 + 3 * q ^ 7 * u ^ 2
            + 3 * q ^ 6 * u ^ 3 + 4 * q ^ 5 * u ^ 4 + 4 * q ^ 4 * u ^ 5 + 3 * q ^ 3 * u ^ 6
            + 3 * q ^ 2 * u ^ 7 - 2 * u ^ 9 - q ^ 8 - 4 * q ^ 7 * u + q ^ 6 * u ^ 2
            + 5 * q ^ 5 * u ^ 3 + 4 * q ^ 4 * u ^ 4 + 5 * q ^ 3 * u ^ 5 + q ^ 2 * u ^ 6
            - 4 * q * u ^ 7 - u ^ 8 - 5 * q ^ 6 * u - 8 * q ^ 5 * u ^ 2 - 4 * q ^ 4 * u ^ 3
            - 4 * q ^ 3 * u ^ 4 - 8 * q ^ 2 * u ^ 5 - 5 * q * u ^ 6 + 2 * q ^ 6 - q ^ 5 * u
            - 8 * q ^ 4 * u ^ 2 - 13 * q ^ 3 * u ^ 3 - 8 * q ^ 2 * u ^ 4 - q * u ^ 5 + 2 * u ^ 6
            + 2 * q ^ 5 + 7 * q ^ 4 * u + 6 * q ^ 3 * u ^ 2 + 6 * q ^ 2 * u ^ 3 + 7 * q * u ^ 4
            + 2 * u ^ 5 - 2 * q ^ 4 + 2 * q ^ 3 * u + 6 * q ^ 2 * u ^ 2 + 2 * q * u ^ 3
            - 2 * u ^ 4 - 3 * q ^ 2 * u - 3 * q * u ^ 2) • (elemSymm L 4 * elemSymm L 5)
        + (-(q ^ 16) - q ^ 15 * u - q ^ 14 * u ^ 2 - q ^ 13 * u ^ 3 - q ^ 12 * u ^ 4
            - q ^ 11 * u ^ 5 - q ^ 10 * u ^ 6 - q ^ 9 * u ^ 7 - q ^ 8 * u ^ 8 - q ^ 7 * u ^ 9
            - q ^ 6 * u ^ 10 - q ^ 5 * u ^ 11 - q ^ 4 * u ^ 12 - q ^ 3 * u ^ 13 - q ^ 2 * u ^ 14
            - q * u ^ 15 - u ^ 16 - q ^ 14 * u - q ^ 13 * u ^ 2 - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4
            - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7 - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9
            - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12 - q ^ 2 * u ^ 13 - q * u ^ 14
            - q ^ 13 * u - 2 * q ^ 12 * u ^ 2 - 2 * q ^ 11 * u ^ 3 - 2 * q ^ 10 * u ^ 4
            - 2 * q ^ 9 * u ^ 5 - 2 * q ^ 8 * u ^ 6 - 2 * q ^ 7 * u ^ 7 - 2 * q ^ 6 * u ^ 8
            - 2 * q ^ 5 * u ^ 9 - 2 * q ^ 4 * u ^ 10 - 2 * q ^ 3 * u ^ 11 - 2 * q ^ 2 * u ^ 12
            - q * u ^ 13 + q ^ 13 - q ^ 11 * u ^ 2 - 2 * q ^ 10 * u ^ 3 - 2 * q ^ 9 * u ^ 4
            - 2 * q ^ 8 * u ^ 5 - 2 * q ^ 7 * u ^ 6 - 2 * q ^ 6 * u ^ 7 - 2 * q ^ 5 * u ^ 8
            - 2 * q ^ 4 * u ^ 9 - 2 * q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 + u ^ 13 + 2 * q ^ 12
            + 2 * q ^ 11 * u - q ^ 9 * u ^ 3 - 2 * q ^ 8 * u ^ 4 - 2 * q ^ 7 * u ^ 5
            - 2 * q ^ 6 * u ^ 6 - 2 * q ^ 5 * u ^ 7 - 2 * q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9
            + 2 * q * u ^ 11 + 2 * u ^ 12 + 2 * q ^ 11 + 6 * q ^ 10 * u + 5 * q ^ 9 * u ^ 2
            + 3 * q ^ 8 * u ^ 3 + 2 * q ^ 7 * u ^ 4 + q ^ 6 * u ^ 5 + q ^ 5 * u ^ 6
            + 2 * q ^ 4 * u ^ 7 + 3 * q ^ 3 * u ^ 8 + 5 * q ^ 2 * u ^ 9 + 6 * q * u ^ 10
            + 2 * u ^ 11 - q ^ 10 + 5 * q ^ 9 * u + 9 * q ^ 8 * u ^ 2 + 7 * q ^ 7 * u ^ 3
            + 6 * q ^ 6 * u ^ 4 + 6 * q ^ 5 * u ^ 5 + 6 * q ^ 4 * u ^ 6 + 7 * q ^ 3 * u ^ 7
            + 9 * q ^ 2 * u ^ 8 + 5 * q * u ^ 9 - u ^ 10 - 3 * q ^ 9 - q ^ 8 * u
            + 8 * q ^ 7 * u ^ 2 + 14 * q ^ 6 * u ^ 3 + 14 * q ^ 5 * u ^ 4 + 14 * q ^ 4 * u ^ 5
            + 14 * q ^ 3 * u ^ 6 + 8 * q ^ 2 * u ^ 7 - q * u ^ 8 - 3 * u ^ 9 - 3 * q ^ 8
            - 7 * q ^ 7 * u - 4 * q ^ 6 * u ^ 2 + 3 * q ^ 5 * u ^ 3 + 7 * q ^ 4 * u ^ 4
            + 3 * q ^ 3 * u ^ 5 - 4 * q ^ 2 * u ^ 6 - 7 * q * u ^ 7 - 3 * u ^ 8 - 2 * q ^ 7
            - 12 * q ^ 6 * u - 19 * q ^ 5 * u ^ 2 - 22 * q ^ 4 * u ^ 3 - 22 * q ^ 3 * u ^ 4
            - 19 * q ^ 2 * u ^ 5 - 12 * q * u ^ 6 - 2 * u ^ 7 + 3 * q ^ 6 - 9 * q ^ 4 * u ^ 2
            - 11 * q ^ 3 * u ^ 3 - 9 * q ^ 2 * u ^ 4 + 3 * u ^ 6 + 3 * q ^ 5 + 8 * q ^ 4 * u
            + 9 * q ^ 3 * u ^ 2 + 9 * q ^ 2 * u ^ 3 + 8 * q * u ^ 4 + 3 * u ^ 5 + 2 * q ^ 4
            + 6 * q ^ 3 * u + 9 * q ^ 2 * u ^ 2 + 6 * q * u ^ 3 + 2 * u ^ 4 - 2 * q ^ 3
            - q ^ 2 * u - q * u ^ 2 - 2 * u ^ 3 - 2 * q ^ 2 - 4 * q * u - 2 * u ^ 2 + q + u)
              • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 7))
        + (-(q ^ 15) - q ^ 14 * u - q ^ 13 * u ^ 2 - q ^ 12 * u ^ 3 - q ^ 11 * u ^ 4
            - q ^ 10 * u ^ 5 - q ^ 9 * u ^ 6 - q ^ 8 * u ^ 7 - q ^ 7 * u ^ 8 - q ^ 6 * u ^ 9
            - q ^ 5 * u ^ 10 - q ^ 4 * u ^ 11 - q ^ 3 * u ^ 12 - q ^ 2 * u ^ 13 - q * u ^ 14
            - u ^ 15 - q ^ 14 - 2 * q ^ 13 * u - 2 * q ^ 12 * u ^ 2 - 2 * q ^ 11 * u ^ 3
            - 2 * q ^ 10 * u ^ 4 - 2 * q ^ 9 * u ^ 5 - 2 * q ^ 8 * u ^ 6 - 2 * q ^ 7 * u ^ 7
            - 2 * q ^ 6 * u ^ 8 - 2 * q ^ 5 * u ^ 9 - 2 * q ^ 4 * u ^ 10 - 2 * q ^ 3 * u ^ 11
            - 2 * q ^ 2 * u ^ 12 - 2 * q * u ^ 13 - u ^ 14 + 2 * q ^ 13 - q ^ 11 * u ^ 2
            - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4 - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7
            - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9 - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 + 2 * u ^ 13
            - 2 * q ^ 10 * u ^ 2 - 3 * q ^ 9 * u ^ 3 - 3 * q ^ 8 * u ^ 4 - 3 * q ^ 7 * u ^ 5
            - 3 * q ^ 6 * u ^ 6 - 3 * q ^ 5 * u ^ 7 - 3 * q ^ 4 * u ^ 8 - 3 * q ^ 3 * u ^ 9
            - 2 * q ^ 2 * u ^ 10 + q ^ 11 + q ^ 10 * u - 2 * q ^ 8 * u ^ 3 - 3 * q ^ 7 * u ^ 4
            - 3 * q ^ 6 * u ^ 5 - 3 * q ^ 5 * u ^ 6 - 3 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8
            + q * u ^ 10 + u ^ 11 + 2 * q ^ 10 + 5 * q ^ 9 * u + 3 * q ^ 8 * u ^ 2
            + 2 * q ^ 7 * u ^ 3 - q ^ 5 * u ^ 5 + 2 * q ^ 3 * u ^ 7 + 3 * q ^ 2 * u ^ 8
            + 5 * q * u ^ 9 + 2 * u ^ 10 - q ^ 9 + 5 * q ^ 8 * u + 9 * q ^ 7 * u ^ 2
            + 7 * q ^ 6 * u ^ 3 + 8 * q ^ 5 * u ^ 4 + 8 * q ^ 4 * u ^ 5 + 7 * q ^ 3 * u ^ 6
            + 9 * q ^ 2 * u ^ 7 + 5 * q * u ^ 8 - u ^ 9 - 2 * q ^ 8 - q ^ 7 * u
            + 9 * q ^ 6 * u ^ 2 + 14 * q ^ 5 * u ^ 3 + 13 * q ^ 4 * u ^ 4 + 14 * q ^ 3 * u ^ 5
            + 9 * q ^ 2 * u ^ 6 - q * u ^ 7 - 2 * u ^ 8 - 5 * q ^ 6 * u - 5 * q ^ 5 * u ^ 2
            + q ^ 4 * u ^ 3 + q ^ 3 * u ^ 4 - 5 * q ^ 2 * u ^ 5 - 5 * q * u ^ 6 - q ^ 6
            - 5 * q ^ 5 * u - 13 * q ^ 4 * u ^ 2 - 16 * q ^ 3 * u ^ 3 - 13 * q ^ 2 * u ^ 4
            - 5 * q * u ^ 5 - u ^ 6 - q ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3
            - q * u ^ 4 - u ^ 5 + 2 * q ^ 4 + 3 * q ^ 3 * u + 4 * q ^ 2 * u ^ 2 + 3 * q * u ^ 3
            + 2 * u ^ 4 + q ^ 2 * u + q * u ^ 2) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 6))
        + (-(q ^ 14) - q ^ 13 * u - q ^ 12 * u ^ 2 - q ^ 11 * u ^ 3 - q ^ 10 * u ^ 4
            - q ^ 9 * u ^ 5 - q ^ 8 * u ^ 6 - q ^ 7 * u ^ 7 - q ^ 6 * u ^ 8 - q ^ 5 * u ^ 9
            - q ^ 4 * u ^ 10 - q ^ 3 * u ^ 11 - q ^ 2 * u ^ 12 - q * u ^ 13 - u ^ 14 - q ^ 12 * u
            - q ^ 11 * u ^ 2 - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4 - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6
            - q ^ 6 * u ^ 7 - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9 - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11
            - q * u ^ 12 - q ^ 12 - 2 * q ^ 11 * u - 3 * q ^ 10 * u ^ 2 - 3 * q ^ 9 * u ^ 3
            - 3 * q ^ 8 * u ^ 4 - 3 * q ^ 7 * u ^ 5 - 3 * q ^ 6 * u ^ 6 - 3 * q ^ 5 * u ^ 7
            - 3 * q ^ 4 * u ^ 8 - 3 * q ^ 3 * u ^ 9 - 3 * q ^ 2 * u ^ 10 - 2 * q * u ^ 11 - u ^ 12
            + 2 * q ^ 11 - q ^ 9 * u ^ 2 - 2 * q ^ 8 * u ^ 3 - 2 * q ^ 7 * u ^ 4
            - 2 * q ^ 6 * u ^ 5 - 2 * q ^ 5 * u ^ 6 - 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8
            - q ^ 2 * u ^ 9 + 2 * u ^ 11 + 3 * q ^ 10 + 3 * q ^ 9 * u - q ^ 7 * u ^ 3
            - 2 * q ^ 6 * u ^ 4 - 2 * q ^ 5 * u ^ 5 - 2 * q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7
            + 3 * q * u ^ 9 + 3 * u ^ 10 + 5 * q ^ 8 * u + 4 * q ^ 7 * u ^ 2 + q ^ 6 * u ^ 3
            + q ^ 3 * u ^ 6 + 4 * q ^ 2 * u ^ 7 + 5 * q * u ^ 8 - q ^ 8 + 3 * q ^ 7 * u
            + 8 * q ^ 6 * u ^ 2 + 7 * q ^ 5 * u ^ 3 + 6 * q ^ 4 * u ^ 4 + 7 * q ^ 3 * u ^ 5
            + 8 * q ^ 2 * u ^ 6 + 3 * q * u ^ 7 - u ^ 8 + q ^ 7 + 4 * q ^ 6 * u
            + 11 * q ^ 5 * u ^ 2 + 18 * q ^ 4 * u ^ 3 + 18 * q ^ 3 * u ^ 4 + 11 * q ^ 2 * u ^ 5
            + 4 * q * u ^ 6 + u ^ 7 - 5 * q ^ 6 - 6 * q ^ 5 * u - 5 * q ^ 4 * u ^ 2
            - 5 * q ^ 3 * u ^ 3 - 5 * q ^ 2 * u ^ 4 - 6 * q * u ^ 5 - 5 * u ^ 6 - 4 * q ^ 5
            - 14 * q ^ 4 * u - 17 * q ^ 3 * u ^ 2 - 17 * q ^ 2 * u ^ 3 - 14 * q * u ^ 4
            - 4 * u ^ 5 + 4 * q ^ 4 + q ^ 3 * u - 4 * q ^ 2 * u ^ 2 + q * u ^ 3 + 4 * u ^ 4
            + 3 * q ^ 3 + 8 * q ^ 2 * u + 8 * q * u ^ 2 + 3 * u ^ 3 + q ^ 2 + 2 * q * u + u ^ 2
            - 2 * q - 2 * u) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 5))
        + (-(q ^ 13) - q ^ 12 * u - q ^ 11 * u ^ 2 - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4
            - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7 - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9
            - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 - q * u ^ 12 - u ^ 13 - q ^ 11 * u - q ^ 10 * u ^ 2
            - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5 - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7
            - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10 - q * u ^ 11 + q ^ 11 - q ^ 9 * u ^ 2
            - q ^ 8 * u ^ 3 - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5 - q ^ 5 * u ^ 6 - q ^ 4 * u ^ 7
            - q ^ 3 * u ^ 8 - q ^ 2 * u ^ 9 + u ^ 11 - q ^ 8 * u ^ 2 - 2 * q ^ 7 * u ^ 3
            - 2 * q ^ 6 * u ^ 4 - 2 * q ^ 5 * u ^ 5 - 2 * q ^ 4 * u ^ 6 - 2 * q ^ 3 * u ^ 7
            - q ^ 2 * u ^ 8 + 3 * q ^ 9 + 3 * q ^ 8 * u + 2 * q ^ 7 * u ^ 2 + q ^ 6 * u ^ 3
            + q ^ 3 * u ^ 6 + 2 * q ^ 2 * u ^ 7 + 3 * q * u ^ 8 + 3 * u ^ 9 + 5 * q ^ 7 * u
            + 4 * q ^ 6 * u ^ 2 + 3 * q ^ 5 * u ^ 3 + 3 * q ^ 4 * u ^ 4 + 3 * q ^ 3 * u ^ 5
            + 4 * q ^ 2 * u ^ 6 + 5 * q * u ^ 7 - 3 * q ^ 7 + q ^ 6 * u + 7 * q ^ 5 * u ^ 2
            + 6 * q ^ 4 * u ^ 3 + 6 * q ^ 3 * u ^ 4 + 7 * q ^ 2 * u ^ 5 + q * u ^ 6 - 3 * u ^ 7
            - 3 * q ^ 6 - 6 * q ^ 5 * u - q ^ 4 * u ^ 2 + 4 * q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4
            - 6 * q * u ^ 5 - 3 * u ^ 6 - 7 * q ^ 4 * u - 11 * q ^ 3 * u ^ 2 - 11 * q ^ 2 * u ^ 3
            - 7 * q * u ^ 4 + 4 * q ^ 4 + 2 * q ^ 3 * u - 2 * q ^ 2 * u ^ 2 + 2 * q * u ^ 3
            + 4 * u ^ 4 + 6 * q ^ 2 * u + 6 * q * u ^ 2 - q ^ 2 - 2 * q * u - u ^ 2)
              • (elemSymm L 1 * (elemSymm L 4 * elemSymm L 4))
        + (-(q ^ 13) - q ^ 12 * u - q ^ 11 * u ^ 2 - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4
            - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7 - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9
            - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 - q * u ^ 12 - u ^ 13 + q ^ 12 + u ^ 12
            - q ^ 9 * u ^ 2 - q ^ 8 * u ^ 3 - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5 - q ^ 5 * u ^ 6
            - q ^ 4 * u ^ 7 - q ^ 3 * u ^ 8 - q ^ 2 * u ^ 9 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4
            - q ^ 5 * u ^ 5 - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3
            - 2 * q ^ 5 * u ^ 4 - 2 * q ^ 4 * u ^ 5 - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7 + q ^ 8
            + 3 * q ^ 7 * u + 3 * q ^ 6 * u ^ 2 + 3 * q ^ 5 * u ^ 3 + 4 * q ^ 4 * u ^ 4
            + 3 * q ^ 3 * u ^ 5 + 3 * q ^ 2 * u ^ 6 + 3 * q * u ^ 7 + u ^ 8 - q ^ 7
            + 3 * q ^ 5 * u ^ 2 + 2 * q ^ 4 * u ^ 3 + 2 * q ^ 3 * u ^ 4 + 3 * q ^ 2 * u ^ 5
            - u ^ 7 - 3 * q ^ 5 * u - 3 * q ^ 4 * u ^ 2 - 3 * q ^ 2 * u ^ 4 - 3 * q * u ^ 5
            + q ^ 5 + 2 * q ^ 4 * u + 2 * q * u ^ 4 + u ^ 5 + q ^ 2 * u ^ 2 - q ^ 3 + q ^ 2 * u
            + q * u ^ 2 - u ^ 3 - 2 * q ^ 2 - 4 * q * u - 2 * u ^ 2 + 2 * q + 2 * u)
              • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 5))
        + (-(q ^ 12) - q ^ 11 * u - q ^ 10 * u ^ 2 - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5
            - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7 - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10
            - q * u ^ 11 - u ^ 12 - q ^ 11 - 2 * q ^ 10 * u - 2 * q ^ 9 * u ^ 2
            - 2 * q ^ 8 * u ^ 3 - 2 * q ^ 7 * u ^ 4 - 2 * q ^ 6 * u ^ 5 - 2 * q ^ 5 * u ^ 6
            - 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8 - 2 * q ^ 2 * u ^ 9 - 2 * q * u ^ 10 - u ^ 11
            + 2 * q ^ 10 - q ^ 8 * u ^ 2 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4 - q ^ 5 * u ^ 5
            - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 + 2 * u ^ 10 - 2 * q ^ 7 * u ^ 2
            - 3 * q ^ 6 * u ^ 3 - 3 * q ^ 5 * u ^ 4 - 3 * q ^ 4 * u ^ 5 - 3 * q ^ 3 * u ^ 6
            - 2 * q ^ 2 * u ^ 7 + q ^ 8 + q ^ 7 * u - 2 * q ^ 5 * u ^ 3 - 3 * q ^ 4 * u ^ 4
            - 2 * q ^ 3 * u ^ 5 + q * u ^ 7 + u ^ 8 + 3 * q ^ 7 + 6 * q ^ 6 * u
            + 5 * q ^ 5 * u ^ 2 + 6 * q ^ 4 * u ^ 3 + 6 * q ^ 3 * u ^ 4 + 5 * q ^ 2 * u ^ 5
            + 6 * q * u ^ 6 + 3 * u ^ 7 - q ^ 6 + 7 * q ^ 5 * u + 11 * q ^ 4 * u ^ 2
            + 10 * q ^ 3 * u ^ 3 + 11 * q ^ 2 * u ^ 4 + 7 * q * u ^ 5 - u ^ 6 - 5 * q ^ 5
            - 9 * q ^ 4 * u - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3 - 9 * q * u ^ 4 - 5 * u ^ 5
            + q ^ 4 - 3 * q ^ 3 * u - 6 * q ^ 2 * u ^ 2 - 3 * q * u ^ 3 + u ^ 4 - q ^ 3
            - 3 * q ^ 2 * u - 3 * q * u ^ 2 - u ^ 3 + 2 * q ^ 2 + 4 * q * u + 2 * u ^ 2)
              • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 4))
        + (-(q ^ 10) - q ^ 9 * u - q ^ 8 * u ^ 2 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4 - q ^ 5 * u ^ 5
            - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 - q * u ^ 9 - u ^ 10 + q ^ 9 + u ^ 9
            + q ^ 8 + q ^ 7 * u + q * u ^ 7 + u ^ 8 - q ^ 7 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4
            - u ^ 7 + q ^ 6 + q ^ 5 * u + 2 * q ^ 4 * u ^ 2 + 3 * q ^ 3 * u ^ 3
            + 2 * q ^ 2 * u ^ 4 + q * u ^ 5 + u ^ 6 + 3 * q ^ 4 * u + 3 * q ^ 3 * u ^ 2
            + 3 * q ^ 2 * u ^ 3 + 3 * q * u ^ 4 - 3 * q ^ 4 - 5 * q ^ 3 * u - 4 * q ^ 2 * u ^ 2
            - 5 * q * u ^ 3 - 3 * u ^ 4 + q ^ 3 - 2 * q ^ 2 * u - 2 * q * u ^ 2 + u ^ 3
            + 2 * q ^ 2 + 4 * q * u + 2 * u ^ 2 - q - u)
              • (elemSymm L 3 * (elemSymm L 3 * elemSymm L 3))
        + (-(q ^ 13) - q ^ 12 * u - q ^ 11 * u ^ 2 - q ^ 10 * u ^ 3 - q ^ 9 * u ^ 4
            - q ^ 8 * u ^ 5 - q ^ 7 * u ^ 6 - q ^ 6 * u ^ 7 - q ^ 5 * u ^ 8 - q ^ 4 * u ^ 9
            - q ^ 3 * u ^ 10 - q ^ 2 * u ^ 11 - q * u ^ 12 - u ^ 13 - q ^ 11 * u - q ^ 10 * u ^ 2
            - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5 - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7
            - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10 - q * u ^ 11 - q ^ 10 * u
            - 2 * q ^ 9 * u ^ 2 - 2 * q ^ 8 * u ^ 3 - 2 * q ^ 7 * u ^ 4 - 2 * q ^ 6 * u ^ 5
            - 2 * q ^ 5 * u ^ 6 - 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8 - 2 * q ^ 2 * u ^ 9
            - q * u ^ 10 + q ^ 10 - q ^ 8 * u ^ 2 - 2 * q ^ 7 * u ^ 3 - 2 * q ^ 6 * u ^ 4
            - 2 * q ^ 5 * u ^ 5 - 2 * q ^ 4 * u ^ 6 - 2 * q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 + u ^ 10
            + 2 * q ^ 9 + 3 * q ^ 8 * u + q ^ 7 * u ^ 2 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5
            + q ^ 2 * u ^ 7 + 3 * q * u ^ 8 + 2 * u ^ 9 + q ^ 8 + 5 * q ^ 7 * u
            + 6 * q ^ 6 * u ^ 2 + 5 * q ^ 5 * u ^ 3 + 5 * q ^ 4 * u ^ 4 + 5 * q ^ 3 * u ^ 5
            + 6 * q ^ 2 * u ^ 6 + 5 * q * u ^ 7 + u ^ 8 - q ^ 7 + 3 * q ^ 6 * u
            + 8 * q ^ 5 * u ^ 2 + 10 * q ^ 4 * u ^ 3 + 10 * q ^ 3 * u ^ 4 + 8 * q ^ 2 * u ^ 5
            + 3 * q * u ^ 6 - u ^ 7 - 3 * q ^ 6 - 5 * q ^ 5 * u - 2 * q ^ 4 * u ^ 2
            - q ^ 3 * u ^ 3 - 2 * q ^ 2 * u ^ 4 - 5 * q * u ^ 5 - 3 * u ^ 6 - q ^ 5
            - 6 * q ^ 4 * u - 9 * q ^ 3 * u ^ 2 - 9 * q ^ 2 * u ^ 3 - 6 * q * u ^ 4 - u ^ 5
            - q ^ 3 * u - 3 * q ^ 2 * u ^ 2 - q * u ^ 3 + 2 * q ^ 3 + 3 * q ^ 2 * u
            + 3 * q * u ^ 2 + 2 * u ^ 3 + q ^ 2 + 2 * q * u + u ^ 2 - q - u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6)))
        + (-(q ^ 12) - q ^ 11 * u - q ^ 10 * u ^ 2 - q ^ 9 * u ^ 3 - q ^ 8 * u ^ 4 - q ^ 7 * u ^ 5
            - q ^ 6 * u ^ 6 - q ^ 5 * u ^ 7 - q ^ 4 * u ^ 8 - q ^ 3 * u ^ 9 - q ^ 2 * u ^ 10
            - q * u ^ 11 - u ^ 12 - q ^ 11 - 2 * q ^ 10 * u - 2 * q ^ 9 * u ^ 2
            - 2 * q ^ 8 * u ^ 3 - 2 * q ^ 7 * u ^ 4 - 2 * q ^ 6 * u ^ 5 - 2 * q ^ 5 * u ^ 6
            - 2 * q ^ 4 * u ^ 7 - 2 * q ^ 3 * u ^ 8 - 2 * q ^ 2 * u ^ 9 - 2 * q * u ^ 10 - u ^ 11
            - q ^ 10 - 3 * q ^ 9 * u - 4 * q ^ 8 * u ^ 2 - 4 * q ^ 7 * u ^ 3 - 4 * q ^ 6 * u ^ 4
            - 4 * q ^ 5 * u ^ 5 - 4 * q ^ 4 * u ^ 6 - 4 * q ^ 3 * u ^ 7 - 4 * q ^ 2 * u ^ 8
            - 3 * q * u ^ 9 - u ^ 10 + 3 * q ^ 9 - 2 * q ^ 7 * u ^ 2 - 3 * q ^ 6 * u ^ 3
            - 3 * q ^ 5 * u ^ 4 - 3 * q ^ 4 * u ^ 5 - 3 * q ^ 3 * u ^ 6 - 2 * q ^ 2 * u ^ 7
            + 3 * u ^ 9 + 2 * q ^ 8 + 3 * q ^ 7 * u - q ^ 6 * u ^ 2 - 3 * q ^ 5 * u ^ 3
            - 4 * q ^ 4 * u ^ 4 - 3 * q ^ 3 * u ^ 5 - q ^ 2 * u ^ 6 + 3 * q * u ^ 7 + 2 * u ^ 8
            + 6 * q ^ 6 * u + 7 * q ^ 5 * u ^ 2 + 5 * q ^ 4 * u ^ 3 + 5 * q ^ 3 * u ^ 4
            + 7 * q ^ 2 * u ^ 5 + 6 * q * u ^ 6 + q ^ 6 + 6 * q ^ 5 * u + 14 * q ^ 4 * u ^ 2
            + 15 * q ^ 3 * u ^ 3 + 14 * q ^ 2 * u ^ 4 + 6 * q * u ^ 5 + u ^ 6 - q ^ 5
            - 2 * q ^ 4 * u - 2 * q * u ^ 4 - u ^ 5 - 4 * q ^ 4 - 7 * q ^ 3 * u
            - 9 * q ^ 2 * u ^ 2 - 7 * q * u ^ 3 - 4 * u ^ 4 - 5 * q ^ 2 * u - 5 * q * u ^ 2
            + 3 * q ^ 2 + 6 * q * u + 3 * u ^ 2 - q - u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5)))
        + (-(q ^ 11) - q ^ 10 * u - q ^ 9 * u ^ 2 - q ^ 8 * u ^ 3 - q ^ 7 * u ^ 4 - q ^ 6 * u ^ 5
            - q ^ 5 * u ^ 6 - q ^ 4 * u ^ 7 - q ^ 3 * u ^ 8 - q ^ 2 * u ^ 9 - q * u ^ 10 - u ^ 11
            - q ^ 10 - 2 * q ^ 9 * u - 2 * q ^ 8 * u ^ 2 - 2 * q ^ 7 * u ^ 3 - 2 * q ^ 6 * u ^ 4
            - 2 * q ^ 5 * u ^ 5 - 2 * q ^ 4 * u ^ 6 - 2 * q ^ 3 * u ^ 7 - 2 * q ^ 2 * u ^ 8
            - 2 * q * u ^ 9 - u ^ 10 - q ^ 9 - 3 * q ^ 8 * u - 4 * q ^ 7 * u ^ 2
            - 4 * q ^ 6 * u ^ 3 - 4 * q ^ 5 * u ^ 4 - 4 * q ^ 4 * u ^ 5 - 4 * q ^ 3 * u ^ 6
            - 4 * q ^ 2 * u ^ 7 - 3 * q * u ^ 8 - u ^ 9 + 2 * q ^ 8 - q ^ 7 * u
            - 3 * q ^ 6 * u ^ 2 - 4 * q ^ 5 * u ^ 3 - 4 * q ^ 4 * u ^ 4 - 4 * q ^ 3 * u ^ 5
            - 3 * q ^ 2 * u ^ 6 - q * u ^ 7 + 2 * u ^ 8 + 3 * q ^ 7 + 3 * q ^ 6 * u
            - q ^ 5 * u ^ 2 - 3 * q ^ 4 * u ^ 3 - 3 * q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5
            + 3 * q * u ^ 6 + 3 * u ^ 7 + 4 * q ^ 6 + 9 * q ^ 5 * u + 9 * q ^ 4 * u ^ 2
            + 8 * q ^ 3 * u ^ 3 + 9 * q ^ 2 * u ^ 4 + 9 * q * u ^ 5 + 4 * u ^ 6 + 10 * q ^ 4 * u
            + 15 * q ^ 3 * u ^ 2 + 15 * q ^ 2 * u ^ 3 + 10 * q * u ^ 4 - 9 * q ^ 4
            - 10 * q ^ 3 * u - 5 * q ^ 2 * u ^ 2 - 10 * q * u ^ 3 - 9 * u ^ 4 - 10 * q ^ 2 * u
            - 10 * q * u ^ 2 + 2 * q ^ 2 + 4 * q * u + 2 * u ^ 2 + q + u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4)))
        + (-(q ^ 10) - q ^ 9 * u - q ^ 8 * u ^ 2 - q ^ 7 * u ^ 3 - q ^ 6 * u ^ 4 - q ^ 5 * u ^ 5
            - q ^ 4 * u ^ 6 - q ^ 3 * u ^ 7 - q ^ 2 * u ^ 8 - q * u ^ 9 - u ^ 10 - q ^ 9
            - 2 * q ^ 8 * u - 2 * q ^ 7 * u ^ 2 - 2 * q ^ 6 * u ^ 3 - 2 * q ^ 5 * u ^ 4
            - 2 * q ^ 4 * u ^ 5 - 2 * q ^ 3 * u ^ 6 - 2 * q ^ 2 * u ^ 7 - 2 * q * u ^ 8 - u ^ 9
            - 2 * q ^ 7 * u - 3 * q ^ 6 * u ^ 2 - 3 * q ^ 5 * u ^ 3 - 3 * q ^ 4 * u ^ 4
            - 3 * q ^ 3 * u ^ 5 - 3 * q ^ 2 * u ^ 6 - 2 * q * u ^ 7 + q ^ 7 - q ^ 6 * u
            - 3 * q ^ 5 * u ^ 2 - 4 * q ^ 4 * u ^ 3 - 4 * q ^ 3 * u ^ 4 - 3 * q ^ 2 * u ^ 5
            - q * u ^ 6 + u ^ 7 + 2 * q ^ 6 + 3 * q ^ 5 * u + q ^ 4 * u ^ 2 + q ^ 2 * u ^ 4
            + 3 * q * u ^ 5 + 2 * u ^ 6 + 2 * q ^ 5 + 7 * q ^ 4 * u + 8 * q ^ 3 * u ^ 2
            + 8 * q ^ 2 * u ^ 3 + 7 * q * u ^ 4 + 2 * u ^ 5 - 4 * q ^ 4 - 2 * q ^ 3 * u
            + q ^ 2 * u ^ 2 - 2 * q * u ^ 3 - 4 * u ^ 4 + 2 * q ^ 3 - 2 * q ^ 2 * u
            - 2 * q * u ^ 2 + 2 * u ^ 3 + q ^ 2 + 2 * q * u + u ^ 2 - 2 * q - 2 * u)
              • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4)))
        + (-(q ^ 9) - q ^ 8 * u - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5
            - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7 - q * u ^ 8 - u ^ 9 - 2 * q ^ 8 - 3 * q ^ 7 * u
            - 3 * q ^ 6 * u ^ 2 - 3 * q ^ 5 * u ^ 3 - 3 * q ^ 4 * u ^ 4 - 3 * q ^ 3 * u ^ 5
            - 3 * q ^ 2 * u ^ 6 - 3 * q * u ^ 7 - 2 * u ^ 8 + q ^ 7 - 2 * q ^ 6 * u
            - 3 * q ^ 5 * u ^ 2 - 3 * q ^ 4 * u ^ 3 - 3 * q ^ 3 * u ^ 4 - 3 * q ^ 2 * u ^ 5
            - 2 * q * u ^ 6 + u ^ 7 - 2 * q ^ 5 * u - 5 * q ^ 4 * u ^ 2 - 6 * q ^ 3 * u ^ 3
            - 5 * q ^ 2 * u ^ 4 - 2 * q * u ^ 5 + 4 * q ^ 5 + 4 * q ^ 4 * u + 3 * q ^ 3 * u ^ 2
            + 3 * q ^ 2 * u ^ 3 + 4 * q * u ^ 4 + 4 * u ^ 5 + 6 * q ^ 4 + 13 * q ^ 3 * u
            + 14 * q ^ 2 * u ^ 2 + 13 * q * u ^ 3 + 6 * u ^ 4 - 5 * q ^ 3 + 2 * q ^ 2 * u
            + 2 * q * u ^ 2 - 5 * u ^ 3 - 8 * q ^ 2 - 16 * q * u - 8 * u ^ 2 + 5 * q + 5 * u)
              • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3)))
        + (-(q ^ 7) - q ^ 6 * u - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5
            - q * u ^ 6 - u ^ 7 - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4
            - q * u ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3 - q * u ^ 4 + q ^ 4
            + q ^ 3 * u + q * u ^ 3 + u ^ 4 + q ^ 3 + 2 * q ^ 2 * u + 2 * q * u ^ 2 + u ^ 3
            + q ^ 2 + 2 * q * u + u ^ 2 - 2 * q - 2 * u)
              • (elemSymm L 2 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3)))
        + (-(q ^ 9) - q ^ 8 * u - q ^ 7 * u ^ 2 - q ^ 6 * u ^ 3 - q ^ 5 * u ^ 4 - q ^ 4 * u ^ 5
            - q ^ 3 * u ^ 6 - q ^ 2 * u ^ 7 - q * u ^ 8 - u ^ 9 - q ^ 7 * u - q ^ 6 * u ^ 2
            - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5 - q ^ 2 * u ^ 6 - q * u ^ 7 + q ^ 7
            - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5 + u ^ 7 + q ^ 6
            + 2 * q ^ 5 * u + q ^ 4 * u ^ 2 + q ^ 3 * u ^ 3 + q ^ 2 * u ^ 4 + 2 * q * u ^ 5
            + u ^ 6 + 2 * q ^ 4 * u + 3 * q ^ 3 * u ^ 2 + 3 * q ^ 2 * u ^ 3 + 2 * q * u ^ 4
            + q ^ 2 * u ^ 2 - q ^ 3 - q ^ 2 * u - q * u ^ 2 - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2
            + q + u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5))))
        + (-(q ^ 8) - q ^ 7 * u - q ^ 6 * u ^ 2 - q ^ 5 * u ^ 3 - q ^ 4 * u ^ 4 - q ^ 3 * u ^ 5
            - q ^ 2 * u ^ 6 - q * u ^ 7 - u ^ 8 - q ^ 7 - 2 * q ^ 6 * u - 2 * q ^ 5 * u ^ 2
            - 2 * q ^ 4 * u ^ 3 - 2 * q ^ 3 * u ^ 4 - 2 * q ^ 2 * u ^ 5 - 2 * q * u ^ 6 - u ^ 7
            - q ^ 6 - 3 * q ^ 5 * u - 4 * q ^ 4 * u ^ 2 - 4 * q ^ 3 * u ^ 3 - 4 * q ^ 2 * u ^ 4
            - 3 * q * u ^ 5 - u ^ 6 + q ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3
            - q * u ^ 4 + u ^ 5 + 7 * q ^ 4 + 9 * q ^ 3 * u + 8 * q ^ 2 * u ^ 2 + 9 * q * u ^ 3
            + 7 * u ^ 4 - 3 * q ^ 3 + 4 * q ^ 2 * u + 4 * q * u ^ 2 - 3 * u ^ 3 - 4 * q ^ 2
            - 8 * q * u - 4 * u ^ 2 + 2 * q + 2 * u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4))))
        + (-(q ^ 7) - q ^ 6 * u - q ^ 5 * u ^ 2 - q ^ 4 * u ^ 3 - q ^ 3 * u ^ 4 - q ^ 2 * u ^ 5
            - q * u ^ 6 - u ^ 7 - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4
            - q * u ^ 5 - q ^ 4 * u - 2 * q ^ 3 * u ^ 2 - 2 * q ^ 2 * u ^ 3 - q * u ^ 4 + q ^ 4
            + q ^ 3 * u + q * u ^ 3 + u ^ 4 + q ^ 3 + 2 * q ^ 2 * u + 2 * q * u ^ 2 + u ^ 3
            + q ^ 2 + 2 * q * u + u ^ 2 - 2 * q - 2 * u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3))))
        + (-(q ^ 6) - q ^ 5 * u - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 2 * u ^ 4 - q * u ^ 5
            - u ^ 6 - 2 * q ^ 5 - 3 * q ^ 4 * u - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 2 * u ^ 3
            - 3 * q * u ^ 4 - 2 * u ^ 5 - 3 * q ^ 4 - 6 * q ^ 3 * u - 6 * q ^ 2 * u ^ 2
            - 6 * q * u ^ 3 - 3 * u ^ 4 + 4 * q ^ 3 + q ^ 2 * u + q * u ^ 2 + 4 * u ^ 3
            + 5 * q ^ 2 + 10 * q * u + 5 * u ^ 2 - 3 * q - 3 * u)
              • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3))))
        + (-(q ^ 3) - q ^ 2 * u - q * u ^ 2 - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2 + 2 * q + 2 * u)
              • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))))
        + (-(q ^ 4) - q ^ 3 * u - q ^ 2 * u ^ 2 - q * u ^ 3 - u ^ 4 + q ^ 3 + u ^ 3 + q ^ 2
            + 2 * q * u + u ^ 2 - q - u)
              • (elemSymm L 1
                  * (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4)))))
        + (-(q ^ 3) - q ^ 2 * u - q * u ^ 2 - u ^ 3 - q ^ 2 - 2 * q * u - u ^ 2 + 2 * q + 2 * u)
              • (elemSymm L 1
                  * (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3)))))
        + (-q - u)
              • (elemSymm L 1
                  * (elemSymm L 1
                      * (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))))))) :
    LhsAt q u 2 3 Θ [3] :=
  (lhsAt_two_three_singleton_iff_onePartSweepValue hq0 hu0 hq1 3 Θ).2
    (by rw [hcre, onePartSweepValue_three_eq hq0 hu0 hq1])

end HJO.Mellit

end
