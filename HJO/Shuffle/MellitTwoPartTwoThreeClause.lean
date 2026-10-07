/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitTwoPartTwoThreeLambda

/-! # The `Λ` side of the two-part clause at `(2,3)`, and the clause itself

`HJO.Mellit.qop_double_apply_one_of_lhsWord`
(`HJO/Shuffle/MellitLhsCompInduction.lean`) reads the clause of
`HJO.Mellit.lhsRewrite_sweepWitness` at the composition `α = (1,1)` as one identity in `Λ`,

`(u+1)·Q_{a,b}(Q_{a,b}1) + u(q-1)·Q_{2a,2b}(1) = (qu+1)·ct(d_-^2G_{2,1}G_{1,1}(1))`.

At `(a,b) = (2,3)` the right-hand side is computed in
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three_eval`. **This file computes the left
one and proves the identity**, so the clause at `(a,b) = (2,3)`, `α = (1,1)` is a theorem:
`HJO.Mellit.qop_double_apply_one_two_three` is the identity in `Λ`, and
`HJO.Mellit.lhsAt_two_three_one_one` is `HJO.Mellit.LhsAt q u 2 3 Θ [1,1]` for every slope
homomorphism there may be.

## The decomposition, and the one that does not work

`Q_{2,3} = M^{-1}[D_2, D_1]`, `Q_{3,5} = M^{-1}[D_2, Q_{2,3}]` (`Split 3 5 = (2,3)`) and
`Q_{4,6} = M^{-1}[Q_{3,5}, D_1]` (`HJO.Regression.qop_four_six`, the non-coprime branch of
`HJO.Sym.Qop` at multiplicity two). Clearing the three `M^{-1}`s first — presenting the two terms
as the bare four-letter brackets `[D_2,D_1]²` and `[[D_2,[D_2,D_1]],D_1]` — makes the
comparison an identity between coefficients of degree eleven in `q` and `u` with about a
hundred terms apiece, and `ring` does not close it; raising `maxSteps` to `10^7` does not help,
because the obstruction is expression swell and not a step budget.

**Dividing by `M` at every recursion step does work**, exactly as
`HJO.Sym.qop_two_three_apply_one` and `HJO.Sym.qop_two_three_apply_elemSymm_one` do: each bracket
comes out as `M` times a *polynomial*, and the intermediates stay small. The sizes, in
`(q,u)`-terms summed over the `e`-monomials: `Q_{2,3}(e_2)` 58, `Q_{3,5}(1)` 28,
`Q_{2,3}(e_3)` 136, `Q_{2,3}(e_1e_2)` 179, `Q_{2,3}(Q_{2,3}1)` 184, `Q_{3,5}(e_1)` 141,
`Q_{4,6}(1)` 155.

## What the file contains

1. Twelve composite basic-operator values `D_j(m)` for the `e`-monomials `m` the recursion reaches,
   each one Pieri rewrite (`HJO.Sym.dop_one_mul_*`, `HJO.Sym.dop_two_mul_*`) against the base table
   of `HJO/Shuffle/MellitTwoPartTwoThreeLambda.lean`. Degree bookkeeping is what makes that
   table sufficient: the Pieri rule for `e_n` raises the operator index by `s ≤ n` while lowering
   the degree of the argument by `n`, so no value `D_j(e_r)` with `j + r > 6` is ever asked for.
2. The seven slope-operator values, in the order the recursion needs them.
3. The identity, and the clause read off it.

## Genericity

`q ∉ {0, 1}`, `u ∉ {0, 1}`, `qu ≠ 1` and — for the clause only — `qu ≠ -1`. The first four are
`M^{-1}` of `HJO.Sym.Qop` together with the `(qu)^{-1}` of `HJO.Sweep.slopeOperator` and the
`(1-q)^{-1}` of `HJO.Sweep.zop`; `u ≠ 1` is **real**, since
`HJO.Mellit.not_lhsWord_two_three_of_slopeHom_u_one` refutes this very clause there. `qu ≠ -1` is
an artefact of reading the clause off the identity, not of the identity: at `qu = -1` the identity
holds with both sides zero, and it is `HJO.Mellit.theta_copComp_one_one` whose scalar `qu+1`
degenerates.

## What is not proved here

This is **one** composition at **one** slope. `HJO.Mellit.LhsWord q u 2 3` quantifies over every
composition and the `hlhs` binder of `HJO.Mellit.shuffle_of_lhs_and_induction`
(`HJO/Shuffle/SweepComputesClosed.lean`) over every coprime `1 < a < b` as well; neither
it nor `hind` is discharged here, and nothing below assumes either. What this is the base
case of is the opposite-ends induction, whose seed is
`HJO.Sweep.stageTotal_two_three_zero_one_one`.

## References

This file concerns `HJO.Sym.DopInt`, `HJO.Sym.Qop`, `HJO.Mellit.lhsRewrite_sweepWitness` and
`HJO.Sweep.slopeOperator`.
-/

@[expose] public section

-- Every exponent written as a numeral in this file is a natural number. Saying so up front lets
-- each `x ^ n` resolve `HPow _ ℕ _` at once instead of retrying instance resolution for the
-- pending numeral type until defaulting, which dominated elaboration here. The elaborated terms
-- are the ones the default instance would produce.
local macro_rules | `($x ^ $n:num) => `(rightact% HPow.hPow $x ($n : ℕ))

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The composite basic-operator values the recursion bottoms out in -/

/-- `D_2(e_1e_2)`, the Pieri rule `HJO.Sym.dop_one_mul_two` at `f = e_2` against `D_2(e_2)`
and `D_3(e_2)`. -/
theorem dop_two_mono_12 (q u : L) :
    Dop q u 2 (elemSymm L 1 * elemSymm L 2)
      = (-1 + u + q - q * u) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
        + (1 : L) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))
        + (1 - 3 * u - 3 * q + 2 * u ^ 2 + 6 * q * u + 2 * q ^ 2 - 3 * q * u ^ 2 - 3 * q ^ 2 * u
            + q ^ 2 * u ^ 2) • (elemSymm L 1 * elemSymm L 4)
        + (-1 + u + q - q * u) • (elemSymm L 2 * elemSymm L 3)
        + (u + q - 2 * u ^ 2 - 4 * q * u - 2 * q ^ 2 + u ^ 3 + 5 * q * u ^ 2 + 5 * q ^ 2 * u
            + q ^ 3 - 2 * q * u ^ 3 - 4 * q ^ 2 * u ^ 2 - 2 * q ^ 3 * u + q ^ 2 * u ^ 3
            + q ^ 3 * u ^ 2) • elemSymm L 5 := by
  rw [dop_one_mul_two q u (elemSymm L 2),
    dop_two_elemSymm_two, dop_three_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add,
    MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `D_1(e_1e_3)`, the Pieri rule `HJO.Sym.dop_one_mul_one` at `f = e_3` against `D_1(e_3)`
and `D_2(e_3)`. -/
theorem dop_one_mono_13 (q u : L) :
    Dop q u 1 (elemSymm L 1 * elemSymm L 3)
      = (-1 + u + q - u ^ 2 - 2 * q * u - q ^ 2 + q * u ^ 2
            + q ^ 2 * u) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
        + (1 - u - q + q * u) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))
        + (-u - q + 3 * u ^ 2 + 5 * q * u + 3 * q ^ 2 - 2 * u ^ 3 - 7 * q * u ^ 2 - 7 * q ^ 2 * u
            - 2 * q ^ 3 + 3 * q * u ^ 3 + 5 * q ^ 2 * u ^ 2 + 3 * q ^ 3 * u - q ^ 2 * u ^ 3
            - q ^ 3 * u ^ 2) • (elemSymm L 1 * elemSymm L 4)
        + (u + q - u ^ 2 - 3 * q * u - q ^ 2 + 2 * q * u ^ 2 + 2 * q ^ 2 * u
            - q ^ 2 * u ^ 2) • (elemSymm L 2 * elemSymm L 3)
        + (-u ^ 2 - q * u - q ^ 2 + 2 * u ^ 3 + 4 * q * u ^ 2 + 4 * q ^ 2 * u + 2 * q ^ 3 - u ^ 4
            - 5 * q * u ^ 3 - 6 * q ^ 2 * u ^ 2 - 5 * q ^ 3 * u - q ^ 4 + 2 * q * u ^ 4
            + 4 * q ^ 2 * u ^ 3 + 4 * q ^ 3 * u ^ 2 + 2 * q ^ 4 * u - q ^ 2 * u ^ 4
            - q ^ 3 * u ^ 3 - q ^ 4 * u ^ 2) • elemSymm L 5 := by
  rw [dop_one_mul_one q u (elemSymm L 3),
    dop_one_elemSymm_three, dop_two_elemSymm_three]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add,
    MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `D_1(e_2^2)`, the Pieri rule `HJO.Sym.dop_two_mul_one` at `f = e_2` against `D_1(e_2)`,
`D_2(e_2)` and `D_3(e_2)`. -/
theorem dop_one_mono_22 (q u : L) :
    Dop q u 1 (elemSymm L 2 * elemSymm L 2)
      = (-1 + 2 * u + 2 * q - u ^ 2 - 4 * q * u - q ^ 2 + 2 * q * u ^ 2 + 2 * q ^ 2 * u
            - q ^ 2 * u ^ 2) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
        + (1 - 2 * u - 2 * q + 2 * q * u) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))
        + (-2 * u - 2 * q + 4 * u ^ 2 + 8 * q * u + 4 * q ^ 2 - 2 * u ^ 3 - 10 * q * u ^ 2
            - 10 * q ^ 2 * u - 2 * q ^ 3 + 4 * q * u ^ 3 + 8 * q ^ 2 * u ^ 2 + 4 * q ^ 3 * u
            - 2 * q ^ 2 * u ^ 3 - 2 * q ^ 3 * u ^ 2) • (elemSymm L 1 * elemSymm L 4)
        + (2 * u + 2 * q - 2 * u ^ 2 - 4 * q * u - 2 * q ^ 2 + 2 * q * u ^ 2
            + 2 * q ^ 2 * u) • (elemSymm L 2 * elemSymm L 3)
        + (-u ^ 2 - 2 * q * u - q ^ 2 + 2 * u ^ 3 + 6 * q * u ^ 2 + 6 * q ^ 2 * u + 2 * q ^ 3
            - u ^ 4 - 6 * q * u ^ 3 - 10 * q ^ 2 * u ^ 2 - 6 * q ^ 3 * u - q ^ 4 + 2 * q * u ^ 4
            + 6 * q ^ 2 * u ^ 3 + 6 * q ^ 3 * u ^ 2 + 2 * q ^ 4 * u - q ^ 2 * u ^ 4
            - 2 * q ^ 3 * u ^ 3 - q ^ 4 * u ^ 2) • elemSymm L 5 := by
  rw [dop_two_mul_one q u (elemSymm L 2),
    dop_one_elemSymm_two, dop_two_elemSymm_two, dop_three_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add,
    MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `D_2(e_1e_3)`, the Pieri rule `HJO.Sym.dop_one_mul_two` at `f = e_3` against `D_2(e_3)`
and `D_3(e_3)`. -/
theorem dop_two_mono_13 (q u : L) :
    Dop q u 2 (elemSymm L 1 * elemSymm L 3)
      = (-u - q + u ^ 2 + 2 * q * u + q ^ 2 - q * u ^ 2
            - q ^ 2 * u) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (u + q - q * u) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (u + q - 3 * u ^ 2 - 5 * q * u - 3 * q ^ 2 + 2 * u ^ 3 + 7 * q * u ^ 2 + 7 * q ^ 2 * u
            + 2 * q ^ 3 - 3 * q * u ^ 3 - 5 * q ^ 2 * u ^ 2 - 3 * q ^ 3 * u + q ^ 2 * u ^ 3
            + q ^ 3 * u ^ 2) • (elemSymm L 1 * elemSymm L 5)
        + (1 - 2 * u - 2 * q + u ^ 2 + 4 * q * u + q ^ 2 - 2 * q * u ^ 2 - 2 * q ^ 2 * u
            + q ^ 2 * u ^ 2) • (elemSymm L 2 * elemSymm L 4)
        + (-1 + u + q - q * u) • elemSymm L 3 ^ 2
        + (u ^ 2 + q * u + q ^ 2 - 2 * u ^ 3 - 4 * q * u ^ 2 - 4 * q ^ 2 * u - 2 * q ^ 3 + u ^ 4
            + 5 * q * u ^ 3 + 6 * q ^ 2 * u ^ 2 + 5 * q ^ 3 * u + q ^ 4 - 2 * q * u ^ 4
            - 4 * q ^ 2 * u ^ 3 - 4 * q ^ 3 * u ^ 2 - 2 * q ^ 4 * u + q ^ 2 * u ^ 4
            + q ^ 3 * u ^ 3 + q ^ 4 * u ^ 2) • elemSymm L 6 := by
  rw [dop_one_mul_two q u (elemSymm L 3),
    dop_two_elemSymm_three, dop_three_elemSymm_three]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add,
    MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `D_2(e_2^2)`, the Pieri rule `HJO.Sym.dop_two_mul_two` at `f = e_2` against `D_2(e_2)`,
`D_3(e_2)` and `D_4(e_2)`. -/
theorem dop_two_mono_22 (q u : L) :
    Dop q u 2 (elemSymm L 2 * elemSymm L 2)
      = (1 - 2 * u - 2 * q + u ^ 2 + 4 * q * u + q ^ 2 - 2 * q * u ^ 2 - 2 * q ^ 2 * u
            + q ^ 2 * u ^ 2) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (-2 + 2 * u + 2 * q - 2 * q * u) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (2 * u + 2 * q - 4 * u ^ 2 - 8 * q * u - 4 * q ^ 2 + 2 * u ^ 3 + 10 * q * u ^ 2
            + 10 * q ^ 2 * u + 2 * q ^ 3 - 4 * q * u ^ 3 - 8 * q ^ 2 * u ^ 2 - 4 * q ^ 3 * u
            + 2 * q ^ 2 * u ^ 3 + 2 * q ^ 3 * u ^ 2) • (elemSymm L 1 * elemSymm L 5)
        + (1 : L) • elemSymm L 2 ^ 3
        + (-2 * u - 2 * q + 2 * u ^ 2 + 4 * q * u + 2 * q ^ 2 - 2 * q * u ^ 2
            - 2 * q ^ 2 * u) • (elemSymm L 2 * elemSymm L 4)
        + (u ^ 2 + 2 * q * u + q ^ 2 - 2 * u ^ 3 - 6 * q * u ^ 2 - 6 * q ^ 2 * u - 2 * q ^ 3
            + u ^ 4 + 6 * q * u ^ 3 + 10 * q ^ 2 * u ^ 2 + 6 * q ^ 3 * u + q ^ 4 - 2 * q * u ^ 4
            - 6 * q ^ 2 * u ^ 3 - 6 * q ^ 3 * u ^ 2 - 2 * q ^ 4 * u + q ^ 2 * u ^ 4
            + 2 * q ^ 3 * u ^ 3 + q ^ 4 * u ^ 2) • elemSymm L 6 := by
  rw [dop_two_mul_two q u (elemSymm L 2),
    dop_two_elemSymm_two, dop_three_elemSymm_two, dop_four_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add,
    MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `D_1(e_1e_4)`, the Pieri rule `HJO.Sym.dop_one_mul_one` at `f = e_4` against `D_1(e_4)`
and `D_2(e_4)`. -/
theorem dop_one_mono_14 (q u : L) :
    Dop q u 1 (elemSymm L 1 * elemSymm L 4)
      = (-1 + u ^ 2 + q * u + q ^ 2 - u ^ 3 - 2 * q * u ^ 2 - 2 * q ^ 2 * u - q ^ 3 + q * u ^ 3
            + q ^ 2 * u ^ 2 + q ^ 3 * u) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (1 - u ^ 2 - q * u - q ^ 2 + q * u ^ 2
            + q ^ 2 * u) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (-u ^ 2 - q * u - q ^ 2 + 3 * u ^ 3 + 5 * q * u ^ 2 + 5 * q ^ 2 * u + 3 * q ^ 3
            - 2 * u ^ 4 - 7 * q * u ^ 3 - 8 * q ^ 2 * u ^ 2 - 7 * q ^ 3 * u - 2 * q ^ 4
            + 3 * q * u ^ 4 + 5 * q ^ 2 * u ^ 3 + 5 * q ^ 3 * u ^ 2 + 3 * q ^ 4 * u
            - q ^ 2 * u ^ 4 - q ^ 3 * u ^ 3 - q ^ 4 * u ^ 2) • (elemSymm L 1 * elemSymm L 5)
        + (1 - 2 * u - 2 * q + 2 * u ^ 2 + 5 * q * u + 2 * q ^ 2 - u ^ 3 - 5 * q * u ^ 2
            - 5 * q ^ 2 * u - q ^ 3 + 2 * q * u ^ 3 + 4 * q ^ 2 * u ^ 2 + 2 * q ^ 3 * u
            - q ^ 2 * u ^ 3 - q ^ 3 * u ^ 2) • (elemSymm L 2 * elemSymm L 4)
        + (-1 + 2 * u + 2 * q - u ^ 2 - 4 * q * u - q ^ 2 + 2 * q * u ^ 2 + 2 * q ^ 2 * u
            - q ^ 2 * u ^ 2) • elemSymm L 3 ^ 2
        + (-u ^ 3 - q * u ^ 2 - q ^ 2 * u - q ^ 3 + 2 * u ^ 4 + 4 * q * u ^ 3 + 4 * q ^ 2 * u ^ 2
            + 4 * q ^ 3 * u + 2 * q ^ 4 - u ^ 5 - 5 * q * u ^ 4 - 6 * q ^ 2 * u ^ 3
            - 6 * q ^ 3 * u ^ 2 - 5 * q ^ 4 * u - q ^ 5 + 2 * q * u ^ 5 + 4 * q ^ 2 * u ^ 4
            + 4 * q ^ 3 * u ^ 3 + 4 * q ^ 4 * u ^ 2 + 2 * q ^ 5 * u - q ^ 2 * u ^ 5
            - q ^ 3 * u ^ 4 - q ^ 4 * u ^ 3 - q ^ 5 * u ^ 2) • elemSymm L 6 := by
  rw [dop_one_mul_one q u (elemSymm L 4),
    dop_one_elemSymm_four, dop_two_elemSymm_four]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add,
    MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `D_1(e_2e_3)`, the Pieri rule `HJO.Sym.dop_two_mul_one` at `f = e_3` against `D_1(e_3)`,
`D_2(e_3)` and `D_3(e_3)`. -/
theorem dop_one_mono_23 (q u : L) :
    Dop q u 1 (elemSymm L 2 * elemSymm L 3)
      = (-u - q + 2 * u ^ 2 + 4 * q * u + 2 * q ^ 2 - u ^ 3 - 5 * q * u ^ 2 - 5 * q ^ 2 * u
            - q ^ 3 + 2 * q * u ^ 3 + 4 * q ^ 2 * u ^ 2 + 2 * q ^ 3 * u - q ^ 2 * u ^ 3
            - q ^ 3 * u ^ 2) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (-1 + 2 * u + 2 * q - 2 * u ^ 2 - 5 * q * u - 2 * q ^ 2 + 3 * q * u ^ 2 + 3 * q ^ 2 * u
            - q ^ 2 * u ^ 2) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (-2 * u ^ 2 - 3 * q * u - 2 * q ^ 2 + 4 * u ^ 3 + 10 * q * u ^ 2 + 10 * q ^ 2 * u
            + 4 * q ^ 3 - 2 * u ^ 4 - 11 * q * u ^ 3 - 16 * q ^ 2 * u ^ 2 - 11 * q ^ 3 * u
            - 2 * q ^ 4 + 4 * q * u ^ 4 + 10 * q ^ 2 * u ^ 3 + 10 * q ^ 3 * u ^ 2 + 4 * q ^ 4 * u
            - 2 * q ^ 2 * u ^ 4 - 3 * q ^ 3 * u ^ 3
            - 2 * q ^ 4 * u ^ 2) • (elemSymm L 1 * elemSymm L 5)
        + (1 - u - q + q * u) • elemSymm L 2 ^ 3
        + (-u - q + 3 * u ^ 2 + 5 * q * u + 3 * q ^ 2 - 2 * u ^ 3 - 7 * q * u ^ 2 - 7 * q ^ 2 * u
            - 2 * q ^ 3 + 3 * q * u ^ 3 + 5 * q ^ 2 * u ^ 2 + 3 * q ^ 3 * u - q ^ 2 * u ^ 3
            - q ^ 3 * u ^ 2) • (elemSymm L 2 * elemSymm L 4)
        + (u + q - u ^ 2 - 2 * q * u - q ^ 2 + q * u ^ 2 + q ^ 2 * u) • elemSymm L 3 ^ 2
        + (-u ^ 3 - 2 * q * u ^ 2 - 2 * q ^ 2 * u - q ^ 3 + 2 * u ^ 4 + 6 * q * u ^ 3
            + 8 * q ^ 2 * u ^ 2 + 6 * q ^ 3 * u + 2 * q ^ 4 - u ^ 5 - 6 * q * u ^ 4
            - 11 * q ^ 2 * u ^ 3 - 11 * q ^ 3 * u ^ 2 - 6 * q ^ 4 * u - q ^ 5 + 2 * q * u ^ 5
            + 6 * q ^ 2 * u ^ 4 + 8 * q ^ 3 * u ^ 3 + 6 * q ^ 4 * u ^ 2 + 2 * q ^ 5 * u
            - q ^ 2 * u ^ 5 - 2 * q ^ 3 * u ^ 4 - 2 * q ^ 4 * u ^ 3
            - q ^ 5 * u ^ 2) • elemSymm L 6 := by
  rw [dop_two_mul_one q u (elemSymm L 3),
    dop_one_elemSymm_three, dop_two_elemSymm_three, dop_three_elemSymm_three]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add,
    MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `D_1(e_1e_2)`, the Pieri rule `HJO.Sym.dop_one_mul_one` at `f = e_2` against `D_1(e_2)`
and `D_2(e_2)`. -/
theorem dop_one_mono_12 (q u : L) :
    Dop q u 1 (elemSymm L 1 * elemSymm L 2)
      = (-u - q + q * u) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))
        + (-1 + 3 * u + 3 * q - 2 * u ^ 2 - 6 * q * u - 2 * q ^ 2 + 3 * q * u ^ 2 + 3 * q ^ 2 * u
            - q ^ 2 * u ^ 2) • (elemSymm L 1 * elemSymm L 3)
        + (1 - u - q + q * u) • (elemSymm L 2 * elemSymm L 2)
        + (-u - q + 2 * u ^ 2 + 4 * q * u + 2 * q ^ 2 - u ^ 3 - 5 * q * u ^ 2 - 5 * q ^ 2 * u
            - q ^ 3 + 2 * q * u ^ 3 + 4 * q ^ 2 * u ^ 2 + 2 * q ^ 3 * u - q ^ 2 * u ^ 3
            - q ^ 3 * u ^ 2) • elemSymm L 4 := by
  rw [dop_one_mul_one q u (elemSymm L 2),
    dop_one_elemSymm_two, dop_two_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add,
    MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `D_3(e_1e_2)`, the Pieri rule `HJO.Sym.dop_one_mul_three` at `f = e_2` against `D_3(e_2)`
and `D_4(e_2)`. This is the highest operator index the computation reaches. -/
theorem dop_three_mono_12 (q u : L) :
    Dop q u 3 (elemSymm L 1 * elemSymm L 2)
      = (1 - u - q + q * u) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (-1 : L) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (-1 + 3 * u + 3 * q - 2 * u ^ 2 - 6 * q * u - 2 * q ^ 2 + 3 * q * u ^ 2 + 3 * q ^ 2 * u
            - q ^ 2 * u ^ 2) • (elemSymm L 1 * elemSymm L 5)
        + (1 - u - q + q * u) • (elemSymm L 2 * elemSymm L 4)
        + (-u - q + 2 * u ^ 2 + 4 * q * u + 2 * q ^ 2 - u ^ 3 - 5 * q * u ^ 2 - 5 * q ^ 2 * u
            - q ^ 3 + 2 * q * u ^ 3 + 4 * q ^ 2 * u ^ 2 + 2 * q ^ 3 * u - q ^ 2 * u ^ 3
            - q ^ 3 * u ^ 2) • elemSymm L 6 := by
  rw [dop_one_mul_three q u (elemSymm L 2),
    dop_three_elemSymm_two, dop_four_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add,
    MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `D_2(e_1^2e_2)`, the Pieri rule `HJO.Sym.dop_one_mul_two` at `f = e_1e_2` against the two
values of `D` on `e_1e_2` above. -/
theorem dop_two_mono_112 (q u : L) :
    Dop q u 2 (elemSymm L 1 * (elemSymm L 1 * elemSymm L 2))
      = (-1 + u + q - q * u) • (elemSymm L 1 ^ 3 * elemSymm L 3)
        + (1 : L) • (elemSymm L 1 ^ 2 * elemSymm L 2 ^ 2)
        + (2 - 5 * u - 5 * q + 3 * u ^ 2 + 10 * q * u + 3 * q ^ 2 - 5 * q * u ^ 2 - 5 * q ^ 2 * u
            + 2 * q ^ 2 * u ^ 2) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (-2 + 2 * u + 2 * q - 2 * q * u) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (-1 + 5 * u + 5 * q - 7 * u ^ 2 - 17 * q * u - 7 * q ^ 2 + 3 * u ^ 3 + 19 * q * u ^ 2
            + 19 * q ^ 2 * u + 3 * q ^ 3 - 7 * q * u ^ 3 - 17 * q ^ 2 * u ^ 2 - 7 * q ^ 3 * u
            + 5 * q ^ 2 * u ^ 3 + 5 * q ^ 3 * u ^ 2
            - q ^ 3 * u ^ 3) • (elemSymm L 1 * elemSymm L 5)
        + (1 - 2 * u - 2 * q + u ^ 2 + 4 * q * u + q ^ 2 - 2 * q * u ^ 2 - 2 * q ^ 2 * u
            + q ^ 2 * u ^ 2) • (elemSymm L 2 * elemSymm L 4)
        + (-u - q + 3 * u ^ 2 + 6 * q * u + 3 * q ^ 2 - 3 * u ^ 3 - 12 * q * u ^ 2
            - 12 * q ^ 2 * u - 3 * q ^ 3 + u ^ 4 + 10 * q * u ^ 3 + 18 * q ^ 2 * u ^ 2
            + 10 * q ^ 3 * u + q ^ 4 - 3 * q * u ^ 4 - 12 * q ^ 2 * u ^ 3 - 12 * q ^ 3 * u ^ 2
            - 3 * q ^ 4 * u + 3 * q ^ 2 * u ^ 4 + 6 * q ^ 3 * u ^ 3 + 3 * q ^ 4 * u ^ 2
            - q ^ 3 * u ^ 4 - q ^ 4 * u ^ 3) • elemSymm L 6 := by
  rw [dop_one_mul_two q u (elemSymm L 1 * elemSymm L 2),
    dop_two_mono_12, dop_three_mono_12]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add,
    MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `D_1(e_1^2e_3)`, the Pieri rule `HJO.Sym.dop_one_mul_one` at `f = e_1e_3` against the two
values of `D` on `e_1e_3` above. -/
theorem dop_one_mono_113 (q u : L) :
    Dop q u 1 (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
      = (-1 + u + q - u ^ 2 - 2 * q * u - q ^ 2 + q * u ^ 2
            + q ^ 2 * u) • (elemSymm L 1 ^ 3 * elemSymm L 3)
        + (1 - u - q + q * u) • (elemSymm L 1 ^ 2 * elemSymm L 2 ^ 2)
        + (-2 * u - 2 * q + 5 * u ^ 2 + 9 * q * u + 5 * q ^ 2 - 3 * u ^ 3 - 12 * q * u ^ 2
            - 12 * q ^ 2 * u - 3 * q ^ 3 + 5 * q * u ^ 3 + 9 * q ^ 2 * u ^ 2 + 5 * q ^ 3 * u
            - 2 * q ^ 2 * u ^ 3 - 2 * q ^ 3 * u ^ 2) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (2 * u + 2 * q - 2 * u ^ 2 - 6 * q * u - 2 * q ^ 2 + 4 * q * u ^ 2 + 4 * q ^ 2 * u
            - 2 * q ^ 2 * u ^ 2) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (u + q - 5 * u ^ 2 - 8 * q * u - 5 * q ^ 2 + 7 * u ^ 3 + 20 * q * u ^ 2 + 20 * q ^ 2 * u
            + 7 * q ^ 3 - 3 * u ^ 4 - 20 * q * u ^ 3 - 30 * q ^ 2 * u ^ 2 - 20 * q ^ 3 * u
            - 3 * q ^ 4 + 7 * q * u ^ 4 + 20 * q ^ 2 * u ^ 3 + 20 * q ^ 3 * u ^ 2 + 7 * q ^ 4 * u
            - 5 * q ^ 2 * u ^ 4 - 8 * q ^ 3 * u ^ 3 - 5 * q ^ 4 * u ^ 2 + q ^ 3 * u ^ 4
            + q ^ 4 * u ^ 3) • (elemSymm L 1 * elemSymm L 5)
        + (1 - 3 * u - 3 * q + 3 * u ^ 2 + 9 * q * u + 3 * q ^ 2 - u ^ 3 - 9 * q * u ^ 2
            - 9 * q ^ 2 * u - q ^ 3 + 3 * q * u ^ 3 + 9 * q ^ 2 * u ^ 2 + 3 * q ^ 3 * u
            - 3 * q ^ 2 * u ^ 3 - 3 * q ^ 3 * u ^ 2
            + q ^ 3 * u ^ 3) • (elemSymm L 2 * elemSymm L 4)
        + (-1 + 2 * u + 2 * q - u ^ 2 - 4 * q * u - q ^ 2 + 2 * q * u ^ 2 + 2 * q ^ 2 * u
            - q ^ 2 * u ^ 2) • elemSymm L 3 ^ 2
        + (u ^ 2 + q * u + q ^ 2 - 3 * u ^ 3 - 6 * q * u ^ 2 - 6 * q ^ 2 * u - 3 * q ^ 3
            + 3 * u ^ 4 + 12 * q * u ^ 3 + 15 * q ^ 2 * u ^ 2 + 12 * q ^ 3 * u + 3 * q ^ 4 - u ^ 5
            - 10 * q * u ^ 4 - 19 * q ^ 2 * u ^ 3 - 19 * q ^ 3 * u ^ 2 - 10 * q ^ 4 * u - q ^ 5
            + 3 * q * u ^ 5 + 12 * q ^ 2 * u ^ 4 + 15 * q ^ 3 * u ^ 3 + 12 * q ^ 4 * u ^ 2
            + 3 * q ^ 5 * u - 3 * q ^ 2 * u ^ 5 - 6 * q ^ 3 * u ^ 4 - 6 * q ^ 4 * u ^ 3
            - 3 * q ^ 5 * u ^ 2 + q ^ 3 * u ^ 5 + q ^ 4 * u ^ 4
            + q ^ 5 * u ^ 3) • elemSymm L 6 := by
  rw [dop_one_mul_one q u (elemSymm L 1 * elemSymm L 3),
    dop_one_mono_13, dop_two_mono_13]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add,
    MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- `D_1(e_1e_2^2)`, the Pieri rule `HJO.Sym.dop_one_mul_one` at `f = e_2^2` against the two
values of `D` on `e_2^2` above. -/
theorem dop_one_mono_122 (q u : L) :
    Dop q u 1 (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))
      = (-1 + 2 * u + 2 * q - u ^ 2 - 4 * q * u - q ^ 2 + 2 * q * u ^ 2 + 2 * q ^ 2 * u
            - q ^ 2 * u ^ 2) • (elemSymm L 1 ^ 3 * elemSymm L 3)
        + (1 - 2 * u - 2 * q + 2 * q * u) • (elemSymm L 1 ^ 2 * elemSymm L 2 ^ 2)
        + (1 - 5 * u - 5 * q + 7 * u ^ 2 + 17 * q * u + 7 * q ^ 2 - 3 * u ^ 3 - 19 * q * u ^ 2
            - 19 * q ^ 2 * u - 3 * q ^ 3 + 7 * q * u ^ 3 + 17 * q ^ 2 * u ^ 2 + 7 * q ^ 3 * u
            - 5 * q ^ 2 * u ^ 3 - 5 * q ^ 3 * u ^ 2
            + q ^ 3 * u ^ 3) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (-2 + 6 * u + 6 * q - 4 * u ^ 2 - 12 * q * u - 4 * q ^ 2 + 6 * q * u ^ 2 + 6 * q ^ 2 * u
            - 2 * q ^ 2 * u ^ 2) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (2 * u + 2 * q - 7 * u ^ 2 - 14 * q * u - 7 * q ^ 2 + 8 * u ^ 3 + 30 * q * u ^ 2
            + 30 * q ^ 2 * u + 8 * q ^ 3 - 3 * u ^ 4 - 26 * q * u ^ 3 - 46 * q ^ 2 * u ^ 2
            - 26 * q ^ 3 * u - 3 * q ^ 4 + 8 * q * u ^ 4 + 30 * q ^ 2 * u ^ 3 + 30 * q ^ 3 * u ^ 2
            + 8 * q ^ 4 * u - 7 * q ^ 2 * u ^ 4 - 14 * q ^ 3 * u ^ 3 - 7 * q ^ 4 * u ^ 2
            + 2 * q ^ 3 * u ^ 4 + 2 * q ^ 4 * u ^ 3) • (elemSymm L 1 * elemSymm L 5)
        + (1 - u - q + q * u) • elemSymm L 2 ^ 3
        + (-2 * u - 2 * q + 4 * u ^ 2 + 8 * q * u + 4 * q ^ 2 - 2 * u ^ 3 - 10 * q * u ^ 2
            - 10 * q ^ 2 * u - 2 * q ^ 3 + 4 * q * u ^ 3 + 8 * q ^ 2 * u ^ 2 + 4 * q ^ 3 * u
            - 2 * q ^ 2 * u ^ 3 - 2 * q ^ 3 * u ^ 2) • (elemSymm L 2 * elemSymm L 4)
        + (u ^ 2 + 2 * q * u + q ^ 2 - 3 * u ^ 3 - 9 * q * u ^ 2 - 9 * q ^ 2 * u - 3 * q ^ 3
            + 3 * u ^ 4 + 15 * q * u ^ 3 + 24 * q ^ 2 * u ^ 2 + 15 * q ^ 3 * u + 3 * q ^ 4 - u ^ 5
            - 11 * q * u ^ 4 - 28 * q ^ 2 * u ^ 3 - 28 * q ^ 3 * u ^ 2 - 11 * q ^ 4 * u - q ^ 5
            + 3 * q * u ^ 5 + 15 * q ^ 2 * u ^ 4 + 24 * q ^ 3 * u ^ 3 + 15 * q ^ 4 * u ^ 2
            + 3 * q ^ 5 * u - 3 * q ^ 2 * u ^ 5 - 9 * q ^ 3 * u ^ 4 - 9 * q ^ 4 * u ^ 3
            - 3 * q ^ 5 * u ^ 2 + q ^ 3 * u ^ 5 + 2 * q ^ 4 * u ^ 4
            + q ^ 5 * u ^ 3) • elemSymm L 6 := by
  rw [dop_one_mul_one q u (elemSymm L 2 * elemSymm L 2),
    dop_one_mono_22, dop_two_mono_22]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_add,
    MvPolynomial.C_neg, MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-! ### The slope-operator values -/

/-- **`Q_{2,3}(e_2)`**, the value the `(3,5)` recursion needs at the vacuum.

`Split 2 3 = (1,1)`, so `HJO.Sym.Qop` reads `Q_{2,3} = M^{-1}[D_2, D_1]`, and the two branches are
`D_2(D_1e_2)` and `D_1(D_2e_2)`, expanded through the Pieri rules of
`HJO/Shuffle/MellitTwoPartTwoThreeLambda.lean` and its base table. The bracket comes out as
`M` times the stated value, so `M ≠ 0` is spent once and the answer is a polynomial. -/
theorem qop_two_three_apply_elemSymm_two (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 2 3 (elemSymm L 2)
      = (u + q - u ^ 2 - 2 * q * u - q ^ 2 + q * u ^ 2
            + q ^ 2 * u) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
        + (-u - q + q * u) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))
        + (-u - q + 2 * u ^ 2 + 4 * q * u + 2 * q ^ 2 - 3 * q * u ^ 2 - 3 * q ^ 2 * u - u ^ 4
            - q * u ^ 3 - q ^ 3 * u - q ^ 4 + q * u ^ 4 + q ^ 2 * u ^ 3 + q ^ 3 * u ^ 2
            + q ^ 4 * u) • (elemSymm L 1 * elemSymm L 4)
        + (u + q - 2 * q * u - u ^ 3 - q * u ^ 2 - q ^ 2 * u - q ^ 3 + q * u ^ 3 + q ^ 2 * u ^ 2
            + q ^ 3 * u) • (elemSymm L 2 * elemSymm L 3)
        + (-u ^ 2 - q * u - q ^ 2 + u ^ 3 + 3 * q * u ^ 2 + 3 * q ^ 2 * u + q ^ 3 + u ^ 4
            - q * u ^ 3 - 2 * q ^ 2 * u ^ 2 - q ^ 3 * u + q ^ 4 - u ^ 5 - 2 * q * u ^ 4
            - q ^ 2 * u ^ 3 - q ^ 3 * u ^ 2 - 2 * q ^ 4 * u - q ^ 5 + q * u ^ 5 + q ^ 2 * u ^ 4
            + q ^ 3 * u ^ 3 + q ^ 4 * u ^ 2 + q ^ 5 * u) • elemSymm L 5 := by
  have hQ := qop_of_coprime q u (m := 2) (n := 3) (by norm_num) (by decide)
  rw [show Split 2 3 = ((1 : ℕ), (1 : ℕ)) from by decide] at hQ
  norm_num only at hQ
  rw [hQ, LinearMap.smul_apply, inv_smul_eq_iff₀ hM]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, qop_one]
  rw [dop_one_elemSymm_two, dop_two_elemSymm_two]
  simp only [map_add, map_sub, map_smul]
  rw [dop_two_mono_12, dop_two_elemSymm_three, dop_one_mono_13, dop_one_mono_22,
    dop_one_elemSymm_four]
  match_scalars <;> grobner

/-- **`Q_{2,3}(e_3)`**, one of the two degree-three values `Q_{2,3}(Q_{2,3}1)` is built from.

Same recursion as `HJO.Sym.qop_two_three_apply_elemSymm_two`, at `e_3`. Nine `e`-monomials of
degree six occur; the `e_2^3` coefficient is `M`. -/
theorem qop_two_three_apply_elemSymm_three (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 2 3 (elemSymm L 3)
      = (1 - 2 * u - 2 * q + u ^ 2 + 4 * q * u + q ^ 2 + u ^ 3 - q * u ^ 2 - q ^ 2 * u + q ^ 3
            - u ^ 4 - 2 * q * u ^ 3 - q ^ 2 * u ^ 2 - 2 * q ^ 3 * u - q ^ 4 + q * u ^ 4
            + q ^ 2 * u ^ 3 + q ^ 3 * u ^ 2 + q ^ 4 * u) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (-2 + 3 * u + 3 * q - u ^ 2 - 4 * q * u - q ^ 2 - u ^ 3 - q ^ 3 + q * u ^ 3
            + q ^ 2 * u ^ 2 + q ^ 3 * u) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (u + q - 2 * u ^ 2 - 4 * q * u - 2 * q ^ 2 + 4 * q * u ^ 2 + 4 * q ^ 2 * u + 2 * u ^ 4
            + 2 * q * u ^ 3 + 2 * q ^ 3 * u + 2 * q ^ 4 - 3 * q * u ^ 4 - 3 * q ^ 2 * u ^ 3
            - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 4 * u - u ^ 6 - q * u ^ 5 - q ^ 5 * u - q ^ 6
            + q * u ^ 6 + q ^ 2 * u ^ 5 + q ^ 3 * u ^ 4 + q ^ 4 * u ^ 3 + q ^ 5 * u ^ 2
            + q ^ 6 * u) • (elemSymm L 1 * elemSymm L 5)
        + (1 - u - q + q * u) • elemSymm L 2 ^ 3
        + (-1 + u + q + u ^ 2 - q * u + q ^ 2 - u ^ 3 - q ^ 3 + u ^ 4 + q * u ^ 3 - q ^ 2 * u ^ 2
            + q ^ 3 * u + q ^ 4 - u ^ 5 - 2 * q * u ^ 4 - q ^ 2 * u ^ 3 - q ^ 3 * u ^ 2
            - 2 * q ^ 4 * u - q ^ 5 + q * u ^ 5 + q ^ 2 * u ^ 4 + q ^ 3 * u ^ 3 + q ^ 4 * u ^ 2
            + q ^ 5 * u) • (elemSymm L 2 * elemSymm L 4)
        + (1 - 2 * u - 2 * q + u ^ 2 + 3 * q * u + q ^ 2 + u ^ 3 - q * u ^ 2 - q ^ 2 * u + q ^ 3
            - u ^ 4 - 2 * q * u ^ 3 - q ^ 2 * u ^ 2 - 2 * q ^ 3 * u - q ^ 4 + q * u ^ 4
            + q ^ 2 * u ^ 3 + q ^ 3 * u ^ 2 + q ^ 4 * u) • elemSymm L 3 ^ 2
        + (q * u - 2 * q * u ^ 2 - 2 * q ^ 2 * u - u ^ 4 + 3 * q ^ 2 * u ^ 2 - q ^ 4 + u ^ 5
            + 3 * q * u ^ 4 + q ^ 2 * u ^ 3 + q ^ 3 * u ^ 2 + 3 * q ^ 4 * u + q ^ 5 + u ^ 6
            - q * u ^ 5 - 2 * q ^ 2 * u ^ 4 - q ^ 3 * u ^ 3 - 2 * q ^ 4 * u ^ 2 - q ^ 5 * u
            + q ^ 6 - u ^ 7 - 2 * q * u ^ 6 - q ^ 2 * u ^ 5 - q ^ 3 * u ^ 4 - q ^ 4 * u ^ 3
            - q ^ 5 * u ^ 2 - 2 * q ^ 6 * u - q ^ 7 + q * u ^ 7 + q ^ 2 * u ^ 6 + q ^ 3 * u ^ 5
            + q ^ 4 * u ^ 4 + q ^ 5 * u ^ 3 + q ^ 6 * u ^ 2 + q ^ 7 * u) • elemSymm L 6 := by
  have hQ := qop_of_coprime q u (m := 2) (n := 3) (by norm_num) (by decide)
  rw [show Split 2 3 = ((1 : ℕ), (1 : ℕ)) from by decide] at hQ
  norm_num only at hQ
  rw [hQ, LinearMap.smul_apply, inv_smul_eq_iff₀ hM]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, qop_one]
  rw [dop_one_elemSymm_three, dop_two_elemSymm_three]
  simp only [map_add, map_smul]
  rw [dop_two_mono_13, dop_two_mono_22, dop_two_elemSymm_four, dop_one_mono_14,
    dop_one_mono_23, dop_one_elemSymm_five]
  match_scalars <;> grobner

/-- **`Q_{2,3}(e_1e_2)`**, the other degree-three value. This is the largest intermediate of
the computation: 179 `(q,u)`-terms over the nine degree-six monomials. -/
theorem qop_two_three_apply_elemSymm_one_mul_two (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 2 3 (elemSymm L 1 * elemSymm L 2)
      = (u + q - u ^ 2 - 2 * q * u - q ^ 2 + q * u ^ 2
            + q ^ 2 * u) • (elemSymm L 1 ^ 3 * elemSymm L 3)
        + (-u - q + q * u) • (elemSymm L 1 ^ 2 * elemSymm L 2 ^ 2)
        + (1 - 4 * u - 4 * q + 4 * u ^ 2 + 11 * q * u + 4 * q ^ 2 + u ^ 3 - 6 * q * u ^ 2
            - 6 * q ^ 2 * u + q ^ 3 - 2 * u ^ 4 - 4 * q * u ^ 3 - q ^ 2 * u ^ 2 - 4 * q ^ 3 * u
            - 2 * q ^ 4 + 3 * q * u ^ 4 + 4 * q ^ 2 * u ^ 3 + 4 * q ^ 3 * u ^ 2 + 3 * q ^ 4 * u
            - q ^ 2 * u ^ 4 - q ^ 3 * u ^ 3 - q ^ 4 * u ^ 2) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (-2 + 5 * u + 5 * q - u ^ 2 - 8 * q * u - q ^ 2 - 2 * u ^ 3 - q * u ^ 2 - q ^ 2 * u
            - 2 * q ^ 3 + 3 * q * u ^ 3 + 3 * q ^ 2 * u ^ 2 + 3 * q ^ 3 * u - q ^ 2 * u ^ 3
            - q ^ 3 * u ^ 2) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (2 * u + 2 * q - 5 * u ^ 2 - 10 * q * u - 5 * q ^ 2 + u ^ 3 + 12 * q * u ^ 2
            + 12 * q ^ 2 * u + q ^ 3 + 4 * u ^ 4 + 3 * q * u ^ 3 - 3 * q ^ 2 * u ^ 2
            + 3 * q ^ 3 * u + 4 * q ^ 4 - u ^ 5 - 9 * q * u ^ 4 - 10 * q ^ 2 * u ^ 3
            - 10 * q ^ 3 * u ^ 2 - 9 * q ^ 4 * u - q ^ 5 - u ^ 6 + 5 * q ^ 2 * u ^ 4
            + 6 * q ^ 3 * u ^ 3 + 5 * q ^ 4 * u ^ 2 - q ^ 6 + 2 * q * u ^ 6 + 2 * q ^ 2 * u ^ 5
            + q ^ 3 * u ^ 4 + q ^ 4 * u ^ 3 + 2 * q ^ 5 * u ^ 2 + 2 * q ^ 6 * u - q ^ 2 * u ^ 6
            - q ^ 3 * u ^ 5 - q ^ 4 * u ^ 4 - q ^ 5 * u ^ 3
            - q ^ 6 * u ^ 2) • (elemSymm L 1 * elemSymm L 5)
        + (1 - u - q + q * u) • elemSymm L 2 ^ 3
        + (-1 + u + q - 2 * q * u + 3 * q * u ^ 2 + 3 * q ^ 2 * u + u ^ 4 - q * u ^ 3
            - 5 * q ^ 2 * u ^ 2 - q ^ 3 * u + q ^ 4 - u ^ 5 - 3 * q * u ^ 4 - 3 * q ^ 4 * u
            - q ^ 5 + 2 * q * u ^ 5 + 3 * q ^ 2 * u ^ 4 + 2 * q ^ 3 * u ^ 3 + 3 * q ^ 4 * u ^ 2
            + 2 * q ^ 5 * u - q ^ 2 * u ^ 5 - q ^ 3 * u ^ 4 - q ^ 4 * u ^ 3
            - q ^ 5 * u ^ 2) • (elemSymm L 2 * elemSymm L 4)
        + (1 - 3 * u - 3 * q + 2 * u ^ 2 + 7 * q * u + 2 * q ^ 2 + u ^ 3 - 3 * q * u ^ 2
            - 3 * q ^ 2 * u + q ^ 3 - u ^ 4 - 3 * q * u ^ 3 - q ^ 2 * u ^ 2 - 3 * q ^ 3 * u
            - q ^ 4 + 2 * q * u ^ 4 + 3 * q ^ 2 * u ^ 3 + 3 * q ^ 3 * u ^ 2 + 2 * q ^ 4 * u
            - q ^ 2 * u ^ 4 - q ^ 3 * u ^ 3 - q ^ 4 * u ^ 2) • elemSymm L 3 ^ 2
        + (u ^ 2 + 2 * q * u + q ^ 2 - u ^ 3 - 6 * q * u ^ 2 - 6 * q ^ 2 * u - q ^ 3 - 2 * u ^ 4
            + 2 * q * u ^ 3 + 8 * q ^ 2 * u ^ 2 + 2 * q ^ 3 * u - 2 * q ^ 4 + 2 * u ^ 5
            + 7 * q * u ^ 4 + 2 * q ^ 2 * u ^ 3 + 2 * q ^ 3 * u ^ 2 + 7 * q ^ 4 * u + 2 * q ^ 5
            + u ^ 6 - 4 * q * u ^ 5 - 8 * q ^ 2 * u ^ 4 - 6 * q ^ 3 * u ^ 3 - 8 * q ^ 4 * u ^ 2
            - 4 * q ^ 5 * u + q ^ 6 - u ^ 7 - 3 * q * u ^ 6 + q ^ 2 * u ^ 5 + 2 * q ^ 3 * u ^ 4
            + 2 * q ^ 4 * u ^ 3 + q ^ 5 * u ^ 2 - 3 * q ^ 6 * u - q ^ 7 + 2 * q * u ^ 7
            + 3 * q ^ 2 * u ^ 6 + 2 * q ^ 3 * u ^ 5 + 2 * q ^ 4 * u ^ 4 + 2 * q ^ 5 * u ^ 3
            + 3 * q ^ 6 * u ^ 2 + 2 * q ^ 7 * u - q ^ 2 * u ^ 7 - q ^ 3 * u ^ 6 - q ^ 4 * u ^ 5
            - q ^ 5 * u ^ 4 - q ^ 6 * u ^ 3 - q ^ 7 * u ^ 2) • elemSymm L 6 := by
  have hQ := qop_of_coprime q u (m := 2) (n := 3) (by norm_num) (by decide)
  rw [show Split 2 3 = ((1 : ℕ), (1 : ℕ)) from by decide] at hQ
  norm_num only at hQ
  rw [hQ, LinearMap.smul_apply, inv_smul_eq_iff₀ hM]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, qop_one]
  rw [dop_one_mono_12, dop_two_mono_12]
  simp only [map_add, map_smul]
  rw [dop_two_mono_112, dop_two_mono_13, dop_two_mono_22, dop_two_elemSymm_four,
    dop_one_mono_113, dop_one_mono_122, dop_one_mono_14, dop_one_mono_23,
    dop_one_elemSymm_five]
  match_scalars <;> grobner

/-- **`Q_{2,3}(Q_{2,3}1)`**, the first term of the `Λ` side of the two-part clause at `(2,3)`.

`HJO.Sym.qop_two_three_apply_one` gives `Q_{2,3}(1) = -e_1e_2 + (1-q-u)e_3`, and the two values
`HJO.Sym.qop_two_three_apply_elemSymm_three` and `HJO.Sym.qop_two_three_apply_elemSymm_one_mul_two`
evaluate `Q_{2,3}` on each summand. -/
theorem qop_two_three_apply_qop_two_three_apply_one (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 2 3 (Qop q u 2 3 (1 : Lambda L))
      = (-u - q + u ^ 2 + 2 * q * u + q ^ 2 - q * u ^ 2
            - q ^ 2 * u) • (elemSymm L 1 ^ 3 * elemSymm L 3)
        + (u + q - q * u) • (elemSymm L 1 ^ 2 * elemSymm L 2 ^ 2)
        + (u + q - u ^ 2 - 3 * q * u - q ^ 2 - u ^ 3 - q ^ 3 + 2 * q * u ^ 3 + 2 * q ^ 2 * u ^ 2
            + 2 * q ^ 3 * u + u ^ 5 + q * u ^ 4 + q ^ 4 * u + q ^ 5 - q * u ^ 5 - q ^ 2 * u ^ 4
            - q ^ 3 * u ^ 3 - q ^ 4 * u ^ 2 - q ^ 5 * u) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (-3 * u ^ 2 - 2 * q * u - 3 * q ^ 2 + 2 * u ^ 3 + 6 * q * u ^ 2 + 6 * q ^ 2 * u
            + 2 * q ^ 3 + u ^ 4 - q * u ^ 3 - 2 * q ^ 2 * u ^ 2 - q ^ 3 * u + q ^ 4 - q * u ^ 4
            - q ^ 2 * u ^ 3 - q ^ 3 * u ^ 2
            - q ^ 4 * u) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (-u - q + 2 * u ^ 2 + 4 * q * u + 2 * q ^ 2 + u ^ 3 - 2 * q * u ^ 2 - 2 * q ^ 2 * u
            + q ^ 3 - 2 * u ^ 4 - 5 * q * u ^ 3 - 5 * q ^ 2 * u ^ 2 - 5 * q ^ 3 * u - 2 * q ^ 4
            - u ^ 5 + 2 * q * u ^ 4 + 5 * q ^ 2 * u ^ 3 + 5 * q ^ 3 * u ^ 2 + 2 * q ^ 4 * u
            - q ^ 5 + 2 * q * u ^ 5 + q ^ 2 * u ^ 4 + q ^ 4 * u ^ 2 + 2 * q ^ 5 * u + u ^ 7
            + q * u ^ 6 + q ^ 6 * u + q ^ 7 - q * u ^ 7 - q ^ 2 * u ^ 6 - q ^ 3 * u ^ 5
            - q ^ 4 * u ^ 4 - q ^ 5 * u ^ 3 - q ^ 6 * u ^ 2
            - q ^ 7 * u) • (elemSymm L 1 * elemSymm L 5)
        + (-u - q + u ^ 2 + 2 * q * u + q ^ 2 - q * u ^ 2 - q ^ 2 * u) • elemSymm L 2 ^ 3
        + (u + q - q * u - 2 * u ^ 3 - 3 * q * u ^ 2 - 3 * q ^ 2 * u - 2 * q ^ 3 + u ^ 4
            + 3 * q * u ^ 3 + 4 * q ^ 2 * u ^ 2 + 3 * q ^ 3 * u + q ^ 4 - u ^ 5 - q * u ^ 4
            - q ^ 2 * u ^ 3 - q ^ 3 * u ^ 2 - q ^ 4 * u - q ^ 5 + u ^ 6 + 2 * q * u ^ 5
            + q ^ 2 * u ^ 4 + q ^ 3 * u ^ 3 + q ^ 4 * u ^ 2 + 2 * q ^ 5 * u + q ^ 6 - q * u ^ 6
            - q ^ 2 * u ^ 5 - q ^ 3 * u ^ 4 - q ^ 4 * u ^ 3 - q ^ 5 * u ^ 2
            - q ^ 6 * u) • (elemSymm L 2 * elemSymm L 4)
        + (u ^ 2 + q ^ 2 - u ^ 3 - 2 * q * u ^ 2 - 2 * q ^ 2 * u - q ^ 3 - u ^ 4 + q * u ^ 3
            + 2 * q ^ 2 * u ^ 2 + q ^ 3 * u - q ^ 4 + u ^ 5 + 2 * q * u ^ 4 + q ^ 2 * u ^ 3
            + q ^ 3 * u ^ 2 + 2 * q ^ 4 * u + q ^ 5 - q * u ^ 5 - q ^ 2 * u ^ 4 - q ^ 3 * u ^ 3
            - q ^ 4 * u ^ 2 - q ^ 5 * u) • elemSymm L 3 ^ 2
        + (-u ^ 2 - q * u - q ^ 2 + u ^ 3 + 3 * q * u ^ 2 + 3 * q ^ 2 * u + q ^ 3 + u ^ 4
            - q ^ 2 * u ^ 2 + q ^ 4 - 3 * q * u ^ 4 - 4 * q ^ 2 * u ^ 3 - 4 * q ^ 3 * u ^ 2
            - 3 * q ^ 4 * u - u ^ 6 - q * u ^ 5 + 2 * q ^ 2 * u ^ 4 + 3 * q ^ 3 * u ^ 3
            + 2 * q ^ 4 * u ^ 2 - q ^ 5 * u - q ^ 6 - u ^ 7 + q * u ^ 6 + q ^ 2 * u ^ 5
            + q ^ 5 * u ^ 2 + q ^ 6 * u - q ^ 7 + u ^ 8 + 2 * q * u ^ 7 + q ^ 2 * u ^ 6
            + q ^ 3 * u ^ 5 + q ^ 4 * u ^ 4 + q ^ 5 * u ^ 3 + q ^ 6 * u ^ 2 + 2 * q ^ 7 * u
            + q ^ 8 - q * u ^ 8 - q ^ 2 * u ^ 7 - q ^ 3 * u ^ 6 - q ^ 4 * u ^ 5 - q ^ 5 * u ^ 4
            - q ^ 6 * u ^ 3 - q ^ 7 * u ^ 2 - q ^ 8 * u) • elemSymm L 6 := by
  rw [qop_two_three_apply_one hM]
  simp only [map_add, map_neg, map_smul]
  rw [qop_two_three_apply_elemSymm_one_mul_two hM, qop_two_three_apply_elemSymm_three hM]
  match_scalars <;> grobner

/-- **`Q_{3,5}(1) = (1-q-u)e_1^2e_3 - e_1e_2^2 + …`**, the coprime slope the doubled slope
`(4,6)` is a commutator of.

`Split 3 5 = (2,3)`, so `HJO.Sym.Qop` reads `Q_{3,5} = M^{-1}[D_2, Q_{2,3}]`: the first branch is
`D_2(Q_{2,3}1)` and the second is `Q_{2,3}(D_2 1) = Q_{2,3}(e_2)`. Only 28 `(q,u)`-terms. -/
theorem qop_three_five_apply_one (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 3 5 (1 : Lambda L)
      = (1 - u - q) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
        + (-1 : L) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))
        + (-1 + 2 * u + 2 * q - q * u - u ^ 3 - q * u ^ 2 - q ^ 2 * u
            - q ^ 3) • (elemSymm L 1 * elemSymm L 4)
        + (1 - u ^ 2 - q * u - q ^ 2) • (elemSymm L 2 * elemSymm L 3)
        + (-u - q + u ^ 2 + 2 * q * u + q ^ 2 + u ^ 3 + q ^ 3 - u ^ 4 - q * u ^ 3 - q ^ 2 * u ^ 2
            - q ^ 3 * u - q ^ 4) • elemSymm L 5 := by
  have hQ := qop_of_coprime q u (m := 3) (n := 5) (by norm_num) (by decide)
  rw [show Split 3 5 = ((2 : ℕ), (3 : ℕ)) from by decide] at hQ
  norm_num only at hQ
  rw [hQ, LinearMap.smul_apply, inv_smul_eq_iff₀ hM]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, qop_one]
  have hd2 : Dop q u 2 (1 : Lambda L) = elemSymm L 2 := by rw [dop_apply_one]; ring
  rw [hd2, qop_two_three_apply_elemSymm_two hM, qop_two_three_apply_one hM]
  simp only [map_add, map_neg, map_smul]
  rw [dop_two_mono_12, dop_two_elemSymm_three]
  match_scalars <;> grobner

/-- **`Q_{3,5}(e_1)`**, the value the `(4,6)` commutator needs away from the vacuum.

`Q_{3,5} = M^{-1}[D_2, Q_{2,3}]` again: the first branch is `D_2(Q_{2,3}e_1)` off
`HJO.Sym.qop_two_three_apply_elemSymm_one`, the second `Q_{2,3}(D_2e_1)` with
`D_2e_1 = e_1e_2 - Me_3`, which is why both degree-three values above are needed. -/
theorem qop_three_five_apply_elemSymm_one (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 3 5 (elemSymm L 1)
      = (1 - u - q) • (elemSymm L 1 ^ 3 * elemSymm L 3)
        + (-1 : L) • (elemSymm L 1 ^ 2 * elemSymm L 2 ^ 2)
        + (-1 + u + q + u ^ 2 + 2 * q * u + q ^ 2 - 2 * q * u ^ 2 - 2 * q ^ 2 * u - u ^ 4
            - 2 * q * u ^ 3 - q ^ 2 * u ^ 2 - 2 * q ^ 3 * u - q ^ 4 + q * u ^ 4 + q ^ 2 * u ^ 3
            + q ^ 3 * u ^ 2 + q ^ 4 * u) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (3 * u + 3 * q - 2 * u ^ 2 - 5 * q * u - 2 * q ^ 2 - u ^ 3 - q ^ 3 + q * u ^ 3
            + q ^ 2 * u ^ 2 + q ^ 3 * u) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (1 - 2 * u - 2 * q - u ^ 2 - q ^ 2 + 2 * u ^ 3 + 5 * q * u ^ 2 + 5 * q ^ 2 * u
            + 2 * q ^ 3 + u ^ 4 - 2 * q ^ 2 * u ^ 2 + q ^ 4 - 3 * q * u ^ 4 - 3 * q ^ 2 * u ^ 3
            - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 4 * u - u ^ 6 - q * u ^ 5 - q ^ 5 * u - q ^ 6
            + q * u ^ 6 + q ^ 2 * u ^ 5 + q ^ 3 * u ^ 4 + q ^ 4 * u ^ 3 + q ^ 5 * u ^ 2
            + q ^ 6 * u) • (elemSymm L 1 * elemSymm L 5)
        + (1 - u - q + q * u) • elemSymm L 2 ^ 3
        + (-1 + 2 * u ^ 2 + q * u + 2 * q ^ 2 - u ^ 3 - q * u ^ 2 - q ^ 2 * u - q ^ 3 + u ^ 4
            + q * u ^ 3 - q ^ 2 * u ^ 2 + q ^ 3 * u + q ^ 4 - u ^ 5 - 2 * q * u ^ 4
            - q ^ 2 * u ^ 3 - q ^ 3 * u ^ 2 - 2 * q ^ 4 * u - q ^ 5 + q * u ^ 5 + q ^ 2 * u ^ 4
            + q ^ 3 * u ^ 3 + q ^ 4 * u ^ 2 + q ^ 5 * u) • (elemSymm L 2 * elemSymm L 4)
        + (-u - q + u ^ 2 + 3 * q * u + q ^ 2 + u ^ 3 - q * u ^ 2 - q ^ 2 * u + q ^ 3 - u ^ 4
            - 2 * q * u ^ 3 - q ^ 2 * u ^ 2 - 2 * q ^ 3 * u - q ^ 4 + q * u ^ 4 + q ^ 2 * u ^ 3
            + q ^ 3 * u ^ 2 + q ^ 4 * u) • elemSymm L 3 ^ 2
        + (u + q - u ^ 2 - 2 * q * u - q ^ 2 - u ^ 3 - q * u ^ 2 - q ^ 2 * u - q ^ 3
            + 2 * q * u ^ 3 + 4 * q ^ 2 * u ^ 2 + 2 * q ^ 3 * u + u ^ 5 + 2 * q * u ^ 4
            + 2 * q ^ 4 * u + q ^ 5 + u ^ 6 - q * u ^ 5 - 2 * q ^ 2 * u ^ 4 - q ^ 3 * u ^ 3
            - 2 * q ^ 4 * u ^ 2 - q ^ 5 * u + q ^ 6 - u ^ 7 - 2 * q * u ^ 6 - q ^ 2 * u ^ 5
            - q ^ 3 * u ^ 4 - q ^ 4 * u ^ 3 - q ^ 5 * u ^ 2 - 2 * q ^ 6 * u - q ^ 7 + q * u ^ 7
            + q ^ 2 * u ^ 6 + q ^ 3 * u ^ 5 + q ^ 4 * u ^ 4 + q ^ 5 * u ^ 3 + q ^ 6 * u ^ 2
            + q ^ 7 * u) • elemSymm L 6 := by
  have hQ := qop_of_coprime q u (m := 3) (n := 5) (by norm_num) (by decide)
  rw [show Split 3 5 = ((2 : ℕ), (3 : ℕ)) from by decide] at hQ
  norm_num only at hQ
  rw [hQ, LinearMap.smul_apply, inv_smul_eq_iff₀ hM]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, qop_one]
  rw [dop_two_elemSymm_one, qop_two_three_apply_elemSymm_one hM]
  simp only [map_add, map_sub, map_neg, map_smul]
  rw [show (elemSymm L 1 * elemSymm L 1 * elemSymm L 2 : Lambda L)
      = elemSymm L 1 * (elemSymm L 1 * elemSymm L 2) from mul_assoc _ _ _,
    dop_two_mono_112, dop_two_mono_22, dop_two_mono_13, dop_two_elemSymm_four,
    qop_two_three_apply_elemSymm_one_mul_two hM, qop_two_three_apply_elemSymm_three hM]
  match_scalars <;> grobner

/-- **`Q_{4,6}(1)`**, the second term of the `Λ` side: the *doubled*, non-coprime slope.

`HJO.Regression.qop_four_six` reads `HJO.Sym.Qop`'s non-coprime branch at multiplicity two:
`Q_{4,6} = M^{-1}[Q_{3,5}, Q_{1,1}] = M^{-1}[Q_{3,5}, D_1]`. At the vacuum `D_1(1) = -e_1`, so
the first branch is `-Q_{3,5}(e_1)` and the second is `D_1(Q_{3,5}1)`. -/
theorem qop_four_six_apply_one (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 4 6 (1 : Lambda L)
      = (-1 + u ^ 2 + q * u + q ^ 2) • (elemSymm L 1 ^ 3 * elemSymm L 3)
        + (1 + u + q) • (elemSymm L 1 ^ 2 * elemSymm L 2 ^ 2)
        + (1 - 2 * u ^ 2 - 3 * q * u - 2 * q ^ 2 - u ^ 3 - q ^ 3 + u ^ 4 + 2 * q * u ^ 3
            + 2 * q ^ 2 * u ^ 2 + 2 * q ^ 3 * u + q ^ 4 + u ^ 5 + q * u ^ 4 + q ^ 2 * u ^ 3
            + q ^ 3 * u ^ 2 + q ^ 4 * u + q ^ 5) • (elemSymm L 1 ^ 2 * elemSymm L 4)
        + (-3 * u - 3 * q - u ^ 2 + q * u - q ^ 2 + 3 * u ^ 3 + 4 * q * u ^ 2 + 4 * q ^ 2 * u
            + 3 * q ^ 3 + u ^ 4 + q * u ^ 3 + q ^ 2 * u ^ 2 + q ^ 3 * u
            + q ^ 4) • (elemSymm L 1 * elemSymm L 2 * elemSymm L 3)
        + (-1 + u + q + 3 * u ^ 2 + 3 * q * u + 3 * q ^ 2 - u ^ 3 - 4 * q * u ^ 2 - 4 * q ^ 2 * u
            - q ^ 3 - 3 * u ^ 4 - 4 * q * u ^ 3 - 4 * q ^ 2 * u ^ 2 - 4 * q ^ 3 * u - 3 * q ^ 4
            - u ^ 5 + q * u ^ 4 + 2 * q ^ 2 * u ^ 3 + 2 * q ^ 3 * u ^ 2 + q ^ 4 * u - q ^ 5
            + u ^ 6 + 2 * q * u ^ 5 + 2 * q ^ 2 * u ^ 4 + 2 * q ^ 3 * u ^ 3 + 2 * q ^ 4 * u ^ 2
            + 2 * q ^ 5 * u + q ^ 6 + u ^ 7 + q * u ^ 6 + q ^ 2 * u ^ 5 + q ^ 3 * u ^ 4
            + q ^ 4 * u ^ 3 + q ^ 5 * u ^ 2 + q ^ 6 * u + q ^ 7) • (elemSymm L 1 * elemSymm L 5)
        + (-1 + u ^ 2 + q * u + q ^ 2) • elemSymm L 2 ^ 3
        + (1 + u + q - 2 * u ^ 2 - 2 * q * u - 2 * q ^ 2 - u ^ 3 - 2 * q * u ^ 2 - 2 * q ^ 2 * u
            - q ^ 3 + q * u ^ 3 + 2 * q ^ 2 * u ^ 2 + q ^ 3 * u + q * u ^ 4 + q ^ 2 * u ^ 3
            + q ^ 3 * u ^ 2 + q ^ 4 * u + u ^ 6 + q * u ^ 5 + q ^ 2 * u ^ 4 + q ^ 3 * u ^ 3
            + q ^ 4 * u ^ 2 + q ^ 5 * u + q ^ 6) • (elemSymm L 2 * elemSymm L 4)
        + (u + q - 2 * q * u - 2 * u ^ 3 - q * u ^ 2 - q ^ 2 * u - 2 * q ^ 3 + q * u ^ 3
            + q ^ 2 * u ^ 2 + q ^ 3 * u + u ^ 5 + q * u ^ 4 + q ^ 2 * u ^ 3 + q ^ 3 * u ^ 2
            + q ^ 4 * u + q ^ 5) • elemSymm L 3 ^ 2
        + (-u - q + q * u + 2 * u ^ 3 + 3 * q * u ^ 2 + 3 * q ^ 2 * u + 2 * q ^ 3 + u ^ 4
            - q * u ^ 3 - 2 * q ^ 2 * u ^ 2 - q ^ 3 * u + q ^ 4 - u ^ 5 - 3 * q * u ^ 4
            - 3 * q ^ 2 * u ^ 3 - 3 * q ^ 3 * u ^ 2 - 3 * q ^ 4 * u - q ^ 5 - 2 * u ^ 6
            - q * u ^ 5 - q ^ 5 * u - 2 * q ^ 6 + q * u ^ 6 + q ^ 2 * u ^ 5 + q ^ 3 * u ^ 4
            + q ^ 4 * u ^ 3 + q ^ 5 * u ^ 2 + q ^ 6 * u + u ^ 8 + q * u ^ 7 + q ^ 2 * u ^ 6
            + q ^ 3 * u ^ 5 + q ^ 4 * u ^ 4 + q ^ 5 * u ^ 3 + q ^ 6 * u ^ 2 + q ^ 7 * u
            + q ^ 8) • elemSymm L 6 := by
  have hQ := Regression.qop_four_six (L := L) q u
  have hd1 : Dop q u 1 (1 : Lambda L) = -elemSymm L 1 := by rw [dop_apply_one]; ring
  rw [hQ, LinearMap.smul_apply, inv_smul_eq_iff₀ hM]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, qop_one]
  rw [hd1, map_neg, qop_three_five_apply_elemSymm_one hM, qop_three_five_apply_one hM]
  simp only [map_add, map_smul]
  rw [dop_one_mono_113, dop_one_mono_122, dop_one_mono_14, dop_one_mono_23,
    dop_one_elemSymm_five]
  match_scalars <;> grobner
end HJO.Sym

namespace HJO.Mellit

open HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The two sides agree: the `Λ`-level clause at `α = (1,1)`, `(a,b) = (2,3)` -/

/-- **The two-part clause at `(a,b) = (2,3)`, `α = (1,1)`, proved in `Λ`.**

`(u+1)·Q_{2,3}(Q_{2,3}1) + u(q-1)·Q_{4,6}(1) = (qu+1)·ct(d_-^2G_{2,1}G_{1,1}(1))`.

This is exactly the identity `HJO.Mellit.qop_double_apply_one_of_lhsWord` extracts from
`HJO.Mellit.LhsWord` at `(a,b) = (2,3)` and the two-part composition — now proved outright rather
than assumed. The `Λ` side is `HJO.Sym.qop_two_three_apply_qop_two_three_apply_one` and
`HJO.Sym.qop_four_six_apply_one`; the sweep side is
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three_eval`.

Both sides are combinations of the same nine degree-six `e`-monomials and every coefficient
matches; at `(q,u) = (2,3)` the nine values are `14, 14, 14, 280, 266, 1428, 616, 336, 1848`. -/
@[hjo "lem_mellit_lhs_two_three_two_part"]
theorem qop_double_apply_one_two_three (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    (u + 1) • Qop q u 2 3 (Qop q u 2 3 (1 : Lambda L))
        + (u * (q - 1)) • Qop q u 4 6 (1 : Lambda L)
      = (q * u + 1) •
          MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u 2 3 [1, 1])) := by
  rw [qop_two_three_apply_qop_two_three_apply_one hM, qop_four_six_apply_one hM,
    constantCoeff_lowerRun_two_stageWordTotal_two_three_eval hq0 hu0 hq1]
  match_scalars <;> grobner

/-- **The identity above is not `0 = 0`.** Its common value has `e_2^3`-coefficient
`(qu+1)(q^2-q)`, so it is nonzero whenever `q ∉ {0,1}` and `qu ≠ -1`.

This is the check the inverse-becomes-zero hazard demands: in a field `0⁻¹ = 0`, so an agreement
between two expressions that both degenerate at the parameters in play is no agreement at all. Here
the two sides agree at *generic* parameters and their common value is nonzero there; `qu = -1` is
exactly where it does vanish, and `HJO.Mellit.lhsAt_two_three_one_one` excludes it. -/
@[hjo "lem_mellit_lhs_two_three_two_part"]
theorem qop_double_apply_one_two_three_ne_zero (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0)
    (hu0 : u ≠ 0) (hq1 : q ≠ 1) (hvm : q * u + 1 ≠ 0) :
    (u + 1) • Qop q u 2 3 (Qop q u 2 3 (1 : Lambda L))
        + (u * (q - 1)) • Qop q u 4 6 (1 : Lambda L) ≠ 0 := by
  rw [qop_double_apply_one_two_three hM hq0 hu0 hq1,
    constantCoeff_lowerRun_two_stageWordTotal_two_three_eval hq0 hu0 hq1]
  have hc : (q * u + 1) * (-q + q ^ 2) ≠ 0 := by
    refine mul_ne_zero hvm ?_
    rw [show -q + q ^ 2 = q * (q - 1) from by ring]
    exact mul_ne_zero hq0 (sub_ne_zero.mpr hq1)
  intro h
  refine elemSymm_deg_six_ne_zero (L := L) ((q * u + 1) * q) ((q * u + 1) * (-q + q ^ 2))
    ((q * u + 1) * (q - q * u - q ^ 2 - q ^ 3 + q ^ 3 * u + q ^ 5))
    ((q * u + 1) * (q * u - 3 * q ^ 2 + q ^ 2 * u + 2 * q ^ 3 + q ^ 4))
    ((q * u + 1) * (-q + q * u + 2 * q ^ 2 - q ^ 2 * u - q ^ 2 * u ^ 2 + q ^ 3 - 2 * q ^ 3 * u
      + q ^ 3 * u ^ 2 - 2 * q ^ 4 + q ^ 4 * u - q ^ 5 + q ^ 5 * u + q ^ 7))
    ((q * u + 1) * (q - q * u ^ 2 - q ^ 2 * u + q ^ 2 * u ^ 2 - 2 * q ^ 3 + q ^ 4 + q ^ 4 * u
      - q ^ 5 + q ^ 6))
    ((q * u + 1) * (-q * u + q * u ^ 2 + q ^ 2 - q ^ 3 + q ^ 3 * u - q ^ 4 + q ^ 5))
    ((q * u + 1) * (-q ^ 2 + q ^ 2 * u + q ^ 3 - q ^ 3 * u ^ 2 + q ^ 4 - 2 * q ^ 4 * u
      + q ^ 4 * u ^ 2 - q ^ 6 + q ^ 6 * u - q ^ 7 + q ^ 8)) hc ?_
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_sub, map_neg, map_mul, map_one, map_pow,
    map_ofNat] at h ⊢
  linear_combination h

/-- **The clause of `HJO.Mellit.lhsRewrite_sweepWitness` at `(a,b) = (2,3)` and the composition
`(1,1)`, for every slope homomorphism there may be.**

`HJO.Mellit.theta_copComp_one_one` turns `(qu+1)·Θ(C_1C_1(1))` into
`(u+1)·Q_{2,3}² + u(q-1)·Q_{4,6}`, and `HJO.Mellit.qop_double_apply_one_two_three` evaluates that
at the vacuum as `(qu+1)` times the sweep side; dividing by `qu+1` gives the clause.

## Genericity, and which exclusions are real

`q ≠ 1` and `u ≠ 1` are `M = (1-q)(1-u) ≠ 0`, the normalisation of `HJO.Sym.Qop`. `u ≠ 1` is **not**
decoration: `HJO.Mellit.not_lhsWord_two_three_of_slopeHom_u_one` refutes this very clause at
`u = 1`, where both slope operators are the zero map and the sweep side is not zero. `q ≠ 0` and
`u ≠ 0` are the `(qu)^{-1}` of `HJO.Sweep.slopeOperator`, and `q ≠ 1` is also the `(1-q)^{-1}` of
`HJO.Sweep.zop`. `qu ≠ 1` is `HJO.Sym.axisGen_one`'s. `qu + 1 ≠ 0` is the one hypothesis that is an
artefact of the *route*: at `qu = -1` the identity above still holds — with both sides zero — but
`HJO.Mellit.theta_copComp_one_one` then says nothing about `Θ`, because `e_2` is not in the span of
`U_1^2` and `U_2` there.

## What is not proved here

This is **one** composition at **one** slope. `HJO.Mellit.LhsWord q u 2 3` quantifies over every
composition, and `HJO.Mellit.LhsComputes`' family over every coprime `1 < a < b`; the `hlhs` binder
of `HJO.Mellit.shuffle_of_lhs_and_induction` is *not* discharged by this, nor is `hind`. -/
@[hjo "lem_mellit_lhs_two_three_two_part"]
theorem lhsAt_two_three_one_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (hu1 : u ≠ 1)
    (hv1 : q * u ≠ 1) (hvm : q * u + 1 ≠ 0)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) :
    LhsAt q u 2 3 Θ [1, 1] := by
  have hM : (1 - q) * (1 - u) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm hq1)) (sub_ne_zero.mpr (Ne.symm hu1))
  have hv0 : q * u ≠ 0 := mul_ne_zero hq0 hu0
  have hop := theta_copComp_one_one hv0 hv1 hΘ
  have h := congrArg (fun T : Module.End L (Lambda L) => T (1 : Lambda L)) hop
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply] at h
  rw [show (2 * 2 : ℕ) = 4 from rfl, show (3 * 2 : ℕ) = 6 from rfl,
    qop_double_apply_one_two_three hM hq0 hu0 hq1] at h
  have hcore : Θ (CopComp q [1, 1] (1 : Lambda L)) 1
      = MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u 2 3 [1, 1])) := by
    have h2 := congrArg (fun z : Lambda L => (q * u + 1)⁻¹ • z) h
    simpa only [inv_smul_smul₀ hvm] using h2
  rw [LhsAt]
  norm_num
  exact hcore

end HJO.Mellit

end
