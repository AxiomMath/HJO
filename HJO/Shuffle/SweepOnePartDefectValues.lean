/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepOnePartDefectTable

/-! # The two defects of the one-part sweep step, evaluated

`HJO/Shuffle/SweepOnePartLambdaStep.lean` reduced the whole one-part `hlhs` family at
`(a,b) = (2,3)` to one hypothesis about the creation side, whose right-hand side names two elements
of `Λ` that nothing evaluated:

  `V_{A+2} = cγ·D_1(D_2(V_{A+1})) + cγ·D_1(Δ²_{A+1}) + c·Δ¹_{A+1}`,
  `c = (qu)^{-1}q/(1-q)`, `γ = q/(1-q)`,

with `Δ²_A = HJO.Mellit.onePartDefectTwo q u A = ∑_m T_{2,m}((G_A)_m)` and
`Δ¹_A = HJO.Mellit.onePartDefectOne q u A = ∑_j T_{1,j}((y_1^2z_1G_A)_j)`, the sums of
`HJO.Sweep.twistDop` over the `y_1`-monomials of the one-part stage word and of the replicated
letter's intermediate vector. **This file evaluates them.** Nothing here is an equivalence except
the one place it is labelled as a negative finding.

The supporting values — the Hall--Littlewood table, the Pieri rules at `e_3` and `e_4`,
`HJO.Sweep.twistProj`, and the values `T_{1,m}` and `T_{2,m}` the defects read — are in
`HJO/Shuffle/SweepOnePartDefectTable.lean`. This file assembles the defects.

## The engine: `T_{l,m}` is a `B`-word against a graded displacement

`HJO.Sweep.twistDop q u l m g = ct(d_-^{(1)}(y_1^l·B_m(d^*_+{}^{(0)}(Cg))))` is a function of the
*displaced* argument alone, so `HJO.Sweep.twistProj` names that function and

  `HJO.Sweep.twistProj_smul_auxVar_pow_mul_C`:  `y_1^jCf ↦ B_{l+j}(B_mf)`

evaluates it on one graded term. Hence **`T_{l,m}(g) = ∑_j x_j·B_{l+j}(B_m f_j)` whenever
`d^*_+{}^{(0)}(Cg) = ∑_j x_j·y_1^jCf_j`** — two Hall--Littlewood operators against the graded
displacement, and no `d_-`, no `bopExt` and no train left. Both inputs are already available: the
graded `d^*_+` rows of `HJO/Shuffle/ZDefectEBasisTable.lean` cover every `e`-monomial of weight
at most four, which is exactly what the stage word carries at `[1]` and `[2]`, and the Pieri rules
`HJO.Sym.bop_elemSymm_one_mul`, `bop_elemSymm_two_mul` hold at every index. What this file adds on
that side is the Pieri rules at `e_3` and `e_4` (`HJO.Sym.bop_elemSymm_three_mul`,
`bop_elemSymm_four_mul`, the same unfolding of `HJO.Sym.dop_elemSymm_mul` at `u = 0`), the base rows
`B_k(e_n)` the two defects reach, and `HJO.Bglx.paramPleth_elemSymm_six_eq`.

The defect sums are read monomial by monomial by `HJO.Sweep.sum_twistDop_add` — additivity, proved
over the union of the supports, `HJO.Sweep.twistDop_zero` killing what falls outside — with
`HJO.Sweep.sum_twistDop_smul_auxVar_pow_mul_C` at each term.

## The four values

* **`HJO.Mellit.onePartDefectTwo_one`**: `Δ²_1`, five `e`-monomials of degree five.
* **`HJO.Mellit.onePartDefectOne_one`**: `Δ¹_1`, nine `e`-monomials of degree six.
* **`HJO.Mellit.onePartDefectTwo_two`**: `Δ²_2`, **eighteen `e`-monomials of degree eight** — the
  eleven monomials of `HJO.Mellit.stageWordTotal_two_three_two_eq`, each through its own
  `HJO.Sweep.twistDop` value (`HJO.Sweep.twistDop_two_two_elemSymm_four` and its ten companions).
* **`HJO.Mellit.onePartInnerValue_one`**: `w_1 = ct(d_-^{(1)}(y_1^2z_1G_1))`, four monomials of
  degree five.

## The general structure the computation exposes, at every `A`

Both defects are **values of one earlier evaluation**, with no `HJO.Sweep.twistDop` on the right:

* `HJO.Mellit.smul_onePartDefectTwo_eq` / `HJO.Mellit.onePartDefectTwo_eq`:
  `Δ²_A = -D_2(V_A) - ((1-q)/q)·w_A`, `w_A = HJO.Mellit.onePartInnerValue q u A`;
* `HJO.Mellit.smul_onePartDefectOne_eq` / `HJO.Mellit.onePartDefectOne_eq`:
  `Δ¹_A = D_1(w_A) - ((1-q)/q)·x_A`, `x_A = HJO.Mellit.onePartOuterValue q u A`.

Both come from one lemma, `HJO.Sweep.smul_sum_twistDop_of_mem_piece`, which solves
`HJO.Sweep.constantCoeff_dminus_one_auxVar_pow_mul_zopOneStar_one_of_mem_piece` for the defect sum.

**Substituting them back into the step makes it collapse.** `q^2·D_1(D_2(V_{A+1}))` cancels term by
term against the inner defect's `-D_2(V_{A+1})`, and `q(1-q)·D_1(w_{A+1})` cancels between the two
defects, leaving `HJO.Mellit.smul_onePartSweepValue_succ_of_defect`:

  `qu(1-q)^2·V_{A+2} = -(1-q)^2·x_{A+1}`,

which `HJO.Mellit.smul_onePartSweepValue_succ_of_letter` proves straight from
`HJO.Sweep.replicatedTotal_two_three_zero_apply` with no defect in it. **So the `D_1D_2` of the step
— the "value-only part" — is not a step towards anything: it is cancelled by the defect that
accompanies it, and the recursion is the replicated letter and nothing more.**

## What is NOT proved, with the quantifier named

* **No instance of the `hlhs` clause is proved here, at any `A`.** Nothing in this file touches the
  creation side except `HJO.Mellit.creation_step_iff_lhsAt_succ`, a negative result (below).
* **`Δ¹_2` is NOT evaluated.** `HJO.Mellit.onePartDefectOne_eq` at `A = 2` states its obligation
  exactly: it is `D_1(w_2) - ((1-q)/q)·x_2` with `w_2 = HJO.Mellit.onePartInnerValue q u 2` and
  `x_2 = HJO.Mellit.onePartOuterValue q u 2`, **and neither is evaluated at `A = 2`**. Both need
  `z_1(G_2)`, one further `z_1` on the eleven-monomial `G_2` — a computation this file does not do.
  `w_1` and `x_1` are evaluated (`HJO.Mellit.onePartInnerValue_one`; `x_1` through
  `HJO.Sweep.zopOneStar_one_auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_one`), `w_A` and
  `x_A` at **no** `A ≥ 2`.
* **`V_3` is not computed and `A = 3` is not decided.** By
  `HJO.Mellit.smul_onePartSweepValue_succ_of_letter`, `V_3` is `-(qu)^{-1}x_2`, so it is the same
  missing `z_1(G_2)` and the two defects at `A = 2` do not shorten the route to it.
* **No defect is shown to be nonzero as an element of `Λ`**, and nothing here says the clause is
  false anywhere: no two evaluated values are compared.
* No closed form in `A` is claimed for either defect. `Δ²_A` has `5` monomials at `A = 1` and
  `18` at `A = 2`, with `q`-degrees `4` and `14`; there is no formula in the general closed forms
  above beyond the one-`z_1`-step recursion they encode.

## The negative finding: the step hypothesis is not weaker than the clause

`HJO.Mellit.creation_step_iff_lhsAt_succ`: **given the clause at `[A+1]`, the `hstep` hypothesis of
`HJO.Mellit.forall_lhsAt_two_three_singleton_succ_of_creation` at `A` is equivalent to the clause at
`[A+2]`.** `HJO.Mellit.lhsAt_two_three_singleton_iff_onePartSweepValue` turns the clause at `[A+1]`
into `Θ(h_{A+1})(1) = V_{A+1}`, and then `HJO.Mellit.onePartSweepValue_succ` says `hstep`'s
right-hand side *is* `V_{A+2}`. So the one-part reduction is the induction restated: it discharges
the sweep side, which is real, but it does not weaken the obligation on the creation side. This is
recorded rather than softened.

## Consistency checks

1. **`HJO.Mellit.smul_onePartSweepValue_two_of_step` vs `..._of_value`, the same `Prop` by `rfl` at
   `..._eq`:** `qu(1-q)^2·V_2 = q^2D_1(D_2(V_1)) + q^2D_1(Δ²_1) + q(1-q)·Δ¹_1`. The first proves it
   from `HJO.Mellit.onePartSweepValue_succ` with no value in it; the second from the values `V_1`
   and `V_2` — `HJO.Mellit.dminus_one_stageWordTotal_two_three_one_eq` and
   `HJO.Mellit.dminus_one_stageWordTotal_two_three_two`, routes with no `HJO.Sweep.twistDop` and no
   graded `d^*_+` anywhere in them — and the two evaluated defects. Both
   defects enter at degree six over all eleven `e`-monomials, so a dropped term, a misread
   Hall--Littlewood index or a lost sign in either would separate the two sides.
2. **`HJO.Mellit.onePartDefectTwo_one` vs `..._one_of_value`, the same `Prop` by `rfl` at
   `..._one_eq`:** `Δ²_1` through the `d^*_+`-expansion machinery, against `Δ²_1` through the closed
   form `-D_2(V_1) - ((1-q)/q)w_1` — which reads the evaluated `z_1` value and the `HJO.Sym.DopInt`
   table and contains no `HJO.Sweep.twistProj`. This is the check on the machinery that
   `HJO.Mellit.onePartDefectTwo_two` runs on, one degree lower.
3. **`HJO.Mellit.smul_onePartSweepValue_succ_of_defect` vs `..._of_letter`, the same `Prop` by `rfl`
   at `..._eq`, at every `A`:** the two closed forms substituted into the step against the
   replicated letter's own definition. A sign or a scalar wrong in either closed form leaves a
   residual term.

`HJO.Mellit.onePartDefectTwo_two` itself has **one** route in Lean; what stands behind it is check 2
on the same machinery at `A = 1` and check 1 on the assembly.

## Genericity

`q ≠ 0`, `u ≠ 0`, `q ≠ 1` are the hazards of discipline: `(qu)^{-1}` of
`HJO.Sweep.slopeOperator` and `q/(1-q)` of `HJO.Sweep.zop` are the zero map at those parameters,
which would make a clause false rather than vacuous.

* **Unconditional**: everything in `HJO.Sym` and `HJO.Bglx` here; every `HJO.Sweep` declaration,
  `HJO.Sweep.twistProj` and its lemmas, `HJO.Sweep.sum_twistDop_add`,
  `HJO.Sweep.smul_sum_twistDop_of_mem_piece` (`γ` is carried on the left and never inverted, so at
  `q ∈ {0,1}` both sides are `0`) and all sixteen `HJO.Sweep.twistDop` values; and
  `HJO.Mellit.onePartOuterValue_eq`, `smul_onePartDefectTwo_eq`, `smul_onePartDefectOne_eq`.
* `q ≠ 0`, `q ≠ 1` only: `HJO.Mellit.onePartDefectTwo_eq`, `onePartDefectOne_eq` — spent on
  dividing by `γ`, and on nothing else.
* `q ≠ 0`, `u ≠ 0`, `q ≠ 1`: the four evaluated values and the two evaluated sweep values, every one
  of them inherited from `HJO.Sweep.stageTotal_two_three_zero_one_one`, the seed
  `-e_1y_1^2 + uy_1^3`; and `HJO.Mellit.creation_step_iff_lhsAt_succ`, verbatim
  `HJO.Mellit.lhsAt_two_three_singleton_iff_onePartSweepValue`'s. The checks add `u ≠ 0` where the
  `(qu)^{-1}` of the step is cleared. **No declaration in this file needs `M = (1-q)(1-u) ≠ 0`**:
  the `e`-basis route to `V_1` avoids `HJO.Sym.Qop`'s `M^{-1}`, which
  `HJO.Mellit.onePartSweepValue_one` does not.

`(2,3)` is coprime with `1 < a < b`, the range the `hlhs` binder quantifies over.

## What the results are

These are values of `HJO.Sym.DopInt`, `HJO.Sym.Bop`, `HJO.Sweep.bopExt`,
`HJO.Sweep.dplusStar`, `HJO.Sweep.zop` and `HJO.Mellit.replicatedLetter`, and a reduction of the
`hlhs` clause rather than an instance of it.

## References

This file concerns `HJO.Mellit.lhsRewrite_sweepWitness`, using `HJO.Mellit.stage`,
`HJO.Mellit.replicatedLetter`, `HJO.Sweep.zop`, `HJO.Sweep.slopeOperator`, `HJO.Sym.Bop`,
`HJO.Sweep.bopExt`, `HJO.Sweep.dplusStar`, `HJO.Sweep.dminus`, `HJO.Sym.DopInt`, `HJO.Sym.Qop`,
`HJO.Sym.elemSymm`, `HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` and
`HJO.Bglx.paramPleth_elemSymm_zero`.
-/

set_option linter.unusedSimpArgs false

@[expose] public section

-- Every exponent written as a numeral in this file is a natural number. Saying so up front lets
-- each `x ^ n` resolve `HPow _ ℕ _` at once instead of retrying instance resolution for the
-- pending numeral type until defaulting, which dominated elaboration here. The elaborated terms
-- are the ones the default instance would produce.
local macro_rules | `($x ^ $n:num) => `(rightact% HPow.hPow $x ($n : ℕ))

namespace HJO.Mellit

open Finset HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The single vector both defects read -/

/-- **`w_A = ct(d_-^{(1)}(y_1^2z_1G_A))`**, the projection of the intermediate vector
`H_A = y_1^2z_1G_A` of the replicated letter. `HJO.Mellit.smul_onePartDefectTwo_eq` and
`HJO.Mellit.smul_onePartDefectOne_eq` express **both** defects of the one-part step through this one
element of `Λ` and the value `V_A`, at every `A`. -/
noncomputable def onePartInnerValue (q u : L) (A : ℕ) : Lambda L :=
  MvPolynomial.constantCoeff (dminus q 1 ((auxVar 1 : Total L) ^ 2 *
    zopOneStar q u 1 (stageWordTotal q u 2 3 [A])))

/-- **`x_A = ct(d_-^{(1)}(y_1z_1(y_1^2z_1G_A)))`**, the same projection one `z_1` further out — the
whole replicated letter of `HJO.Mellit.replicatedLetter` bar its scalar `(qu)^{-1}`, so
`HJO.Mellit.onePartSweepValue_succ_eq_outer` reads `V_{A+2} = -(qu)^{-1}x_{A+1}`. This is the one
datum the outer defect still carries. -/
noncomputable def onePartOuterValue (q u : L) (A : ℕ) : Lambda L :=
  MvPolynomial.constantCoeff (dminus q 1 ((auxVar 1 : Total L) ^ 1 *
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2 *
      zopOneStar q u 1 (stageWordTotal q u 2 3 [A]))))

/-- `HJO.Mellit.onePartOuterValue` with the outer letter's single power of `y_1` written without the
exponent, the shape `HJO.Sweep.replicatedTotal_two_three_zero_apply` is in. -/
theorem onePartOuterValue_eq (q u : L) (A : ℕ) :
    onePartOuterValue q u A
      = MvPolynomial.constantCoeff (dminus q 1 ((auxVar 1 : Total L) *
          zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2 *
            zopOneStar q u 1 (stageWordTotal q u 2 3 [A])))) := by
  rw [onePartOuterValue, pow_one]

/-- **THE INNER DEFECT AT EVERY `A`, AS A VALUE:** `γ·Δ²_A = -γ·D_2(V_A) - w_A`, `γ = q/(1-q)`.

`HJO.Sweep.smul_sum_twistDop_of_mem_piece` at `l = 2` and `F = G_A` — the membership being
`HJO.Mellit.stageWordTotal_singleton_mem_piece` — with
`HJO.Mellit.onePartSweepValue_eq_neg_constantCoeff` for the sign. **No `HJO.Sweep.twistDop` is left
on the right**: the inner defect is a function of the value `V_A` and of
`HJO.Mellit.onePartInnerValue` alone.

`γ` is never inverted, so this is unconditional: at `q = 0` and `q = 1` it reads `0 = 0`. -/
theorem smul_onePartDefectTwo_eq (q u : L) (A : ℕ) :
    (q / (1 - q)) • onePartDefectTwo q u A
      = -((q / (1 - q)) • Dop q u 2 (onePartSweepValue q u A)) - onePartInnerValue q u A := by
  rw [onePartDefectTwo, onePartInnerValue, smul_sum_twistDop_of_mem_piece q u 2
      (stageWordTotal_singleton_mem_piece q u 2 3 A),
    onePartSweepValue_eq_neg_constantCoeff q u A, map_neg, smul_neg, neg_neg]

/-- **THE INNER DEFECT, SOLVED FOR:** `Δ²_A = -D_2(V_A) - ((1-q)/q)·w_A`, at every `A`.

`HJO.Mellit.smul_onePartDefectTwo_eq` divided by `γ = q/(1-q)`, which is exactly where `q ≠ 0` and
`q ≠ 1` are spent and nowhere else: at either value the scalar is `0` and the equation above
determines nothing. This is the closed form of `HJO.Mellit.onePartDefectTwo`, and with
`HJO.Mellit.onePartSweepValue_succ` it says the `D_1D_2` term of the step **cancels identically**
against the inner defect, leaving the step a function of `w_{A+1}` and `Δ¹_{A+1}`. -/
theorem onePartDefectTwo_eq (hq0 : q ≠ 0) (hq1 : q ≠ 1) (A : ℕ) :
    onePartDefectTwo q u A
      = -Dop q u 2 (onePartSweepValue q u A) - ((1 - q) / q) • onePartInnerValue q u A := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  refine smul_right_injective (Lambda L) (div_ne_zero hq0 h1q) ?_
  dsimp only
  rw [smul_onePartDefectTwo_eq, smul_sub, smul_neg, smul_smul,
    show (q / (1 - q)) * ((1 - q) / q) = 1 from by field_simp, one_smul]

/-- **THE OUTER DEFECT AT EVERY `A`, AS A VALUE:**
`γ·Δ¹_A = γ·D_1(w_A) - ct(d_-^{(1)}(y_1z_1H_A))`, `H_A = y_1^2z_1G_A`.

`HJO.Sweep.smul_sum_twistDop_of_mem_piece` at `l = 1` and `F = H_A`, the membership being
`HJO.Sweep.auxVar_sq_mul_zopOneStar_one_mem_piece`. Unconditional.

The subtracted term is the outer `z_1` of the replicated letter read one step further in than
`HJO.Mellit.onePartInnerValue`; it is **not** eliminated here, and it is where the whole remaining
content of the one-part recursion sits. -/
theorem smul_onePartDefectOne_eq (q u : L) (A : ℕ) :
    (q / (1 - q)) • onePartDefectOne q u A
      = (q / (1 - q)) • Dop q u 1 (onePartInnerValue q u A) - onePartOuterValue q u A := by
  rw [onePartDefectOne, onePartInnerValue, onePartOuterValue, smul_sum_twistDop_of_mem_piece q u 1
    (auxVar_sq_mul_zopOneStar_one_mem_piece q u (stageWordTotal_singleton_mem_piece q u 2 3 A))]

/-- **THE OUTER DEFECT, SOLVED FOR:** `Δ¹_A = D_1(w_A) - ((1-q)/q)·x_A`, at every `A`.
`HJO.Mellit.smul_onePartDefectOne_eq` divided by `γ`, which is the only place `q ≠ 0` and `q ≠ 1`
are spent. -/
theorem onePartDefectOne_eq (hq0 : q ≠ 0) (hq1 : q ≠ 1) (A : ℕ) :
    onePartDefectOne q u A
      = Dop q u 1 (onePartInnerValue q u A) - ((1 - q) / q) • onePartOuterValue q u A := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  refine smul_right_injective (Lambda L) (div_ne_zero hq0 h1q) ?_
  dsimp only
  rw [smul_onePartDefectOne_eq, smul_sub, smul_smul,
    show (q / (1 - q)) * ((1 - q) / q) = 1 from by field_simp, one_smul]

/-! ### The two defects at `[1]`, evaluated -/

/-- **`Δ²_1 = ∑_m T_{2,m}((G_1)_m) = -T_{2,2}(e_1) + u·T_{2,3}(1)`, written out.**

The one-part stage word at `[1]` is `-e_1y_1^2 + uy_1^3`
(`HJO.Mellit.stageWordTotal_two_three_one_expand`), two monomials, so the defect sum has two terms
and `HJO.Sweep.sum_twistDop_add` with `HJO.Sweep.sum_twistDop_smul_auxVar_pow_mul_C` reads them off.
Homogeneous of degree `5`, as `D_2` on the degree-three `V_1` must be.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, all three the seed's own
(`HJO.Sweep.stageTotal_two_three_zero_one_one`); nothing of this evaluation's. -/
theorem onePartDefectTwo_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    onePartDefectTwo q u 1
      = (-q ^ 4 + q ^ 3 - q ^ 2 * u + q ^ 2 + q * u - q) • elemSymm L 5
        + (-q ^ 3 - q * u + 2 * q + u - 1) • (elemSymm L 1 * elemSymm L 4)
        + (-q ^ 2 - u + 1) • (elemSymm L 2 * elemSymm L 3)
        + (1 - q) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
        + (-1 : L) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)) := by
  rw [onePartDefectTwo, stageWordTotal_two_three_one_expand hq0 hu0 hq1, sum_twistDop_add,
    sum_twistDop_smul_auxVar_pow_mul_C, sum_twistDop_smul_auxVar_pow_mul_C,
    twistDop_two_two_elemSymm_one, twistDop_two_three_one]
  module

/-- **`Δ¹_1 = ∑_j T_{1,j}((y_1^2z_1G_1)_j)`, written out.**

`HJO.Sweep.auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_one` is the intermediate vector
`H_1 = y_1^2z_1G_1` as four monomials over the `y_1`-degrees `3, 4, 5`, so the outer defect is
`(qu^2+q^2u-qu)T_{1,3}(e_2) + qu·T_{1,3}(e_1^2) - (qu^3+qu^2)T_{1,4}(e_1) + qu^4·T_{1,5}(1)`.
Homogeneous of degree `6`, and every coefficient is divisible by `qu` — the `u` of the seed and the
`q` of the inner `z_1`.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, the intermediate vector's own. -/
theorem onePartDefectOne_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    onePartDefectOne q u 1
      = (q ^ 9 * u - q ^ 8 * u + q ^ 7 * u ^ 2 - q ^ 7 * u + q ^ 5 * u ^ 3 - 2 * q ^ 5 * u ^ 2
            + q ^ 5 * u + q ^ 4 * u ^ 4 - 2 * q ^ 4 * u ^ 3 + q ^ 4 * u - q ^ 3 * u ^ 4
            + q ^ 3 * u ^ 3 + q ^ 3 * u ^ 2 - q ^ 3 * u) • elemSymm L 6
        + (q ^ 8 * u + q ^ 6 * u ^ 2 - q ^ 6 * u + q ^ 5 * u ^ 2 - 2 * q ^ 5 * u
            + 2 * q ^ 4 * u ^ 3 - 3 * q ^ 4 * u ^ 2 + 2 * q ^ 4 * u + q ^ 3 * u ^ 4
            - 3 * q ^ 3 * u ^ 3 + q ^ 3 * u ^ 2 + q ^ 3 * u - q ^ 2 * u ^ 4 + 2 * q ^ 2 * u ^ 3
            + q ^ 2 * u ^ 2 - 2 * q ^ 2 * u + q * u ^ 4 - q * u ^ 3 - q * u ^ 2 + q * u)
            • (elemSymm L 1 * elemSymm L 5)
        + (q ^ 7 * u - q ^ 6 * u + q ^ 5 * u ^ 2 + q ^ 5 * u + q ^ 4 * u ^ 2 - 3 * q ^ 4 * u
            + q ^ 3 * u ^ 3 - 2 * q ^ 3 * u ^ 2 + q ^ 3 * u + q ^ 2 * u ^ 4 - 2 * q ^ 2 * u ^ 3
            - q ^ 2 * u ^ 2 + 2 * q ^ 2 * u - q * u ^ 4 + q * u ^ 3 + q * u ^ 2 - q * u)
            • (elemSymm L 2 * elemSymm L 4)
        + (q ^ 6 * u - q ^ 5 * u + q ^ 4 * u ^ 2 - q ^ 4 * u - q ^ 3 * u ^ 2 + q ^ 3 * u)
            • (elemSymm L 3 * elemSymm L 3)
        + (q ^ 6 * u + q ^ 4 * u ^ 2 - q ^ 4 * u + q ^ 3 * u ^ 3 - q ^ 3 * u ^ 2 - q ^ 2 * u ^ 3
            + q ^ 2 * u ^ 2 + q ^ 2 * u + q * u ^ 3 - q * u)
            • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (q ^ 5 * u + 2 * q ^ 4 * u + 2 * q ^ 3 * u ^ 2 - 4 * q ^ 3 * u + q ^ 2 * u ^ 3
            - 2 * q ^ 2 * u ^ 2 + q ^ 2 * u - q * u ^ 3 + q * u ^ 2)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))
        + (q ^ 3 * u + q ^ 2 * u ^ 2 - 2 * q ^ 2 * u - q * u ^ 2 + q * u)
            • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))
        + (q ^ 3 * u - q ^ 2 * u + q * u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (q ^ 2 * u - q * u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))) := by
  rw [onePartDefectOne, auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_one hq0 hu0 hq1,
    sum_twistDop_add, sum_twistDop_add, sum_twistDop_add, sum_twistDop_smul_auxVar_pow_mul_C,
    sum_twistDop_smul_auxVar_pow_mul_C, sum_twistDop_smul_auxVar_pow_mul_C,
    sum_twistDop_smul_auxVar_pow_mul_C, twistDop_one_three_elemSymm_two,
    twistDop_one_three_elemSymm_one_sq, twistDop_one_four_elemSymm_one, twistDop_one_five_one]
  module

/-! ### The inner defect at `[2]`, evaluated -/

set_option maxHeartbeats 400000 in
-- A size, not a loop: the closing normalisation of this value needs more than half the
-- default budget, so it is given twice the default to stay clear of it.
/-- **`Δ²_2 = ∑_m T_{2,m}((G_2)_m)`, written out: eighteen `e`-monomials of degree eight.**

`HJO.Mellit.stageWordTotal_two_three_two_eq` is `G_2` as eleven monomials over the `y_1`-degrees
`2` to `6`, so `HJO.Sweep.sum_twistDop_add` and `HJO.Sweep.sum_twistDop_smul_auxVar_pow_mul_C` turn
the defect into eleven values of `HJO.Sweep.twistDop` at `l = 2`. Each is evaluated by
`HJO.Sweep.twistProj_smul_auxVar_pow_mul_C` against the graded displacement of its coefficient —
the eleven rows `HJO.Sweep.dplusStar_C_one`, `dplusStar_C_elemSymm_one_expand`, `_two_expand`,
`_one_sq_expand`, `_three_expand`, `_four_expand`, `_one_mul_two_expand`, `_one_cube_expand`,
`_one_mul_three_expand`, `_one_sq_mul_two_expand`, `_two_sq_expand`, which are exactly the
`e`-monomials `G_2` carries — and the Hall--Littlewood table, stripped by the four Pieri rules
`HJO.Sym.bop_elemSymm_one_mul` through `HJO.Sym.bop_elemSymm_four_mul` down to the base rows
`B_k(1)` and `B_k(e_n)`, `3 ≤ n ≤ 6`.

Homogeneous of degree `8`, as `D_2` on the degree-six `V_2` must be, and every coefficient is
divisible by `qu`. This is the second decided point of `HJO.Mellit.onePartDefectTwo`.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, all three
`HJO.Mellit.stageWordTotal_two_three_two_eq`'s own and none of this evaluation's. -/
theorem onePartDefectTwo_two (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    onePartDefectTwo q u 2
      = (q^14*u - q^13*u + q^12*u^2 - q^12*u + q^10*u^3 - q^10*u^2 - 2*q^9*u^2 + 2*q^9*u
            + q^8*u^4 - q^8*u^2 + q^7*u^4 - 4*q^7*u^3 + 3*q^7*u^2 + 2*q^6*u^5 - 3*q^6*u^4
            + 2*q^6*u^2 - q^6*u + q^5*u^6 - 2*q^5*u^5 - 2*q^5*u^4 + 4*q^5*u^3 - q^5*u + q^4*u^7
            - q^4*u^6 - 2*q^4*u^5 + 3*q^4*u^4 - 2*q^4*u^2 + q^4*u + q^3*u^8 - 2*q^3*u^7 - q^3*u^6
            + 2*q^3*u^5 + q^3*u^4 - q^3*u^2 - q^2*u^8 + q^2*u^7 + q^2*u^6 - q^2*u^4 - q^2*u^3
            + q^2*u^2) • (elemSymm L 8)
        + (q^13*u + q^11*u^2 - q^11*u + q^10*u^2 - q^10*u + q^9*u^3 - 2*q^9*u + q^8*u^3
            - 2*q^8*u^2 + q^8*u + q^7*u^4 + 2*q^7*u^3 - 6*q^7*u^2 + 3*q^7*u + 3*q^6*u^4
            - 6*q^6*u^3 + q^6*u^2 + 2*q^6*u + 3*q^5*u^5 - 3*q^5*u^4 - 5*q^5*u^3 + 6*q^5*u^2
            - q^5*u + 2*q^4*u^6 - 2*q^4*u^5 - 6*q^4*u^4 + 6*q^4*u^3 + 3*q^4*u^2 - 3*q^4*u
            + 2*q^3*u^7 - 2*q^3*u^6 - 4*q^3*u^5 + 3*q^3*u^4 + 3*q^3*u^3 - 2*q^3*u^2 + q^2*u^8
            - 3*q^2*u^7 - q^2*u^6 + 3*q^2*u^5 + 3*q^2*u^4 - q^2*u^3 - 3*q^2*u^2 + q^2*u - q*u^8
            + q*u^7 + q*u^6 - q*u^4 - q*u^3 + q*u^2) • (elemSymm L 1 * elemSymm L 7)
        + (q^12*u - q^11*u + q^10*u^2 - q^9*u + q^8*u^3 + q^8*u - q^7*u^2 + q^6*u^4 + 2*q^6*u^3
            - 2*q^6*u^2 - q^6*u + 2*q^5*u^4 - 5*q^5*u^3 + q^5*u^2 + 2*q^5*u + 3*q^4*u^5
            - 3*q^4*u^4 + 2*q^4*u^2 - 2*q^4*u + 2*q^3*u^6 - 3*q^3*u^5 - q^3*u^4 + 2*q^3*u^3
            - q^3*u^2 + q^3*u + q^2*u^7 - q^2*u^6 - q^2*u^5 + 2*q^2*u^4 - q^2*u^3 - q^2*u^2
            + q^2*u + q*u^8 - q*u^7 - q*u^6 + q*u^5 - q*u^4 + q*u^3 + q*u^2 - q*u)
            • (elemSymm L 2 * elemSymm L 6)
        + (q^11*u - q^10*u + q^9*u^2 + q^7*u^3 - 2*q^7*u - q^6*u^2 + q^6*u + q^5*u^4 + q^5*u^3
            - 3*q^5*u^2 + q^5*u + q^4*u^4 - 3*q^4*u^3 + 2*q^4*u + 2*q^3*u^5 - 3*q^3*u^4
            - 2*q^3*u^3 + 4*q^3*u^2 - q^3*u - q^2*u^5 - q^2*u^4 + 3*q^2*u^3 + q^2*u^2 - 2*q^2*u
            - q*u^5 + 2*q*u^4 - 2*q*u^2 + q*u) • (elemSymm L 3 * elemSymm L 5)
        + (q^10*u - q^9*u + q^8*u^2 - q^8*u + q^6*u^3 - q^6*u^2 + q^6*u - 2*q^5*u^2 + q^5*u
            + q^4*u^4 - q^4*u^3 + q^4*u^2 - q^4*u - 2*q^3*u^3 + 2*q^3*u^2 - q^2*u^4 + 2*q^2*u^3
            - q^2*u^2) • (elemSymm L 4 * elemSymm L 4)
        + (q^11*u + q^9*u^2 + q^8*u^2 - 2*q^8*u + q^7*u^3 + q^7*u^2 - 2*q^7*u + 2*q^6*u^3
            - 4*q^6*u^2 + q^6*u + 2*q^5*u^4 - 4*q^5*u^2 + 2*q^5*u + q^4*u^5 + q^4*u^4 - 7*q^4*u^3
            + 2*q^4*u^2 + 3*q^4*u + q^3*u^6 + q^3*u^5 - 5*q^3*u^4 + q^3*u^3 + 4*q^3*u^2 - 2*q^3*u
            + q^2*u^7 - q^2*u^6 - 3*q^2*u^5 + 4*q^2*u^3 + q^2*u^2 - 2*q^2*u - q*u^7 + q*u^5
            + 2*q*u^4 - q*u^3 - 2*q*u^2 + q*u) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 6))
        + (q^10*u + q^9*u + q^8*u^2 - 2*q^8*u + 2*q^7*u^2 + q^6*u^3 + q^6*u^2 - q^6*u + 4*q^5*u^3
            - 4*q^5*u^2 - q^5*u + 3*q^4*u^4 - 2*q^4*u^3 - 3*q^4*u^2 + 2*q^4*u + 2*q^3*u^5
            + q^3*u^4 - 3*q^3*u^3 + 2*q^2*u^6 - q^2*u^5 - 3*q^2*u^4 - q^2*u^3 + 3*q^2*u^2 + q*u^7
            - q*u^6 - q*u^4 + q*u^3) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 5))
        + (q^9*u + q^8*u + q^7*u^2 + 2*q^6*u^2 - 4*q^6*u + q^5*u^3 + 2*q^5*u^2 - 2*q^5*u
            + 3*q^4*u^3 - 6*q^4*u^2 + 2*q^4*u + 2*q^3*u^4 - q^3*u^3 - 5*q^3*u^2 + 3*q^3*u
            + q^2*u^5 - q^2*u^4 - 6*q^2*u^3 + 5*q^2*u^2 + q^2*u - q*u^5 - q*u^4 + 3*q*u^3 + q*u^2
            - 2*q*u) • (elemSymm L 1 * (elemSymm L 3 * elemSymm L 4))
        + (q^8*u - q^7*u + q^6*u^2 + q^6*u + q^5*u^2 - 2*q^5*u + 2*q^4*u^3 - q^4*u^2 + 2*q^4*u
            + q^3*u^4 - q^3*u^3 - q^3*u + q^2*u^5 + q^2*u^2 - 2*q^2*u + q*u^6 - q*u^5 + q*u^4
            - q*u^3 - 2*q*u^2 + 2*q*u) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 4))
        + (q^7*u + q^5*u^2 + 2*q^4*u^2 - 3*q^4*u + 2*q^3*u^3 - 2*q^3*u^2 + q^2*u^4 - 4*q^2*u^2
            + 3*q^2*u + q*u^5 - q*u^4 - 2*q*u^3 + 3*q*u^2 - q*u)
            • (elemSymm L 2 * (elemSymm L 3 * elemSymm L 3))
        + (q^8*u + q^6*u^2 - q^6*u + q^5*u^2 - q^5*u + 2*q^4*u^3 - 2*q^4*u^2 - q^4*u + q^3*u^4
            - 2*q^3*u^3 - q^3*u^2 + 2*q^3*u + q^2*u^5 - q^2*u^4 - q^2*u^3 + q^2*u - q*u^5 + q*u^3
            + q*u^2 - q*u) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 5)))
        + (q^7*u + q^6*u + q^5*u^2 + q^5*u + 3*q^4*u^2 - 5*q^4*u + 3*q^3*u^3 - q^3*u^2
            + 2*q^2*u^4 - 6*q^2*u^2 + 3*q^2*u + q*u^5 - q*u^4 - 2*q*u^3 + 3*q*u^2 - q*u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 4)))
        + (q^6*u + q^4*u^2 + q^3*u^2 - 2*q^3*u + q^2*u^3 - q^2*u^2 - q^2*u - q*u^3 - q*u^2
            + 2*q*u) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 3 * elemSymm L 3)))
        + (q^5*u + 2*q^4*u + 2*q^3*u^2 + q^2*u^3 + 3*q^2*u^2 - 4*q^2*u + q*u^4 + 2*q*u^3
            - 4*q*u^2 + q*u) • (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 3)))
        + (q^2*u + q*u^2 - q*u) • (elemSymm L 2 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2)))
        + (q^4*u - q^3*u + q^2*u^2 - q^2*u - q*u^2 + q*u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))))
        + (q^3*u + q^2*u + q*u^2 - 2*q*u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))))
        + (q*u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2)))) := by
  rw [onePartDefectTwo, stageWordTotal_two_three_two_eq hq0 hu0 hq1]
  rw [sum_twistDop_add, sum_twistDop_add, sum_twistDop_add, sum_twistDop_add, sum_twistDop_add,
    sum_twistDop_add, sum_twistDop_add, sum_twistDop_add, sum_twistDop_add, sum_twistDop_add]
  rw [sum_twistDop_smul_auxVar_pow_mul_C, sum_twistDop_smul_auxVar_pow_mul_C,
    sum_twistDop_smul_auxVar_pow_mul_C, sum_twistDop_smul_auxVar_pow_mul_C,
    sum_twistDop_smul_auxVar_pow_mul_C, sum_twistDop_smul_auxVar_pow_mul_C,
    sum_twistDop_smul_auxVar_pow_mul_C, sum_twistDop_smul_auxVar_pow_mul_C,
    sum_twistDop_smul_auxVar_pow_mul_C, sum_twistDop_smul_auxVar_pow_mul_C,
    sum_twistDop_smul_auxVar_pow_mul_C]
  rw [twistDop_two_two_elemSymm_four, twistDop_two_two_elemSymm_two_sq,
    twistDop_two_two_elemSymm_one_mul_three, twistDop_two_two_elemSymm_one_sq_mul_two,
    twistDop_two_three_elemSymm_three, twistDop_two_three_elemSymm_one_mul_two,
    twistDop_two_three_elemSymm_one_cube, twistDop_two_four_elemSymm_two,
    twistDop_two_four_elemSymm_one_sq, twistDop_two_five_elemSymm_one, twistDop_two_six_one]
  match_scalars <;> grobner

/-! ### The two values the check is read against -/

/-- **`V_1 = e_1e_2 + (q+u-1)e_3`** in the `e`-basis, off
`HJO.Mellit.dminus_one_stageWordTotal_two_three_one_eq` —
`HJO.Mellit.onePartSweepValue_one` says the same element is `-Q_{2,3}(1)`, but that spells `M^{-1}`
and so carries `M ≠ 0`, which nothing below needs. -/
theorem onePartSweepValue_one_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    onePartSweepValue q u 1
      = (q + u - 1) • elemSymm L 3 + (1 : L) • (elemSymm L 1 * elemSymm L 2) := by
  rw [onePartSweepValue_eq_neg_constantCoeff,
    dminus_one_stageWordTotal_two_three_one_eq hq0 hu0 hq1]
  module

/-- **`w_1 = ct(d_-^{(1)}(y_1^2z_1G_1))`, written out**: four Hall--Littlewood values at the four
monomials of `HJO.Sweep.auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_one`, at the indices
`3, 3, 4, 5`. Homogeneous of degree `5`, every coefficient divisible by `qu`. -/
theorem onePartInnerValue_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    onePartInnerValue q u 1
      = (-(q ^ 4 * u) - q ^ 3 * u ^ 2 + q ^ 3 * u - q ^ 2 * u ^ 3 + q ^ 2 * u - q * u ^ 4
            + q * u ^ 3 + q * u ^ 2 - q * u) • elemSymm L 5
        + (-(q ^ 3 * u) - q ^ 2 * u ^ 2 - q * u ^ 3 + q * u) • (elemSymm L 1 * elemSymm L 4)
        + (-(q ^ 2 * u) - q * u ^ 2 + q * u) • (elemSymm L 2 * elemSymm L 3)
        + (-(q * u)) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)) := by
  rw [onePartInnerValue, auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_one hq0 hu0 hq1]
  simp only [map_add, map_smul, constantCoeff_smul, dminus_one_auxVar_pow_mul_C,
    MvPolynomial.constantCoeff_C, bop_three_elemSymm_two, bop_three_elemSymm_one_sq,
    bop_four_elemSymm_one, bop_five_one]
  module

/-- **`V_2` in the `e`-basis**, the nine-monomial degree-six value of
`HJO.Mellit.dminus_one_stageWordTotal_two_three_two` negated. -/
theorem onePartSweepValue_two_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    onePartSweepValue q u 2
      = (-(q ^ 8 * u) - q ^ 7 * u ^ 2 + q ^ 7 * u - q ^ 6 * u ^ 3 + q ^ 6 * u - q ^ 5 * u ^ 4
            + q ^ 5 * u ^ 2 - q ^ 4 * u ^ 5 + 2 * q ^ 4 * u ^ 2 - q ^ 4 * u - q ^ 3 * u ^ 6
            + 3 * q ^ 3 * u ^ 3 - q ^ 3 * u ^ 2 - q ^ 3 * u - q ^ 2 * u ^ 7 + q ^ 2 * u ^ 5
            + 2 * q ^ 2 * u ^ 4 - q ^ 2 * u ^ 3 - 2 * q ^ 2 * u ^ 2 + q ^ 2 * u - q * u ^ 8
            + q * u ^ 7 + q * u ^ 6 - q * u ^ 4 - q * u ^ 3 + q * u ^ 2) • elemSymm L 6
        + (-(q ^ 7 * u) - q ^ 6 * u ^ 2 - q ^ 5 * u ^ 3 - q ^ 5 * u ^ 2 + q ^ 5 * u
            - q ^ 4 * u ^ 4 - q ^ 4 * u ^ 3 + 2 * q ^ 4 * u - q ^ 3 * u ^ 5 - q ^ 3 * u ^ 4
            - q ^ 3 * u ^ 3 + 4 * q ^ 3 * u ^ 2 - q ^ 3 * u - q ^ 2 * u ^ 6 - q ^ 2 * u ^ 5
            + 4 * q ^ 2 * u ^ 3 - 2 * q ^ 2 * u - q * u ^ 7 + q * u ^ 5 + 2 * q * u ^ 4
            - q * u ^ 3 - 2 * q * u ^ 2 + q * u) • (elemSymm L 1 * elemSymm L 5)
        + (-(q ^ 6 * u) - q ^ 5 * u ^ 2 + q ^ 5 * u - q ^ 4 * u ^ 3 - q ^ 4 * u - q ^ 3 * u ^ 4
            - q ^ 3 * u ^ 2 + 2 * q ^ 3 * u - q ^ 2 * u ^ 5 - q ^ 2 * u ^ 3
            + 2 * q ^ 2 * u ^ 2 - q * u ^ 6 + q * u ^ 5 - q * u ^ 4 + 2 * q * u ^ 3 - q * u)
            • (elemSymm L 2 * elemSymm L 4)
        + (-(q ^ 5 * u) - q ^ 4 * u ^ 2 + q ^ 4 * u - q ^ 3 * u ^ 3 + q ^ 3 * u - q ^ 2 * u ^ 4
            + 2 * q ^ 2 * u ^ 2 - q ^ 2 * u - q * u ^ 5 + q * u ^ 4 + q * u ^ 3 - q * u ^ 2)
            • (elemSymm L 3 * elemSymm L 3)
        + (-(q ^ 5 * u) - q ^ 4 * u ^ 2 - q ^ 3 * u ^ 3 - q ^ 3 * u ^ 2 + q ^ 3 * u
            - q ^ 2 * u ^ 4 - q ^ 2 * u ^ 3 + q ^ 2 * u ^ 2 + q ^ 2 * u - q * u ^ 5 + q * u ^ 3
            + q * u ^ 2 - q * u) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 4))
        + (-(q ^ 4 * u) - q ^ 3 * u ^ 2 - 2 * q ^ 3 * u - q ^ 2 * u ^ 3 - 3 * q ^ 2 * u ^ 2
            + 3 * q ^ 2 * u - q * u ^ 4 - 2 * q * u ^ 3 + 3 * q * u ^ 2)
            • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 3))
        + (-(q ^ 2 * u) - q * u ^ 2 + q * u) • (elemSymm L 2 * (elemSymm L 2 * elemSymm L 2))
        + (-(q ^ 2 * u) - q * u ^ 2 + q * u)
            • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3)))
        + (-(q * u)) • (elemSymm L 1 * (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2))) := by
  rw [onePartSweepValue_eq_neg_constantCoeff, dminus_one_stageWordTotal_two_three_two hq0 hu0 hq1,
    MvPolynomial.constantCoeff_C]
  module

/-- **THE SAME VALUE, re-derived through the closed form** — the check on the `d^*_+`-expansion
machinery that computes `HJO.Sweep.twistDop`.

`HJO.Mellit.onePartDefectTwo_eq` at `A = 1` reads `Δ²_1` off `D_2(V_1)` and
`HJO.Mellit.onePartInnerValue_one`, i.e. off the `z_1`-value
`HJO.Sweep.auxVar_sq_mul_zopOneStar_one_stageWordTotal_two_three_one` and the `HJO.Sym.DopInt`
table.
**No `HJO.Sweep.twistDop`, no `HJO.Sweep.twistProj` and no graded `d^*_+` row occurs in this
proof**, while `HJO.Mellit.onePartDefectTwo_one` is nothing but those. So the agreement checks the
machinery that `HJO.Mellit.onePartDefectTwo_two` runs on, one degree lower, against a route that
shares no lemma with it.

`HJO.Mellit.onePartDefectTwo_one_eq` is the `rfl` between the two. -/
theorem onePartDefectTwo_one_of_value (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    onePartDefectTwo q u 1
      = (-q ^ 4 + q ^ 3 - q ^ 2 * u + q ^ 2 + q * u - q) • elemSymm L 5
        + (-q ^ 3 - q * u + 2 * q + u - 1) • (elemSymm L 1 * elemSymm L 4)
        + (-q ^ 2 - u + 1) • (elemSymm L 2 * elemSymm L 3)
        + (1 - q) • (elemSymm L 1 * (elemSymm L 1 * elemSymm L 3))
        + (-1 : L) • (elemSymm L 1 * (elemSymm L 2 * elemSymm L 2)) := by
  rw [onePartDefectTwo_eq hq0 hq1, onePartSweepValue_one_eq hq0 hu0 hq1,
    onePartInnerValue_one hq0 hu0 hq1]
  refine smul_right_injective (Lambda L) hq0 ?_
  dsimp only
  rw [smul_sub, smul_neg, smul_smul, show q * ((1 - q) / q) = 1 - q from by field_simp]
  simp only [map_add, map_smul, dop_elemSymm_one_mul, dop_two_mul, Nat.reduceAdd,
    dop_one_elemSymm_two, dop_two_elemSymm_two, dop_three_elemSymm_two, dop_four_elemSymm_two,
    dop_one_elemSymm_three, dop_two_elemSymm_three, dop_three_elemSymm_three,
    dop_one_elemSymm_four, dop_two_elemSymm_four, dop_one_elemSymm_five]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  ring

/-- **The two routes to `Δ²_1` state the same `Prop`**, hypothesis lists included. -/
theorem onePartDefectTwo_one_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    onePartDefectTwo_one (L := L) (u := u) hq0 hu0 hq1
      = onePartDefectTwo_one_of_value hq0 hu0 hq1 := rfl

/-! ### The consistency check: the step at `A = 0`, with the defects evaluated -/

/-- **THE ONE-PART RECURSION AT `A = 0` WITH THE SCALARS CLEARED:**

  `qu(1-q)^2·V_2 = q^2·D_1(D_2(V_1)) + q^2·D_1(Δ²_1) + q(1-q)·Δ¹_1`.

`HJO.Mellit.onePartSweepValue_succ` at `A = 0` with `qu(1-q)^2·` applied to both sides — the two
scalars `(qu)^{-1}(q/(1-q))^2` and `(qu)^{-1}q/(1-q)` of the step become `q^2` and `q(1-q)`, which
is where `q ≠ 0`, `u ≠ 0` and `q ≠ 1` are spent and nowhere else. No value of anything is used. -/
theorem smul_onePartSweepValue_two_of_step (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    (q * u * (1 - q) ^ 2) • onePartSweepValue q u 2
      = (q ^ 2) • Dop q u 1 (Dop q u 2 (onePartSweepValue q u 1))
        + (q ^ 2) • Dop q u 1 (onePartDefectTwo q u 1)
        + (q * (1 - q)) • onePartDefectOne q u 1 := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have h := onePartSweepValue_succ (L := L) q u 0
  rw [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl] at h
  rw [h, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
    show q * u * (1 - q) ^ 2 * ((q * u)⁻¹ * (q / (1 - q)) ^ 2) = q ^ 2 from by field_simp,
    show q * u * (1 - q) ^ 2 * ((q * u)⁻¹ * (q / (1 - q))) = q * (1 - q) from by field_simp]

/-- **THE SAME IDENTITY, WITH EVERY TERM EVALUATED — the consistency check on the two defects.**

`V_1` and `V_2` are the values `HJO.Mellit.onePartSweepValue_one_eq` and
`HJO.Mellit.onePartSweepValue_two_eq`, computed from the stage word by
`HJO.Mellit.dminus_one_stageWordTotal_two_three_one_eq` and
`HJO.Mellit.dminus_one_stageWordTotal_two_three_two` — routes that contain no
`HJO.Sweep.twistDop`, no `d^*_+` expansion and no defect at all. `Δ²_1` and `Δ¹_1` are
`HJO.Mellit.onePartDefectTwo_one` and `HJO.Mellit.onePartDefectOne_one`, computed from the
`d^*_+`-expansion route through `HJO.Sweep.twistProj`. The `D`-values are the
`HJO.Sym.DopInt` table, unfolded by the two Pieri rules.

**So a dropped term, a wrong Hall--Littlewood index or a lost sign in either defect would separate
the two sides here**: `Δ¹_1` enters at degree six with nine monomials and `q^2D_1(Δ²_1)` at the same
degree with none of the same provenance, and the identity is exact over all eleven `e`-monomials of
degree six.

`HJO.Mellit.smul_onePartSweepValue_two_of_step_eq` checks by `rfl` that this is the same `Prop` as
`HJO.Mellit.smul_onePartSweepValue_two_of_step`, which proves it from
`HJO.Mellit.onePartSweepValue_succ` with no value in it. -/
theorem smul_onePartSweepValue_two_of_value (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    (q * u * (1 - q) ^ 2) • onePartSweepValue q u 2
      = (q ^ 2) • Dop q u 1 (Dop q u 2 (onePartSweepValue q u 1))
        + (q ^ 2) • Dop q u 1 (onePartDefectTwo q u 1)
        + (q * (1 - q)) • onePartDefectOne q u 1 := by
  rw [onePartSweepValue_two_eq hq0 hu0 hq1, onePartSweepValue_one_eq hq0 hu0 hq1,
    onePartDefectTwo_one hq0 hu0 hq1, onePartDefectOne_one hq0 hu0 hq1]
  simp only [map_add, map_sub, map_neg, map_smul, dop_elemSymm_one_mul, dop_two_mul,
    Nat.reduceAdd, dop_one_elemSymm_two, dop_two_elemSymm_two, dop_three_elemSymm_two,
    dop_four_elemSymm_two, dop_one_elemSymm_three, dop_two_elemSymm_three,
    dop_three_elemSymm_three, dop_one_elemSymm_four, dop_two_elemSymm_four, dop_one_elemSymm_five]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
    MvPolynomial.C_mul, MvPolynomial.C_1, MvPolynomial.C_pow, map_ofNat]
  grobner

/-- **The two routes state the same `Prop`.** `rfl` between two proofs typechecks only if their
statements — and their hypothesis lists — are identical. -/
theorem smul_onePartSweepValue_two_of_step_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    smul_onePartSweepValue_two_of_step (L := L) hq0 hu0 hq1
      = smul_onePartSweepValue_two_of_value hq0 hu0 hq1 := rfl

/-! ### What the recursion is, once both defects are values

The two closed forms above are substituted back into `HJO.Mellit.onePartSweepValue_succ`, and the
`D_1D_2` term — the "value-only part of the step" — **cancels identically** against the inner
defect, `D_1(w_{A+1})` cancels between the two defects, and what survives is
`V_{A+2} = -(qu)^{-1}x_{A+1}`, which is the replicated letter's definition. So the step identity
carries no information beyond one further `z_1`; the check below is that statement, proved twice. -/

/-- **`qu(1-q)^2·V_{A+2} = -(1-q)^2·x_{A+1}`, THROUGH THE TWO EVALUATED DEFECTS**, at every `A`.

`HJO.Mellit.onePartSweepValue_succ` with `HJO.Mellit.onePartDefectTwo_eq` and
`HJO.Mellit.onePartDefectOne_eq` substituted: `q^2·D_1(D_2(V_{A+1}))` cancels against the inner
defect's `-D_2(V_{A+1})`, and `q(1-q)·D_1(w_{A+1})` cancels between the two defects; one term
survives.

Genericity: `q ≠ 0`, `u ≠ 0` for the `(qu)^{-1}` of `HJO.Sweep.slopeOperator` and `q ≠ 1` for the
`q/(1-q)` of `HJO.Sweep.zop`; all three are spent on clearing the scalars and none on the
cancellation, which is term by term. -/
theorem smul_onePartSweepValue_succ_of_defect (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (A : ℕ) :
    (q * u * (1 - q) ^ 2) • onePartSweepValue q u (A + 2)
      = (-((1 - q) ^ 2)) • onePartOuterValue q u (A + 1) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [onePartSweepValue_succ, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
    show q * u * (1 - q) ^ 2 * ((q * u)⁻¹ * (q / (1 - q)) ^ 2) = q ^ 2 from by field_simp,
    show q * u * (1 - q) ^ 2 * ((q * u)⁻¹ * (q / (1 - q))) = q * (1 - q) from by field_simp,
    onePartDefectTwo_eq hq0 hq1, onePartDefectOne_eq hq0 hq1, map_sub, map_neg, map_smul, smul_sub,
    smul_neg, smul_sub, smul_smul, smul_smul,
    show q ^ 2 * ((1 - q) / q) = q * (1 - q) from by field_simp,
    show q * (1 - q) * ((1 - q) / q) = (1 - q) ^ 2 from by field_simp]
  module

/-- **THE SAME IDENTITY, STRAIGHT FROM THE REPLICATED LETTER.**

`HJO.Mellit.stageWordTotal_singleton_succ` and `HJO.Sweep.replicatedTotal_two_three_zero_apply`:
`G_{A+2} = (qu)^{-1}y_1z_1y_1^2z_1G_{A+1}`, so `V_{A+2} = -(qu)^{-1}x_{A+1}` by the definition of
`HJO.Mellit.onePartSweepValue`. **No defect, no `HJO.Sym.DopInt` operator and no
`HJO.Sweep.twistDop` occurs in this proof.**

`HJO.Mellit.smul_onePartSweepValue_succ_of_defect_eq` checks by `rfl` that the two are the same
`Prop`, which is the consistency check on `HJO.Mellit.onePartDefectTwo_eq` and
`HJO.Mellit.onePartDefectOne_eq` **at every `A` at once**: a sign or a scalar wrong in either closed
form would leave a residual term here. -/
theorem smul_onePartSweepValue_succ_of_letter (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (A : ℕ) :
    (q * u * (1 - q) ^ 2) • onePartSweepValue q u (A + 2)
      = (-((1 - q) ^ 2)) • onePartOuterValue q u (A + 1) := by
  rw [onePartSweepValue_eq_neg_constantCoeff, stageWordTotal_singleton_succ,
    replicatedTotal_two_three_zero_apply, map_smul, constantCoeff_smul, ← onePartOuterValue_eq,
    smul_neg, smul_smul, show q * u * (1 - q) ^ 2 * (q * u)⁻¹ = (1 - q) ^ 2 from by field_simp]
  module

/-- **The two routes state the same `Prop`**, hypothesis lists included. -/
theorem smul_onePartSweepValue_succ_of_defect_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (A : ℕ) :
    smul_onePartSweepValue_succ_of_defect (L := L) hq0 hu0 hq1 A
      = smul_onePartSweepValue_succ_of_letter hq0 hu0 hq1 A := rfl

/-! ### What that costs the reduction: the step hypothesis is not weaker than the clause -/

/-- **THE `hstep` OF `HJO.Mellit.forall_lhsAt_two_three_singleton_succ_of_creation` IS, GIVEN THE
CLAUSE AT `[A+1]`, EQUIVALENT TO THE CLAUSE AT `[A+2]`.**

`HJO.Mellit.lhsAt_two_three_singleton_iff_onePartSweepValue` turns the clause at `[A+1]` into
`Θ(h_{A+1})(1) = V_{A+1}`, and then `HJO.Mellit.onePartSweepValue_succ` says the right-hand side of
`hstep` **is** `V_{A+2}`. So `hstep` at `A` says exactly `Θ(h_{A+2})(1) = V_{A+2}`, which is the
clause at `[A+2]`.

This is recorded because it is a **negative** structural fact and it bounds what the one-part
reduction achieved: the step identity is not a weaker obligation than the family it is used to
prove, so `HJO.Mellit.forall_lhsAt_two_three_singleton_succ_of_creation` is the induction restated,
not a reduction of it. What the defect evaluations above do buy is the *explicit* right-hand side:
`HJO.Mellit.onePartDefectTwo_one` and `HJO.Mellit.onePartDefectOne_one` make `V_2` computable from
`V_1`, and `HJO.Mellit.smul_onePartSweepValue_succ_of_letter` says the same computation at every `A`
is one `z_1` step and nothing else.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, all three
`HJO.Mellit.lhsAt_two_three_singleton_iff_onePartSweepValue`'s. -/
theorem creation_step_iff_lhsAt_succ (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (A : ℕ)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hA : LhsAt q u 2 3 Θ [A + 1]) :
    (Θ (completeHomog L (A + 2)) 1
        = ((q * u)⁻¹ * (q / (1 - q)) ^ 2) •
              Dop q u 1 (Dop q u 2 (Θ (completeHomog L (A + 1)) 1))
          + ((q * u)⁻¹ * (q / (1 - q)) ^ 2) • Dop q u 1 (onePartDefectTwo q u (A + 1))
          + ((q * u)⁻¹ * (q / (1 - q))) • onePartDefectOne q u (A + 1))
      ↔ LhsAt q u 2 3 Θ [A + 2] := by
  rw [lhsAt_two_three_singleton_iff_onePartSweepValue hq0 hu0 hq1 (A + 2) Θ,
    (lhsAt_two_three_singleton_iff_onePartSweepValue hq0 hu0 hq1 (A + 1) Θ).1 hA,
    onePartSweepValue_succ]

end HJO.Mellit

end
