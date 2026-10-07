/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitLhsSlopeBase
public import HJO.Shuffle.MellitSweepSecondZ
public meta import HJO.Attr

/-! # The base case of `HJO.Mellit.lhsRewrite_sweepWitness` at `(a, b) = (3, 4)`

`HJO/Shuffle/MellitLhsSlopeBase.lean` settles the `α = (1)` instance of
`HJO.Mellit.LhsComputes` at `(a, b) = (2, 3)`, the smallest slope whose word carries a letter `z`.
`HJO/Shuffle/MellitQopThreeFour.lean` computes the `Q` side of the next instance,
`HJO.Sym.qop_three_four_apply_one`. On the sweep side the new difficulty is the second `z` of
`β_{3,4} = yzyzy` (`HJO.Mellit.slopeWord_three_four`).

`HJO.Sweep.dplusStar_C_elemSymm` and
`HJO.Sweep.zopOneStar_one_auxVar_mul_dplusStar_C_elemSymm_two_sub` evaluate that second `z`. **This
file takes the remaining three steps, so the `(3,4)` instance of the general-slope gluing identity
is a theorem.**

## Main results

* `HJO.Sweep.slopeOperator_three_four`: `Ξ^{(1)}_{3,4}` read off the word `yzyzy`, the exact
  analogue of `HJO.Sweep.slopeOperator_two_three`.
* `HJO.Sweep.slopeOperator_three_four_eq_mul`: the mediant factorisation as an operator identity,
  `Ξ^{(1)}_{3,4} = (-y_1)·(qu)^{-1}z_1·Ξ^{(1)}_{2,3}` — the reading of
  `HJO.Sym.split_three_four` in which the outer factor `Ξ_2` of the general reduction is the
  identity, so the whole content of the step is one `YZ` past `(2,3)`.
* `HJO.Sweep.slopeOperator_three_four_auxVar`: `Ξ^{(1)}_{3,4}(y_1)` in closed form, every `z`
  discharged.
* `HJO.Mellit.constantCoeff_lowerRun_stageWordTotal_three_four`: **the sweep side of the base case
  at `(3,4)`**, equal to `e_1^2e_2 + (q+u-1)e_2^2 + (q^2+qu+u^2-1)e_1e_3 +`
  `(1-q-u-q^2-u^2+q^3+q^2u+qu^2+u^3)e_4`.
* `HJO.Mellit.lhsBase_three_four`: the base case itself, against
  `HJO.Sym.qop_three_four_apply_one`.

## Why both bridges are needed

`HJO.Mellit.constantCoeff_lowerRun_stageWordTotal_three_four` reaches `Λ` through *two* bridges: the
summands carrying `d^*_+{}^{(0)}` go through
`HJO.Sweep.dop_succ_eq_dminus_auxVar_pow_dplusStar` and land on `D^{q,u}`, the summands that do not
go through `HJO.Sweep.dminus_auxVar_pow_mul_C` and land on `D^{q,0} = B`. The scalar in front is
`((qu)^{-1}q/(1-q))^2`, whose `u^{-2}` the combination must absorb.

It does, but neither group absorbs it alone: grouped by bridge, each of the two contributions has
minimal `u`-degree `1` where `2` is needed, so each separately has a simple pole at `u = 0` and only
their sum is a polynomial. That is the `(P - y_1N)` phenomenon of the general reduction — `N` is
load-bearing — seen here at the last step of this file's proof. It is *not* itself a theorem below;
it is the reason the proof cannot be split into two independent halves.

## Genericity

`q ∉ {0, 1}` and `u ≠ 0` for the sweep side, exactly as at `(2,3)`: the inverses are `(qu)^{-1}`
from `HJO.Sweep.slopeOperator` and `(1-q)^{-1}` from `HJO.Sweep.zop`, both carried symbolically
through expansions that are themselves unconditional
(`HJO.Sweep.dplusStar_C_elemSymm`). The full clause adds `u ≠ 1`, which enters only through
`HJO.Sym.Qop`'s `((1-q)(1-u))^{-1}`; at `(2,3)` that hypothesis is *necessary on a curve*
(`HJO.Mellit.not_lhsBase_two_three_of_u_eq_one`).

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking
functions*, §3.
-/

@[expose] public section

open HJO.Sym HJO.Sweep HJO.Mellit HJO.Bglx

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The one Pieri expansion the `(3,4)` sweep side needs -/

/-- **`D_1(e_1e_2) = (M-1)e_1^2e_2 + Me_2^2 + ((q+u)M - M^2)e_1e_3 - (q+u)M^2e_4`.**

The Pieri rule `HJO.Sym.dop_elemSymm_one_mul` at `k = 1`, `f = e_2`, against
`HJO.Sym.dop_one_elemSymm_two` and `HJO.Sym.dop_two_elemSymm_two`. This is the value the second `z`
of `β_{3,4}` forces: `HJO.Sym.bop_two_elemSymm_one` puts `e_1e_2` into the `Λ`-coefficient, so the
outer lowering operator meets `D_1` on a *product* and not on an `e_n`. Read at `u = 0` it is the
Hall--Littlewood value `B_1(e_1e_2)`, by `HJO.Sym.bop_natCast`. -/
theorem dop_one_elemSymm_one_mul_two (q u : L) :
    Dop q u 1 (elemSymm L 1 * elemSymm L 2)
      = ((1 - q) * (1 - u) - 1) • (elemSymm L 1 * elemSymm L 1 * elemSymm L 2)
        + ((1 - q) * (1 - u)) • (elemSymm L 2 * elemSymm L 2)
        + ((q + u) * ((1 - q) * (1 - u)) - ((1 - q) * (1 - u)) ^ 2)
            • (elemSymm L 1 * elemSymm L 3)
        - ((q + u) * ((1 - q) * (1 - u)) ^ 2) • elemSymm L 4 := by
  rw [dop_elemSymm_one_mul, dop_one_elemSymm_two, dop_two_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_one, map_pow]
  ring

end HJO.Sym

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The slope operator at `(3, 4)` -/

/-- **`Ξ^{(1)}_{3,4} = (-y_1)·(qu)^{-1}z_1·(-y_1)·(qu)^{-1}z_1·(-y_1)`**, the word
`β_{3,4} = yzyzy` (`HJO.Mellit.slopeWord_three_four`) read by `HJO.Sweep.slopeOperator` with the
head outermost. The exact analogue of `HJO.Sweep.slopeOperator_two_three`, one `yz` longer. -/
theorem slopeOperator_three_four (q u : L) :
    slopeOperator q u 1 3 4
      = (-LinearMap.mulLeft L (auxVar 1 : Total L)) * ((q * u)⁻¹ • zop q u 1 1)
        * (-LinearMap.mulLeft L (auxVar 1 : Total L)) * ((q * u)⁻¹ • zop q u 1 1)
        * (-LinearMap.mulLeft L (auxVar 1 : Total L)) := by
  rw [slopeOperator, Mellit.slopeWord_three_four]
  simp [mul_assoc]

/-- **The mediant factorisation at `(3,4)`, as an operator identity**:
`Ξ^{(1)}_{3,4} = (-y_1)·(qu)^{-1}z_1·Ξ^{(1)}_{2,3}`.

`Split 3 4 = (1,1)` (`HJO.Sym.split_three_four`), so `HJO.Mellit.slopeEval_mediant` reads
`Ξ_{3,4} = Ξ_{1,1}·Y·Z·Ξ_{2,3}` with `Ξ_{1,1} = 1`: the outer factor of the general reduction is the
identity here, and the whole content of the `(3,4)` step is the single `YZ` in front of the
`(2,3)` operator. Proved by splitting `yzyzy` as `yz ++ yzy`, which is what
`HJO.Mellit.slopeWord_three_four` and `HJO.Mellit.slopeWord_two_three` say. -/
theorem slopeOperator_three_four_eq_mul (q u : L) :
    slopeOperator q u 1 3 4
      = (-LinearMap.mulLeft L (auxVar 1 : Total L)) * ((q * u)⁻¹ • zop q u 1 1)
        * slopeOperator q u 1 2 3 := by
  rw [slopeOperator_three_four, slopeOperator_two_three]
  simp only [mul_assoc]

/-- **`Ξ^{(1)}_{3,4}(y_1)` in closed form**, with both `z` letters discharged and no operator left
on the right but `d^*_+` on constants:

`Ξ^{(1)}_{3,4}(y_1) = -((qu)^{-1}q/(1-q))^2 · y_1·[ (q-1)u(d^*_+(Ce_1e_2) - (1-q)d^*_+(Ce_3)`
`- Ce_1e_2 + (1-q)Ce_3 - (q-1)u·y_1Ce_2) + (1-q)u^2(Ce_3 - d^*_+(Ce_3)) ]`.

The route is the mediant factorisation `HJO.Sweep.slopeOperator_three_four_eq_mul`:
`HJO.Sweep.slopeOperator_two_three_auxVar` supplies `Ξ^{(1)}_{2,3}(y_1)` as
`((qu)^{-1}q/(1-q))·y_1·(d^*_+(Ce_2) - Ce_2)`, and the outer `z` on that is exactly
`HJO.Sweep.zopOneStar_one_auxVar_mul_dplusStar_C_elemSymm_two_sub`. The
two scalars `(qu)^{-1}q/(1-q)` multiply, which is where the square comes from, and the three `y`
letters contribute `(-1)^3`.

No hypothesis on `q` or `u`: every scalar is carried symbolically. -/
theorem slopeOperator_three_four_auxVar (q u : L) :
    slopeOperator q u 1 3 4 (auxVar 1 : Total L)
      = (-(((q * u)⁻¹ * (q / (1 - q))) ^ 2)) • ((auxVar 1 : Total L) *
          (((q - 1) * u) •
              (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 2))
                - (1 - q) • dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 3))
                - MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 2)
                + (1 - q) • (MvPolynomial.C (Sym.elemSymm L 3) : Total L)
                - ((q - 1) * u) •
                    ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 2)))
            + ((1 - q) * u ^ 2) • (MvPolynomial.C (Sym.elemSymm L 3)
                - dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 3))))) := by
  rw [slopeOperator_three_four_eq_mul]
  simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply,
    LinearMap.smul_apply, zop_one]
  rw [slopeOperator_two_three_auxVar q u, ← mul_sub, map_smul,
    zopOneStar_one_auxVar_mul_dplusStar_C_elemSymm_two_sub]
  simp only [mul_smul_comm, smul_smul]
  module

end HJO.Sweep

namespace HJO.Mellit

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The sweep side of the base case at `(3, 4)` -/

/-- **The sweep side of the base case at `(a,b) = (3,4)`:**
`ct(d_-(G_1(1))) = e_1^2e_2 + (q+u-1)e_2^2 + (q^2+qu+u^2-1)e_1e_3`
`+ (1-q-u-q^2-u^2+q^3+q^2u+qu^2+u^3)e_4`.

`HJO.Mellit.stageWordTotal_singleton_one` is stated at general `(a,b)`, so at `(3,4)` the stage word
is `-Ξ^{(1)}_{3,4}(y_1)` outright — the sign `(-1)^{a-1}` is `+1` at `a = 3`, where at `(2,3)` it
was `-1`. `HJO.Sweep.slopeOperator_three_four_auxVar` puts that in the form the two bridges
read: every summand is `y_1·d^*_+{}^{(0)}(Cf)`, `y_1·Cf` or `y_1^2·Ce_2`, and

* `d_-(y_1d^*_+(Cf)) = C(D^{q,u}_1f)` by
  `HJO.Sweep.dop_succ_eq_dminus_auxVar_pow_dplusStar` at `m = 0`;
* `d_-(y_1^mCf) = C(B_mf) = C(D^{q,0}_mf)` by `HJO.Sweep.dminus_auxVar_pow_mul_C` with
  `HJO.Sym.bop_natCast`.

So the whole answer is five values of the basic operator in degree `4`:
`D^{q,u}_1(e_1e_2)`, `D^{q,u}_1(e_3)`, `D^{q,0}_1(e_1e_2)`, `D^{q,0}_1(e_3)`, `D^{q,0}_2(e_2)`,
by `HJO.Sym.dop_one_elemSymm_one_mul_two`, `HJO.Sym.dop_one_elemSymm_three` and
`HJO.Sym.dop_two_elemSymm_two`. Their combination carries the factor `u^2(1-q)^2` that the scalar
`((qu)^{-1}q/(1-q))^2 = (u(1-q))^{-2}` cancels exactly, which is why the answer is a polynomial in
`q` and `u`. Split by bridge it does not: the `D^{q,u}` group and the `D^{q,0}` group each have
minimal `u`-degree `1` rather than `2`, so neither is a polynomial once the scalar is applied.

The hypotheses are the inverses the word carries: `(qu)^{-1}` from
`HJO.Sweep.slopeOperator` and `(1-q)^{-1}` from `HJO.Sweep.zop`, the same three as at `(2,3)`. No
hypothesis on `u - 1`; that one belongs to `HJO.Sym.Qop`. -/
theorem constantCoeff_lowerRun_stageWordTotal_three_four
    (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    MvPolynomial.constantCoeff (lowerRun q 1 (stageWordTotal q u 3 4 [1]))
      = elemSymm L 1 * elemSymm L 1 * elemSymm L 2
        + (q + u - 1) • (elemSymm L 2 * elemSymm L 2)
        + (q ^ 2 + q * u + u ^ 2 - 1) • (elemSymm L 1 * elemSymm L 3)
        + (1 - q - u - q ^ 2 - u ^ 2 + q ^ 3 + q ^ 2 * u + q * u ^ 2 + u ^ 3)
            • elemSymm L 4 := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hD : ∀ f : Sym.Lambda L,
      dminus q 1 ((auxVar 1 : Total L) * dplusStar q u 0 (MvPolynomial.C f))
        = MvPolynomial.C (Sym.Dop q u 1 f) := fun f => by
    simpa using (dop_succ_eq_dminus_auxVar_pow_dplusStar q u 0 f).symm
  have hB1 : ∀ f : Sym.Lambda L,
      dminus q 1 ((auxVar 1 : Total L) * MvPolynomial.C f)
        = MvPolynomial.C (Sym.Dop q 0 1 f) := fun f => by
    rw [← Sym.bop_natCast q 1]
    simpa using dminus_auxVar_pow_mul_C q 0 1 f
  have hB2 : dminus q 1 ((auxVar 1 : Total L) *
        ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 2)))
      = MvPolynomial.C (Sym.Dop q 0 2 (Sym.elemSymm L 2)) := by
    rw [← mul_assoc, show (auxVar 1 : Total L) * (auxVar 1 : Total L)
        = (auxVar 1 : Total L) ^ 2 from (sq _).symm, ← Sym.bop_natCast q 2]
    simpa using dminus_auxVar_pow_mul_C q 0 2 (Sym.elemSymm L 2)
  have hstage : stageWordTotal q u 3 4 [1]
      = -slopeOperator q u 1 3 4 (auxVar 1 : Total L) := by
    rw [stageWordTotal_singleton_one, dplusStar_one, mul_one,
      show trainDownEnd q 1 1 = 1 from Braid.trainDown_self _ _ 1, Module.End.one_apply]
    norm_num
  rw [hstage, show lowerRun q 1 = dminus q 1 from by simp [lowerRun],
    slopeOperator_three_four_auxVar]
  simp only [map_neg, map_smul, mul_add, mul_sub, mul_smul_comm, map_add, map_sub, hD, hB1, hB2]
  simp only [MvPolynomial.constantCoeff_smul, map_add, map_sub, MvPolynomial.constantCoeff_C]
  rw [Sym.dop_one_elemSymm_one_mul_two q u, Sym.dop_one_elemSymm_three q u,
    Sym.dop_one_elemSymm_one_mul_two q 0, Sym.dop_one_elemSymm_three q 0,
    Sym.dop_two_elemSymm_two q 0]
  match_scalars <;> (field_simp; ring)

/-! ### The base case at `(a, b) = (3, 4)` -/

/-- **The base case of `HJO.Mellit.lhsRewrite_sweepWitness` holds at `(a, b) = (3, 4)`.**

This is the conclusion of `HJO.Mellit.qop_apply_one_of_lhsComputes` at `(a,b) = (3,4)`, proved in
`Λ` before any realisation is applied, so the stated form of the clause follows by `congrArg ι`.
Both sides are
`e_1^2e_2 + (q+u-1)e_2^2 + (q^2+qu+u^2-1)e_1e_3 + (1-q-u-q^2-u^2+q^3+q^2u+qu^2+u^3)e_4`:
the `Q` side is `HJO.Sym.qop_three_four_apply_one`, the sweep side
`HJO.Mellit.constantCoeff_lowerRun_stageWordTotal_three_four`. The two signs `(-1)^b` and
`(-1)^{a-1}` are both `+1` here, where at `(2,3)` they were both `-1`.

`(3,4)` is the smallest slope whose word carries *two* letters `z`, hence the first at which a `z`
meets an element of `V_1` with a nontrivial `Λ`-coefficient, and the first at which `HJO.Sym.Qop`
performs two nested commutators. -/
theorem lhsBase_three_four (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (hu1 : u ≠ 1) :
    (-1 : L) ^ (4 : ℕ) • Qop q u 3 4 (1 : Lambda L)
      = (-1 : L) ^ (3 - 1 : ℕ) •
        MvPolynomial.constantCoeff (lowerRun q 1 (stageWordTotal q u 3 4 [1])) := by
  rw [qop_three_four_apply_one (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hq1))
      (sub_ne_zero.mpr (Ne.symm hu1))),
    constantCoeff_lowerRun_stageWordTotal_three_four hq0 hu0 hq1]
  norm_num

end HJO.Mellit
