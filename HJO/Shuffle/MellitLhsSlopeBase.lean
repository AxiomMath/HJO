/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWitnessLhsSingleton
public import HJO.CarlssonMellit.DopIndexFromDplusStar
public import HJO.CarlssonMellit.BopModified
public import HJO.Collinear.ShiftEsymm
public import HJO.Collinear.Commutation
public import HJO.Collinear.EsymmAlphabet
public import HJO.Regression
public meta import HJO.Attr

/-! # The `a > 1` column of the base case of `HJO.Mellit.lhsRewrite_sweepWitness`, computed at
`(a, b) = (2, 3)`

`HJO.Mellit.qop_apply_one_of_lhsComputes` (`HJO/Shuffle/SweepWitnessLhsSingleton.lean`)
reduces the `α = (1)` instance of `HJO.Mellit.LhsComputes` to a single identity in `Λ`, pushed
forward along an arbitrary realisation `ι`:

`(-1)^b ι(Q_{a,b} 1) = (-1)^{a-1} ι(ct(d_-(G_{1}(1))))`,

with the sweep side written out by `HJO.Mellit.stageWordTotal_singleton_one`. At `a = 1` that
identity is `HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` and is proved. **This file settles
the smallest instance with `a > 1`, namely `(a, b) = (2, 3)`, without the `ι`** — the identity is
proved in `Λ` itself, so `ι` follows by `congrArg`, and the two sides are computed in closed form:

`Q_{2,3}(1) = -e_1e_2 + (1 - q - u) e_3 = ct(d_-(Ξ^{(1)}_{2,3}(y_1)))`.

## What the computation shows about the shape of the general identity

Three structural facts come out of it, each of which is what makes the `(2,3)` proof below short.

**The base case lives in `V_1`, not in `V_*` or in `Mellit.Graded`.** At `α = (1)` the stage word is
`HJO.Sweep.slopeOperator q u 1 a b` — the slope operator at `k = 1`, where
`HJO.Sweep.slopeOperator` reads the word `β_{a,b}` with *no* `T_i` and no square root of `q`, its
two letters being multiplication by `-y_1` and `(qu)^{-1}z_1`. Both are endomorphisms of
`V_1 = Λ[y_1]`, the vacuum `y_1 d^*_+(1)` is `y_1`, and `HJO.Mellit.lowerRun q 1` is `d_-` at index
`1`, landing in `V_0 = Λ`. So no bridge between `HJO.Sweep.Vstar` and `HJO.Mellit.Graded` is needed
for the base case, and none is used here.

**The `a`-dependent signs cancel.** `stageWordTotal` carries `-(-1)^{a-1}` and the clause carries
`(-1)^{a-1}`, so the identity the base case asks for is, for every coprime `a, b ≥ 1`,

`(-1)^b Q_{a,b}(1) = -ct(d_-(Ξ^{(1)}_{a,b}(y_1)))`,  equivalently
`Q_{a,b}(1) = (-1)^{b+1} ct(d_-(Ξ^{(1)}_{a,b}(y_1)))`.

At `a = 1` this is `HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` read at `f = 1`:
`β_{1,n} = y^{n-1}` (`HJO.Mellit.slopeWord_one_left`) makes `Ξ^{(1)}_{1,n}(y_1) = (-1)^{n-1}y_1^n`,
and `HJO.Sweep.dminus_auxVar_pow` turns that into `(-1)^{n-1}(-1)^n e_n = -e_n`, whose `(-1)^{n+1}`
multiple is `(-1)^ne_n = D_n(1)`.

**`z_1` on `V_1` is a difference of two basic operators.** The whole sweep side of `(2,3)` collapses
through two proved statements: `HJO.Sweep.dop_succ_eq_dminus_auxVar_pow_dplusStar`
(`C(D_{m+1}f) = d_-(y_1^{m+1}d^*_+(Cf))`) and `HJO.Sweep.dminus_auxVar_pow_mul_C` together with
`HJO.Sweep.bop_natCast` (`d_-(y_1^i · Cf) = C(B_i f) = C(D^{q,0}_i f)`, the Hall--Littlewood
operator being the basic operator at `u = 0`). The first is the `d^*_+d_-` half of `z_1`, the second
the `d_-d^*_+` half, and what survives is

`ct(d_-(Ξ^{(1)}_{2,3}(y_1))) = (qu)^{-1}\frac{q}{1-q}\,(D^{q,u}_1(e_2) - D^{q,0}_1(e_2))`,

with the scalar `(qu)^{-1}q/(1-q)` exactly cancelling the factor `(1-q)u` that the difference
carries. That is the mechanism, and it is the reason the identity is scalar-tight rather than
approximately right.

## The commutator lead, and why it is not a proof strategy

Both sides are commutators, and the counts match: `β_{a,b}` has `a - 1` letters `z` and `b - 1`
letters `y` (`HJO.Mellit.slopeWord_one_left`, `HJO.Mellit.slopeWord_one_right` at the boundaries),
and the recursion of `HJO.Sym.Qop` performs exactly `a - 1` commutators before bottoming out at
`Q_{1,n} = D_n`. But the correspondence is **not** term by term, and `(2,3)` is already a
counterexample to the term-by-term reading. There the `Q`-side commutator is
`Q_{2,3} = M^{-1}(Q_{1,2}Q_{1,1} - Q_{1,1}Q_{1,2})`, whose two summands at the vacuum are
`-D_2(e_1)` and `-D_1(e_2)`; the sweep-side commutator `d^*_+d_- - d_-d^*_+` contributes
`D^{q,u}_1(e_2)` and `D^{q,0}_1(e_2)`. The first summands agree up to sign, but
`D_2(e_1) = e_1e_2 - M e_3` and `D^{q,0}_1(e_2) = -q(e_1e_2 - (1-q)e_3)` are not proportional —
their `e_3` coefficients differ off `u = 0`. The identity holds only after the two summands are
added. So the commutator shape is real and is what makes the two sides comparable, but no
substitution of "commutator for `z`" proves it; the matching is a genuine theorem about the
relations `z_1` satisfies against multiplication by `y_1`.

## The genericity condition

`HJO.Sym.qop_two_three_apply_one` needs `(1-q)(1-u) ≠ 0` — the normalisation `M^{-1}` of
`HJO.Sym.Qop`. `HJO.Mellit.constantCoeff_lowerRun_stageWordTotal_two_three` needs `q ≠ 0`, `u ≠ 0`
and `q ≠ 1` — the `(qu)^{-1}` of `HJO.Sweep.slopeOperator` and the `(1-q)^{-1}` of `HJO.Sweep.zop`.
So the identity as a whole wants

`q ∉ {0, 1}`, `u ∉ {0, 1}`,

all of which `HJO.Mellit.not_degenerate_of_algebraicIndependent` and the two hypotheses of
`HJO.Mellit.qop_apply_one_of_lhsComputes` supply from the hypothesis
`AlgebraicIndependent ℤ ![q, u]`.

`HJO.Mellit.not_lhsBase_two_three_of_u_eq_one` shows `u ≠ 1` is **not** decoration: at `u = 1` and
`q ∉ {0, 1}` the identity is false, the slope operator vanishing
(`HJO.Regression.qop_eq_zero_at_one`) while the sweep side does not. This is a regime the earlier
refutation does not reach: `HJO.Mellit.not_lhsComputes_of_degenerate` needs `qu ∈ {0, 1}`, and at
`u = 1` with `q ∉ {0,1}` the product `qu = q` is neither. It is the same defect class as
`HJO.Mellit.not_sweepAppend_one_left` — an inverse of a vanishing scalar silently becoming zero.

## The general-slope statement

`HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` is the `a = 1` identity and says nothing about
`HJO.Sym.Qop`; the general-slope statement these results are the `(2,3)` instance of is not
formalized. That statement, stated for a general `f` so that it can be fed through the commutator
recursion of `HJO.Sym.Qop`, is

`C(Q_{a,b}f) = (-1)^{b+1} d_-(Ξ^{(1)}_{a,b}(y_1 · d^*_+(Cf)))`   for coprime `a, b ≥ 1`,

whose `a = 1` case is exactly `HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` (both signs
cancelling as above).

The evaluation of `HJO.Sweep.zopOneStar q u 1` on a general element of `V_1`, and not only on the
monomials `y_1^m` with trivial `Λ`-coefficient, is available:

* `HJO.Sweep.zopOneStar_one_of_mem_piece` (`HJO/Shuffle/MellitZopOneV1.lean`) — a general
  element of `V_1`;
* `HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C` — monomials with arbitrary `Λ`-coefficient;
* `HJO.Sweep.zopOneStar_one_auxVar_mul_of_mem_piece`
  (`HJO/Shuffle/MellitStarVertex.lean`) — the `y_1`-shift form on all of `V_1`.

**What remains.** `HJO.Sweep.auxVar_mul_dplusStar_dminus_of_mem_piece_one`
(`MellitStarVertex.lean`) gives `P = qu·YZ - ZY` on `V_1`, so reading it as `ZY = qu·YZ - P`
straightens every word to the **straight monomials** `πY^aZ^bΦ` plus `P`-insertions, whose matrix
elements factor into products the induction supplies. So the clause family is *equivalent* to
evaluating `πY^aZ^bΦ` for `a, b ≥ 1`, and that is the remaining content. Three facts about it:

* the `a`-row is `HJO.Mellit.lhsSlope_one_left` (`MellitLhsSlopeMediant.lean`), proved;
* the `b`-row **is** the `(a,1)` column with `a ≥ 2` that `MellitLhsSlopeMediant.lean`
  records as untreated, so that column is **required**, not optional, even though the mediant
  route it belongs to is circular;
* these are **not** the slope operator at the corresponding non-coprime slope. Numerically,
  `πYZΦ(1) = -e_2` against `-Q_{2,2}(1) = -e_1^2 - (68/77)e_2` at `(q,u) = (3/7, 5/11)`. The doubled
  slope has to come from `HJO.Sweep.exists_slopeActions` (`HJO/Shuffle/SlopeActions.lean`), not from
  width-one straight monomials. This numerical counterexample is not formalized here.
-/

@[expose] public section

open HJO.Sym HJO.Sweep HJO.Mellit HJO.Bglx

namespace HJO.Bglx

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The kernel coefficients of the parameter alphabet in closed form -/

/-- `κ(e_1) = M = (1-q)(1-u)`, read off the `n = 1` kernel recursion
`HJO.Bglx.paramPleth_elemSymm_one`. -/
theorem paramPleth_elemSymm_one_eq (q u : L) :
    paramPleth q u (elemSymm L 1) = (1 - q) * (1 - u) := by
  have h := paramPleth_elemSymm_one (K := L) q u
  rw [paramPleth_elemSymm_zero] at h
  linear_combination h

/-- `κ(e_2) = -(q+u)M`, read off the `n = 0` kernel recursion
`HJO.Bglx.paramPleth_elemSymm_add_two`. -/
theorem paramPleth_elemSymm_two_eq (q u : L) :
    paramPleth q u (elemSymm L 2) = -((q + u) * ((1 - q) * (1 - u))) := by
  have h := paramPleth_elemSymm_add_two (K := L) q u 0
  rw [paramPleth_elemSymm_zero, show (0 : ℕ) + 1 = 1 from rfl, paramPleth_elemSymm_one_eq,
    show (0 : ℕ) + 2 = 2 from rfl] at h
  simp only [ite_true] at h
  linear_combination h

end HJO.Bglx

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The basic operator on `e_2`, and the slope operator `Q_{2,3}` at the vacuum -/

/-- **`D_1(e_2) = (M - 1)e_1e_2 + (q+u)M e_3`.** The displacement of `e_2` is the convolution
`∑_{s ≤ 2} e_{2-s}κ(e_s)w^s` of `HJO.Bglx.plethShift_elemSymm`, and `HJO.Sym.DopInt` pairs its `w^s`
coefficient with `(-1)^{1+s}e_{1+s}`; the three kernel coefficients are `1`, `M` and `-(q+u)M`. -/
theorem dop_one_elemSymm_two (q u : L) :
    Dop q u 1 (elemSymm L 2)
      = ((1 - q) * (1 - u) - 1) • (elemSymm L 1 * elemSymm L 2)
        + ((q + u) * ((1 - q) * (1 - u))) • elemSymm L 3 := by
  rw [dop_apply, plethShift_elemSymm q u 2, map_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Polynomial.C_mul_X_pow_eq_monomial, coeffPairing_monomial]
  rw [paramPleth_elemSymm_one_eq, paramPleth_elemSymm_two_eq, paramPleth_elemSymm_zero]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_one,
    Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- **`Q_{2,3}(1) = -e_1e_2 + (1-q-u)e_3`.**

`(2,3)` is coprime with `Split 2 3 = (1,1)`, so `HJO.Sym.Qop`'s primitive recursion reads
`Q_{2,3} = M^{-1}(Q_{1,2}Q_{1,1} - Q_{1,1}Q_{1,2}) = M^{-1}(D_2D_1 - D_1D_2)`. At the vacuum
`D_1(1) = -e_1` and `D_2(1) = e_2` (`HJO.Sym.dop_apply_one`), the first branch is
`-D_2(e_1) = -e_1e_2 + M e_3` by `HJO.Sym.dop_elemSymm_one_mul`, and the second is
`HJO.Sym.dop_one_elemSymm_two`. The bracket comes out as `M` times the stated value, which is
where `M ≠ 0` is spent and nowhere else. -/
theorem qop_two_three_apply_one (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 2 3 (1 : Lambda L)
      = -(elemSymm L 1 * elemSymm L 2) + (1 - q - u) • elemSymm L 3 := by
  have hsplit : Split 2 3 = (1, 1) := by decide
  have hQ := qop_of_coprime q u (m := 2) (n := 3) (by norm_num) (by decide)
  rw [hsplit] at hQ
  norm_num only at hQ
  have hd1 : Dop q u 1 (1 : Lambda L) = -elemSymm L 1 := by rw [dop_apply_one]; ring
  have hd2 : Dop q u 2 (1 : Lambda L) = elemSymm L 2 := by rw [dop_apply_one]; ring
  have hd3 : Dop q u 3 (1 : Lambda L) = -elemSymm L 3 := by rw [dop_apply_one]; ring
  have hd2e1 : Dop q u 2 (elemSymm L 1)
      = elemSymm L 1 * elemSymm L 2 - ((1 - q) * (1 - u)) • elemSymm L 3 := by
    have h := dop_elemSymm_one_mul q u 2 (1 : Lambda L)
    rw [mul_one, hd2, hd3, smul_neg, ← sub_eq_add_neg] at h
    exact h
  have key : (Qop q u 1 2 * Qop q u 1 1 - Qop q u 1 1 * Qop q u 1 2) (1 : Lambda L)
      = ((1 - q) * (1 - u)) •
        (-(elemSymm L 1 * elemSymm L 2) + (1 - q - u) • elemSymm L 3) := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply, qop_one]
    rw [hd1, hd2, map_neg, hd2e1, dop_one_elemSymm_two]
    simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_one]
    ring
  rw [hQ, LinearMap.smul_apply, key, inv_smul_smul₀ hM]

/-! ### An evaluation of `Λ` separating `e_3` from `e_1e_2` -/

/-- The evaluation of `Λ` sending `p_3` to `1` and every other power sum to `0`. `HJO.Sym.Lambda` is
the *free* polynomial algebra on the power-sum symbols, so no verification is owed. It kills `e_1`
and not `e_3`, which is what separates the two degree-`3` monomials the base case produces. -/
noncomputable def evalThree (L : Type*) [Field L] [Algebra ℚ L] : Lambda L →ₐ[L] L :=
  MvPolynomial.aeval fun i => if i = 2 then (1 : L) else 0

theorem evalThree_elemSymm_one : evalThree L (elemSymm L 1) = 0 := by
  rw [elemSymm_one_eq_X, evalThree, MvPolynomial.aeval_X]
  norm_num

theorem evalThree_elemSymm_three :
    evalThree L (elemSymm L 3) = algebraMap ℚ L ((2 + 1 : ℚ))⁻¹ := by
  have hX : ∀ i : ℕ, evalThree L (MvPolynomial.X i : Lambda L) = if i = 2 then (1 : L) else 0 :=
    fun i => MvPolynomial.aeval_X _ i
  rw [show (3 : ℕ) = 2 + 1 from rfl, elemSymm, map_mul]
  rw [map_sum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp only [powerSum, elemSymm_zero, Nat.sub_zero, Nat.sub_self, map_mul, map_pow, map_neg,
    map_one, hX, MvPolynomial.algHom_C]
  norm_num

end HJO.Sym

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### `z_1` on the square of the first auxiliary variable

This is the only evaluation of `HJO.Sweep.zopOneStar` the `a = 2` word needs, and the precise
point at which the general `a` is harder: the argument `y_1^2` has trivial `Λ`-coefficient, so
`τ^-` and `τ` act on nothing and the second half of the commutator returns the first half's input
unchanged. On a general `C(A)y_1^m` the second half is a *two-letter* displacement of `A`, by
`(q-1)uy_1 - (q-1)y_2`, followed by an extraction in `y_2` — that evaluation is
`HJO.Sweep.zopOneStar_one_of_mem_piece`, and it is not used here.
-/

/-- **`z_1(y_1^2) = q/(1-q)·(d^*_+(Ce_2) - Ce_2)` on `V_1`.**

`HJO.Sweep.zop` at `k = 1` is `q/(1-q)(d^*_+d_- - d_-d^*_+)T^*_{1↘1}`, and the train is empty
(`HJO.Braid.trainUp_self`). The two halves are computed by `HJO.Sweep.dminus_auxVar_pow` and
`HJO.Sweep.dplusStar_auxVar_pow`: `d_-(y_1^2) = e_2`, and `d^*_+(y_1^2) = y_2^2` whose `d_-` at
index `2` is `e_2` again. So the second half contributes the undisplaced `e_2`, and the whole
operator is the difference between adding the letter `(q-1)uy_1` and not adding it. -/
theorem zopOneStar_one_auxVar_sq (q u : L) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2)
      = (q / (1 - q)) • (dplusStar q u 0 (MvPolynomial.C (elemSymm L 2))
          - MvPolynomial.C (elemSymm L 2)) := by
  rw [zopOneStar, show trainUpEnd q 1 1 = 1 from Braid.trainUp_self _ _ 1, mul_one]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, pow_one,
    Nat.sub_self]
  rw [show dminus q 1 ((auxVar 1 : Total L) ^ 2) = MvPolynomial.C (elemSymm L 2) from by
      simpa using dminus_auxVar_pow q 0 2,
    dplusStar_auxVar_pow q u (i := 1) (k := 1) le_rfl le_rfl,
    show dminus q 2 ((auxVar 2 : Total L) ^ 2) = MvPolynomial.C (elemSymm L 2) from by
      simpa using dminus_auxVar_pow q 1 2]

/-! ### The slope operator at `(2, 3)` -/

/-- **`Ξ^{(1)}_{2,3} = (-y_1)·(qu)^{-1}z_1·(-y_1)`**, the word `β_{2,3} = yzy`
(`HJO.Mellit.slopeWord_two_three`) read by `HJO.Sweep.slopeOperator` with the head outermost. -/
theorem slopeOperator_two_three (q u : L) :
    slopeOperator q u 1 2 3
      = (-LinearMap.mulLeft L (auxVar 1 : Total L)) * ((q * u)⁻¹ • zop q u 1 1)
        * (-LinearMap.mulLeft L (auxVar 1 : Total L)) := by
  rw [slopeOperator, Mellit.slopeWord_two_three]
  simp [mul_assoc]

/-- **`Ξ^{(1)}_{2,3}(y_1) = (qu)^{-1}\frac{q}{1-q}(y_1d^*_+(Ce_2) - y_1Ce_2)`.** The two sign
factors of the two `y` letters cancel, and `HJO.Sweep.zopOneStar_one_auxVar_sq` supplies the
middle. Nothing here divides by a quantity that can vanish: the scalars are carried symbolically. -/
theorem slopeOperator_two_three_auxVar (q u : L) :
    slopeOperator q u 1 2 3 (auxVar 1 : Total L)
      = ((q * u)⁻¹ * (q / (1 - q))) •
          ((auxVar 1 : Total L) * dplusStar q u 0 (MvPolynomial.C (elemSymm L 2))
            - (auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 2)) := by
  rw [slopeOperator_two_three]
  simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply,
    LinearMap.smul_apply, zop_one]
  rw [show (auxVar 1 : Total L) * (auxVar 1 : Total L) = (auxVar 1 : Total L) ^ 2 from (sq _).symm]
  rw [show zopOneStar q u 1 (-(auxVar 1 : Total L) ^ 2)
      = -((q / (1 - q)) • (dplusStar q u 0 (MvPolynomial.C (elemSymm L 2))
          - MvPolynomial.C (elemSymm L 2))) from by
    rw [← zopOneStar_one_auxVar_sq, ← map_neg]]
  simp only [smul_neg, neg_neg, mul_neg, mul_smul_comm, smul_smul, mul_sub]

end HJO.Sweep

namespace HJO.Mellit

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The sweep side of the base case at `(2, 3)` -/

/-- **The sweep side of the base case at `(a,b) = (2,3)`:**
`ct(d_-(G_1(1))) = -e_1e_2 + (1-q-u)e_3`.

The stage word at `α = (1)` is `HJO.Mellit.stageWordTotal_singleton_one`; `d^*_+` fixes the unit,
the descending train at `(1,1)` is the identity, and the `(-1)^{a-1}` of the stage cancels the
outer sign. What is left is `Ξ^{(1)}_{2,3}(y_1)` under one lowering operator, and the two halves of
`z_1` are read by the two proved identities: `d_-(y_1d^*_+(Ce_2)) = C(D^{q,u}_1e_2)` by
`HJO.Sweep.dop_succ_eq_dminus_auxVar_pow_dplusStar`, and
`d_-(y_1Ce_2) = C(B_1e_2) = C(D^{q,0}_1e_2)` by `HJO.Sweep.dminus_auxVar_pow_mul_C` with
`HJO.Sweep.bop_natCast`. The difference of the two basic
operators carries a factor `(1-q)u` which the scalar `(qu)^{-1}q/(1-q)` cancels exactly.

The hypotheses are the three inverses the word carries: `(qu)^{-1}` from
`HJO.Sweep.slopeOperator` and `(1-q)^{-1}` from `HJO.Sweep.zop`. No hypothesis on `u - 1`: the
sweep side is a theorem at `u = 1`, which is what makes
`HJO.Mellit.not_lhsBase_two_three_of_u_eq_one` available. -/
theorem constantCoeff_lowerRun_stageWordTotal_two_three (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    MvPolynomial.constantCoeff (lowerRun q 1 (stageWordTotal q u 2 3 [1]))
      = -(elemSymm L 1 * elemSymm L 2) + (1 - q - u) • elemSymm L 3 := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hstage : stageWordTotal q u 2 3 [1]
      = ((q * u)⁻¹ * (q / (1 - q))) •
          ((auxVar 1 : Total L) * dplusStar q u 0 (MvPolynomial.C (elemSymm L 2))
            - (auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 2)) := by
    rw [stageWordTotal_singleton_one, dplusStar_one, mul_one,
      show trainDownEnd q 1 1 = 1 from Braid.trainDown_self _ _ 1,
      Module.End.one_apply, slopeOperator_two_three_auxVar q u]
    norm_num
  rw [hstage, show lowerRun q 1 = dminus q 1 from by simp [lowerRun], map_smul, map_sub]
  rw [show dminus q 1 ((auxVar 1 : Total L) *
        dplusStar q u 0 (MvPolynomial.C (elemSymm L 2)))
      = MvPolynomial.C (Dop q u 1 (elemSymm L 2)) from by
    simpa using (dop_succ_eq_dminus_auxVar_pow_dplusStar q u 0 (elemSymm L 2)).symm]
  rw [show dminus q 1 ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 2))
      = MvPolynomial.C (Dop q 0 1 (elemSymm L 2)) from by
    rw [← bop_natCast q 1]
    simpa using dminus_auxVar_pow_mul_C q 0 1 (elemSymm L 2)]
  rw [← map_sub, MvPolynomial.constantCoeff_smul, MvPolynomial.constantCoeff_C,
    dop_one_elemSymm_two q u, dop_one_elemSymm_two q 0]
  match_scalars
  · field_simp
    ring
  · field_simp
    ring

/-! ### The base case at `(a, b) = (2, 3)`, and its failure at `u = 1` -/

/-- **The base case of `HJO.Mellit.lhsRewrite_sweepWitness` holds at `(a, b) = (2, 3)`.**

This is the conclusion of `HJO.Mellit.qop_apply_one_of_lhsComputes` at `(a,b) = (2,3)`, proved in
`Λ` before any realisation is applied — so the stated form of the clause follows by `congrArg ι`,
and the identity is not an artefact of what `ι` can see. Both sides are
`-e_1e_2 + (1-q-u)e_3`; the two signs `(-1)^b` and `(-1)^{a-1}` agree at `(2,3)`, so the common
value is the slope operator's own.

This is the smallest instance of the clause with `a > 1`, the case where the slope word first
carries a letter `z` and the recursion of `HJO.Sym.Qop` first performs a commutator. -/
theorem lhsBase_two_three (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (hu1 : u ≠ 1) :
    (-1 : L) ^ (3 : ℕ) • Qop q u 2 3 (1 : Lambda L)
      = (-1 : L) ^ (2 - 1 : ℕ) •
        MvPolynomial.constantCoeff (lowerRun q 1 (stageWordTotal q u 2 3 [1])) := by
  rw [qop_two_three_apply_one (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hq1))
      (sub_ne_zero.mpr (Ne.symm hu1))),
    constantCoeff_lowerRun_stageWordTotal_two_three hq0 hu0 hq1]
  norm_num

/-- **The base case is FALSE at `u = 1`, for every `q ∉ {0, 1}`.**

At `u = 1` the normalisation `((1-q)(1-u))⁻¹` of `HJO.Sym.Qop` is the zero map, so `Q_{2,3} = 0`
(`HJO.Regression.qop_eq_zero_at_one`); the sweep side is untouched, needing only `q ∉ {0,1}` and
`u ≠ 0`, and equals `-e_1e_2 - q e_3`, which `HJO.Sym.evalThree` sees as `q ≠ 0`.

So the genericity hypothesis `(1-q)(1-u) ≠ 0` of `HJO.Mellit.lhsRewrite_sweepWitness` is necessary
already at the smallest instance with `a > 1`, and necessary on a *curve* rather than at isolated
points: `HJO.Mellit.not_lhsComputes_of_degenerate` reaches only `qu ∈ {0,1}`, which at `u = 1` means
`q ∈ {0,1}` — exactly the two values excluded here. -/
theorem not_lhsBase_two_three_of_u_eq_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    (-1 : L) ^ (3 : ℕ) • Qop q 1 2 3 (1 : Lambda L)
      ≠ (-1 : L) ^ (2 - 1 : ℕ) •
        MvPolynomial.constantCoeff (lowerRun q 1 (stageWordTotal q 1 2 3 [1])) := by
  rw [HJO.Regression.qop_eq_zero_at_one q (le_refl 2) 3, LinearMap.zero_apply, smul_zero,
    constantCoeff_lowerRun_stageWordTotal_two_three hq0 one_ne_zero hq1]
  have h3 : algebraMap ℚ L ((2 + 1 : ℚ))⁻¹ ≠ 0 := by
    refine (map_ne_zero_iff _ (algebraMap ℚ L).injective).2 ?_
    norm_num
  intro h
  have hev := congrArg (evalThree L) h
  simp only [map_zero, map_smul, map_add, map_neg, map_mul, evalThree_elemSymm_one,
    evalThree_elemSymm_three, smul_eq_mul, zero_mul, neg_zero, zero_add] at hev
  exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (one_ne_zero (α := L))))
    (mul_ne_zero (fun hc => hq0 (by linear_combination -hc)) h3)) hev.symm

end HJO.Mellit
