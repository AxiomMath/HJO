/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitLhsSlopeBase
public meta import HJO.Attr

/-! # `Q_{3,4}` at the vacuum: the slope side of the `(3,4)` gluing check

`HJO/Shuffle/MellitZopOneV1.lean`'s module docstring reduces the general-slope gluing identity
to an operator identity on `V_1`, whose first real test is **at `(a,b) = (3,4)`** — `(3,4)` being
the smallest slope whose word `β_{3,4} = yzyzy` applies its second `z` to an element with nontrivial
`Λ`-coefficient. This file computes the `Q` side of that check in closed form.

## The main result

`HJO.Sym.qop_three_four_apply_one`:

`Q_{3,4}(1) = e_1^2e_2 + (q+u-1)e_2^2 + (q^2+qu+u^2-1)e_1e_3`
`             + (1-q-u-q^2-u^2+q^3+q^2u+qu^2+u^3)e_4`.

`Split 3 4 = (1,1)`, so `HJO.Sym.Qop`'s primitive recursion reads
`Q_{3,4} = M^{-1}(Q_{2,3}Q_{1,1} - Q_{1,1}Q_{2,3}) = M^{-1}(Q_{2,3}D_1 - D_1Q_{2,3})`, and the
two branches at the vacuum are `Q_{2,3}(-e_1)` and `D_1` of
`HJO.Sym.qop_two_three_apply_one`. As at `(2,3)` the bracket comes out as `M` times the stated
value, which is where `M ≠ 0` is spent; that the answer is a *polynomial* in `q` and `u` is the
first nontrivial thing here, since `Q_{3,4}` carries two nested `M^{-1}`.

The coefficients are the complete homogeneous symmetric functions of the two parameters: with
`h_j = ∑_{i ≤ j} q^iu^{j-i}`, they are `h_0`, `h_1 - h_0`, `h_2 - h_0` and
`h_3 - h_2 + qu - h_1 + h_0`. The same family governs the kernel, by
`HJO.Bglx.paramPleth_elemSymm_three_eq` below and its two predecessors:
`κ(e_n) = (-1)^{n-1}h_{n-1}M` for `n ≥ 1`.

## The general `Dop` on an elementary symmetric function

The computation is organised around `HJO.Sym.dop_elemSymm`, the `(k, r)`-general form of
`HJO.Sym.dop_one_elemSymm_two`: `HJO.Sym.DopInt` pairs the `w^s` coefficient of the displacement
with `(-1)^{k+s}e_{k+s}`, and `HJO.Bglx.plethShift_elemSymm` says that coefficient is
`e_{r-s}κ(e_s)`. Every `Dop` value below is a `Finset.range` unfolding of it against the four kernel
values `κ(e_0) = 1`, `κ(e_1) = M`, `κ(e_2) = -(q+u)M`, `κ(e_3) = (q^2+qu+u^2)M`. The one place it
is *not* used is on `e_1 · f`, where the Pieri rule `HJO.Sym.dop_elemSymm_one_mul` is
shorter.

## What this settles, and what it does not

**This is the `Q` half of the `(3,4)` check only.** The sweep half `ct(d_-(Ξ^{(1)}_{3,4}(y_1)))` is
*not* computed here; it is `HJO.Mellit.constantCoeff_lowerRun_stageWordTotal_three_four`
(`HJO/Shuffle/MellitLhsSlopeThreeFour.lean`), and it equals `-Q_{3,4}(1)` — exactly the value
`HJO.Mellit.stageWordTotal_singleton_one`'s sign bookkeeping demands, the clause at `a = 3`, `b = 4`
reading `Q_{3,4}(1) = -ct(d_-(Ξ^{(1)}_{3,4}(y_1)))`. The two halves are matched in
`HJO.Mellit.lhsBase_three_four`. The statement below is written in the same degree-`4`
`e`-monomial basis the sweep side lands in.

The same computation settles the load-bearing structural question of the reduction. Writing
`P := y_1d^*_+{}^{(0)}d_-^{(1)}` and `N := d_-^{(2)}d^*_+{}^{(1)}` on `V_1`, so that
`y_1z_1 = q/(1-q)(P - y_1N)`:

* the `N` term is **nonzero and load-bearing** — dropping it breaks the `(3,4)` identity, the
  defect being exactly the `N` contribution, which is not zero for any `q, u`;
* both contributions have denominator `q^2u(1-q)` and neither is a polynomial on its own, only their
  sum is;
* the matching is **not** term by term: the `P` contribution is not `M^{-1}Q_{2,3}D_1(1)`, the `N`
  contribution is not `-M^{-1}D_1Q_{2,3}(1)`, and neither crossed pairing holds either.

That is the same mechanism as at `(2,3)`, recorded in
`HJO/Shuffle/MellitLhsSlopeBase.lean`'s docstring: the identity holds only after the two
summands are added, and no substitution of "commutator for `z`" reproduces it.

## Genericity

`M = (1-q)(1-u) ≠ 0`, and nothing else. `HJO.Sym.qop_two_three_apply_one` needs the same and no
more, and the two nested normalisations of `HJO.Sym.Qop` are the only inverses in this computation —
no `(qu)^{-1}` occurs, that being the slope operator's and hence the sweep side's. The sweep side
needs `q ∉ {0,1}` and `u ≠ 0` besides, so the `(3,4)` clause as a whole wants what the `(2,3)`
clause wants: `q ∉ {0,1}` and `u ∉ {0,1}`, with `u ≠ 1` necessary on a curve rather than at isolated
points by `HJO.Mellit.not_lhsBase_two_three_of_u_eq_one`.
-/

@[expose] public section

open HJO.Sym HJO.Bglx

namespace HJO.Bglx

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The third kernel coefficient -/

/-- **`κ(e_3) = (q^2+qu+u^2)M`**, from the kernel recursion
`HJO.Bglx.paramPleth_elemSymm_add_two` at `n = 1`, whose inhomogeneous term vanishes there. With
`HJO.Bglx.paramPleth_elemSymm_one_eq` and `HJO.Bglx.paramPleth_elemSymm_two_eq` this completes the
pattern `κ(e_n) = (-1)^{n-1}h_{n-1}M`, with `h_j` the complete homogeneous symmetric function of
`q, u` of degree `j`. -/
theorem paramPleth_elemSymm_three_eq (q u : L) :
    paramPleth q u (elemSymm L 3) = (q ^ 2 + q * u + u ^ 2) * ((1 - q) * (1 - u)) := by
  have h := paramPleth_elemSymm_add_two (K := L) q u 1
  rw [show (1 : ℕ) + 2 = 3 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
    paramPleth_elemSymm_two_eq, paramPleth_elemSymm_one_eq] at h
  simp only [one_ne_zero, ite_false] at h
  linear_combination h

end HJO.Bglx

namespace HJO.Mellit

/-! ### Why `(3,4)` is the instance to check -/

/-- **`β_{3,4} = y z y z y`**, computed outright. This is the smallest slope word with two `z`
letters, and therefore the smallest at which a `z` meets an element of `V_1` with a nontrivial
`Λ`-coefficient: the first `z` acts on `y_1^2`, as at `(2,3)`
(`HJO.Mellit.slopeWord_two_three`), but the second acts on `y_1·d^*_+{}^{(0)}(Ce_2) - y_1Ce_2`,
whose `y_1`-coefficients are `(q-1)ue_1` and `(1-q)u^2`. That is the case
`HJO.Sweep.zopOneStar_one_auxVar_sq` cannot reach and
`HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C` supplies, and it is why the general-slope gluing
identity has to be checked here. -/
theorem slopeWord_three_four : slopeWord 3 4 = [.y, .z, .y, .z, .y] := by decide

end HJO.Mellit

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The split of `(3,4)`, and the two factorisations it induces -/

/-- **`Split 3 4 = (1,1)`.** So `HJO.Sym.Qop`'s primitive recursion at `(3,4)` is
`Q_{3,4} = M^{-1}(Q_{2,3}D_1 - D_1Q_{2,3})`, `Q_{1,1}` being `D_1` by `HJO.Sym.qop_one`.

The mediant factorisation of the *word* reads the same parents the other way round:
`HJO.Mellit.slopeEval_mediant` at `(m_1,n_1) = (2,3)`, `(m_2,n_2) = (1,1)` — whose determinant
condition `m_2n_1 = m_1n_2 + 1` is `3 = 2 + 1` — gives
`Ξ_{3,4} = Ξ_{1,1}·Y·Z·Ξ_{2,3} = Y·Z·Ξ_{2,3}`, since `Ξ_{1,1} = 1`
(`HJO.Mellit.slopeEval_one_one`). That is the `yzyzy` of `HJO.Mellit.slopeWord_three_four`, and it
is the reason the `(3,4)` sweep side is one `YZ` step past
`HJO.Sweep.slopeOperator_two_three_auxVar`: in the reduction's notation the outer factor `Ξ_2` is
the *identity* here, so the whole content of the step is carried by `P - y_1N` against
`Ξ_1 = Ξ_{2,3}`. -/
theorem split_three_four : Split 3 4 = ((1 : ℕ), (1 : ℕ)) := by decide

/-! ### The basic operator on an elementary symmetric function, in general -/

/-- **`D_k(e_r) = ∑_{s ≤ r} e_{r-s}κ(e_s)(-1)^{k+s}e_{k+s}`.**

The `(k, r)`-general form of `HJO.Sym.dop_one_elemSymm_two`: `HJO.Sym.DopInt` pairs the `w^s`
coefficient of the displacement with `(-1)^{k+s}e_{k+s}`, and `HJO.Bglx.plethShift_elemSymm` says
that coefficient is `e_{r-s}κ(e_s)`. Every evaluation below is a `Finset.range` unfolding of
this. -/
theorem dop_elemSymm (q u : L) (k r : ℕ) :
    Dop q u k (elemSymm L r)
      = ∑ s ∈ Finset.range (r + 1),
          elemSymm L (r - s) * MvPolynomial.C (paramPleth q u (elemSymm L s))
            * ((-1) ^ (k + s) * elemSymm L (k + s)) := by
  rw [dop_apply, plethShift_elemSymm q u r, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Polynomial.C_mul_X_pow_eq_monomial, coeffPairing_monomial]

/-- **`D_3(e_1) = -e_1e_3 + Me_4`**, the `r = 1` convolution at `k = 3`. The `k = 1` case of the
same convolution is `HJO.Sym.dop_one_elemSymm_one`
(`HJO/Shuffle/MellitNablaConjStarRefuted.lean`), `D_1(e_1) = -e_1^2 + Me_2`, which is used
below and is the smallest check that `HJO.Sym.dop_elemSymm` unfolds the way this proof assumes. -/
theorem dop_three_elemSymm_one (q u : L) :
    Dop q u 3 (elemSymm L 1)
      = -(elemSymm L 1 * elemSymm L 3) + ((1 - q) * (1 - u)) • elemSymm L 4 := by
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    paramPleth_elemSymm_zero, paramPleth_elemSymm_one_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one, Nat.sub_zero, Nat.sub_self,
    elemSymm_zero]
  norm_num

/-- **`D_2(e_2) = e_2^2 - Me_1e_3 - (q+u)Me_4`.** The pairing family at `k = 2` is `(-1)^se_{2+s}`,
so all three signs are `+`, and the three kernel values needed are the known
`κ(e_0), κ(e_1), κ(e_2)`. -/
theorem dop_two_elemSymm_two (q u : L) :
    Dop q u 2 (elemSymm L 2)
      = elemSymm L 2 * elemSymm L 2 - ((1 - q) * (1 - u)) • (elemSymm L 1 * elemSymm L 3)
        - ((q + u) * ((1 - q) * (1 - u))) • elemSymm L 4 := by
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, paramPleth_elemSymm_zero, paramPleth_elemSymm_one_eq,
    paramPleth_elemSymm_two_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_neg, map_sub, map_add, map_mul, map_one,
    Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-- **`D_1(e_3) = Me_2^2 + (-1+(q+u)M)e_1e_3 + (q^2+qu+u^2)Me_4`.** The only evaluation here that
needs `HJO.Bglx.paramPleth_elemSymm_three_eq`; the four signs are `(-1)^{1+s}`, `s = 0,1,2,3`. -/
theorem dop_one_elemSymm_three (q u : L) :
    Dop q u 1 (elemSymm L 3)
      = ((1 - q) * (1 - u)) • (elemSymm L 2 * elemSymm L 2)
        + (-1 + (q + u) * ((1 - q) * (1 - u))) • (elemSymm L 1 * elemSymm L 3)
        + ((q ^ 2 + q * u + u ^ 2) * ((1 - q) * (1 - u))) • elemSymm L 4 := by
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, paramPleth_elemSymm_zero,
    paramPleth_elemSymm_one_eq, paramPleth_elemSymm_two_eq, paramPleth_elemSymm_three_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_neg, map_sub, map_add, map_mul, map_one, map_pow,
    Nat.sub_zero, Nat.sub_self, elemSymm_zero]
  norm_num
  ring

/-! ### `D_2(e_1)` and the two Pieri expansions the recursion needs -/

/-- **`D_2(e_1) = e_1e_2 - Me_3`.** The Pieri rule `HJO.Sym.dop_elemSymm_one_mul` at `f = 1`, as in
the proof of `HJO.Sym.qop_two_three_apply_one`. -/
theorem dop_two_elemSymm_one (q u : L) :
    Dop q u 2 (elemSymm L 1)
      = elemSymm L 1 * elemSymm L 2 - ((1 - q) * (1 - u)) • elemSymm L 3 := by
  have hd2 : Dop q u 2 (1 : Lambda L) = elemSymm L 2 := by rw [dop_apply_one]; ring
  have hd3 : Dop q u 3 (1 : Lambda L) = -elemSymm L 3 := by rw [dop_apply_one]; ring
  have h := dop_elemSymm_one_mul q u 2 (1 : Lambda L)
  rw [mul_one, hd2, hd3, smul_neg, ← sub_eq_add_neg] at h
  exact h

/-- **`D_2(D_1e_1) = -e_1^2e_2 + Me_2^2 + (2M - M^2)e_1e_3 - (1+q+u)M^2e_4`**, the first branch of
the `(2,3)` commutator away from the vacuum. `D_1e_1` is `HJO.Sym.dop_one_elemSymm_one`, its
`e_1 · e_1` part is expanded by the Pieri rule against `HJO.Sym.dop_two_elemSymm_one` and
`HJO.Sym.dop_three_elemSymm_one`, and its `e_2` part by `HJO.Sym.dop_two_elemSymm_two`. -/
theorem dop_two_dop_one_elemSymm_one (q u : L) :
    Dop q u 2 (Dop q u 1 (elemSymm L 1))
      = -(elemSymm L 1 * elemSymm L 1 * elemSymm L 2)
        + ((1 - q) * (1 - u)) • (elemSymm L 2 * elemSymm L 2)
        + (2 * ((1 - q) * (1 - u)) - ((1 - q) * (1 - u)) ^ 2) • (elemSymm L 1 * elemSymm L 3)
        - ((1 + q + u) * ((1 - q) * (1 - u)) ^ 2) • elemSymm L 4 := by
  rw [dop_one_elemSymm_one, map_add, map_neg, map_smul, dop_two_elemSymm_two,
    dop_elemSymm_one_mul q u 2 (elemSymm L 1), dop_two_elemSymm_one, dop_three_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_one, map_pow, map_ofNat]
  ring

/-- **`D_1(D_2e_1) = (M-1)e_1^2e_2 + (M-M^2)e_2^2 + ((q+u)M - M^2 + M - (q+u)M^2)e_1e_3`**
`- ((q+u)+(q^2+qu+u^2))M^2e_4`, the second branch. `D_2e_1` is
`HJO.Sym.dop_two_elemSymm_one`, its `e_1 · e_2` part is expanded by the Pieri rule against
`HJO.Sym.dop_one_elemSymm_two` and `HJO.Sym.dop_two_elemSymm_two`, and its `e_3` part by
`HJO.Sym.dop_one_elemSymm_three`. -/
theorem dop_one_dop_two_elemSymm_one (q u : L) :
    Dop q u 1 (Dop q u 2 (elemSymm L 1))
      = (((1 - q) * (1 - u)) - 1) • (elemSymm L 1 * elemSymm L 1 * elemSymm L 2)
        + (((1 - q) * (1 - u)) - ((1 - q) * (1 - u)) ^ 2) • (elemSymm L 2 * elemSymm L 2)
        + ((q + u) * ((1 - q) * (1 - u)) - ((1 - q) * (1 - u)) ^ 2 + ((1 - q) * (1 - u))
            - (q + u) * ((1 - q) * (1 - u)) ^ 2) • (elemSymm L 1 * elemSymm L 3)
        - (((q + u) + (q ^ 2 + q * u + u ^ 2)) * ((1 - q) * (1 - u)) ^ 2) • elemSymm L 4 := by
  rw [dop_two_elemSymm_one, map_sub, map_smul, dop_one_elemSymm_three,
    dop_elemSymm_one_mul q u 1 (elemSymm L 2), dop_one_elemSymm_two, dop_two_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, map_neg, map_sub, map_add, map_mul, map_one, map_pow]
  ring

/-! ### `Q_{2,3}` on `e_1`, and `Q_{3,4}` at the vacuum -/

/-- **`Q_{2,3}(e_1) = -e_1^2e_2 + Me_2^2 + (1-q-u+(q+u)M)e_1e_3 + (q^2+qu+u^2-1)Me_4`**, the value
the `(3,4)` recursion needs from the `(2,3)` operator away from the vacuum.

`Split 2 3 = (1,1)`, so `HJO.Sym.Qop` reads `Q_{2,3} = M^{-1}(D_2D_1 - D_1D_2)`, and the two
branches are `HJO.Sym.dop_two_dop_one_elemSymm_one` and `HJO.Sym.dop_one_dop_two_elemSymm_one`. The
bracket comes out as `M` times the stated value; that is where `M ≠ 0` is spent, and it is why the
answer is a polynomial. -/
theorem qop_two_three_apply_elemSymm_one (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 2 3 (elemSymm L 1)
      = -(elemSymm L 1 * elemSymm L 1 * elemSymm L 2)
        + ((1 - q) * (1 - u)) • (elemSymm L 2 * elemSymm L 2)
        + (1 - q - u + (q + u) * ((1 - q) * (1 - u))) • (elemSymm L 1 * elemSymm L 3)
        + ((q ^ 2 + q * u + u ^ 2 - 1) * ((1 - q) * (1 - u))) • elemSymm L 4 := by
  have hsplit : Split 2 3 = (1, 1) := by decide
  have hQ := qop_of_coprime q u (m := 2) (n := 3) (by norm_num) (by decide)
  rw [hsplit] at hQ
  norm_num only at hQ
  have key : (Qop q u 1 2 * Qop q u 1 1 - Qop q u 1 1 * Qop q u 1 2) (elemSymm L 1)
      = ((1 - q) * (1 - u)) •
        (-(elemSymm L 1 * elemSymm L 1 * elemSymm L 2)
          + ((1 - q) * (1 - u)) • (elemSymm L 2 * elemSymm L 2)
          + (1 - q - u + (q + u) * ((1 - q) * (1 - u))) • (elemSymm L 1 * elemSymm L 3)
          + ((q ^ 2 + q * u + u ^ 2 - 1) * ((1 - q) * (1 - u))) • elemSymm L 4) := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply, qop_one]
    rw [dop_two_dop_one_elemSymm_one, dop_one_dop_two_elemSymm_one]
    simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_one, map_pow, map_ofNat]
    ring
  rw [hQ, LinearMap.smul_apply, key, inv_smul_smul₀ hM]

/-- **`Q_{3,4}(1) = e_1^2e_2 + (q+u-1)e_2^2 + (q^2+qu+u^2-1)e_1e_3`**
`+ (1-q-u-q^2-u^2+q^3+q^2u+qu^2+u^3)e_4`.

`Split 3 4 = (1,1)`, so `HJO.Sym.Qop`'s primitive recursion reads
`Q_{3,4} = M^{-1}(Q_{2,3}Q_{1,1} - Q_{1,1}Q_{2,3}) = M^{-1}(Q_{2,3}D_1 - D_1Q_{2,3})`. At the vacuum
`D_1(1) = -e_1`, so the first branch is `-Q_{2,3}(e_1)`
(`HJO.Sym.qop_two_three_apply_elemSymm_one`) and the second is `D_1` of
`HJO.Sym.qop_two_three_apply_one` — whose `e_1 · e_2` part needs the Pieri rule against
`HJO.Sym.dop_one_elemSymm_two` and `HJO.Sym.dop_two_elemSymm_two`, and whose `e_3` part needs
`HJO.Sym.dop_one_elemSymm_three`. The bracket is again `M` times the stated value, so `M ≠ 0` is
spent once more and no `M` survives in the answer: `Q_{3,4}(1)` is a polynomial in `q` and `u`
despite the two nested normalisations.

**This is the `Q` side of the `(3,4)` instance of the general-slope gluing identity.** The clause,
whose signs `HJO.Mellit.stageWordTotal_singleton_one` fixes, asks at `a = 3`, `b = 4` for
`Q_{3,4}(1) = -ct(d_-(Ξ^{(1)}_{3,4}(y_1)))`; the sweep side is
`HJO.Mellit.constantCoeff_lowerRun_stageWordTotal_three_four`, and the two are matched in
`HJO.Mellit.lhsBase_three_four`. -/
theorem qop_three_four_apply_one (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 3 4 (1 : Lambda L)
      = elemSymm L 1 * elemSymm L 1 * elemSymm L 2
        + (q + u - 1) • (elemSymm L 2 * elemSymm L 2)
        + (q ^ 2 + q * u + u ^ 2 - 1) • (elemSymm L 1 * elemSymm L 3)
        + (1 - q - u - q ^ 2 - u ^ 2 + q ^ 3 + q ^ 2 * u + q * u ^ 2 + u ^ 3) • elemSymm L 4 := by
  have hQ := qop_of_coprime q u (m := 3) (n := 4) (by norm_num) (by decide)
  rw [split_three_four] at hQ
  norm_num only at hQ
  have hd1 : Dop q u 1 (1 : Lambda L) = -elemSymm L 1 := by rw [dop_apply_one]; ring
  have key : (Qop q u 2 3 * Qop q u 1 1 - Qop q u 1 1 * Qop q u 2 3) (1 : Lambda L)
      = ((1 - q) * (1 - u)) •
        (elemSymm L 1 * elemSymm L 1 * elemSymm L 2
          + (q + u - 1) • (elemSymm L 2 * elemSymm L 2)
          + (q ^ 2 + q * u + u ^ 2 - 1) • (elemSymm L 1 * elemSymm L 3)
          + (1 - q - u - q ^ 2 - u ^ 2 + q ^ 3 + q ^ 2 * u + q * u ^ 2 + u ^ 3)
              • elemSymm L 4) := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply, qop_one]
    rw [hd1, map_neg, qop_two_three_apply_elemSymm_one hM, qop_two_three_apply_one hM,
      map_add, map_neg, map_smul, dop_one_elemSymm_three,
      dop_elemSymm_one_mul q u 1 (elemSymm L 2), dop_one_elemSymm_two, dop_two_elemSymm_two]
    simp only [MvPolynomial.smul_eq_C_mul, map_neg, map_sub, map_add, map_mul, map_one, map_pow]
    ring
  rw [hQ, LinearMap.smul_apply, key, inv_smul_smul₀ hM]

end HJO.Sym
