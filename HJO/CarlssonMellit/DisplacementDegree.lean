/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.ShiftStarGraded
public meta import HJO.Attr

/-! # The displacement coefficients drop degree

The plethystic displacement `δ : f ↦ f[X + M/z]` sends `p_k` to `p_k + (1 - q^k)(1 - u^k)z^{-k}`,
so it trades one unit of weighted degree for one power of `z^{-1}`. Read on a homogeneous
`f ∈ Λ_d`, this says that the displacement coefficient `f_{[s]}` — the coefficient of `z^{-s}` in
`f[X + M/z]` — is homogeneous of degree `d - s`, and that it vanishes once `s > d`, there being no
degree left to pay for the power of `z^{-1}`. Equivalently, the displacement of a homogeneous
element of degree `d` is `d`-graded in the sense of `HJO.Sym.shiftGraded`.

## Main results

* `HJO.Sym.shiftCoeff_mem_lambdaComp` and `HJO.Sym.shiftCoeff_eq_zero_of_lt`: the two halves of
  "`f_{[s]} ∈ Λ_{d-s}`, read as `0` when `s > d`".
* `HJO.Sym.plethShift_mem_shiftGraded`: the same fact stated for the whole displacement rather
  than one coefficient at a time, and over an arbitrary commutative base ring. This is the form the
  proof establishes, and the form that composes: a product of displaced homogeneous elements is
  graded by the sum of their degrees.

## Implementation notes

The vanishing above `d` is a separate statement and has to be one: at `s > d` the truncated
subtraction makes `Λ_{d-s}` the graded piece `Λ_0`, which is the scalars and not the zero subspace,
so the membership clause alone would say nothing there. The two clauses together are exactly
membership in `HJO.Sym.shiftGraded`, the `d`-graded elements of `Λ[w]` for `w = z⁻¹`, which the
starred displacement already supplies.

The direct proof expands the product `∏_i (p_{λ_i} + (1 - q^{λ_i})(1 - u^{λ_i})z^{-λ_i})` and
indexes the resulting terms by the set of factors contributing their second summand. Here that
enumeration is replaced by the multiplicativity of the grading: each displaced factor is
`λ_i`-graded, so the product is `(λ_1 + ⋯ + λ_ℓ)`-graded. The bookkeeping is the same one, with the
terms left unlisted.

Only a commutative base ring is needed, the displacement asking nothing of the scalars; the
coefficient form is stated over the field its `f_{[s]}` of `HJO.Sym.shiftCoeff` is indexed by.

## References

The lemma `HJO.Sym.shiftCoeff_mem_lambdaComp`, and definitions `HJO.Sym.LambdaComp`,
`HJO.Sym.plethShift`, `HJO.Sym.shiftCoeff`; the displacement, with `t` in place of `u`, is the one
used to define the operators `D_n` in A. Mellit, *Toric braids and `(m, n)`-parking functions*,
arXiv:1604.07456, §3.7 ("Relation with `N` and `S` operators").
-/

@[expose] public section

namespace HJO.Sym

section CommRing

variable {K : Type*} [CommRing K]

/-- The displacement of the power sum `p_{i+1}` is `(i+1)`-graded: it is `p_{i+1}`, which is
homogeneous of degree `i + 1`, plus a scalar times `w^{i+1}`. -/
theorem plethShift_X_mem_shiftGraded (q u : K) (i : ℕ) :
    plethShift q u (MvPolynomial.X i) ∈ shiftGraded K (i + 1) := by
  have hps : powerSum K (i + 1) ∈ LambdaComp K (i + 1) := by
    rw [mem_lambdaComp, powerSum, Nat.add_sub_cancel]
    exact MvPolynomial.isWeightedHomogeneous_X K _ i
  have hmono : Polynomial.C (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1))))
        * Polynomial.X ^ (i + 1)
      = Polynomial.monomial (i + 1)
        (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1))) : Lambda K) :=
    Polynomial.C_mul_X_pow_eq_monomial
  rw [plethShift, MvPolynomial.aeval_X, hmono]
  exact Submodule.add_mem _ (C_mem_shiftGraded hps) (monomial_C_mem_shiftGraded _ _)

/-- **The displacement of a homogeneous element is graded.** For `f ∈ Λ_d`, the Laurent polynomial
`f[X + M/z]` is `∑_s f_{[s]}z^{-s}` with `f_{[s]} ∈ Λ_{d-s}` for `s ≤ d` and `f_{[s]} = 0` beyond.

The `d`-graded elements form a subspace and the displacement is `𝕜`-linear, so by
`HJO.Sym.lambdaComp_eq_span` it suffices to check a product of power sums of total degree `d`;
there the displacement is the product of the images of the factors, each graded by its own degree,
and the grading is multiplicative. -/
theorem plethShift_mem_shiftGraded (q u : K) {d : ℕ} {f : Lambda K} (hf : f ∈ LambdaComp K d) :
    plethShift q u f ∈ shiftGraded K d := by
  classical
  have hle : LambdaComp K d ≤
      Submodule.comap (plethShift q u).toLinearMap (shiftGraded K d) := by
    rw [lambdaComp_eq_span]
    refine Submodule.span_le.2 ?_
    rintro g ⟨e, he, rfl⟩
    have hprod : plethShift q u (∏ i ∈ e.support, powerSum K (i + 1) ^ e i)
        ∈ shiftGraded K (∑ i ∈ e.support, (i + 1) * e i) := by
      rw [map_prod]
      refine prod_mem_shiftGraded (d := fun i => (i + 1) * e i) fun i _ => ?_
      rw [map_pow, show powerSum K (i + 1) = MvPolynomial.X i from by
        rw [powerSum, Nat.add_sub_cancel]]
      exact pow_mem_shiftGraded (plethShift_X_mem_shiftGraded q u i) (e i)
    have hdeg : ∑ i ∈ e.support, (i + 1) * e i = d := by
      rw [← he, Finsupp.weight_apply, Finsupp.sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, Nat.mul_comm]
    rw [hdeg] at hprod
    exact hprod
  exact hle hf

end CommRing

section Coefficients

variable {L : Type*} [Field L]

/-- **The displacement coefficients drop degree.** For `f ∈ Λ_d` and
`s ≤ d`, the coefficient `f_{[s]}` of `z^{-s}` in `f[X + M/z]` lies in `Λ_{d-s}`. -/
@[hjo "lem_shift_coeff_degree"]
theorem shiftCoeff_mem_lambdaComp (q u : L) {d : ℕ} {f : Lambda L} (hf : f ∈ LambdaComp L d)
    {s : ℕ} (hs : s ≤ d) : shiftCoeff q u f s ∈ LambdaComp L (d - s) :=
  (plethShift_mem_shiftGraded q u hf).1 s hs

/-- **`HJO.Sym.shiftCoeff_mem_lambdaComp` above the degree**: `f_{[s]} = 0` for `s > d`, which is
the convention "read as `0` when `s > d`". The parts of a product of power sums of total degree `d`
are positive, so none of them sums to more than `d`, and no term of the expanded displacement
reaches `z^{-s}`. This is a statement in its own right rather than an instance of the previous one:
at `s > d` the truncated subtraction reads `Λ_{d-s}` as `Λ_0`, the scalars. -/
@[hjo "lem_shift_coeff_degree"]
theorem shiftCoeff_eq_zero_of_lt (q u : L) {d : ℕ} {f : Lambda L} (hf : f ∈ LambdaComp L d)
    {s : ℕ} (hs : d < s) : shiftCoeff q u f s = 0 :=
  (plethShift_mem_shiftGraded q u hf).2 s hs

end Coefficients

end HJO.Sym
