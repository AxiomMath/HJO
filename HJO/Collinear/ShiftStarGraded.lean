/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.ShiftPair
public meta import HJO.Attr

/-! # The degree-zero graded piece, and the grading of the starred displacement

Two results: that `Λ_0` is the set of `𝕜`-multiples of `1`, and that the
starred displacement of a homogeneous element of degree `d` is `∑_{r=0}^{d} g_r z^{-r}` with
`g_r ∈ Λ_{d-r}`.

## Main definitions

* `HJO.Sym.shiftGraded`: the `d`-graded elements of `Λ[w]`, `w = z⁻¹` — the polynomials whose
  coefficient at `w^r` lies in `Λ_{d-r}` for `r ≤ d` and vanishes for `r > d`. This is the
  notion "`d`-graded" of the proof of `HJO.Sym.plethShiftStar_mem_shiftGraded`, named because
  the argument is that it is a subspace closed under multiplication with the degrees adding.

## Main results

* `HJO.Sym.lambdaComp_zero`.
* `HJO.Sym.plethShiftStar_mem_shiftGraded`, `HJO.Sym.shiftStarCoeff_mem_lambdaComp`,
  `HJO.Sym.shiftStarCoeff_eq_zero_of_lt`: `HJO.Sym.plethShiftStar_mem_shiftGraded`. The coefficients
  are the `f^*_{[r]}` of `HJO.Sym.shiftStarCoeff`.

## Implementation notes

**The vanishing above `d` is stated separately, and it has to be.** The conclusion is
that `f[X - M̃/z]` is `∑_{r=0}^{d}g_rz^{-r}` with `g_r ∈ Λ_{d-r}`, which asserts two things: the
coefficient at `w^r` lies in `Λ_{d-r}` for `r ≤ d`, *and* there is no coefficient beyond `r = d`.
Writing the first clause for every `r : ℕ` would say nothing at `r > d`, since the truncated
subtraction `d - r` is then `0` and `Λ_0` is not the zero subspace — it is the scalars. So
`HJO.Sym.shiftGraded` carries both clauses and the two conclusions are drawn from it separately.

**Why a submodule of `Λ[w]` rather than an induction on `f`.** The proof is exactly
this: the `d`-graded elements form a subspace, the displacement is `𝕜`-linear, and `Λ_d` is spanned
by the products of power sums of total degree `d`, so it suffices to check one product — which is a
product of the images of the `p_j`, each `j`-graded, and the grading is multiplicative. Naming the
subspace is what lets `Submodule.span_le` do the reduction and `prod_mem_shiftGraded` the product.

## References

This file proves `HJO.Sym.lambdaComp_zero` and `HJO.Sym.plethShiftStar_mem_shiftGraded`, about
`HJO.Sym.LambdaComp` and `HJO.Sym.plethShiftStar`.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The graded piece in degree zero -/

section DegreeZero

variable {K : Type*} [CommRing K]

/-- **The graded piece in degree zero.** `Λ_0` is the `𝕜`-span of
`1`, that is, the set of `𝕜`-multiples of `1`.

Every generator of `Λ` has positive weight, so an exponent vector of weighted degree `0` is the zero
vector and a weighted homogeneous element of degree `0` is its own constant term. -/
@[hjo "lem_ght_component_degree_zero"]
theorem lambdaComp_zero (K : Type*) [CommRing K] :
    LambdaComp K 0 = Submodule.span K {(1 : Lambda K)} := by
  refine le_antisymm (fun f hf => ?_) (Submodule.span_le.2 ?_)
  · have h1 : MvPolynomial.weightedHomogeneousComponent (fun i : ℕ => i + 1) 0 f
        = MvPolynomial.C (MvPolynomial.coeff 0 f) :=
      MvPolynomial.weightedHomogeneousComponent_zero (w := fun i : ℕ => i + 1) f
        fun i => Nat.succ_ne_zero i
    have h2 : MvPolynomial.weightedHomogeneousComponent (fun i : ℕ => i + 1) 0 f = f :=
      (mem_lambdaComp.1 hf).weightedHomogeneousComponent_same
    have h3 : MvPolynomial.C (MvPolynomial.coeff 0 f)
        = MvPolynomial.coeff 0 f • (1 : Lambda K) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [← h2, h1, h3]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rintro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact one_mem_lambdaComp K

/-- `HJO.Sym.lambdaComp_zero` in this form: an element of `Λ_0` is a scalar,
and every scalar is one. -/
@[hjo "lem_ght_component_degree_zero"]
theorem mem_lambdaComp_zero_iff {f : Lambda K} :
    f ∈ LambdaComp K 0 ↔ ∃ c : K, f = MvPolynomial.C c := by
  constructor
  · intro hf
    refine ⟨MvPolynomial.coeff 0 f, ?_⟩
    have h1 : MvPolynomial.weightedHomogeneousComponent (fun i : ℕ => i + 1) 0 f
        = MvPolynomial.C (MvPolynomial.coeff 0 f) :=
      MvPolynomial.weightedHomogeneousComponent_zero (w := fun i : ℕ => i + 1) f
        fun i => Nat.succ_ne_zero i
    have h2 : MvPolynomial.weightedHomogeneousComponent (fun i : ℕ => i + 1) 0 f = f :=
      (mem_lambdaComp.1 hf).weightedHomogeneousComponent_same
    exact h2.symm.trans h1
  · rintro ⟨c, rfl⟩
    exact mem_lambdaComp.2 (MvPolynomial.isWeightedHomogeneous_C _ c)

end DegreeZero

/-! ### The graded elements of the polynomial ring in `w = z⁻¹` -/

section Graded

variable {K : Type*} [CommRing K]

/-- **The `d`-graded elements of `Λ[w]`**, `w = z⁻¹`: the polynomials `∑_r g_r w^r` with
`g_r ∈ Λ_{d-r}` for every `r ≤ d` and `g_r = 0` for `r > d`. This is the `d`-graded
elements of `Λ[z, z^{-1}]`, read in the variable in which the starred displacement is written.

Both clauses are needed: without the second, the condition says nothing at `r > d`, the truncated
subtraction making `Λ_{d-r}` the scalars there. -/
def shiftGraded (K : Type*) [CommRing K] (d : ℕ) : Submodule K (Polynomial (Lambda K)) where
  carrier := {P | (∀ r ≤ d, P.coeff r ∈ LambdaComp K (d - r)) ∧ ∀ r, d < r → P.coeff r = 0}
  add_mem' {P Q} hP hQ := by
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · rw [Polynomial.coeff_add]
      exact Submodule.add_mem _ (hP.1 r hr) (hQ.1 r hr)
    · rw [Polynomial.coeff_add, hP.2 r hr, hQ.2 r hr, add_zero]
  zero_mem' := ⟨fun r _ => by rw [Polynomial.coeff_zero]; exact Submodule.zero_mem _,
    fun r _ => Polynomial.coeff_zero r⟩
  smul_mem' c P hP := by
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · rw [Polynomial.coeff_smul]
      exact Submodule.smul_mem _ c (hP.1 r hr)
    · rw [Polynomial.coeff_smul, hP.2 r hr, smul_zero]

theorem mem_shiftGraded {d : ℕ} {P : Polynomial (Lambda K)} :
    P ∈ shiftGraded K d ↔
      (∀ r ≤ d, P.coeff r ∈ LambdaComp K (d - r)) ∧ ∀ r, d < r → P.coeff r = 0 := Iff.rfl

/-- A constant of `Λ[w]` whose value is homogeneous of degree `d` is `d`-graded: the single
coefficient sits at `r = 0`, where the condition reads `Λ_d`. -/
theorem C_mem_shiftGraded {d : ℕ} {f : Lambda K} (hf : f ∈ LambdaComp K d) :
    Polynomial.C f ∈ shiftGraded K d := by
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · rw [Polynomial.coeff_C]
    split_ifs with h
    · rw [h, Nat.sub_zero]; exact hf
    · exact Submodule.zero_mem _
  · rw [Polynomial.coeff_C, ite_eq_right (show ¬(r = 0) by omega)]

/-- The monomial `c w^k` with a scalar coefficient is `k`-graded: its one coefficient sits at
`r = k`, where the condition reads `Λ_0`, and `Λ_0` is the scalars. -/
theorem monomial_C_mem_shiftGraded (k : ℕ) (c : K) :
    Polynomial.monomial k (MvPolynomial.C c : Lambda K) ∈ shiftGraded K k := by
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · rw [Polynomial.coeff_monomial]
    split_ifs with h
    · rw [show k - r = 0 from by omega]
      exact mem_lambdaComp_zero_iff.2 ⟨c, rfl⟩
    · exact Submodule.zero_mem _
  · rw [Polynomial.coeff_monomial, ite_eq_right (show ¬(k = r) by omega)]

/-- `1` is `0`-graded. -/
theorem one_mem_shiftGraded (K : Type*) [CommRing K] :
    (1 : Polynomial (Lambda K)) ∈ shiftGraded K 0 := by
  have h := C_mem_shiftGraded (one_mem_lambdaComp K)
  rwa [map_one] at h

/-- **The grading is multiplicative**: the product of an `a`-graded and a `b`-graded element is
`(a+b)`-graded. The coefficient of `w^r` in the product is `∑_{i+j=r}P_iQ_j`; a term with `i > a` or
`j > b` vanishes, and in the surviving ones `(a-i) + (b-j) = a+b-r`. -/
theorem mul_mem_shiftGraded {a b : ℕ} {P Q : Polynomial (Lambda K)}
    (hP : P ∈ shiftGraded K a) (hQ : Q ∈ shiftGraded K b) :
    P * Q ∈ shiftGraded K (a + b) := by
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · rw [Polynomial.coeff_mul]
    refine Submodule.sum_mem _ fun x hx => ?_
    have hxr : x.1 + x.2 = r := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge a x.1 with h1 | h1
    · rw [hP.2 x.1 h1, zero_mul]
      exact Submodule.zero_mem _
    rcases Nat.lt_or_ge b x.2 with h2 | h2
    · rw [hQ.2 x.2 h2, mul_zero]
      exact Submodule.zero_mem _
    have hsum : a - x.1 + (b - x.2) = a + b - r := by omega
    exact hsum ▸ mul_mem_lambdaComp (hP.1 x.1 h1) (hQ.1 x.2 h2)
  · rw [Polynomial.coeff_mul, Finset.sum_eq_zero]
    intro x hx
    have hxr : x.1 + x.2 = r := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge a x.1 with h1 | h1
    · rw [hP.2 x.1 h1, zero_mul]
    · rw [hQ.2 x.2 (by omega), mul_zero]

/-- A power of an `a`-graded element is `(a * n)`-graded. -/
theorem pow_mem_shiftGraded {a : ℕ} {P : Polynomial (Lambda K)} (hP : P ∈ shiftGraded K a) (n : ℕ) :
    P ^ n ∈ shiftGraded K (a * n) := by
  induction n with
  | zero => rw [pow_zero, Nat.mul_zero]; exact one_mem_shiftGraded K
  | succ n ih =>
    rw [pow_succ, show a * (n + 1) = a * n + a from by ring]
    exact mul_mem_shiftGraded ih hP

/-- A finite product of graded elements is graded, the degrees adding. -/
theorem prod_mem_shiftGraded {ι : Type*} {s : Finset ι} {P : ι → Polynomial (Lambda K)} {d : ι → ℕ}
    (h : ∀ i ∈ s, P i ∈ shiftGraded K (d i)) :
    ∏ i ∈ s, P i ∈ shiftGraded K (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact one_mem_shiftGraded K
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact mul_mem_shiftGraded (h i (Finset.mem_cons_self i s))
      (ih fun j hj => h j (Finset.mem_cons_of_mem hj))

end Graded

/-! ### The starred displacement of a homogeneous element -/

section ShiftStar

variable {L : Type*} [Field L]

/-- The starred displacement of the power sum `p_{i+1}` is `(i+1)`-graded: it is `p_{i+1}`, which is
homogeneous of degree `i + 1`, minus a scalar times `w^{i+1}`. -/
theorem plethShiftStar_X_mem_shiftGraded (q u : L) (i : ℕ) :
    plethShiftStar q u (MvPolynomial.X i) ∈ shiftGraded L (i + 1) := by
  have hps : powerSum L (i + 1) ∈ LambdaComp L (i + 1) := by
    rw [mem_lambdaComp, powerSum, Nat.add_sub_cancel]
    exact MvPolynomial.isWeightedHomogeneous_X L _ i
  have hmono : Polynomial.C (MvPolynomial.C ((1 - (q ^ (i + 1))⁻¹) * (1 - (u ^ (i + 1))⁻¹)))
        * Polynomial.X ^ (i + 1)
      = Polynomial.monomial (i + 1)
        (MvPolynomial.C ((1 - (q ^ (i + 1))⁻¹) * (1 - (u ^ (i + 1))⁻¹)) : Lambda L) :=
    Polynomial.C_mul_X_pow_eq_monomial
  rw [plethShiftStar_X, hmono]
  exact Submodule.sub_mem _ (C_mem_shiftGraded hps) (monomial_C_mem_shiftGraded _ _)

/-- **The starred displacement of a homogeneous element.** For
`f ∈ Λ_d`, the Laurent polynomial `f[X - M̃/z]` is `d`-graded: writing it `∑_r g_r z^{-r}`, one has
`g_r ∈ Λ_{d-r}` for `r ≤ d` and `g_r = 0` beyond, so the sum runs over `0 ≤ r ≤ d`.

The `d`-graded elements form a subspace and `Λ_d` is spanned by the products of power sums of total
degree `d`, so it suffices to check one such product; there the displacement is the product of the
images of the factors, each graded by its own degree, and the grading is multiplicative. -/
@[hjo "lem_ght_shift_star_graded"]
theorem plethShiftStar_mem_shiftGraded (q u : L) {d : ℕ} {f : Lambda L} (hf : f ∈ LambdaComp L d) :
    plethShiftStar q u f ∈ shiftGraded L d := by
  classical
  have hle : LambdaComp L d ≤
      Submodule.comap (plethShiftStar q u).toLinearMap (shiftGraded L d) := by
    rw [lambdaComp_eq_span]
    refine Submodule.span_le.2 ?_
    rintro g ⟨e, he, rfl⟩
    have hprod : plethShiftStar q u (∏ i ∈ e.support, powerSum L (i + 1) ^ e i)
        ∈ shiftGraded L (∑ i ∈ e.support, (i + 1) * e i) := by
      rw [map_prod]
      refine prod_mem_shiftGraded (d := fun i => (i + 1) * e i) fun i _ => ?_
      rw [map_pow, show powerSum L (i + 1) = MvPolynomial.X i from by
        rw [powerSum, Nat.add_sub_cancel]]
      exact pow_mem_shiftGraded (plethShiftStar_X_mem_shiftGraded q u i) (e i)
    have hdeg : ∑ i ∈ e.support, (i + 1) * e i = d := by
      rw [← he, Finsupp.weight_apply, Finsupp.sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, Nat.mul_comm]
    rw [hdeg] at hprod
    exact hprod
  exact hle hf

/-- **The coefficients of `HJO.Sym.plethShiftStar_mem_shiftGraded`**: for `r ≤ d` the coefficient
`f^*_{[r]}` of `z^{-r}` in `f[X - M̃/z]` lies in `Λ_{d-r}`. This is the `g_r ∈ Λ_{d-r}`. -/
@[hjo "lem_ght_shift_star_graded"]
theorem shiftStarCoeff_mem_lambdaComp (q u : L) {d : ℕ} {f : Lambda L}
    (hf : f ∈ LambdaComp L d) {r : ℕ} (hr : r ≤ d) :
    shiftStarCoeff q u f r ∈ LambdaComp L (d - r) :=
  (plethShiftStar_mem_shiftGraded q u hf).1 r hr

/-- **The sum stops at `r = d`**: beyond the degree the coefficients of `f[X - M̃/z]` vanish, which
is what makes the sum `∑_{r=0}^{d}` exhaustive. Stating this separately is not
bookkeeping: at `r > d` the truncated subtraction makes `Λ_{d-r}` the scalars, so the membership
clause alone would say nothing there. -/
@[hjo "lem_ght_shift_star_graded"]
theorem shiftStarCoeff_eq_zero_of_lt (q u : L) {d : ℕ} {f : Lambda L}
    (hf : f ∈ LambdaComp L d) {r : ℕ} (hr : d < r) : shiftStarCoeff q u f r = 0 :=
  (plethShiftStar_mem_shiftGraded q u hf).2 r hr

end ShiftStar

end HJO.Sym
