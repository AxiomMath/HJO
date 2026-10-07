/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.LeadingExponent
public import HJO.Macdonald.OperatorStable
public import HJO.Macdonald.StandingFacts
public meta import HJO.Attr

/-! # Macdonald's operator is triangular on the monomial symmetric polynomials

`HJO.Mac.macOpComp_msymm_sub_smul_mem_span`: for a partition `μ` of `d` with at most `n` parts,
`D^{(n)}_1 m_μ[X_n] - E_n(μ) m_μ[X_n]` lies in the `𝕜`-span of the `m_ν[X_n]` with
`\bar\nu <_lex \bar\mu`. Together with `HJO.Mac.exists_eq_macOp_algebraMap` this is what pins
Macdonald's polynomial `P_μ[X_n]` as the monic eigenfunction of `D^{(n)}_1`.

## Main results

* `HJO.Mac.macOpComp_msymm_sub_smul_mem_span_of_ne_zero`: the triangularity, over any field in
  which `u ≠ 0`.
* `HJO.Mac.macOpComp_msymm_sub_smul_mem_span`: the same at generic parameters, which is the
  statement used later.

## Genericity: exactly one nonvanishing is spent

The theory of Macdonald polynomials is developed over `𝕜 = ℚ(q, u)` with `q` and `u`
indeterminates. The statement below is therefore phrased at generic parameters --
`AlgebraicIndependent ℤ ![q, u]`, this library's standing spelling of that -- and
**`u ≠ 0` is the only consequence of genericity the proof consumes**, through
`HJO.Standing.u_ne_zero`, the module that collects the standing facts. It is spent in
Step 2, where the leading term of `u x_i - x_j` for `i < j` is `u x_i` rather than `-x_j`; at
`u = 0` the leading exponents of the `n` summands of `HJO.Mac.vandermondeProd_mul_macOp` no longer
agree and the argument breaks
(not merely its bookkeeping: at `u = 0` and `n = 2` the Step 2 leading coefficient
`(-1)^{i-1}u^{n-i}` vanishes at `i = 1`). The `_of_ne_zero` form carries that hypothesis alone and
is true over every field.

Two further nonvanishings the proof invokes are **not** needed and are not carried.
`q ≠ 0` is free here because `HJO.Mac.macOp` already takes `q` as a unit of `𝕜`
(`HJO/Macdonald/FiniteAlphabet.lean`). And `E_n(μ) ≠ 0`, which the Step 5 takes
from `HJO.Sym.macdonaldEigenvalue_ne_zero` -- a lemma that is **false** over a general field, at
`u = -1` and `μ = ∅` -- is avoided by the case split of `coeff_partExp_macOpComp` below: if
`D^{(n)}_1 m_μ` is zero, or has leading exponent strictly below `\bar\mu`, then `E_n(μ)` is zero
too, and the conclusion holds for that reason rather than in spite of it.

## The shape of the argument

The six steps, in the order they appear here.

Steps 1 and 2 are `lex_degree_macOpNumFactor` and `lex_leadingCoeff_macOpNumFactor`: the polynomial
factor `F_i = (-1)^{c_i}\mathcal{V}_{N∖\{i\}}\prod_{j≠i}(ux_i-x_j)` of the `i`-th summand of
`HJO.Mac.vandermondeProd_mul_macOp` has the *same* leading exponent as `\mathcal{V}_N`, with leading
coefficient `u^{\#\{j : i<j\}}`. One could compute both leading exponents entrywise; here they
are compared instead, through the repo's `vandermondeProd_univ_eq_erase`, which already splits
`\mathcal{V}_N` as `(-1)^{c_i}(\prod_{j≠i}(x_i-x_j))\mathcal{V}_{N∖\{i\}}` -- and
`\prod_{j≠i}(x_i-x_j)` has the same leading exponent as `\prod_{j≠i}(ux_i-x_j)`, factor by factor.
This is why the false reading of the Step 1 at `k ∉ S` (see
`HJO/Macdonald/LeadingExponent.lean`) costs nothing.

Step 3 is `lex_degree_qShiftPoly` and `lex_leadingCoeff_qShiftPoly` on top of
`HJO.Mac.lex_degree_msymm`: the parameter shift multiplies each coefficient by a unit, so it moves
no leading exponent, and `ld(m_μ) = \bar\mu` with coefficient `1`.

Step 4 is `lex_degree_macOpNum_le` and `coeff_macOpNum`: every exponent of
`\mathcal{V}_N D^{(n)}_1 m_μ` is at most `ld(\mathcal{V}_N) + \bar\mu`, and the coefficient there
is `E_n(μ)`.

Steps 5 and 6 are `coeff_partExp_macOpComp` and the main theorem: dividing by `\mathcal{V}_N`
transports that to `D^{(n)}_1 m_μ` itself, and the coefficients of a member of `𝒮_{n,d}` at the
exponents `\bar\nu` are its coordinates in the monomial symmetric basis
(`HJO.Mac.repr_msymmBasis`).

## References

This file formalises the lemma `HJO.Mac.macOpComp_msymm_sub_smul_mem_span`, on
`MvPolynomial.symmetricHomogeneousSubmodule`, `HJO.Mac.msymmMem`, `Finsupp.lex_lt_iff_isLeast`,
`HJO.Mac.macOp`, `HJO.Sym.macdonaldEigenvalue`, `Finset.vandermondeProd`, `HJO.Mac.qShift`,
`MvPolynomial.exists_basis_symmetricHomogeneousSubmodule_msymm`,
`HJO.Mac.exists_eq_macOp_algebraMap`, `HJO.Mac.vandermondeProd_mul_macOp`. The leading-exponent
calculus stated as `MonomialOrder.lex_degree_isGreatest`, `Finsupp.lex_lt_iff_isLeast`,
`Finsupp.isStrictTotalOrder_lex`, `Finsupp.add_lex_add_iff_right`,
`MonomialOrder.le_degree_add_degree_of_mem_support_mul`, `MonomialOrder.coeff_mul_of_degree_add`,
`MonomialOrder.mul_ne_zero_and_degree_mul` is Mathlib's `MonomialOrder.lex`.
-/

@[expose] public section

open Finset MvPolynomial MonomialOrder

namespace HJO.Mac

/-! ### The lexicographic leading data of a linear form -/

section Linear

variable {σ : Type*} [LinearOrder σ] {K : Type*} [Field K]

/-- The indicator of a letter decreases lexicographically as the letter increases: `x_j` is
lexicographically smaller than `x_i` exactly when `i < j`. -/
theorem toLex_single_lt_single {i j : σ} (h : i < j) :
    toLex (Finsupp.single j 1 : σ →₀ ℕ) < toLex (Finsupp.single i 1) := by
  refine Finsupp.Lex.lt_iff.mpr ⟨i, fun m hm => ?_, ?_⟩
  · have h1 : j ≠ m := by rintro rfl; exact absurd h (asymm hm)
    have h2 : i ≠ m := by rintro rfl; exact absurd hm (lt_irrefl i)
    simp [h1, h2]
  · simp [ne_of_gt h]

variable [WellFoundedGT σ]

/-- The leading exponent of a nonzero monomial. -/
theorem lex_degree_monomial_of_ne_zero {D : σ →₀ ℕ} {a : K} (ha : a ≠ 0) :
    lex.degree (monomial D a : MvPolynomial σ K) = D := by
  classical
  rw [lex.degree_monomial a, ite_eq_right fun h => absurd h ha]

/-- **The lexicographic order on exponents is translation invariant**,
`Finsupp.add_lex_add_iff_right`: Mathlib's `Lex (σ →₀ ℕ)` is an ordered additive monoid, and `toLex`
is additive. -/
theorem lex_toSyn_add_lt_add_left {D E F : σ →₀ ℕ} (h : lex.toSyn E < lex.toSyn F) :
    lex.toSyn (D + E) < lex.toSyn (D + F) := by
  rw [lex_lt_iff] at h ⊢
  exact add_lt_add_right h (toLex D)

/-- A binomial with distinct exponents: the larger exponent is the leading one and its coefficient
is the leading coefficient. -/
theorem lex_degree_leadingCoeff_add_monomial {D E : σ →₀ ℕ} (hDE : toLex E < toLex D) {a b : K}
    (ha : a ≠ 0) :
    lex.degree (monomial D a + monomial E b : MvPolynomial σ K) = D ∧
      lex.leadingCoeff (monomial D a + monomial E b : MvPolynomial σ K) = a := by
  have hlt : lex.toSyn (lex.degree (monomial E b : MvPolynomial σ K))
      < lex.toSyn (lex.degree (monomial D a : MvPolynomial σ K)) := by
    rw [lex_degree_monomial_of_ne_zero ha]
    exact lt_of_le_of_lt (lex.degree_monomial_le b) (lex_lt_iff.mpr hDE)
  have hdeg : lex.degree (monomial D a + monomial E b : MvPolynomial σ K) = D := by
    rw [lex.degree_add_of_lt hlt, lex_degree_monomial_of_ne_zero ha]
  have hDE' : D ≠ E := fun h => absurd (h ▸ hDE) (lt_irrefl _)
  refine ⟨hdeg, ?_⟩
  rw [MonomialOrder.leadingCoeff, hdeg, coeff_add, coeff_monomial, coeff_monomial,
    ite_eq_left rfl, ite_eq_right fun h => absurd h.symm hDE', add_zero]

variable {u : K}

/-- **The leading data of `u x_i - x_j`**, for `u ≠ 0` and `i ≠ j`: the leading exponent is the
indicator of the *smaller* of the two letters, and the leading coefficient is `u` if `i < j` and
`-1` if `j < i`. This is the computation inside Steps 1 and 2, at `u = 1` for the
factors of the Vandermonde product and at a general `u` for the numerators. -/
theorem lex_degree_leadingCoeff_linear (hu : u ≠ 0) {i j : σ} (hij : i ≠ j) :
    lex.degree (C u * X i - X j : MvPolynomial σ K) = Finsupp.single (min i j) 1 ∧
      lex.leadingCoeff (C u * X i - X j : MvPolynomial σ K) = if i < j then u else -1 := by
  have hrw : (C u * X i - X j : MvPolynomial σ K)
      = monomial (Finsupp.single i 1) u + monomial (Finsupp.single j 1) (-1 : K) := by
    rw [← C_mul_X_eq_monomial, ← C_mul_X_eq_monomial]
    simp [sub_eq_add_neg]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [hrw, min_eq_left h.le, ite_eq_left h]
    exact lex_degree_leadingCoeff_add_monomial (toLex_single_lt_single h) hu
  · rw [hrw, add_comm, min_eq_right h.le, ite_eq_right fun hc => absurd hc (asymm h)]
    exact lex_degree_leadingCoeff_add_monomial (toLex_single_lt_single h)
      (neg_ne_zero.mpr one_ne_zero)

/-- A linear form `u x_i - x_j` with `u ≠ 0` and `i ≠ j` is not the zero polynomial. -/
theorem linear_ne_zero (hu : u ≠ 0) {i j : σ} (hij : i ≠ j) :
    (C u * X i - X j : MvPolynomial σ K) ≠ 0 := by
  intro h
  have hlc := (lex_degree_leadingCoeff_linear hu hij).2
  rw [h, MonomialOrder.leadingCoeff, coeff_zero] at hlc
  split_ifs at hlc
  · exact hu hlc.symm
  · exact one_ne_zero (neg_eq_zero.mp hlc.symm)

/-- The leading data of `x_k - x_l`: the case `u = 1` of `lex_degree_leadingCoeff_linear`. -/
theorem lex_degree_leadingCoeff_X_sub_X {k l : σ} (h : k ≠ l) :
    lex.degree (X k - X l : MvPolynomial σ K) = Finsupp.single (min k l) 1 ∧
      lex.leadingCoeff (X k - X l : MvPolynomial σ K) = if k < l then 1 else -1 := by
  have h1 : (X k - X l : MvPolynomial σ K) = C 1 * X k - X l := by simp
  rw [h1]
  exact lex_degree_leadingCoeff_linear one_ne_zero h

/-- **The Vandermonde product is monic**: each of its factors is, the factor `x_k - x_l` being
oriented so that `k < l`. This is the coefficient half of the Step 1. -/
theorem lex_leadingCoeff_vandermondeProd (S : Finset σ) :
    lex.leadingCoeff (S.vandermondeProd (X : σ → MvPolynomial σ K)) = 1 := by
  simp only [Finset.vandermondeProd]
  rw [lex.leadingCoeff_prod]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [lex.leadingCoeff_prod]
  refine Finset.prod_eq_one fun l hl => ?_
  have hkl : k < l := (Finset.mem_filter.mp hl).2
  rw [(lex_degree_leadingCoeff_X_sub_X (ne_of_lt hkl)).2, ite_eq_left hkl]

/-- A Vandermonde product is not the zero polynomial: it is monic. -/
theorem vandermondeProd_ne_zero (S : Finset σ) :
    S.vandermondeProd (X : σ → MvPolynomial σ K) ≠ 0 := fun h => by
  have h1 := lex_leadingCoeff_vandermondeProd (K := K) S
  rw [h, MonomialOrder.leadingCoeff, coeff_zero] at h1
  exact zero_ne_one h1

end Linear

/-! ### Step 1: the leading data of a Vandermonde product -/

section Vandermonde

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [Field K] {u : K}

/-- The leading exponent of `∏_{j≠i}(u x_i - x_j)`: the sum, over the letters `j ≠ i`, of the
indicator of the smaller of `i` and `j`. It does not depend on `u`, which is the whole of what
Step 2 needs. -/
theorem lex_degree_prod_linear (hu : u ≠ 0) (i : σ) :
    lex.degree (∏ j ∈ univ.erase i, (C u * X i - X j) : MvPolynomial σ K)
      = ∑ j ∈ univ.erase i, Finsupp.single (min i j) 1 := by
  rw [lex.degree_prod fun j hj => linear_ne_zero hu (Finset.ne_of_mem_erase hj).symm]
  exact Finset.sum_congr rfl fun j hj =>
    (lex_degree_leadingCoeff_linear hu (Finset.ne_of_mem_erase hj).symm).1

/-- The leading coefficient of `∏_{j≠i}(u x_i - x_j)`: one factor of `-1` for each letter below `i`
and one factor of `u` for each letter above it. This is the `(-1)^{i-1}u^{n-i}`. -/
theorem lex_leadingCoeff_prod_linear (hu : u ≠ 0) (i : σ) :
    lex.leadingCoeff (∏ j ∈ univ.erase i, (C u * X i - X j) : MvPolynomial σ K)
      = (-1) ^ #{k ∈ (univ : Finset σ) | k < i} * u ^ #{j ∈ (univ : Finset σ) | i < j} := by
  classical
  have hfa : {j ∈ univ.erase i | i < j} = {j ∈ (univ : Finset σ) | i < j} :=
    Finset.ext fun j => by
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      exact ⟨fun h => h.2, fun h => ⟨(ne_of_lt h).symm, h⟩⟩
  have hfb : {j ∈ univ.erase i | ¬ i < j} = {k ∈ (univ : Finset σ) | k < i} :=
    Finset.ext fun j => by
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and,
        not_lt]
      exact ⟨fun h => lt_of_le_of_ne h.2 h.1, fun h => ⟨ne_of_lt h, h.le⟩⟩
  rw [lex.leadingCoeff_prod, Finset.prod_congr rfl fun j hj =>
      (lex_degree_leadingCoeff_linear hu (Finset.ne_of_mem_erase hj).symm).2,
    Finset.prod_ite, Finset.prod_const, Finset.prod_const, hfa, hfb, mul_comm]

/-- **Step 2 for the exponent.** The polynomial factor `F_i` of the `i`-th summand of
`HJO.Mac.vandermondeProd_mul_macOp` has the same leading exponent as the full Vandermonde product
`𝒱_N`: the repo's `vandermondeProd_univ_eq_erase` splits `𝒱_N` as a sign times `∏_{j≠i}(x_i-x_j)`
times `𝒱_{N∖{i}}`, and `∏_{j≠i}(x_i-x_j)` and `∏_{j≠i}(u x_i-x_j)` have equal leading exponents. -/
theorem lex_degree_macOpNumFactor (hu : u ≠ 0) (i : σ) :
    lex.degree ((-1) ^ #{k ∈ (univ : Finset σ) | k < i} *
        (univ.erase i).vandermondeProd (X : σ → MvPolynomial σ K) *
        ∏ j ∈ univ.erase i, (C u * X i - X j))
      = lex.degree ((univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ K)) := by
  classical
  have hsign : ((-1 : MvPolynomial σ K)) ^ #{k ∈ (univ : Finset σ) | k < i}
      = C ((-1 : K) ^ #{k ∈ (univ : Finset σ) | k < i}) := by
    rw [map_pow, map_neg, map_one]
  have hsne : ((-1 : K) ^ #{k ∈ (univ : Finset σ) | k < i}) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hCne : (C ((-1 : K) ^ #{k ∈ (univ : Finset σ) | k < i}) : MvPolynomial σ K) ≠ 0 := by
    rwa [ne_eq, C_eq_zero]
  have hW := vandermondeProd_ne_zero (K := K) (univ.erase i)
  have hQ : (∏ j ∈ univ.erase i, (C u * X i - X j) : MvPolynomial σ K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => linear_ne_zero hu (Finset.ne_of_mem_erase hj).symm
  have hP : (∏ j ∈ univ.erase i, (X i - X j) : MvPolynomial σ K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj =>
      X_sub_X_ne_zero (Finset.ne_of_mem_erase hj).symm
  have hPQ : lex.degree (∏ j ∈ univ.erase i, (X i - X j) : MvPolynomial σ K)
      = lex.degree (∏ j ∈ univ.erase i, (C u * X i - X j) : MvPolynomial σ K) := by
    rw [lex_degree_prod_linear hu, lex.degree_prod fun j hj =>
      X_sub_X_ne_zero (Finset.ne_of_mem_erase hj).symm]
    exact Finset.sum_congr rfl fun j hj =>
      (lex_degree_leadingCoeff_X_sub_X (Finset.ne_of_mem_erase hj).symm).1
  rw [vandermondeProd_univ_eq_erase (K := K) i, hsign, lex.degree_mul (mul_ne_zero hCne hP) hW,
    lex.degree_mul hCne hP, lex.degree_C, zero_add, hPQ,
    lex.degree_mul (mul_ne_zero hCne hW) hQ, lex.degree_mul hCne hW, lex.degree_C, zero_add,
    add_comm]

/-- **Step 2 for the coefficient.** The leading coefficient of the polynomial factor `F_i` is
`u^{#\{j : i<j\}}`: the two signs `(-1)^{c_i}` -- the one `HJO.Mac.vandermondeProd_mul_macOp`
carries and the one coming from the letters below `i` -- cancel, and `𝒱_{N∖\{i\}}` is monic. -/
theorem lex_leadingCoeff_macOpNumFactor (hu : u ≠ 0) (i : σ) :
    lex.leadingCoeff ((-1) ^ #{k ∈ (univ : Finset σ) | k < i} *
        (univ.erase i).vandermondeProd (X : σ → MvPolynomial σ K) *
        ∏ j ∈ univ.erase i, (C u * X i - X j))
      = u ^ #{j ∈ (univ : Finset σ) | i < j} := by
  classical
  have hsign : ((-1 : MvPolynomial σ K)) ^ #{k ∈ (univ : Finset σ) | k < i}
      = C ((-1 : K) ^ #{k ∈ (univ : Finset σ) | k < i}) := by
    rw [map_pow, map_neg, map_one]
  rw [hsign, lex.leadingCoeff_mul, lex.leadingCoeff_mul, lex_leadingCoeff_prod_linear hu,
    lex_leadingCoeff_vandermondeProd, MonomialOrder.leadingCoeff, lex.degree_C, coeff_C,
    ite_eq_left rfl, mul_one, ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_mul]

end Vandermonde

/-! ### Step 3: the parameter shift moves no leading exponent -/

section Shift

variable {σ : Type*} {K : Type*} [Field K]

/-- The unit by which rescaling multiplies a coefficient is not zero. -/
theorem prod_units_pow_ne_zero (c : σ → Kˣ) (e : σ →₀ ℕ) :
    (∏ i ∈ e.support, (c i : K) ^ e i) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (Units.ne_zero (c i))

/-- Rescaling the variables creates and destroys no monomial. -/
theorem support_rescaleEquiv (c : σ → Kˣ) (p : MvPolynomial σ K) :
    (rescaleEquiv c p).support = p.support := by
  ext e
  rw [mem_support_iff, mem_support_iff, coeff_rescaleEquiv, ne_eq, ne_eq,
    mul_eq_zero, or_iff_left (prod_units_pow_ne_zero c e)]

/-- Rescaling by units is an automorphism, so it kills nothing. -/
theorem rescaleEquiv_ne_zero (c : σ → Kˣ) {p : MvPolynomial σ K} (hp : p ≠ 0) :
    rescaleEquiv c p ≠ 0 := fun h => hp ((rescaleEquiv c).injective (by rw [h, map_zero]))

/-- The parameter shift of `x_i` rescales only that variable, so its unit at `x^e` is `q^{e_i}`. -/
theorem prod_mulSingle_pow [DecidableEq σ] (q : Kˣ) (i : σ) (e : σ →₀ ℕ) :
    ∏ j ∈ e.support, ((Pi.mulSingle i q : σ → Kˣ) j : K) ^ e j = (q : K) ^ e i := by
  classical
  rw [Finset.prod_eq_single i
      (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, Units.val_one, one_pow])
      fun hi => by rw [Finsupp.notMem_support_iff.mp hi, pow_zero],
    Pi.mulSingle_eq_same]

variable [LinearOrder σ] [WellFoundedGT σ]

/-- **Step 3 for the exponent.** The parameter shift does not move the leading exponent: it
multiplies each coefficient by a unit. -/
theorem lex_degree_rescaleEquiv (c : σ → Kˣ) (p : MvPolynomial σ K) :
    lex.degree (rescaleEquiv c p) = lex.degree p := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [map_zero]
  · refine MonomialOrder.degree_eq_of_coeff_ne_zero ?_ fun e he => ?_
    · rw [coeff_rescaleEquiv]
      exact mul_ne_zero (mem_support_iff.mp (lex.degree_mem_support hp))
        (prod_units_pow_ne_zero c _)
    · exact lex.le_degree (by rwa [support_rescaleEquiv] at he)

/-- **Step 3 for the coefficient.** Rescaling multiplies the leading coefficient by the unit
attached to the leading exponent. -/
theorem lex_leadingCoeff_rescaleEquiv (c : σ → Kˣ) (p : MvPolynomial σ K) :
    lex.leadingCoeff (rescaleEquiv c p)
      = lex.leadingCoeff p * ∏ i ∈ (lex.degree p).support, (c i : K) ^ (lex.degree p) i := by
  rw [MonomialOrder.leadingCoeff, lex_degree_rescaleEquiv, coeff_rescaleEquiv,
    MonomialOrder.leadingCoeff]

end Shift

/-! ### Steps 4, 5 and 6 -/

section Triangular

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [Field K] {q : Kˣ} {u : K} {d : ℕ}

/-- The polynomial factor of the `i`-th summand of `HJO.Mac.vandermondeProd_mul_macOp`, as it
appears in `HJO.Mac.macOpNum`. -/
private noncomputable def numFactor (u : K) (i : σ) : MvPolynomial σ K :=
  (-1) ^ #{k ∈ (univ : Finset σ) | k < i} *
    (univ.erase i).vandermondeProd (X : σ → MvPolynomial σ K) *
    ∏ j ∈ univ.erase i, (C u * X i - X j)

private theorem numFactor_ne_zero (hu : u ≠ 0) (i : σ) : numFactor u i ≠ (0 : MvPolynomial σ K) :=
  fun h => by
    have h1 := lex_leadingCoeff_macOpNumFactor (K := K) hu i
    rw [show ((-1) ^ #{k ∈ (univ : Finset σ) | k < i} *
      (univ.erase i).vandermondeProd (X : σ → MvPolynomial σ K) *
      ∏ j ∈ univ.erase i, (C u * X i - X j)) = numFactor u i from rfl, h,
      MonomialOrder.leadingCoeff, coeff_zero] at h1
    exact pow_ne_zero _ hu h1.symm

/-- **Step 4 for one summand.** The `i`-th summand of `𝒱_N D^{(n)}_1 m_μ` has leading exponent
`ld(𝒱_N) + \bar\mu`, with coefficient `u^{#\{j : i<j\}} q^{\bar\mu_i}` there. -/
private theorem lex_degree_leadingCoeff_summand (hu : u ≠ 0) (μ : PartIdx σ d) (i : σ) :
    lex.degree (numFactor u i * rescaleEquiv (Pi.mulSingle i q) (msymm σ K μ.1))
        = lex.degree ((univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ K)) + partExp σ μ ∧
      lex.leadingCoeff (numFactor u i * rescaleEquiv (Pi.mulSingle i q) (msymm σ K μ.1))
        = u ^ #{j ∈ (univ : Finset σ) | i < j} * (q : K) ^ partExp σ μ i := by
  have hM : (msymm σ K μ.1) ≠ 0 := msymm_ne_zero μ
  have hT := rescaleEquiv_ne_zero (Pi.mulSingle i q) hM
  refine ⟨?_, ?_⟩
  · rw [lex.degree_mul (numFactor_ne_zero hu i) hT, lex_degree_rescaleEquiv, lex_degree_msymm,
      numFactor, lex_degree_macOpNumFactor hu]
  · rw [lex.leadingCoeff_mul, lex_leadingCoeff_rescaleEquiv, prod_mulSingle_pow,
      lex_degree_msymm, lex_leadingCoeff_msymm, one_mul, numFactor,
      lex_leadingCoeff_macOpNumFactor hu]

private theorem macOpNum_eq_sum (f : MvPolynomial σ K) :
    macOpNum q u f = ∑ i : σ, numFactor u i * rescaleEquiv (Pi.mulSingle i q) f := rfl

/-- **Step 4 for the exponent.** Every exponent of `𝒱_N D^{(n)}_1 m_μ` is at most
`ld(𝒱_N) + \bar\mu`: the `n` summands all have that leading exponent. -/
theorem lex_degree_macOpNum_le (hu : u ≠ 0) (μ : PartIdx σ d) :
    lex.toSyn (lex.degree (macOpNum q u (msymm σ K μ.1)))
      ≤ lex.toSyn (lex.degree ((univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ K))
          + partExp σ μ) := by
  rw [macOpNum_eq_sum]
  refine le_trans MonomialOrder.degree_sum_le (Finset.sup_le fun i _ => ?_)
  rw [(lex_degree_leadingCoeff_summand hu μ i).1]

/-- **Step 4 for the coefficient.** The coefficient of `𝒱_N D^{(n)}_1 m_μ` at
`ld(𝒱_N) + \bar\mu` is the eigenvalue `E_n(μ)`. -/
theorem coeff_macOpNum (hu : u ≠ 0) (μ : PartIdx σ d) :
    coeff (lex.degree ((univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ K)) + partExp σ μ)
        (macOpNum q u (msymm σ K μ.1))
      = HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ) := by
  rw [macOpNum_eq_sum, coeff_sum, macdonaldEigenvalue_partDiagram]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (lex_degree_leadingCoeff_summand hu μ i).1, ← MonomialOrder.leadingCoeff,
    (lex_degree_leadingCoeff_summand hu μ i).2, mul_comm]

/-! #### Dividing by the Vandermonde product -/

variable [Algebra ℚ K]

/-- `𝒱_N D^{(n)}_1 m_μ` as a product in the polynomial ring: `HJO.Mac.vandermondeProd_mul_macOp`
read through `HJO.Mac.exists_eq_macOp_algebraMap`. -/
private theorem macOpNum_eq_vandermondeProd_mul (μ : PartIdx σ d) :
    macOpNum q u (msymm σ K μ.1)
      = (univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ K) *
          (macOpComp q u d (msymmMem σ K μ) : MvPolynomial σ K) :=
  IsFractionRing.injective (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
    (by rw [algebraMap_macOpNum, map_mul, algebraMap_macOpComp, coe_msymmMem])

/-- **Steps 5 and 6.** The coefficient of `x^{\bar\nu}` in `D^{(n)}_1 m_μ`, at every `\bar\nu`
that is not below `\bar\mu`: it is the eigenvalue `E_n(μ)` at `ν = μ` and `0` otherwise.

`HJO.Sym.macdonaldEigenvalue_ne_zero` is not used. If `D^{(n)}_1 m_μ` vanishes, or has leading
exponent strictly below `\bar\mu`, then the coefficient of `𝒱_N D^{(n)}_1 m_μ` at
`ld(𝒱_N) + \bar\mu` vanishes too, so `E_n(μ) = 0` and both sides are `0`. -/
theorem coeff_partExp_macOpComp (hu : u ≠ 0) (μ ν : PartIdx σ d)
    (hν : ¬ toLex (partExp σ ν) < toLex (partExp σ μ)) :
    coeff (partExp σ ν) (macOpComp q u d (msymmMem σ K μ) : MvPolynomial σ K)
      = if ν = μ then HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ)
        else 0 := by
  have hbound := lex_degree_macOpNum_le (q := q) hu μ
  have hcoeff := coeff_macOpNum (q := q) hu μ
  rw [macOpNum_eq_vandermondeProd_mul] at hbound hcoeff
  set V := (univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ K) with hVdef
  set g := (macOpComp q u d (msymmMem σ K μ) : MvPolynomial σ K) with hgdef
  set E := HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ) with hEdef
  have hVne : V ≠ 0 := vandermondeProd_ne_zero _
  -- every exponent of `D^{(n)}_1 m_μ` is at most `\bar\mu`
  have key : lex.toSyn (lex.degree g) ≤ lex.toSyn (partExp σ μ) := by
    rcases eq_or_ne g 0 with hg0 | hgne
    · rw [hg0, lex.degree_le_iff]
      simp
    · rw [lex.degree_mul hVne hgne, lex_le_iff] at hbound
      exact lex_le_iff.mpr (AddLeftReflectLE.le_of_add_le_add_left hbound)
  -- and the coefficient at `\bar\mu` is the eigenvalue
  have key2 : coeff (partExp σ μ) g = E := by
    rcases eq_or_ne g 0 with hg0 | hgne
    · rw [hg0, mul_zero, coeff_zero] at hcoeff
      rw [hg0, coeff_zero]
      exact hcoeff
    · rcases eq_or_lt_of_le key with heq | hlt
      · have hd : lex.degree g = partExp σ μ := lex.toSyn.injective heq
        calc coeff (partExp σ μ) g = lex.leadingCoeff g := by
              rw [MonomialOrder.leadingCoeff, hd]
          _ = lex.leadingCoeff V * lex.leadingCoeff g := by
              rw [lex_leadingCoeff_vandermondeProd, one_mul]
          _ = coeff (lex.degree V + lex.degree g) (V * g) :=
              MonomialOrder.coeff_mul_of_degree_add.symm
          _ = E := by rw [hd]; exact hcoeff
      · have hz : coeff (lex.degree V + partExp σ μ) (V * g) = 0 := by
          refine lex.coeff_eq_zero_of_lt ?_
          rw [lex.degree_mul hVne hgne]
          exact lex_toSyn_add_lt_add_left hlt
        rw [lex.coeff_eq_zero_of_lt hlt, ← hcoeff, hz]
  rcases lt_trichotomy (toLex (partExp σ ν)) (toLex (partExp σ μ)) with hlt | heq | hgt
  · exact absurd hlt hν
  · have hνμ : ν = μ := partExp_injective (toLex.injective heq)
    subst hνμ
    rw [ite_eq_left rfl]
    exact key2
  · have hνμ : ν ≠ μ := by rintro rfl; exact absurd hgt (lt_irrefl _)
    rw [ite_eq_right fun hc => absurd hc hνμ]
    exact lex.coeff_eq_zero_of_lt (lt_of_le_of_lt key (lex_lt_iff.mpr hgt))

/-- **Macdonald's operator is triangular on the monomial symmetric polynomials**, over any field in
which `u ≠ 0`: `D^{(n)}_1 m_μ - E_n(μ) m_μ` is a combination of the `m_ν` whose exponent vector is
lexicographically below `\bar\mu`.

The coordinates of an element of `𝒮_{n,d}` in the monomial symmetric basis are its coefficients at
the exponents `\bar\nu` (the `hrepr` step), so the two coefficient computations of
`coeff_partExp_macOpComp` say exactly that the coordinates outside the lower set vanish. -/
theorem macOpComp_msymm_sub_smul_mem_span_of_ne_zero (hu : u ≠ 0) (μ : PartIdx σ d) :
    (macOpComp q u d (msymmMem σ K μ) : MvPolynomial σ K)
        - HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ) •
          msymm σ K μ.1
      ∈ Submodule.span K {p : MvPolynomial σ K | ∃ ν : PartIdx σ d,
          toLex (partExp σ ν) < toLex (partExp σ μ) ∧ p = msymm σ K ν.1} := by
  classical
  obtain ⟨B, hB⟩ := exists_basis_symmetricHomogeneousSubmodule_msymm σ K d
  set E := HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ) with hEdef
  set h : symmetricHomogeneousSubmodule σ K d :=
    macOpComp q u d (msymmMem σ K μ) - E • msymmMem σ K μ with hhdef
  have hcoe : (h : MvPolynomial σ K)
      = (macOpComp q u d (msymmMem σ K μ) : MvPolynomial σ K) - E • msymm σ K μ.1 := rfl
  -- the coordinates of an element of `𝒮_{n,d}` are its coefficients at the exponents `\bar\nu`
  have hrepr : ∀ (ν : PartIdx σ d) (x : symmetricHomogeneousSubmodule σ K d),
      B.repr x ν = coeff (partExp σ ν) (x : MvPolynomial σ K) := by
    intro ν
    have hext : (Finsupp.lapply ν).comp (B.repr : symmetricHomogeneousSubmodule σ K d →ₗ[K] _)
        = (lcoeff K (partExp σ ν)).comp (symmetricHomogeneousSubmodule σ K d).subtype :=
      B.ext fun ρ => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
          Module.Basis.repr_self, Submodule.subtype_apply, lcoeff_apply, hB, coeff_partExp_msymm,
          Finsupp.single_apply]
        exact if_congr eq_comm rfl rfl
    exact fun x => LinearMap.congr_fun hext x
  -- every coordinate of `h` outside the lower set vanishes
  have hzero : ∀ ν : PartIdx σ d, ¬ toLex (partExp σ ν) < toLex (partExp σ μ) →
      B.repr h ν = 0 := by
    intro ν hν
    rw [hrepr, hcoe, coeff_sub, coeff_smul, smul_eq_mul, coeff_partExp_msymm,
      coeff_partExp_macOpComp hu μ ν hν]
    split_ifs
    · rw [mul_one, sub_self]
    · rw [mul_zero, sub_zero]
  have hsum : (h : MvPolynomial σ K) = ∑ ν : PartIdx σ d, B.repr h ν • msymm σ K ν.1 := by
    have h1 : ((∑ ν : PartIdx σ d, B.repr h ν • B ν :
        symmetricHomogeneousSubmodule σ K d) : MvPolynomial σ K)
        = ∑ ν : PartIdx σ d, B.repr h ν • msymm σ K ν.1 := by
      rw [AddSubmonoidClass.coe_finsetSum]
      exact Finset.sum_congr rfl fun ν _ => by rw [SetLike.val_smul, hB]
    rw [← h1, B.sum_repr h]
  rw [← hcoe, hsum]
  refine Submodule.sum_mem _ fun ν _ => ?_
  by_cases hlow : toLex (partExp σ ν) < toLex (partExp σ μ)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ν, hlow, rfl⟩)
  · rw [hzero ν hlow, zero_smul]
    exact Submodule.zero_mem _

/-- **Macdonald's operator is triangular on the monomial symmetric polynomials.** For a partition
`μ` of `d` with at most `n` parts, `D^{(n)}_1 m_μ[X_n] - E_n(μ)\,m_μ[X_n]` lies in the `𝕜`-span of
the `m_ν[X_n]` with `|ν| = d`, `ν_{n+1} = 0` and `\bar\nu <_lex \bar\mu`.

Stated at the generic parameters of the Macdonald theory, `𝕜 = ℚ(q, u)`. The only
consequence of genericity the proof consumes is `u ≠ 0`; see
`macOpComp_msymm_sub_smul_mem_span_of_ne_zero`, which is the same statement over any field in which
that holds. -/
@[hjo "lem_mac_dop_triangular"]
theorem macOpComp_msymm_sub_smul_mem_span (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) :
    (macOpComp q u d (msymmMem σ K μ) : MvPolynomial σ K)
        - HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ) •
          msymm σ K μ.1
      ∈ Submodule.span K {p : MvPolynomial σ K | ∃ ν : PartIdx σ d,
          toLex (partExp σ ν) < toLex (partExp σ μ) ∧ p = msymm σ K ν.1} :=
  macOpComp_msymm_sub_smul_mem_span_of_ne_zero (HJO.Standing.u_ne_zero hqu) μ

end Triangular

end HJO.Mac
