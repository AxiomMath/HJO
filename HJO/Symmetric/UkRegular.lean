/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The linear coefficient of an axis generator

At a nonzero parameter that is not a root of unity, the axis generators form a triangular
change of generators of the ring of symmetric functions. This file extracts the coefficient of
`p_k` in `U_k` in closed form and proves its nonvanishing under those hypotheses.

The alphabet of the axis generators is a diagonal substitution, so the coefficient of a monomial
is computed for a diagonal substitution and then specialised to it, where the scalar at `p_k` is
`v ^ (-k) - 1`. For `k ≥ 1` and `v ≠ 0, 1`, the coefficient of `p_k` in `U_k` is
`-v ^ (1 - k) * (1 + v + ⋯ + v ^ (k - 1)) / k`; it vanishes at nontrivial `k`-th roots of unity.
Avoiding `0` and `1` is therefore not enough: at `v = -1` and `k = 2` the coefficient is `0`. The
cancellation formula does not describe the totalized points `v = 0, 1`, where the definition gives
`U_k = 0`.
-/

@[expose] public section

open Finset

namespace HJO.UkRegular

open MvPolynomial HJO.Sym

/-- The complete homogeneous function of degree `0` is `1`. -/
lemma completeHomog_zero (K : Type*) [CommRing K] [Algebra ℚ K] : completeHomog K 0 = 1 := by
  rw [completeHomog]

/-- Newton's identity in the form defining the complete homogeneous functions. -/
lemma completeHomog_succ (K : Type*) [CommRing K] [Algebra ℚ K] (n : ℕ) :
    completeHomog K (n + 1) = C (algebraMap ℚ K ((n + 1 : ℚ)⁻¹)) *
      ∑ k ∈ range (n + 1), powerSum K (k + 1) * completeHomog K (n - k) := by
  rw [completeHomog]

/-- A diagonal substitution multiplies a monomial by the matching product of the scalars, the
exponent at the generator `i` being that generator's exponent in the monomial. -/
lemma diagScale_monomial {K : Type*} [CommRing K] (c : ℕ → K) (d : ℕ →₀ ℕ) (a : K) :
    diagScale c (monomial d a) = monomial d (a * ∏ i ∈ d.support, c i ^ d i) := by
  rw [diagScale, aeval_monomial, algebraMap_eq, monomial_eq, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, ← C_pow, prod_mul_distrib, ← map_prod, C_mul, mul_assoc]

/-- The coefficient of a monomial in the image of a diagonal substitution is the matching product
of the scalars times its coefficient in the argument. -/
lemma coeff_diagScale {K : Type*} [CommRing K] (c : ℕ → K) (d : ℕ →₀ ℕ) (f : Lambda K) :
    coeff d (diagScale c f) = (∏ i ∈ d.support, c i ^ d i) * coeff d f := by
  classical
  refine MvPolynomial.induction_on' f ?_ ?_
  · intro e a
    rw [diagScale_monomial, coeff_monomial, coeff_monomial]
    by_cases h : e = d
    · subst h
      simp [mul_comm]
    · simp [h]
  · intro p q hp hq
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

/-- The coefficient of the generator `p_{m+1}` in the image of a diagonal substitution is the
scalar `c m` attached to that generator times its coefficient in the argument. -/
lemma coeff_single_diagScale {K : Type*} [CommRing K] (c : ℕ → K) (m : ℕ) (f : Lambda K) :
    coeff (Finsupp.single m 1) (diagScale c f) = c m * coeff (Finsupp.single m 1) f := by
  rw [coeff_diagScale, Finsupp.support_single m one_ne_zero, Finset.prod_singleton,
    Finsupp.single_eq_same, pow_one]

/-- The coefficient of the generator `p_{n+1}` in the complete homogeneous function `h_{n+1}`
is `1 / (n + 1)`: only the leading term of Newton's identity is linear in the generators. -/
lemma coeff_single_completeHomog {K : Type*} [CommRing K] [Algebra ℚ K] (n : ℕ) :
    coeff (Finsupp.single n 1) (completeHomog K (n + 1)) = algebraMap ℚ K ((n + 1 : ℚ)⁻¹) := by
  classical
  rw [completeHomog_succ, coeff_C_mul, coeff_sum,
    Finset.sum_eq_single_of_mem n (self_mem_range_succ n)]
  · simp [powerSum, completeHomog_zero]
  · intro b _ hb
    simp only [powerSum, Nat.add_sub_cancel]
    rw [coeff_X_mul']
    simp [hb]

/-- A rational scalar structure carries the inverse of a natural number to the inverse of its
image. -/
lemma algebraMap_inv_natCast {L : Type*} [Field L] [Algebra ℚ L] (n : ℕ) :
    algebraMap ℚ L ((n : ℚ))⁻¹ = ((n : L))⁻¹ := by
  rw [map_inv₀, map_natCast]

/-- The coefficient of the generator `p_{k+1}` in the axis generator `U_{k+1}` at the parameter
`v`, in closed form: the prefactor `v / (v - 1)` times the scalar `v ^ (-(k+1)) - 1` that the axis
alphabet attaches to `p_{k+1}` times the coefficient `1 / (k + 1)` of `p_{k+1}` in `h_{k+1}`. -/
lemma coeff_single_axisGen {L : Type*} [Field L] [Algebra ℚ L] (v : L) (k : ℕ) :
    coeff (Finsupp.single k 1) (axisGen v (k + 1)) =
      v / (v - 1) * (((v ^ (k + 1))⁻¹ - 1) * ((k : L) + 1)⁻¹) := by
  rw [axisGen, coeff_C_mul, plethAxis_eq_diagScale, coeff_single_diagScale,
    coeff_single_completeHomog,
    show ((k : ℚ) + 1)⁻¹ = (((k + 1 : ℕ) : ℚ))⁻¹ by push_cast; ring,
    algebraMap_inv_natCast]
  push_cast
  ring

/-- **The axis generators are a triangular change of generators away from zero and roots
of unity.** For `k ≥ 1`, the coefficient of `p_k` in `U_k` is
`v / (v - 1) * (1 / k) * (v ^ (-k) - 1)`. When `v ≠ 0, 1`, it simplifies to
`-v ^ (1 - k) * (1 + v + ⋯ + v ^ (k-1)) / k`. At the excluded totalized points `v = 0, 1`,
the unsimplified coefficient and `U_k` are zero; the simplified formula must not be used there.

For positive `k`, the coefficient is nonzero exactly when `v ≠ 0` and `v ^ k ≠ 1`. The
hypothesis on all positive powers ensures this simultaneously for every generator. It cannot
be weakened to `v ≠ 0, 1`: at `v = -1`, the `p₂` coefficient vanishes, and no axis generator
involves `p₂` at all, so they do not generate the whole ring. -/
@[hjo "lem_uk_regular"]
theorem coeff_single_axisGen_ne_zero {L : Type*} [Field L] [Algebra ℚ L] [CharZero L] {v : L}
    (hv0 : v ≠ 0) (hv1 : ∀ j : ℕ, v ^ (j + 1) ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    coeff (Finsupp.single (k - 1) 1) (axisGen v k) =
        v / (v - 1) * ((k : L)⁻¹ * ((v ^ k)⁻¹ - 1)) ∧
      coeff (Finsupp.single (k - 1) 1) (axisGen v k) ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hne1 : v ≠ 1 := fun h => hv1 0 (by rw [h, one_pow])
  have hval : coeff (Finsupp.single (m + 1 - 1) 1) (axisGen v (m + 1)) =
      v / (v - 1) * (((m + 1 : ℕ) : L)⁻¹ * ((v ^ (m + 1))⁻¹ - 1)) := by
    rw [Nat.add_sub_cancel, coeff_single_axisGen]
    push_cast
    ring
  refine ⟨hval, ?_⟩
  rw [hval]
  have h1 : ((m + 1 : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)
  have hinv : (v ^ (m + 1))⁻¹ ≠ 1 := fun h => hv1 m (inv_injective (by rw [h, inv_one]))
  exact mul_ne_zero (div_ne_zero hv0 (sub_ne_zero_of_ne hne1))
    (mul_ne_zero (inv_ne_zero h1) (sub_ne_zero_of_ne hinv))

end HJO.UkRegular
