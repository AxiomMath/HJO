/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.SplitVandermonde

/-! # The numerator factor `∏_{j ≠ i}(u x_i - x_j)` under `splitAt`

The last factor of Step 2 of the proof of `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`.
`HJO.Mac.macOpNum` — the polynomial form of Macdonald's operator — has one summand per letter `i`,
carrying the factor `∏_{j ≠ i}(u x_i - x_j)`. Read in the greatest variable `x_t` it behaves in two
different ways:

* at `i = t` every factor mentions `x_t`, so the product is linear in `x_t` in each factor and has
  degree `n-1` overall, with `u^{n-1}` there;
* at `i ≠ t` exactly one factor mentions `x_t`, namely `u x_i - x_t`, so the product is linear in
  `x_t`, with `-∏_{j ≠ i, j ≠ t}(u x_i - x_j)` as the coefficient of `x_t`.

## Upper bounds and one coefficient, not exact degrees

Step 3 extracts the coefficient of `x_t^{n-1+r}` from a product, and the tool for that is
`Polynomial.coeff_mul_add_eq_of_natDegree_le`, which asks only for `natDegree ≤ d` on each factor
and returns the product of the coefficients at the two chosen indices. So what is proved here is a
degree *bound* together with the coefficient *at* the bound. That is strictly weaker than an exact
degree and a leading coefficient, and it is what makes the statements unconditional: no `u ≠ 0`, no
nonvanishing of any product, no domain hypothesis. Asking for the exact degree would require
`u ≠ 0` at `i = t` — the product genuinely collapses to a constant when `u = 0` — and would put a
hypothesis into Step 3 that Step 3 does not need.

Both coefficient computations are `Polynomial.coeff_prod_of_natDegree_le`, which turns the
coefficient of a product of `#S` polynomials of degree at most one, taken at `#S`, into the product
of their coefficients at one.

## Main results

* `HJO.Mac.splitAt_prod_numFactor_top`, with `natDegree_splitAt_prod_numFactor_top_le` and
  `coeff_splitAt_prod_numFactor_top`: at the split letter, degree at most `n-1` with `u^{n-1}`.
* `HJO.Mac.splitAt_prod_numFactor`, with `natDegree_splitAt_prod_numFactor_le` and
  `coeff_splitAt_prod_numFactor`: at any other letter, degree at most one with
  `-∏_{j ≠ i, j ≠ t}(u x_i - x_j)`.

## References

Step 2 of the proof of `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`, on the definitions
`HJO.Mac.macCoeff` and `HJO.Mac.macOp`. -/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

/-! ### The two linear shapes, at index one -/

section Linear

variable {R : Type*} [CommRing R] {ι : Type*}

theorem natDegree_C_mul_X_sub_C_le (c a : R) :
    (Polynomial.C c * Polynomial.X - Polynomial.C a).natDegree ≤ 1 := by
  rw [sub_eq_add_neg, ← Polynomial.C_neg]
  exact Polynomial.natDegree_linear_le

theorem coeff_C_mul_X_sub_C_one (c a : R) :
    (Polynomial.C c * Polynomial.X - Polynomial.C a).coeff 1 = c := by
  simp

theorem coeff_C_sub_X_one (a : R) :
    (Polynomial.C a - Polynomial.X : Polynomial R).coeff 1 = -1 := by
  simp

theorem natDegree_C_sub_X_le (a : R) :
    (Polynomial.C a - Polynomial.X : Polynomial R).natDegree ≤ 1 := by
  rw [← neg_sub, Polynomial.natDegree_neg]
  exact Polynomial.natDegree_X_sub_C_le a

/-- **A product of `#S` polynomials of degree at most one has degree at most `#S`.** -/
theorem natDegree_prod_le_card {f : ι → Polynomial R} (S : Finset ι)
    (hf : ∀ i ∈ S, (f i).natDegree ≤ 1) : (∏ i ∈ S, f i).natDegree ≤ S.card :=
  (Polynomial.natDegree_prod_le S f).trans <| by
    simpa using Finset.sum_le_sum hf

/-- **Its coefficient at `#S` is the product of the coefficients at one.** -/
theorem coeff_prod_card {f : ι → Polynomial R} (S : Finset ι)
    (hf : ∀ i ∈ S, (f i).natDegree ≤ 1) :
    (∏ i ∈ S, f i).coeff S.card = ∏ i ∈ S, (f i).coeff 1 := by
  simpa using Polynomial.coeff_prod_of_natDegree_le S f 1 hf

end Linear

/-! ### The numerator factor, split -/

section Num

variable {σ K : Type*} [Field K] [LinearOrder σ] [Fintype σ] {t : σ}

/-- The small alphabet is the big one with the greatest letter erased. -/
theorem univ_erase_top_eq_image (t : σ) :
    (Finset.univ : Finset σ).erase t
      = (Finset.univ : Finset {b : σ // b ≠ t}).image Subtype.val := by
  refine Finset.ext fun b => ?_
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image, true_and]
  exact ⟨fun hb => ⟨⟨b, hb⟩, rfl⟩, fun ⟨c, hc⟩ => hc ▸ c.2⟩

/-- **`∏_{j ≠ t}(u x_t - x_j)` read in `x_t`**: every factor mentions `x_t`, and becomes the linear
`C u · X - C x_b`. -/
theorem splitAt_prod_numFactor_top (u : K) (t : σ) :
    splitAt t (∏ j ∈ (Finset.univ : Finset σ).erase t, (C u * X t - X j))
      = ∏ b : {b : σ // b ≠ t},
          (Polynomial.C (C u) * Polynomial.X - Polynomial.C (X b : MvPolynomial _ K)) := by
  rw [univ_erase_top_eq_image t, map_prod,
    Finset.prod_image fun x _ y _ hxy => Subtype.ext hxy]
  exact Finset.prod_congr rfl fun b _ => by
    rw [map_sub, map_mul, splitAt_C, splitAt_X_self, splitAt_X_of_ne b.2]

/-- The degree in `x_t` is at most `n-1`, written without a truncated subtraction. -/
theorem natDegree_splitAt_prod_numFactor_top_le (u : K) (t : σ) :
    (splitAt t (∏ j ∈ (Finset.univ : Finset σ).erase t,
      (C u * X t - X j))).natDegree ≤ Fintype.card {b : σ // b ≠ t} := by
  rw [splitAt_prod_numFactor_top, ← Finset.card_univ]
  exact natDegree_prod_le_card _ fun b _ => natDegree_C_mul_X_sub_C_le _ _

/-- **The coefficient there is `u^{n-1}`**, each factor contributing `u`. -/
theorem coeff_splitAt_prod_numFactor_top (u : K) (t : σ) :
    (splitAt t (∏ j ∈ (Finset.univ : Finset σ).erase t, (C u * X t - X j))).coeff
        (Fintype.card {b : σ // b ≠ t})
      = C u ^ Fintype.card {b : σ // b ≠ t} := by
  rw [splitAt_prod_numFactor_top, ← Finset.card_univ,
    coeff_prod_card _ fun b _ => natDegree_C_mul_X_sub_C_le _ _,
    Finset.prod_congr rfl fun b _ => coeff_C_mul_X_sub_C_one (C u) (X b),
    Finset.prod_const, Finset.card_univ]

/-- **`∏_{j ≠ i}(u x_i - x_j)` read in `x_t`, for `i ≠ t`**: exactly one factor mentions `x_t`,
namely `u x_i - x_t`, and the rest are constants. -/
theorem splitAt_prod_numFactor (u : K) {i : σ} (h : i ≠ t) :
    splitAt t (∏ j ∈ (Finset.univ : Finset σ).erase i, (C u * X i - X j))
      = (Polynomial.C (C u * X (⟨i, h⟩ : {b : σ // b ≠ t})) - Polynomial.X) *
          Polynomial.C (∏ b ∈ (Finset.univ : Finset {b : σ // b ≠ t}).erase ⟨i, h⟩,
            (C u * X (⟨i, h⟩ : {b : σ // b ≠ t}) - X b)) := by
  rw [erase_eq_insert_image h, Finset.prod_insert (by simp), map_mul, map_prod,
    Finset.prod_image fun x _ y _ hxy => Subtype.ext hxy, map_prod]
  refine congrArg₂ _ ?_ (Finset.prod_congr rfl fun b _ => ?_)
  · rw [map_sub, map_mul, splitAt_C, splitAt_X_of_ne h, splitAt_X_self, Polynomial.C_mul]
  · rw [map_sub, map_mul, splitAt_C, splitAt_X_of_ne h, splitAt_X_of_ne b.2,
      ← Polynomial.C_mul, ← Polynomial.C_sub]

/-- The degree in `x_t` is at most one. -/
theorem natDegree_splitAt_prod_numFactor_le (u : K) {i : σ} (h : i ≠ t) :
    (splitAt t (∏ j ∈ (Finset.univ : Finset σ).erase i, (C u * X i - X j))).natDegree ≤ 1 := by
  rw [splitAt_prod_numFactor u h]
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, add_zero]
  exact natDegree_C_sub_X_le _

/-- **The coefficient of `x_t` there is `-∏_{j ≠ i, j ≠ t}(u x_i - x_j)`.** -/
theorem coeff_splitAt_prod_numFactor (u : K) {i : σ} (h : i ≠ t) :
    (splitAt t (∏ j ∈ (Finset.univ : Finset σ).erase i, (C u * X i - X j))).coeff 1
      = -∏ b ∈ (Finset.univ : Finset {b : σ // b ≠ t}).erase ⟨i, h⟩,
          (C u * X (⟨i, h⟩ : {b : σ // b ≠ t}) - X b) := by
  rw [splitAt_prod_numFactor u h, Polynomial.coeff_mul_C, coeff_C_sub_X_one, neg_one_mul]

end Num

end HJO.Mac

end
