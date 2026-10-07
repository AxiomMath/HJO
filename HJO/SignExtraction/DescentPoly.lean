/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Order.Interval.Finset.Nat
public import HJO.SignExtraction.Defs
public meta import HJO.Attr

/-! # The descent polynomial, its roots and its values

The descent polynomial `D_{n,j} = (1 / n!) ∏_{r < n} (t - j + r)` of
`HJO.Sym.descentPoly` is read here at the three places the sign-extraction route needs it: at
the integers of the window `[j - n + 1, j]`, where it vanishes; at `t = -1` for the full descent
set `j = n - 1`, where it is `(-1) ^ n`; and at a non-negative integer `m ≥ j`, where it is the
shifted binomial coefficient `C(m - j + n - 1, n)` counting the words the polynomial was built to
count.

Two further facts of the route live here because they are about polynomials rather than words: a
polynomial over a characteristic-zero domain vanishing at every non-negative integer is zero,
which is what turns the numerical identity into a polynomial identity, and a descent set of the
maximal size `n - 1` is the full set `{1, …, n - 1}`, which is what identifies the surviving
terms after `t = -1` is substituted.
-/

@[expose] public section

open Finset
open scoped Nat

namespace HJO.Sym

section DescentPoly

variable (K : Type*) [CommRing K] [Algebra ℚ K]

/-- The reciprocal of `n!`, taken in `K` through its `ℚ`-algebra structure, cancels the image of
`n!`. This is the only arithmetic of the denominator of `descentPoly` that its values need. -/
theorem inv_factorial_mul_factorial (n : ℕ) :
    algebraMap ℚ K ((n ! : ℚ)⁻¹) * (n ! : K) = 1 := by
  rw [← map_natCast (algebraMap ℚ K) (n !), ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), map_one]

/-- The value of the descent polynomial, read off the product with its denominator cleared: if
`n!` times a candidate value is the product `∏_{r < n} (x - j + r)`, then that candidate is the
value. Every value computed below is computed in this shape. -/
theorem eval_descentPoly_of_factorial_mul {n j : ℕ} {x v : K}
    (h : ∏ r ∈ range n, (x - j + r) = (n ! : K) * v) :
    (descentPoly K n j).eval x = v := by
  rw [eval_descentPoly, h, ← mul_assoc, inv_factorial_mul_factorial, one_mul]

/-- **The roots of the descent polynomial**: `D_{n,j}` vanishes at every integer `x` of the window
`j - n + 1 ≤ x ≤ j`, the factor indexed by `r = j - x` being zero there. The hypothesis `n ≥ 1`
is not needed: at `n = 0` the window is empty, so the hypotheses cannot both hold. -/
@[hjo "lem_descent_poly_root"]
theorem eval_descentPoly_intCast_eq_zero (n : ℕ) (j : ℕ) {x : ℤ}
    (hlow : (j : ℤ) - n + 1 ≤ x) (hhigh : x ≤ (j : ℤ)) :
    (descentPoly K n j).eval ((x : ℤ) : K) = 0 := by
  rw [eval_descentPoly]
  refine mul_eq_zero_of_right _ (prod_eq_zero (i := (j - x).toNat) (mem_range.mpr ?_) ?_)
  · omega
  · have h1 : ((((j : ℤ) - x).toNat : ℕ) : ℤ) = (j : ℤ) - x := Int.toNat_of_nonneg (by omega)
    have hz : ((((j : ℤ) - x).toNat : ℕ) : K) = (j : K) - ((x : ℤ) : K) := by
      rw [← Int.cast_natCast (R := K), h1]
      push_cast
      ring
    rw [hz]
    ring

/-- **The descent polynomial at `-1` for a full descent set**: `D_{n, n-1}(-1) = (-1) ^ n`. The
factors are `-n, …, -1`, so the product is `(-1) ^ n` times `n!`, and the denominator cancels. -/
@[hjo "lem_descent_poly_full"]
theorem eval_descentPoly_neg_one {n : ℕ} (hn : 1 ≤ n) :
    (descentPoly K n (n - 1)).eval (-1) = (-1) ^ n := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  refine eval_descentPoly_of_factorial_mul K ?_
  have hfactor : ∀ r ∈ range (N + 1),
      ((-1 : K) - ((N + 1 - 1 : ℕ) : K) + r) = -(((N + 1 - r : ℕ) : K)) := by
    intro r hr
    have hrn : r < N + 1 := mem_range.mp hr
    rw [Nat.cast_sub (le_of_lt hrn)]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  have hfac : ∏ r ∈ range (N + 1), (N + 1 - r) = (N + 1)! := by
    rw [← prod_range_reflect (fun r => N + 1 - r) (N + 1)]
    rw [← Finset.prod_range_add_one_eq_factorial (N + 1)]
    exact prod_congr rfl fun r hr => by have := mem_range.mp hr; omega
  rw [prod_congr rfl hfactor, prod_neg, card_range, ← Nat.cast_prod, hfac]
  ring

/-- The descent polynomial at `-1` for a full descent set, in the shape its use sites have: on
degree `n + 1` the full descent set `{1, …, n}` has `n` elements, so no truncated subtraction
occurs. -/
theorem eval_descentPoly_neg_one_succ (n : ℕ) :
    (descentPoly K (n + 1) n).eval (-1) = (-1) ^ (n + 1) := by
  have h := eval_descentPoly_neg_one K (n := n + 1) (by omega)
  rwa [Nat.add_sub_cancel] at h

/-- **The descent polynomial counts at a non-negative integer**: for `j ≤ m` the value
`D_{n,j}(m)` is the image in `K` of the shifted binomial coefficient `C(m - j + n - 1, n)`, the
product `∏_{r < n} (m - j + r)` being the ascending factorial of `m - j`. The hypothesis `n ≥ 1`
is not needed: at `n = 0` both sides are `1`. -/
@[hjo "lem_descent_poly_binom"]
theorem eval_descentPoly_natCast (n : ℕ) {j m : ℕ} (hjm : j ≤ m) :
    (descentPoly K n j).eval (m : K) = (((m - j + n - 1).choose n : ℕ) : K) := by
  refine eval_descentPoly_of_factorial_mul K ?_
  have hfactor : ∀ r ∈ range n, ((m : K) - j + r) = (((m - j + r : ℕ)) : K) := by
    intro r _
    rw [Nat.cast_add, Nat.cast_sub hjm]
  rw [prod_congr rfl hfactor, ← Nat.cast_prod, ← Nat.ascFactorial_eq_prod_range,
    Nat.ascFactorial_eq_factorial_mul_choose']
  push_cast
  ring

end DescentPoly

/-- **A polynomial vanishing at every non-negative integer is zero**: over a characteristic-zero
domain the images of `0, 1, 2, …` are infinitely many distinct roots, and a nonzero polynomial has
finitely many. This is what turns the identity of values at every letter count into an identity of
polynomials, so that `t = -1` may be substituted. -/
@[hjo "lem_poly_nat_vanish"]
theorem eq_zero_of_eval_natCast_eq_zero {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    {P : Polynomial K} (h : ∀ m : ℕ, P.eval (m : K) = 0) : P = 0 :=
  P.eq_zero_of_infinite_isRoot
    (Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (m : K)) Nat.cast_injective h)

/-- **A descent set of maximal size is full**: a subset of `{1, …, n - 1}` with `n - 1` elements
is `{1, …, n - 1}`. This is what identifies the terms surviving the substitution `t = -1` with the
terms whose descent set is full. -/
@[hjo "lem_full_descent_set"]
theorem eq_Ico_of_card_eq {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Ico 1 n) (hcard : #S = n - 1) :
    S = Ico 1 n :=
  eq_of_subset_of_card_le hS (by rw [Nat.card_Ico, hcard])

end HJO.Sym
