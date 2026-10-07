/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CreationSeeds.LogDeriv
public meta import HJO.Attr

/-! # Adding a letter to `h`, and the complete homogeneous function of a composition

Three ingredients of the Gessel expansions: what one more letter does to a complete homogeneous
function, the product `h_α` over the parts of a composition, and the partial-sum set `ps(α)` that
`h_α` is paired with.

## Main definitions

* `HJO.Sym.completeHomogComp`: `h_α`.
* `HJO.Sym.compDescent`: `ps(α)`.

## Main statements

* `HJO.CreationSeeds.completeHomog_add_letter`.

## Implementation notes

`HJO.CreationSeeds.completeHomog_add_letter` is the `h`-side companion of
`HJO.CreationSeeds.elemSymm_sub_letter` and is proved the same way: the generating series of the
`h`'s has logarithmic derivative `∑ₖ φ(p_{k+1})zᵏ`
(`HJO.CreationSeeds.derivative_mk_completeHomog`), the geometric series `∑ⱼ aʲzʲ` has logarithmic
derivative `∑ₖ a^{k+1}zᵏ` (`HJO.CreationSeeds.derivative_geometric`), the hypothesis says these two
add up to the logarithmic derivative of `ψ`'s series
(`HJO.CreationSeeds.derivative_mul_of_logDeriv`), and both sides have constant term `1`, so
`HJO.CreationSeeds.powerSeries_ext_of_logDeriv` identifies them. Unlike the `e` side, no term
collapses: adding one letter to `hₙ` contributes at every degree, which is the asymmetry the two
lemmas record.

An alphabet is only ever touched through a ring homomorphism out of `Lambda K`, so "adding the
letter `a`" is "a second homomorphism exceeding the first by `aᵏ` on every power sum `p_k`" — the
phrasing `HJO.CreationSeeds.LogDeriv` already uses, so the same lemma serves over the
coefficient field and over `𝒫` with `a = x_m`.

A composition is a `List ℕ`, as for `HJO.Sym.elemSymmComp`: the order of the parts is visible,
which is what the descent-set arguments need, and the empty product is `1` by `List.prod`.

`ps(α)` is the *proper* prefix sums, `α₁ + ⋯ + α_i` for `1 ≤ i ≤ ℓ-1`. The truncated subtraction
`α.length - 1` is honest at the degenerate corner: for the empty composition it gives `0`, hence the
empty set, which is what "no `i` with `1 ≤ i ≤ -1`" means.

## References

This file formalises `HJO.CreationSeeds.completeHomog_add_letter`, `HJO.Sym.completeHomogComp` and
`HJO.Sym.compDescent`.
-/

@[expose] public section

open Finset

namespace HJO.CreationSeeds

section Letters

variable {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R] [Algebra ℚ R]
  {F G : Type*} [FunLike F (Sym.Lambda K) R] [RingHomClass F (Sym.Lambda K) R]
  [FunLike G (Sym.Lambda K) R] [RingHomClass G (Sym.Lambda K) R]

/-- **Adding one letter `a` to the alphabet.** If `ψ` exceeds `φ` by `aᵏ`
on every power sum `p_k`, then `ψ(hₙ) = ∑_{j=0}ⁿ aʲ φ(h_{n-j})`.

The generating series of `ψ`'s complete homogeneous functions is the geometric series `∑ⱼ aʲzʲ`
times that of `φ`'s: the two logarithmic derivatives add up to `ψ`'s by hypothesis, and both series
have constant term `1`. -/
@[hjo "lem_om_hsymm_add_letter"]
theorem completeHomog_add_letter (f : F) (g : G) (a : R)
    (h : ∀ k : ℕ, 0 < k → g (Sym.powerSum K k) = f (Sym.powerSum K k) + a ^ k) (n : ℕ) :
    g (Sym.completeHomog K n) = ∑ j ∈ range (n + 1), a ^ j * f (Sym.completeHomog K (n - j)) := by
  have hQ : (PowerSeries.mk fun k => a ^ (k + 1))
      + (PowerSeries.mk fun k => f (Sym.powerSum K (k + 1)))
      = PowerSeries.mk fun k => g (Sym.powerSum K (k + 1)) := by
    refine PowerSeries.ext fun k => ?_
    simp only [map_add, PowerSeries.coeff_mk]
    rw [h (k + 1) k.succ_pos]
    ring
  have hlog : PowerSeries.derivative R
        ((PowerSeries.mk fun j => a ^ j) * PowerSeries.mk fun n => f (Sym.completeHomog K n))
      = (PowerSeries.mk fun k => g (Sym.powerSum K (k + 1)))
        * ((PowerSeries.mk fun j => a ^ j)
          * PowerSeries.mk fun n => f (Sym.completeHomog K n)) := by
    rw [← hQ]
    exact derivative_mul_of_logDeriv (derivative_geometric a) (derivative_mk_completeHomog f)
  have key : (PowerSeries.mk fun n => g (Sym.completeHomog K n))
      = (PowerSeries.mk fun j => a ^ j)
        * PowerSeries.mk fun n => f (Sym.completeHomog K n) :=
    powerSeries_ext_of_logDeriv (derivative_mk_completeHomog g) hlog
      (by simp [PowerSeries.coeff_mul, CopPower.completeHomog_zero])
  have hc := congrArg (PowerSeries.coeff n) key
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simp only [PowerSeries.coeff_mk] at hc
  exact hc

end Letters

end HJO.CreationSeeds

namespace HJO.Sym

section Composition

variable (K : Type*) [CommRing K] [Algebra ℚ K]

/-- **The complete homogeneous function of a composition**
`h_α = h_{α₁}h_{α₂}⋯h_{α_ℓ}`, the empty product being `1`. The composition is the list of its
parts, as for `HJO.Sym.elemSymmComp`. -/
@[hjo "def_om_hsymm_comp"]
noncomputable def completeHomogComp (α : List ℕ) : Lambda K :=
  (α.map (completeHomog K)).prod

/-- `h_α` of the empty composition is `1`, the empty product. -/
@[hjo "def_om_hsymm_comp", simp]
theorem completeHomogComp_nil : completeHomogComp K [] = 1 := rfl

/-- `h_α` splits off its first part: `h_{(a, α)} = h_a h_α`. With `completeHomogComp_nil` this is
the product formula, read by induction on the list of parts. -/
@[hjo "def_om_hsymm_comp", simp]
theorem completeHomogComp_cons (a : ℕ) (α : List ℕ) :
    completeHomogComp K (a :: α) = completeHomog K a * completeHomogComp K α := by
  rw [completeHomogComp, completeHomogComp, List.map_cons, List.prod_cons]

/-- A value check: `h_{(2,1)} = h₂h₁`, a product of two factors in the order the composition lists
them. -/
theorem completeHomogComp_pair (a b : ℕ) :
    completeHomogComp K [a, b] = completeHomog K a * completeHomog K b := by
  rw [completeHomogComp_cons, completeHomogComp_cons, completeHomogComp_nil, mul_one]

end Composition

/-- **The partial-sum set of a composition**
`ps(α) = \{α₁ + ⋯ + α_i : 1 ≤ i ≤ ℓ-1\}`, the *proper* prefix sums.

`α.length - 1` is truncated subtraction, which is the intended reading at the degenerate corner:
for the empty composition there is no `i` at all, and the set is empty. -/
@[hjo "def_om_comp_descent"]
def compDescent (α : List ℕ) : Finset ℕ :=
  (range (α.length - 1)).image fun i => (α.take (i + 1)).sum

/-- **Membership in `ps(α)`**: an integer lies in it exactly when it is a proper prefix sum. -/
@[hjo "def_om_comp_descent"]
theorem mem_compDescent {α : List ℕ} {n : ℕ} :
    n ∈ compDescent α ↔ ∃ i < α.length - 1, (α.take (i + 1)).sum = n := by
  simp [compDescent]

/-- The partial-sum set of the empty composition is empty, and so is that of a one-part
composition: there are no proper prefixes in either case. -/
@[simp]
theorem compDescent_of_length_le_one {α : List ℕ} (h : α.length ≤ 1) : compDescent α = ∅ := by
  rw [compDescent, show α.length - 1 = 0 by omega, range_zero, image_empty]

/-- A value check: `ps((2,1,3)) = \{2, 3\}`, the two proper prefix sums and not the total `6`. The
error this rules out is reading the set as all prefix sums, which would add `6`. -/
theorem compDescent_two_one_three : compDescent [2, 1, 3] = {2, 3} := by
  decide +kernel

end HJO.Sym
