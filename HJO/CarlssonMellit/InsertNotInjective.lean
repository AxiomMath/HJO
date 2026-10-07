/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PowerRing
public meta import HJO.Attr

/-! # The insertion is not injective on all of `P_k`

The insertion `Φ_k` is naturally described as a map from `P_k` to `P_{k+1}`, and as an injective
one. The first description is false as stated, so the second is not a well-posed statement about a
map on all of `P_k`: substituting
`y_{k+1}` for `x₁` turns an unbounded `x₁`-degree into an unbounded `y_{k+1}`-degree, which the
*polynomial* coefficients of `P_{k+1}` cannot carry. The series `∑_{a ≥ 0} x₁^a` is an element of
`P_k` whose image would have to be the constant `∑_{a ≥ 0} y_{k+1}^a`, and that is not a polynomial
in `y_{k+1}`.

`HJO.Sym.insertFront` is the total extension of the substitution by `0` at the
letter-monomials where the sum is infinite — which is the only way to write it as a function on the
whole of `P_k`, and which its own docstring records. This file records the consequence: that
extension is **not** injective, so injectivity on all of `P_k` fails for
`HJO.Sym.insertFront`. The witness is the series above, which the extension
sends to `0`.

What the natural argument for injectivity does establish is injectivity on monomials,
which is true and is the part used downstream; the step from there to injectivity on `P_k` is
exactly the step that needs the map to be defined, and it is the one that fails. So the statement
needs a restatement — injectivity on the subring of series of bounded `x₁`-degree at each
letter-monomial, or on the graded pieces, which is where every application actually lives, and
which is `HJO.Sym.injOn_insertFront` — and is not merely an unfinished proof.

## Main results

* `HJO.Sym.not_injective_insertFront`: `Φ_k`, as the total extension `HJO.Sym.insertFront`, is not
  injective, so injectivity on all of `P_k` fails for that rendering.

## Implementation notes

The witness is the indicator of the letter-monomials supported at the first letter: the series whose
coefficient is `1` at `x₁^a` for every `a` and `0` elsewhere. At the empty letter-monomial the
defining sum of `insertFront` is `∑ᶠ a, y_{k+1}^a`, whose support is all of `ℕ`, so `finsum` returns
`0`; at every other letter-monomial every term already vanishes, the pushed-up monomial being
supported away from the first letter. So the image is `0`, while the witness is not, its coefficient
at the empty monomial being `1`. Nontriviality of the base is needed and nothing else.

## References

The file concerns the definition `HJO.Sym.insertFront` and the lemma
`HJO.Sym.injOn_insertFront`, used in the raising and lowering recursions.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K]

/-- The witness: the series whose coefficient is `1` at each power of the first letter and `0` at
every other letter-monomial. It lies in `P_k` — a formal power series has no bound on its degrees —
and its `x₁`-degree is unbounded at the empty letter-monomial, which is exactly what
`Φ_k` cannot act on. -/
noncomputable def firstLetterGeometric (K : Type*) [CommRing K] (k : ℕ) :
    AuxAlphabetSeries K k :=
  fun e => if e.support ⊆ {0} then 1 else 0

theorem coeff_firstLetterGeometric (k : ℕ) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (firstLetterGeometric K k) = if e.support ⊆ {0} then 1 else 0 :=
  rfl

/-- The witness is nonzero: its coefficient at the empty letter-monomial is `1`. -/
theorem firstLetterGeometric_ne_zero [Nontrivial K] (k : ℕ) :
    firstLetterGeometric K k ≠ 0 := by
  intro h
  have h1 : MvPowerSeries.coeff (0 : ℕ →₀ ℕ) (firstLetterGeometric K k) = 1 := by
    rw [coeff_firstLetterGeometric, ite_eq_left (by simp)]
  rw [h, map_zero] at h1
  exact one_ne_zero h1.symm

/-- The insertion sends the witness to `0`: at the empty letter-monomial the defining sum is
`∑ᶠ a, y_{k+1}^a`, whose support is all of `ℕ`, and at every other letter-monomial every term
vanishes. -/
theorem insertFront_firstLetterGeometric [Nontrivial K] (k : ℕ) :
    insertFront K k (firstLetterGeometric K k) = 0 := by
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_insertFront, map_zero]
  by_cases he : e = 0
  · subst he
    refine finsum_of_infinite_support ?_
    refine Set.Infinite.mono (fun a (ha : a ∈ (Set.univ : Set ℕ)) => ?_) Set.infinite_univ
    have hcoeff : MvPowerSeries.coeff (Finsupp.single 0 a + (0 : ℕ →₀ ℕ).mapDomain Nat.succ)
        (firstLetterGeometric K k) = 1 := by
      rw [Finsupp.mapDomain_zero, add_zero, coeff_firstLetterGeometric,
        ite_eq_left Finsupp.support_single_subset]
    rw [Function.mem_support, hcoeff, map_one, mul_one]
    rw [MvPolynomial.X_pow_eq_monomial]
    exact fun hc => one_ne_zero (MvPolynomial.monomial_eq_zero.1 hc)
  · refine finsum_eq_zero_of_forall_eq_zero fun a => ?_
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 he
    have hmem : j + 1 ∈ (Finsupp.single 0 a + e.mapDomain Nat.succ).support := by
      refine Finsupp.mem_support_iff.2 ?_
      have hsingle : (Finsupp.single (0 : ℕ) a) (j + 1) = 0 :=
        Finsupp.single_eq_of_ne (by omega)
      have hmap : (e.mapDomain Nat.succ) (j + 1) = e j :=
        Finsupp.mapDomain_apply Nat.succ_injective e j
      rw [Finsupp.add_apply, hsingle, hmap, zero_add]
      simpa using hj
    have hcoeff : MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ)
        (firstLetterGeometric K k) = 0 := by
      refine (coeff_firstLetterGeometric k _).trans (ite_eq_right fun hsub => ?_)
      have := hsub hmem
      simp at this
    rw [hcoeff, map_zero, mul_zero]

/-- **The insertion is not injective**, so injectivity on all of `P_k` is false at
`HJO.Sym.insertFront`, the only total rendering of `Φ_k` on `P_k`. The witness
`HJO.Sym.firstLetterGeometric` is nonzero and has image `0`. The natural argument establishes
injectivity on *monomials*, which is true; what fails is the passage from there to all of `P_k`,
and it fails because `Φ_k` is not defined there — see this file's module docstring. -/
theorem not_injective_insertFront (K : Type*) [CommRing K] [Nontrivial K] (k : ℕ) :
    ¬ Function.Injective (insertFront K k) := fun h =>
  firstLetterGeometric_ne_zero k
    (h ((insertFront_firstLetterGeometric k).trans (insertFront_zero k).symm))

end HJO.Sym
