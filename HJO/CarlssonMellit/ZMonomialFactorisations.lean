/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Finsupp.Antidiagonal
public meta import HJO.Attr

/-! # A monomial in the merged alphabet has finitely many factorisations

The graded pieces `𝒵^{(k)}_d` of the series ring are spanned by the monomials of total degree `d`
in the letters `y_k, x₁, x₂, …`, and to multiply two such pieces one reads off the coefficient of a
monomial `μ` in a product as a sum over the ordered pairs `(μ', μ'')` with `μ = μ'μ''`. That sum is
only meaningful because there are finitely many such pairs, which is what this file records.

## Main results

* `HJO.Sym.finite_setOf_add_eq`: the set of ordered pairs of monomials whose product is a given
  monomial is finite.
* `HJO.Sym.coe_antidiagonal`: that set is the `Finset` `Finset.antidiagonal μ`, which is the form a
  finite sum over the factorisations takes.

## Implementation notes

A monomial in a family of letters is a function from the letters to `ℕ` of finite support — in
Mathlib, an element of `ι →₀ ℕ` for `ι` the type indexing the letters — and `μ = μ'μ''` says that
the exponent of each letter in `μ` is the sum of its exponents in `μ'` and `μ''`, i.e. that
`μ' + μ'' = μ` in `ι →₀ ℕ`. So the lemma is the finiteness of the additive antidiagonal of a
finitely supported function to `ℕ`.

The statement is made for an arbitrary index type `ι`, not for a type of letters specific to the
level `k`. The letters are `y_k, x₁, x₂, …`, one distinguished letter together with the
alphabet, but nothing in the statement or the proof distinguishes one letter from another, or uses
anything of the index type at all, so under *any* indexing of `y_k, x₁, x₂, …` the
required instance is this lemma at that `ι`. Fixing one `ι` would only commit the lemma to a
choice it is independent of.

Finiteness is not re-derived. Mathlib's `Finsupp.instHasAntidiagonal` already provides the `Finset`
of pairs summing to a given `μ : ι →₀ ℕ`, built by transporting `Multiset.antidiagonal` along
`Finsupp.toMultiset`, together with its membership criterion `Finset.mem_antidiagonal`; this is the
same machinery `MvPowerSeries.coeff_mul` uses to define multiplication of power series in the first
place. The direct proof — the factors are supported inside the support of `μ` and at each
letter of it the exponent of `μ'` is one of finitely many values, with `μ''` then determined — is
an independent argument for the same fact, and is not repeated. That instance needs
`DecidableEq ι`, which the `Set.Finite` statement does not mention and which `classical` supplies;
`coe_antidiagonal`, naming the `Finset` itself, takes it as a hypothesis.

## References

E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4.
-/

@[expose] public section

namespace HJO.Sym

variable {ι : Type*}

/-- **A monomial of given degree has finitely many factorisations**: for a monomial `μ` in the
letters `y_k, x₁, x₂, …`, recorded as the exponent vector `μ : ι →₀ ℕ` of finite support over any
indexing `ι` of those letters, only finitely many ordered pairs `(μ', μ'')` of monomials in the
same letters satisfy `μ = μ'μ''`, which in exponent vectors reads `μ' + μ'' = μ`. This is the
finiteness that makes the coefficient of `μ` in a product of two series a finite sum, hence the
multiplicativity of the alphabet grading. -/
@[hjo "lem_cm_zmon_factorisations"]
theorem finite_setOf_add_eq (μ : ι →₀ ℕ) :
    {p : (ι →₀ ℕ) × (ι →₀ ℕ) | p.1 + p.2 = μ}.Finite := by
  classical
  exact (Finset.antidiagonal μ).finite_toSet.subset fun _ hp => Finset.mem_antidiagonal.2 hp

/-- The factorisations of a monomial `μ`, as the `Finset` `Finset.antidiagonal μ`: the form in
which a sum over the pairs `(μ', μ'')` with `μ = μ'μ''` is written. -/
theorem coe_antidiagonal [DecidableEq ι] (μ : ι →₀ ℕ) :
    (Finset.antidiagonal μ : Set ((ι →₀ ℕ) × (ι →₀ ℕ))) =
      {p : (ι →₀ ℕ) × (ι →₀ ℕ) | p.1 + p.2 = μ} := by
  ext p
  simp

end HJO.Sym
