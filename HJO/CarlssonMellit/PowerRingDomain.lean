/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import HJO.CarlssonMellit.PowerRing
public meta import HJO.Attr

/-! # The series ring of the Carlsson--Mellit recursions is a domain

The operator `Δ_m` of the merged alphabet is a division in disguise: it names "the `H` with
`(z^{(k)}_{m+1} - z^{(k)}_m) H = ⋯`", and the divisor has no constant term, so it is not
invertible in `P°_k`. Uniqueness of such an `H` is therefore all that stands in for a quotient,
and uniqueness rests on `P°_k = 𝕂(y₁, …, y_k)⟦x₁, x₂, …⟧` having no zero divisors. This file
records that.

## Main results

* `HJO.Sym.isDomain_auxAlphabetSeriesFrac`: `P°_k` is an integral domain.

## Implementation notes

One can prove this by hand: order the letter-monomials by total degree and then arbitrarily,
take the least monomial with a nonzero coefficient in each of two nonzero series, and observe that
the product of those two least monomials receives exactly one contribution in the product. That is
the argument Mathlib's `MvPowerSeries.instNoZeroDivisors` carries out through
`MvPowerSeries.lexOrder_mul`, with a well-order on the alphabet supplied by
`Finsupp.exists_wellFoundedGT`; nothing about the index type `ℕ` is needed beyond its being a
type, and nothing about the coefficient ring beyond its having no zero divisors. So the lemma is an
instance derivation, and the only real work is the domain-ness of the coefficient ring.

That domain-ness is where a hypothesis on `K` enters, and it is genuine rather than bookkeeping:
`P°_k` has `FractionRing (MvPolynomial (Fin k) K)` for coefficients, and `FractionRing` is the total
ring of fractions of an arbitrary commutative ring, which over a ring with zero divisors has zero
divisors of its own. It is a *field* exactly when the ring it localizes is a domain. So the
statement carries `[IsDomain K]`, which forces `MvPolynomial (Fin k) K` to be a domain and its
fraction ring to be a field. The base ring of interest is `𝕂 = ℚ(q, u)`, a field and in particular a
domain, so the hypothesis holds in the only case the layer instantiates; the definition
`AuxAlphabetSeriesFrac` deliberately does not bake it into the ring, per the implementation notes of
`HJO.CarlssonMellit.PowerRing`, which is why it is stated here instead.

The result is registered as an `instance` rather than a plain theorem: every consumer of this fact
— the uniqueness statements of the `Δ_m` layer — wants it by typeclass inference at a
`mul_eq_zero` or a `mul_left_cancel₀`, and Mathlib has `NoZeroDivisors (MvPowerSeries σ R)` but no
`IsDomain (MvPowerSeries σ R)` for inference to land on.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc.
**31** (2018) 661--697, Section 4.
-/

@[expose] public section

namespace HJO.Sym

/-- **The series ring is a domain**: for every `k ≥ 0` the ring `P°_k = 𝕂(y₁, …, y_k)⟦x₁, x₂, …⟧` of
`HJO.Sym.AuxAlphabetSeriesFrac` is an integral domain, over any base ring `K` that is one. The
hypothesis is needed for the coefficients: `FractionRing` is the total ring of fractions of an
arbitrary commutative ring, and it is a field — hence has no zero divisors — exactly because
`MvPolynomial (Fin k) K` is a domain, which is where `[IsDomain K]` is spent. The base `𝕂 = ℚ(q, u)`
of interest is a field, so the hypothesis holds there. The power-series half is
`MvPowerSeries.instNoZeroDivisors`, whose proof is the argument sketched in the module
documentation: the lexicographically least letter-monomial of a product is the sum of the least
monomials of the factors. -/
@[hjo "lem_cm_pring_domain"]
instance isDomain_auxAlphabetSeriesFrac (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    IsDomain (AuxAlphabetSeriesFrac K k) :=
  NoZeroDivisors.to_isDomain _

end HJO.Sym
