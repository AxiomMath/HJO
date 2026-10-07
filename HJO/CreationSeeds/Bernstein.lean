/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The Bernstein displacement

The elementary symmetric functions are recovered from the creation operators by expanding the
creation displacement `δ'` of `Sym.plethCreate` around the displacement that removes a single
letter from the alphabet. This file defines that displacement: the Bernstein displacement `δ₀`,
sending `p_k` to `p_k - z⁻ᵏ` and written `f[X - 1/z]` on elements.

Like `Sym.plethShift` and `Sym.plethCreate`, it is written in the variable `w = z⁻¹` rather than
in the Laurent ring `Λ[z, z⁻¹]`: only non-negative powers of `w` occur in the image
of a generator, hence in the image of anything, so the target is the honest polynomial ring `Λ[w]`
and extracting the coefficient of a power of `z` from a product with a power series in `z` stays a
finite sum. The inclusion `ι : Λ → Λ[w]` is `Polynomial.C`.

Since `Lambda K` is the polynomial algebra on the generators `p_1, p_2, …` -- generator `i` of
`MvPolynomial ℕ K` standing for `p_{i+1}` -- prescribing the images of the `p_k` determines an
algebra homomorphism, and `MvPolynomial.aeval` is that prescription. The natural subtraction in
`Sym.powerSum` makes `powerSum K 0` the same generator as `powerSum K 1`, so the characterisation
`plethBernstein_powerSum` carries the hypothesis `k ≥ 1`; the raw form on generators is
`plethBernstein_X`.
-/

@[expose] public section

namespace HJO.Sym

/-- The Bernstein displacement `δ₀`: the `K`-algebra homomorphism from `Lambda K` to
`Polynomial (Lambda K)` sending `p_k` to `p_k - z⁻ᵏ`, written `f[X - 1/z]` on elements; the minus
sign is a virtual difference of alphabets, so removing the letter `1/z` is not adding `-1/z`. Its
target is the polynomial ring on `w = z⁻¹`. It is the creation displacement `Sym.plethCreate` with
the scalar `1 - q⁻¹` deleted, so it carries no parameter and needs no inverses: it is defined over
any commutative ring. -/
@[hjo "def_pleth_bernstein"]
noncomputable def plethBernstein (K : Type*) [CommRing K] :
    Lambda K →ₐ[K] Polynomial (Lambda K) :=
  MvPolynomial.aeval fun i => Polynomial.C (powerSum K (i + 1)) - Polynomial.X ^ (i + 1)

variable {K : Type*} [CommRing K]

/-- The Bernstein displacement on the generator `i` of `Lambda K`, which stands for `p_{i+1}`. -/
@[simp]
theorem plethBernstein_X (i : ℕ) :
    plethBernstein K (MvPolynomial.X i) =
      Polynomial.C (powerSum K (i + 1)) - Polynomial.X ^ (i + 1) := by
  simp [plethBernstein]

/-- **The defining property of the Bernstein displacement**: it sends `p_k` to `p_k - z⁻ᵏ` for
every `k ≥ 1`, the inclusion `Λ → Λ[w]` being `Polynomial.C`. -/
@[hjo "def_pleth_bernstein"]
theorem plethBernstein_powerSum {k : ℕ} (hk : 0 < k) :
    plethBernstein K (powerSum K k) = Polynomial.C (powerSum K k) - Polynomial.X ^ k := by
  rw [powerSum, plethBernstein_X, Nat.sub_add_cancel hk, powerSum]

/-- The Bernstein displacement of a constant is that constant. -/
@[simp]
theorem plethBernstein_C (a : K) :
    plethBernstein K (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  simp [plethBernstein]

end HJO.Sym
