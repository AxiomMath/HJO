/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.Parameters
public meta import HJO.Attr

/-! # The Hall--Littlewood operators

The raising side of the Carlsson--Mellit layer is built from the family `B_r`, `r ∈ ℤ`, extracting
the coefficient of `z^r` from the displaced symmetric function against the alternating elementary
series. This file defines that family.

## Main definitions

* `HJO.Sym.elemSymmAlt`: the coefficients `(-1)^n e_n` of `Ω(z)`, at an integer index.
* `HJO.Sym.Bop`: the operator `B_r`.

## Implementation notes

The index `r` is an integer, and negative indices are not decoration: `B_{-1}` is what the
lowering recursion pairs against. The displacement `β f` has only non-negative powers of `w = z⁻¹`
and the series `Ω(z)` only non-negative powers of `z`, so `[z^r]` of the product is the finite sum
of the coefficient of `w^j` of `β f` against the coefficient of `Ω` at `r + j`, and the latter
vanishes for `r + j < 0`. That vanishing is `elemSymmAlt_of_neg`, and it is what makes the negative
indices right rather than an extension by zero.

For a non-negative index `B_r` is the basic operator `HJO.Sym.Dop q 0 r` (`bop_natCast`). The two
families are distinct over the field `ℚ(q, u)`, where `u` is a free parameter, so that is
a specialisation and not an identification; it is what makes the `Dop` API available for `B_r` with
`r ≥ 0`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 3.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- The alternating elementary symmetric functions at an integer index: `(-1)ⁿ eₙ` for `n ≥ 0`
and `0` for `n < 0`. These are the Laurent coefficients of the series
`Ω(z) = ∑_{n ≥ 0} (-1)ⁿ eₙ zⁿ`, which has no negative-exponent term; the vanishing below `0` is
what makes the Hall--Littlewood operators of negative index right. -/
noncomputable def elemSymmAlt (K : Type*) [CommRing K] [Algebra ℚ K] (n : ℤ) : Lambda K :=
  if 0 ≤ n then (-1) ^ n.toNat * elemSymm K n.toNat else 0

@[simp]
theorem elemSymmAlt_natCast (n : ℕ) : elemSymmAlt K (n : ℤ) = (-1) ^ n * elemSymm K n := by
  simp [elemSymmAlt]

@[simp]
theorem elemSymmAlt_of_neg {n : ℤ} (hn : n < 0) : elemSymmAlt K n = 0 := by
  simp [elemSymmAlt, hn.not_ge]

/-- **The Hall--Littlewood operator** `B_r`, for `r : ℤ`: the `K`-linear endomorphism of
`Lambda K` extracting the coefficient of `zʳ` from `f[X - (q - 1)/z] ∑_{n ≥ 0} (-z)ⁿ eₙ`. Written
in `w = z⁻¹` the coefficient of `wʲ` of the displacement is paired with the coefficient of the
alternating elementary series at `r + j`, which vanishes for `r + j < 0`. -/
@[hjo "def_cm_bop"]
noncomputable def Bop (q : K) (r : ℤ) : Module.End K (Lambda K) :=
  coeffPairing (fun j => elemSymmAlt K (r + j)) ∘ₗ (plethHallLittlewood q).toLinearMap

/-- **The defining formula of `B_r`**: the coefficient of `zʳ` in
`f[X - (q - 1)/z] ∑_{n ≥ 0} (-z)ⁿ eₙ` is the finite sum, over the support of the displacement
`β f` read in `w = z⁻¹`, of the coefficient of `wʲ` of `β f` against the coefficient of
`Ω(z) = ∑_{n ≥ 0} (-1)ⁿ eₙ zⁿ` at `r + j` — the pairs `(j, n)` with `n - j = r`. -/
@[hjo "def_cm_bop"]
theorem bop_apply (q : K) (r : ℤ) (f : Lambda K) :
    Bop q r f = (plethHallLittlewood q f).sum fun j A => A * elemSymmAlt K (r + j) := rfl

/-- For a non-negative index the Hall--Littlewood operator is the basic operator
`HJO.Sym.Dop q 0 r` of `HJO.Sym.DopInt`: the displacements agree at `u = 0` and the two pairing
families agree, every index `r + j` being non-negative. The two families are distinct over the
field `ℚ(q, u)`, where `u` is free, so this is a specialisation and not an identification;
it is what makes the `Dop` API available for `B_r` with `r ≥ 0`. -/
theorem bop_natCast (q : K) (k : ℕ) : Bop q (k : ℤ) = Dop q 0 k := by
  have hfam : (fun j : ℕ => elemSymmAlt K ((k : ℤ) + j))
      = fun j : ℕ => (-1) ^ (k + j) * elemSymm K (k + j) := by
    funext j
    rw [show ((k : ℤ) + j) = ((k + j : ℕ) : ℤ) by push_cast; ring, elemSymmAlt_natCast]
  rw [Bop, Dop, plethHallLittlewood_eq_plethShift, hfam]

/-- **The normalisation of the family**: `B_r 1` is the coefficient of the alternating elementary
series at `r`, so `(-1)ʳ e_r` for `r ≥ 0` and `0` for `r < 0`. This is the convention used here;
Haglund--Morse--Zabrocki's `𝔹_r` gives `e_r` at `1`.

The statement is usually given for `r ≥ 0` in the form `B_r(1) = (-1)^r e_r`: that is the value of
`HJO.Sym.elemSymmAlt` at a non-negative index (`elemSymmAlt_natCast`), and the integer statement
here adds the negative indices, where the value is `0`. -/
@[hjo "lem_cm_bop_one"]
theorem bop_one (q : K) (r : ℤ) : Bop q r 1 = elemSymmAlt K r := by
  rw [bop_apply, map_one, ← Polynomial.C_1, Polynomial.sum_C_index (by simp)]
  simp

/-- The Hall--Littlewood operator on a power sum: the displacement of `p_k` has the two
coefficients `p_k` at `w⁰` and `1 - qᵏ` at `wᵏ`, so `B_r p_k = p_k Ω_r + (1 - qᵏ) Ω_{r+k}`, where
`Ω_n` is the coefficient of the alternating elementary series at `n`. At `k = 1` and `r = -1` the
first term vanishes and the value is `1 - q`. -/
theorem bop_powerSum (q : K) (r : ℤ) {k : ℕ} (hk : 0 < k) :
    Bop q r (powerSum K k) = powerSum K k * elemSymmAlt K r
      + MvPolynomial.C (1 - q ^ k) * elemSymmAlt K (r + k) := by
  have hC : ∀ (c : ℕ → Lambda K) (a : Lambda K), coeffPairing c (Polynomial.C a) = a * c 0 :=
    fun c a => Polynomial.sum_C_index (f := fun j A => A * c j) (by simp)
  have hmono : ∀ (c : ℕ → Lambda K) (n : ℕ) (a : Lambda K),
      coeffPairing c (Polynomial.monomial n a) = a * c n :=
    fun c n a => Polynomial.sum_monomial_index a (fun j A => A * c j) (by simp)
  rw [Bop, LinearMap.comp_apply, AlgHom.toLinearMap_apply, plethHallLittlewood_powerSum q hk,
    Polynomial.C_mul_X_pow_eq_monomial, map_add, hC, hmono, Nat.cast_zero, add_zero]

end HJO.Sym
