/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.KernelExpansion
public import HJO.Collinear.WordMap
public meta import HJO.Attr

/-! # Clearing the denominator on the rational kernel factor

The kernel factor
`Ω_k = ∏_{i<j} (1 - z_i/z_j)(1 - qu z_i/z_j) / ((1 - q z_i/z_j)(1 - u z_i/z_j))` of
`HJO.Sym.dopKernelFactor` is a *rational* function: a genuine quotient in the fraction field
`𝕜(z_1, …, z_k) = FractionRing (MvPolynomial (Fin k) K)`. Multiplying it by the **kernel
denominator**

`Θ_k = ∏_{i ≠ j} (1 - q z_i/z_j)(1 - u z_i/z_j)`,

the product over the *ordered* pairs of distinct indices, clears every denominator: the factors of
`Θ_k` indexed by the pairs with `i < j` are exactly the denominator of `Ω_k` and cancel against it,
while the factors indexed by the pairs with `i > j` survive, so that

`Θ_k Ω_k = ∏_{i<j} (1 - z_i/z_j)(1 - qu z_i/z_j)(1 - q z_j/z_i)(1 - u z_j/z_i)`.

That right-hand side is the same Laurent polynomial as the one the formal-sum analogue
`HJO.Bglx.kernelDenom_mul_kernelExpansion` produces in the cone ring, and comparing the two
clearings is how the expansion `Ω̂_k` gets identified with the rational function `Ω_k`.

## Main definitions

* `HJO.Bglx.zVar`: the variable `z_i` read in the fraction field — the `z` of the body of
  `HJO.Sym.dopKernelFactor`, named so that the two statements are visibly about the same objects.
* `HJO.Bglx.kernelDenomRat`: the kernel denominator `Θ_k` as a rational function.

## Main statements

* `HJO.Bglx.zVar_ne_zero`: a variable is nonzero in the fraction field.
* `HJO.Bglx.one_sub_C_mul_div_ne_zero`: for `i ≠ j` and *any* scalar `a`, the element
  `1 - a z_i/z_j` is nonzero. This is what makes the cancellation legitimate.
* `HJO.Bglx.kernelDenomRat_mul_dopKernelFactor`: clearing the denominator on the kernel factor.
* `HJO.Bglx.mvRatFuncSymmetrization_mem_adjoin_zVar`: symmetrisation maps the Laurent subalgebra
  `K[z_1^{±1}, …, z_k^{±1}]` into itself.

## Implementation notes

**Hypotheses.** The lemma is usually stated over `𝕜 = ℚ(q, u)`, saying only that "each factor is
a nonzero element of the field". Here the base is a general `K` with `CommRing K` and `IsDomain K` —
exactly the hypotheses of `HJO.Sym.dopKernelFactor`, which needs them so that
`MvPolynomial (Fin k) K` is a domain and its fraction field is a field. Nothing more is required:
`Field K` is *not* needed, and `Nontrivial K` comes free from `IsDomain K`. In particular **no
hypothesis on `q` or `u`** is needed, which is worth saying because the phrase "each factor
is nonzero" might suggest otherwise: `1 - a z_i/z_j` is nonzero for every scalar `a` whatsoever,
including `a = 0` and `a = 1`, because its numerator `z_j - a z_i` has coefficient `1` at the
monomial `z_j` as soon as `i ≠ j`. So the only hypothesis that phrase does not cover is
`IsDomain K`, and that one is forced by the statement even making sense.

**The finset split is shared with the formal-sum clearing.** The first step of the proof
— that the ordered pairs of distinct indices are the pairs `i < j` together with their transposes,
grouped as `∏_{i<j} [ f(i,j) · f(j,i) ]` — is `HJO.Bglx.prod_offDiag_pair` of
`HJO/Collinear/KernelExpansion.lean`, reused here rather than copied; that is why this file
imports `KernelExpansion`, whose other contents it does not use.

**`zVar` and the shape of the statement.** `HJO.Sym.dopKernelFactor` introduces its variables by a
`let` in its body, so `zVar` reproduces that `let` as a definition and
`HJO.Bglx.dopKernelFactor_eq` records that the two agree (by `rfl`); the scalars `q`, `u` and `qu`
are spelled through `algebraMap K _` in both places, as in the definition of
`HJO.Sym.dopKernelFactor`.

## References

F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the
theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, whose Theorem
2.1 is the vanishing criterion the kernel factor occurs in, and whose SSS Trick extracts
`z₁⁰ ⋯ z_m⁰` from `Sym_m F` for a Laurent polynomial `F` (equations (2.6) and (2.7)), leaving
implicit that `Sym_m F` is again a Laurent polynomial. -/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ}

/-! ### The variables in the fraction field -/

/-- The `i`-th variable read in the rational function field `𝕜(z_1, …, z_k)`: the image of
`MvPolynomial.X i` under the localisation map. This is the `z` of the body of
`HJO.Sym.dopKernelFactor`, written as a definition so that it can be named in a statement. -/
noncomputable def zVar (K : Type*) [CommRing K] [IsDomain K] {k : ℕ} (i : Fin k) :
    FractionRing (MvPolynomial (Fin k) K) :=
  algebraMap (MvPolynomial (Fin k) K) _ (MvPolynomial.X i)

/-- A variable is nonzero in the fraction field: `X i` is nonzero in the polynomial ring, and the
localisation map of a domain at its nonzero divisors is injective. -/
theorem zVar_ne_zero (i : Fin k) : zVar K i ≠ 0 := by
  rw [zVar, ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact MvPolynomial.X_ne_zero i

omit [IsDomain K] in
/-- A constant of the base ring, mapped into the fraction field through the polynomial ring, is the
image of that constant under the structure map of the field as a `K`-algebra. -/
theorem algebraMap_mvPolynomial_C (a : K) :
    algebraMap (MvPolynomial (Fin k) K) (FractionRing (MvPolynomial (Fin k) K))
        (MvPolynomial.C a) = algebraMap K _ a := by
  rw [← MvPolynomial.algebraMap_eq]
  exact (IsScalarTower.algebraMap_apply K (MvPolynomial (Fin k) K) _ a).symm

/-- The numerator of `1 - a z_i/z_j` after clearing `z_j`: for `i ≠ j` the polynomial
`z_j - a z_i` is nonzero, its coefficient at the monomial `z_j` being `1`. -/
theorem X_sub_C_mul_X_ne_zero (a : K) {i j : Fin k} (h : i ≠ j) :
    (MvPolynomial.X j - MvPolynomial.C a * MvPolynomial.X i : MvPolynomial (Fin k) K) ≠ 0 := by
  classical
  have hne : (Finsupp.single i 1 : Fin k →₀ ℕ) ≠ Finsupp.single j 1 := fun hh =>
    h (Finsupp.single_left_injective one_ne_zero hh)
  intro hc
  have hco := congrArg (MvPolynomial.coeff (Finsupp.single j 1)) hc
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
    MvPolynomial.coeff_X, ite_eq_left rfl, ite_eq_right hne, MvPolynomial.coeff_zero, mul_zero,
    sub_zero] at hco
  exact one_ne_zero hco

/-- **Each factor of the kernel denominator is nonzero.** For `i ≠ j` and *any* scalar `a`, the
element `1 - a z_i/z_j` of the fraction field is nonzero: it is `(z_j - a z_i)/z_j`, and the
numerator is nonzero by `HJO.Bglx.X_sub_C_mul_X_ne_zero`. No hypothesis on `a` is needed. -/
theorem one_sub_C_mul_div_ne_zero (a : K) {i j : Fin k} (h : i ≠ j) :
    1 - algebraMap K (FractionRing (MvPolynomial (Fin k) K)) a * (zVar K i / zVar K j) ≠ 0 := by
  have hj : zVar K j ≠ 0 := zVar_ne_zero j
  have key : 1 - algebraMap K (FractionRing (MvPolynomial (Fin k) K)) a * (zVar K i / zVar K j)
      = algebraMap (MvPolynomial (Fin k) K) (FractionRing (MvPolynomial (Fin k) K))
          (MvPolynomial.X j - MvPolynomial.C a * MvPolynomial.X i) / zVar K j := by
    rw [map_sub, map_mul, algebraMap_mvPolynomial_C, sub_div, ← zVar, ← zVar, div_self hj,
      mul_div_assoc]
  rw [key, ne_eq, div_eq_zero_iff, not_or]
  refine ⟨?_, hj⟩
  rw [IsFractionRing.to_map_eq_zero_iff]
  exact X_sub_C_mul_X_ne_zero a h

/-- The cancellation the clearing is made of: multiplying `n / d` by `d` (and by a bystander `c`)
returns `n * c`, provided `d ≠ 0`. -/
theorem mul_mul_div_cancel {F : Type*} [Field F] {d : F} (hd : d ≠ 0) (n c : F) :
    d * c * (n / d) = n * c := by
  rw [mul_comm d c, mul_assoc, mul_div_cancel₀ _ hd, mul_comm]

/-! ### The kernel denominator and the clearing identity -/

/-- The kernel denominator as a rational function: `Θ_k = ∏_{i ≠ j}(1 - q z_i/z_j)(1 - u z_i/z_j)`,
the product over the ordered pairs of distinct indices. -/
@[hjo "def_bglx_kernel_denominator"]
noncomputable def kernelDenomRat (q u : K) (k : ℕ) : FractionRing (MvPolynomial (Fin k) K) :=
  ∏ p ∈ Finset.univ.offDiag,
    ((1 - algebraMap K _ q * (zVar K p.1 / zVar K p.2)) *
      (1 - algebraMap K _ u * (zVar K p.1 / zVar K p.2)))

/-- The kernel factor `Ω_k` of `HJO.Sym.dopKernelFactor`, with its `let`-bound variables named by
`HJO.Bglx.zVar`. -/
theorem dopKernelFactor_eq (q u : K) (k : ℕ) :
    dopKernelFactor q u k
      = ∏ i : Fin k, ∏ j ∈ Finset.Ioi i,
          (1 - zVar K i / zVar K j) * (1 - algebraMap K _ (q * u) * (zVar K i / zVar K j)) /
            ((1 - algebraMap K _ q * (zVar K i / zVar K j)) *
              (1 - algebraMap K _ u * (zVar K i / zVar K j))) :=
  rfl

/-- **Clearing the denominator on the kernel factor.** In `𝕜(z_1, …, z_k)`,
`Θ_k Ω_k = ∏_{i<j}(1 - z_i/z_j)(1 - qu z_i/z_j)(1 - q z_j/z_i)(1 - u z_j/z_i)`: the ordered pairs of
distinct indices split into the pairs `i < j` and their transposes, the first group is the
denominator of `Ω_k` and cancels it, and the second group survives. -/
@[hjo "lem_bglx_kernel_factor_clear"]
theorem kernelDenomRat_mul_dopKernelFactor (q u : K) (k : ℕ) :
    kernelDenomRat q u k * dopKernelFactor q u k
      = ∏ i : Fin k, ∏ j ∈ Finset.Ioi i,
          ((1 - zVar K i / zVar K j) * (1 - algebraMap K _ (q * u) * (zVar K i / zVar K j)) *
            ((1 - algebraMap K _ q * (zVar K j / zVar K i)) *
              (1 - algebraMap K _ u * (zVar K j / zVar K i)))) := by
  rw [kernelDenomRat, prod_offDiag_pair (fun a b =>
      (1 - algebraMap K _ q * (zVar K a / zVar K b)) *
        (1 - algebraMap K _ u * (zVar K a / zVar K b))),
    dopKernelFactor_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.1 hj)
  exact mul_mul_div_cancel
    (mul_ne_zero (one_sub_C_mul_div_ne_zero q hij) (one_sub_C_mul_div_ne_zero u hij)) _ _

/-! ### Symmetrisation preserves the Laurent polynomials -/

section SymLaurent

variable {K : Type*} [Field K] {k : ℕ}

/-- A family whose reindexing by a surjection `σ` of the index set is its relabelling by `g` has
`g`-invariant range: `g '' Set.range f = Set.range f` as soon as `f ∘ σ = g ∘ f`. -/
private theorem image_range_of_semiconj {ι M : Type*} {σ : ι → ι} {f : ι → M} {g : M → M}
    (hσ : Function.Surjective σ) (h : Function.Semiconj f σ g) :
    g '' Set.range f = Set.range f :=
  h.mapsTo_range.image_subset.antisymm (h.surjOn_range hσ)

/-- The automorphism of `K(z_1, …, z_k)` extending the relabelling `z_i ↦ z_{σ(i)}` of the
polynomial ring: one of the `k!` summands of `Sym_k`. -/
private noncomputable abbrev renameFieldEquiv (K : Type*) [Field K] {k : ℕ}
    (σ : Equiv.Perm (Fin k)) :
    FractionRing (MvPolynomial (Fin k) K) ≃ₐ[K] FractionRing (MvPolynomial (Fin k) K) :=
  IsFractionRing.fieldEquivOfAlgEquiv K _ _ (MvPolynomial.renameEquiv K σ)

/-- The relabelling carries the variable `z_i` to the variable `z_{σ i}`: on the image of the
polynomial ring the extension to the fraction field is the relabelling itself. -/
private theorem renameFieldEquiv_zVar (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    renameFieldEquiv K σ (zVar K i) = zVar K (σ i) := by
  simp [zVar, IsFractionRing.fieldEquivOfAlgEquiv_algebraMap]

/-- **The Laurent subalgebra is invariant under one relabelling.** The relabelling permutes the
generating set `{z_i} ∪ {z_i⁻¹}` of `K[z_1^{±1}, …, z_k^{±1}]`, so it maps the subalgebra that
set generates onto itself. -/
private theorem adjoin_zVar_map_renameFieldEquiv (σ : Equiv.Perm (Fin k)) :
    (Algebra.adjoin K (Set.range (fun i : Fin k => zVar K i) ∪
          Set.range fun i : Fin k => (zVar K i)⁻¹)).map (renameFieldEquiv K σ : _ →ₐ[K] _)
      = Algebra.adjoin K (Set.range (fun i : Fin k => zVar K i) ∪
          Set.range fun i : Fin k => (zVar K i)⁻¹) := by
  rw [AlgHom.map_adjoin, AlgEquiv.coe_toAlgHom, Set.image_union,
    image_range_of_semiconj (f := fun i : Fin k => zVar K i) σ.surjective
      fun i => (renameFieldEquiv_zVar σ i).symm,
    image_range_of_semiconj (f := fun i : Fin k => (zVar K i)⁻¹) σ.surjective
      fun i => by rw [map_inv₀, renameFieldEquiv_zVar]]

/-- **Symmetrisation preserves the Laurent polynomials.** If `F` lies in the `K`-subalgebra
`K[z₁^±1, …, z_k^±1]` of `K(z₁, …, z_k)` generated by the variables and their inverses, then so
does `Sym_k F = (1/k!) ∑_σ F(z_{σ(1)}, …, z_{σ(k)})`: each summand is a field automorphism
permuting the generators, so it maps the subalgebra onto itself, and the subalgebra is closed under
the average. -/
@[hjo "lem_bglx_sym_laurent"]
theorem mvRatFuncSymmetrization_mem_adjoin_zVar [CharZero K]
    {F : FractionRing (MvPolynomial (Fin k) K)}
    (hF : F ∈ Algebra.adjoin K (Set.range (fun i : Fin k => zVar K i) ∪
      Set.range fun i : Fin k => (zVar K i)⁻¹)) :
    mvRatFuncSymmetrization K k F ∈
      Algebra.adjoin K (Set.range (fun i : Fin k => zVar K i) ∪
        Set.range fun i : Fin k => (zVar K i)⁻¹) := by
  rw [mvRatFuncSymmetrization, LinearMap.smul_apply, LinearMap.sum_apply]
  exact Subalgebra.smul_mem _
    (sum_mem fun σ _ => (adjoin_zVar_map_renameFieldEquiv σ).le
      (Subalgebra.mem_map.2 ⟨F, hF, rfl⟩)) _

end SymLaurent

end HJO.Bglx
