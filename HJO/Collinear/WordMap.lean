/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Localization.FractionRing
public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # Words in the basic operators: the operator, the symbol, the raise, and the criterion's data

The basic operators `Dop q u 0, Dop q u 1, Dop q u 2, …` generate a subalgebra `𝖠` of
`Module.End L (Lambda L)`, and the two questions BGLX ask about that subalgebra — which
combinations of the generators act by zero, and whether raising every index preserves vanishing —
are questions about *words* in the generators. A word of length `k` is a tuple `a : Fin k → ℕ` of
indices, a combination of words of length `k` is a finitely supported `c : (Fin k → ℕ) →₀ K`, and
the criterion that decides vanishing is a statement about the *symmetrised symbol* of `c`. This
file supplies the four objects those statements are made of, together with the symmetrisation
operator itself:

* the operator `V_c = ∑ a, c a • (D_{a_k} ⋯ D_{a_1})` a family names;
* its symbol `Π_c = ∑ a, c a • z₁^{-a₁} ⋯ z_k^{-a_k}`, a Laurent polynomial;
* the raise `c ↦ c⁺`, which raises every index of every word by one;
* the kernel factor `Ω_k = ∏_{i<j} (1 - zᵢ/z_j)(1 - qu zᵢ/z_j)/((1 - q zᵢ/z_j)(1 - u zᵢ/z_j))`,
  the one part of the criterion independent of the family;
* symmetrisation `F ↦ (1/k!) ∑_σ σ_* F` of rational functions in `k` variables.

## Main definitions

* `HJO.Sym.dopWordOperator`: the operator `V_c` of a coefficient family, as a linear map in `c`.
* `HJO.Sym.dopWordSymbol`: the symbol `Π_c`, as a linear map in `c`.
* `HJO.Sym.dopWordRaise`: the raise `c ↦ c⁺`.
* `HJO.Sym.dopKernelFactor`: the kernel factor `Ω_k`.
* `HJO.Sym.mvRatFuncSymmetrization`: symmetrisation in `k` variables.

## Implementation notes

Each of the five is bundled as a linear map where it is linear, because every use the argument
makes of it is a use of that linearity or of its kernel: the families acting by zero are
`LinearMap.ker (dopWordOperator q u k)`, a submodule, and both the vanishing criterion and the
theorem that raising every index preserves vanishing are statements about that submodule.

The hypotheses are per-definition and are the weakest each one needs, not a common set: the symbol
is an identity about exponents and asks only `CommSemiring`, the raise only `Semiring`, the
operator `CommRing` with `Algebra ℚ K` as `Dop` itself does, the kernel factor `CommRing` with
`IsDomain` so that the quotients exist, and the symmetrisation `Field` with `CharZero` so that
`k!` is invertible.

The Laurent polynomial ring is the group algebra `AddMonoidAlgebra K (Fin k →₀ ℤ)` of the exponent
lattice, so the variable `z i` is the monomial `AddMonoidAlgebra.single (Finsupp.single i 1) 1`;
no division is needed to state anything about it, negative exponents being exponents like any
other. The kernel factor, by contrast, genuinely divides, and so lives in the rational function
field `FractionRing (MvPolynomial (Fin k) K)`.

## References

The reference for the definitions `HJO.Sym.dopWordOperator`, `HJO.Sym.dopWordSymbol`,
`HJO.Sym.dopWordRaise`, `HJO.Sym.dopKernelFactor` and `HJO.Sym.mvRatFuncSymmetrization` is
F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the
theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, whose
Theorem 2.1 is the criterion these objects state and whose Theorem 2.2 is the raise.
-/

@[expose] public section

namespace HJO.Sym

/-- The operator of a coefficient family: for a finitely supported family `c` of scalars indexed
by the words `a : Fin k → ℕ` of length `k` in the basic operators, the `K`-linear combination
`∑ a, c a • (Dop q u aₖ ∘ ⋯ ∘ Dop q u a₁)`, an endomorphism of `Lambda K`. The rightmost factor
carries the first index, as in BGLX. Bundled as a linear map in `c`, whose kernel is the
family of combinations acting by zero. -/
@[hjo "def_bglx_word_operator"]
noncomputable def dopWordOperator {K : Type*} [CommRing K] [Algebra ℚ K] (q u : K) (k : ℕ) :
    ((Fin k → ℕ) →₀ K) →ₗ[K] Module.End K (Lambda K) :=
  Finsupp.linearCombination K fun a => (List.ofFn fun i => Dop q u (a i)).reverse.prod

/-- The symbol of a coefficient family: for a finitely supported family `c` of scalars indexed by
the words `a : Fin k → ℕ` of length `k` in the basic operators, the Laurent polynomial
`∑ a, c a • z₁^(-a₁) ⋯ z_k^(-a_k)` in `k` variables, the exponents being the negatives of the
indices of the word, as in BGLX. Bundled as a linear map in `c`; the Laurent polynomial ring
`K[z₁^±1, …, z_k^±1]` is the group algebra of the exponent lattice `Fin k →₀ ℤ`. -/
@[hjo "def_bglx_word_symbol"]
noncomputable def dopWordSymbol (K : Type*) [CommSemiring K] (k : ℕ) :
    ((Fin k → ℕ) →₀ K) →ₗ[K] AddMonoidAlgebra K (Fin k →₀ ℤ) :=
  Finsupp.linearCombination K fun a =>
    AddMonoidAlgebra.single (Finsupp.equivFunOnFinite.symm fun i => -(a i : ℤ)) 1

/-- The raised family `c⁺` of a coefficient family: for a finitely supported family `c` of scalars
indexed by the words `a : Fin k → ℕ` of length `k` in the basic operators, the family supported on
the words with every index at least `1` whose value at `a + (1, …, 1)` is `c a`; equivalently, the
family sending `b` to `c (b - (1, …, 1))` when `b i ≥ 1` for every `i`, and to `0` otherwise. It
attaches to `D_{a_k+1} ⋯ D_{a_1+1}` the coefficient that `c` attaches to `D_{a_k} ⋯ D_{a_1}`.
Bundled as a linear map in `c`, the kernel of `dopWordOperator q u k` being stable under it. -/
@[hjo "def_bglx_index_raise"]
noncomputable def dopWordRaise (K : Type*) [Semiring K] (k : ℕ) :
    ((Fin k → ℕ) →₀ K) →ₗ[K] ((Fin k → ℕ) →₀ K) :=
  Finsupp.lmapDomain K K fun a => a + 1

/-- The kernel factor of the vanishing criterion: for words of length `k` in the basic operators
with parameters `q, u`, the rational function

`Ω_k = ∏_{i < j} (1 - zᵢ/z_j)(1 - qu zᵢ/z_j) / ((1 - q zᵢ/z_j)(1 - u zᵢ/z_j))`

in `k` variables, the product running over the pairs `i < j` of indices. Each factor is the
plethystic `Exp[-M v]` at `v = zᵢ/z_j`, with `M = (1 - q)(1 - u)`; the product is empty, hence
`1`, for `k ≤ 1`. The symbol of a coefficient family is multiplied by this before being
symmetrised, so `Ω_k` is the only part of the criterion that does not depend on the family.

Faithfulness to Definition "The kernel factor":
(1) No hypothesis is dead: `k` is both the number of variables and the bound of the product, `q`
and `u` each occur in a factor, and `CommRing K` with `IsDomain K` is exactly what makes the
target a field, so that the quotients exist.
(2) The scalars and the base are those of the definition: `q, u` and the coefficients lie in the
ring `K` (to be read as `ℚ(q, u)`), and `Ω_k` lies in the rational function field over that same
`K` — not over a subring, an extension, or a completion of it.
(3) The element is pinned, not characterised: its value is the displayed product on the nose, with
`zᵢ/z_j` and not `z_j/zᵢ` in each factor, and for `k ≤ 1` it is `1` by the empty product.
(4) The instantiation is not degenerate: `Ω_k ≠ 0` for every `k`, `q` and `u`, and at `k = 2` with
`q = u = 0` the value is `1 - z₀/z₁ ≠ 1`, so the product is not vacuous for `k ≥ 2`. -/
@[hjo "def_bglx_kernel_factor"]
noncomputable def dopKernelFactor {K : Type*} [CommRing K] [IsDomain K] (q u : K) (k : ℕ) :
    FractionRing (MvPolynomial (Fin k) K) :=
  let z : Fin k → FractionRing (MvPolynomial (Fin k) K) :=
    fun i => algebraMap (MvPolynomial (Fin k) K) _ (MvPolynomial.X i)
  ∏ i : Fin k, ∏ j ∈ Finset.Ioi i,
    (1 - z i / z j) * (1 - algebraMap K _ (q * u) * (z i / z j)) /
      ((1 - algebraMap K _ q * (z i / z j)) * (1 - algebraMap K _ u * (z i / z j)))

/-- Symmetrisation in `k` variables: the `K`-linear map of the rational function field
`K(z₁, …, z_k) = FractionRing (MvPolynomial (Fin k) K)` to itself sending `F` to
`(1/k!) ∑_σ F(z_{σ(1)}, …, z_{σ(k)})`, the sum over the `k!` permutations of the variables. Each
summand is the automorphism of the field extending the relabelling `z_i ↦ z_{σ(i)}` of the
polynomial ring, and `k!` is invertible since `K` has characteristic zero. -/
@[hjo "def_bglx_symmetrisation"]
noncomputable def mvRatFuncSymmetrization (K : Type*) [Field K] [CharZero K] (k : ℕ) :
    FractionRing (MvPolynomial (Fin k) K) →ₗ[K] FractionRing (MvPolynomial (Fin k) K) :=
  (Nat.factorial k : K)⁻¹ • ∑ σ : Equiv.Perm (Fin k),
    (IsFractionRing.fieldEquivOfAlgEquiv K (FractionRing (MvPolynomial (Fin k) K))
      (FractionRing (MvPolynomial (Fin k) K)) (MvPolynomial.renameEquiv K σ)).toLinearMap

end HJO.Sym
