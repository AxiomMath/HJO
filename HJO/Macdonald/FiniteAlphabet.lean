/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import HJO.Macdonald.Vocabulary
public import HJO.Evaluation.PhiPoly
public import HJO.Symmetric.AxisFree
public meta import HJO.Attr

/-! # The finite alphabet: restriction, the parameter shift, and the eigenvalue

Macdonald's polynomials are built in a finite alphabet and only then transported to the ring of
symmetric functions. This file lays the finite-alphabet ground: the graded pieces `𝒮_{n,d}` of the
symmetric polynomials, the restriction `res_n : Λ → 𝕜[x_1, …, x_n]`, the parameter shift
`T_{q,x_i}` on the rational function field, the Vandermonde products `𝒱_S`, **Macdonald's operator
`D^{(n)}_1`** with its linearity and its denominator-clearing identity, and the eigenvalue `E_n(μ)`
that pins Macdonald's polynomial.

What is **not** here, and is proved in `HJO/Macdonald/OperatorStable.lean`: `HJO.Mac.permAct_macOp`
(the operator preserves symmetry) and `HJO.Mac.exists_eq_macOp_algebraMap` (it acts on `𝒮_{n,d}`).
The first needs the permutation action of `σ` on the rational function field, built the way `qShift`
is; the second needs that plus the antisymmetry-and-divisibility argument -- `𝒱_N` divides
`𝒱_N D^{(n)}_1 f` because the latter is antisymmetric and the `x_k - x_l` are pairwise non-associate
primes -- and then a degree count. `vandermondeProd_mul_macOp` below is the identity both of them
start from.

## The eigenvalue needs generic parameters

Two lemmas here, `HJO.Sym.macdonaldEigenvalue_ne_zero` and `HJO.Sym.eq_of_macdonaldEigenvalue_eq`,
are usually stated with no hypothesis on `q` and `u`, and **both are false over a general
field**. Their usual proofs read the monomials of `E_n(μ) = ∑_{i=1}^{n} q^{μ_i}u^{n-i}` off
`ℚ[q, u]`, "which is a subring of `𝕜`" -- an appeal to `q` and `u` being indeterminates that the
statements do not record. Over a general `ℚ`-algebra:

* `E_2(∅) = u + 1`, which vanishes at `u = -1`, refuting `HJO.Sym.macdonaldEigenvalue_ne_zero`;
* `E_1((1)) = q` and `E_1((3)) = q³` agree at `q = -1` with `(1) ≠ (3)`, refuting
  `HJO.Sym.eq_of_macdonaldEigenvalue_eq`.

The two theorems
below therefore carry `AlgebraicIndependent ℤ ![q, u]`, this library's standing spelling of the
generic parameters `q, u` (`HJO.CollinearNarrowed.CollinearCommute`, `HJO/Defs.lean`),
and that hypothesis is necessary, not decorative.

## Main definitions

* `MvPolynomial.symmetricHomogeneousSubmodule`: the graded piece `𝒮_{n,d}`.
* `MvPolynomial.rescaleEquiv`, `HJO.Mac.qShift`: the parameter shift `T_{q,x_i}`.
* `Finset.vandermondeProd`: the Vandermonde product `𝒱_S`.
* `HJO.Mac.macCoeff`, `HJO.Mac.macOp`: Macdonald's operator `D^{(n)}_1`.
* `HJO.Sym.restrictAlphabet`: the restriction `res_n`.
* `HJO.Sym.macdonaldEigenvalue`: the eigenvalue `E_n(μ)`.

## Main results

* `HJO.Sym.restrictAlphabet_mem_symmetricHomogeneousSubmodule`: `res_n(Λ_d) ⊆ 𝒮_{n,d}`.
* `HJO.Mac.macOp_smul_add`: Macdonald's operator is `𝕜`-linear.
* `HJO.Mac.vandermondeProd_mul_macOp`: the operator cleared of denominators.
* `HJO.Sym.macdonaldEigenvalue_ne_zero`, `HJO.Sym.eq_of_macdonaldEigenvalue_eq`: the eigenvalue is
  nonzero and determines the partition, at generic parameters.

## Implementation notes

The definitions `MvPolynomial.symmetricHomogeneousSubmodule`, `Finset.vandermondeProd`,
`HJO.Mac.qShift`, `HJO.Sym.restrictAlphabet` and `HJO.Sym.macdonaldEigenvalue`, together with
`MvPolynomial.rescaleEquiv` (a helper of `HJO.Mac.qShift`), keep the names and namespaces under
which they are cited. The triangular-basis lemma `Module.Basis.exists_basis_of_triangular` is in
`HJO.Symmetric.TriangularBasis`.

The alphabet is an arbitrary `Fintype σ` rather than `Fin n`: nothing below uses an ordering of the
letters except the Vandermonde product and the operator built on it, which ask only for a
`LinearOrder`. A hypothesis `n ≥ 1` is never needed and is not imposed; at the empty alphabet
`D^{(n)}_1` is the zero map. The sign `(-1)^{i-1}` becomes the parity of the number of
letters below `i`, which is `i` itself at `σ = Fin n` with rows numbered from `0`.

In the operator block `DecidableEq σ` is derived from `LinearOrder σ` rather than assumed
separately. With both in scope Lean has two `DecidableEq σ` instances, `Finset.insert` and
`Finset.erase` pick up different ones in different places, and `Finset.insert_erase` then fails to
rewrite a goal it visibly matches.

Macdonald's operator takes its first parameter as a **unit** `q : Kˣ`. That is what "`q` is
invertible in `𝕜`" means for `HJO.Mac.qShift`: the shift needs `q⁻¹` for its two-sided inverse, and
at `q = 0` there is no automorphism at all. As usually written, this is said in prose inside the
definition and carried in no statement -- the same kind of omission as the genericity above.

## References

The definitions `MvPolynomial.symmetricSubalgebra`, `MvPolynomial.symmetricHomogeneousSubmodule`,
`HJO.Sym.restrictAlphabet`, `HJO.Mac.qShift`, `Finset.vandermondeProd`,
`HJO.Sym.macdonaldEigenvalue` and `HJO.Mac.macOp`, and the lemmas
`HJO.Sym.restrictAlphabet_mem_symmetricHomogeneousSubmodule`, `HJO.Sym.macdonaldEigenvalue_ne_zero`,
`HJO.Sym.eq_of_macdonaldEigenvalue_eq`, `HJO.Mac.macOp_smul_add` and
`HJO.Mac.vandermondeProd_mul_macOp`. Macdonald's operator is his `D^1_n` and
Garsia--Haiman--Tesler's `D^{(n)}_1`, with their second parameter `t` written `u`. -/

@[expose] public section

open Finset MvPolynomial

/-! ### The graded pieces of a finite alphabet, and rescaling the variables

The symmetric polynomials homogeneous of a given degree,
`MvPolynomial.symmetricHomogeneousSubmodule`, and the rescaling of the variables by a vector of
units, `MvPolynomial.rescaleEquiv`, which `HJO.Mac.qShift` uses. -/

namespace MvPolynomial

/-- The `R`-submodule of symmetric polynomials in the alphabet `σ` that are homogeneous of
degree `d`: the graded piece `𝒮_{n,d}`, at `σ = Fin n`. Membership means being invariant under
every permutation of `σ` and having every monomial of total degree `d`, the zero polynomial
included. -/
@[hjo "def_mac_symm_component"]
noncomputable def symmetricHomogeneousSubmodule (σ R : Type*) [CommSemiring R] (d : ℕ) :
    Submodule R (MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).toSubmodule ⊓ homogeneousSubmodule σ R d

variable {σ R : Type*} [CommSemiring R]

@[simp]
theorem mem_symmetricHomogeneousSubmodule {d : ℕ} {p : MvPolynomial σ R} :
    p ∈ symmetricHomogeneousSubmodule σ R d ↔ p.IsSymmetric ∧ p.IsHomogeneous d :=
  Iff.rfl

theorem symmetricHomogeneousSubmodule_le_symmetricSubalgebra (σ R : Type*) [CommSemiring R]
    (d : ℕ) :
    symmetricHomogeneousSubmodule σ R d ≤ (symmetricSubalgebra σ R).toSubmodule :=
  inf_le_left

theorem symmetricHomogeneousSubmodule_le_homogeneousSubmodule (σ R : Type*) [CommSemiring R]
    (d : ℕ) :
    symmetricHomogeneousSubmodule σ R d ≤ homogeneousSubmodule σ R d :=
  inf_le_right

/-- Rescaling the variables by a vector of units `c`: the `R`-algebra automorphism of
`MvPolynomial σ R` sending `X j` to `c j • X j`, with inverse the rescaling by `c⁻¹`. -/
noncomputable def rescaleEquiv (c : σ → Rˣ) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval fun j => (c j : R) • X j) (aeval fun j => (↑(c j)⁻¹ : R) • X j)
    (by apply algHom_ext; intro j; simp [smul_smul])
    (by apply algHom_ext; intro j; simp [smul_smul])

@[simp]
theorem rescaleEquiv_X (c : σ → Rˣ) (j : σ) : rescaleEquiv c (X j) = (c j : R) • X j := by
  simp [rescaleEquiv]

theorem rescaleEquiv_symm (c : σ → Rˣ) : (rescaleEquiv c).symm = rescaleEquiv c⁻¹ := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply algHom_ext
  intro j
  simp [rescaleEquiv]

theorem rescaleEquiv_trans (c d : σ → Rˣ) :
    (rescaleEquiv c).trans (rescaleEquiv d) = rescaleEquiv (c * d) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply algHom_ext
  intro j
  simp [smul_smul]

/-- Rescaling the variables multiplies the coefficient of each monomial by a scalar and creates no
new monomial. -/
theorem rescaleEquiv_monomial (c : σ → Rˣ) (e : σ →₀ ℕ) (a : R) :
    rescaleEquiv c (monomial e a) = monomial e (a * ∏ i ∈ e.support, (c i : R) ^ e i) := by
  classical
  have hC : ∀ b : R, rescaleEquiv c (C b) = C b := fun b => by
    rw [← MvPolynomial.algebraMap_eq]; exact (rescaleEquiv c).commutes b
  have hX : ∀ i : σ, rescaleEquiv c (X i ^ e i) = C ((c i : R) ^ e i) * X i ^ e i := fun i => by
    rw [map_pow, rescaleEquiv_X, smul_eq_C_mul, mul_pow, C_pow]
  rw [monomial_eq, Finsupp.prod, map_mul, map_prod, hC,
    Finset.prod_congr rfl fun i _ => hX i, Finset.prod_mul_distrib, ← map_prod C,
    monomial_eq, Finsupp.prod, C_mul]
  ring

/-- Rescaling the variables preserves homogeneity. -/
theorem IsHomogeneous.rescaleEquiv {c : σ → Rˣ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous d) : (MvPolynomial.rescaleEquiv c p).IsHomogeneous d := by
  classical
  rw [p.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun e he => ?_
  rw [rescaleEquiv_monomial]
  exact isHomogeneous_monomial _
    (by rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.1 he))

/-- Rescaling the variables preserves symmetry: the rescaling by a constant vector commutes with
every renaming, so a symmetric polynomial stays symmetric. -/
theorem IsSymmetric.rescaleEquiv_const {a : Rˣ} {p : MvPolynomial σ R} (hp : p.IsSymmetric) :
    (MvPolynomial.rescaleEquiv (fun _ : σ => a) p).IsSymmetric := by
  intro e
  have hcomm : (rename (σ := σ) (τ := σ) e).comp
      (MvPolynomial.rescaleEquiv (fun _ : σ => a)).toAlgHom =
      (MvPolynomial.rescaleEquiv (fun _ : σ => a)).toAlgHom.comp (rename e) := by
    apply algHom_ext
    intro j
    simp [smul_eq_C_mul]
  have h := AlgHom.congr_fun hcomm p
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom] at h
  rw [h, hp e]

end MvPolynomial

/-! ### The Vandermonde product

`Finset.vandermondeProd`, the Vandermonde product of a family over a finite index set, with its
recursion on adjoining an index. -/

namespace Finset

variable {ι R R' : Type*} [LinearOrder ι] [CommRing R] [CommRing R']

/-- The Vandermonde product of a family `v : ι → R` over a finite index set `S`:
`∏_{k < l, k, l ∈ S}(v k - v l)`, one factor for each pair of distinct indices of `S`, oriented by
the order of `ι`, the empty product being `1`. The Vandermonde product `𝒱_S ∈ 𝕂[x₁, …, x_n]` is this
at `v = MvPolynomial.X`. -/
@[hjo "def_mac_vandermonde"]
def vandermondeProd (S : Finset ι) (v : ι → R) : R :=
  ∏ k ∈ S, ∏ l ∈ S with k < l, (v k - v l)

@[simp]
theorem vandermondeProd_empty (v : ι → R) : vandermondeProd (∅ : Finset ι) v = 1 := by
  simp [vandermondeProd]

@[simp]
theorem vandermondeProd_singleton (a : ι) (v : ι → R) : vandermondeProd {a} v = 1 := by
  simp [vandermondeProd, Finset.filter_singleton]

/-- Adjoining an index `a` to `S` multiplies the Vandermonde product by exactly the factors that
mention `a`. -/
theorem vandermondeProd_insert {a : ι} {S : Finset ι} (ha : a ∉ S) (v : ι → R) :
    (insert a S).vandermondeProd v =
      (∏ l ∈ S with a < l, (v a - v l)) * (∏ k ∈ S with k < a, (v k - v a)) *
        S.vandermondeProd v := by
  have key : ∀ k ∈ S, ∏ l ∈ insert a S with k < l, (v k - v l)
      = (if k < a then v k - v a else 1) * ∏ l ∈ S with k < l, (v k - v l) := by
    intro k _
    by_cases hka : k < a
    · have ha' : a ∉ Finset.filter (k < ·) S := by simp [ha]
      simp only [Finset.filter_insert, hka, ite_true, Finset.prod_insert ha']
    · simp only [Finset.filter_insert, hka, ite_false, one_mul]
  simp only [vandermondeProd]
  rw [Finset.prod_insert ha, Finset.prod_congr rfl key, Finset.prod_mul_distrib,
    ← Finset.prod_filter, Finset.filter_insert]
  simp only [lt_irrefl, ite_false]
  ring

/-- A ring homomorphism carries the Vandermonde product of `v` to the Vandermonde product of the
image family. -/
theorem map_vandermondeProd {F : Type*} [FunLike F R R'] [RingHomClass F R R'] (f : F)
    (S : Finset ι) (v : ι → R) :
    f (S.vandermondeProd v) = S.vandermondeProd fun i => f (v i) := by
  simp [vandermondeProd, map_prod, map_sub]

end Finset

/-! ### The parameter shift of a variable

`HJO.Mac.qShift`, the `q`-shift `T_{q,x_i}` of one variable, as a `K`-algebra automorphism of the
rational function field. -/

namespace HJO.Mac

variable {σ K : Type*} [Field K] [DecidableEq σ]

/-- The q-shift `T_{q,x_i}` of the variable `x_i`: the `K`-algebra automorphism of the rational
function field `K(x_j : j ∈ σ) = FractionRing (MvPolynomial σ K)` sending `x_i` to `q x_i` and
fixing `x_j` for every `j ≠ i`. It is the extension to the fraction field of the rescaling of the
polynomial ring by the vector of units with `q` at `i` and `1` elsewhere. -/
@[hjo "def_mac_shift"]
noncomputable def qShift (q : Kˣ) (i : σ) :
    FractionRing (MvPolynomial σ K) ≃ₐ[K] FractionRing (MvPolynomial σ K) :=
  IsFractionRing.fieldEquivOfAlgEquiv K (FractionRing (MvPolynomial σ K))
    (FractionRing (MvPolynomial σ K)) (rescaleEquiv (Pi.mulSingle i q))

theorem qShift_algebraMap (q : Kˣ) (i : σ) (p : MvPolynomial σ K) :
    qShift q i (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p) =
      algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
        (rescaleEquiv (Pi.mulSingle i q) p) :=
  IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K _ _ _ p

@[simp]
theorem qShift_algebraMap_X_self (q : Kˣ) (i : σ) :
    qShift q i (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (X i)) =
      (q : K) • algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (X i) := by
  rw [qShift_algebraMap, rescaleEquiv_X, Pi.mulSingle_eq_same, smul_eq_C_mul, map_mul,
    Algebra.smul_def, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

@[simp]
theorem qShift_algebraMap_X_of_ne (q : Kˣ) {i j : σ} (h : j ≠ i) :
    qShift q i (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (X j)) =
      algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (X j) := by
  rw [qShift_algebraMap, rescaleEquiv_X, Pi.mulSingle_eq_of_ne h, Units.val_one, one_smul]

end HJO.Mac

/-! ### Macdonald's operator

`HJO.Mac.macOp` and the two structural facts about it that need no divisibility argument: linearity,
and the identity that clears its denominators against the Vandermonde product.
-/

namespace HJO.Mac

-- `DecidableEq σ` is taken from `LinearOrder σ` rather than assumed separately: with both in scope,
-- `Finset.erase` and `Finset.insert` pick up different instances in different places and the
-- Vandermonde rewrites below silently fail to match.
variable {σ K : Type*} [Field K] [LinearOrder σ] [Fintype σ]

open Finset

omit [Fintype σ] in
/-- Distinct variables have distinct values: `x_i - x_j` is a nonzero polynomial for `i ≠ j`. This
is what makes the denominators of Macdonald's operator legitimate. -/
theorem X_sub_X_ne_zero {i j : σ} (h : i ≠ j) :
    (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial σ K) ≠ 0 := by
  intro h0
  have hne : (Finsupp.single j 1 : σ →₀ ℕ) ≠ Finsupp.single i 1 := fun he => by
    have hj := congrArg (fun m : σ →₀ ℕ => m j) he
    simp [h] at hj
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) h0
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X, MvPolynomial.coeff_X] at hc
  simp [hne] at hc

/-- **The coefficients of Macdonald's operator**, Garsia--Haiman--Tesler's equation (4.9): the
coefficient the operator attaches to the letter `i`,
`A_i = ∏_{j ≠ i} (u x_i - x_j)/(x_i - x_j)`, an element of the rational function field. The
denominators are nonzero because distinct variables are distinct (`HJO.Mac.X_sub_X_ne_zero`), so
each quotient is a legitimate element of `𝕜(x_1, …, x_n)`.

The conditions `n ≥ 1` and `1 ≤ i ≤ n` are the existence of the letter `i : σ` and nothing more;
the second parameter is a bare field element, no invertibility of `u` being used to *state* the
coefficient. -/
@[hjo "def_ght3_acoef"]
noncomputable def macCoeff (u : K) (i : σ) : FractionRing (MvPolynomial σ K) :=
  ∏ j ∈ Finset.univ.erase i,
    (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
        (MvPolynomial.C u * MvPolynomial.X i - MvPolynomial.X j)) /
      (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
        (MvPolynomial.X i - MvPolynomial.X j))

/-- `A_i` at an alphabet whose other letters are the single letter `j`: the one-factor product. -/
theorem macCoeff_of_erase_eq_singleton (u : K) {i j : σ} (h : Finset.univ.erase i = {j}) :
    macCoeff u i =
      algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          (MvPolynomial.C u * MvPolynomial.X i - MvPolynomial.X j) /
        algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          (MvPolynomial.X i - MvPolynomial.X j) := by
  rw [macCoeff, h, Finset.prod_singleton]

/-- **The value check at two letters**: `A_1 = (u x_1 - x_2)/(x_1 - x_2)`, the `n = 2` case of
(4.9). This pins the orientation of both the numerator and the denominator, which a definition
denoting the wrong rational function would typecheck without. -/
theorem macCoeff_fin_two (u : K) :
    macCoeff u (0 : Fin 2) =
      algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (MvPolynomial.C u * MvPolynomial.X 0 - MvPolynomial.X 1) /
        algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (MvPolynomial.X 0 - MvPolynomial.X 1) :=
  macCoeff_of_erase_eq_singleton u (by decide)

/-- `A_i` at the one-letter alphabet is `1`: the empty product. -/
theorem macCoeff_subsingleton [Subsingleton σ] (u : K) (i : σ) : macCoeff u i = 1 := by
  rw [macCoeff, Finset.eq_empty_of_forall_notMem fun j hj =>
    (Finset.mem_erase.1 hj).1 (Subsingleton.elim j i), Finset.prod_empty]

/-- **Macdonald's operator `D^{(n)}_1`**, on the rational function field in the finite alphabet:
`D^{(n)}_1 f = ∑_i (∏_{j ≠ i} (u x_i - x_j)/(x_i - x_j)) T_{q,x_i} f`.

This is the operator Macdonald writes `D^1_n` and Garsia--Haiman--Tesler write `D^{(n)}_1`, with
their second parameter `t` written `u`. No hypothesis `n ≥ 1` is imposed: at the empty
alphabet the sum is empty and the operator is `0`.

The first parameter is a unit rather than a field element, which is what "`q` is invertible in `𝕜`"
amounts to: `HJO.Mac.qShift` needs `q⁻¹` to build the two-sided inverse of the shift, and over a
general field `q = 0` gives no automorphism at all. As usually written, this is said in prose about
`HJO.Mac.qShift` and carried in no statement. -/
@[hjo "def_mac_dop"]
noncomputable def macOp (q : Kˣ) (u : K) :
    FractionRing (MvPolynomial σ K) →ₗ[K] FractionRing (MvPolynomial σ K) where
  toFun f := ∑ i : σ, macCoeff u i * qShift q i f
  map_add' f g := by
    simp only [map_add, mul_add]
    rw [Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [RingHom.id_apply, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm]

theorem macOp_apply (q : Kˣ) (u : K) (f : FractionRing (MvPolynomial σ K)) :
    macOp q u f = ∑ i : σ, macCoeff u i * qShift q i f := rfl

/-- **Macdonald's operator is linear.** Each `T_{q,x_i}` is a `K`-algebra automorphism, hence
`K`-linear, and the coefficient attached to `i` does not depend on the argument. -/
@[hjo "lem_mac_dop_linear"]
theorem macOp_smul_add (q : Kˣ) (u : K) (c : K) (f g : FractionRing (MvPolynomial σ K)) :
    macOp q u (c • f + g) = c • macOp q u f + macOp q u g := by
  rw [map_add, map_smul]

/-! #### Clearing the denominators against the Vandermonde product -/

/-- **The Vandermonde product, split at one letter.**
`𝒱_N = (-1)^{c_i} (∏_{j ≠ i}(x_i - x_j)) 𝒱_{N∖{i}}`, with `c_i` the number of letters below `i`.

This is the computation inside the proof of `HJO.Mac.vandermondeProd_mul_macOp`: the factors of
`𝒱_N` split into those with `i` on the left, those with `i` on the right -- which contribute the
sign, being `x_k - x_i = -(x_i - x_k)` -- and those not mentioning `i` at all. The sign `(-1)^{i-1}`
is this `c_i` at `σ = Fin n`. -/
theorem vandermondeProd_univ_eq_erase (i : σ) :
    (Finset.univ : Finset σ).vandermondeProd (MvPolynomial.X : σ → MvPolynomial σ K) =
      (-1) ^ #{k ∈ (Finset.univ : Finset σ) | k < i} *
        (∏ j ∈ Finset.univ.erase i, (MvPolynomial.X i - MvPolynomial.X j)) *
        (Finset.univ.erase i).vandermondeProd (MvPolynomial.X : σ → MvPolynomial σ K) := by
  classical
  -- the filters over `univ` and over `univ.erase i` agree, `i < i` being false
  have hfilt : {k ∈ (Finset.univ : Finset σ) | k < i} = {k ∈ Finset.univ.erase i | k < i} := by
    refine Finset.ext fun k => ?_
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    exact ⟨fun h => ⟨h.ne, h⟩, fun h => h.2⟩
  -- the factors with `i` on the right carry the sign
  have hsign : ∏ k ∈ Finset.univ.erase i with k < i,
        (MvPolynomial.X k - MvPolynomial.X i : MvPolynomial σ K) =
      (-1) ^ #{k ∈ Finset.univ.erase i | k < i} *
        ∏ k ∈ Finset.univ.erase i with k < i, (MvPolynomial.X i - MvPolynomial.X k) := by
    rw [← Finset.prod_const (-1 : MvPolynomial σ K), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by ring
  -- `univ.erase i` is the disjoint union of the letters below `i` and those above it
  have hfe : {j ∈ Finset.univ.erase i | ¬ (j < i)} = {j ∈ Finset.univ.erase i | i < j} := by
    refine Finset.ext fun j => ?_
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    refine and_congr_right fun hj => ?_
    rw [not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (Ne.symm hj), fun h => h.le⟩
  have hsplit : (∏ l ∈ Finset.univ.erase i with i < l,
        (MvPolynomial.X i - MvPolynomial.X l : MvPolynomial σ K)) *
      (∏ k ∈ Finset.univ.erase i with k < i, (MvPolynomial.X i - MvPolynomial.X k)) =
      ∏ j ∈ Finset.univ.erase i, (MvPolynomial.X i - MvPolynomial.X j) := by
    rw [mul_comm, ← Finset.prod_filter_mul_prod_filter_not (Finset.univ.erase i) (· < i), hfe]
  have hexp := Finset.vandermondeProd_insert (a := i) (S := Finset.univ.erase i) (by simp)
    (MvPolynomial.X : σ → MvPolynomial σ K)
  rw [Finset.insert_erase (Finset.mem_univ i)] at hexp
  rw [hfilt, hexp, hsign, ← hsplit]
  ring

/-- **Macdonald's operator cleared of denominators.**
`𝒱_N D^{(n)}_1 f = ∑_i (-1)^{c_i} 𝒱_{N∖{i}} (∏_{j ≠ i}(u x_i - x_j)) T_{q,x_i} f`,
with `c_i` the number of letters below `i` -- the `(-1)^{i-1}` at `σ = Fin n`.

Dividing the split of `vandermondeProd_univ_eq_erase` by the denominator `∏_{j ≠ i}(x_i - x_j)` of
the `i`-th coefficient leaves exactly `(-1)^{c_i} 𝒱_{N∖{i}}`, and the division is legitimate
because distinct variables differ (`X_sub_X_ne_zero`). -/
@[hjo "lem_mac_dop_vandermonde"]
theorem vandermondeProd_mul_macOp (q : Kˣ) (u : K) (f : FractionRing (MvPolynomial σ K)) :
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
        ((Finset.univ : Finset σ).vandermondeProd MvPolynomial.X) * macOp q u f =
      ∑ i : σ, (-1) ^ #{k ∈ (Finset.univ : Finset σ) | k < i} *
        algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          ((Finset.univ.erase i).vandermondeProd MvPolynomial.X) *
        algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          (∏ j ∈ Finset.univ.erase i, (MvPolynomial.C u * MvPolynomial.X i - MvPolynomial.X j)) *
        qShift q i f := by
  classical
  rw [macOp_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- the denominator of the `i`-th coefficient is nonzero
  have hden : algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
      (∏ j ∈ Finset.univ.erase i, (MvPolynomial.X i - MvPolynomial.X j)) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact Finset.prod_ne_zero_iff.2 fun j hj =>
      X_sub_X_ne_zero (Finset.ne_of_mem_erase hj).symm
  -- the coefficient is a single quotient
  have hcoeff : macCoeff u i =
      algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          (∏ j ∈ Finset.univ.erase i, (MvPolynomial.C u * MvPolynomial.X i - MvPolynomial.X j)) /
        algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          (∏ j ∈ Finset.univ.erase i, (MvPolynomial.X i - MvPolynomial.X j)) := by
    rw [macCoeff, Finset.prod_div_distrib, map_prod, map_prod]
  -- the split of the Vandermonde product, read in the fraction field
  have hV : algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
      ((Finset.univ : Finset σ).vandermondeProd MvPolynomial.X) =
      (-1) ^ #{k ∈ (Finset.univ : Finset σ) | k < i} *
        algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          (∏ j ∈ Finset.univ.erase i, (MvPolynomial.X i - MvPolynomial.X j)) *
        algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          ((Finset.univ.erase i).vandermondeProd MvPolynomial.X) := by
    rw [vandermondeProd_univ_eq_erase (K := K) i, map_mul, map_mul, map_pow, map_neg, map_one]
  rw [hcoeff, hV]
  field_simp

end HJO.Mac

/-! ### Restriction to a finite alphabet

`HJO.Sym.restrictAlphabet`, the restriction of symmetric functions to a finite alphabet. The
gradedness lemma below is `HJO.Sym.restrictAlphabet_mem_symmetricHomogeneousSubmodule`. -/

namespace HJO.Sym

/-- Restriction to a finite alphabet: the unique `K`-algebra homomorphism from the ring of
symmetric functions `Lambda K` to the polynomials in the finite alphabet `σ` sending the power-sum
symbol `p_k` to the actual power sum `∑ᵢ xᵢ ^ k`. It is the substitution the sources write as
passing from the alphabet `X` to the alphabet `X_n = x₁ + ⋯ + x_n`, and is the restriction `res_n`
at `σ = Fin n`. -/
@[hjo "def_mac_res"]
noncomputable def restrictAlphabet (σ : Type*) [Fintype σ] (K : Type*) [CommRing K] :
    Lambda K →ₐ[K] MvPolynomial σ K :=
  aeval fun i => psum σ K (i + 1)

variable {σ : Type*} [Fintype σ] {K : Type*} [CommRing K]

/-- The defining values of the restriction: the power-sum symbol `p_{k+1}` goes to the power sum
`∑ᵢ xᵢ ^ (k + 1)` of the finite alphabet. -/
@[simp]
theorem restrictAlphabet_powerSum (k : ℕ) :
    restrictAlphabet σ K (powerSum K (k + 1)) = psum σ K (k + 1) := by
  rw [powerSum, Nat.add_sub_cancel, restrictAlphabet, aeval_X]

/-- The restriction at a bare generator `X i` of `Lambda K = MvPolynomial ℕ K`, which is the
power-sum symbol `p_{i+1}`. -/
@[simp]
theorem restrictAlphabet_powerSum' (i : ℕ) :
    restrictAlphabet σ K (X i) = psum σ K (i + 1) := by
  rw [restrictAlphabet, aeval_X]

/-- Those values pin the map: there is exactly one `K`-algebra homomorphism
`Lambda K → MvPolynomial σ K` sending each `p_k` to the `k`-th power sum of the finite alphabet. -/
theorem eq_restrictAlphabet (φ : Lambda K →ₐ[K] MvPolynomial σ K)
    (h : ∀ k : ℕ, φ (powerSum K (k + 1)) = psum σ K (k + 1)) :
    φ = restrictAlphabet σ K := by
  refine MvPolynomial.algHom_ext fun i => ?_
  have hi := h i
  rw [powerSum, Nat.add_sub_cancel] at hi
  rw [hi, restrictAlphabet, aeval_X]

/-- A power sum of a finite alphabet is homogeneous of its own degree. -/
theorem psum_isHomogeneous (σ : Type*) [Fintype σ] (K : Type*) [CommRing K] (k : ℕ) :
    (psum σ K k).IsHomogeneous k := by
  rw [psum]
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i k

/-- Every restriction is symmetric: the generators `p_k` go to power sums, which are symmetric, and
symmetry is preserved by the ring operations. -/
theorem restrictAlphabet_isSymmetric (f : Lambda K) :
    (restrictAlphabet σ K f).IsSymmetric := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [algHom_C]; exact IsSymmetric.C a
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp =>
      rw [map_mul, restrictAlphabet_powerSum']
      exact hp.mul (psum_isSymmetric σ K (i + 1))

/-- **Restriction is graded.** That is, `res_n(Λ_d) ⊆ 𝒮_{n,d}`: a product of power sums of
total degree `d` restricts to a product of power sums of the finite alphabet, whose monomials all
have total degree `d`, and both sides are spans. -/
@[hjo "lem_mac_res_component"]
theorem restrictAlphabet_mem_symmetricHomogeneousSubmodule {d : ℕ} {f : Lambda K}
    (hf : f ∈ LambdaComp K d) :
    restrictAlphabet σ K f ∈ symmetricHomogeneousSubmodule σ K d := by
  classical
  refine ⟨restrictAlphabet_isSymmetric f, (mem_homogeneousSubmodule d _).1 ?_⟩
  -- the graded piece is contained in the preimage of the homogeneous submodule, a submodule, so
  -- it suffices to check the products of power sums that span it
  have hle : LambdaComp K d ≤
      Submodule.comap (restrictAlphabet σ K).toLinearMap (homogeneousSubmodule σ K d) := by
    rw [lambdaComp_eq_span, Submodule.span_le]
    rintro g ⟨e, hwt, rfl⟩
    have hdeg : ∑ i ∈ e.support, (i + 1) * e i = d := by
      rw [← hwt, Finsupp.weight_apply, Finsupp.sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
    refine (mem_homogeneousSubmodule d _).2 ?_
    change (restrictAlphabet σ K (∏ i ∈ e.support, powerSum K (i + 1) ^ e i)).IsHomogeneous d
    rw [map_prod, ← hdeg]
    refine IsHomogeneous.prod _ _ _ fun i _ => ?_
    rw [map_pow, restrictAlphabet_powerSum]
    exact (psum_isHomogeneous σ K (i + 1)).pow (e i)
  exact hle hf

end HJO.Sym

/-! ### The eigenvalue of a partition in a finite alphabet

`HJO.Sym.macdonaldEigenvalue`, the eigenvalue `E_n(μ)` of a partition in a finite alphabet. The two
lemmas below both carry a genericity hypothesis that cannot be dropped -- see the module
docstring. -/

namespace HJO.Sym

/-- The eigenvalue Macdonald's operator `D^{(n)}_1` attaches to the partition `μ` in an alphabet of
`n` letters: `macdonaldEigenvalue q u n μ = ∑ i ∈ Finset.range n, q ^ μ.rowLen i * u ^ (n - 1 - i)`,
the usual `E_n(μ) = ∑_{i=1}^{n} q^{μ_i} u^{n-i}` read on the `0`-indexed rows of `μ`. Parts
beyond the last row of `μ` are `0`, so no truncation hypothesis is needed, and `E_0(μ) = 0`. -/
@[hjo "def_mac_eigenvalue"]
def macdonaldEigenvalue {K : Type*} [Semiring K] (q u : K) (n : ℕ) (μ : YoungDiagram) : K :=
  ∑ i ∈ Finset.range n, q ^ μ.rowLen i * u ^ (n - 1 - i)

section Semiring

variable {K : Type*} [Semiring K] (q u : K) (μ : YoungDiagram)

/-- The eigenvalue in the empty alphabet is `0`, the sum over no indices. -/
@[simp]
theorem macdonaldEigenvalue_zero : macdonaldEigenvalue q u 0 μ = 0 := by
  simp [macdonaldEigenvalue]

/-- Horner's rule in the size of the alphabet: `E_{n+1}(μ) = E_n(μ) u + q^{μ_{n+1}}`, the last
index `n + 1` of the longer alphabet contributing the part `μ.rowLen n` with no factor of `u`. -/
theorem macdonaldEigenvalue_succ (n : ℕ) :
    macdonaldEigenvalue q u (n + 1) μ = macdonaldEigenvalue q u n μ * u + q ^ μ.rowLen n := by
  rw [macdonaldEigenvalue, macdonaldEigenvalue, Finset.sum_range_succ, Finset.sum_mul]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i < n := Finset.mem_range.mp hi
  rw [mul_assoc, ← pow_succ]
  congr 2
  omega

/-- The eigenvalue in a one-letter alphabet is the first part of `μ` in the exponent of `q`. -/
@[simp]
theorem macdonaldEigenvalue_one : macdonaldEigenvalue q u 1 μ = q ^ μ.rowLen 0 := by
  simp [macdonaldEigenvalue_succ]

end Semiring

/-! #### The eigenvalue at generic parameters -/

section Generic

variable {L : Type*} [CommRing L] {q u : L}

/-- The eigenvalue as a two-variable integer polynomial: `∑_{i<n} Q^{μ_i} U^{n-1-i}`, a sum of `n`
pairwise distinct monomials each with coefficient `1`, the exponents of `U` being the distinct
integers `n-1, …, 0`. Evaluating at `(q, u)` returns `E_n(μ)`. -/
noncomputable def eigenvaluePoly (n : ℕ) (μ : YoungDiagram) : MvPolynomial (Fin 2) ℤ :=
  ∑ i ∈ Finset.range n, X 0 ^ μ.rowLen i * X 1 ^ (n - 1 - i)

theorem aeval_eigenvaluePoly (q u : L) (n : ℕ) (μ : YoungDiagram) :
    MvPolynomial.aeval ![q, u] (eigenvaluePoly n μ) = macdonaldEigenvalue q u n μ := by
  rw [eigenvaluePoly, macdonaldEigenvalue, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- The exponent vector of the `i`-th monomial of `eigenvaluePoly n μ`. -/
private noncomputable def eigenExp (n : ℕ) (μ : YoungDiagram) (i : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (μ.rowLen i) + Finsupp.single 1 (n - 1 - i)

private theorem eigenExp_apply_zero (n : ℕ) (μ : YoungDiagram) (i : ℕ) :
    eigenExp n μ i 0 = μ.rowLen i := by simp [eigenExp]

private theorem eigenExp_apply_one (n : ℕ) (μ : YoungDiagram) (i : ℕ) :
    eigenExp n μ i 1 = n - 1 - i := by simp [eigenExp]

/-- Each summand of `eigenvaluePoly` is a monomial with coefficient `1`. -/
private theorem eigenvaluePoly_summand (n : ℕ) (μ : YoungDiagram) (j : ℕ) :
    (X 0 ^ μ.rowLen j * X 1 ^ (n - 1 - j) : MvPolynomial (Fin 2) ℤ) =
      monomial (eigenExp n μ j) 1 := by
  rw [eigenExp, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, mul_one]

/-- Two summands of `eigenvaluePoly n μ` with distinct indices below `n` are distinct monomials:
their exponents of the second variable, the integers `n - 1 - j`, differ. -/
private theorem eigenExp_injOn {n : ℕ} {μ ν : YoungDiagram} {i j : ℕ} (hi : i < n) (hj : j < n)
    (h : eigenExp n ν j = eigenExp n μ i) : j = i := by
  have h1 : eigenExp n ν j 1 = eigenExp n μ i 1 := by rw [h]
  rw [eigenExp_apply_one, eigenExp_apply_one] at h1
  omega

private theorem coeff_eigenvaluePoly (n : ℕ) (μ : YoungDiagram) {i : ℕ} (hi : i < n) :
    coeff (eigenExp n μ i) (eigenvaluePoly n μ) = 1 := by
  classical
  rw [eigenvaluePoly, Finset.sum_congr rfl fun j _ => eigenvaluePoly_summand n μ j, coeff_sum,
    Finset.sum_eq_single i]
  · simp
  · intro j hj hne
    have hEx : eigenExp n μ j ≠ eigenExp n μ i := fun hEq =>
      hne (eigenExp_injOn hi (Finset.mem_range.mp hj) hEq)
    simp [coeff_monomial, hEx]
  · intro h; exact absurd (Finset.mem_range.mpr hi) h

/-- **The eigenvalue is nonzero, at generic parameters.**

Stated with no hypothesis on `q` and `u`, this is false: `E_2(∅) = u + 1` vanishes at `u = -1`. The
usual proof reads the monomials of `E_n(μ)` off `ℚ[q, u]`, which presumes `q` and `u`
algebraically independent; that is the hypothesis carried here, and the counterexample shows it
cannot be dropped. -/
@[hjo "lem_mac_eigenvalue_ne_zero"]
theorem macdonaldEigenvalue_ne_zero (hqu : AlgebraicIndependent ℤ ![q, u]) {n : ℕ} (hn : 0 < n)
    (μ : YoungDiagram) : macdonaldEigenvalue q u n μ ≠ 0 := by
  intro h
  have hpoly : eigenvaluePoly n μ = 0 := by
    refine HJO.PhiPoly.eq_of_aeval_eq hqu ?_
    rw [aeval_eigenvaluePoly, h, map_zero]
  have hc := coeff_eigenvaluePoly n μ hn
  rw [hpoly, coeff_zero] at hc
  exact zero_ne_one hc

/-- **The eigenvalue determines the partition, at generic parameters.**

Stated with no hypothesis on `q` and `u`, this is false: `E_1((1)) = q` and `E_1((3)) = q³` agree at
`q = -1`. As with `macdonaldEigenvalue_ne_zero`, the usual proof presumes `q` and `u`
algebraically independent, which is the hypothesis carried here. -/
@[hjo "lem_mac_eigenvalue_injective"]
theorem eq_of_macdonaldEigenvalue_eq (hqu : AlgebraicIndependent ℤ ![q, u]) {n : ℕ}
    {μ ν : YoungDiagram} (hμ : μ.rowLen n = 0) (hν : ν.rowLen n = 0)
    (h : macdonaldEigenvalue q u n μ = macdonaldEigenvalue q u n ν) : μ = ν := by
  classical
  have hpoly : eigenvaluePoly n μ = eigenvaluePoly n ν := by
    refine HJO.PhiPoly.eq_of_aeval_eq hqu ?_
    rw [aeval_eigenvaluePoly, aeval_eigenvaluePoly, h]
  -- the coefficient at `eigenExp n μ i` is `1` on the left, so it is `1` on the right, which for
  -- a sum of distinct monomials forces `μ.rowLen i = ν.rowLen i`
  have hrow : ∀ i < n, μ.rowLen i = ν.rowLen i := by
    intro i hi
    by_contra hne
    have h1 : coeff (eigenExp n μ i) (eigenvaluePoly n ν) = 1 := by
      rw [← hpoly]; exact coeff_eigenvaluePoly n μ hi
    rw [eigenvaluePoly, Finset.sum_congr rfl fun j _ => eigenvaluePoly_summand n ν j,
      coeff_sum] at h1
    rw [Finset.sum_eq_zero fun j hj => ?_] at h1
    · exact one_ne_zero h1.symm
    · have hEx : eigenExp n ν j ≠ eigenExp n μ i := fun hEq => hne (by
        obtain rfl := eigenExp_injOn hi (Finset.mem_range.mp hj) hEq
        have h0' : eigenExp n ν j 0 = eigenExp n μ j 0 := by rw [hEq]
        rw [eigenExp_apply_zero, eigenExp_apply_zero] at h0'
        exact h0'.symm)
      simp [coeff_monomial, hEx]
  -- rows at and beyond `n` vanish on both sides, so all rows agree
  have hall : ∀ i, μ.rowLen i = ν.rowLen i := by
    intro i
    rcases lt_or_ge i n with hi | hi
    · exact hrow i hi
    · have h1 := μ.rowLen_anti n i hi
      have h2 := ν.rowLen_anti n i hi
      omega
  refine YoungDiagram.ext (Finset.ext fun c => ?_)
  obtain ⟨i, j⟩ := c
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen, hall i]

end Generic

end HJO.Sym
