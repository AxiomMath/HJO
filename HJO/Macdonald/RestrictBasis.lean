/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import HJO.Collinear.GradedBasis
public import HJO.Macdonald.MonomialBasis
public meta import HJO.Attr

/-! # Restriction to a finite alphabet is bijective on a graded piece

Fix a finite alphabet `σ` and a degree `d ≤ #σ`. The restriction `res_n : Λ → 𝕜[x_1, …, x_n]` of
`HJO.Sym.restrictAlphabet` carries the graded piece `Λ_d` **bijectively** onto the symmetric
polynomials `𝒮_{n,d}` in the finite alphabet that are homogeneous of degree `d`. That bijection is
what makes Macdonald's symmetric function `P_μ ∈ Λ_{|μ|}` well defined: its finite-alphabet avatar
`P_μ[X_n]` lies in `𝒮_{n,d}`, and the bijection supplies both a preimage and its uniqueness.

Three things are proved, in this order.

*The values of the restriction on the elementary symmetric functions.* `res_n(e_r)` is the
elementary symmetric *polynomial* `MvPolynomial.esymm σ 𝕜 r`, whose definition is exactly the
sum `∑_T ∏_{i ∈ T} x_i` over the `r`-element subsets `T` of the alphabet. Both sides
satisfy Newton's identity with the same value `1` at `r = 0`, and the identity determines its
solution because the positive integers are invertible; no generating function is needed. The
usual `E(z) = ∏_i(1 - x_iz)` argument is a second proof of the same recursion.

*Surjectivity.* Mathlib's fundamental theorem of symmetric polynomials
(`MvPolynomial.esymmAlgHom_surjective`) writes a symmetric polynomial as a polynomial in the
`esymm σ 𝕜 r`, and the previous paragraph realises each of those as a value of `res_n`; since
`res_n` is an algebra homomorphism, every symmetric polynomial is a value of it. To place the
preimage in `Λ_d` rather than in `Λ`, take its weighted homogeneous component of degree `d`:
`res_n` is graded (`HJO.Sym.restrictAlphabet_mem_symmetricHomogeneousSubmodule`), so it commutes
with taking components (`HJO.Sym.restrictAlphabet_homogeneousComponent`), and the component of a
polynomial already homogeneous of degree `d` is the polynomial itself.

*Bijectivity.* `Λ_d` and `𝒮_{n,d}` are free modules on the partitions of `d` --- the first by
`HJO.Sym.exists_basis_lambdaComp_elemSymmMonomial`, the second by
`MvPolynomial.exists_basis_symmetricHomogeneousSubmodule_msymm`, whose index set
`{μ // μ.parts.card ≤ #σ}` is all of `Nat.Partition d` once `d ≤ #σ`, a partition of `d` having at
most `d` parts. Transporting one basis to the other gives an isomorphism `𝒮_{n,d} ≃ₗ Λ_d`, and
composing it with the restriction turns the surjection into a surjective endomorphism of a finitely
generated module over a commutative ring, which is bijective by the Orzech property.

## Main results

* `HJO.Sym.restrictAlphabet_elemSymm`.
* `HJO.Sym.restrictAlphabetComp_bijective`.
* `HJO.Sym.exists_basis_symmetricHomogeneousSubmodule_restrictAlphabet`: the restricted elementary
  monomials are a basis of `𝒮_{n,d}`.
* `HJO.Sym.restrictAlphabetEquiv`: the bijection bundled as a `LinearEquiv`, which is the form
  `HJO.Sym.macPfun` needs in order to name the preimage of `P_μ[X_n]`.

## Implementation notes

**The route is not the textbook one, and it is shorter.** The usual proof shows the restricted
elementary monomials to be a basis of `𝒮_{n,d}` by a triangularity argument against the monomial
symmetric polynomials --- `res_n(e_λ)` has leading exponent the conjugate of `λ` and leading
coefficient `1` --- and deduces bijectivity from that. Here bijectivity is proved first, from
Mathlib's fundamental theorem, and the basis statement is then the image of the basis `e_λ` of `Λ_d`
under an isomorphism, which is two lines. Nothing is lost: the two routes prove the same two facts.

**No genericity, and no field.** Everything here holds over a commutative ring `K` that is a
`ℚ`-algebra. The `ℚ`-algebra hypothesis is what makes `e_n` exist at all in the power-sum
presentation (`HJO.Sym.elemSymm` divides by `n`) and is the only hypothesis Newton's identity needs;
the Orzech property replaces the dimension count a field would give. In particular no fact from
`HJO/Macdonald/StandingFacts.lean` is used: the parameters `q` and `u` do not occur.

**The hypothesis is `d ≤ #σ`, and no hypothesis `n ≥ 1` is imposed.** It is not needed: at
`d = 0` and an empty alphabet both sides are the constants and the restriction is the identity on
them, so the statement holds there too, and carrying `n ≥ 1` would decorate it with an unused side
condition. The index condition `μ_{n+1} = 0` on the monomial symmetric basis is where
`d ≤ #σ` is used a second time, to identify that index set with `Nat.Partition d`.

`Nat.Partition d` is the index type of the elementary-monomial basis of `Λ_d` and hence of the
family in `HJO.Sym.exists_basis_symmetricHomogeneousSubmodule_restrictAlphabet`; the reindexing of
the monomial symmetric basis by the conjugate involution `μ ↦ μ'` is not needed, the two index types
being identified by `Equiv.subtypeUnivEquiv` instead. Mathlib has no conjugate of a `Nat.Partition`
at this revision.

## References

This file formalises the restriction `HJO.Sym.restrictAlphabet` to finitely many variables and
the submodule `MvPolynomial.symmetricHomogeneousSubmodule`, with the lemmas
`HJO.Sym.restrictAlphabet_elemSymm`, `HJO.Sym.restrictAlphabet_mem_symmetricHomogeneousSubmodule`,
`HJO.Sym.exists_basis_symmetricHomogeneousSubmodule_restrictAlphabet`,
`HJO.Sym.restrictAlphabetComp_bijective` and `HJO.Sym.exists_basis_lambdaComp_elemSymmMonomial`.
Macdonald's `P_μ` of `HJO.Sym.macPfun` is the first consumer.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Sym

/-! ### The restriction of an elementary symmetric function -/

/-- **Newton's identity for the elementary symmetric polynomials**, in the shape
`HJO.Sym.elemSymm` is defined by: `n e_n = ∑_{k < n} (-1)^k π_{k+1} e_{n-1-k}`, with `π_k` the
`k`-th power sum of the alphabet. This is Mathlib's `MvPolynomial.mul_esymm_eq_sum` with its
filtered antidiagonal reindexed as a reflected range. -/
private theorem natCast_mul_esymm {σ : Type*} [Fintype σ] {R : Type*} [CommRing R] {n : ℕ}
    (hn : 1 ≤ n) :
    (n : MvPolynomial σ R) * esymm σ R n
      = ∑ k ∈ Finset.range n, (-1) ^ k * psum σ R (k + 1) * esymm σ R (n - 1 - k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [mul_esymm_eq_sum, Finset.sum_filter,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
  simp only [lt_self_iff_false, ite_false, add_zero]
  rw [Finset.mul_sum, ← Finset.sum_range_reflect
    (fun k => (-1 : MvPolynomial σ R) ^ k * psum σ R (k + 1) * esymm σ R (m - k)) (m + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [ite_eq_left (Nat.lt_succ_of_le hj')]
  obtain ⟨i, rfl⟩ : ∃ i, m = j + i := ⟨m - j, by omega⟩
  have hsign : (-1 : MvPolynomial σ R) ^ (j + i + 1 + 1) * (-1) ^ j = (-1) ^ i := by
    rw [← pow_add, show j + i + 1 + 1 + j = i + 2 * (j + 1) from by omega, pow_add, pow_mul]
    simp
  rw [show j + i + 1 - 1 - j = i from by omega, show j + i - i = j from by omega,
    show j + i + 1 - j = i + 1 from by omega,
    show (-1 : MvPolynomial σ R) ^ (j + i + 1 + 1) * ((-1) ^ j * esymm σ R j * psum σ R (i + 1))
      = ((-1) ^ (j + i + 1 + 1) * (-1) ^ j) * (esymm σ R j * psum σ R (i + 1)) from by ring,
    hsign]
  ring

/-- **Restriction sends the elementary symmetric functions to the elementary symmetric
polynomials.** For every `r`, `res_n(e_r) = ∑_T ∏_{i ∈ T} x_i`, the sum over the `r`-element subsets
`T` of the alphabet, which is `MvPolynomial.esymm σ K r`. Both sides are `1` at `r = 0` and satisfy
Newton's identity, whose solution is determined because the positive integers are invertible in a
`ℚ`-algebra. -/
@[hjo "lem_mac_res_esymm"]
theorem restrictAlphabet_elemSymm (σ : Type*) [Fintype σ] (K : Type*) [CommRing K] [Algebra ℚ K]
    (r : ℕ) : restrictAlphabet σ K (elemSymm K r) = esymm σ K r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => rw [Bglx.elemSymm_zero_eq_one, map_one, esymm_zero]
    | n + 1 =>
      refine Bglx.cancel_natCast (K := K) (n := n + 1) (by omega) ?_
      rw [Bglx.natCast_mul_map_elemSymm (restrictAlphabet σ K) (by omega),
        natCast_mul_esymm (σ := σ) (R := K) (n := n + 1) (by omega)]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [restrictAlphabet_powerSum, ih (n + 1 - 1 - k) (by omega)]

/-- The restriction read as a sum over subsets: `res_n(e_r)` is the sum, over the `r`-element
subsets `T` of the alphabet, of the products `∏_{i ∈ T} x_i`. This is
`HJO.Sym.restrictAlphabet_elemSymm` with `MvPolynomial.esymm` unfolded to its definition. -/
theorem restrictAlphabet_elemSymm_eq_sum_powersetCard (σ : Type*) [Fintype σ] (K : Type*)
    [CommRing K] [Algebra ℚ K] (r : ℕ) :
    restrictAlphabet σ K (elemSymm K r)
      = ∑ T ∈ Finset.powersetCard r (Finset.univ : Finset σ), ∏ i ∈ T, X i :=
  restrictAlphabet_elemSymm σ K r

/-! ### Restriction is surjective onto a graded piece -/

/-- **Restriction commutes with taking a graded component.** A symmetric function is the sum of its
weighted homogeneous components, and the restriction of the component of degree `N` is homogeneous
of degree `N` by `HJO.Sym.restrictAlphabet_mem_symmetricHomogeneousSubmodule`, so only the summand
`N = d` survives the projection to degree `d`. -/
theorem restrictAlphabet_homogeneousComponent (σ : Type*) [Fintype σ] {K : Type*} [CommRing K]
    (d : ℕ) (f : Lambda K) :
    homogeneousComponent d (restrictAlphabet σ K f)
      = restrictAlphabet σ K (weightedHomogeneousComponent (fun i => i + 1) d f) := by
  have hmem : ∀ N : ℕ, restrictAlphabet σ K (weightedHomogeneousComponent (fun i => i + 1) N f)
      ∈ homogeneousSubmodule σ K N := fun N =>
    (mem_homogeneousSubmodule N _).2
      (mem_symmetricHomogeneousSubmodule.1 (restrictAlphabet_mem_symmetricHomogeneousSubmodule
        (weightedHomogeneousComponent_mem _ f N))).2
  conv_lhs => rw [← sum_weightedHomogeneousComponent_range f]
  rw [map_sum, map_sum]
  simp only [homogeneousComponent_of_mem (hmem _)]
  by_cases hd : d ∈ Finset.range (weightedTotalDegree (fun i => i + 1) f + 1)
  · rw [Finset.sum_eq_single_of_mem d hd fun N _ hN => ite_eq_right (Ne.symm hN),
      ite_eq_left rfl]
  · rw [Finset.mem_range, Nat.lt_succ_iff, Nat.not_le] at hd
    rw [weightedHomogeneousComponent_eq_zero _ f hd, map_zero, Finset.sum_eq_zero]
    intro N hN
    rw [Finset.mem_range, Nat.lt_succ_iff] at hN
    exact ite_eq_right (by omega)

/-- **Every symmetric polynomial is a restriction.** By the fundamental theorem of symmetric
polynomials a symmetric polynomial is a polynomial in the `esymm σ K (i + 1)`, and each of those is
`res_n(e_{i+1})` by `HJO.Sym.restrictAlphabet_elemSymm`; substituting `e_{i+1}` for the variables
produces a preimage, `res_n` being an algebra homomorphism. -/
theorem exists_restrictAlphabet_eq (σ : Type*) [Fintype σ] (K : Type*) [CommRing K] [Algebra ℚ K]
    {g : MvPolynomial σ K} (hg : g.IsSymmetric) : ∃ f, restrictAlphabet σ K f = g := by
  obtain ⟨p, hp⟩ := esymmAlgHom_surjective (σ := σ) K (n := Fintype.card σ) le_rfl ⟨g, hg⟩
  have h : (aeval fun i : Fin (Fintype.card σ) => esymm σ K ((i : ℕ) + 1)) p = g := by
    rw [← esymmAlgHom_apply, hp]
  refine ⟨aeval (fun i : Fin (Fintype.card σ) => elemSymm K ((i : ℕ) + 1)) p, ?_⟩
  rw [← h, ← AlgHom.comp_apply, comp_aeval]
  simp only [restrictAlphabet_elemSymm]

/-- **Restriction is surjective onto a graded piece**: a symmetric polynomial homogeneous of degree
`d` is the restriction of an element of `Λ_d`. Take any preimage and keep its weighted homogeneous
component of degree `d`. -/
theorem exists_mem_lambdaComp_restrictAlphabet_eq (σ : Type*) [Fintype σ] (K : Type*) [CommRing K]
    [Algebra ℚ K] {d : ℕ} {g : MvPolynomial σ K}
    (hg : g ∈ symmetricHomogeneousSubmodule σ K d) :
    ∃ f ∈ LambdaComp K d, restrictAlphabet σ K f = g := by
  obtain ⟨hsym, hhom⟩ := mem_symmetricHomogeneousSubmodule.1 hg
  obtain ⟨f, hf⟩ := exists_restrictAlphabet_eq σ K hsym
  refine ⟨weightedHomogeneousComponent (fun i => i + 1) d f,
    weightedHomogeneousComponent_mem _ f d, ?_⟩
  rw [← restrictAlphabet_homogeneousComponent, hf, homogeneousComponent_eq_self hhom]

/-! ### Restriction is bijective on a graded piece -/

/-- The restriction of `res_n` to the graded piece `Λ_d`, a `K`-linear map into `𝒮_{n,d}`. The
target is the graded piece `𝒮_{n,d}` and the containment is
`HJO.Sym.restrictAlphabet_mem_symmetricHomogeneousSubmodule`. -/
noncomputable def restrictAlphabetComp (σ : Type*) [Fintype σ] (K : Type*) [CommRing K] (d : ℕ) :
    LambdaComp K d →ₗ[K] symmetricHomogeneousSubmodule σ K d :=
  (restrictAlphabet σ K).toLinearMap.restrict
    fun _ hf => restrictAlphabet_mem_symmetricHomogeneousSubmodule hf

@[simp]
theorem coe_restrictAlphabetComp {σ : Type*} [Fintype σ] {K : Type*} [CommRing K] {d : ℕ}
    (f : LambdaComp K d) :
    (restrictAlphabetComp σ K d f : MvPolynomial σ K) = restrictAlphabet σ K (f : Lambda K) := rfl

theorem restrictAlphabetComp_surjective (σ : Type*) [Fintype σ] (K : Type*) [CommRing K]
    [Algebra ℚ K] (d : ℕ) : Function.Surjective (restrictAlphabetComp σ K d) := by
  rintro ⟨g, hg⟩
  obtain ⟨f, hf, hfg⟩ := exists_mem_lambdaComp_restrictAlphabet_eq σ K hg
  exact ⟨⟨f, hf⟩, Subtype.ext hfg⟩

/-- A partition of `d` has at most `d` parts, its parts being positive and summing to `d`. This is
the identification of the partitions `μ` of `d` with `μ_{n+1} = 0` with the partitions
of `d` outright, once `d ≤ n`. -/
private theorem parts_card_le (d : ℕ) (μ : Nat.Partition d) : μ.parts.card ≤ d := by
  have h := Multiset.card_nsmul_le_sum (s := μ.parts) (a := 1) fun x hx => μ.parts_pos hx
  rwa [μ.parts_sum, smul_eq_mul, mul_one] at h

/-- **Restriction is bijective on a graded piece.** For `d ≤ #σ` the restriction `res_n` carries
`Λ_d` bijectively onto the symmetric polynomials in the finite alphabet `σ` that are homogeneous of
degree `d`. It is surjective by the fundamental theorem of symmetric polynomials, and both sides are
free modules on the partitions of `d`, so transporting a basis makes it a surjective endomorphism of
a finitely generated module over a commutative ring, hence bijective. -/
@[hjo "lem_mac_res_bijective"]
theorem restrictAlphabetComp_bijective (σ : Type*) [Fintype σ] (K : Type*) [CommRing K]
    [Algebra ℚ K] {d : ℕ} (hd : d ≤ Fintype.card σ) :
    Function.Bijective (restrictAlphabetComp σ K d) := by
  classical
  obtain ⟨B₁, -⟩ := exists_basis_lambdaComp_elemSymmMonomial K d
  obtain ⟨B₂, -⟩ := exists_basis_symmetricHomogeneousSubmodule_msymm σ K d
  have e : symmetricHomogeneousSubmodule σ K d ≃ₗ[K] LambdaComp K d :=
    B₂.equiv B₁ (Equiv.subtypeUnivEquiv fun μ => (parts_card_le d μ).trans hd)
  have _ : Module.Finite K (symmetricHomogeneousSubmodule σ K d) := Module.Finite.of_basis B₂
  have hbij := OrzechProperty.bijective_of_surjective_endomorphism
    ((restrictAlphabetComp σ K d).comp (e : _ →ₗ[K] _))
    ((restrictAlphabetComp_surjective σ K d).comp e.surjective)
  refine ⟨fun x y hxy => ?_, restrictAlphabetComp_surjective σ K d⟩
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  exact congrArg e (hbij.1 (by simpa using hxy))

/-- The bijection of `HJO.Sym.restrictAlphabetComp_bijective`, bundled as a `K`-linear equivalence
`Λ_d ≃ₗ 𝒮_{n,d}`. This is the form Macdonald's symmetric function needs: `P_μ` is the preimage of
`P_μ[X_n]` under it. -/
noncomputable def restrictAlphabetEquiv (σ : Type*) [Fintype σ] (K : Type*) [CommRing K]
    [Algebra ℚ K] {d : ℕ} (hd : d ≤ Fintype.card σ) :
    LambdaComp K d ≃ₗ[K] symmetricHomogeneousSubmodule σ K d :=
  LinearEquiv.ofBijective _ (restrictAlphabetComp_bijective σ K hd)

@[simp]
theorem coe_restrictAlphabetEquiv {σ : Type*} [Fintype σ] {K : Type*} [CommRing K] [Algebra ℚ K]
    {d : ℕ} (hd : d ≤ Fintype.card σ) (f : LambdaComp K d) :
    (restrictAlphabetEquiv σ K hd f : MvPolynomial σ K) = restrictAlphabet σ K (f : Lambda K) :=
  rfl

/-- **The restricted elementary monomials are a basis.** For `d ≤ #σ` the family
`res_n(e_λ) = res_n(e_{λ₁}) ⋯ res_n(e_{λ_m})`, indexed by the partitions `λ` of `d`, is a `K`-basis
of `𝒮_{n,d}`: the elementary monomials are a basis of `Λ_d` by
`HJO.Sym.exists_basis_lambdaComp_elemSymmMonomial`, and restriction carries `Λ_d` isomorphically
onto `𝒮_{n,d}`. -/
@[hjo "lem_mac_res_emonomial_basis"]
theorem exists_basis_symmetricHomogeneousSubmodule_restrictAlphabet (σ : Type*) [Fintype σ]
    (K : Type*) [CommRing K] [Algebra ℚ K] {d : ℕ} (hd : d ≤ Fintype.card σ) :
    ∃ B : Module.Basis (Nat.Partition d) K (symmetricHomogeneousSubmodule σ K d),
      ∀ μ : Nat.Partition d, (B μ : MvPolynomial σ K)
        = restrictAlphabet σ K (elemSymmMonomial K μ.parts) := by
  obtain ⟨B, hB⟩ := exists_basis_lambdaComp_elemSymmMonomial K d
  refine ⟨B.map (restrictAlphabetEquiv σ K hd), fun μ => ?_⟩
  rw [Module.Basis.map_apply, coe_restrictAlphabetEquiv, hB μ]

end HJO.Sym
