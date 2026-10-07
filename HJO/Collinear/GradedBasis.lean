/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.OrzechProperty
public import HJO.Collinear.EsymmIndependent
public meta import HJO.Attr

/-! # The two bases of a graded piece of the ring of symmetric functions

`Λ = MvPolynomial ℕ K` is the polynomial ring on the power sums, `p_{i+1}` being the generator
`X i`, so a product `p_{λ₁}⋯p_{λ_m}` is the monomial whose exponent vector records the
multiplicities of the parts, `λ_i` contributing to the generator `λ_i - 1`. That identification is
a bijection between the partitions of `d` and the exponent vectors of weighted degree `d` for the
weight `i ↦ i + 1`: the two conditions on a partition -- positive parts, parts summing to `d` --
are exactly what makes the shift `λ_i ↦ λ_i - 1` invertible and the weighted degree `d`. Hence the
power-sum monomials `p_λ`, `λ` a partition of `d`, are a `K`-basis of `Λ_d`: they are a subfamily
of Mathlib's monomial basis of `Λ` composed with an injection, hence independent, and their span is
the span of *all* monomials of weighted degree `d`, which is `Λ_d`.

The elementary monomials `e_λ` are the image of that basis under the substitution `Φ : p_k ↦ e_k`
of `HJO.Sym.elemSymmSub`, by `HJO.Sym.elemSymmSub_powerSum`. That substitution is surjective
(`HJO.Sym.elemSymmSub_surjective`, Newton's identity solved for its last term) and weight-graded
(`HJO.Sym.elemSymmSub_mem_lambdaComp`), so it restricts to a surjective endomorphism of `Λ_d`: a
homogeneous function of degree `d` is the image of the degree `d` component of any preimage. And
`Λ_d` is a finitely generated module -- the power-sum basis has the finite index type
`Nat.Partition d` -- so a surjective endomorphism of it is bijective over any commutative ring.
Carrying the power-sum basis across that bijection gives the elementary monomials, and a basis.

## Main results

* `HJO.Sym.exists_basis_lambdaComp_prod_powerSum`.
* `HJO.Sym.exists_basis_lambdaComp_elemSymmMonomial`.

## Implementation notes

Nothing is sorted. One usually matches a product of power sums with a partition by putting its
parts in nonincreasing order; `Nat.Partition d` carries the parts as a multiset and the product of a
multiset does not depend on an ordering. The bijection is with exponent vectors rather than with
sorted lists, since it is exponent vectors that index `MvPolynomial.basisMonomials` and that
describe `Λ_d` through `HJO.Sym.lambdaComp_eq_span`.

Two of the private helpers are general facts with no `Λ` in them, stated here at the generality they
hold at because Mathlib has neither: `weight_toFinsupp` reads the weight of a multiset's
multiplicity vector as the sum of the weights of its elements, and `prod_map_X_eq_monomial`
identifies the product of the variables indexed by a multiset with the monomial of the corresponding
exponent vector.

The power-sum basis is assembled with `Module.Basis.span`, which makes the values of the basis the
given family by construction (`Module.Basis.coe_span_apply`), and then transported along the
equality of submodules `span K {p_λ} = Λ_d` by `LinearEquiv.ofEq`, which does not move the
underlying elements; the elementary basis is transported along
`LinearEquiv.ofBijective (elemSymmSubComp K d)`, which moves them by exactly the substitution. That
is what makes the second component of each conclusion hold on the nose.

The base is a commutative `ℚ`-algebra for the elementary monomials and an arbitrary commutative
ring for the power-sum ones. `[Algebra ℚ K]` is not decoration in the first: it is what makes `eₙ`
exist at all, `HJO.Sym.elemSymm` dividing by `n`. Over `ℤ` Newton's identity forces
`2 e_2 = p_1² - p_2`, whose coefficient at `p_1²` is odd, so no `e_2` exists in `Lambda ℤ`; the
obstruction is to this presentation of `Λ` by its power sums, not to the elementary symmetric
functions, which are integral in the monomial presentation. Surjectivity of the substitution and
the Orzech property of a commutative ring are all the elementary statement needs beyond that, so
no field and no finite dimensionality enters -- unlike `HJO.Sym.elemSymmSub_injective`, which gets
injectivity on `Λ` itself from a dimension count over a field.

## References

This file proves the lemmas
`HJO.Sym.exists_basis_lambdaComp_prod_powerSum` and
`HJO.Sym.exists_basis_lambdaComp_elemSymmMonomial`.
-/

@[expose] public section

open MvPolynomial

namespace HJO.Sym

/-! ### The power-sum monomials -/

/-- The weight of the multiplicity vector of a multiset is the sum of the weights of its
elements. -/
private theorem weight_toFinsupp {α M : Type*} [DecidableEq α] [AddCommMonoid M] (w : α → M)
    (m : Multiset α) : Finsupp.weight w (Multiset.toFinsupp m) = (m.map w).sum := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [← Multiset.singleton_add, map_add, map_add, Multiset.toFinsupp_singleton,
        Finsupp.weight_single, ih, Multiset.map_add, Multiset.sum_add]
      simp

/-- The product of the variables indexed by a multiset is the monomial whose exponent vector
records the multiplicities of that multiset. -/
private theorem prod_map_X_eq_monomial {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (m : Multiset σ) :
    (m.map (X : σ → MvPolynomial σ R)).prod = monomial (Multiset.toFinsupp m) 1 := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add,
        map_add, Multiset.toFinsupp_singleton, X, monomial_mul, one_mul]

/-- A product of power sums is the monomial of `Lambda K` whose exponent vector records, at the
generator `i`, the multiplicity of the part `i + 1`. -/
private theorem prod_map_powerSum_eq_monomial {K : Type*} [CommRing K] (m : Multiset ℕ) :
    (m.map (powerSum K)).prod = monomial (Multiset.toFinsupp (m.map (· - 1))) 1 := by
  rw [← prod_map_X_eq_monomial (R := K), Multiset.map_map]
  rfl

/-- Shifting the elements of a multiset of positive naturals down by one and back up again is the
identity. -/
private theorem map_pred_succ {m : Multiset ℕ} (hm : ∀ i ∈ m, 0 < i) :
    (m.map (· - 1)).map (fun i => i + 1) = m := by
  rw [Multiset.map_map]
  refine (Multiset.map_congr rfl fun x hx => ?_).trans (Multiset.map_id m)
  have := hm x hx
  simp only [Function.comp_apply, id]
  omega

/-- **Partitions of `d` are the exponent vectors of weighted degree `d`.** A partition `λ` of `d`
is sent to the vector recording, at the generator `i`, the multiplicity of the part `i + 1`; its
weighted degree for the weight `i ↦ i + 1` is the sum of the parts, namely `d`. -/
private noncomputable def partitionEquivWeightEq (d : ℕ) :
    Nat.Partition d ≃ {e : ℕ →₀ ℕ // Finsupp.weight (fun i => i + 1) e = d} where
  toFun μ := ⟨Multiset.toFinsupp (μ.parts.map (· - 1)), by
    rw [weight_toFinsupp, map_pred_succ fun i hi => μ.parts_pos hi, μ.parts_sum]⟩
  invFun e :=
    { parts := (Finsupp.toMultiset e.1).map (fun i => i + 1)
      parts_pos := by
        intro i hi
        obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hi
        omega
      parts_sum := by
        rw [← weight_toFinsupp, Finsupp.toMultiset_toFinsupp, e.2] }
  left_inv μ := by
    refine Nat.Partition.ext ?_
    dsimp only
    rw [Multiset.toFinsupp_toMultiset, map_pred_succ fun i hi => μ.parts_pos hi]
  right_inv e := by
    refine Subtype.ext ?_
    dsimp only
    have : ((Finsupp.toMultiset e.1).map (fun i => i + 1)).map (· - 1)
        = Finsupp.toMultiset e.1 := by
      rw [Multiset.map_map]
      exact (Multiset.map_congr rfl fun x _ => rfl).trans (Multiset.map_id _)
    rw [this, Finsupp.toMultiset_toFinsupp]

/-- **The power-sum monomials of a graded piece.** For every `d` the power-sum monomials
`p_λ = p_{λ₁}⋯p_{λ_m}`, indexed by the partitions `λ` of `d`, form a `K`-basis of the graded piece
`Λ_d`: there is a basis of `LambdaComp K d` over `Nat.Partition d` whose value at `λ` is the
product of the `p_i` over the parts `i` of `λ`. -/
@[hjo "lem_lambda_component_pmonomial_basis"]
theorem exists_basis_lambdaComp_prod_powerSum (K : Type*) [CommRing K] (d : ℕ) :
    ∃ B : Module.Basis (Nat.Partition d) K (LambdaComp K d),
      ∀ μ : Nat.Partition d, (B μ : Lambda K) = (μ.parts.map (powerSum K)).prod := by
  have hmono : ∀ μ : Nat.Partition d,
      (μ.parts.map (powerSum K)).prod = monomial ((partitionEquivWeightEq d μ).1) 1 :=
    fun μ => prod_map_powerSum_eq_monomial _
  have hli :
      LinearIndependent K (fun μ : Nat.Partition d => (μ.parts.map (powerSum K)).prod) := by
    have : (fun μ : Nat.Partition d => (μ.parts.map (powerSum K)).prod)
        = (basisMonomials ℕ K) ∘ (fun μ => (partitionEquivWeightEq d μ).1) := by
      funext μ; rw [hmono μ]; simp
    rw [this]
    exact (basisMonomials ℕ K).linearIndependent.comp _
      (Subtype.val_injective.comp (partitionEquivWeightEq d).injective)
  have hspan : Submodule.span K
      (Set.range fun μ : Nat.Partition d => (μ.parts.map (powerSum K)).prod)
      = LambdaComp K d := by
    rw [lambdaComp_eq_span]
    congr 1
    ext f
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨μ, rfl⟩
      exact ⟨(partitionEquivWeightEq d μ).1, (partitionEquivWeightEq d μ).2,
        by rw [prod_powerSum_eq_monomial, hmono μ]⟩
    · rintro ⟨e, he, rfl⟩
      refine ⟨(partitionEquivWeightEq d).symm ⟨e, he⟩, ?_⟩
      rw [hmono, Equiv.apply_symm_apply, prod_powerSum_eq_monomial]
  exact ⟨(Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan), fun μ => by simp⟩

/-! ### The elementary monomials -/

/-- The substitution `p_k ↦ e_k` sends the power-sum monomial of a multiset of positive parts to
the elementary monomial of the same multiset. -/
theorem elemSymmSub_prod_map_powerSum (K : Type*) [CommRing K] [Algebra ℚ K] {μ : Multiset ℕ}
    (hμ : ∀ i ∈ μ, 1 ≤ i) :
    elemSymmSub K (μ.map (powerSum K)).prod = elemSymmMonomial K μ := by
  rw [elemSymmMonomial, map_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod
    (Multiset.map_congr rfl fun i hi => elemSymmSub_powerSum K (hμ i hi))

/-- The substitution `p_k ↦ e_k` restricted to a graded piece, a linear endomorphism of that
piece. -/
noncomputable def elemSymmSubComp (K : Type*) [CommRing K] [Algebra ℚ K] (d : ℕ) :
    LambdaComp K d →ₗ[K] LambdaComp K d :=
  (elemSymmSub K).toLinearMap.restrict fun _ hf => elemSymmSub_mem_lambdaComp K hf

/-- The restriction of the substitution `p_k ↦ e_k` to a graded piece, on elements. -/
theorem elemSymmSubComp_coe (K : Type*) [CommRing K] [Algebra ℚ K] (d : ℕ)
    (f : LambdaComp K d) : (elemSymmSubComp K d f : Lambda K) = elemSymmSub K f := rfl

/-- **Degreewise surjectivity of `p_k ↦ e_k`.** A homogeneous symmetric function of degree `d` is
the image of a homogeneous one of the same degree: take the degree `d` component of any preimage,
which the substitution commutes with, being graded. -/
theorem elemSymmSubComp_surjective (K : Type*) [CommRing K] [Algebra ℚ K] (d : ℕ) :
    Function.Surjective (elemSymmSubComp K d) := by
  have hcomp : ∀ g : Lambda K,
      weightedHomogeneousComponent (fun i => i + 1) d (elemSymmSub K g)
        = elemSymmSub K (weightedHomogeneousComponent (fun i => i + 1) d g) :=
    weightedHomogeneousComponent_of_mem_lambdaComp (elemSymmSub K).toLinearMap
      (fun _ _ hf => elemSymmSub_mem_lambdaComp K hf) d
  rintro ⟨f, hf⟩
  obtain ⟨h, hh⟩ := elemSymmSub_surjective K f
  refine ⟨⟨weightedHomogeneousComponent (fun i => i + 1) d h,
    weightedHomogeneousComponent_mem _ h d⟩, Subtype.ext ?_⟩
  change elemSymmSub K (weightedHomogeneousComponent (fun i => i + 1) d h) = f
  rw [← hcomp h, hh]
  exact (mem_lambdaComp.1 hf).weightedHomogeneousComponent_same

/-- **Degreewise bijectivity of `p_k ↦ e_k`.** The graded piece `Λ_d` is a finitely generated
module, having a basis indexed by the finitely many partitions of `d`, and a surjective
endomorphism of such a module over a commutative ring is bijective. -/
theorem elemSymmSubComp_bijective (K : Type*) [CommRing K] [Algebra ℚ K] (d : ℕ) :
    Function.Bijective (elemSymmSubComp K d) := by
  obtain ⟨B, -⟩ := exists_basis_lambdaComp_prod_powerSum K d
  have : Module.Finite K (LambdaComp K d) := Module.Finite.of_basis B
  exact OrzechProperty.bijective_of_surjective_endomorphism _ (elemSymmSubComp_surjective K d)

/-- **The elementary monomials are a basis.** For every `d` the elementary monomials
`e_λ = e_{λ₁}⋯e_{λ_m}`, indexed by the partitions `λ` of `d`, form a `K`-basis of the graded piece
`Λ_d`: there is a basis of `LambdaComp K d` over `Nat.Partition d` whose value at `λ` is the
elementary monomial of `λ`. In particular `e_λ ∈ Λ_d`. -/
@[hjo "lem_cm_emonomial_basis"]
theorem exists_basis_lambdaComp_elemSymmMonomial (K : Type*) [CommRing K] [Algebra ℚ K] (d : ℕ) :
    ∃ B : Module.Basis (Nat.Partition d) K (LambdaComp K d),
      ∀ μ : Nat.Partition d, (B μ : Lambda K) = elemSymmMonomial K μ.parts := by
  obtain ⟨B, hB⟩ := exists_basis_lambdaComp_prod_powerSum K d
  refine ⟨B.map (LinearEquiv.ofBijective (elemSymmSubComp K d) (elemSymmSubComp_bijective K d)),
    fun μ => ?_⟩
  rw [Module.Basis.map_apply]
  change elemSymmSub K (B μ : Lambda K) = elemSymmMonomial K μ.parts
  rw [hB μ]
  exact elemSymmSub_prod_map_powerSum K fun i hi => μ.parts_pos hi

end HJO.Sym
