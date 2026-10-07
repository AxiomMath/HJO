/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.RealisationInjective
public import HJO.Symmetric.AxisFree
public meta import HJO.Attr

/-! # The power-sum monomials are a basis of a graded piece

`HJO.Sym.linearIndependent_pmonomial`: for every `d ≥ 0` the family `(p_λ)`, indexed by the
partitions `λ` of `d`, is a `𝕜`-basis of `Λ_d`.

## Main definitions

* `HJO.Sym.expOfPartition`: the exponent vector of `p_λ`, the section of `HJO.Sym.partsOfExp`.

## Main statements

* `HJO.Sym.degOfExp_eq_weight`: the weight of a monomial of `Λ` read two ways, which is the bridge
  between `HJO.Sym.degOfExp` and `HJO.Sym.LambdaComp`.
* `HJO.Sym.linearIndependent_pmonomial` and `HJO.Sym.span_pmonomial`:
  `HJO.Sym.linearIndependent_pmonomial`.

## Implementation notes

`Λ = MvPolynomial ℕ 𝕜` is the polynomial ring on the power sums, so `p_λ` is a *monomial* of it:
`expOfPartition` is the exponent vector, carrying `i + 1` with multiplicity, and
`HJO.Sym.pmonomial_eq_monomial` is the identification. Independence is then
`MvPolynomial.basisMonomials` reindexed along an injection, and spanning is
`HJO.Sym.lambdaComp_eq_span` — the defining description of `Λ_d` — with each of its
generators recognised as a `p_λ`. The bijection "partitions of `d` ↔ sequences `(a_k)`
with `∑ k a_k = d`" is exactly `expOfPartition` against `HJO.Sym.partitionOfExp`.

`HJO.Sym.degOfExp` and `Finsupp.weight (· + 1)` are two spellings of the same weight — the first
reading it off the multiset of parts, the second off the exponent vector. `degOfExp_eq_weight`
records that, so the two halves of this file can be stated in whichever one is natural for them;
without it `LambdaComp` and `partitionOfExp` are about the same grading and cannot be composed.

## References

This file proves `HJO.Sym.linearIndependent_pmonomial`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The exponent vector of a power-sum monomial -/

/-- **The exponent vector of `p_λ`**: the generator `p_{i+1}` occurs with the multiplicity of the
part `i + 1` in `λ`. -/
noncomputable def expOfPartition {d : ℕ} (l : Nat.Partition d) : ℕ →₀ ℕ :=
  Finsupp.onFinset (range d) (fun i => l.parts.count (i + 1)) fun i hi => by
    rw [mem_range]
    have hmem : i + 1 ∈ l.parts := Multiset.count_ne_zero.1 hi
    have hle := Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
    rw [l.parts_sum] at hle
    omega

theorem expOfPartition_apply {d : ℕ} (l : Nat.Partition d) (i : ℕ) :
    expOfPartition l i = l.parts.count (i + 1) := rfl

/-- `expOfPartition` is a section of `partsOfExp`: the parts it records are the parts of `λ`. -/
theorem partsOfExp_expOfPartition {d : ℕ} (l : Nat.Partition d) :
    partsOfExp (expOfPartition l) = l.parts := by
  refine Multiset.ext.2 fun x => ?_
  match x with
  | 0 =>
    rw [Multiset.count_eq_zero_of_notMem fun hx => absurd (partsOfExp_pos hx) (by omega),
      Multiset.count_eq_zero_of_notMem fun hx => absurd (l.parts_pos hx) (by omega)]
  | i + 1 => rw [count_partsOfExp, expOfPartition_apply]

theorem degOfExp_expOfPartition {d : ℕ} (l : Nat.Partition d) :
    degOfExp (expOfPartition l) = d := by
  rw [degOfExp, partsOfExp_expOfPartition, l.parts_sum]

theorem partitionOfExp_expOfPartition {d : ℕ} (l : Nat.Partition d) :
    partitionOfExp d (expOfPartition l) = l :=
  Nat.Partition.ext (by
    rw [parts_partitionOfExp (degOfExp_expOfPartition l), partsOfExp_expOfPartition])

theorem expOfPartition_injective {d : ℕ} : Function.Injective (expOfPartition (d := d)) :=
  fun l l' h => by rw [← partitionOfExp_expOfPartition l, ← partitionOfExp_expOfPartition l', h]

/-- **`p_λ` is a monomial of `Λ`**, at the exponent vector recording the multiplicities of the
parts of `λ`. -/
theorem pmonomial_eq_monomial (K : Type*) [CommRing K] {d : ℕ} (l : Nat.Partition d) :
    pmonomial K l = MvPolynomial.monomial (expOfPartition l) (1 : K) := by
  rw [← pmonomial_partitionOfExp K (degOfExp_expOfPartition l), partitionOfExp_expOfPartition]

/-! ### The two readings of the weight -/

theorem sum_finsetSum (t : Finset ℕ) (m : ℕ → Multiset ℕ) :
    (∑ i ∈ t, m i).sum = ∑ i ∈ t, (m i).sum := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.sum_add, ih]

/-- **The weight of a monomial of `Λ`, read off the parts or off the exponent vector.** This is what
lets `HJO.Sym.partitionOfExp` and `HJO.Sym.LambdaComp` speak about one grading. -/
theorem degOfExp_eq_weight (e : ℕ →₀ ℕ) : degOfExp e = Finsupp.weight (fun i => i + 1) e := by
  rw [degOfExp, partsOfExp, Finsupp.sum, sum_finsetSum, Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun i _ => by simp

/-! ### The basis -/

/-- `p_λ` is homogeneous of degree `d` when `λ` is a partition of `d`. -/
theorem pmonomial_mem_lambdaComp (K : Type*) [CommRing K] {d : ℕ} (l : Nat.Partition d) :
    pmonomial K l ∈ LambdaComp K d := by
  rw [pmonomial_eq_monomial, mem_lambdaComp]
  exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _
    (by rw [← degOfExp_eq_weight, degOfExp_expOfPartition])

/-- **Independence: the power-sum monomials of the partitions of `d` are
linearly independent.** They are distinct monomials of the polynomial ring `Λ`, and
`expOfPartition` is injective. -/
@[hjo "lem_sf_pmonomial_basis"]
theorem linearIndependent_pmonomial (K : Type*) [CommRing K] (d : ℕ) :
    LinearIndependent K fun l : Nat.Partition d => pmonomial K l := by
  have h := (MvPolynomial.basisMonomials ℕ K).linearIndependent.comp _
    (expOfPartition_injective (d := d))
  rw [MvPolynomial.coe_basisMonomials] at h
  simpa only [Function.comp_def, ← pmonomial_eq_monomial] using h

/-- **`HJO.Sym.linearIndependent_pmonomial`, spanning: the power-sum monomials of the partitions of
`d` span `Λ_d`.** `lambdaComp_eq_span` presents `Λ_d` as the span of the products of power sums of
total degree `d`, and each such product is `p_λ` for the partition its exponent vector records. -/
@[hjo "lem_sf_pmonomial_basis"]
theorem span_pmonomial (K : Type*) [CommRing K] (d : ℕ) :
    Submodule.span K (Set.range fun l : Nat.Partition d => pmonomial K l) = LambdaComp K d := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro f ⟨l, rfl⟩
    exact pmonomial_mem_lambdaComp K l
  · rw [lambdaComp_eq_span]
    refine Submodule.span_le.2 ?_
    rintro f ⟨e, he, rfl⟩
    rw [SetLike.mem_coe, prod_powerSum_eq_monomial]
    refine Submodule.subset_span ⟨partitionOfExp d e, ?_⟩
    exact pmonomial_partitionOfExp K (show degOfExp e = d by rw [degOfExp_eq_weight]; exact he)

end HJO.Sym
