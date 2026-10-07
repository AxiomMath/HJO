/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.PartitionDiagram
public meta import HJO.Attr

/-! # The power-sum monomial of a partition, and the independence of the monomial series

Two results: `p_λ = p_{λ₁}⋯p_{λ_m}`, and the linear independence of the monomial symmetric
series `m_λ` over the partitions of a fixed degree.

## Main definitions

* `HJO.Sym.pmonomial`: `p_λ`.
* `HJO.Sym.partitionExponent`: the exponent vector `x^λ` of a partition, the monomial that
  separates `m_λ` from every other `m_μ`.

## Main statements

* `HJO.Sym.linearIndependent_msymmSeries`.

## Implementation notes

`p_λ` is the product over the *multiset* of parts, which is the empty product `1` when `λ` is the
partition of `0`: no ordering of the parts is chosen, and none is needed, `Lambda K` being
commutative.

The independence is the proof verbatim: read the coefficient of `x^μ`. What has to be
supplied is `x^μ` itself as a `Finsupp`, which `partitionExponent` builds by `Finsupp.onFinset` from
the nonincreasing listing of the parts; `support_partitionExponent` is the computation that its
support is exactly the index range of the parts (all parts being positive) and
`map_partitionExponent` that reading the values off that support returns the multiset of parts.
Those two are what make `coeff_msymmSeries` fire at `x^μ`.

## References

The file formalises `HJO.Sym.pmonomial` and `HJO.Sym.linearIndependent_msymmSeries`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The power-sum monomial -/

/-- **The power-sum monomial of a partition** `p_λ = p_{λ₁}p_{λ₂}⋯p_{λ_m}`, the
empty product being `1`. Taken over the multiset of parts: `Lambda K` is commutative, so no listing
of the parts has to be chosen. -/
@[hjo "def_sf_pmonomial"]
noncomputable def pmonomial (K : Type*) [CommRing K] {d : ℕ} (p : Nat.Partition d) : Lambda K :=
  (p.parts.map (powerSum K)).prod

/-- **The power-sum monomial of the partition of `0` is `1`**, the empty product `p_{λ₁}⋯p_{λ_m}` at
`m = 0`. -/
@[hjo "def_sf_pmonomial"]
theorem pmonomial_of_parts_eq_zero (K : Type*) [CommRing K] {d : ℕ} {p : Nat.Partition d}
    (hp : p.parts = 0) : pmonomial K p = 1 := by
  rw [pmonomial, hp, Multiset.map_zero, Multiset.prod_zero]

/-- **Inserting a part multiplies the power-sum monomial by that power sum**, which is the
recursion the product `p_{λ₁}⋯p_{λ_m}` abbreviates. -/
@[hjo "def_sf_pmonomial"]
theorem pmonomial_of_parts_eq_cons (K : Type*) [CommRing K] {d : ℕ} {p : Nat.Partition d} {a : ℕ}
    {s : Multiset ℕ} (hp : p.parts = a ::ₘ s) :
    pmonomial K p = powerSum K a * (s.map (powerSum K)).prod := by
  rw [pmonomial, hp, Multiset.map_cons, Multiset.prod_cons]

/-! ### The exponent vector of a partition -/

/-- **The exponent vector `x^λ`**: the sequence whose `j`-th entry is the `j`-th part of `λ` in
nonincreasing order, and `0` past the length of `λ`. -/
noncomputable def partitionExponent {d : ℕ} (p : Nat.Partition d) : ℕ →₀ ℕ :=
  Finsupp.onFinset (range (Multiset.card p.parts))
    (fun j => (p.parts.sort (· ≥ ·)).getD j 0) fun j hj => by
      rw [mem_range, ← Multiset.length_sort (r := (· ≥ ·))]
      by_contra h
      exact hj (List.getD_eq_default _ 0 (by omega))

theorem partitionExponent_apply {d : ℕ} (p : Nat.Partition d) (j : ℕ) :
    partitionExponent p j = (p.parts.sort (· ≥ ·)).getD j 0 :=
  rfl

/-- The support of `x^λ` is the index range of the parts of `λ`: the parts are positive, so no
entry inside the range vanishes, and every entry outside it does. -/
theorem support_partitionExponent {d : ℕ} (p : Nat.Partition d) :
    (partitionExponent p).support = range (Multiset.card p.parts) := by
  classical
  rw [partitionExponent, Finsupp.support_onFinset]
  refine filter_true_of_mem fun j hj => ?_
  rw [mem_range, ← Multiset.length_sort (r := (· ≥ ·))] at hj
  rw [List.getD_eq_getElem _ 0 hj]
  exact (pos_of_mem_sort p (List.getElem_mem hj)).ne'

/-- Reading the entries of `x^λ` off its support returns the parts of `λ`. This is the clause
`coeff_msymmSeries` tests, so it is what makes the coefficient of `x^λ` in `m_λ` equal to `1`. -/
theorem map_partitionExponent {d : ℕ} (p : Nat.Partition d) :
    (partitionExponent p).support.val.map (partitionExponent p) = p.parts := by
  rw [support_partitionExponent]
  conv_rhs => rw [← Multiset.sort_eq p.parts (· ≥ ·)]
  rw [show (range (Multiset.card p.parts)).val
      = ((List.range (p.parts.sort (· ≥ ·)).length : List ℕ) : Multiset ℕ) by
    rw [Multiset.length_sort]; rfl]
  rw [Multiset.map_coe]
  refine congrArg _ (List.ext_getElem (by simp) fun n h₁ h₂ => ?_)
  simp only [List.getElem_map, List.getElem_range]
  rw [partitionExponent_apply, List.getD_eq_getElem _ 0 h₂]

/-- **The coefficient of `x^ν` in `m_μ`** is `1` when `μ = ν` and `0` otherwise: the monomial
`x^ν` occurs in `m_μ` exactly when the nonzero entries of its exponent vector, listed in
nonincreasing order, form `μ`, and they form `ν`. -/
theorem coeff_partitionExponent_msymmSeries (K : Type*) [CommRing K] {d : ℕ}
    (μ ν : Nat.Partition d) :
    MvPowerSeries.coeff (partitionExponent ν) (msymmSeries K μ) = if μ = ν then 1 else 0 := by
  rw [coeff_msymmSeries, map_partitionExponent]
  refine if_congr ⟨fun h => (Nat.Partition.ext h).symm, fun h => by rw [h]⟩ rfl rfl

/-- **The monomial symmetric series of the partitions of `d` are
linearly independent.** The coefficient of `x^ν` is `1` in `m_ν` and `0` in every other `m_μ`, so
reading that coefficient off a vanishing linear combination returns its `ν`-th scalar. -/
@[hjo "lem_sf_msymm_independent"]
theorem linearIndependent_msymmSeries (K : Type*) [CommRing K] (d : ℕ) :
    LinearIndependent K fun μ : Nat.Partition d => msymmSeries K μ := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg ν
  have hc := congrArg (MvPowerSeries.coeff (partitionExponent ν)) hg
  rw [map_sum, map_zero] at hc
  simp only [MvPowerSeries.coeff_smul, coeff_partitionExponent_msymmSeries, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hc
  exact hc

end HJO.Sym
