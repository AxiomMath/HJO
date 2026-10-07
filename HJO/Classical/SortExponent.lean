/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Logic.Denumerable
public import HJO.Classical.IotaPmonomial
public import HJO.Shuffle.LetterReversal
public meta import HJO.Attr

/-! # Sorting the letters of a monomial

A monomial `x^α` of the alphabet series ring is carried to the monomial `x^{μ_α}` of the partition
`μ_α` formed by the nonzero values of `α` by a *relabelling of the letters*, that is by a
permutation `ρ` of the index type `ℕ`. This file builds that permutation and records the one fact
about the tuple-counting series `HJO.Sym.tupleCount` that makes it useful: a coefficient of
`tupleCount L` is unchanged by a relabelling.

Together the two say that a coefficient of `ι(p_λ)` at an arbitrary `α` of total degree `d` equals
its coefficient at the exponent vector `x^{μ_α}` of a *partition* — which is what turns the two
coefficient facts of `HJO/Classical/IotaPmonomial.lean` into an expansion of `ι(p_λ)` in the
monomial symmetric series.

## Main definitions

* `HJO.Sym.partitionOfValues`: the partition `μ_α` formed by the nonzero values of `α`.
* `HJO.Sym.sortedSupport`: the support of `α` listed so that the values are nonincreasing.
* `HJO.Sym.sortIndex`: the permutation of `ℕ` carrying `0, 1, 2, …` to that listing, and everything
  past the support of `α` bijectively onto the complement of the support.

## Main statements

* `HJO.Sym.equivMapDomain_sortIndex`: `ρ · α = x^{μ_α}` for `ρ = (sortIndex α).symm`.
* `HJO.Sym.coeff_iota_eq_partitionOfValues`: the coefficient of a realised symmetric function at
  `x^α` is its coefficient at `x^{μ_α}`.

## Implementation notes

**The support has to be sorted with a tie-break, and that is the whole difficulty of the
permutation.** `Finset.sort` needs a decidable, transitive, *antisymmetric* and total relation, and
the pullback `α b ≤ α a` of the order on the values is not antisymmetric: two distinct letters can
carry the same exponent. `HJO.Sym.valueGE` therefore orders the letters by decreasing value and
breaks ties by the letter itself, which is antisymmetric because it is a lexicographic order on the
injective pair `a ↦ (α a, a)`.

**The permutation is assembled from the two halves of `Equiv.sumCompl`, not extended off a finite
piece.** `Equiv.extendSubtype` would produce a permutation of `ℕ` from a bijection between two
subtypes, but it needs `Fintype`, which neither `{j // j < #α.support}` nor its complement has here.
Instead: the bounded halves are matched by the sorted listing (`HJO.Sym.sortSub`), the two cofinite
halves are matched because a cofinite decidable subset of `ℕ` is `Denumerable`
(`Nat.Subtype.denumerable`), and `Equiv.sumCompl` glues the two matchings into a permutation of `ℕ`.

**The symmetry half is not proved here: it is already in the library.**
`HJO.Sym.letterPerm_realisation` (`HJO/Shuffle/LetterReversal.lean`) says that a realised
symmetric function is fixed by the relabelling endomorphism `letterPerm K ρ`, for every permutation
`ρ` of the alphabet and over any commutative ring; with `HJO.Sym.coeff_letterPerm` that is exactly
"a coefficient of `ι f` is unchanged by relabelling the letters". Nothing about `tupleCount`, and no
induction on the parts, is needed.

## References

This file serves `HJO.Sym.exists_triangular_msymm`, whose proof uses the fact "a permutation of
the variable indices carries the tuples producing `x^{α}` bijectively onto those producing the
monomial with the permuted exponent sequence".
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The support ordered by decreasing value -/

/-- **Letters ordered by decreasing `α`-value, ties broken by the letter.** The tie-break is what
makes the relation antisymmetric, hence usable by `Finset.sort`: `α b ≤ α a` alone identifies no two
letters carrying the same exponent. -/
def valueGE (α : ℕ →₀ ℕ) (a b : ℕ) : Prop := α b < α a ∨ (α a = α b ∧ a ≤ b)

instance (α : ℕ →₀ ℕ) : DecidableRel (valueGE α) := fun a b => by rw [valueGE]; infer_instance

instance (α : ℕ →₀ ℕ) : IsTrans ℕ (valueGE α) :=
  ⟨fun _ _ _ hab hbc => by simp only [valueGE] at *; omega⟩

instance (α : ℕ →₀ ℕ) : Std.Antisymm (valueGE α) :=
  ⟨fun _ _ hab hba => by simp only [valueGE] at *; omega⟩

instance (α : ℕ →₀ ℕ) : Std.Total (valueGE α) := ⟨fun _ _ => by simp only [valueGE]; omega⟩

theorem le_of_valueGE {α : ℕ →₀ ℕ} {a b : ℕ} (h : valueGE α a b) : α b ≤ α a := by
  rcases h with h | ⟨h, _⟩ <;> omega

/-- **The support of `α`, listed so that the values are nonincreasing.** -/
noncomputable def sortedSupport (α : ℕ →₀ ℕ) : List ℕ := α.support.sort (valueGE α)

theorem length_sortedSupport (α : ℕ →₀ ℕ) : (sortedSupport α).length = #α.support :=
  Finset.length_sort _

theorem mem_sortedSupport {α : ℕ →₀ ℕ} {a : ℕ} : a ∈ sortedSupport α ↔ a ∈ α.support :=
  Finset.mem_sort _

theorem sortedSupport_nodup (α : ℕ →₀ ℕ) : (sortedSupport α).Nodup := Finset.sort_nodup _ _

/-- The values along the sorted support are nonincreasing. -/
theorem pairwise_map_sortedSupport (α : ℕ →₀ ℕ) :
    ((sortedSupport α).map α).Pairwise (· ≥ ·) :=
  List.pairwise_map.2 ((Finset.pairwise_sort _ _).imp fun h => le_of_valueGE h)

theorem coe_map_sortedSupport (α : ℕ →₀ ℕ) :
    (((sortedSupport α).map α : List ℕ) : Multiset ℕ) = α.support.val.map α := by
  rw [← Multiset.map_coe, sortedSupport, Finset.sort_eq]

/-! ### The partition formed by the values -/

theorem degHom_apply (α : ℕ →₀ ℕ) : degHom α = ∑ i ∈ α.support, α i := by
  rw [degHom, Finsupp.liftAddHom_apply, Finsupp.sum]
  rfl

/-- The multiset of nonzero values of an exponent vector: the parts of the partition it determines,
and the multiset `HJO.Sym.msymmSeries` reads off it. -/
noncomputable def valueParts (α : ℕ →₀ ℕ) : Multiset ℕ := α.support.val.map α

theorem valueParts_pos {α : ℕ →₀ ℕ} {x : ℕ} (hx : x ∈ valueParts α) : 0 < x := by
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 hx
  exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hi)

theorem sum_valueParts (α : ℕ →₀ ℕ) : (valueParts α).sum = degHom α := by
  rw [valueParts, degHom_apply, Finset.sum_eq_multiset_sum]

/-- **The partition `μ_α` of an exponent vector of total degree `d`**: its parts are the nonzero
values of `α`. -/
noncomputable def partitionOfValues {d : ℕ} {α : ℕ →₀ ℕ} (h : degHom α = d) : Nat.Partition d where
  parts := valueParts α
  parts_pos := valueParts_pos
  parts_sum := by rw [sum_valueParts, h]

theorem parts_partitionOfValues {d : ℕ} {α : ℕ →₀ ℕ} (h : degHom α = d) :
    (partitionOfValues h).parts = α.support.val.map α := rfl

/-- The nonincreasing listing of the parts of `μ_α` is the list of values along the sorted support:
both are nonincreasing lists with the same multiset of entries. -/
theorem sort_parts_partitionOfValues {d : ℕ} {α : ℕ →₀ ℕ} (h : degHom α = d) :
    (partitionOfValues h).parts.sort (· ≥ ·) = (sortedSupport α).map α := by
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _)
    (pairwise_map_sortedSupport α) (Multiset.coe_eq_coe.1 ?_)
  rw [Multiset.sort_eq, parts_partitionOfValues, ← coe_map_sortedSupport]

/-! ### The sorting permutation -/

/-- The indices below the size of the support, matched with the support in order of decreasing
value. -/
noncomputable def sortSub (α : ℕ →₀ ℕ) :
    {j : ℕ // j < #α.support} ≃ {i : ℕ // i ∈ α.support} :=
  Equiv.ofBijective
    (fun j => ⟨(sortedSupport α)[j.1]'(by rw [length_sortedSupport]; exact j.2),
      mem_sortedSupport.1 (List.getElem_mem _)⟩)
    ⟨fun j k hjk => Subtype.ext
      ((sortedSupport_nodup α).getElem_inj_iff.1 (Subtype.ext_iff.1 hjk)),
      fun i => by
        obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.1 (mem_sortedSupport.2 i.2)
        exact ⟨⟨j, by rwa [← length_sortedSupport]⟩, Subtype.ext hji⟩⟩

/-- The indices past the support, matched with the letters off the support: both are cofinite
decidable subsets of `ℕ`, hence denumerable. -/
noncomputable def sortCompl (α : ℕ →₀ ℕ) :
    {j : ℕ // ¬ j < #α.support} ≃ {i : ℕ // i ∉ α.support} := by
  classical
  haveI : Infinite ({j : ℕ | ¬ j < #α.support} : Set ℕ) :=
    Infinite.of_injective
      (fun k : ℕ => (⟨#α.support + k, by simp⟩ : ({j : ℕ | ¬ j < #α.support} : Set ℕ)))
      fun a b h => by simpa using h
  haveI : Infinite ({i : ℕ | i ∉ α.support} : Set ℕ) :=
    Set.infinite_coe_iff.2 (Set.Finite.infinite_compl (s := (α.support : Set ℕ))
      α.support.finite_toSet)
  letI := Nat.Subtype.denumerable {j : ℕ | ¬ j < #α.support}
  letI := Nat.Subtype.denumerable {i : ℕ | i ∉ α.support}
  exact Denumerable.equiv₂ ({j : ℕ | ¬ j < #α.support} : Set ℕ) ({i : ℕ | i ∉ α.support} : Set ℕ)

/-- **The sorting relabelling of the letters.** It carries `j` to the `j`-th letter of the support
of `α` in order of decreasing value, and the indices past the support bijectively onto the letters
off the support. -/
noncomputable def sortIndex (α : ℕ →₀ ℕ) : ℕ ≃ ℕ :=
  (Equiv.sumCompl (· < #α.support)).symm.trans
    (((sortSub α).sumCongr (sortCompl α)).trans (Equiv.sumCompl (· ∈ α.support)))

theorem sortIndex_apply_of_lt {α : ℕ →₀ ℕ} {j : ℕ} (hj : j < #α.support) :
    sortIndex α j = (sortedSupport α)[j]'(by rw [length_sortedSupport]; exact hj) := by
  rw [sortIndex, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.sumCompl_symm_apply_of_pos (p := (· < #α.support)) hj, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.sumCompl_apply_inl]
  rfl

theorem sortIndex_notMem_support {α : ℕ →₀ ℕ} {j : ℕ} (hj : ¬ j < #α.support) :
    sortIndex α j ∉ α.support := by
  rw [sortIndex, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.sumCompl_symm_apply_of_neg (p := (· < #α.support)) hj, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.sumCompl_apply_inr]
  exact (sortCompl α ⟨j, hj⟩).2

/-- **The sorting permutation carries `x^α` to `x^{μ_α}`.** Below the size of the support the value
read off is the `j`-th largest, which is the `j`-th part of `μ_α`; past it both sides vanish. -/
theorem equivMapDomain_sortIndex {d : ℕ} {α : ℕ →₀ ℕ} (h : degHom α = d) :
    Finsupp.equivMapDomain (sortIndex α).symm α = partitionExponent (partitionOfValues h) := by
  refine Finsupp.ext fun j => ?_
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm, partitionExponent_apply,
    sort_parts_partitionOfValues]
  by_cases hj : j < #α.support
  · rw [sortIndex_apply_of_lt hj,
      List.getD_eq_getElem _ 0 (by rw [List.length_map, length_sortedSupport]; exact hj),
      List.getElem_map]
  · rw [Finsupp.notMem_support_iff.1 (sortIndex_notMem_support hj),
      List.getD_eq_default _ 0 (by rw [List.length_map, length_sortedSupport]; omega)]

/-! ### Reading a coefficient at a partition -/

/-- **A coefficient of a realised symmetric function is read at a partition.** Its value at `x^α`
is its value at the monomial `x^{μ_α}` of the partition formed by the values of `α`: the sorting
permutation carries the one monomial to the other, and `HJO.Sym.letterReverse_realisation`'s
`HJO.Sym.letterPerm_realisation` says a realised symmetric function does not notice. -/
theorem coeff_iota_eq_partitionOfValues {K : Type*} [CommRing K]
    {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι) (f : Lambda K) {d : ℕ}
    {α : ℕ →₀ ℕ} (h : degHom α = d) :
    MvPowerSeries.coeff α (ι f)
      = MvPowerSeries.coeff (partitionExponent (partitionOfValues h)) (ι f) := by
  conv_lhs => rw [← letterPerm_realisation hι (sortIndex α) f]
  rw [coeff_letterPerm, equivMapDomain_sortIndex h]

/-- **A coefficient of `ι(p_λ)` is read at a partition.** -/
theorem coeff_iota_pmonomial_eq_partitionOfValues {K : Type*} [CommRing K]
    {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι) {d : ℕ} (p : Nat.Partition d)
    {α : ℕ →₀ ℕ} (h : degHom α = d) :
    MvPowerSeries.coeff α (ι (pmonomial K p))
      = MvPowerSeries.coeff (partitionExponent (partitionOfValues h)) (ι (pmonomial K p)) :=
  coeff_iota_eq_partitionOfValues hι _ h

end HJO.Sym
