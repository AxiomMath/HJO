/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Determinant.DetCoeffSolves
public import HJO.RankGraph
public meta import HJO.Attr

/-! # Vertex-disjoint collections of cycles in the rank graph

Fix `a`, `b` and a height `H`, and let `G_H` be the rank graph `rankGraph a b H`: the vertices
`0, …, H` with the up edges `r → r + b` and the down edges `r → r - a`. A *simple directed cycle*
of `G_H` is a closed directed walk whose vertices are distinct except for the repeated initial
endpoint; a collection of such cycles is *vertex-disjoint* when no vertex of `G_H` lies on two of
them, and a *`k`-collection* is a vertex-disjoint collection of `k` of them. These are the objects
the transfer-matrix method enumerates: expanding `det(I - L_H)` by the Leibniz formula leaves
exactly the permutations of the vertices all of whose non-trivial orbits run along edges, and such
a permutation *is* a vertex-disjoint collection of cycles, its cycles being the orbits.

A cycle is presented as a cyclic permutation `c` of the vertices each of whose moved vertices `i`
is moved along an edge `i → c i` of `G_H`; a collection is a `Finset` of such cycles, pairwise
disjoint as permutations, which for permutations is exactly vertex-disjointness, and `k` is its
cardinality.

## Main definitions

* `HJO.Determinant.IsRankCycle a b H c`: the permutation `c` of the vertices of `G_H` is a simple
  directed cycle of `G_H`.
* `HJO.Determinant.IsCycleCollection a b H C`: the finite set `C` of permutations of the vertices
  of `G_H` is a collection of pairwise vertex-disjoint simple directed cycles of `G_H`; it is a
  `k`-collection when `C.card = k`.

## Main results

* `HJO.Determinant.isRankCycle_iff_isEdgePerm`: a cycle of `G_H` is a cyclic edge permutation in
  the sense of `HJO.DetEquation.IsEdgePerm`.
* `HJO.Determinant.isCycleCollection_cycleFactorsFinset` and
  `HJO.Determinant.IsCycleCollection.existsUnique_isEdgePerm`: the cycles of an edge permutation
  form a collection, and a collection is the set of cycles of a unique edge permutation -- the
  bijection the Leibniz expansion of `det(I - L_H)` is reindexed along.

## Implementation notes

A cycle is a permutation rather than a walk because `Digraph` carries no walk API, and because
`Equiv.Perm.IsCycle` has already quotiented by the choice of a starting point, so no ordering or
choice of a starting point of a cycle is counted; pairwise disjointness is
`Equiv.Perm.Disjoint`, whose `Finset` of cycles is `Equiv.Perm.cycleFactorsFinset` of the product.
The vertices are indexed by `Fin (H + 1)`, the index type of `transferMatrix a b H`, so the bound
`r ≤ H` inside `rankGraph a b H`'s adjacency is automatic. `k` is `C.card` rather than a parameter:
in `HJO.Determinant.lt_of_degreeOf_collectionWeight_le` the hypothesis `k ≥ 0` is never used, and in
`HJO.Determinant.det_one_sub_edgeWeight_eq_sum_collectionWeight` the `k` of the inner sum is read
off the collection. The comparison of collections across two heights, which
`HJO.DetLimit.coeff_coeff_det_one_sub_weightedAdjacency_eq` needs, is carried instead by
`HJO.DetCoeff.CycleSystem`.

## References

K. Lau, K. Ono and Y. Huang, *Rogers-Ramanujan identities from the geometry of `X^a = Y^b`*,
Section 6 "The rank graph and its directed cycles", and the paragraph of Section 7 "Finite
determinants, cofactors, and the second equation" that follows the definition of
`D_H(s,q) = det(I - L_H(s,q))`. -/

@[expose] public section

namespace HJO.Determinant

/-- A **simple directed cycle of the rank graph** `G_H`, presented as a permutation of its
vertices: `c` is a cyclic permutation of `Fin (H + 1)` and every vertex `i` it moves is moved
along an edge `i → c i` of `rankGraph a b H`. Its vertices are `c.support`, and its edges are the
`i → c i` for `i ∈ c.support`. -/
@[hjo "def_cycle_collection"]
structure IsRankCycle (a b H : ℕ) (c : Equiv.Perm (Fin (H + 1))) : Prop where
  /-- The vertices of `c` are distinct except for the repeated initial endpoint. -/
  isCycle : c.IsCycle
  /-- Every step `i → c i` of `c` is an edge of the rank graph. -/
  adj : ∀ i ∈ c.support, (rankGraph a b H).Adj (i : ℕ) (c i : ℕ)

/-- A **collection of vertex-disjoint cycles** in the rank graph `G_H`: a finite set `C` of
simple directed cycles of `rankGraph a b H`, pairwise disjoint as permutations, which for
permutations is exactly the condition that no vertex of `G_H` lies on two of them. It is a
*`k`-collection* when `C.card = k`. -/
@[hjo "def_cycle_collection"]
structure IsCycleCollection (a b H : ℕ) (C : Finset (Equiv.Perm (Fin (H + 1)))) : Prop where
  /-- Every member of `C` is a simple directed cycle of the rank graph. -/
  isRankCycle : ∀ c ∈ C, IsRankCycle a b H c
  /-- Distinct cycles of `C` share no vertex. -/
  pairwise_disjoint : (C : Set (Equiv.Perm (Fin (H + 1)))).Pairwise Equiv.Perm.Disjoint

variable {a b H : ℕ} {c : Equiv.Perm (Fin (H + 1))} {C : Finset (Equiv.Perm (Fin (H + 1)))}

/-- A simple directed cycle of `G_H` is the same thing as a cyclic edge permutation: on the
vertex type `Fin (H + 1)` the bounds `r ≤ H` in the adjacency of `rankGraph a b H` are
automatic. -/
lemma isRankCycle_iff_isEdgePerm :
    IsRankCycle a b H c ↔ c.IsCycle ∧ DetEquation.IsEdgePerm a b H c :=
  ⟨fun h => ⟨h.isCycle, fun i hi => (rankGraph_adj.1 (h.adj i hi)).1⟩,
    fun h => ⟨h.1, fun i hi => rankGraph_adj.2 ⟨h.2 i hi,
      Nat.lt_succ_iff.mp i.isLt, Nat.lt_succ_iff.mp (c i).isLt⟩⟩⟩

/-- The empty collection is the `0`-collection. -/
lemma isCycleCollection_empty : IsCycleCollection a b H ∅ where
  isRankCycle _ hc := absurd hc (Finset.notMem_empty _)
  pairwise_disjoint := by simp

/-- A single simple directed cycle is a `1`-collection. -/
lemma isCycleCollection_singleton (hc : IsRankCycle a b H c) : IsCycleCollection a b H {c} where
  isRankCycle _ hc' := Finset.mem_singleton.1 hc' ▸ hc
  pairwise_disjoint := by simp

/-- The cycles of a permutation moving every vertex of its support along an edge form a
collection of vertex-disjoint cycles: this is the direction the Leibniz expansion of
`det(I - L_H)` supplies. -/
theorem isCycleCollection_cycleFactorsFinset {σ : Equiv.Perm (Fin (H + 1))}
    (hσ : DetEquation.IsEdgePerm a b H σ) : IsCycleCollection a b H σ.cycleFactorsFinset where
  isRankCycle _ hc := isRankCycle_iff_isEdgePerm.2
    ⟨(Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc).1,
      DetCoeffSolves.isEdgePerm_of_mem_cycleFactorsFinset hσ hc⟩
  pairwise_disjoint := Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ

/-- Conversely, a collection of vertex-disjoint cycles is the set of cycles of a *unique*
permutation moving every vertex of its support along an edge, namely the product of its cycles:
`Equiv.Perm.cycleFactorsFinset` is injective, so the equation `σ.cycleFactorsFinset = C`
determines `σ`. Together with `isCycleCollection_cycleFactorsFinset` this says that the surviving
Leibniz terms are exactly the `k`-collections: it is the bijection the Leibniz expansion of
`det(I - L_H)` is reindexed along. -/
theorem IsCycleCollection.existsUnique_isEdgePerm (hC : IsCycleCollection a b H C) :
    ∃! σ : Equiv.Perm (Fin (H + 1)),
      DetEquation.IsEdgePerm a b H σ ∧ σ.cycleFactorsFinset = C := by
  set σ := C.noncommProd id (hC.pairwise_disjoint.mono' fun _ _ => Equiv.Perm.Disjoint.commute)
    with hσdef
  have hfac : σ.cycleFactorsFinset = C :=
    Equiv.Perm.cycleFactorsFinset_eq_finset.2
      ⟨fun _ hc => (hC.isRankCycle _ hc).isCycle, hC.pairwise_disjoint, hσdef.symm⟩
  refine ⟨σ, ⟨fun i hi => ?_, hfac⟩,
    fun τ hτ => Equiv.Perm.cycleFactorsFinset_injective (hτ.2.trans hfac.symm)⟩
  obtain ⟨c, hc, hic⟩ := Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.1 hi
  rw [← (Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc).2 i hic]
  exact (isRankCycle_iff_isEdgePerm.1 (hC.isRankCycle c (hfac ▸ hc))).2 i hic

end HJO.Determinant
