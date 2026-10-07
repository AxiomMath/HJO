/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import HJO.RankGraph
public meta import HJO.Attr

/-! # The weight of a collection of cycles in the rank graph

Fix `a`, `b` and a height `H`, and let `G_H` be the rank graph `HJO.Determinant.rankGraph a b H`:
the vertices `0, …, H`, the up edges `r → r + b` of weight `s q^{⌊r/a⌋}` and the down edges
`r → r - a` of weight `s`. A collection of vertex-disjoint simple directed cycles of `G_H` is
presented, here as elsewhere in this library, by the finite set of cyclic permutations of the
vertices that its cycles are, a cycle `c` having the vertices `c.support` and the edges `i → c i`
for `i ∈ c.support`. Its *weight* is the product, over the edges of all of its cycles, of those
edge weights.

The weight is built in two steps. The weight of a permutation `σ` of the vertices is the product
of the edge weights along the steps `i → σ i` that it makes, one factor for each vertex it moves;
the weight of a collection is the product of the weights of its members. Neither asks for a cycle
or for disjointness: those hypotheses belong to the theorems, and since `edgeWeight` already
vanishes off the two edge families, a permutation that steps along a non-edge has weight `0`, as
does any collection containing one.

Three facts make the two definitions usable without unfolding them. The weight of a member cycle
divides the weight of the collection, which is the divisibility behind the `q`-degree bound on the
vertices of a collection. The weight of the collection of cycles of a permutation is the weight of
that permutation, which is the shape the Leibniz expansion of `det(I - L_H)` hands over: the
permutations surviving that expansion are exactly the ones moving every vertex of their support
along an edge, and the collection they present is their set of cyclic factors. Finally, a
collection whose cycles do run along edges has for weight the single monomial `s^e q^w`, with `e`
the total number of its edges and `w` the sum of the levels `⌊r/a⌋` over the tails `r` of its up
edges — the form in which the `s`-degree and the `q`-degree of a weight are read off.

## Main definitions

* `HJO.Determinant.permWeight a b s q σ`: the weight of the permutation `σ` of the vertices of
  `G_H`, the product of the edge weights of its steps `i → σ i`. The weight of a single simple
  directed cycle of `G_H` is this at that cycle.
* `HJO.Determinant.collectionWeight a b s q C`: the weight of the collection `C`, the product over
  the cycles of `C` of their weights. For a `k`-collection, `k` being `C.card`, this is the
  weight `wt(C)`.

## Main results

* `HJO.Determinant.permWeight_dvd_collectionWeight`: the weight of a cycle of a collection divides
  the weight of the collection.
* `HJO.Determinant.collectionWeight_cycleFactorsFinset`: the weight of the collection of cycles of
  a permutation is the weight of that permutation.
* `HJO.Determinant.permWeight_eq_pow_mul_pow` and
  `HJO.Determinant.collectionWeight_eq_pow_mul_pow`: a weight all of whose steps are edges is the
  monomial `s^e q^w`, with `e` the number of edges and `w` the sum of the levels of the up edges.

## Implementation notes

The vertices are indexed by `Fin (H + 1)` rather than by `ℕ`, so that a permutation of them has a
finite support and a collection of cycles a finite set of them; the bounds `r ≤ H` in the
adjacency of `rankGraph a b H` are then automatic, and the height enters the weight only through
that index type, `edgeWeight` itself not mentioning `H`.

The hypothesis under which the monomial formula holds is stated as the disjunction
`σ i = i + b ∨ i = σ i + a`, the bare condition that each step be one of the two edge families,
rather than as adjacency in `rankGraph a b H`: on `Fin (H + 1)` the two are equivalent, and the
disjunction is what the computation uses. It is the condition `HJO.DetEquation.IsEdgePerm`
names, and the `adj` field of a simple directed cycle of `G_H`.

The `q`-exponent is written out as the sum `∑ i ∈ σ.support, if σ i = i + b then ⌊i/a⌋ else 0`
rather than through a name, so that the weight depends on nothing beyond the edge weights. It is
the exponent that `HJO.DetEquation.edgeExp` carries with an extra shift of the up-edge levels, and
the one that `HJO.DetCoeff.CycleSystem.weightExp` carries in the presentation of a collection by
its occupied vertex set.

`support_eq_biUnion_cycleFactorsFinset` is a statement about permutations alone, with nothing of
the rank graph in it, and is stated for an arbitrary permutation of a finite type; Mathlib carries
its membership form, `Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset`, but not
the identity of finite sets.

## References

`HJO.Determinant.collectionWeight` is used by
`HJO.Determinant.det_one_sub_edgeWeight_eq_sum_collectionWeight`,
`HJO.DetLimit.coeff_det_one_sub_weightedAdjacency_eq_zero` and
`HJO.Determinant.lt_of_degreeOf_collectionWeight_le`. See K. Lau, K. Ono and Y. Huang,
*Rogers-Ramanujan identities from the geometry of `X^a = Y^b`*, Section 6 "The rank graph and its
directed cycles" for the edge weights and the weight of a walk, and Section 7 "Finite determinants,
cofactors, and the second equation", Proposition 7.1, for the cycle expansion of the determinant
in which these weights appear.
-/

@[expose] public section

open Finset

namespace HJO.Determinant

variable {R : Type*} [CommMonoidWithZero R]

/-! ### The weight of a permutation of the vertices -/

/-- The weight of the permutation `σ` of the vertices of the rank graph `G_H`: the product, over
the vertices `i` that `σ` moves, of the weight of the step `i → σ i`. When `σ` is a simple directed
cycle of `G_H` these steps are its edges, and this is the weight of that cycle; when some step is
not an edge of `G_H` the corresponding factor, hence the product, is `0`. -/
def permWeight (a b : ℕ) (s q : R) {H : ℕ} (σ : Equiv.Perm (Fin (H + 1))) : R :=
  ∏ i ∈ σ.support, edgeWeight a b s q (i : ℕ) (σ i : ℕ)

/-- The identity permutation moves no vertex, so its weight is the empty product. -/
@[simp]
lemma permWeight_one (a b : ℕ) (s q : R) (H : ℕ) :
    permWeight a b s q (1 : Equiv.Perm (Fin (H + 1))) = 1 := by
  rw [permWeight, Equiv.Perm.support_one, Finset.prod_empty]

/-! ### The weight of a collection of cycles -/

/-- The **weight of a collection of vertex-disjoint cycles** in the rank graph `G_H`: the product,
over all edges of all of the cycles of `C`, of the edge weights of `G_H`. The cycles are presented
as cyclic permutations of the vertices, so this is the product over `c ∈ C` of the weight of `c`,
and for a `k`-collection — one with `C.card = k` — it is the weight `wt(C)`. -/
@[hjo "def_collection_weight"]
def collectionWeight (a b : ℕ) (s q : R) {H : ℕ} (C : Finset (Equiv.Perm (Fin (H + 1)))) : R :=
  ∏ c ∈ C, permWeight a b s q c

variable {a b H : ℕ} {c : Equiv.Perm (Fin (H + 1))} {C D : Finset (Equiv.Perm (Fin (H + 1)))}

/-- The empty collection, the unique `0`-collection, has weight `1`. -/
@[simp]
lemma collectionWeight_empty (a b : ℕ) (s q : R) (H : ℕ) :
    collectionWeight a b s q (∅ : Finset (Equiv.Perm (Fin (H + 1)))) = 1 :=
  Finset.prod_empty

/-- A `1`-collection has the weight of its single cycle. -/
@[simp]
lemma collectionWeight_singleton (a b : ℕ) (s q : R) (c : Equiv.Perm (Fin (H + 1))) :
    collectionWeight a b s q {c} = permWeight a b s q c := by
  rw [collectionWeight, Finset.prod_singleton]

/-- Adjoining a cycle to a collection multiplies the weight by the weight of that cycle. -/
lemma collectionWeight_insert (a b : ℕ) (s q : R) (h : c ∉ C) :
    collectionWeight a b s q (insert c C) = permWeight a b s q c * collectionWeight a b s q C :=
  Finset.prod_insert h

/-- The weight of a disjoint union of collections is the product of their weights. -/
lemma collectionWeight_union (a b : ℕ) (s q : R) (h : Disjoint C D) :
    collectionWeight a b s q (C ∪ D)
      = collectionWeight a b s q C * collectionWeight a b s q D :=
  Finset.prod_union h

/-- **The weight of a cycle of a collection divides the weight of the collection.** This is the
divisibility behind the bound on the vertices of a collection of bounded `q`-degree: the weight is
a monomial, so a bound on its `q`-degree bounds the `q`-degree of each of its cycles. -/
lemma permWeight_dvd_collectionWeight (a b : ℕ) (s q : R) (hc : c ∈ C) :
    permWeight a b s q c ∣ collectionWeight a b s q C :=
  Finset.dvd_prod_of_mem _ hc

/-! ### The weight of the collection of cycles of a permutation -/

/-- The support of a permutation is the union of the supports of its cyclic factors. Mathlib
carries the membership form of this,
`Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset`. -/
lemma support_eq_biUnion_cycleFactorsFinset {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm α) : σ.support = σ.cycleFactorsFinset.biUnion Equiv.Perm.support := by
  ext i
  rw [Finset.mem_biUnion]
  exact Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset

/-- **The weight of the collection of cycles of a permutation is the weight of that permutation.**
The cyclic factors of `σ` are vertex-disjoint and their supports cover `σ.support`, and each
factor agrees with `σ` on its own support, so the edges of the collection are exactly the steps of
`σ`. This is the shape in which the Leibniz expansion of `det(I - L_H)` produces a weight: it runs
over permutations, while the expansion runs over collections. -/
theorem collectionWeight_cycleFactorsFinset (a b : ℕ) (s q : R)
    (σ : Equiv.Perm (Fin (H + 1))) :
    collectionWeight a b s q σ.cycleFactorsFinset = permWeight a b s q σ := by
  have hdisj : (σ.cycleFactorsFinset : Set (Equiv.Perm (Fin (H + 1)))).PairwiseDisjoint
      Equiv.Perm.support := fun _ hc _ hc' hne =>
    (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ hc hc' hne).disjoint_support
  simp only [collectionWeight, permWeight]
  rw [support_eq_biUnion_cycleFactorsFinset σ, Finset.prod_biUnion hdisj]
  refine Finset.prod_congr rfl fun d hd => Finset.prod_congr rfl fun i hi => ?_
  rw [(Equiv.Perm.mem_cycleFactorsFinset_iff.1 hd).2 i hi]

/-! ### A weight is a monomial -/

/-- **The weight of a permutation all of whose steps are edges is a monomial.** Each step
contributes one factor of `s`, and an up step `i → i + b` contributes in addition the level
`⌊i/a⌋` of its tail, so the weight is `s^e q^w` with `e` the number of vertices moved — the number
of edges — and `w` the sum of the levels of the up steps. The hypothesis is that every step is one
of the two edge families of `G_H`, which on `Fin (H + 1)` is adjacency in `rankGraph a b H`. -/
theorem permWeight_eq_pow_mul_pow (a b : ℕ) (s q : R) {σ : Equiv.Perm (Fin (H + 1))}
    (hσ : ∀ i ∈ σ.support, (σ i : ℕ) = (i : ℕ) + b ∨ (i : ℕ) = (σ i : ℕ) + a) :
    permWeight a b s q σ =
      s ^ σ.support.card *
        q ^ ∑ i ∈ σ.support, if (σ i : ℕ) = (i : ℕ) + b then (i : ℕ) / a else 0 := by
  have hterm : ∀ i ∈ σ.support, edgeWeight a b s q (i : ℕ) (σ i : ℕ)
      = s * q ^ (if (σ i : ℕ) = (i : ℕ) + b then (i : ℕ) / a else 0) := by
    intro i hi
    by_cases hup : (σ i : ℕ) = (i : ℕ) + b
    · rw [ite_eq_left hup, hup, edgeWeight_up]
    · rw [ite_eq_right hup, pow_zero, mul_one, (hσ i hi).resolve_left hup, edgeWeight_down]
  rw [permWeight, Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum]

/-- **The weight of a collection all of whose steps are edges is a monomial.** Its `s`-degree is
the total number of edges of its cycles and its `q`-degree is the total of the levels of their up
edges; for coprime `a` and `b` each cycle has `a + b` edges, which is how a `k`-collection comes to
have `s`-degree `(a + b) k`. -/
theorem collectionWeight_eq_pow_mul_pow (a b : ℕ) (s q : R)
    (hC : ∀ c ∈ C, ∀ i ∈ c.support, (c i : ℕ) = (i : ℕ) + b ∨ (i : ℕ) = (c i : ℕ) + a) :
    collectionWeight a b s q C =
      s ^ (∑ c ∈ C, c.support.card) *
        q ^ ∑ c ∈ C, ∑ i ∈ c.support, if (c i : ℕ) = (i : ℕ) + b then (i : ℕ) / a else 0 := by
  rw [collectionWeight,
    Finset.prod_congr rfl fun c hc => permWeight_eq_pow_mul_pow a b s q (hC c hc),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

end HJO.Determinant
