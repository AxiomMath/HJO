/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public meta import HJO.Attr

/-! # The rank graph and its directed cycles

Fix `a`, `b` and a height `H`. The *rank graph* `G_H` is the weighted directed graph on the
vertices `0, …, H` with two families of edges: the *up edges* `r → r + b`, of weight
`s q^{⌊r/a⌋}`, and the *down edges* `r → r - a`, of weight `s`. Its vertices are the ranks
`r = bx - ay` of the below-diagonal `(aN, bN)`-paths, and a closed walk at `0` of length `dN`,
`d = a + b`, is such a path, the product of its edge weights being `s^{dN} q^{area}`.

A closed walk of length `n` in `G_H` is recorded here by its cyclic list of vertices, a map
`c : ZMod n → ℕ` with `c i → c (i + 1)` an edge for every `i`; it is a *simple cycle* when `c`
is injective. This file defines the graph and its edge weights and proves the three combinatorial
facts about its closed walks that the enumeration of vertex-disjoint cycle collections needs: the
counts of the two kinds of step, the span bound, and the `q`-depth of the weight.

## Main definitions

* `HJO.Determinant.rankGraph a b H`: the edges of `G_H`, as a `Digraph ℕ`.
* `HJO.Determinant.edgeWeight a b s q r r'`: the weight of the edge `r → r'`, and `0` when there
  is no such edge.
* `HJO.Determinant.cyclicUpSteps`, `HJO.Determinant.cyclicDownSteps`: the indices of the up and
  of the down steps of a closed walk.

## Main results

* `HJO.Determinant.ncard_up_ncard_down_of_rankGraph_walk`: a closed walk of length `a + b` in
  `G_H` has exactly `a` up steps and exactly `b` down steps.
* `HJO.Determinant.pow_dvd_prod_edgeWeight`: the weight of a closed walk of `G_H` all of whose
  vertices are at least `r` is divisible by `q ^ (r / a)`.
* `HJO.Determinant.le_add_mul_of_rankGraph_walk`: two vertices of a closed walk of length `a + b`
  in `G_H` differ by at most `a * b`.
* `HJO.Determinant.eq_add_of_rankGraph_cycle`: a simple directed cycle of `G_H`, indexed by
  `ZMod n`, has `n = a + b`.

## Implementation notes

The vertex set `{0, …, H}` is recorded as a bound inside the adjacency relation rather than as the
vertex type `Fin (H + 1)`: `Digraph` has no vertex-set field, so the vertices above `H` survive as
isolated ones, carrying no edge and hence no walk. What is gained is that `H` enters only through
that bound, so `G_H` is literally a subgraph of `G_{H'}` for `H ≤ H'`.

`edgeWeight` does not mention `H`, because a weight belongs to an edge: in §6 (The rank graph and
its directed cycles) of *Rogers-Ramanujan identities from the geometry of `X^a = Y^b`* the graph on
all of `ℕ` carries the weights and `H` only deletes edges. Off the two families its value is `0`.
The two families overlap only when `a = b = 0`, where both prescribe `s`.

A walk is spelled as a map out of `ZMod n`, and not as a `Walk`, because Mathlib's `Digraph` is a
relation with a lattice structure, while `Walk`, `IsCycle` and `support` live on `SimpleGraph`,
which cannot see the direction of an edge.
-/

@[expose] public section

open Finset

namespace HJO.Determinant

variable {R : Type*} [MonoidWithZero R]

/-! ### The graph and its edge weights -/

/-- The weight of the edge `r → r'` of the rank graph: `s q^{⌊r/a⌋}` on an up edge `r → r + b`,
`s` on a down edge `r → r - a`, and `0` when `r` and `r'` are joined by neither. -/
@[hjo "def_transfer_graph"]
def edgeWeight (a b : ℕ) (s q : R) (r r' : ℕ) : R :=
  if r' = r + b then s * q ^ (r / a) else if r = r' + a then s else 0

/-- The rank graph `G_H`: the directed graph on the vertices `0, …, H` whose edges are the up
edges `r → r + b` and the down edges `r → r - a`. Their weights are `edgeWeight a b s q`. -/
@[hjo "def_transfer_graph"]
def rankGraph (a b H : ℕ) : Digraph ℕ where
  Adj r r' := (r' = r + b ∨ r = r' + a) ∧ r ≤ H ∧ r' ≤ H

/-- Adjacency in the rank graph, unfolded: an edge is an up step or a down step between two
vertices of `{0, …, H}`. -/
@[simp]
lemma rankGraph_adj {a b H r r' : ℕ} :
    (rankGraph a b H).Adj r r' ↔ (r' = r + b ∨ r = r' + a) ∧ r ≤ H ∧ r' ≤ H := Iff.rfl

/-- Adjacency in the rank graph is decidable, being a conjunction of decidable arithmetic. -/
instance (a b H : ℕ) : DecidableRel (rankGraph a b H).Adj :=
  fun _ _ => decidable_of_iff _ rankGraph_adj.symm

/-- The weight of an up edge `r → r + b` is `s q^{⌊r/a⌋}`. -/
@[simp]
lemma edgeWeight_up (a b : ℕ) (s q : R) (r : ℕ) : edgeWeight a b s q r (r + b) = s * q ^ (r / a) :=
  ite_eq_left rfl

/-- The weight of a down edge `r + a → r` is `s`. -/
@[simp]
lemma edgeWeight_down (a b : ℕ) (s q : R) (r : ℕ) : edgeWeight a b s q (r + a) r = s := by
  unfold edgeWeight
  split_ifs with hb ha
  · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    simp
  · rfl
  · exact absurd rfl ha

/-- Off the two edge families the weight is `0`. -/
lemma edgeWeight_eq_zero {a b : ℕ} {s q : R} {r r' : ℕ} (hup : r' ≠ r + b) (hdown : r ≠ r' + a) :
    edgeWeight a b s q r r' = 0 := by
  unfold edgeWeight
  rw [ite_eq_right hup, ite_eq_right hdown]

/-! ### The two kinds of step of a closed walk -/

/-- The up steps of the closed walk `c`: the indices `i` at which the step `c i → c (i + 1)`
raises the vertex by `b`. -/
def cyclicUpSteps (b : ℕ) {n : ℕ} [NeZero n] (c : ZMod n → ℕ) : Finset (ZMod n) :=
  {i | c (i + 1) = c i + b}

/-- The down steps of the closed walk `c`: the indices `i` at which the step `c i → c (i + 1)`
lowers the vertex by `a`. -/
def cyclicDownSteps (a : ℕ) {n : ℕ} [NeZero n] (c : ZMod n → ℕ) : Finset (ZMod n) :=
  {i | c i = c (i + 1) + a}

/-- Membership in the set of up steps. -/
@[simp]
lemma mem_cyclicUpSteps {b n : ℕ} [NeZero n] {c : ZMod n → ℕ} {i : ZMod n} :
    i ∈ cyclicUpSteps b c ↔ c (i + 1) = c i + b := by
  simp [cyclicUpSteps]

/-- Membership in the set of down steps. -/
@[simp]
lemma mem_cyclicDownSteps {a n : ℕ} [NeZero n] {c : ZMod n → ℕ} {i : ZMod n} :
    i ∈ cyclicDownSteps a c ↔ c i = c (i + 1) + a := by
  simp [cyclicDownSteps]

/-- The set of up steps is the up-step set of the statement of
`ncard_up_ncard_down_of_rankGraph_walk`, so its cardinality is that set's `Set.ncard`. -/
lemma ncard_setOf_up {b n : ℕ} [NeZero n] (c : ZMod n → ℕ) :
    {i | c (i + 1) = c i + b}.ncard = (cyclicUpSteps b c).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  simp

/-- The set of down steps is the down-step set of the statement of
`ncard_up_ncard_down_of_rankGraph_walk`, so its cardinality is that set's `Set.ncard`. -/
lemma ncard_setOf_down {a n : ℕ} [NeZero n] (c : ZMod n → ℕ) :
    {i | c i = c (i + 1) + a}.ncard = (cyclicDownSteps a c).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  simp

/-- Reindexing a sum over `ZMod n` along the successor map `i ↦ i + 1`, which is a bijection:
this is the telescoping identity behind every closure computation below. -/
lemma sum_shift_succ {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M] (f : ZMod n → M) :
    ∑ i, f (i + 1) = ∑ i, f i :=
  Fintype.sum_equiv (Equiv.addRight (1 : ZMod n)) _ _ fun _ => by simp

/-- **Closure and completeness of the step counts of a closed walk.** For `a + b ≠ 0` every step
of a closed walk in `rankGraph a b H` is of exactly one of the two kinds, so the two counts add up
to the length `n`; and summing the vertices around the walk telescopes, which turns the two step
relations into `u * b = v * a`. -/
lemma card_cyclicUpSteps_add_card_cyclicDownSteps {a b H n : ℕ} [NeZero n] (hd : a + b ≠ 0)
    {c : ZMod n → ℕ} (hadj : ∀ i, (rankGraph a b H).Adj (c i) (c (i + 1))) :
    (cyclicUpSteps b c).card + (cyclicDownSteps a c).card = n ∧
      (cyclicUpSteps b c).card * b = (cyclicDownSteps a c).card * a := by
  have hdisj : Disjoint (cyclicUpSteps b c) (cyclicDownSteps a c) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [mem_cyclicUpSteps] at hi
    rw [mem_cyclicDownSteps] at hi'
    omega
  have hunion : cyclicUpSteps b c ∪ cyclicDownSteps a c = Finset.univ := by
    refine Finset.eq_univ_of_forall fun i => ?_
    rcases (hadj i).1 with h | h
    · exact Finset.mem_union_left _ (mem_cyclicUpSteps.mpr h)
    · exact Finset.mem_union_right _ (mem_cyclicDownSteps.mpr h)
  refine ⟨?_, ?_⟩
  · rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, ZMod.card]
  · have key : ∑ i ∈ cyclicUpSteps b c ∪ cyclicDownSteps a c, ((c (i + 1) : ℤ) - c i) = 0 := by
      rw [hunion, Finset.sum_sub_distrib, sum_shift_succ fun i => (c i : ℤ)]
      exact sub_self _
    rw [Finset.sum_union hdisj] at key
    have hup : ∀ i ∈ cyclicUpSteps b c, ((c (i + 1) : ℤ) - c i) = (b : ℤ) := by
      intro i hi
      rw [mem_cyclicUpSteps] at hi
      rw [hi]
      push_cast
      ring
    have hdown : ∀ i ∈ cyclicDownSteps a c, ((c (i + 1) : ℤ) - c i) = -(a : ℤ) := by
      intro i hi
      rw [mem_cyclicDownSteps] at hi
      rw [eq_comm] at hi
      rw [← hi]
      push_cast
      ring
    rw [Finset.sum_eq_card_nsmul hup, Finset.sum_eq_card_nsmul hdown, nsmul_eq_mul,
      nsmul_eq_mul] at key
    have : ((cyclicUpSteps b c).card * b : ℤ) = ((cyclicDownSteps a c).card * a : ℤ) := by
      linear_combination key
    exact_mod_cast this

/-! ### The edge counts, the `q`-depth and the span -/

/-- **The edge types of a closed walk of length `d` are counted.** A closed walk of length
`n = a + b` in the rank graph `rankGraph a b H` — a map `c : ZMod n → ℕ` each of whose steps
`c i → c (i + 1)` is an edge — has exactly `a` up steps `c (i + 1) = c i + b` and exactly `b`
down steps `c i = c (i + 1) + a`. For coprime `a` and `b` a simple cycle has this length, by
`eq_add_of_rankGraph_cycle`, which gives the lemma in its form for simple cycles. -/
@[hjo "lem_cycle_edge_counts"]
theorem ncard_up_ncard_down_of_rankGraph_walk {a b H n : ℕ} (hn : n = a + b) {c : ZMod n → ℕ}
    (hadj : ∀ i, (rankGraph a b H).Adj (c i) (c (i + 1))) :
    {i | c (i + 1) = c i + b}.ncard = a ∧ {i | c i = c (i + 1) + a}.ncard = b := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    have huniv : ∀ p : ZMod 0 → Prop, (∀ i, p i) → {i | p i}.ncard = 0 := by
      intro p hp
      rw [Set.eq_univ_of_forall hp]
      exact Set.Infinite.ncard Set.infinite_univ
    refine ⟨huniv _ fun i => ?_, huniv _ fun i => ?_⟩
    · rcases (hadj i).1 with h | h <;> omega
    · rcases (hadj i).1 with h | h <;> omega
  · have : NeZero n := ⟨hn0.ne'⟩
    have hd : a + b ≠ 0 := by omega
    obtain ⟨hsum, hmul⟩ := card_cyclicUpSteps_add_card_cyclicDownSteps hd hadj
    rw [ncard_setOf_up, ncard_setOf_down]
    have hne : (a : ℤ) + b ≠ 0 := by exact_mod_cast hd
    have h1 : ((cyclicUpSteps b c).card : ℤ) + (cyclicDownSteps a c).card = (a : ℤ) + b := by
      exact_mod_cast hsum.trans hn
    have h2 : ((cyclicUpSteps b c).card : ℤ) * b = ((cyclicDownSteps a c).card : ℤ) * a := by
      exact_mod_cast hmul
    have hu : ((cyclicUpSteps b c).card : ℤ) = (a : ℤ) := by
      refine mul_right_cancel₀ hne ?_
      linear_combination (a : ℤ) * h1 + h2
    have hu' : (cyclicUpSteps b c).card = a := by exact_mod_cast hu
    exact ⟨hu', by omega⟩

/-- A bi-infinite closed walk each of whose steps is a loop is constant: over the index type `ℤ`
— which is `ZMod 0`, the length of a walk that does not close up — the successor map `i ↦ i + 1`
generates every translation. -/
lemma eq_of_forall_succ_eq {c : ℤ → ℕ} (h : ∀ i : ℤ, c (i + 1) = c i) (i j : ℤ) : c i = c j := by
  have key : ∀ k : ℤ, c (j + k) = c j := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      have hx : j + ((k : ℤ) + 1) = j + (k : ℤ) + 1 := by ring
      rw [hx, h, ih]
    | pred k ih =>
      have hx : j + (-(k : ℤ) - 1) + 1 = j + -(k : ℤ) := by ring
      rw [← h (j + (-(k : ℤ) - 1)), hx, ih]
  have h2 : j + (i - j) = i := by ring
  have hk := key (i - j)
  rw [h2] at hk
  exact hk

/-- **A closed walk of length `a + b` in the rank graph spans at most `ab`.** Two vertices of a
closed walk of length `n = a + b` in `rankGraph a b H` — a map `c : ZMod n → ℕ` each of whose
steps `c i → c (i + 1)` is an edge — differ by at most `a * b`. For coprime `a` and `b` a simple
cycle has this length, by `eq_add_of_rankGraph_cycle`; taking `c j` to be its least vertex `r`
gives the form for simple cycles, that every vertex is at most `r + a * b`. -/
@[hjo "lem_cycle_span"]
theorem le_add_mul_of_rankGraph_walk {a b H n : ℕ} (hn : n = a + b) {c : ZMod n → ℕ}
    (hadj : ∀ i, (rankGraph a b H).Adj (c i) (c (i + 1))) (i j : ZMod n) :
    c i ≤ c j + a * b := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    have h : ∀ x : ZMod 0, c (x + 1) = c x := by
      intro x
      rcases (hadj x).1 with hx | hx <;> omega
    simp [eq_of_forall_succ_eq h i j]
  · have : NeZero n := ⟨hn0.ne'⟩
    obtain ⟨hcount, -⟩ := ncard_up_ncard_down_of_rankGraph_walk hn hadj
    rw [ncard_setOf_up] at hcount
    have step : ∀ t : ℕ, c (j + (t : ZMod n)) ≤ c j + b *
        ((Finset.range t).filter
          fun s : ℕ => c (j + (s : ZMod n) + 1) = c (j + (s : ZMod n)) + b).card := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        have hcast : ((t + 1 : ℕ) : ZMod n) = (t : ZMod n) + 1 := by push_cast; ring
        rw [Finset.range_add_one, Finset.filter_insert, hcast, ← add_assoc]
        by_cases hu : c (j + (t : ZMod n) + 1) = c (j + (t : ZMod n)) + b
        · rw [ite_eq_left hu, Finset.card_insert_of_notMem (by simp), Nat.mul_succ,
            ← Nat.add_assoc, hu]
          exact Nat.add_le_add_right ih b
        · rw [ite_eq_right hu]
          have hdn : c (j + (t : ZMod n)) = c (j + (t : ZMod n) + 1) + a :=
            ((hadj (j + (t : ZMod n))).1).resolve_left hu
          omega
    have cnt_le : ∀ t : ℕ, t ≤ n →
        ((Finset.range t).filter
          fun s : ℕ => c (j + (s : ZMod n) + 1) = c (j + (s : ZMod n)) + b).card ≤ a := by
      intro t ht
      rw [← hcount]
      refine Finset.card_le_card_of_injOn (fun s : ℕ => j + (s : ZMod n)) ?_ ?_
      · intro s hs
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hs
        simpa using hs.2
      · intro s hs s' hs' heq
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hs hs'
        have hmod : ((s : ZMod n)) = ((s' : ZMod n)) := add_left_cancel heq
        rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, Nat.mod_eq_of_lt (hs.1.trans_le ht),
          Nat.mod_eq_of_lt (hs'.1.trans_le ht)] at hmod
        exact hmod
    have hij : j + (((i - j).val : ℕ) : ZMod n) = i := by
      rw [ZMod.natCast_rightInverse (i - j)]
      ring
    calc c i = c (j + (((i - j).val : ℕ) : ZMod n)) := by rw [hij]
      _ ≤ c j + b * ((Finset.range ((i - j).val)).filter
            fun s : ℕ => c (j + (s : ZMod n) + 1) = c (j + (s : ZMod n)) + b).card := step _
      _ ≤ c j + b * a :=
          Nat.add_le_add_left (Nat.mul_le_mul_left b (cnt_le _ (ZMod.val_lt (i - j)).le)) _
      _ = c j + a * b := by rw [Nat.mul_comm]

/-! ### The vertex count of a simple cycle -/

/-- The closure identity `u * b = v * a` on the step counts of a closed walk forces its length
`u + v` to be a multiple of `a + b`, when `a` and `b` are coprime. -/
lemma add_dvd_of_counts {a b u v : ℕ} (hab : Nat.Coprime a b) (hmul : u * b = v * a) :
    (a + b) ∣ u + v := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Nat.coprime_zero_left] at hab
    simp [hab]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [Nat.coprime_zero_right] at hab
    simp [hab]
  obtain ⟨t₁, ht₁⟩ : a ∣ u := hab.dvd_of_dvd_mul_right ⟨v, by rw [hmul]; ring⟩
  obtain ⟨t₂, ht₂⟩ : b ∣ v := hab.symm.dvd_of_dvd_mul_right ⟨u, by rw [← hmul]; ring⟩
  have ht : t₁ = t₂ := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos ha hb) (?_ : a * b * t₁ = a * b * t₂)
    calc a * b * t₁ = a * t₁ * b := by ring
      _ = u * b := by rw [← ht₁]
      _ = v * a := hmul
      _ = b * t₂ * a := by rw [← ht₂]
      _ = a * b * t₂ := by ring
  exact ⟨t₁, by rw [ht₁, ht₂, ht]; ring⟩

/-- **A simple cycle of the rank graph has `d = a + b` vertices.** For `a` and `b` coprime, a
simple directed cycle of `rankGraph a b H` — an injective `c : ZMod n → ℕ` each of whose steps
`c i → c (i + 1)` is an edge — has `n = a + b` vertices, hence that many edges. -/
@[hjo "lem_cycle_length"]
theorem eq_add_of_rankGraph_cycle {a b H n : ℕ} (hab : Nat.Coprime a b) {c : ZMod n → ℕ}
    (hc : Function.Injective c) (hadj : ∀ i, (rankGraph a b H).Adj (c i) (c (i + 1))) :
    n = a + b := by
  have hd : a + b ≠ 0 := by
    intro h
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    simp at hab
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hinj : Function.Injective
        fun i : ZMod 0 => (⟨c i, Nat.lt_succ_of_le (hadj i).2.1⟩ : Fin (H + 1)) := by
      intro p q hpq
      exact hc (by simpa using hpq)
    have : Finite (ZMod 0) := Finite.of_injective _ hinj
    exact not_finite (ZMod 0)
  have : NeZero n := ⟨hn0⟩
  -- The length is a multiple of `a + b`, by the two step counts and coprimality.
  have hdvd : (a + b) ∣ n := by
    obtain ⟨hsum, hmul⟩ := card_cyclicUpSteps_add_card_cyclicDownSteps hd hadj
    exact hsum ▸ add_dvd_of_counts hab hmul
  -- Each step moves the vertex by an amount congruent to `b` modulo `a + b`.
  have hcong : ∀ (x : ZMod n) (k : ℕ), ∃ m : ℤ,
      (c (x + (k : ZMod n)) : ℤ) = c x + k * b + ((a + b : ℕ) : ℤ) * m := by
    intro x k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨m, hm⟩ := ih
      have hcast : ((k + 1 : ℕ) : ZMod n) = (k : ZMod n) + 1 := by push_cast; ring
      rw [hcast, ← add_assoc]
      rcases (hadj (x + (k : ZMod n))).1 with h | h
      · refine ⟨m, ?_⟩
        rw [h]
        push_cast at hm ⊢
        linear_combination hm
      · refine ⟨m - 1, ?_⟩
        have h' : (c (x + (k : ZMod n)) : ℤ) = c (x + (k : ZMod n) + 1) + a := by
          rw [h]
          push_cast
          ring
        push_cast at hm h' ⊢
        linear_combination hm - h'
  -- One step is strictly monotone on a pair of vertices congruent modulo `a + b`.
  have hstep1 : ∀ x y : ZMod n, ((a + b : ℕ) : ℤ) ∣ (c y : ℤ) - c x → (c x : ℤ) < c y →
      ((a + b : ℕ) : ℤ) ∣ (c (y + 1) : ℤ) - c (x + 1) ∧ (c (x + 1) : ℤ) < c (y + 1) := by
    intro x y h1 h2
    have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
    have hb0 : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
    rcases (hadj x).1 with hx | hx <;> rcases (hadj y).1 with hy | hy
    · have ex : (c (x + 1) : ℤ) = c x + b := by rw [hx]; push_cast; ring
      have ey : (c (y + 1) : ℤ) = c y + b := by rw [hy]; push_cast; ring
      refine ⟨?_, by linarith⟩
      have e : (c (y + 1) : ℤ) - c (x + 1) = (c y : ℤ) - c x := by rw [ex, ey]; ring
      rw [e]
      exact h1
    · have ex : (c (x + 1) : ℤ) = c x + b := by rw [hx]; push_cast; ring
      have ey : (c y : ℤ) = c (y + 1) + a := by rw [hy]; push_cast; ring
      have hle : ((a + b : ℕ) : ℤ) ≤ (c y : ℤ) - c x := Int.le_of_dvd (by linarith) h1
      have hne : (c y : ℤ) - c x ≠ ((a + b : ℕ) : ℤ) := by
        intro heq
        have heq' : c (x + 1) = c (y + 1) := by
          have : (c (x + 1) : ℤ) = c (y + 1) := by push_cast at heq ⊢; linarith
          exact_mod_cast this
        have hxy : x = y := add_right_cancel (hc heq')
        rw [hxy] at h2
        exact absurd h2 (lt_irrefl _)
      have hlt : ((a + b : ℕ) : ℤ) < (c y : ℤ) - c x := lt_of_le_of_ne hle (Ne.symm hne)
      push_cast at hlt
      refine ⟨?_, by linarith⟩
      have e : (c (y + 1) : ℤ) - c (x + 1) = ((c y : ℤ) - c x) - ((a + b : ℕ) : ℤ) := by
        rw [ex, ey]
        push_cast
        ring
      rw [e]
      exact dvd_sub h1 dvd_rfl
    · have ex : (c x : ℤ) = c (x + 1) + a := by rw [hx]; push_cast; ring
      have ey : (c (y + 1) : ℤ) = c y + b := by rw [hy]; push_cast; ring
      refine ⟨?_, by linarith⟩
      have e : (c (y + 1) : ℤ) - c (x + 1) = ((c y : ℤ) - c x) + ((a + b : ℕ) : ℤ) := by
        rw [ex, ey]
        push_cast
        ring
      rw [e]
      exact dvd_add h1 dvd_rfl
    · have ex : (c x : ℤ) = c (x + 1) + a := by rw [hx]; push_cast; ring
      have ey : (c y : ℤ) = c (y + 1) + a := by rw [hy]; push_cast; ring
      refine ⟨?_, by linarith⟩
      have e : (c (y + 1) : ℤ) - c (x + 1) = (c y : ℤ) - c x := by rw [ex, ey]; ring
      rw [e]
      exact h1
  -- Hence walking `k` steps is strictly monotone on such a pair.
  have hmono : ∀ (k : ℕ) (x y : ZMod n), ((a + b : ℕ) : ℤ) ∣ (c y : ℤ) - c x →
      (c x : ℤ) < c y →
      ((a + b : ℕ) : ℤ) ∣ (c (y + (k : ZMod n)) : ℤ) - c (x + (k : ZMod n)) ∧
        (c (x + (k : ZMod n)) : ℤ) < c (y + (k : ZMod n)) := by
    intro k
    induction k with
    | zero =>
      intro x y h1 h2
      simpa using And.intro h1 h2
    | succ k ih =>
      intro x y h1 h2
      obtain ⟨g1, g2⟩ := ih x y h1 h2
      have hcast : ((k + 1 : ℕ) : ZMod n) = (k : ZMod n) + 1 := by push_cast; ring
      simp only [hcast, ← add_assoc]
      exact hstep1 _ _ g1 g2
  -- The `d`-th successor of a least vertex is itself, so `n` divides `d`.
  obtain ⟨x₀, -, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (ZMod n)) c ⟨0, Finset.mem_univ 0⟩
  have hfix : c (x₀ + ((a + b : ℕ) : ZMod n)) = c x₀ := by
    by_contra hne
    have hlt : (c x₀ : ℤ) < c (x₀ + ((a + b : ℕ) : ZMod n)) := by
      have h1 := hmin _ (Finset.mem_univ (x₀ + ((a + b : ℕ) : ZMod n)))
      exact_mod_cast lt_of_le_of_ne h1 fun h => hne h.symm
    have hcg : ((a + b : ℕ) : ℤ) ∣ (c (x₀ + ((a + b : ℕ) : ZMod n)) : ℤ) - c x₀ := by
      obtain ⟨m, hm⟩ := hcong x₀ (a + b)
      exact ⟨(b : ℤ) + m, by linear_combination hm⟩
    obtain ⟨-, hlt2⟩ := hmono ((n - 1) * (a + b)) x₀ (x₀ + ((a + b : ℕ) : ZMod n)) hcg hlt
    have hK1 : (((n - 1 : ℕ)) : ZMod n) = -1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0), ZMod.natCast_self, Nat.cast_one]
      ring
    have hK : x₀ + ((a + b : ℕ) : ZMod n) + (((n - 1) * (a + b) : ℕ) : ZMod n) = x₀ := by
      rw [Nat.cast_mul, hK1]
      ring
    rw [hK] at hlt2
    exact absurd (hmin _ (Finset.mem_univ _)) (by exact_mod_cast not_le.mpr hlt2)
  have hn_dvd : n ∣ a + b := by
    refine (ZMod.natCast_eq_zero_iff _ _).mp (add_left_cancel (a := x₀) ?_)
    rw [add_zero]
    exact hc hfix
  exact Nat.dvd_antisymm hn_dvd hdvd

variable {R : Type*} [CommMonoidWithZero R]

/-- **The weight of a closed walk of the rank graph is divisible by `q ^ ⌊r/a⌋` for `r` below all
of its vertices.** A closed walk of `rankGraph a b H` is a map `c : ZMod n → ℕ` each of whose
steps `c i → c (i + 1)` is an edge, and its weight is the product of the weights of its edges.
In particular a simple cycle with least vertex `r` has weight divisible by `q ^ ⌊r/a⌋`. -/
@[hjo "lem_cycle_qweight"]
theorem pow_dvd_prod_edgeWeight {a b H n : ℕ} [NeZero n] {s q : R} {c : ZMod n → ℕ} {r : ℕ}
    (hadj : ∀ i, (rankGraph a b H).Adj (c i) (c (i + 1))) (hr : ∀ i, r ≤ c i) :
    q ^ (r / a) ∣ ∏ i, edgeWeight a b s q (c i) (c (i + 1)) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  obtain ⟨i₀, hi₀⟩ : ∃ i : ZMod n, c (i + 1) = c i + b := by
    by_contra hcon
    push Not at hcon
    have hdown : ∀ i : ZMod n, c i = c (i + 1) + a := fun i => (hadj i).1.resolve_left (hcon i)
    have h1 : ∑ i : ZMod n, c i = ∑ i : ZMod n, (c (i + 1) + a) :=
      Finset.sum_congr rfl fun i _ => hdown i
    rw [Finset.sum_add_distrib, sum_shift_succ fun i => c i, Finset.sum_const, Finset.card_univ,
      ZMod.card, smul_eq_mul] at h1
    have hna : n * a = 0 := by simpa using h1
    have hn0 : n ≠ 0 := NeZero.ne n
    rcases Nat.mul_eq_zero.mp hna with h | h <;> omega
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i₀))
  rw [hi₀, edgeWeight_up]
  exact (pow_dvd_pow q (Nat.div_le_div_right (hr i₀))).mul_left s

end HJO.Determinant
