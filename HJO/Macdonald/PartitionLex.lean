/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Combinatorics.Young.YoungDiagram
public meta import HJO.Attr

/-! # The lexicographic order on partitions

`HJO.Sym.partitionLex`: for partitions `λ` and `μ`, `μ > λ` means that `μ` exceeds `λ` at the least
row where the two differ.

## The shape, and why it is not stated as "`μ ≠ λ` and at the least differing index"

It is usually phrased that way -- `μ ≠ λ`, and `μ_i > λ_i` at the least `i` where `μ_i` and `λ_i`
differ -- which needs the least differing index to exist before it says anything, so as a definition
it carries a side condition. The equivalent form used here,

  `∃ i, (∀ j < i, λ_j = μ_j) ∧ λ_i < μ_i`,

says the same thing without one: the `i` it produces IS the least differing index, since the rows
below `i` are equal by the first clause and `i` itself differs by the second. It is also the shape
Mathlib states lexicographic comparisons in (`DFinsupp.Lex.lt_iff`, `HahnSeries.lt_iff`), so a
consumer that wants to reuse Mathlib's order theory can. `HJO.Sym.partitionLex_ne` recovers the
`μ ≠ λ` clause, which is the half a consumer actually spends.

The convention that both are "extended by zeros beyond their lengths" is automatic:
`YoungDiagram.rowLen` is already `0` beyond the last row, so no truncation hypothesis appears.

The condition "of one and the same `d`" is also absent, and deliberately. Nothing in the
definition or in the two lemmas below uses it -- equal size matters to the CONSUMERS, which compare
partitions of a fixed degree, not to the order itself. Carrying it here would force every consumer
to supply it at each use and would make the relation's transitivity awkward to state.
-/

@[expose] public section

namespace HJO.Sym

/-- **The lexicographic order on partitions.** `partitionLex lam mu` is `mu > lam`: the two agree on
every row below some `i`, and at `i` the partition `mu` has the longer row.

The `i` produced is necessarily the least row at which they differ, which is what makes this the
usual reading; `HJO.Sym.partitionLex_ne` is its `mu ≠ lam` clause. -/
@[hjo "def_cm_partition_lex"]
def partitionLex (lam mu : YoungDiagram) : Prop :=
  ∃ i : ℕ, (∀ j < i, lam.rowLen j = mu.rowLen j) ∧ lam.rowLen i < mu.rowLen i

/-- **Lexicographically comparable partitions are distinct**, the `mu ≠ lam` clause.
Equal partitions have equal rows at every index, and the witness `i` has `lam_i < mu_i`. -/
theorem partitionLex_ne {lam mu : YoungDiagram} (h : partitionLex lam mu) : lam ≠ mu := by
  obtain ⟨i, _, hi⟩ := h
  exact fun hEq => absurd (hEq ▸ hi) (lt_irrefl _)

/-- The lexicographic order is irreflexive: a partition does not exceed itself at any row. -/
theorem not_partitionLex_self (lam : YoungDiagram) : ¬ partitionLex lam lam :=
  fun h => partitionLex_ne h rfl

/-- **The least differing row is the witness.** For a lexicographic comparison the witnessing index
is unique, so "the least `i` at which the rows differ" names exactly it. This is
what lets a consumer move between the two phrasings without carrying the existence of a least
differing index as a hypothesis. -/
theorem partitionLex_witness_unique {lam mu : YoungDiagram} {i i' : ℕ}
    (h : (∀ j < i, lam.rowLen j = mu.rowLen j) ∧ lam.rowLen i < mu.rowLen i)
    (h' : (∀ j < i', lam.rowLen j = mu.rowLen j) ∧ lam.rowLen i' < mu.rowLen i') : i = i' := by
  by_contra hne
  rcases Nat.lt_or_ge i i' with hlt | hge
  · exact absurd (h'.1 i hlt) (ne_of_lt h.2)
  · have hlt' : i' < i := lt_of_le_of_ne hge (Ne.symm hne)
    exact absurd (h.1 i' hlt') (ne_of_lt h'.2)

end HJO.Sym
