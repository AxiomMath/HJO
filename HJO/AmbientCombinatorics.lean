/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Order.Preorder.Finite
public meta import HJO.Attr

/-! # Three ambient facts: maximal pairs, splitting a monomial, and empty rows

Three steps of the symmetric-function argument are about no object of this library at all: they
are facts about a finite set of pairs, about a monomial, and about a Young diagram, and each is
stated here in the namespace of its own subject rather than in one of ours.

* The *maximal attacking pair* of that argument is produced by a bare finiteness argument: inside
  a nonempty finite set of pairs there is one that can be widened at neither end. Taking the set
  inside `{(j, j') : 1 ≤ j < j' ≤ m}` gives the maximal attacking pair.
* *Splitting a monomial off two letters*: every monomial of total degree `d` is uniquely
  `ρ · u ^ a · v ^ b` with `ρ` free of `u` and of `v`. On exponent vectors the product is a sum, so
  the assertion is that `(ρ, a, b) ↦ ρ + single u a + single v b` is a bijection.
* A partition *vanishes beyond its number of cells*: once the row index reaches `|μ|`, the row is
  empty, because a nonempty row `i` forces the rows `0, …, i` to be nonempty too.

## Main results

* `Finset.exists_maximal_prod`: a nonempty finite set of pairs contains a pair that cannot be
  widened inside it at either end.
* `Finsupp.bijOn_add_single_add_single`: for `u ≠ v`, the map
  `(ρ, a, b) ↦ ρ + single u a + single v b` is a bijection from the triples with `ρ u = 0`,
  `ρ v = 0` and `degree ρ + a + b = d` onto the finitely supported functions of degree `d`.
* `YoungDiagram.rowLen_eq_zero_of_card_le`: `μ.rowLen i = 0` whenever `μ.card ≤ i`.

## Implementation notes

The maximal pair is found in two steps rather than by a single descent, and deliberately: the
one-step argument — widen the pair repeatedly and appeal to finiteness — has no decreasing measure
in a preorder, the lexicographic relation on the two coordinates failing to be transitive there.
Instead a maximal second coordinate is chosen first, which makes the first condition automatic, and
a minimal first coordinate among the pairs carrying it second. Both choices are
`Finset.exists_maximal` / `Finset.exists_minimal`, which need only a preorder.

Monomials are recorded as their exponent vectors `L →₀ M` and the total degree as `Finsupp.degree`.
The exponents are not required to be natural numbers: nothing subtracts or compares them, so `M` is
an arbitrary additive commutative monoid, and in particular injectivity is proved by reading the
three parts off the image pointwise rather than by cancelling the two `single`s, which a general `M`
would not allow.

The vanishing of the later rows is stated as the equation and not as the contrapositive
`0 < μ.rowLen i → i < μ.card`, because the lemmas that use it rewrite with it. The sharper count
`(i + 1) * μ.rowLen i ≤ μ.card`, which the same argument gives, is a different assertion from the
statement `μ_i = 0` for `i > |μ|` and is not claimed here.
-/

@[expose] public section

namespace Finset

/-- A nonempty finite set `R` of pairs contains a pair `(a, b)` that cannot be widened inside `R`
at either end: `(a, j) ∉ R` for every `j > b` and `(j, b) ∉ R` for every `j < a`. Taking `R` inside
`{(j, j') : 1 ≤ j < j' ≤ m}` gives the maximal attacking pair. -/
@[hjo "lem_cm_max_pair"]
theorem exists_maximal_prod {α β : Type*} [Preorder α] [Preorder β] {R : Finset (α × β)}
    (hR : R.Nonempty) :
    ∃ a b, (a, b) ∈ R ∧ (∀ j, b < j → (a, j) ∉ R) ∧ (∀ j, j < a → (j, b) ∉ R) := by
  classical
  obtain ⟨b, hbmem, hbmax⟩ := (R.image Prod.snd).exists_maximal (hR.image _)
  simp only [Finset.mem_image] at hbmem
  obtain ⟨p, hp, rfl⟩ := hbmem
  obtain ⟨a, hamem, hamin⟩ := ({q ∈ R | q.2 = p.2}.image Prod.fst).exists_minimal
    ⟨p.1, Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩⟩
  simp only [Finset.mem_image, Finset.mem_filter] at hamem
  obtain ⟨q, ⟨hqR, hq2⟩, rfl⟩ := hamem
  refine ⟨q.1, q.2, by simpa using hqR, ?_, ?_⟩
  · intro j hj hmem
    rw [hq2] at hj
    exact hj.not_ge (hbmax (Finset.mem_image.mpr ⟨(q.1, j), hmem, rfl⟩) hj.le)
  · intro j hj hmem
    exact hj.not_ge (hamin
      (Finset.mem_image.mpr ⟨(j, q.2), Finset.mem_filter.mpr ⟨hmem, hq2⟩, rfl⟩) hj.le)

end Finset

namespace Finsupp

/-- **Splitting a monomial off two letters.** For distinct letters `u ≠ v` and a degree `d`, the map
`(ρ, a, b) ↦ ρ + single u a + single v b` — the exponent-vector form of
`(ρ, a, b) ↦ ρ · u ^ a · v ^ b` — is a bijection from the triples in which `ρ` is a monomial with
no `u` and no `v` and the degrees satisfy `deg ρ + a + b = d`, onto the monomials of total degree
`d` in the letters of `L`. -/
@[hjo "lem_cm_zmon_split"]
theorem bijOn_add_single_add_single {L M : Type*} [AddCommMonoid M] (u v : L) (huv : u ≠ v)
    (d : M) :
    Set.BijOn (fun p : (L →₀ M) × M × M => p.1 + single u p.2.1 + single v p.2.2)
      {p | p.1 u = 0 ∧ p.1 v = 0 ∧ degree p.1 + p.2.1 + p.2.2 = d}
      {μ | degree μ = d} := by
  have key : ∀ (ρ : L →₀ M) (a b : M),
      degree (ρ + single u a + single v b) = degree ρ + a + b := by
    intro ρ a b
    rw [map_add, map_add, degree_single, degree_single]
  refine ⟨fun p hp => (key p.1 p.2.1 p.2.2).trans hp.2.2, fun p hp p' hp' hpp' => ?_,
    fun μ hμ => ?_⟩
  · obtain ⟨hu, hv, -⟩ := hp
    obtain ⟨hu', hv', -⟩ := hp'
    have hau : p.2.1 = p'.2.1 := by
      have := congrArg (fun f => f u) hpp'
      simpa [hu, hu', single_eq_same, single_eq_of_ne huv] using this
    have hbv : p.2.2 = p'.2.2 := by
      have := congrArg (fun f => f v) hpp'
      simpa [hv, hv', single_eq_same, single_eq_of_ne huv.symm] using this
    have hρ : p.1 = p'.1 := by
      refine Finsupp.ext fun w => ?_
      by_cases hwu : w = u
      · rw [hwu, hu, hu']
      by_cases hwv : w = v
      · rw [hwv, hv, hv']
      have := congrArg (fun f => f w) hpp'
      simpa [single_eq_of_ne hwu, single_eq_of_ne hwv] using this
    exact Prod.ext hρ (Prod.ext hau hbv)
  · have hu : ((μ.erase u).erase v) u = 0 := by rw [erase_ne huv, erase_same]
    have hv : ((μ.erase u).erase v) v = 0 := erase_same
    have hid : (μ.erase u).erase v + single u (μ u) + single v (μ v) = μ := by
      refine Finsupp.ext fun w => ?_
      by_cases hwu : w = u
      · subst hwu
        rw [add_apply, add_apply, hu, single_eq_same, single_eq_of_ne huv, zero_add, add_zero]
      by_cases hwv : w = v
      · subst hwv
        rw [add_apply, add_apply, hv, single_eq_of_ne hwu, single_eq_same, add_zero, zero_add]
      rw [add_apply, add_apply, single_eq_of_ne hwu, single_eq_of_ne hwv, add_zero, add_zero,
        erase_ne hwv, erase_ne hwu]
    exact ⟨((μ.erase u).erase v, μ u, μ v), ⟨hu, hv, by rw [← key, hid]; exact hμ⟩, hid⟩

end Finsupp

namespace YoungDiagram

/-- **A partition vanishes beyond its number of cells**: if the row index `i` is at least the
number `|μ| = μ.card` of cells of `μ`, then row `i` of `μ` is empty. Rows being numbered from
`0` here, this is the familiar `μ_i = 0` for `i > |μ|` of the numbering from `1`. -/
@[hjo "lem_ght_partition_entry_vanish"]
theorem rowLen_eq_zero_of_card_le {μ : YoungDiagram} {i : ℕ} (hi : μ.card ≤ i) :
    μ.rowLen i = 0 := by
  by_contra h
  have hpos : 0 < μ.rowLen i := Nat.pos_of_ne_zero h
  have hsub : (Finset.range (i + 1)).image (fun k => (k, 0)) ⊆ μ.cells := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    exact YoungDiagram.mem_iff_lt_rowLen.mpr (lt_of_lt_of_le hpos (μ.rowLen_anti k i (by omega)))
  have hcard : i + 1 ≤ μ.card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ (fun a b hab => by simpa using hab),
      Finset.card_range] at this
  omega

end YoungDiagram
