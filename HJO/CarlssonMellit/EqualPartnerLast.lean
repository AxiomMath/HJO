/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.WordStatistics
public import HJO.DyckAttackSets
public meta import HJO.Attr

/-! # A transitive attack set with an equal attacking pair has a last single partner

The Carlsson--Mellit `χ` combinatorics splits a labelling along a position whose equal-partner
count `d_i(R, u)` is exactly one, and the existence of such a position is what makes that split
available whenever some attacking pair carries equal letters. This file proves it: the largest
position with a partner of its own letter has exactly one, because a second partner would hand a
strictly larger position a partner of its own.

## Main results

* `HJO.Sym.exists_equalPartners_eq_one`: for a transitive attack set `R` on `{1, …, n}` and a word
  `u`, if `u i = u j` for some `(i, j) ∈ R` then some position `i^* < n` has `d_{i^*}(R, u) = 1`.

## Implementation notes

Positions are indexed from `0`, as for the paths of `HJO.Dyck.IsSquareDyck` and the pairs of
`HJO.Dyck.IsTransitiveAttackSet`, so the paper's range `1 ≤ i^* ≤ n` reads `i^* < n`; the bound is
returned rather than assumed, coming from `HJO.Dyck.IsTransitiveAttackSet.snd_lt` on the pair the
maximal position carries.

The statement is more general than the in two idle respects, both of them the shape of
`HJO.Sym.equalPartners` rather than a choice made here. The letters are drawn from any type with
decidable equality instead of `ℤ_{>0}`: only equalities `u_a = u_b` are read, so neither the order
nor the positivity of the letters is spent. And the word is a total function `ℕ → α` instead of an
`n`-tuple, as `equalPartners` counts pairs of `R` and every such pair lies in the window `< n`, so
the letters outside the window are never read.

Both halves of `(*)` are available, but only `HJO.Dyck.IsTransitiveAttackSet.mem_upper` is used: the
proof splits the pair `(i^*, j_2)` at `j_1` and keeps the upper half `(j_1, j_2)`, the lower half
`(i^*, j_1)` being one of the two partners already in hand.

## References

The lemma `HJO.Sym.exists_equalPartners_eq_one` and definitions `HJO.Sym.equalPartners`,
`HJO.Dyck.IsTransitiveAttackSet`; E. Carlsson and A. Mellit,
*A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 5.
-/

@[expose] public section

open Finset HJO.Dyck

namespace HJO.Sym

variable {α : Type*} [DecidableEq α] {n : ℕ} {R : Finset (ℕ × ℕ)} {u : ℕ → α}

/-- Two partners of one position, both carrying its letter, hand the lower of them a partner of its
own letter at a strictly larger position: from `(i, a)` and `(i, b)` in `R` with `a < b` and
`u_a = u_b = u_i`, transitivity splits `(i, b)` at `a` and gives `(a, b) ∈ R`, so `d_a(R, u) ≥ 1`
while `a > i`. This is the step of `HJO.Sym.exists_equalPartners_eq_one` that contradicts
maximality, stated once and applied to the two orderings of the two partners. -/
private theorem exists_gt_equalPartners_pos (hR : IsTransitiveAttackSet n R) {i a b : ℕ}
    (ha : (i, a) ∈ R) (hb : (i, b) ∈ R) (hab : a < b) (hua : u a = u i) (hub : u b = u i) :
    ∃ l, i < l ∧ l < n ∧ 0 < equalPartners R u l := by
  have hia : i < a := hR.fst_lt_snd (i, a) ha
  refine ⟨a, hia, hR.snd_lt (i, a) ha, card_pos.2 ⟨(a, b), ?_⟩⟩
  exact mem_filter.2 ⟨hR.mem_upper hia hab hb, rfl, hub.trans hua.symm⟩

/-- **A transitive attack set has a last single partner.** Let `R` be a
transitive attack set on `{1, …, n}` and `u` a word. If some attacking pair `(i, j) ∈ R` carries
equal letters, `u_i = u_j`, then some position `i^* < n` has exactly one attack partner of its own
letter, `d_{i^*}(R, u) = 1`.

Take `i^*` largest among the positions below `n` with at least one such partner; the hypothesis puts
`i` there, so the set is nonempty, and it is finite. A second partner would give `j_1 < j_2` with
`(i^*, j_1)` and `(i^*, j_2)` in `R` and `u_{j_1} = u_{j_2} = u_{i^*}`; splitting `(i^*, j_2)` at
`j_1` puts `(j_1, j_2)` in `R`, so `j_1` itself has a partner of its own letter at the strictly
larger position `j_1 > i^*`, against maximality. -/
@[hjo "lem_cm_equal_partners_one"]
theorem exists_equalPartners_eq_one (hR : IsTransitiveAttackSet n R) {i j : ℕ} (hij : (i, j) ∈ R)
    (hu : u i = u j) : ∃ i' < n, equalPartners R u i' = 1 := by
  obtain ⟨i', hi'n, hpos, hmax⟩ : ∃ i' < n, 0 < equalPartners R u i' ∧
      ∀ l < n, 0 < equalPartners R u l → l ≤ i' := by
    have hne : ({l ∈ range n | 0 < equalPartners R u l} : Finset ℕ).Nonempty := by
      refine ⟨i, mem_filter.2 ⟨mem_range.2 (hR.fst_lt hij), card_pos.2 ⟨(i, j), ?_⟩⟩⟩
      exact mem_filter.2 ⟨hij, rfl, hu.symm⟩
    obtain ⟨hmem, hmem'⟩ := mem_filter.1 (max'_mem _ hne)
    exact ⟨_, mem_range.1 hmem, hmem', fun l hl hl' =>
      le_max' _ l (mem_filter.2 ⟨mem_range.2 hl, hl'⟩)⟩
  refine ⟨i', hi'n, ?_⟩
  by_contra hone
  have hone' : #{p ∈ R | p.1 = i' ∧ u p.2 = u i'} ≠ 1 := hone
  have hpos' : 0 < #{p ∈ R | p.1 = i' ∧ u p.2 = u i'} := hpos
  have h2 : 1 < #{p ∈ R | p.1 = i' ∧ u p.2 = u i'} := by omega
  obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.1 h2
  obtain ⟨i₁, a⟩ := p
  obtain ⟨i₂, b⟩ := q
  simp only [mem_filter] at hp hq
  obtain ⟨haR, hi₁, hua⟩ := hp
  obtain ⟨hbR, hi₂, hub⟩ := hq
  subst hi₁
  subst hi₂
  have hab : a ≠ b := fun h => hpq (by rw [h])
  rcases hab.lt_or_gt with h | h
  · obtain ⟨l, hl, hln, hlpos⟩ := exists_gt_equalPartners_pos hR haR hbR h hua hub
    have := hmax l hln hlpos
    omega
  · obtain ⟨l, hl, hln, hlpos⟩ := exists_gt_equalPartners_pos hR hbR haR h hub hua
    have := hmax l hln hlpos
    omega

end HJO.Sym
