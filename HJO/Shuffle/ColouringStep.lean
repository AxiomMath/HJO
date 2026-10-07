/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ColouringLevel
public import HJO.Shuffle.MellitRem41

/-! # Lowering the level past one event appends that event's operator

The four rules of Mellit's Theorem 4.2 all compare the partial sweep word at two levels that
bracket the rank of a single lattice point `P`, and all four make the same comparison before
evaluating the one new factor. That comparison is carried out once here: crossing `P` appends
`Φ_{P̂}(P)` on the left of the composite, which is to say it is the factor applied last.

## Main results

* `HJO.Mellit.sweptAbove_eq_insert_of_isolating` — the index set of the partial word grows by the
  single point `P`.
* `HJO.Mellit.partialSweepWord_eq_sweepOperator_mul` — lowering the level
  past one event appends its operator.

## Implementation notes

The comparison is usually stated for `P̂` above-diagonal and both levels admissible. Neither is
needed in this shape: `HJO.Paths.sweptRegion` already confines its members to the rectangle, so the
isolation hypothesis applies to them whatever `y` does, and only the upper level's admissibility is
used — to rule out a swept point of rank exactly `ηhi`, which the isolation hypothesis, being stated
with a strict inequality, does not cover. What *is* needed and is easily overlooked is `0 < a`: the
listing of a set of lattice points by rank is unambiguous only because the rank is injective on the
swept region, and `HJO.Mellit.pointRank_inj_of_mem_sweptRegion` is false at `a = 0`.

## References

This file concerns `HJO.Mellit.partialSweepWord_eq_sweepOperator_mul`,
`HJO.Mellit.partialSweepWord`, `HJO.Mellit.sweepOperator`, `HJO.Paths.sweptRegion`,
`HJO.Mellit.IsAdmissibleLevel`, `HJO.Paths.abovePointRank_injOn`.
-/

@[expose] public section

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-- The index set of the partial sweep word consists of swept points, hence of lattice points of
the rectangle. -/
theorem sweptAbove_subset (y : Heights a b N) (η : ℚ) : sweptAbove y η ⊆ sweptRegion y :=
  Finset.filter_subset _ _

/-- The rank listing of a one-point set is that point. -/
theorem sortByRank_singleton (a b N : ℕ) (P : ℕ × ℕ) :
    sortByRank a b N ({P} : Finset (ℕ × ℕ)) = [P] := by
  have h := sortByRank_perm a b N ({P} : Finset (ℕ × ℕ))
  rw [Finset.toList_singleton] at h
  exact h.eq_singleton

/-- **Lowering the level past a single event adds exactly that event's point.** Let `ηhi` be an
admissible level, let the rank of `P` lie strictly between `ηlo` and `ηhi`, and let `rk̂(P)` be the
only rank taken on the rectangle strictly between the two levels. Then the swept points outranking
`ηlo` are those outranking `ηhi` together with `P`.

A swept point `Q` of rank in the half-open window `(ηlo, ηhi]` cannot have rank exactly `ηhi`, that
level being admissible and the rank an integer; so its rank is `rk̂(P)` by the isolation hypothesis
and `Q = P` by the injectivity of the rank on the swept region. -/
theorem sweptAbove_eq_insert_of_isolating (ha : 0 < a) {y : Heights a b N} {P : ℕ × ℕ}
    {ηlo ηhi : ℚ} (hhi : IsAdmissibleLevel ηhi)
    (hlo : ηlo < ((pointRank a b N P : ℤ) : ℚ)) (hup : ((pointRank a b N P : ℤ) : ℚ) < ηhi)
    (hiso : ∀ Q : ℕ × ℕ, Q.1 ≤ a * N → Q.2 ≤ b * N →
      ηlo < ((pointRank a b N Q : ℤ) : ℚ) → ((pointRank a b N Q : ℤ) : ℚ) < ηhi →
      pointRank a b N Q = pointRank a b N P)
    (hPmem : P ∈ sweptRegion y) :
    sweptAbove y ηlo = {P} ∪ sweptAbove y ηhi := by
  ext Q
  simp only [sweptAbove, Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨hQ, hQη⟩
    rcases lt_or_ge ηhi ((pointRank a b N Q : ℤ) : ℚ) with h | h
    · exact Or.inr ⟨hQ, h⟩
    · refine Or.inl ?_
      have hQ1 := mem_sweptRegion.1 hQ
      have hQ2 : Q.2 ≤ b * N := hQ1.2.2.trans (ht_le_mul y _)
      have hne : ((pointRank a b N Q : ℤ) : ℚ) ≠ ηhi :=
        pointRank_ne_of_isAdmissibleLevel hhi a b N hQ1.1 hQ2
      exact pointRank_inj_of_mem_sweptRegion ha hQ hPmem
        (hiso Q hQ1.1 hQ2 hQη (lt_of_le_of_ne h hne))
  · rintro (rfl | ⟨hQ, hQη⟩)
    · exact ⟨hPmem, hlo⟩
    · exact ⟨hQ, hlo.trans (hup.trans hQη)⟩

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **Lowering the level by one event appends its operator.** This is
`HJO.Mellit.partialSweepWord_eq_sweepOperator_mul`: with `ηlo < rk̂(P) < ηhi` isolating the rank of
a swept point `P`, `W_{ηlo}(P̂) = Φ_{P̂}(P) ∘ W_{ηhi}(P̂)`.

`HJO.Mellit.sweptAbove_eq_insert_of_isolating` adds `P` to the index set, and `P` is outranked by
every point already there, so it stands first in the increasing rank listing — which is the
*leftmost* factor of `HJO.Mellit.partialSweepWord`'s product, hence the operator applied last, as
the `Φ_{P̂}(P) ∘ W_{ηhi}(P̂)` asks. -/
@[hjo "lem_colouring_partial_word_step"]
theorem partialSweepWord_eq_sweepOperator_mul (q u : L) (ha : 0 < a) {y : Heights a b N}
    {P : ℕ × ℕ} {ηlo ηhi : ℚ} (hhi : IsAdmissibleLevel ηhi)
    (hlo : ηlo < ((pointRank a b N P : ℤ) : ℚ)) (hup : ((pointRank a b N P : ℤ) : ℚ) < ηhi)
    (hiso : ∀ Q : ℕ × ℕ, Q.1 ≤ a * N → Q.2 ≤ b * N →
      ηlo < ((pointRank a b N Q : ℤ) : ℚ) → ((pointRank a b N Q : ℤ) : ℚ) < ηhi →
      pointRank a b N Q = pointRank a b N P)
    (hPmem : P ∈ sweptRegion y) :
    partialSweepWord q u y ηlo = sweepOperator q u y P * partialSweepWord q u y ηhi := by
  have hsplit := sweptAbove_eq_insert_of_isolating ha hhi hlo hup hiso hPmem
  have hPnot : P ∉ sweptAbove y ηhi := by
    simp only [sweptAbove, Finset.mem_filter, not_and]
    exact fun _ => not_lt.2 hup.le
  have hsub : ({P} : Finset (ℕ × ℕ)) ∪ sweptAbove y ηhi ⊆ sweptRegion y := by
    rw [← hsplit]
    exact sweptAbove_subset y ηlo
  have hltrank : ∀ R ∈ ({P} : Finset (ℕ × ℕ)), ∀ Q ∈ sweptAbove y ηhi,
      pointRank a b N R < pointRank a b N Q := by
    intro R hR Q hQ
    rw [Finset.mem_singleton] at hR
    subst hR
    have hQη : ηhi < ((pointRank a b N Q : ℤ) : ℚ) := (Finset.mem_filter.1 hQ).2
    exact_mod_cast hup.trans hQη
  rw [partialSweepWord, partialSweepWord, hsplit,
    sortByRank_union (y := y) ha hsub (Finset.disjoint_singleton_left.2 hPnot) hltrank,
    sortByRank_singleton, List.singleton_append, List.map_cons, List.prod_cons]

end HJO.Mellit
