/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.PartitionDiagram
public import HJO.Macdonald.PartitionLex
public meta import HJO.Attr

/-! # The lexicographic order, dominance, and the coarsening of a partition

Three results: the lexicographic order on the partitions of a fixed number is a strict
total order; dominance refines it; and merging the parts of a partition into blocks produces a
partition that dominates it.

## Main statements

* `HJO.Sym.isStrictTotalOrder_partitionLex`: `HJO.Sym.partitionLex_trichotomy`.
* `HJO.Sym.partitionLex_of_dominates`.
* `HJO.Sym.dominates_of_blockSums`.

## Implementation notes

The two orders are stated on different carriers — `HJO.Sym.partitionLex` on `YoungDiagram`, read off
`rowLen`, and `HJO.Sym.Dominates` on `Nat.Partition d`, read off `partialSum` — so
`HJO.Sym.partitionLex_of_dominates` needs the bridge `partialSum_eq_sum_rowLen`, which says that the
`i`-th partial sum of a partition is the number of cells in the first `i` rows of its diagram.

`HJO.Sym.partitionLex_trichotomy` is proved for arbitrary Young diagrams first: irreflexivity,
transitivity and trichotomy all hold without a common size, the size entering only through the
carrier of the statement. Trichotomy needs that a Young diagram is determined by its
row lengths, which is `YoungDiagram.eq_of_rowLen_eq`.

`HJO.Sym.dominates_of_blockSums` is stated with the blocks presented as the fibres of a labelling
`g : ℕ → ℕ` on the indices `0, …, m-1` of the parts of `λ`, rather than as a family of sets: fibres
are automatically pairwise disjoint with union the whole index range, so the condition
"nonempty pairwise disjoint sets with union `\{1, …, m\}`" costs one hypothesis (`hg`) instead of
three. Nonemptiness is not assumed and not needed: it is what makes the block sums positive, and
that is already carried by `q` being a partition.

Its engine is `HJO.Sym.sum_le_partialSum`: the sum of any `i` of the parts of a partition is at most
the sum of its `i` largest, which is the statement that lets a set of blocks be compared with a
prefix of `μ`. That step is often left implicit ("`μ₁ + ⋯ + μ_i` is the largest sum of `i` of
the numbers `s_1, …, s_r`").

## References

The file proves `HJO.Sym.partitionLex_trichotomy`, `HJO.Sym.partitionLex_of_dominates` and
`HJO.Sym.dominates_of_blockSums`.
-/

@[expose] public section

open Finset

namespace YoungDiagram

/-- **A Young diagram is determined by its row lengths.** A cell is one exactly when its column
index is below the length of its row, so two diagrams with the same rows have the same cells. -/
theorem eq_of_rowLen_eq {μ ν : YoungDiagram} (h : ∀ i, μ.rowLen i = ν.rowLen i) : μ = ν := by
  ext ⟨i, j⟩
  rw [mem_cells, mem_cells, mem_iff_lt_rowLen, mem_iff_lt_rowLen, h]

end YoungDiagram

namespace HJO.Sym

/-! ### The lexicographic order is a strict total order -/

/-- **The lexicographic order is transitive.** The witnessing row of the composite is the earlier of
the two witnessing rows: below it all three diagrams agree, and at it the outer two already
differ. -/
theorem partitionLex_trans {μ ν ρ : YoungDiagram} (h₁ : partitionLex μ ν)
    (h₂ : partitionLex ν ρ) : partitionLex μ ρ := by
  obtain ⟨i, hi1, hi2⟩ := h₁
  obtain ⟨j, hj1, hj2⟩ := h₂
  rcases lt_or_ge j i with hji | hij
  · exact ⟨j, fun k hk => (hi1 k (hk.trans hji)).trans (hj1 k hk), by rw [hi1 j hji]; exact hj2⟩
  · refine ⟨i, fun k hk => (hi1 k hk).trans (hj1 k (hk.trans_le hij)), ?_⟩
    rcases eq_or_lt_of_le hij with rfl | hij'
    · exact hi2.trans hj2
    · rw [← hj1 i hij']; exact hi2

/-- **The lexicographic order is asymmetric**, which is transitivity against irreflexivity. -/
theorem partitionLex_asymm {μ ν : YoungDiagram} (h : partitionLex μ ν) : ¬partitionLex ν μ :=
  fun h' => not_partitionLex_self μ (partitionLex_trans h h')

/-- **Any two Young diagrams are lexicographically comparable.** If they are not equal their rows
differ somewhere; at the least such row one of the two is the longer, and that row witnesses the
comparison. -/
@[hjo "lem_sf_lex_total"]
theorem partitionLex_trichotomy (μ ν : YoungDiagram) :
    partitionLex μ ν ∨ μ = ν ∨ partitionLex ν μ := by
  by_cases h : ∀ i, μ.rowLen i = ν.rowLen i
  · exact Or.inr (Or.inl (YoungDiagram.eq_of_rowLen_eq h))
  · classical
    simp only [not_forall] at h
    have hlt : ∀ k < Nat.find h, μ.rowLen k = ν.rowLen k := fun k hk =>
      not_not.1 (Nat.find_min h hk)
    rcases lt_or_gt_of_ne (Nat.find_spec h) with hne | hne
    · exact Or.inl ⟨Nat.find h, hlt, hne⟩
    · exact Or.inr (Or.inr ⟨Nat.find h, fun k hk => (hlt k hk).symm, hne⟩)

/-- **`HJO.Sym.partitionLex_trichotomy`: the lexicographic order on the partitions of `d` is a
strict total order.** Irreflexivity, transitivity and trichotomy hold for arbitrary Young diagrams;
fixing the
number of cells only chooses the carrier of the statement. -/
@[hjo "lem_sf_lex_total"]
theorem isStrictTotalOrder_partitionLex (d : ℕ) :
    IsStrictTotalOrder {μ : YoungDiagram // μ.card = d} fun μ ν => partitionLex μ.1 ν.1 where
  irrefl a := not_partitionLex_self a.1
  trans _ _ _ := partitionLex_trans
  trichotomous a b hab hba := by
    rcases partitionLex_trichotomy a.1 b.1 with h | h | h
    · exact absurd h hab
    · exact Subtype.ext h
    · exact absurd h hba

/-! ### Dominance refines the lexicographic order -/

/-- The `i`-th partial sum of a partition counts the cells in the first `i` rows of its diagram:
the bridge between `Dominates`, stated on `Nat.Partition`, and `partitionLex`, stated on
`YoungDiagram`. -/
theorem partialSum_eq_sum_rowLen {d : ℕ} (p : Nat.Partition d) (i : ℕ) :
    partialSum p i = ∑ j ∈ range i, (partitionDiagram p).rowLen j := by
  rw [partialSum, List.sum_take_eq_sum_range_getD]
  exact sum_congr rfl fun j _ => (rowLen_partitionDiagram p j).symm

/-- The diagram of a partition determines the partition: its rows are the parts. -/
theorem partitionDiagram_injective {d : ℕ} : Function.Injective (partitionDiagram (d := d)) := by
  intro p q h
  have hrow : ∀ i, (partitionDiagram p).rowLen i = (partitionDiagram q).rowLen i := fun i => by
    rw [h]
  refine Nat.Partition.ext ?_
  rw [← Multiset.sort_eq p.parts (· ≥ ·), ← Multiset.sort_eq q.parts (· ≥ ·)]
  refine congrArg _ (List.ext_getElem ?_ fun n h₁ h₂ => ?_)
  · have hp : ∀ r : Nat.Partition d,
        (r.parts.sort (· ≥ ·)).length = (partitionDiagram r).colLen 0 := fun r => by
      rw [← YoungDiagram.length_rowLens, partitionDiagram,
        YoungDiagram.rowLens_ofRowLens_eq_self fun _ hx => pos_of_mem_sort r hx]
    rw [hp p, hp q, h]
  · rw [← List.getD_eq_getElem _ 0 h₁, ← List.getD_eq_getElem _ 0 h₂,
      ← rowLen_partitionDiagram, ← rowLen_partitionDiagram, hrow]

/-- **Dominance refines the lexicographic order.** At the least row where
two distinct partitions of the same number differ, the dominating one is the longer: the partial
sums agree strictly below that row, and dominance at the row itself then forces the inequality
between the two rows. -/
@[hjo "lem_sf_dominance_lex"]
theorem partitionLex_of_dominates {d : ℕ} {p q : Nat.Partition d} (h : Dominates p q)
    (hne : q ≠ p) : partitionLex (partitionDiagram q) (partitionDiagram p) := by
  rcases partitionLex_trichotomy (partitionDiagram q) (partitionDiagram p) with hlex | heq | hlex
  · exact hlex
  · exact absurd (partitionDiagram_injective heq) hne
  · obtain ⟨i, hi1, hi2⟩ := hlex
    have hsum := h (i + 1)
    have hpre : ∑ k ∈ range i, (partitionDiagram p).rowLen k
        = ∑ k ∈ range i, (partitionDiagram q).rowLen k :=
      sum_congr rfl fun k hk => hi1 k (mem_range.1 hk)
    rw [partialSum_eq_sum_rowLen, partialSum_eq_sum_rowLen, sum_range_succ, sum_range_succ,
      hpre] at hsum
    omega

/-! ### A coarsening dominates -/

/-- **The sum of any `i` of the entries of a nonincreasing list is at most the sum of its first
`i`.** The induction peels the head: a sub-multiset either contains it, and then the remaining
`i - 1` entries are compared with the tail, or it does not, and then its `i` entries are compared
with the first `i` of the tail, each of which is at most the head. -/
theorem sum_le_sum_take_of_pairwise {L : List ℕ} (hL : L.Pairwise (· ≥ ·)) :
    ∀ {A : Multiset ℕ}, A ≤ (L : Multiset ℕ) → ∀ {i : ℕ}, Multiset.card A ≤ i →
      A.sum ≤ (L.take i).sum := by
  induction L with
  | nil =>
    intro A hA i _
    have hA0 : A = 0 := Multiset.le_zero.1 (by simpa using hA)
    rw [hA0]
    simp
  | cons x L ih =>
    intro A hA i hcard
    rw [List.pairwise_cons] at hL
    match i with
    | 0 => rw [Multiset.card_eq_zero.1 (Nat.le_zero.1 hcard)]; simp
    | i + 1 =>
      rw [List.take_succ_cons, List.sum_cons]
      by_cases hx : x ∈ A
      · have hAe : A.erase x ≤ (L : Multiset ℕ) := by
          simpa using Multiset.erase_le_erase x hA
        have hce : Multiset.card (A.erase x) ≤ i := by
          rw [Multiset.card_erase_of_mem hx, Nat.pred_eq_sub_one]
          omega
        calc A.sum = x + (A.erase x).sum := by
              conv_lhs => rw [← Multiset.cons_erase hx]
              rw [Multiset.sum_cons]
          _ ≤ x + (L.take i).sum := Nat.add_le_add_left (ih hL.2 hAe hce) x
      · have hAL : A ≤ (L : Multiset ℕ) := (Multiset.le_cons_of_notMem hx).1 hA
        refine le_trans (ih hL.2 hAL hcard) ?_
        by_cases hi : i < L.length
        · rw [List.sum_take_succ _ _ hi]
          have := hL.1 L[i] (List.getElem_mem hi)
          omega
        · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
          omega

/-- **The sum of any `i` of the parts of a partition is at most its `i`-th partial sum**, the
partial sum being the sum of the `i` largest parts. -/
theorem sum_le_partialSum {d : ℕ} (p : Nat.Partition d) {A : Multiset ℕ} (hA : A ≤ p.parts)
    {i : ℕ} (hcard : Multiset.card A ≤ i) : A.sum ≤ partialSum p i :=
  sum_le_sum_take_of_pairwise (Multiset.pairwise_sort _ _)
    (by rwa [Multiset.sort_eq]) hcard

/-- **A coarsening dominates.** The parts of `λ`, indexed by
`0, …, m-1`, are merged along the fibres of a labelling `g` into `r` blocks; the multiset of block
sums is the partition `μ`. Then `μ ⪰ λ`.

Fix `i`. The first `i` parts of `λ` all lie in blocks labelled by `g` on `\{0, …, min(i,m)-1\}`, a
set of at most `i` labels, so their sum is at most the sum of those blocks; and the sum of at most
`i` blocks is at most the sum of the `i` largest, which is the `i`-th partial sum of `μ`. -/
@[hjo "lem_sf_coarsening_dominance"]
theorem dominates_of_blockSums {d m r : ℕ} (p q : Nat.Partition d)
    (hm : Multiset.card p.parts = m) (g : ℕ → ℕ) (hg : ∀ j < m, g j < r)
    (hq : q.parts = (Multiset.range r).map fun t =>
      ∑ j ∈ (range m).filter fun j => g j = t, (p.parts.sort (· ≥ ·)).getD j 0) :
    Dominates q p := by
  classical
  set L := p.parts.sort (· ≥ ·) with hL
  set f : ℕ → ℕ := fun j => L.getD j 0 with hf
  set s : ℕ → ℕ := fun t => ∑ j ∈ (range m).filter fun j => g j = t, f j with hs
  have hlen : L.length = m := by rw [hL, Multiset.length_sort, hm]
  intro i
  set T : Finset ℕ := (range (min i m)).image g with hT
  -- The first `i` parts of `λ` are the parts indexed below `min (i, m)`.
  have h1 : partialSum p i = ∑ j ∈ range (min i m), f j := by
    rw [partialSum, List.sum_take_eq_sum_range_getD]
    have hsub : range (min i m) ⊆ range i := Finset.range_subset_range.2 (min_le_left i m)
    refine (sum_subset hsub fun j hj hj' => ?_).symm
    rw [mem_range] at hj
    rw [mem_range, not_lt] at hj'
    exact List.getD_eq_default _ 0 (by rw [hlen]; omega)
  -- Those parts lie in the blocks labelled by `T`, and the blocks are disjoint.
  have hdisj : (T : Set ℕ).PairwiseDisjoint fun t => (range m).filter fun j => g j = t := by
    intro a _ b _ hab
    refine Finset.disjoint_left.2 fun j hja hjb => hab ?_
    rw [mem_filter] at hja hjb
    rw [← hja.2, hjb.2]
  have h2 : ∑ j ∈ range (min i m), f j ≤ ∑ t ∈ T, s t := by
    rw [hs, ← sum_biUnion hdisj]
    refine sum_le_sum_of_subset fun j hj => ?_
    rw [mem_range] at hj
    exact mem_biUnion.2 ⟨g j, mem_image_of_mem g (mem_range.2 hj),
      mem_filter.2 ⟨mem_range.2 (by omega), rfl⟩⟩
  -- At most `i` blocks, so their sum is at most the `i`-th partial sum of `μ`.
  have hTr : T ⊆ range r := fun t ht => by
    obtain ⟨j, hj, rfl⟩ := mem_image.1 ht
    rw [mem_range] at hj ⊢
    exact hg j (by omega)
  have h3 : ∑ t ∈ T, s t ≤ partialSum q i := by
    refine sum_le_partialSum q (A := T.val.map s) ?_ ?_
    · rw [hq]
      exact Multiset.map_le_map (Finset.val_le_iff_val_subset.2 hTr)
    · have hcard : Multiset.card (T.val.map s) = #T := Multiset.card_map _ _
      rw [hcard, hT]
      exact le_trans card_image_le (by rw [card_range]; exact min_le_left _ _)
  rw [h1]
  exact le_trans h2 h3

end HJO.Sym
