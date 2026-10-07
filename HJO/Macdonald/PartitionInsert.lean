/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Combinatorics.Young.YoungDiagram
public import HJO.Classical.PartitionDiagram
public meta import HJO.Attr

/-! # Inserting a part into a partition, and the shift by one

Two pieces of the partition vocabulary: `c ∪ ν`, the partition obtained from `ν` by adding one
further part equal to `c`; and the bijection between weakly decreasing tuples of naturals and
partitions given by adding one to every entry.

## Main definitions

* `HJO.Sym.insertPart`, the partition `c ∪ ν`.
* `HJO.Sym.shiftPartitionEquiv`, the shift by one.

## Main statements

* `HJO.Sym.rowLens_insertPart`: the rows of `c ∪ ν` are those of `ν` with `c` inserted in place,
  which is the phrase "arranged in nonincreasing order" of the definition.
* `HJO.Sym.rowLens_insertPart_toMultiset`: the multiset bridge, `c ∪ ν` has the parts of `ν`
  together with one further part `c`. This is the form `HJO.Sym.elemSymmMonomial` reads, since
  `elemSymmMonomial_cons` is stated for `a ::ₘ μ`.
* `HJO.Sym.rowLen_insertPart_zero`, `HJO.Sym.rowLen_insertPart_succ`: the two clauses
  `HJO.Sym.partitionLex_insertPart` spends, that for `c ≥ ν_1` the partition `c ∪ ν` is
  `(c, ν_1, ν_2, …)`.
* `HJO.Sym.le_rowLen_insertPart_zero`: the clause
  `HJO.Sym.foldr_bop_sub_smul_elemSymmMonomial_mem_span` spends, that the first part of `c ∪ ν` is
  at least `c` with no hypothesis relating `c` to `ν`.
* `HJO.Sym.card_insertPart`: `|c ∪ ν| = |ν| + c`, which is what makes `c ∪ μ` and `c ∪ λ'`
  partitions of one and the same integer in `HJO.Sym.partitionLex_insertPart`.
* `HJO.Sym.shiftPartitionEquiv_rowLens`: the forward map read off, without which the `Equiv` would
  identify nothing.

## Implementation notes

A partition is a `YoungDiagram`, its parts being `YoungDiagram.rowLens`. This is the representation
`HJO.Sym.partitionLex` compares in, so the consumers `HJO.Sym.partitionLex_insertPart` and
`HJO.Sym.foldr_bop_sub_smul_elemSymmMonomial_mem_span` need no translation;
`rowLens_insertPart_toMultiset` is the bridge to the `Multiset ℕ` reading that
`HJO.Sym.elemSymmMonomial` indexes by. No third representation of a partition is introduced.

The hypothesis `c \ge 1` is essential and is carried as `0 < c` on every statement about the rows:
`YoungDiagram.ofRowLens` ignores a zero entry, so for `c = 0` the list handed to it is not the list
of rows of the result. Sortedness of the inserted list is `List.Pairwise.orderedInsert`, for which
`(· ≥ ·)` on `ℕ` is total, transitive and decidable.

Rows are `0`-based, so `ν_1` is `nu.rowLen 0` and `ν_i` is `nu.rowLen (i - 1)`;
the pair of clauses `HJO.Sym.partitionLex_insertPart` spends therefore reads "row `0` of `c ∪ ν` is
`c`, and row `i + 1` of `c ∪ ν` is row `i` of `ν`".

For the shift bijection the domain carries NO positivity and the codomain does, and this is the
content of the statement rather than an accident: the tuples satisfy `a_m ≥ 0`, which is
vacuous for natural numbers, so the domain is exactly the weakly decreasing lists of naturals, while
its image consists of the weakly decreasing lists of POSITIVE naturals, which is what a
`YoungDiagram` is (`YoungDiagram.equivListRowLens`). The inverse subtracts one in `ℕ`, where
subtraction is truncated; the round trip is nevertheless the identity because every entry of
`YoungDiagram.rowLens` is positive, so no truncation occurs.

## References

The definitions `HJO.Sym.insertPart` and `HJO.Sym.shiftPartitionEquiv`, and the clauses spent by
`HJO.Sym.partitionLex_insertPart` and `HJO.Sym.foldr_bop_sub_smul_elemSymmMonomial_mem_span`.
-/

@[expose] public section

namespace YoungDiagram

/-- **`ofRowLens` depends only on the list of row lengths.** The sortedness argument is a proof of a
proposition, so two calls on the same list agree; this is the congruence needed to rewrite the list
under `ofRowLens`, which no `rw` can do on its own because the second argument mentions it. -/
theorem ofRowLens_congr {w w' : List ℕ} {hw : w.SortedGE} {hw' : w'.SortedGE} (h : w = w') :
    ofRowLens w hw = ofRowLens w' hw' := by
  subst h
  rfl

/-- **A row length is the corresponding entry of the list of row lengths**, read with `0` beyond its
end: `YoungDiagram.get_rowLens` inside the list, and a row past the last nonempty one is empty. -/
theorem rowLen_eq_getD (μ : YoungDiagram) (i : ℕ) : μ.rowLen i = μ.rowLens.getD i 0 := by
  by_cases hi : i < μ.rowLens.length
  · rw [List.getD_eq_getElem _ 0 hi, get_rowLens]
  · rw [List.getD_eq_default _ 0 (by omega)]
    exact rowLen_eq_zero_of_colLen_le (by rw [← length_rowLens]; omega)

/-- **The number of cells is the sum of the list of row lengths.** The unindexed form of
`YoungDiagram.card_eq_sum_rowLen`, taken over the whole list, which is the form in which a
permutation of the rows can be used. -/
theorem card_eq_sum_rowLens (μ : YoungDiagram) : μ.card = μ.rowLens.sum := by
  have h : μ.rowLens.sum = ∑ i ∈ Finset.range μ.rowLens.length, μ.rowLens.getD i 0 := by
    rw [← List.sum_take_eq_sum_range_getD, List.take_of_length_le le_rfl]
  rw [h, μ.card_eq_sum_rowLen (N := μ.rowLens.length) (by rw [length_rowLens])]
  exact Finset.sum_congr rfl fun i _ => μ.rowLen_eq_getD i

end YoungDiagram

namespace HJO.Sym

/-! ### Inserting a part -/

/-- **The partition `c ∪ ν`.** The parts of `ν` together with one further
part equal to `c`, arranged in nonincreasing order: `c` is inserted into the weakly decreasing list
`nu.rowLens` at the place that keeps it weakly decreasing.

The insertion is `List.orderedInsert` for `(· ≥ ·)`, whose output is sorted because the input is
(`List.Pairwise.orderedInsert`, using that `(· ≥ ·)` on `ℕ` is total and transitive). For `c = 0`
the result is `ν` itself rather than a diagram with an extra empty row, which is why
`c ≥ 1` appears as a hypothesis on every statement below and not on the definition. -/
@[hjo "def_cm_partition_insert"]
def insertPart (c : ℕ) (nu : YoungDiagram) : YoungDiagram :=
  YoungDiagram.ofRowLens (nu.rowLens.orderedInsert (· ≥ ·) c)
    (nu.rowLens_sorted.pairwise.orderedInsert c _).sortedGE

/-- **The rows of `c ∪ ν` are the rows of `ν` with `c` inserted in place**,
"arranged in nonincreasing order". `YoungDiagram.ofRowLens` returns the list it was given as its
list of rows exactly when every entry is positive, which here is `c ≥ 1` together with the
positivity of the rows of `ν`. -/
@[hjo "def_cm_partition_insert"]
theorem rowLens_insertPart {c : ℕ} (hc : 0 < c) (nu : YoungDiagram) :
    (insertPart c nu).rowLens = nu.rowLens.orderedInsert (· ≥ ·) c := by
  refine YoungDiagram.rowLens_ofRowLens_eq_self fun x hx => ?_
  rcases (List.mem_orderedInsert _).1 hx with rfl | hx
  · exact hc
  · exact nu.pos_of_mem_rowLens x hx

/-- **The parts of `c ∪ ν` are those of `ν` together with one further part equal to `c`**, as
multisets: the description of the parts, with the ordering forgotten.

This is the bridge to the `Multiset ℕ` reading of a partition that `HJO.Sym.elemSymmMonomial`
indexes by, and it is what makes `e_{c ∪ ν} = e_c · e_ν` available from
`elemSymmMonomial_cons`: inserting into a list is a permutation of consing onto it
(`List.perm_orderedInsert`), and permuted lists are equal as multisets. -/
@[hjo "def_cm_partition_insert"]
theorem rowLens_insertPart_toMultiset {c : ℕ} (hc : 0 < c) (nu : YoungDiagram) :
    ((insertPart c nu).rowLens : Multiset ℕ) = c ::ₘ (nu.rowLens : Multiset ℕ) := by
  rw [rowLens_insertPart hc]
  exact Multiset.coe_eq_coe.2 (List.perm_orderedInsert _ c _)

/-- **For `c ≥ ν_1` the parts of `c ∪ ν` are `(c, ν_1, ν_2, …)`.** The insertion stops at the very
first entry, since `c` is at least the largest row of `ν`. -/
theorem rowLens_insertPart_of_rowLen_zero_le {c : ℕ} (hc : 0 < c) {nu : YoungDiagram}
    (h : nu.rowLen 0 ≤ c) : (insertPart c nu).rowLens = c :: nu.rowLens := by
  rw [rowLens_insertPart hc]
  cases hl : nu.rowLens with
  | nil => simp
  | cons b l =>
    refine List.orderedInsert_cons_of_le _ _ ?_
    have hb : b = nu.rowLen 0 := by
      have h0 := nu.rowLen_eq_getD 0
      rw [hl] at h0
      simpa using h0.symm
    exact hb ▸ h

/-- **For `c ≥ ν_1` the first part of `c ∪ ν` is `c`**, one of the two clauses
`HJO.Sym.partitionLex_insertPart` spends on `HJO.Sym.insertPart`. Rows are `0`-based, so
`ν_1` is `nu.rowLen 0`. -/
@[hjo "def_cm_partition_insert"]
theorem rowLen_insertPart_zero {c : ℕ} (hc : 0 < c) {nu : YoungDiagram} (h : nu.rowLen 0 ≤ c) :
    (insertPart c nu).rowLen 0 = c := by
  rw [YoungDiagram.rowLen_eq_getD, rowLens_insertPart_of_rowLen_zero_le hc h]
  rfl

/-- **For `c ≥ ν_1` the later parts of `c ∪ ν` are the parts of `ν`, shifted by one place**, the
other clause `HJO.Sym.partitionLex_insertPart` spends: the two sequences `c ∪ μ` and `c ∪ λ'` agree
in position `1` and carry `μ_i` and `λ'_i` in position `i + 1`. -/
@[hjo "def_cm_partition_insert"]
theorem rowLen_insertPart_succ {c : ℕ} (hc : 0 < c) {nu : YoungDiagram} (h : nu.rowLen 0 ≤ c)
    (i : ℕ) : (insertPart c nu).rowLen (i + 1) = nu.rowLen i := by
  rw [YoungDiagram.rowLen_eq_getD, rowLens_insertPart_of_rowLen_zero_le hc h,
    YoungDiagram.rowLen_eq_getD]
  rfl

/-- **The first part of `c ∪ ν` is at least `c`**, with no hypothesis relating `c` to the rows of
`ν`. This is the clause `HJO.Sym.foldr_bop_sub_smul_elemSymmMonomial_mem_span` spends when it
concludes that the first part of `s ∪ ρ` is at least `s`: the part `c` sits at some row of `c ∪ ν`,
and row `0` is the longest. -/
@[hjo "def_cm_partition_insert"]
theorem le_rowLen_insertPart_zero {c : ℕ} (hc : 0 < c) (nu : YoungDiagram) :
    c ≤ (insertPart c nu).rowLen 0 := by
  have hmem : c ∈ (insertPart c nu).rowLens := by
    rw [rowLens_insertPart hc]
    exact (List.mem_orderedInsert _).2 (Or.inl rfl)
  obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.1 hmem
  have hce : (insertPart c nu).rowLen i = c := (YoungDiagram.get_rowLens (h := hi)).symm.trans hci
  exact hce.symm.trans_le ((insertPart c nu).rowLen_anti 0 i (Nat.zero_le i))

/-- **`|c ∪ ν| = |ν| + c`**: adding a part of size `c` adds `c` cells, so `c ∪ μ` and `c ∪ λ'` are
partitions of one and the same integer whenever `μ` and `λ'` are, which is what
`HJO.Sym.partitionLex_insertPart` needs before it may compare them.

The number of cells is the sum of the rows, and inserting `c` into the list of rows permutes
`c :: nu.rowLens`, whose sum is `c` more. -/
@[hjo "def_cm_partition_insert"]
theorem card_insertPart {c : ℕ} (hc : 0 < c) (nu : YoungDiagram) :
    (insertPart c nu).card = nu.card + c := by
  rw [YoungDiagram.card_eq_sum_rowLens, YoungDiagram.card_eq_sum_rowLens, rowLens_insertPart hc,
    (List.perm_orderedInsert (· ≥ ·) c nu.rowLens).sum_eq, List.sum_cons]
  omega

/-! ### The shift by one -/

/-- Adding one to every entry preserves weak decrease. -/
theorem sortedGE_map_add_one {l : List ℕ} (hl : l.SortedGE) : (l.map (· + 1)).SortedGE :=
  (hl.pairwise.map (S := (· ≥ ·)) _ fun _ _ h => Nat.succ_le_succ h).sortedGE

/-- Subtracting one from every entry preserves weak decrease. Truncated subtraction is monotone, so
no positivity is needed here. -/
theorem sortedGE_map_sub_one {l : List ℕ} (hl : l.SortedGE) : (l.map (· - 1)).SortedGE :=
  (hl.pairwise.map (S := (· ≥ ·)) (· - 1) fun _ _ h => Nat.sub_le_sub_right h 1).sortedGE

/-- Every entry of a list of successors is positive:
`a_1 + 1 ≥ … ≥ a_m + 1 ≥ 1`. -/
theorem pos_of_mem_map_add_one {l : List ℕ} {x : ℕ} (hx : x ∈ l.map (· + 1)) : 0 < x := by
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
  omega

/-- **Adding one to every entry is a bijection from the weakly
decreasing tuples of naturals onto the partitions.** The tuples
`a_1 ≥ … ≥ a_m ≥ 0`, over all `m ≥ 0`, are the weakly decreasing lists of naturals, the condition
`a_m ≥ 0` being vacuous there; the partitions are the weakly decreasing lists of POSITIVE naturals,
which is what a `YoungDiagram` is by `YoungDiagram.equivListRowLens`. So the domain of this `Equiv`
carries no positivity and its codomain does, and that asymmetry is the whole content of the
statement.

The inverse subtracts one in `ℕ`, where subtraction is truncated; the round trip is still the
identity because every row of a `YoungDiagram` is positive, so nothing is truncated. -/
@[hjo "lem_cm_partition_shift_bijection"]
def shiftPartitionEquiv : {l : List ℕ // l.SortedGE} ≃ YoungDiagram where
  toFun l := YoungDiagram.ofRowLens (l.1.map (· + 1)) (sortedGE_map_add_one l.2)
  invFun mu := ⟨mu.rowLens.map (· - 1), sortedGE_map_sub_one mu.rowLens_sorted⟩
  left_inv l := by
    refine Subtype.ext ?_
    change (YoungDiagram.ofRowLens (l.1.map (· + 1))
      (sortedGE_map_add_one l.2)).rowLens.map (· - 1) = l.1
    rw [YoungDiagram.rowLens_ofRowLens_eq_self fun _ hx => pos_of_mem_map_add_one hx, List.map_map]
    simp [Function.comp_def]
  right_inv mu := by
    refine (YoungDiagram.ofRowLens_congr (w' := mu.rowLens) ?_).trans
      YoungDiagram.ofRowLens_to_rowLens_eq_self
    rw [List.map_map]
    refine (List.map_congr_left ?_).trans (List.map_id' _)
    intro x hx
    have hpos := mu.pos_of_mem_rowLens x hx
    simp only [Function.comp_apply]
    omega

/-- **The forward map of `shiftPartitionEquiv` adds one to every entry**: the parts of the image
partition are the entries of the tuple, each raised by one. Without this the `Equiv` would identify
nothing. -/
@[hjo "lem_cm_partition_shift_bijection"]
theorem shiftPartitionEquiv_rowLens (l : List ℕ) (hl : l.SortedGE) :
    (shiftPartitionEquiv ⟨l, hl⟩).rowLens = l.map (· + 1) :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := sortedGE_map_add_one hl)
    fun _ hx => pos_of_mem_map_add_one hx

/-- **The inverse map of `shiftPartitionEquiv` subtracts one from every part**,
`(λ_1 - 1, …, λ_m - 1)` witnessing surjectivity. -/
theorem shiftPartitionEquiv_symm_apply (mu : YoungDiagram) :
    (shiftPartitionEquiv.symm mu).1 = mu.rowLens.map (· - 1) := rfl

end HJO.Sym
