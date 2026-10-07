/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Young.SemistandardTableau
public import HJO.Macdonald.Vocabulary
public import HJO.Determinant.CycleWeight
public meta import HJO.Attr

/-! # Compositions, partitions, Young diagrams, tableaux and conjugation

This file records that the Mathlib objects this library computes with are the usual textbook
objects, and proves the elementary facts about them that are usually stated separately.

* A *composition* of `N` is a finite sequence of positive integers summing to `N`; Mathlib's
  `Composition N` is exactly such a list, and its `Composition.reverse` reverses the list.
* A *partition* of `d`, read as a weakly decreasing finite sequence of positive integers summing
  to `d`, is Mathlib's `Nat.Partition d`, a multiset of positive integers summing to `d`: a
  multiset has exactly one weakly decreasing listing.
* A *Young diagram* is a finite set of pairs of positive integers closed under decreasing either
  coordinate; Mathlib's `YoungDiagram` is the same object with rows and columns numbered from `0`.
* A *semistandard tableau* of a Young diagram `D` is a map `T : D → ℤ_{>0}` weakly increasing
  along rows and strictly increasing down columns, both conditions imposed only between
  *adjacent* cells; Mathlib's `SemistandardYoungTableau` imposes them between all pairs of cells
  in a row or column, numbers rows, columns and entries from `0`, and is equivalent.
* The *conjugate* `μ'` of a partition, whose `j`-th entry is the number of `i` with `μ_i ≥ j`, is
  Mathlib's `YoungDiagram.transpose`; its cells are the transposed cells, it is an involution, and
  it preserves containment.

It also proves that there are finitely many partitions of each size, and the vertex bound for the
cycle collections of the rank graph whose weight has bounded `q`-degree.

## Main definitions

* `HJO.Comp.equivList`: a composition of `N` is a list of positive integers summing to `N`.
* `HJO.Sym.partitionEquivList`: a partition of `d` is a weakly decreasing list of positive
  integers summing to `d`.
* `HJO.Sym.IsYoungDiagram`, `HJO.Sym.youngDiagramEquiv`: Young diagrams with `1`-based cells.
* `HJO.Sym.ssyt`, `HJO.Sym.ssytEquiv`: semistandard tableaux of a `1`-based Young diagram.

## Main results

* `HJO.Comp.equivList_reverse`, `HJO.Comp.reverse_reverse`: reversing a composition reverses its
  list of parts, and reversing twice is the identity.
* `HJO.Sym.rowLen_transpose_eq_natCard`: the `j`-th row of `μ'` has `#{i | μ_i > j}` cells.
* `HJO.Sym.conjugate_isPartition`: that sequence is a partition.
* `HJO.Sym.mem_transpose_iff_swap`, `HJO.Sym.transpose_transpose`, `HJO.Sym.transpose_mono`.
* `HJO.Sym.finite_setOf_card_eq`: there are finitely many partitions of each size.
* `HJO.Determinant.lt_of_degreeOf_collectionWeight_le`: a cycle collection of the rank graph
  whose weight has `q`-degree at most `D` has all its vertices below `a(D + 1) + ab`.

## Implementation notes

The usual convention numbers rows, columns and the values of a tableau from `1`; Mathlib numbers all
three from `0`. The equivalences `youngDiagramEquiv` and `ssytEquiv` make the shift
`(i, j) ↦ (i+1, j+1)` on cells and `v ↦ v + 1` on values explicitly, so that nothing is assumed in
identifying the two. Everywhere else the `0`-based convention of `HJO.Sym.rowLenSeq` is kept: the
`1`-based `μ'_{j+1}` is `μ.transpose.rowLen j`.

The vertex bound is stated for a finite set of cycles of the rank graph without requiring them to
be pairwise disjoint: disjointness plays no part in the bound, so the statement covers every
collection of vertex-disjoint cycles in the sense of `HJO.Determinant.IsRankCycle`. The `q`-degree
is read in the polynomial ring `R[s, q] = MvPolynomial (Fin 2) R`, with `s = X 0` and `q = X 1`,
over any nontrivial commutative semiring `R`.

## References

This file concerns the definitions `HJO.Comp.equivList`, `HJO.Comp.equivList_reverse`,
`HJO.Sym.partitionEquivList`, `HJO.Sym.IsYoungDiagram`, `HJO.Sym.ssyt`,
`HJO.Sym.rowLen_transpose_eq_natCard`, and the lemmas `HJO.Comp.reverse_reverse`,
`HJO.Sym.conjugate_isPartition`, `HJO.Sym.mem_transpose_iff_swap`, `HJO.Sym.transpose_transpose`,
`HJO.Sym.transpose_mono`, `HJO.Sym.finite_setOf_card_eq`,
`HJO.Determinant.lt_of_degreeOf_collectionWeight_le`.
-/

@[expose] public section

open Finset

/-! ### Compositions -/

namespace HJO.Comp

/-- **A composition of `N` is a list of positive integers summing to `N`.** Mathlib's
`Composition N` records exactly the usual `α = (α_1, …, α_ℓ)` with every `α_i ≥ 1` and
`α_1 + ⋯ + α_ℓ = N`; the empty list is the only composition of `0`. -/
@[hjo "def_composition"]
def equivList (N : ℕ) : Composition N ≃ {α : List ℕ // (∀ i ∈ α, 1 ≤ i) ∧ α.sum = N} where
  toFun c := ⟨c.blocks, fun _ h => c.blocks_pos h, c.blocks_sum⟩
  invFun α := ⟨α.1, fun h => α.2.1 _ h, α.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The list underlying `equivList N c` is the list of blocks of `c`. -/
@[simp]
theorem equivList_apply_coe {N : ℕ} (c : Composition N) : (equivList N c : List ℕ) = c.blocks :=
  rfl

/-- **The reverse of a composition reverses its list of parts**: `Composition.reverse` is the
usual `α^rev = (α_ℓ, α_{ℓ-1}, …, α_1)`. -/
@[hjo "def_comp_reverse"]
theorem equivList_reverse {N : ℕ} (c : Composition N) :
    (equivList N c.reverse : List ℕ) = (equivList N c : List ℕ).reverse :=
  rfl

/-- **Reversing a composition twice gives it back**: `(α^rev)^rev = α`. -/
@[hjo "lem_comp_reverse_involutive"]
theorem reverse_reverse {N : ℕ} (c : Composition N) : c.reverse.reverse = c :=
  Composition.reverse_reverse c

end HJO.Comp

namespace HJO.Sym

/-! ### Partitions as weakly decreasing lists -/

/-- **A partition of `d` is a weakly decreasing list of positive integers summing to `d`.**
Mathlib's `Nat.Partition d` records the parts as a multiset; the equivalence lists them in
nonincreasing order, which a multiset admits in exactly one way, so the usual
`λ_1 ≥ ⋯ ≥ λ_m ≥ 1` with `λ_1 + ⋯ + λ_m = d` carries the same information. The empty list is the
unique partition of `0`. -/
@[hjo "def_cm_partition"]
def partitionEquivList (d : ℕ) :
    Nat.Partition d ≃ {l : List ℕ // l.Pairwise (· ≥ ·) ∧ (∀ x ∈ l, 1 ≤ x) ∧ l.sum = d} where
  toFun p := ⟨p.parts.sort (· ≥ ·), Multiset.pairwise_sort _ _,
    fun _ hx => p.parts_pos ((Multiset.mem_sort _).1 hx), by
      rw [← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]⟩
  invFun l := ⟨l.1, fun hx => l.2.2.1 _ hx, by simpa using l.2.2.2⟩
  left_inv p := Nat.Partition.ext (Multiset.sort_eq _ _)
  right_inv l := Subtype.ext (by
    change Multiset.sort (l.1 : Multiset ℕ) (· ≥ ·) = l.1
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self _ (by simpa using l.2.1))

/-! ### Young diagrams with cells numbered from `1` -/

/-- The shift `(i, j) ↦ (i + 1, j + 1)` from Mathlib's `0`-based cells to the usual `1`-based
cells. -/
def cellShift : ℕ × ℕ ↪ ℕ × ℕ :=
  ⟨fun c => (c.1 + 1, c.2 + 1), fun c d h => by
    simpa [Prod.ext_iff] using h⟩

/-- `cellShift` sends `(i, j)` to `(i + 1, j + 1)`. -/
@[simp]
theorem cellShift_apply (c : ℕ × ℕ) : cellShift c = (c.1 + 1, c.2 + 1) := rfl

/-- **A Young diagram**: a finite set `D` of pairs of positive integers such that `(i, j) ∈ D`,
`1 ≤ i' ≤ i` and `1 ≤ j' ≤ j` imply `(i', j') ∈ D`. The first coordinate of a cell is its row and
the second its column. -/
@[hjo "def_cm_young_diagram"]
def IsYoungDiagram (D : Finset (ℕ × ℕ)) : Prop :=
  (∀ c ∈ D, 1 ≤ c.1 ∧ 1 ≤ c.2) ∧
    ∀ i j i' j' : ℕ, (i, j) ∈ D → 1 ≤ i' → i' ≤ i → 1 ≤ j' → j' ≤ j → (i', j') ∈ D

/-- The `1`-based cells of a Mathlib Young diagram: the `1`-based cell `(i + 1, j + 1)` for each
cell `(i, j)` of `μ`. -/
def oneCells (μ : YoungDiagram) : Finset (ℕ × ℕ) :=
  μ.cells.map cellShift

/-- A pair `c` is a `1`-based cell of `μ` iff both coordinates are positive and
`(c.1 - 1, c.2 - 1)` is a cell of `μ`. -/
theorem mem_oneCells {μ : YoungDiagram} {c : ℕ × ℕ} :
    c ∈ oneCells μ ↔ 1 ≤ c.1 ∧ 1 ≤ c.2 ∧ (c.1 - 1, c.2 - 1) ∈ μ := by
  simp only [oneCells, Finset.mem_map, YoungDiagram.mem_cells, cellShift_apply]
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨by omega, by omega, by simpa using hd⟩
  · rintro ⟨h1, h2, h⟩
    exact ⟨_, h, Prod.ext (by simp; omega) (by simp; omega)⟩

/-- The pair `(i + 1, j + 1)` is a `1`-based cell of `μ` iff `(i, j)` is a cell of `μ`. -/
@[simp]
theorem add_one_mem_oneCells {μ : YoungDiagram} {i j : ℕ} :
    (i + 1, j + 1) ∈ oneCells μ ↔ (i, j) ∈ μ := by
  simp [mem_oneCells]

/-- The `1`-based cells of a Mathlib Young diagram form a Young diagram. -/
theorem isYoungDiagram_oneCells (μ : YoungDiagram) : IsYoungDiagram (oneCells μ) := by
  refine ⟨fun c hc => ⟨(mem_oneCells.1 hc).1, (mem_oneCells.1 hc).2.1⟩, ?_⟩
  intro i j i' j' h hi' hii hj' hjj
  obtain ⟨-, -, h⟩ := mem_oneCells.1 h
  exact mem_oneCells.2 ⟨hi', hj', μ.up_left_mem (by omega) (by omega) h⟩

/-- **Mathlib's Young diagrams are the usual Young diagrams**, up to numbering rows and columns
from `0`: the equivalence sends `μ` to its cells shifted by `(1, 1)`, and a `1`-based diagram `D`
to the diagram of cells `(i, j)` with `(i + 1, j + 1) ∈ D`. -/
@[hjo "def_cm_young_diagram"]
noncomputable def youngDiagramEquiv : YoungDiagram ≃ {D : Finset (ℕ × ℕ) // IsYoungDiagram D} where
  toFun μ := ⟨oneCells μ, isYoungDiagram_oneCells μ⟩
  invFun D :=
    { cells := D.1.preimage cellShift cellShift.injective.injOn
      isLowerSet := by
        intro c d hcd hc
        simp only [Finset.coe_preimage, Set.mem_preimage, Finset.mem_coe, cellShift_apply] at hc ⊢
        exact D.2.2 _ _ _ _ hc (by omega) (Nat.add_le_add_right hcd.1 1) (by omega)
          (Nat.add_le_add_right hcd.2 1) }
  left_inv μ := by
    ext c
    simp [Finset.mem_preimage]
  right_inv D := by
    refine Subtype.ext (Finset.ext fun c => ?_)
    simp only [mem_oneCells, YoungDiagram.mem_mk, Finset.mem_preimage, cellShift_apply]
    constructor
    · rintro ⟨h1, h2, h⟩
      have hc : c = (c.1 - 1 + 1, c.2 - 1 + 1) := Prod.ext (by simp; omega) (by simp; omega)
      rwa [hc]
    · intro h
      have := D.2.1 c h
      have hc : (c.1 - 1 + 1, c.2 - 1 + 1) = c := Prod.ext (by simp; omega) (by simp; omega)
      exact ⟨this.1, this.2, by rwa [hc]⟩

/-- The finite set underlying `youngDiagramEquiv μ` is `oneCells μ`. -/
@[simp]
theorem coe_youngDiagramEquiv (μ : YoungDiagram) : (youngDiagramEquiv μ : Finset (ℕ × ℕ)) =
    oneCells μ :=
  rfl

/-! ### Semistandard tableaux -/

/-- **The semistandard tableaux `SSYT(D)` of a Young diagram `D`**: the maps `T : D → ℤ_{>0}`
with `T(i, j) ≤ T(i, j + 1)` whenever `(i, j)` and `(i, j + 1)` are cells of `D`, and
`T(i, j) < T(i + 1, j)` whenever `(i, j)` and `(i + 1, j)` are cells of `D`. -/
@[hjo "def_cm_ssyt"]
def ssyt (D : Finset (ℕ × ℕ)) : Set (D → ℕ+) :=
  {T | (∀ i j (h : (i, j) ∈ D) (h' : (i, j + 1) ∈ D), T ⟨_, h⟩ ≤ T ⟨_, h'⟩) ∧
    ∀ i j (h : (i, j) ∈ D) (h' : (i + 1, j) ∈ D), T ⟨_, h⟩ < T ⟨_, h'⟩}

/-- The entry of Mathlib's `0`-based tableau read off a `1`-based map: the value at the `1`-based
cell `(i + 1, j + 1)`, lowered by one, and `0` off the diagram. -/
def ssytEntry {μ : YoungDiagram} (T : oneCells μ → ℕ+) (i j : ℕ) : ℕ :=
  if h : (i + 1, j + 1) ∈ oneCells μ then (T ⟨_, h⟩ : ℕ) - 1 else 0

/-- On a cell `(i, j)` of `μ`, `ssytEntry T i j` is the value of `T` at `(i + 1, j + 1)`, lowered
by one. -/
theorem ssytEntry_of_mem {μ : YoungDiagram} (T : oneCells μ → ℕ+) {i j : ℕ} (h : (i, j) ∈ μ) :
    ssytEntry T i j = (T ⟨_, add_one_mem_oneCells.2 h⟩ : ℕ) - 1 := by
  rw [ssytEntry, dite_eq_left_of_eq_true (eq_true (add_one_mem_oneCells.2 h))]

/-- The `0`-based Mathlib semistandard tableau with entries `ssytEntry T` of a `1`-based
semistandard tableau `T`. -/
def ssytToMathlib {μ : YoungDiagram} (T : ssyt (oneCells μ)) : SemistandardYoungTableau μ where
  entry := ssytEntry T.1
  row_weak' := by
    intro i j1 j2 hj h2
    have step : ∀ j, (i, j + 1) ∈ μ → ssytEntry T.1 i j ≤ ssytEntry T.1 i (j + 1) := by
      intro j hj1
      have hj0 : (i, j) ∈ μ := μ.up_left_mem le_rfl (Nat.le_succ j) hj1
      rw [ssytEntry_of_mem _ hj0, ssytEntry_of_mem _ hj1]
      have := T.2.1 (i + 1) (j + 1) (add_one_mem_oneCells.2 hj0) (add_one_mem_oneCells.2 hj1)
      exact Nat.sub_le_sub_right (by exact_mod_cast this) 1
    induction j2 with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
      · exact (ih hlt (μ.up_left_mem le_rfl (Nat.le_succ k) h2)).trans (step k h2)
      · exact step _ h2
  col_strict' := by
    intro i1 i2 j hi h2
    have step : ∀ i, (i + 1, j) ∈ μ → ssytEntry T.1 i j < ssytEntry T.1 (i + 1) j := by
      intro i hi1
      have hi0 : (i, j) ∈ μ := μ.up_left_mem (Nat.le_succ i) le_rfl hi1
      rw [ssytEntry_of_mem _ hi0, ssytEntry_of_mem _ hi1]
      have := T.2.2 (i + 1) (j + 1) (add_one_mem_oneCells.2 hi0) (add_one_mem_oneCells.2 hi1)
      have h1 := (T.1 ⟨_, add_one_mem_oneCells.2 hi0⟩).pos
      have h3 : ((T.1 ⟨_, add_one_mem_oneCells.2 hi0⟩ : ℕ+) : ℕ) <
          (T.1 ⟨_, add_one_mem_oneCells.2 hi1⟩ : ℕ) := by exact_mod_cast this
      omega
    induction i2 with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
      · exact (ih hlt (μ.up_left_mem (Nat.le_succ k) le_rfl h2)).trans (step k h2)
      · exact step _ h2
  zeros' := by
    intro i j h
    rw [ssytEntry, dite_eq_right_of_eq_false (eq_false (by simpa using h))]

/-- **Mathlib's semistandard Young tableaux are the usual ones**, up to numbering rows, columns and
values from `0`: a tableau `T` of `μ` corresponds to the map sending the `1`-based cell
`(i + 1, j + 1)` to `T(i, j) + 1`. The usual adjacent-cell conditions imply Mathlib's
conditions between any two cells of a row or column, the cells in between lying in the diagram. -/
@[hjo "def_cm_ssyt"]
def ssytEquiv (μ : YoungDiagram) : SemistandardYoungTableau μ ≃ ssyt (oneCells μ) where
  toFun T := ⟨fun c => ⟨T (c.1.1 - 1) (c.1.2 - 1) + 1, Nat.succ_pos _⟩, by
    refine ⟨fun i j h h' => ?_, fun i j h h' => ?_⟩
    · obtain ⟨hi, hj, -⟩ := mem_oneCells.1 h
      obtain ⟨-, -, h'⟩ := mem_oneCells.1 h'
      change T (i - 1) (j - 1) + 1 ≤ T (i - 1) (j + 1 - 1) + 1
      exact Nat.add_le_add_right (T.row_weak (by omega) h') 1
    · obtain ⟨hi, hj, -⟩ := mem_oneCells.1 h
      obtain ⟨-, -, h'⟩ := mem_oneCells.1 h'
      change T (i - 1) (j - 1) + 1 < T (i + 1 - 1) (j - 1) + 1
      exact Nat.add_lt_add_right (T.col_strict (by omega) h') 1⟩
  invFun := ssytToMathlib
  left_inv T := by
    ext i j
    change ssytEntry _ i j = T i j
    by_cases h : (i, j) ∈ μ
    · rw [ssytEntry_of_mem _ h]
      simp
    · rw [ssytEntry, dite_eq_right_of_eq_false (eq_false (by simpa using h)), T.zeros h]
  right_inv T := by
    refine Subtype.ext (funext fun c => ?_)
    obtain ⟨hi, hj, h⟩ := mem_oneCells.1 c.2
    have hc : (⟨(c.1.1 - 1 + 1, c.1.2 - 1 + 1), add_one_mem_oneCells.2 h⟩ : oneCells μ) = c :=
      Subtype.ext (Prod.ext (by simp; omega) (by simp; omega))
    apply PNat.eq
    change ssytEntry T.1 (c.1.1 - 1) (c.1.2 - 1) + 1 = _
    rw [ssytEntry_of_mem _ h, hc]
    have := (T.1 c).pos
    omega

/-! ### The conjugate partition -/

/-- **The conjugate of a partition is Mathlib's transpose**: the `j`-th row of `μ.transpose` has
as many cells as there are rows `i` of `μ` with `μ_i > j`. In the usual `1`-based indexing this
is `μ'_{j+1} = #{i | μ_i ≥ j + 1}`, which is the definition of `μ'`. -/
@[hjo "def_dua_conjugate"]
theorem rowLen_transpose_eq_natCard (μ : YoungDiagram) (j : ℕ) :
    μ.transpose.rowLen j = Nat.card {i | j < μ.rowLen i} := by
  have h : {i | j < μ.rowLen i} = Set.Iio (μ.colLen j) := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_Iio, ← YoungDiagram.mem_iff_lt_rowLen,
      YoungDiagram.mem_iff_lt_colLen]
  rw [YoungDiagram.rowLen_transpose, h]
  simp

/-- **The conjugate sequence is a partition**: for each `j` the set of `i` with `μ_i > j` is
finite, and the sequence of their numbers is weakly decreasing and zero from some point on. In
`1`-based indexing, the sequence `κ_j = #{i | μ_i ≥ j}` is a partition. -/
@[hjo "lem_dua_conjugate_partition"]
theorem conjugate_isPartition (μ : YoungDiagram) :
    (∀ j, {i | j < μ.rowLen i}.Finite) ∧
      Antitone (fun j => Nat.card {i | j < μ.rowLen i}) ∧
        {j | Nat.card {i | j < μ.rowLen i} ≠ 0}.Finite := by
  simp only [← rowLen_transpose_eq_natCard]
  refine ⟨fun j => (Set.finite_Iio (μ.colLen j)).subset fun i hi => ?_,
    rowLenSeq_antitone μ.transpose, rowLenSeq_finite_support μ.transpose⟩
  simpa only [Set.mem_ofPred_eq, Set.mem_Iio, ← YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_colLen] using hi

/-- **The cells of the conjugate are the transposed cells**: `(i, j)` is a cell of `μ` exactly
when `(j, i)` is a cell of `μ'`. -/
@[hjo "lem_dua_conjugate_cells"]
theorem mem_transpose_iff_swap (μ : YoungDiagram) (i j : ℕ) :
    (i, j) ∈ μ ↔ (j, i) ∈ μ.transpose := by
  rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk]

/-- **Conjugation is an involution**: `(μ')' = μ`. -/
@[hjo "lem_dua_conjugate_involutive"]
theorem transpose_transpose (μ : YoungDiagram) : μ.transpose.transpose = μ :=
  YoungDiagram.transpose_transpose μ

/-- **Conjugation preserves containment**: `ν ⊆ μ` implies `ν' ⊆ μ'`. -/
@[hjo "lem_dua_conjugate_subset"]
theorem transpose_mono {ν μ : YoungDiagram} (h : ν ≤ μ) : ν.transpose ≤ μ.transpose :=
  YoungDiagram.transpose_mono h

/-! ### Finitely many partitions of each size -/

/-- Every cell of a diagram of size `d` has both coordinates below `d`: the cells `(k, 0)` for
`k ≤ i` lie in the diagram, as do the cells `(0, k)` for `k ≤ j`. -/
theorem cells_subset_range_product (μ : YoungDiagram) :
    μ.cells ⊆ range μ.card ×ˢ range μ.card := by
  intro c hc
  rw [YoungDiagram.mem_cells] at hc
  have hrow : (range (c.1 + 1)).image (fun k => (k, 0)) ⊆ μ.cells := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    exact (YoungDiagram.mem_cells _).2 (μ.up_left_mem (by simp at hk; omega) (Nat.zero_le _) hc)
  have hcol : (range (c.2 + 1)).image (fun k => (0, k)) ⊆ μ.cells := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    exact (YoungDiagram.mem_cells _).2 (μ.up_left_mem (Nat.zero_le _) (by simp at hk; omega) hc)
  have h1 := Finset.card_le_card hrow
  have h2 := Finset.card_le_card hcol
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), card_range] at h1 h2
  simp only [Finset.mem_product, mem_range, YoungDiagram.card]
  omega

/-- **The partitions of a given size are finite in number**: for every `d` there are finitely
many partitions `μ` with `|μ| = d`. -/
@[hjo "lem_ght_partition_finite"]
theorem finite_setOf_card_eq (d : ℕ) : {μ : YoungDiagram | μ.card = d}.Finite := by
  have hfin : ((fun μ : YoungDiagram => μ.cells) ⁻¹'
      ((range d ×ˢ range d).powerset : Set (Finset (ℕ × ℕ)))).Finite :=
    (Finset.finite_toSet _).preimage fun μ _ ν _ h => YoungDiagram.ext h
  refine hfin.subset fun μ hμ => ?_
  simp only [Set.mem_ofPred_eq] at hμ
  simp only [Set.mem_preimage, Finset.coe_powerset, Set.mem_powerset_iff,
    Finset.coe_subset]
  rw [← hμ]
  exact cells_subset_range_product μ

end HJO.Sym

/-! ### The vertices of a cycle collection of bounded `q`-degree -/

namespace HJO.Determinant

variable {a b H : ℕ}

/-- Along a cycle `c`, the walk `k ↦ c^k x₀` from a moved point `x₀` is injective on
`ZMod #c.support`. -/
theorem _root_.Equiv.Perm.IsCycle.injective_pow_val_apply {α : Type*} [DecidableEq α]
    [Fintype α] {c : Equiv.Perm α} (hcyc : c.IsCycle) {x₀ : α} (hx₀ : x₀ ∈ c.support) :
    Function.Injective fun k : ZMod c.support.card => (c ^ k.val) x₀ := by
  have : NeZero c.support.card := ⟨by have := hcyc.two_le_card_support; omega⟩
  have key : ∀ k l : ZMod c.support.card, k.val ≤ l.val → (c ^ k.val) x₀ = (c ^ l.val) x₀ →
      k = l := by
    intro k l hkl h
    have hy : c ((c ^ k.val) x₀) ≠ (c ^ k.val) x₀ :=
      Equiv.Perm.mem_support.1 (Equiv.Perm.pow_apply_mem_support.2 hx₀)
    have h' : (c ^ (l.val - k.val)) ((c ^ k.val) x₀) = (c ^ k.val) x₀ := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hkl, h]
    have hdvd := orderOf_dvd_of_pow_eq_one ((hcyc.pow_eq_one_iff' hy).2 h')
    rw [hcyc.orderOf] at hdvd
    have h₀ : l.val - k.val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdvd ((Nat.sub_le _ _).trans_lt (ZMod.val_lt l))
    exact ZMod.val_injective _ (by omega)
  intro k l h
  rcases le_total k.val l.val with hkl | hlk
  · exact key k l hkl h
  · exact (key l k hlk h.symm).symm

/-- A simple directed cycle `c` of the rank graph, for coprime `a` and `b`, moves `a + b` vertices
and spans at most `ab`: any two of its vertices differ by at most `ab`. The cycle is read as the
closed walk `k ↦ c^k x₀` around `ZMod n`, `n` being the number of vertices it moves. -/
theorem cycle_card_support_and_span (hab : Nat.Coprime a b) {c : Equiv.Perm (Fin (H + 1))}
    (hcyc : c.IsCycle) (hadj : ∀ i ∈ c.support, (rankGraph a b H).Adj i (c i)) :
    c.support.card = a + b ∧ ∀ u ∈ c.support, ∀ v ∈ c.support, (u : ℕ) ≤ v + a * b := by
  obtain ⟨x₀, hx₀⟩ := hcyc.nonempty_support
  set n := c.support.card with hn
  have hn2 : 2 ≤ n := hcyc.two_le_card_support
  have : NeZero n := ⟨by omega⟩
  have hord : orderOf c = n := hcyc.orderOf
  have hmod : ∀ m : ℕ, (c ^ (m % n)) x₀ = (c ^ m) x₀ := fun m => by
    rw [← hord, pow_mod_orderOf]
  let w : ZMod n → ℕ := fun k => ((c ^ k.val) x₀ : ℕ)
  have hstep : ∀ k : ZMod n, (c ^ (k + 1).val) x₀ = c ((c ^ k.val) x₀) := by
    intro k
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod, hmod, pow_succ',
      Equiv.Perm.mul_apply]
  have hadjw : ∀ k : ZMod n, (rankGraph a b H).Adj (w k) (w (k + 1)) := by
    intro k
    simp only [w, hstep]
    exact hadj _ (Equiv.Perm.pow_apply_mem_support.2 hx₀)
  have hinj : Function.Injective w := fun k l h => hcyc.injective_pow_val_apply hx₀ (Fin.ext h)
  have hlen : n = a + b := eq_add_of_rankGraph_cycle hab hinj hadjw
  refine ⟨hlen, fun u hu v hv => ?_⟩
  have hcover : ∀ y ∈ c.support, ∃ k : ZMod n, w k = y := by
    intro y hy
    obtain ⟨m, hm⟩ := hcyc.exists_pow_eq (Equiv.Perm.mem_support.1 hx₀)
      (Equiv.Perm.mem_support.1 hy)
    refine ⟨(m : ZMod n), ?_⟩
    simp only [w, ZMod.val_natCast, hmod, hm]
  obtain ⟨k, hk⟩ := hcover u hu
  obtain ⟨l, hl⟩ := hcover v hv
  rw [← hk, ← hl]
  exact le_add_mul_of_rankGraph_walk hlen hadjw k l

/-- **Bounded `q`-exponent bounds the vertices**: for coprime `a` and `b`, if the total level
`∑_{c ∈ C} ∑_{i ∈ c} [i → c i is up] ⌊i/a⌋` of the up edges of a finite set `C` of simple directed
cycles of the rank graph is at most `D`, then every vertex of every cycle of `C` is below
`a(D + 1) + ab`. -/
theorem lt_of_qExp_le (hab : Nat.Coprime a b) {C : Finset (Equiv.Perm (Fin (H + 1)))}
    (hC : ∀ c ∈ C, c.IsCycle ∧ ∀ i ∈ c.support, (rankGraph a b H).Adj i (c i)) {D : ℕ}
    (hD : ∑ c ∈ C, ∑ i ∈ c.support, (if (c i : ℕ) = (i : ℕ) + b then (i : ℕ) / a else 0) ≤ D) :
    ∀ c ∈ C, ∀ v ∈ c.support, (v : ℕ) < a * (D + 1) + a * b := by
  intro c hc v hv
  obtain ⟨hcyc, hadj⟩ := hC c hc
  obtain ⟨hlen, hspan⟩ := cycle_card_support_and_span hab hcyc hadj
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have hb : b = 1 := Nat.coprime_zero_left b |>.1 hab
      have := hcyc.two_le_card_support
      omega
    · exact ha
  obtain ⟨r, hr, hrmin⟩ := c.support.exists_min_image (fun i => (i : ℕ)) ⟨v, hv⟩
  have hup : (c r : ℕ) = (r : ℕ) + b := by
    rcases (rankGraph_adj.1 (hadj r hr)).1 with h | h
    · exact h
    · have := hrmin (c r) (Equiv.Perm.apply_mem_support.2 hr)
      exact absurd (Fin.ext (by omega)) (Equiv.Perm.mem_support.1 hr)
  have hexp : (r : ℕ) / a ≤ D := by
    refine le_trans ?_ (le_trans (Finset.single_le_sum (f := fun c : Equiv.Perm (Fin (H + 1)) =>
      ∑ i ∈ c.support, (if (c i : ℕ) = (i : ℕ) + b then (i : ℕ) / a else 0))
      (fun _ _ => Nat.zero_le _) hc) hD)
    refine le_trans ?_ (Finset.single_le_sum (f := fun i : Fin (H + 1) =>
      (if (c i : ℕ) = (i : ℕ) + b then (i : ℕ) / a else 0)) (fun _ _ => Nat.zero_le _) hr)
    simp [hup]
  have h1 : (r : ℕ) < a * (D + 1) :=
    lt_of_lt_of_le (Nat.lt_mul_div_succ _ ha) (Nat.mul_le_mul_left a (by omega))
  have h2 := hspan v hv r hr
  omega

/-- **Bounded `q`-degree bounds the vertices.** Let `a` and `b` be coprime and `D ≥ 0`. If the
weight of a collection `C` of simple directed cycles of the rank graph `G_H`, computed in
`R[s, q]`, has `q`-degree at most `D`, then every vertex of every cycle of `C` is strictly below
`a(D + 1) + ab`. The weight is the monomial `s^e q^E` of `collectionWeight_eq_pow_mul_pow`, whose
`q`-degree is the total level `E` of its up edges. -/
@[hjo "lem_cycle_collection_finite"]
theorem lt_of_degreeOf_collectionWeight_le {R : Type*} [CommSemiring R] [Nontrivial R]
    (hab : Nat.Coprime a b) {C : Finset (Equiv.Perm (Fin (H + 1)))}
    (hC : ∀ c ∈ C, c.IsCycle ∧ ∀ i ∈ c.support, (rankGraph a b H).Adj i (c i)) {D : ℕ}
    (hD : (collectionWeight a b (MvPolynomial.X 0 : MvPolynomial (Fin 2) R)
      (MvPolynomial.X 1) C).degreeOf 1 ≤ D) :
    ∀ c ∈ C, ∀ v ∈ c.support, (v : ℕ) < a * (D + 1) + a * b := by
  refine lt_of_qExp_le hab hC ?_
  rw [collectionWeight_eq_pow_mul_pow a b _ _
    (fun c hc i hi => (rankGraph_adj.1 ((hC c hc).2 i hi)).1)] at hD
  refine le_trans (le_of_eq ?_) hD
  set m := ∑ c ∈ C, c.support.card
  set E := ∑ c ∈ C, ∑ i ∈ c.support, (if (c i : ℕ) = (i : ℕ) + b then (i : ℕ) / a else 0)
  have : (MvPolynomial.X 0 : MvPolynomial (Fin 2) R) ^ m * MvPolynomial.X 1 ^ E =
      MvPolynomial.monomial (Finsupp.single 0 m + Finsupp.single 1 E) 1 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul, one_mul]
  rw [this, MvPolynomial.degreeOf_monomial_eq _ _ one_ne_zero]
  simp

end HJO.Determinant
