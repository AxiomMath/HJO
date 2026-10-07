/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SuperAlphabet
public import HJO.CarlssonMellit.SuperWords
public import HJO.CarlssonMellit.Tableaux
public meta import HJO.Attr

/-! # The descent set of a standard tableau, and the super tableaux of a Young diagram

Two notions of the super expansion live on a Young diagram rather than on a word: the descent set
`Des(S)` of a standard tableau, read off the columns of the cells carrying consecutive values, and
the set `SSYT^±(D)` of super tableaux, the fillings of `D` by super letters that increase weakly in
both directions and repeat a letter only in the manner its sign permits. This file defines both.

## Main definitions

* `HJO.Sym.sytDescentSet`: `Des(S)`.
* `HJO.Sym.SuperYoungTableau`: `SSYT^±(D)`.
* `HJO.Sym.superTableauMonomial`: `z_T`.

## Main results

* `HJO.Sym.mem_sytDescentSet_iff_exists`: on a standard tableau the descent condition is the
  comparison of the columns of `S^{-1}(a)` and `S^{-1}(a+1)`.
* `HJO.Sym.SuperYoungTableau.ofAdjacent`: a filling satisfying the *adjacent* weak
  increase, together with the two strip conditions, is a super tableau.

## Implementation notes

`Mathlib`'s `YoungDiagram` and `SemistandardYoungTableau` are used unchanged, as in
`HJO/CarlssonMellit/Tableaux.lean`: cells are `0`-based and so are the entries, so the one-based
tableau values `1, …, n` are `0, …, n - 1` here.

`sytDescentSet` keeps the library's `1`-based indexing of *steps*, matching
`HJO.Sym.descentSet` and `HJO.ParkingFunctions.gessel`: a step `a` names the step from the value
`a - 1` to the value `a`, so the one-based descent `a ∈ {1, …, n-1}` — comparing the columns of
`S^{-1}(a)` and `S^{-1}(a+1)` — is the step `a` here, comparing the columns of the cells carrying
the `0`-based values `a - 1` and `a`, and the set lands in `Finset.Ico 1 n` where its consumer
`F_{n,Des(S)}` needs it. So no index is shifted relative to `HJO.ParkingFunctions.gessel`.

The definition quantifies over *all* cells carrying the two values rather than naming
`S^{-1}(a)` by choice: it is then total on every semistandard tableau, decidable, and free of
`Classical.choice`. On a standard tableau the two cells exist and are unique, so the bounded
quantifier is the comparison; that is `mem_sytDescentSet_iff_exists`, which is the form
a consumer uses and which also shows the definition is not vacuous.

`SuperYoungTableau` is a *separate* structure and not an instance of `SemistandardYoungTableau`.
Three things rule the reuse out: the entries are super letters rather than natural numbers; the
column condition is weak increase rather than strict; and the two strip conditions — no repeated
positive letter in a column, no repeated negative letter in a row — have no counterpart there.
`Mathlib`'s `SemistandardYoungTableau` is instead the *restriction* of this notion to positive
letters, an observation made in the proof of `HJO.Sym.schurSeries_eq_sum_gessel`, and it is
already used unchanged for `SSYT(D)` and `SYT(D)`, so nothing is duplicated.

What is mirrored from `Mathlib` is the *shape*: the entry is an unrestricted `ℕ → ℕ → SuperLetter`
required to take the fixed value `SuperLetter.mk 0 false` off the diagram, so that two tableaux
agreeing on the cells are equal and the type is extensional; and the weak-increase fields are stated
between *any* two cells of a row or a column rather than between adjacent ones. They are usually
stated for adjacent cells and then chained — that is the first preliminary of the proof of
`HJO.Sym.superTableauOfPair_bijective` — so the two readings define the same set, and the chaining
is proved here rather than asserted: `SuperYoungTableau.ofAdjacent` builds a tableau from exactly
the four adjacent clauses, using only `YoungDiagram.up_left_mem` to know that a row and a column of
a diagram are contiguous. The two strip clauses are already stated for arbitrary pairs of cells,
so they are fields verbatim.

## References

Definitions `HJO.Sym.sytDescentSet`, `HJO.Sym.SuperYoungTableau` and
`HJO.Sym.superTableauMonomial`; and
E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The descent set of a standard tableau -/

/-- **The descent set of a standard tableau** `Des(S)`: the steps `a` of the
window `{1, …, n-1}` at which the column of the cell carrying the value `a` is at most the column of
the cell carrying the value `a - 1`.

Steps are `1`-based and values `0`-based, as everywhere in this library, so the step `a`
compares the `0`-based values `a - 1` and `a`, the one-based `a` and `a + 1`; the set therefore lies
in `Finset.Ico 1 #D` exactly where `HJO.ParkingFunctions.gessel` wants it. The comparison is
quantified over all cells carrying the two values rather than over chosen ones, which keeps
the definition total and choice-free; `mem_sytDescentSet_iff_exists` reads it as the
column comparison on a standard tableau, where the two cells exist and are unique. -/
@[hjo "def_cm_syt_descent"]
def sytDescentSet {μ : YoungDiagram} (S : SemistandardYoungTableau μ) : Finset ℕ :=
  {a ∈ Ico 1 μ.card | ∀ c ∈ μ.cells, ∀ c' ∈ μ.cells,
    S c.1 c.2 = a → S c'.1 c'.2 = a - 1 → c.2 ≤ c'.2}

/-- Membership in the descent set of a tableau, by definition. -/
@[simp]
theorem mem_sytDescentSet {μ : YoungDiagram} {S : SemistandardYoungTableau μ} {a : ℕ} :
    a ∈ sytDescentSet S ↔ 1 ≤ a ∧ a < μ.card ∧
      ∀ c ∈ μ.cells, ∀ c' ∈ μ.cells, S c.1 c.2 = a → S c'.1 c'.2 = a - 1 → c.2 ≤ c'.2 := by
  simp only [sytDescentSet, mem_filter, mem_Ico, and_assoc]

/-- The descent set lies in the window `{1, …, n-1}` of steps, which is what makes it an
admissible index for the Gessel fundamental `F_{n,Des(S)}`. -/
theorem sytDescentSet_subset_Ico {μ : YoungDiagram} (S : SemistandardYoungTableau μ) :
    sytDescentSet S ⊆ Ico 1 μ.card :=
  filter_subset _ _

/-- **The descent set of a standard tableau is the usual one**: a step `a` of the window is a
descent exactly when *some* cell carrying the value `a` has column at most that of *some* cell
carrying `a - 1`. On a standard tableau both cells exist and are unique, so the existential and the
universal readings agree, and this is the usual comparison of the columns of `S^{-1}(a+1)` and
`S^{-1}(a)` in `0`-based values. -/
theorem mem_sytDescentSet_iff_exists {μ : YoungDiagram} {S : SemistandardYoungTableau μ}
    (hS : IsStandard S) {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a < μ.card) :
    a ∈ sytDescentSet S ↔ ∃ c ∈ μ.cells, ∃ c' ∈ μ.cells,
      S c.1 c.2 = a ∧ S c'.1 c'.2 = a - 1 ∧ c.2 ≤ c'.2 := by
  obtain ⟨c, hc, hca⟩ := hS.exists_eq ha2
  obtain ⟨c', hc', hca'⟩ := hS.exists_eq (show a - 1 < μ.card by omega)
  rw [mem_sytDescentSet]
  refine ⟨fun h => ⟨c, hc, c', hc', hca, hca', h.2.2 c hc c' hc' hca hca'⟩, fun h => ?_⟩
  obtain ⟨d, hd, d', hd', hda, hda', hle⟩ := h
  refine ⟨ha1, ha2, fun e he e' he' hea hea' => ?_⟩
  have hed : e = d := hS.injOn (by simpa using he) (by simpa using hd) (by simp only [hea, hda])
  have hed' : e' = d' := hS.injOn (by simpa using he') (by simpa using hd')
    (by simp only [hea', hda'])
  rw [hed, hed']
  exact hle

/-! ### Super tableaux -/

/-- **The super tableaux of a Young diagram** `SSYT^±(D)`: the fillings of
the cells of `D` by letters of the super alphabet that increase weakly along each row and down each
column for the order of `HJO.Sym.SuperLetter`, and in which no two cells of one column carry the
same positive letter and no two cells of one row carry the same negative letter. The last two
conditions are the usual requirement that the cells carrying a positive letter form a horizontal
strip and those carrying a negative letter a vertical strip.

As for `Mathlib`'s `SemistandardYoungTableau`, the filling is an unrestricted map
`ℕ → ℕ → SuperLetter` required to take the fixed value `SuperLetter.mk 0 false` off the diagram, so
that the type is extensional; and the weak-increase fields are stated between any two cells of a row
or a column, which is the adjacent form chained along the contiguous rows and columns of
a diagram. `SuperYoungTableau.ofAdjacent` builds a super tableau from the four clauses
verbatim, so the two readings are identified by proof rather than by assertion. -/
@[hjo "def_cm_super_tableau"]
structure SuperYoungTableau (μ : YoungDiagram) where
  /-- The letter filling the cell `(i, j)`; off the diagram it is held at `SuperLetter.mk 0 false`
  so that two tableaux agreeing on the cells are equal. -/
  entry : ℕ → ℕ → SuperLetter
  /-- The letters increase weakly along a row: `T(i,j) ≺ T(i,j') or T(i,j) = T(i,j')`
  for `j < j'`. -/
  row_weak' : ∀ {i j1 j2 : ℕ}, j1 < j2 → (i, j2) ∈ μ → entry i j1 ≤ entry i j2
  /-- The letters increase weakly down a column:
  `T(i,j) ≺ T(i',j) or T(i,j) = T(i',j)` for `i < i'`. -/
  col_weak' : ∀ {i1 i2 j : ℕ}, i1 < i2 → (i2, j) ∈ μ → entry i1 j ≤ entry i2 j
  /-- No two cells of one column carry the same positive letter: a repeated letter in a column is
  negative. This is the horizontal-strip condition on the positive letters. -/
  col_isNegative' : ∀ {i1 i2 j : ℕ}, i1 < i2 → (i2, j) ∈ μ →
    entry i1 j = entry i2 j → (entry i1 j).IsNegative
  /-- No two cells of one row carry the same negative letter: a repeated letter in a row is
  positive. This is the vertical-strip condition on the negative letters. -/
  row_isPositive' : ∀ {i j1 j2 : ℕ}, j1 < j2 → (i, j2) ∈ μ →
    entry i j1 = entry i j2 → (entry i j1).IsPositive
  /-- Off the diagram the filling is held at the least letter, which is what makes two super
  tableaux agreeing on the cells equal. -/
  outside' : ∀ {i j : ℕ}, (i, j) ∉ μ → entry i j = SuperLetter.mk 0 false

namespace SuperYoungTableau

variable {μ : YoungDiagram}

instance instFunLike : FunLike (SuperYoungTableau μ) ℕ (ℕ → SuperLetter) where
  coe := SuperYoungTableau.entry
  coe_injective T T' h := by
    cases T
    cases T'
    congr

@[simp]
theorem to_fun_eq_coe {T : SuperYoungTableau μ} : T.entry = (T : ℕ → ℕ → SuperLetter) :=
  rfl

@[ext]
theorem ext {T T' : SuperYoungTableau μ} (h : ∀ i j, T i j = T' i j) : T = T' :=
  DFunLike.ext T T' fun _ => funext fun _ => h _ _

/-- The letters increase weakly along a row, between any two of its cells. -/
theorem row_weak (T : SuperYoungTableau μ) {i j1 j2 : ℕ} (hj : j1 < j2) (hcell : (i, j2) ∈ μ) :
    T i j1 ≤ T i j2 :=
  T.row_weak' hj hcell

/-- The letters increase weakly down a column, between any two of its cells. -/
theorem col_weak (T : SuperYoungTableau μ) {i1 i2 j : ℕ} (hi : i1 < i2) (hcell : (i2, j) ∈ μ) :
    T i1 j ≤ T i2 j :=
  T.col_weak' hi hcell

/-- A letter repeated in a column is negative: no two cells of one column carry the same positive
letter. -/
theorem col_isNegative (T : SuperYoungTableau μ) {i1 i2 j : ℕ} (hi : i1 < i2)
    (hcell : (i2, j) ∈ μ) (heq : T i1 j = T i2 j) : (T i1 j).IsNegative :=
  T.col_isNegative' hi hcell heq

/-- A letter repeated in a row is positive: no two cells of one row carry the same negative
letter. -/
theorem row_isPositive (T : SuperYoungTableau μ) {i j1 j2 : ℕ} (hj : j1 < j2)
    (hcell : (i, j2) ∈ μ) (heq : T i j1 = T i j2) : (T i j1).IsPositive :=
  T.row_isPositive' hj hcell heq

/-- Off the diagram a super tableau takes the least letter. -/
theorem outside (T : SuperYoungTableau μ) {i j : ℕ} (h : (i, j) ∉ μ) :
    T i j = SuperLetter.mk 0 false :=
  T.outside' h

/-- Two cells of one column carrying the same positive letter do not occur, in the contrapositive
form the block analysis in the proof of `HJO.Sym.superTableauOfPair_bijective` uses. -/
theorem ne_of_isPositive_of_col (T : SuperYoungTableau μ) {i1 i2 j : ℕ} (hi : i1 < i2)
    (hcell : (i2, j) ∈ μ) (hp : (T i1 j).IsPositive) : T i1 j ≠ T i2 j := fun heq =>
  absurd (T.col_isNegative hi hcell heq) ((SuperLetter.isPositive_iff_not_isNegative _).1 hp)

/-- Two cells of one row carrying the same negative letter do not occur. -/
theorem ne_of_isNegative_of_row (T : SuperYoungTableau μ) {i j1 j2 : ℕ} (hj : j1 < j2)
    (hcell : (i, j2) ∈ μ) (hn : (T i j1).IsNegative) : T i j1 ≠ T i j2 := fun heq =>
  (SuperLetter.isPositive_iff_not_isNegative _).1 (T.row_isPositive hj hcell heq) hn

end SuperYoungTableau

/-- A row of a Young diagram is contiguous, so weak increase between *adjacent* cells of a row
chains to weak increase between any two: this is the row half of the first preliminary of the
proof of `HJO.Sym.superTableauOfPair_bijective`. -/
theorem le_of_adjacent_row {μ : YoungDiagram} {T : ℕ → ℕ → SuperLetter}
    (h : ∀ i j : ℕ, (i, j) ∈ μ → (i, j + 1) ∈ μ → T i j ≤ T i (j + 1)) {i : ℕ} :
    ∀ {j1 j2 : ℕ}, j1 ≤ j2 → (i, j2) ∈ μ → T i j1 ≤ T i j2 := by
  intro j1 j2
  induction j2 with
  | zero => intro hj _; rw [Nat.le_zero.1 hj]
  | succ j ih =>
    intro hj hcell
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hlt | rfl
    · have hj' : j1 ≤ j := by omega
      have hcell' : (i, j) ∈ μ := μ.up_left_mem le_rfl (Nat.le_succ j) hcell
      exact (ih hj' hcell').trans (h i j hcell' hcell)
    · exact le_rfl

/-- A column of a Young diagram is contiguous, so weak increase between adjacent cells of a column
chains to weak increase between any two. -/
theorem le_of_adjacent_col {μ : YoungDiagram} {T : ℕ → ℕ → SuperLetter}
    (h : ∀ i j : ℕ, (i, j) ∈ μ → (i + 1, j) ∈ μ → T i j ≤ T (i + 1) j) {j : ℕ} :
    ∀ {i1 i2 : ℕ}, i1 ≤ i2 → (i2, j) ∈ μ → T i1 j ≤ T i2 j := by
  intro i1 i2
  induction i2 with
  | zero => intro hi _; rw [Nat.le_zero.1 hi]
  | succ i ih =>
    intro hi hcell
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi) with hlt | rfl
    · have hi' : i1 ≤ i := by omega
      have hcell' : (i, j) ∈ μ := μ.up_left_mem (Nat.le_succ i) le_rfl hcell
      exact (ih hi' hcell').trans (h i j hcell' hcell)
    · exact le_rfl

namespace SuperYoungTableau

/-- **The definition of a super tableau, verbatim.** A filling of the diagram that
increases weakly between *adjacent* cells of a row and of a column, in which a letter repeated in a
column is negative and a letter repeated in a row is positive, and which is held at the least letter
off the diagram, is a super tableau. Rows and columns of a Young diagram being contiguous, the
adjacent conditions chain to the non-adjacent ones of the structure, which is the first preliminary
of the proof of `HJO.Sym.superTableauOfPair_bijective`. -/
def ofAdjacent {μ : YoungDiagram} (T : ℕ → ℕ → SuperLetter)
    (hrow : ∀ i j : ℕ, (i, j) ∈ μ → (i, j + 1) ∈ μ → T i j ≤ T i (j + 1))
    (hcol : ∀ i j : ℕ, (i, j) ∈ μ → (i + 1, j) ∈ μ → T i j ≤ T (i + 1) j)
    (hcolpos : ∀ i1 i2 j : ℕ, i1 < i2 → (i2, j) ∈ μ → T i1 j = T i2 j → (T i1 j).IsNegative)
    (hrowneg : ∀ i j1 j2 : ℕ, j1 < j2 → (i, j2) ∈ μ → T i j1 = T i j2 → (T i j1).IsPositive)
    (houtside : ∀ i j : ℕ, (i, j) ∉ μ → T i j = SuperLetter.mk 0 false) :
    SuperYoungTableau μ where
  entry := T
  row_weak' hj hcell := le_of_adjacent_row hrow hj.le hcell
  col_weak' hi hcell := le_of_adjacent_col hcol hi.le hcell
  col_isNegative' hi hcell heq := hcolpos _ _ _ hi hcell heq
  row_isPositive' hj hcell heq := hrowneg _ _ _ hj hcell heq
  outside' h := houtside _ _ h

@[simp]
theorem coe_ofAdjacent {μ : YoungDiagram} (T : ℕ → ℕ → SuperLetter)
    (hrow : ∀ i j : ℕ, (i, j) ∈ μ → (i, j + 1) ∈ μ → T i j ≤ T i (j + 1))
    (hcol : ∀ i j : ℕ, (i, j) ∈ μ → (i + 1, j) ∈ μ → T i j ≤ T (i + 1) j)
    (hcolpos : ∀ i1 i2 j : ℕ, i1 < i2 → (i2, j) ∈ μ → T i1 j = T i2 j → (T i1 j).IsNegative)
    (hrowneg : ∀ i j1 j2 : ℕ, j1 < j2 → (i, j2) ∈ μ → T i j1 = T i j2 → (T i j1).IsPositive)
    (houtside : ∀ i j : ℕ, (i, j) ∉ μ → T i j = SuperLetter.mk 0 false) :
    ⇑(ofAdjacent T hrow hcol hcolpos hrowneg houtside) = T :=
  rfl

/-- The empty diagram has exactly one super tableau, the empty filling: this is the base of the
recursion on the number of cells, and it shows the type is never empty. -/
instance instUniqueBot : Unique (SuperYoungTableau (⊥ : YoungDiagram)) where
  default :=
    { entry := fun _ _ => SuperLetter.mk 0 false
      row_weak' := fun _ hcell => absurd hcell (by simp)
      col_weak' := fun _ hcell => absurd hcell (by simp)
      col_isNegative' := fun _ hcell => absurd hcell (by simp)
      row_isPositive' := fun _ hcell => absurd hcell (by simp)
      outside' := fun _ => rfl }
  uniq T := SuperYoungTableau.ext fun i j => by
    rw [T.outside (by simp)]
    rfl

end SuperYoungTableau

/-! ### The monomial of a super tableau -/

/-- **The monomial of a super tableau** `z_T`: the product of the
variables `ζ_{T(c)}` of `HJO.Sym.superVar` over the cells `c` of the diagram, the empty product
being `1`. Only the values on the cells are read, so the fixed value a super tableau takes off the
diagram does not enter. -/
@[hjo "def_cm_super_tableau_monomial"]
noncomputable def superTableauMonomial (K : Type*) [CommRing K] (q : K) {μ : YoungDiagram}
    (T : SuperYoungTableau μ) : AlphabetSeries K :=
  ∏ c ∈ μ.cells, superVar q (T c.1 c.2)

/-- The monomial of the unique super tableau of the empty diagram is `1`: the empty product. -/
@[simp]
theorem superTableauMonomial_bot (K : Type*) [CommRing K] (q : K)
    (T : SuperYoungTableau (⊥ : YoungDiagram)) : superTableauMonomial K q T = 1 := by
  rw [superTableauMonomial, show (⊥ : YoungDiagram).cells = ∅ from rfl, Finset.prod_empty]

end HJO.Sym
