/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Combinatorics.Young.YoungDiagram
public meta import HJO.Attr

/-! # Partitions and the cell statistics of the modified Macdonald family

The combinatorial vocabulary the modified Macdonald family is stated with: a partition, its cells,
the weight of a cell, and the three statistics built from those weights -- the cell sum `B_μ`, the
inverted cell sum `B^*_μ` and the cell product `T_μ` -- together with the covering relation
`μ ← ν` and the parameter product `M`.

A partition is recorded by its Young diagram, Mathlib's `YoungDiagram`: the finite lower set of
`ℕ × ℕ` whose `i`-th row has `μ.rowLen i` cells. The sources' weakly decreasing, eventually zero
sequence `μ = (μ₁, μ₂, …)` is the sequence of row lengths, and `equivRowLenSeq` is the
identification: `YoungDiagram` is *equivalent* to the type of such sequences, so nothing is lost
and nothing is assumed by working with diagrams. Rows and columns are numbered from `0`, so the
sources' `μ_i` is `rowLen (i - 1)` and the sources' cell `(i, j)` is the pair `(i - 1, j - 1)`;
that index shift is made once, here.

## Main definitions

* `HJO.Sym.rowLenSeq`, `HJO.Sym.equivRowLenSeq`: a partition as a weakly decreasing, eventually
  zero sequence of nonnegative integers.
* `HJO.Sym.cells`, `HJO.Sym.cellWeight`: the cells of a partition and the weight `q^{j-1}u^{i-1}`
  of a cell.
* `HJO.Sym.cellSum` (`B_μ`), `HJO.Sym.cellSumInv` (`B^*_μ`), `HJO.Sym.cellProd` (`T_μ`).
* `HJO.Sym.Covers`: `μ` covers `ν`, the sources' `ν → μ`.
* `HJO.Sym.paramProduct`: `M = (1 - q)(1 - u)`.

## Main results

* `HJO.Sym.cellWeight_mul`: a cell weight is multiplicative in its parameter pair,
  `w_{q q', u u'}(c) = w_{q, u}(c) w_{q', u'}(c)`.
* `HJO.Sym.cellWeight_inv`, `HJO.Sym.cellSumInv_eq_cellSum_inv`: the inverse of a cell weight is
  the cell weight at the inverted parameters, and so `B^*_μ = B_μ(q⁻¹, u⁻¹)`.

## Implementation notes

The three notations the sources introduce alongside the cells are ones a Young diagram already
carries, so nothing here adds to them: `c ∈ μ` is the `SetLike` membership, `|μ|` is
`YoungDiagram.card`, and `ν ⊆ μ` is the lattice order `ν ≤ μ`, which *is* `cells ν ⊆ cells μ`.

Every statistic takes `q` and `u` as explicit arguments over a general coefficient type rather
than reading them off a fixed `ℚ(q, u)`. This is what lets the *inverted* statistics be spelled as
the same statistic at the inverted parameters: `B^*_μ = cellSum q⁻¹ u⁻¹ μ` and
`M̃ = paramProduct q⁻¹ u⁻¹`, so the parameter inversion of the sources needs no separate
vocabulary at the level of these scalars. For `M̃` that identification is definitional, the
inverted parameter product being an `abbrev` for the parameter product at `q⁻¹`, `u⁻¹`; for `B^*`
it is a lemma, `cellSumInv_eq_cellSum_inv`, the inverted cell sum summing the inverses of the cell
weights rather than reading the cell sum at inverted parameters. Neither identification is a `simp`
lemma: the results downstream are stated in both spellings at once -- `M̃ B^*_μ` is
`paramProduct q⁻¹ u⁻¹ * cellSumInv q u μ` -- so neither is a normal form to rewrite towards.

The two readings of a change of parameter pair are independent, neither a case of the other:
multiplicativity in the pair asks only that the coefficients form a commutative monoid, while
inverting a pair asks for the inversion of that monoid and is *not* the multiplicative reading at
an inverting pair -- a `DivisionCommMonoid` has no `q q⁻¹ = 1`, which is what lets `cellWeight_inv`
hold where a parameter vanishes.

## References

The definitions `HJO.Sym.rowLenSeq`, `HJO.Sym.cells`, `HJO.Sym.cellWeight`, `HJO.Sym.cellSum`,
`HJO.Sym.cellSumInv`, `HJO.Sym.cellProd`, `HJO.Sym.Covers` and `HJO.Sym.paramProduct`. The sources
are F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the
theory of Macdonald polynomials*, arXiv:1405.0316, J. Comb. **7** (2016) 671--714, where
`B_μ(q, t)`, `T_μ = t^{n(μ)}q^{n(μ')}` and `D_μ(q, t) = M B_μ(q, t) - 1` appear in Section 1 and
equation (1.10); and A. M. Garsia, M. Haiman and G. Tesler, *Explicit plethystic formulas for
Macdonald (q,t)-Kostka coefficients*, Sém. Lothar. Combin. **42** (1999), B42m, whose equation
(1.31) b) is the one-cell Pieri expansion the covering relation indexes. The sources' `t` is written
`u` here.
-/

@[expose] public section

namespace HJO.Sym

/-! ### A partition as a weakly decreasing, eventually zero sequence -/

section Partition

/-- The row lengths of a partition, as a sequence: `rowLenSeq μ i` is the sources' `μ_{i+1}`,
the number of cells in the `i`-th row. The sequence is weakly decreasing
(`rowLenSeq_antitone`) and zero from some point on (`rowLenSeq_finite_support`), and
`equivRowLenSeq` says that a partition *is* such a sequence. -/
@[hjo "def_ght_partition"]
def rowLenSeq (μ : YoungDiagram) : ℕ → ℕ := μ.rowLen

@[simp]
theorem rowLenSeq_apply (μ : YoungDiagram) (i : ℕ) : rowLenSeq μ i = μ.rowLen i := rfl

/-- A partition is weakly decreasing. -/
theorem rowLenSeq_antitone (μ : YoungDiagram) : Antitone (rowLenSeq μ) :=
  fun _ _ h => μ.rowLen_anti _ _ h

/-- A partition has only finitely many nonzero entries. -/
theorem rowLenSeq_finite_support (μ : YoungDiagram) : {i | rowLenSeq μ i ≠ 0}.Finite := by
  refine Set.Finite.subset (μ.cells.image Prod.fst).finite_toSet fun i hi => ?_
  simp only [Set.mem_ofPred_eq, rowLenSeq_apply, ← Nat.pos_iff_ne_zero,
    ← YoungDiagram.mem_iff_lt_rowLen] at hi
  exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i, 0), hi, rfl⟩)

/-- The partition attached to a weakly decreasing, eventually zero sequence `f`: the Young diagram
whose `i`-th row has `f i` cells. -/
noncomputable def ofRowLenSeq (f : ℕ → ℕ) (hf : Antitone f) (hfin : {i | f i ≠ 0}.Finite) :
    YoungDiagram where
  cells := {c ∈ hfin.toFinset ×ˢ Finset.range (f 0) | c.2 < f c.1}
  isLowerSet := by
    intro c d hcd hd
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Set.Finite.mem_toFinset,
      Finset.mem_range] at hd ⊢
    have h1 : d.1 ≤ c.1 := hcd.1
    have h2 : d.2 ≤ c.2 := hcd.2
    have h3 : f c.1 ≤ f d.1 := hf h1
    have h4 : f d.1 ≤ f 0 := hf (Nat.zero_le _)
    omega

@[simp]
theorem mem_ofRowLenSeq {f : ℕ → ℕ} {hf : Antitone f} {hfin : {i | f i ≠ 0}.Finite}
    {c : ℕ × ℕ} : c ∈ ofRowLenSeq f hf hfin ↔ c.2 < f c.1 := by
  have h4 : f c.1 ≤ f 0 := hf (Nat.zero_le _)
  simp only [ofRowLenSeq, ← YoungDiagram.mem_cells, Finset.mem_filter, Finset.mem_product,
    Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_range]
  omega

@[simp]
theorem rowLen_ofRowLenSeq {f : ℕ → ℕ} {hf : Antitone f} {hfin : {i | f i ≠ 0}.Finite} (i : ℕ) :
    (ofRowLenSeq f hf hfin).rowLen i = f i := by
  have h1 := (YoungDiagram.mem_iff_lt_rowLen (μ := ofRowLenSeq f hf hfin) (i := i) (j := f i))
  have h2 := (YoungDiagram.mem_iff_lt_rowLen (μ := ofRowLenSeq f hf hfin) (i := i)
    (j := (ofRowLenSeq f hf hfin).rowLen i))
  simp only [mem_ofRowLenSeq, lt_self_iff_false, false_iff, iff_false, not_lt] at h1 h2
  omega

/-- **A partition is a weakly decreasing sequence of nonnegative integers that is zero from some
point on.** The equivalence sends a Young diagram to its sequence of row lengths and a sequence to
the diagram whose `i`-th row has that many cells, so the two descriptions of a partition carry the
same information. The sequence is indexed from `0`, so its `i`-th entry is the sources'
`μ_{i+1}`. -/
@[hjo "def_ght_partition"]
noncomputable def equivRowLenSeq :
    YoungDiagram ≃ {f : ℕ → ℕ // Antitone f ∧ {i | f i ≠ 0}.Finite} where
  toFun μ := ⟨rowLenSeq μ, rowLenSeq_antitone μ, rowLenSeq_finite_support μ⟩
  invFun f := ofRowLenSeq f.1 f.2.1 f.2.2
  left_inv μ := by
    refine YoungDiagram.ext (Finset.ext fun c => ?_)
    obtain ⟨i, j⟩ := c
    simp [YoungDiagram.mem_iff_lt_rowLen]
  right_inv f := Subtype.ext (funext fun i => rowLen_ofRowLenSeq i)

end Partition

/-! ### The cells of a partition and their weights -/

/-- The cells of the partition `μ`, recorded by its Young diagram: the pairs `(i, j)` with
`j < μ.rowLen i`, which are the sources' cells `(i + 1, j + 1)` with `1 ≤ j + 1 ≤ μ_{i+1}`. The
size `|μ|` is `μ.card = (cells μ).card`, and the sources' `ν ⊆ μ` is `ν ≤ μ`, which is
`cells ν ⊆ cells μ`. -/
@[hjo "def_ght_cells"]
abbrev cells (μ : YoungDiagram) : Finset (ℕ × ℕ) := μ.cells

/-- The weight of a cell: `cellWeight q u (i, j) = q ^ j * u ^ i`, the sources'
`w(i + 1, j + 1) = q^{(j+1)-1} u^{(i+1)-1}` in the `0`-indexed cell coordinates of `cells`. The
exponent of `q` is the column index of the cell and the exponent of `u` is its row index. -/
@[hjo "def_ght_cell_weight"]
abbrev cellWeight {K : Type*} [CommMonoid K] (q u : K) (c : ℕ × ℕ) : K := q ^ c.2 * u ^ c.1

/-- **A cell weight is multiplicative in its parameter pair**:
`w_{q q', u u'}(c) = w_{q, u}(c) w_{q', u'}(c)`. The weight is the monomial `q^j u^i`, whose
exponents are read off the cell alone, so only the parameters multiply and nothing is asked of them
beyond commutativity. It is what makes the one-cell increment of a cover multiplicative in the
pair, hence what makes the increments at a pair and at its inverse cancel. -/
theorem cellWeight_mul {K : Type*} [CommMonoid K] (q u q' u' : K) (c : ℕ × ℕ) :
    cellWeight (q * q') (u * u') c = cellWeight q u c * cellWeight q' u' c := by
  simp only [cellWeight, mul_pow]
  exact mul_mul_mul_comm _ _ _ _

/-- **Inverting a cell weight inverts its parameters**: `w(c)⁻¹ = w_{q⁻¹, u⁻¹}(c)`. The inversion
of a monomial is termwise, so this asks nothing of `q` or `u` and holds where a parameter
vanishes, `0⁻¹` being `0`. It is what makes each inverted statistic the statistic at the inverted
parameters. -/
theorem cellWeight_inv {K : Type*} [DivisionCommMonoid K] (q u : K) (c : ℕ × ℕ) :
    (cellWeight q u c)⁻¹ = cellWeight q⁻¹ u⁻¹ c := by
  simp only [cellWeight, mul_inv, inv_pow]

/-- The cell sum of a partition: `cellSum q u μ = ∑ c ∈ cells μ, cellWeight q u c`, the sources'
`B_μ(q, u) = ∑_{(i,j) ∈ μ} q^{j-1} u^{i-1}` read on the `0`-indexed cells of `μ`. The inverted
cell sum `B^*_μ` is `cellSum q⁻¹ u⁻¹ μ`, and `cellSum u q μ` is the cell sum of the conjugate
partition. -/
@[hjo "def_ght_bmu"]
abbrev cellSum {K : Type*} [CommSemiring K] (q u : K) (μ : YoungDiagram) : K :=
  ∑ c ∈ cells μ, cellWeight q u c

/-- The inverted cell sum of a partition: `cellSumInv q u μ = ∑ c ∈ cells μ, (cellWeight q u c)⁻¹`,
the sources' `B^*_μ = ∑_{(i,j) ∈ μ} (q^{j-1} u^{i-1})⁻¹` read on the `0`-indexed cells of `μ`. It
is the cell sum of the *inverses* of the cell weights, not the inverse `(cellSum q u μ)⁻¹` of the
cell sum, and it equals `cellSum q⁻¹ u⁻¹ μ`, the value of `B_μ` after inverting both
parameters (`cellSumInv_eq_cellSum_inv`). -/
@[hjo "def_ght_bmu_star"]
abbrev cellSumInv {K : Type*} [Semifield K] (q u : K) (μ : YoungDiagram) : K :=
  ∑ c ∈ cells μ, (cellWeight q u c)⁻¹

/-- **The inverted cell sum is the cell sum at the inverted parameters**: `B^*_μ = B_μ(q⁻¹, u⁻¹)`.
The two spellings of `B^*_μ` are exchangeable with no hypothesis on `q` or `u`, the inversion of
a cell weight being termwise. -/
theorem cellSumInv_eq_cellSum_inv {K : Type*} [Semifield K] (q u : K) (μ : YoungDiagram) :
    cellSumInv q u μ = cellSum q⁻¹ u⁻¹ μ :=
  Finset.sum_congr rfl fun c _ => cellWeight_inv q u c

/-- The cell product of a partition: `cellProd q u μ = ∏ c ∈ cells μ, cellWeight q u c`, the
sources' `T_μ = ∏_{(i,j) ∈ μ} q^{j-1} u^{i-1} = u^{n(μ)} q^{n(μ')}` read on the `0`-indexed cells
of `μ`. Its value under the parameter inversion is `cellProd q⁻¹ u⁻¹ μ`, and `cellProd u q μ` is
the cell product of the conjugate partition. -/
@[hjo "def_ght_tmu"]
abbrev cellProd {K : Type*} [CommMonoid K] (q u : K) (μ : YoungDiagram) : K :=
  ∏ c ∈ cells μ, cellWeight q u c

/-- The partition `μ` **covers** the partition `ν`: `ν ⊆ μ` and `|μ| = |ν| + 1`, so the cells of
`μ` are those of `ν` together with one more. This is the sources' `ν → μ`, read as removing a
corner of `μ`, and `μ ← ν`, read as adding a corner to `ν`. The larger diagram is the first
argument, as in the English "`μ` covers `ν`"; on the lattice `YoungDiagram` the relation is
`ν ⋖ μ`. -/
@[hjo "def_ght_cover"]
abbrev Covers (μ ν : YoungDiagram) : Prop := ν ≤ μ ∧ μ.card = ν.card + 1

/-- The parameter product `M = (1 - q)(1 - u)`: the scalar of the plethystic displacement
`X + M/z` and the normalisation of the slope recursion. The inverted parameter product
`M̃ = (1 - q⁻¹)(1 - u⁻¹)` is `paramProduct q⁻¹ u⁻¹`. -/
@[hjo "def_Mparam"]
abbrev paramProduct {K : Type*} [CommRing K] (q u : K) : K := (1 - q) * (1 - u)

/-- The inverted parameter product `M̃ = (1 - q⁻¹)(1 - u⁻¹)`: the parameter product at the
inverted parameters, `paramProduct q⁻¹ u⁻¹`, and so no second object.

Stated over a field, since it is the only definition of this vocabulary that reads an inverse: over
a commutative ring `q⁻¹` is not available, and the library's `𝕜 = ℚ(q, u)` and its extension
`𝕜(q^{1/2})` are both fields. An `abbrev`, so that the lemmas already proved about
`paramProduct q⁻¹ u⁻¹` — `HJO.Sym.paramProduct_inv_eq_mul_inv` and
`HJO.Sym.inv_mul_paramProduct_inv` — apply to it with no rewriting. -/
@[hjo "def_Mtilde"]
abbrev paramProductInv {K : Type*} [Field K] (q u : K) : K := paramProduct q⁻¹ u⁻¹

end HJO.Sym
