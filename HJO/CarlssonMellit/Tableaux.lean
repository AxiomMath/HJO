/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Young.SemistandardTableau
public import Mathlib.Data.Multiset.Sort
public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # Tableaux, their content and monomial, the monomial symmetric functions, and dominance

The expansion of a characteristic series into monomial symmetric functions, and the triangularity
of that expansion, need five notions this file supplies: the standard Young tableaux inside
`Mathlib`'s semistandard ones, the content of a tableau and the monomial it carries, the monomial
symmetric function `m_λ` of a partition, and the dominance order on partitions of a fixed number.

## Main definitions

* `HJO.Sym.IsStandard`, `HJO.Sym.SYT`: `SYT(D)`.
* `SemistandardYoungTableau.content`, `SemistandardYoungTableau.wt`: `ct(T)`.
* `HJO.Sym.ssytMonomial`: `x_T`.
* `HJO.Sym.msymmSeries`: `m_λ`.
* `HJO.Sym.partialSum`, `HJO.Sym.Dominates`: the dominance order `μ ⪰ λ`.

## Implementation notes

`Mathlib`'s `YoungDiagram` and `SemistandardYoungTableau` are used unchanged, with their `0`-based
cells and their `0`-based entries: the usual tableau values `1, …, n` are `0, …, n - 1` here, so
a standard tableau is a bijection from the cells onto `Finset.range μ.card` and the content is
indexed from `0`, matching the `0`-based alphabet `x_{a+1} = MvPowerSeries.X a`. That choice is
what makes `ct(T)` and the multidegree of `x_T` the same function, which is
`SemistandardYoungTableau.wt_apply`.

`m_λ` is *not* `MvPolynomial.msymm`. The symmetric function `m_λ` lives in `P = 𝕂⟦x₁, x₂, …⟧`, a
power series in an infinite alphabet, while `MvPolynomial.msymm` is a finite sum over a `Fintype` of
variables; no finite-variable polynomial expresses the infinite-alphabet object, so the definition
here is the coefficient indicator: the coefficient of the monomial `x^α` is `1` exactly when the
multiset of nonzero entries of `α` is the multiset of parts of `λ`. `Finsupp.support` contains
precisely the indices where `α` is nonzero, so that multiset is `α.support.val.map α` with nothing
to filter.

Dominance is the relation, not an order instance: reflexivity and transitivity are proved, and the
antisymmetry a `PartialOrder` would need is the separate statement that the partial sums determine
the partition. Parts are read off `p.parts.sort (· ≥ ·)`, the nonincreasing listing, so
`partialSum p i` is the usual `λ₁ + ⋯ + λ_i` with the extension by zeros past the length built
in by `List.take`.

## References

This file formalises `HJO.Sym.IsStandard`, `SemistandardYoungTableau.content`,
`HJO.Sym.ssytMonomial`, `HJO.Sym.msymmSeries` and `HJO.Sym.Dominates`.
-/

@[expose] public section

open Finset

/-! ### The content and the monomial of a semistandard tableau -/

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- **The content of a tableau** `ct(T)`: its `a`-th entry is the number of cells carrying the value
`a`. The usual content is indexed from `1` and reads the values `1, …, n`; entries here are
`Mathlib`'s, indexed from `0`, so `content T a` is the usual `ct(T)_{a+1}`. -/
@[hjo "def_sf_ssyt_content"]
def content (T : SemistandardYoungTableau μ) (a : ℕ) : ℕ :=
  #{c ∈ μ.cells | T c.1 c.2 = a}

/-- **The content vanishes off the values taken**, so only finitely many of its entries are
nonzero, as the definition of the content requires. -/
@[hjo "def_sf_ssyt_content"]
theorem content_eq_zero (T : SemistandardYoungTableau μ) {a : ℕ}
    (h : ∀ c ∈ μ.cells, T c.1 c.2 ≠ a) : content T a = 0 := by
  rw [content, card_eq_zero]
  exact filter_eq_empty_iff.2 fun {c} hc => h c hc

/-- **The content sums to the number of cells**: every cell carries exactly one value, so the
fibres of `T` partition the cells. This is "the entries sum to the number of cells of `D`", read
over any window containing all the values. -/
@[hjo "def_sf_ssyt_content"]
theorem sum_content (T : SemistandardYoungTableau μ) {N : ℕ}
    (h : ∀ c ∈ μ.cells, T c.1 c.2 < N) : ∑ a ∈ range N, content T a = μ.card := by
  rw [YoungDiagram.card]
  exact (card_eq_sum_card_fiberwise fun c hc => mem_range.2 (h c hc)).symm

/-- **The multidegree of a tableau**: the exponent vector attaching to each value the number of
cells carrying it. It is the content, by `wt_apply`, in the shape the monomial `x_T` needs. -/
noncomputable def wt (T : SemistandardYoungTableau μ) : ℕ →₀ ℕ :=
  ∑ c ∈ μ.cells, Finsupp.single (T c.1 c.2) 1

/-- The multidegree of a tableau *is* its content. -/
@[simp]
theorem wt_apply (T : SemistandardYoungTableau μ) (a : ℕ) : wt T a = content T a := by
  rw [wt, content, Finset.sum_apply']
  simp [Finsupp.single_apply, Finset.sum_boole]

end SemistandardYoungTableau

namespace HJO.Sym

/-! ### Standard Young tableaux -/

/-- **A semistandard tableau is standard** when its entries run over each value once: the usual
`T ∈ SSYT(D)` that is a bijection from `D` onto `\{1, …, n\}`, with `n = #D`, read at `Mathlib`'s
`0`-based entries so that the target is `Finset.range #D`. -/
@[hjo "def_cm_syt"]
def IsStandard {μ : YoungDiagram} (T : SemistandardYoungTableau μ) : Prop :=
  Set.BijOn (fun c : ℕ × ℕ => T c.1 c.2) ↑μ.cells ↑(range μ.card)

/-- **The standard Young tableaux of a diagram** `SYT(D)`: the semistandard tableaux whose entries
biject onto the values. -/
@[hjo "def_cm_syt"]
def SYT (μ : YoungDiagram) : Type :=
  {T : SemistandardYoungTableau μ // IsStandard T}

namespace IsStandard

variable {μ : YoungDiagram} {T : SemistandardYoungTableau μ}

/-- A standard tableau takes each cell to a value below the number of cells: the usual
`T(c) ∈ \{1, …, n\}`, lowered by one. -/
theorem lt_card (h : IsStandard T) {c : ℕ × ℕ} (hc : c ∈ μ.cells) : T c.1 c.2 < μ.card :=
  mem_range.1 (by simpa using h.1 (by simpa using hc))

/-- A standard tableau is injective on the cells: no value is repeated. -/
theorem injOn (h : IsStandard T) :
    Set.InjOn (fun c : ℕ × ℕ => T c.1 c.2) ↑μ.cells :=
  h.2.1

/-- Every value below the number of cells is attained: the usual surjectivity onto
`\{1, …, n\}`. -/
theorem exists_eq (h : IsStandard T) {a : ℕ} (ha : a < μ.card) :
    ∃ c ∈ μ.cells, T c.1 c.2 = a := by
  obtain ⟨c, hc, hca⟩ := h.2.2 (by simpa using mem_range.2 ha)
  exact ⟨c, by simpa using hc, hca⟩

/-- **Each value of a standard tableau is attained exactly once**: its content is `1` below the
number of cells. This is the form the column extraction of the descent set uses, and it separates
`SYT` from `SSYT`, whose contents are arbitrary. -/
theorem content_eq_one (h : IsStandard T) {a : ℕ} (ha : a < μ.card) :
    SemistandardYoungTableau.content T a = 1 := by
  obtain ⟨c, hc, hca⟩ := h.exists_eq ha
  rw [SemistandardYoungTableau.content, card_eq_one]
  refine ⟨c, eq_singleton_iff_unique_mem.2 ⟨mem_filter.2 ⟨hc, hca⟩, fun b hb => ?_⟩⟩
  obtain ⟨hbm, hba⟩ := mem_filter.1 hb
  exact h.injOn (by simpa using hbm) (by simpa using hc) (show T b.1 b.2 = T c.1 c.2 by
    rw [hba, hca])

end IsStandard

/-! ### The monomial of a tableau -/

/-- **The monomial of a tableau** `x_T = ∏_{c ∈ D} x_{T(c)}`, the empty product being `1`: the
monomial of `P` whose exponent vector is the multidegree of `T`, hence whose exponent at the value
`a` is the content `ct(T)_a`. -/
@[hjo "def_cm_ssyt_monomial"]
noncomputable def ssytMonomial (K : Type*) [CommRing K] {μ : YoungDiagram}
    (T : SemistandardYoungTableau μ) : AlphabetSeries K :=
  MvPowerSeries.monomial T.wt 1

/-- **The coefficients of `x_T`**: it is the monomial at the multidegree of `T`, so its coefficient
is `1` there and `0` elsewhere. -/
@[hjo "def_cm_ssyt_monomial"]
theorem coeff_ssytMonomial (K : Type*) [CommRing K] {μ : YoungDiagram}
    (T : SemistandardYoungTableau μ) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α (ssytMonomial K T) = if α = T.wt then 1 else 0 := by
  rw [ssytMonomial, MvPowerSeries.coeff_monomial]

/-- The exponent of `x_T` at the value `a` is the content of `T` at `a`: this is the defining
"product of `x_{T(c)}` over the cells", read through the multiplicities. -/
theorem wt_ssytMonomial {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (a : ℕ) :
    T.wt a = SemistandardYoungTableau.content T a :=
  T.wt_apply a

/-! ### The monomial symmetric functions -/

/-- **The monomial symmetric function** `m_λ ∈ P`: the sum of the monomials `x^α` over those
exponent vectors `α` whose nonzero entries, listed in nonincreasing order, form `λ`. Written as its
coefficient indicator, which is what the clause "each such monomial arises from exactly one `α`"
says: the coefficient at `α` is `1` when the multiset of nonzero entries of `α` is the multiset of
parts of `λ`, and `0` otherwise.

This is *not* `MvPolynomial.msymm`: that is a finite sum over a `Fintype` of variables, while `P`
is a power series ring in an infinite alphabet and `m_λ` has infinitely many terms. -/
@[hjo "def_sf_msymm"]
noncomputable def msymmSeries (K : Type*) [CommRing K] {d : ℕ} (μ : Nat.Partition d) :
    AlphabetSeries K :=
  fun α => if α.support.val.map α = μ.parts then 1 else 0

/-- **The coefficients of `m_λ`**: `1` on the exponent vectors whose nonzero entries form the parts
of `λ`, and `0` elsewhere. `Finsupp.support` is exactly the set of indices where `α` is nonzero, so
`α.support.val.map α` is the multiset of nonzero entries with nothing to filter. -/
@[hjo "def_sf_msymm"]
theorem coeff_msymmSeries (K : Type*) [CommRing K] {d : ℕ} (μ : Nat.Partition d) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α (msymmSeries K μ) =
      if α.support.val.map α = μ.parts then 1 else 0 :=
  rfl

/-- **Every monomial of `m_λ` has total degree `d`**, since the nonzero entries of `α` sum to the
sum of the parts of `λ`. -/
@[hjo "def_sf_msymm"]
theorem coeff_msymmSeries_eq_zero_of_sum_ne (K : Type*) [CommRing K] {d : ℕ}
    (μ : Nat.Partition d) {α : ℕ →₀ ℕ} (h : (α.sum fun _ n => n) ≠ d) :
    MvPowerSeries.coeff α (msymmSeries K μ) = 0 := by
  rw [coeff_msymmSeries, ite_eq_right_iff]
  intro hα
  exact absurd (show (α.sum fun _ n => n) = d by
    rw [Finsupp.sum, Finset.sum_eq_multiset_sum, hα, μ.parts_sum]) h

/-- **A value check separating two partitions of the same number.** At `d = 2` the coefficient of
`x₁x₂` is `1` in `m_{(1,1)}` and `0` in `m_{(2)}`: the exponent vector `(1, 1)` has nonzero entries
`\{1, 1\}`, which is the parts of the first partition and not of the second. Reading the *support*
of `α` rather than its multiset of values — the off-by-one this shape invites — would make both
coefficients equal. -/
theorem coeff_msymmSeries_example (K : Type*) [CommRing K] [Nontrivial K]
    {p q : Nat.Partition 2} (hp : p.parts = {1, 1}) (hq : q.parts = {2}) :
    MvPowerSeries.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) (msymmSeries K p) = 1 ∧
      MvPowerSeries.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) (msymmSeries K q) = 0 := by
  have hsupp : (Finsupp.single 0 1 + Finsupp.single 1 1 : ℕ →₀ ℕ).support = {0, 1} := by
    ext i; simp [Finsupp.single_apply]; omega
  refine ⟨?_, ?_⟩
  · rw [coeff_msymmSeries, hp, hsupp]
    norm_num [Finsupp.single_apply]
  · rw [coeff_msymmSeries, hq, hsupp]
    norm_num [Finsupp.single_apply]
    decide

/-! ### The dominance order on partitions -/

/-- The sum of the first `i` parts of a partition, listed in nonincreasing order: the usual
`λ₁ + ⋯ + λ_i`, the extension of `λ` by zeros past its length being `List.take`'s truncation. -/
def partialSum {d : ℕ} (p : Nat.Partition d) (i : ℕ) : ℕ :=
  ((p.parts.sort (· ≥ ·)).take i).sum

/-- No parts sum to nothing. -/
@[simp]
theorem partialSum_zero {d : ℕ} (p : Nat.Partition d) : partialSum p 0 = 0 := by
  simp [partialSum]

/-- Past the length of a partition every partial sum is the whole of `d`: this is the extension by
zeros that the definition of dominance prescribes. -/
theorem partialSum_of_card_le {d : ℕ} (p : Nat.Partition d) {i : ℕ}
    (h : Multiset.card p.parts ≤ i) : partialSum p i = d := by
  rw [partialSum, List.take_of_length_le (by simpa using h), ← Multiset.sum_coe,
    Multiset.sort_eq, p.parts_sum]

/-- **The dominance order** `μ ⪰ λ` on the partitions of one and the same `d`: every partial sum of
`μ` is at least the corresponding partial sum of `λ`. -/
@[hjo "def_sf_dominance"]
def Dominates {d : ℕ} (p q : Nat.Partition d) : Prop :=
  ∀ i, partialSum q i ≤ partialSum p i

/-- Dominance is reflexive. -/
@[refl]
theorem Dominates.refl {d : ℕ} (p : Nat.Partition d) : Dominates p p := fun _ => le_rfl

/-- Dominance is transitive. -/
theorem Dominates.trans {d : ℕ} {p q r : Nat.Partition d} (hpq : Dominates p q)
    (hqr : Dominates q r) : Dominates p r := fun i => (hqr i).trans (hpq i)

/-- **A value check of the direction of the order**: the partition `(1, 1, 1, 1)` of `4` does not
dominate `(2, 1, 1)`, their first partial sums being `1` and `2`. Reading `⪰` in the other direction
would make the finer partition the larger one, which is the error this rules out. -/
theorem not_dominates_example {p q : Nat.Partition 4}
    (hp : p.parts.sort (· ≥ ·) = [1, 1, 1, 1]) (hq : q.parts.sort (· ≥ ·) = [2, 1, 1]) :
    ¬Dominates p q := fun h => by
  have h1 := h 1
  rw [partialSum, partialSum, hp, hq] at h1
  simp at h1

end HJO.Sym
