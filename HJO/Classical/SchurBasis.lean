/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.BenderKnuth
public import HJO.Classical.IotaMsymm
public meta import HJO.Attr

/-! # The Schur series and their triangularity against the monomial series

Three results: the Schur series `sch(D)` of a Young diagram; its expansion
`sch(D) = ∑_μ K_D(μ) m_μ` (`HJO.Sym.schurSeries_eq_sum_msymm`); and the consequence that the
`sch(D_λ)`, indexed by the partitions `λ` of `n`, are a basis of the span `W_n` of the `m_μ`
(`HJO.Sym.exists_basis_schurSeries`).

## Main definitions

* `HJO.Sym.schurSeries`: `sch(D)`.

## Main statements

* `HJO.Sym.kostka_eq_partitionExponent`: `K_D(α) = K_D(μ_α)`, the sorting step.
* `HJO.Sym.schurSeries_eq_sum_msymm`.
* `HJO.Sym.exists_basis_schurSeries`.

## Implementation notes

**`sch(D)` is written by its coefficients, as `HJO.Sym.msymmSeries` is.** The `∑_T x_T`
is an infinite sum in the power series ring, well defined precisely because each coefficient is a
finite count — and that count is the Kostka number, since `x_T` is the monomial at the multidegree
of `T` (`HJO.Sym.coeff_ssytMonomial`). So `coeff α (sch D) = K_D(α)` *is* the definition, and
`HJO.Sym.schurSeries_eq_sum_msymm` becomes the identification of the other side's coefficients.

**The sorting step is `HJO.Sym.kostka_eq_of_map_range`, not `HJO.Sym.kostka_comp`.** The usual
argument carries `α` to the partition `μ_α` by "some permutation of the positive integers fixing all
but finitely many of them". `HJO.Sym.sortIndex` does carry `x^α` to `x^{μ_α}`, but it is *not*
finitely supported — it matches the two cofinite complements by a `Denumerable` equivalence — so
`HJO.Sym.kostka_comp` does not apply to it. What does apply is the engine behind that lemma: `α` and
`x^{μ_α}` agree above a common window and have the same multiset of entries inside it, which is
exactly `kostka_eq_of_map_range`'s hypothesis. `HJO.Sym.map_range_val` is the computation of that
multiset: the nonzero values, padded with zeros.

**`HJO.Sym.exists_basis_schurSeries` needs no hypothesis on `𝕜` beyond being a commutative ring.**
The diagonal coefficients of the expansion are all `1` (`HJO.Sym.kostka_partitionExponent`), and `1`
is a unit in any ring; the characteristic-zero and field hypotheses that
`HJO.Sym.exists_basis_iota_pmonomial` needs come from *its* diagonal being a product of multiplicity
factorials, and have no analogue here. The order is the *reverse* of the lexicographic one, because
`HJO.Sym.dominates_of_kostka_ne_zero` puts the correction terms lexicographically *below* the index.

## References

This file formalises `HJO.Sym.schurSeries`, `HJO.Sym.schurSeries_eq_sum_msymm` and
`HJO.Sym.exists_basis_schurSeries`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The multiset of entries of a window -/

/-- **The entries of an exponent vector over a window containing its support**: the nonzero values,
padded with zeros. -/
theorem map_range_val (α : ℕ →₀ ℕ) {M : ℕ} (hM : α.support ⊆ range M) :
    Multiset.map α (range M).val
      = Multiset.replicate (M - #α.support) 0 + α.support.val.map α := by
  have hle : α.support.val ≤ (range M).val := Finset.val_le_iff_val_subset.2 hM
  have hzero : ∀ x ∈ (range M \ α.support).val, α x = (0 : ℕ) := by
    intro x hx
    rw [← Finset.mem_def, Finset.mem_sdiff] at hx
    exact Finsupp.notMem_support_iff.1 hx.2
  have h0 : Multiset.map α (range M \ α.support).val
      = Multiset.replicate (M - #α.support) 0 := by
    rw [Multiset.map_congr rfl hzero, Multiset.map_const',
      show (range M \ α.support).val.card = #(range M \ α.support) from rfl,
      Finset.card_sdiff, Finset.inter_eq_left.2 hM, Finset.card_range]
  rw [show (range M).val = (range M \ α.support).val + α.support.val by
      rw [Finset.sdiff_val, Multiset.sub_add_cancel hle], Multiset.map_add, h0]

/-- **The Kostka number is read at a partition**: `K_D(α) = K_D(μ_α)`, where `μ_α` is the partition
formed by the nonzero entries of `α`. The two sequences agree above a window containing both
supports and have the same multiset of entries inside it, which is `HJO.Sym.kostka_comp`'s
mechanism. -/
theorem kostka_eq_partitionExponent (D : YoungDiagram) {d : ℕ} {α : ℕ →₀ ℕ} (h : degHom α = d) :
    kostka D α = kostka D (partitionExponent (partitionOfValues h)) := by
  classical
  set β := partitionExponent (partitionOfValues h) with hβ
  have hvals : β.support.val.map β = α.support.val.map α := by
    rw [hβ, map_partitionExponent, parts_partitionOfValues]
  have hcard : #β.support = #α.support := by
    have h1 : Multiset.card (Multiset.map β β.support.val) = #β.support := Multiset.card_map _ _
    have h2 : Multiset.card (Multiset.map α α.support.val) = #α.support := Multiset.card_map _ _
    rw [← h1, ← h2, hvals]
  obtain ⟨M₁, hM₁⟩ := Finset.exists_nat_subset_range α.support
  obtain ⟨M₂, hM₂⟩ := Finset.exists_nat_subset_range β.support
  have hα : α.support ⊆ range (max M₁ M₂) :=
    hM₁.trans (Finset.range_subset_range.2 (le_max_left _ _))
  have hβ' : β.support ⊆ range (max M₁ M₂) :=
    hM₂.trans (Finset.range_subset_range.2 (le_max_right _ _))
  refine kostka_eq_of_map_range D (max M₁ M₂) α β (fun a ha => ?_) ?_
  · rw [Finsupp.notMem_support_iff.1 fun hc => absurd (mem_range.1 (hα hc)) (by omega),
      Finsupp.notMem_support_iff.1 fun hc => absurd (mem_range.1 (hβ' hc)) (by omega)]
  · rw [map_range_val α hα, map_range_val β hβ', hcard, hvals]

/-! ### The Schur series -/

/-- **The Schur series of a Young diagram** `sch(D) = ∑_{T ∈ SSYT(D)} x_T`.
The sum is written by its coefficients, which is what makes it an element of `𝒫` at all: `x_T` is
the monomial at the multidegree of `T` (`HJO.Sym.coeff_ssytMonomial`), so the coefficient of
`sch(D)` at `x^α` is the number of `T ∈ SSYT(D)` of content `α`, that is `K_D(α)`, finite by
`HJO.Sym.finite_ssyt_wt_eq`. This is the same shape as `HJO.Sym.msymmSeries`, and for the same
reason: `𝒫` is a power series ring in infinitely many letters, so an infinite family of monomials is
presented coefficientwise. -/
@[hjo "def_cm_schur_series"]
noncomputable def schurSeries (K : Type*) [CommRing K] (D : YoungDiagram) : AlphabetSeries K :=
  fun α => (kostka D α : K)

/-- **The coefficients of `sch(D)`** are the Kostka numbers. -/
@[hjo "def_cm_schur_series"]
theorem coeff_schurSeries (K : Type*) [CommRing K] (D : YoungDiagram) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α (schurSeries K D) = (kostka D α : K) := rfl

/-- **The coefficient of `sch(D)` at `x^α` counts the tableaux whose monomial is `x^α`**, which is
the `∑_{T ∈ SSYT(D)} x_T` read at one monomial: `x_T` has coefficient `1` at `x^{ct(T)}`
and `0` elsewhere. -/
@[hjo "def_cm_schur_series"]
theorem coeff_schurSeries_eq_ncard (K : Type*) [CommRing K] (D : YoungDiagram) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α (schurSeries K D)
      = (({T : SemistandardYoungTableau D | α = T.wt}.ncard : ℕ) : K) := by
  rw [coeff_schurSeries, kostka]
  exact congrArg _ (congrArg Set.ncard (Set.ext fun T => eq_comm))

/-- **A tableau of shape `D` has content of total degree `#D`**, so the Kostka number vanishes off
that degree. -/
theorem kostka_eq_zero_of_degHom_ne (D : YoungDiagram) {n : ℕ} (hD : D.card = n) {α : ℕ →₀ ℕ}
    (h : degHom α ≠ n) : kostka D α = 0 := by
  classical
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range α.support
  refine (Set.ncard_eq_zero (finite_ssyt_wt_eq D α)).2 (Set.eq_empty_iff_forall_notMem.2 ?_)
  intro T hT
  have hT' : T.wt = α := hT
  have hlt : ∀ c ∈ D.cells, T c.1 c.2 < N := by
    intro c hc
    refine mem_range.1 (hN (Finsupp.mem_support_iff.2 ?_))
    rw [← hT', SemistandardYoungTableau.wt_apply, SemistandardYoungTableau.content,
      ← Nat.pos_iff_ne_zero, card_pos]
    exact ⟨c, mem_filter.2 ⟨hc, rfl⟩⟩
  have hsum := SemistandardYoungTableau.sum_content T hlt
  rw [hD] at hsum
  have hcontent : ∀ a, SemistandardYoungTableau.content T a = α a := fun a => by
    rw [← SemistandardYoungTableau.wt_apply, hT']
  rw [sum_congr rfl fun a _ => hcontent a] at hsum
  refine h ?_
  rw [degHom_apply, Finset.sum_subset hN fun a _ ha => Finsupp.notMem_support_iff.1 ha, hsum]

/-- **The Schur series is the Kostka combination of the monomial
series.** A monomial of total degree other than `n` occurs in neither side; and at one of total
degree `n` the left side is `K_D(α) = K_D(μ_α)`, while the right side is the single contribution
of `m_{μ_α}`. -/
@[hjo "lem_sf_sch_msymm_expansion"]
theorem schurSeries_eq_sum_msymm (K : Type*) [CommRing K] {n : ℕ} (D : YoungDiagram)
    (hD : D.card = n) :
    schurSeries K D
      = ∑ μ : Nat.Partition n, ((kostka D (partitionExponent μ) : ℕ) : K) • msymmSeries K μ := by
  classical
  refine MvPowerSeries.ext fun α => ?_
  rw [coeff_schurSeries, map_sum]
  simp only [MvPowerSeries.coeff_smul]
  by_cases hd : degHom α = n
  · rw [Finset.sum_eq_single (partitionOfValues hd) (fun q _ hne => ?_)
      (fun hc => absurd (mem_univ _) hc)]
    · rw [coeff_msymmSeries, ite_eq_left (parts_partitionOfValues hd).symm, mul_one,
        kostka_eq_partitionExponent D hd]
    · rw [coeff_msymmSeries, ite_eq_right fun hq => hne (Nat.Partition.ext
        (hq.symm.trans (parts_partitionOfValues hd).symm)), mul_zero]
  · rw [kostka_eq_zero_of_degHom_ne D hD hd, Nat.cast_zero]
    refine (Finset.sum_eq_zero fun q _ => ?_).symm
    refine mul_eq_zero_of_right _ (coeff_msymmSeries_eq_zero_of_sum_ne K q ?_)
    exact fun hc => hd ((degHom_apply α).trans hc)

/-! ### The Schur series of the diagrams of the partitions are a basis -/

/-- The reverse of the lexicographic order on the partitions of `d`: the order for which the
correction terms of the Schur expansion lie above the index. -/
def partitionGt {d : ℕ} (p q : Nat.Partition d) : Prop := partitionLt q p

instance {d : ℕ} : IsStrictTotalOrder (Nat.Partition d) partitionGt where
  irrefl p := not_partitionLex_self (partitionDiagram p)
  trans _ _ _ hpq hqs := partitionLex_trans hqs hpq
  trichotomous p q hpq hqp := by
    rcases partitionLex_trichotomy (partitionDiagram q) (partitionDiagram p) with h | h | h
    · exact absurd h hpq
    · exact (partitionDiagram_injective h).symm
    · exact absurd h hqp

theorem schurSeries_mem_msymmSpan (K : Type*) [CommRing K] {n : ℕ} (p : Nat.Partition n) :
    schurSeries K (partitionDiagram p) ∈ msymmSpan K n := by
  rw [schurSeries_eq_sum_msymm K _ (card_partitionDiagram p)]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (msymmSeries_mem_msymmSpan K q)

/-- **The correction term of the Schur expansion lies lexicographically below the index.** -/
theorem schurSeries_sub_mem_span (K : Type*) [CommRing K] {n : ℕ} (p : Nat.Partition n) :
    schurSeries K (partitionDiagram p) - (1 : K) • msymmSeries K p
      ∈ Submodule.span K ((fun q : Nat.Partition n => msymmSeries K q) '' {q | partitionGt p q}) :=
  by
  classical
  rw [schurSeries_eq_sum_msymm K _ (card_partitionDiagram p),
    ← Finset.sum_erase_add _ _ (mem_univ p), kostka_partitionExponent p, Nat.cast_one,
    add_sub_cancel_right]
  refine Submodule.sum_mem _ fun q hq => ?_
  by_cases hzero : kostka (partitionDiagram p) (partitionExponent q) = 0
  · rw [hzero, Nat.cast_zero, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, ?_, rfl⟩)
    exact partitionLex_of_dominates (dominates_of_kostka_ne_zero p q hzero)
      (Finset.mem_erase.1 hq).1

/-- **The Schur series of the diagrams of the partitions of `n` are a basis of
the monomial span.** The expansion is triangular over the basis `(m_μ)` of `W_n` for the reverse of
the lexicographic order, with every diagonal coefficient `1` (`HJO.Sym.kostka_partitionExponent`),
so `Module.Basis.exists_basis_of_triangular` turns it into a basis. -/
@[hjo "lem_sf_sch_basis"]
theorem exists_basis_schurSeries (K : Type*) [CommRing K] (n : ℕ) :
    ∃ b : Module.Basis (Nat.Partition n) K (msymmSpan K n),
      ∀ p : Nat.Partition n, (b p : AlphabetSeries K) = schurSeries K (partitionDiagram p) := by
  classical
  have htri : ∀ p : Nat.Partition n,
      (⟨schurSeries K (partitionDiagram p), schurSeries_mem_msymmSpan K p⟩ : msymmSpan K n)
          - (1 : K) • msymmBasis K n p
        ∈ Submodule.span K (⇑(msymmBasis K n) '' {q | partitionGt p q}) := by
    intro p
    refine mem_span_of_coe_mem_span _ _ ?_
    rw [show ⇑(msymmSpan K n).subtype '' (⇑(msymmBasis K n) '' {q | partitionGt p q})
        = (fun q : Nat.Partition n => msymmSeries K q) '' {q | partitionGt p q} by
      rw [Set.image_image]
      exact Set.image_congr fun q _ => coe_msymmBasis K q]
    simpa only [Submodule.coe_sub, SetLike.val_smul, coe_msymmBasis]
      using schurSeries_sub_mem_span K p
  obtain ⟨b, hb⟩ := exists_basis_of_triangular_of_sto (partitionGt (d := n)) (msymmBasis K n)
    (fun _ => isUnit_one) htri
  exact ⟨b, fun p => by rw [hb]⟩

end HJO.Sym
