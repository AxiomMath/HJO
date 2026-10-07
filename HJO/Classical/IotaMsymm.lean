/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import HJO.Classical.SortExponent
public import HJO.Classical.PmonomialBasis
public import HJO.Symmetric.TriangularBasis
public meta import HJO.Attr

/-! # The realised power-sum monomials expand triangularly in the monomial series

Three results. `ι(p_λ)` is a combination of the `m_μ` with `μ ⪰ λ` and a nonzero coefficient
at `m_λ` (`HJO.Sym.exists_triangular_msymm`); consequently the `ι(p_λ)`, indexed by the partitions
of `d`, are a basis of the span `W_d` of the `m_μ` (`HJO.Sym.exists_basis_iota_pmonomial`); and that
span is the image `ι(Λ_d)` of the graded piece (`HJO.Sym.map_lambdaComp_eq_msymmSpan`).

## Main definitions

* `HJO.Sym.msymmSpan`: `W_d`, the `𝕜`-span of the `m_μ` with `μ` a partition of `d`.
* `HJO.Sym.msymmBasis`: the `m_μ` as a basis of `W_d`.

## Main statements

* `HJO.Sym.iota_pmonomial_eq_sum_msymm`: the expansion `ι(p_λ) = ∑_μ R_μ m_μ`.
* `HJO.Sym.exists_triangular_msymm`.
* `HJO.Sym.exists_basis_iota_pmonomial`.
* `HJO.Sym.map_lambdaComp_eq_msymmSpan`.
* `HJO.Sym.isUnit_pmonomialMsymmCoeff`: the diagonal coefficient is a unit over any `ℚ`-algebra,
  which is what lets the last two dispense with the field hypothesis.

## Implementation notes

**The expansion is a coefficient identity, and the one thing it needs beyond
`HJO/Classical/IotaPmonomial.lean` is that a coefficient of `ι(p_λ)` may be read at a
partition.** That is `HJO.Sym.coeff_iota_pmonomial_eq_partitionOfValues`, the sorting permutation of
`HJO/Classical/SortExponent.lean`: at an `α` of total degree `d` the coefficient of `ι(p_λ)`
agrees with its coefficient at the exponent vector of the partition `μ_α` formed by the values of
`α`, and `m_{μ_α}` is the unique monomial series containing `x^α`. So `R_μ` is the coefficient at
`x^μ`, and the two coefficient facts already proved — `R_λ ≠ 0` and `R_μ ≠ 0 ⇒ μ ⪰ λ` — are exactly
the diagonal and the triangularity.

**The scalars `a_μ` of the triangular expansion are given as a function on *all* partitions of `d`
whose support is contained in `{μ : μ > λ}`.** The expansion attaches one `a_μ` to each `μ > λ`;
extending by zero is the same data, and it avoids a `Finset.filter` — hence a decidability instance
— in the statement.

**`HJO.Sym.exists_basis_iota_pmonomial` is stated as the existence of a bundled basis of `W_d` whose
underlying family is the `ι(p_λ)`,** which is how `Module.Basis.exists_basis_of_triangular` states
"this family is a basis" and asserts both halves at once: independence *and* spanning.

**The base of the last two statements is a `ℚ`-algebra and not a field.**
`Module.Basis.exists_basis_of_triangular` needs the diagonal coefficients to be *units*, and over a
ring a nonzero one need not be; over the field `𝕜 = ℚ(q,u)` of characteristic zero,
`isUnit_iff_ne_zero` closes the gap. But the diagonal coefficient is the cast of a *positive natural
number*
(`HJO.Sym.coeff_iota_pmonomial`), and such a cast is a unit in any `ℚ`-algebra —
`HJO.Sym.isUnit_pmonomialMsymmCoeff` — so a field is not needed and is not assumed. That matters
downstream: the Carlsson--Mellit lowering step needs the image of a graded piece over the
*polynomial* base `𝕜[y_1, …, y_k]`, not a field, and
`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter` would be out of reach with the field
hypothesis in place. A field of characteristic zero is a `ℚ`-algebra, so every use of the
field-based statement reads the general one unchanged.

## References

The triangularity of the power sums against the monomial symmetric functions:
`HJO.Sym.exists_triangular_msymm`, `HJO.Sym.exists_basis_iota_pmonomial` and
`HJO.Sym.map_lambdaComp_eq_msymmSpan`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### A triangular family indexed by a finite strict total order -/

/-- `Module.Basis.exists_basis_of_triangular` with the order presented as a strict total order
rather than as a `LinearOrder` instance: on `Nat.Partition d` the order is `HJO.Sym.partitionLex`,
which carries no instance, and a finite strict total order is a `LinearOrder` with no infinite
ascending chain. -/
theorem exists_basis_of_triangular_of_sto {J R W : Type*} [Ring R] [AddCommGroup W] [Module R W]
    [Finite J] (r : J → J → Prop) [IsStrictTotalOrder J r] (b : Module.Basis J R W)
    {v : J → W} {c : J → R} (hc : ∀ i, IsUnit (c i))
    (htri : ∀ i, v i - c i • b i ∈ Submodule.span R (⇑b '' {j | r i j})) :
    ∃ b' : Module.Basis J R W, ⇑b' = v := by
  classical
  let _ : LinearOrder J := linearOrderOfSTO r
  exact Module.Basis.exists_basis_of_triangular b hc htri

/-- The lexicographic order on the partitions of `d`, read through their diagrams. -/
def partitionLt {d : ℕ} (p q : Nat.Partition d) : Prop :=
  partitionLex (partitionDiagram p) (partitionDiagram q)

instance {d : ℕ} : IsStrictTotalOrder (Nat.Partition d) partitionLt where
  irrefl p := not_partitionLex_self (partitionDiagram p)
  trans _ _ _ := partitionLex_trans
  trichotomous p q hpq hqp := by
    rcases partitionLex_trichotomy (partitionDiagram p) (partitionDiagram q) with h | h | h
    · exact absurd h hpq
    · exact partitionDiagram_injective h
    · exact absurd h hqp

/-! ### The span of the monomial series -/

variable {K : Type*} [CommRing K] {ι : Lambda K →ₐ[K] AlphabetSeries K}

/-- **`W_d`, the `𝕜`-span of the monomial symmetric series of the partitions of `d`.** -/
noncomputable def msymmSpan (K : Type*) [CommRing K] (d : ℕ) : Submodule K (AlphabetSeries K) :=
  Submodule.span K (Set.range fun μ : Nat.Partition d => msymmSeries K μ)

/-- The monomial series are a basis of their span, being linearly independent. -/
noncomputable def msymmBasis (K : Type*) [CommRing K] (d : ℕ) :
    Module.Basis (Nat.Partition d) K (msymmSpan K d) :=
  Module.Basis.span (linearIndependent_msymmSeries K d)

@[simp]
theorem coe_msymmBasis (K : Type*) [CommRing K] {d : ℕ} (μ : Nat.Partition d) :
    (msymmBasis K d μ : AlphabetSeries K) = msymmSeries K μ :=
  Module.Basis.coe_span_apply (linearIndependent_msymmSeries K d) μ

theorem msymmSeries_mem_msymmSpan (K : Type*) [CommRing K] {d : ℕ} (μ : Nat.Partition d) :
    msymmSeries K μ ∈ msymmSpan K d :=
  Submodule.subset_span ⟨μ, rfl⟩

/-! ### The expansion -/

/-- **`R_μ`, the coefficient of `m_μ` in `ι(p_λ)`**: the coefficient of `ι(p_λ)` at the monomial
`x^μ`. -/
noncomputable def pmonomialMsymmCoeff (ι : Lambda K →ₐ[K] AlphabetSeries K) {d : ℕ}
    (p q : Nat.Partition d) : K :=
  MvPowerSeries.coeff (partitionExponent q) (ι (pmonomial K p))

/-- **The expansion of `ι(p_λ)` in the monomial series.** A monomial of total degree other than `d`
occurs in neither side; and at a monomial `x^α` of total degree `d` the left side has the
coefficient it has at `x^{μ_α}`, by the sorting permutation, while the right side has the single
contribution of `m_{μ_α}`. -/
theorem iota_pmonomial_eq_sum_msymm (hι : IsRealisation ι) {d : ℕ} (p : Nat.Partition d) :
    ι (pmonomial K p) = ∑ q : Nat.Partition d, pmonomialMsymmCoeff ι p q • msymmSeries K q := by
  classical
  refine MvPowerSeries.ext fun α => ?_
  rw [map_sum]
  simp only [MvPowerSeries.coeff_smul]
  by_cases hd : degHom α = d
  · rw [Finset.sum_eq_single (partitionOfValues hd) (fun q _ hne => ?_)
      (fun h => absurd (mem_univ _) h)]
    · rw [coeff_msymmSeries, ite_eq_left (parts_partitionOfValues hd).symm, mul_one,
        pmonomialMsymmCoeff, coeff_iota_pmonomial_eq_partitionOfValues hι p hd]
    · rw [coeff_msymmSeries, ite_eq_right fun hq => hne (Nat.Partition.ext
        (hq.symm.trans (parts_partitionOfValues hd).symm)), mul_zero]
  · rw [show MvPowerSeries.coeff α (ι (pmonomial K p)) = 0 from by_contra fun hne =>
      hd (degHom_of_coeff_iota_pmonomial_ne_zero hι p hne)]
    refine (Finset.sum_eq_zero fun q _ => ?_).symm
    refine (mul_eq_zero_of_right _ (coeff_msymmSeries_eq_zero_of_sum_ne K q ?_))
    exact fun h => hd ((degHom_apply α).trans h)

/-- `ι(p_λ)` lies in the span of the monomial series. -/
theorem iota_pmonomial_mem_msymmSpan (hι : IsRealisation ι) {d : ℕ} (p : Nat.Partition d) :
    ι (pmonomial K p) ∈ msymmSpan K d := by
  rw [iota_pmonomial_eq_sum_msymm hι]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (msymmSeries_mem_msymmSpan K q)

/-- **The correction term of the expansion lies above the index.** Subtracting the diagonal term
leaves a combination of the `m_μ` with `μ ⪰ λ` and `μ ≠ λ`, hence `μ > λ`
(`HJO.Sym.partitionLex_of_dominates`). -/
theorem iota_pmonomial_sub_mem_span (hι : IsRealisation ι) {d : ℕ} (p : Nat.Partition d) :
    ι (pmonomial K p) - pmonomialMsymmCoeff ι p p • msymmSeries K p
      ∈ Submodule.span K ((fun q : Nat.Partition d => msymmSeries K q) '' {q | partitionLt p q}) :=
  by
  classical
  rw [iota_pmonomial_eq_sum_msymm hι, ← Finset.sum_erase_add _ _ (mem_univ p), add_sub_cancel_right]
  refine Submodule.sum_mem _ fun q hq => ?_
  by_cases hzero : pmonomialMsymmCoeff ι p q = 0
  · rw [hzero, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, ?_, rfl⟩)
    exact partitionLex_of_dominates
      (dominates_of_coeff_iota_pmonomial_ne_zero hι p q hzero) (Ne.symm (Finset.mem_erase.1 hq).1)

/-- **The diagonal coefficient of the expansion is a unit in a `ℚ`-algebra.** By
`HJO.Sym.coeff_iota_pmonomial` it is the cast of a natural number, nonzero because the identity
letter assignment produces `x^λ`; and the cast of a nonzero natural number is the image of the unit
`(n : ℚ)` under `algebraMap ℚ K`. Over a field of characteristic zero this is `isUnit_iff_ne_zero`
applied to `HJO.Sym.coeff_partitionExponent_iota_pmonomial_ne_zero`; the point of the present
form is that it needs no inverses in `K`, so the triangular basis exists over `𝕜[y_1, …, y_k]`. -/
theorem isUnit_pmonomialMsymmCoeff [Algebra ℚ K] (hι : IsRealisation ι) {d : ℕ}
    (p : Nat.Partition d) : IsUnit (pmonomialMsymmCoeff ι p p) := by
  rcases subsingleton_or_nontrivial K with _ | _
  · exact isUnit_of_subsingleton _
  · have hinj : Function.Injective (algebraMap ℚ K) := (algebraMap ℚ K).injective
    have : CharZero K := charZero_of_inj_zero fun m hm =>
      Nat.cast_eq_zero.1 (hinj (by rw [map_natCast, hm, map_zero]))
    have hne := coeff_partitionExponent_iota_pmonomial_ne_zero hι p
    have hdef : pmonomialMsymmCoeff ι p p
        = MvPowerSeries.coeff (partitionExponent p) (ι (pmonomial K p)) := rfl
    rw [coeff_iota_pmonomial hι] at hne
    rw [hdef, coeff_iota_pmonomial hι]
    set n := MvPowerSeries.coeff (partitionExponent p) (tupleCount (p.parts.sort (· ≥ ·)))
    have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.cast_ne_zero.1 hne)
    rw [show ((n : K)) = algebraMap ℚ K (n : ℚ) from by rw [map_natCast]]
    exact (isUnit_iff_ne_zero.2 hn0).map (algebraMap ℚ K)

/-! ### The three main results -/

/-- Membership in a span inside a submodule is membership of the image span in the ambient
module: the inclusion is injective. -/
theorem mem_span_of_coe_mem_span {M : Type*} [AddCommGroup M] [Module K M] (W : Submodule K M)
    (S : Set W) {x : W} (h : (x : M) ∈ Submodule.span K (⇑W.subtype '' S)) :
    x ∈ Submodule.span K S := by
  rw [← Submodule.map_span, Submodule.mem_map] at h
  obtain ⟨y, hy, hyx⟩ := h
  rwa [← Subtype.ext hyx]

/-- **The power-sum monomials are triangular against the
monomial series.** There are a nonzero `c` and scalars `a_μ`, supported on the partitions `μ > λ`,
with `ι(p_λ) = c m_λ + ∑_μ a_μ m_μ`.

`c` is the coefficient `R_λ` of `ι(p_λ)` at `x^λ`, nonzero because the identity letter assignment
produces `x^λ` and a positive count is nonzero in characteristic zero; and `a_μ = R_μ`, which for
`μ ≠ λ` forces `μ ⪰ λ` hence `μ > λ`. -/
@[hjo "lem_sf_pmonomial_msymm_triangular"]
theorem exists_triangular_msymm [CharZero K] (hι : IsRealisation ι) {d : ℕ} (p : Nat.Partition d) :
    ∃ c : K, c ≠ 0 ∧ ∃ a : Nat.Partition d → K,
      (∀ q, a q ≠ 0 → partitionLex (partitionDiagram p) (partitionDiagram q)) ∧
        ι (pmonomial K p)
          = c • msymmSeries K p + ∑ q : Nat.Partition d, a q • msymmSeries K q := by
  classical
  refine ⟨pmonomialMsymmCoeff ι p p, coeff_partitionExponent_iota_pmonomial_ne_zero hι p,
    fun q => if q = p then 0 else pmonomialMsymmCoeff ι p q, fun q hq => ?_, ?_⟩
  · have hne : q ≠ p := fun h => hq (ite_eq_left h)
    exact partitionLex_of_dominates
      (dominates_of_coeff_iota_pmonomial_ne_zero hι p q fun h => hq ((ite_eq_right hne).trans h))
      hne.symm
  · have hsplit : ∀ q : Nat.Partition d, pmonomialMsymmCoeff ι p q • msymmSeries K q
        = (if q = p then pmonomialMsymmCoeff ι p p • msymmSeries K p else 0)
          + (if q = p then 0 else pmonomialMsymmCoeff ι p q) • msymmSeries K q := by
      intro q
      by_cases h : q = p
      · subst h; simp
      · simp [h]
    rw [iota_pmonomial_eq_sum_msymm hι, Finset.sum_congr rfl fun q _ => hsplit q,
      Finset.sum_add_distrib]
    exact congrArg₂ _ (by simp) rfl

/-- **The realised power-sum monomials are a basis of the monomial
span.** The expansion is triangular over the basis `(m_μ)` of `W_d` for the lexicographic order,
with the invertible diagonal `R_λ` (`HJO.Sym.isUnit_pmonomialMsymmCoeff`), so
`Module.Basis.exists_basis_of_triangular` turns it into a basis. The base is a `ℚ`-algebra and need
not be a field: what the triangular basis asks of the diagonal is that it be a unit, and a positive
natural number is one already. -/
@[hjo "lem_sf_iota_pmonomial_basis"]
theorem exists_basis_iota_pmonomial {K : Type*} [CommRing K] [Algebra ℚ K]
    {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι) (d : ℕ) :
    ∃ b : Module.Basis (Nat.Partition d) K (msymmSpan K d),
      ∀ p : Nat.Partition d, (b p : AlphabetSeries K) = ι (pmonomial K p) := by
  classical
  have htri : ∀ p : Nat.Partition d,
      (⟨ι (pmonomial K p), iota_pmonomial_mem_msymmSpan hι p⟩ : msymmSpan K d)
          - pmonomialMsymmCoeff ι p p • msymmBasis K d p
        ∈ Submodule.span K (⇑(msymmBasis K d) '' {q | partitionLt p q}) := by
    intro p
    refine mem_span_of_coe_mem_span _ _ ?_
    rw [show ⇑(msymmSpan K d).subtype '' (⇑(msymmBasis K d) '' {q | partitionLt p q})
        = (fun q : Nat.Partition d => msymmSeries K q) '' {q | partitionLt p q} by
      rw [Set.image_image]
      exact Set.image_congr fun q _ => coe_msymmBasis K q]
    simpa only [Submodule.coe_sub, SetLike.val_smul, coe_msymmBasis]
      using iota_pmonomial_sub_mem_span hι p
  obtain ⟨b, hb⟩ := exists_basis_of_triangular_of_sto (partitionLt (d := d)) (msymmBasis K d)
    (fun p => isUnit_pmonomialMsymmCoeff hι p) htri
  exact ⟨b, fun p => by rw [hb]⟩

/-- **The image of a graded piece is the monomial span.** The `p_λ`
span `Λ_d` (`HJO.Sym.linearIndependent_pmonomial`) and `ι` is linear, so `ι(Λ_d)` is the span of the
`ι(p_λ)`; and those are a basis of `W_d`. The base is a `ℚ`-algebra and need not be a field; see
`HJO.Sym.exists_basis_iota_pmonomial`. -/
@[hjo "lem_sf_iota_component_image"]
theorem map_lambdaComp_eq_msymmSpan {K : Type*} [CommRing K] [Algebra ℚ K]
    {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι) (d : ℕ) :
    Submodule.map ι.toLinearMap (LambdaComp K d) = msymmSpan K d := by
  obtain ⟨b, hb⟩ := exists_basis_iota_pmonomial hι d
  have hfun : (⇑ι.toLinearMap ∘ fun l : Nat.Partition d => pmonomial K l)
      = ⇑(msymmSpan K d).subtype ∘ ⇑b := funext fun l => (hb l).symm
  rw [← span_pmonomial K d, Submodule.map_span, ← Set.range_comp, hfun, Set.range_comp,
    ← Submodule.map_span, b.span_eq]
  exact Submodule.map_subtype_top _

end HJO.Sym
