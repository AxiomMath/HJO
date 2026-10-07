/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPowerSeries.Order
public import HJO.PointwiseSum
public meta import HJO.Attr

/-! # Grouping a homogeneous power series by the monomials in the other variables

Let `A` be a commutative semiring, `σ` a set of variables, `s` a *finite* set of variables and
`d` a degree. A formal power series `G : MvPowerSeries σ A` all of whose monomials have total
degree `d` — `MvPowerSeries.IsHomogeneous G d`, the graded part
`𝒫^gr_{k,d} ⊆ 𝒫°_k` — is in general not a polynomial: the realisation of the power sum `p_d` is
`∑_{l ≥ 1} x_l^d`, homogeneous of degree `d` and supported on infinitely many monomials. So `G`
cannot be divided as a polynomial in finitely many variables, and what is finite instead is each
*group* of terms sharing a monomial in the variables outside `s`.

Every monomial `μ` factors uniquely as `ρ * ν` with `ρ` a monomial in the variables outside `s`
and `ν` a monomial in the variables of `s`, namely by splitting the exponents; if `μ` has total
degree `d` then `ρ.degree ≤ d` and `ν` is one of the finitely many — here `s` is used — monomials
of degree `d - ρ.degree` in the variables of `s`. Collecting the terms of `G` with a given `ρ`
therefore produces an honest polynomial `G_ρ` in the variables of `s`, homogeneous of degree
`d - ρ.degree`, and the family `(ρ * G_ρ)` is summable in the elementary sense of
`HJO.Sym.IsSummableFamily` — a monomial of degree `d` receives a contribution from the single `ρ`
that is its part outside `s`, and a monomial of any other degree from none. Its sum is `G`, and
this is the only family of that shape with those two properties: the coefficient of `ν` in `G_ρ`
is forced to be the coefficient of `ρ * ν` in `G`.

This grouping is needed in two ambient rings, and both statements are here. The second is the
case `s = {u, v}` of the first, at `hs = (Set.finite_singleton v).insert u`, so the two statements
are one theorem at two instantiations and the pair case is not reproved.

## Main results

* `MvPowerSeries.IsHomogeneous.existsUnique_eq_monomialwiseFinsum`: a series homogeneous of
  degree `d` is, in exactly one way, the sum of a summable family `(ρ * G_ρ)` indexed by the
  monomials `ρ` in the variables outside the finite set `s`, with each `G_ρ` a polynomial in the
  variables of `s` homogeneous of degree `d - ρ.degree`.
* `MvPowerSeries.IsHomogeneous.existsUnique_eq_monomialwiseFinsum_monomial_mul`: the same
  decomposition along two distinguished letters `u` and `v`, with the *blocks* `H ρ` polynomials in
  `u` and `v` alone — the form the swapping operator `HJO.Sym.IsZDelta` consumes, since it divides
  each block by `v - u` inside the two-variable polynomial ring.

## Implementation notes

*The distinguished variables are a finite set, not a pair.* The grouping is naturally stated
by the monomials in the variables `x_l` with `l ∉ {i, j}` for `i ≠ j`; here the pair is replaced by
an arbitrary finite set `s : Set σ`, instantiated at `s = ({u, v} : Set σ)` with
`hs = (Set.finite_singleton v).insert u`, which needs no `DecidableEq σ`. Nothing is weakened: the
argument never separates the two variables, and `i ≠ j` is *not* needed for the statement — at
`i = j` the set `{i, j}` is a singleton and the grouping and its uniqueness hold unchanged, so
carrying `i ≠ j` would be a dead hypothesis. Finiteness of `s` is a different matter and cannot be
dropped: over `σ = ℕ`, `A = ℚ`, with `s = Set.univ` and `d = 1`, the only families allowed by the
vanishing clause are supported at `ρ = 0`, so their sum is the image of a single polynomial, while
the homogeneous series `∑_l x_l` is not such an image, its coefficient at `Finsupp.single l 1`
being `1` for every `l`.

*Dropping distinctness changes the route, and the direct route is not the uniform one.* The direct
proof derives the two-letter statement from `Finsupp.bijOn_add_single_add_single`, whose bijection
`(ρ, a, b) ↦ ρ + single u a + single v b` is not merely unavailable at `u = v` but false there,
because `(ρ, 1, 0)` and `(ρ, 0, 1)` then have the same image while `deg ρ + 1 + 0 = deg ρ + 0 + 1`
keeps both in its domain. What fails is injectivity alone, so that route still yields a
decomposition at `u = v` and loses only its uniqueness — which is the whole of the `∃!`. Grouping by
the monomials outside the finite set `{u, v}` needs no split, which is why `{u, v}` is carried as a
set rather than as two singled-out letters.

*The two conjunctions are not the same conjunction, and matching them is not a matter of shape.*
The block-ring clause is membership in `MvPolynomial.supported A s` in the finite-set form and the
containment `↑(H ρ).vars ⊆ ({u, v} : Set σ)` in the two-letter one, equivalent by
`MvPolynomial.mem_supported` — the form that
`MvPolynomial.exists_rename_eq_of_vars_subset_range` consumes to transfer a block to a genuine
two-variable polynomial ring. The two clauses restricting `ρ` stand in the opposite order, so
`and_left_comm` is needed and not `Iff.rfl`. The membership `∀ l ∈ ({u, v} : Set σ), ρ l = 0`
becomes `ρ u = 0 ∧ ρ v = 0` only once `Set.forall_mem_insert`, `Set.mem_singleton_iff` and
`forall_eq` have peeled the pair, and the resulting conjunction is *mis-associated* against the
two-letter form, whence `and_assoc`. Finally the two families are equal as functions rather than
merely corresponding: the coercion `MvPolynomial σ A → MvPowerSeries σ A` is a ring homomorphism,
so the product `ρ * G_ρ` formed in the polynomial ring is the product `monomial ρ 1 * ↑(G_ρ)`
formed in the series ring, by `MvPolynomial.coe_mul` and `MvPolynomial.coe_monomial` and not by
any unfolding.

*The family is indexed by all of `σ →₀ ℕ`* rather than by the subtype of monomials outside `s` of
degree at most `d`, with the clause `F ρ ≠ 0 → (∀ l ∈ s, ρ l = 0) ∧ ρ.degree ≤ d` cutting it down.
Extension by zero is a bijection between families on that subtype and families on `σ →₀ ℕ` obeying
the clause, so this is the statement and not a weaker one; it is preferred because the
index type is then independent of `d`, which is what the consumer
`HJO.Sym.existsUnique_mem_pGraded_eq_X_sub_X_mul` needs — it transforms a family for degree `d` into
one for degree `d - 1` — and because `d - ρ.degree` is truncated subtraction, so on the subtype-free
indexing the vanishing clause is exactly what stops `ρ.degree > d` from asking for a *constant*
`G_ρ` instead of `0`. The blocks that do vanish are homogeneous of every degree, so the homogeneity
and vanishing clauses are not in conflict.

*The splitting of a monomial is produced by an existential*, `exists_add_eq`, rather than by naming
`Finsupp.filter`, so that the rest of the argument uses only the three properties it has — the part
outside `s` vanishes on `s`, the part on `s` is supported there, and the two add up to the monomial.
Decidability of membership in `s` and of equality in `σ` is therefore never needed in a statement,
only inside proofs and inside `groupedPart`, which is why no `DecidableEq` hypothesis appears.
The hard part of both the summability and the sum clause is one vanishing statement,
`coeff_monomial_mul_eq_zero_of_ne`: the coefficient of `μ` in `ρ' * F ρ'` vanishes unless `ρ'` is
the part of `μ` outside `s`. Summability is then that the contributing indices lie in a singleton,
and both halves of the theorem are readings of `coeff_summableSum_monomial_mul`.

*The base is a commutative semiring* rather than the field `𝕂(y₁, …, y_k)` over which the grouping
is applied: only the ring operations on coefficients are used, and no coefficient is ever inverted —
the divisions of the argument happen in `HJO.Sym.existsUnique_mem_pGraded_eq_X_sub_X_mul` and in
`HJO.Sym.IsZDelta`, not here, and they divide polynomials rather than coefficients. At
`A = FractionRing (MvPolynomial (Fin k) K)` and `σ = ℕ` the first statement is the grouping over
`𝕂(y₁, …, y_k)` itself, the ambient ring being `HJO.Sym.AuxAlphabetSeriesFrac K k`; the second is
read in `𝒵^{(k)}_d`, whose realisation inside `𝒫°_k` is the business of `HJO.Sym.zGraded` and not of
this file, the regrouping being untouched by that embedding.

## References

Lemma `MvPowerSeries.IsHomogeneous.existsUnique_eq_monomialwiseFinsum`, scaffolding for the divided
differences `Δ_{x_r, x_{r+1}}` of E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*,
arXiv:1508.06239, §4, and Lemma
`MvPowerSeries.IsHomogeneous.existsUnique_eq_monomialwiseFinsum_monomial_mul`, used in the
Carlsson--Mellit recursion. Both are built on `HJO.Sym.IsSummableFamily` and `HJO.Sym.summableSum`
of `HJO.PointwiseSum`, the first also on `HJO.Sym.pGraded` and the second also on `HJO.Sym.zvar` and
`HJO.Sym.zGraded`. Used by `HJO.Sym.existsUnique_mem_pGraded_eq_X_sub_X_mul`, `HJO.Sym.zDeltaOn` and
`HJO.Sym.isZDelta_summableSum`. The two-letter route for
`MvPowerSeries.IsHomogeneous.existsUnique_eq_monomialwiseFinsum_monomial_mul` would be
`Finsupp.bijOn_add_single_add_single`, proved in `HJO.AmbientCombinatorics`; the route taken here is
the finite-set form instead, of which the two-letter statement is the case `s = {u, v}`.
-/

@[expose] public section

namespace MvPowerSeries.IsHomogeneous

section Auxiliary

variable {σ A : Type*} [CommSemiring A] {s : Set σ} {F : (σ →₀ ℕ) → MvPolynomial σ A}

/-- A polynomial lies in `MvPolynomial.supported A s` exactly when every monomial occurring in it
involves only variables of `s`. Mathlib characterises that subalgebra through `MvPolynomial.vars`;
this is the same condition read one coefficient at a time. -/
private lemma mem_supported_iff_coeff {p : MvPolynomial σ A} :
    p ∈ MvPolynomial.supported A s ↔ ∀ ν, MvPolynomial.coeff ν p ≠ 0 → ↑ν.support ⊆ s := by
  rw [MvPolynomial.mem_supported]
  refine ⟨fun h ν hν l hl => h (Finset.mem_coe.mpr ((MvPolynomial.mem_vars_iff_mem_support l).mpr
    ⟨ν, MvPolynomial.mem_support_iff.mpr hν, Finset.mem_coe.mp hl⟩)), fun h l hl => ?_⟩
  obtain ⟨ν, hν, hl'⟩ := (MvPolynomial.mem_vars_iff_mem_support l).mp (Finset.mem_coe.mp hl)
  exact h ν (MvPolynomial.mem_support_iff.mp hν) (Finset.mem_coe.mpr hl')

/-- Every monomial splits as a monomial vanishing on `s` plus a monomial supported on `s`, by
restricting its exponents off and onto `s`. -/
private lemma exists_add_eq (s : Set σ) (μ : σ →₀ ℕ) :
    ∃ ρ ν : σ →₀ ℕ, (∀ l ∈ s, ρ l = 0) ∧ ↑ν.support ⊆ s ∧ ρ + ν = μ := by
  classical
  refine ⟨μ.filter (· ∉ s), μ.filter (· ∈ s),
    fun l hl => Finsupp.filter_apply_neg _ _ (not_not.mpr hl), fun l hl => ?_, ?_⟩
  · by_contra hc
    exact Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hl) (Finsupp.filter_apply_neg _ _ hc)
  · rw [add_comm]
    exact Finsupp.filter_add_filter_not μ (fun l => l ∈ s)

/-- A monomial splits in at most one way as a sum of a monomial vanishing on `s` and a monomial
supported on `s`: the two summands are determined by the sum, one variable at a time. -/
private lemma eq_of_add_eq_add {ρ ν ρ' ν' : σ →₀ ℕ}
    (hρ : ∀ l ∈ s, ρ l = 0) (hν : ↑ν.support ⊆ s)
    (hρ' : ∀ l ∈ s, ρ' l = 0) (hν' : ↑ν'.support ⊆ s)
    (h : ρ + ν = ρ' + ν') : ρ = ρ' ∧ ν = ν' := by
  have hpt : ∀ l, ρ l + ν l = ρ' l + ν' l := fun l => by
    simpa only [Finsupp.add_apply] using DFunLike.congr_fun h l
  have hout : ∀ l ∉ s, ν l = 0 ∧ ν' l = 0 := fun l hl =>
    ⟨Finsupp.notMem_support_iff.mp fun hc => hl (hν (Finset.mem_coe.mpr hc)),
      Finsupp.notMem_support_iff.mp fun hc => hl (hν' (Finset.mem_coe.mpr hc))⟩
  refine ⟨Finsupp.ext fun l => ?_, Finsupp.ext fun l => ?_⟩ <;> by_cases hl : l ∈ s
  · rw [hρ l hl, hρ' l hl]
  · obtain ⟨h1, h2⟩ := hout l hl
    have := hpt l
    omega
  · have h1 := hρ l hl
    have h2 := hρ' l hl
    have := hpt l
    omega
  · obtain ⟨h1, h2⟩ := hout l hl
    rw [h1, h2]

/-- **At most one member of the family contributes to a given monomial.** Let `F` be a family of
polynomials supported on `s` whose member at `ρ` vanishes unless `ρ` does not involve the variables
of `s`, and let `μ = ρ + ν` be the splitting of a monomial. Then the coefficient of `μ` in
`ρ' * F ρ'` vanishes for every `ρ' ≠ ρ`: a nonzero coefficient would exhibit a second splitting of
`μ`. This is the finiteness in the summability clause and the single surviving term in the
coefficient of the sum. -/
private lemma coeff_monomial_mul_eq_zero_of_ne
    (hsupp : ∀ ρ, F ρ ∈ MvPolynomial.supported A s)
    (hvan : ∀ ρ, F ρ ≠ 0 → ∀ l ∈ s, ρ l = 0)
    {μ ρ ν : σ →₀ ℕ} (hρ : ∀ l ∈ s, ρ l = 0) (hν : ↑ν.support ⊆ s) (hμ : ρ + ν = μ)
    {ρ' : σ →₀ ℕ} (hne : ρ' ≠ ρ) :
    MvPowerSeries.coeff μ
      ((↑(MvPolynomial.monomial ρ' (1 : A) * F ρ') : MvPowerSeries σ A)) = 0 := by
  rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_monomial_mul', one_mul]
  split_ifs with hle
  · by_contra hc
    exact hne (eq_of_add_eq_add
      (hvan ρ' fun h => hc (by rw [h, MvPolynomial.coeff_zero]))
      (mem_supported_iff_coeff.mp (hsupp ρ') _ hc) hρ hν
      ((add_tsub_cancel_of_le hle).trans hμ.symm)).1
  · rfl

/-- A family of polynomials supported on `s`, whose member at `ρ` vanishes unless `ρ` does not
involve the variables of `s`, is summable after multiplication by the monomials: each monomial
receives a contribution from the single index that is its part outside `s`. -/
private lemma isSummableFamily_monomial_mul
    (hsupp : ∀ ρ, F ρ ∈ MvPolynomial.supported A s)
    (hvan : ∀ ρ, F ρ ≠ 0 → ∀ l ∈ s, ρ l = 0) :
    HJO.Sym.IsSummableFamily
      (fun ρ => (↑(MvPolynomial.monomial ρ (1 : A) * F ρ) : MvPowerSeries σ A) ) := by
  refine HJO.Sym.isSummableFamily_iff.mpr fun μ => ?_
  obtain ⟨ρ, ν, hρ, hν, hμ⟩ := exists_add_eq s μ
  refine (Set.finite_singleton ρ).subset fun ρ' hρ' => ?_
  exact Set.mem_singleton_iff.mpr
    (not_not.mp fun hne => hρ' (coeff_monomial_mul_eq_zero_of_ne hsupp hvan hρ hν hμ hne))

/-- The coefficient of a monomial `μ = ρ + ν` in the sum of the family `(ρ * F ρ)` is the
coefficient of `ν` in `F ρ`, for `ρ` the part of `μ` outside `s` and `ν` the part on `s`. -/
private lemma coeff_summableSum_monomial_mul
    (hsupp : ∀ ρ, F ρ ∈ MvPolynomial.supported A s)
    (hvan : ∀ ρ, F ρ ≠ 0 → ∀ l ∈ s, ρ l = 0)
    {μ ρ ν : σ →₀ ℕ} (hρ : ∀ l ∈ s, ρ l = 0) (hν : ↑ν.support ⊆ s) (hμ : ρ + ν = μ) :
    MvPowerSeries.coeff μ (HJO.Sym.summableSum
        (fun ρ => (↑(MvPolynomial.monomial ρ (1 : A) * F ρ) : MvPowerSeries σ A)))
      = MvPolynomial.coeff ν (F ρ) := by
  rw [HJO.Sym.coeff_summableSum,
    finsum_eq_single _ ρ fun ρ' hne => coeff_monomial_mul_eq_zero_of_ne hsupp hvan hρ hν hμ hne,
    ← hμ, MvPolynomial.coeff_coe, MvPolynomial.coeff_monomial_mul, one_mul]

/-- The members of a family obeying the support, vanishing and sum clauses are read off its sum:
the coefficient of a monomial `ν` of `s` in `F ρ` is the coefficient of `ρ * ν` in the sum. This is
the uniqueness half of the theorem. -/
private lemma coeff_eq_coeff_of_eq_summableSum {G : MvPowerSeries σ A}
    (hsupp : ∀ ρ, F ρ ∈ MvPolynomial.supported A s)
    (hvan : ∀ ρ, F ρ ≠ 0 → ∀ l ∈ s, ρ l = 0)
    (hG : G = HJO.Sym.summableSum
      (fun ρ => (↑(MvPolynomial.monomial ρ (1 : A) * F ρ) : MvPowerSeries σ A)))
    {ρ ν : σ →₀ ℕ} (hρ : ∀ l ∈ s, ρ l = 0) (hν : ↑ν.support ⊆ s) :
    MvPolynomial.coeff ν (F ρ) = MvPowerSeries.coeff (ρ + ν) G := by
  rw [hG, coeff_summableSum_monomial_mul hsupp hvan hρ hν rfl]

/-- **Finiteness of the monomials of a given degree in finitely many variables.** This is the only
place the finiteness of `s` is used. -/
private lemma finite_setOf_degree_eq (hs : s.Finite) (n : ℕ) :
    {ν : σ →₀ ℕ | ↑ν.support ⊆ s ∧ ν.degree = n}.Finite := by
  classical
  refine Set.Finite.subset (hs.toFinset.finsuppAntidiag n).finite_toSet fun ν hν => ?_
  obtain ⟨hsupp, hdeg⟩ := hν
  have hsub : ν.support ⊆ hs.toFinset :=
    fun l hl => hs.mem_toFinset.mpr (hsupp (Finset.mem_coe.mpr hl))
  rw [Finset.mem_coe, Finset.mem_finsuppAntidiag]
  refine ⟨?_, hsub⟩
  rw [← hdeg, Finsupp.degree_apply,
    Finset.sum_subset hsub fun x _ hx => Finsupp.notMem_support_iff.mp hx]

open Classical in
/-- The part of a homogeneous series `G` of degree `d` belonging to a monomial `ρ` in the variables
outside the finite set `s`: the polynomial in the variables of `s`, homogeneous of degree
`d - ρ.degree`, whose coefficient at `ν` is the coefficient of `ρ + ν` in `G`. It is cut off to `0`
unless `ρ` avoids the variables of `s` and has degree at most `d`, so that the family it forms is
indexed by all monomials. -/
private noncomputable def groupedPart (hs : s.Finite) (d : ℕ) (G : MvPowerSeries σ A)
    (ρ : σ →₀ ℕ) : MvPolynomial σ A :=
  if (∀ l ∈ s, ρ l = 0) ∧ ρ.degree ≤ d then
    ∑ ν ∈ (finite_setOf_degree_eq hs (d - ρ.degree)).toFinset,
      MvPolynomial.monomial ν (MvPowerSeries.coeff (ρ + ν) G)
  else 0

variable (hs : s.Finite) (d : ℕ) (G : MvPowerSeries σ A) (ρ : σ →₀ ℕ)

private lemma groupedPart_eq_zero (h : ¬((∀ l ∈ s, ρ l = 0) ∧ ρ.degree ≤ d)) :
    groupedPart hs d G ρ = 0 := by
  simp only [groupedPart]
  split_ifs with h'
  · exact absurd h' h
  · rfl

private lemma groupedPart_mem_supported : groupedPart hs d G ρ ∈ MvPolynomial.supported A s := by
  simp only [groupedPart]
  split_ifs
  · refine Subalgebra.sum_mem _ fun ν hν => mem_supported_iff_coeff.mpr fun ν' hν' => ?_
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset
      (MvPolynomial.mem_support_iff.mpr hν'))]
    exact ((finite_setOf_degree_eq hs _).mem_toFinset.mp hν).1
  · exact Subalgebra.zero_mem _

private lemma groupedPart_isHomogeneous :
    (groupedPart hs d G ρ).IsHomogeneous (d - ρ.degree) := by
  simp only [groupedPart]
  split_ifs
  · exact MvPolynomial.IsHomogeneous.sum _ _ _ fun ν hν =>
      MvPolynomial.isHomogeneous_monomial _ ((finite_setOf_degree_eq hs _).mem_toFinset.mp hν).2
  · exact MvPolynomial.isHomogeneous_zero _ _ _

private lemma coeff_groupedPart {ν : σ →₀ ℕ} (hρ : ∀ l ∈ s, ρ l = 0) (hd : ρ.degree ≤ d)
    (hν : ↑ν.support ⊆ s) (hdeg : ν.degree = d - ρ.degree) :
    MvPolynomial.coeff ν (groupedPart hs d G ρ) = MvPowerSeries.coeff (ρ + ν) G := by
  classical
  simp only [groupedPart]
  split_ifs with h'
  · rw [MvPolynomial.coeff_sum, Finset.sum_eq_single_of_mem ν
      ((finite_setOf_degree_eq hs _).mem_toFinset.mpr ⟨hν, hdeg⟩)
      fun ν' _ hne => by simp [MvPolynomial.coeff_monomial, hne]]
    simp
  · exact absurd ⟨hρ, hd⟩ h'

end Auxiliary

/-- **Grouping a homogeneous power series by the monomials in the other variables.** Let `s` be a
finite set of variables and let `G` be a formal power series all of whose monomials have total
degree `d`. Then there is exactly one family `(G_ρ)` of polynomials, indexed by the monomials `ρ`
and vanishing unless `ρ` is a monomial of degree at most `d` in the variables outside `s`, such
that each `G_ρ` is a polynomial in the variables of `s` homogeneous of degree `d - ρ.degree`, the
family `(ρ * G_ρ)` is summable, and its sum is `G`. This is the finiteness that replaces division
in finitely many variables: `G` itself need not be a polynomial, but each group of its terms
sharing a monomial outside `s` is one. The case is `s = {x_i, x_j}`. -/
@[hjo "lem_cm_group_other_monomials"]
theorem existsUnique_eq_monomialwiseFinsum {σ A : Type*} [CommSemiring A] {s : Set σ}
    (hs : s.Finite) {d : ℕ} {G : MvPowerSeries σ A} (hG : G.IsHomogeneous d) :
    ∃! F : (σ →₀ ℕ) → MvPolynomial σ A,
      (∀ ρ, F ρ ∈ MvPolynomial.supported A s) ∧
      (∀ ρ, F ρ ≠ 0 → (∀ l ∈ s, ρ l = 0) ∧ ρ.degree ≤ d) ∧
      (∀ ρ, (F ρ).IsHomogeneous (d - ρ.degree)) ∧
      HJO.Sym.IsSummableFamily
        (fun ρ => (↑(MvPolynomial.monomial ρ (1 : A) * F ρ) : MvPowerSeries σ A)) ∧
      G = HJO.Sym.summableSum
        (fun ρ => (↑(MvPolynomial.monomial ρ (1 : A) * F ρ) : MvPowerSeries σ A)) := by
  have hcut : ∀ ρ : σ →₀ ℕ, groupedPart hs d G ρ ≠ 0 → (∀ l ∈ s, ρ l = 0) ∧ ρ.degree ≤ d :=
    fun ρ h => not_not.mp fun hP => h (groupedPart_eq_zero hs d G ρ hP)
  have hsupp := groupedPart_mem_supported hs d G
  have hvan : ∀ ρ : σ →₀ ℕ, groupedPart hs d G ρ ≠ 0 → ∀ l ∈ s, ρ l = 0 :=
    fun ρ h => (hcut ρ h).1
  have hsum : G = HJO.Sym.summableSum
      (fun ρ => (↑(MvPolynomial.monomial ρ (1 : A) * groupedPart hs d G ρ) :
        MvPowerSeries σ A)) := by
    refine MvPowerSeries.ext fun μ => ?_
    obtain ⟨ρ, ν, hρ, hν, hμ⟩ := exists_add_eq s μ
    have hdeg : μ.degree = ρ.degree + ν.degree := by
      rw [← hμ]; exact map_add Finsupp.degree ρ ν
    rw [coeff_summableSum_monomial_mul hsupp hvan hρ hν hμ]
    by_cases h : ρ.degree ≤ d ∧ ν.degree = d - ρ.degree
    · rw [coeff_groupedPart hs d G ρ hρ h.1 hν h.2, hμ]
    · have h0 : MvPolynomial.coeff ν (groupedPart hs d G ρ) = 0 := by
        by_cases hd : ρ.degree ≤ d
        · exact (groupedPart_isHomogeneous hs d G ρ).coeff_eq_zero fun hdd => h ⟨hd, hdd⟩
        · rw [groupedPart_eq_zero hs d G ρ fun hh => hd hh.2, MvPolynomial.coeff_zero]
      rw [h0]
      exact hG.coeff_eq_zero (by omega)
  refine ⟨groupedPart hs d G, ⟨hsupp, hcut, groupedPart_isHomogeneous hs d G,
    isSummableFamily_monomial_mul hsupp hvan, hsum⟩, ?_⟩
  rintro F' ⟨hsupp', hcut', -, -, hsum'⟩
  have hvan' : ∀ ρ : σ →₀ ℕ, F' ρ ≠ 0 → ∀ l ∈ s, ρ l = 0 := fun ρ h => (hcut' ρ h).1
  funext ρ
  by_cases hP : (∀ l ∈ s, ρ l = 0) ∧ ρ.degree ≤ d
  · refine MvPolynomial.ext _ _ fun ν => ?_
    by_cases hν : ↑ν.support ⊆ s
    · exact (coeff_eq_coeff_of_eq_summableSum hsupp' hvan' hsum' hP.1 hν).trans
        (coeff_eq_coeff_of_eq_summableSum hsupp hvan hsum hP.1 hν).symm
    · have hz : ∀ p : MvPolynomial σ A, p ∈ MvPolynomial.supported A s →
          MvPolynomial.coeff ν p = 0 :=
        fun p hp => not_not.mp fun h => hν (mem_supported_iff_coeff.mp hp ν h)
      rw [hz _ (hsupp' ρ), hz _ (hsupp ρ)]
  · rw [groupedPart_eq_zero hs d G ρ hP]
    exact not_not.mp fun h => hP (hcut' ρ h)

/-- The regrouping of a homogeneous series along a finite set `s` of letters, in the form
`MvPowerSeries.IsHomogeneous.existsUnique_eq_monomialwiseFinsum_monomial_mul` states it: the block
ring is described by `↑(H ρ).vars ⊆ s`, the two conditions on `ρ` come first, and the summands are
the products `monomial ρ 1 * ↑(H ρ)` formed in the series ring. -/
private lemma existsUnique_eq_monomialwiseFinsum_monomial_mul' {L K : Type*} [CommSemiring K]
    {s : Set L} (hs : s.Finite) {d : ℕ} {G : MvPowerSeries L K} (hG : G.IsHomogeneous d) :
    ∃! H : (L →₀ ℕ) → MvPolynomial L K,
      (∀ ρ, H ρ ≠ 0 → (∀ l ∈ s, ρ l = 0) ∧ ρ.degree ≤ d) ∧
      (∀ ρ, ↑(H ρ).vars ⊆ s) ∧
      (∀ ρ, (H ρ).IsHomogeneous (d - ρ.degree)) ∧
      HJO.Sym.IsSummableFamily
        (fun ρ => MvPowerSeries.monomial ρ 1 * (H ρ : MvPowerSeries L K)) ∧
      G = HJO.Sym.summableSum
        fun ρ => MvPowerSeries.monomial ρ 1 * (H ρ : MvPowerSeries L K) :=
  (existsUnique_congr fun _ => by
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_monomial, MvPolynomial.mem_supported]
    exact and_left_comm).mp (existsUnique_eq_monomialwiseFinsum hs hG)

/-- **The graded part splits along two of its letters.** Let `G : MvPowerSeries L K` be homogeneous
of degree `d` and let `u` and `v` be two letters. Then there is exactly one family of *blocks*
`H : (L →₀ ℕ) → MvPolynomial L K` such that a block is nonzero only at a monomial `ρ` free of `u`
and of `v` with `deg ρ ≤ d`, each block is a polynomial in `u` and `v` alone and is homogeneous of
degree `d - deg ρ`, the family `ρ · H ρ` is summable, and `G = ∑ ρ, ρ · H ρ`. Since the blocks are
unique, a construction on homogeneous series of degree `d` may be carried out one block at a time,
inside the two-variable polynomial ring `K[u, v]`. This is the case `s = {u, v}` of
`existsUnique_eq_monomialwiseFinsum`, so `u ≠ v` is not needed. -/
@[hjo "lem_cm_zblock"]
theorem existsUnique_eq_monomialwiseFinsum_monomial_mul {L K : Type*} [CommSemiring K] (u v : L)
    {d : ℕ} {G : MvPowerSeries L K} (hG : G.IsHomogeneous d) :
    ∃! H : (L →₀ ℕ) → MvPolynomial L K,
      (∀ ρ, H ρ ≠ 0 → ρ u = 0 ∧ ρ v = 0 ∧ ρ.degree ≤ d) ∧
      (∀ ρ, ↑(H ρ).vars ⊆ ({u, v} : Set L)) ∧
      (∀ ρ, (H ρ).IsHomogeneous (d - ρ.degree)) ∧
      HJO.Sym.IsSummableFamily (fun ρ => monomial ρ 1 * (H ρ : MvPowerSeries L K)) ∧
      G = HJO.Sym.summableSum fun ρ => monomial ρ 1 * (H ρ : MvPowerSeries L K) :=
  (existsUnique_congr fun _ => by
    simp only [Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq, and_assoc]).mp
      (existsUnique_eq_monomialwiseFinsum_monomial_mul' ((Set.finite_singleton v).insert u) hG)

end MvPowerSeries.IsHomogeneous
