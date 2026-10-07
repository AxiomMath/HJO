/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.Ppoly
public meta import HJO.Attr

/-! # The leading exponent of Macdonald's polynomial, and the first column

Two lemmas of the Pieri block that need only the finite alphabet:
`HJO.Mac.coeff_partExp_macPpoly` and `HJO.Mac.eq_zero_of_sum_smul_macPpoly_eq_esymm_mul`.

`HJO.Mac.coeff_partExp_macPpoly`: for a partition `μ` of `d` with at most `n` parts, the leading
exponent of `P_μ[X_n]` for the lexicographic order is `\bar\mu = (μ_1, …, μ_n)` and the coefficient
there is `1`. The third assertion, that `P_μ[X_n] ≠ 0`, is immediate from the second and is also
`HJO.Mac.macPpoly_ne_zero`, proved in `HJO/Macdonald/Htilde.lean` from the basis.

That is the bottom of the Pieri block: four lemmas stand on it (`HJO.Mac.macPpoly_eq_prod_X_mul`,
`HJO.Mac.eq_zero_of_sum_smul_macPpoly_eq_esymm_mul`, `HJO.Mac.rowLen_zero_le_of_coeff_ne_zero`,
`HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`).

`HJO.Mac.eq_zero_of_sum_smul_macPpoly_eq_esymm_mul`: a combination of the `P_λ[X_n]` whose indices
all leave some letter with exponent `0` is a multiple of `res_n(e_n) = x_1 ⋯ x_n` only if every
coefficient vanishes. It follows from the leading exponent alone: the largest index occurring reads
off its own coefficient, and a multiple of `x_1 ⋯ x_n` has no monomial missing a variable.

## The proof, and what it does not need

`HJO.Mac.macPpoly` gives `P_μ[X_n] - m_μ[X_n]` in the span of the `m_ν[X_n]` with
`\bar\nu <_lex \bar\mu` (`HJO.Mac.macPpoly_sub_msymm_mem_span`), and that is the whole input: the
eigenvector condition is not used. One lemma about spans does both halves of the work
(`MvPolynomial.coeff_eq_zero_of_mem_span`): a coefficient vanishing on a spanning set vanishes on
the span, being a linear functional. At the exponent `\bar\mu` itself every `m_ν` in the set
contributes `0` (`HJO.Mac.coeff_partExp_msymm`, the indices differing), and above `\bar\mu` every
`m_ν` in the set contributes `0` because its own exponents are at most `\bar\nu <_lex \bar\mu`
(`HJO.Mac.toLex_le_of_mem_support_msymm`).

Genericity enters only because `macPpoly` is a function of it; the argument consumes no
nonvanishing.

## Main results

* `MvPolynomial.coeff_eq_zero_of_mem_span`: a coefficient that vanishes on a set vanishes on its
  span.
* `HJO.Mac.coeff_partExp_macPpoly`, `HJO.Mac.lex_degree_macPpoly`
  (`HJO.Mac.coeff_partExp_macPpoly`).
* `HJO.Mac.toLex_le_of_mem_support_macPpoly`: the form of the leading-exponent statement its
  consumers use --- no exponent of `P_μ[X_n]` exceeds `\bar\mu`.
* `HJO.Mac.eq_zero_of_sum_smul_macPpoly_eq_esymm_mul`, and the
  two facts about the top elementary symmetric polynomial it rests on,
  `HJO.Mac.esymm_fintypeCard` and `HJO.Mac.coeff_esymm_fintypeCard_mul_eq_zero`.

## References

This file proves `HJO.Mac.coeff_partExp_macPpoly` and
`HJO.Mac.eq_zero_of_sum_smul_macPpoly_eq_esymm_mul`, from `HJO.Sym.elemSymm`, `HJO.Sym.rowLenSeq`,
`Finsupp.lex_lt_iff_isLeast`, `MonomialOrder.lex_degree_isGreatest`, `HJO.Sym.restrictAlphabet`
and `HJO.Mac.macPpoly`.
-/

@[expose] public section

open Finset MvPolynomial MonomialOrder

/-! ### A coefficient vanishing on a set vanishes on its span -/

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- **A coefficient that vanishes on a set of polynomials vanishes on its span**: `coeff c` is the
linear functional `MvPolynomial.lcoeff`, so the span of a set inside its kernel is inside its
kernel. -/
theorem coeff_eq_zero_of_mem_span {c : σ →₀ ℕ} {S : Set (MvPolynomial σ R)}
    (hS : ∀ p ∈ S, coeff c p = 0) {x : MvPolynomial σ R} (hx : x ∈ Submodule.span R S) :
    coeff c x = 0 := by
  have hle : Submodule.span R S ≤ LinearMap.ker (lcoeff R c) :=
    Submodule.span_le.mpr fun p hp => LinearMap.mem_ker.mpr ((lcoeff_apply R c p).trans (hS p hp))
  exact (lcoeff_apply R c x).symm.trans (LinearMap.mem_ker.mp (hle hx))

end MvPolynomial

namespace HJO.Mac

/-! ### The lower monomial symmetric polynomials contribute nothing at or above `\bar\mu` -/

section Lower

variable {σ : Type*} [Fintype σ] [LinearOrder σ] {R : Type*} [CommSemiring R] {d : ℕ}

/-- The set of the second condition on `P_μ[X_n]`: the `m_ν[X_n]` with
`\bar\nu <_lex \bar\mu`. -/
def lowerMsymmSet (σ : Type*) [Fintype σ] [LinearOrder σ] (R : Type*) [CommSemiring R] {d : ℕ}
    (μ : PartIdx σ d) : Set (MvPolynomial σ R) :=
  {p : MvPolynomial σ R | ∃ ν : PartIdx σ d,
    toLex (partExp σ ν) < toLex (partExp σ μ) ∧ p = msymm σ R ν.1}

/-- **Nothing in the span of the lower monomial symmetric polynomials has a coefficient at
`\bar\mu`**: a `ν` with `\bar\nu <_lex \bar\mu` is not `μ`, and `coeff \bar\mu m_ν` separates the
indices. -/
theorem coeff_partExp_eq_zero_of_mem_span_lowerMsymmSet {μ : PartIdx σ d}
    {x : MvPolynomial σ R} (hx : x ∈ Submodule.span R (lowerMsymmSet σ R μ)) :
    coeff (partExp σ μ) x = 0 := by
  refine coeff_eq_zero_of_mem_span (fun p hp => ?_) hx
  obtain ⟨ν, hν, rfl⟩ := hp
  have hne : μ ≠ ν := by rintro rfl; exact absurd hν (lt_irrefl _)
  rw [coeff_partExp_msymm]
  exact ite_eq_right fun h => absurd h hne

/-- **Nothing in the span of the lower monomial symmetric polynomials has a coefficient above
`\bar\mu`**: the exponents of `m_ν` are at most `\bar\nu`, which is below `\bar\mu`. -/
theorem coeff_eq_zero_of_mem_span_lowerMsymmSet {μ : PartIdx σ d} {c : σ →₀ ℕ}
    (hc : toLex (partExp σ μ) < toLex c) {x : MvPolynomial σ R}
    (hx : x ∈ Submodule.span R (lowerMsymmSet σ R μ)) : coeff c x = 0 := by
  refine coeff_eq_zero_of_mem_span (fun p hp => ?_) hx
  obtain ⟨ν, hν, rfl⟩ := hp
  by_contra hne
  exact absurd (lt_of_lt_of_le hc
    ((toLex_le_of_mem_support_msymm (mem_support_iff.mpr hne)).trans hν.le)) (lt_irrefl _)

end Lower

/-! ### The leading exponent of `P_μ[X_n]` -/

section Lead

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ}
  {u : K} {d : ℕ}

/-- The second condition on `P_μ[X_n]`, read through `lowerMsymmSet`. -/
theorem macPpoly_sub_msymm_mem_span_lowerMsymmSet (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) :
    (macPpoly hqu μ : MvPolynomial σ K) - msymm σ K μ.1
      ∈ Submodule.span K (lowerMsymmSet σ K μ) :=
  macPpoly_sub_msymm_mem_span hqu μ

/-- **The coefficient of `x^{\bar\mu}` in `P_μ[X_n]` is `1`**: `m_μ[X_n]` contributes `1` there
and the correction contributes nothing. This is the third assertion of
`HJO.Mac.coeff_partExp_macPpoly`, and with the first it gives the second. -/
@[hjo "lem_pie_ppoly_lead"]
theorem coeff_partExp_macPpoly (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : PartIdx σ d) :
    coeff (partExp σ μ) (macPpoly hqu μ : MvPolynomial σ K) = 1 := by
  have hmm : coeff (partExp σ μ) (msymm σ K μ.1) = 1 := by simp [coeff_partExp_msymm]
  have h := coeff_partExp_eq_zero_of_mem_span_lowerMsymmSet
    (macPpoly_sub_msymm_mem_span_lowerMsymmSet hqu μ)
  rw [coeff_sub, hmm, sub_eq_zero] at h
  exact h

/-- **No exponent of `P_μ[X_n]` exceeds `\bar\mu`**: neither `m_μ[X_n]`, whose exponents are the
rearrangements of `\bar\mu`, nor the correction, whose exponents are below `\bar\mu`, has one. -/
@[hjo "lem_pie_ppoly_lead"]
theorem toLex_le_of_mem_support_macPpoly (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) {c : σ →₀ ℕ} (hc : c ∈ (macPpoly hqu μ : MvPolynomial σ K).support) :
    toLex c ≤ toLex (partExp σ μ) := by
  by_contra hlt
  rw [not_le] at hlt
  refine mem_support_iff.mp hc ?_
  have h := coeff_eq_zero_of_mem_span_lowerMsymmSet hlt
    (macPpoly_sub_msymm_mem_span_lowerMsymmSet hqu μ)
  have hm : coeff c (msymm σ K μ.1) = 0 := by
    by_contra hne
    exact absurd (lt_of_lt_of_le hlt (toLex_le_of_mem_support_msymm (mem_support_iff.mpr hne)))
      (lt_irrefl _)
  rw [coeff_sub, hm, sub_zero] at h
  exact h

/-- **The leading exponent of `P_μ[X_n]` is `\bar\mu`**: the coefficient there is `1` and no
exponent above it occurs. This is the second assertion of `HJO.Mac.coeff_partExp_macPpoly`. -/
@[hjo "lem_pie_ppoly_lead"]
theorem lex_degree_macPpoly (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : PartIdx σ d) :
    lex.degree (macPpoly hqu μ : MvPolynomial σ K) = partExp σ μ :=
  degree_eq_of_coeff_ne_zero (by rw [coeff_partExp_macPpoly]; exact one_ne_zero)
    fun _ hc => lex_le_iff.mpr (toLex_le_of_mem_support_macPpoly hqu μ hc)

/-- **The leading coefficient of `P_μ[X_n]` is `1`**: Macdonald's polynomial is monic for the
lexicographic order. -/
theorem lex_leadingCoeff_macPpoly (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) : lex.leadingCoeff (macPpoly hqu μ : MvPolynomial σ K) = 1 := by
  rw [MonomialOrder.leadingCoeff, lex_degree_macPpoly, coeff_partExp_macPpoly]

end Lead

/-! ### A combination of short indices is not divisible by the product of the variables -/

section Ones

variable {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R]

/-- **The exponent vector of the product of all the variables**: every entry `1`. This is the
leading --- and only --- exponent of `res_n(e_n) = x_1 ⋯ x_n`. -/
noncomputable def onesExp (σ : Type*) [Fintype σ] : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun _ => 1

@[simp]
theorem onesExp_apply (j : σ) : onesExp σ j = 1 := rfl

/-- **The product of all the variables is the monomial `x^{(1,…,1)}`.** -/
theorem prod_X_eq_monomial_onesExp (σ : Type*) [Fintype σ] (R : Type*) [CommSemiring R] :
    ∏ j : σ, (X j : MvPolynomial σ R) = monomial (onesExp σ) 1 := by
  classical
  have hs : (onesExp σ).support = Finset.univ := by
    ext j
    simp [Finsupp.mem_support_iff]
  rw [← MvPolynomial.prod_X_pow_eq_monomial, hs]
  exact Finset.prod_congr rfl fun j _ => by rw [onesExp_apply, pow_one]

/-- **The top elementary symmetric polynomial is the product of all the variables**: at `r = n` the
only `n`-element subset of the alphabet is the whole of it. This is the reading of
`res_n(e_n)`, which `HJO.Sym.restrictAlphabet_elemSymm` identifies with
`esymm σ 𝕜 n`. -/
theorem esymm_fintypeCard (σ : Type*) [Fintype σ] (R : Type*) [CommSemiring R] :
    esymm σ R (Fintype.card σ) = ∏ i : σ, X i := by
  classical
  rw [MvPolynomial.esymm, ← Finset.card_univ (α := σ), Finset.powersetCard_self,
    Finset.sum_singleton]

/-- **A multiple of the top elementary symmetric polynomial has no monomial missing a variable.**
This is the observation that every monomial of `res_n(e_n)h` has all `n` of its
exponents at least `1`, in the form its use needs: a coefficient at an exponent with a zero
entry. -/
theorem coeff_esymm_fintypeCard_mul_eq_zero {j : σ} {e : σ →₀ ℕ} (he : e j = 0)
    (h : MvPolynomial σ R) : coeff e (esymm σ R (Fintype.card σ) * h) = 0 := by
  classical
  have hnot : ¬ onesExp σ ≤ e := fun hle => by
    have := hle j
    rw [onesExp_apply, he] at this
    exact absurd this (by omega)
  rw [esymm_fintypeCard, prod_X_eq_monomial_onesExp, coeff_monomial_mul']
  exact ite_eq_right fun hle => absurd hle hnot

end Ones

section Column

variable {σ : Type*} [Fintype σ] [LinearOrder σ] {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ}
  {u : K}

/-- The index of a Macdonald polynomial, with its size: the type over which the finite
set `S` of partitions --- of any sizes --- ranges. -/
abbrev SizedIdx (σ : Type*) [Fintype σ] : Type := (d : ℕ) × PartIdx σ d

/-- **Distinct sized indices have distinct exponent vectors**, mixed sizes and all: the exponent
vector has total degree the size (`HJO.Mac.degree_partExp`), so it decides the size first and then
the partition (`HJO.Mac.partExp_injective`). -/
theorem sizedIdx_eq_of_partExp_eq {s t : SizedIdx σ}
    (h : partExp σ s.2 = partExp σ t.2) : s = t := by
  obtain ⟨d, μ⟩ := s
  obtain ⟨e, ν⟩ := t
  have hde : d = e := by rw [← degree_partExp μ, ← degree_partExp ν, h]
  subst hde
  exact congrArg (fun x : PartIdx σ d => (⟨d, x⟩ : SizedIdx σ)) (partExp_injective h)

/-- **A combination of Macdonald polynomials of short index is not a
multiple of the product of the variables**, unless all its coefficients vanish.

The `S` is a finite set of partitions of any sizes, which is `S` here: a finite set of
indices carrying their sizes (`HJO.Mac.SizedIdx`), since `P_λ[X_n]` is defined for a partition of a
given size. Its hypothesis that each member has `n`th entry `0` is `hS`, an index some letter of
which carries exponent `0` --- for a weakly decreasing exponent vector, the same condition read at
the last letter. Its `res_n(e_n)` is `esymm σ 𝕜 n` by `HJO.Sym.restrictAlphabet_elemSymm`.

The proof: were some coefficient nonzero, take among the indices carrying one the
one whose exponent vector `\bar\rho` is lexicographically largest. The coefficient of `x^{\bar\rho}`
in the combination is then `c_ρ`, every other `P_λ[X_n]` having all its exponents at most
`\bar\lambda <_lex \bar\rho` (`toLex_le_of_mem_support_macPpoly`) and `P_ρ[X_n]` contributing `1`
there (`coeff_partExp_macPpoly`); while on the other side that coefficient is `0`, because
`\bar\rho` has a zero entry and every monomial of a multiple of `x_1 ⋯ x_n` has none
(`coeff_esymm_fintypeCard_mul_eq_zero`). -/
@[hjo "lem_pie_column_independent"]
theorem eq_zero_of_sum_smul_macPpoly_eq_esymm_mul
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) {S : Finset (SizedIdx σ)}
    {c : SizedIdx σ → K} (hS : ∀ s ∈ S, ∃ j : σ, partExp σ s.2 j = 0) {h : MvPolynomial σ K}
    (hsum : ∑ s ∈ S, c s • (macPpoly hqu s.2 : MvPolynomial σ K)
      = esymm σ K (Fintype.card σ) * h) :
    ∀ s ∈ S, c s = 0 := by
  classical
  intro s₀ hs₀S
  by_contra hs₀
  obtain ⟨ρ, hρT, hρmax⟩ := Finset.exists_max_image ({s ∈ S | c s ≠ 0})
    (fun s => toLex (partExp σ s.2)) ⟨s₀, Finset.mem_filter.mpr ⟨hs₀S, hs₀⟩⟩
  obtain ⟨hρS, hρ⟩ := Finset.mem_filter.mp hρT
  -- the coefficient of `x^{\bar\rho}` in the combination is `c_ρ`
  have hterm : ∀ s ∈ S, s ≠ ρ →
      coeff (partExp σ ρ.2) (c s • (macPpoly hqu s.2 : MvPolynomial σ K)) = 0 := by
    intro s hsS hne
    rw [coeff_smul, smul_eq_mul]
    rcases eq_or_ne (c s) 0 with hc | hc
    · rw [hc, zero_mul]
    · refine mul_eq_zero_of_right _ ?_
      have hlt : toLex (partExp σ s.2) < toLex (partExp σ ρ.2) :=
        lt_of_le_of_ne (hρmax s (Finset.mem_filter.mpr ⟨hsS, hc⟩))
          fun heq => hne (sizedIdx_eq_of_partExp_eq (toLex.injective heq))
      by_contra hne0
      exact absurd (lt_of_lt_of_le hlt
        (toLex_le_of_mem_support_macPpoly hqu s.2 (mem_support_iff.mpr hne0))) (lt_irrefl _)
  have hleft : coeff (partExp σ ρ.2)
      (∑ s ∈ S, c s • (macPpoly hqu s.2 : MvPolynomial σ K)) = c ρ := by
    rw [coeff_sum, Finset.sum_eq_single_of_mem ρ hρS hterm, coeff_smul, smul_eq_mul,
      coeff_partExp_macPpoly, mul_one]
  obtain ⟨j, hj⟩ := hS ρ hρS
  rw [hsum, coeff_esymm_fintypeCard_mul_eq_zero hj] at hleft
  exact hρ hleft.symm

end Column

end HJO.Mac
