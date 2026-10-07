/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.PieriPpoly
public meta import HJO.Attr

/-! # The degree of Macdonald's polynomial in one variable

`HJO.Mac.apply_le_partExp_of_mem_support_macPpoly`: for a partition `λ` with `λ_{n+1} = 0`, every
exponent occurring in `P_λ[X_n]` has `n`th entry at most `λ_1`.

## The bound is entrywise, and the `n` plays no role

The statement singles out the `n`th entry because that is the variable its consumer
`HJO.Mac.coeff_partExp_splitAt_macPpoly_eq` reads `P_λ[X_n]` as a polynomial in. The argument does
not: it swaps the entry being bounded with the *first* one, and what the first entry is bounded by
is `λ_1`. So the statement proved here is the entrywise bound
```
c j ≤ \bar\lambda_i   for every j, where i is the least letter of the alphabet,
```
of which the conclusion is the case `j = n`. Only `i` has to be the least letter: it is
there that "`i` is the least index at which the two exponents differ" is automatic, which is the
step of the proof that a general index would not support.

The two ingredients are `HJO.Mac.toLex_le_of_mem_support_macPpoly`
(`HJO.Mac.coeff_partExp_macPpoly`: no exponent of `P_λ[X_n]` exceeds `\bar\lambda`
lexicographically) and the symmetry of `P_λ[X_n]`, which is carried by
`MvPolynomial.IsSymmetric.coeff_mapDomain`: transposing two letters permutes the monomials without
changing coefficients, so `c` occurs iff its transpose does.

`Finsupp.apply_le_of_toLex_le` is the lexicographic step in isolation: at the least
letter a lexicographic `≤` is an entrywise `≤`. It is stated separately because the same step
appears in `HJO.Mac.rowLen_zero_le_of_coeff_ne_zero` and `HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero`.

## Generality

The alphabet is an arbitrary linearly ordered `Fintype σ`, as everywhere in
`HJO/Macdonald/`; the `n ≥ 1` is absent, `σ` being allowed to be empty (the
conclusion then quantifies over no `j`, and over no least letter either). The field and the
genericity hypothesis are exactly those needed to *name* `P_λ[X_n]` at all
(`HJO.Mac.macPpoly`): nothing here spends any further arithmetic in `q` and `u`, and in particular
no corner of the parameter space is excluded beyond the one `macPpoly` already excludes.

## Main results

* `Finsupp.apply_le_of_toLex_le`: at the least index, a lexicographic comparison of exponent
  vectors gives a comparison of entries.
* `MvPolynomial.IsSymmetric.coeff_mapDomain`: a symmetric polynomial has equal coefficients at an
  exponent and at any permutation of it.
* `HJO.Mac.apply_le_partExp_of_mem_support_macPpoly`.

## References

This file proves `HJO.Mac.apply_le_partExp_of_mem_support_macPpoly`, about Macdonald's polynomials,
on the definitions `HJO.Sym.rowLenSeq`, `MvPolynomial.symmetricSubalgebra` and `HJO.Mac.macPpoly`
and the lemma `HJO.Mac.coeff_partExp_macPpoly`. The consumers are
`HJO.Mac.coeff_partExp_splitAt_macPpoly_eq` and `HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero`.
-/

@[expose] public section

open Finset MvPolynomial

/-! ### Two ingredients -/

namespace Finsupp

/-- **At the least index a lexicographic comparison is an entrywise one.** If `toLex a ≤ toLex b`
and `i` is a lower bound for the index type, then `a i ≤ b i`: either the two agree, or the least
index `k` at which they differ has `a k < b k`, and then `k = i` gives `a i < b i` while `i < k`
gives `a i = b i`.

This is the step written informally as "`1` is the least index at which `β` and
`(λ_1, …, λ_n)` differ and `β` is larger there". It fails at any other index. -/
theorem apply_le_of_toLex_le {σ : Type*} [LinearOrder σ] {a b : σ →₀ ℕ} {i : σ} (hi : IsBot i)
    (h : toLex a ≤ toLex b) : a i ≤ b i := by
  rcases h.lt_or_eq with hlt | heq
  · obtain ⟨k, hk, hklt⟩ := Finsupp.Lex.lt_iff.1 hlt
    rcases eq_or_lt_of_le (hi k) with rfl | hik
    · exact hklt.le
    · exact (hk i hik).le
  · exact le_of_eq (congrArg (fun p : σ →₀ ℕ => p i) (toLex_inj.mp heq))

end Finsupp

namespace MvPolynomial

/-- **A symmetric polynomial has the same coefficient at an exponent and at any permutation of
it.** Renaming along `w` carries the monomial `x^c` to `x^{w(c)}` and fixes the polynomial. -/
theorem IsSymmetric.coeff_mapDomain {σ R : Type*} [CommSemiring R] {f : MvPolynomial σ R}
    (hf : f.IsSymmetric) (w : Equiv.Perm σ) (c : σ →₀ ℕ) :
    coeff (Finsupp.mapDomain w c) f = coeff c f := by
  rw [← coeff_rename_mapDomain (⇑w) w.injective f c, hf w]

end MvPolynomial

/-! ### The degree bound -/

namespace HJO.Mac

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ}
  {u : K} {d : ℕ}

/-- **Every exponent occurring in `P_λ[X_n]` is bounded entrywise by
`λ_1`.** Here `i` is the least letter of the alphabet, so that `partExp σ μ i` is
`λ_1` — `partExp` being weakly decreasing (`HJO.Mac.antitone_partExp`) — and `j` is arbitrary; the
stated conclusion about the `n`th entry is the case `j = n`.

Let `c` be an exponent of `P_λ[X_n]` and let `β` be `c` with its entries at `i` and `j` exchanged.
`P_λ[X_n]` is symmetric, so `β` occurs too (`MvPolynomial.IsSymmetric.coeff_mapDomain`), hence
`β ≤_lex \bar\lambda` by `HJO.Mac.coeff_partExp_macPpoly`; and at the least letter that inequality
is an inequality of entries (`Finsupp.apply_le_of_toLex_le`), which reads `c j = β i ≤ λ_1`. -/
@[hjo "lem_dua_ppoly_degree"]
theorem apply_le_partExp_of_mem_support_macPpoly (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) {c : σ →₀ ℕ}
    (hc : c ∈ (macPpoly hqu μ : MvPolynomial σ K).support) {i : σ} (hi : IsBot i) (j : σ) :
    c j ≤ partExp σ μ i := by
  have hswap : Finsupp.mapDomain (Equiv.swap i j) c i = c j := by
    rw [← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply, Equiv.symm_swap,
      Equiv.swap_apply_left]
  have hmem : Finsupp.mapDomain (Equiv.swap i j) c ∈ (macPpoly hqu μ : MvPolynomial σ K).support :=
    mem_support_iff.mpr <| by
      rw [IsSymmetric.coeff_mapDomain
        (mem_symmetricHomogeneousSubmodule.1 (macPpoly hqu μ).2).1]
      exact mem_support_iff.mp hc
  exact hswap ▸ Finsupp.apply_le_of_toLex_le hi (toLex_le_of_mem_support_macPpoly hqu μ hmem)

end HJO.Mac
