/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.ConjugateSize
public import HJO.Macdonald.DualitySupportTransfer
public import HJO.Macdonald.PieriSupportFirst
public meta import HJO.Attr

/-! # The one-cell Pieri expansion at a longer index

`HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short`: `e₁P_ν` lies in the `𝕜`-span of the
`P_λ` with `λ` covering `ν` together with the `P_λ` with `|λ| = |ν|+1` and `λ_{l+1} = 0`, where `l`
is the number of indices `i` with `ν_i ≥ 1`.

## The route

The content is that `λ_{l+1} ≥ 1` and `c_λ ≠ 0` force `λ` to cover `ν`,
and that is proved at the conjugate. Write `ρ := ν'`.

* `ρ_1 = l`, the first row of the conjugate being the number of nonempty rows
  (`YoungDiagram.rowLen_transpose` and `HJO.Sym.lt_colLen_zero_iff_rowLen_ne_zero`, which is why the
  statement below spells `l` as `ν.colLen 0`).
* `λ'_1 ≥ l+1`, because `λ_{l+1} ≥ 1` puts a cell in row `l` of `λ` and hence `l+1` cells in the
  first column.
* `HJO.Ascent.coeff_transpose_ne_zero_of_coeff_ne_zero` moves `c_λ ≠ 0`
  to `b_{λ'} ≠ 0` in an expansion of `e₁P_ρ`, and `HJO.Mac.rowLen_zero_le_of_coeff_ne_zero` bounds
  `λ'_1 ≤ ρ_1+1 = l+1`. So `λ'_1 = ρ_1+1` exactly, which is the hypothesis
  `HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero` asks for, and that gives `λ'_i = ρ_i` for `i ≥ 2`.
* Hence `ρ_i ≤ λ'_i` entrywise, so `ρ ⊆ λ'` (`HJO.Sym.le_iff_rowLen_le`), so `ν ⊆ λ`
  (`YoungDiagram.transpose_mono` and `YoungDiagram.transpose_transpose`), and with `|λ| = |ν|+1`
  that is covering.

## The expansion, once

All four of the lemmas used here are stated at an arbitrary identity
`e₁P_ν = ∑_{μ ∈ S} c_μ P_μ` with `|μ| = |ν|+1` on `S`, and three of them are applied to the SAME
expansion at `ρ`. So the expansion is produced once, by
`HJO.Sym.exists_expansion_elemSymm_one_mul_macPfun`: `e₁P_ν` lies in `Λ_{|ν|+1}`
(`HJO.Sym.elemSymm_one_mul_macPfun_mem_lambdaComp`) and the `P_μ` of that degree are a basis of it
(`HJO.Sym.exists_basis_lambdaComp_macPfun`), so one expansion of that shape exists. That lemma and
`HJO.Sym.elemSymm_one_mul_macPfun_mem_span_of_coeff` -- which turns any criterion on the
coefficients into a span statement -- are the two halves of the earlier
`HJO.Sym.hasPfunPieriSupport_of_hasPfunPieriCoeff`, split apart because this result needs them at a
different target set and `HJO.Standing.hasPfunPieriSupport_param` needs the first one twice more.

## Which form is the main statement

The main statement is the span statement. The coefficient
form `HJO.Ascent.covers_or_rowLen_colLen_zero_eq_zero_of_coeff_ne_zero` is the real content and is
what `HJO.Standing.hasPfunPieriSupport_param` consumes: expansions in a basis being unique, "lies in
the span of this subfamily" and "the coefficients off the subfamily vanish" are the same statement,
and the second is the usable one.

## Genericity

At the standing field, because `HJO.Ascent.coeff_transpose_ne_zero_of_coeff_ne_zero` is: it runs on
`Ω`, which needs the parameter automorphism `ι∘τ` of the coefficient field.
`HJO.Mac.rowLen_zero_le_of_coeff_ne_zero` and `HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero` are both
available at an arbitrary pair carrying `AlgebraicIndependent ℤ ![q, u]`, and nothing else here
spends anything, so this result is at `𝕜` solely because the transfer is. See
`HJO/Macdonald/DualityOmegaPfun.lean`.

## Main results

* `HJO.Sym.exists_expansion_elemSymm_one_mul_macPfun`: `e₁P_ν` has an expansion in the `P_μ` of
  degree `|ν|+1`.
* `HJO.Sym.elemSymm_one_mul_macPfun_mem_span_of_coeff`: a criterion on the coefficients of every
  such expansion is a span statement.
* `HJO.Ascent.covers_or_rowLen_colLen_zero_eq_zero_of_coeff_ne_zero`,
  `HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short`.

## References

Lemma `HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short`, on
Definitions `HJO.Sym.Lambda`, `HJO.Sym.elemSymm`, `HJO.Sym.rowLenSeq`, `HJO.Sym.cells`,
`HJO.Sym.Covers`, `HJO.Sym.macPfun` and `HJO.Sym.rowLen_transpose_eq_natCard` and Lemmas
`HJO.Sym.elemSymm_one_mul_macPfun_mem_lambdaComp`, `HJO.Sym.exists_basis_lambdaComp_macPfun`,
`HJO.Sym.card_transpose`, `HJO.Sym.transpose_transpose`, `HJO.Sym.transpose_mono`,
`HJO.Mac.rowLen_zero_le_of_coeff_ne_zero`, `HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero` and
`HJO.Ascent.coeff_transpose_ne_zero_of_coeff_ne_zero`. The consumer is
`HJO.Standing.hasPfunPieriSupport_param`.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

/-! ### One expansion of `e₁P_ν`, and what a criterion on its coefficients says -/

/-- **`e₁P_ν` has an expansion in the `P_μ` with `|μ| = |ν|+1`.** It lies in `Λ_{|ν|+1}`
(`HJO.Sym.elemSymm_one_mul_macPfun_mem_lambdaComp`) and those `P_μ` are a basis of that graded piece
(`HJO.Sym.exists_basis_lambdaComp_macPfun`), so its coordinates there are such an expansion, with
the zero coefficients discarded.

This is the first half of `HJO.Sym.hasPfunPieriSupport_of_hasPfunPieriCoeff`, stated on its own
because the Pieri block applies it at three different indices. -/
theorem exists_expansion_elemSymm_one_mul_macPfun (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (ν : YoungDiagram) :
    ∃ (S : Finset YoungDiagram) (c : YoungDiagram → K),
      (∀ μ ∈ S, μ.card = ν.card + 1) ∧
      elemSymm K 1 * macPfun hqu ν = ∑ μ ∈ S, c μ • macPfun hqu μ := by
  classical
  obtain ⟨B, hB⟩ := exists_basis_lambdaComp_macPfun hqu (ν.card + 1)
  set x : LambdaComp K (ν.card + 1) :=
    ⟨elemSymm K 1 * macPfun hqu ν, elemSymm_one_mul_macPfun_mem_lambdaComp hqu ν⟩ with hxdef
  set r : {μ : YoungDiagram // μ.card = ν.card + 1} →₀ K := B.repr x with hrdef
  set c : YoungDiagram → K := fun μ => if hμ : μ.card = ν.card + 1 then r ⟨μ, hμ⟩ else 0 with hcdef
  have hcval : ∀ μ : {μ : YoungDiagram // μ.card = ν.card + 1}, c (μ : YoungDiagram) = r μ :=
    fun μ => by rw [hcdef]; exact dite_eq_iff.mpr (Or.inl ⟨μ.2, rfl⟩)
  have hinj : Set.InjOn (fun ρ : {μ : YoungDiagram // μ.card = ν.card + 1} => (ρ : YoungDiagram))
      r.support := fun _ _ _ _ hab => Subtype.ext hab
  refine ⟨r.support.image fun ρ : {μ : YoungDiagram // μ.card = ν.card + 1} =>
    (ρ : YoungDiagram), c, fun μ hμ => ?_, ?_⟩
  · obtain ⟨ρ, -, rfl⟩ := Finset.mem_image.mp hμ
    exact ρ.2
  · rw [Finset.sum_image hinj]
    have hx : (x : Lambda K) = ∑ μ ∈ r.support, r μ • (B μ : Lambda K) := by
      have h1 := B.linearCombination_repr x
      rw [Finsupp.linearCombination_apply, Finsupp.sum, ← hrdef] at h1
      have h2 := congrArg (Subtype.val (p := fun f => f ∈ LambdaComp K (ν.card + 1))) h1.symm
      rw [AddSubmonoidClass.coe_finsetSum] at h2
      simpa only [SetLike.val_smul] using h2
    rw [show elemSymm K 1 * macPfun hqu ν = (x : Lambda K) from rfl, hx]
    exact Finset.sum_congr rfl fun μ _ => by rw [hcval μ, hB μ]

/-- **A criterion on the coefficients of every expansion of `e₁P_ν` is a span statement.** If a
nonzero coefficient always has its index in `T`, then `e₁P_ν` lies in the span of the `P_μ` with
`μ ∈ T`: take the expansion of `HJO.Sym.exists_expansion_elemSymm_one_mul_macPfun` and discard the
zero terms.

This is the second half of `HJO.Sym.hasPfunPieriSupport_of_hasPfunPieriCoeff`, stated for an
arbitrary target set because `HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short` needs it
at a union. -/
theorem elemSymm_one_mul_macPfun_mem_span_of_coeff (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (ν : YoungDiagram) (T : Set YoungDiagram)
    (h : ∀ (S : Finset YoungDiagram) (c : YoungDiagram → K), (∀ μ ∈ S, μ.card = ν.card + 1) →
      elemSymm K 1 * macPfun hqu ν = ∑ μ ∈ S, c μ • macPfun hqu μ →
      ∀ μ ∈ S, c μ ≠ 0 → μ ∈ T) :
    elemSymm K 1 * macPfun hqu ν ∈ Submodule.span K (macPfun hqu '' T) := by
  classical
  obtain ⟨S, c, hcard, hsum⟩ := exists_expansion_elemSymm_one_mul_macPfun hqu ν
  rw [hsum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  rcases eq_or_ne (c μ) 0 with h0 | h0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, h S c hcard hsum μ hμ h0, rfl⟩)

end HJO.Sym

/-! ### The covering-or-short expansion -/

namespace HJO.Ascent

open HJO.Sym HJO.Mac

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **The content of `HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short`, in
coordinates**: in an expansion `e₁P_ν = ∑_{μ ∈ S} c_μ P_μ` with `|μ| = |ν|+1` on `S`, an index with
a nonzero coefficient either covers `ν` or has `λ_{l+1} = 0`, where `l = ν.colLen 0` is the number
of nonempty rows of `ν`.

The proof, at the conjugate `ρ := ν'`. If `λ_{l+1} ≥ 1` then `λ'_1 ≥ l+1`, while
`HJO.Ascent.coeff_transpose_ne_zero_of_coeff_ne_zero` and `HJO.Mac.rowLen_zero_le_of_coeff_ne_zero`
at an expansion of `e₁P_ρ` give `λ'_1 ≤ ρ_1+1 = l+1`; so `λ'_1 = ρ_1+1`,
`HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero` gives `λ'_i = ρ_i` for `i ≥ 2`, and `ρ ⊆ λ'` entrywise,
whence `ν ⊆ λ`. -/
theorem covers_or_rowLen_colLen_zero_eq_zero_of_coeff_ne_zero (ν : YoungDiagram)
    (S : Finset YoungDiagram) (c : YoungDiagram → K)
    (hcard : ∀ μ ∈ S, μ.card = ν.card + 1)
    (hexp : elemSymm K 1 * macPfun (Standing.algebraicIndependent_paramQUnit K) ν
      = ∑ μ ∈ S, c μ • macPfun (Standing.algebraicIndependent_paramQUnit K) μ)
    {lam : YoungDiagram} (hlam : lam ∈ S) (hc : c lam ≠ 0) :
    Covers lam ν ∨ lam.rowLen (ν.colLen 0) = 0 := by
  by_cases hz : lam.rowLen (ν.colLen 0) = 0
  · exact Or.inr hz
  refine Or.inl ⟨?_, hcard lam hlam⟩
  -- one expansion of `e₁P_ρ` at the conjugate `ρ = ν'`, shared by the three lemmas below
  obtain ⟨T, b, hTcard, hTexp⟩ :=
    exists_expansion_elemSymm_one_mul_macPfun (Standing.algebraicIndependent_paramQUnit K)
      ν.transpose
  obtain ⟨hmemT, hbne⟩ :=
    coeff_transpose_ne_zero_of_coeff_ne_zero K ν S T c b hexp hTexp hlam hc
  -- `ρ_1 = l`, and `λ'_1 ≥ l+1` because `λ_{l+1} ≥ 1`
  have hρ1 : ν.transpose.rowLen 0 = ν.colLen 0 := YoungDiagram.rowLen_transpose ν 0
  have hup : ν.colLen 0 < lam.transpose.rowLen 0 := by
    rw [YoungDiagram.rowLen_transpose]
    exact lt_colLen_zero_iff_rowLen_ne_zero.mpr hz
  -- `λ'_1 ≤ ρ_1 + 1`, so the two are equal
  have hdown := rowLen_zero_le_of_coeff_ne_zero (Standing.algebraicIndependent_paramQUnit K)
    ν.transpose T b hTcard hTexp hmemT hbne
  have hone : lam.transpose.rowLen 0 = ν.transpose.rowLen 0 + 1 := by omega
  -- agreement from the second row on, hence containment of the conjugates
  have htop := rowLen_succ_eq_of_coeff_ne_zero (Standing.algebraicIndependent_paramQUnit K)
    ν.transpose T b hTcard hTexp hmemT hbne hone
  have hle : ν.transpose ≤ lam.transpose := le_iff_rowLen_le.mpr fun i => by
    cases i with
    | zero => omega
    | succ k => exact (htop k).ge
  have hfinal := YoungDiagram.transpose_mono hle
  rwa [YoungDiagram.transpose_transpose, YoungDiagram.transpose_transpose] at hfinal

/-- **The one-cell Pieri expansion at a longer index.** `e₁P_ν` lies in
the `𝕜`-span of the `P_λ` with `λ ⋗ ν` together with the `P_λ` with `|λ| = |ν|+1` and
`λ_{l+1} = 0`, where `l = ν.colLen 0` is the number of indices `i` with `ν_i ≥ 1`
(`HJO.Sym.lt_colLen_zero_iff_rowLen_ne_zero`).

The coefficient form `HJO.Ascent.covers_or_rowLen_colLen_zero_eq_zero_of_coeff_ne_zero` read
through `HJO.Sym.elemSymm_one_mul_macPfun_mem_span_of_coeff`.

At the standing field, because `HJO.Ascent.coeff_transpose_ne_zero_of_coeff_ne_zero` is: see the
module docstring. -/
@[hjo "lem_pie_pfun_support_long"]
theorem elemSymm_one_mul_macPfun_mem_span_covers_or_short (ν : YoungDiagram) :
    elemSymm K 1 * macPfun (Standing.algebraicIndependent_paramQUnit K) ν
      ∈ Submodule.span K (macPfun (Standing.algebraicIndependent_paramQUnit K) ''
          ({μ : YoungDiagram | Covers μ ν} ∪
            {μ : YoungDiagram | μ.card = ν.card + 1 ∧ μ.rowLen (ν.colLen 0) = 0})) :=
  elemSymm_one_mul_macPfun_mem_span_of_coeff _ ν _ fun S c hcard hexp μ hμ h0 =>
    (covers_or_rowLen_colLen_zero_eq_zero_of_coeff_ne_zero K ν S c hcard hexp hμ h0).imp id
      fun h => ⟨hcard μ hμ, h⟩

end HJO.Ascent
