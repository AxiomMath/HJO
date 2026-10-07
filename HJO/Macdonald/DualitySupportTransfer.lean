/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.DualityOmegaPfun
public import HJO.Macdonald.PfunBasisAll
public meta import HJO.Attr

/-! # The one-cell Pieri support transfers to the conjugates

`HJO.Ascent.coeff_transpose_ne_zero_of_coeff_ne_zero`: if `e₁P_ν = ∑_κ c_κ P_κ` and
`e₁P_{ν'} = ∑_κ b_κ P_κ`, then a nonzero `c_λ` forces a nonzero `b_{λ'}`.

## The route

Apply `Ω` to the first expansion. It is a ring endomorphism with `Ω(cF) = ι(τ(c))Ω(F)`
(`HJO.Ascent.dualityOmega_smul`), it scales `e₁ = p₁` by the nonzero `-q(1-u)/(1-q)`
(`HJO.Ascent.omegaScalar_ne_zero`), and by `HJO.Ascent.exists_smul_dualityOmega_macPfun` it carries
each `P_κ` to a nonzero multiple of `P_{κ'}`. So the first expansion becomes a second expansion of
`e₁P_{ν'}`, indexed by the conjugates, and the two are compared coefficientwise.

## What the comparison is, and what it is not

The usual argument compares in `HJO.Sym.exists_basis_lambdaComp_macPfun`, the basis of the single
graded piece `Λ_{d+1}`, and therefore has to know that the partitions of `d+1` are finite and that
`κ ↦ κ'` is a bijection of them. Here the comparison is in `HJO.Sym.exists_basis_macPfun`, the basis
of ALL of `Λ`: linear independence over the whole index type compares the two sums directly, and
`κ ↦ κ'` needs only to be injective, which it is because it is an involution
(`YoungDiagram.transpose_transpose`, which is `HJO.Sym.transpose_transpose`).

That is why the statement below carries **no** hypothesis on the sizes of the indices. The usual
`|κ| = |ν|+1` and `|λ| = |ν|+1` were there to place the comparison inside one graded piece;
comparing in the basis of `Λ` makes them unnecessary, so the statement here is strictly stronger
than the usual one and needs neither `HJO.Sym.finite_setOf_card_eq` nor `HJO.Sym.card_transpose`.
Nothing downstream is weakened: `HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short`, the
only consumer, has the size conditions in hand and simply does not pass them.

## The shape of the two expansions

Both index sets are `Finset`s of diagrams with an arbitrary coefficient function, exactly as in
`HJO.Sym.HasPfunPieriCoeff` and `HJO.Mac.rowLen_zero_le_of_coeff_ne_zero`; the families
indexed by all partitions of `d+1` are the special case where the `Finset` is everything. Since the
zero coefficients may have been discarded, the conclusion has to say that `λ'` is among the retained
indices as well as that its coefficient is nonzero -- when the index set is all partitions of `d+1`
the first half is vacuous, and the consumers need both.

## Genericity

`γ_μ ≠ 0` is spent through `HJO.Ascent.exists_smul_dualityOmega_macPfun`, and `Ω` exists only
because `𝕜` has the parameter automorphism `ι∘τ`; so this statement is at the standing field for the
same reason its input is. See the module docstring of `HJO/Macdonald/DualityOmegaPfun.lean`.

## Main results

* `HJO.Ascent.dualityOmega_elemSymm_one`: `Ω(e₁) = -q(1-u)/(1-q) · e₁`.
* `HJO.Ascent.coeff_transpose_ne_zero_of_coeff_ne_zero`.

## References

The lemma `HJO.Ascent.coeff_transpose_ne_zero_of_coeff_ne_zero` on duality, using
`HJO.Sym.Lambda`, `HJO.Sym.elemSymm`, `HJO.Sym.rowLenSeq`, `HJO.Sym.cells`, `HJO.Sym.macPfun` and
`HJO.Sym.rowLen_transpose_eq_natCard`. The consumer is
`HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short`.
-/

@[expose] public section

namespace HJO.Ascent

open HJO.Sym

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **`Ω` scales `e₁`**, by `-q(1-u)/(1-q)`, which is nonzero (`HJO.Ascent.omegaScalar_ne_zero`).
`e₁ = p₁` (`HJO.Sym.elemSymm_one`) and `Ω` scales each power sum by its own scalar
(`HJO.Ascent.dualityOmega`). -/
theorem dualityOmega_elemSymm_one :
    dualityOmega K (elemSymm K 1) = omegaScalar K 0 • elemSymm K 1 := by
  rw [elemSymm_one, MvPolynomial.smul_eq_C_mul, ← dualityOmega_powerSum K 0]

/-- **The one-cell Pieri support transfers to the conjugates.** Given
expansions `e₁P_ν = ∑_{κ ∈ S} c_κ P_κ` and `e₁P_{ν'} = ∑_{κ ∈ T} b_κ P_κ` and an index `λ ∈ S` with
`c_λ ≠ 0`, the conjugate `λ'` lies in `T` and `b_{λ'} ≠ 0`.

Applying `Ω` to the first expansion turns it into an expansion of `e₁P_{ν'}` indexed by the
conjugates, with coefficients `ι(τ(c_κ))g_κ` where `g_κ` is the nonzero scalar of
`HJO.Ascent.exists_smul_dualityOmega_macPfun` at `κ`; comparing it with the second in the basis
`HJO.Sym.exists_basis_macPfun` gives `s·g_ν·b_ρ = ι(τ(c_{ρ'}))g_{ρ'}` for every `ρ`, and at `ρ = λ'`
the right side is nonzero.

No hypothesis on the sizes of the indices is needed: see the module docstring. -/
@[hjo "lem_dua_support_transfer"]
theorem coeff_transpose_ne_zero_of_coeff_ne_zero (ν : YoungDiagram)
    (S T : Finset YoungDiagram) (c b : YoungDiagram → K)
    (hc : elemSymm K 1 * macPfun (Standing.algebraicIndependent_paramQUnit K) ν
      = ∑ κ ∈ S, c κ • macPfun (Standing.algebraicIndependent_paramQUnit K) κ)
    (hb : elemSymm K 1 * macPfun (Standing.algebraicIndependent_paramQUnit K) ν.transpose
      = ∑ κ ∈ T, b κ • macPfun (Standing.algebraicIndependent_paramQUnit K) κ)
    {lam : YoungDiagram} (hlam : lam ∈ S) (hclam : c lam ≠ 0) :
    lam.transpose ∈ T ∧ b lam.transpose ≠ 0 := by
  classical
  have hqu := Standing.algebraicIndependent_paramQUnit K
  -- the scalars of `HJO.Ascent.exists_smul_dualityOmega_macPfun`, one per index
  choose g hg0 hg using fun κ : YoungDiagram => exists_smul_dualityOmega_macPfun K κ
  -- `(P_κ)` is independent over ALL partitions
  obtain ⟨B, hB⟩ := exists_basis_macPfun hqu
  have hind : LinearIndependent K (macPfun hqu) := by
    rw [← funext hB]; exact B.linearIndependent
  -- `Ω` applied to the first expansion, read against the second
  have key : ∑ κ ∈ T, (omegaScalar K 0 * g ν * b κ) • macPfun hqu κ
      = ∑ κ ∈ S, (paramSwapInvHom K (c κ) * g κ) • macPfun hqu κ.transpose := by
    calc ∑ κ ∈ T, (omegaScalar K 0 * g ν * b κ) • macPfun hqu κ
        = (omegaScalar K 0 * g ν) • ∑ κ ∈ T, b κ • macPfun hqu κ := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun κ _ => (smul_smul _ _ _).symm
      _ = (omegaScalar K 0 * g ν) • (elemSymm K 1 * macPfun hqu ν.transpose) := by rw [hb]
      _ = dualityOmega K (elemSymm K 1 * macPfun hqu ν) := by
          rw [map_mul, dualityOmega_elemSymm_one, hg ν, smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = ∑ κ ∈ S, (paramSwapInvHom K (c κ) * g κ) • macPfun hqu κ.transpose := by
          rw [hc, map_sum]
          exact Finset.sum_congr rfl fun κ _ => by rw [dualityOmega_smul, hg κ, smul_smul]
  -- both sums, read over one index set with the coefficients extended by zero
  set U : Finset YoungDiagram := T ∪ S.image YoungDiagram.transpose with hUdef
  set F : YoungDiagram → K :=
    fun κ => if κ ∈ T then omegaScalar K 0 * g ν * b κ else 0 with hFdef
  set G : YoungDiagram → K :=
    fun ρ => if ρ.transpose ∈ S then paramSwapInvHom K (c ρ.transpose) * g ρ.transpose
      else 0 with hGdef
  have hTU : T ⊆ U := Finset.subset_union_left
  have hSU : S.image YoungDiagram.transpose ⊆ U := Finset.subset_union_right
  have hFsum : ∑ κ ∈ U, F κ • macPfun hqu κ
      = ∑ κ ∈ T, (omegaScalar K 0 * g ν * b κ) • macPfun hqu κ := by
    rw [← Finset.sum_subset hTU fun κ _ hκ => by rw [hFdef]; simp [hκ]]
    exact Finset.sum_congr rfl fun κ hκ => by rw [hFdef]; simp [hκ]
  have hGsum : ∑ ρ ∈ U, G ρ • macPfun hqu ρ
      = ∑ κ ∈ S, (paramSwapInvHom K (c κ) * g κ) • macPfun hqu κ.transpose := by
    rw [← Finset.sum_subset hSU fun ρ _ hρ => by
      rw [hGdef]
      have : ρ.transpose ∉ S := fun hmem => hρ (Finset.mem_image.mpr
        ⟨ρ.transpose, hmem, YoungDiagram.transpose_transpose ρ⟩)
      simp [this]]
    rw [Finset.sum_image fun x _ y _ h => YoungDiagram.transpose_eq_iff.mp h]
    exact Finset.sum_congr rfl fun κ hκ => by rw [hGdef]; simp [hκ]
  -- linear independence: the two coefficient functions agree on `U`
  have hzero : ∑ κ ∈ U, (F κ - G κ) • macPfun hqu κ = 0 := by
    rw [Finset.sum_congr rfl fun κ _ => sub_smul (F κ) (G κ) _, Finset.sum_sub_distrib, hFsum,
      hGsum, key, sub_self]
  have heq := linearIndependent_iff'.mp hind U (fun κ => F κ - G κ) hzero
  -- read the agreement at `λ'`
  have hmemU : lam.transpose ∈ U :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨lam, hlam, rfl⟩)
  have hGlam : G lam.transpose = paramSwapInvHom K (c lam) * g lam := by
    rw [hGdef]; simp [hlam]
  have hGne : G lam.transpose ≠ 0 := by
    rw [hGlam]
    exact mul_ne_zero (fun h => hclam ((paramSwapInvHom K).injective (by rw [h, map_zero])))
      (hg0 lam)
  have hFne : F lam.transpose ≠ 0 := by
    rw [sub_eq_zero.mp (heq _ hmemU)]
    exact hGne
  have hmemT : lam.transpose ∈ T := by
    by_contra hT
    rw [hFdef] at hFne
    simp [hT] at hFne
  refine ⟨hmemT, fun h0 => hFne ?_⟩
  rw [hFdef]
  simp [hmemT, h0]

end HJO.Ascent
