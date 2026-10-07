/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.Duality
public import HJO.Macdonald.HtildeSpan
public meta import HJO.Attr

/-! # What the duality maps do: the cell sum, and injectivity

Two statements about the maps built in `HJO/Macdonald/Duality.lean`.

* `HJO.Sym.paramSwapHom_cellSum` -- the exchange carries the cell sum of a partition to that of its
  conjugate, `τ(B_μ) = B_{μ'}`.
* `HJO.Sym.plethDivide_paramUInvLambda_injective` -- `f ↦ 𝒴(ȷ(f))` is injective.

## `HJO.Sym.paramSwapHom_cellSum` is a statement about `Prod.swap`, not about the parameters

`HJO.Sym.cellSum q u μ` is `∑_{c ∈ cells μ} q^{c.2} u^{c.1}`, and conjugating a partition is
`YoungDiagram.transpose`, whose membership is `c ∈ μ.transpose ↔ c.swap ∈ μ`. So exchanging the two
parameters and transposing the diagram are the SAME reindexing of one sum, and the underlying fact
is `HJO.Sym.cellSum_swap` below: `cellSum u q μ = cellSum q u μ.transpose` over any commutative
semiring, with no parameters and no genericity. The `Vocabulary` docstring for `cellSum` already
asserts this in prose ("`cellSum u q μ` is the cell sum of the conjugate partition"); it is proved
here.

The statement here is then that general fact read at `τ`, which sends `q` to `u` and `u` to `q`.
Two things make that step a rewrite rather than an argument: `τ` is a ring homomorphism, so it
passes through the sum and the powers, and `HJO.Ascent.paramSwapHom_paramQ`/`_paramU` say where it
sends the two indeterminates.

## `HJO.Sym.plethDivide_paramUInvLambda_injective` is a composite of two injections

`𝒴(ȷ(f))` is `plethDivide u (coeffSubst υ f)`, and each factor is injective at the standing field
for a different reason:

* `ȷ = coeffSubst υ` is `MvPolynomial.map υ`, and `υ` is a homomorphism of fields, hence injective;
  `MvPolynomial.map_injective` lifts that to `Λ`.
* `𝒴 = plethDivide u` is `diagScale` at the scalars `(1 - u⁻¹^{i+1})⁻¹`, and a diagonal scaling with
  every scalar nonzero is injective because `diagScale` at the reciprocal scalars is a left inverse
  (`HJO.Sym.diagScale_injective`, the one lemma this file adds to that pile -- the composition law
  and the unit law were already in `Htilde.lean` and `HtildeSpan.lean`). The scalars are nonzero
  exactly because no positive power of `u` is `1`, which at `𝕜` is
  `HJO.Standing.paramU_pow_succ_ne_one`.

THE SECOND REASON IS THE ONE THAT CONSTRAINS THE STATEMENT, and it is why it is stated at the
standing field rather than over an arbitrary field. At a root of unity some scalar of `plethDivide`
vanishes and `𝒴` is genuinely NOT injective -- that corner is recorded in
`HJO/Macdonald/Htilde.lean` and in `HJO/Macdonald/HtildeSpan.lean`, and it is the same
degeneracy that makes the nonvanishing clause of a Macdonald eigenbasis fail. So the general-field
reading of this statement is false, and the algebraically independent pair is not decoration.
-/

@[expose] public section

namespace HJO.Sym

open Finset

/-! ### Diagonal scalings with nonzero scalars are injective -/

variable {K : Type*} [Field K] [Algebra ℚ K]

omit [Algebra ℚ K] in
/-- **A diagonal scaling with every scalar nonzero is injective.** The scaling at the reciprocal
scalars is a left inverse, by `HJO.Sym.diagScale_diagScale` (`HJO/Macdonald/Htilde.lean`) and
`HJO.Sym.diagScale_one_eq_self` (`HJO/Macdonald/HtildeSpan.lean`). -/
theorem diagScale_injective {c : ℕ → K} (hc : ∀ i, c i ≠ 0) :
    Function.Injective (diagScale c) := by
  have hleft : Function.LeftInverse (diagScale fun i => (c i)⁻¹) (diagScale c) := fun f => by
    rw [diagScale_diagScale]
    simpa only [inv_mul_cancel₀ (hc _)] using diagScale_one_eq_self f
  exact hleft.injective

/-! ### The exchange and the cell sum -/

/-- **Exchanging the two parameters in the cell sum transposes the diagram.**
`cellSum u q μ = cellSum q u μ'`, over any commutative semiring and with no hypothesis on the
parameters.

Both sides are one sum reindexed: the cells of `μ'` are the cells of `μ` with their coordinates
exchanged (`YoungDiagram.mem_transpose`), and the weight `q^j u^i` of a cell becomes the weight
`u^j q^i` of its transpose. -/
theorem cellSum_swap {R : Type*} [CommSemiring R] (q u : R) (μ : YoungDiagram) :
    cellSum u q μ = cellSum q u μ.transpose :=
  Finset.sum_equiv (Equiv.prodComm ℕ ℕ)
    (fun c => by
      simp only [cells, YoungDiagram.mem_cells, Equiv.prodComm_apply, YoungDiagram.mem_transpose,
        Prod.swap_swap])
    (fun c _ => by simp only [cellWeight, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
      mul_comm])

/-- **The exchange carries the cell sum to that of the conjugate.**
`τ(B_μ) = B_{μ'}` at the standing coefficient field.

`HJO.Sym.cellSum_swap` is the content; `τ` being a ring homomorphism passes it through the sum and
the powers, and `HJO.Ascent.paramSwapHom_paramQ`/`_paramU` say that it sends `q` to `u` and `u` to
`q`. -/
@[hjo "lem_dua_swap_bmu"]
theorem paramSwapHom_cellSum (K : Type*) [Field K] [Algebra ℚ K] [Algebra Ascent.ParamRing K]
    [IsFractionRing Ascent.ParamRing K] (μ : YoungDiagram) :
    Ascent.paramSwapHom K (cellSum (Ascent.paramQ K) (Ascent.paramU K) μ)
      = cellSum (Ascent.paramQ K) (Ascent.paramU K) μ.transpose := by
  rw [← cellSum_swap]
  simp only [cellSum, cellWeight, map_sum, map_mul, map_pow, Ascent.paramSwapHom_paramQ,
    Ascent.paramSwapHom_paramU]

/-! ### The plethystic substitution of the modified family is injective -/

/-- **`HJO.Sym.plethDivide_paramUInvLambda_injective`: `f ↦ 𝒴(ȷ(f))` is injective** at the standing
coefficient field.

A composite of two injections. `ȷ` is `MvPolynomial.map υ` for a homomorphism of fields, so
`MvPolynomial.map_injective` applies; `𝒴` is a diagonal scaling whose scalars
`(1 - u⁻¹^{i+1})⁻¹` are nonzero because no positive power of `u` is `1`
(`HJO.Standing.paramU_pow_succ_ne_one`).

Stated at `𝕜` on purpose: at a root of unity a scalar of `𝒴` vanishes and the map is NOT injective,
so this is one of the statements whose general-field reading is false. -/
@[hjo "lem_dua_pleth_injective"]
theorem plethDivide_paramUInvLambda_injective (K : Type*) [Field K] [Algebra ℚ K]
    [Algebra Ascent.ParamRing K] [IsFractionRing Ascent.ParamRing K] :
    Function.Injective fun f : Lambda K =>
      plethDivide (Ascent.paramU K) (coeffSubst (Ascent.paramUInvHom K) f) := by
  have hscal : ∀ i : ℕ, (1 - (Ascent.paramU K)⁻¹ ^ (i + 1))⁻¹ ≠ 0 := by
    intro i
    refine inv_ne_zero fun hc => Standing.paramU_pow_succ_ne_one K i ?_
    rw [inv_pow, sub_eq_zero, eq_comm, inv_eq_one] at hc
    exact hc
  exact (diagScale_injective hscal).comp
    (MvPolynomial.map_injective _ (Ascent.paramUInvHom K).injective)

end HJO.Sym
