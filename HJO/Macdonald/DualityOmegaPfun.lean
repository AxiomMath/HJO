/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.DualityOmegaPleth
public import HJO.Macdonald.DualitySwapHtilde
public meta import HJO.Attr

/-! # The duality map carries Macdonald's `P` to its conjugate, up to a scalar

`HJO.Ascent.exists_smul_dualityOmega_macPfun`: for a partition `μ` there is a nonzero `c ∈ 𝕜` with
`Ω(P_μ) = c · P_{μ'}`.

## The route, and why nothing here is new mathematics

The proof transports the statement along `Φ : f ↦ 𝒴(ȷ(f))`, under which `H̃` is `J` rescaled by one
nonzero scalar per index (`HJO.Sym.macHtilde`), and the corresponding statement for `H̃` is
`HJO.Standing.exists_smul_dualitySwap_macHtilde`, already proved. Every ingredient is available:

* `HJO.Ascent.plethDivide_paramUInvLambda_dualityOmega` is
  `Φ ∘ Ω = Θ ∘ Φ`, the transport itself;
* `HJO.Standing.exists_smul_dualitySwap_macHtilde` is `Θ(H̃_μ) = b H̃_{μ'}`
  with `b ≠ 0`;
* `HJO.Sym.plethDivide_paramUInvLambda_injective` turns an identity
  between the images back into one between the arguments;
* `HJO.Sym.normalisingProduct_ne_zero` is `γ_μ ≠ 0`, which is what lets the
  statement pass from `J_μ = γ_μ P_μ` to `P_μ`.

So the file adds the three semilinearity lemmas the transport needs and runs the two steps.

## The scalar, and why it is not computed

The usual computation evaluates `τ(u^{-n(μ)}) = q^{-n(μ)}` and writes the scalar out as
`υ(a)γ_{μ'}ι(τ(γ_μ))^{-1}` with `a = q^{-n(μ)}b u^{n(μ')}`. The statement asserts only that some
nonzero scalar works, and no consumer reads its value --
`HJO.Ascent.coeff_transpose_ne_zero_of_coeff_ne_zero`, the only one, uses nothing but `g ≠ 0`. So
`τ(u^{-n(μ)})` is left unevaluated and shown nonzero instead, `τ` being injective; that is one lemma
rather than three and loses nothing. Each of the four factors is nonzero for its own reason,
recorded at the `have` that produces it.

## Where the scalar's nonvanishing comes from

`u^{n(μ)} ≠ 0` is `HJO.Standing.paramU_ne_zero`; `b ≠ 0` comes with
`HJO.Standing.exists_smul_dualitySwap_macHtilde`; `γ_μ ≠ 0` is `HJO.Sym.normalisingProduct_ne_zero`,
and it is the one that genuinely needs the parameters to be indeterminates -- at `u = 1` every
factor of `γ_μ` vanishes for a nonempty `μ`, so `J_μ = 0` and the conclusion at `P_μ` cannot be
recovered from the one at `J_μ` at all. `τ` and `υ` being injective is free, a ring endomorphism of
a field being injective.

## Why this lemma is stated at the standing field

`Ω`, `Θ` and `ȷ` each act on the coefficients through a nontrivial automorphism of `𝕜`, and a
general field of characteristic zero has none -- over `ℝ` the only ring endomorphism is the
identity. So the general-field reading of this lemma is not a weaker true statement, it is not a
statement at all, exactly as for `HJO.Standing.exists_smul_dualitySwap_macHtilde` and
`HJO.Ascent.plethDivide_paramUInvLambda_dualityOmega`. The nonvanishing of `c` also fails at the
degenerate parameters: at a root of unity of `u` the scalars of `𝒴` have a zero denominator and
`H̃_μ` itself vanishes.

## Main results

* `HJO.Ascent.dualityOmega_smul`, `HJO.Ascent.plethDivide_paramUInvLambda_smul`: `Ω` is
  `ι∘τ`-semilinear and `Φ` is `υ`-semilinear.
* `HJO.Ascent.plethDivide_paramUInvLambda_macJfun`: `Φ(J_μ) = u^{-n(μ)} H̃_μ`.
* `HJO.Ascent.exists_smul_dualityOmega_macJfun`: the statement at Macdonald's integral form `J`.
* `HJO.Ascent.exists_smul_dualityOmega_macPfun`.

## References

This file proves `HJO.Ascent.exists_smul_dualityOmega_macPfun`, the duality for `P`, on Definitions
`HJO.Sym.Lambda`, `HJO.Sym.rowLenSeq`, `HJO.Sym.macPfun`, `HJO.Sym.rowLen_transpose_eq_natCard` and
`HJO.Ascent.dualityOmega`. The consumer is `HJO.Ascent.coeff_transpose_ne_zero_of_coeff_ne_zero`.
-/

@[expose] public section

namespace HJO.Ascent

open HJO.Sym

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-! ### The three semilinearities -/

/-- **`Ω` is `ι∘τ`-semilinear**, `Ω(cF) = ι(τ(c))Ω(F)`: it is a ring homomorphism whose restriction
to the coefficients is `ι∘τ` (`HJO.Ascent.dualityOmega_C`), and a scalar multiple is a product with
a constant. This is the clause of `HJO.Ascent.dualityOmega` used to push `Ω` through an
expansion. -/
theorem dualityOmega_smul (c : K) (f : Lambda K) :
    dualityOmega K (c • f) = paramSwapInvHom K c • dualityOmega K f := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, dualityOmega_C, MvPolynomial.smul_eq_C_mul]

/-- **`Φ = 𝒴 ∘ ȷ` is `υ`-semilinear**, `Φ(cF) = υ(c)Φ(F)`: `ȷ` twists the scalar by `υ`
(`HJO.Sym.coeffSubst_smul`) and `𝒴` is `𝕜`-linear, being a `𝕜`-algebra map. This is the opening
remark in the proof of `HJO.Ascent.plethDivide_paramUInvLambda_dualityOmega`, restated here because
the present lemma is where it is spent. -/
theorem plethDivide_paramUInvLambda_smul (c : K) (f : Lambda K) :
    plethDivide (paramU K) (paramUInvLambda K (c • f))
      = paramUInvHom K c • plethDivide (paramU K) (paramUInvLambda K f) := by
  rw [paramUInvLambda, coeffSubst_smul, map_smul]

/-! ### `Φ` at Macdonald's integral form -/

/-- **`Φ(J_μ) = u^{-n(μ)} H̃_μ`**: `H̃_μ` is by definition
`u^{n(μ)}Φ(J_μ)` (`HJO.Sym.macHtilde`) and `u^{n(μ)}` is invertible, `u ≠ 0` at the standing field
(`HJO.Standing.paramU_ne_zero`). -/
theorem plethDivide_paramUInvLambda_macJfun (μ : YoungDiagram) :
    plethDivide (paramU K) (paramUInvLambda K
        (macJfun (Standing.algebraicIndependent_paramQUnit K) μ))
      = (paramU K ^ rowOffsetSum μ)⁻¹ •
          macHtilde (paramUInvHom K) (Standing.algebraicIndependent_paramQUnit K) μ := by
  rw [macHtilde, smul_smul, inv_mul_cancel₀
    (pow_ne_zero _ (Standing.paramU_ne_zero K)), one_smul]
  rfl

/-! ### The statement at `J`, and then at `P` -/

/-- **The statement at Macdonald's integral form**: there is a nonzero `a ∈ 𝕜` with
`Ω(J_μ) = a J_{μ'}`.

Both sides are compared through `Φ`, which is injective
(`HJO.Sym.plethDivide_paramUInvLambda_injective`). On the left `Φ(Ω(J_μ)) = Θ(Φ(J_μ))`
(`HJO.Ascent.plethDivide_paramUInvLambda_dualityOmega`) is
`Θ(u^{-n(μ)}H̃_μ) = τ(u^{-n(μ)})b H̃_{μ'}` by the semilinearity of `Θ` and
`HJO.Standing.exists_smul_dualitySwap_macHtilde`; on the right `Φ(υ(a)J_{μ'}) = a Φ(J_{μ'})` because
`υ` is an involution, and `Φ(J_{μ'}) = u^{-n(μ')}H̃_{μ'}`. Choosing
`a := τ(u^{-n(μ)}) · b · u^{n(μ')}` makes the two agree, and the witness is `υ(a)`. -/
theorem exists_smul_dualityOmega_macJfun (μ : YoungDiagram) :
    ∃ a : K, a ≠ 0 ∧
      dualityOmega K (macJfun (Standing.algebraicIndependent_paramQUnit K) μ)
        = a • macJfun (Standing.algebraicIndependent_paramQUnit K) μ.transpose := by
  obtain ⟨b, hb0, hb⟩ := Standing.exists_smul_dualitySwap_macHtilde K μ
  have hu : paramU K ≠ 0 := Standing.paramU_ne_zero K
  have hpow : ∀ ν : YoungDiagram, paramU K ^ rowOffsetSum ν ≠ 0 := fun ν => pow_ne_zero _ hu
  set A : K := paramSwapHom K ((paramU K ^ rowOffsetSum μ)⁻¹) * b *
    paramU K ^ rowOffsetSum μ.transpose with hAdef
  have hA0 : A ≠ 0 :=
    mul_ne_zero (mul_ne_zero (fun h => (inv_ne_zero (hpow μ)) ((paramSwapHom K).injective
      (by rw [h, map_zero]))) hb0) (hpow μ.transpose)
  refine ⟨paramUInvHom K A, fun h => hA0 ((paramUInvHom K).injective (by rw [h, map_zero])), ?_⟩
  refine plethDivide_paramUInvLambda_injective K ?_
  change plethDivide (paramU K) (paramUInvLambda K _)
    = plethDivide (paramU K) (paramUInvLambda K _)
  rw [plethDivide_paramUInvLambda_dualityOmega, plethDivide_paramUInvLambda_macJfun,
    dualitySwap_smul, hb, smul_smul, plethDivide_paramUInvLambda_smul,
    paramUInvHom_involutive, plethDivide_paramUInvLambda_macJfun, smul_smul, hAdef]
  congr 1
  field_simp

/-- **The duality map carries `P_μ` to `P_{μ'}` up to a nonzero scalar.**
There is a nonzero `c ∈ 𝕜` with `Ω(P_μ) = c · P_{μ'}`.

`J_κ = γ_κ P_κ` with `γ_κ ≠ 0` (`HJO.Sym.macJfun`, `HJO.Sym.normalisingProduct_ne_zero`), so the
statement at `J` (`HJO.Ascent.exists_smul_dualityOmega_macJfun`) reads
`ι(τ(γ_μ))Ω(P_μ) = aγ_{μ'}P_{μ'}` by the semilinearity of `Ω`, and `ι(τ(γ_μ)) ≠ 0`, `ι∘τ` being
injective. Dividing by it is the statement.

Stated at the standing field: see the module docstring. -/
@[hjo "lem_dua_omega_ppoly"]
theorem exists_smul_dualityOmega_macPfun (μ : YoungDiagram) :
    ∃ c : K, c ≠ 0 ∧
      dualityOmega K (macPfun (Standing.algebraicIndependent_paramQUnit K) μ)
        = c • macPfun (Standing.algebraicIndependent_paramQUnit K) μ.transpose := by
  obtain ⟨a, ha0, ha⟩ := exists_smul_dualityOmega_macJfun K μ
  set g : K := paramSwapInvHom K
    (normalisingProduct ((Standing.paramQUnit K : K)) (paramU K) μ) with hgdef
  have hg : g ≠ 0 := fun h => normalisingProduct_ne_zero
    (Standing.algebraicIndependent_paramQUnit K) μ
    ((paramSwapInvHom K).injective (by rw [← hgdef, h, map_zero]))
  have hstep : g • dualityOmega K (macPfun (Standing.algebraicIndependent_paramQUnit K) μ)
      = (a * normalisingProduct ((Standing.paramQUnit K : K)) (paramU K) μ.transpose) •
          macPfun (Standing.algebraicIndependent_paramQUnit K) μ.transpose := by
    rw [hgdef, ← dualityOmega_smul, ← smul_smul]
    exact ha
  refine ⟨g⁻¹ * (a * normalisingProduct ((Standing.paramQUnit K : K)) (paramU K) μ.transpose),
    mul_ne_zero (inv_ne_zero hg) (mul_ne_zero ha0
      (normalisingProduct_ne_zero (Standing.algebraicIndependent_paramQUnit K) μ.transpose)), ?_⟩
  rw [← smul_smul, ← hstep, inv_smul_smul₀ hg]

end HJO.Ascent
