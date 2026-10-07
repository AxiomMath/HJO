/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.EigenbasisNormalisation
public import HJO.Macdonald.EopJfun
public import HJO.Macdonald.HtildeSpan
public meta import HJO.Attr

/-! # The modified Macdonald polynomials are a basis of `Λ`

`HJO.Standing.exists_basis_macHtilde`: the family `(H̃_μ)`, indexed by all partitions, is a
`𝕜`-basis of `Λ`.

Both halves are proved in earlier files; this file is where they meet.

* **Spanning** -- `HJO.Standing.span_range_macHtilde_param_eq_top`, at the standing field with no
  hypothesis.
* **Independence** -- `HJO.Sym.linearIndependent_of_dop_zero`, which derives it from two facts
  rather than from a triangularity argument: that every `H̃_μ` is nonzero, and that `D_0` scales
  `H̃_μ` by `dopZeroEigenvalue q u μ`. Distinct partitions get distinct eigenvalues at an
  algebraically independent pair, so a family of nonzero eigenvectors is automatically independent.
  The two inputs are `HJO.Sym.macHtilde_ne_zero` and `HJO.Standing.dop_zero_smul_macHtilde_param`
  (`HJO.Standing.dop_zero_smul_macHtilde_param`, Garsia--Haiman--Tesler's (1.11)a), both proved
  earlier.

The eigenvalue matches on the nose: `HJO.Sym.dopZeroEigenvalue q u μ` is by definition
`-(M B_μ - 1)`, which is exactly the scalar `dop_zero_smul_macHtilde_param` produces, so no
bridging computation is needed.

## Why this is stated at the standing field, and not over a general field

This is one of the statements of this library whose general-field reading is FALSE. Two of the
three ingredients fail at a degenerate corner:

* `macHtilde_ne_zero` needs `u ≠ 0` and `∀ k, u^{k+1} ≠ 1`. At a root of unity a scalar of the
  plethystic substitution vanishes and `H̃_μ` really is zero, which is the same corner that breaks
  `HJO.Sym.plethDivide_paramUInvLambda_injective`.
* `linearIndependent_of_dop_zero` needs the cell sum to separate partitions, which fails at `q = u`,
  and needs `M ≠ 0`, without which every eigenvalue is `1` and `D_0` is the identity.

At `𝕜 = ℚ(q, u)` all of these are theorems rather than hypotheses -- `HJO.Standing.paramU_ne_zero`,
`paramU_pow_succ_ne_one` and `HJO.Ascent.algebraicIndependent_param` -- so the statement below
carries nothing. That is the whole reason the library fixes the parameters as indeterminates
instead of quantifying over fields.

## Shape

"The family is a basis" is the existence of a bundled basis whose members ARE the `H̃_μ`, as in
`HJO.Sym.exists_basis_macPfun`. The equation `B μ = H̃_μ` is what makes this a statement about the
modified Macdonald polynomials rather than about the dimension of `Λ`.
-/

@[expose] public section

namespace HJO.Standing

open HJO.Sym HJO.Ascent

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **The modified Macdonald polynomials are `𝕜`-linearly independent.** From the two clauses
`HJO.Sym.linearIndependent_of_dop_zero` asks for: nonvanishing, and the `D_0` eigenrelation. -/
theorem linearIndependent_macHtilde_param :
    LinearIndependent K (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K)) :=
  linearIndependent_of_dop_zero (algebraicIndependent_paramQUnit K)
    (fun μ => macHtilde_ne_zero (paramU_ne_zero K) (paramU_pow_succ_ne_one K)
      (algebraicIndependent_paramQUnit K) μ)
    (fun μ => dop_zero_smul_macHtilde_param K μ)

/-- **The modified Macdonald polynomials are a `𝕜`-basis of `Λ`.**

`Module.Basis.mk` on the independence above and the spanning of
`HJO.Standing.span_range_macHtilde_param_eq_top`. Both are proved in earlier files; what is done
here is the assembly. -/
@[hjo "lem_mac_htilde_basis"]
theorem exists_basis_macHtilde :
    ∃ B : Module.Basis YoungDiagram K (Lambda K),
      ∀ μ : YoungDiagram,
        B μ = macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ :=
  ⟨Module.Basis.mk (linearIndependent_macHtilde_param K)
    (span_range_macHtilde_param_eq_top K).ge, fun μ => Module.Basis.mk_apply _ _ μ⟩

end HJO.Standing
