/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.DopCommute
public import HJO.Macdonald.EopJfun
public import HJO.Macdonald.HtildeSpan
public meta import HJO.Attr

/-! # The unnormalised Macdonald eigenbasis, unconditionally

`HJO.Sym.HasUnnormalisedMacdonaldEigenbasis` is one of the two inputs the collinear half of this
library still asked for. It is now a theorem at the standing coefficient field, with no
hypothesis at all, and this file is where the three pieces meet.

What was owed, and what closed each of it:

* that the `H̃_μ` span `Λ` -- the spanning half of `HJO.Standing.exists_basis_macHtilde` -- is
  `HJO.Standing.span_range_macHtilde_param_eq_top`.
* `HJO.Standing.dop_zero_smul_macHtilde_param`, Garsia--Haiman--Tesler's Theorem 1.2 equation (1.11)
  a, is `HJO.Standing.dop_zero_smul_macHtilde_param`. Its own last input is GHT (4.24), proved as
  `HJO.Sym.isEopEigenJfun`.
* `HJO.Sym.coeffSubst_macPfun`, that `P_μ` is fixed by inverting both parameters, is
  `HJO.Standing.coeffSubst_macPfun_param`.

None of the three carries a hypothesis here: at `𝕜 = ℚ(q,u)` the algebraic independence they are
stated at is `HJO.Ascent.algebraicIndependent_param` rather than an assumption.

Three clauses of the predicate were weakened before any of this was proved, and the weakening is
why the work was finishable. Linear independence came off clause (a), because it follows from
nonvanishing together with the `D_0` relation (`HJO.Sym.linearIndependent_of_dop_zero`); clause (c)
stopped naming the value `T_μ⁻¹`, because the only thing downstream ever used of it was that an
inversion eigenvalue satisfies `ι c * c = 1`; and the eigenbasis was allowed to differ from the
Pieri family. A predicate that asked for the strong forms would still be open.

The other input of the collinear half is `HJO.Sym.HasPieriEigenfamily` --
`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`. It needs `HJO.Sym.HasPfunPieriSupport`,
for which the Macdonald duality is unavoidable: at `ν = (3,2,2,1)` the
partition `λ = (3,3,1,1,1)` survives dominance triangularity, the lex leading exponent, `λ₁ ≤ ν₁`
and the column-removal induction all at once, while the conjugate partitions exclude it at once. So
this file proves the first of the two inputs and not the second.
-/

@[expose] public section

namespace HJO.Standing

open HJO.Sym HJO.Mac HJO.Ascent

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **An unnormalised Macdonald eigenbasis exists at the standing field, unconditionally.**

This is `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_of_dop_param` with its one remaining
hypothesis supplied: `hdop` is `HJO.Standing.dop_zero_smul_macHtilde_param`.

The statement is in the form its consumers spend, rather than asking for a `𝕜`-basis and for the
inversion clause to name the value `T_μ⁻¹`; the first is equivalent to
the clause here in the presence of the `D_0` relation, since distinct partitions have distinct
eigenvalues at generic parameters and a spanning family of nonzero eigenvectors is automatically
independent, and the second is genuinely weaker but is all any consumer spends -- what they use of
`c_μ` is only `ι c_μ * c_μ = 1`, which follows from `↓` being an involution. Naming the value would
additionally cost the hook-length identities, which nothing else consumes. -/
@[hjo "lem_ght2_eigenbasis_exists"]
theorem hasUnnormalisedMacdonaldEigenbasis_param :
    HasUnnormalisedMacdonaldEigenbasis (paramQUInvHom K) (paramQ K) (paramU K) :=
  hasUnnormalisedMacdonaldEigenbasis_of_dop_param K (dop_zero_smul_macHtilde_param K)

/-- **The Macdonald conjugator at the standing field, from the Pieri eigenfamily alone.**

`HJO.Standing.exists_isMacdonaldConjugator_of_hasPieriEigenfamily_param` takes two Props; the first
is now a theorem, so the collinear input costs exactly `HJO.Sym.HasPieriEigenfamily`. That is
`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`, and it in turn reduces to
`HJO.Sym.HasPfunPieriSupport` together with the `D_0` relation that is already available here. -/
theorem exists_isMacdonaldConjugator_of_hasPieriEigenfamily_param'
    (hpieri : HasPieriEigenfamily (paramQ K) (paramU K)) :
    ∃ nabla : Module.End K (Lambda K),
      IsMacdonaldConjugator (paramQ K) (paramU K) nabla :=
  exists_isMacdonaldConjugator_of_hasPieriEigenfamily_param K
    (hasUnnormalisedMacdonaldEigenbasis_param K) hpieri

end HJO.Standing
