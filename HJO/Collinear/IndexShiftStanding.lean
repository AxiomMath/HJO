/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Ascent.Embedding
public import HJO.Collinear.ExpPairingSeparating
public meta import HJO.Attr

/-! # The index shift at the standing field

`HJO.Bglx.exists_isIndexShift` produces an index shift from `AlgebraicIndependent ℤ ![q, u]`, and
that is the strongest form: it applies at any coefficient field carrying an algebraically
independent pair, not only at the standing one.

`HJO.Bglx.exists_isIndexShift_param` states no hypothesis on the parameters, because it is read
at `𝕜 = ℚ(q,u)` where `q` and `u` are indeterminates and the independence is automatic. So the
statement is the hypothesis-free reading, and that is what this file records:
`HJO.Ascent.algebraicIndependent_param` supplies the independence at any field presented as a field
of fractions of `ParamRing`.

The general theorem keeps its hypothesis, which is not a residual but a fact at the standing field,
so the hypothesis-free corollary `HJO.Bglx.exists_isIndexShift_param` is the faithful form of the
statement there, and the general theorem keeps its greater strength.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym HJO.Ascent

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **An index shift exists**, at the standing coefficient field and with no hypothesis on the
parameters. `HJO.Bglx.exists_isIndexShift_param`.

This is `HJO.Bglx.exists_isIndexShift` read at `𝕜`, where the algebraic independence it asks for is
`HJO.Ascent.algebraicIndependent_param` rather than an assumption. Both halves of BGLX's Theorem 2.1
stand behind it: sufficiency is `HJO.Bglx.dopWordOperator_eq_zero_of_symbolSym`, and necessity is
`HJO.Bglx.isExpPairingSeparating`, which carries no parameter hypothesis at all. -/
@[hjo "lem_index_shift_exists"]
theorem exists_isIndexShift_param :
    ∃ S : DopAlgebra (paramQ K) (paramU K) →ₐ[K] DopAlgebra (paramQ K) (paramU K),
      IsIndexShift (paramQ K) (paramU K) S :=
  exists_isIndexShift (paramQ K) (paramU K) (algebraicIndependent_param K)

end HJO.Bglx
