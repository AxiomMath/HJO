/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.Diagonal
public import HJO.Evaluation.CollinearNarrowed

/-! # The collinear commutation from a Macdonald conjugator and an index shift

`HJO.External.CollinearCommutation` is reduced here to two structures. This file writes that
reduction down as one statement, `collinearCommutation_of_structures`.

Reading upwards from the `Prop`:

* `CollinearNarrowed.collinearCommutation` drops the second clause -- the slope homomorphism the
  input also asks for is produced from the commuting operators, so only the commutation is at issue.
* `CollinearNarrowed.collinearCommute_of_structures` proves that commutation by the Euclidean
  descent on `a + b`, with the diagonal base case discharged, from a Macdonald conjugator and an
  index shift. Every parameter condition the descent and the base case need -- `M ≠ 0`, `q u ≠ 0`,
  `q u ≠ 1` -- is supplied by the algebraic independence the statement is already stated at,
  so none of them appears below.

Composing the two gives `collinearCommutation_of_structures`, below, which asks for
`HJO.Sym.exists_isMacdonaldConjugator` and `HJO.Bglx.exists_isIndexShift_param`.

Neither hypothesis is needed in the end:

* `HJO.Bglx.exists_isIndexShift_param` is a theorem -- `HJO.Bglx.exists_isIndexShift`, and at the
  standing field `HJO.Bglx.exists_isIndexShift_param` with no hypothesis at all -- so `hshift` need
  never be supplied.
* `hconj` is not provable in the generality asked here, over every field of characteristic zero
  carrying an algebraically independent pair: the route goes through
  `HJO.Sym.exists_isMacdonaldConjugator_of_hasPieriEigenfamily`, which needs a ring involution of
  the coefficient field inverting both parameters, and no such involution exists at a general field
  -- over `ℝ` the only ring endomorphism is the identity. `HJO.Ascent.commute_qop_ascend` carries a
  commutation from the standing instance to any such field, so the Macdonald conjugator is only
  needed at `𝕜 = ℚ(q, u)`.

`HJO.CollinearNarrowed.collinearCommutation_of_pfunPieriSupport`
(`HJO/Collinear/PfunSupportDischarge.lean`) derives the commutation at every coefficient field
from one `Prop` at the standing field, `HJO.Sym.HasPfunPieriSupport`, and
`HJO/Collinear/CommutationTheorem.lean` assembles the unconditional statement.
`collinearCommutation_of_structures` remains the statement of what the Euclidean descent itself
needs.
-/

@[expose] public section

namespace HJO.CollinearNarrowed

open HJO.Sym

/-- **The collinear input, reduced to two existence statements.** Given that a Macdonald
conjugator and an index shift exist at every algebraically independent pair of parameters,
`HJO.External.CollinearCommutation` holds -- the quoted input in the form every consumer in this
library takes it.

This is the composite of `collinearCommute_of_structures` (the Euclidean descent with its diagonal
base case) and `collinearCommutation` (which discharges the input's second clause). Neither
hypothesis mentions a slope operator: they are `HJO.Sym.exists_isMacdonaldConjugator` and
`HJO.Bglx.exists_isIndexShift_param`, and they are the whole of what the collinear side still
assumes. -/
theorem collinearCommutation_of_structures {L : Type*} [Field L] [Algebra ℚ L]
    (hconj : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] →
      ∃ nabla : Module.End L (Lambda L), IsMacdonaldConjugator q u nabla)
    (hshift : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] →
      ∃ S : DopAlgebra q u →ₐ[L] DopAlgebra q u, IsIndexShift q u S) :
    HJO.External.CollinearCommutation L :=
  collinearCommutation (collinearCommute_of_structures hconj hshift)

end HJO.CollinearNarrowed
