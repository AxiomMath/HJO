/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.PfunBasis
public import HJO.Symmetric.AxisFree
public meta import HJO.Attr

/-! # Macdonald's symmetric functions are a basis of all of `Λ`

`HJO.Sym.exists_basis_macPfun`: the family `(P_μ)`, indexed by ALL partitions, is a `𝕜`-basis of
`Λ`.

The graded statement is already proved. `HJO.Sym.exists_basis_lambdaComp_macPfun` gives, for each
`d`, a basis of `Λ_d` indexed by the partitions of `d` whose members are the `P_μ`. So the only
thing left to prove here is the passage from "a basis of each graded piece" to "a basis of the
whole", and both halves of that are off the shelf:

* `HJO.Sym.lambdaComp_isInternal` says `Λ` is the internal
  direct sum of its graded pieces.
* `DirectSum.IsInternal.collectedBasis` assembles bases of the pieces of an internal direct sum into
  a basis of the whole, indexed by the sigma type `Σ d, {μ // |μ| = d}`.
* `Equiv.sigmaFiberEquiv YoungDiagram.card` identifies that sigma type with `YoungDiagram` -- the
  partitions of `d`, summed over `d`, are the partitions. This is the step that turns the graded
  index into the index set "all partitions", and it is an equivalence rather than a
  bijection to be built because grouping a type by the fibres of a function is exactly what
  `sigmaFiberEquiv` names.

So the statement costs only a reindex.

## The hypothesis, and why the statement is in general form

`HJO.Sym.macPfun` takes the algebraic independence of `(q, u)` as DATA -- the family is defined from
it -- so unlike `HJO.Bglx.exists_isIndexShift_param` there is no hypothesis-free restatement:
any statement about `P_μ` must name the independence in order to name `P_μ` at all. At `𝕜 = ℚ(q, u)`
that argument is `HJO.Ascent.algebraicIndependent_param`, a theorem, so reading the statement at its
own coefficient field costs nothing. The general theorem is therefore the main statement: it is the
strongest form and the only one that can be stated.
-/

@[expose] public section

namespace HJO.Sym

open MvPolynomial HJO.Mac

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

/-- **Macdonald's symmetric functions are a `𝕜`-basis of `Λ`.** There is a
basis of `Λ` indexed by all partitions whose member at `μ` is `P_μ`.

The graded pieces already have such bases (`HJO.Sym.exists_basis_lambdaComp_macPfun`), `Λ` is their
internal direct sum (`HJO.Sym.lambdaComp_isInternal`), and `DirectSum.IsInternal.collectedBasis`
glues them; the resulting index `Σ d, {μ // |μ| = d}` is `YoungDiagram` by
`Equiv.sigmaFiberEquiv YoungDiagram.card`.

As in the graded statement, "the family is a basis" is the existence of a bundled basis whose
members ARE the `P_μ` -- the equation `B μ = P_μ` is what makes this a statement about Macdonald's
symmetric functions rather than about the dimension of `Λ`. -/
@[hjo "lem_mac_pfun_basis"]
theorem exists_basis_macPfun (hqu : AlgebraicIndependent ℤ ![(q : K), u]) :
    ∃ B : Module.Basis YoungDiagram K (Lambda K), ∀ μ : YoungDiagram, B μ = macPfun hqu μ := by
  classical
  choose Bd hBd using fun d : ℕ => exists_basis_lambdaComp_macPfun (q := q) (u := u) hqu d
  refine ⟨((lambdaComp_isInternal (K := K)).collectedBasis Bd).reindex
      (Equiv.sigmaFiberEquiv YoungDiagram.card), fun μ => ?_⟩
  rw [Module.Basis.reindex_apply, DirectSum.IsInternal.collectedBasis_coe]
  exact hBd μ.card ⟨μ, rfl⟩

end HJO.Sym
