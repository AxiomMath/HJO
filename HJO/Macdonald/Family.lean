/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.Vocabulary
public import HJO.Macdonald.Vocabulary
public import HJO.Symmetric.AxisFree
public meta import HJO.Attr

/-! # The modified Macdonald family and its eigenoperator

The modified Macdonald polynomials are named here by the four properties the Macdonald conjugator
argument consumes, and by nothing else: no Schur functions, no `*`-scalar product, no dominance
order. A family `(H̃_μ)` of elements of `Λ` indexed by the partitions is a **modified Macdonald
family** when

* it is a `𝕜`-basis of `Λ`;
* `D_0 H̃_μ = -(M B_μ - 1) H̃_μ`;
* `D*_0 H̃_μ = -(M̃ B*_μ - 1) H̃_μ`;
* `e₁ H̃_ν` lies in the `𝕜`-span of the `H̃_μ` with `μ` covering `ν`.

The last clause asserts the **support** of the one-cell Pieri expansion and nothing else: the set
of partitions that can occur, never the value of a coefficient. That is all the argument above it
uses, so it is all that is recorded.

This is a predicate on families, not a construction. Nothing here asserts that a modified Macdonald
family exists; a consumer that needs one takes it as a hypothesis, exactly as with
`IsMacdonaldConjugator` and `IsIndexShift`.

The **eigenoperator** `∇` of such a family is the `𝕜`-linear map with `∇ H̃_μ = T_μ H̃_μ`. Being an
eigenoperator is again a predicate, on a pair (family, linear map); since a modified Macdonald
family is a basis, prescribing the values on it determines exactly one linear map, so
`nablaOf` builds the eigenoperator of a given family and `eq_of_isEigenoperator` says it is the
only one. That is linear algebra.

## Main definitions

* `HJO.Sym.IsModifiedMacdonaldFamily`: the four clauses above.
* `HJO.Sym.IsEigenoperator`, `HJO.Sym.nablaOf`: the eigenoperator `∇` of a family.
* `HJO.Sym.reachStar`: the set `G_k = {D*_1 A + e₁ B : A, B ∈ Λ_{k-1}}`.

## Implementation notes

The inverted parameter product `M̃ = (1 - q⁻¹)(1 - u⁻¹)` is spelled `paramProduct q⁻¹ u⁻¹`, the
parameter product at the inverted parameters, and `B^*_μ` is `cellSumInv q u μ`. So the starred
clause needs no vocabulary of its own beyond the starred operator `DopStar`, matching
`HJO/Collinear/Vocabulary.lean`, where `M̃` likewise occurs in no definition.

Clause (i) is two fields, `linearIndependent` and `span_eq_top`, rather than an existential over
`Module.Basis`: together they are the single clause "it is a `𝕜`-basis of `Λ`", and
`IsModifiedMacdonaldFamily.basis` packages them as the basis itself, which is what the consumers
of clause (i) want.

Everything is stated over a general field `L` that is a `ℚ`-algebra, never at `ℚ(q, u)`: the
parameters `q` and `u` are explicit arguments, so the clauses at the inverted parameters are the
same clauses at different arguments.

## References

Clause (ii) is Theorem 1.2, equation
(1.11) a), of A. M. Garsia, M. Haiman and G. Tesler, *Explicit plethystic formulas for Macdonald
(q,t)-Kostka coefficients*, Sém. Lothar. Combin. **42** (1999), B42m, copied as clause (i) of
Proposition 1.1 of F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic
operators in the theory of Macdonald polynomials*, arXiv:1405.0316, J. Comb. **7** (2016) 671--714,
their equation (1.9); clause (iii) is Garsia--Haiman--Tesler's equation (1.11) b); clause (iv) is
the support half of their equation (1.31) b). The eigenoperator is Bergeron--Garsia--Leven--Xin's
equation (1.7) and Garsia--Haiman--Tesler's equation (I.8).
-/

@[expose] public section

namespace HJO.Sym

section Family

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- A **modified Macdonald family** `(H̃_μ)`, indexed by the partitions: a `𝕜`-basis of `Λ`
(clause (i), the two fields `linearIndependent` and `span_eq_top`) which is an eigenbasis of the
basic operator `D_0` with eigenvalue `-(M B_μ - 1)` (clause (ii)) and of the starred basic operator
`D*_0` with eigenvalue `-(M̃ B*_μ - 1)` (clause (iii)), and along which multiplication by `e₁`
raises the index by one cell (clause (iv)).

Clause (iv) is the **support** of the one-cell Pieri expansion
`e₁ H̃_ν = ∑_{μ ← ν} d_{μν} H̃_μ`: only the set of partitions that can occur is asserted, never a
value of a coefficient. Nothing built on this definition uses more.

This is a predicate, not a construction: nothing here asserts that such a family exists. -/
@[hjo "def_ght_family"]
structure IsModifiedMacdonaldFamily (q u : L) (H : YoungDiagram → Lambda L) : Prop where
  /-- Clause (i), first half: the family is `𝕜`-linearly independent. -/
  linearIndependent : LinearIndependent L H
  /-- Clause (i), second half: the family spans `Λ` over `𝕜`. -/
  span_eq_top : Submodule.span L (Set.range H) = ⊤
  /-- Clause (ii): `D_0 H̃_μ = -(M B_μ - 1) H̃_μ`. -/
  dop_zero : ∀ μ : YoungDiagram,
    Dop q u 0 (H μ) = -(paramProduct q u * cellSum q u μ - 1) • H μ
  /-- Clause (iii): `D*_0 H̃_μ = -(M̃ B*_μ - 1) H̃_μ`, with `M̃ = (1 - q⁻¹)(1 - u⁻¹)` the parameter
  product at the inverted parameters and `B*_μ` the inverted cell sum. -/
  dopStar_zero : ∀ μ : YoungDiagram,
    DopStar q u 0 (H μ) = -(paramProduct q⁻¹ u⁻¹ * cellSumInv q u μ - 1) • H μ
  /-- Clause (iv): `e₁ H̃_ν` lies in the `𝕜`-span of the `H̃_μ` with `μ` covering `ν`. This is the
  support of the one-cell Pieri expansion, with no claim about any coefficient. -/
  elemSymm_one_mul_mem : ∀ ν : YoungDiagram,
    elemSymm L 1 * H ν ∈ Submodule.span L (H '' {μ : YoungDiagram | Covers μ ν})

namespace IsModifiedMacdonaldFamily

variable {q u : L} {H : YoungDiagram → Lambda L}

/-- Clause (i) as the basis it is: a modified Macdonald family, read as a `𝕜`-basis of `Λ` indexed
by the partitions. -/
noncomputable def basis (h : IsModifiedMacdonaldFamily q u H) :
    Module.Basis YoungDiagram L (Lambda L) :=
  Module.Basis.mk h.linearIndependent (h.span_eq_top.ge)

@[simp]
theorem basis_apply (h : IsModifiedMacdonaldFamily q u H) (μ : YoungDiagram) :
    h.basis μ = H μ :=
  Module.Basis.mk_apply _ _ _

end IsModifiedMacdonaldFamily

/-- `∇` is an **eigenoperator** for the family `(H̃_μ)`: the `𝕜`-linear endomorphism of `Λ` scales
each `H̃_μ` by the cell product `T_μ`.

The condition mentions only the family and the map; being a modified Macdonald family is what makes
such a `∇` exist and be unique (`nablaOf` and `eq_of_isEigenoperator`), not what the condition
says. -/
@[hjo "def_ght_scaling"]
def IsEigenoperator (q u : L) (H : YoungDiagram → Lambda L) (nabla : Module.End L (Lambda L)) :
    Prop :=
  ∀ μ : YoungDiagram, nabla (H μ) = cellProd q u μ • H μ

/-- The eigenoperator of a modified Macdonald family: the unique `𝕜`-linear map sending `H̃_μ` to
`T_μ H̃_μ`, got by prescribing those values on the basis. The existence and
the uniqueness are linear algebra. -/
noncomputable def nablaOf {q u : L} {H : YoungDiagram → Lambda L}
    (h : IsModifiedMacdonaldFamily q u H) : Module.End L (Lambda L) :=
  h.basis.constr L fun μ => cellProd q u μ • H μ

theorem isEigenoperator_nablaOf {q u : L} {H : YoungDiagram → Lambda L}
    (h : IsModifiedMacdonaldFamily q u H) : IsEigenoperator q u H (nablaOf h) := fun μ => by
  rw [nablaOf, ← h.basis_apply μ, Module.Basis.constr_basis, h.basis_apply]

/-- An eigenoperator for a modified Macdonald family is unique: two of them agree on a basis. -/
theorem eq_of_isEigenoperator {q u : L} {H : YoungDiagram → Lambda L}
    (h : IsModifiedMacdonaldFamily q u H) {n₁ n₂ : Module.End L (Lambda L)}
    (h₁ : IsEigenoperator q u H n₁) (h₂ : IsEigenoperator q u H n₂) : n₁ = n₂ :=
  h.basis.ext fun μ => by rw [h.basis_apply, h₁ μ, h₂ μ]

end Family

/-! ### One starred step from the degree below -/

section ReachStar

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **One starred step from the degree below**: the set
`G_k = {D*_1 A + e₁ B : A, B ∈ Λ_{k-1}}`, a subset of `Λ`.

The informal definition is for `k ≥ 1`. The natural subtraction totalises it, so `reachStar q u 0`
is `reachStar q u 1`; every consumer has `k ≥ 1`. -/
@[hjo "def_ght_reach_star"]
def reachStar (q u : L) (k : ℕ) : Set (Lambda L) :=
  {f | ∃ A ∈ LambdaComp L (k - 1), ∃ B ∈ LambdaComp L (k - 1),
    f = DopStar q u 1 A + elemSymm L 1 * B}

theorem mem_reachStar {q u : L} {k : ℕ} {f : Lambda L} :
    f ∈ reachStar q u k ↔ ∃ A ∈ LambdaComp L (k - 1), ∃ B ∈ LambdaComp L (k - 1),
      f = DopStar q u 1 A + elemSymm L 1 * B := Iff.rfl

end ReachStar

end HJO.Sym
