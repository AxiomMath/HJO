/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import HJO.Macdonald.ParamInversion
public meta import HJO.Attr

/-! # The normalisation clause of a Macdonald eigenbasis is not needed

`HJO/Macdonald/EigenbasisFamily.lean` reduces the whole collinear side of this library to
one hypothesis: that some family `H : YoungDiagram → Lambda L` is a Macdonald eigenbasis
(`HJO.Sym.IsMacdonaldEigenbasis`) whose `e₁`-products have covering support
(`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`). This file makes that
hypothesis **strictly smaller**, in three independent ways, and names what is left.

## What is cut: the value in clause `(c)`

Clause `(c)` of `HJO.Sym.IsMacdonaldEigenbasis` reads `↓H̃_μ = T_μ⁻¹ H̃_μ`: the family is an
eigenbasis of the inversion `↓`, *with the eigenvalue named*. Only the first half of that is ever
used. The single consumer of clause `(c)` is `HJO.Sym.dopStar_zero_smul_of_dop_zero`,
which turns clauses `(b)` and `(c)` into clause (iii) of `HJO.Sym.IsModifiedMacdonaldFamily`; and
`dopStar_zero_of_exists_inversion_smul` below proves that same clause (iii) from clause `(b)`
together with the bare statement that **each `H̃_μ` is some eigenvector of `↓`**:

    ∀ μ, ∃ c : L, inversion ι (H μ) = c • H μ.

The value `T_μ⁻¹` is not needed, and neither are the hypotheses `q ≠ 0` and `u ≠ 0` that
`dopStar_zero_smul_of_dop_zero` carries only to make `T_μ` invertible. What replaces the named
value is free: `↓` is an involution when `ι` is (`inversion_inversion`), so a nonzero eigenvector
forces `ι(c) * c = 1` (`mul_inversion_eigenvalue_eq_one`), and that is the one fact about the
eigenvalue the derivation of clause (iii) spends. With `c = T_μ⁻¹` it is `T_μ * T_μ⁻¹ = 1`, which
is where `q ≠ 0` and `u ≠ 0` used to enter.

**This takes three lemmas out of the proof of the collinear goal.** The standard argument
proves clause `(c)` as `HJO.Standing.inversion_macHtilde_param`, and that proof spends
`HJO.Sym.cellProd_eq_pow_sum_cellArm_mul_pow_sum_cellLeg`, `HJO.Sym.sum_cellLeg` and
`HJO.Sym.sum_cellArm` -- the arm-and-leg bookkeeping identifying `T_μ = q^{∑ a_μ(c)} u^{n(μ)}` -- in
its last paragraph and nowhere else: everything before that paragraph establishes exactly
`∃ c, ↓H̃_μ = c H̃_μ`, the scalar being `(-1)^{|μ|} u^{-|μ|-2n(μ)} ιυ(γ_μ) υ(γ_μ)⁻¹` uniformly in
the power-sum index. So the weakened clause is what that proof delivers when it is stopped one
paragraph early, and `HJO.Sym.cellArm`, `HJO.Sym.cellLeg`, `HJO.Sym.sum_cellArm`,
`HJO.Sym.sum_cellLeg` and `HJO.Sym.cellProd_eq_pow_sum_cellArm_mul_pow_sum_cellLeg` are needed by
this library's collinear half only through results that are not on this route.

## What is cut: linear independence in clause `(a)`

Both halves of the reduction ask a family for `D_0 F_μ = -(M B_μ - 1) F_μ`, and at generic `(q, u)`
the eigenvalues attached to distinct indices are distinct
(`HJO.Sym.eq_of_dopZeroEigenvalue_eq`). A family of **nonzero** eigenvectors with pairwise distinct
eigenvalues is linearly independent, so linear independence is not an assumption to be made about
either family: `linearIndependent_of_dop_zero` derives it from `∀ μ, F μ ≠ 0` and clause `(b)`. Both
residual Props ask only for nonvanishing, and the genericity they spend for it is `hqu`, which the
reduction carries anyway.

## What is split

`HJO.Standing.elemSymm_one_mul_mem_span_of_dop_zero_param` transports the covering Pieri support
from *one* family with clause `(b)` to *every* eigenbasis, and
`HJO.Sym.elemSymm_one_mul_mem_of_dop_zero` is that transport, proved. So the eigenbasis and the
family carrying the Pieri support need not be the same function, and the Pieri family need not span
`Λ` nor satisfy any inversion clause. The two halves are named separately here,
`HasUnnormalisedMacdonaldEigenbasis` and `HasPieriEigenfamily`, so that they can be discharged from
different constructions.

## The residual

`HJO.Standing.exists_isMacdonaldConjugator_of_hasPieriEigenfamily_param` is the collinear goal at
the standing field with exactly those two Props as hypotheses and nothing else. Against
`HJO.Standing.exists_isMacdonaldConjugator_param`, whose hypothesis is the bundled
`IsMacdonaldEigenbasis`-plus-support, what has been removed is the value `T_μ⁻¹` in clause `(c)`,
linear independence in clause `(a)` on both families, the requirement that one family carry all four
properties, and the spanning and inversion clauses for the Pieri family.

## Main results

* `HJO.Sym.inversion_inversion`: `↓` is an involution when `ι` is.
* `HJO.Sym.mul_inversion_eigenvalue_eq_one`: an eigenvalue of `↓` at a nonzero vector satisfies
  `ι(c) * c = 1`.
* `HJO.Sym.linearIndependent_of_dop_zero`: clause `(b)` plus nonvanishing gives clause `(a)`'s
  first half.
* `HJO.Sym.IsUnnormalisedMacdonaldEigenbasis`: clauses `(a)`, `(b)` and `(c)`, the first and the
  last weakened.
* `HJO.Sym.IsUnnormalisedMacdonaldEigenbasis.dopStar_zero`: clause (iii) of
  `HJO.Sym.IsModifiedMacdonaldFamily`, with no hypothesis on `q` or `u`.
* `HJO.Sym.HasUnnormalisedMacdonaldEigenbasis`, `HJO.Sym.HasPieriEigenfamily`: the two residual
  Props.
* `HJO.Sym.exists_isMacdonaldConjugator_of_hasPieriEigenfamily`, and its standing-field form
  `HJO.Standing.exists_isMacdonaldConjugator_of_hasPieriEigenfamily_param`.

Every statement is either a weakening of a clause of `HJO.Sym.IsMacdonaldEigenbasis` or a
reduction with a hypothesis the statement does not carry, and `inversion_inversion` extends to `↓`
the involutivity known for `ι` (`HJO.Sym.paramQUInv_involutive`).

## References

This file weakens the definitions `HJO.Sym.IsMacdonaldEigenbasis` and
`HJO.Sym.IsModifiedMacdonaldFamily`, and bears on the lemmas
`HJO.Sym.dopStar_zero_smul_of_dop_zero`, `HJO.Sym.exists_smul_of_dop_zero_eigenbasis`,
`HJO.Standing.elemSymm_one_mul_mem_span_of_dop_zero_param`,
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_param` and
`HJO.Standing.exists_isModifiedMacdonaldFamily_param'`, and, on Macdonald's polynomials,
`HJO.Standing.inversion_macHtilde_param`, `HJO.Sym.cellProd_eq_pow_sum_cellArm_mul_pow_sum_cellLeg`,
`HJO.Sym.sum_cellArm`, `HJO.Sym.sum_cellLeg` and
`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The inversion of the symmetric functions is an involution -/

section Involutive

variable {K : Type*} [CommRing K]

/-- **`↓` is an involution when `ι` is.** `Λ` is a polynomial ring over the coefficients on the
`p_k`, `↓` applies `ι` to a coefficient and multiplies `p_k` by `(-1)^{k-1}`, and both of those
square to the identity.

Involutivity is known for the coefficient inversion `ι` (`HJO.Sym.paramQUInv_involutive`) and for
`↓_z` inside the proof of `HJO.Sym.inversionW_plethShift`, but is not stated elsewhere for `↓`
itself; this is that statement, carried as a hypothesis `hιι` on `ι` exactly as in
`HJO/Macdonald/EigenbasisFamily.lean`. -/
theorem inversion_inversion (ι : K →+* K) (hιι : ∀ c : K, ι (ι c) = c) (f : Lambda K) :
    inversion ι (inversion ι f) = f := by
  induction f using MvPolynomial.induction_on with
  | C c => rw [inversion_C, inversion_C, hιι]
  | add p r hp hr => rw [map_add, map_add, hp, hr]
  | mul_X p i hp =>
      have h1 : ((-1 : Lambda K) ^ i) * ((-1 : Lambda K) ^ i) = 1 := by
        rw [← pow_add, show i + i = 2 * i by ring, pow_mul]; norm_num
      rw [map_mul, map_mul, hp, inversion_X, map_mul, map_pow, map_neg, map_one, inversion_X,
        ← mul_assoc ((-1 : Lambda K) ^ i) ((-1 : Lambda K) ^ i), h1, one_mul]

end Involutive

/-! ### A Macdonald eigenbasis with its normalisation clause weakened -/

section Unnormalised

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

omit [Algebra ℚ L] in
/-- **An eigenvalue of `↓` at a nonzero vector has `ι`-norm one.** If `↓f = c f` with `f ≠ 0` then
`ι(c) * c = 1`, because applying `↓` twice returns `f` while multiplying it by `ι(c) * c`.

This is what replaces the named value `T_μ⁻¹` of clause `(c)` of `HJO.Sym.IsMacdonaldEigenbasis`: it
is the only property of that value the derivation of clause (iii) of
`HJO.Sym.IsModifiedMacdonaldFamily` uses, and it comes for free from involutivity rather than from
the arm-and-leg identity `HJO.Sym.cellProd_eq_pow_sum_cellArm_mul_pow_sum_cellLeg`. -/
theorem mul_inversion_eigenvalue_eq_one (ι : L →+* L) (hιι : ∀ c : L, ι (ι c) = c)
    {f : Lambda L} (hf : f ≠ 0) {c : L} (hc : inversion ι f = c • f) : ι c * c = 1 := by
  have key : inversion ι (inversion ι f) = (ι c * c) • f := by
    rw [hc, inversion_smul, hc, smul_smul]
  rw [inversion_inversion ι hιι] at key
  have h0 : (ι c * c - 1) • f = 0 := by rw [sub_smul, one_smul, ← key, sub_self]
  rcases smul_eq_zero.mp h0 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hf

/-- **Clause `(a)`'s first half from clause `(b)` and nonvanishing.** A family of nonzero
eigenvectors of `D_0` whose eigenvalues are the `-(M B_μ - 1)` is `𝕜`-linearly independent, because
at generic `(q, u)` those eigenvalues are pairwise distinct (`eq_of_dopZeroEigenvalue_eq`) and
eigenvectors for distinct eigenvalues are independent.

So neither residual Prop below has to assume linear independence: both ask only that no member
vanish. The hypothesis `hqu` is the one `HJO.Sym.exists_smul_of_dop_zero_eigenbasis` needs -- it
supplies `M ≠ 0` as well -- and is already carried by every reduction here. -/
theorem linearIndependent_of_dop_zero (hqu : AlgebraicIndependent ℤ ![q, u])
    {G : YoungDiagram → Lambda L} (hGne : ∀ μ, G μ ≠ 0)
    (hGdop : ∀ μ, Dop q u 0 (G μ) = dopZeroEigenvalue q u μ • G μ) : LinearIndependent L G := by
  have hinj : Function.Injective (dopZeroEigenvalue q u) :=
    fun _ _ h => eq_of_dopZeroEigenvalue_eq hqu h
  set e : YoungDiagram ≃ Set.range (dopZeroEigenvalue q u) := Equiv.ofInjective _ hinj with he
  have hval : ∀ ν : Set.range (dopZeroEigenvalue q u),
      dopZeroEigenvalue q u (e.symm ν) = (ν : L) := by
    intro ν
    have h := e.apply_symm_apply ν
    rw [he, Equiv.ofInjective_apply] at h
    exact congrArg Subtype.val h
  have h := Module.End.eigenvectors_linearIndependent (Dop q u 0)
    (Set.range (dopZeroEigenvalue q u)) (fun ν => G (e.symm ν)) fun ν =>
      ⟨Module.End.mem_eigenspace_iff.mpr (by rw [hGdop, hval]), hGne _⟩
  have h2 := h.comp e e.injective
  have heq : (fun ν => G (e.symm ν)) ∘ (e : YoungDiagram → Set.range (dopZeroEigenvalue q u))
      = G := funext fun μ => by rw [Function.comp_apply, e.symm_apply_apply]
  rwa [heq] at h2

/-- An **unnormalised Macdonald eigenbasis** `(H̃_μ)`: a family of nonzero elements spanning `Λ`
(clause `(a)` of `HJO.Sym.IsMacdonaldEigenbasis`, with linear independence dropped) which is an
eigenbasis of `D_0` with eigenvalue `-(M B_μ - 1)` (clause `(b)`) and each of whose members is an
eigenvector of the inversion `↓` (clause `(c)`, with the eigenvalue *not* named).

`IsMacdonaldEigenbasis` implies this (`IsMacdonaldEigenbasis.unnormalised`) with no hypothesis, and
the implication is strict in both weakened clauses. Clause `(c)` is a
normalisation, clauses `(a)` and `(b)` leaving one nonzero scalar per index free; this is invariant
under
a rescaling `H̃_μ ↦ d_μ H̃_μ` by nonzero scalars, which clause `(c)` is not, and it is still enough
for every clause of `HJO.Sym.IsModifiedMacdonaldFamily`.

Linear independence is not lost, only unassumed: `linearIndependent` recovers it at `M ≠ 0` and
generic `(q, u)`, so at the standing field this predicate and the conjunction of clauses `(a)`,
`(b)` and the weakened `(c)` are the same thing. -/
structure IsUnnormalisedMacdonaldEigenbasis (ι : L →+* L) (q u : L)
    (H : YoungDiagram → Lambda L) : Prop where
  /-- Clause `(a)`, first half, weakened: no member of the family is zero. -/
  ne_zero : ∀ μ : YoungDiagram, H μ ≠ 0
  /-- Clause `(a)`, second half: the family spans `Λ` over `𝕜`. -/
  span_eq_top : Submodule.span L (Set.range H) = ⊤
  /-- Clause `(b)`: `D_0 H̃_μ = -(M B_μ - 1) H̃_μ`. -/
  dop_zero : ∀ μ : YoungDiagram,
    Dop q u 0 (H μ) = -(paramProduct q u * cellSum q u μ - 1) • H μ
  /-- Clause `(c)`, weakened: `H̃_μ` is an eigenvector of `↓`, with the eigenvalue not named. -/
  exists_inversion_smul : ∀ μ : YoungDiagram, ∃ c : L, inversion ι (H μ) = c • H μ

namespace IsUnnormalisedMacdonaldEigenbasis

variable {ι : L →+* L} {H : YoungDiagram → Lambda L}

/-- Clause `(a)`'s first half, recovered: the family is `𝕜`-linearly independent, by
`linearIndependent_of_dop_zero`. -/
theorem linearIndependent (h : IsUnnormalisedMacdonaldEigenbasis ι q u H)
    (hqu : AlgebraicIndependent ℤ ![q, u]) : LinearIndependent L H :=
  linearIndependent_of_dop_zero hqu h.ne_zero fun μ => h.dop_zero μ

/-- **Clause (iii) of `HJO.Sym.IsModifiedMacdonaldFamily` from the weakened clause `(c)`.**
`D*_0 H̃_μ = -(M̃ B*_μ - 1) H̃_μ`.

This is `HJO.Sym.dopStar_zero_smul_of_dop_zero` with the named value `T_μ⁻¹` removed from its second
hypothesis, and with `q ≠ 0` and `u ≠ 0` removed from its statement: those two were carried only to
make `T_μ` invertible, and what the derivation needs of the eigenvalue is `ι(c) * c = 1`, which
`mul_inversion_eigenvalue_eq_one` supplies from involutivity.

The proof is Garsia--Haiman--Tesler's Remark 1.1 unchanged: conjugate clause `(b)` by `↓` using
`HJO.Sym.dopStar_zero_eq`, and read the conjugated scalar with `HJO.Sym.paramInv_paramProduct` and
`HJO.Sym.paramInv_cellSum`. Writing `↓H̃_μ = c H̃_μ`, the two factors `ι(c)` and `c` produced by the
two applications of `↓` meet as `ι(c) * c = 1`; with `c = T_μ⁻¹` that is `T_μ * T_μ⁻¹ = 1`. -/
theorem dopStar_zero (h : IsUnnormalisedMacdonaldEigenbasis ι q u H) (hq : ι q = q⁻¹)
    (hu : ι u = u⁻¹) (hιι : ∀ c : L, ι (ι c) = c)
    (hQ : ∀ r : ℚ, ι (algebraMap ℚ L r) = algebraMap ℚ L r) (μ : YoungDiagram) :
    DopStar q u 0 (H μ) = -(paramProduct q⁻¹ u⁻¹ * cellSumInv q u μ - 1) • H μ := by
  obtain ⟨c, hc⟩ := h.exists_inversion_smul μ
  have hcc : ∀ A : L, ι c * A * c = A := fun A => by
    rw [mul_comm (ι c) A, mul_assoc,
      mul_inversion_eigenvalue_eq_one ι hιι (h.ne_zero μ) hc, mul_one]
  rw [dopStar_zero_eq ι hq hu hιι hQ, hc, map_smul, h.dop_zero μ, inversion_smul, inversion_smul,
    hc, smul_smul, smul_smul, map_neg, map_sub, map_one, map_mul, paramInv_paramProduct ι hq hu,
    paramInv_cellSum ι hq hu, hcc]

end IsUnnormalisedMacdonaldEigenbasis

/-- A Macdonald eigenbasis is an unnormalised one: clause `(c)` names the `↓`-eigenvalue, and the
weakened clause asks only that there be one. No hypothesis on `q` or `u` is needed. -/
theorem IsMacdonaldEigenbasis.unnormalised {ι : L →+* L} {H : YoungDiagram → Lambda L}
    (h : IsMacdonaldEigenbasis ι q u H) : IsUnnormalisedMacdonaldEigenbasis ι q u H where
  ne_zero := h.linearIndependent.ne_zero
  span_eq_top := h.span_eq_top
  dop_zero := h.dop_zero
  exists_inversion_smul μ := ⟨(cellProd q u μ)⁻¹, h.inversion_apply μ⟩

end Unnormalised

/-! ### The two residual hypotheses of the collinear goal -/

section Residual

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **The first residual hypothesis: an unnormalised Macdonald eigenbasis exists.** This is
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_param` with the value `T_μ⁻¹` struck out of clause
`(c)` of `HJO.Sym.IsMacdonaldEigenbasis` and linear independence struck out of clause `(a)`, and it
is strictly weaker than that statement. -/
def HasUnnormalisedMacdonaldEigenbasis (ι : L →+* L) (q u : L) : Prop :=
  ∃ H : YoungDiagram → Lambda L, IsUnnormalisedMacdonaldEigenbasis ι q u H

/-- **The second residual hypothesis: some `D_0`-eigenfamily has covering Pieri support.** A family
`(G_μ)` of nonzero elements satisfying clause `(b)` of `HJO.Sym.IsMacdonaldEigenbasis` for which
`e₁ G_ν` lies in the `𝕜`-span of the `G_μ` with `μ` covering `ν`.

This is `HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param` with four requirements dropped:
`(G_μ)` need not be linearly independent (`linearIndependent_of_dop_zero` supplies that), need not
span `Λ`, need not satisfy any inversion clause, and need not be the family of the first residual
hypothesis. What makes the last three droppable is
`HJO.Standing.elemSymm_one_mul_mem_span_of_dop_zero_param`, whose transport half
(`HJO.Sym.elemSymm_one_mul_mem_of_dop_zero`) is proved: at generic parameters with `M ≠ 0` the
support passes from any one such family to every Macdonald eigenbasis, because two families with the
same `D_0` eigenvalues differ by one nonzero scalar per index. -/
def HasPieriEigenfamily (q u : L) : Prop :=
  ∃ G : YoungDiagram → Lambda L, (∀ μ : YoungDiagram, G μ ≠ 0) ∧
    (∀ μ : YoungDiagram, Dop q u 0 (G μ) = dopZeroEigenvalue q u μ • G μ) ∧
    ∀ ν : YoungDiagram,
      elemSymm L 1 * G ν ∈ Submodule.span L (G '' {μ : YoungDiagram | Covers μ ν})

/-- An unnormalised Macdonald eigenbasis is a modified Macdonald family, once some `D_0`-eigenfamily
is known to have covering Pieri support.

Clauses (i) and (ii) of `HJO.Sym.IsModifiedMacdonaldFamily` are clauses `(a)` and `(b)`, the first
recovered by `IsUnnormalisedMacdonaldEigenbasis.linearIndependent`; clause (iii) is
`IsUnnormalisedMacdonaldEigenbasis.dopStar_zero`; clause (iv) is transported from the Pieri family
by `HJO.Sym.elemSymm_one_mul_mem_of_dop_zero`.

Against `HJO.Sym.isModifiedMacdonaldFamily_of_isMacdonaldEigenbasis` the hypotheses `q ≠ 0` and
`u ≠ 0` are gone, clause `(c)` no longer names its eigenvalue, neither family is assumed linearly
independent, and the Pieri family is separate. The genericity hypothesis `hqu` remains and is not
removable: clause (iv) passes through `HJO.Sym.exists_smul_of_dop_zero_eigenbasis`, which is false
at `M = 0` and false at non-generic `(q, u)`.
Genericity covers the first of those itself, by `HJO.Sym.paramProduct_ne_zero`, so `M ≠ 0` is not
asked for beside it. -/
theorem isModifiedMacdonaldFamily_of_isUnnormalisedMacdonaldEigenbasis
    (hqu : AlgebraicIndependent ℤ ![q, u]) {ι : L →+* L}
    (hq : ι q = q⁻¹) (hu : ι u = u⁻¹) (hιι : ∀ c : L, ι (ι c) = c)
    (hQ : ∀ r : ℚ, ι (algebraMap ℚ L r) = algebraMap ℚ L r) (hpieri : HasPieriEigenfamily q u)
    {H : YoungDiagram → Lambda L} (hH : IsUnnormalisedMacdonaldEigenbasis ι q u H) :
    IsModifiedMacdonaldFamily q u H := by
  obtain ⟨G, hGne, hGdop, hGpieri⟩ := hpieri
  have hG : LinearIndependent L G := linearIndependent_of_dop_zero hqu hGne hGdop
  exact
    { linearIndependent := hH.linearIndependent hqu
      span_eq_top := hH.span_eq_top
      dop_zero := hH.dop_zero
      dopStar_zero := hH.dopStar_zero hq hu hιι hQ
      elemSymm_one_mul_mem :=
        elemSymm_one_mul_mem_of_dop_zero hqu hG hGdop hGpieri (hH.linearIndependent hqu)
          hH.span_eq_top fun μ => hH.dop_zero μ }

/-- **`HJO.Standing.exists_isModifiedMacdonaldFamily_param'` from the two residual hypotheses.** A
modified Macdonald family exists, given an unnormalised Macdonald eigenbasis and some
`D_0`-eigenfamily with covering Pieri support. -/
theorem exists_isModifiedMacdonaldFamily_of_hasPieriEigenfamily
    (hqu : AlgebraicIndependent ℤ ![q, u]) {ι : L →+* L} (hq : ι q = q⁻¹) (hu : ι u = u⁻¹)
    (hιι : ∀ c : L, ι (ι c) = c) (hQ : ∀ r : ℚ, ι (algebraMap ℚ L r) = algebraMap ℚ L r)
    (hbasis : HasUnnormalisedMacdonaldEigenbasis ι q u) (hpieri : HasPieriEigenfamily q u) :
    ∃ H : YoungDiagram → Lambda L, IsModifiedMacdonaldFamily q u H := by
  obtain ⟨H, hH⟩ := hbasis
  exact ⟨H, isModifiedMacdonaldFamily_of_isUnnormalisedMacdonaldEigenbasis hqu hq hu hιι hQ
    hpieri hH⟩

/-- **The whole collinear side from the two residual hypotheses**: a Macdonald conjugator exists,
given an unnormalised Macdonald eigenbasis and some `D_0`-eigenfamily with covering Pieri support.

`q ≠ 0` and `u ≠ 0` reappear here, but for a different reason than in
`HJO.Sym.exists_isMacdonaldConjugator_of_exists_isMacdonaldEigenbasis`: they are hypotheses of
`HJO.Sym.exists_isMacdonaldConjugator` itself, which needs `T_μ` invertible to invert the
eigenoperator `∇`, and they are no longer spent on clause (iii). -/
theorem exists_isMacdonaldConjugator_of_hasPieriEigenfamily (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hqu : AlgebraicIndependent ℤ ![q, u]) {ι : L →+* L}
    (hq : ι q = q⁻¹) (hu : ι u = u⁻¹) (hιι : ∀ c : L, ι (ι c) = c)
    (hQ : ∀ r : ℚ, ι (algebraMap ℚ L r) = algebraMap ℚ L r)
    (hbasis : HasUnnormalisedMacdonaldEigenbasis ι q u) (hpieri : HasPieriEigenfamily q u) :
    ∃ nabla : Module.End L (Lambda L), IsMacdonaldConjugator q u nabla :=
  exists_isMacdonaldConjugator hq0 hu0 (paramProduct_ne_zero hqu)
    (exists_isModifiedMacdonaldFamily_of_hasPieriEigenfamily hqu hq hu hιι hQ hbasis hpieri)

/-- The bundled hypothesis of `HJO.Sym.exists_isMacdonaldConjugator_of_exists_isMacdonaldEigenbasis`
implies both residual hypotheses, so this file's reduction is at least as strong as that one. The
converse fails: nothing in the two residual Props names the `↓`-eigenvalue. -/
theorem hasUnnormalisedMacdonaldEigenbasis_and_hasPieriEigenfamily {ι : L →+* L}
    (hex : ∃ H : YoungDiagram → Lambda L, IsMacdonaldEigenbasis ι q u H ∧
      ∀ ν, elemSymm L 1 * H ν ∈ Submodule.span L (H '' {μ : YoungDiagram | Covers μ ν})) :
    HasUnnormalisedMacdonaldEigenbasis ι q u ∧ HasPieriEigenfamily q u := by
  obtain ⟨H, hH, hpieri⟩ := hex
  exact ⟨⟨H, hH.unnormalised⟩,
    ⟨H, hH.linearIndependent.ne_zero, fun μ => hH.dop_zero μ, hpieri⟩⟩

end Residual

end HJO.Sym

namespace HJO.Standing

open HJO.Ascent HJO.Sym

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- **A Macdonald conjugator exists at the standing field**, given an unnormalised Macdonald
eigenbasis for the constructed coefficient inversion and some `D_0`-eigenfamily with covering Pieri
support.

This is `HJO.Standing.exists_isMacdonaldConjugator_param` with its one hypothesis made strictly
smaller: the bundle of four properties on a single family becomes two independent Props, clause
`(c)` of `HJO.Sym.IsMacdonaldEigenbasis` no longer names its eigenvalue `T_μ⁻¹`, and the family
carrying the Pieri support need neither span `Λ` nor satisfy any inversion clause. Everything else
the statement needs is discharged as before, from `HJO/Macdonald/StandingFacts.lean` and
`HJO.Ascent.paramQUInvHom`.

The two hypotheses are what remains of `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_param` and
`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`. -/
theorem exists_isMacdonaldConjugator_of_hasPieriEigenfamily_param
    (hbasis : HasUnnormalisedMacdonaldEigenbasis (paramQUInvHom K) (paramQ K) (paramU K))
    (hpieri : HasPieriEigenfamily (paramQ K) (paramU K)) :
    ∃ nabla : Module.End K (Lambda K), IsMacdonaldConjugator (paramQ K) (paramU K) nabla :=
  HJO.Sym.exists_isMacdonaldConjugator_of_hasPieriEigenfamily (paramQ_ne_zero K)
    (paramU_ne_zero K) (algebraicIndependent_param K) (paramQUInvHom_paramQ K)
    (paramQUInvHom_paramU K) (paramQUInvHom_involutive K)
    (ringHom_algebraMap_rat (paramQUInvHom K)) hbasis hpieri

end HJO.Standing
