/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.Ppoly
public import HJO.Symmetric.TriangularBasis
public meta import HJO.Attr

/-! # Macdonald's polynomials are a basis of a graded piece

`HJO.Mac.exists_basis_macPpoly`: the family `P_μ[X_n]`, indexed by the partitions `μ` of `d` with at
most `n` parts, is a `𝕜`-basis of `𝒮_{n,d}`.

## Main results

* `HJO.Mac.exists_basis_macPpoly`: the family `macPpoly hqu` is a basis of
  `symmetricHomogeneousSubmodule σ K d`.

## The proof, and the direction of the order

This is `Module.Basis.exists_basis_of_triangular` applied to the
monomial symmetric basis with every diagonal coefficient `1`, which is a unit: `P_μ[X_n]` is
`m_μ[X_n]` plus a combination of the other basis vectors, so the matrix of the family is triangular
with `1`s on the diagonal.

The one thing to arrange is the *direction*. `HJO.Mac.macPpoly_sub_msymm_mem_span` puts the
correction term **below** `μ` — in the span of the `m_ν[X_n]` with `\bar\nu <_lex \bar\mu`, which is
`Set.Iio μ` for `HJO.Mac.partIdxLexOrder` — while `Module.Basis.exists_basis_of_triangular` asks for
it **above**, in `⇑B '' Set.Ioi μ`. This is the "reverse of the lexicographic order" of the standard
proof, and it is taken here by transporting the order rather than by restating either side: the
order used is `OrderDual.instLinearOrder` at `partIdxLexOrder σ d`, for which `ν ∈ Set.Ioi μ`
unfolds to `toLex (partExp σ ν) < toLex (partExp σ μ)` — the condition itself, by definitional
unfolding and not up to a lemma. So no reversed triangularity lemma is stated, and no basis is
reindexed: the index type stays `PartIdx σ d`, and the basis produced is the family `macPpoly hqu`
indexed by that type, as asserted.

`exists_basis_of_triangular` also wants `WellFoundedGT` on the index. `PartIdx σ d` is a finite
type, so both it and its order dual carry `WellFoundedGT` by instance and nothing extra is supplied
— which is the appeal to `HJO.Sym.finite_setOf_card_eq` for the finiteness of its index set.

The only other step is bookkeeping: the triangularity is available as a membership in a span of
*polynomials*, and the basis lemma wants one in a span inside the submodule `𝒮_{n,d}`. The
inclusion of a submodule is injective, so `Submodule.apply_mem_span_image_iff_mem_span` turns the
one into the other, the image of the basis under it being the set of `m_ν[X_n]` by the defining
property of the monomial symmetric basis.

## Hypotheses

The genericity `AlgebraicIndependent ℤ ![(q : K), u]` is carried only because `macPpoly` is a
function of it; nothing here spends it. The `n ≥ 1` is dropped: at an empty alphabet
the statement is still true, `PartIdx σ d` then being empty for `d ≥ 1` and a singleton for
`d = 0`, and `𝒮_{0,d}` correspondingly.

## References

`HJO.Mac.exists_basis_macPpoly` is used by
`HJO.Sym.exists_basis_lambdaComp_macPfun`, `HJO.Mac.macOpCompInv_macPpoly`,
`HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero` and `HJO.Standing.hasPfunPieriSupport_param`.
-/

@[expose] public section

open Finset MvPolynomial MonomialOrder

namespace HJO.Mac

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [Field K] [Algebra ℚ K]
  {q : Kˣ} {u : K} {d : ℕ}

/-- **Macdonald's polynomials are a basis of a graded piece.** The family `P_μ[X_n]`, indexed by
the partitions `μ` of `d` with at most `n` parts, is a `𝕜`-basis of `𝒮_{n,d}`.

"The family is a basis" is stated as the existence of a bundled basis indexed by `PartIdx σ d`
whose coercion to a function is `macPpoly hqu`, as in `Module.Basis.exists_basis_of_triangular`;
the equation `⇑B = macPpoly hqu` is what makes this a statement about `P_μ[X_n]`. -/
@[hjo "lem_mac_ppoly_basis"]
theorem exists_basis_macPpoly (hqu : AlgebraicIndependent ℤ ![(q : K), u]) :
    ∃ B : Module.Basis (PartIdx σ d) K (symmetricHomogeneousSubmodule σ K d),
      ⇑B = macPpoly hqu := by
  classical
  obtain ⟨B, hB⟩ := exists_basis_symmetricHomogeneousSubmodule_msymm σ K d
  -- the reverse of the lexicographic order, for which `Set.Ioi μ` *is* the lower set
  let _ : LinearOrder (PartIdx σ d) := @OrderDual.instLinearOrder _ (partIdxLexOrder σ d)
  refine Module.Basis.exists_basis_of_triangular B (c := fun _ => (1 : K)) (v := macPpoly hqu)
    (fun _ => isUnit_one) fun μ => ?_
  rw [one_smul, ← Submodule.apply_mem_span_image_iff_mem_span
    (Submodule.injective_subtype (symmetricHomogeneousSubmodule σ K d))]
  -- the image of the monomial symmetric basis is the family of `m_ν[X_n]`
  have hset : (symmetricHomogeneousSubmodule σ K d).subtype '' (⇑B '' Set.Ioi μ)
      = {p : MvPolynomial σ K | ∃ ν : PartIdx σ d,
          toLex (partExp σ ν) < toLex (partExp σ μ) ∧ p = msymm σ K ν.1} := by
    rw [Set.image_image]
    ext p
    exact ⟨fun ⟨ν, hν, hp⟩ => ⟨ν, hν, by rw [← hp]; simpa using hB ν⟩,
      fun ⟨ν, hν, hp⟩ => ⟨ν, hν, by rw [hp]; simpa using hB ν⟩⟩
  rw [hset, Submodule.subtype_apply,
    show ((macPpoly hqu μ - B μ : symmetricHomogeneousSubmodule σ K d) : MvPolynomial σ K)
      = (macPpoly hqu μ : MvPolynomial σ K) - msymm σ K μ.1 by rw [Submodule.coe_sub, hB]]
  exact macPpoly_sub_msymm_mem_span hqu μ

end HJO.Mac
