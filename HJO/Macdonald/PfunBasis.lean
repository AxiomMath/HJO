/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.HtildeSpan
public import HJO.Macdonald.PieriSupport
public meta import HJO.Attr

/-! # Macdonald's symmetric functions of one degree, and the Pieri support in coordinates

`HJO.Sym.exists_basis_lambdaComp_macPfun`: the family `P_μ`, indexed by the partitions `μ` with
`|μ| = d`, is a `𝕜`-basis of `Λ_d`. It is what turns "`e₁P_ν` lies in a span" into "the coefficients
`c_λ` of `e₁P_ν = ∑_λ c_λP_λ` vanish off the covers", which is the shape
`HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short`,
`HJO.Mac.rowLen_zero_le_of_coeff_ne_zero`, `HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero` and
`HJO.Ascent.coeff_transpose_ne_zero_of_coeff_ne_zero` are all stated in.

This file proves it, proves `HJO.Sym.elemSymm_one_mul_macPfun_mem_lambdaComp`, and uses both to
reduce `HJO.Sym.HasPfunPieriSupport` -- the statement `HJO.Standing.hasPfunPieriSupport_param` --
to its coefficient form
`HJO.Sym.HasPfunPieriCoeff`. The base case `ν = ∅` of the induction is then proved outright.

## Main definitions

* `HJO.Sym.partDiagramEquiv`: the indices of the monomial symmetric basis at the base alphabet of
  degree `d` **are** the diagrams with `d` cells.
* `HJO.Sym.HasPfunPieriCoeff`: `HJO.Standing.hasPfunPieriSupport_param` in coordinates -- in any
  expansion `e₁P_ν = ∑_{μ ∈ S} c_μ P_μ` with every index of size `|ν| + 1`, a nonzero `c_μ` forces
  `μ ⋗ ν`.

## Main results

* `HJO.Sym.exists_basis_lambdaComp_macPfun`.
* `HJO.Sym.lambdaComp_le_span_macPfun_card`: the graded refinement of
  `HJO.Sym.lambdaComp_le_span_macPfun` -- `Λ_D` is spanned by the `P_μ` **of size `D`**.
* `HJO.Sym.elemSymm_one_mul_macPfun_mem_lambdaComp`.
* `HJO.Sym.hasPfunPieriSupport_of_hasPfunPieriCoeff`: `HJO.Standing.hasPfunPieriSupport_param` from
  its coefficient form.
* `HJO.Sym.elemSymm_one_mul_macPfun_bot_mem_span`: the case `ν = ∅`, where `e₁P_∅ = e₁` spans
  `Λ_1` on its own and every diagram with one cell covers `∅`.

## Why the duality is needed

**The duality is not avoidable by a cheaper argument.** What the conjugate side supplies is the
exclusion of an index with *more* nonzero rows than `ν`, and the tools that need no duality do not
reach it. The column-removal induction of `HJO.Standing.hasPfunPieriSupport_param` sees only the `λ`
with at most `ℓ(ν)` rows; the dominance triangularity of `HJO.Mac.macPpoly` and the lexicographic
leading exponent of `HJO.Mac.coeff_partExp_macPpoly` give `λ₁ ≤ ν₁ + 1` and the entrywise dominance
bound, and `HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero` read on the rows rather than the columns
disposes of `λ₁ = ν₁ + 1`. Those three together are not enough: at `ν = (3,2,2,1)` the index
`λ = (3,3,1,1,1)` has `|λ| = |ν| + 1`, dominates `ν`, has `λ₁ = ν₁` and `ℓ(λ) = ℓ(ν) + 1`, and
does **not** contain `ν` -- while the conjugates rule it out at once, `λ' = (5,2,2)` having
`λ'₁ = ν'₁ + 1` and `λ'₂ ≠ ν'₂` for `ν' = (4,3,1)`. So an argument that never conjugates has to
exclude `(3,3,1,1,1)` by some other means, and `HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero` is the only
lemma that can.

## Where genericity is spent, and the degenerate corners

Nowhere and none. `AlgebraicIndependent ℤ ![(q : K), u]` is carried only because `macPfun` and
`macPpoly` are functions of it; no nonvanishing is consumed.

The degenerate corners cannot be reached at all: `HasPfunPieriSupport` takes the genericity as the
argument of `macPfun`, and `AlgebraicIndependent ℤ ![q, u]` already excludes every one of them --
`u = 0` by the polynomial `Y`, `u = 1` by `Y - 1`, `u = -1` by `Y + 1`, `u` a `k`-th root of unity
by `Y ^ k - 1`, `q = 0` by `X` and `qu = 1` by `XY - 1`. So unlike
`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`, which is false at `u = 1` and at `u = 0`,
this statement has no hypothesis to omit: it is stated at parameters that are generic by
construction. The satisfiable side is `elemSymm_one_mul_macPfun_bot_mem_span`: at `ν = ∅` the claim
reads `e₁ ∈ span{P_μ : |μ| = 1}` and is proved below.

## References

This file formalises Lemmas `HJO.Sym.exists_basis_lambdaComp_macPfun`,
`HJO.Sym.elemSymm_one_mul_macPfun_mem_lambdaComp` and `HJO.Standing.hasPfunPieriSupport_param`, on
Definitions `HJO.Sym.Lambda`, `HJO.Sym.LambdaComp`, `HJO.Sym.elemSymm`, `HJO.Sym.rowLenSeq`,
`HJO.Sym.cells`, `HJO.Sym.Covers`, `HJO.Sym.restrictAlphabet`, `HJO.Mac.macPpoly` and
`HJO.Sym.macPfun` and Lemmas `HJO.Mac.exists_basis_macPpoly`,
`HJO.Sym.restrictAlphabetComp_bijective` and `HJO.Sym.elemSymm_one`.
-/

@[expose] public section

open MvPolynomial HJO.Mac

namespace HJO.Sym

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

/-! ### The diagrams of a given size, as indices in one alphabet -/

/-- The base alphabet of degree `d` has at least `d` letters. This is the hypothesis of
`HJO.Sym.restrictAlphabetEquiv` and of `HJO.Sym.macPfun_partDiagram` at that alphabet. -/
theorem card_le_card_baseAlphabetOfDeg (d : ℕ) : d ≤ Fintype.card (Fin (max d 1)) := by
  rw [Fintype.card_fin]
  exact le_max_left _ _

/-- **The indices of the monomial symmetric basis of `𝒮_{n_d, d}` are the diagrams with `d` cells.**
The forward map is `HJO.Mac.partDiagram`, injective by `HJO.Mac.partDiagram_injective` and landing
in the diagrams of size `d` by `HJO.Mac.card_partDiagram`; it is onto them by
`HJO.Mac.exists_partDiagram_eq`, whose hypothesis is that the alphabet truncates no row of the
diagram and holds because a diagram with `d` cells has no row at index `d`
(`HJO.Mac.rowLen_eq_zero_of_card_le`).

This is the reindexing `HJO.Sym.exists_basis_lambdaComp_macPfun` needs: the statement indexes the
basis of `Λ_d` by the partitions of `d` while `HJO.Mac.exists_basis_macPpoly` indexes the basis of
`𝒮_{n_d, d}` by `PartIdx`. -/
noncomputable def partDiagramEquiv (d : ℕ) :
    PartIdx (Fin (max d 1)) d ≃ {μ : YoungDiagram // μ.card = d} :=
  Equiv.ofBijective (fun ν => ⟨partDiagram (Fin (max d 1)) ν, card_partDiagram ν⟩)
    ⟨fun _ _ h => partDiagram_injective (Subtype.ext_iff.mp h), by
      rintro ⟨μ, hμ⟩
      subst hμ
      obtain ⟨ν, hν⟩ := exists_partDiagram_eq (σ := Fin (max μ.card 1))
        (rowLen_eq_zero_of_card_le (card_le_card_baseAlphabetOfDeg μ.card))
      exact ⟨ν, Subtype.ext hν⟩⟩

@[simp]
theorem coe_partDiagramEquiv {d : ℕ} (ν : PartIdx (Fin (max d 1)) d) :
    (partDiagramEquiv d ν : YoungDiagram) = partDiagram (Fin (max d 1)) ν := rfl

/-- The diagram of the index `(partDiagramEquiv d).symm μ` is `μ` itself. -/
theorem partDiagram_partDiagramEquiv_symm {d : ℕ} (μ : {μ : YoungDiagram // μ.card = d}) :
    partDiagram (Fin (max d 1)) ((partDiagramEquiv d).symm μ) = (μ : YoungDiagram) :=
  congrArg Subtype.val ((partDiagramEquiv d).apply_symm_apply μ)

/-! ### Macdonald's symmetric functions of one degree are a basis of that degree -/

/-- **The `P_μ` with `|μ| = d` are a `𝕜`-basis of `Λ_d`.**

The `P_μ[X_{n_d}]` are a basis of `𝒮_{n_d, d}` (`HJO.Mac.exists_basis_macPpoly`,
`HJO.Mac.exists_basis_macPpoly`) and `res_{n_d}` carries `Λ_d` isomorphically onto `𝒮_{n_d, d}`
(`HJO.Sym.restrictAlphabetEquiv`, `HJO.Sym.restrictAlphabetComp_bijective`), so the preimage of that
basis is a basis of `Λ_d`; `HJO.Sym.macPfun_partDiagram` says its members are the `P_μ`, and
`partDiagramEquiv` reindexes it by the diagrams of size `d`.

The usual route to this statement goes through `HJO.Mac.restrictAlphabet_macPfun_partDiagram` --
`res_n(P_μ) = P_μ[X_n]` for
*every* `n ≥ |μ|` -- and so through the whole alphabet descent. None of that is needed, for the
reason recorded in `HJO/Macdonald/HtildeSpan.lean`: the alphabet of `HJO.Sym.macPfun` depends
on `μ` through `|μ|` alone, so all the `P_μ` of one degree already live in one alphabet and the
restriction named by `HJO.Sym.macPfun` is the only one that occurs.

"The family is a basis" is the existence of a bundled basis whose members are the `P_μ`, as in
`HJO.Mac.exists_basis_macPpoly`: the equation `(B μ : Λ) = P_μ` is what makes this a statement about
Macdonald's symmetric functions. -/
@[hjo "lem_mac_pfun_component_basis"]
theorem exists_basis_lambdaComp_macPfun (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (d : ℕ) :
    ∃ B : Module.Basis {μ : YoungDiagram // μ.card = d} K (LambdaComp K d),
      ∀ μ : {μ : YoungDiagram // μ.card = d},
        (B μ : Lambda K) = macPfun hqu (μ : YoungDiagram) := by
  obtain ⟨B, hB⟩ := exists_basis_macPpoly (σ := Fin (max d 1)) (K := K) (q := q) (u := u) (d := d)
    hqu
  refine ⟨(B.map (restrictAlphabetEquiv (Fin (max d 1)) K
    (card_le_card_baseAlphabetOfDeg d)).symm).reindex (partDiagramEquiv d), fun μ => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply, hB,
    ← macPfun_partDiagram hqu (card_le_card_baseAlphabetOfDeg d),
    partDiagram_partDiagramEquiv_symm]

/-- **A graded piece is spanned by Macdonald's symmetric functions of that degree.** This is the
refinement of `HJO.Sym.lambdaComp_le_span_macPfun` that records the size of the indices, which is
what an expansion of an element of `Λ_D` in the `P_μ` needs in order to have all its indices of
size `D`. -/
theorem lambdaComp_le_span_macPfun_card (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (D : ℕ) :
    LambdaComp K D
      ≤ Submodule.span K (macPfun hqu '' {μ : YoungDiagram | μ.card = D}) := by
  intro f hf
  obtain ⟨B, hB⟩ := exists_basis_lambdaComp_macPfun hqu D
  have hmem : f ∈ Submodule.map (LambdaComp K D).subtype
      (Submodule.span K (Set.range B)) := ⟨⟨f, hf⟩, by rw [B.span_eq]; trivial, rfl⟩
  rw [Submodule.map_span] at hmem
  refine Submodule.span_le.mpr ?_ hmem
  rintro g ⟨y, ⟨μ, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨(μ : YoungDiagram), μ.2, (hB μ).symm⟩

/-! ### The product with the first elementary symmetric function -/

/-- **`HJO.Sym.elemSymm_one_mul_macPfun_mem_lambdaComp`: `e₁P_ν` lies in `Λ_{|ν|+1}`.** `e₁ = p₁`
(`HJO.Sym.elemSymm_one`) is the generator `X 0` of `Λ = 𝕜[p₁, p₂, …]`, weighted homogeneous of
degree `1`, and `P_ν ∈ Λ_{|ν|}` by `HJO.Sym.macPfun`; a product of weighted homogeneous elements is
weighted homogeneous of the sum of the degrees. -/
@[hjo "lem_dua_pfun_component"]
theorem elemSymm_one_mul_macPfun_mem_lambdaComp (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (ν : YoungDiagram) : elemSymm K 1 * macPfun hqu ν ∈ LambdaComp K (ν.card + 1) := by
  have he : elemSymm K 1 ∈ LambdaComp K 1 := by
    rw [elemSymm_one, powerSum]
    exact isWeightedHomogeneous_X K _ 0
  have h := (mem_lambdaComp.mp he).mul (mem_lambdaComp.mp (macPfun_mem hqu ν))
  rw [Nat.add_comm] at h
  exact mem_lambdaComp.mpr h

/-! ### The Pieri support in coordinates -/

/-- **`HJO.Standing.hasPfunPieriSupport_param` in coordinates**: in every expansion
`e₁P_ν = ∑_{μ ∈ S} c_μ P_μ` whose indices all have `|μ| = |ν| + 1`, a nonzero coefficient forces
`μ ⋗ ν`.

This is the form the usual proof of `HJO.Standing.hasPfunPieriSupport_param` reaches for and the
form `HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short`,
`HJO.Mac.rowLen_zero_le_of_coeff_ne_zero`, `HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero` and
`HJO.Ascent.coeff_transpose_ne_zero_of_coeff_ne_zero` are stated in, so it is the right residual to
leave: the passage from it to the span statement is `hasPfunPieriSupport_of_hasPfunPieriCoeff` and
is the only place `HJO.Sym.exists_basis_lambdaComp_macPfun` is spent.

The standard formulation quantifies over a family indexed by the finitely many partitions of
`|ν| + 1`; the `Finset` here is that index set with the zero coefficients discarded, which is the
same statement and needs no finiteness of the set of partitions. Nothing about the parameters is
asked beyond the genericity `macPfun` carries, exactly as in `HJO.Sym.HasPfunPieriSupport`. -/
def HasPfunPieriCoeff (hqu : AlgebraicIndependent ℤ ![(q : K), u]) : Prop :=
  ∀ (ν : YoungDiagram) (S : Finset YoungDiagram) (c : YoungDiagram → K),
    (∀ μ ∈ S, μ.card = ν.card + 1) →
    elemSymm K 1 * macPfun hqu ν = ∑ μ ∈ S, c μ • macPfun hqu μ →
    ∀ μ ∈ S, c μ ≠ 0 → Covers μ ν

/-- **`HJO.Standing.hasPfunPieriSupport_param` from its coefficient form.** `e₁P_ν` lies in
`Λ_{|ν|+1}` (`HJO.Sym.elemSymm_one_mul_macPfun_mem_lambdaComp`), the `P_μ` with `|μ| = |ν|+1` are a
basis of that graded piece (`HJO.Sym.exists_basis_lambdaComp_macPfun`), so `e₁P_ν` has one expansion
of the shape `HasPfunPieriCoeff` speaks about; the coefficients off the covers vanish, and what is
left is a combination of the `P_μ` with `μ ⋗ ν`. -/
theorem hasPfunPieriSupport_of_hasPfunPieriCoeff (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (h : HasPfunPieriCoeff hqu) : HasPfunPieriSupport hqu := by
  classical
  intro ν
  obtain ⟨B, hB⟩ := exists_basis_lambdaComp_macPfun hqu (ν.card + 1)
  set x : LambdaComp K (ν.card + 1) :=
    ⟨elemSymm K 1 * macPfun hqu ν, elemSymm_one_mul_macPfun_mem_lambdaComp hqu ν⟩ with hxdef
  set r : {μ : YoungDiagram // μ.card = ν.card + 1} →₀ K := B.repr x with hrdef
  -- the coefficient, read at a bare diagram
  set c : YoungDiagram → K := fun μ => if hμ : μ.card = ν.card + 1 then r ⟨μ, hμ⟩ else 0 with hcdef
  have hcval : ∀ μ : {μ : YoungDiagram // μ.card = ν.card + 1}, c (μ : YoungDiagram) = r μ :=
    fun μ => by rw [hcdef]; exact dite_eq_iff.mpr (Or.inl ⟨μ.2, rfl⟩)
  set S : Finset YoungDiagram :=
    r.support.image (fun ρ : {μ : YoungDiagram // μ.card = ν.card + 1} => (ρ : YoungDiagram))
    with hSdef
  have hinj : Set.InjOn (fun ρ : {μ : YoungDiagram // μ.card = ν.card + 1} => (ρ : YoungDiagram))
      r.support := fun _ _ _ _ hab => Subtype.ext hab
  have hcard : ∀ μ ∈ S, μ.card = ν.card + 1 := by
    intro μ hμ
    obtain ⟨ρ, -, rfl⟩ := Finset.mem_image.mp hμ
    exact ρ.2
  -- the expansion of `e₁P_ν` in the basis, read as a sum over diagrams
  have hsum : elemSymm K 1 * macPfun hqu ν = ∑ μ ∈ S, c μ • macPfun hqu μ := by
    rw [hSdef, Finset.sum_image hinj]
    have hx : (x : Lambda K) = ∑ μ ∈ r.support, (r μ) • (B μ : Lambda K) := by
      have h1 := B.linearCombination_repr x
      rw [Finsupp.linearCombination_apply, Finsupp.sum, ← hrdef] at h1
      have h2 := congrArg (Subtype.val (p := fun f => f ∈ LambdaComp K (ν.card + 1))) h1.symm
      rw [AddSubmonoidClass.coe_finsetSum] at h2
      simpa only [SetLike.val_smul] using h2
    rw [show elemSymm K 1 * macPfun hqu ν = (x : Lambda K) from rfl, hx]
    exact Finset.sum_congr rfl fun μ _ => by rw [hcval μ, hB μ]
  rw [hsum]
  refine Submodule.sum_mem _ fun μ hμ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hμ
  refine ⟨(ρ : YoungDiagram), h ν S c hcard hsum _ hμ ?_, rfl⟩
  rw [hcval ρ]
  exact Finsupp.mem_support_iff.mp (Finset.mem_coe.mpr hρ)

/-- **The case `ν = ∅` of `HJO.Standing.hasPfunPieriSupport_param`**, which is the statement's
sanity check and needs none of the induction: `e₁P_∅` lies in `Λ_1`
(`HJO.Sym.elemSymm_one_mul_macPfun_mem_lambdaComp`), that graded piece is spanned by the `P_μ` with
`|μ| = 1` (`lambdaComp_le_span_macPfun_card`), and every diagram with one cell covers `∅`, the empty
diagram being below everything. -/
theorem elemSymm_one_mul_macPfun_bot_mem_span (hqu : AlgebraicIndependent ℤ ![(q : K), u]) :
    elemSymm K 1 * macPfun hqu ⊥
      ∈ Submodule.span K (macPfun hqu '' {μ : YoungDiagram | Covers μ ⊥}) := by
  have hbot : (⊥ : YoungDiagram).card = 0 := rfl
  have hmem : elemSymm K 1 * macPfun hqu ⊥ ∈ LambdaComp K 1 := by
    have h := elemSymm_one_mul_macPfun_mem_lambdaComp hqu ⊥
    rwa [hbot, Nat.zero_add] at h
  refine Submodule.span_le.mpr ?_ (lambdaComp_le_span_macPfun_card hqu 1 hmem)
  rintro x ⟨μ, hμ, rfl⟩
  exact Submodule.subset_span
    ⟨μ, ⟨bot_le, show μ.card = (⊥ : YoungDiagram).card + 1 by rw [hμ, hbot]⟩, rfl⟩

end HJO.Sym
