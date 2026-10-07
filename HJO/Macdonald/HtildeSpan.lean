/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.Htilde
public meta import HJO.Attr

/-! # Macdonald's symmetric functions span, and so does the modified family

The spanning half of `HJO.Sym.exists_basis_macPfun` and of `HJO.Standing.exists_basis_macHtilde`:
the `P_μ` span `Λ` over `𝕜`, and so do the `H̃_μ`. The second is the hypothesis `hspan` of
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param`, and it is discharged here.

## Main results

* `HJO.Sym.lambdaComp_le_span_macPfun`: the graded piece `Λ_d` lies in the span of the `P_μ`.
* `HJO.Sym.span_range_macPfun_eq_top`: the `P_μ` span `Λ`.
* `HJO.Sym.span_range_macHtilde_eq_top`: the `H̃_μ` span `Λ`.
* `HJO.Standing.span_range_macHtilde_param_eq_top`: the same at the standing field, in the shape
  `hasUnnormalisedMacdonaldEigenbasis_macHtilde_param` asks for.
* `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_dop_param`: that reduction with
  `hspan` struck out, so that **two** hypotheses remain,
  `HJO.Standing.dop_zero_smul_macHtilde_param` and `HJO.Sym.coeffSubst_macPfun`.

## The base alphabet of a degree, and why `HJO.Mac.restrictAlphabet_macPfun_partDiagram` is not
needed

The usual proof of `HJO.Sym.exists_basis_macPfun` goes through
`HJO.Sym.exists_basis_lambdaComp_macPfun`, which needs
`HJO.Mac.restrictAlphabet_macPfun_partDiagram` --- `res_n(P_μ) = P_μ[X_n]` for *every* `n ≥ |μ|`,
whose proof runs through `HJO.Sym.killCompl_restrictAlphabet`, `HJO.Mac.killComplComp_macPpoly` and
`MvPolynomial.killComplComp_bijective`. **None of that is used here**, and the reason is a feature
of `HJO.Sym.macPfun`: its alphabet `HJO.Mac.baseAlphabet μ` is `Fin (max μ.card 1)`, which depends
on `μ` only through `|μ|`. So all the `P_μ` of a given degree `d` are already defined in *one*
alphabet, and `res_{n_μ}` --- the only restriction `HJO.Sym.macPfun` mentions --- suffices: no
comparison between two alphabets ever arises.

Concretely, `HJO.Mac.baseIdx` and `HJO.Mac.partDiagram` are mutually inverse between the diagrams
with `d` cells and `PartIdx (Fin (max d 1)) d` (`partDiagram_baseIdx`, `card_partDiagram` and
`HJO.Mac.partDiagram_injective`), so the family `(P_μ)_{|μ| = d}` **is** the image of the basis
`HJO.Mac.exists_basis_macPpoly` of `𝒮_{n_d, d}` under the inverse of the linear equivalence
`HJO.Sym.restrictAlphabetEquiv`. Spanning is then transport along a bijection, as in the
proof of `HJO.Standing.exists_basis_macHtilde`.

`macPfun_partDiagram` is where the one piece of dependent-type bookkeeping happens: `baseAlphabet μ`
is `Fin (max μ.card 1)` and the ambient alphabet is `Fin (max d 1)`, equal types once `|μ| = d` but
not syntactically so, and the proof substitutes `d := |μ|` rather than transporting anything.

## Spanning, not a basis

Neither statement here claims linear independence: `HJO.Sym.exists_basis_macPfun` and
`HJO.Standing.exists_basis_macHtilde` assert bases and these are their spanning halves. Nothing is
lost on the route to the collinear goal. `HJO.Sym.IsUnnormalisedMacdonaldEigenbasis` asks only for
spanning, and `HJO.Sym.linearIndependent_of_dop_zero` recovers independence for `H̃` from
`HJO.Standing.dop_zero_smul_macHtilde_param` and nonvanishing --- which is why that clause was
weakened in the first place.

## Where genericity is spent, and the degenerate corners

`AlgebraicIndependent ℤ ![(q : K), u]` is carried because `macPfun` is a function of it. Beyond
that, the passage from the `P_μ` to the `H̃_μ` spends exactly the invertibility of the two
normalisations, and **both fail at a degenerate corner**:

* `u = 1`, and more generally `u` a root of unity: `γ_μ = 0` for `μ` a single row
  (`HJO.Sym.normalisingProduct_ne_zero` is what excludes it), so `H̃_μ = 0` and the family spans
  nothing. This is the corner at which `HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param` is
  false as well.
* `u` a root of unity again, from the other side: the scalar `(1 - u^{-k})^{-1}` of `𝒴` vanishes,
  so `𝒴` is not injective and `exists_mem_plethDivide_coeffSubst_eq` fails. Hence `hu1`.
* `u = 0`: `u^{n(μ)} = 0` for `μ` with a second row, so again `H̃_μ = 0`. Hence `hu0`.

So `hspan` is **false** without `hu0` and `hu1`, and the witnesses are single rows and single
columns; all three hypotheses hold at the standing field
(`HJO.Standing.paramU_ne_zero`, `HJO.Standing.paramU_pow_succ_ne_one`). `hυυ` is the involutivity
of `υ`, which is what makes `ȷ` bijective; it is `HJO.Ascent.paramUInvHom_involutive` at the
standing field.

## References

Builds on the lemmas `HJO.Sym.exists_basis_macPfun`, `HJO.Sym.exists_basis_lambdaComp_macPfun`,
`HJO.Mac.exists_basis_macPpoly`, `HJO.Sym.restrictAlphabetComp_bijective`,
`HJO.Sym.normalisingProduct_ne_zero` and `HJO.Standing.exists_basis_macHtilde`, and the definitions
`HJO.Sym.macPfun`, `HJO.Sym.macJfun`, `HJO.Ascent.paramUInvLambda`, `HJO.Sym.plethDivide`,
`HJO.Sym.macHtilde` and `HJO.Sym.IsMacdonaldEigenbasis`.
-/

@[expose] public section

open MvPolynomial HJO.Mac

namespace HJO.Sym

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

/-! ### Macdonald's symmetric functions of a given degree, in one alphabet -/

/-- The bookkeeping of `macPfun_partDiagram`, with the degree generalised so that it can be
substituted. The hypothesis `hm : |μ| = m` is what makes `Fin (max m 1)` the base alphabet of `μ`,
and substituting it is the whole proof: `ν` is then an index with `partDiagram ν = μ`, hence
`HJO.Mac.baseIdx μ` by `HJO.Mac.partDiagram_injective`, and both sides are the definition of
`HJO.Sym.macPfun`. -/
private theorem macPfun_eq_of_card_eq (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : YoungDiagram) (m : ℕ) (hm : μ.card = m)
    (hd : m ≤ Fintype.card (Fin (max m 1))) (ν : PartIdx (Fin (max m 1)) m)
    (hν : partDiagram (Fin (max m 1)) ν = μ) :
    (((restrictAlphabetEquiv (Fin (max m 1)) K hd).symm (macPpoly hqu ν) :
      LambdaComp K m) : Lambda K) = macPfun hqu μ := by
  subst hm
  have hνb : ν = baseIdx μ := partDiagram_injective (hν.trans (partDiagram_baseIdx μ).symm)
  subst hνb
  rfl

/-- **`P_μ` is the preimage of `P_μ[X_{n_d}]`, read at an index rather than at a diagram.** For
`ν` an index of the monomial symmetric basis of `𝒮_{n_d, d}` with `n_d = max(d, 1)`, the element
`P_{partDiagram ν}` of `Λ_d` is the preimage of `P_ν[X_{n_d}]` under `res_{n_d}`.

This is `HJO.Sym.macPfun` with its two indexings identified. It is the only step that has to know
that `HJO.Mac.baseAlphabet` depends on `μ` through `|μ|` alone, and it is what lets the basis
`HJO.Mac.exists_basis_macPpoly` be transported in one move. -/
theorem macPfun_partDiagram (hqu : AlgebraicIndependent ℤ ![(q : K), u]) {d : ℕ}
    (hd : d ≤ Fintype.card (Fin (max d 1))) (ν : PartIdx (Fin (max d 1)) d) :
    macPfun hqu (partDiagram (Fin (max d 1)) ν)
      = (((restrictAlphabetEquiv (Fin (max d 1)) K hd).symm (macPpoly hqu ν) :
          LambdaComp K d) : Lambda K) :=
  (macPfun_eq_of_card_eq hqu _ d (card_partDiagram ν) hd ν rfl).symm

/-- **A graded piece is spanned by Macdonald's symmetric functions.** Every `f ∈ Λ_d` is a
`𝕜`-combination of the `P_μ`.

The `P_μ[X_{n_d}]` are a basis of `𝒮_{n_d, d}` (`HJO.Mac.exists_basis_macPpoly`,
`HJO.Mac.exists_basis_macPpoly`) and `res_{n_d}` carries `Λ_d` isomorphically onto `𝒮_{n_d, d}`
(`HJO.Sym.restrictAlphabetEquiv`, `HJO.Sym.restrictAlphabetComp_bijective`), so the preimages of
that basis are a basis of `Λ_d`; `macPfun_partDiagram` says they are `P_μ`. This is
`HJO.Sym.exists_basis_lambdaComp_macPfun` without its appeal to
`HJO.Mac.restrictAlphabet_macPfun_partDiagram`. -/
theorem lambdaComp_le_span_macPfun (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (d : ℕ) :
    LambdaComp K d ≤ Submodule.span K (Set.range (macPfun hqu)) := by
  intro f hf
  have hd : d ≤ Fintype.card (Fin (max d 1)) := by
    rw [Fintype.card_fin]; exact le_max_left _ _
  obtain ⟨B, hB⟩ := exists_basis_macPpoly (σ := Fin (max d 1)) (K := K) (q := q) (u := u)
    (d := d) hqu
  set B' := B.map (restrictAlphabetEquiv (Fin (max d 1)) K hd).symm with hB'
  have hmem : f ∈ Submodule.map (LambdaComp K d).subtype
      (Submodule.span K (Set.range B')) := ⟨⟨f, hf⟩, by rw [B'.span_eq]; trivial, rfl⟩
  rw [Submodule.map_span] at hmem
  refine Submodule.span_le.mpr ?_ hmem
  rintro g ⟨y, ⟨ν, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨partDiagram (Fin (max d 1)) ν, ?_⟩
  rw [macPfun_partDiagram hqu hd ν, Submodule.subtype_apply, hB', Module.Basis.map_apply, hB]

/-- **Macdonald's symmetric functions span `Λ`**: the spanning half of
`HJO.Sym.exists_basis_macPfun`. Every symmetric function is the sum of its graded components
(`HJO.Sym.sum_weightedHomogeneousComponent_range`; compare
`HJO.Sym.lambdaComp_isInternal`), and each component is in the span by
`lambdaComp_le_span_macPfun`. -/
theorem span_range_macPfun_eq_top (hqu : AlgebraicIndependent ℤ ![(q : K), u]) :
    Submodule.span K (Set.range (macPfun hqu)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun f => ?_
  rw [← sum_weightedHomogeneousComponent_range f]
  exact Submodule.sum_mem _ fun N _ =>
    lambdaComp_le_span_macPfun hqu N (weightedHomogeneousComponent_mem _ f N)

/-! ### The two normalisations are invertible on a graded piece -/

omit [Algebra ℚ K] in
/-- A diagonal substitution with every scalar `1` is the identity: both sides are `𝕜`-algebra
endomorphisms of `Λ` fixing every generator. -/
theorem diagScale_one_eq_self (f : Lambda K) : diagScale (fun _ => (1 : K)) f = f := by
  have h : (diagScale (fun _ => (1 : K)) : Lambda K →ₐ[K] Lambda K) = AlgHom.id K _ :=
    MvPolynomial.algHom_ext fun i => by
      rw [diagScale_X, MvPolynomial.C_1, one_mul, AlgHom.id_apply]
  exact AlgHom.congr_fun h f

omit [Algebra ℚ K] in
/-- The substitution of the coefficients at the identity is the identity. -/
theorem coeffSubst_id (f : Lambda K) : coeffSubst (RingHom.id K) f = f :=
  MvPolynomial.map_id f

omit [Algebra ℚ K] in
/-- **`𝒴 ∘ ȷ` is surjective on a graded piece.** For `υ` an involution and `u` not a root of unity,
every `z ∈ Λ_d` is `𝒴(ȷ(x))` for some `x ∈ Λ_d`.

Both factors are inverted explicitly, as in the proof of `HJO.Standing.exists_basis_macHtilde`: the
inverse of `ȷ` is `ȷ` itself, `υ` being an involution, and the inverse of `𝒴` is the diagonal
substitution with the reciprocal scalars `1 - u^{-k}`, which is where `hu1` is spent --- at a root
of unity the scalar of `𝒴` at `p_k` vanishes and `𝒴` is not injective, let alone surjective. Both
substitutions respect the grading (`HJO.Sym.diagScale_mem_lambdaComp`,
`HJO.Sym.coeffSubst_mem_lambdaComp`), so the preimage stays in `Λ_d`. -/
theorem exists_mem_plethDivide_coeffSubst_eq {υ : K →+* K} (hu1 : ∀ k : ℕ, u ^ (k + 1) ≠ 1)
    (hυυ : ∀ c : K, υ (υ c) = c) {d : ℕ} {z : Lambda K} (hz : z ∈ LambdaComp K d) :
    ∃ x ∈ LambdaComp K d, plethDivide u (coeffSubst υ x) = z := by
  have hne : ∀ i : ℕ, (1 : K) - u⁻¹ ^ (i + 1) ≠ 0 := by
    intro i hc
    refine hu1 i ?_
    rw [inv_pow, sub_eq_zero, eq_comm, inv_eq_one] at hc
    exact hc
  refine ⟨coeffSubst υ (diagScale (fun i => 1 - u⁻¹ ^ (i + 1)) z),
    coeffSubst_mem_lambdaComp _ (diagScale_mem_lambdaComp _ hz), ?_⟩
  rw [coeffSubst_coeffSubst, show υ.comp υ = RingHom.id K from RingHom.ext hυυ, coeffSubst_id,
    plethDivide, diagScale_diagScale,
    show (fun i => (1 - u⁻¹ ^ (i + 1))⁻¹ * (1 - u⁻¹ ^ (i + 1))) = fun _ => (1 : K) from
      funext fun i => inv_mul_cancel₀ (hne i)]
  exact diagScale_one_eq_self z

/-! ### The modified Macdonald family spans -/

/-- **`𝒴 ∘ ȷ` carries the span of the `P_μ` into the span of the `H̃_μ`.** `H̃_μ` is
`u^{n(μ)} υ(γ_μ)` times `𝒴(ȷ(P_μ))` (`HJO.Sym.macHtilde_eq_smul`) and that scalar is nonzero, so
each `𝒴(ȷ(P_μ))` is a multiple of `H̃_μ`; the composite is additive and `υ`-semilinear
(`HJO.Sym.coeffSubst_smul`, `𝒴` being `𝕜`-linear), which is enough to carry a `𝕜`-span to a
`𝕜`-span since `υ` is surjective onto the scalars it produces.

This is where `HJO.Sym.normalisingProduct_ne_zero` and `u ≠ 0` are spent:
at `u = 1` the scalar vanishes for every nonempty `μ` and the conclusion is false. -/
theorem plethDivide_coeffSubst_mem_span_macHtilde {υ : K →+* K} (hu0 : u ≠ 0)
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) {x : Lambda K}
    (hx : x ∈ Submodule.span K (Set.range (macPfun hqu))) :
    plethDivide u (coeffSubst υ x) ∈ Submodule.span K (Set.range (macHtilde υ hqu)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨μ, rfl⟩ := hy
      have hA : u ^ rowOffsetSum μ * υ (normalisingProduct (q : K) u μ) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hu0) fun h =>
          normalisingProduct_ne_zero hqu μ (υ.injective (by rw [h, map_zero]))
      have hval : plethDivide u (coeffSubst υ (macPfun hqu μ))
          = (u ^ rowOffsetSum μ * υ (normalisingProduct (q : K) u μ))⁻¹ • macHtilde υ hqu μ := by
        rw [macHtilde_eq_smul, smul_smul, inv_mul_cancel₀ hA, one_smul]
      rw [hval]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, rfl⟩)
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add, map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [coeffSubst_smul, map_smul]; exact Submodule.smul_mem _ _ hy

/-- **The modified Macdonald polynomials span `Λ`**: the spanning half of
`HJO.Standing.exists_basis_macHtilde`, and the hypothesis `hspan` of
`HJO.Sym.hasUnnormalisedMacdonaldEigenbasis_macHtilde`.

Every `z ∈ Λ_d` is `𝒴(ȷ(x))` for some `x ∈ Λ_d` (`exists_mem_plethDivide_coeffSubst_eq`), that `x`
is in the span of the `P_μ` (`lambdaComp_le_span_macPfun`), and `𝒴 ∘ ȷ` carries that span into the
span of the `H̃_μ` (`plethDivide_coeffSubst_mem_span_macHtilde`). The graded pieces exhaust `Λ`.

The three hypotheses on the parameters are not decoration: `H̃_μ = 0` for a single-row `μ` at
`u = 1`, for a single-column `μ` at `u = 0`, and `𝒴` is not surjective at any root of unity. -/
theorem span_range_macHtilde_eq_top {υ : K →+* K} (hu0 : u ≠ 0) (hu1 : ∀ k : ℕ, u ^ (k + 1) ≠ 1)
    (hυυ : ∀ c : K, υ (υ c) = c) (hqu : AlgebraicIndependent ℤ ![(q : K), u]) :
    Submodule.span K (Set.range (macHtilde υ hqu)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  rw [← sum_weightedHomogeneousComponent_range y]
  refine Submodule.sum_mem _ fun N _ => ?_
  obtain ⟨x, hx, hxz⟩ := exists_mem_plethDivide_coeffSubst_eq (u := u) (υ := υ) hu1 hυυ
    (weightedHomogeneousComponent_mem (fun i => i + 1) y N)
  rw [← hxz]
  exact plethDivide_coeffSubst_mem_span_macHtilde hu0 hqu
    (lambdaComp_le_span_macPfun hqu N hx)

end HJO.Sym

/-! ### The same at the standing field -/

namespace HJO.Standing

open HJO.Ascent HJO.Sym

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- **The modified Macdonald polynomials span `Λ` at the standing field**, in exactly the shape
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param` asks for. The three hypotheses of
`HJO.Sym.span_range_macHtilde_eq_top` are theorems here: `u ≠ 0` and `u^{k+1} ≠ 1` come from
`HJO/Macdonald/StandingFacts.lean` and the involutivity of `υ` from
`HJO.Ascent.paramUInvHom_involutive`. -/
theorem span_range_macHtilde_param_eq_top :
    Submodule.span K (Set.range (macHtilde (paramUInvHom K)
      (algebraicIndependent_paramQUnit K))) = ⊤ :=
  span_range_macHtilde_eq_top (paramU_ne_zero K) (paramU_pow_succ_ne_one K)
    (paramUInvHom_involutive K) (algebraicIndependent_paramQUnit K)

/-- **The first residual hypothesis of the collinear goal, now resting on two statements.**
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param` with `hspan` discharged: what
remains is `HJO.Standing.dop_zero_smul_macHtilde_param` (`hdop`, Garsia--Haiman--Tesler's
Theorem 1.2 (1.11) a) and `HJO.Sym.coeffSubst_macPfun` (`hPι`, the invariance of `P_μ` under
inverting both parameters).

Together with `HJO.Sym.HasPieriEigenfamily` ---
`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param` --- those two are the whole of what this
reduction of the collinear side asks for. -/
theorem hasUnnormalisedMacdonaldEigenbasis_macHtilde_dop_param
    (hdop : ∀ μ : YoungDiagram,
      Dop (paramQ K) (paramU K) 0
          (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ)
        = -(HJO.Sym.paramProduct (paramQ K) (paramU K) * cellSum (paramQ K) (paramU K) μ - 1) •
            macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ)
    (hPι : ∀ μ : YoungDiagram,
      coeffSubst (paramQUInvHom K) (macPfun (algebraicIndependent_paramQUnit K) μ)
        = macPfun (algebraicIndependent_paramQUnit K) μ) :
    HasUnnormalisedMacdonaldEigenbasis (paramQUInvHom K) (paramQ K) (paramU K) :=
  hasUnnormalisedMacdonaldEigenbasis_macHtilde_param K (span_range_macHtilde_param_eq_top K)
    hdop hPι

end HJO.Standing
