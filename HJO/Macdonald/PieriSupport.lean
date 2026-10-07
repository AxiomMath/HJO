/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.Htilde
public meta import HJO.Attr

/-! # The support of the one-cell Pieri expansion

`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`: `e₁ H̃_ν` lies in the `𝕜`-span of the
`H̃_μ` with `μ` covering `ν`. That statement is the second residual hypothesis of the collinear
goal, `HJO.Sym.HasPieriEigenfamily`, and this file reduces it to the same statement for Macdonald's
own `P_μ` --- `HJO.Standing.hasPfunPieriSupport_param`, carried here as the named residual
`HJO.Sym.HasPfunPieriSupport`.

## The transport, and why it is cheap

`H̃_μ = u^{n(μ)} 𝒴(ȷ(J_μ))` and `J_μ = γ_μ P_μ`, so `H̃_μ` is one nonzero scalar times `Φ(P_μ)`,
where `Φ := 𝒴 ∘ ȷ` (`HJO.Sym.macHtilde_eq_smul`). Two facts then move the support across:

* `Φ(e₁)` is a nonzero scalar times `e₁`, namely `(1 - u^{-1})^{-1} e₁`
  (`HJO.Sym.plethDivide_coeffSubst_elemSymm_one`). The Step 1 arranges the scalar away
  by applying `Φ` to `(1-u)e₁` instead; nothing needs that normalisation, only that the scalar is
  invertible.
* `Φ` carries the span of a set into the span of its image
  (`HJO.Sym.plethDivide_coeffSubst_mem_span`). It is *not* `𝕜`-linear --- `ȷ` twists a scalar by
  `υ` --- but `υ(c)` is again a scalar, which is all a span membership needs. That is
  Steps 2 and 3 of the proof, with the coefficients
  `a_μ = (1-u)γ_ν γ_μ^{-1} c_μ` never written down.

## Main definitions

* `HJO.Sym.HasPfunPieriSupport`: `HJO.Standing.hasPfunPieriSupport_param` as a `Prop`, the one
  residual this file leaves.

## Main results

* `HJO.Sym.elemSymm_one_mul_macHtilde_mem_span`:
  `HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param` from `HJO.Sym.HasPfunPieriSupport`.
* `HJO.Sym.hasPieriEigenfamily_macHtilde`, and its standing-field form
  `HJO.Standing.hasPieriEigenfamily_macHtilde_param`: the second residual hypothesis of the
  collinear goal reduced to `HJO.Standing.hasPfunPieriSupport_param` together with
  `HJO.Standing.dop_zero_smul_macHtilde_param`.

## Where genericity is spent

`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param` is **false** without it. At `u = 1`:
`H̃_∅ = 1`, while `γ_{(1)} = 1 - u` vanishes, so `H̃_{(1)} = 0` and the claim at `ν = ∅` reads
`e₁ ∈ span{0}`, which is false. The hypotheses below that rule this out are `u ≠ 0`, `u ≠ 1` and
`∀ k, u^{k+1} ≠ 1`, each a consequence of `AlgebraicIndependent ℤ ![q, u]`
(`HJO.Standing.u_ne_zero`, `HJO.Standing.u_pow_succ_ne_one`); `u ≠ 1` is spent on the invertibility
of the scalar of `Φ(e₁)` and `u^{k+1} ≠ 1` on the nonvanishing of `H̃_μ`
(`HJO.Sym.macHtilde_ne_zero`). The scalar `u^{n(μ)}υ(γ_μ)` relating `H̃_μ` to `Φ(P_μ)` needs
`γ_μ ≠ 0` (`HJO.Sym.normalisingProduct_ne_zero`), which is the `u = 1` failure itself.
-/

@[expose] public section

namespace HJO.Sym

/-! ### Rescaling a family does not move the span of its image -/

section SpanImage

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] {ι : Type*}

/-- **Rescaling each member of a family by a nonzero scalar does not change the span of its image.**
This is what makes the support statement the same question for `H̃_μ` and for `Φ(P_μ)`: the two
differ by one nonzero scalar per index. -/
theorem span_image_smul_eq (a : ι → K) (f : ι → M) (S : Set ι) (ha : ∀ i ∈ S, a i ≠ 0) :
    Submodule.span K ((fun i => a i • f i) '' S) = Submodule.span K (f '' S) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro x ⟨i, hi, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rintro x ⟨i, hi, rfl⟩
    have hfi : f i = (a i)⁻¹ • (a i • f i) := by
      rw [smul_smul, inv_mul_cancel₀ (ha i hi), one_smul]
    rw [hfi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

end SpanImage

/-! ### The composite of the two substitutions on a span -/

section Substitution

variable {K : Type*} [Field K] [Algebra ℚ K] {u : K}

omit [Algebra ℚ K] in
/-- **`Φ = 𝒴 ∘ ȷ` carries a span into the span of the image.** The composite is a ring
endomorphism of `Λ` but not a `𝕜`-linear one: `ȷ` twists a scalar `c` by `υ`
(`HJO.Sym.coeffSubst_smul`) and `𝒴` fixes it. A span membership survives the twist, `υ(c)` being
again a scalar. -/
theorem plethDivide_coeffSubst_mem_span (υ : K →+* K) {s : Set (Lambda K)} {x : Lambda K}
    (hx : x ∈ Submodule.span K s) :
    plethDivide u (coeffSubst υ x)
      ∈ Submodule.span K ((fun f => plethDivide u (coeffSubst υ f)) '' s) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add, map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [coeffSubst_smul, map_smul]; exact Submodule.smul_mem _ _ hy

omit [Algebra ℚ K] in
/-- **`Φ` carries the span of an indexed family into the span of the image family**: the form the
transport is used in, `plethDivide_coeffSubst_mem_span` composed with `Set.image_image`. -/
theorem plethDivide_coeffSubst_mem_span_image (υ : K →+* K) {ι : Type*} (g : ι → Lambda K)
    (S : Set ι) {x : Lambda K} (hx : x ∈ Submodule.span K (g '' S)) :
    plethDivide u (coeffSubst υ x)
      ∈ Submodule.span K ((fun i => plethDivide u (coeffSubst υ (g i))) '' S) := by
  have h := plethDivide_coeffSubst_mem_span (u := u) υ hx
  rwa [Set.image_image] at h

/-- **`Φ(e₁) = (1 - u^{-1})^{-1} e₁`**: `ȷ` fixes `p₁` and `𝒴` scales it by `(1 - u^{-1})^{-1}`,
and `e₁ = p₁` (`HJO.Sym.elemSymm_one`). The Step 1 reads this as `Φ((1-u)e₁) = e₁`, the same
computation with the scalar cleared. -/
theorem plethDivide_coeffSubst_elemSymm_one (υ : K →+* K) :
    plethDivide u (coeffSubst υ (elemSymm K 1)) = (1 - u⁻¹)⁻¹ • elemSymm K 1 := by
  rw [elemSymm_one, coeffSubst_powerSum, plethDivide_powerSum u le_rfl, pow_one,
    MvPolynomial.smul_eq_C_mul]

end Substitution

/-! ### The residual statement about Macdonald's own symmetric function -/

section Residual

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

/-- **`HJO.Standing.hasPfunPieriSupport_param` as a `Prop`**: `e₁ P_ν` lies in the `𝕜`-span of the
`P_μ` with `μ` covering `ν`.

Nothing about the parameters is asked beyond the genericity already carried by `P` itself: the
statement is Macdonald's, and its proof (an induction removing the first column,
resting on `HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short`) uses no nonvanishing. -/
def HasPfunPieriSupport (hqu : AlgebraicIndependent ℤ ![(q : K), u]) : Prop :=
  ∀ ν : YoungDiagram, elemSymm K 1 * macPfun hqu ν
    ∈ Submodule.span K (macPfun hqu '' {μ : YoungDiagram | Covers μ ν})

omit [Algebra ℚ K] in
/-- The scalar relating `H̃_μ` to `Φ(P_μ)` is not zero: `u^{n(μ)} ≠ 0` and `γ_μ ≠ 0`
(`HJO.Sym.normalisingProduct_ne_zero`), and `υ` is injective, a ring endomorphism of a field
being so. -/
theorem macHtilde_scalar_ne_zero {υ : K →+* K} (hu0 : u ≠ 0)
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : YoungDiagram) :
    u ^ rowOffsetSum μ * υ (normalisingProduct (q : K) u μ) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hu0)
    fun h => normalisingProduct_ne_zero hqu μ (υ.injective (by rw [h, map_zero]))

/-- **`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param` from
`HJO.Standing.hasPfunPieriSupport_param`**: `e₁ H̃_ν` lies in the `𝕜`-span of the `H̃_μ` with `μ`
covering `ν`.

The three steps, with its coefficients left implicit: `H̃` is `Φ ∘ P` rescaled by one
nonzero scalar per index (`span_image_smul_eq`), `Φ(e₁)` is `e₁` rescaled
(`plethDivide_coeffSubst_elemSymm_one`), and `Φ` respects spans
(`plethDivide_coeffSubst_mem_span`). -/
theorem elemSymm_one_mul_macHtilde_mem_span {υ : K →+* K} (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (hP : HasPfunPieriSupport hqu)
    (ν : YoungDiagram) :
    elemSymm K 1 * macHtilde υ hqu ν
      ∈ Submodule.span K (macHtilde υ hqu '' {μ : YoungDiagram | Covers μ ν}) := by
  have hu : (1 - u⁻¹) ≠ 0 := sub_ne_zero.mpr fun h => hu1 (inv_eq_one.mp h.symm)
  have hspan : Submodule.span K (macHtilde υ hqu '' {μ : YoungDiagram | Covers μ ν})
      = Submodule.span K ((fun μ => plethDivide u (coeffSubst υ (macPfun hqu μ)))
          '' {μ : YoungDiagram | Covers μ ν}) := by
    rw [show macHtilde υ hqu = fun μ => (u ^ rowOffsetSum μ *
        υ (normalisingProduct (q : K) u μ)) • plethDivide u (coeffSubst υ (macPfun hqu μ)) from
      funext (macHtilde_eq_smul υ hqu)]
    exact span_image_smul_eq _ _ _ fun μ _ => macHtilde_scalar_ne_zero hu0 hqu μ
  -- `e₁ Φ(P_ν)` is `(1 - u^{-1})` times `Φ(e₁ P_ν)`
  have hmul : elemSymm K 1 * plethDivide u (coeffSubst υ (macPfun hqu ν))
      = (1 - u⁻¹) • plethDivide u (coeffSubst υ (elemSymm K 1 * macPfun hqu ν)) := by
    rw [map_mul, map_mul, plethDivide_coeffSubst_elemSymm_one, smul_mul_assoc, smul_smul,
      mul_inv_cancel₀ hu, one_smul]
  rw [hspan, macHtilde_eq_smul υ hqu ν, mul_smul_comm, hmul]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (plethDivide_coeffSubst_mem_span_image υ (macPfun hqu) _ (hP ν)))

/-- **The second residual hypothesis of the collinear goal, reduced to two statements about the
constructed family `H̃`.**

`HJO.Sym.HasPieriEigenfamily` asks for a family of nonzero `D_0`-eigenvectors with covering Pieri
support. `H̃` is that family: the nonvanishing is `HJO.Sym.macHtilde_ne_zero` and the support is
`elemSymm_one_mul_macHtilde_mem_span`, so what remains is

* `hdop`, `HJO.Standing.dop_zero_smul_macHtilde_param`, which the first residual hypothesis needs as
  well (`HJO.Sym.hasUnnormalisedMacdonaldEigenbasis_macHtilde`);
* `hP`, `HJO.Standing.hasPfunPieriSupport_param`.

Neither is weakened, and no clause of `HasPieriEigenfamily` beyond those two is left: the family
need not span, need not be independent, and satisfies no inversion clause. -/
theorem hasPieriEigenfamily_macHtilde {υ : K →+* K} (hu0 : u ≠ 0)
    (hu1 : ∀ k : ℕ, u ^ (k + 1) ≠ 1) (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (hdop : ∀ μ : YoungDiagram, Dop (q : K) u 0 (macHtilde υ hqu μ)
      = -(paramProduct (q : K) u * cellSum (q : K) u μ - 1) • macHtilde υ hqu μ)
    (hP : HasPfunPieriSupport hqu) : HasPieriEigenfamily (q : K) u :=
  ⟨macHtilde υ hqu, fun μ => macHtilde_ne_zero hu0 hu1 hqu μ, hdop,
    fun ν => elemSymm_one_mul_macHtilde_mem_span hu0 (by simpa using hu1 0) hqu hP ν⟩

end Residual

end HJO.Sym

/-! ### The same reduction at the standing field -/

namespace HJO.Standing

open HJO.Ascent HJO.Sym

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- **The second residual hypothesis of the collinear goal at the standing field, reduced to two
unproved statements.**

Together with `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param` this feeds
`HJO.Standing.exists_isMacdonaldConjugator_of_hasPieriEigenfamily_param`, so the collinear side
rests on `HJO.Standing.exists_basis_macHtilde`, `HJO.Standing.dop_zero_smul_macHtilde_param`,
`HJO.Sym.coeffSubst_macPfun` and `HJO.Standing.hasPfunPieriSupport_param` and on nothing else.
Everything about the parameters is discharged here from `HJO/Macdonald/StandingFacts.lean`. -/
theorem hasPieriEigenfamily_macHtilde_param
    (hdop : ∀ μ : YoungDiagram,
      Dop (paramQ K) (paramU K) 0
          (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ)
        = -(HJO.Sym.paramProduct (paramQ K) (paramU K) * cellSum (paramQ K) (paramU K) μ - 1) •
            macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ)
    (hP : HasPfunPieriSupport (q := paramQUnit K) (u := paramU K)
      (algebraicIndependent_paramQUnit K)) :
    HasPieriEigenfamily (paramQ K) (paramU K) :=
  hasPieriEigenfamily_macHtilde (q := paramQUnit K) (u := paramU K) (υ := paramUInvHom K)
    (paramU_ne_zero K) (paramU_pow_succ_ne_one K) (algebraicIndependent_paramQUnit K) hdop hP

end HJO.Standing
