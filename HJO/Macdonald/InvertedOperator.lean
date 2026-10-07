/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.DopCommute
public meta import HJO.Attr

/-! # The inverted Macdonald operator, and the parameter inversion of the symmetric functions

Two objects of Macdonald's chapter carrying the inversion `ι` of both parameters of `𝕜 = ℚ(q, u)`:
one on the rational function field in a finite alphabet, one on the symmetric functions.

`\widehat D^{(n)}_1 := \widehat\iota_n ∘ D^{(n)}_1 ∘ \widehat\iota_n` is Macdonald's operator
conjugated by the parameter inversion of the alphabet, a map of `𝕜(x_1,…,x_n)` to itself. It is
`𝕜`-linear although `\widehat\iota_n` is not: for `c ∈ 𝕜` the two applications of `\widehat\iota_n`
contribute `ι(c)` and then `ι(ι(c)) = c`. Being a conjugate by an involution it also intertwines,
`\widehat\iota_n ∘ \widehat D^{(n)}_1 = D^{(n)}_1 ∘ \widehat\iota_n`, which is the form the
uniqueness arguments for Macdonald's polynomials use.

`ς` is the ring endomorphism of `Λ` whose restriction to `𝕜` is `ι` and which fixes `p_k` for every
`k ≥ 1`; the sources write `ς(F)` as `F[X; 1/q, 1/u]`. It is not `𝕜`-linear: a ring endomorphism
restricting to `ι` on `𝕜` satisfies `ς(cF) = ι(c)ς(F)` instead. Since `Λ` is a polynomial ring over
`𝕜` on the `p_k`, prescribing the values on `𝕜` and on the generators determines exactly one such
endomorphism. The inversion `↓` of Garsia--Haiman--Tesler has the same restriction to `𝕜` and
differs from `ς` on the generators by the sign `(-1)^{k-1}`.

## Main definitions

* `HJO.Mac.macOpInv`: `\widehat D^{(n)}_1`, as a `𝕜`-linear map of `𝕜(x_1,…,x_n)`.
* `HJO.Sym.paramQUInvLambda`: `ς`.

## Main results

* `HJO.Mac.paramInvFrac_macOpInv`: the intertwining
  `\widehat\iota_n ∘ \widehat D^{(n)}_1 = D^{(n)}_1 ∘ \widehat\iota_n`.
* `HJO.Mac.macOpInv_eq_macOp`: `\widehat D^{(n)}_1` is Macdonald's operator at the inverted
  parameters, and `HJO.Mac.algebraMap_macOpCompInv` identifies its restriction to the graded piece
  `𝒮_{n,d}` with `HJO.Mac.macOpCompInv`.
* `HJO.Sym.paramQUInvLambda_C` and `HJO.Sym.paramQUInvLambda_powerSum`: the two defining clauses
  of `ς`; `HJO.Sym.paramQUInvLambda_smul` is the semilinearity that replaces `𝕜`-linearity, and
  `HJO.Sym.paramQUInvLambda_paramQUInvLambda` says `ς` is an involution.
* `HJO.Sym.inversion_powerSum_eq_paramQUInvLambda`: `↓` and `ς` differ on `p_k` by `(-1)^{k-1}`.

## Implementation notes

The coefficient inversion of `\widehat D^{(n)}_1` is carried as a bare ring endomorphism `ι`
together with `ι ∘ ι = id`, as the rest of this library carries it, rather than as the specific
automorphism of `ℚ(q, u)`; instantiating at `HJO.Sym.paramQUInvHom` recovers the operator with both
parameters inverted. The involutivity is what makes the conjugate `𝕜`-linear, so it is a hypothesis
of the definition rather than of a later lemma, and the definition is a `LinearMap` rather than a
bare function for the same reason.

The `n ≥ 1` is not imposed: at the empty alphabet `D^{(n)}_1` is `0`, as `HJO.Mac.macOp`
records, and so is its conjugate.

`ς` is `HJO.Sym.coeffSubst` at `ι`, that is `MvPolynomial.map ι`; acting on the coefficients and
fixing every generator is exactly what that map does, so the uniqueness appealed to
needs no separate argument. This is how `Θ` (`HJO.Ascent.dualitySwap`) and `ȷ`
(`HJO.Ascent.paramUInvLambda`) are named in `HJO.Macdonald.Duality`, and `ς` is the third of the
family.

## References

This file formalises Definitions `HJO.Mac.macOpInv` and
`HJO.Sym.paramQUInvLambda`. The operator is Macdonald's `D^1_n` conjugated as in A. M. Garsia, M.
Haiman and G. Tesler, *Explicit plethystic formulas for Macdonald (q,t)-Kostka coefficients*, Sém.
Lothar. Combin. **42** (1999), B42m, whose `t` is written `u` here.
-/

@[expose] public section

namespace HJO.Mac

/-! ### The inverted Macdonald operator -/

section DopInv

open MvPolynomial

variable {σ K : Type*} [Field K] [LinearOrder σ] [Fintype σ]

omit [LinearOrder σ] [Fintype σ] in
/-- **`\widehat\iota_n` twists the scalars by `ι` instead of fixing them**: it is `ι`-semilinear on
`𝕜(x_1,…,x_n)`, being a ring homomorphism whose restriction to `𝕜` is `ι`. -/
theorem paramInvFrac_smul (ι : K ≃+* K) (c : K) (f : FractionRing (MvPolynomial σ K)) :
    paramInvFrac ι (c • f) = ι c • paramInvFrac ι f := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul,
    IsScalarTower.algebraMap_apply K (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)),
    IsScalarTower.algebraMap_apply K (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)),
    paramInvFrac_algebraMap]
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.map_C, RingHom.coe_coe]

/-- **The inverted Macdonald operator**:
`\widehat D^{(n)}_1 := \widehat\iota_n ∘ D^{(n)}_1 ∘ \widehat\iota_n`, a map of the rational
function field `𝕜(x_1,…,x_n)` to itself.

It is `𝕜`-linear although `\widehat\iota_n` is not: for `c ∈ 𝕜` the inner application contributes
`ι(c)` and the outer one `ι(ι(c)) = c`, so the two twists cancel. -/
@[hjo "def_mac2_dop_inv"]
noncomputable def macOpInv {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c) (q : Kˣ) (u : K) :
    FractionRing (MvPolynomial σ K) →ₗ[K] FractionRing (MvPolynomial σ K) where
  toFun f := paramInvFrac (ringEquivOfInvolutive hιι)
    (macOp q u (paramInvFrac (ringEquivOfInvolutive hιι) f))
  map_add' f g := by rw [map_add, map_add, map_add]
  map_smul' c f := by
    rw [RingHom.id_apply, paramInvFrac_smul, map_smul, paramInvFrac_smul,
      show ringEquivOfInvolutive hιι (ringEquivOfInvolutive hιι c) = c from hιι c]

/-- **The inverted Macdonald operator is the conjugate of Macdonald's**: its defining property. -/
@[hjo "def_mac2_dop_inv"]
theorem macOpInv_apply {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c) (q : Kˣ) (u : K)
    (f : FractionRing (MvPolynomial σ K)) :
    macOpInv hιι q u f = paramInvFrac (ringEquivOfInvolutive hιι)
      (macOp q u (paramInvFrac (ringEquivOfInvolutive hιι) f)) := rfl

/-- **The inverted operator intertwines with Macdonald's**:
`\widehat\iota_n ∘ \widehat D^{(n)}_1 = D^{(n)}_1 ∘ \widehat\iota_n`, the outer `\widehat\iota_n` of
the conjugate being cancelled by the involutivity. -/
@[hjo "def_mac2_dop_inv"]
theorem paramInvFrac_macOpInv {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c) (q : Kˣ) (u : K)
    (f : FractionRing (MvPolynomial σ K)) :
    paramInvFrac (ringEquivOfInvolutive hιι) (macOpInv hιι q u f)
      = macOp q u (paramInvFrac (ringEquivOfInvolutive hιι) f) :=
  paramInvFrac_paramInvFrac hιι _

/-- **The inverted operator is Macdonald's operator at the inverted parameters**: this is
`HJO.Mac.paramInvFrac_macCoeff`, read on the named operator. -/
theorem macOpInv_eq_macOp {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c) (q : Kˣ) (u : K)
    (f : FractionRing (MvPolynomial σ K)) :
    macOpInv hιι q u f = macOp (Units.map (ι : K →* K) q) (ι u) f :=
  paramInvFrac_macOp hιι q u f

variable [Algebra ℚ K]

/-- **The graded inverted operator is the restriction of the named one**: `HJO.Mac.macOpCompInv`,
the conjugate read on `𝒮_{n,d}`, agrees with `\widehat D^{(n)}_1` inside the rational function
field. -/
theorem algebraMap_macOpCompInv {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c) (q : Kˣ) (u : K) (d : ℕ)
    (v : symmetricHomogeneousSubmodule σ K d) :
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
        ((macOpCompInv ι q u d v : MvPolynomial σ K))
      = macOpInv hιι q u (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          (v : MvPolynomial σ K)) := by
  rw [macOpInv_apply, macOpCompInv, paramInvFrac_algebraMap, coe_ringEquivOfInvolutive,
    ← coe_paramInvComp, ← algebraMap_macOpComp, paramInvFrac_algebraMap,
    coe_ringEquivOfInvolutive, ← coe_paramInvComp]

end DopInv

end HJO.Mac

namespace HJO.Sym

/-! ### The parameter inversion of the symmetric functions -/

section ParamSub

open HJO.Ascent

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- **The parameter inversion of the symmetric functions.** `ς`, the ring
endomorphism of `Λ` whose restriction to `𝕜` is `ι` and which fixes `p_k` for every `k ≥ 1`; the
sources write `ς(F)` as `F[X; 1/q, 1/u]`.

It is `HJO.Sym.coeffSubst` at `ι`, as `Θ` and `ȷ` are at their own automorphisms of `𝕜`: acting on
the coefficients and fixing every generator is what `MvPolynomial.map` does, so the endomorphism so
characterised needs no separate construction. It is not `𝕜`-linear but satisfies
`ς(cF) = ι(c)ς(F)`, which is `paramQUInvLambda_smul`. -/
@[hjo "def_mac_param_sub"]
noncomputable def paramQUInvLambda : Lambda K →+* Lambda K := coeffSubst (paramQUInvHom K)

/-- **The restriction of `ς` to `𝕜` is `ι`**: the first defining clause. -/
@[hjo "def_mac_param_sub", simp]
theorem paramQUInvLambda_C (c : K) :
    paramQUInvLambda K (MvPolynomial.C c) = MvPolynomial.C (paramQUInvHom K c) :=
  coeffSubst_C _ c

/-- **`ς` fixes every power sum**: the second defining clause. -/
@[hjo "def_mac_param_sub", simp]
theorem paramQUInvLambda_powerSum (k : ℕ) :
    paramQUInvLambda K (powerSum K k) = powerSum K k :=
  coeffSubst_powerSum _ k

/-- `ς` twists the scalars by `ι` rather than fixing them, which is what replaces `𝕜`-linearity. -/
theorem paramQUInvLambda_smul (c : K) (f : Lambda K) :
    paramQUInvLambda K (c • f) = paramQUInvHom K c • paramQUInvLambda K f :=
  coeffSubst_smul _ c f

/-- **`ς` is an involution**, `ι` being one: it fixes every generator and inverts the coefficients
twice. -/
theorem paramQUInvLambda_paramQUInvLambda (f : Lambda K) :
    paramQUInvLambda K (paramQUInvLambda K f) = f := by
  have h : (paramQUInvHom K).comp (paramQUInvHom K) = RingHom.id K :=
    RingHom.ext fun c => paramQUInvHom_involutive K c
  rw [paramQUInvLambda, coeffSubst_coeffSubst, h]
  exact MvPolynomial.map_id f

/-- **`ς` respects the grading**: applying `ι` to each coefficient cannot create a monomial. -/
theorem paramQUInvLambda_mem_lambdaComp {d : ℕ} {f : Lambda K} (hf : f ∈ LambdaComp K d) :
    paramQUInvLambda K f ∈ LambdaComp K d :=
  coeffSubst_mem_lambdaComp _ hf

/-- **`↓` and `ς` differ on the power sums by the sign `(-1)^{k-1}`**, and agree on `𝕜` by
`inversion_C` and `paramQUInvLambda_C`: this is the comparison between the
inversion of Garsia--Haiman--Tesler and the parameter substitution. -/
theorem inversion_powerSum_eq_paramQUInvLambda {k : ℕ} (hk : 0 < k) :
    inversion (paramQUInvHom K) (powerSum K k)
      = (-1 : Lambda K) ^ (k - 1) * paramQUInvLambda K (powerSum K k) := by
  rw [inversion_powerSum _ hk, paramQUInvLambda_powerSum]

end ParamSub

end HJO.Sym
