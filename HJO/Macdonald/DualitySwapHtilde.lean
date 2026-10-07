/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.DualityDopZero
public import HJO.Macdonald.DualityFacts
public import HJO.Macdonald.EigenbasisFamily
public import HJO.Macdonald.HtildeBasis
public meta import HJO.Attr

/-! # The exchange carries the modified Macdonald basis to its conjugate, up to a scalar

`HJO.Standing.exists_smul_dualitySwap_macHtilde`: for a partition `μ` there is a nonzero `c ∈ 𝕜`
with `Θ(H̃_μ) = c · H̃_{μ'}`.

## The shape of the argument, and where the work is

The argument transports the basis along `Θ` and then appeals to uniqueness of a `D_0`-eigenbasis.
Every ingredient of that is available elsewhere in the library:

* `HJO.Sym.exists_smul_of_dop_zero_eigenbasis` is the conclusion's
  shape: two families with the same `D_0` eigenvalues, one of them a basis and the other merely
  independent, differ by one nonzero scalar per index.
* `HJO.Standing.linearIndependent_macHtilde_param` and
  `HJO.Standing.span_range_macHtilde_param_eq_top` make `H̃` a basis at the standing field, with no
  hypothesis (`HJO.Standing.exists_basis_macHtilde`).
* `HJO.Standing.dop_zero_smul_macHtilde_param` is the eigenrelation for
  `H̃`, and `HJO.Ascent.dualitySwap_dop_zero` plus
  `HJO.Sym.paramSwapHom_cellSum` push it through `Θ` to get the eigenrelation
  for the transported family. `HJO.Sym.dopZeroEigenvalue` is by definition
  `-(M B_μ - 1)`, so pushing `τ` through the eigenvalue is exactly `τ(M) = M` -- the product
  `(1 - q)(1 - u)` is symmetric -- together with `τ(B_{μ'}) = B_{μ''} = B_μ`.

So the file adds only two things.

**`τ` is an involution** (`HJO.Ascent.paramSwapHom_involutive`). The composite fixes `q` and fixes
`u`, and the standing field is rigid over those two values
(`HJO.Ascent.ringHom_eq_id_of_param_fixed`): this is the same two-line argument that
`paramUInvHom_involutive` and `paramQUInvHom_involutive` are given in
`HJO/Macdonald/ParamInversion.lean`, and it is also the opening step, that `Θ` is
bijective.

**The transported family is independent** (`HJO.Sym.linearIndependent_coeffSubst`). This is the one
new piece of mathematics, and the reason it is not `LinearIndependent.map'` is that `Θ` is NOT
`𝕜`-linear: it is `τ`-semilinear, `Θ(cF) = τ(c)Θ(F)` (`HJO.Sym.coeffSubst_smul`). Reading the
semilinearity backwards is what makes the argument work anyway. If `∑ᵢ cᵢ • Θ(vᵢ) = 0`, apply `Θ`
again -- which is the identity, `Θ` being an involution whenever `τ` is -- to get
`∑ᵢ τ(cᵢ) • vᵢ = 0`; independence of `(vᵢ)` gives `τ(cᵢ) = 0`, and `cᵢ = τ(τ(cᵢ)) = τ(0) = 0`. The
lemma is stated for an arbitrary involutive endomorphism of an arbitrary commutative ring of
coefficients and an arbitrary index type, because nothing else is used.

Re-indexing along conjugation is then free: `μ ↦ μ'` is injective because it is its own inverse
(`YoungDiagram.transpose_transpose`, `HJO.Sym.transpose_transpose`), so
`LinearIndependent.comp` applies.

## Generality

Stated at the standing field `𝕜 = ℚ(q, u)`, and it has to be. `Θ` is a nontrivial ring
endomorphism of the coefficients, which a general field of characteristic zero does not have; and
the nonvanishing of `c` genuinely fails at a degenerate corner, because `H̃_μ` itself vanishes when
`u` is a root of unity (`HJO.Sym.macHtilde_ne_zero` is where that is recorded) and because the cell
sum stops separating partitions at `q = u`, which is what makes the eigenvalue determine the index.
The two facts about `τ` and about coefficient substitution that this file adds carry no genericity:
`HJO.Sym.linearIndependent_coeffSubst` is at an arbitrary commutative ring.
-/

@[expose] public section

namespace HJO.Sym

/-! ### A coefficient substitution at an involution preserves linear independence -/

section CoeffSubstIndep

variable {L : Type*} [CommRing L]

/-- **A coefficient substitution at an involutive endomorphism is its own inverse.** The composite
is the substitution at `φ ∘ φ = id`, which is `MvPolynomial.map_id`. -/
theorem coeffSubst_coeffSubst_self {φ : L →+* L} (hφ : ∀ c, φ (φ c) = c) (f : Lambda L) :
    coeffSubst φ (coeffSubst φ f) = f := by
  rw [coeffSubst_coeffSubst, show φ.comp φ = RingHom.id L from RingHom.ext hφ]
  exact MvPolynomial.map_id f

/-- **A coefficient substitution at an involutive endomorphism carries an independent family to an
independent family.**

The substitution is a ring endomorphism of `Λ` but NOT `L`-linear -- it twists the scalars,
`coeffSubst φ (c • f) = φ(c) • coeffSubst φ f` (`HJO.Sym.coeffSubst_smul`) -- so
`LinearIndependent.map'` does not apply. Reading that twisting backwards is the proof: apply the
substitution to a vanishing combination of the images, which by
`HJO.Sym.coeffSubst_coeffSubst_self` returns a vanishing combination of the originals with the
coefficients twisted, and untwist the conclusion using that `φ` is injective, itself immediate from
involutivity. -/
theorem linearIndependent_coeffSubst {ι : Type*} {φ : L →+* L} (hφ : ∀ c, φ (φ c) = c)
    {v : ι → Lambda L} (hv : LinearIndependent L v) :
    LinearIndependent L fun i => coeffSubst φ (v i) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  have h0 : ∑ j ∈ s, φ (g j) • v j = 0 := by
    have h := congrArg (coeffSubst φ) hg
    rw [map_sum, map_zero] at h
    simpa only [coeffSubst_smul, coeffSubst_coeffSubst_self hφ] using h
  rw [← hφ (g i), hv s (fun j => φ (g j)) h0 i hi, map_zero]

end CoeffSubstIndep

end HJO.Sym

namespace HJO.Ascent

open HJO.Sym

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-! ### The exchange of the two parameters is an involution -/

/-- The exchange of the two parameters, composed with itself, is the identity: it sends `q` to `u`
and back, and `u` to `q` and back, and the standing field is rigid over those two values
(`HJO.Ascent.ringHom_eq_id_of_param_fixed`). -/
theorem paramSwapHom_comp_self : (paramSwapHom K).comp (paramSwapHom K) = RingHom.id K := by
  refine ringHom_eq_id_of_param_fixed ?_ ?_ <;> simp [RingHom.comp_apply]

/-- **The exchange of the two parameters is an involution**, `τ(τ(c)) = c`. This is the
opening step in `HJO.Standing.exists_smul_dualitySwap_macHtilde`, that `Θ` is bijective: the
endomorphism built the same way from `τ` again is a two-sided inverse. -/
theorem paramSwapHom_involutive (c : K) : paramSwapHom K (paramSwapHom K c) = c :=
  RingHom.congr_fun (paramSwapHom_comp_self K) c

/-- **`Θ` is an involution**, hence bijective: it is `HJO.Sym.coeffSubst` at `τ`, and `τ` is an
involution. -/
theorem dualitySwap_dualitySwap (f : Lambda K) : dualitySwap K (dualitySwap K f) = f :=
  coeffSubst_coeffSubst_self (paramSwapHom_involutive K) f

/-- **`Θ` is `τ`-semilinear**, `Θ(cF) = τ(c)Θ(F)`: it is `HJO.Sym.coeffSubst` at `τ`, so this is
`HJO.Sym.coeffSubst_smul`. Recorded here because it is what stops `Θ` from carrying a basis to a
basis by `LinearIndependent.map'`. -/
theorem dualitySwap_smul (c : K) (f : Lambda K) :
    dualitySwap K (c • f) = paramSwapHom K c • dualitySwap K f :=
  coeffSubst_smul (paramSwapHom K) c f

/-! ### The exchange on the eigenvalue of the degree-zero operator -/

/-- **The exchange fixes `M = (1 - q)(1 - u)`**, because the product is symmetric in the two
parameters and `τ` exchanges its two factors. -/
theorem paramSwapHom_paramProduct :
    paramSwapHom K (paramProduct (paramQ K) (paramU K)) = paramProduct (paramQ K) (paramU K) := by
  change paramSwapHom K ((1 - paramQ K) * (1 - paramU K)) = (1 - paramQ K) * (1 - paramU K)
  rw [map_mul, map_sub, map_sub, map_one, paramSwapHom_paramQ, paramSwapHom_paramU, mul_comm]

/-- **The exchange carries the `D_0` eigenvalue of `μ` to that of the conjugate partition**,
`τ(-(M B_μ - 1)) = -(M B_{μ'} - 1)`.

`HJO.Sym.dopZeroEigenvalue` is by definition `-(M B_μ - 1)`, so this is two facts: `τ(M) = M`
(`HJO.Ascent.paramSwapHom_paramProduct`) and `τ(B_μ) = B_{μ'}`
(`HJO.Sym.paramSwapHom_cellSum`). -/
theorem paramSwapHom_dopZeroEigenvalue (μ : YoungDiagram) :
    paramSwapHom K (dopZeroEigenvalue (paramQ K) (paramU K) μ)
      = dopZeroEigenvalue (paramQ K) (paramU K) μ.transpose := by
  simp only [dopZeroEigenvalue]
  rw [map_neg, map_sub, map_one, map_mul, paramSwapHom_paramProduct, paramSwapHom_cellSum]

end HJO.Ascent

/-! ### `τ` as an automorphism of the standing field

The exchange is wanted as an *automorphism*, and `HJO.Ascent.paramSwapHom` is typed as a ring
endomorphism, so `HJO.Sym.paramSwap` is a form that carries the bijectivity. The exact analogue is
already in the library: `HJO.Sym.paramUInv` and `HJO.Sym.paramQUInv` bundle `υ` and `ι` as
`K ≃ₐ[ℚ] K` out of their endomorphisms and their involutivity. So `τ` is bundled the same way. The
`≃ₐ[ℚ]` discharges two of the three required clauses by typing -- it is bijective, and it fixes
`ℚ` -- and the two value lemmas below are the third.
-/

namespace HJO.Sym

open HJO.Ascent

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **The exchange of the two parameters** `τ`: the
automorphism of the standing coefficient field `𝕜 = ℚ(q, u)` over `ℚ` which sends `q` to `u` and `u`
to `q`. `τ(c)` is commonly written `c(u, q)`.

The justification is carried out where the pieces are: the assignment extends to an
endomorphism of `𝕜` because `(u, q)` is algebraically independent
(`HJO.Ascent.algebraicIndependent_param_swap` feeding `HJO.Ascent.paramEmbedding`), and that
endomorphism is an automorphism because its square fixes `q` and `u` and the standing field is rigid
over those two values (`HJO.Ascent.paramSwapHom_involutive`). Bundling those two facts as an
`AlgEquiv` is what makes this declaration an automorphism rather than merely an endomorphism. -/
@[hjo "def_dua_swap_field"]
noncomputable def paramSwap : K ≃ₐ[ℚ] K :=
  AlgEquiv.ofAlgHom (toRatAlgHom (paramSwapHom K)) (toRatAlgHom (paramSwapHom K))
    (AlgHom.ext fun c => paramSwapHom_involutive K c)
    (AlgHom.ext fun c => paramSwapHom_involutive K c)

@[simp]
theorem paramSwap_apply (c : K) : paramSwap K c = paramSwapHom K c := rfl

/-- `τ` sends the dinv parameter to the area parameter. -/
@[simp]
theorem paramSwap_paramQ : paramSwap K (paramQ K) = paramU K := paramSwapHom_paramQ K

/-- `τ` sends the area parameter to the dinv parameter. -/
@[simp]
theorem paramSwap_paramU : paramSwap K (paramU K) = paramQ K := paramSwapHom_paramU K

/-- `τ` fixes `ℚ` pointwise, which for a map of `ℚ`-algebras is `AlgEquiv.commutes`. -/
theorem paramSwap_algebraMap_rat (r : ℚ) :
    paramSwap K (algebraMap ℚ K r) = algebraMap ℚ K r := (paramSwap K).commutes r

/-- **`τ` is an involution**, so the automorphism above is its own inverse. -/
theorem paramSwap_involutive (c : K) : paramSwap K (paramSwap K c) = c :=
  paramSwapHom_involutive K c

end HJO.Sym

namespace HJO.Standing

open HJO.Ascent HJO.Sym

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- Conjugation of partitions is injective, being its own inverse
(`YoungDiagram.transpose_transpose`). This is `HJO.Sym.transpose_transpose` read as
an injectivity, which is what re-indexing a family along conjugation asks for. -/
theorem transpose_injective : Function.Injective YoungDiagram.transpose :=
  Function.Involutive.injective YoungDiagram.transpose_transpose

/-- **The family `μ ↦ Θ(H̃_{μ'})` is `𝕜`-linearly independent.**

Two reductions and one semilinear argument. Re-indexing `H̃` along conjugation keeps it independent,
conjugation being injective (`HJO.Standing.transpose_injective`); and `Θ` is
`HJO.Sym.coeffSubst` at the involution `τ`, so `HJO.Sym.linearIndependent_coeffSubst` applies. It is
NOT an application of `LinearIndependent.map'`: `Θ` is `τ`-semilinear rather than `𝕜`-linear. -/
theorem linearIndependent_dualitySwap_macHtilde_transpose :
    LinearIndependent K fun μ : YoungDiagram =>
      dualitySwap K (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ.transpose) :=
  linearIndependent_coeffSubst (paramSwapHom_involutive K)
    ((linearIndependent_macHtilde_param K).comp YoungDiagram.transpose transpose_injective)

/-- **The family `μ ↦ Θ(H̃_{μ'})` satisfies the same `D_0` eigenrelation as `H̃`.**

`Θ` commutes with `D_0` (`HJO.Ascent.dualitySwap_dop_zero`), so the eigenrelation for `H̃_{μ'}`
(`HJO.Standing.dop_zero_smul_macHtilde_param`) transports, and the `τ`-semilinearity of `Θ` puts
`τ` on the eigenvalue. There `HJO.Ascent.paramSwapHom_dopZeroEigenvalue` sends the eigenvalue of
`μ'` to that of `μ'' = μ`. -/
theorem dop_zero_smul_dualitySwap_macHtilde_transpose (μ : YoungDiagram) :
    Dop (paramQ K) (paramU K) 0
        (dualitySwap K
          (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ.transpose))
      = dopZeroEigenvalue (paramQ K) (paramU K) μ •
          dualitySwap K
            (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ.transpose) := by
  have hsc : paramSwapHom K (dopZeroEigenvalue (paramQ K) (paramU K) μ.transpose)
      = dopZeroEigenvalue (paramQ K) (paramU K) μ := by
    rw [paramSwapHom_dopZeroEigenvalue, YoungDiagram.transpose_transpose]
  have hdop : Dop (paramQ K) (paramU K) 0
      (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ.transpose)
        = dopZeroEigenvalue (paramQ K) (paramU K) μ.transpose •
            macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ.transpose :=
    dop_zero_smul_macHtilde_param K μ.transpose
  rw [← dualitySwap_dop_zero, hdop, dualitySwap_smul, hsc]

/-- **The exchange carries `H̃_μ` to a nonzero multiple of `H̃_{μ'}`.**
There is a nonzero `c ∈ 𝕜` with `Θ(H̃_μ) = c · H̃_{μ'}`.

The proof: `(H̃_μ)` is a `𝕜`-basis of `Λ`
(`HJO.Standing.linearIndependent_macHtilde_param`,
`HJO.Standing.span_range_macHtilde_param_eq_top`) satisfying the `D_0` eigenrelation
(`HJO.Standing.dop_zero_smul_macHtilde_param`); the transported family `μ ↦ Θ(H̃_{μ'})` is
independent and satisfies the same eigenrelation, by the two lemmas above; so
`HJO.Sym.exists_smul_of_dop_zero_eigenbasis` supplies one nonzero
scalar per index. Reading that at `μ'` and using `μ'' = μ` is the statement.

Stated at the standing field, and not over a general field: `Θ` needs a nontrivial endomorphism of
the coefficients to exist at all, and the nonvanishing of `c` fails where `H̃_μ` itself vanishes,
which is at a root of unity. -/
@[hjo "lem_dua_swap_htilde"]
theorem exists_smul_dualitySwap_macHtilde (μ : YoungDiagram) :
    ∃ c : K, c ≠ 0 ∧
      dualitySwap K (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ)
        = c • macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ.transpose := by
  obtain ⟨c, hc0, hc⟩ :=
    exists_smul_of_dop_zero_eigenbasis (algebraicIndependent_param K)
      (linearIndependent_macHtilde_param K) (span_range_macHtilde_param_eq_top K)
      (linearIndependent_dualitySwap_macHtilde_transpose K)
      (fun ν => dop_zero_smul_macHtilde_param K ν)
      (dop_zero_smul_dualitySwap_macHtilde_transpose K) μ.transpose
  rw [YoungDiagram.transpose_transpose] at hc
  exact ⟨c, hc0, hc⟩

end HJO.Standing
