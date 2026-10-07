/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.Duality
public meta import HJO.Attr

/-! # The duality map is the exchange transported along the plethystic substitution

`HJO.Ascent.plethDivide_paramUInvLambda_dualityOmega` -- `𝒴(ȷ(Ω f)) = Θ(𝒴(ȷ(f)))` for every `f ∈ Λ`.

Write `Φ` for `f ↦ 𝒴(ȷ(f))`. Both `Φ ∘ Ω` and `Θ ∘ Φ` are ring endomorphisms of `Λ`, and `Λ` is a
polynomial ring over the coefficients on the power sums, so the statement is
`MvPolynomial.ringHom_ext` at two computations: one on the constants and one on a generator.

## On the constants: a commutation of parameter automorphisms

The two restrictions to `𝕜` are `υ ∘ ι ∘ τ` and `τ ∘ υ`, and they agree. Both send `q` to `u` --
`q ↦ u ↦ u⁻¹ ↦ u` on the left, `q ↦ q ↦ u` on the right -- and both send `u` to `q⁻¹`:
`u ↦ q ↦ q⁻¹ ↦ q⁻¹` on the left, `u ↦ u⁻¹ ↦ q⁻¹` on the right. That is enough because the standing
field is rigid over its two parameters, which is `HJO.Ascent.ringHom_ext_param` in
`HJO/Macdonald/ParamInversion.lean`: `𝕜` is generated as a field over `ℚ` by `q` and `u`, so it is
enough to compare two homomorphisms at those two.

## On a generator: one identity of scalars

`Φ(p_k) = (1 - u^{-k})^{-1} p_k`, so the generator case is

  `υ(-q^k (1-u^k)/(1-q^k)) · (1-u^{-k})^{-1} = τ((1-u^{-k})^{-1})`,

the left side being `-q^k (1-u^{-k})/(1-q^k) · (1-u^{-k})^{-1} = -q^k/(1-q^k)` and the right side
`(1-q^{-k})^{-1} = q^k/(q^k-1)`. The second of those is `HJO.Sym.inv_one_sub_pow_eq` read at `q⁻¹`
rather than at `u`.

Exactly two nonvanishing facts are spent, and both are standing facts about the two indeterminates
rather than hypotheses: `1 - u^{-k} ≠ 0` for the cancellation on the left, which is
`HJO.Standing.paramU_pow_succ_ne_one`, and `q ≠ 0` for the right side, which is
`HJO.Standing.paramQ_ne_zero`. `1 - q^k ≠ 0` is **not** needed -- at `q^k = 1` both sides of the
right-hand identity are `0` in Lean's convention -- so `HJO.Ascent.one_sub_paramQ_pow_ne_zero` is
not used here even though the displayed identity divides by `1 - q^k`.

## Why the statement is made at the standing field

`Ω`, `Θ` and `ȷ` each act on the coefficients through a nontrivial automorphism of `𝕜`, and no such
automorphism exists over a general field of characteristic zero -- over `ℝ` the only ring
endomorphism is the identity. So the general-field reading of this statement is not a weaker true
statement, it is not a statement at all, exactly as for
`HJO.Sym.plethDivide_paramUInvLambda_injective` in `HJO/Macdonald/DualityFacts.lean`. The parameters
being indeterminates is also what supplies the three nonvanishing facts above; at a root of unity of
`q` the scalar of `Ω` has a zero denominator and the generator computation collapses.
-/

@[expose] public section

namespace HJO.Ascent

open HJO.Sym

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-! ### The commutation `υ ∘ ι ∘ τ = τ ∘ υ` of parameter automorphisms -/

/-- **`υ ∘ (ι ∘ τ) = τ ∘ υ`**, the restriction to `𝕜` of the statement: the coefficient action of
`Φ ∘ Ω` is that of `Θ ∘ Φ`.

Both composites send `q` to `u` and `u` to `q⁻¹`, and the standing field is rigid over its two
parameters (`HJO.Ascent.ringHom_ext_param`). -/
theorem paramUInvHom_comp_paramSwapInvHom :
    (paramUInvHom K).comp (paramSwapInvHom K) = (paramSwapHom K).comp (paramUInvHom K) := by
  refine ringHom_ext_param ?_ ?_ <;> simp [RingHom.comp_apply, map_inv₀]

/-- `υ(ι(τ(c))) = τ(υ(c))` for every `c ∈ 𝕜`, the pointwise form of
`HJO.Ascent.paramUInvHom_comp_paramSwapInvHom`. -/
theorem paramUInvHom_paramSwapInvHom (c : K) :
    paramUInvHom K (paramSwapInvHom K c) = paramSwapHom K (paramUInvHom K c) :=
  RingHom.congr_fun (paramUInvHom_comp_paramSwapInvHom K) c

/-! ### The scalar identity on a generator -/

omit [Algebra ℚ K] in
/-- `1 - u^{-k} ≠ 0` for `k ≥ 1`, the nonvanishing the scalars of `𝒴` are built from: no positive
power of `u` is `1` at the standing field (`HJO.Standing.paramU_pow_succ_ne_one`), hence no positive
power of `u⁻¹` is either. -/
theorem one_sub_paramU_inv_pow_ne_zero (i : ℕ) : 1 - (paramU K)⁻¹ ^ (i + 1) ≠ 0 := by
  refine sub_ne_zero_of_ne fun hc => Standing.paramU_pow_succ_ne_one K i ?_
  rw [inv_pow, eq_comm, inv_eq_one] at hc
  exact hc

/-- **The generator case of the statement, as an identity in `𝕜`**:
`υ(Ω's scalar at p_k) · (1 - u^{-k})^{-1} = τ((1 - u^{-k})^{-1})`, at `k = i + 1`.

On the left, `υ` fixes `q` and inverts `u`, so `Ω`'s scalar becomes `-q^k (1-u^{-k})/(1-q^k)` and
the factor `(1-u^{-k})` cancels against the plethystic scalar, leaving `-q^k/(1-q^k)`. On the
right, `τ` exchanges the two parameters, so the plethystic scalar becomes `(1-q^{-k})^{-1}`, and
`HJO.Sym.inv_one_sub_pow_eq` at `q⁻¹` identifies that with `-q^k (1-q^k)^{-1}`.

The cancellation spends `1 - u^{-k} ≠ 0` and the right-hand identity spends `q ≠ 0`; nothing here
needs `1 - q^k ≠ 0`, both sides of the right-hand identity being `0` when `q^k = 1`. -/
theorem paramUInvHom_omegaScalar_mul_plethDivide_scalar (i : ℕ) :
    paramUInvHom K (omegaScalar K i) * (1 - (paramU K)⁻¹ ^ (i + 1))⁻¹
      = paramSwapHom K ((1 - (paramU K)⁻¹ ^ (i + 1))⁻¹) := by
  have hu : 1 - (paramU K)⁻¹ ^ (i + 1) ≠ 0 := one_sub_paramU_inv_pow_ne_zero K i
  have key : (1 - (paramQ K)⁻¹ ^ (i + 1))⁻¹
      = -paramQ K ^ (i + 1) * (1 - paramQ K ^ (i + 1))⁻¹ := by
    have h := inv_one_sub_pow_eq (u := (paramQ K)⁻¹)
      (inv_ne_zero (Standing.paramQ_ne_zero K)) (i + 1)
    rwa [inv_inv] at h
  have cancel : ∀ A B : K, A ≠ 0 →
      -paramQ K ^ (i + 1) * A / B * A⁻¹ = -paramQ K ^ (i + 1) * B⁻¹ := by
    intro A B hA
    rw [div_eq_mul_inv, show -paramQ K ^ (i + 1) * A * B⁻¹ * A⁻¹
      = -paramQ K ^ (i + 1) * B⁻¹ * (A * A⁻¹) by ring, mul_inv_cancel₀ hA, mul_one]
  rw [omegaScalar, map_div₀, map_mul, map_neg, map_pow, map_sub, map_one, map_pow, map_sub, map_one,
    map_pow, paramUInvHom_paramQ, paramUInvHom_paramU, map_inv₀, map_sub, map_one, map_pow,
    map_inv₀, paramSwapHom_paramU, key]
  exact cancel _ _ hu

/-! ### The statement -/

/-- `Ω` on a generator: `Ω(X i) = Ω`'s scalar at `p_{i+1}` times `X i`. The same fact as
`HJO.Ascent.dualityOmega_powerSum`, stated at the generator rather than at `p_{i+1}`, which is the
form `MvPolynomial.ringHom_ext` asks for. -/
@[simp]
theorem dualityOmega_X (i : ℕ) :
    dualityOmega K (MvPolynomial.X i) = MvPolynomial.C (omegaScalar K i) * MvPolynomial.X i := by
  simp [dualityOmega]

/-- `ȷ` fixes every generator, being a substitution of the coefficients. Stated at `X i` rather than
at `p_{i+1}`, which is the form `MvPolynomial.ringHom_ext` asks for. -/
@[simp]
theorem paramUInvLambda_X (i : ℕ) : paramUInvLambda K (MvPolynomial.X i) = MvPolynomial.X i :=
  coeffSubst_X _ i

/-- `Θ` fixes every generator, the companion of `HJO.Ascent.paramUInvLambda_X`. -/
@[simp]
theorem dualitySwap_X (i : ℕ) : dualitySwap K (MvPolynomial.X i) = MvPolynomial.X i :=
  coeffSubst_X _ i

/-- **The duality map is the exchange transported along the plethystic
substitution.** `𝒴(ȷ(Ω f)) = Θ(𝒴(ȷ(f)))` for every `f ∈ Λ`, at the standing coefficient field.

Both sides are ring endomorphisms of `Λ` applied to `f`, so `MvPolynomial.ringHom_ext` reduces the
statement to the constants and one generator. On the constants it is the commutation
`υ ∘ ι ∘ τ = τ ∘ υ` (`HJO.Ascent.paramUInvHom_paramSwapInvHom`), which comes from the rigidity of
`𝕜` over its two parameters; on a generator it is the scalar identity
`HJO.Ascent.paramUInvHom_omegaScalar_mul_plethDivide_scalar`, both sides reducing to `-q^k/(1-q^k)`.

Stated at `𝕜`: all three maps act on the coefficients through nontrivial automorphisms of the
coefficient field, which a general field of characteristic zero does not have. -/
@[hjo "lem_dua_omega_pleth"]
theorem plethDivide_paramUInvLambda_dualityOmega (f : Lambda K) :
    plethDivide (paramU K) (paramUInvLambda K (dualityOmega K f))
      = dualitySwap K (plethDivide (paramU K) (paramUInvLambda K f)) := by
  have h : (((plethDivide (paramU K)).toRingHom.comp (paramUInvLambda K)).comp
        (dualityOmega K) : Lambda K →+* Lambda K)
      = (dualitySwap K).comp ((plethDivide (paramU K)).toRingHom.comp (paramUInvLambda K)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dualityOmega_C,
        paramUInvLambda_C, plethDivide, diagScale_C, dualitySwap_C,
        paramUInvHom_paramSwapInvHom]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dualityOmega_X,
        map_mul, paramUInvLambda_C, paramUInvLambda_X, dualitySwap_C, dualitySwap_X, plethDivide,
        diagScale_C, diagScale_X]
      rw [← mul_assoc, ← MvPolynomial.C_mul, paramUInvHom_omegaScalar_mul_plethDivide_scalar]
  exact RingHom.congr_fun h f

end HJO.Ascent
