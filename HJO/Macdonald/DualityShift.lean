/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.Duality
public meta import HJO.Attr

/-! # The exchange commutes with the plethystic displacement

`HJO.Ascent.polynomialMap_dualitySwap_plethShift`: `Θ_z(δ(f)) = δ(Θ(f))` for every `f ∈ Λ`.

## Why the SAME `δ` appears on both sides, which is the whole content

`Θ` exchanges the two parameters, so one would expect pushing it through a map built from `q` and
`u` to produce that map at the exchanged parameters. It does not, and the reason is that `δ`'s
scalar is **symmetric**: `HJO.Sym.plethShift` sends `p_k` to `p_k + (1 - q^k)(1 - u^k) z^{-k}`, and
`(1 - u^k)(1 - q^k)` is the same element. So `τ` fixes every scalar `δ` uses, and the statement is
exactly that symmetry plus the fact that both sides are ring homomorphisms out of a polynomial ring.

`HJO.Ascent.paramSwapHom_shiftScalar` below isolates the symmetry, so that a reader can see the one
fact the statement rests on without reading the `ringHom_ext` bookkeeping around it. The same remark
applies to the starred displacement `HJO.Sym.plethShiftStar`, whose scalar
`(1 - q^{-k})(1 - u^{-k})` is symmetric for the same reason.

## Where the statement lives

`δ`'s target is `Polynomial (Lambda K)`, the polynomial ring on `w = z^{-1}` -- only NON-NEGATIVE
powers of `w` occur in a displacement, which is why `HJO.Sym.plethShift` was given that target
rather than a Laurent one. So the identity is stated there, and `Θ_z` restricted to that subring is
`Polynomial.map (dualitySwap K)`.

That is not a weakening of the identity as usually read, in `Λ[z^{-1}][[z]]`: the displacement's
image lies in the polynomial subring, `HJO.Ascent.dualitySwapZ` acts coefficientwise by `Θ` there as
everywhere, and the two therefore agree on every element `δ` produces. Stating it at the polynomial
ring avoids carrying an embedding through the proof for no gain, and it is the form every consumer
in this library uses, since they all pair a displacement against a family with
`HJO.Sym.coeffPairing`, which is defined on `Polynomial (Lambda K)`.

## Generality

Stated at the standing coefficient field, because `Θ` is: the exchange is a nontrivial ring
endomorphism of the coefficients, and a general field of characteristic zero has none -- over `ℝ`
the only ring endomorphism is the identity. The two parameters themselves are unconstrained beyond
being the standing indeterminates; no genericity is spent, and in particular the symmetry argument
holds at every degenerate corner.
-/

@[expose] public section

namespace HJO.Ascent

open HJO.Sym

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **The displacement's scalar is symmetric in the two parameters, so the exchange fixes it.**
`τ((1 - q^n)(1 - u^n)) = (1 - q^n)(1 - u^n)`: the exchange swaps the two factors, and they commute.

This is the one fact `HJO.Ascent.polynomialMap_dualitySwap_plethShift` rests on. -/
@[simp]
theorem paramSwapHom_shiftScalar (n : ℕ) :
    paramSwapHom K ((1 - paramQ K ^ n) * (1 - paramU K ^ n))
      = (1 - paramQ K ^ n) * (1 - paramU K ^ n) := by
  rw [map_mul, map_sub, map_sub, map_one, map_pow, map_pow, paramSwapHom_paramQ,
    paramSwapHom_paramU, mul_comm]

/-- **The exchange commutes with the plethystic displacement.**
`Θ_z(δ(f)) = δ(Θ(f))`, with `Θ_z` read on `Polynomial (Lambda K)` -- the polynomial ring on
`w = z^{-1}`, which is where `δ` lands -- as the coefficientwise `Θ`.

Both sides are ring homomorphisms `Λ → Λ[w]`, so `MvPolynomial.ringHom_ext` reduces the claim to the
constants and the generators. On a constant both sides give `τ` of it. On the generator `X i = p_k`
both sides give `p_k + (1 - q^k)(1 - u^k) w^k`, because `Θ` fixes every power sum and
`HJO.Ascent.paramSwapHom_shiftScalar` says it fixes the scalar. -/
@[hjo "lem_dua_swap_shift"]
theorem polynomialMap_dualitySwap_plethShift (f : Lambda K) :
    Polynomial.map (dualitySwap K) (plethShift (paramQ K) (paramU K) f)
      = plethShift (paramQ K) (paramU K) (dualitySwap K f) := by
  have key : (Polynomial.mapRingHom (dualitySwap K)).comp
        (plethShift (paramQ K) (paramU K) : Lambda K →+* Polynomial (Lambda K))
      = (plethShift (paramQ K) (paramU K) : Lambda K →+* Polynomial (Lambda K)).comp
        (dualitySwap K) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom,
        Polynomial.coe_mapRingHom]
      have h : ∀ b : K, plethShift (paramQ K) (paramU K) (MvPolynomial.C b)
          = Polynomial.C (MvPolynomial.C b) := fun b => by
        rw [show MvPolynomial.C b = algebraMap K (Lambda K) b from rfl, AlgHom.commutes]; rfl
      rw [dualitySwap_C, h a, h (paramSwapHom K a), Polynomial.map_C, dualitySwap_C]
    · have hX : dualitySwap K (MvPolynomial.X i) = MvPolynomial.X i := coeffSubst_X _ i
      have hp : powerSum K (i + 1) = MvPolynomial.X i := by simp [powerSum]
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, hX,
        Polynomial.coe_mapRingHom, plethShift, MvPolynomial.aeval_X, Polynomial.map_add,
        Polynomial.map_C, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
        dualitySwap_powerSum, dualitySwap_C, paramSwapHom_shiftScalar]
  exact RingHom.congr_fun key f

end HJO.Ascent
