/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Ascent.Transport
public import HJO.Macdonald.DualityShift
public meta import HJO.Attr

/-! # The exchange commutes with the degree-zero operator

`HJO.Ascent.dualitySwap_dop_zero`: `Θ(D_0 f) = D_0(Θ f)` for every `f ∈ Λ`.

## The two general facts it rests on

**`D_0` does not depend on the ORDER of the two parameters.** `HJO.Sym.Dop q u k` is
`coeffPairing (...) ∘ plethShift q u`, the pairing factor involves only the elementary symmetric
functions, and `HJO.Sym.plethShift`'s scalar is `(1 - q^k)(1 - u^k)`, which is symmetric. So
`plethShift q u = plethShift u q` and hence `Dop q u k = Dop u q k`, over any commutative
`ℚ`-algebra and with no hypothesis on the parameters. Those are `HJO.Sym.plethShift_comm` and
`HJO.Sym.dop_comm` below, and they are worth having on their own: every statement about the
operators proved at one order of the parameters is now available at the other for free.

**A coefficient extension intertwines the operators.** `HJO.Ascent.lambdaMap_dop`
says `lambdaMap φ (Dop q u k f) = Dop (φ q) (φ u) k (lambdaMap φ f)` for a homomorphism `φ` of
coefficient fields.

Put together, the statement is immediate rather than a computation. `Θ` IS a coefficient extension
-- `HJO.Ascent.dualitySwap` is `coeffSubst` is `MvPolynomial.map`, the same construction `lambdaMap`
bundles -- so the transport applies to it and produces `Dop (τ q) (τ u) 0 = Dop u q 0`, which the
symmetry turns back into `Dop q u 0`.

The transport lemmas for coefficient extensions apply to the duality maps elsewhere too:
`HJO.Ascent.dualitySwap_elemSymm` comes the same way, from `HJO.Ascent.lambdaMap_elemSymm`. `Θ` and
a coefficient extension are literally the same construction, so anything proved about one holds of
the other.

## What the usual proof does instead, and why this is the same argument

The usual argument runs through `Λ[z^{-1}][[z]]`: write `D_0 f = [z^0](δ(f) ∑_r (-z)^r e_r)`,
observe that `Θ_z` commutes with reading off a coefficient, that it is multiplicative, that it
carries `δ(f)` to `δ(Θ f)` (`HJO.Ascent.polynomialMap_dualitySwap_plethShift`) and fixes
`∑_r (-z)^r e_r` (`HJO.Ascent.dualitySwap_elemSymm`). Every one of those steps is contained in
`lambdaMap_dop`, whose proof is exactly that decomposition run once and for all for an arbitrary
coefficient extension. So nothing of the argument is skipped; it has been factored.

## Generality

Stated at the standing field because `Θ` is: the exchange is a nontrivial ring endomorphism of the
coefficients, and a general field of characteristic zero has none. No genericity is spent -- the two
supporting facts hold at every degenerate corner -- and `HJO.Sym.plethShift_comm` and
`HJO.Sym.dop_comm` are at an arbitrary commutative `ℚ`-algebra.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [Algebra ℚ K]

omit [Algebra ℚ K] in
/-- **The plethystic displacement is symmetric in the two parameters.**
`δ^{q,u} = δ^{u,q}`, because its scalar `(1 - q^k)(1 - u^k)` is.

Both sides are `K`-algebra maps out of a polynomial ring, so agreeing on the generators suffices,
and there they differ by one `mul_comm`. -/
theorem plethShift_comm (q u : K) : plethShift q u = plethShift u q := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [plethShift, MvPolynomial.aeval_X, mul_comm]

/-- **The basic operators are symmetric in the two parameters.** `D^{q,u}_k = D^{u,q}_k`: the
operator is a fixed pairing composed with the displacement, and the displacement is symmetric by
`HJO.Sym.plethShift_comm`. -/
theorem dop_comm (q u : K) (k : ℕ) : Dop q u k = Dop u q k := by
  rw [Dop, Dop, plethShift_comm]

end HJO.Sym

namespace HJO.Ascent

open HJO.Sym

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **The exchange commutes with the degree-zero operator.**
`Θ(D_0 f) = D_0(Θ f)`.

`Θ` is a coefficient extension, so `HJO.Ascent.lambdaMap_dop` carries `D_0` through it and yields
`D_0` at the EXCHANGED parameters; `HJO.Sym.dop_comm` says that is the same operator. -/
@[hjo "lem_dua_swap_dop_zero"]
theorem dualitySwap_dop_zero (f : Lambda K) :
    dualitySwap K (Dop (paramQ K) (paramU K) 0 f)
      = Dop (paramQ K) (paramU K) 0 (dualitySwap K f) := by
  have h := lambdaMap_dop (φ := toRatAlgHom (paramSwapHom K)) (paramQ K) (paramU K) 0 f
  rw [lambdaMap_apply, lambdaMap_apply] at h
  rw [show (MvPolynomial.map ((toRatAlgHom (paramSwapHom K) : K →+* K)) :
      Lambda K → Lambda K) = dualitySwap K from rfl] at h
  simpa only [coe_toRatAlgHom, paramSwapHom_paramQ, paramSwapHom_paramU,
    dop_comm (paramU K) (paramQ K)] using h

end HJO.Ascent
