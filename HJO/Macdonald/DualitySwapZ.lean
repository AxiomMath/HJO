/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import HJO.Macdonald.Duality
public meta import HJO.Attr

/-! # The exchange of the two parameters in the auxiliary variable

`HJO.Ascent.dualitySwapZ` -- `Θ_z`, the ring endomorphism of `Λ[z^{-1}][[z]]` applying `Θ` to each
coefficient and fixing `z`.

## `Λ[z^{-1}][[z]]` is `LaurentSeries (Lambda K)`

The ring is the formal series `F = ∑_{n ≥ -N} F_n z^n` with `N ≥ 0` and every
`F_n ∈ Λ`: arbitrary in the positive direction, finitely many negative powers. That is exactly a
Hahn series over the exponent group `ℤ`, whose defining condition is that the support be partially
well-ordered; over a linear order that is well-foundedness, and a subset of `ℤ` is well-founded iff
it is bounded below. So `HahnSeries ℤ (Lambda K) = LaurentSeries (Lambda K)` is the ring
on the nose, and no series type is built here. `HJO/Main/Endgame.lean` already reads the auxiliary
variable this way.

## The only thing missing from Mathlib was the bundling

`HahnSeries.map` applies a zero-preserving map to each coefficient, and Mathlib proves it
multiplicative (`HahnSeries.map_mul`, from the convolution formula over the finite antidiagonal),
additive, unital and zero-preserving. What it does not do is package those four facts as a
`RingHom`, which is what a "ring endomorphism of `Λ[z^{-1}][[z]]`" has to be if `Θ_z` is to be
composed with anything. `HJO.Sym.hahnMapRingHom` is that packaging, stated for an arbitrary exponent
monoid rather than for `ℤ`, since nothing in it is about the auxiliary variable.

## No sign, and no genericity beyond `Θ`'s own

Unlike the inversion in the auxiliary variable there is no sign here, `z` carrying no parameter: the
map is literally `Θ` on each coefficient. The standing-field binders are inherited from `Θ`
(`HJO.Ascent.dualitySwap`), which needs the exchange `τ` of the two parameters and therefore does
not exist over a general field -- over `ℝ` the only ring endomorphism is the identity. Nothing in
this file adds a hypothesis of its own.
-/

@[expose] public section

namespace HJO.Sym

/-- **Applying a ring homomorphism to every coefficient of a Hahn series is a ring
homomorphism.** Mathlib has the four component facts -- `HahnSeries.map_zero`, `HahnSeries.map_add`,
`HahnSeries.map_one` and `HahnSeries.map_mul`, the last of them the genuine content, proved from the
convolution formula over the finite antidiagonal -- but no bundled `RingHom`, and a bundled one is
what the "ring endomorphism of `Λ[z^{-1}][[z]]`" asks for. Stated at an arbitrary
exponent monoid: nothing here is about the auxiliary variable. -/
noncomputable def hahnMapRingHom {Γ : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ] {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) :
    HahnSeries Γ R →+* HahnSeries Γ S where
  toFun x := x.map f
  map_zero' := by ext g; simp [HahnSeries.map_coeff]
  map_one' := by ext g; simp [HahnSeries.map_coeff]
  map_add' x y := by ext g; simp [HahnSeries.map_coeff]
  map_mul' _ _ := HahnSeries.map_mul (f : R →ₙ+* S)

@[simp]
theorem hahnMapRingHom_coeff {Γ : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ] {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (x : HahnSeries Γ R) (g : Γ) : (hahnMapRingHom f x).coeff g = f (x.coeff g) :=
  HahnSeries.map_coeff x f g

@[simp]
theorem hahnMapRingHom_C {Γ : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ] {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (a : R) :
    hahnMapRingHom f (HahnSeries.C a : HahnSeries Γ R) = HahnSeries.C (f a) :=
  HahnSeries.map_C a f

end HJO.Sym

namespace HJO.Ascent

open HJO.Sym

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **The exchange of the two parameters in the auxiliary variable.** `Θ_z`, the
ring endomorphism of `Λ[z^{-1}][[z]]` sending `F = ∑_{n ≥ -N} F_n z^n` to `∑_{n ≥ -N} Θ(F_n) z^n`:
apply `Θ` to each coefficient and fix `z`.

`Λ[z^{-1}][[z]]` is `LaurentSeries (Lambda K)`, the Hahn series over the exponent group `ℤ`, whose
partially-well-ordered support condition is over `ℤ` exactly the "finitely many negative
powers". So the definition is `HJO.Sym.hahnMapRingHom` at `Θ` and nothing more; the
ring-endomorphism clause of the definition is discharged by that bundling rather than asserted.

Its restriction to `Λ` -- the series with `F_n = 0` for `n ≠ 0`, i.e. the image of
`HahnSeries.C` -- is `Θ`, which is `dualitySwapZ_C` below. Unlike the inversion in the auxiliary
variable there is no sign, `z` carrying no parameter.

At the standing field because `Θ` is: the exchange `τ` of the two parameters is a nontrivial ring
endomorphism of the coefficients, and over a general field of characteristic zero -- `ℝ`, say --
there is none. -/
@[hjo "def_dua_swap_z"]
noncomputable def dualitySwapZ :
    LaurentSeries (Lambda K) →+* LaurentSeries (Lambda K) :=
  hahnMapRingHom (dualitySwap K)

/-- `Θ_z` acts coefficientwise by `Θ`: the defining clause. -/
@[simp]
theorem dualitySwapZ_coeff (F : LaurentSeries (Lambda K)) (n : ℤ) :
    (dualitySwapZ K F).coeff n = dualitySwap K (F.coeff n) :=
  hahnMapRingHom_coeff _ F n

/-- **The restriction of `Θ_z` to `Λ` is `Θ`**: on the series supported at `z^0` -- the image of
`HahnSeries.C`, which is how `Λ` sits inside `Λ[z^{-1}][[z]]` -- `Θ_z` is `Θ`. -/
@[simp]
theorem dualitySwapZ_C (f : Lambda K) :
    dualitySwapZ K (HahnSeries.C f) = HahnSeries.C (dualitySwap K f) :=
  hahnMapRingHom_C _ f

end HJO.Ascent
