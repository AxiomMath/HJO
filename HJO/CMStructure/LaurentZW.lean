/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The two-variable Laurent series ring of the Carlsson--Mellit layer

The Haglund--Morse--Zabrocki block of the Carlsson--Mellit layer works inside
`𝒵 = Λ[[z]][z⁻¹][[w]][w⁻¹]`: formal Laurent series in `w` whose coefficients are formal Laurent
series in `z` with coefficients in `Λ`. Everything the layer does with `𝒵` is a bivariate
coefficient extraction `[z^a w^b]`, so this file names the ring and that extraction and nothing
else.

`Mathlib.RingTheory.LaurentSeries` already identifies `R[[z]][z⁻¹]` with `LaurentSeries R`, the Hahn
series over `ℤ` (`LaurentSeries.of_powerSeries_localization` is the identification), so `𝒵` is the
iteration of that construction: the *outer* variable is `w` and the *inner* one is `z`, matching the
order in which the tower `Λ[[z]][z⁻¹][[w]][w⁻¹]` is written.

## Main definitions

* `HJO.Sym.LaurentZW`: the ring `𝒵`.
* `HJO.Sym.bicoeff`: the extraction `[z^a w^b]`, as an additive homomorphism to `Λ`.
* `HJO.Sym.monomialZW`: the monomial `f z^a w^b`, which is what `bicoeff` is tested against.

## Implementation notes

`LaurentZW` is an `abbrev`, so every `Ring`, `CommRing` and `Module` instance `Mathlib` proves for
an iterated `HahnSeries` is available on it without a single transfer lemma. This is deliberate: a
`def` here would need each instance restated, and there are no `𝒵`-specific instances to prove.

The coefficient extraction is packaged as an `AddMonoidHom` rather than a `K`-linear map. The reason
is a genuine instance diamond and not a matter of taste: `HahnSeries` has both
`HahnSeries.instAlgebra` and `HahnSeries.powerSeriesAlgebra`, and on `𝒵` over the base `K` both
apply, so a statement mentioning `Algebra K 𝒵` is a statement about whichever instance the
elaborator reached for. Additivity is all the layer's coefficient manipulations use, and scalars
enter through `Λ` itself, where there is no ambiguity.
-/

@[expose] public section

namespace HJO.Sym

section LaurentZW

variable (K : Type*) [CommRing K]

/-- **The two-variable Laurent series ring** `𝒵 = Λ[[z]][z⁻¹][[w]][w⁻¹]`: formal Laurent series in
the outer variable `w` whose coefficients are formal Laurent series in the inner variable `z` with
coefficients in `Λ`. -/
@[hjo "def_cm_laurent_zw"]
abbrev LaurentZW : Type _ := LaurentSeries (LaurentSeries (Lambda K))

variable {K}

/-- **The bivariate coefficient extraction** `[z^a w^b]`: take the coefficient of `w^b`, which is a
Laurent series in `z`, then the coefficient of `z^a` in that. This is the only operation the layer
performs on `𝒵`, and it is what makes the ring the one described above. -/
@[hjo "def_cm_laurent_zw"]
def bicoeff (a b : ℤ) (f : LaurentZW K) : Lambda K := (f.coeff b).coeff a

/-- `[z^a w^b]` is additive. -/
@[simp]
theorem bicoeff_add (a b : ℤ) (f g : LaurentZW K) :
    bicoeff a b (f + g) = bicoeff a b f + bicoeff a b g := by
  rfl

/-- `[z^a w^b]` kills zero. -/
@[simp]
theorem bicoeff_zero (a b : ℤ) : bicoeff a b (0 : LaurentZW K) = 0 := by
  rw [bicoeff, HahnSeries.coeff_zero, HahnSeries.coeff_zero]

/-- `[z^a w^b]`, packaged as an additive homomorphism `𝒵 →+ Λ`. -/
@[hjo "def_cm_laurent_zw"]
def bicoeffAddHom (a b : ℤ) : LaurentZW K →+ Lambda K where
  toFun := bicoeff a b
  map_zero' := bicoeff_zero a b
  map_add' := bicoeff_add a b

@[simp]
theorem bicoeffAddHom_apply (a b : ℤ) (f : LaurentZW K) : bicoeffAddHom a b f = bicoeff a b f :=
  rfl

/-- **The monomial `f z^a w^b`** of `𝒵`, for a coefficient `f ∈ Λ`. -/
@[hjo "def_cm_laurent_zw"]
noncomputable def monomialZW (a b : ℤ) (f : Lambda K) : LaurentZW K :=
  HahnSeries.single b (HahnSeries.single a f)

/-- The defining property of the bivariate extraction: it reads the coefficient off a monomial,
returning `f` at the monomial's own bidegree and `0` at every other. -/
@[hjo "def_cm_laurent_zw", simp]
theorem bicoeff_monomialZW (a b a' b' : ℤ) (f : Lambda K) :
    bicoeff a' b' (monomialZW a b f) = if a' = a ∧ b' = b then f else 0 := by
  rw [bicoeff, monomialZW]
  split_ifs with h
  · rw [h.2, HahnSeries.coeff_single_same, h.1, HahnSeries.coeff_single_same]
  · rcases not_and_or.mp h with ha | hb
    · by_cases hb' : b' = b
      · rw [hb', HahnSeries.coeff_single_same, HahnSeries.coeff_single_of_ne ha]
      · rw [HahnSeries.coeff_single_of_ne hb', HahnSeries.coeff_zero]
    · rw [HahnSeries.coeff_single_of_ne hb, HahnSeries.coeff_zero]

end LaurentZW

end HJO.Sym
