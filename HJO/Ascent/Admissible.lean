/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Ascent.Embedding
public import HJO.Collinear.Commutation
public meta import HJO.Attr

/-!
# Admissible instances

A pair of parameters `x`, `y` in a field is admissible when `x`, `y`, every `(x * y) ^ (j + 1) - 1`
and `(1 - x) * (1 - y)` are nonzero. Algebraically independent parameters are admissible, so in
particular the two indeterminates of `ℚ(q, u)` are, and admissibility is preserved by every ring
homomorphism between fields.

## Main definitions

* `HJO.Ascent.IsAdmissible`: the pair `x`, `y` is admissible.

## Main results

* `HJO.Ascent.isAdmissible_of_algebraicIndependent`: algebraically independent parameters are
  admissible.
* `HJO.Ascent.isAdmissible_standing`: the parameters `paramQ K`, `paramU K` are admissible.
* `HJO.Ascent.IsAdmissible.map`: the image of an admissible pair under a ring homomorphism of
  fields is admissible.
-/

@[expose] public section

namespace HJO.Ascent

/-! ### The four conditions -/

/-- A pair of parameters `x`, `y` in a field is admissible when `x` and `y` are nonzero, no
positive power of `x * y` is `1`, and `(1 - x) * (1 - y)` is nonzero. -/
@[hjo "def_asc_admissible"]
structure IsAdmissible {K : Type*} [Field K] (x y : K) : Prop where
  /-- The first parameter is invertible. -/
  fst_ne_zero : x ≠ 0
  /-- The second parameter is invertible. -/
  snd_ne_zero : y ≠ 0
  /-- No positive power of the parameter product is `1`; at `j = 0` this is `x * y ≠ 1`. -/
  mul_pow_succ_ne_one : ∀ j : ℕ, (x * y) ^ (j + 1) ≠ 1
  /-- The parameter product `M = (1 - x) * (1 - y)` is invertible. -/
  mparam_ne_zero : (1 - x) * (1 - y) ≠ 0

/-! ### Algebraically independent parameters are admissible -/

/-- A pair of parameters algebraically independent over `ℤ` is admissible. -/
@[hjo "lem_asc_generic_admissible"]
theorem isAdmissible_of_algebraicIndependent {L : Type*} [Field L] {x y : L}
    (h : AlgebraicIndependent ℤ ![x, y]) : IsAdmissible x y where
  fst_ne_zero := left_ne_zero_of_mul (CollinearNarrowed.mul_ne_zero_of_algebraicIndependent h)
  snd_ne_zero := right_ne_zero_of_mul (CollinearNarrowed.mul_ne_zero_of_algebraicIndependent h)
  mul_pow_succ_ne_one := CollinearNarrowed.pow_succ_ne_one_of_algebraicIndependent h
  mparam_ne_zero :=
    CollinearNarrowed.one_sub_mul_one_sub_ne_zero_of_algebraicIndependent h

/-- The two indeterminates `paramQ K`, `paramU K` of the fraction field `K` of the parameter ring
are admissible. -/
@[hjo "lem_asc_standing_admissible"]
theorem isAdmissible_standing (K : Type*) [Field K] [Algebra ParamRing K]
    [IsFractionRing ParamRing K] : IsAdmissible (paramQ K) (paramU K) :=
  isAdmissible_of_algebraicIndependent (algebraicIndependent_param K)

/-! ### Admissibility passes forward -/

/-- The image of an admissible pair under a ring homomorphism of fields is admissible. -/
@[hjo "lem_asc_admissible_image"]
theorem IsAdmissible.map {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') {x y : K}
    (h : IsAdmissible x y) : IsAdmissible (φ x) (φ y) where
  fst_ne_zero := by
    simpa [map_ne_zero_iff φ φ.injective] using h.fst_ne_zero
  snd_ne_zero := by
    simpa [map_ne_zero_iff φ φ.injective] using h.snd_ne_zero
  mul_pow_succ_ne_one j := by
    rw [← map_mul, ← map_pow, ← map_one φ]
    exact fun hj => h.mul_pow_succ_ne_one j (φ.injective hj)
  mparam_ne_zero := by
    rw [← map_one φ, ← map_sub, ← map_sub, ← map_mul, map_ne_zero_iff φ φ.injective]
    exact h.mparam_ne_zero

end HJO.Ascent
