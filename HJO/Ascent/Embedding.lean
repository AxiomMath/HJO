/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.MvPolynomial.Basic
public meta import HJO.Attr

/-!
# The coefficient field `ℚ(q, u)` and its embedding into a field of characteristic zero

Let `𝕜 = ℚ(q, u)` be the field of rational functions in two indeterminates `q` and `u` over `ℚ`.
If `L` is a field of characteristic zero and `x, y ∈ L` satisfy no nonzero integer polynomial
relation, then there is an injective homomorphism of `ℚ`-algebras `𝕜 → L` sending `q` to `x` and
`u` to `y`.

## Main definitions

* `ParamRing`: the polynomial ring `ℚ[q, u] = MvPolynomial (Fin 2) ℚ`.
* `Kk`: the field of fractions of `ParamRing`.
* `paramSubst`: the `ℚ`-algebra homomorphism `ℚ[q, u] → K` sending `q` to `x` and `u` to `y`.
* `paramQ`, `paramU`: the images of the two indeterminates in a field of fractions of `ParamRing`.
* `toRatAlgHom`: a ring homomorphism between division rings of characteristic zero, as a
  homomorphism of `ℚ`-algebras.
* `paramEmbedding`: the extension to a field of fractions of `ParamRing` of the evaluation at an
  algebraically independent pair.

## Main results

* `algebraicIndependent_param`: `q` and `u` are algebraically independent over `ℤ`.
* `algebraicIndependent_rat`: algebraic independence of a pair over `ℤ` implies algebraic
  independence over `ℚ`.
* `exists_paramEmbedding`: an algebraically independent pair `x, y` in a field of characteristic
  zero `L` gives an injective `ℚ`-algebra homomorphism `𝕜 → L` sending `q` to `x` and `u` to `y`.

## Implementation notes

The field `𝕜` is not fixed as `FractionRing ParamRing`; instead every statement is quantified over
a field `K` with `[Algebra ParamRing K]` and `[IsFractionRing ParamRing K]`, and `Kk` witnesses
that such a field exists. This way the ring structure on `K` is always the one coming from
`[Field K]`, rather than the ring structure of the localization, with which it agrees only after
unfolding.
-/

@[expose] public section

namespace HJO.Ascent

/-! ### The parameter ring and the standing coefficient field -/

/-- The parameter ring `ℚ[q, u]`: the polynomial ring over `ℚ` on two indeterminates, the
indeterminate `MvPolynomial.X 0` standing for the dinv parameter `q` and `MvPolynomial.X 1` for the
area parameter `u`. -/
abbrev ParamRing : Type := MvPolynomial (Fin 2) ℚ

/-- The field `𝕜 = ℚ(q, u)` of rational functions in two indeterminates over `ℚ`: the field of
fractions of the parameter ring. -/
abbrev Kk : Type := FractionRing ParamRing

/-- The homomorphism of `ℚ`-algebras from the parameter ring `ℚ[q, u]` to `K` sending the
indeterminate standing for `q` to `x` and the one standing for `u` to `y`. -/
@[hjo "def_asc_instance"]
abbrev paramSubst {K : Type*} [CommRing K] [Algebra ℚ K] (x y : K) :
    ParamRing →ₐ[ℚ] K :=
  MvPolynomial.aeval ![x, y]

section Parameters

/-- The dinv parameter `q` of a presented copy of `𝕜`: the image of the first indeterminate of
`ℚ[q, u]`. -/
noncomputable def paramQ (K : Type*) [Field K] [Algebra ParamRing K] : K :=
  algebraMap ParamRing K (MvPolynomial.X 0)

/-- The area parameter `u` of a presented copy of `𝕜`: the image of the second indeterminate of
`ℚ[q, u]`. -/
noncomputable def paramU (K : Type*) [Field K] [Algebra ParamRing K] : K :=
  algebraMap ParamRing K (MvPolynomial.X 1)

variable (K : Type*) [Field K] [Algebra ParamRing K]

/-- The two parameters, as the family indexed by `Fin 2` that the independence and embedding
statements are phrased with. -/
theorem paramMatrix_eq :
    (fun i : Fin 2 => algebraMap ParamRing K (MvPolynomial.X i)) = ![paramQ K, paramU K] := by
  funext i
  fin_cases i <;> rfl

/-- Evaluating an integer polynomial in two variables at the two parameters is reading its
coefficients in `ℚ` and including the result in `K`. -/
theorem aeval_param_eq (p : MvPolynomial (Fin 2) ℤ) :
    (MvPolynomial.aeval fun i : Fin 2 => algebraMap ParamRing K (MvPolynomial.X i)) p =
      algebraMap ParamRing K (MvPolynomial.map (Int.castRingHom ℚ) p) := by
  have h : (MvPolynomial.aeval fun i : Fin 2 => algebraMap ParamRing K (MvPolynomial.X i) :
      MvPolynomial (Fin 2) ℤ →ₐ[ℤ] K).toRingHom =
      (algebraMap ParamRing K).comp (MvPolynomial.map (Int.castRingHom ℚ)) :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun i => by simp)
  exact RingHom.congr_fun h p

/-- The parameters `q` and `u` of a field of fractions of `ℚ[q, u]` are algebraically independent
over `ℤ`. -/
theorem algebraicIndependent_param [IsFractionRing ParamRing K] :
    AlgebraicIndependent ℤ ![paramQ K, paramU K] := by
  rw [← paramMatrix_eq, algebraicIndependent_iff_injective_aeval]
  intro a b hab
  rw [aeval_param_eq, aeval_param_eq] at hab
  exact MvPolynomial.map_injective _ (Int.castRingHom ℚ).injective_int
    (IsFractionRing.injective ParamRing K hab)

end Parameters

/-! ### From independence over the integers to independence over the rationals -/

/-- `ℚ` is algebraic over `ℤ`, being a localization of it: a rational `n / d` is a root of the
nonzero integer polynomial `d * T - n`. -/
theorem isAlgebraic_int_rat : Algebra.IsAlgebraic ℤ ℚ :=
  IsLocalization.isAlgebraic (S := ℚ) (nonZeroDivisors ℤ)

/-- Two elements of a field of characteristic zero that are algebraically independent over `ℤ` are
algebraically independent over `ℚ`. -/
@[hjo "lem_asc_alg_indep_rational"]
theorem algebraicIndependent_rat {L : Type*} [Field L] [Algebra ℚ L] {x y : L}
    (h : AlgebraicIndependent ℤ ![x, y]) : AlgebraicIndependent ℚ ![x, y] :=
  haveI := isAlgebraic_int_rat
  h.extendScalars (S := ℚ)

/-! ### A ring homomorphism between fields of characteristic zero is a `ℚ`-algebra map -/

section RatAlgebra

variable {A B : Type*} [DivisionRing A] [Algebra ℚ A] [DivisionRing B] [Algebra ℚ B]

/-- A ring homomorphism between division rings of characteristic zero fixes `ℚ` pointwise: there is
only one ring homomorphism out of `ℚ` into a division ring, so the two composites `ℚ → A → B` and
`ℚ → B` coincide. -/
theorem ringHom_algebraMap_rat (φ : A →+* B) (c : ℚ) :
    φ (algebraMap ℚ A c) = algebraMap ℚ B c :=
  RingHom.congr_fun (Subsingleton.elim (φ.comp (algebraMap ℚ A)) (algebraMap ℚ B)) c

/-- A ring homomorphism between division rings of characteristic zero, read as a homomorphism of
`ℚ`-algebras. -/
def toRatAlgHom (φ : A →+* B) : A →ₐ[ℚ] B :=
  { φ with commutes' := ringHom_algebraMap_rat φ }

/-- The underlying function of `toRatAlgHom φ` is that of `φ`. -/
@[simp]
theorem coe_toRatAlgHom (φ : A →+* B) : (toRatAlgHom φ : A → B) = φ := rfl

end RatAlgebra

/-! ### The embedding -/

section Embedding

variable {K : Type*} [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K]
variable {L : Type*} [Field L] [Algebra ℚ L] {x y : L}

/-- The embedding of the standing coefficient field into a field carrying an algebraically
independent pair of parameters: the unique extension to `𝕜 = ℚ(q, u)` of the evaluation
`ℚ[q, u] → L` at the pair, which is injective by algebraic independence. -/
noncomputable def paramEmbedding (K : Type*) [Field K] [Algebra ParamRing K]
    [IsFractionRing ParamRing K] (h : AlgebraicIndependent ℤ ![x, y]) : K →+* L :=
  IsFractionRing.lift (A := ParamRing) (K := K) (g := (MvPolynomial.aeval ![x, y]).toRingHom)
    (algebraicIndependent_rat h)

/-- The embedding extends the evaluation at the pair: on the image of a polynomial in the two
parameters it is that polynomial evaluated at the pair. -/
@[simp]
theorem paramEmbedding_algebraMap (h : AlgebraicIndependent ℤ ![x, y]) (p : ParamRing) :
    paramEmbedding K h (algebraMap ParamRing K p) = MvPolynomial.aeval ![x, y] p :=
  IsFractionRing.lift_algebraMap _ p

/-- The embedding carries the dinv parameter of `𝕜` to the first of the two given parameters. -/
@[simp]
theorem paramEmbedding_paramQ (h : AlgebraicIndependent ℤ ![x, y]) :
    paramEmbedding K h (paramQ K) = x := by
  rw [paramQ, paramEmbedding_algebraMap, MvPolynomial.aeval_X]
  rfl

/-- The embedding carries the area parameter of `𝕜` to the second of the two given parameters. -/
@[simp]
theorem paramEmbedding_paramU (h : AlgebraicIndependent ℤ ![x, y]) :
    paramEmbedding K h (paramU K) = y := by
  rw [paramU, paramEmbedding_algebraMap, MvPolynomial.aeval_X]
  rfl

/-- The embedding is injective, its source being a field. -/
theorem paramEmbedding_injective (h : AlgebraicIndependent ℤ ![x, y]) :
    Function.Injective (paramEmbedding K h) := (paramEmbedding K h).injective

/-- Over a field of characteristic zero carrying two parameters that satisfy no nonzero integer
polynomial relation there is an injective homomorphism of `ℚ`-algebras from `𝕜 = ℚ(q, u)` carrying
`q` to the first parameter and `u` to the second. -/
@[hjo "lem_asc_param_embedding"]
theorem exists_paramEmbedding (K : Type*) [Field K] [Algebra ParamRing K]
    [IsFractionRing ParamRing K] [Algebra ℚ K] (h : AlgebraicIndependent ℤ ![x, y]) :
    ∃ φ : K →ₐ[ℚ] L, Function.Injective φ ∧ φ (paramQ K) = x ∧ φ (paramU K) = y :=
  ⟨toRatAlgHom (paramEmbedding K h), paramEmbedding_injective h, paramEmbedding_paramQ h,
    paramEmbedding_paramU h⟩

end Embedding

end HJO.Ascent
