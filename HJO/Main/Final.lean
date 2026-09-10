/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Main.Assembly
public import HJO.Evaluation.PhiMul
public meta import HJO.Attr

/-! # The five conclusions at the model

The chain over one hypothesis is closed here by reading it at the concrete specialisation data.
That data supplies a coefficient *ring* whose specialisation sends the second parameter to `1`,
while the chain asks for a coefficient *field* carrying the first parameter alone. The two fit
because the coefficient ring is the power series over `ℚ((q))` in the deformation parameter, so
`ℚ((q))` itself sits inside it as the constants: it is a field, it contains the first parameter,
and it omits the second, which is `1` plus the deformation parameter. The evaluation map on the
symmetric functions with coefficients in `ℚ((q))` is therefore the evaluation map over the
coefficient ring precomposed with the inclusion of the constants, and the clause of the
multiplicativity statement about a weighted homogeneous element is exactly what the chain asks of
it.

The genericity of the two parameters, which the compositional rational shuffle identity is quoted
at and which the witness polynomials are pinned down by, is proved rather than assumed, alongside
the rest of the specialisation data: the first parameter is the variable of `ℚ((q))`, which is
transcendental over `ℚ`, and the second is `1` plus the deformation parameter, so a relation between
them is a polynomial in two variables over `ℤ` vanishing after the substitutions
`x ↦ q, y ↦ ℏ + 1`, and those substitutions factor through the polynomials in two variables over
`ℤ` by a map with a left inverse.

The conclusions are the exponential form of the generating series of the finite polynomials, the
`q`-difference equation it satisfies, the scalar recurrence, the finite identity and the
conjecture. Beyond the results quoted from the literature nothing is assumed.
-/

@[expose] public section

open Finset

namespace HJO.Final

open HJO.Sym HJO.ReesRegular HJO.PhiMul
open HJO.PhiMul.Witness (Target Coeff Base)

/-! ### Transfer between the coefficient field and the coefficient ring -/

/-- A coefficientwise ring homomorphism preserves weighted homogeneity. -/
theorem isWeightedHomogeneous_map {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (hom : R →+* S) {w : σ → ℕ} {f : MvPolynomial σ R} {n : ℕ}
    (hf : MvPolynomial.IsWeightedHomogeneous w f n) :
    MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.map hom f) n := fun d hd =>
  hf fun h => hd (by rw [MvPolynomial.coeff_map, h, map_zero])

/-- The coefficient field sits inside the coefficient ring as the constants: its structure map to
the base field is the inclusion of the constants followed by the structure map of the coefficient
ring. -/
theorem algebraMap_target (x : Target) :
    algebraMap Target Base x = algebraMap Coeff Base (PowerSeries.C x) := by
  rw [IsScalarTower.algebraMap_apply Target Coeff Base]; rfl

/-- The first parameter is the same read in the coefficient field and in the coefficient ring. -/
theorem algebraMap_qVar :
    algebraMap Target Base Determinant.qVar = algebraMap Coeff Base Witness.q :=
  algebraMap_target Determinant.qVar

/-- Extending a symmetric function over the coefficient field to the coefficient ring and then to
the base field is extending it to the base field directly. -/
theorem coeffInc_map_C (f : Lambda Target) :
    coeffInc Coeff Base (MvPolynomial.map (PowerSeries.C : Target →+* Coeff) f)
      = MvPolynomial.map (algebraMap Target Base) f := by
  rw [coeffInc_apply, MvPolynomial.map_map]; congr 1

/-- Substituting the variable of `ℚ((q))` for the first parameter and `1` for the second is the
image along the inclusion of the integral power series of the same substitution there. -/
theorem qOfInt_aeval (π : MvPolynomial (Fin 2) ℤ) :
    Determinant.qOfInt (MvPolynomial.aeval ![(PowerSeries.X : PowerSeries ℤ), 1] π)
      = polyValue π Determinant.qVar 1 := by
  rw [polyValue_eq_aeval]
  induction π using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp only [map_add, hp, hr]
  | mul_X p i hp =>
    have hi : Determinant.qOfInt (![(PowerSeries.X : PowerSeries ℤ), 1] i)
        = ![Determinant.qVar, (1 : LaurentSeries ℚ)] i := by
      fin_cases i <;> simp [Determinant.qVar]
    simp only [map_mul, MvPolynomial.aeval_X, hp, hi]

/-- The value the chain reads off a witness polynomial of a seed of degree `n` is the value the
specialisation reads off it, carrying the same sign. -/
theorem qOfInt_phiValue (b n : ℕ) (π : MvPolynomial (Fin 2) ℤ) :
    Determinant.qOfInt (PhiPoly.phiValue b n π)
      = (-1) ^ (n * (b + 1)) * polyValue π Determinant.qVar 1 := by
  rw [PhiPoly.phiValue, map_mul, map_pow, map_neg, map_one, qOfInt_aeval]

/-! ### The evaluation map on the symmetric functions over `ℚ((q))` -/

/-- The evaluation map of the model, read on the symmetric functions whose coefficients lie in
`ℚ((q))`: the evaluation map over the coefficient ring, precomposed with the inclusion of `ℚ((q))`
as the constants. -/
noncomputable def phi {a b : ℕ} {Θ : Lambda Base →ₐ[Base] Module.End Base (Lambda Base)}
    (hΘ : IsSlopeHom a b (algebraMap Coeff Base Witness.q)
      (algebraMap Coeff Base Witness.u) Θ) :
    Lambda Target →+* LaurentSeries ℚ :=
  (phiRegHom b Witness.isUnit_one_sub_q Witness.isUnit_v Witness.isUnit_one_sub_v_pow
      Witness.algebraMap_injective Witness.sp Witness.sp_u hΘ).comp
    (MvPolynomial.map (PowerSeries.C : Target →+* Coeff))

/-- That map is an evaluation map in the sense the chain asks for: on a weighted homogeneous
element of degree `n` it is the value read off any witness polynomial, which is the clause of the
multiplicativity statement about such an element. -/
theorem isEvaluationHom_phi {a b : ℕ} {Θ : Lambda Base →ₐ[Base] Module.End Base (Lambda Base)}
    (hΘ : IsSlopeHom a b (algebraMap Coeff Base Witness.q)
      (algebraMap Coeff Base Witness.u) Θ) :
    Assembly.IsEvaluationHom b Determinant.qVar (algebraMap Coeff Base Witness.u) Θ (phi hΘ) := by
  obtain ⟨-, -, -, -, hpoly⟩ := phiReg_isUnitalAlgHom Witness.isUnit_one_sub_q Witness.isUnit_v
    Witness.isUnit_one_sub_v_pow Witness.algebraMap_injective Witness.sp Witness.sp_u hΘ
  intro n f π hf hπ
  have hπ' : signExtract Base (Θ (coeffInc Coeff Base
        (MvPolynomial.map (PowerSeries.C : Target →+* Coeff) f)) 1)
      = polyValue π (algebraMap Coeff Base Witness.q) (algebraMap Coeff Base Witness.u) := by
    rw [coeffInc_map_C, polyValue_eq_aeval, ← algebraMap_qVar]; exact hπ
  rw [phi, RingHom.comp_apply, phiRegHom_apply,
    hpoly _ n π (isWeightedHomogeneous_map _ hf) hπ', Witness.sp_q, qOfInt_phiValue]

/-! ### The five conclusions -/

/-- `ℋ(z;q) = exp(∑_{k ≥ 1} r_k z^k / (k (1 - q^k)))`: the generating series of the finite
polynomials is the formal exponential of the series built from the evaluation coefficients, at a
slope homomorphism and an evaluation map which are exhibited rather than assumed. -/
@[hjo "lem_h_exponential"]
theorem exists_genH_eq_formalExp (rankOne : External.RankOneDinv)
    (goodTraverse : External.GoodTraverse) (coercivity : HJO.Literature.HuangCoercivity)
    (collinear : External.CollinearCommutation Base) (shuffle : External.Shuffle Base)
    (epsilonGessel : External.EpsilonGessel Base) {a b : ℕ} (hab : Nat.Coprime a b) (ha : 1 < a)
    (hb : a < b) :
    ∃ (Θ : Lambda Base →ₐ[Base] Module.End Base (Lambda Base))
      (Φ : Lambda Target →+* LaurentSeries ℚ),
      IsSlopeHom a b (algebraMap Coeff Base Witness.q) (algebraMap Coeff Base Witness.u) Θ ∧
        Assembly.IsEvaluationHom b Determinant.qVar (algebraMap Coeff Base Witness.u) Θ Φ ∧
          Determinant.genH a b = AExponential.formalExp
            (Endgame.coeffLog fun j => Φ (powerSum Target j) / (1 - Determinant.qVar ^ j)) := by
  obtain ⟨Θ, hΘ⟩ := Witness.exists_isSlopeHom collinear hab ha hb
  exact ⟨Θ, phi hΘ, hΘ, isEvaluationHom_phi hΘ,
    Assembly.genH_eq_formalExp rankOne goodTraverse coercivity shuffle epsilonGessel
      (realise Base) (isRealisation_realise Base) hab ha hb
      (Witness.algebraicIndependent_param (algebraMap Coeff Base) Witness.algebraMap_injective _
        algebraMap_qVar)
      (by rw [algebraMap_qVar]; exact hΘ) (isEvaluationHom_phi hΘ)⟩

/-- The generating series of the finite polynomials solves the common `q`-difference equation. -/
@[hjo "prop_hjo_equation"]
theorem isCommonSolution_genH (rankOne : External.RankOneDinv)
    (goodTraverse : External.GoodTraverse) (coercivity : HJO.Literature.HuangCoercivity)
    (collinear : External.CollinearCommutation Base) (shuffle : External.Shuffle Base)
    (epsilonGessel : External.EpsilonGessel Base)
    (creationExpansion : External.CreationExpansion Base) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 < a) (hb : a < b) :
    Determinant.IsCommonSolution a b (Determinant.genH a b) := by
  obtain ⟨Θ, hΘ⟩ := Witness.exists_isSlopeHom collinear hab ha hb
  exact Assembly.isCommonSolution_genH rankOne goodTraverse coercivity shuffle epsilonGessel
    creationExpansion (realise Base) (isRealisation_realise Base) hab ha hb
    (Witness.algebraicIndependent_param (algebraMap Coeff Base) Witness.algebraMap_injective _
      algebraMap_qVar) (by rw [algebraMap_qVar]; exact hΘ) (isEvaluationHom_phi hΘ)

/-- The scalar recurrence: the coefficientwise form of the common equation for the generating
series of the finite polynomials. -/
@[hjo "lem_recurrence"]
theorem finiteSeries_recurrence (rankOne : External.RankOneDinv)
    (goodTraverse : External.GoodTraverse) (coercivity : HJO.Literature.HuangCoercivity)
    (collinear : External.CollinearCommutation Base) (shuffle : External.Shuffle Base)
    (epsilonGessel : External.EpsilonGessel Base)
    (creationExpansion : External.CreationExpansion Base) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 < a) (hb : a < b) (N : ℕ) (hN : 0 < N) :
    (PowerSeries.X : PowerSeries ℤ) ^ Paths.gammaShift a b N * Gaps.finiteSeries a b N
      = ∑ j ∈ Icc 1 N, (-1 : PowerSeries ℤ) ^ (j + 1) * Paths.areaPoly a b j *
          PowerSeries.X ^ Paths.gammaShift a b (N - j) * Gaps.finiteSeries a b (N - j) *
          ∏ i ∈ Ico (N - j + 1) N, (1 - PowerSeries.X ^ i) :=
  Endgame.finiteSeries_recurrence (isCommonSolution_genH rankOne goodTraverse coercivity collinear
    shuffle epsilonGessel creationExpansion hab ha hb) N hN

/-- The finite identity `F_N(q) = (q)_N C_{𝐜,≤N}(q)`. -/
@[hjo "thm_finite"]
theorem finiteSeries_eq_qPochhammer_mul_boundedGF (rankOne : External.RankOneDinv)
    (goodTraverse : External.GoodTraverse) (coercivity : HJO.Literature.HuangCoercivity)
    (collinear : External.CollinearCommutation Base) (shuffle : External.Shuffle Base)
    (epsilonGessel : External.EpsilonGessel Base)
    (creationExpansion : External.CreationExpansion Base) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 < a) (hb : a < b) (N : ℕ) :
    Gaps.finiteSeries a b N
      = qPochhammer PowerSeries.X PowerSeries.X N * HJO.Cylindric.boundedGF a b N := by
  obtain ⟨Θ, hΘ⟩ := Witness.exists_isSlopeHom collinear hab ha hb
  exact Assembly.finiteSeries_eq_qPochhammer_mul_boundedGF rankOne goodTraverse coercivity shuffle
    epsilonGessel creationExpansion (realise Base) (isRealisation_realise Base) hab ha hb
    (Witness.algebraicIndependent_param (algebraMap Coeff Base) Witness.algebraMap_injective _
      algebraMap_qVar) (by rw [algebraMap_qVar]; exact hΘ) (isEvaluationHom_phi hΘ) N

/-- The Huang--Jiang--Oblomkov conjecture. -/
@[hjo "thm_main"]
theorem conjecture (rankOne : External.RankOneDinv) (goodTraverse : External.GoodTraverse)
    (coercivity : HJO.Literature.HuangCoercivity) (collinear : External.CollinearCommutation Base)
    (shuffle : External.Shuffle Base) (epsilonGessel : External.EpsilonGessel Base)
    (creationExpansion : External.CreationExpansion Base)
    (cylindricProduct : HJO.Literature.CylindricProduct) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 < a) (hb : a < b) : HJO.Conjecture a b := by
  obtain ⟨Θ, hΘ⟩ := Witness.exists_isSlopeHom collinear hab ha hb
  exact Assembly.conjecture rankOne goodTraverse coercivity shuffle epsilonGessel
    creationExpansion (realise Base) (isRealisation_realise Base) hab ha hb
    (Witness.algebraicIndependent_param (algebraMap Coeff Base) Witness.algebraMap_injective _
      algebraMap_qVar) (by rw [algebraMap_qVar]; exact hΘ) (isEvaluationHom_phi hΘ)
    cylindricProduct

end HJO.Final
