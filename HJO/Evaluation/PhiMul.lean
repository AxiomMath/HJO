/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import QSeriesLib.RingTheory.PowerSeries.Basic
public import HJO.Symmetric.DopCommutator
public import HJO.Evaluation.PhiPoly
public meta import HJO.Attr
public import HJO.Defs

/-! # The evaluation map as an algebra homomorphism, and the area series it exponentiates

A specialisation sending the second parameter to `1` cannot be a ring homomorphism out of the base
field: over a field the kernel is `0` or everything, so such a homomorphism forces the parameter to
be `1` there, and at that point the normalisation of the commutators defining the slope operators
vanishes and every slope operator of first index at least two with it. The specialisation therefore
has to be taken on a coefficient ring `R` mapping into the base field, and the evaluation map has to
be read on the symmetric functions with coefficients in `R`.

That is what this file does. For a symmetric function `f` with coefficients in `R`, the value on `1`
of the operator attached to `f` again has coefficients in `R`, because the operator lies in the
commutator filtration over `R`; sign extraction of that value is an element of `R`, and its image
under the specialisation is the evaluation of `f`, corrected by the sign carried by the scaling of
the alphabet by `(-1) ^ (b + 1)`. The resulting map is total, unital, additive, multiplicative and
semilinear over the specialisation, and on a weighted homogeneous element it is the value at the
specialised first parameter and `1` of any two-variable integer polynomial the sign extraction is a
value of, which is what the evaluation map is asked to be.

Multiplicativity is the one part that is not formal: applying a composite of operators to `1` is not
a product of values, and what makes it one after specialisation is that the operators lie in the
filtration over `R`, so that the specialisation kills every term of their expansion above the
constant one and leaves a multiplication operator.

Two consequences follow. Newton's identity for the elementary symmetric functions, carried along a
ring homomorphism, makes the generating series of the evaluated elementary symmetric functions the
formal exponential of the series built from the evaluated power sums; and the evaluated elementary
symmetric functions are the area polynomials of the below-diagonal paths, because the witness
polynomial of `e_N` is symmetric in its two variables and the symmetry descends to the coefficient
ring, where the specialisation is defined.

The last five sections are about non-vacuity. A realisation of the ring of symmetric functions in an
alphabet is constructed, and a coefficient ring is exhibited in which every hypothesis above holds
with both parameters generic: the power series in the deformation parameter over `ℚ((q))`, with the
specialisation the constant coefficient, the first parameter the variable of `ℚ((q))` and the second
`1` plus the deformation parameter. There `1 - u` is a nonzero non-unit while `1 - q`, `q u` and
`1 - q u` are units, the specialised first parameter satisfies no integral relation, and the basic
operators are not multiplication operators. The last of them states the two conclusions at that
model: the evaluation map is a ring homomorphism there, and the area generating series is the formal
exponential of the series built from its values on the power sums.
-/

@[expose] public section

open Finset

namespace HJO.PhiMul

open MvPolynomial HJO.Sym HJO.ReesRegular HJO.DopCommutator HJO.DiffOrder
open HJO.Multiplication HJO.UkRegular

/-! ### Transfer along a ring homomorphism of the coefficients -/

section Transfer

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The value of a two-variable integer polynomial at a pair of elements of a commutative ring: the
witness polynomial of a seed, read at the two parameters. -/
noncomputable def polyValue (π : MvPolynomial (Fin 2) ℤ) (x y : R) : R :=
  MvPolynomial.aeval ![x, y] π

/-- The value of a two-variable integer polynomial is its evaluation. -/
theorem polyValue_eq_aeval (π : MvPolynomial (Fin 2) ℤ) (x y : R) :
    polyValue π x y = MvPolynomial.aeval ![x, y] π := rfl

/-- A generator is carried to the corresponding generator by a coefficientwise ring
homomorphism. -/
theorem map_powerSum (hom : R →+* S) (k : ℕ) :
    MvPolynomial.map hom (powerSum R k) = powerSum S k := by
  rw [powerSum, powerSum, MvPolynomial.map_X]

/-- A diagonal substitution fixes the constants. -/
theorem diagScale_C (c : ℕ → R) (a : R) : diagScale c (C a : Lambda R) = C a := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

/-- A diagonal substitution multiplies the generator of index `i` by the scalar `c i`. -/
theorem diagScale_X (c : ℕ → R) (i : ℕ) :
    diagScale c (X i : Lambda R) = C (c i) * X i := by
  rw [diagScale, MvPolynomial.aeval_X]

/-- A diagonal substitution commutes with a coefficientwise ring homomorphism, the family of
scalars being carried along. -/
theorem map_diagScale (hom : R →+* S) (c : ℕ → R) (f : Lambda R) :
    MvPolynomial.map hom (diagScale c f)
      = diagScale (fun i => hom (c i)) (MvPolynomial.map hom f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp only [diagScale_C, MvPolynomial.map_C]
  | add p r hp hr => simp only [map_add, hp, hr]
  | mul_X p i hp =>
    simp only [map_mul, diagScale_X, MvPolynomial.map_C, MvPolynomial.map_X, hp]

/-- Evaluating a two-variable integer polynomial commutes with a ring homomorphism of the ring
the two arguments live in. -/
theorem map_aeval_fin2 (hom : R →+* S) (x y : R) (π : MvPolynomial (Fin 2) ℤ) :
    hom (MvPolynomial.aeval ![x, y] π) = MvPolynomial.aeval ![hom x, hom y] π := by
  induction π using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp only [map_add, hp, hr]
  | mul_X p i hp =>
    have hi : hom (![x, y] i) = ![hom x, hom y] i := by fin_cases i <;> simp
    simp only [map_mul, MvPolynomial.aeval_X, hp, hi]

/-- The value of a two-variable integer polynomial commutes with a ring homomorphism of the ring
the two arguments live in. -/
theorem map_polyValue (hom : R →+* S) (π : MvPolynomial (Fin 2) ℤ) (x y : R) :
    hom (polyValue π x y) = polyValue π (hom x) (hom y) := map_aeval_fin2 hom x y π

variable [Algebra ℚ R] [Algebra ℚ S]

/-- The complete homogeneous functions are carried to the complete homogeneous functions by a
coefficientwise ring homomorphism compatible with the rational scalars. -/
theorem map_completeHomog (hom : R →+* S)
    (hhom : ∀ x : ℚ, hom (algebraMap ℚ R x) = algebraMap ℚ S x) (n : ℕ) :
    MvPolynomial.map hom (completeHomog R n) = completeHomog S n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [completeHomog_zero, completeHomog_zero, map_one]
    | m + 1 =>
      rw [completeHomog_succ, completeHomog_succ, map_mul, MvPolynomial.map_C, hhom, map_sum]
      refine congrArg _ (Finset.sum_congr rfl fun k hk => ?_)
      rw [Finset.mem_range] at hk
      rw [map_mul, map_powerSum, ih (m - k) (by omega)]

/-- The elementary symmetric functions are carried to the elementary symmetric functions by a
coefficientwise ring homomorphism compatible with the rational scalars. -/
theorem map_elemSymm (hom : R →+* S)
    (hhom : ∀ x : ℚ, hom (algebraMap ℚ R x) = algebraMap ℚ S x) (n : ℕ) :
    MvPolynomial.map hom (elemSymm R n) = elemSymm S n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [PhiE.elemSymm_zero, PhiE.elemSymm_zero, map_one]
    | m + 1 =>
      rw [PhiE.elemSymm_succ, PhiE.elemSymm_succ, map_mul, MvPolynomial.map_C, hhom, map_sum]
      refine congrArg _ (Finset.sum_congr rfl fun k hk => ?_)
      rw [Finset.mem_range] at hk
      rw [map_mul, map_mul, map_pow, map_neg, map_one, map_powerSum, ih (m - k) (by omega)]

end Transfer

/-! ### The axis generators over the coefficient ring -/

section AxisGen

variable {R : Type*} [CommRing R] [Algebra ℚ R] {L : Type*} [Field L] [Algebra ℚ L]
  [Algebra R L] [IsScalarTower ℚ R L]

omit [Algebra ℚ R] [Algebra ℚ L] [IsScalarTower ℚ R L] in
/-- The coefficientwise inclusion fixes the constants, up to the structure map. -/
theorem coeffInc_C (a : R) : coeffInc R L (C a) = C (algebraMap R L a) := by
  rw [coeffInc_apply, MvPolynomial.map_C]

omit [Algebra ℚ R] [Algebra ℚ L] [IsScalarTower ℚ R L] in
/-- The coefficientwise inclusion commutes with a diagonal substitution. -/
theorem coeffInc_diagScale (c : ℕ → R) (f : Lambda R) :
    coeffInc R L (diagScale c f)
      = diagScale (fun i => algebraMap R L (c i)) (coeffInc R L f) := by
  rw [coeffInc_apply, coeffInc_apply, map_diagScale]

/-- The complete homogeneous functions over the coefficient ring are the complete homogeneous
functions. -/
theorem coeffInc_completeHomog (n : ℕ) :
    coeffInc R L (completeHomog R n) = completeHomog L n := by
  rw [coeffInc_apply]
  exact map_completeHomog _ (fun x => (IsScalarTower.algebraMap_apply ℚ R L x).symm) n

/-- The elementary symmetric functions over the coefficient ring are the elementary symmetric
functions. -/
theorem coeffInc_elemSymm (n : ℕ) : coeffInc R L (elemSymm R n) = elemSymm L n := by
  rw [coeffInc_apply]
  exact map_elemSymm _ (fun x => (IsScalarTower.algebraMap_apply ℚ R L x).symm) n

/-- The axis generators are defined over a coefficient ring in which the parameter `v` is a unit and
`1 - v ^ k` is a unit for every `k ≥ 1`, with the coefficient of `p_k` in `U_k` a unit there.

The prefactor `v / (v - 1)` needs the case `k = 1`. The virtual alphabet of the axis generators
attaches `v ^ (-k) - 1` to `p_k`, so what the coefficient of `p_k` in `U_k` needs is exactly the
case `k`: writing `w` for the inverse of `v`, `w ^ k - 1 = w ^ k * (1 - v ^ k)`, a product of units
precisely when `1 - v ^ k` is one. Nonvanishing would not do, the change of generators being
inverted over the ring rather than over a field; and no hypothesis on `v` alone would do either,
since at a `k`-th root of unity the coefficient is zero. -/
theorem exists_axisGen_reg {v : R} (hv : IsUnit v) (hv1 : ∀ j : ℕ, IsUnit (1 - v ^ (j + 1))) :
    ∃ Uk : ℕ → Lambda R,
      (∀ k, 0 < k → coeffInc R L (Uk k) = axisGen (algebraMap R L v) k) ∧
        ∀ m, IsUnit (coeff (Finsupp.single m 1) (Uk (m + 1))) := by
  obtain ⟨w, hw⟩ := hv.exists_right_inv
  have hv1' : IsUnit (1 - v) := by simpa using hv1 0
  obtain ⟨w', hw'⟩ := hv1'.exists_right_inv
  have hwu : IsUnit w := isUnit_iff_exists_inv.mpr ⟨v, by rw [mul_comm]; exact hw⟩
  have hwu' : IsUnit w' := isUnit_iff_exists_inv.mpr ⟨1 - v, by rw [mul_comm]; exact hw'⟩
  set vL : L := algebraMap R L v with hvL
  have hmapw : algebraMap R L w = vL⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [hvL, ← map_mul, mul_comm, hw, map_one]
  have hmapw' : algebraMap R L w' = (1 - vL)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    have h : algebraMap R L (w' * (1 - v)) = 1 := by rw [mul_comm, hw', map_one]
    rwa [map_mul, map_sub, map_one] at h
  refine ⟨fun k => C (-(v * w')) * diagScale (fun i => w ^ (i + 1) - 1) (completeHomog R k),
    fun k _ => ?_, fun m => ?_⟩
  · have h1 : algebraMap R L (-(v * w')) = vL / (vL - 1) := by
      rw [map_neg, map_mul, hmapw', div_eq_mul_inv, show vL - 1 = -(1 - vL) from by ring, inv_neg,
        mul_neg, ← hvL]
    have h2 : (fun i => algebraMap R L (w ^ (i + 1) - 1)) = fun i => (vL ^ (i + 1))⁻¹ - 1 := by
      funext i
      rw [map_sub, map_one, map_pow, hmapw, ← inv_pow]
    rw [map_mul, coeffInc_C, coeffInc_diagScale, coeffInc_completeHomog, axisGen,
      plethAxis_eq_diagScale, h1, h2]
  · rw [coeff_C_mul, coeff_single_diagScale, coeff_single_completeHomog]
    have hwv : w ^ (m + 1) * v ^ (m + 1) = 1 := by rw [← mul_pow, mul_comm, hw, one_pow]
    have hkey : w ^ (m + 1) - 1 = w ^ (m + 1) * (1 - v ^ (m + 1)) := by
      rw [mul_sub, mul_one, hwv]
    rw [hkey]
    refine ((hv.mul hwu').neg.mul ((((hwu.pow (m + 1)).mul (hv1 m))).mul ?_))
    refine IsUnit.map (algebraMap ℚ R) (isUnit_iff_ne_zero.2 ?_)
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    simpa using inv_ne_zero hm

/-- A slope homomorphism at `(a, b)` whose parameters are drawn from a coefficient ring in which
`1 - q`, `q u` and `1 - q u` are units takes every symmetric function with coefficients in that
ring into the commutator filtration over it. -/
theorem mem_reesRegComm_of_slopeHom {a b : ℕ} {q u : R} (hq : IsUnit (1 - q))
    (hv : IsUnit (q * u)) (hv1 : ∀ j : ℕ, IsUnit (1 - (q * u) ^ (j + 1)))
    (hinj : Function.Injective (algebraMap R L))
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b (algebraMap R L q) (algebraMap R L u) Θ) (f : Lambda R) :
    Θ (coeffInc R L f) ∈ ReesRegComm R L u := by
  obtain ⟨Uk, hUk, hUnit⟩ := exists_axisGen_reg (L := L) hv hv1
  refine mem_reesRegComm_of_isSlopeHom hq hinj Uk (fun k hk => ?_) hUnit hΘ f
  rw [hUk k hk, map_mul]

end AxisGen

/-! ### The evaluation over the coefficient ring -/

section EvalReg

variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L] {F : Type*} [CommRing F]

/-- The unsigned evaluation of a symmetric function `f` with coefficients in the coefficient ring:
the value on `1` of the operator attached to `f`, pulled back to a symmetric function over that
ring, its sign extracted there and the result specialised. -/
noncomputable def evalReg (sp : R →+* F) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L))
    (f : Lambda R) : F :=
  sp (signExtract R (Function.invFun (coeffInc R L) (Θ (coeffInc R L f) 1)))
/-- Whenever the value on `1` of the operator attached to `f` is exhibited over the coefficient
ring, the unsigned evaluation of `f` is the specialisation of its sign extraction; that witness is
unique, the coefficientwise inclusion being injective. -/
theorem evalReg_eq (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) {f g : Lambda R}
    (hg : Θ (coeffInc R L f) 1 = coeffInc R L g) : evalReg sp Θ f = sp (signExtract R g) := by
  rw [evalReg, hg, Function.leftInverse_invFun (coeffInc_injective hinj) g]
/-- The unsigned evaluation takes `1` to `1`, a slope homomorphism sending `1` to the identity. -/
theorem evalReg_one (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) : evalReg sp Θ (1 : Lambda R) = 1 := by
  have h : Θ (coeffInc R L (1 : Lambda R)) 1 = coeffInc R L (1 : Lambda R) := by
    simp only [map_one, Module.End.one_apply]
  rw [evalReg_eq hinj sp Θ h, map_one, map_one]
/-- The unsigned evaluation vanishes on `0`. -/
theorem evalReg_zero (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) : evalReg sp Θ (0 : Lambda R) = 0 := by
  have h : Θ (coeffInc R L (0 : Lambda R)) 1 = coeffInc R L (0 : Lambda R) := by
    simp only [map_zero, LinearMap.zero_apply]
  rw [evalReg_eq hinj sp Θ h, map_zero, map_zero]
/-- The unsigned evaluation is additive: the witnesses of the two summands add. -/
theorem evalReg_add (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) {u : R}
    (hmem : ∀ f : Lambda R, Θ (coeffInc R L f) ∈ ReesRegComm R L u) (f f' : Lambda R) :
    evalReg sp Θ (f + f') = evalReg sp Θ f + evalReg sp Θ f' := by
  obtain ⟨g, hg⟩ := exists_coeffInc_apply_one_reesRegComm (hmem f)
  obtain ⟨g', hg'⟩ := exists_coeffInc_apply_one_reesRegComm (hmem f')
  have h : Θ (coeffInc R L (f + f')) 1 = coeffInc R L (g + g') := by
    rw [map_add, map_add, LinearMap.add_apply, hg, hg', map_add]
  rw [evalReg_eq hinj sp Θ h, evalReg_eq hinj sp Θ hg, evalReg_eq hinj sp Θ hg', map_add, map_add]
/-- Constants are pulled out of the unsigned evaluation through the specialisation: the operator
attached to a constant multiple is that multiple of the operator. -/
theorem evalReg_C_mul (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) {u : R}
    (hmem : ∀ f : Lambda R, Θ (coeffInc R L f) ∈ ReesRegComm R L u) (c : R) (f : Lambda R) :
    evalReg sp Θ (C c * f) = sp c * evalReg sp Θ f := by
  obtain ⟨g, hg⟩ := exists_coeffInc_apply_one_reesRegComm (hmem f)
  have hC : coeffInc R L (C c * f) = C (algebraMap R L c) * coeffInc R L f := by
    rw [map_mul, coeffInc_apply, MvPolynomial.map_C]
  have hΘC : Θ (C (algebraMap R L c) * coeffInc R L f)
      = (algebraMap R L c) • Θ (coeffInc R L f) := by
    rw [map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]
  have h : Θ (coeffInc R L (C c * f)) 1 = coeffInc R L (c • g) := by
    rw [hC, hΘC, LinearMap.smul_apply, hg, map_smul]
    exact algebraMap_smul_eq c (coeffInc R L g)
  rw [evalReg_eq hinj sp Θ h, evalReg_eq hinj sp Θ hg, map_smul, smul_eq_mul, map_mul]
/-- The unsigned evaluation is multiplicative. The operator attached to a product is the composite
of the two operators, and applying a composite to `1` is a product of values only after
specialisation: that is what membership in the commutator filtration over `R` supplies. -/
theorem evalReg_mul (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) {u : R} (hsp : sp u = 1)
    (hmem : ∀ f : Lambda R, Θ (coeffInc R L f) ∈ ReesRegComm R L u) (f f' : Lambda R) :
    evalReg sp Θ (f * f') = evalReg sp Θ f * evalReg sp Θ f' := by
  obtain ⟨g, hg⟩ := exists_coeffInc_apply_one_reesRegComm (hmem f)
  obtain ⟨g', hg'⟩ := exists_coeffInc_apply_one_reesRegComm (hmem f')
  obtain ⟨G, hG, hmul⟩ := exists_map_eq_mul_of_mem_reesRegComm hinj sp hsp (hmem f) hg g'
  have h : Θ (coeffInc R L (f * f')) 1 = coeffInc R L G := by
    rw [map_mul, map_mul, Module.End.mul_apply, hg', hG]
  rw [evalReg_eq hinj sp Θ h, evalReg_eq hinj sp Θ hg, evalReg_eq hinj sp Θ hg',
    ← PhiE.signExtract_map, ← PhiE.signExtract_map, ← PhiE.signExtract_map, hmul, map_mul]

end EvalReg

section Phi

variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L] {F : Type*} [CommRing F]

/-- The evaluation map over the coefficient ring: the unsigned evaluation precomposed with the
scaling of the alphabet by `(-1) ^ (b + 1)`, which is what carries the sign `(-1) ^ (N (b + 1))` on
the component of degree `N`. -/
noncomputable def phiReg (b : ℕ) (sp : R →+* F) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L))
    (f : Lambda R) : F :=
  evalReg sp Θ (plethScale ((-1 : R) ^ (b + 1)) f)

variable (b : ℕ) (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
  (Θ : Lambda L →ₐ[L] Module.End L (Lambda L))

include hinj in
/-- The evaluation map is unital. -/
theorem phiReg_one : phiReg b sp Θ (1 : Lambda R) = 1 := by
  rw [phiReg, map_one, evalReg_one hinj sp Θ]

include hinj in
/-- The evaluation map vanishes on `0`. -/
theorem phiReg_zero : phiReg b sp Θ (0 : Lambda R) = 0 := by
  rw [phiReg, map_zero, evalReg_zero hinj sp Θ]

include hinj in
/-- The evaluation map is additive. -/
theorem phiReg_add {u : R} (hmem : ∀ f : Lambda R, Θ (coeffInc R L f) ∈ ReesRegComm R L u)
    (f g : Lambda R) : phiReg b sp Θ (f + g) = phiReg b sp Θ f + phiReg b sp Θ g := by
  rw [phiReg, phiReg, phiReg, map_add, evalReg_add hinj sp Θ hmem]

include hinj in
/-- The evaluation map is multiplicative. The sign needs no homogeneity hypothesis: it is the effect
of an algebra endomorphism of the ring of symmetric functions. -/
theorem phiReg_mul {u : R} (hsp : sp u = 1)
    (hmem : ∀ f : Lambda R, Θ (coeffInc R L f) ∈ ReesRegComm R L u) (f g : Lambda R) :
    phiReg b sp Θ (f * g) = phiReg b sp Θ f * phiReg b sp Θ g := by
  rw [phiReg, phiReg, phiReg, map_mul, evalReg_mul hinj sp Θ hsp hmem]

include hinj in
/-- Constants are pulled out of the evaluation map through the specialisation. -/
theorem phiReg_C_mul {u : R} (hmem : ∀ f : Lambda R, Θ (coeffInc R L f) ∈ ReesRegComm R L u)
    (c : R) (f : Lambda R) : phiReg b sp Θ (C c * f) = sp c * phiReg b sp Θ f := by
  rw [phiReg, phiReg, ← MvPolynomial.smul_eq_C_mul, map_smul, MvPolynomial.smul_eq_C_mul,
    evalReg_C_mul hinj sp Θ hmem]

include hinj in
/-- On a weighted homogeneous element of degree `n` the evaluation map is a single unsigned
evaluation, corrected by the sign `(-1) ^ (n (b + 1))`. -/
theorem phiReg_of_isWeightedHomogeneous {u : R}
    (hmem : ∀ f : Lambda R, Θ (coeffInc R L f) ∈ ReesRegComm R L u) {f : Lambda R} {n : ℕ}
    (hf : IsWeightedHomogeneous degWeight f n) :
    phiReg b sp Θ f = (-1) ^ (n * (b + 1)) * evalReg sp Θ f := by
  rw [phiReg, PhiE.plethScale_of_isWeightedHomogeneous hf, evalReg_C_mul hinj sp Θ hmem,
    ← pow_mul, mul_comm (b + 1) n, map_pow, map_neg, map_one]

end Phi

/-! ### The evaluation map is a unital algebra homomorphism -/

section Hom

variable {R : Type*} [CommRing R] [Algebra ℚ R] {L : Type*} [Field L] [Algebra ℚ L]
  [Algebra R L] [IsScalarTower ℚ R L] {F : Type*} [CommRing F]

omit [Algebra ℚ R] [Algebra ℚ L] [IsScalarTower ℚ R L] in
/-- The value of the unsigned evaluation read off a witness polynomial: if sign extraction on the
operator attached to `f`, applied to `1`, is the value of a two-variable integer polynomial at the
two parameters, then the unsigned evaluation of `f` is the value of that polynomial at the
specialised first parameter and `1`. -/
theorem evalReg_eq_aeval (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) {u : R}
    (hmem : ∀ f : Lambda R, Θ (coeffInc R L f) ∈ ReesRegComm R L u) (hsp : sp u = 1) {q : R}
    {f : Lambda R} {π : MvPolynomial (Fin 2) ℤ}
    (hπ : signExtract L (Θ (coeffInc R L f) 1)
      = polyValue π (algebraMap R L q) (algebraMap R L u)) :
    evalReg sp Θ f = polyValue π (sp q) 1 := by
  obtain ⟨g, hg⟩ := exists_coeffInc_apply_one_reesRegComm (hmem f)
  have hgR : signExtract R g = polyValue π q u := by
    refine hinj ?_
    have h1 : algebraMap R L (signExtract R g) = signExtract L (coeffInc R L g) := by
      rw [coeffInc_apply, PhiE.signExtract_map]
    rw [h1, ← hg, hπ, map_polyValue]
  rw [evalReg_eq hinj sp Θ hg, hgR, map_polyValue sp π q u, hsp]

/-- The evaluation map attached to a slope homomorphism whose parameters are drawn from the
coefficient ring, bundled as a ring homomorphism from the symmetric functions over that ring to
the target of the specialisation. -/
noncomputable def phiRegHom (b : ℕ) {a : ℕ} {q u : R} (hq : IsUnit (1 - q)) (hv : IsUnit (q * u))
    (hv1 : ∀ j : ℕ, IsUnit (1 - (q * u) ^ (j + 1)))
    (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    (hsp : sp u = 1) {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b (algebraMap R L q) (algebraMap R L u) Θ) : Lambda R →+* F where
  toFun := phiReg b sp Θ
  map_one' := phiReg_one b hinj sp Θ
  map_mul' := phiReg_mul b hinj sp Θ hsp (mem_reesRegComm_of_slopeHom hq hv hv1 hinj hΘ)
  map_zero' := phiReg_zero b hinj sp Θ
  map_add' := phiReg_add b hinj sp Θ (mem_reesRegComm_of_slopeHom hq hv hv1 hinj hΘ)

/-- The bundled evaluation map is the evaluation map. -/
@[simp] theorem phiRegHom_apply (b : ℕ) {a : ℕ} {q u : R} (hq : IsUnit (1 - q))
    (hv : IsUnit (q * u)) (hv1 : ∀ j : ℕ, IsUnit (1 - (q * u) ^ (j + 1)))
    (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F) (hsp : sp u = 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b (algebraMap R L q) (algebraMap R L u) Θ) (f : Lambda R) :
    phiRegHom b hq hv hv1 hinj sp hsp hΘ f = phiReg b sp Θ f := rfl

/-- For a slope homomorphism at `(a, b)` whose parameters are drawn from a coefficient ring in
which `1 - q`, `q u` and `1 - q u` are units, and a specialisation of that ring sending the second
parameter to `1`, the evaluation map on the symmetric functions with coefficients in that ring is
unital, additive, multiplicative and semilinear over the specialisation of the scalars; and on a
weighted homogeneous element of degree `n` it is the value at the specialised first parameter and
`1` of any two-variable integer polynomial whose value at the two parameters is the scalar obtained
by sign extraction, corrected by the sign `(-1) ^ (n (b + 1))`. -/
@[hjo "prop_phi_hom"]
theorem phiReg_isUnitalAlgHom {a b : ℕ} {q u : R} (hq : IsUnit (1 - q)) (hv : IsUnit (q * u))
    (hv1 : ∀ j : ℕ, IsUnit (1 - (q * u) ^ (j + 1)))
    (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    (hsp : sp u = 1) {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b (algebraMap R L q) (algebraMap R L u) Θ) :
    phiReg b sp Θ (1 : Lambda R) = 1 ∧
      (∀ f g : Lambda R, phiReg b sp Θ (f + g) = phiReg b sp Θ f + phiReg b sp Θ g) ∧
      (∀ f g : Lambda R, phiReg b sp Θ (f * g) = phiReg b sp Θ f * phiReg b sp Θ g) ∧
      (∀ (c : R) (f : Lambda R), phiReg b sp Θ (C c * f) = sp c * phiReg b sp Θ f) ∧
      (∀ (f : Lambda R) (n : ℕ) (π : MvPolynomial (Fin 2) ℤ),
        IsWeightedHomogeneous degWeight f n →
        signExtract L (Θ (coeffInc R L f) 1) = polyValue π (algebraMap R L q) (algebraMap R L u) →
          phiReg b sp Θ f = (-1) ^ (n * (b + 1)) * polyValue π (sp q) 1) := by
  have hmem := mem_reesRegComm_of_slopeHom hq hv hv1 hinj hΘ
  refine ⟨phiReg_one b hinj sp Θ, phiReg_add b hinj sp Θ hmem, phiReg_mul b hinj sp Θ hsp hmem,
    phiReg_C_mul b hinj sp Θ hmem, fun f n π hf hπ => ?_⟩
  rw [phiReg_of_isWeightedHomogeneous b hinj sp Θ hmem hf,
    evalReg_eq_aeval hinj sp Θ hmem hsp hπ]

/-- The evaluation coefficient `r_k` is defined at every index, and no witness polynomial is needed
for it: the value on `1` of the operator attached to a generator has coefficients in the coefficient
ring, and `r_k` is the specialisation of its sign extraction. This is a well-definedness claim about
`r_k`, stated for the record. -/
theorem exists_phiReg_powerSum {a b : ℕ} {q u : R} (hq : IsUnit (1 - q)) (hv : IsUnit (q * u))
    (hv1 : ∀ j : ℕ, IsUnit (1 - (q * u) ^ (j + 1)))
    (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b (algebraMap R L q) (algebraMap R L u) Θ) (k : ℕ) :
    ∃ g : Lambda R,
      Θ (coeffInc R L (plethScale ((-1 : R) ^ (b + 1)) (powerSum R k))) 1 = coeffInc R L g ∧
        phiReg b sp Θ (powerSum R k) = sp (signExtract R g) := by
  obtain ⟨g, hg⟩ := exists_coeffInc_apply_one_reesRegComm
    (mem_reesRegComm_of_slopeHom hq hv hv1 hinj hΘ (plethScale ((-1 : R) ^ (b + 1)) (powerSum R k)))
  exact ⟨g, hg, by rw [phiReg, evalReg_eq hinj sp Θ hg]⟩

end Hom

/-! ### The area generating series as an exponential -/

section AExp

variable {a b : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R] {L : Type*} [Field L] [Algebra ℚ L]
  [Algebra R L] [IsScalarTower ℚ R L] {F : Type*} [CommRing F] [Algebra ℚ F]

/-- The generating series of the images of the elementary symmetric functions under the evaluation
map is the formal exponential of the series built from the evaluation coefficients: the evaluation
map is a ring homomorphism, so it carries Newton's identity for the elementary symmetric functions
to the logarithmic derivative of that generating series. -/
theorem mk_phiReg_elemSymm_eq_formalExp {q u : R} (hq : IsUnit (1 - q)) (hv : IsUnit (q * u))
    (hv1 : ∀ j : ℕ, IsUnit (1 - (q * u) ^ (j + 1)))
    (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    (hsp : sp u = 1) {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b (algebraMap R L q) (algebraMap R L u) Θ) :
    (PowerSeries.mk fun n => phiReg b sp Θ (elemSymm R n))
      = AExponential.formalExp (AExponential.logSeries fun k => phiReg b sp Θ (powerSum R k)) := by
  refine AExponential.eq_formalExp_logSeries ?_ ?_
  · have h := AExponential.derivative_mk_elemSymm (K := R) (R := F)
      (phiRegHom b hq hv hv1 hinj sp hsp hΘ)
    simpa only [phiRegHom_apply] using h
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_mk,
      PhiE.elemSymm_zero, phiReg_one b hinj sp Θ]

omit [Algebra ℚ F] in
/-- The evaluation map takes the elementary symmetric function `e_N` to the area generating
polynomial of the below-diagonal `(aN, bN)`-paths at the specialised first parameter. The witness
polynomial of `e_N` is symmetric in its two variables; the symmetry descends to the coefficient
ring, where the specialisation is defined, and there it exchanges the hook count for the area. -/
theorem phiReg_elemSymm_eq_sum_area {N : ℕ} {q u : R} (hq : IsUnit (1 - q)) (hv : IsUnit (q * u))
    (hv1 : ∀ j : ℕ, IsUnit (1 - (q * u) ^ (j + 1)))
    (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    (hsp : sp u = 1) {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b (algebraMap R L q) (algebraMap R L u) Θ) (shuffle : External.Shuffle L)
    (epsilonGessel : External.EpsilonGessel L) (creationExpansion : External.CreationExpansion L)
    (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b)
    (hqu : AlgebraicIndependent ℤ ![algebraMap R L q, algebraMap R L u])
    (ι : Lambda L →ₐ[L] AlphabetSeries L)
    (hι : IsRealisation ι) (hN : 0 < N) :
    phiReg b sp Θ (elemSymm R N) =
      ∑ y ∈ (univ : Finset (Paths.Heights a b N)) with Paths.IsBelowDiagonal y,
        sp q ^ Paths.area y := by
  have hgs : ThetaSymmetry.GesselSelection L := epsilonGessel
  obtain ⟨hval, hswap⟩ := ThetaSymmetry.signExtract_elemSymm_isPoly_and_swap
    (shuffle a b hab ha hb (algebraMap R L q) (algebraMap R L u) hqu)
    (shuffle a b hab ha hb (algebraMap R L u) (algebraMap R L q)
      (ThetaSymmetry.algebraicIndependent_swap hqu)) hgs ι hι Θ hΘ (by omega)
    (by omega) hN (creationExpansion (algebraMap R L q) N hN)
    (creationExpansion (algebraMap R L u) N hN)
  have hmem := mem_reesRegComm_of_slopeHom hq hv hv1 hinj hΘ
  have hval' : signExtract L (Θ (coeffInc R L (elemSymm R N)) 1)
      = MvPolynomial.aeval ![algebraMap R L q, algebraMap R L u]
        (ThetaSymmetry.signedPathPoly a b N) := by
    rw [coeffInc_elemSymm]
    exact hval
  have hswapR : MvPolynomial.aeval ![q, u] (ThetaSymmetry.signedPathPoly a b N)
      = MvPolynomial.aeval ![u, q] (ThetaSymmetry.signedPathPoly a b N) := by
    refine hinj ?_
    rw [map_aeval_fin2, map_aeval_fin2]
    exact hswap
  have hspswap : MvPolynomial.aeval ![sp q, 1] (ThetaSymmetry.signedPathPoly a b N)
      = MvPolynomial.aeval ![1, sp q] (ThetaSymmetry.signedPathPoly a b N) := by
    have h := congrArg sp hswapR
    rwa [map_aeval_fin2, map_aeval_fin2, hsp] at h
  rw [phiReg_of_isWeightedHomogeneous b hinj sp Θ hmem (PhiE.isWeightedHomogeneous_elemSymm R N),
    evalReg_eq_aeval hinj sp Θ hmem hsp hval', polyValue_eq_aeval, hspswap,
    ThetaSymmetry.aeval_signedPathPoly, ThetaSymmetry.aeval_pathPoly, ← mul_assoc, ← pow_add,
    Even.neg_one_pow ⟨_, rfl⟩, one_mul]
  exact Finset.sum_congr rfl fun y _ => by rw [one_pow, one_mul]

omit [Algebra ℚ F] in
/-- The same evaluation read off the area polynomial itself, along any specialisation of the
integral power series carrying the variable to the specialised first parameter. -/
theorem phiReg_elemSymm_eq_areaPoly {N : ℕ} {q u : R} (hq : IsUnit (1 - q)) (hv : IsUnit (q * u))
    (hv1 : ∀ j : ℕ, IsUnit (1 - (q * u) ^ (j + 1)))
    (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    (hsp : sp u = 1) {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b (algebraMap R L q) (algebraMap R L u) Θ) (shuffle : External.Shuffle L)
    (epsilonGessel : External.EpsilonGessel L) (creationExpansion : External.CreationExpansion L)
    (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b)
    (hqu : AlgebraicIndependent ℤ ![algebraMap R L q, algebraMap R L u])
    (ι : Lambda L →ₐ[L] AlphabetSeries L)
    (hι : IsRealisation ι) (hN : 0 < N) (g : PowerSeries ℤ →+* F) (hg : g PowerSeries.X = sp q) :
    phiReg b sp Θ (elemSymm R N) = g (Paths.areaPoly a b N) := by
  rw [phiReg_elemSymm_eq_sum_area hq hv hv1 hinj sp hsp hΘ shuffle epsilonGessel creationExpansion
    hab ha hb hqu ι hι hN, Paths.areaPoly, map_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [map_pow, hg]

end AExp

/-! ### The area generating series in the field of `q`-Laurent series -/

section GenA

/-- `𝒜(z;q) = exp(∑_{k ≥ 1} (-1)^{k-1} rₖ zᵏ / k)`. For a slope homomorphism at `(a, b)` whose
parameters are drawn from a coefficient ring, with a specialisation of that ring sending the second
parameter to `1` and the first to the variable of `ℚ((q))`, the area generating series is the formal
exponential of the series built from the evaluation coefficients `rₖ` of the power sums. -/
@[hjo "lem_a_exponential"]
theorem genA_eq_formalExp {a b : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R] {L : Type*} [Field L]
    [Algebra ℚ L] [Algebra R L] [IsScalarTower ℚ R L] {q u : R} (hq : IsUnit (1 - q))
    (hv : IsUnit (q * u)) (hv1 : ∀ j : ℕ, IsUnit (1 - (q * u) ^ (j + 1)))
    (hinj : Function.Injective (algebraMap R L))
    (sp : R →+* LaurentSeries ℚ) (hsp : sp u = 1) (hspq : sp q = Determinant.qVar)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b (algebraMap R L q) (algebraMap R L u) Θ) (shuffle : External.Shuffle L)
    (epsilonGessel : External.EpsilonGessel L) (creationExpansion : External.CreationExpansion L)
    (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b)
    (hqu : AlgebraicIndependent ℤ ![algebraMap R L q, algebraMap R L u])
    (ι : Lambda L →ₐ[L] AlphabetSeries L)
    (hι : IsRealisation ι) :
    Determinant.genA a b
      = AExponential.formalExp (AExponential.logSeries fun k => phiReg b sp Θ (powerSum R k)) := by
  rw [← mk_phiReg_elemSymm_eq_formalExp hq hv hv1 hinj sp hsp hΘ]
  refine PowerSeries.ext fun n => ?_
  rw [Determinant.genA, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  match n with
  | 0 => rw [AExponential.areaPoly_zero, map_one, PhiE.elemSymm_zero, phiReg_one b hinj sp Θ]
  | m + 1 =>
    rw [phiReg_elemSymm_eq_areaPoly hq hv hv1 hinj sp hsp hΘ shuffle epsilonGessel
      creationExpansion hab ha hb hqu ι hι (Nat.succ_pos m) Determinant.qOfInt
      (by rw [hspq, Determinant.qVar])]

end GenA

/-! ### A realisation of the ring of symmetric functions in an alphabet -/

section Realisation

variable (K : Type*) [CommRing K]

/-- The power sum `∑ᵢ xᵢ ^ k` of the alphabet, as a power series: the monomials occurring are
exactly the `k`-th powers of the letters, each with coefficient `1`. -/
noncomputable def alphabetPowerSum (k : ℕ) : AlphabetSeries K :=
  Set.indicator {d : ℕ →₀ ℕ | ∃ i, d = Finsupp.single i k} 1

/-- The `k`-th power of a letter occurs in the `k`-th power sum with coefficient `1`. -/
theorem coeff_alphabetPowerSum_single (k i : ℕ) :
    MvPowerSeries.coeff (Finsupp.single i k) (alphabetPowerSum K k) = (1 : K) := by
  have hmem : (Finsupp.single i k) ∈ {d : ℕ →₀ ℕ | ∃ j, d = Finsupp.single j k} := ⟨i, rfl⟩
  rw [MvPowerSeries.coeff_apply, alphabetPowerSum, Set.indicator_of_mem hmem]
  rfl

/-- No other monomial occurs in the `k`-th power sum. -/
theorem coeff_alphabetPowerSum_of_ne (k : ℕ) (d : ℕ →₀ ℕ) (hd : ∀ i, d ≠ Finsupp.single i k) :
    MvPowerSeries.coeff d (alphabetPowerSum K k) = (0 : K) := by
  rw [MvPowerSeries.coeff_apply, alphabetPowerSum, Set.indicator_of_notMem]
  rintro ⟨i, rfl⟩
  exact hd i rfl

/-- The realisation of the ring of symmetric functions in the alphabet: the algebra homomorphism
sending the generator `p_k` to the power sum `∑ᵢ xᵢ ^ k`. -/
noncomputable def realise : Lambda K →ₐ[K] AlphabetSeries K :=
  MvPolynomial.aeval fun i => alphabetPowerSum K (i + 1)

/-- The realisation is a realisation: it sends each generator to the actual power sum of the
alphabet, so the hypotheses of the external inputs about a realisation are satisfiable. -/
theorem isRealisation_realise : IsRealisation (realise K) := by
  constructor
  · intro k i
    rw [realise, powerSum, Nat.add_sub_cancel, MvPolynomial.aeval_X,
      coeff_alphabetPowerSum_single]
  · intro k d hd
    rw [realise, powerSum, Nat.add_sub_cancel, MvPolynomial.aeval_X,
      coeff_alphabetPowerSum_of_ne _ _ _ hd]

end Realisation

/-! ### The coefficient ring is available with both parameters generic -/

namespace Witness

/-- The specialisation: the constant coefficient in the deformation parameter, a ring homomorphism
onto `ℚ((q))` whose kernel is the ideal generated by that parameter. -/
noncomputable def sp : Coeff →+* Target := PowerSeries.constantCoeff

/-- The first parameter, the variable of `ℚ((q))` viewed as a constant of the coefficient ring; the
specialisation leaves it alone. -/
noncomputable def q : Coeff := PowerSeries.C Determinant.qVar

/-- The second parameter, `1` plus the deformation parameter: a unit of the coefficient ring which
the specialisation sends to `1`, while `1 - u` is a nonzero non-unit there. -/
noncomputable def u : Coeff := 1 + PowerSeries.X

/-- The inclusion of the integral power series in one variable into `ℚ((q))` is injective, so the
image of the variable is transcendental: no nonzero integral relation holds there. -/
theorem qOfInt_injective : Function.Injective Determinant.qOfInt := by
  have h1 : Function.Injective (PowerSeries.map (Int.castRingHom ℚ)) :=
    PowerSeries.map_injective (Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int
  have h2 : Function.Injective (HahnSeries.ofPowerSeries ℤ ℚ) :=
    HahnSeries.ofPowerSeries_injective
  intro x y hxy
  exact h1 (h2 hxy)

/-- The variable of `ℚ((q))` is nonzero. -/
theorem qVar_ne_zero : Determinant.qVar ≠ 0 := fun h => by
  have hx : (PowerSeries.X : PowerSeries ℤ) = 0 := by
    refine qOfInt_injective ?_
    rw [← Determinant.qVar, h, map_zero]
  exact PowerSeries.X_ne_zero hx

/-- The variable of `ℚ((q))` is not `1`. -/
theorem qVar_ne_one : Determinant.qVar ≠ 1 := fun h => by
  have hx : (PowerSeries.X : PowerSeries ℤ) = 1 := by
    refine qOfInt_injective ?_
    rw [← Determinant.qVar, h, map_one]
  simpa using congrArg (PowerSeries.coeff 0) hx

/-- The structure map of the coefficient ring into the base field is injective. -/
theorem algebraMap_injective : Function.Injective (algebraMap Coeff Base) :=
  IsFractionRing.injective Coeff Base

/-- The specialisation sends the second parameter to `1`. -/
@[simp] theorem sp_u : sp u = 1 := by simp [sp, u]

/-- The specialisation leaves the first parameter alone. -/
@[simp] theorem sp_q : sp q = Determinant.qVar := by simp [sp, q]

/-- The complement of the first parameter is a unit of the coefficient ring, so the normalisation
of a commutator does not leave that ring. -/
theorem isUnit_one_sub_q : IsUnit (1 - q) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_sub, map_one, q, PowerSeries.constantCoeff_C]
  exact isUnit_iff_ne_zero.2 (sub_ne_zero_of_ne (Ne.symm qVar_ne_one))

/-- The parameter of the axis generators is a unit of the coefficient ring. -/
theorem isUnit_v : IsUnit (q * u) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_mul, q, u, map_add, map_one, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X, add_zero, mul_one]
  exact isUnit_iff_ne_zero.2 qVar_ne_zero

/-- The complement of the parameter of the axis generators is a unit of the coefficient ring, so
the prefactor of an axis generator is defined there. -/
theorem isUnit_one_sub_v : IsUnit (1 - q * u) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_sub, map_mul, map_one, q, u, map_add, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X, add_zero, mul_one]
  exact isUnit_iff_ne_zero.2 (sub_ne_zero_of_ne (Ne.symm qVar_ne_one))

/-- An element of the coefficient ring whose constant term is a unit of `ℚ((q))` is a unit: the
coefficient ring is a power series ring, hence local, with the vanishing of the constant term as its
maximal ideal. This is the criterion that turns nonvanishing in `ℚ((q))` into invertibility over the
ring, which is what inverting the triangular change of generators there requires. -/
theorem isUnit_of_sp {f : Coeff} (h : IsUnit (sp f)) : IsUnit f :=
  PowerSeries.isUnit_iff_constantCoeff.2 h

/-- The specialisation sends the parameter of the axis generators to the variable of `ℚ((q))`. -/
@[simp] theorem sp_v : sp (q * u) = Determinant.qVar := by rw [map_mul, sp_q, sp_u, mul_one]

/-- The geometric sums `1 + q + ⋯ + q ^ k` are nonzero in `ℚ((q))`: the corresponding integral power
series has constant coefficient `1`, and the inclusion of the integral power series is injective. -/
theorem geomSum_qVar_ne_zero (k : ℕ) :
    (∑ j ∈ range (k + 1), Determinant.qVar ^ j) ≠ 0 := by
  have hsum : (∑ j ∈ range (k + 1), Determinant.qVar ^ j)
      = Determinant.qOfInt (∑ j ∈ range (k + 1), (PowerSeries.X : PowerSeries ℤ) ^ j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_pow, ← Determinant.qVar]
  rw [hsum]
  intro h
  have hx : (∑ j ∈ range (k + 1), (PowerSeries.X : PowerSeries ℤ) ^ j) = 0 :=
    qOfInt_injective (by rw [h, map_zero])
  have h0 := congrArg (PowerSeries.coeff 0) hx
  simp [PowerSeries.coeff_X_pow] at h0

/-- **The geometric sums in the parameter of the axis generators are units of the coefficient
ring.** Their constant terms are the sums `1 + q + ⋯ + q ^ k` in `ℚ((q))`, which are nonzero because
the variable there is transcendental over `ℚ`; the power-series unit criterion upgrades that to
invertibility. -/
theorem isUnit_geomSum (k : ℕ) : IsUnit (∑ j ∈ range (k + 1), (q * u) ^ j) := by
  refine isUnit_of_sp (isUnit_iff_ne_zero.2 ?_)
  rw [map_sum, Finset.sum_congr rfl fun j _ => by rw [map_pow, sp_v]]
  exact geomSum_qVar_ne_zero k

/-- **The complement `1 - v ^ k` of every positive power of the parameter of the axis generators is
a unit of the coefficient ring.** This is the hypothesis that the corrected virtual alphabet of the
axis generators needs, and it follows from the previous two lemmas:
`1 - v ^ (k+1) = (1 - v) * (1 + v + ⋯ + v ^ k)`, a product of units. -/
theorem isUnit_one_sub_v_pow (k : ℕ) : IsUnit (1 - (q * u) ^ (k + 1)) := by
  have hgeom : (1 - q * u) * ∑ j ∈ range (k + 1), (q * u) ^ j = 1 - (q * u) ^ (k + 1) := by
    have h := geom_sum_mul (q * u) (k + 1)
    linear_combination -h
  rw [← hgeom]
  exact isUnit_one_sub_v.mul (isUnit_geomSum k)

/-- The second parameter is not `1`: the specialisation sends it there while it is a nontrivial
power series, so its kernel is nonzero and no collapse follows. -/
theorem u_ne_one : u ≠ 1 := fun h => by
  have hx : (PowerSeries.X : Coeff) = 0 := by
    have h1 : (1 : Coeff) + PowerSeries.X = 1 + 0 := by rw [add_zero]; exact h
    exact add_left_cancel h1
  exact PowerSeries.X_ne_zero hx

/-- The second parameter is not `1` in the base field either. -/
theorem algebraMap_u_ne_one : algebraMap Coeff Base u ≠ 1 := fun h =>
  u_ne_one (algebraMap_injective (by rw [h, map_one]))

/-- The deformation parameter `ℏ = 1 - u` is nonzero in the base field, so the operators are not
read at a point where the normalisation of every commutator vanishes. -/
theorem one_sub_algebraMap_u_ne_zero : (1 : Base) - algebraMap Coeff Base u ≠ 0 := fun h =>
  algebraMap_u_ne_one (eq_of_sub_eq_zero h).symm

/-- The parameter of the axis generators is nonzero in the base field. -/
theorem algebraMap_v_ne_zero :
    algebraMap Coeff Base q * algebraMap Coeff Base u ≠ 0 := fun h => by
  have h1 : q * u = 0 := algebraMap_injective (by rw [map_mul, h, map_zero])
  have h2 := isUnit_v
  rw [h1] at h2
  exact not_isUnit_zero h2

/-- The parameter of the axis generators is not `1` in the base field. -/
theorem algebraMap_v_ne_one :
    algebraMap Coeff Base q * algebraMap Coeff Base u ≠ 1 := fun h => by
  have h1 : q * u = 1 := algebraMap_injective (by rw [map_mul, h, map_one])
  have h2 := isUnit_one_sub_v
  rw [h1, sub_self] at h2
  exact not_isUnit_zero h2

/-- The parameter of the axis generators is not a root of unity in the base field: no positive power
of it is `1`. This is the hypothesis of the corrected triangularity statement, and it is strictly
stronger than avoiding `0` and `1`. -/
theorem algebraMap_v_pow_ne_one (j : ℕ) :
    (algebraMap Coeff Base q * algebraMap Coeff Base u) ^ (j + 1) ≠ 1 := fun h => by
  have h1 : (q * u) ^ (j + 1) = 1 :=
    algebraMap_injective (by rw [map_pow, map_mul, h, map_one])
  have h2 := isUnit_one_sub_v_pow j
  rw [h1, sub_self] at h2
  exact not_isUnit_zero h2

/-- **The triangularity hypotheses of the specialisation theorem are satisfied at the parameters of
this model.** The parameter of the axis generators is nonzero there and not a root of unity, which
is what the corrected virtual alphabet needs, so the axis generators do form a triangular change of
generators with invertible leading coefficients and the hypotheses of
`HJO.DopCommutator.slopeHom_specialisation` are not vacuous. -/
theorem exists_axisGen_witness :
    ∃ Uk : ℕ → Lambda Base,
      (∀ k, 0 < k → coeffInc Base Base (Uk k) =
        axisGen (algebraMap Coeff Base q * algebraMap Coeff Base u) k) ∧
        ∀ m, IsUnit (coeff (Finsupp.single m 1) (Uk (m + 1))) :=
  HJO.DopCommutator.Witness.exists_axisGen_witness algebraMap_v_ne_zero algebraMap_v_pow_ne_one

/-- A monomial power series is the constant times a power of the variable. -/
theorem C_mul_X_pow_eq_monomial (a : ℚ) (n : ℕ) :
    PowerSeries.C a * PowerSeries.X ^ n = PowerSeries.monomial n a := by
  ext m
  rw [PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_monomial]

/-- The variable of `ℚ((q))` is the image of the variable of the rational power series. -/
theorem qVar_eq_ofPowerSeries :
    Determinant.qVar = HahnSeries.ofPowerSeries ℤ ℚ PowerSeries.X := by
  rw [Determinant.qVar, Determinant.qOfInt]
  simp

/-- A rational polynomial evaluated at the variable of `ℚ((q))` is the image of that polynomial. -/
theorem aeval_qVar (p : Polynomial ℚ) :
    Polynomial.aeval Determinant.qVar p = HahnSeries.ofPowerSeries ℤ ℚ (p : PowerSeries ℚ) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add, Polynomial.coe_add, map_add, hp, hr]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.coe_monomial, qVar_eq_ofPowerSeries,
      HahnSeries.algebraMap_apply' ℤ (R := ℚ) (S := ℚ) a, PowerSeries.algebraMap_apply,
      ← map_pow, ← map_mul, C_mul_X_pow_eq_monomial, Algebra.algebraMap_self_apply]

/-- The variable of `ℚ((q))` is transcendental over `ℚ`: a rational polynomial vanishing there is
the zero polynomial, the passage from polynomials to Laurent series being injective. -/
theorem transcendental_qVar : Transcendental ℚ Determinant.qVar := by
  rw [Transcendental, IsAlgebraic]
  rintro ⟨p, hp, hp0⟩
  rw [aeval_qVar] at hp0
  refine hp (Polynomial.coe_injective ℚ
    (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ) ?_))
  rw [hp0, Polynomial.coe_zero, map_zero]

/-- The specialised first parameter is transcendental over `ℚ`, so the specialisation keeps that
parameter generic instead of collapsing it to a number. -/
theorem transcendental_sp_q : Transcendental ℚ (sp q) := by
  rw [sp_q]
  exact transcendental_qVar

/-- The complement of the first parameter is nonzero in the base field. -/
theorem one_sub_algebraMap_q_ne_zero : (1 : Base) - algebraMap Coeff Base q ≠ 0 := by
  have h : IsUnit ((1 : Base) - algebraMap Coeff Base q) := by
    have h1 := isUnit_one_sub_q.map (algebraMap Coeff Base)
    rwa [map_sub, map_one] at h1
  exact h.ne_zero

/-- At the parameters of the model the basic operator of index zero is not a multiplication
operator: the deformation parameter does not vanish there, so specialising an operator of the
filtration to a multiplication is a conclusion with content rather than an identity. -/
theorem dop_ne_mulLeft (h : Lambda Base) :
    Dop (algebraMap Coeff Base q) (algebraMap Coeff Base u) 0 ≠ LinearMap.mulLeft Base h :=
  HJO.DopCommutator.Witness.dop_zero_ne_mulLeft one_sub_algebraMap_q_ne_zero
    one_sub_algebraMap_u_ne_zero h

/-- The specialisation data is available with both parameters generic: the coefficient ring is a
local ring mapping injectively into a field, the specialisation sends the second parameter to `1`
in a nontrivial target while leaving the first alone, the deformation parameter `ℏ = 1 - u` is
nonzero both in the coefficient ring and in the base field, the parameter of the axis generators
avoids `0` and `1` and is not a root of unity -- indeed every `1 - (qu) ^ k` is a unit of the
coefficient ring, which is what the corrected axis generators need -- the specialised first
parameter is transcendental over `ℚ`, and the basic operator of index zero is not a multiplication
operator. -/
theorem nondegenerate_data :
    Function.Injective (algebraMap Coeff Base) ∧ sp u = 1 ∧ sp q = Determinant.qVar ∧
      Nontrivial Target ∧ Transcendental ℚ (sp q) ∧ IsUnit (1 - q) ∧
      IsUnit (q * u) ∧ IsUnit (1 - q * u) ∧ (∀ j : ℕ, IsUnit (1 - (q * u) ^ (j + 1))) ∧
      u ≠ 1 ∧ algebraMap Coeff Base u ≠ 1 ∧
      (1 : Base) - algebraMap Coeff Base u ≠ 0 ∧
      algebraMap Coeff Base q * algebraMap Coeff Base u ≠ 0 ∧
      algebraMap Coeff Base q * algebraMap Coeff Base u ≠ 1 ∧
      (∀ j : ℕ, (algebraMap Coeff Base q * algebraMap Coeff Base u) ^ (j + 1) ≠ 1) ∧
      (1 : Base) - algebraMap Coeff Base q ≠ 0 ∧
      ∀ h : Lambda Base,
        Dop (algebraMap Coeff Base q) (algebraMap Coeff Base u) 0 ≠ LinearMap.mulLeft Base h :=
  ⟨algebraMap_injective, sp_u, sp_q, inferInstance, transcendental_sp_q, isUnit_one_sub_q, isUnit_v,
    isUnit_one_sub_v, isUnit_one_sub_v_pow, u_ne_one, algebraMap_u_ne_one,
    one_sub_algebraMap_u_ne_zero, algebraMap_v_ne_zero, algebraMap_v_ne_one,
    algebraMap_v_pow_ne_one, one_sub_algebraMap_q_ne_zero, dop_ne_mulLeft⟩

/-! ### The two parameters are algebraically independent -/

/-- The evaluation of an integral polynomial in one variable at the variable of `ℚ((q))`. -/
noncomputable def intEval : Polynomial ℤ →+* Target :=
  ((Polynomial.aeval Determinant.qVar : Polynomial ℚ →ₐ[ℚ] Target) :
    Polynomial ℚ →+* Target).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

/-- That evaluation is injective: the variable of `ℚ((q))` is transcendental over `ℚ` and the
rational coefficients extend the integral ones. -/
theorem injective_intEval : Function.Injective intEval :=
  (transcendental_iff_injective.mp transcendental_qVar).comp
    (Polynomial.map_injective _ (Int.castRingHom ℚ).injective_int)

/-- The evaluation takes the variable to the variable. -/
theorem intEval_X : intEval Polynomial.X = Determinant.qVar := by
  rw [intEval, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
  exact Polynomial.aeval_X Determinant.qVar

/-- The substitution putting the first parameter in the inner variable and `1` plus the second in
the outer one, into the polynomials in two variables over `ℤ`, is injective: reversing the shift
and reading the inner variable off recovers the polynomial. -/
theorem injective_bivar :
    Function.Injective (MvPolynomial.aeval ![Polynomial.C Polynomial.X, Polynomial.X + 1] :
      MvPolynomial (Fin 2) ℤ →ₐ[ℤ] Polynomial (Polynomial ℤ)) := by
  have hinv : ∀ P : MvPolynomial (Fin 2) ℤ,
      (Polynomial.aeval (MvPolynomial.X 1 - 1 : MvPolynomial (Fin 2) ℤ) :
          Polynomial (MvPolynomial (Fin 2) ℤ) →ₐ[MvPolynomial (Fin 2) ℤ] MvPolynomial (Fin 2) ℤ)
        (Polynomial.map
          ((Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) :
            Polynomial ℤ →ₐ[ℤ] MvPolynomial (Fin 2) ℤ) : Polynomial ℤ →+* MvPolynomial (Fin 2) ℤ)
          (MvPolynomial.aeval ![Polynomial.C Polynomial.X, Polynomial.X + 1] P)) = P := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p r hp hr => simp only [map_add, Polynomial.map_add, hp, hr]
    | mul_X p i hp =>
      rw [map_mul, Polynomial.map_mul, map_mul, hp]
      congr 1
      fin_cases i <;> simp
  intro P Q h
  have hP := hinv P
  rw [h, hinv Q] at hP
  exact hP.symm

/-- A relation between the two parameters over the coefficient ring factors through the
polynomials in two variables over `ℤ`: the first parameter is a constant carrying the variable of
`ℚ((q))` and the second is `1` plus the deformation parameter, both of them polynomial. -/
theorem aeval_q_u (P : MvPolynomial (Fin 2) ℤ) :
    MvPolynomial.aeval ![Witness.q, Witness.u] P
      = ((Polynomial.map intEval
          (MvPolynomial.aeval ![Polynomial.C Polynomial.X, Polynomial.X + 1] P) :
          Polynomial Target) : Coeff) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => rw [map_add, hp, hr, map_add, Polynomial.map_add, Polynomial.coe_add]
  | mul_X p i hp =>
    have hX : MvPolynomial.aeval ![Witness.q, Witness.u]
          (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ)
        = ((Polynomial.map intEval (MvPolynomial.aeval
            ![Polynomial.C Polynomial.X, Polynomial.X + 1]
            (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ)) : Polynomial Target) : Coeff) := by
      fin_cases i <;> simp [intEval_X, Witness.q, Witness.u, add_comm]
    rw [map_mul, hp, hX, map_mul, Polynomial.map_mul, Polynomial.coe_mul]

/-- The two parameters admit no integral relation over the coefficient ring. -/
theorem injective_aeval_q_u :
    Function.Injective (MvPolynomial.aeval ![Witness.q, Witness.u] :
      MvPolynomial (Fin 2) ℤ →ₐ[ℤ] Coeff) := by
  intro P Q h
  rw [aeval_q_u, aeval_q_u] at h
  exact injective_bivar (Polynomial.map_injective _ injective_intEval
    (Polynomial.coe_injective Target h))

/-- The two parameters of the specialisation data are algebraically independent over `ℤ` in any
field the coefficient ring maps into injectively: the degenerate values at which the slope
operators collapse are therefore excluded, the compositional rational shuffle identity is quoted at
parameters it is stated for, and a witness polynomial is pinned down by its value at the two
parameters. -/
theorem algebraicIndependent_param {L : Type*} [Field L] [Algebra ℚ L] (f : Coeff →+* L)
    (hf : Function.Injective f) (x : L) (hx : x = f Witness.q) :
    AlgebraicIndependent ℤ ![x, f Witness.u] := by
  subst hx
  rw [algebraicIndependent_iff_injective_aeval]
  have hcomp : ∀ P : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.aeval ![f Witness.q, f Witness.u] P
        = f (MvPolynomial.aeval ![Witness.q, Witness.u] P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p r hp hr => simp only [map_add, hp, hr]
    | mul_X p i hp =>
      have hi : f (![Witness.q, Witness.u] i) = ![f Witness.q, f Witness.u] i := by
        fin_cases i <;> simp
      simp only [map_mul, MvPolynomial.aeval_X, hp, hi]
  intro P Q h
  rw [hcomp, hcomp] at h
  exact injective_aeval_q_u (hf h)

/-! ### The slope homomorphism the collinear commutation input supplies -/

/-- A slope homomorphism at `(a, b)` exists over the base field at the two parameters of the
model. Their algebraic independence over `ℤ` allows the generic collinear commutation input to
be applied and guarantees the nonvanishing conditions for the axis change of generators; it
is sufficient, not necessary for generation alone. In this model `qu` is a power series whose
constant term is the variable of `ℚ((q))`, so `qu` and every `1 - (qu) ^ k`, `k ≥ 1`, are
units of the coefficient ring. -/
theorem exists_isSlopeHom (collinear : External.CollinearCommutation Base) {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b) :
    ∃ Θ : Lambda Base →ₐ[Base] Module.End Base (Lambda Base),
      IsSlopeHom a b (algebraMap Coeff Base q) (algebraMap Coeff Base u) Θ :=
  (collinear a b hab ha hb (algebraMap Coeff Base q) (algebraMap Coeff Base u)
    (algebraicIndependent_param (algebraMap Coeff Base) algebraMap_injective _ rfl)).2

/-! ### The two statements at the model -/

/-- The evaluation map is a genuine ring homomorphism at genuine data: over the coefficient ring of
the model, at a slope homomorphism at `(a, b)` supplied by the collinear commutation input for
parameters at which the axis generators are defined, there is a ring homomorphism from the
symmetric functions with coefficients in that ring to `ℚ((q))` which is the evaluation map, is
semilinear over the specialisation, and on a weighted homogeneous element of degree `n` returns the
value at `(q, 1)` of any two-variable integer polynomial whose value at the two parameters is the
scalar obtained by sign extraction. -/
theorem exists_slopeHom_phiRegHom (collinear : External.CollinearCommutation Base) {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b) :
    ∃ (Θ : Lambda Base →ₐ[Base] Module.End Base (Lambda Base))
      (Ψ : Lambda Coeff →+* Target),
      IsSlopeHom a b (algebraMap Coeff Base q) (algebraMap Coeff Base u) Θ ∧
        (∀ f : Lambda Coeff, Ψ f = phiReg b sp Θ f) ∧
        (∀ (c : Coeff) (f : Lambda Coeff), Ψ (C c * f) = sp c * Ψ f) ∧
        ∀ (f : Lambda Coeff) (n : ℕ) (π : MvPolynomial (Fin 2) ℤ),
          IsWeightedHomogeneous degWeight f n →
          signExtract Base (Θ (coeffInc Coeff Base f) 1)
              = polyValue π (algebraMap Coeff Base q) (algebraMap Coeff Base u) →
            Ψ f = (-1) ^ (n * (b + 1)) * polyValue π Determinant.qVar 1 := by
  obtain ⟨Θ, hΘ⟩ := exists_isSlopeHom collinear hab ha hb
  obtain ⟨-, -, -, hlin, hpoly⟩ := phiReg_isUnitalAlgHom isUnit_one_sub_q isUnit_v
    isUnit_one_sub_v_pow algebraMap_injective sp sp_u hΘ
  refine ⟨Θ, phiRegHom b isUnit_one_sub_q isUnit_v isUnit_one_sub_v_pow algebraMap_injective sp sp_u
      hΘ, hΘ, fun f => rfl, hlin, fun f n π hf hπ => ?_⟩
  rw [phiRegHom_apply, hpoly f n π hf hπ, sp_q]

/-- The area generating series is the exponential of the evaluation coefficients: over the
coefficient ring of the model, at a slope homomorphism at `(a, b)` supplied by the collinear
commutation input and at the realisation of the ring of symmetric functions built above,
`Determinant.genA a b` is the formal exponential of the logarithmic series of the evaluation map's
values on the power sums, the specialisation sending the second parameter to `1` and the first to
the variable of `ℚ((q))`. -/
theorem exists_slopeHom_genA (collinear : External.CollinearCommutation Base)
    (shuffle : External.Shuffle Base) (epsilonGessel : External.EpsilonGessel Base)
    (creationExpansion : External.CreationExpansion Base) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 < a) (hb : a < b) :
    ∃ Θ : Lambda Base →ₐ[Base] Module.End Base (Lambda Base),
      IsSlopeHom a b (algebraMap Coeff Base q) (algebraMap Coeff Base u) Θ ∧
        Determinant.genA a b = AExponential.formalExp
          (AExponential.logSeries fun k => phiReg b sp Θ (powerSum Coeff k)) := by
  obtain ⟨Θ, hΘ⟩ := exists_isSlopeHom collinear hab ha hb
  exact ⟨Θ, hΘ, genA_eq_formalExp isUnit_one_sub_q isUnit_v isUnit_one_sub_v_pow
    algebraMap_injective sp sp_u sp_q hΘ shuffle epsilonGessel creationExpansion hab ha hb
    (algebraicIndependent_param (algebraMap Coeff Base) algebraMap_injective _ rfl)
    (realise Base) (isRealisation_realise Base)⟩

end Witness

end HJO.PhiMul
