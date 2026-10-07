/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.PpolyParamInv
public meta import HJO.Attr

/-! # The inverted Macdonald operator, and that it is diagonal on `P_μ[X_n]`

`HJO.Mac.macOpCompInv_macPpoly`: the conjugated operator
`\widehat D^{(n)}_1 = \widehat\iota_n ∘ D^{(n)}_1 ∘ \widehat\iota_n` scales `P_μ[X_n]` by
`ι(E_n(μ))`. This is the hypothesis `hinv` of `HJO.Sym.coeffSubst_macPfun_of_eigen` and of
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_of_dop_and_eigen_param`, so proving it proves
`hPι` --- `HJO.Sym.coeffSubst_macPfun` --- and with it the parameter-inversion half of the collinear
commutation argument.

## Main definitions

* `HJO.Mac.paramInvFrac`: `\widehat\iota_n` on the rational function field `𝕜(x_1,…,x_n)`, the
  extension to the fraction field of applying `ι` to each coefficient.
* `HJO.Mac.macFactor`: one factor `(u x_i - x_k)/(x_i - x_k)` of `A_i`, which is how the cross
  identity is cut down to two variables.
* `HJO.Mac.macDiag`: the scalar `c`, the diagonal part of the commutator.

## Main results

* `HJO.Mac.paramInvFrac_macOp`: **the inverted operator is Macdonald's operator at the inverted
  parameters**, `\widehat D^{(n)}_1 = D^{(n)}_1[q^{-1}, u^{-1}]` (`HJO.Mac.paramInvFrac_macCoeff`).
  It replaces the usual route through `\widehat\iota_n(A_i)` and `T_{q,x_i}^{-1}` by the
  observation that the conjugate of `∑_i A_i(u) T_{q,x_i}` is `∑_i A_i(u^{-1}) T_{q^{-1},x_i}`,
  which is the *same* operator with both parameters inverted.
* `HJO.Mac.exists_mem_eq_paramInvFrac_algebraMap`.
* `HJO.Mac.macCoeff_cross`.
* `HJO.Mac.macOp_comm`, `HJO.Mac.macOpComp_comm`: Macdonald's operator commutes with its inversion.
* `HJO.Mac.exists_eq_paramInvFrac_macOp_msymm`.
* `HJO.Mac.macOpCompInv_macPpoly`.
* `HJO.Mac.paramInvComp_macPpoly`.
* `HJO.Sym.coeffSubst_macPfun`, `ς(P_μ) = P_μ`.
* `HJO.Standing.coeffSubst_macPfun_param`: `hPι` at the standing field, with nothing assumed.
* `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_of_dop_param`: the collinear residue, with
  only the hypothesis `hdop`, the statement of `HJO.Standing.dop_zero_smul_macHtilde_param`, left.

## Genericity, and the degenerate corners

`HJO.Mac.macCoeff_cross` spends **nothing**: it is a polynomial identity between two products of
linear forms, valid over any field, and its only hypotheses are that `q` is a unit --- which
`HJO.Mac.qShift` needs anyway --- and `uv = 1`, which is what `\widehat\iota_n` being the inversion
of `u` means. `HJO.Mac.macOp_comm` adds only `[Algebra ℚ K]`, and that is the char-zero appeal the
proof of `HJO.Mac.exists_eq_macOp_algebraMap` makes. So neither degenerates at a root of unity, at
`u = ±1` or on `qu = 1`: instantiating there changes nothing.

`HJO.Mac.macOpCompInv_macPpoly` carries `hqu` and `n ≥ 1`. Both are already in the statement: `hqu`
is needed for `P_ν[X_n]` to exist at all (`HJO.Mac.existsUnique_isMonicEigen`, which fails at
`q = u = -1` and on `qu = 1`), and `n ≥ 1` is the lemma's own hypothesis --- it is what makes
`E_n(ν) ≠ 0` (`HJO.Sym.macdonaldEigenvalue_ne_zero`, which needs `hqu` too), the one thing the
normalisation below divides by. Nothing beyond those is spent, and in particular no `u ≠ 0` appears
that `hqu` does not already give.

## References

This file formalises Definitions `HJO.Mac.macCoeff`, `HJO.Mac.paramInvFrac` and `HJO.Mac.macOpInv`,
and Lemmas `HJO.Mac.exists_mem_eq_paramInvFrac_algebraMap`, `HJO.Mac.paramInvFrac_macCoeff`,
`HJO.Mac.macCoeff_cross`, `HJO.Mac.macOp_comm`, `HJO.Mac.exists_eq_paramInvFrac_macOp_msymm`,
`HJO.Mac.macOpCompInv_macPpoly`, `HJO.Mac.paramInvComp_macPpoly` and `HJO.Sym.coeffSubst_macPfun`,
of the theory of Macdonald polynomials.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

/-! ### The parameter inversion on the rational function field -/

section Frac

variable {σ K : Type*} [Field K] [DecidableEq σ]

/-- An involutive ring endomorphism of a field, read as a ring automorphism: it is its own
inverse. This is how the coefficient inversion `ι`, carried through this library as a bare
`RingHom` together with `ι ∘ ι = id`, becomes the automorphism `HJO.Sym.paramQUInv` asserts. -/
def ringEquivOfInvolutive {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c) : K ≃+* K :=
  { toFun := ι, invFun := ι, left_inv := hιι, right_inv := hιι,
    map_mul' := ι.map_mul, map_add' := ι.map_add }

@[simp]
theorem coe_ringEquivOfInvolutive {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c) :
    ((ringEquivOfInvolutive hιι : K ≃+* K) : K →+* K) = ι := rfl

/-- **`\widehat\iota_n`, the parameter inversion of a finite alphabet**: the
automorphism of the rational function field `𝕜(x_1,…,x_n)` which fixes each `x_i` and acts on the
coefficients by `ι`.

The usual construction extends an assignment on the `n+2` generators `q, u, x_1, …, x_n`; here
it is the extension to the fraction field of the coefficient substitution on the polynomial ring,
which needs no algebraic independence because `ι` is given. The usual construction's appeal to
`HJO.Ascent.algebraicIndependent_invCoords` is what produces `ι` on `𝕜` in the first place, and that
is `HJO.Sym.paramQUInv`. -/
@[hjo "def_mac2_param_inv"]
noncomputable def paramInvFrac (ι : K ≃+* K) :
    FractionRing (MvPolynomial σ K) ≃+* FractionRing (MvPolynomial σ K) :=
  IsFractionRing.ringEquivOfRingEquiv (MvPolynomial.mapEquiv σ ι)

omit [DecidableEq σ] in
/-- **`\widehat\iota_n` applies `ι` to the coefficients of a polynomial and fixes each `x_i`**: its
defining property, and the second half of what `HJO.Mac.paramInvFrac` asserts. -/
@[hjo "def_mac2_param_inv"]
theorem paramInvFrac_algebraMap (ι : K ≃+* K) (p : MvPolynomial σ K) :
    paramInvFrac ι (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p)
      = algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          (MvPolynomial.map (ι : K →+* K) p) := by
  rw [paramInvFrac, IsFractionRing.ringEquivOfRingEquiv_algebraMap]; rfl

omit [DecidableEq σ] in
/-- Two ring endomorphisms of the rational function field agreeing on the polynomials agree. -/
theorem ringHom_ext_frac {j k : FractionRing (MvPolynomial σ K) →+* FractionRing (MvPolynomial σ K)}
    (h : ∀ p : MvPolynomial σ K,
      j (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p)
        = k (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p)) : j = k :=
  IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial σ K)) (RingHom.ext h)

omit [DecidableEq σ] in
/-- **`\widehat\iota_n` is an involution**, `ι` being one. -/
theorem paramInvFrac_paramInvFrac {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c)
    (f : FractionRing (MvPolynomial σ K)) :
    paramInvFrac (ringEquivOfInvolutive hιι) (paramInvFrac (ringEquivOfInvolutive hιι) f) = f := by
  have h : ((paramInvFrac (σ := σ) (ringEquivOfInvolutive hιι) :
        FractionRing (MvPolynomial σ K) ≃+* _).toRingHom.comp
        (paramInvFrac (ringEquivOfInvolutive hιι) :
          FractionRing (MvPolynomial σ K) ≃+* _).toRingHom)
      = RingHom.id _ := by
    refine ringHom_ext_frac fun p => ?_
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply]
    rw [paramInvFrac_algebraMap, paramInvFrac_algebraMap, coe_ringEquivOfInvolutive,
      MvPolynomial.map_map, show ι.comp ι = RingHom.id K from RingHom.ext hιι,
      MvPolynomial.map_id]
  exact RingHom.congr_fun h f

omit [DecidableEq σ] in
/-- **The parameter inversion acts on a graded piece**, read on the
rational function field where `HJO.Mac.paramInvFrac` lives: `\widehat\iota_n` carries the image of
`𝒮_{n,d}` into the image of `𝒮_{n,d}`. Its graded-piece form, which is all the uniqueness argument
consumes, is `HJO.Mac.map_mem_symmetricHomogeneousSubmodule`. -/
@[hjo "lem_mac2_param_inv_stable"]
theorem exists_mem_eq_paramInvFrac_algebraMap (ι : K ≃+* K) {d : ℕ} {f : MvPolynomial σ K}
    (hf : f ∈ symmetricHomogeneousSubmodule σ K d) :
    ∃ g ∈ symmetricHomogeneousSubmodule σ K d,
      paramInvFrac ι (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) f)
        = algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) g :=
  ⟨MvPolynomial.map (ι : K →+* K) f, map_mem_symmetricHomogeneousSubmodule _ hf,
    paramInvFrac_algebraMap ι f⟩

/-- Applying `ι` to the coefficients turns a rescaling by `q` into a rescaling by `ι(q)`. -/
theorem map_rescaleEquiv (ι : K ≃+* K) (q : Kˣ) (i : σ) (p : MvPolynomial σ K) :
    MvPolynomial.map (ι : K →+* K) (rescaleEquiv (Pi.mulSingle i q) p)
      = rescaleEquiv (Pi.mulSingle i (Units.map (ι : K →* K) q))
          (MvPolynomial.map (ι : K →+* K) p) := by
  have h : ((MvPolynomial.map (ι : K →+* K) : MvPolynomial σ K →+* MvPolynomial σ K).comp
        ((rescaleEquiv (Pi.mulSingle i q)).toAlgHom : MvPolynomial σ K →+* MvPolynomial σ K))
      = (((rescaleEquiv (Pi.mulSingle i (Units.map (ι : K →* K) q))).toAlgHom :
            MvPolynomial σ K →+* MvPolynomial σ K).comp
          (MvPolynomial.map (ι : K →+* K))) := by
    have hC : ∀ (c : σ → Kˣ) (a : K), rescaleEquiv c (C a : MvPolynomial σ K) = C a :=
      fun c a => by rw [← MvPolynomial.algebraMap_eq]; exact (rescaleEquiv c).commutes a
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.coe_toAlgHom, hC,
        MvPolynomial.map_C]
    · simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.coe_toAlgHom, rescaleEquiv_X,
        MvPolynomial.map_X, smul_eq_C_mul, map_mul, MvPolynomial.map_C]
      rcases eq_or_ne j i with rfl | hj
      · rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]; rfl
      · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, Units.val_one, map_one]
  exact RingHom.congr_fun h p

/-- **`\widehat\iota_n` turns the `q`-shift into the `ι(q)`-shift**: the first step of the usual
proof of `HJO.Mac.paramInvFrac_macCoeff`, where `ι(q) = q^{-1}` makes it the inverse shift
`T_{q,x_i}^{-1}`. -/
theorem paramInvFrac_qShift (ι : K ≃+* K) (q : Kˣ) (i : σ) (f : FractionRing (MvPolynomial σ K)) :
    paramInvFrac ι (qShift q i f)
      = qShift (Units.map (ι : K →* K) q) i (paramInvFrac ι f) := by
  have h : ((paramInvFrac (σ := σ) ι : FractionRing (MvPolynomial σ K) ≃+* _).toRingHom.comp
        (qShift q i).toRingEquiv.toRingHom)
      = ((qShift (Units.map (ι : K →* K) q) i).toRingEquiv.toRingHom.comp
          (paramInvFrac ι : FractionRing (MvPolynomial σ K) ≃+* _).toRingHom) := by
    refine ringHom_ext_frac fun p => ?_
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv]
    rw [qShift_algebraMap, paramInvFrac_algebraMap, paramInvFrac_algebraMap, qShift_algebraMap,
      map_rescaleEquiv]
  exact RingHom.congr_fun h f

end Frac

/-! ### The inverted operator is Macdonald's operator at the inverted parameters

This is the whole of `HJO.Mac.paramInvFrac_macCoeff`, and rather more: conjugating
`D^{(n)}_1 = ∑_i A_i(u)T_{q,x_i}` by `\widehat\iota_n` replaces `A_i(u)` by `A_i(ι u)` and
`T_{q,x_i}` by `T_{ι q, x_i}`, so `\widehat D^{(n)}_1` is *the same operator* with both parameters
inverted. The computation can stop at `∑_i \widehat\iota_n(A_i)T_{q,x_i}^{-1}`; naming the result as
`D^{(n)}_1[q^{-1}, u^{-1}]` costs nothing extra and makes `HJO.Mac.macOp_comm` the commutation of
two Macdonald operators, which is how it is proved below.
-/

section Operator

variable {σ K : Type*} [Field K] [LinearOrder σ] [Fintype σ]

/-- **`\widehat\iota_n(A_i)` is `A_i` with `u` inverted**: the inversion fixes each variable and
sends the coefficient `u` to `ι(u)`. This is `\widehat\iota_n(A_i)` of
`HJO.Mac.paramInvFrac_macCoeff`, at `ι(u) = u^{-1}`. -/
@[hjo "lem_mac2_dop_inv_explicit"]
theorem paramInvFrac_macCoeff (ι : K ≃+* K) (u : K) (i : σ) :
    paramInvFrac ι (macCoeff u i) = macCoeff (ι u) i := by
  rw [macCoeff, macCoeff, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_div₀, paramInvFrac_algebraMap, paramInvFrac_algebraMap]
  simp only [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  rfl

/-- **The inverted Macdonald operator is Macdonald's operator at the inverted parameters**
(`HJO.Mac.macOpInv`, `HJO.Mac.paramInvFrac_macCoeff`):
`\widehat D^{(n)}_1 = D^{(n)}_1[ι q, ι u]`.

`\widehat\iota_n` is a ring homomorphism, so it distributes over the sum and over each product
`A_i T_{q,x_i}`; it carries `A_i(u)` to `A_i(ι u)` (`paramInvFrac_macCoeff`) and
`T_{q,x_i} ∘ \widehat\iota_n` to `T_{ι q, x_i}` (`paramInvFrac_qShift`), the inner
`\widehat\iota_n` being cancelled by the involutivity. At `ι q = q^{-1}` and `ι u = u^{-1}` the
shift is the `T_{q,x_i}^{-1}` and the coefficient its `\widehat\iota_n(A_i)`. -/
@[hjo "lem_mac2_dop_inv_explicit"]
theorem paramInvFrac_macOp {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c) (q : Kˣ) (u : K)
    (f : FractionRing (MvPolynomial σ K)) :
    paramInvFrac (ringEquivOfInvolutive hιι)
        (macOp q u (paramInvFrac (ringEquivOfInvolutive hιι) f))
      = macOp (Units.map (ι : K →* K) q) (ι u) f := by
  rw [macOp_apply, macOp_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, paramInvFrac_macCoeff, paramInvFrac_qShift, paramInvFrac_paramInvFrac hιι]
  rfl

variable [Algebra ℚ K]

/-- **The inverted operator on a graded piece is Macdonald's operator at the inverted
parameters.** `HJO.Mac.macOpCompInv`, the conjugate of `D^{(n)}_1` by the coefficient substitution
on `𝒮_{n,d}`, is `HJO.Mac.macOpComp` at `ι q` and `ι u`; in particular it is the *same kind* of
object, so everything already proved about `macOpComp` --- its linearity, its triangularity, and
the uniqueness of its monic eigenfunctions --- applies to it. -/
theorem macOpCompInv_eq_macOpComp {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c) (q : Kˣ) (u : K)
    (d : ℕ) (f : symmetricHomogeneousSubmodule σ K d) :
    macOpCompInv ι q u d f = macOpComp (Units.map (ι : K →* K) q) (ι u) d f := by
  refine (eq_macOpComp (Units.map (ι : K →* K) q) (ι u) d ?_).symm
  rw [← paramInvFrac_macOp hιι q u, paramInvFrac_algebraMap, coe_ringEquivOfInvolutive,
    ← coe_paramInvComp ι f, ← algebraMap_macOpComp, paramInvFrac_algebraMap,
    coe_ringEquivOfInvolutive]
  rfl

end Operator

/-! ### The shifts, and the linear forms they move -/

section Shift

-- `DecidableEq σ` is taken from `LinearOrder σ` rather than assumed separately, as in
-- `HJO/Macdonald/FiniteAlphabet.lean`: with both in scope, `Pi.mulSingle` and
-- `Finset.erase` pick up different instances in different places and the rewrites below
-- silently fail to match.
variable {σ K : Type*} [Field K] [LinearOrder σ]

/-- The rescaling at `i` fixes every other variable. -/
theorem rescaleEquiv_mulSingle_X_of_ne (q : Kˣ) {i j : σ} (h : j ≠ i) :
    rescaleEquiv (Pi.mulSingle i q) (X j : MvPolynomial σ K) = X j := by
  rw [rescaleEquiv_X, Pi.mulSingle_eq_of_ne h, Units.val_one, one_smul]

/-- The rescaling at `i` multiplies `x_i` by `q`. -/
theorem rescaleEquiv_mulSingle_X_self (q : Kˣ) (i : σ) :
    rescaleEquiv (Pi.mulSingle i q) (X i : MvPolynomial σ K) = C (q : K) * X i := by
  rw [rescaleEquiv_X, Pi.mulSingle_eq_same, smul_eq_C_mul]

omit [LinearOrder σ] in
/-- The trivial rescaling is the identity. -/
theorem rescaleEquiv_one (p : MvPolynomial σ K) : rescaleEquiv (1 : σ → Kˣ) p = p := by
  have h : (rescaleEquiv (1 : σ → Kˣ)).toAlgHom = AlgHom.id K (MvPolynomial σ K) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    rw [AlgEquiv.coe_toAlgHom, rescaleEquiv_X, Pi.one_apply, Units.val_one, one_smul,
      AlgHom.id_apply]
  exact AlgHom.congr_fun h p

/-- **The `q`-shifts commute**: they are rescalings, and the rescaling vectors multiply. -/
theorem qShift_comm (q r : Kˣ) (i j : σ) (f : FractionRing (MvPolynomial σ K)) :
    qShift q i (qShift r j f) = qShift r j (qShift q i f) := by
  have h : ((qShift (σ := σ) q i).toRingEquiv.toRingHom.comp
        (qShift r j).toRingEquiv.toRingHom)
      = ((qShift (σ := σ) r j).toRingEquiv.toRingHom.comp (qShift q i).toRingEquiv.toRingHom) := by
    refine ringHom_ext_frac fun p => ?_
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv]
    rw [qShift_algebraMap, qShift_algebraMap, qShift_algebraMap, qShift_algebraMap,
      show rescaleEquiv (Pi.mulSingle i q) (rescaleEquiv (Pi.mulSingle j r) p)
        = rescaleEquiv (Pi.mulSingle j r * Pi.mulSingle i q) p from
        AlgEquiv.congr_fun (rescaleEquiv_trans _ _) p,
      show rescaleEquiv (Pi.mulSingle j r) (rescaleEquiv (Pi.mulSingle i q) p)
        = rescaleEquiv (Pi.mulSingle i q * Pi.mulSingle j r) p from
        AlgEquiv.congr_fun (rescaleEquiv_trans _ _) p, mul_comm]
  exact RingHom.congr_fun h f

/-- **The `q`-shift and the `q⁻¹`-shift at the same letter are inverse.** -/
theorem qShift_inv_qShift (q : Kˣ) (i : σ) (f : FractionRing (MvPolynomial σ K)) :
    qShift q⁻¹ i (qShift q i f) = f := by
  have h : ((qShift (σ := σ) q⁻¹ i).toRingEquiv.toRingHom.comp
      (qShift q i).toRingEquiv.toRingHom) = RingHom.id _ := by
    refine ringHom_ext_frac fun p => ?_
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, RingHom.id_apply]
    rw [qShift_algebraMap, qShift_algebraMap,
      show rescaleEquiv (Pi.mulSingle i q⁻¹) (rescaleEquiv (Pi.mulSingle i q) p)
        = rescaleEquiv (Pi.mulSingle i q * Pi.mulSingle i q⁻¹) p from
        AlgEquiv.congr_fun (rescaleEquiv_trans _ _) p,
      ← Pi.mulSingle_mul, mul_inv_cancel, Pi.mulSingle_one, rescaleEquiv_one]
  exact RingHom.congr_fun h f

/-- The rescaling at `b` by a unit carries `x_a - x_b` to `x_a - c x_b`. -/
theorem rescaleEquiv_X_sub_X (c : Kˣ) {a b : σ} (hab : a ≠ b) :
    rescaleEquiv (Pi.mulSingle b c) (X a - X b : MvPolynomial σ K)
      = X a - C (c : K) * X b := by
  rw [map_sub, rescaleEquiv_mulSingle_X_of_ne c hab, rescaleEquiv_mulSingle_X_self]

/-- A linear form `x_a - c x_b` in two distinct variables, with `c` a unit, is a nonzero
polynomial: it is a rescaling of `x_a - x_b`. This is what makes the denominators of the shifted
coefficients of Macdonald's operator legitimate. -/
theorem X_sub_C_mul_X_ne_zero {a b : σ} (hab : a ≠ b) (c : Kˣ) :
    (X a - C (c : K) * X b : MvPolynomial σ K) ≠ 0 := fun h0 =>
  X_sub_X_ne_zero hab ((rescaleEquiv (Pi.mulSingle b c)).injective
    (by rw [rescaleEquiv_X_sub_X c hab, h0, map_zero]))

end Shift

/-! ### The cross terms

`HJO.Mac.macCoeff_cross`. The two coefficients `A_i(u)` and `A_j(u^{-1})` are products over the
letters other than `i` and other than `j`; each splits into the factor mentioning the *other* of the
two letters and a product over the letters mentioning neither. The shifts fix the second part, and
what is left is the two-variable identity `L = R`, which is the scalar `hpoly` below.
-/

section Cross

variable {σ K : Type*} [Field K] [LinearOrder σ] [Fintype σ]

/-- The `k`-th factor of `A_i`: `(u x_i - x_k)/(x_i - x_k)`. Splitting `A_i` into its factors is
how the cross identity is reduced to a statement in the two variables `x_i` and `x_j`. -/
noncomputable def macFactor (u : K) (i k : σ) : FractionRing (MvPolynomial σ K) :=
  algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (C u * X i - X k) /
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (X i - X k)

/-- `A_i` is the product of its factors: `HJO.Mac.macCoeff` read factorwise. -/
theorem macCoeff_eq_prod_macFactor (u : K) (i : σ) :
    macCoeff u i = ∏ k ∈ Finset.univ.erase i, macFactor u i k := rfl

omit [Fintype σ] in
/-- The shift at `c` fixes a factor mentioning neither `x_c` nor, through the shift, anything
else: both variables of the factor are different from `x_c`. -/
theorem qShift_macFactor_of_ne (q : Kˣ) (u : K) {a b c : σ} (hac : a ≠ c) (hbc : b ≠ c) :
    qShift q c (macFactor u a b) = macFactor u a b := by
  have hn : rescaleEquiv (Pi.mulSingle c q) (C u * X a - X b : MvPolynomial σ K)
      = C u * X a - X b := by
    rw [map_sub, map_mul, rescaleEquiv_C, rescaleEquiv_mulSingle_X_of_ne q hac,
      rescaleEquiv_mulSingle_X_of_ne q hbc]
  have hd : rescaleEquiv (Pi.mulSingle c q) (X a - X b : MvPolynomial σ K) = X a - X b := by
    rw [map_sub, rescaleEquiv_mulSingle_X_of_ne q hac, rescaleEquiv_mulSingle_X_of_ne q hbc]
  simp only [macFactor, map_div₀, qShift_algebraMap, hn, hd]

omit [Fintype σ] in
/-- The shift at `c` multiplies the `x_c` of a factor by `q`. -/
theorem qShift_macFactor_self (q : Kˣ) (u : K) {a c : σ} (hac : a ≠ c) :
    qShift q c (macFactor u a c)
      = algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
            (C u * X a - C (q : K) * X c) /
          algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
            (X a - C (q : K) * X c) := by
  have hn : rescaleEquiv (Pi.mulSingle c q) (C u * X a - X c : MvPolynomial σ K)
      = C u * X a - C (q : K) * X c := by
    rw [map_sub, map_mul, rescaleEquiv_C, rescaleEquiv_mulSingle_X_of_ne q hac,
      rescaleEquiv_mulSingle_X_self]
  simp only [macFactor, map_div₀, qShift_algebraMap, hn, rescaleEquiv_X_sub_X q hac]

omit [LinearOrder σ] [Fintype σ] in
/-- The image of a nonzero polynomial in the rational function field is nonzero. -/
theorem algebraMap_ne_zero {p : MvPolynomial σ K} (hp : p ≠ 0) :
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p ≠ 0 := by
  rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  exact hp

/-- **The cross terms of the two operators agree**. With
`\widehat\iota_n(A_j) = A_j(u^{-1})` and `T_{q,x_j}^{-1} = T_{q^{-1},x_j}`, which is what
`paramInvFrac_macOp` and `qShift_inv_qShift` make of the notation, the identity reads
`A_i(u) T_{q,x_i}(A_j(v)) = A_j(v) T_{q^{-1},x_j}(A_i(u))` for `uv = 1` and `i ≠ j`.

The hypothesis is `uv = 1`, not `u ≠ 0`: the identity is between the parameter `u` and its
*inverse*, and nothing here needs either of them to be invertible on its own. -/
@[hjo "lem_mac2_cross"]
theorem macCoeff_cross (q : Kˣ) {u v : K} (huv : u * v = 1) {i j : σ} (hij : i ≠ j) :
    macCoeff u i * qShift q i (macCoeff v j)
      = macCoeff v j * qShift q⁻¹ j (macCoeff u i) := by
  classical
  have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩
  have himem : i ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩
  have hEeq : (Finset.univ.erase j).erase i = (Finset.univ.erase i).erase j :=
    Finset.erase_right_comm
  -- the letters other than `i` and `j`, and what they are
  have hmemE : ∀ k ∈ (Finset.univ.erase i).erase j, k ≠ i ∧ k ≠ j := fun k hk =>
    ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk), Finset.ne_of_mem_erase hk⟩
  -- the four splittings
  have h1 : macCoeff u i
      = (∏ k ∈ (Finset.univ.erase i).erase j, macFactor u i k) * macFactor u i j := by
    rw [macCoeff_eq_prod_macFactor, Finset.prod_erase_mul _ _ hjmem]
  have h3 : macCoeff v j
      = (∏ l ∈ (Finset.univ.erase i).erase j, macFactor v j l) * macFactor v j i := by
    rw [macCoeff_eq_prod_macFactor, ← hEeq, Finset.prod_erase_mul _ _ himem]
  have h2 : qShift q i (macCoeff v j)
      = (∏ l ∈ (Finset.univ.erase i).erase j, macFactor v j l)
        * qShift q i (macFactor v j i) := by
    rw [macCoeff_eq_prod_macFactor, map_prod, ← hEeq, ← Finset.prod_erase_mul _ _ himem, hEeq]
    exact congrArg (· * _) (Finset.prod_congr rfl fun l hl =>
      qShift_macFactor_of_ne q v hij.symm (hmemE l hl).1)
  have h4 : qShift q⁻¹ j (macCoeff u i)
      = (∏ k ∈ (Finset.univ.erase i).erase j, macFactor u i k)
        * qShift q⁻¹ j (macFactor u i j) := by
    rw [macCoeff_eq_prod_macFactor, map_prod, ← Finset.prod_erase_mul _ _ hjmem]
    exact congrArg (· * _) (Finset.prod_congr rfl fun k hk =>
      qShift_macFactor_of_ne q⁻¹ u hij (hmemE k hk).2)
  -- the two-variable identity, `L = R` of the proof
  have key : macFactor u i j * qShift q i (macFactor v j i)
      = macFactor v j i * qShift q⁻¹ j (macFactor u i j) := by
    have hCuv : (C u : MvPolynomial σ K) * C v = 1 := by rw [← C_mul, huv, C_1]
    have hCq : (C (q : K) : MvPolynomial σ K) * C ((q⁻¹ : Kˣ) : K) = 1 := by
      rw [← C_mul, Units.mul_inv, C_1]
    have hpoly : (C u * X i - X j) * (C v * X j - C (q : K) * X i)
          * ((X j - X i) * (X i - C ((q⁻¹ : Kˣ) : K) * X j))
        = (C v * X j - X i) * (C u * X i - C ((q⁻¹ : Kˣ) : K) * X j)
          * ((X i - X j) * (X j - C (q : K) * X i)) := by
      have hA : (C v * X j - X i : MvPolynomial σ K) = -(C v * (C u * X i - X j)) := by
        linear_combination (X i : MvPolynomial σ K) * hCuv
      have hB : (C u * X i - C ((q⁻¹ : Kˣ) : K) * X j : MvPolynomial σ K)
          = C ((q⁻¹ : Kˣ) : K) * (C (q : K) * C u * X i - X j) := by
        linear_combination (-(C u * X i) : MvPolynomial σ K) * hCq
      have hC3 : (C v * X j - C (q : K) * X i : MvPolynomial σ K)
          = C v * (X j - C (q : K) * C u * X i) := by
        linear_combination (C (q : K) * X i : MvPolynomial σ K) * hCuv
      have hD : (X i - C ((q⁻¹ : Kˣ) : K) * X j : MvPolynomial σ K)
          = C ((q⁻¹ : Kˣ) : K) * (C (q : K) * X i - X j) := by
        linear_combination (-(X i) : MvPolynomial σ K) * hCq
      rw [hA, hB, hC3, hD]
      ring
    rw [qShift_macFactor_self q v hij.symm, qShift_macFactor_self q⁻¹ u hij]
    simp only [macFactor]
    rw [div_mul_div_comm, div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero (algebraMap_ne_zero (X_sub_X_ne_zero hij))
          (algebraMap_ne_zero (X_sub_C_mul_X_ne_zero hij.symm q)))
        (mul_ne_zero (algebraMap_ne_zero (X_sub_X_ne_zero hij.symm))
          (algebraMap_ne_zero (X_sub_C_mul_X_ne_zero hij q⁻¹)))]
    simp only [← map_mul]
    rw [hpoly]
  rw [h2, h4, h1, h3]
  linear_combination ((∏ k ∈ (Finset.univ.erase i).erase j, macFactor u i k)
    * ∏ l ∈ (Finset.univ.erase i).erase j, macFactor v j l) * key

end Cross

/-! ### Macdonald's operator commutes with its inversion

`HJO.Mac.macOp_comm`, in the form
`D^{(n)}_1[q, u] D^{(n)}_1[q^{-1}, v] = D^{(n)}_1[q^{-1}, v] D^{(n)}_1[q, u]` for `uv = 1`. The
proof: expand both composites, note that the shifts commute pairwise, kill the off-diagonal brackets
with `HJO.Mac.macCoeff_cross`, and kill the remaining scalar by evaluating at `f = 1`, where both
operators multiply by elements of `𝕜` and therefore commute.
-/

section Commute

variable {σ K : Type*} [Field K] [LinearOrder σ] [Fintype σ]

omit [Fintype σ] in
/-- The `q`-shift undoes the `q⁻¹`-shift at the same letter. -/
theorem qShift_qShift_inv (q : Kˣ) (i : σ) (f : FractionRing (MvPolynomial σ K)) :
    qShift q i (qShift q⁻¹ i f) = f := by
  have h := qShift_inv_qShift q⁻¹ i f
  rwa [inv_inv] at h

/-- **The scalar by which the two composites differ** --- the scalar `c`, the diagonal part of
the commutator. It does not depend on the argument, and `macDiag_eq_zero` says it vanishes. -/
noncomputable def macDiag (q : Kˣ) (u v : K) : FractionRing (MvPolynomial σ K) :=
  ∑ i : σ, (macCoeff u i * qShift q i (macCoeff v i)
    - macCoeff v i * qShift q⁻¹ i (macCoeff u i))

/-- **The commutator of the two operators is multiplication by `macDiag`**: expanding both
composites and grouping by the pair `(i, j)`, the off-diagonal brackets vanish by
`HJO.Mac.macCoeff_cross` and the diagonal shifts cancel. -/
theorem macOp_sub_macOp (q : Kˣ) {u v : K} (huv : u * v = 1)
    (f : FractionRing (MvPolynomial σ K)) :
    macOp q u (macOp q⁻¹ v f) - macOp q⁻¹ v (macOp q u f) = macDiag q u v * f := by
  have hL : macOp q u (macOp q⁻¹ v f)
      = ∑ i : σ, ∑ j : σ,
          macCoeff u i * qShift q i (macCoeff v j) * qShift q i (qShift q⁻¹ j f) := by
    rw [macOp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [macOp_apply, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, mul_assoc]
  have hR : macOp q⁻¹ v (macOp q u f)
      = ∑ i : σ, ∑ j : σ,
          macCoeff v j * qShift q⁻¹ j (macCoeff u i) * qShift q i (qShift q⁻¹ j f) := by
    rw [show (∑ i : σ, ∑ j : σ, macCoeff v j * qShift q⁻¹ j (macCoeff u i)
            * qShift q i (qShift q⁻¹ j f))
          = ∑ j : σ, ∑ i : σ, macCoeff v j * qShift q⁻¹ j (macCoeff u i)
            * qShift q i (qShift q⁻¹ j f) from Finset.sum_comm, macOp_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [macOp_apply, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_assoc, qShift_comm]
  rw [hL, hR, ← Finset.sum_sub_distrib, macDiag, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib,
    Finset.sum_eq_single i
      (fun j _ hji => sub_eq_zero.2
        (congrArg (· * qShift q i (qShift q⁻¹ j f)) (macCoeff_cross q huv hji.symm)))
      fun h => absurd (Finset.mem_univ i) h,
    qShift_qShift_inv, sub_mul]

/-- An element of `𝕜` is fixed by every shift, so `D^{(n)}_1` multiplies it by `D^{(n)}_1(1)`. -/
theorem macOp_algebraMap_C (q : Kˣ) (u c : K) :
    macOp q u (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (C c))
      = algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (C c)
        * macOp q u (1 : FractionRing (MvPolynomial σ K)) := by
  rw [macOp_apply, macOp_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [qShift_algebraMap, rescaleEquiv_C, map_one, mul_one, mul_comm]

omit [LinearOrder σ] [Fintype σ] in
/-- `𝒮_{n,0}` consists of the constants: a polynomial all of whose monomials have degree `0` is
one. -/
theorem eq_C_of_mem_symmetricHomogeneousSubmodule_zero {g : MvPolynomial σ K}
    (hg : g ∈ symmetricHomogeneousSubmodule σ K 0) : g = C (g.coeff 0) :=
  totalDegree_eq_zero_iff_eq_C.1
    ((totalDegree_zero_iff_isHomogeneous σ).2 (mem_symmetricHomogeneousSubmodule.1 hg).2)

variable [Algebra ℚ K]

/-- **`D^{(n)}_1(1)` is a scalar**: `1` lies in `𝒮_{n,0}`, which
`HJO.Mac.exists_eq_macOp_algebraMap` keeps and which consists of the constants. This is the
scalar `a := D(1) ∈ 𝕜`. -/
theorem exists_macOp_one_eq_C (q : Kˣ) (u : K) :
    ∃ a : K, macOp q u (1 : FractionRing (MvPolynomial σ K))
      = algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (C a) := by
  have h1 : (1 : MvPolynomial σ K) ∈ symmetricHomogeneousSubmodule σ K 0 :=
    mem_symmetricHomogeneousSubmodule.2 ⟨fun e => map_one _, isHomogeneous_one σ K⟩
  obtain ⟨g, hg, hmac⟩ := exists_eq_macOp_algebraMap q u h1
  refine ⟨g.coeff 0, ?_⟩
  rw [← map_one (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))), hmac,
    ← eq_C_of_mem_symmetricHomogeneousSubmodule_zero hg]

/-- **The scalar vanishes** --- the last step of the proof of
`HJO.Mac.macOp_comm`: at `f = 1` both composites are the product of the two scalars `D(1)` and
`\widehat D(1)`, in the two orders. -/
theorem macDiag_eq_zero (q : Kˣ) {u v : K} (huv : u * v = 1) :
    macDiag q u v = (0 : FractionRing (MvPolynomial σ K)) := by
  obtain ⟨a, ha⟩ := exists_macOp_one_eq_C (σ := σ) q u
  obtain ⟨b, hb⟩ := exists_macOp_one_eq_C (σ := σ) q⁻¹ v
  have h := macOp_sub_macOp q huv (1 : FractionRing (MvPolynomial σ K))
  rw [mul_one, ha, hb, macOp_algebraMap_C, macOp_algebraMap_C, ha, hb] at h
  rw [← h]
  ring

/-- **Macdonald's operator commutes with its inversion**: for `uv = 1`,
`D^{(n)}_1[q, u]` and `D^{(n)}_1[q^{-1}, v]` commute on the rational function field.

That these are `D^{(n)}_1` and its inversion `\widehat D^{(n)}_1` is `paramInvFrac_macOp`. -/
@[hjo "lem_mac2_dop_commute"]
theorem macOp_comm (q : Kˣ) {u v : K} (huv : u * v = 1)
    (f : FractionRing (MvPolynomial σ K)) :
    macOp q u (macOp q⁻¹ v f) = macOp q⁻¹ v (macOp q u f) :=
  sub_eq_zero.1 (by rw [macOp_sub_macOp q huv, macDiag_eq_zero q huv, zero_mul])

/-- **The two operators commute on a graded piece**, which is the form the uniqueness argument
uses. -/
theorem macOpComp_comm (q : Kˣ) {u v : K} (huv : u * v = 1) (d : ℕ)
    (f : symmetricHomogeneousSubmodule σ K d) :
    macOpComp q u d (macOpComp q⁻¹ v d f) = macOpComp q⁻¹ v d (macOpComp q u d f) := by
  refine Subtype.ext (IsFractionRing.injective (MvPolynomial σ K)
    (FractionRing (MvPolynomial σ K)) ?_)
  rw [algebraMap_macOpComp, algebraMap_macOpComp, algebraMap_macOpComp, algebraMap_macOpComp,
    macOp_comm q huv]

end Commute

/-! ### The inverted operator is diagonal on Macdonald's polynomials

`HJO.Mac.macOpCompInv_macPpoly`, and then `hPι`. The usual proof reads
`g := \widehat D^{(n)}_1 P_ν[X_n]` in the basis `HJO.Mac.exists_basis_macPpoly` to see that it is
a multiple of
`P_ν[X_n]` and then reads the coefficient of `m_ν[X_n]` to identify the multiple. The route
below normalises `g` by `ι(E_n(ν))` and checks the *two conditions of `HJO.Mac.macPpoly`* against
`HJO.Mac.existsUnique_isMonicEigen` instead, so that neither `HJO.Mac.exists_basis_macPpoly` nor
`HJO.Sym.eq_of_macdonaldEigenvalue_eq` is spent; what is spent instead is `ι(E_n(ν)) ≠ 0`, which is
`HJO.Sym.macdonaldEigenvalue_ne_zero` and needs `n ≥ 1`, the hypothesis the statement already
carries.
-/

section Eigen

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [Field K] [Algebra ℚ K] {d : ℕ}
  {q : Kˣ} {u : K}

omit [Algebra ℚ K] in
/-- Membership in the span of part of the monomial symmetric basis is the same question inside
`𝒮_{n,d}` and inside the polynomial ring: the basis vectors are the `m_ν[X_n]`, and the inclusion of
the submodule is injective. -/
theorem coe_mem_span_msymm_iff
    {B : Module.Basis (PartIdx σ d) K (symmetricHomogeneousSubmodule σ K d)}
    (hB : ∀ ν, (B ν : MvPolynomial σ K) = msymm σ K ν.1) (S : Set (PartIdx σ d))
    (x : symmetricHomogeneousSubmodule σ K d) :
    (x : MvPolynomial σ K) ∈ Submodule.span K {p : MvPolynomial σ K | ∃ ν ∈ S, p = msymm σ K ν.1}
      ↔ x ∈ Submodule.span K (⇑B '' S) := by
  have himg : {p : MvPolynomial σ K | ∃ ν ∈ S, p = msymm σ K ν.1}
      = (symmetricHomogeneousSubmodule σ K d).subtype '' (⇑B '' S) := by
    ext p
    constructor
    · rintro ⟨ν, hν, rfl⟩
      exact ⟨B ν, ⟨ν, hν, rfl⟩, hB ν⟩
    · rintro ⟨y, ⟨ν, hν, rfl⟩, rfl⟩
      exact ⟨ν, hν, hB ν⟩
  rw [himg, ← Submodule.map_span]
  refine ⟨fun hx => ?_, fun hx => Submodule.mem_map_of_mem hx⟩
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
  exact Subtype.coe_injective hyx ▸ hy

/-- **A second Macdonald operator, triangular on the monomial symmetric polynomials with the
diagonal entries `w_ρ` and commuting with the first, scales `P_ν[X_n]` by `w_ν`.**

This is the usual proof of `HJO.Mac.macOpCompInv_macPpoly`, normalised: `g := D' P_ν[X_n]` is an
eigenvector of `D^{(n)}_1` for `E_n(ν)` by the commutation, and it is `w_ν m_ν[X_n]` modulo the
lower `m_τ[X_n]` because `D'` is triangular and carries each lower set into itself. So
`w_ν^{-1} g` satisfies both conditions of `HJO.Mac.macPpoly` and `HJO.Mac.existsUnique_isMonicEigen`
identifies it with `P_ν[X_n]`. -/
theorem macOpComp_macPpoly_of_triangular (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (q2 : Kˣ) (u2 : K) (w : PartIdx σ d → K) {ν : PartIdx σ d} (hwν : w ν ≠ 0)
    (htri : ∀ ρ : PartIdx σ d,
      (macOpComp q2 u2 d (msymmMem σ K ρ) : MvPolynomial σ K) - w ρ • msymm σ K ρ.1
        ∈ Submodule.span K {p : MvPolynomial σ K | ∃ τ : PartIdx σ d,
            toLex (partExp σ τ) < toLex (partExp σ ρ) ∧ p = msymm σ K τ.1})
    (hcomm : ∀ f : symmetricHomogeneousSubmodule σ K d,
      macOpComp q u d (macOpComp q2 u2 d f) = macOpComp q2 u2 d (macOpComp q u d f)) :
    macOpComp q2 u2 d (macPpoly hqu ν) = w ν • macPpoly hqu ν := by
  classical
  obtain ⟨B, hB⟩ := exists_basis_symmetricHomogeneousSubmodule_msymm σ K d
  have hBmem : ∀ ρ : PartIdx σ d, B ρ = msymmMem σ K ρ := fun ρ => Subtype.ext (hB ρ)
  set S : PartIdx σ d → Set (PartIdx σ d) :=
    fun ρ => {τ : PartIdx σ d | toLex (partExp σ τ) < toLex (partExp σ ρ)} with hS
  -- the triangularity, read inside `𝒮_{n,d}`
  have htri2 : ∀ ρ : PartIdx σ d,
      macOpComp q2 u2 d (B ρ) - w ρ • B ρ ∈ Submodule.span K (⇑B '' S ρ) := by
    intro ρ
    rw [← coe_mem_span_msymm_iff hB, Submodule.coe_sub, SetLike.val_smul, hBmem ρ,
      coe_msymmMem]
    exact htri ρ
  -- `D'` carries each lower set into itself
  have hmap : ∀ ρ : PartIdx σ d, ∀ x ∈ Submodule.span K (⇑B '' S ρ),
      macOpComp q2 u2 d x ∈ Submodule.span K (⇑B '' S ρ) := by
    intro ρ x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨τ, hτ, rfl⟩ := hy
        have h2 : Submodule.span K (⇑B '' S τ) ≤ Submodule.span K (⇑B '' S ρ) :=
          Submodule.span_mono (Set.image_mono fun π hπ =>
            show toLex (partExp σ π) < toLex (partExp σ ρ) from
              lt_trans (show toLex (partExp σ π) < toLex (partExp σ τ) from hπ)
                (show toLex (partExp σ τ) < toLex (partExp σ ρ) from hτ))
        have h4 := Submodule.add_mem _ (h2 (htri2 τ))
          (Submodule.smul_mem _ (w τ) (Submodule.subset_span ⟨τ, hτ, rfl⟩))
        rwa [sub_add_cancel] at h4
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  -- `P_ν[X_n]` is `m_ν[X_n]` modulo the lower set, so `g` is `w_ν m_ν[X_n]` modulo it
  have hP : macPpoly hqu ν - B ν ∈ Submodule.span K (⇑B '' S ν) := by
    rw [← coe_mem_span_msymm_iff hB, Submodule.coe_sub, hB ν]
    exact macPpoly_sub_msymm_mem_span hqu ν
  have hg : macOpComp q2 u2 d (macPpoly hqu ν) - w ν • B ν
      ∈ Submodule.span K (⇑B '' S ν) := by
    have h1 := hmap ν _ hP
    rw [map_sub] at h1
    have h2 := Submodule.add_mem _ h1 (htri2 ν)
    rwa [sub_add_sub_cancel] at h2
  -- the two conditions of `HJO.Mac.macPpoly` for the normalised `g`
  have hkey : (w ν)⁻¹ • macOpComp q2 u2 d (macPpoly hqu ν) = macPpoly hqu ν := by
    refine eq_macPpoly hqu ⟨?_, ?_⟩
    · rw [map_smul, hcomm, macOpComp_macPpoly, map_smul, smul_comm]
    · have h := (coe_mem_span_msymm_iff hB (S ν)
        ((w ν)⁻¹ • (macOpComp q2 u2 d (macPpoly hqu ν) - w ν • B ν))).2
        (Submodule.smul_mem _ _ hg)
      rw [SetLike.val_smul, Submodule.coe_sub, SetLike.val_smul, smul_sub, smul_smul,
        inv_mul_cancel₀ hwν, one_smul, hB ν] at h
      rw [SetLike.val_smul]
      exact h
  calc macOpComp q2 u2 d (macPpoly hqu ν)
      = w ν • ((w ν)⁻¹ • macOpComp q2 u2 d (macPpoly hqu ν)) := by
        rw [smul_smul, mul_inv_cancel₀ hwν, one_smul]
    _ = w ν • macPpoly hqu ν := by rw [hkey]

/-- **The inverted operator is diagonal on Macdonald's polynomials**:
`\widehat D^{(n)}_1 P_ν[X_n] = ι(E_n(ν)) P_ν[X_n]`.

`\widehat D^{(n)}_1` is `D^{(n)}_1` at `q^{-1}` and `ι(u)` (`macOpCompInv_eq_macOpComp`), it is
triangular with the diagonal entries `ι(E_n(ρ))` (`HJO.Mac.exists_eq_paramInvFrac_macOp_msymm`), and
it commutes with `D^{(n)}_1` (`HJO.Mac.macOp_comm`); `macOpComp_macPpoly_of_triangular` is the rest.
The hypothesis `n ≥ 1` is `hn`, and it is genuinely needed: at the empty alphabet every eigenvalue
is `0` and the normalisation has nothing to divide by. -/
@[hjo "lem_mac2_dop_inv_eigen"]
theorem macOpCompInv_macPpoly (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (hn : 0 < Fintype.card σ) {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c)
    (hιq : ι (q : K) = ((q⁻¹ : Kˣ) : K)) (hιu : ι u * u = 1) (ν : PartIdx σ d) :
    macOpCompInv ι q u d (macPpoly hqu ν)
      = ι (HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ ν))
        • macPpoly hqu ν := by
  have hq2 : Units.map (ι : K →* K) q = q⁻¹ := Units.ext hιq
  have hEq : ∀ f : symmetricHomogeneousSubmodule σ K d,
      macOpCompInv ι q u d f = macOpComp q⁻¹ (ι u) d f := fun f => by
    rw [macOpCompInv_eq_macOpComp hιι, hq2]
  rw [hEq]
  refine macOpComp_macPpoly_of_triangular hqu q⁻¹ (ι u)
    (fun ρ => ι (HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ ρ)))
    ?_ (fun ρ => ?_) fun f => ?_
  · intro h0
    refine HJO.Sym.macdonaldEigenvalue_ne_zero hqu hn (partDiagram σ ν) ?_
    have h := hιι (HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ ν))
    rw [h0, map_zero] at h
    exact h.symm
  · rw [← hEq]
    exact macOpCompInv_msymm_sub_smul_mem_span (HJO.Standing.u_ne_zero hqu) ι ρ
  · exact macOpComp_comm q (by rw [mul_comm]; exact hιu) d f

/-- **The inverted operator is triangular on the monomial symmetric polynomials**, read on the
rational function field where `HJO.Mac.macOpInv` lives:
`\widehat D^{(n)}_1 m_μ[X_n]` is the image of a polynomial which is `ι(E_n(μ)) m_μ[X_n]` modulo the
`m_ν[X_n]` with `\bar\nu <_lex \bar\mu`.

Its graded-piece form, which is what the argument above consumes, is
`HJO.Mac.macOpCompInv_msymm_sub_smul_mem_span`; the two agree because the graded operator is the
fraction-field one (`macOpCompInv_eq_macOpComp` and `paramInvFrac_macOp`). The hypothesis `u ≠ 0`
is the one `HJO.Mac.macOpComp_msymm_sub_smul_mem_span` carries, and it holds wherever
`𝕜 = ℚ(q, u)`. -/
@[hjo "lem_mac2_dop_inv_triangular"]
theorem exists_eq_paramInvFrac_macOp_msymm (hu : u ≠ 0) {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c)
    (μ : PartIdx σ d) :
    ∃ g : MvPolynomial σ K,
      paramInvFrac (ringEquivOfInvolutive hιι) (macOp q u
            (paramInvFrac (ringEquivOfInvolutive hιι)
              (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (msymm σ K μ.1))))
          = algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) g ∧
        g - ι (HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ))
              • msymm σ K μ.1
          ∈ Submodule.span K {p : MvPolynomial σ K | ∃ ν : PartIdx σ d,
              toLex (partExp σ ν) < toLex (partExp σ μ) ∧ p = msymm σ K ν.1} := by
  refine ⟨(macOpCompInv ι q u d (msymmMem σ K μ) : MvPolynomial σ K), ?_,
    macOpCompInv_msymm_sub_smul_mem_span hu ι μ⟩
  rw [paramInvFrac_macOp hιι, macOpCompInv_eq_macOpComp hιι, ← coe_msymmMem μ,
    ← algebraMap_macOpComp]

/-- **Macdonald's polynomials in a finite alphabet are invariant under inverting both
parameters**: `\widehat\iota_n(P_ν[X_n]) = P_ν[X_n]`.

`HJO.Mac.paramInvComp_macPpoly_of_eigen` with its hypothesis discharged by
`HJO.Mac.macOpCompInv_macPpoly`. -/
@[hjo "lem_mac2_ppoly_param_inv_finite"]
theorem paramInvComp_macPpoly (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (hn : 0 < Fintype.card σ) {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c)
    (hιq : ι (q : K) = ((q⁻¹ : Kˣ) : K)) (hιu : ι u * u = 1) (ν : PartIdx σ d) :
    paramInvComp ι d (macPpoly hqu ν) = macPpoly hqu ν :=
  paramInvComp_macPpoly_of_eigen hqu hιι (macOpCompInv_macPpoly hqu hn hιι hιq hιu ν)

end Eigen

end HJO.Mac

/-! ### `hPι`, and the collinear residue

`HJO.Sym.coeffSubst_macPfun`, and the two composition points of
`HJO/Macdonald/PpolyParamInv.lean` with their remaining hypothesis discharged.
-/

namespace HJO.Sym

open HJO.Mac

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

/-- **Macdonald's polynomials are invariant under inverting both parameters**: `ς(P_μ) = P_μ`.

This is `HJO.Sym.coeffSubst_macPfun_of_eigen` with its hypothesis `hinv` discharged by
`HJO.Mac.macOpCompInv_macPpoly`. The alphabet is `HJO.Mac.baseAlphabet μ`, of cardinality
`max(|μ|, 1) ≥ 1`, so the hypothesis `n ≥ 1` of `HJO.Mac.macOpCompInv_macPpoly` holds. -/
@[hjo "lem_mac_ppoly_param_inv"]
theorem coeffSubst_macPfun (hqu : AlgebraicIndependent ℤ ![(q : K), u]) {ι : K →+* K}
    (hιι : ∀ c : K, ι (ι c) = c) (hιq : ι (q : K) = ((q⁻¹ : Kˣ) : K)) (hιu : ι u * u = 1)
    (μ : YoungDiagram) :
    coeffSubst ι (macPfun hqu μ) = macPfun hqu μ :=
  coeffSubst_macPfun_of_eigen hqu hιι
    (macOpCompInv_macPpoly hqu
      (by simp only [baseAlphabet, Fintype.card_fin]; omega) hιι hιq hιu (baseIdx μ))

end HJO.Sym

/-! ### `hPι` at the standing field, and what is left of the collinear side -/

namespace HJO.Standing

open HJO.Ascent HJO.Sym HJO.Mac

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- **`hPι` at the standing field**, in exactly the shape
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_dop_param` asks for, and with nothing
assumed: `ς` fixes `P_μ`.

The three properties of `ι` that `HJO.Sym.coeffSubst_macPfun` needs are
`HJO.Ascent.paramQUInvHom_involutive`, `HJO.Ascent.paramQUInvHom_paramQ` and
`HJO.Ascent.paramQUInvHom_paramU`, the last against `HJO.Standing.paramU_ne_zero`. -/
theorem coeffSubst_macPfun_param (μ : YoungDiagram) :
    coeffSubst (paramQUInvHom K) (macPfun (algebraicIndependent_paramQUnit K) μ)
      = macPfun (algebraicIndependent_paramQUnit K) μ :=
  HJO.Sym.coeffSubst_macPfun (algebraicIndependent_paramQUnit K) (paramQUInvHom_involutive K)
    (by rw [paramQUnit_val, paramQUInvHom_paramQ, Units.val_inv_eq_inv_val, paramQUnit_val])
    (by rw [paramQUInvHom_paramU, inv_mul_cancel₀ (paramU_ne_zero K)]) μ

/-- **The collinear residue, with `hPι` discharged**: an unnormalised Macdonald eigenbasis exists at
the standing field given only `hdop`, `HJO.Standing.dop_zero_smul_macHtilde_param`
(Garsia--Haiman--Tesler's Theorem 1.2 (1.11) a).

Against `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_of_dop_and_eigen_param` this has the second
hypothesis `hinv` --- `HJO.Mac.macOpCompInv_macPpoly` --- discharged as well. Together with
`HJO.Sym.HasPieriEigenfamily`, that one clause is what the collinear side asks for at this point;
it is proved as `HJO.Standing.dop_zero_smul_macHtilde_param`. -/
theorem hasUnnormalisedMacdonaldEigenbasis_of_dop_param
    (hdop : ∀ μ : YoungDiagram,
      Dop (paramQ K) (paramU K) 0
          (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ)
        = -(HJO.Sym.paramProduct (paramQ K) (paramU K) * cellSum (paramQ K) (paramU K) μ - 1) •
            macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ) :
    HasUnnormalisedMacdonaldEigenbasis (paramQUInvHom K) (paramQ K) (paramU K) :=
  hasUnnormalisedMacdonaldEigenbasis_macHtilde_dop_param K hdop (coeffSubst_macPfun_param K)

end HJO.Standing

