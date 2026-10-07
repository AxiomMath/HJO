/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.NegateHsymm
public import HJO.Classical.OmegaExchange
public import HJO.Collinear.ShiftPair
public meta import HJO.Attr

/-! # The conjugate involution exchanges the two basic operators

`HJO.Sym.omegaBar_dop`: `ω̄(D_1f) = D^*_1(ω̄f)`, where `ω̄ = ω₋ ∘ cj` is the conjugate involution of
`HJO.Sym.omegaBar` — negate the alphabet and invert the parameters.

## The three ingredients

* **`ω̄` intertwines the two displacements.** `HJO.Sym.map_plethShift_omegaBar`: applying `ω̄` to
  every coefficient of `f[X + M/z]` gives `(ω̄f)[X - M̃/z]`. On `p_k` the left sends
  `p_k + (1-q^k)(1-u^k)z^{-k}` to `-p_k + (1-q^{-k})(1-u^{-k})z^{-k}`, and so does the right, the
  minus sign of `δ*` being the virtual difference of alphabets rather than a squared scalar.
* **`ω̄` fixes each elementary function up to the exchange.** `cj` fixes `e_r`, its defining
  recursion having rational coefficients (`HJO.Sym.paramInvLambda_elemSymm`, which is
  `RingHom.map_rat_algebraMap` inside the recursion), and `ω₋(e_r) = (-1)^rh_r`
  (`HJO.Sym.plethNegate_elemSymm`, which is `HJO.Sym.plethNegate_completeHomog` conjugated by the
  involutivity of `ω₋`). So `ω̄((-1)^{k+j}e_{k+j}) = h_{k+j}`, the two signs cancelling — which is
  why the statement carries none.
* **`ω̄` passes the pairing.** `HJO.Sym.map_coeffPairing`: a ring homomorphism applied to
  `∑_j A_j c_j` is the same pairing of the moved coefficients against the moved family.

## The `k = 1` is not where the argument stops

Nothing above reads `k`, so the statement is proved for every `k ≥ 0`: `ω̄(D_kf) = D^*_k(ω̄f)`, and
the identity `ω̄(D_1f) = D^*_1(ω̄f)` is the instance at `k = 1`. That is a generalisation, not a
weakening.

**The absence of a sign is the point.** The familiar relation
`↓D_k↓ = (-1)^kD^*_k` is about a *different* involution `↓`, which negates the alphabet in the sense
`p_k ↦ (-1)^{k-1}p_k` and inverts the parameters; `↓` and `ω̄` differ by `(-1)^k` on a homogeneous
element of degree `k`, which is exactly the sign at issue. Reading one for the other
would wrongly suggest an error in that relation.

## References

This file proves `HJO.Sym.omegaBar_dop`, on the definitions `HJO.Sym.omegaBar`,
`HJO.Sym.plethNegate`, `HJO.Sym.paramInvLambda`, `HJO.Sym.DopInt`, `HJO.Sym.DopStar`,
`HJO.Sym.plethShift` and `HJO.Sym.plethShiftStar`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The two involutions on the elementary functions -/

section Elementary

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- **`cj` fixes every elementary symmetric function.** Its defining recursion has coefficients in
the image of `ℚ`, which every ring endomorphism of a `ℚ`-algebra fixes
(`RingHom.map_rat_algebraMap`), and it fixes each power sum. -/
theorem paramInvLambda_elemSymm (σ : K ≃+* K) (n : ℕ) :
    paramInvLambda σ (elemSymm K n) = elemSymm K n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [elemSymm, map_one]
    | m + 1 =>
      have hQ : ∀ c : ℚ, σ (algebraMap ℚ K c) = algebraMap ℚ K c := fun c =>
        RingHom.map_rat_algebraMap (σ : K →+* K) c
      rw [elemSymm, map_mul, paramInvLambda_C, hQ, map_sum]
      refine congrArg _ (Finset.sum_congr rfl fun k hk => ?_)
      rw [Finset.mem_range] at hk
      rw [map_mul, map_mul, map_pow, map_neg, map_one, paramInvLambda_powerSum,
        ih (m - k) (by omega)]

omit [Algebra ℚ K] in
/-- `ω₋` is an involution: it scales every power sum by `-1` twice. -/
theorem plethNegate_plethNegate (f : Lambda K) :
    plethNegate K (plethNegate K f) = f := by
  have key : (plethNegate K).comp (plethNegate K) = AlgHom.id K (Lambda K) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, plethNegate_X, map_neg, plethNegate_X, neg_neg, AlgHom.id_apply]
  exact congrArg (fun g : Lambda K →ₐ[K] Lambda K => g f) key

/-- **`ω₋(e_n) = (-1)^n h_n`**, the companion of `HJO.Sym.plethNegate_completeHomog`:
apply `ω₋` to `ω₋(h_n) = (-1)^ne_n` and use that `ω₋` is an involution. -/
theorem plethNegate_elemSymm (n : ℕ) :
    plethNegate K (elemSymm K n) = (-1) ^ n * completeHomog K n := by
  have h := plethNegate_plethNegate (K := K) (completeHomog K n)
  rw [plethNegate_completeHomog, map_mul, map_pow, map_neg, map_one] at h
  have hsq : ((-1 : Lambda K)) ^ n * ((-1 : Lambda K)) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc plethNegate K (elemSymm K n)
      = ((-1 : Lambda K) ^ n * (-1) ^ n) * plethNegate K (elemSymm K n) := by rw [hsq, one_mul]
    _ = (-1 : Lambda K) ^ n * ((-1) ^ n * plethNegate K (elemSymm K n)) := by ring
    _ = (-1 : Lambda K) ^ n * completeHomog K n := by rw [h]

omit [Algebra ℚ K] in
/-- `ω̄` fixes the generator `i` up to sign, `cj` fixing it and `ω₋` negating it. -/
@[simp]
theorem omegaBar_X (σ : K ≃+* K) (i : ℕ) :
    omegaBar σ (MvPolynomial.X i) = -MvPolynomial.X i := by
  rw [omegaBar_apply, paramInvLambda_X, plethNegate_X]

/-- **`ω̄(e_n) = (-1)^n h_n`**: `cj` fixes `e_n` and `ω₋` exchanges the two families. -/
theorem omegaBar_elemSymm (σ : K ≃+* K) (n : ℕ) :
    omegaBar σ (elemSymm K n) = (-1) ^ n * completeHomog K n := by
  rw [omegaBar_apply, paramInvLambda_elemSymm, plethNegate_elemSymm]

/-- **`ω̄` carries the alternating elementary family to the complete homogeneous one.** The sign of
`(-1)^n e_n` and the sign `ω̄` introduces in `e_n` cancel, which is why
`HJO.Sym.omegaBar_dop` has none. -/
theorem omegaBar_neg_one_pow_mul_elemSymm (σ : K ≃+* K) (n : ℕ) :
    omegaBar σ ((-1) ^ n * elemSymm K n) = completeHomog K n := by
  rw [map_mul, map_pow, map_neg, map_one, omegaBar_elemSymm, ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_mul]

end Elementary

/-! ### A ring homomorphism passes the coefficient pairing -/

section Pairing

variable {K : Type*} [CommRing K]

/-- **A ring homomorphism passes the pairing of `HJO.Sym.DopInt`**: applying `φ` to `∑_j A_jc_j` is
the pairing of the moved coefficients against the moved family. Both sides are additive in the
polynomial, so it is enough to check a monomial, where the pairing is a single product. -/
theorem map_coeffPairing (φ : Lambda K →+* Lambda K) (c : ℕ → Lambda K)
    (P : Polynomial (Lambda K)) :
    φ (coeffPairing c P) = coeffPairing (fun j => φ (c j)) (P.map φ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.map_add, map_add, hP, hQ]
  | monomial j a =>
    have hL : coeffPairing c (Polynomial.monomial j a) = a * c j :=
      Polynomial.sum_monomial_index a (fun j A => A * c j) (by simp)
    have hR : coeffPairing (fun j => φ (c j)) (Polynomial.monomial j (φ a)) = φ a * φ (c j) :=
      Polynomial.sum_monomial_index (φ a) (fun j A => A * φ (c j)) (by simp)
    rw [hL, Polynomial.map_monomial, hR, map_mul]

end Pairing

/-! ### `ω̄` intertwines the two displacements -/

section Displacement

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- **`ω̄` intertwines the two displacements.** Applying `ω̄` to every coefficient of `f[X + M/z]`
gives `(ω̄f)[X - M̃/z]`.

Both sides are ring homomorphisms out of `Λ`, so they are compared on the constants — where `cj`
moves the scalar by `σ` and `ω₋` fixes it — and on the power sums, where the left gives
`-p_k + σ((1-q^k)(1-u^k))z^{-k}` and the right `-p_k + (1-q^{-k})(1-u^{-k})z^{-k}`. Those agree
because `σ` is a ring homomorphism sending `q` to `q⁻¹` and `u` to `u⁻¹`. -/
theorem map_plethShift_omegaBar {σ : L ≃+* L} {q u : L} (hq : σ q = q⁻¹) (hu : σ u = u⁻¹)
    (f : Lambda L) :
    (plethShift q u f).map (omegaBar σ) = plethShiftStar q u (omegaBar σ f) := by
  have hscal : ∀ i : ℕ, σ ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))
      = (1 - (q ^ (i + 1))⁻¹) * (1 - (u ^ (i + 1))⁻¹) := by
    intro i
    simp only [map_mul, map_sub, map_one, map_pow, hq, hu, inv_pow]
  have key : (Polynomial.mapRingHom (omegaBar σ)).comp
        (plethShift q u : Lambda L →+* Polynomial (Lambda L))
      = ((plethShiftStar q u : Lambda L →+* Polynomial (Lambda L))).comp
        (omegaBar σ : Lambda L →+* Lambda L) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe,
        plethShift_C, omegaBar_C, plethShiftStar_C, Polynomial.coe_mapRingHom,
        Polynomial.map_C, omegaBar_C]
    · have hL : ((Polynomial.mapRingHom (omegaBar σ)).comp
            (plethShift q u : Lambda L →+* Polynomial (Lambda L))) (MvPolynomial.X i)
          = -Polynomial.C (MvPolynomial.X i : Lambda L)
            + Polynomial.C (MvPolynomial.C ((1 - (q ^ (i + 1))⁻¹) * (1 - (u ^ (i + 1))⁻¹)))
              * Polynomial.X ^ (i + 1) := by
        rw [RingHom.comp_apply, RingHom.coe_coe, plethShift_gen, Polynomial.coe_mapRingHom,
          Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
          Polynomial.map_pow, Polynomial.map_X, omegaBar_X, omegaBar_C, hscal, map_neg]
      have hR : (((plethShiftStar q u : Lambda L →+* Polynomial (Lambda L))).comp
            (omegaBar σ : Lambda L →+* Lambda L)) (MvPolynomial.X i)
          = -Polynomial.C (MvPolynomial.X i : Lambda L)
            + Polynomial.C (MvPolynomial.C ((1 - (q ^ (i + 1))⁻¹) * (1 - (u ^ (i + 1))⁻¹)))
              * Polynomial.X ^ (i + 1) := by
        rw [RingHom.comp_apply, RingHom.coe_coe, omegaBar_X, map_neg, plethShiftStar_gen]
        ring
      rw [hL, hR]
  exact congrArg (fun g : Lambda L →+* Polynomial (Lambda L) => g f) key

/-- **The conjugate involution exchanges the two basic operators.** `ω̄(D_kf) = D^*_k(ω̄f)` for
every `k ≥ 0` and every `f ∈ Λ`; the identity usually stated is the case `k = 1`.

`ω̄` passes the pairing (`HJO.Sym.map_coeffPairing`), carries the displacement to the starred one
(`HJO.Sym.map_plethShift_omegaBar`), and carries the family `(-1)^{k+j}e_{k+j}` that `D_k` pairs
against to the family `h_{k+j}` that `D^*_k` pairs against
(`HJO.Sym.omegaBar_neg_one_pow_mul_elemSymm`) — the two signs cancelling, which is why the statement
carries none. -/
@[hjo "lem_cm_omegabar_dop"]
theorem omegaBar_dop {σ : L ≃+* L} {q u : L} (hq : σ q = q⁻¹) (hu : σ u = u⁻¹) (k : ℕ)
    (f : Lambda L) :
    omegaBar σ (Dop q u k f) = DopStar q u k (omegaBar σ f) := by
  have hfam : (fun j => omegaBar σ ((-1) ^ (k + j) * elemSymm L (k + j)))
      = fun j => completeHomog L (k + j) :=
    funext fun j => omegaBar_neg_one_pow_mul_elemSymm σ (k + j)
  calc omegaBar σ (Dop q u k f)
      = omegaBar σ (coeffPairing (fun j => (-1) ^ (k + j) * elemSymm L (k + j))
          (plethShift q u f)) := rfl
    _ = coeffPairing (fun j => omegaBar σ ((-1) ^ (k + j) * elemSymm L (k + j)))
          ((plethShift q u f).map (omegaBar σ)) :=
        map_coeffPairing _ _ _
    _ = coeffPairing (fun j => completeHomog L (k + j)) (plethShiftStar q u (omegaBar σ f)) := by
        rw [hfam, map_plethShift_omegaBar hq hu]
    _ = DopStar q u k (omegaBar σ f) := rfl

end Displacement

end HJO.Sym
