/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.GesselTruncation
public import HJO.Classical.HsymmComposition
public import HJO.Classical.OmegaInvolution
public import HJO.CarlssonMellit.Parameters
public import HJO.Symmetric.UkRegular
public meta import HJO.Attr

/-! # The standard involution exchanges `h` and `e`, and the three sign identities

Five short results about `ω`, together with the conjugate involution
`ω̄` the Carlsson--Mellit statement is phrased with.

* `ω(h_n) = e_n` and `ω(h_α) = e_α`: Newton's identity for `h` carries the sign `(-1)^{k-1}` of
  `ω(p_k)` onto Newton's identity for `e`.
* `ω₋ = σ_{-1} ∘ ω`: the two scalars `(-1)^{k-1}` and `(-1)^k` multiply to `-1` at every `k`.
* `ι ∘ σ_{-1} = ng ∘ ι`: a realisation turns the scaling of the alphabet by `-1` into the
  negation of the letters.
* `ng(F_{n,S}) = (-1)^n F_{n,S}`: a fundamental of degree `n` is homogeneous of degree `n`.

## Main definitions

* `HJO.Sym.omegaBar`: `ω̄ = ω₋ ∘ cj`.

## Main statements

* `HJO.Sym.omegaStd_completeHomog`.
* `HJO.Sym.omegaStd_completeHomogComp`.
* `HJO.Sym.plethNegate_eq_plethScale_omegaStd`.
* `HJO.Sym.realisation_plethScale_neg_one`.
* `HJO.ParkingFunctions.letterNegate_gessel`.

## Implementation notes

`Λ` is the polynomial ring on the power sums, so each of the two identities between endomorphisms
is `MvPolynomial.algHom_ext` against a computation on one generator; no well-definedness enters.

The `C`-form of Newton's identity for `e` is a one-line unfolding of
`HJO.Sym.elemSymm`, restated privately here for the same reason `HJO.CreationSeeds.LogDeriv`
restates `elemSymm_zero`: the only other copy, `HJO.PhiE.elemSymm_succ`, sits downstream of all the
evaluation maps, which this file has no other reason to import.

*Neither sign lemma needs the hypothesis `n ≥ 1`.* `HJO.ParkingFunctions.letterNegate_gessel` is
stated for every `n` and every `S`, with no containment in the window: the argument is that every
monomial of `F_{n,S}` has total degree `n`, which holds of the totalization too, `gessel` being
supported on the exponent vectors of tuples of length `n` whatever `S` is. That is a generalisation.

`ω̄` is a `RingHom` and not an `AlgHom`: `cj` moves the coefficients by an automorphism of the base,
so it is semilinear, exactly as `HJO.Sym.paramInvLambda` records.

## References

This file formalises `HJO.Sym.omegaStd_completeHomog`, `HJO.Sym.omegaStd_completeHomogComp`,
`HJO.Sym.plethNegate_eq_plethScale_omegaStd`, `HJO.Sym.realisation_plethScale_neg_one`,
`HJO.ParkingFunctions.letterNegate_gessel` and `HJO.Sym.omegaBar`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The involution exchanges the two families -/

section Newton

variable (K : Type*) [CommRing K] [Algebra ℚ K]

/-- Newton's identity in the form defining the elementary symmetric functions. The same one-line
unfolding as `HJO.PhiE.elemSymm_succ`, repeated here so that this file need not import the
evaluation-map files. -/
private theorem elemSymm_succ' (n : ℕ) :
    elemSymm K (n + 1) = MvPolynomial.C (algebraMap ℚ K ((n + 1 : ℚ)⁻¹)) *
      ∑ k ∈ range (n + 1), (-1) ^ k * powerSum K (k + 1) * elemSymm K (n - k) := by
  rw [elemSymm]

/-- **The involution exchanges the two families.** `ω(h_n) = e_n` for every
`n ≥ 0`.

Newton's identity presents `h_n` as `(1/n)∑_k p_k h_{n-k}`; `ω` fixes the scalar, is multiplicative,
and multiplies `p_k` by `(-1)^{k-1}`, so the image is Newton's identity for `e_n`. -/
@[hjo "lem_om_omega_hsymm"]
theorem omegaStd_completeHomog (n : ℕ) : omegaStd K (completeHomog K n) = elemSymm K n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [CopPower.completeHomog_zero, CreationSeeds.elemSymm_zero, map_one]
    | m + 1 =>
      rw [UkRegular.completeHomog_succ, elemSymm_succ' K m, map_mul, map_sum]
      refine congrArg₂ _ ?_ (Finset.sum_congr rfl fun k hk => ?_)
      · rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      · rw [map_mul, omegaStd_powerSum K k.succ_pos, Nat.succ_sub_one,
          ih (m - k) (by omega)]

/-- **The involution on a complete homogeneous product.**
`ω(h_α) = e_α` for every composition `α`: `ω` is multiplicative and unital, and exchanges the two
families factor by factor. -/
@[hjo "lem_om_omega_hsymm_comp"]
theorem omegaStd_completeHomogComp (α : List ℕ) :
    omegaStd K (completeHomogComp K α) = elemSymmComp K α := by
  induction α with
  | nil => rw [completeHomogComp_nil, elemSymmComp_nil, map_one]
  | cons a α ih =>
    rw [completeHomogComp_cons, elemSymmComp_cons, map_mul, omegaStd_completeHomog K a, ih]

end Newton

/-! ### Negating the alphabet is the involution followed by a scaling -/

/-- **Negating the alphabet is the involution followed by a scaling.**
`ω₋(f) = σ_{-1}(ω(f))` for every `f ∈ Λ`.

Both sides are `K`-algebra endomorphisms of the polynomial ring on the power sums, so it is enough
to compare them on `p_k`: the left multiplies it by `-1`, the right by
`(-1)^{k-1}(-1)^k = (-1)^{2k-1} = -1`. -/
@[hjo "lem_negate_omega_scale"]
theorem plethNegate_eq_plethScale_omegaStd (K : Type*) [CommRing K] (f : Lambda K) :
    plethNegate K f = plethScale (-1 : K) (omegaStd K f) := by
  have hcomp : plethNegate K = (plethScale (-1 : K)).comp (omegaStd K) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, plethNegate_X, omegaStd, MvPolynomial.aeval_X, map_mul, map_pow,
      map_neg, map_one, plethScale, diagScale_X,
      show ((-1 : Lambda K) ^ i) = MvPolynomial.C ((-1 : K) ^ i) from by
        rw [map_pow, map_neg, map_one],
      ← mul_assoc, ← MvPolynomial.C_mul, ← pow_add,
      show ((-1 : K) ^ (i + (i + 1))) = -1 from Odd.neg_one_pow ⟨i, by ring⟩,
      map_neg, map_one, neg_one_mul]
  exact congrArg (fun φ => φ f) hcomp

/-! ### A realisation turns the scaling by `-1` into negating the letters -/

section Realisation

variable {K : Type*} [CommRing K] {ι : Lambda K →ₐ[K] AlphabetSeries K}

/-- **Negating the letters of a realised power sum** multiplies it by `(-1)^k`: a realisation puts
a `1` at each `x_i^k` and nothing else, and `ng` multiplies the coefficient of a monomial of total
degree `k` by `(-1)^k`. -/
theorem letterNegate_realisation_powerSum (hι : IsRealisation ι) (k : ℕ) :
    letterNegate K (ι (powerSum K (k + 1)))
      = ((-1 : K) ^ (k + 1)) • ι (powerSum K (k + 1)) := by
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_letterNegate, map_smul, smul_eq_mul]
  by_cases h : ∃ i, d = Finsupp.single i (k + 1)
  · obtain ⟨i, rfl⟩ := h
    rw [Finsupp.sum_single_index rfl]
  · rw [hι.coeff_of_ne k d (by simpa using h), mul_zero, mul_zero]

/-- **A realisation turns the scaling by `-1` into negating the
letters.** `ι(σ_{-1}(f)) = ng(ι(f))` for every `f ∈ Λ`.

Both sides are `K`-algebra homomorphisms out of the polynomial ring on the power sums, so it is
enough to compare them on `p_k`, where both give `(-1)^k∑_i x_i^k`. -/
@[hjo "lem_scale_neg_realisation"]
theorem realisation_plethScale_neg_one (hι : IsRealisation ι) (f : Lambda K) :
    ι (plethScale (-1 : K) f) = letterNegate K (ι f) := by
  have hcomp : ι.comp (plethScale (-1 : K)) = (letterNegate K).comp ι := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, plethScale, diagScale_X,
      show (MvPolynomial.X i : Lambda K) = powerSum K (i + 1) from by
        rw [powerSum, Nat.add_sub_cancel],
      ← MvPolynomial.smul_eq_C_mul, map_smul, letterNegate_realisation_powerSum hι i]
  exact congrArg (fun φ => φ f) hcomp

end Realisation

/-! ### The conjugate involution -/

/-- **The conjugate involution** `ω̄ = ω₋ ∘ cj`, the composite of the negation of
the alphabet with the inversion of the parameters. It is a `RingHom` and not an `AlgHom`, `cj`
moving the coefficients by the automorphism `σ` of the base. -/
@[hjo "def_cm_omegabar"]
noncomputable def omegaBar {K : Type*} [CommRing K] (σ : K ≃+* K) : Lambda K →+* Lambda K :=
  (plethNegate K : Lambda K →+* Lambda K).comp (paramInvLambda σ : Lambda K →+* Lambda K)

variable {K : Type*} [CommRing K]

/-- `ω̄` is `ω₋` applied to the parameter conjugate, which is its definition. -/
@[hjo "def_cm_omegabar"]
theorem omegaBar_apply (σ : K ≃+* K) (f : Lambda K) :
    omegaBar σ f = plethNegate K (paramInvLambda σ f) := rfl

/-- **`ω̄` negates each power sum**, `cj` fixing it: `ω̄(p_k) = -p_k`. -/
theorem omegaBar_powerSum (σ : K ≃+* K) (k : ℕ) :
    omegaBar σ (powerSum K k) = -powerSum K k := by
  rw [omegaBar_apply, paramInvLambda_powerSum, plethNegate_powerSum]

/-- **`ω̄` moves a scalar by `σ` and negates it**: `ω̄(c) = -σ(c)` would be false — `ω₋` is unital —
and the truth is `ω̄(c) = σ(c)`, the negation touching only the power sums. -/
theorem omegaBar_C (σ : K ≃+* K) (c : K) :
    omegaBar σ (MvPolynomial.C c) = MvPolynomial.C (σ c) := by
  rw [omegaBar_apply, paramInvLambda_C, plethNegate, diagScale_C]

end HJO.Sym

namespace HJO.ParkingFunctions

/-- **Negating the letters of a fundamental.**
`ng(F_{n,S}) = (-1)^n F_{n,S}`.

Every monomial of `F_{n,S}` is a product of exactly `n` letters, so `ng` multiplies each of them by
the same scalar `(-1)^n`. Neither `n ≥ 1` nor `S ⊆ \{1, …, n-1\}` is used: the degree argument
applies to the totalization as well. -/
@[hjo "lem_letter_negation_gessel"]
theorem letterNegate_gessel (K : Type*) [CommRing K] (n : ℕ) (S : Finset ℕ) :
    Sym.letterNegate K (gessel K n S) = ((-1 : K) ^ n) • gessel K n S := by
  refine MvPowerSeries.ext fun d => ?_
  rw [Sym.coeff_letterNegate, map_smul, smul_eq_mul]
  by_cases h : (d.sum fun _ e => e) = n
  · rw [h]
  · rw [coeff_gessel_eq_zero K ?_, mul_zero, mul_zero]
    rintro ⟨i, -, -, rfl⟩
    refine h ?_
    set w : Fin n → ℕ := fun k => i ((k : ℕ) + 1) with hw
    have hd : ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1 = Sym.wordExponent w :=
      sum_Icc_single_eq_wordExponent n i
    have hall : ∀ k, w k ∈ (Sym.wordExponent w).support := fun k =>
      (Sym.mem_support_wordExponent w (w k)).2 ⟨k, rfl⟩
    rw [hd, Finsupp.sum]
    exact Sym.sum_wordExponent w hall

end HJO.ParkingFunctions
