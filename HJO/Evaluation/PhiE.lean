/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.ThetaSymmetry
public import HJO.Evaluation.PhiHom
public import HJO.Defs

/-! # The evaluation map on the elementary symmetric functions

The elementary symmetric function `e_N` is weighted homogeneous of degree `N`, the generator
`p_k` weighing `k`, so the sign the evaluation map carries is a single power of `-1` and the
scaling of the alphabet by `(-1) ^ (b + 1)` acts on `e_N` as the scalar `(-1) ^ (N (b + 1))`.
The evaluation map on `e_N` is therefore the specialisation of one scalar: the sign extraction
of the operator attached to `e_N`, applied to `1`.

That scalar is the value at the two parameters of the generating polynomial of all
below-diagonal `(aN, bN)`-paths by hook count and area, and it is unchanged when the two
parameters are exchanged. Once exchanged, a specialisation sending the second parameter to `1`
kills the hook count and leaves the area, so the image of the scalar is the area generating
polynomial of those paths, evaluated at the specialised first parameter.

The compositional rational shuffle identity, the reading of sign extraction on the fundamental
quasisymmetric functions and the expansion of `e_N` over the compositions of `N` are taken as
explicit hypotheses; none of the three is proved here.
-/

@[expose] public section

open Finset

namespace HJO.PhiE

open MvPolynomial HJO.Sym HJO.Multiplication HJO.Paths HJO.ThetaSymmetry

/-! ### The elementary symmetric functions are homogeneous -/

/-- The elementary symmetric function of degree `0` is `1`. -/
lemma elemSymm_zero (K : Type*) [CommRing K] [Algebra ℚ K] : elemSymm K 0 = 1 := by
  rw [elemSymm]

/-- Newton's identity in the form defining the elementary symmetric functions. -/
lemma elemSymm_succ (K : Type*) [CommRing K] [Algebra ℚ K] (n : ℕ) :
    elemSymm K (n + 1) = C (algebraMap ℚ K ((n + 1 : ℚ)⁻¹)) *
      ∑ k ∈ range (n + 1), (-1) ^ k * powerSum K (k + 1) * elemSymm K (n - k) := by
  rw [elemSymm]

/-- The elementary symmetric function `e_n` is weighted homogeneous of degree `n`, the generator
`p_k` weighing `k`. -/
theorem isWeightedHomogeneous_elemSymm (K : Type*) [CommRing K] [Algebra ℚ K] (n : ℕ) :
    IsWeightedHomogeneous degWeight (elemSymm K n) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      rw [elemSymm_zero]
      exact isWeightedHomogeneous_one K degWeight
    | m + 1 =>
      rw [elemSymm_succ]
      refine IsWeightedHomogeneous.C_mul (IsWeightedHomogeneous.sum _ _ _ fun k hk => ?_) _
      simp only [Finset.mem_range] at hk
      have hX : powerSum K (k + 1) = (X k : Lambda K) := by
        rw [powerSum, Nat.add_sub_cancel]
      have hmul := (isWeightedHomogeneous_X (R := K) degWeight k).mul (ih (m - k) (by omega))
      rw [degWeight_apply, show k + 1 + (m - k) = m + 1 from by omega] at hmul
      have hsign : ((-1 : Lambda K)) ^ k * powerSum K (k + 1) * elemSymm K (m - k) =
          C ((-1 : K) ^ k) * ((X k : Lambda K) * elemSymm K (m - k)) := by
        rw [hX, map_pow, map_neg, map_one, mul_assoc]
      rw [hsign]
      exact IsWeightedHomogeneous.C_mul hmul _

/-! ### The evaluation map on a homogeneous element -/

/-- Scaling the alphabet by `c` multiplies a weighted homogeneous element of degree `n` by
`c ^ n`. -/
theorem plethScale_of_isWeightedHomogeneous {K : Type*} [CommRing K] {f : Lambda K} {n : ℕ}
    (hf : IsWeightedHomogeneous degWeight f n) (c : K) :
    plethScale c f = C (c ^ n) * f := by
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_plethScale, coeff_C_mul]
  by_cases h : coeff d f = 0
  · rw [h, mul_zero, mul_zero]
  · have hw : Finsupp.weight (fun i => i + 1) d = n := hf h
    rw [← PhiHom.weight_eq_sum_support d, hw]

/-- Sign extraction sends the generator of index `i` to `(-1) ^ i`. -/
lemma signExtract_X (K : Type*) [CommRing K] (i : ℕ) :
    signExtract K (X i : Lambda K) = (-1 : K) ^ i :=
  MvPolynomial.aeval_X _ i

/-- Sign extraction commutes with a specialisation of the coefficients. -/
theorem signExtract_map {K G : Type*} [CommRing K] [CommRing G] (spec : K →+* G) (x : Lambda K) :
    signExtract G (MvPolynomial.map spec x) = spec (signExtract K x) := by
  induction x using MvPolynomial.induction_on with
  | C r => rw [MvPolynomial.map_C, PhiHom.signExtract_C, PhiHom.signExtract_C]
  | add p r hp hr => simp only [map_add, hp, hr]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X, signExtract_X, hp, map_pow, map_neg, map_one]

section Homogeneous

variable {L : Type*} [Field L] {F : Type*} [CommRing F]

/-- On a weighted homogeneous element of degree `n` the evaluation map is the specialisation of a
single scalar, the sign extraction of the attached operator applied to `1`, corrected by the sign
`(-1) ^ (n (b + 1))`. -/
theorem phi_of_isWeightedHomogeneous (b : ℕ) (spec : L →+* F)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) {f : Lambda L} {n : ℕ}
    (hf : IsWeightedHomogeneous degWeight f n) :
    Phi b spec Θ f = (-1) ^ (n * (b + 1)) * spec (signExtract L (Θ f 1)) := by
  have hsign : spec (((-1 : L) ^ (b + 1)) ^ n) = (-1 : F) ^ (n * (b + 1)) := by
    rw [← pow_mul, mul_comm (b + 1) n, map_pow, map_neg, map_one]
  rw [PhiHom.phi_eq_evalOne_plethScale b spec Θ, plethScale_of_isWeightedHomogeneous hf,
    PhiHom.evalOne_C_mul, hsign]
  simp only [PhiHom.evalOne, signExtract_map]

end Homogeneous

/-! ### The all-path evaluation -/

section Main

variable {a b N : ℕ} {L : Type*} [Field L] [Algebra ℚ L] {F : Type*} [CommRing F]

/-- For a slope homomorphism at `(a, b)` and every `N ≥ 1`, the evaluation map whose
specialisation sends the second parameter to `1` takes the elementary symmetric function `e_N` to
the area generating polynomial of the below-diagonal `(aN, bN)`-paths, evaluated at the
specialisation of the first parameter.

The hypotheses are inconsistent, so the statement holds vacuously: `L` is a field, so `spec u = 1`
forces `u = 1` by `Multiplication.eq_one_of_map_eq_one`, and then every slope operator of first
index at least two vanishes, giving `Θ (elemSymm L N) = 0`, which contradicts the assumed shuffle
identity's nonzero path sum. -/
theorem phi_elemSymm {q u : L} (spec : L →+* F) (hspec : spec u = 1)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (hΘ : IsSlopeHom a b q u Θ)
    (shuffle : External.Shuffle L) (epsilonGessel : External.EpsilonGessel L)
    (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b)
    (hqu : AlgebraicIndependent ℤ ![q, u])
    (ι : Lambda L →ₐ[L] AlphabetSeries L) (hι : IsRealisation ι) (hN : 0 < N)
    (hexp : IsCreationExpansion N q) (hexpSwap : IsCreationExpansion N u) :
    Phi b spec Θ (elemSymm L N) =
      ∑ y ∈ (univ : Finset (Heights a b N)) with IsBelowDiagonal y, spec q ^ area y := by
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hgs : GesselSelection L := epsilonGessel
  obtain ⟨hval, hswap⟩ := signExtract_elemSymm_isPoly_and_swap (shuffle a b hab ha hb q u hqu)
    (shuffle a b hab ha hb u q (algebraicIndependent_swap hqu)) hgs ι hι Θ hΘ ha0 hb0 hN hexp
    hexpSwap
  rw [phi_of_isWeightedHomogeneous b spec Θ (isWeightedHomogeneous_elemSymm L N), hval, hswap,
    aeval_signedPathPoly, aeval_pathPoly]
  simp only [map_mul, map_pow, map_neg, map_one, map_sum, hspec, one_pow, one_mul]
  rw [← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]

/-- The same evaluation read off the area polynomial itself: for any specialisation of the
integral power series in which the variable becomes the first parameter, the evaluation map sends
`e_N` to the image of the area polynomial of the below-diagonal `(aN, bN)`-paths.

The hypotheses are those of `phi_elemSymm`, so they are inconsistent and this statement too holds
vacuously: over a field `spec u = 1` forces `u = 1`, and there `Θ (elemSymm L N) = 0` contradicts
the assumed shuffle identity's nonzero path sum. -/
theorem phi_elemSymm_eq_areaPoly {q u : L} (spec : L →+* F) (hspec : spec u = 1)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (hΘ : IsSlopeHom a b q u Θ)
    (shuffle : External.Shuffle L) (epsilonGessel : External.EpsilonGessel L)
    (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b)
    (hqu : AlgebraicIndependent ℤ ![q, u])
    (ι : Lambda L →ₐ[L] AlphabetSeries L) (hι : IsRealisation ι) (hN : 0 < N)
    (hexp : IsCreationExpansion N q) (hexpSwap : IsCreationExpansion N u)
    (g : PowerSeries ℤ →+* F) (hg : g PowerSeries.X = spec q) :
    Phi b spec Θ (elemSymm L N) = g (Paths.areaPoly a b N) := by
  rw [phi_elemSymm spec hspec Θ hΘ shuffle epsilonGessel hab ha hb hqu ι hι hN hexp hexpSwap,
    Paths.areaPoly, map_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [map_pow, hg]

end Main

end HJO.PhiE
