/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import HJO.Symmetric.CopPower
public import HJO.Evaluation.PhiE
public import HJO.Determinant.Basic

/-! # The area generating series as an exponential

Newton's identity defining the elementary symmetric functions says that the generating series
`∑ₙ eₙ zⁿ` has logarithmic derivative `∑ₖ (-1)ᵏ p_{k+1} zᵏ`, and a ring homomorphism out of the
ring of symmetric functions carries that statement to the generating series of the images. Over a
`ℚ`-algebra a power series is pinned down by its constant term together with its logarithmic
derivative, so the generating series of the images of the elementary symmetric functions is the
formal exponential of the series `∑_{k ≥ 1} (-1)^{k-1} rₖ zᵏ / k` whose derivative is that
logarithmic derivative, `rₖ` being the image of the power sum `p_k`.

The formal exponential used here is the honest one: the exponential power series with the given
series, of zero constant term, substituted for its variable. The two ingredients that make the
identification a two-line argument are Mathlib's chain rule for that substitution and the fact
that the exponential power series is its own derivative.

The area generating series is the generating series of those images: its coefficient of `zᴺ` is
the area polynomial of the below-diagonal `(aN, bN)`-paths, which is what the evaluation map
does to `e_N`. The external inputs feeding that identification are threaded as hypotheses.
-/

@[expose] public section

open Finset

namespace HJO.AExponential

open MvPolynomial HJO.Sym HJO.CopPower HJO.ThetaSymmetry

/-! ### Newton's identity for the elementary symmetric functions -/

section Newton

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- Newton's identity for the elementary symmetric functions, cleared of its denominator. -/
lemma natCast_mul_elemSymm (n : ℕ) :
    ((n : Lambda K) + 1) * elemSymm K (n + 1)
      = ∑ k ∈ range (n + 1), (-1) ^ k * powerSum K (k + 1) * elemSymm K (n - k) := by
  rw [PhiE.elemSymm_succ]
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have e : ((n : Lambda K) + 1) = MvPolynomial.C ((n : K) + 1) := by
    rw [map_add, MvPolynomial.C_1, map_natCast]
  have key : ((n : K) + 1) * algebraMap ℚ K ((n : ℚ) + 1)⁻¹ = 1 := by
    rw [show ((n : K) + 1) = algebraMap ℚ K ((n : ℚ) + 1) by
      rw [map_add, map_natCast, map_one], ← map_mul, mul_inv_cancel₀ hn, map_one]
  rw [e, ← mul_assoc, ← MvPolynomial.C_mul, key, MvPolynomial.C_1, one_mul]

/-- The generating series of the images of the elementary symmetric functions under a ring
homomorphism has logarithmic derivative the alternating generating series of the images of the
power sums. -/
lemma derivative_mk_elemSymm {R : Type*} [CommRing R] {G : Type*}
    [FunLike G (Lambda K) R] [RingHomClass G (Lambda K) R] (f : G) :
    PowerSeries.derivative R (PowerSeries.mk fun n => f (elemSymm K n))
      = (PowerSeries.mk fun k => (-1) ^ k * f (powerSum K (k + 1)))
        * PowerSeries.mk fun n => f (elemSymm K n) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]
  have h := congrArg f (natCast_mul_elemSymm (K := K) n)
  rw [map_mul, map_sum] at h
  simp only [map_add, map_natCast, map_one, map_mul, map_pow, map_neg] at h
  rw [← h]
  ring

end Newton

/-! ### The formal exponential of a power series with zero constant term -/

section FormalExp

variable {F : Type*} [CommRing F] [Algebra ℚ F]

/-- The formal exponential of a power series `A`: the exponential power series with `A`
substituted for its variable. It is the honest `exp A` exactly when `A` has zero constant
term, which every use below supplies. -/
noncomputable def formalExp (A : PowerSeries F) : PowerSeries F :=
  (PowerSeries.exp F).subst A

/-- The formal exponential of a power series with zero constant term has constant term `1`. -/
lemma coeff_zero_formalExp {A : PowerSeries F} (hA : PowerSeries.constantCoeff A = 0) :
    PowerSeries.coeff 0 (formalExp A) = 1 := by
  have hs : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero' hA
  rw [formalExp, PowerSeries.coeff_subst' hs, finsum_eq_single _ 0]
  · simp
  · intro d hd
    have hz : PowerSeries.coeff 0 (A ^ d) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hA, zero_pow hd]
    rw [hz, smul_zero]

/-- The formal exponential of a power series with zero constant term has that series'
derivative as its logarithmic derivative. -/
lemma derivative_formalExp {A : PowerSeries F} (hA : PowerSeries.constantCoeff A = 0) :
    PowerSeries.derivative F (formalExp A)
      = PowerSeries.derivative F A * formalExp A := by
  rw [formalExp, PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hA),
    PowerSeries.derivative_exp]
  ring

/-- A power series with constant term `1` whose logarithmic derivative is the derivative of a
power series with zero constant term is the formal exponential of the latter. -/
theorem eq_formalExp_of_logDeriv {A G : PowerSeries F} (hA : PowerSeries.constantCoeff A = 0)
    (hd : PowerSeries.derivative F G = PowerSeries.derivative F A * G)
    (h0 : PowerSeries.coeff 0 G = 1) : G = formalExp A :=
  powerSeries_ext_of_logDeriv hd (derivative_formalExp hA)
    (by rw [h0, coeff_zero_formalExp hA])

/-- The series `∑_{k ≥ 1} (-1)^{k-1} rₖ zᵏ / k`, the logarithm to be exponentiated. The
coefficient of `z⁰` vanishes because `(0 : ℚ)⁻¹` does. -/
noncomputable def logSeries (r : ℕ → F) : PowerSeries F :=
  PowerSeries.mk fun k => algebraMap ℚ F ((k : ℚ)⁻¹) * ((-1) ^ (k - 1) * r k)

/-- The logarithm series has zero constant term. -/
@[simp] lemma constantCoeff_logSeries (r : ℕ → F) :
    PowerSeries.constantCoeff (logSeries r) = 0 := by
  rw [logSeries, PowerSeries.constantCoeff_mk]
  simp

/-- The derivative of the logarithm series is the alternating generating series of the `rₖ`. -/
lemma derivative_logSeries (r : ℕ → F) :
    PowerSeries.derivative F (logSeries r)
      = PowerSeries.mk fun k => (-1) ^ k * r (k + 1) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_derivative, logSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    Nat.add_sub_cancel]
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hcast : (((n + 1 : ℕ) : ℚ))⁻¹ = ((n : ℚ) + 1)⁻¹ := by push_cast; ring
  have hkey : algebraMap ℚ F ((n : ℚ) + 1)⁻¹ * ((n : F) + 1) = 1 := by
    rw [show ((n : F) + 1) = algebraMap ℚ F ((n : ℚ) + 1) by
      rw [map_add, map_natCast, map_one], ← map_mul, inv_mul_cancel₀ hn, map_one]
  rw [hcast]
  linear_combination ((-1 : F) ^ n * r (n + 1)) * hkey

/-- A power series with constant term `1` whose logarithmic derivative is the alternating
generating series of the `rₖ` is the formal exponential of `∑_{k ≥ 1} (-1)^{k-1} rₖ zᵏ / k`. -/
theorem eq_formalExp_logSeries {r : ℕ → F} {G : PowerSeries F}
    (hd : PowerSeries.derivative F G
      = (PowerSeries.mk fun k => (-1) ^ k * r (k + 1)) * G)
    (h0 : PowerSeries.coeff 0 G = 1) : G = formalExp (logSeries r) :=
  eq_formalExp_of_logDeriv (constantCoeff_logSeries r)
    (by rw [derivative_logSeries]; exact hd) h0

end FormalExp

/-! ### The generating series of the evaluated elementary symmetric functions -/

section Phi

variable {a b : ℕ} {L : Type*} [Field L] [Algebra ℚ L] {F : Type*} [CommRing F] [Algebra ℚ F]

/-- For a slope homomorphism at `(a, b)` specialised at `u = 1`, the generating series of the
images of the elementary symmetric functions under the evaluation map is the formal exponential
of `∑_{k ≥ 1} (-1)^{k-1} rₖ zᵏ / k`, where `rₖ` is the evaluation coefficient of `p_k`. -/
theorem mk_phi_elemSymm_eq_formalExp {q u : L} (spec : L →+* F)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (hspec : spec u = 1) (hv0 : q * u ≠ 0)
    (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1) (hΘ : IsSlopeHom a b q u Θ) :
    (PowerSeries.mk fun n => Phi b spec Θ (elemSymm L n))
      = formalExp (logSeries (phiCoeff b spec Θ)) := by
  refine eq_formalExp_logSeries ?_ ?_
  · have h := derivative_mk_elemSymm (K := L) (R := F)
      (PhiHom.phiRingHom b spec Θ hspec hv0 hv1 hΘ)
    simpa only [PhiHom.phiRingHom_apply, phiCoeff] using h
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_mk,
      PhiE.elemSymm_zero, PhiHom.phi_one]

end Phi

/-! ### The area generating series -/

section Main

variable {a b : ℕ} {L : Type*} [Field L] [Algebra ℚ L]

/-- The area polynomial at rank zero is `1`: the only path of rank zero is the empty one, and its
area is zero. -/
lemma areaPoly_zero (a b : ℕ) : Paths.areaPoly a b 0 = 1 := by
  have hone : ∀ y : Paths.Heights a b 0, ∀ r : Fin (a * 0 + 1), (y r : ℕ) = 0 := by
    intro y r
    have := (y r).isLt
    omega
  have hcard : Fintype.card (Paths.Heights a b 0) = 1 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    simp
  have hht : ∀ (y : Paths.Heights a b 0) (r : ℕ), Paths.ht y r = 0 := by
    intro y r
    rw [Paths.ht]
    split
    · exact hone y _
    · omega
  have hbd : ∀ y : Paths.Heights a b 0, Paths.IsBelowDiagonal y := by
    intro y
    refine ⟨hht y 0, by rw [hht y (a * 0), Nat.mul_zero], fun r hr => by omega, fun r _ => ?_⟩
    rw [hht y r, Nat.mul_zero]
    exact Nat.zero_le _
  have harea : ∀ y : Paths.Heights a b 0, Paths.area y = 0 := by
    intro y
    rw [Paths.area, Nat.mul_zero, Finset.Ico_eq_empty (by omega), Finset.sum_empty]
  rw [Paths.areaPoly, Finset.filter_true_of_mem fun y _ => hbd y,
    Finset.sum_congr rfl fun y _ => by rw [harea y, pow_zero], Finset.sum_const,
    Finset.card_univ, hcard, one_smul]

/-- For a slope homomorphism at `(a, b)` whose specialisation sends the first parameter to the
variable `q` of `ℚ((q))` and the second to `1`, the area generating series is the generating
series of the images of the elementary symmetric functions under the evaluation map. -/
theorem genA_eq_mk_phi_elemSymm {q u : L} (spec : L →+* LaurentSeries ℚ)
    (hspecq : spec q = Determinant.qVar) (hspecu : spec u = 1)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (hΘ : IsSlopeHom a b q u Θ)
    (shuffle : External.Shuffle L) (epsilonGessel : External.EpsilonGessel L)
    (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b)
    (hqu : AlgebraicIndependent ℤ ![q, u])
    (ι : Lambda L →ₐ[L] AlphabetSeries L) (hι : IsRealisation ι)
    (hexp : ∀ n : ℕ, IsCreationExpansion n q) (hexpSwap : ∀ n : ℕ, IsCreationExpansion n u) :
    Determinant.genA a b = PowerSeries.mk fun n => Phi b spec Θ (elemSymm L n) := by
  refine PowerSeries.ext fun n => ?_
  rw [Determinant.genA, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  match n with
  | 0 =>
    rw [areaPoly_zero, map_one, PhiE.elemSymm_zero, PhiHom.phi_one]
  | m + 1 =>
    rw [PhiE.phi_elemSymm_eq_areaPoly spec hspecu Θ hΘ shuffle epsilonGessel hab ha hb hqu ι hι
      (Nat.succ_pos m) (hexp (m + 1)) (hexpSwap (m + 1)) Determinant.qOfInt
      (by rw [hspecq, Determinant.qVar])]

/-- `𝒜(z;q) = exp(∑_{k ≥ 1} (-1)^{k-1} rₖ zᵏ / k)`: for a slope homomorphism at `(a, b)` whose
specialisation sends the first parameter to the variable `q` and the second to `1`, the area
generating series is the formal exponential of the series built from the evaluation
coefficients.

Since `L` is a field, `spec u = 1` forces `u = 1`; the slope operators then collapse and the
assumed shuffle identity is contradicted, so the hypotheses cannot all hold at once. -/
theorem genA_eq_formalExp {q u : L} (spec : L →+* LaurentSeries ℚ)
    (hspecq : spec q = Determinant.qVar) (hspecu : spec u = 1) (hv0 : q * u ≠ 0)
    (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (hΘ : IsSlopeHom a b q u Θ)
    (shuffle : External.Shuffle L) (epsilonGessel : External.EpsilonGessel L)
    (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b)
    (hqu : AlgebraicIndependent ℤ ![q, u])
    (ι : Lambda L →ₐ[L] AlphabetSeries L) (hι : IsRealisation ι)
    (hexp : ∀ n : ℕ, IsCreationExpansion n q) (hexpSwap : ∀ n : ℕ, IsCreationExpansion n u) :
    Determinant.genA a b = formalExp (logSeries (phiCoeff b spec Θ)) := by
  rw [genA_eq_mk_phi_elemSymm spec hspecq hspecu Θ hΘ shuffle epsilonGessel hab ha hb hqu ι hι hexp
    hexpSwap, mk_phi_elemSymm_eq_formalExp spec Θ hspecu hv0 hv1 hΘ]

end Main

end HJO.AExponential
