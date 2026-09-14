/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import HJO.Symmetric.CopPower
public meta import HJO.Attr

/-! # Logarithmic derivatives and the letter-by-letter recursions of `e` and `h`

Over a `ℚ`-algebra a formal power series is pinned down by its constant term together with its
logarithmic derivative, and Newton's identities say exactly what the logarithmic derivative of the
generating series of the elementary or the complete homogeneous symmetric functions is. This file
assembles the four power-series facts that make the technique work, reads off the two logarithmic
derivatives, and derives the three consequences the creation-operator computation needs: the
Cauchy relation `∑_m (-1)ᵐ e_{N-m} h_m = 0`, the expansion of `eₙ` after one letter is *removed*
from the alphabet, and its one-term shadow after one letter is *added*.

Three of the four power-series facts, and the logarithmic derivative of the series of complete
homogeneous symmetric functions, are already proved in `HJO.Symmetric.CopPower`, which needed
them for the iterated first creation operator. They are restated here in the shape the creation
seeds are computed in rather than reproved: each statement whose proof is a single reference to
that file says so in its docstring.

An alphabet is only ever manipulated through a ring homomorphism out of `Lambda K`, so "adding the
letter `a`" means "a second homomorphism exceeding the first by `aᵏ` on every power sum `p_k`".
That phrasing is what lets the same lemma serve both over the coefficient field and over
`Polynomial (Lambda L)`, where the added letter is `1/(qz)`.
-/

@[expose] public section

open Finset

namespace HJO.CreationSeeds

/-! ### Power series pinned down by a logarithmic derivative -/

section PowerSeriesFacts

variable {R : Type*} [CommRing R]

/-- **The geometric series has logarithmic derivative `∑ₖ a^{k+1} zᵏ`.** This is
`HJO.CopPower.derivative_geometric`. -/
@[hjo "lem_geom_logderiv"]
theorem derivative_geometric (a : R) :
    PowerSeries.derivative R (PowerSeries.mk fun k => a ^ k)
      = (PowerSeries.mk fun k => a ^ (k + 1)) * PowerSeries.mk fun k => a ^ k :=
  CopPower.derivative_geometric a

/-- **Logarithmic derivatives add under multiplication.** This is
`HJO.CopPower.derivative_mul_of_logDeriv`. -/
@[hjo "lem_logderiv_mul"]
theorem derivative_mul_of_logDeriv {P Q F G : PowerSeries R}
    (hF : PowerSeries.derivative R F = P * F) (hG : PowerSeries.derivative R G = Q * G) :
    PowerSeries.derivative R (F * G) = (P + Q) * (F * G) :=
  CopPower.derivative_mul_of_logDeriv hF hG

/-- **Rescaling the variable multiplies the derivative by the scaling factor**, in the
coefficientwise form in which it gets applied: if `G` is `F` with the coefficient of `zⁿ` scaled
by `cⁿ`, and `H` is `F'` scaled the same way, then `G' = cH`. -/
@[hjo "lem_rescale_derivative"]
theorem derivative_eq_of_coeff_scaled (c : R) (F G H : PowerSeries R)
    (hG : ∀ n, PowerSeries.coeff n G = c ^ n * PowerSeries.coeff n F)
    (hH : ∀ n, PowerSeries.coeff n H
      = c ^ n * PowerSeries.coeff n (PowerSeries.derivative R F)) :
    PowerSeries.derivative R G = PowerSeries.C c * H := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_derivative, hG, PowerSeries.coeff_C_mul, hH,
    PowerSeries.coeff_derivative]
  ring

/-- **A power series over a `ℚ`-algebra is determined by its constant term together with its
logarithmic derivative.** This is `HJO.CopPower.powerSeries_ext_of_logDeriv`. -/
@[hjo "lem_logderiv_unique"]
theorem powerSeries_ext_of_logDeriv [Algebra ℚ R] {Q F G : PowerSeries R}
    (hF : PowerSeries.derivative R F = Q * F) (hG : PowerSeries.derivative R G = Q * G)
    (h0 : PowerSeries.coeff 0 F = PowerSeries.coeff 0 G) : F = G :=
  CopPower.powerSeries_ext_of_logDeriv hF hG h0

end PowerSeriesFacts

/-! ### The two logarithmic derivatives -/

section Newton

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- The zeroth elementary symmetric function is one. The same one-line unfolding as
`HJO.PhiE.elemSymm_zero`, repeated here so that this file need not import the evaluation-map
tree. -/
theorem elemSymm_zero : Sym.elemSymm K 0 = 1 := by
  rw [Sym.elemSymm]

/-- Newton's identity for the elementary symmetric functions, cleared of its denominator:
`(n+1) e_{n+1} = ∑_{j=0}ⁿ (-1)ʲ p_{j+1} e_{n-j}`, an identity between honest elements of
`Lambda K`. -/
theorem natCast_mul_elemSymm (n : ℕ) :
    ((n : Sym.Lambda K) + 1) * Sym.elemSymm K (n + 1)
      = ∑ k ∈ range (n + 1), (-1) ^ k * Sym.powerSum K (k + 1) * Sym.elemSymm K (n - k) := by
  rw [Sym.elemSymm]
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have e : ((n : Sym.Lambda K) + 1) = MvPolynomial.C ((n : K) + 1) := by
    rw [map_add, MvPolynomial.C_1, map_natCast]
  have key : ((n : K) + 1) * algebraMap ℚ K ((n : ℚ) + 1)⁻¹ = 1 := by
    rw [show ((n : K) + 1) = algebraMap ℚ K ((n : ℚ) + 1) by
      rw [map_add, map_natCast, map_one], ← map_mul, mul_inv_cancel₀ hn, map_one]
  rw [e, ← mul_assoc, ← MvPolynomial.C_mul, key, MvPolynomial.C_1, one_mul]

/-- **The logarithmic derivative of the series of elementary symmetric functions.** For a ring
homomorphism `φ : Λ → R`, the series `∑ₙ φ(eₙ)zⁿ` has logarithmic derivative
`∑ₖ (-1)ᵏ φ(p_{k+1})zᵏ`. -/
@[hjo "lem_esymm_logderiv"]
theorem derivative_mk_elemSymm {R : Type*} [CommRing R] {F : Type*}
    [FunLike F (Sym.Lambda K) R] [RingHomClass F (Sym.Lambda K) R] (f : F) :
    PowerSeries.derivative R (PowerSeries.mk fun n => f (Sym.elemSymm K n))
      = (PowerSeries.mk fun k => (-1) ^ k * f (Sym.powerSum K (k + 1)))
        * PowerSeries.mk fun n => f (Sym.elemSymm K n) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]
  have h := congrArg f (natCast_mul_elemSymm (K := K) n)
  rw [map_mul, map_sum] at h
  simp only [map_add, map_natCast, map_one, map_mul, map_pow, map_neg] at h
  rw [← h]
  ring

/-- **The logarithmic derivative of the series of complete homogeneous symmetric functions.** For
a ring homomorphism `φ : Λ → R`, the series `∑ₙ φ(hₙ)zⁿ` has logarithmic derivative
`∑ₖ φ(p_{k+1})zᵏ`. This is `HJO.CopPower.derivative_mk_completeHomog`. -/
@[hjo "lem_hsymm_logderiv"]
theorem derivative_mk_completeHomog {R : Type*} [CommRing R] {F : Type*}
    [FunLike F (Sym.Lambda K) R] [RingHomClass F (Sym.Lambda K) R] (f : F) :
    PowerSeries.derivative R (PowerSeries.mk fun n => f (Sym.completeHomog K n))
      = (PowerSeries.mk fun k => f (Sym.powerSum K (k + 1)))
        * PowerSeries.mk fun n => f (Sym.completeHomog K n) :=
  CopPower.derivative_mk_completeHomog f

end Newton

/-! ### The Cauchy relation between `e` and `h` -/

section Cauchy

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- The generating series of the elementary symmetric functions is inverse to the
*sign-alternating* generating series of the complete homogeneous symmetric functions: both have
logarithmic derivative summing to zero, and both have constant term one. -/
theorem mk_elemSymm_mul_mk_alternating_completeHomog :
    ((PowerSeries.mk fun n => Sym.elemSymm K n)
        * PowerSeries.mk fun n => (-1) ^ n * Sym.completeHomog K n) = 1 := by
  have hEd : PowerSeries.derivative (Sym.Lambda K) (PowerSeries.mk fun n => Sym.elemSymm K n)
      = (PowerSeries.mk fun k => (-1) ^ k * Sym.powerSum K (k + 1))
        * PowerSeries.mk fun n => Sym.elemSymm K n := by
    simpa using derivative_mk_elemSymm (RingHom.id (Sym.Lambda K))
  have hHd : PowerSeries.derivative (Sym.Lambda K)
        (PowerSeries.mk fun n => Sym.completeHomog K n)
      = (PowerSeries.mk fun k => Sym.powerSum K (k + 1))
        * PowerSeries.mk fun n => Sym.completeHomog K n :=
    CopPower.derivative_mk_completeHomog_self
  have hcoeff : ∀ n, PowerSeries.coeff n
        ((PowerSeries.mk fun k => (-1) ^ k * Sym.powerSum K (k + 1))
          * PowerSeries.mk fun n => (-1) ^ n * Sym.completeHomog K n)
      = (-1 : Sym.Lambda K) ^ n * PowerSeries.coeff n
          (PowerSeries.derivative (Sym.Lambda K)
            (PowerSeries.mk fun n => Sym.completeHomog K n)) := by
    intro n
    rw [hHd, PowerSeries.coeff_mul, PowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    simp only [PowerSeries.coeff_mk]
    rw [← hij, pow_add]
    ring
  have hGd : PowerSeries.derivative (Sym.Lambda K)
        (PowerSeries.mk fun n => (-1) ^ n * Sym.completeHomog K n)
      = (-(PowerSeries.mk fun k => (-1) ^ k * Sym.powerSum K (k + 1)))
        * PowerSeries.mk fun n => (-1) ^ n * Sym.completeHomog K n := by
    rw [derivative_eq_of_coeff_scaled (-1 : Sym.Lambda K)
        (PowerSeries.mk fun n => Sym.completeHomog K n)
        (PowerSeries.mk fun n => (-1) ^ n * Sym.completeHomog K n)
        ((PowerSeries.mk fun k => (-1) ^ k * Sym.powerSum K (k + 1))
          * PowerSeries.mk fun n => (-1) ^ n * Sym.completeHomog K n)
        (fun n => by simp) hcoeff,
      show (PowerSeries.C (-1 : Sym.Lambda K)) = -1 by rw [map_neg, map_one]]
    ring
  refine powerSeries_ext_of_logDeriv (Q := 0) ?_ ?_ ?_
  · rw [derivative_mul_of_logDeriv hEd hGd]
    simp
  · simp
  · simp [PowerSeries.coeff_mul, elemSymm_zero, CopPower.completeHomog_zero]

/-- **The Cauchy relation.** For every `N ≥ 1`, `∑_{m=0}^{N} (-1)ᵐ e_{N-m} h_m = 0`. -/
@[hjo "lem_esymm_cauchy"]
theorem sum_alternating_elemSymm_mul_completeHomog {N : ℕ} (hN : 0 < N) :
    ∑ m ∈ range (N + 1), (-1) ^ m * Sym.elemSymm K (N - m) * Sym.completeHomog K m = 0 := by
  have h : PowerSeries.coeff N
      ((PowerSeries.mk fun n => (-1) ^ n * Sym.completeHomog K n)
        * PowerSeries.mk fun n => Sym.elemSymm K n) = 0 := by
    rw [mul_comm, mk_elemSymm_mul_mk_alternating_completeHomog]
    simp [hN.ne']
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [PowerSeries.coeff_mk] at h
  exact Eq.trans (Finset.sum_congr rfl fun m _ => by ring) h

end Cauchy

/-! ### Adding and removing a single letter -/

section Letters

variable {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R] [Algebra ℚ R]
  {F G : Type*} [FunLike F (Sym.Lambda K) R] [RingHomClass F (Sym.Lambda K) R]
  [FunLike G (Sym.Lambda K) R] [RingHomClass G (Sym.Lambda K) R]

/-- **Removing one letter `b` from the alphabet.** If `ψ` falls short of `φ` by `bᵏ` on every
power sum `p_k`, then `ψ(eₙ) = ∑_{j=0}ⁿ (-b)ʲ φ(e_{n-j})`. -/
@[hjo "lem_esymm_sub_letter"]
theorem elemSymm_sub_letter (f : F) (g : G) (b : R)
    (h : ∀ k : ℕ, 0 < k → g (Sym.powerSum K k) = f (Sym.powerSum K k) - b ^ k) (n : ℕ) :
    g (Sym.elemSymm K n) = ∑ j ∈ range (n + 1), (-b) ^ j * f (Sym.elemSymm K (n - j)) := by
  have hQ : (PowerSeries.mk fun k => (-b) ^ (k + 1))
      + (PowerSeries.mk fun k => (-1) ^ k * f (Sym.powerSum K (k + 1)))
      = PowerSeries.mk fun k => (-1) ^ k * g (Sym.powerSum K (k + 1)) := by
    refine PowerSeries.ext fun k => ?_
    simp only [map_add, PowerSeries.coeff_mk]
    rw [h (k + 1) k.succ_pos, neg_pow]
    ring
  have hlog : PowerSeries.derivative R
        ((PowerSeries.mk fun j => (-b) ^ j) * PowerSeries.mk fun n => f (Sym.elemSymm K n))
      = (PowerSeries.mk fun k => (-1) ^ k * g (Sym.powerSum K (k + 1)))
        * ((PowerSeries.mk fun j => (-b) ^ j)
          * PowerSeries.mk fun n => f (Sym.elemSymm K n)) := by
    rw [← hQ]
    exact derivative_mul_of_logDeriv (derivative_geometric (-b)) (derivative_mk_elemSymm f)
  have key : (PowerSeries.mk fun n => g (Sym.elemSymm K n))
      = (PowerSeries.mk fun j => (-b) ^ j)
        * PowerSeries.mk fun n => f (Sym.elemSymm K n) :=
    powerSeries_ext_of_logDeriv (derivative_mk_elemSymm g) hlog
      (by simp [PowerSeries.coeff_mul, elemSymm_zero])
  have hc := congrArg (PowerSeries.coeff n) key
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simp only [PowerSeries.coeff_mk] at hc
  exact hc

/-- **Adding one letter `a` to the alphabet.** If `ψ` exceeds `φ` by `aᵏ` on every power sum
`p_k`, then for `n ≥ 1` the elementary symmetric function picks up exactly one new term:
`ψ(eₙ) = φ(eₙ) + a φ(e_{n-1})`. -/
@[hjo "lem_esymm_add_letter"]
theorem elemSymm_add_letter (f : F) (g : G) (a : R)
    (h : ∀ k : ℕ, 0 < k → g (Sym.powerSum K k) = f (Sym.powerSum K k) + a ^ k) {n : ℕ}
    (hn : 0 < n) :
    g (Sym.elemSymm K n) = f (Sym.elemSymm K n) + a * f (Sym.elemSymm K (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsub : ∀ p : ℕ, f (Sym.elemSymm K p)
      = ∑ j ∈ range (p + 1), (-a) ^ j * g (Sym.elemSymm K (p - j)) :=
    elemSymm_sub_letter g f a fun k hk => by rw [h k hk]; ring
  have e1 : f (Sym.elemSymm K (m + 1))
      = (∑ j ∈ range (m + 1), (-a) ^ (j + 1) * g (Sym.elemSymm K (m - j)))
        + g (Sym.elemSymm K (m + 1)) := by
    rw [hsub (m + 1), Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.sub_zero]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show m + 1 - (j + 1) = m - j by omega]
  have e2 : a * f (Sym.elemSymm K m)
      = ∑ j ∈ range (m + 1), a * ((-a) ^ j * g (Sym.elemSymm K (m - j))) := by
    rw [hsub m, Finset.mul_sum]
  have hzero : ∀ j ∈ range (m + 1),
      (-a) ^ (j + 1) * g (Sym.elemSymm K (m - j))
        + a * ((-a) ^ j * g (Sym.elemSymm K (m - j))) = 0 := by
    intro j _
    rw [pow_succ]
    ring
  rw [Nat.add_sub_cancel, e1, e2, add_right_comm, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl hzero, Finset.sum_const_zero, zero_add]

end Letters

end HJO.CreationSeeds
