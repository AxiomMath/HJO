/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.LinearCombination
public import QSeriesLib.NumberTheory.QTheory.Defs
public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The iterated first creation operator applied to one

The first creation operator, applied `N` times to `1`, produces a single complete homogeneous
symmetric function in the divided alphabet `X / (1 - q)`, up to an explicit scalar. The proof
runs through generating series: a power series over a `ℚ`-algebra is pinned down by its
constant term together with its logarithmic derivative, and Newton's identity says exactly
what the logarithmic derivative of the series of complete homogeneous symmetric functions is.
-/

@[expose] public section

open Finset

namespace HJO.CopPower

/-! ### Power series pinned down by a logarithmic derivative -/

section PowerSeriesAux

variable {R : Type*} [CommRing R]

/-- In a `ℚ`-algebra every positive integer is cancellable. -/
lemma mul_natSucc_cancel [Algebra ℚ R] (n : ℕ) {x y : R}
    (h : x * ((n : R) + 1) = y * ((n : R) + 1)) : x = y := by
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have h1 : ((n : R) + 1) * algebraMap ℚ R ((n : ℚ) + 1)⁻¹ = 1 := by
    have e : ((n : R) + 1) = algebraMap ℚ R ((n : ℚ) + 1) := by
      rw [map_add, map_natCast, map_one]
    rw [e, ← map_mul, mul_inv_cancel₀ hn, map_one]
  calc x = x * (((n : R) + 1) * algebraMap ℚ R ((n : ℚ) + 1)⁻¹) := by rw [h1, mul_one]
    _ = x * ((n : R) + 1) * algebraMap ℚ R ((n : ℚ) + 1)⁻¹ := by ring
    _ = y * ((n : R) + 1) * algebraMap ℚ R ((n : ℚ) + 1)⁻¹ := by rw [h]
    _ = y := by rw [mul_assoc, h1, mul_one]

/-- Over a `ℚ`-algebra a power series is determined by its constant term together with its
logarithmic derivative. -/
lemma powerSeries_ext_of_logDeriv [Algebra ℚ R] {Q F G : PowerSeries R}
    (hF : PowerSeries.derivative R F = Q * F) (hG : PowerSeries.derivative R G = Q * G)
    (h0 : PowerSeries.coeff 0 F = PowerSeries.coeff 0 G) : F = G := by
  have key : ∀ n m : ℕ, m ≤ n → PowerSeries.coeff m F = PowerSeries.coeff m G := by
    intro n
    induction n with
    | zero => intro m hm; rw [Nat.le_zero.mp hm]; exact h0
    | succ n ih =>
      intro m hm
      rcases eq_or_lt_of_le hm with rfl | hlt
      · refine mul_natSucc_cancel n ?_
        have e1 : PowerSeries.coeff (n + 1) F * ((n : R) + 1)
            = ∑ ij ∈ antidiagonal n,
              PowerSeries.coeff ij.1 Q * PowerSeries.coeff ij.2 F := by
          rw [← PowerSeries.coeff_derivative, hF, PowerSeries.coeff_mul]
        have e2 : PowerSeries.coeff (n + 1) G * ((n : R) + 1)
            = ∑ ij ∈ antidiagonal n,
              PowerSeries.coeff ij.1 Q * PowerSeries.coeff ij.2 G := by
          rw [← PowerSeries.coeff_derivative, hG, PowerSeries.coeff_mul]
        rw [e1, e2]
        refine Finset.sum_congr rfl fun ij hij => ?_
        rw [ih ij.2 (by simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij; omega)]
      · exact ih m (Nat.lt_succ_iff.mp hlt)
  exact PowerSeries.ext fun n => key n n le_rfl

/-- Logarithmic derivatives add under multiplication of power series. -/
lemma derivative_mul_of_logDeriv {Q Q' F G : PowerSeries R}
    (hF : PowerSeries.derivative R F = Q * F) (hG : PowerSeries.derivative R G = Q' * G) :
    PowerSeries.derivative R (F * G) = (Q + Q') * (F * G) := by
  rw [Derivation.leibniz, hF, hG, smul_eq_mul, smul_eq_mul]
  ring

/-- Rescaling the variable multiplies the derivative by the scaling factor. -/
lemma derivative_rescale (c : R) (f : PowerSeries R) :
    PowerSeries.derivative R (PowerSeries.rescale c f)
      = PowerSeries.C c * PowerSeries.rescale c (PowerSeries.derivative R f) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale, PowerSeries.coeff_derivative]
  ring

/-- The geometric series of `a` has logarithmic derivative `∑ₖ a ^ (k + 1) zᵏ`. -/
lemma derivative_geometric (a : R) :
    PowerSeries.derivative R (PowerSeries.mk fun k => a ^ k)
      = (PowerSeries.mk fun k => a ^ (k + 1)) * PowerSeries.mk fun k => a ^ k := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]
  have hterm : ∀ k ∈ range (n + 1), a ^ (k + 1) * a ^ (n - k) = a ^ (n + 1) := by
    intro k hk
    rw [← pow_add]
    congr 1
    have := Finset.mem_range.mp hk
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

end PowerSeriesAux

/-! ### Newton's identity in generating-series form -/

section Newton

variable {K : Type*} [CommRing K] [Algebra ℚ K]

omit [Algebra ℚ K] in
/-- The power sum `p_{k+1}` is the generator with index `k`. -/
lemma powerSum_succ (k : ℕ) : Sym.powerSum K (k + 1) = MvPolynomial.X k := by
  rw [Sym.powerSum, Nat.add_sub_cancel]

/-- The zeroth complete homogeneous symmetric function is one. -/
lemma completeHomog_zero : Sym.completeHomog K 0 = 1 := by
  rw [Sym.completeHomog]

/-- The first complete homogeneous symmetric function is the first power sum. -/
lemma completeHomog_one : Sym.completeHomog K 1 = Sym.powerSum K 1 := by
  rw [Sym.completeHomog]
  simp [completeHomog_zero]

omit [Algebra ℚ K] in
/-- The first power sum is the generator with index zero. -/
lemma powerSum_one : Sym.powerSum K 1 = MvPolynomial.X 0 := powerSum_succ 0

omit [Algebra ℚ K] in
/-- The second power sum is the generator with index one. -/
lemma powerSum_two : Sym.powerSum K 2 = MvPolynomial.X 1 := powerSum_succ 1

/-- Newton's identity for the complete homogeneous symmetric functions, cleared of its
denominator. -/
lemma natCast_mul_completeHomog (n : ℕ) :
    ((n : Sym.Lambda K) + 1) * Sym.completeHomog K (n + 1)
      = ∑ k ∈ range (n + 1), Sym.powerSum K (k + 1) * Sym.completeHomog K (n - k) := by
  rw [Sym.completeHomog]
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have e : ((n : Sym.Lambda K) + 1) = MvPolynomial.C ((n : K) + 1) := by
    rw [map_add, MvPolynomial.C_1, map_natCast]
  have key : ((n : K) + 1) * algebraMap ℚ K ((n : ℚ) + 1)⁻¹ = 1 := by
    rw [show ((n : K) + 1) = algebraMap ℚ K ((n : ℚ) + 1) by
      rw [map_add, map_natCast, map_one], ← map_mul, mul_inv_cancel₀ hn, map_one]
  rw [e, ← mul_assoc, ← MvPolynomial.C_mul, key, MvPolynomial.C_1, one_mul]

/-- The generating series of the images of the complete homogeneous symmetric functions under a
ring homomorphism has logarithmic derivative the generating series of the images of the power
sums. -/
lemma derivative_mk_completeHomog {R : Type*} [CommRing R] {F : Type*}
    [FunLike F (Sym.Lambda K) R] [RingHomClass F (Sym.Lambda K) R] (f : F) :
    PowerSeries.derivative R (PowerSeries.mk fun n => f (Sym.completeHomog K n))
      = (PowerSeries.mk fun k => f (Sym.powerSum K (k + 1)))
        * PowerSeries.mk fun n => f (Sym.completeHomog K n) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]
  have h := congrArg f (natCast_mul_completeHomog (K := K) n)
  rw [map_mul, map_sum] at h
  simp only [map_add, map_natCast, map_one, map_mul] at h
  rw [← h]
  ring

/-- The identity homomorphism case of `derivative_mk_completeHomog`. -/
lemma derivative_mk_completeHomog_self :
    PowerSeries.derivative (Sym.Lambda K) (PowerSeries.mk fun n => Sym.completeHomog K n)
      = (PowerSeries.mk fun k => Sym.powerSum K (k + 1))
        * PowerSeries.mk fun n => Sym.completeHomog K n := by
  simpa using derivative_mk_completeHomog (RingHom.id (Sym.Lambda K))

/-- Adding one letter `a` to the alphabet. If a ring homomorphism `g` exceeds `f` on every power
sum `p_k` by `a ^ k`, then `g` sends `h_n` to `∑ₖ aᵏ f(h_{n-k})`. -/
lemma completeHomog_add_letter {R : Type*} [CommRing R] [Algebra ℚ R] {F G : Type*}
    [FunLike F (Sym.Lambda K) R] [RingHomClass F (Sym.Lambda K) R]
    [FunLike G (Sym.Lambda K) R] [RingHomClass G (Sym.Lambda K) R] (f : F) (g : G) (a : R)
    (h : ∀ i : ℕ, g (MvPolynomial.X i) = f (MvPolynomial.X i) + a ^ (i + 1)) (n : ℕ) :
    g (Sym.completeHomog K n)
      = ∑ k ∈ range (n + 1), a ^ k * f (Sym.completeHomog K (n - k)) := by
  have hQ : (PowerSeries.mk fun k => a ^ (k + 1))
      + (PowerSeries.mk fun k => f (Sym.powerSum K (k + 1)))
      = PowerSeries.mk fun k => g (Sym.powerSum K (k + 1)) := by
    refine PowerSeries.ext fun k => ?_
    simp only [map_add, PowerSeries.coeff_mk]
    rw [powerSum_succ, h k]
    ring
  have key : (PowerSeries.mk fun n => g (Sym.completeHomog K n))
      = (PowerSeries.mk fun k => a ^ k) * PowerSeries.mk fun n => f (Sym.completeHomog K n) := by
    refine powerSeries_ext_of_logDeriv (derivative_mk_completeHomog g) ?_ ?_
    · rw [derivative_mul_of_logDeriv (derivative_geometric a) (derivative_mk_completeHomog f), hQ]
    · simp [PowerSeries.coeff_mul, completeHomog_zero]
  have hc := congrArg (PowerSeries.coeff n) key
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simpa using hc

/-- Newton's identity at `n = 2`: `2 h₂ = p₁² + p₂`. -/
lemma two_mul_completeHomog_two :
    (2 : Sym.Lambda K) * Sym.completeHomog K 2
      = Sym.powerSum K 1 ^ 2 + Sym.powerSum K 2 := by
  have h := natCast_mul_completeHomog (K := K) 1
  rw [show ((1 : ℕ) : Sym.Lambda K) + 1 = 2 by norm_num] at h
  rw [h]
  simp [Finset.sum_range_succ, completeHomog_zero, completeHomog_one, sq]

end Newton

/-! ### The divided alphabet `X / (1 - q)` -/

section Divided

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- Division of the alphabet by `1 - q`: the `L`-algebra endomorphism of `Lambda L` sending the
power sum `p_k` to `p_k / (1 - q ^ k)`, written `f[X / (1 - q)]` on elements. Note that this is
not a scaling of the alphabet, since the denominator is `1 - q ^ k` and not `(1 - q) ^ k`. -/
noncomputable def plethDiv (q : L) : Sym.Lambda L →ₐ[L] Sym.Lambda L :=
  MvPolynomial.aeval fun i => MvPolynomial.C (1 - q ^ (i + 1))⁻¹ * MvPolynomial.X i

omit [Algebra ℚ L] in
/-- The value of the divided alphabet on a generator. -/
lemma plethDiv_X (q : L) (i : ℕ) :
    plethDiv q (MvPolynomial.X i) = MvPolynomial.C (1 - q ^ (i + 1))⁻¹ * MvPolynomial.X i := by
  simp [plethDiv]

/-- The generating identity `H_X(v) · H_Y(q v) = H_Y(v)` for the divided alphabet
`Y = X / (1 - q)`, read off coefficientwise. -/
lemma plethDiv_completeHomog (q : L) (hq : ∀ k : ℕ, q ^ (k + 1) ≠ 1) (n : ℕ) :
    plethDiv q (Sym.completeHomog L n)
      = ∑ j ∈ range (n + 1), Sym.completeHomog L j *
          (MvPolynomial.C (q ^ (n - j)) * plethDiv q (Sym.completeHomog L (n - j))) := by
  have hdA : PowerSeries.derivative (Sym.Lambda L)
      (PowerSeries.mk fun n => plethDiv q (Sym.completeHomog L n))
      = (PowerSeries.mk fun k => plethDiv q (Sym.powerSum L (k + 1)))
        * PowerSeries.mk fun n => plethDiv q (Sym.completeHomog L n) :=
    derivative_mk_completeHomog (plethDiv q)
  have hdA' : PowerSeries.derivative (Sym.Lambda L)
      (PowerSeries.rescale (MvPolynomial.C q)
        (PowerSeries.mk fun n => plethDiv q (Sym.completeHomog L n)))
      = (PowerSeries.C (MvPolynomial.C q) * PowerSeries.rescale (MvPolynomial.C q)
            (PowerSeries.mk fun k => plethDiv q (Sym.powerSum L (k + 1))))
        * PowerSeries.rescale (MvPolynomial.C q)
            (PowerSeries.mk fun n => plethDiv q (Sym.completeHomog L n)) := by
    rw [derivative_rescale, hdA, map_mul]
    ring
  have hsum : (PowerSeries.mk fun k => Sym.powerSum L (k + 1))
      + (PowerSeries.C (MvPolynomial.C q) * PowerSeries.rescale (MvPolynomial.C q)
          (PowerSeries.mk fun k => plethDiv q (Sym.powerSum L (k + 1))))
      = PowerSeries.mk fun k => plethDiv q (Sym.powerSum L (k + 1)) := by
    refine PowerSeries.ext fun k => ?_
    rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, powerSum_succ, plethDiv_X]
    have hne : (1 : L) - q ^ (k + 1) ≠ 0 := sub_ne_zero_of_ne (Ne.symm (hq k))
    have hprod : (MvPolynomial.C q : Sym.Lambda L) * MvPolynomial.C q ^ k
        * MvPolynomial.C ((1 : L) - q ^ (k + 1))⁻¹
        = MvPolynomial.C (q ^ (k + 1) * ((1 : L) - q ^ (k + 1))⁻¹) := by
      rw [← map_pow, ← MvPolynomial.C_mul, ← MvPolynomial.C_mul, pow_succ']
    have hone : (1 : Sym.Lambda L)
        + (MvPolynomial.C (q ^ (k + 1) * ((1 : L) - q ^ (k + 1))⁻¹) : Sym.Lambda L)
        = MvPolynomial.C ((1 : L) - q ^ (k + 1))⁻¹ := by
      rw [← MvPolynomial.C_1, ← MvPolynomial.C_add]
      congr 1
      field_simp
      ring
    linear_combination (MvPolynomial.X k : Sym.Lambda L) * hone
      + (MvPolynomial.X k : Sym.Lambda L) * hprod
  have key : (PowerSeries.mk fun n => plethDiv q (Sym.completeHomog L n))
      = (PowerSeries.mk fun n => Sym.completeHomog L n)
        * PowerSeries.rescale (MvPolynomial.C q)
            (PowerSeries.mk fun n => plethDiv q (Sym.completeHomog L n)) := by
    refine powerSeries_ext_of_logDeriv hdA ?_ ?_
    · rw [derivative_mul_of_logDeriv derivative_mk_completeHomog_self hdA', hsum]
    · simp [PowerSeries.coeff_mul, completeHomog_zero, PowerSeries.coeff_rescale]
  have hc := congrArg (PowerSeries.coeff n) key
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simpa only [PowerSeries.coeff_mk, PowerSeries.coeff_rescale, map_pow] using hc

/-! ### The first creation operator on the divided alphabet -/

omit [Algebra ℚ L] in
/-- Pairing a monomial in `w = z⁻¹` against a family of symmetric functions picks out the
member matching its degree. -/
lemma coeffPairing_monomial (c : ℕ → Sym.Lambda L) (k : ℕ) (b : Sym.Lambda L) :
    Sym.coeffPairing c (Polynomial.monomial k b) = b * c k := by
  change (Polynomial.monomial k b).sum (fun j A => A * c j) = b * c k
  exact Polynomial.sum_monomial_index b _ (by simp)

omit [Algebra ℚ L] in
/-- Constants of `L`, viewed in the polynomial ring in `w = z⁻¹` over `Lambda L`. -/
lemma algebraMap_eq_C_C (c : L) :
    algebraMap L (Polynomial (Sym.Lambda L)) c = Polynomial.C (MvPolynomial.C c) := by
  rw [IsScalarTower.algebraMap_apply L (Sym.Lambda L) (Polynomial (Sym.Lambda L)),
    MvPolynomial.algebraMap_eq, Polynomial.algebraMap_eq]

omit [Algebra ℚ L] in
/-- A power of the single letter `1 / (q z)` times a constant is a monomial in `w = z⁻¹`. -/
lemma letter_pow_mul_C (q : L) (k : ℕ) (b : Sym.Lambda L) :
    (Polynomial.C (MvPolynomial.C q⁻¹) * Polynomial.X) ^ k * Polynomial.C b
      = Polynomial.monomial k (MvPolynomial.C (q⁻¹ ^ k) * b) := by
  rw [mul_pow, ← map_pow, ← map_pow, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul]
  ring

omit [Algebra ℚ L] in
/-- On a generator, the creation displacement of the divided alphabet adds the single letter
`1 / (q z)` to it. -/
lemma plethCreate_plethDiv_X (q : L) (hq0 : q ≠ 0) (hq : ∀ k : ℕ, q ^ (k + 1) ≠ 1) (i : ℕ) :
    Sym.plethCreate q (plethDiv q (MvPolynomial.X i))
      = Polynomial.C (plethDiv q (MvPolynomial.X i))
        + (Polynomial.C (MvPolynomial.C q⁻¹) * Polynomial.X) ^ (i + 1) := by
  have hne : (1 : L) - q ^ (i + 1) ≠ 0 := sub_ne_zero_of_ne (Ne.symm (hq i))
  have hp : q ^ (i + 1) ≠ 0 := pow_ne_zero _ hq0
  rw [plethDiv_X, map_mul, Sym.plethCreate, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    algebraMap_eq_C_C, powerSum_succ, mul_pow, ← map_pow, ← map_pow]
  have hA : (Polynomial.C (MvPolynomial.C ((1 : L) - q ^ (i + 1))⁻¹)
        : Polynomial (Sym.Lambda L)) * Polynomial.C (MvPolynomial.X i)
      = Polynomial.C (MvPolynomial.C ((1 : L) - q ^ (i + 1))⁻¹ * MvPolynomial.X i) := by
    rw [← Polynomial.C_mul]
  have hB : (Polynomial.C (MvPolynomial.C ((1 : L) - q ^ (i + 1))⁻¹)
        : Polynomial (Sym.Lambda L))
        * Polynomial.C (MvPolynomial.C ((1 : L) - (q ^ (i + 1))⁻¹))
      = -Polynomial.C (MvPolynomial.C (q⁻¹ ^ (i + 1))) := by
    rw [← Polynomial.C_mul, ← MvPolynomial.C_mul, ← map_neg, ← map_neg, inv_pow]
    congr 2
    field_simp
    ring
  linear_combination hA - (Polynomial.X : Polynomial (Sym.Lambda L)) ^ (i + 1) * hB

/-- The first creation operator, unfolded: the creation displacement paired against the complete
homogeneous symmetric functions shifted up by one. -/
lemma cop_one_apply (q : L) (f : Sym.Lambda L) :
    Sym.Cop q 1 f
      = Sym.coeffPairing (fun j => Sym.completeHomog L (1 + j)) (Sym.plethCreate q f) := by
  rw [Sym.Cop]
  simp

/-- The first creation operator advances the divided-alphabet complete homogeneous symmetric
functions, at the cost of an explicit scalar. -/
lemma cop_one_plethDiv_completeHomog (q : L) (hq0 : q ≠ 0) (hq : ∀ k : ℕ, q ^ (k + 1) ≠ 1)
    (N : ℕ) :
    Sym.Cop q 1 (plethDiv q (Sym.completeHomog L N))
      = MvPolynomial.C (q⁻¹ ^ N * (1 - q ^ (N + 1)))
        * plethDiv q (Sym.completeHomog L (N + 1)) := by
  have hshift := completeHomog_add_letter (K := L)
    ((Polynomial.C : Sym.Lambda L →+* Polynomial (Sym.Lambda L)).comp (plethDiv q).toRingHom)
    ((Sym.plethCreate q).comp (plethDiv q))
    (Polynomial.C (MvPolynomial.C q⁻¹) * Polynomial.X)
    (fun i => by simpa using plethCreate_plethDiv_X q hq0 hq i) N
  simp only [AlgHom.coe_comp, Function.comp_apply, RingHom.coe_comp,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hshift
  rw [cop_one_apply, hshift, map_sum]
  simp only [letter_pow_mul_C, coeffPairing_monomial]
  have hkey := plethDiv_completeHomog q hq (N + 1)
  rw [Finset.sum_range_succ'] at hkey
  simp only [Nat.sub_zero, completeHomog_zero, one_mul, Nat.add_sub_add_right] at hkey
  have hmul : MvPolynomial.C (q ^ N) * (∑ x ∈ range (N + 1),
        MvPolynomial.C (q⁻¹ ^ x) * plethDiv q (Sym.completeHomog L (N - x))
          * Sym.completeHomog L (1 + x))
      = ∑ i ∈ range (N + 1), Sym.completeHomog L (i + 1)
          * (MvPolynomial.C (q ^ (N - i)) * plethDiv q (Sym.completeHomog L (N - i))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hqs : q ^ (N - k) * q ^ k = q ^ N := by
      rw [← pow_add, Nat.sub_add_cancel hkN]
    have hqs2 : q ^ N * q⁻¹ ^ k = q ^ (N - k) := by
      rw [← hqs, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero k hq0), mul_one]
    have hC : (MvPolynomial.C (q ^ N) : Sym.Lambda L) * MvPolynomial.C (q⁻¹ ^ k)
        = MvPolynomial.C (q ^ (N - k)) := by
      rw [← MvPolynomial.C_mul, hqs2]
    rw [add_comm 1 k]
    linear_combination (plethDiv q (Sym.completeHomog L (N - k))
      * Sym.completeHomog L (k + 1)) * hC
  refine mul_left_cancel₀ (a := (MvPolynomial.C (q ^ N) : Sym.Lambda L)) ?_ ?_
  · rw [Ne, MvPolynomial.C_eq_zero]
    exact pow_ne_zero N hq0
  · rw [hmul, ← mul_assoc, ← MvPolynomial.C_mul]
    have hqq : q ^ N * (q⁻¹ ^ N * (1 - q ^ (N + 1))) = 1 - q ^ (N + 1) := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, one_mul]
    rw [hqq, MvPolynomial.C_sub, MvPolynomial.C_1, sub_mul, one_mul]
    linear_combination -hkey

/-- Iterating the first creation operator on `1`, with the scalar written as an explicit
product. -/
lemma cop_one_pow_apply_one_prod (q : L) (hq0 : q ≠ 0) (hq : ∀ k : ℕ, q ^ (k + 1) ≠ 1) (N : ℕ) :
    (Sym.Cop q 1 ^ N) 1
      = MvPolynomial.C (q⁻¹ ^ N.choose 2 * ∏ j ∈ range N, (1 - q ^ (j + 1)))
        * plethDiv q (Sym.completeHomog L N) := by
  induction N with
  | zero => simp [completeHomog_zero]
  | succ N ih =>
    have hch : (N + 1).choose 2 = N.choose 2 + N := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    rw [pow_succ', Module.End.mul_apply, ih, ← MvPolynomial.smul_eq_C_mul, map_smul,
      cop_one_plethDiv_completeHomog q hq0 hq N, MvPolynomial.smul_eq_C_mul, ← mul_assoc,
      ← MvPolynomial.C_mul, hch, Finset.prod_range_succ, pow_add]
    ring_nf

/-- The first creation operator sends `1` to the first power sum. -/
lemma cop_one_apply_one (q : L) (hq0 : q ≠ 0) (hq : ∀ k : ℕ, q ^ (k + 1) ≠ 1) :
    Sym.Cop q 1 1 = Sym.powerSum L 1 := by
  have hne : (1 : L) - q ≠ 0 := by simpa using sub_ne_zero_of_ne (Ne.symm (hq 0))
  have h := cop_one_plethDiv_completeHomog q hq0 hq 0
  rw [completeHomog_zero, map_one] at h
  rw [h, zero_add, completeHomog_one, powerSum_succ, plethDiv_X, ← mul_assoc,
    ← MvPolynomial.C_mul, pow_zero, one_mul, pow_one, mul_inv_cancel₀ hne,
    MvPolynomial.C_1, one_mul]

/-- The rank-two seed, cleared of its denominator: `2 · C₁² 1 = (1 + q⁻¹) p₁² + (q⁻¹ - 1) p₂`.
The extra factor at rank two is `q⁻¹`, not `1`. -/
lemma two_mul_cop_one_sq_apply_one (q : L) (hq0 : q ≠ 0) (hq : ∀ k : ℕ, q ^ (k + 1) ≠ 1) :
    (2 : Sym.Lambda L) * (Sym.Cop q 1 ^ 2) 1
      = MvPolynomial.C (1 + q⁻¹) * Sym.powerSum L 1 ^ 2
        + MvPolynomial.C (q⁻¹ - 1) * Sym.powerSum L 2 := by
  have h1 : (1 : L) - q ≠ 0 := by simpa using sub_ne_zero_of_ne (Ne.symm (hq 0))
  have h2 : (1 : L) - q ^ 2 ≠ 0 := by simpa using sub_ne_zero_of_ne (Ne.symm (hq 1))
  have hd := congrArg (plethDiv q) (two_mul_completeHomog_two (K := L))
  rw [map_mul, map_add, map_pow, powerSum_one, powerSum_two, plethDiv_X, plethDiv_X,
    map_ofNat] at hd
  rw [cop_one_pow_apply_one_prod q hq0 hq 2, mul_left_comm, hd, powerSum_one, powerSum_two]
  have hs : q⁻¹ ^ Nat.choose 2 2 * ∏ j ∈ range 2, (1 - q ^ (j + 1))
      = q⁻¹ * ((1 - q) * (1 - q ^ 2)) := by
    norm_num [Finset.prod_range_succ]
  have e1 : q⁻¹ * ((1 - q) * (1 - q ^ 2)) * ((1 - q ^ (0 + 1))⁻¹ ^ 2) = 1 + q⁻¹ := by
    rw [zero_add, pow_one]
    field_simp
    ring
  have e2 : q⁻¹ * ((1 - q) * (1 - q ^ 2)) * (1 - q ^ (1 + 1))⁻¹ = q⁻¹ - 1 := by
    rw [show (1 : ℕ) + 1 = 2 from rfl]
    field_simp
  have hc1 : (MvPolynomial.C (q⁻¹ * ((1 - q) * (1 - q ^ 2))) : Sym.Lambda L)
      * MvPolynomial.C ((1 - q ^ (0 + 1))⁻¹ ^ 2) = MvPolynomial.C (1 + q⁻¹) := by
    rw [← MvPolynomial.C_mul, e1]
  have hc2 : (MvPolynomial.C (q⁻¹ * ((1 - q) * (1 - q ^ 2))) : Sym.Lambda L)
      * MvPolynomial.C ((1 - q ^ (1 + 1))⁻¹) = MvPolynomial.C (q⁻¹ - 1) := by
    rw [← MvPolynomial.C_mul, e2]
  rw [hs, mul_pow, ← map_pow]
  linear_combination (MvPolynomial.X 0 ^ 2 : Sym.Lambda L) * hc1
    + (MvPolynomial.X 1 : Sym.Lambda L) * hc2

/-- The iterated creation seed: applying the first creation operator `N` times to `1` gives
`q ^ (-C(N, 2))` times the `q`-Pochhammer symbol `(q; q)_N` times `h_N[X / (1 - q)]`. -/
@[hjo "lem_cop_power"]
theorem cop_one_pow_apply_one (q : L) (hq0 : q ≠ 0) (hq : ∀ k : ℕ, q ^ (k + 1) ≠ 1) (N : ℕ) :
    (Sym.Cop q 1 ^ N) 1
      = MvPolynomial.C (q ^ (-(N.choose 2 : ℤ)) * qPochhammer q q N)
        * plethDiv q (Sym.completeHomog L N) := by
  have hsc : q ^ (-(N.choose 2 : ℤ)) * qPochhammer q q N
      = q⁻¹ ^ N.choose 2 * ∏ j ∈ range N, (1 - q ^ (j + 1)) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, qPochhammer]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by rw [pow_succ']
  rw [cop_one_pow_apply_one_prod q hq0 hq N, hsc]

end Divided

end HJO.CopPower
