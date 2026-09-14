/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.PowerSeries.Order
public import QSeriesLib.RingTheory.PowerSeries.PiTopology
public import HJO.Series.Limits
public meta import HJO.Attr

/-! # Products of integer powers of `1 - q^m` determine their exponents

A convergent product `∏_{m ≥ 1} (1 - q^m)^{e(m)}` with integer exponents determines the
exponent sequence `e`. The proof reads off one coefficient at a time: the factor indexed by `m` is
congruent to `1` modulo `q^{m+1}`, so at degree `m + 1` the whole product reads off `-e(m+1)`,
the factors below `m` being trivial by induction and those above contributing nothing.

The integer powers are `HJO.Limits.zpowOneSub`, taken in the unit group of `ℤ⟦X⟧`, indexed so
that `zpowOneSub m k = (1 - q^{m+1})^k`. The one further fact recorded here is that the
self-Pochhammer symbol `(q^d; q^d)_∞` is a unit, so that it may be cancelled.
-/

@[expose] public section

open Finset Filter PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-! ### The coefficient at the critical degree -/

/-- Two power series congruent to `1` modulo `q^{m+1}` have additive coefficients at degree
`m + 1`: the cross term of the product is divisible by `q^{2m+2}`. -/
theorem coeff_succ_mul_of_dvd {m : ℕ} {A B : ℤ⟦X⟧} (hA : (X : ℤ⟦X⟧) ^ (m + 1) ∣ A - 1)
    (hB : (X : ℤ⟦X⟧) ^ (m + 1) ∣ B - 1) :
    coeff (m + 1) (A * B) = coeff (m + 1) A + coeff (m + 1) B := by
  have hone : coeff (m + 1) (1 : ℤ⟦X⟧) = 0 := by simp
  have hcross : coeff (m + 1) ((A - 1) * (B - 1)) = 0 := by
    obtain ⟨A', hA'⟩ := hA
    obtain ⟨B', hB'⟩ := hB
    have hdvd : (X : ℤ⟦X⟧) ^ (m + 1 + (m + 1)) ∣ (A - 1) * (B - 1) := by
      rw [hA', hB', pow_add]
      exact ⟨A' * B', by ring⟩
    exact PowerSeries.X_pow_dvd_iff.mp hdvd (m + 1) (by omega)
  have hexp : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by ring
  have h1 : coeff (m + 1) (A * B - 1) = coeff (m + 1) (A - 1) + coeff (m + 1) (B - 1) := by
    rw [hexp, map_add, map_add, hcross, add_zero]
  rw [map_sub, hone, sub_zero] at h1
  rw [map_sub, hone, sub_zero, map_sub, hone, sub_zero] at h1
  exact h1

/-- The coefficient of `q^{m+1}` in `(1 - q^{m+1})^k` is `-k`, for every integer exponent `k`. -/
theorem coeff_succ_zpowOneSub (m : ℕ) (k : ℤ) :
    coeff (m + 1) (Limits.zpowOneSub m k) = -k := by
  have hone : coeff (m + 1) (Limits.zpowOneSub m 1) = -1 := by
    rw [Limits.zpowOneSub_one, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    simp
  have hadd : ∀ k l : ℤ, coeff (m + 1) (Limits.zpowOneSub m (k + l))
      = coeff (m + 1) (Limits.zpowOneSub m k) + coeff (m + 1) (Limits.zpowOneSub m l) := by
    intro k l
    rw [Limits.zpowOneSub_add]
    exact coeff_succ_mul_of_dvd (Limits.X_pow_dvd_zpowOneSub_sub_one m k)
      (Limits.X_pow_dvd_zpowOneSub_sub_one m l)
  have hneg : coeff (m + 1) (Limits.zpowOneSub m (-1)) = 1 := by
    have h := hadd 1 (-1)
    rw [add_neg_cancel, Limits.zpowOneSub_zero, hone] at h
    simp only [PowerSeries.coeff_one] at h
    omega
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [hadd, ih, hone]; ring
  | pred n ih =>
    rw [show (-(n : ℤ) - 1) = (-(n : ℤ)) + (-1) by ring, hadd, ih, hneg]
    ring

/-! ### Reading the exponents off the product -/

/-- Only the factors indexed below `d` reach the coefficient of `q^d`. -/
theorem coeff_tprod_zpowOneSub (e : ℕ → ℤ) (d : ℕ) :
    coeff d (∏' m, Limits.zpowOneSub m (e m))
      = coeff d (∏ m ∈ range d, Limits.zpowOneSub m (e m)) := by
  have horder : ∀ m ≥ d, (d : ℕ∞) < (Limits.zpowOneSub m (e m) - 1).order := by
    intro m hm
    refine lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ (m + 1) fun i hi =>
      PowerSeries.X_pow_dvd_iff.mp (Limits.X_pow_dvd_zpowOneSub_sub_one m (e m)) i hi)
    exact_mod_cast Nat.lt_succ_of_le hm
  rw [PowerSeries.WithPiTopology.coeff_tprod_of_lt_order_sub_one
    (Limits.multipliable_zpowOneSub e) horder, Nat.Iio_eq_range]

/-- A product of integer powers of the `1 - q^m` that equals `1` has every exponent zero. -/
theorem eq_zero_of_tprod_zpowOneSub_eq_one {f : ℕ → ℤ}
    (h : (∏' m, Limits.zpowOneSub m (f m)) = 1) : f = 0 := by
  have key : ∀ n : ℕ, (∀ m < n, f m = 0) → f n = 0 := by
    intro n hn
    have hprod : (∏ m ∈ range (n + 1), Limits.zpowOneSub m (f m)) = Limits.zpowOneSub n (f n) := by
      rw [Finset.prod_range_succ, Finset.prod_congr rfl
        (fun m hm => by rw [hn m (mem_range.mp hm), Limits.zpowOneSub_zero]),
        Finset.prod_const_one, one_mul]
    have h1 : coeff (n + 1) (∏' m, Limits.zpowOneSub m (f m)) = -f n := by
      rw [coeff_tprod_zpowOneSub, hprod, coeff_succ_zpowOneSub]
    rw [h] at h1
    simp only [PowerSeries.coeff_one] at h1
    omega
  have hall : ∀ n : ℕ, ∀ m < n, f m = 0 := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro m hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h' | rfl
      · exact ih m h'
      · exact key m ih
  funext n
  exact key n (hall n)

/-- **A product of these factors determines its exponents.** Two convergent products of integer
powers of the `1 - q^m` agree only if their exponent sequences do. Here `zpowOneSub m k` is
`(1 - q^{m+1})^k`, so the sequences are indexed from `m = 0` standing for the exponent of
`1 - q`. -/
@[hjo "lem_exponent_unique"]
theorem tprod_zpowOneSub_injective {e e' : ℕ → ℤ}
    (h : (∏' m, Limits.zpowOneSub m (e m)) = ∏' m, Limits.zpowOneSub m (e' m)) : e = e' := by
  have hcancel : (∏' m, Limits.zpowOneSub m (e' m)) * (∏' m, Limits.zpowOneSub m (-e' m)) = 1 := by
    rw [Limits.tprod_zpowOneSub_mul]
    simp
  have h1 : (∏' m, Limits.zpowOneSub m (e m + -e' m)) = 1 := by
    rw [← Limits.tprod_zpowOneSub_mul, h, hcancel]
  have h2 := eq_zero_of_tprod_zpowOneSub_eq_one h1
  funext m
  have := congrFun h2 m
  simp only [Pi.zero_apply] at this
  omega

/-! ### The self-Pochhammer symbol is a unit -/

/-- Each factor of `(q^d; q^d)_∞` is congruent to `1` modulo `q^d`, so the product has constant
coefficient `1`. -/
theorem constantCoeff_selfQPochhammerInf {d : ℕ} (hd : 0 < d) :
    constantCoeff ((X ^ d; X ^ d)_∞ : ℤ⟦X⟧) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    Limits.qPochhammerInf_eq_tprod_zpowOneSub hd hd, coeff_tprod_zpowOneSub]
  simp

/-- **The self-Pochhammer symbol is cancellable**: `(q^d; q^d)_∞` is invertible in `ℤ⟦X⟧`,
its constant coefficient being `1`. -/
@[hjo "lem_selfpoch_unit"]
theorem isUnit_selfQPochhammerInf {d : ℕ} (hd : 0 < d) :
    IsUnit ((X ^ d; X ^ d)_∞ : ℤ⟦X⟧) :=
  IsUnit.of_mul_eq_one _ (PowerSeries.mul_invOfUnit _ 1
    (by simpa using constantCoeff_selfQPochhammerInf hd))

end HJO.CylindricProduct
