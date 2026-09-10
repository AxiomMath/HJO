/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Main.Endgame
public import HJO.Determinant.DetCoeffSolves
public meta import HJO.Attr

/-! # The scalar recurrence implies the common equation

`HJO.Endgame.finiteSeries_recurrence` reads the common `q`-difference equation satisfied by
the HJO generating series off at each coefficient of `z`. This module runs that computation
backwards: the recurrence for every positive rank, together with the value `1` of the finite
polynomial at rank zero, is enough to recover the equation itself.

Two power series in `z` are equal exactly when all their coefficients agree, so the equation is
the family of scalar identities indexed by the rank. At rank `N` the identity is the recurrence
with the denominators `(q)_N` restored, and at rank `0` it is the tautology `1 = 1`; the
normalisation `ℋ(0;q) = 1` is the rank-zero value of the finite polynomial.
-/

@[expose] public section

open Finset
open scoped PowerSeries QTheory

namespace HJO.RecurrenceConverse

/-- The converse of `HJO.Endgame.finiteSeries_recurrence`: the scalar recurrence for every
positive rank implies that the HJO generating series satisfies the common equation. Multiplying
the recurrence at rank `N` by `(q)_{N-1}⁻¹` turns the displayed finite product back into the
Pochhammer quotient `(q)_{N-1} / (q)_{N-k}`, and `(1 - q^N) (q)_{N-1} = (q)_N` makes the result
the `z^N` coefficient of the equation; the rank-zero coefficient holds unconditionally, and the
normalisation is `F_0(q) = 1`. -/
@[hjo "lem_recurrence_converse"]
theorem isCommonSolution_of_recurrence (a b : ℕ) (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b)
    (hrec : ∀ N : ℕ, 0 < N →
      (PowerSeries.X : PowerSeries ℤ) ^ Paths.gammaShift a b N * Gaps.finiteSeries a b N
        = ∑ j ∈ Icc 1 N, (-1 : PowerSeries ℤ) ^ (j + 1) * Paths.areaPoly a b j *
            PowerSeries.X ^ Paths.gammaShift a b (N - j) * Gaps.finiteSeries a b (N - j) *
            ∏ i ∈ Ico (N - j + 1) N, (1 - PowerSeries.X ^ i)) :
    Determinant.IsCommonSolution a b (Determinant.genH a b) := by
  have hDne : ∀ M : ℕ, Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_M ≠ 0 :=
    Endgame.qOfInt_qPochhammer_ne_zero
  have hgA : ∀ k : ℕ, PowerSeries.coeff k (PowerSeries.rescale (-1) (Determinant.genA a b))
      = (-1) ^ k * Determinant.qOfInt (Paths.areaPoly a b k) := fun k => by
    rw [PowerSeries.coeff_rescale, Determinant.genA, PowerSeries.coeff_mk]
  have hgH : ∀ M : ℕ, PowerSeries.coeff M (Determinant.genH a b)
      = Determinant.qOfInt (PowerSeries.X ^ Paths.gammaShift a b M * Gaps.finiteSeries a b M) /
        Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_M := fun M => by
    rw [Determinant.genH, PowerSeries.coeff_mk]
  refine ⟨PowerSeries.ext fun N => ?_, ?_⟩
  · have hS : (Determinant.qVar ^ N - 1) *
          (Determinant.qOfInt (PowerSeries.X ^ Paths.gammaShift a b N * Gaps.finiteSeries a b N) /
            Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_N)
        = ∑ k ∈ Icc 1 N, (-1) ^ k * Determinant.qOfInt (Paths.areaPoly a b k) *
            (Determinant.qOfInt (PowerSeries.X ^ Paths.gammaShift a b (N - k) *
                Gaps.finiteSeries a b (N - k)) /
              Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_(N - k)) := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · have hI : Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
        rw [pow_zero, sub_self, zero_mul, hI, Finset.sum_empty]
      have ht : (1 : LaurentSeries ℚ) - Determinant.qVar ^ N ≠ 0 := by
        have h := Endgame.one_sub_qVar_pow_ne_zero (N - 1)
        rwa [show N - 1 + 1 = N from by omega] at h
      have hDN : Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_N
          = Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_(N - 1) *
            (1 - Determinant.qVar ^ N) := by
        rw [← Endgame.qPochhammer_self_succ hN, map_mul, map_sub, map_one, map_pow,
          ← Determinant.qVar]
      have hterm : ∀ k ∈ Icc 1 N, Determinant.qOfInt ((-1 : PowerSeries ℤ) ^ (k + 1) *
            Paths.areaPoly a b k * PowerSeries.X ^ Paths.gammaShift a b (N - k) *
            Gaps.finiteSeries a b (N - k) * ∏ j ∈ Ico (N - k + 1) N, (1 - PowerSeries.X ^ j))
          = -Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_(N - 1) *
            ((-1) ^ k * Determinant.qOfInt (Paths.areaPoly a b k) *
              (Determinant.qOfInt (PowerSeries.X ^ Paths.gammaShift a b (N - k) *
                  Gaps.finiteSeries a b (N - k)) /
                Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_(N - k))) := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        have hsplit : Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_(N - 1)
            = Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_(N - k) *
              Determinant.qOfInt (∏ j ∈ Ico (N - k + 1) N, (1 - PowerSeries.X ^ j)) := by
          rw [← map_mul, Endgame.qPochhammer_self_split hk.1 hk.2]
        have hne := hDne (N - k)
        rw [hsplit]
        simp only [map_mul, map_pow, map_neg, map_one]
        field_simp
        ring
      have hmapped := congrArg Determinant.qOfInt (hrec N hN)
      rw [map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hmapped
      have hD1 := hDne (N - 1)
      rw [hDN, hmapped]
      field_simp
      ring
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Endgame.sum_range_succ_eq_add_sum_Icc]
    simp only [hgA, hgH, Nat.sub_zero, pow_zero, AExponential.areaPoly_zero, map_one, one_mul]
    linear_combination hS
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hgH 0, Paths.gammaShift,
      Endgame.finiteSeries_zero a b hab ha hb, qPochhammer_zero, map_one, div_one]
    simp

/-! ### What the converse buys

The determinant coefficient count is unconditional --- it assumes nothing from the literature ---
and the uniqueness of the normalised solution is proved outright. So once the recurrence yields
the common equation, the finite identity follows from the recurrence *alone*: none of the eight
external inputs is needed, coercivity included.

This is worth stating separately: it offers the recurrence as a hypothesis and assumes nothing from
the literature.
-/

/-- **The finite identity, from the recurrence alone.** `F_N(q) = (q)_N C_{𝐜,≤N}(q)` for every
rank, assuming only the scalar recurrence and the arithmetic on `a` and `b`. -/
theorem finiteSeries_eq_qPochhammer_mul_boundedGF_of_recurrence (a b : ℕ) (hab : Nat.Coprime a b)
    (ha : 1 < a) (hb : a < b)
    (hrec : ∀ N : ℕ, 0 < N →
      (PowerSeries.X : PowerSeries ℤ) ^ Paths.gammaShift a b N * Gaps.finiteSeries a b N
        = ∑ j ∈ Icc 1 N, (-1 : PowerSeries ℤ) ^ (j + 1) * Paths.areaPoly a b j *
            PowerSeries.X ^ Paths.gammaShift a b (N - j) * Gaps.finiteSeries a b (N - j) *
            ∏ i ∈ Ico (N - j + 1) N, (1 - PowerSeries.X ^ i)) (N : ℕ) :
    Gaps.finiteSeries a b N
      = (PowerSeries.X; PowerSeries.X)_N * HJO.Cylindric.boundedGF a b N :=
  Endgame.finiteSeries_eq_qPochhammer_mul_boundedGF hab (by omega) (by omega)
    (isCommonSolution_of_recurrence a b hab ha hb hrec)
    (fun M => by
      rw [DetCoeffSolves.coeff_rescale_neg_one_detSeries a b M hab (by omega) (by omega),
        map_mul, map_pow, ← Determinant.qVar])
    N

end HJO.RecurrenceConverse
