/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.SignExtraction.Basic
public import HJO.Shuffle.LetterReversal
public meta import HJO.Attr

/-! # Truncating a realisation and a fundamental to the first `m` letters

The two computations `HJO.ParkingFunctions.realisation_completeHomog` and
`HJO.ParkingFunctions.realisation_elemSymm` both run through: what `tr_m` does to a realised power
sum, and what it does to a fundamental quasisymmetric function.

## Main statements

* `HJO.Sym.letterTrunc_realisation_powerSum`: `tr_m(ι(p_k)) = ∑_{i<m} x_i^k`, so the homomorphisms
  `φ_m = tr_m ∘ ι` differ by exactly one letter, which is the hypothesis
  `HJO.CreationSeeds.elemSymm_add_letter` and `HJO.CreationSeeds.completeHomog_add_letter` take.
* `HJO.ParkingFunctions.letterTrunc_gessel`: `tr_m(F_{n,S})` is the sum of the monomials of the
  `S`-ascending words in the first `m` letters, which is the set `W^{(m)}_{n,S}`.

## Implementation notes

The letters are indexed from `0`, so the `1`-based `∑_{i=1}^m x_i^k` is `∑_{i<m} x_i^k` and the
bound `i_n ≤ m` is `i_n < m`, matching `HJO.Sym.boundedWords`.

`letterTrunc_gessel` is the structure of `HJO.ParkingFunctions.coeff_letterEval_gessel` read at the
level of series rather than of one coefficient: the exponent vectors supported in the first `m`
letters at which `F_{n,S}` is nonzero are exactly those of the `S`-ascending words in those letters,
each with coefficient `1`, and `HJO.Sym.eq_of_wordExponent_eq` says distinct such words carry
distinct exponent vectors.

## References

The definitions this file concerns: `HJO.Sym.letterTrunc`, `HJO.Sym.boundedWords` and
`HJO.ParkingFunctions.gessel`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-- **`tr_m` of a realised power sum is the power sum of the first `m` letters.**
`tr_m(ι(p_{k+1})) = ∑_{i<m}x_i^{k+1}`: a realisation puts a `1` at each `x_i^{k+1}` and nothing
else, and `tr_m` keeps exactly those with `i < m`. -/
theorem letterTrunc_realisation_powerSum {K : Type*} [CommRing K]
    {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι) (m k : ℕ) :
    letterTrunc K m (ι (powerSum K (k + 1)))
      = ∑ i ∈ range m, (MvPowerSeries.X i : AlphabetSeries K) ^ (k + 1) := by
  classical
  refine MvPowerSeries.ext fun d => ?_
  have hX : ∀ i : ℕ, MvPowerSeries.coeff d ((MvPowerSeries.X i : AlphabetSeries K) ^ (k + 1))
      = if d = Finsupp.single i (k + 1) then 1 else 0 := fun i => by
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial]
  rw [map_sum, Finset.sum_congr rfl fun i _ => hX i]
  by_cases hd : ∀ i ∈ d.support, i < m
  · rw [coeff_letterTrunc_of_support hd]
    by_cases hex : ∃ i, d = Finsupp.single i (k + 1)
    · obtain ⟨i, rfl⟩ := hex
      have hi : i < m := hd i (by simp)
      rw [hι.coeff_pow k i, Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd ?_ h)]
      · rw [ite_eq_left rfl]
      · exact ite_eq_right fun hcon =>
          hji (Finsupp.single_left_injective (b := k + 1) (by omega) hcon).symm
      · exact mem_range.2 hi
    · rw [hι.coeff_of_ne k d (by simpa using hex)]
      refine (Finset.sum_eq_zero fun i _ => ite_eq_right fun hcon => hex ⟨i, hcon⟩).symm
  · rw [coeff_letterTrunc_of_not_support hd]
    refine (Finset.sum_eq_zero fun i hi => ite_eq_right fun hcon => hd fun j hj => ?_).symm
    rw [hcon, Finsupp.support_single _ (by omega), mem_singleton] at hj
    exact hj ▸ mem_range.1 hi

/-- **One more letter.** `φ_{m+1} = tr_{m+1} ∘ ι` exceeds `φ_m = tr_m ∘ ι` by `x_m^k` on every power
sum `p_k`, which is the hypothesis `HJO.CreationSeeds.elemSymm_add_letter` and
`HJO.CreationSeeds.completeHomog_add_letter` take. -/
theorem letterTrunc_realisation_powerSum_succ {K : Type*} [CommRing K]
    {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι) (m : ℕ) {k : ℕ} (hk : 0 < k) :
    letterTrunc K (m + 1) (ι (powerSum K k))
      = letterTrunc K m (ι (powerSum K k)) + (MvPowerSeries.X m : AlphabetSeries K) ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [letterTrunc_realisation_powerSum hι, letterTrunc_realisation_powerSum hι,
    Finset.sum_range_succ]

end HJO.Sym

namespace HJO.ParkingFunctions

/-- **`tr_m` of a fundamental is the sum over the bounded ascending words.**
`tr_m(F_{n,S}) = ∑_{w ∈ W^{(m)}_{n,S}}x_w`: the coefficients of `F_{n,S}` at the exponent vectors
supported in the first `m` letters are the indicator of the exponent vectors of the `S`-ascending
words in those letters, and distinct such words have distinct exponent vectors. -/
theorem letterTrunc_gessel (K : Type*) [CommRing K] {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Ico 1 n)
    (m : ℕ) :
    Sym.letterTrunc K m (gessel K n S)
      = ∑ w ∈ Sym.boundedWords n S m, MvPowerSeries.monomial (Sym.wordExponent w) 1 := by
  classical
  refine MvPowerSeries.ext fun d => ?_
  rw [map_sum, Finset.sum_congr rfl fun w _ => MvPowerSeries.coeff_monomial d _ (1 : K)]
  by_cases hmem : ∃ w ∈ Sym.boundedWords n S m, Sym.wordExponent w = d
  · obtain ⟨w, hw, rfl⟩ := hmem
    have hsupp : ∀ i ∈ (Sym.wordExponent w).support, i < m := fun i hi => by
      obtain ⟨k, rfl⟩ := (Sym.mem_support_wordExponent w i).1 hi
      exact (Sym.mem_boundedWords.1 hw).2 k
    rw [Sym.coeff_letterTrunc_of_support hsupp,
      coeff_wordExponent_gessel K hS (Sym.mem_boundedWords.1 hw).1,
      Finset.sum_eq_single w (fun w' hw' hne => ite_eq_right fun hcon => hne ?_)
        fun h => absurd hw h]
    · rw [ite_eq_left rfl]
    · exact Sym.eq_of_wordExponent_eq (Sym.mem_boundedWords.1 hw').1
        (Sym.mem_boundedWords.1 hw).1 hcon.symm
  · rw [Finset.sum_eq_zero fun w hw => ite_eq_right fun hcon => hmem ⟨w, hw, hcon.symm⟩]
    by_cases hsupp : ∀ i ∈ d.support, i < m
    · rw [Sym.coeff_letterTrunc_of_support hsupp]
      refine coeff_gessel_eq_zero_of_forall_ne K fun w hw hdw => hmem ⟨w, ?_, hdw.symm⟩
      refine Sym.mem_boundedWords.2 ⟨hw, fun k => hsupp _ ?_⟩
      rw [hdw]
      exact (Sym.mem_support_wordExponent w (w k)).2 ⟨k, rfl⟩
    · rw [Sym.coeff_letterTrunc_of_not_support hsupp]

end HJO.ParkingFunctions
