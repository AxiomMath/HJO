/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import HJO.SignExtraction.Defs
public meta import HJO.Attr

/-! # Evaluation at `m` letters

The evaluation `E_m` of `HJO.Sym.letterEval` is shown here to be a `K`-algebra homomorphism, and
its values are computed on the objects the sign-extraction route feeds it: a realised power sum
goes to `m y^k`, so a realised symmetric function homogeneous of degree `n` goes to
`ν_f(m) y^n`, where `ν_f` is the letter-count polynomial of `HJO.Sym.letterCount`. The companion
value of `ν_f` at `-1` is the sign extraction up to the sign `(-1)^n`, which is what makes the
substitution `t = -1` read sign extraction off the letter-count polynomial.

Homogeneity is used exactly once, and only in the form of the weighted degree of the power-sum
monomials: it makes the power of `y` the same for every monomial of `f`, so that the image is a
scalar multiple of a single power of `y` and its coefficient can be read.
-/

@[expose] public section

open Finset

namespace HJO.Sym

variable {K : Type*} [CommRing K]

/-! ### The evaluation at `m` letters is an algebra homomorphism -/

/-- The evaluation at `m` letters is additive: it is a sum of coefficients, and coefficients are
additive. -/
theorem letterEval_add (m : ℕ) (G H : AlphabetSeries K) :
    letterEval m (G + H) = letterEval m G + letterEval m H := by
  ext N
  rw [coeff_letterEval, map_add, coeff_letterEval, coeff_letterEval, ← sum_add_distrib]
  exact sum_congr rfl fun d _ => map_add (MvPowerSeries.coeff d) G H

/-- The evaluation at `m` letters sends `0` to `0`. -/
theorem letterEval_zero (m : ℕ) : letterEval m (0 : AlphabetSeries K) = 0 := by
  ext N
  rw [coeff_letterEval, map_zero]
  exact sum_eq_zero fun d _ => map_zero (MvPowerSeries.coeff d)

/-- The evaluation at `m` letters commutes with scalars. -/
theorem letterEval_smul (m : ℕ) (r : K) (G : AlphabetSeries K) :
    letterEval m (r • G) = r • letterEval m G := by
  ext N
  rw [coeff_letterEval, PowerSeries.coeff_smul, coeff_letterEval, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun d _ => MvPowerSeries.coeff_smul G d r

/-- The evaluation at `m` letters sends `1` to `1`: the only exponent vector of total degree `0` is
`0`, and it is the only one whose coefficient in `1` is nonzero. -/
theorem letterEval_one (m : ℕ) : letterEval m (1 : AlphabetSeries K) = 1 := by
  classical
  ext N
  rw [coeff_letterEval, PowerSeries.coeff_one]
  split_ifs with hN
  · subst hN
    rw [Finset.finsuppAntidiag_zero, sum_singleton]
    simp
  · refine sum_eq_zero fun d hd => ?_
    have hne : d ≠ 0 := by
      rintro rfl
      rw [mem_finsuppAntidiag'] at hd
      simp only [Finsupp.sum_zero_index] at hd
      exact hN hd.1.symm
    simp [MvPowerSeries.coeff_one, hne]

/-- The evaluation at `m` letters is multiplicative: the Cauchy formula for the coefficients of a
product in the alphabet matches the Cauchy formula in `y`, because an exponent vector supported in
the first `m` letters splits only into vectors supported there, and total degrees add. -/
theorem letterEval_mul (m : ℕ) (G H : AlphabetSeries K) :
    letterEval m (G * H) = letterEval m G * letterEval m H := by
  classical
  ext N
  rw [coeff_letterEval, PowerSeries.coeff_mul]
  have hL : ∀ d ∈ (range m).finsuppAntidiag N, MvPowerSeries.coeff d (G * H)
      = ∑ p ∈ HasAntidiagonal.antidiagonal d,
          MvPowerSeries.coeff p.1 G * MvPowerSeries.coeff p.2 H :=
    fun d _ => MvPowerSeries.coeff_mul d G H
  have hR : ∀ p ∈ HasAntidiagonal.antidiagonal N,
      PowerSeries.coeff p.1 (letterEval m G) * PowerSeries.coeff p.2 (letterEval m H)
        = ∑ q ∈ ((range m).finsuppAntidiag p.1) ×ˢ ((range m).finsuppAntidiag p.2),
            MvPowerSeries.coeff q.1 G * MvPowerSeries.coeff q.2 H := by
    intro p _
    rw [coeff_letterEval, coeff_letterEval, sum_mul_sum, ← sum_product']
  rw [sum_congr rfl hL, sum_congr rfl hR, sum_sigma', sum_sigma']
  refine sum_nbij' (fun x => ⟨((range m).sum x.2.1, (range m).sum x.2.2), x.2⟩)
    (fun y => ⟨y.2.1 + y.2.2, y.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_sigma, mem_finsuppAntidiag, HasAntidiagonal.mem_antidiagonal] at hx
    obtain ⟨⟨hsum, hsupp⟩, hp⟩ := hx
    have hsupp1 : x.2.1.support ⊆ range m := fun i hi => hsupp (by
      rw [Finsupp.mem_support_iff, ← hp]
      have := Finsupp.mem_support_iff.mp hi
      simp only [Finsupp.add_apply]
      omega)
    have hsupp2 : x.2.2.support ⊆ range m := fun i hi => hsupp (by
      rw [Finsupp.mem_support_iff, ← hp]
      have := Finsupp.mem_support_iff.mp hi
      simp only [Finsupp.add_apply]
      omega)
    have hadd : (range m).sum x.2.1 + (range m).sum x.2.2 = N := by
      rw [← hsum, ← hp, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => rfl
    simp only [mem_sigma, mem_product]
    exact ⟨HasAntidiagonal.mem_antidiagonal.mpr hadd, mem_finsuppAntidiag.mpr ⟨rfl, hsupp1⟩,
      mem_finsuppAntidiag.mpr ⟨rfl, hsupp2⟩⟩
  · intro y hy
    simp only [mem_sigma, mem_finsuppAntidiag, HasAntidiagonal.mem_antidiagonal, mem_product] at hy
    obtain ⟨hp, ⟨hs1, hsupp1⟩, hs2, hsupp2⟩ := hy
    have hsum : (range m).sum (y.2.1 + y.2.2) = N := by
      rw [← hp, ← hs1, ← hs2, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => rfl
    have hsupp : (y.2.1 + y.2.2).support ⊆ range m := by
      intro i hi
      rw [Finsupp.mem_support_iff] at hi
      simp only [Finsupp.add_apply] at hi
      rcases Nat.eq_zero_or_pos (y.2.1 i) with h1 | h1
      · exact hsupp2 (Finsupp.mem_support_iff.mpr (by omega))
      · exact hsupp1 (Finsupp.mem_support_iff.mpr (by omega))
    simp only [mem_sigma]
    exact ⟨mem_finsuppAntidiag.mpr ⟨hsum, hsupp⟩, HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
  · intro x hx
    simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal] at hx
    simp only [hx.2]
  · intro y hy
    simp only [mem_sigma, mem_product, mem_finsuppAntidiag] at hy
    simp only [hy.2.1.1, hy.2.2.1]
  · exact fun _ _ => rfl

/-- **The evaluation at `m` letters is an algebra homomorphism**: `E_m` as a `K`-algebra
homomorphism from the power series in the alphabet to the power series in `y`. -/
@[hjo "lem_letter_eval_hom"]
noncomputable def letterEvalHom (K : Type*) [CommRing K] (m : ℕ) :
    AlphabetSeries K →ₐ[K] PowerSeries K where
  toFun := letterEval m
  map_one' := letterEval_one m
  map_mul' := letterEval_mul m
  map_zero' := letterEval_zero m
  map_add' := letterEval_add m
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, letterEval_smul,
      letterEval_one]

/-- **The algebra homomorphism `E_m` is the evaluation at `m` letters.** -/
@[hjo "lem_letter_eval_hom", simp]
theorem letterEvalHom_apply (K : Type*) [CommRing K] (m : ℕ) (G : AlphabetSeries K) :
    letterEvalHom K m G = letterEval m G :=
  rfl

/-! ### The values of the evaluation at `m` letters -/

/-- **The letters seen by a power sum**: a realised power sum `p_k` is sent to `m y^k`, the
contributing exponent vectors being the `k`-th multiples of the first `m` unit vectors. -/
@[hjo "lem_letter_eval_power_sum"]
theorem letterEval_powerSum {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι) (m : ℕ)
    {k : ℕ} (hk : 1 ≤ k) :
    letterEval m (ι (powerSum K k)) = PowerSeries.C (m : K) * PowerSeries.X ^ k := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  ext N
  rw [coeff_letterEval, PowerSeries.coeff_C_mul_X_pow]
  have hsingle : ∀ (i : ℕ), (range m).sum (Finsupp.single i (k + 1))
      = if i ∈ range m then k + 1 else 0 := by
    intro i
    rw [sum_congr rfl fun j _ => Finsupp.single_apply (a := i) (a' := j) (b := k + 1),
      Finset.sum_ite_eq]
  have hmemN : ∀ (d : ℕ →₀ ℕ), d ∈ (range m).finsuppAntidiag N →
      ∀ i : ℕ, d = Finsupp.single i (k + 1) → i ∈ range m ∧ N = k + 1 := by
    intro d hd i hdi
    rw [mem_finsuppAntidiag] at hd
    have hi : i ∈ range m := by
      refine hd.2 ?_
      rw [hdi, Finsupp.mem_support_iff, Finsupp.single_eq_same]
      omega
    refine ⟨hi, ?_⟩
    rw [← hd.1, hdi, hsingle i]
    simp only [hi, ite_true]
  rcases eq_or_ne N (k + 1) with rfl | hN
  · simp only [ite_true]
    have himg : (range m).image (fun i => Finsupp.single i (k + 1))
        ⊆ (range m).finsuppAntidiag (k + 1) := by
      intro d hd
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hd
      rw [mem_finsuppAntidiag]
      exact ⟨by rw [hsingle i]; simp only [hi, ite_true],
        (Finsupp.support_single_subset).trans (by simpa using hi)⟩
    rw [← sum_subset himg, sum_image]
    · rw [sum_congr rfl fun i _ => hι.coeff_pow k i, sum_const, card_range, nsmul_eq_mul, mul_one]
    · intro i _ j _ hij
      exact Finsupp.single_left_injective (by omega) hij
    · intro d hd hdnot
      refine hι.coeff_of_ne k d fun i hdi => ?_
      exact hdnot (mem_image.mpr ⟨i, (hmemN d hd i hdi).1, hdi.symm⟩)
  · simp only [hN, ite_false]
    refine sum_eq_zero fun d hd => ?_
    refine hι.coeff_of_ne k d fun i hdi => ?_
    exact hN (hmemN d hd i hdi).2

/-- The weighted degree of a power-sum monomial, written as a sum over the letters occurring in
it: the generator `i` of `Lambda K` stands for `p_{i+1}`, of degree `i + 1`. -/
theorem weight_eq_sum (d : ℕ →₀ ℕ) :
    Finsupp.weight (fun i => i + 1) d = ∑ i ∈ d.support, (i + 1) * d i := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]

/-- The value of an evaluation of `Lambda K` in `K`, expanded over the power-sum monomials. -/
theorem aeval_eq_sum (g : ℕ → K) (f : Lambda K) :
    MvPolynomial.aeval g f
      = ∑ d ∈ f.support, MvPolynomial.coeff d f * ∏ i ∈ d.support, g i ^ d i := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  simp

/-- **The values of the letter-count polynomial**: `ν_f(x)` is the value of `f` at every power sum
equal to `x`, expanded over the power-sum monomials of `f`, a monomial in `r` power sums
contributing `x ^ r`. -/
theorem eval_letterCount (f : Lambda K) (x : K) :
    (letterCount K f).eval x
      = ∑ d ∈ f.support, MvPolynomial.coeff d f * x ^ (∑ i ∈ d.support, d i) := by
  have h1 : (letterCount K f).eval x = MvPolynomial.aeval (fun _ => x) f := by
    rw [← Polynomial.coe_aeval_eq_eval x, letterCount, ← AlgHom.comp_apply,
      MvPolynomial.comp_aeval]
    simp
  rw [h1, aeval_eq_sum]
  exact sum_congr rfl fun d _ => by rw [prod_pow_eq_pow_sum]

/-- The evaluation at `m` letters of a realised power-sum monomial: each of its `r` power sums
contributes a factor `m`, and the powers of `y` add up to the weighted degree of the monomial. -/
theorem letterEval_monomial {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι) (m : ℕ)
    (d : ℕ →₀ ℕ) (c : K) :
    letterEval m (ι (MvPolynomial.monomial d c))
      = PowerSeries.C (c * (m : K) ^ (∑ i ∈ d.support, d i)) *
          PowerSeries.X ^ (∑ i ∈ d.support, (i + 1) * d i) := by
  have hX : ∀ i : ℕ, ((letterEvalHom K m).comp ι) (MvPolynomial.X i)
      = PowerSeries.C (m : K) * PowerSeries.X ^ (i + 1) :=
    fun i => letterEval_powerSum hι m (k := i + 1) (by omega)
  have hC : ((letterEvalHom K m).comp ι) (MvPolynomial.C c) = PowerSeries.C c := by
    rw [MvPolynomial.algHom_C, PowerSeries.algebraMap_eq]
  change ((letterEvalHom K m).comp ι) (MvPolynomial.monomial d c) = _
  rw [MvPolynomial.monomial_eq, map_mul, hC, Finsupp.prod, map_prod,
    prod_congr rfl fun i _ => by rw [map_pow, hX i]]
  rw [prod_congr rfl fun i (_ : i ∈ d.support) => mul_pow (PowerSeries.C (m : K))
      (PowerSeries.X ^ (i + 1)) (d i),
    prod_mul_distrib, prod_pow_eq_pow_sum, ← map_pow,
    prod_congr rfl fun i (_ : i ∈ d.support) => (pow_mul (PowerSeries.X : PowerSeries K) (i + 1)
      (d i)).symm,
    prod_pow_eq_pow_sum, map_mul]
  ring

/-- **The `m`-letter evaluation of a homogeneous function**: a realised symmetric function
homogeneous of degree `n` is sent to `ν_f(m) y^n`. Homogeneity is used only to make the power of
`y` the same for every power-sum monomial of `f`. -/
@[hjo "lem_letter_eval_homog"]
theorem letterEval_realisation {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι)
    (m : ℕ) {n : ℕ} {f : Lambda K}
    (hf : MvPolynomial.IsWeightedHomogeneous (fun i => i + 1) f n) :
    letterEval m (ι f)
      = PowerSeries.C ((letterCount K f).eval (m : K)) * PowerSeries.X ^ n := by
  change ((letterEvalHom K m).comp ι) f = _
  conv_lhs => rw [MvPolynomial.as_sum f]
  rw [map_sum, eval_letterCount, map_sum, sum_mul]
  refine sum_congr rfl fun d hd => ?_
  have hw : ∑ i ∈ d.support, (i + 1) * d i = n := by
    rw [← weight_eq_sum]
    exact hf (MvPolynomial.mem_support_iff.mp hd)
  have h := letterEval_monomial hι m d (MvPolynomial.coeff d f)
  rw [hw] at h
  exact h

/-- **Sign extraction is the letter count at `-1`**: on a symmetric function homogeneous of degree
`n` the sign extraction is `(-1)^n ν_f(-1)`. Homogeneity is what makes the factor `(-1)^n` common
to all the power-sum monomials of `f`. -/
@[hjo "lem_epsilon_letter_count"]
theorem signExtract_eq_eval_letterCount {n : ℕ} {f : Lambda K}
    (hf : MvPolynomial.IsWeightedHomogeneous (fun i => i + 1) f n) :
    signExtract K f = (-1 : K) ^ n * (letterCount K f).eval (-1) := by
  rw [signExtract, aeval_eq_sum, eval_letterCount, mul_sum]
  refine sum_congr rfl fun d hd => ?_
  have hw : ∑ i ∈ d.support, (i + 1) * d i = n := by
    rw [← weight_eq_sum]
    exact hf (MvPolynomial.mem_support_iff.mp hd)
  have hprod : ∏ i ∈ d.support, ((-1 : K) ^ i) ^ d i = (-1) ^ (∑ i ∈ d.support, i * d i) := by
    rw [prod_congr rfl fun i (_ : i ∈ d.support) => (pow_mul (-1 : K) i (d i)).symm,
      prod_pow_eq_pow_sum]
  have hsplit : n = (∑ i ∈ d.support, i * d i) + ∑ i ∈ d.support, d i := by
    rw [← hw, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  have hB : ((-1 : K) ^ ∑ i ∈ d.support, d i) * ((-1 : K) ^ ∑ i ∈ d.support, d i) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [hprod, hsplit, pow_add]
  calc MvPolynomial.coeff d f * (-1 : K) ^ ∑ i ∈ d.support, i * d i
      = MvPolynomial.coeff d f * (-1 : K) ^ (∑ i ∈ d.support, i * d i) *
          (((-1 : K) ^ ∑ i ∈ d.support, d i) * ((-1 : K) ^ ∑ i ∈ d.support, d i)) := by
        rw [hB, mul_one]
    _ = (-1 : K) ^ (∑ i ∈ d.support, i * d i) * (-1 : K) ^ (∑ i ∈ d.support, d i) *
          (MvPolynomial.coeff d f * (-1 : K) ^ ∑ i ∈ d.support, d i) := by ring

end HJO.Sym
