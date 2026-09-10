/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import QSeriesLib.NumberTheory.QTheory.Basic
public import HJO.Evaluation.AExponential
public import HJO.Determinant.DetSolves
public import HJO.Series.GapPoset

/-! # The conditional links of the final chain

Every statement in this file is conditional: the inputs it does not prove are carried as explicit
hypotheses, and nothing here is complete on its own.

The chain runs from the exponential forms of the two generating series, through the `q`-difference
equation the generating series of the finite polynomials satisfies, to its coefficientwise form ---
the scalar recurrence --- and the finite identity `F_N(q) = (q)_N C_{𝐜,≤N}(q)`.

The supporting material is the weighted homogeneity of the divided alphabet and of the iterated
return seed, the characterisation of a power series by its logarithmic derivative, the
invertibility of the `q`-Pochhammer symbol in the field of `q`-Laurent series, the value `1` of the
finite polynomial at rank zero, and the splitting of the `q`-Pochhammer symbol that clears the
denominators in the recurrence.
-/

@[expose] public section

open Finset NumericalSemigroup
open scoped PowerSeries QTheory

namespace HJO.Endgame

/-! ### Rescaling the generators one by one preserves the weighted grading -/

open MvPolynomial in
/-- An algebra endomorphism rescaling each generator separately multiplies a monomial by the
matching product of the scalars. -/
lemma aeval_scale_monomial {K : Type*} [CommRing K] (c : ℕ → K) (d : ℕ →₀ ℕ) (a : K) :
    aeval (fun i => C (c i) * X i) (monomial d a : Sym.Lambda K)
      = monomial d (a * ∏ i ∈ d.support, c i ^ d i) := by
  rw [aeval_monomial, algebraMap_eq, monomial_eq, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, ← C_pow, prod_mul_distrib, ← map_prod, C_mul, mul_assoc]

open MvPolynomial in
/-- Dividing the alphabet by `1 - q` multiplies each monomial coefficient by the matching
product of inverse powers of `1 - q^j`, introducing no new monomials. If all these denominators
are nonzero, support is preserved; otherwise totalized inversion can remove monomials. -/
lemma coeff_plethDiv {L : Type*} [Field L] [Algebra ℚ L] (q : L) (d : ℕ →₀ ℕ)
    (f : Sym.Lambda L) :
    coeff d (CopPower.plethDiv q f)
      = (∏ i ∈ d.support, ((1 - q ^ (i + 1))⁻¹) ^ d i) * coeff d f := by
  classical
  refine MvPolynomial.induction_on' f ?_ ?_
  · intro e a
    rw [CopPower.plethDiv, aeval_scale_monomial, coeff_monomial, coeff_monomial]
    by_cases h : e = d
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl, mul_comm]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  · intro p r hp hr
    rw [map_add, coeff_add, coeff_add, hp, hr, mul_add]

/-- Dividing the alphabet by `1 - q` preserves weighted homogeneity. -/
lemma isWeightedHomogeneous_plethDiv {L : Type*} [Field L] [Algebra ℚ L] (q : L)
    {f : Sym.Lambda L} {n : ℕ}
    (hf : MvPolynomial.IsWeightedHomogeneous Multiplication.degWeight f n) :
    MvPolynomial.IsWeightedHomogeneous Multiplication.degWeight (CopPower.plethDiv q f) n := by
  intro d hd
  rw [coeff_plethDiv] at hd
  exact hf (right_ne_zero_of_mul hd)

/-- The iterated return seed is weighted homogeneous of degree `N`, the generator `p_k` weighing
`k`. -/
lemma isWeightedHomogeneous_cop_one_pow {L : Type*} [Field L] [Algebra ℚ L] (q : L) (hq0 : q ≠ 0)
    (hq : ∀ k : ℕ, q ^ (k + 1) ≠ 1) (N : ℕ) :
    MvPolynomial.IsWeightedHomogeneous Multiplication.degWeight ((Sym.Cop q 1 ^ N) 1) N := by
  rw [CopPower.cop_one_pow_apply_one q hq0 hq N]
  exact (isWeightedHomogeneous_plethDiv q
    (Multiplication.isWeightedHomogeneous_completeHomog L N)).C_mul _

/-! ### Power series pinned down by a logarithmic derivative -/

section ExpLog

variable {F : Type*} [CommRing F] [Algebra ℚ F]

/-- The series `∑_{k ≥ 1} c_k z^k / k`, to be exponentiated. Its constant coefficient vanishes
because `(0 : ℚ)⁻¹` does. -/
noncomputable def coeffLog (c : ℕ → F) : PowerSeries F :=
  PowerSeries.mk fun k => algebraMap ℚ F ((k : ℚ)⁻¹) * c k

/-- The series to be exponentiated has zero constant coefficient. -/
@[simp] lemma constantCoeff_coeffLog (c : ℕ → F) :
    PowerSeries.constantCoeff (coeffLog c) = 0 := by
  rw [coeffLog, PowerSeries.constantCoeff_mk]
  simp

/-- The series to be exponentiated is the one whose alternating form the area series uses. -/
lemma coeffLog_eq_logSeries (r : ℕ → F) :
    coeffLog (fun k => (-1) ^ (k - 1) * r k) = AExponential.logSeries r := rfl

/-- Its derivative is the shifted generating series of the coefficients. -/
lemma derivative_coeffLog (c : ℕ → F) :
    PowerSeries.derivative F (coeffLog c) = PowerSeries.mk fun k => c (k + 1) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_derivative, coeffLog, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hcast : (((n + 1 : ℕ) : ℚ))⁻¹ = ((n : ℚ) + 1)⁻¹ := by push_cast; ring
  have hkey : algebraMap ℚ F ((n : ℚ) + 1)⁻¹ * ((n : F) + 1) = 1 := by
    rw [show ((n : F) + 1) = algebraMap ℚ F ((n : ℚ) + 1) by
      rw [map_add, map_natCast, map_one], ← map_mul, inv_mul_cancel₀ hn, map_one]
  rw [hcast]
  linear_combination (c (n + 1)) * hkey

/-- A power series with constant coefficient `1` whose logarithmic derivative is the shifted
generating series of the `c_k` is the formal exponential of `∑_{k ≥ 1} c_k z^k / k`. -/
theorem eq_formalExp_coeffLog {c : ℕ → F} {G : PowerSeries F}
    (hd : PowerSeries.derivative F G = (PowerSeries.mk fun k => c (k + 1)) * G)
    (h0 : PowerSeries.coeff 0 G = 1) : G = AExponential.formalExp (coeffLog c) :=
  AExponential.eq_formalExp_of_logDeriv (constantCoeff_coeffLog c)
    (by rw [derivative_coeffLog]; exact hd) h0

/-- The formal exponential of `∑_{k ≥ 1} c_k z^k / k` has constant coefficient `1`. -/
lemma coeff_zero_formalExp_coeffLog (c : ℕ → F) :
    PowerSeries.coeff 0 (AExponential.formalExp (coeffLog c)) = 1 :=
  AExponential.coeff_zero_formalExp (constantCoeff_coeffLog c)

/-- The formal exponential of `∑_{k ≥ 1} c_k z^k / k` has the shifted generating series of the
`c_k` as its logarithmic derivative. -/
lemma derivative_formalExp_coeffLog (c : ℕ → F) :
    PowerSeries.derivative F (AExponential.formalExp (coeffLog c))
      = (PowerSeries.mk fun k => c (k + 1)) * AExponential.formalExp (coeffLog c) := by
  rw [AExponential.derivative_formalExp (constantCoeff_coeffLog c), derivative_coeffLog]

end ExpLog

/-! ### The coefficient field -/

/-- The inclusion of integral `q`-power series into the field of `q`-Laurent series is
injective. -/
lemma qOfInt_injective : Function.Injective Determinant.qOfInt := by
  intro x y h
  rw [Determinant.qOfInt, RingHom.coe_comp, Function.comp_apply, Function.comp_apply] at h
  exact PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
    (HahnSeries.ofPowerSeries_injective h)

/-- The `q`-Pochhammer symbol is invertible in the field of `q`-Laurent series: each of its
factors is. -/
lemma qOfInt_qPochhammer_ne_zero (N : ℕ) :
    Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_N ≠ 0 := by
  rw [map_qPochhammer]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  have h : Determinant.qOfInt PowerSeries.X * Determinant.qOfInt PowerSeries.X ^ i
      = Determinant.qVar ^ (i + 1) := by
    rw [Determinant.qVar, pow_succ']
  rw [h, sub_ne_zero]
  exact fun hc => Uniqueness.qVar_pow_sub_one_ne_zero (Nat.succ_ne_zero i) (by rw [← hc, sub_self])

/-! ### The finite polynomial at rank zero -/

/-- The zero gap vector lies in the monotonicity cone. -/
lemma zero_mem_cone (a b : ℕ) : (0 : (finspan {a, b}).gaps → ℤ) ∈ HJO.cone a b :=
  ⟨fun _ => le_rfl, fun _ _ => le_rfl, fun _ _ => le_rfl⟩

/-- At rank zero the index set of the finite polynomial is the single zero gap vector: the
Frobenius gap is the largest gap, so a nonnegative monotone vector vanishing there vanishes
everywhere. -/
lemma sep_cone_frobeniusGap_le_zero (a b : ℕ) (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) :
    {n ∈ HJO.cone a b | HJO.extend n (Gaps.frobeniusGap a b) ≤ ((0 : ℕ) : ℤ)}
      = {(0 : (finspan {a, b}).gaps → ℤ)} := by
  obtain ⟨hfmem, hfmax⟩ := GapPoset.frobeniusGap_max a b hco ha hab
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Nat.cast_zero]
  refine ⟨fun ⟨hn, hf⟩ => ?_, fun h => ?_⟩
  · rw [GapPoset.extend_of_mem n hfmem] at hf
    rw [Gaps.cone_eq a b hco] at hn
    funext g
    exact le_antisymm ((hn.2 g ⟨_, hfmem⟩ (hfmax (g : ℕ) g.2)).trans hf) (hn.1 g)
  · subst h
    exact ⟨zero_mem_cone a b, by simp [HJO.extend]⟩

/-- The generalised Gaussian multinomial at rank zero and the zero gap vector is `1`. -/
lemma multinomial_zero_zero (a b : ℕ) :
    Gaps.multinomial a b 0 (0 : (finspan {a, b}).gaps → ℤ) = 1 := by
  have hinv : PowerSeries.invOfUnit (1 : PowerSeries ℤ) 1 = 1 := by
    have h := PowerSeries.mul_invOfUnit (1 : PowerSeries ℤ) 1 (by simp)
    rwa [one_mul] at h
  rw [Gaps.multinomial]
  simp [HJO.extend, HJO.extendedSelfQPochhammer, HJO.extendedSelfQPochhammerInv, HJO.multiplicand,
    hinv]

/-- The finite polynomial at rank zero is `1`. -/
lemma finiteSeries_zero (a b : ℕ) (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) :
    Gaps.finiteSeries a b 0 = 1 := by
  rw [Gaps.finiteSeries, sep_cone_frobeniusGap_le_zero a b hco ha hab, finsum_mem_singleton,
    multinomial_zero_zero, map_zero, Int.toNat_zero, pow_zero, one_mul]

/-! ### The rank shift and the nonvanishing of `q` -/

section HExponential

variable {a b : ℕ} {L : Type*} [Field L] [Algebra ℚ L]

/-- The rank shift exceeds the block hook shift by `C(N, 2)`. -/
lemma gammaShift_eq (a b N : ℕ) (hd : 0 < a + b) :
    Paths.gammaShift a b N = N.choose 2 + Paths.kappaShift a b N := by
  have hle : N.choose 2 ≤ (a + b) * N.choose 2 := Nat.le_mul_of_pos_left _ hd
  rw [Paths.gammaShift, Paths.kappaShift, Nat.sub_mul, one_mul]
  omega

/-- The variable `q` is nonzero in the field of `q`-Laurent series. -/
lemma qVar_ne_zero : (Determinant.qVar : LaurentSeries ℚ) ≠ 0 := by
  intro h
  have hX : (PowerSeries.X : PowerSeries ℤ) = 0 := by
    refine qOfInt_injective ?_
    rw [← Determinant.qVar, h, map_zero]
  simpa using congrArg (PowerSeries.coeff 1) hX

end HExponential

/-! ### The HJO series solves the common equation -/

/-- For every `k ≥ 1` the element `1 - q^k` of the field of `q`-Laurent series is nonzero. -/
lemma one_sub_qVar_pow_ne_zero (k : ℕ) :
    (1 : LaurentSeries ℚ) - Determinant.qVar ^ (k + 1) ≠ 0 := fun h =>
  Uniqueness.qVar_pow_sub_one_ne_zero (show k + 1 ≠ 0 by omega) (by linear_combination -h)

/-- `ℋ(z;q)` satisfies the common equation, given the exponential forms of the two generating
series in the same coefficients `r_k` as hypotheses. Subtracting the logarithm of the first from
its value at `qz` telescopes to the logarithm of `𝒜(-z;q)`, and the normalisation is the constant
coefficient of the exponential. -/
theorem isCommonSolution_genH {a b : ℕ} (r : ℕ → LaurentSeries ℚ)
    (hH : Determinant.genH a b
      = AExponential.formalExp (coeffLog fun k => r k / (1 - Determinant.qVar ^ k)))
    (hA : Determinant.genA a b = AExponential.formalExp (AExponential.logSeries r)) :
    Determinant.IsCommonSolution a b (Determinant.genH a b) := by
  have hcH : PowerSeries.derivative (LaurentSeries ℚ) (Determinant.genH a b)
      = (PowerSeries.mk fun k => r (k + 1) / (1 - Determinant.qVar ^ (k + 1)))
        * Determinant.genH a b := by
    rw [hH]
    exact derivative_formalExp_coeffLog _
  have hcA : PowerSeries.derivative (LaurentSeries ℚ) (Determinant.genA a b)
      = (PowerSeries.mk fun k => (-1) ^ k * r (k + 1)) * Determinant.genA a b := by
    rw [hA, AExponential.derivative_formalExp (AExponential.constantCoeff_logSeries r),
      AExponential.derivative_logSeries]
  have h0H : PowerSeries.coeff 0 (Determinant.genH a b) = 1 := by
    rw [hH]
    exact coeff_zero_formalExp_coeffLog _
  have h0A : PowerSeries.coeff 0 (Determinant.genA a b) = 1 := by
    rw [hA]
    exact AExponential.coeff_zero_formalExp (AExponential.constantCoeff_logSeries r)
  have hA' : PowerSeries.derivative (LaurentSeries ℚ)
        (PowerSeries.rescale (-1) (Determinant.genA a b))
      = (PowerSeries.C (-1 : LaurentSeries ℚ) *
          PowerSeries.rescale (-1) (PowerSeries.mk fun k => (-1) ^ k * r (k + 1)))
        * PowerSeries.rescale (-1) (Determinant.genA a b) := by
    rw [CopPower.derivative_rescale, hcA, map_mul]
    ring
  refine ⟨CopPower.powerSeries_ext_of_logDeriv
    (Q := PowerSeries.C Determinant.qVar * PowerSeries.rescale Determinant.qVar
      (PowerSeries.mk fun k => r (k + 1) / (1 - Determinant.qVar ^ (k + 1)))) ?_ ?_ ?_, ?_⟩
  · rw [CopPower.derivative_rescale, hcH, map_mul]
    ring
  · rw [CopPower.derivative_mul_of_logDeriv hA' hcH]
    congr 1
    refine PowerSeries.ext fun k => ?_
    rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
      PowerSeries.coeff_mk]
    have hsq : ((-1 : LaurentSeries ℚ)) ^ k * ((-1) ^ k * r (k + 1)) = r (k + 1) := by
      rw [← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, by ring⟩, one_mul]
    rw [hsq]
    have ht := one_sub_qVar_pow_ne_zero k
    field_simp
    ring
  · rw [PowerSeries.coeff_rescale, pow_zero, one_mul, h0H,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
      one_mul, h0A, h0H, one_mul]
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, h0H]

/-! ### Splitting the `q`-Pochhammer symbol -/

/-- The `q`-Pochhammer symbol as a product over an interval of exponents. -/
lemma qPochhammer_self_eq_prod_Ico (M : ℕ) :
    ((PowerSeries.X; PowerSeries.X)_M : PowerSeries ℤ)
      = ∏ j ∈ Ico 1 (M + 1), (1 - PowerSeries.X ^ j) := by
  rw [qPochhammer, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  exact Finset.prod_congr rfl fun i _ => by rw [add_comm 1 i, pow_succ']

/-- Peeling the last factor off the `q`-Pochhammer symbol at a positive index. -/
lemma qPochhammer_self_succ {N : ℕ} (hN : 0 < N) :
    ((PowerSeries.X; PowerSeries.X)_(N - 1) : PowerSeries ℤ) * (1 - PowerSeries.X ^ N)
      = (PowerSeries.X; PowerSeries.X)_N := by
  have h1 : N - 1 + 1 = N := by omega
  have h2 : (PowerSeries.X : PowerSeries ℤ) * PowerSeries.X ^ (N - 1) = PowerSeries.X ^ N := by
    rw [← pow_succ', h1]
  rw [← h2, ← qPochhammer_succ', h1]

/-- The `q`-Pochhammer quotient `(q)_{N-1} / (q)_{N-k}` as a finite product. -/
lemma qPochhammer_self_split {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    ((PowerSeries.X; PowerSeries.X)_(N - k) : PowerSeries ℤ) *
        ∏ j ∈ Ico (N - k + 1) N, (1 - PowerSeries.X ^ j)
      = (PowerSeries.X; PowerSeries.X)_(N - 1) := by
  rw [qPochhammer_self_eq_prod_Ico, qPochhammer_self_eq_prod_Ico,
    show N - 1 + 1 = N from by omega,
    Finset.prod_Ico_consecutive _ (show 1 ≤ N - k + 1 by omega) (show N - k + 1 ≤ N by omega)]

/-- Peeling the bottom term off a sum over an initial segment. -/
lemma sum_range_succ_eq_add_sum_Icc {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ∑ k ∈ range (N + 1), f k = f 0 + ∑ k ∈ Icc 1 N, f k := by
  have hIco : Ico 1 (N + 1) = Icc 1 N := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (show 0 < N + 1 by omega), Nat.zero_add,
    hIco]

/-! ### The scalar recurrence -/

/-- The scalar recurrence, given that `ℋ` satisfies the common equation: extracting `[z^N]` from
the equation and using `(q)_N / (1 - q^N) = (q)_{N-1}` clears the denominators, the quotient
`(q)_{N-1} / (q)_{N-k}` becoming the displayed finite product. -/
theorem finiteSeries_recurrence {a b : ℕ}
    (hjo : Determinant.IsCommonSolution a b (Determinant.genH a b)) (N : ℕ) (hN : 0 < N) :
    (PowerSeries.X : PowerSeries ℤ) ^ Paths.gammaShift a b N * Gaps.finiteSeries a b N
      = ∑ k ∈ Icc 1 N, (-1 : PowerSeries ℤ) ^ (k + 1) * Paths.areaPoly a b k *
          PowerSeries.X ^ Paths.gammaShift a b (N - k) * Gaps.finiteSeries a b (N - k) *
          ∏ j ∈ Ico (N - k + 1) N, (1 - PowerSeries.X ^ j) := by
  have hDne : ∀ M : ℕ, Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_M ≠ 0 :=
    qOfInt_qPochhammer_ne_zero
  have ht : (1 : LaurentSeries ℚ) - Determinant.qVar ^ N ≠ 0 := by
    have h := one_sub_qVar_pow_ne_zero (N - 1)
    rwa [show N - 1 + 1 = N from by omega] at h
  have hgA : ∀ k : ℕ, PowerSeries.coeff k (PowerSeries.rescale (-1) (Determinant.genA a b))
      = (-1) ^ k * Determinant.qOfInt (Paths.areaPoly a b k) := fun k => by
    rw [PowerSeries.coeff_rescale, Determinant.genA, PowerSeries.coeff_mk]
  have hgH : ∀ M : ℕ, PowerSeries.coeff M (Determinant.genH a b)
      = Determinant.qOfInt (PowerSeries.X ^ Paths.gammaShift a b M * Gaps.finiteSeries a b M) /
        Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_M := fun M => by
    rw [Determinant.genH, PowerSeries.coeff_mk]
  have hcoeff := congrArg (PowerSeries.coeff N) hjo.1
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ_eq_add_sum_Icc] at hcoeff
  simp only [hgA, hgH, Nat.sub_zero, pow_zero, AExponential.areaPoly_zero, map_one,
    one_mul] at hcoeff
  have hS : (Determinant.qVar ^ N - 1) *
        (Determinant.qOfInt (PowerSeries.X ^ Paths.gammaShift a b N * Gaps.finiteSeries a b N) /
          Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_N)
      = ∑ k ∈ Icc 1 N, (-1) ^ k * Determinant.qOfInt (Paths.areaPoly a b k) *
          (Determinant.qOfInt (PowerSeries.X ^ Paths.gammaShift a b (N - k) *
              Gaps.finiteSeries a b (N - k)) /
            Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_(N - k)) := by
    linear_combination hcoeff
  have hDN : Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_N
      = Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_(N - 1) *
        (1 - Determinant.qVar ^ N) := by
    rw [← qPochhammer_self_succ hN, map_mul, map_sub, map_one, map_pow, ← Determinant.qVar]
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
      rw [← map_mul, qPochhammer_self_split hk.1 hk.2]
    have hne := hDne (N - k)
    rw [hsplit]
    simp only [map_mul, map_pow, map_neg, map_one]
    field_simp
    ring
  refine qOfInt_injective ?_
  rw [map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hS, hDN]
  have hD1 := hDne (N - 1)
  field_simp
  ring

/-! ### The finite identity -/

/-- `F_N(q) = (q)_N C_{𝐜,≤N}(q)`, given that `ℋ` satisfies the common equation and the
determinant coefficient count. The determinant series satisfies the same equation outright, so
uniqueness of the normalised solution identifies the two, and the rank shift cancels. -/
theorem finiteSeries_eq_qPochhammer_mul_boundedGF {a b : ℕ} (hco : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) (hjo : Determinant.IsCommonSolution a b (Determinant.genH a b))
    (hdet : ∀ N : ℕ, PowerSeries.coeff N
          (PowerSeries.rescale (-1) (Determinant.detSeries a b))
        = Determinant.qOfInt (PowerSeries.X ^ Paths.gammaShift a b N *
            HJO.Cylindric.boundedGF a b N))
    (N : ℕ) :
    Gaps.finiteSeries a b N
      = (PowerSeries.X; PowerSeries.X)_N * HJO.Cylindric.boundedGF a b N := by
  have hD : Determinant.qOfInt (PowerSeries.X; PowerSeries.X)_N ≠ 0 :=
    qOfInt_qPochhammer_ne_zero N
  have hqg : (Determinant.qVar : LaurentSeries ℚ) ^ Paths.gammaShift a b N ≠ 0 :=
    pow_ne_zero _ qVar_ne_zero
  have hc := congrArg (PowerSeries.coeff N)
    (Uniqueness.eq_of_isCommonSolution hjo
      (DetSolves.isCommonSolution_rescale_neg_one_detSeries a b hco ha hb))
  rw [Determinant.genH, PowerSeries.coeff_mk, hdet N, div_eq_iff hD, map_mul, map_mul, map_pow,
    ← Determinant.qVar] at hc
  refine qOfInt_injective ?_
  rw [map_mul]
  refine mul_left_cancel₀ hqg ?_
  rw [hc]
  ring

end HJO.Endgame
