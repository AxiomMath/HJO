/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.CopPower
public import HJO.Symmetric.AxisFree
public meta import HJO.Attr

/-! # Complete homogeneous functions of a sum of alphabets, and the axis generators

The analytic input of the diagonal chain is a single principle: the generating series of the
complete homogeneous functions is multiplicative under adding alphabets. Over a `ℚ`-algebra a
power series is pinned down by its constant term and its logarithmic derivative, and Newton's
identity says the logarithmic derivative of `∑ₙ φ(hₙ) tⁿ` is `∑ₖ φ(p_{k+1}) tᵏ`; so a
homomorphism whose values on the power sums are a sum of two others has `h`-series the product of
the two `h`-series. That is `completeHomog_of_add`, and everything below is an evaluation of it at
an explicit alphabet: one letter, one negated letter, a negated dilation, a dilation, and the
four-letter alphabet `(1 - x)(1 - y) ζ` whose `h`-values are the coefficients of both plethystic
displacements.

Two consequences are recorded for the diagonal chain. The alternating convolution
`∑ₛ (-1)ˢ h_{n-s} eₛ` vanishes for `n ≥ 1`, because it is the value of `hₙ` under the empty
alphabet; and its dilated form `∑ₛ (-1)ˢ vˢ h_{k-s} eₛ` is the axis generator `U_k` up to the
scalar `(v - 1) v^{k-1}`, which is how the commutator of the two families of basic operators turns
into multiplication by `U_k`.

Over a general field the dilated statements carry the two conditions that come for free when
working in `ℚ(q, u)`: `v = q u` is nonzero, so that the axis substitution's inverse powers
are what they say, and `v ≠ 1`, so that dividing by `v - 1` is legitimate. At `v = 1` the closed
form is genuinely false -- `plethAxis 1` is the map sending every `p_j` to `0`, so every `U_k`
vanishes while the convolution does not.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### Newton's identity for the elementary functions -/

section Newton

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- Newton's identity for the elementary symmetric functions, cleared of its denominator. -/
theorem natCast_mul_elemSymm (n : ℕ) :
    ((n : Lambda K) + 1) * elemSymm K (n + 1)
      = ∑ k ∈ range (n + 1), (-1) ^ k * powerSum K (k + 1) * elemSymm K (n - k) := by
  rw [elemSymm]
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have e : ((n : Lambda K) + 1) = MvPolynomial.C ((n : K) + 1) := by
    rw [map_add, MvPolynomial.C_1, map_natCast]
  have key : ((n : K) + 1) * algebraMap ℚ K ((n : ℚ) + 1)⁻¹ = 1 := by
    rw [show ((n : K) + 1) = algebraMap ℚ K ((n : ℚ) + 1) by
      rw [map_add, map_natCast, map_one], ← map_mul, mul_inv_cancel₀ hn, map_one]
  rw [e, ← mul_assoc, ← MvPolynomial.C_mul, key, MvPolynomial.C_1, one_mul]

/-- The zeroth elementary symmetric function is one. -/
theorem elemSymm_zero (K : Type*) [CommRing K] [Algebra ℚ K] : elemSymm K 0 = 1 := by
  rw [elemSymm]

/-- **The first elementary symmetric function is the first power sum**: `e₁ = p₁`. -/
@[hjo "lem_e1_eq_p1"]
theorem elemSymm_one (K : Type*) [CommRing K] [Algebra ℚ K] :
    elemSymm K 1 = powerSum K 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, elemSymm]
  simp [elemSymm_zero]

end Newton

/-! ### The complete homogeneous functions of a sum of alphabets -/

section Add

variable {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R] [Algebra ℚ R]

/-- **The complete homogeneous functions of a sum of alphabets.** If three homomorphisms out of
`Λ` satisfy `χ(p_j) = φ(p_j) + ψ(p_j)` for every `j ≥ 1`, then
`χ(hₙ) = ∑_{s ≤ n} φ(h_{n-s}) ψ(hₛ)`.

This is the statement of `HJO.Sym.completeHomog_add_alphabet`, proved here a second time; the
duplication is recorded rather than left silent. The proof is the generating-series
one: both sides have constant term `1` and logarithmic derivative `∑ₖ χ(p_{k+1}) tᵏ`. -/
theorem completeHomog_of_add {F G H : Type*}
    [FunLike F (Lambda K) R] [RingHomClass F (Lambda K) R]
    [FunLike G (Lambda K) R] [RingHomClass G (Lambda K) R]
    [FunLike H (Lambda K) R] [RingHomClass H (Lambda K) R]
    (φ : F) (ψ : G) (χ : H)
    (h : ∀ i : ℕ, χ (MvPolynomial.X i) = φ (MvPolynomial.X i) + ψ (MvPolynomial.X i)) (n : ℕ) :
    χ (completeHomog K n)
      = ∑ s ∈ range (n + 1), φ (completeHomog K (n - s)) * ψ (completeHomog K s) := by
  have hP : (PowerSeries.mk fun k => φ (powerSum K (k + 1)))
      + (PowerSeries.mk fun k => ψ (powerSum K (k + 1)))
      = PowerSeries.mk fun k => χ (powerSum K (k + 1)) := by
    refine PowerSeries.ext fun k => ?_
    simp only [map_add, PowerSeries.coeff_mk]
    rw [CopPower.powerSum_succ, h k]
  have hG := CopPower.derivative_mul_of_logDeriv
    (CopPower.derivative_mk_completeHomog (K := K) φ)
    (CopPower.derivative_mk_completeHomog (K := K) ψ)
  rw [hP] at hG
  have key : (PowerSeries.mk fun n => χ (completeHomog K n))
      = (PowerSeries.mk fun n => φ (completeHomog K n))
        * PowerSeries.mk fun n => ψ (completeHomog K n) :=
    CopPower.powerSeries_ext_of_logDeriv (CopPower.derivative_mk_completeHomog χ) hG
      (by simp [CopPower.completeHomog_zero])
  have hc := congrArg (PowerSeries.coeff n) key
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simp only [PowerSeries.coeff_mk] at hc
  rw [hc, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsn : s ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  rw [show n + 1 - 1 - s = n - s from rfl, show n - (n - s) = s by omega]

/-- **A one-letter alphabet.** If `φ(p_j) = aʲ` for every `j ≥ 1` then `φ(hₙ) = aⁿ`. -/
theorem completeHomog_single {F : Type*} [FunLike F (Lambda K) R] [RingHomClass F (Lambda K) R]
    (φ : F) (a : R) (h : ∀ i : ℕ, φ (MvPolynomial.X i) = a ^ (i + 1)) (n : ℕ) :
    φ (completeHomog K n) = a ^ n := by
  have hP : (PowerSeries.mk fun k => φ (powerSum K (k + 1)))
      = PowerSeries.mk fun k => a ^ (k + 1) := by
    refine PowerSeries.ext fun k => ?_
    simp only [PowerSeries.coeff_mk]
    rw [CopPower.powerSum_succ, h k]
  have hF := CopPower.derivative_mk_completeHomog (K := K) φ
  rw [hP] at hF
  have key : (PowerSeries.mk fun n => φ (completeHomog K n))
      = PowerSeries.mk fun n => a ^ n :=
    CopPower.powerSeries_ext_of_logDeriv hF (CopPower.derivative_geometric a)
      (by simp [CopPower.completeHomog_zero])
  have hc := congrArg (PowerSeries.coeff n) key
  simpa using hc

/-- **A negated one-letter alphabet.** If `ψ(p_j) = -aʲ` for every `j ≥ 1` then `ψ(h₀) = 1`,
`ψ(h₁) = -a` and `ψ(h_m) = 0` for every `m ≥ 2`: the `h`-series of a negated letter is the
polynomial `1 - a t`. -/
theorem completeHomog_neg_single [Algebra K R] {F : Type*} [FunLike F (Lambda K) R]
    [RingHomClass F (Lambda K) R]
    (ψ : F) (a : R) (h : ∀ i : ℕ, ψ (MvPolynomial.X i) = -a ^ (i + 1)) :
    ψ (completeHomog K 0) = 1 ∧ ψ (completeHomog K 1) = -a ∧
      ∀ m : ℕ, 2 ≤ m → ψ (completeHomog K m) = 0 := by
  -- the empty alphabet is the letter `a` added to its negation
  set φ : Lambda K →ₐ[K] R := MvPolynomial.aeval fun i => a ^ (i + 1) with hφ
  have hφX : ∀ i : ℕ, φ (MvPolynomial.X i) = a ^ (i + 1) := fun i => by
    rw [hφ, MvPolynomial.aeval_X]
  set χ : Lambda K →ₐ[K] R := MvPolynomial.aeval fun _ => 0 with hχ
  have hχX : ∀ i : ℕ, χ (MvPolynomial.X i) = φ (MvPolynomial.X i) + ψ (MvPolynomial.X i) :=
    fun i => by rw [hχ, MvPolynomial.aeval_X, hφX i, h i, add_neg_cancel]
  have hχh : ∀ n : ℕ, χ (completeHomog K n) = (0 : R) ^ n :=
    completeHomog_single χ 0 (fun i => by rw [hχ, MvPolynomial.aeval_X, zero_pow (by omega)])
  have key : ∀ n : ℕ, (0 : R) ^ n
      = ∑ s ∈ range (n + 1), a ^ (n - s) * ψ (completeHomog K s) := by
    intro n
    rw [← hχh n, completeHomog_of_add φ ψ χ hχX n]
    exact Finset.sum_congr rfl fun s _ => by rw [completeHomog_single φ a hφX]
  have h0 : ψ (completeHomog K 0) = 1 := by
    have := key 0
    simpa using this.symm
  have h1 : ψ (completeHomog K 1) = -a := by
    have := key 1
    rw [Finset.sum_range_succ, Finset.sum_range_one, h0] at this
    simp only [pow_one, Nat.sub_zero, Nat.sub_self, pow_zero, mul_one, one_mul] at this
    linear_combination -this
  refine ⟨h0, h1, ?_⟩
  intro m hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    -- only the top two terms of `key m` survive, and they cancel
    have hm2 : 2 ≤ m := hm
    have hsplit : ∀ s ∈ range (m + 1), s ∉ ({0, 1, m} : Finset ℕ) →
        a ^ (m - s) * ψ (completeHomog K s) = 0 := by
      intro s hs hsn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hsn
      have hslt : s < m := by
        have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
        omega
      rw [ih s hslt (by omega), mul_zero]
    have hsub : ({0, 1, m} : Finset ℕ) ⊆ range (m + 1) := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      simp only [Finset.mem_range]
      omega
    have hkey := key m
    rw [← Finset.sum_subset hsub hsplit] at hkey
    rw [show ({0, 1, m} : Finset ℕ) = {0, 1} ∪ {m} by
      ext s; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]; tauto,
      Finset.sum_union (by simp only [Finset.disjoint_singleton_right, Finset.mem_insert,
        Finset.mem_singleton]; omega)] at hkey
    rw [Finset.sum_pair (by omega), Finset.sum_singleton, h0, h1] at hkey
    rw [zero_pow (by omega)] at hkey
    have hpa : a ^ (m - 1) * a = a ^ m := by
      rw [← pow_succ]
      congr 1
      omega
    have hpow : a ^ (m - 1) * -a = -a ^ m := by rw [mul_neg, hpa]
    rw [Nat.sub_zero, Nat.sub_self, pow_zero, mul_one, hpow] at hkey
    linear_combination -hkey

end Add

/-! ### Dilated and negated-dilated alphabets -/

section Dilate

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- **A negated scaled alphabet.** If `ψ(p_j) = -cʲ p_j` for every `j ≥ 1` then
`ψ(hₙ) = (-1)ⁿ cⁿ eₙ`: Newton's identity for `h` under `ψ` is Newton's identity for `e`. -/
theorem completeHomog_neg_scale {F : Type*} [FunLike F (Lambda K) (Lambda K)]
    [RingHomClass F (Lambda K) (Lambda K)] (ψ : F) (c : K)
    (h : ∀ i : ℕ, ψ (MvPolynomial.X i)
      = -(MvPolynomial.C (c ^ (i + 1)) * MvPolynomial.X i)) (n : ℕ) :
    ψ (completeHomog K n) = (-1) ^ n * MvPolynomial.C (c ^ n) * elemSymm K n := by
  have hQ : ∀ k : ℕ, ψ (powerSum K (k + 1))
      = -(MvPolynomial.C (c ^ (k + 1)) * powerSum K (k + 1)) := by
    intro k
    rw [CopPower.powerSum_succ, h k]
  have hG : PowerSeries.derivative (Lambda K)
        (PowerSeries.mk fun n => (-1) ^ n * MvPolynomial.C (c ^ n) * elemSymm K n)
      = (PowerSeries.mk fun k => ψ (powerSum K (k + 1)))
        * PowerSeries.mk fun n => (-1) ^ n * MvPolynomial.C (c ^ n) * elemSymm K n := by
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk]
    have hterm : ∀ k ∈ range (n + 1),
        ψ (powerSum K (k + 1)) * ((-1) ^ (n - k) * MvPolynomial.C (c ^ (n - k))
            * elemSymm K (n - k))
          = (-1) ^ (n + 1) * MvPolynomial.C (c ^ (n + 1))
              * ((-1) ^ k * powerSum K (k + 1) * elemSymm K (n - k)) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hc : (MvPolynomial.C (c ^ (n + 1)) : Lambda K)
          = MvPolynomial.C (c ^ (k + 1)) * MvPolynomial.C (c ^ (n - k)) := by
        rw [← MvPolynomial.C_mul, ← pow_add]
        congr 2
        omega
      have hsign : ((-1 : Lambda K)) ^ (n - k) = (-1) ^ n * (-1) ^ k := by
        rw [← pow_add, show n + k = (n - k) + 2 * k by omega, pow_add, pow_mul]
        simp
      rw [hQ k, hsign, hc, pow_succ]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← natCast_mul_elemSymm]
    ring
  have key : (PowerSeries.mk fun n => ψ (completeHomog K n))
      = PowerSeries.mk fun n => (-1) ^ n * MvPolynomial.C (c ^ n) * elemSymm K n :=
    CopPower.powerSeries_ext_of_logDeriv (CopPower.derivative_mk_completeHomog ψ) hG
      (by simp [CopPower.completeHomog_zero, elemSymm_zero])
  have hc := congrArg (PowerSeries.coeff n) key
  simpa using hc

/-- **A dilated alphabet.** If `χ(p_j) = (1 - cʲ) p_j` for every `j ≥ 1` then
`χ(hₙ) = ∑ₛ (-1)ˢ cˢ h_{n-s} eₛ`.

This is the statement of `HJO.Sym.completeHomog_dilate_alphabet`, proved here a second time; the
duplication is recorded rather than left silent. -/
theorem completeHomog_dilate (c : K) {F : Type*} [FunLike F (Lambda K) (Lambda K)]
    [RingHomClass F (Lambda K) (Lambda K)] (χ : F)
    (h : ∀ i : ℕ, χ (MvPolynomial.X i)
      = MvPolynomial.C (1 - c ^ (i + 1)) * MvPolynomial.X i) (n : ℕ) :
    χ (completeHomog K n)
      = ∑ s ∈ range (n + 1),
          (-1) ^ s * MvPolynomial.C (c ^ s) * completeHomog K (n - s) * elemSymm K s := by
  set ψ : Lambda K →ₐ[K] Lambda K :=
    MvPolynomial.aeval fun i => -(MvPolynomial.C (c ^ (i + 1)) * MvPolynomial.X i) with hψ
  have hψX : ∀ i : ℕ, ψ (MvPolynomial.X i)
      = -(MvPolynomial.C (c ^ (i + 1)) * MvPolynomial.X i) := fun i => by
    rw [hψ, MvPolynomial.aeval_X]
  have hadd : ∀ i : ℕ, χ (MvPolynomial.X i)
      = (RingHom.id (Lambda K)) (MvPolynomial.X i) + ψ (MvPolynomial.X i) := by
    intro i
    rw [h i, hψX i, RingHom.id_apply, map_sub, MvPolynomial.C_1]
    ring
  rw [completeHomog_of_add (RingHom.id (Lambda K)) ψ χ hadd n]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [RingHom.id_apply, completeHomog_neg_scale ψ c hψX s]
  ring

/-- **The alternating convolution of the two bases.** For every `n ≥ 1`,
`∑_{s=0}^{n} (-1)ˢ h_{n-s} eₛ = 0`: it is the value of `hₙ` under the empty alphabet, which
vanishes above degree zero, and the empty alphabet is the dilation at `c = 1`. -/
@[hjo "lem_h_cancel"]
theorem sum_alternating_completeHomog_mul_elemSymm {n : ℕ} (hn : 1 ≤ n) :
    ∑ s ∈ range (n + 1), (-1) ^ s * completeHomog K (n - s) * elemSymm K s = 0 := by
  set χ : Lambda K →ₐ[K] Lambda K := MvPolynomial.aeval fun _ => 0 with hχ
  have hχX : ∀ i : ℕ, χ (MvPolynomial.X i)
      = MvPolynomial.C (1 - (1 : K) ^ (i + 1)) * MvPolynomial.X i := by
    intro i
    rw [hχ, MvPolynomial.aeval_X, one_pow, sub_self, map_zero, zero_mul]
  have hzero : χ (completeHomog K n) = 0 := by
    rw [completeHomog_single χ 0 (fun i => by rw [hχ, MvPolynomial.aeval_X,
      zero_pow (by omega)]) n, zero_pow (by omega)]
  rw [completeHomog_dilate (1 : K) χ hχX n] at hzero
  rw [← hzero]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [one_pow, map_one, mul_one]

end Dilate

/-! ### The four-letter alphabet of the displacements -/

section Scaled

variable {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R] [Algebra ℚ R]
  [Algebra K R]

/-- **The complete homogeneous functions of a scaled parameter product.** If
`χ(p_j) = (1 - xʲ)(1 - yʲ) ζʲ` for every `j ≥ 1` then, for every `m ≥ 1`,
`(1 - x y) χ(h_m) = (1 - x)(1 - y)(1 - (x y)^m) ζ^m`.

This is `HJO.Sym.completeHomog_scaled` with the division by `1 - x y` cleared, so no
invertibility hypothesis is needed. The alphabet is `ζ + x y ζ - x ζ - y ζ`, four letters of
which two are negated, so the `h`-series is
`(1 - x ζ t)(1 - y ζ t) / ((1 - ζ t)(1 - x y ζ t))`; the proof adds the letters one at a time. -/
@[hjo "lem_h_scaled_M"]
theorem completeHomog_scaled {F : Type*} [FunLike F (Lambda K) R] [RingHomClass F (Lambda K) R]
    (χ : F) (x y ζ : R)
    (h : ∀ i : ℕ, χ (MvPolynomial.X i)
      = (1 - x ^ (i + 1)) * (1 - y ^ (i + 1)) * ζ ^ (i + 1)) {m : ℕ} (hm : 1 ≤ m) :
    (1 - x * y) * χ (completeHomog K m)
      = (1 - x) * (1 - y) * (1 - (x * y) ^ m) * ζ ^ m := by
  -- the two positive letters `ζ` and `x y ζ`
  set φ₁ : Lambda K →ₐ[K] R := MvPolynomial.aeval fun i => ζ ^ (i + 1) with hφ₁
  set φ₂ : Lambda K →ₐ[K] R := MvPolynomial.aeval fun i => (x * y * ζ) ^ (i + 1) with hφ₂
  set χ₁ : Lambda K →ₐ[K] R :=
    MvPolynomial.aeval fun i => ζ ^ (i + 1) + (x * y * ζ) ^ (i + 1) with hχ₁def
  have hχ₁sum : ∀ n : ℕ, χ₁ (completeHomog K n)
      = ∑ s ∈ range (n + 1), ζ ^ (n - s) * (x * y * ζ) ^ s := by
    intro n
    rw [completeHomog_of_add φ₁ φ₂ χ₁ (fun i => by
      rw [hχ₁def, hφ₁, hφ₂, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
        MvPolynomial.aeval_X]) n]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [completeHomog_single φ₁ ζ (fun i => by rw [hφ₁, MvPolynomial.aeval_X]),
      completeHomog_single φ₂ (x * y * ζ) (fun i => by rw [hφ₂, MvPolynomial.aeval_X])]
  -- the closed form of the two-letter alphabet, with the geometric denominator cleared
  have hχ₁cl : ∀ n : ℕ, (1 - x * y) * χ₁ (completeHomog K n) = ζ ^ n * (1 - (x * y) ^ (n + 1)) := by
    intro n
    rw [hχ₁sum n, Finset.mul_sum]
    have hterm : ∀ s ∈ range (n + 1),
        (1 - x * y) * (ζ ^ (n - s) * (x * y * ζ) ^ s) = (1 - x * y) * (ζ ^ n * (x * y) ^ s) := by
      intro s hs
      have hsn : s ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      rw [mul_pow, show ζ ^ (n - s) * ((x * y) ^ s * ζ ^ s)
          = ζ ^ (n - s) * ζ ^ s * (x * y) ^ s by ring,
        ← pow_add, show n - s + s = n by omega]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum]
    have hgeom : (1 - x * y) * ∑ s ∈ range (n + 1), (x * y) ^ s
        = 1 - (x * y) ^ (n + 1) := by
      have hg := geom_sum_mul (x * y) (n + 1)
      linear_combination -hg
    rw [show (1 - x * y) * (ζ ^ n * ∑ s ∈ range (n + 1), (x * y) ^ s)
        = ζ ^ n * ((1 - x * y) * ∑ s ∈ range (n + 1), (x * y) ^ s) by ring, hgeom]
  -- adding the negated letter `x ζ`
  set ν₁ : Lambda K →ₐ[K] R := MvPolynomial.aeval fun i => -(x * ζ) ^ (i + 1) with hν₁
  set χ₂ : Lambda K →ₐ[K] R :=
    MvPolynomial.aeval fun i => ζ ^ (i + 1) + (x * y * ζ) ^ (i + 1) - (x * ζ) ^ (i + 1) with hχ₂def
  obtain ⟨hν₁0, hν₁1, hν₁2⟩ := completeHomog_neg_single ν₁ (x * ζ)
    (fun i => by rw [hν₁, MvPolynomial.aeval_X])
  have hχ₂step : ∀ j : ℕ, χ₂ (completeHomog K (j + 1))
      = χ₁ (completeHomog K (j + 1)) - x * ζ * χ₁ (completeHomog K j) := by
    intro j
    rw [completeHomog_of_add χ₁ ν₁ χ₂ (fun i => by
      rw [hχ₂def, hχ₁def, hν₁, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
        MvPolynomial.aeval_X]
      ring) (j + 1)]
    have hsub : ({0, 1} : Finset ℕ) ⊆ range (j + 1 + 1) := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      simp only [Finset.mem_range]
      omega
    rw [← Finset.sum_subset hsub (fun s hs hs2 => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs2
      rw [hν₁2 s (by omega), mul_zero]), Finset.sum_pair (by omega), hν₁0, hν₁1,
      Nat.sub_zero, Nat.add_sub_cancel]
    ring
  have hχ₂0 : χ₂ (completeHomog K 0) = 1 := by
    rw [CopPower.completeHomog_zero, map_one]
  have hχ₂cl : ∀ j : ℕ, (1 - x * y) * χ₂ (completeHomog K (j + 1))
      = ζ ^ (j + 1) * ((1 - (x * y) ^ (j + 1 + 1)) - x * (1 - (x * y) ^ (j + 1))) := by
    intro j
    rw [hχ₂step j, mul_sub, hχ₁cl (j + 1),
      show (1 - x * y) * (x * ζ * χ₁ (completeHomog K j))
        = x * ζ * ((1 - x * y) * χ₁ (completeHomog K j)) by ring, hχ₁cl j]
    ring
  -- adding the negated letter `y ζ`
  set ν₂ : Lambda K →ₐ[K] R := MvPolynomial.aeval fun i => -(y * ζ) ^ (i + 1) with hν₂
  obtain ⟨hν₂0, hν₂1, hν₂2⟩ := completeHomog_neg_single ν₂ (y * ζ)
    (fun i => by rw [hν₂, MvPolynomial.aeval_X])
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hlast : χ (completeHomog K (j + 1))
      = χ₂ (completeHomog K (j + 1)) - y * ζ * χ₂ (completeHomog K j) := by
    rw [completeHomog_of_add χ₂ ν₂ χ (fun i => by
      rw [h i, hχ₂def, hν₂, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      ring) (j + 1)]
    have hsub : ({0, 1} : Finset ℕ) ⊆ range (j + 1 + 1) := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      simp only [Finset.mem_range]
      omega
    rw [← Finset.sum_subset hsub (fun s hs hs2 => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs2
      rw [hν₂2 s (by omega), mul_zero]), Finset.sum_pair (by omega), hν₂0, hν₂1,
      Nat.sub_zero, Nat.add_sub_cancel]
    ring
  rw [hlast, mul_sub]
  match j with
  | 0 =>
    rw [hχ₂cl 0, hχ₂0]
    ring
  | i + 1 =>
    rw [hχ₂cl (i + 1),
      show (1 - x * y) * (y * ζ * χ₂ (completeHomog K (i + 1)))
        = y * ζ * ((1 - x * y) * χ₂ (completeHomog K (i + 1))) by ring, hχ₂cl i]
    ring

end Scaled

/-! ### The axis generators -/

section Axis

/-- **A diagonal substitution rescaled by the powers of `t` acts on a homogeneous element of
degree `k` as the scalar `tᵏ`.** Both substitutions multiply each monomial by a product of
scalars; rescaling the scalar at `p_j` by `tʲ` multiplies that product by `t` raised to the
weighted degree of the monomial, which is `k` throughout a homogeneous element. -/
theorem diagScale_pow_smul_of_mem_lambdaComp {K : Type*} [CommRing K] (t : K) (c : ℕ → K)
    {k : ℕ} {f : Lambda K} (hf : f ∈ LambdaComp K k) :
    diagScale (fun i => t ^ (i + 1) * c i) f = MvPolynomial.C (t ^ k) * diagScale c f := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [UkRegular.coeff_diagScale, MvPolynomial.coeff_C_mul, UkRegular.coeff_diagScale]
  by_cases hd : MvPolynomial.coeff d f = 0
  · rw [hd, mul_zero, mul_zero, mul_zero]
  · have hw : ∑ i ∈ d.support, (i + 1) * d i = k := by
      have h := mem_lambdaComp.1 hf hd
      rw [Finsupp.weight_apply, Finsupp.sum] at h
      simpa [mul_comm] using h
    rw [Finset.prod_congr rfl (fun i _ => mul_pow (t ^ (i + 1)) (c i) (d i)),
      Finset.prod_mul_distrib]
    have hpow : ∏ i ∈ d.support, (t ^ (i + 1)) ^ d i = t ^ k := by
      rw [Finset.prod_congr rfl (fun i _ => (pow_mul t (i + 1) (d i)).symm),
        Finset.prod_pow_eq_pow_sum, hw]
    rw [hpow, mul_assoc]

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- The axis substitution on a generator. -/
theorem plethAxis_X (v : L) (i : ℕ) :
    plethAxis v (MvPolynomial.X i)
      = MvPolynomial.C ((v ^ (i + 1))⁻¹ - 1) * MvPolynomial.X i :=
  MvPolynomial.aeval_X _ i

/-- The dilation of the alphabet by `v`: the substitution sending `p_j` to `(1 - vʲ) p_j`. It is
the unstarred half of the pair whose `h`-values are the axis generators. -/
noncomputable def plethDilate (v : L) : Lambda L →ₐ[L] Lambda L :=
  diagScale fun i => 1 - v ^ (i + 1)

omit [Algebra ℚ L] in
/-- The dilation on a generator. -/
theorem plethDilate_X (v : L) (i : ℕ) :
    plethDilate v (MvPolynomial.X i)
      = MvPolynomial.C (1 - v ^ (i + 1)) * MvPolynomial.X i :=
  MvPolynomial.aeval_X _ i

omit [Algebra ℚ L] in
/-- **The axis substitution is the dilation scaled by `v^{-k}` in degree `k`.** On the generator
`p_j` the axis scalar `v^{-j} - 1` is `v^{-j}` times the dilation scalar `1 - vʲ`, so on a
homogeneous element of degree `k` the two differ by the single scalar `v^{-k}`. -/
theorem plethAxis_eq_of_mem_lambdaComp {v : L} (hv0 : v ≠ 0) {k : ℕ} {f : Lambda L}
    (hf : f ∈ LambdaComp L k) :
    plethAxis v f = MvPolynomial.C ((v ^ k)⁻¹) * plethDilate v f := by
  have hrw : (fun i => (v ^ (i + 1))⁻¹ - 1)
      = fun i => (v⁻¹) ^ (i + 1) * (1 - v ^ (i + 1)) := by
    funext i
    have hvi : v ^ (i + 1) ≠ 0 := pow_ne_zero _ hv0
    rw [inv_pow, mul_sub, mul_one, inv_mul_cancel₀ hvi]
  rw [plethAxis_eq_diagScale, hrw, diagScale_pow_smul_of_mem_lambdaComp _ _ hf, plethDilate,
    inv_pow]

/-- **The first axis generator.** For `v = q u` neither `0` nor `1`, `U₁ = -e₁`. -/
@[hjo "lem_axis_gen_one"]
theorem axisGen_one {v : L} (hv0 : v ≠ 0) (hv1 : v ≠ 1) :
    axisGen v 1 = -elemSymm L 1 := by
  have h1 : completeHomog L 1 = MvPolynomial.X 0 := by
    rw [CopPower.completeHomog_one, CopPower.powerSum_one]
  have hscal : v / (v - 1) * ((v ^ (0 + 1))⁻¹ - 1) = -1 := by
    have hv : v - 1 ≠ 0 := sub_ne_zero_of_ne hv1
    field_simp
    ring
  rw [axisGen, h1, plethAxis_X, ← mul_assoc, ← MvPolynomial.C_mul, hscal, elemSymm_one,
    CopPower.powerSum_one, map_neg, MvPolynomial.C_1, neg_one_mul]

/-- **The axis generator as a dilated convolution.** For `v = q u` neither `0` nor `1` and every
`k ≥ 1`, `∑_{s=0}^{k} (-1)ˢ vˢ h_{k-s} eₛ = (v - 1) v^{k-1} U_k`.

Both substitutions send each `p_j` to a scalar multiple of itself, the axis one by
`v^{-j}(1 - v^j)` and the dilation by `1 - v^j`; since `h_k` is weighted homogeneous of degree
`k` the two differ on it by exactly `v^{-k}`, which is what turns `U_k` into the convolution. -/
@[hjo "lem_axis_dilate"]
theorem sum_alternating_pow_completeHomog_mul_elemSymm {v : L} (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) :
    ∑ s ∈ range (k + 1),
        (-1) ^ s * MvPolynomial.C (v ^ s) * completeHomog L (k - s) * elemSymm L s
      = MvPolynomial.C ((v - 1) * v ^ (k - 1)) * axisGen v k := by
  have hv : v - 1 ≠ 0 := sub_ne_zero_of_ne hv1
  have hvk : v ^ k ≠ 0 := pow_ne_zero _ hv0
  have hk' : v ^ (k - 1) * v = v ^ k := by
    rw [← pow_succ]
    congr 1
    omega
  have hscal : (v - 1) * v ^ (k - 1) * (v / (v - 1)) * (v ^ k)⁻¹ = 1 := by
    rw [div_eq_mul_inv, show (v - 1) * v ^ (k - 1) * (v * (v - 1)⁻¹) * (v ^ k)⁻¹
      = ((v - 1) * (v - 1)⁻¹) * ((v ^ (k - 1) * v) * (v ^ k)⁻¹) by ring, hk',
      mul_inv_cancel₀ hv, mul_inv_cancel₀ hvk, mul_one]
  have key : MvPolynomial.C ((v - 1) * v ^ (k - 1)) * axisGen v k
      = plethDilate v (completeHomog L k) := by
    rw [axisGen, plethAxis_eq_of_mem_lambdaComp hv0 (completeHomog_mem_lambdaComp L k),
      show MvPolynomial.C ((v - 1) * v ^ (k - 1)) * (MvPolynomial.C (v / (v - 1)) *
          (MvPolynomial.C ((v ^ k)⁻¹) * plethDilate v (completeHomog L k)))
        = MvPolynomial.C ((v - 1) * v ^ (k - 1)) * MvPolynomial.C (v / (v - 1)) *
            MvPolynomial.C ((v ^ k)⁻¹) * plethDilate v (completeHomog L k) by ring,
      ← MvPolynomial.C_mul, ← MvPolynomial.C_mul, hscal, MvPolynomial.C_1, one_mul]
  rw [key, completeHomog_dilate v (plethDilate v) (plethDilate_X v) k]

end Axis

end HJO.Sym
