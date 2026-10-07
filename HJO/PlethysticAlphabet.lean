/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.HAlphabet
public meta import HJO.Attr

/-! # The plethystic alphabet operations on the complete homogeneous functions

An alphabet is a ring homomorphism out of `Λ = HJO.Sym.Lambda K = K[p₁, p₂, …]`, and the
plethystic operations on alphabets -- adding two of them, taking one letter, negating a letter,
dilating -- are read off the generators `p_j`. Each operation has a closed form for the images of
the complete homogeneous functions `hₙ`, and this file states those closed forms at the least
generality possible: the target ring carries only the structure the identity actually uses.

`HJO.Collinear.HAlphabet` already proves the same five principles, but each time with the
target either equal to `Λ` itself or carrying a `ℚ`-algebra structure of its own. Two observations
lift them:

* A ring homomorphism out of `Λ` already carries `ℚ` into the target, so a target that is a
  commutative ring is a `ℚ`-algebra for free -- and the identities do not mention that structure,
  so an instance manufactured inside the proof does no harm. This is what removes `[Algebra ℚ R]`
  from `completeHomog_add_alphabet` and `completeHomog_dilate_letter`.
* A one-letter alphabet factors through `Λ` itself: the homomorphism `p_j ↦ p₁ʲ` agrees with the
  given one after composition, so the identity in a general -- possibly noncommutative -- target
  is the identity in `Λ` transported along a ring homomorphism. This is what removes both
  commutativity and `[Algebra ℚ R]` from `completeHomog_single_letter` and
  `completeHomog_neg_letter_eq_zero`.

## Main results

* `HJO.Sym.completeHomog_single_letter`: a one-letter alphabet sends `hₙ` to `aⁿ`.
* `HJO.Sym.completeHomog_neg_letter_eq_zero`: a negated one-letter alphabet kills `h_m` for
  `m ≥ 2`.
* `HJO.Sym.completeHomog_add_alphabet`: the `h` of a sum of alphabets is the convolution of the two
  `h`-families.
* `HJO.Sym.completeHomog_neg_scale_alphabet`: a negated scaled alphabet exchanges `h` for `e`.
* `HJO.Sym.completeHomog_dilate_alphabet`: a dilated alphabet gives the alternating convolution of
  `h` against `e`.
* `HJO.Sym.completeHomog_dilate_letter`: the twisted alphabet `(1 - q)x` on one letter sends `h_b`
  to `(1 - q) x^b` in every positive degree.

## Implementation notes

`HJO.Sym.elemSymm_one` -- `e₁ = p₁` -- is `HJO.Sym.elemSymm_one` of
`HJO.Collinear.HAlphabet`, verbatim and over the same base; it is not restated here, since one
import cone cannot hold the name twice.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-! ### One letter, and one negated letter, in an arbitrary ring -/

section Letter

variable {R : Type*} [Ring R] {F : Type*} [FunLike F (Lambda K) R] [RingHomClass F (Lambda K) R]

/-- **A one-letter alphabet.** If a homomorphism `φ : Λ → R` sends every power sum `p_j`, `j ≥ 1`,
to the `j`-th power of `a`, then it sends every complete homogeneous function `hₙ` to `aⁿ`. -/
@[hjo "lem_h_single"]
theorem completeHomog_single_letter
    (φ : F) (a : R) (h : ∀ j : ℕ, 0 < j → φ (powerSum K j) = a ^ j) (n : ℕ) :
    φ (completeHomog K n) = a ^ n := by
  have ha : φ (MvPolynomial.X (0 : ℕ)) = a := by
    rw [← CopPower.powerSum_one, h 1 Nat.one_pos, pow_one]
  set θ : Lambda K →ₐ[K] Lambda K :=
    MvPolynomial.aeval fun i => (MvPolynomial.X 0 : Lambda K) ^ (i + 1) with hθ
  have hθX : ∀ i : ℕ, θ (MvPolynomial.X i) = (MvPolynomial.X 0 : Lambda K) ^ (i + 1) :=
    fun i => by rw [hθ, MvPolynomial.aeval_X]
  have hθC : ∀ r : K, θ (MvPolynomial.C r) = MvPolynomial.C r := fun r => by
    rw [hθ, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  have hcomp : ((φ : Lambda K →+* R).comp (θ : Lambda K →+* Lambda K))
      = (φ : Lambda K →+* R) :=
    MvPolynomial.ringHom_ext (fun r => by simp only [RingHom.comp_apply, RingHom.coe_coe, hθC])
      fun i => by
        simp only [RingHom.comp_apply, RingHom.coe_coe, hθX i, map_pow, ha]
        rw [← CopPower.powerSum_succ]
        exact (h (i + 1) i.succ_pos).symm
  have hφθ : φ (θ (completeHomog K n)) = φ (completeHomog K n) :=
    DFunLike.congr_fun hcomp (completeHomog K n)
  rw [← hφθ, completeHomog_single θ (MvPolynomial.X 0) hθX n, map_pow, ha]

/-- **A negated one-letter alphabet.** If a ring homomorphism `ψ : Λ → R` sends each power sum
`p_j`, `j ≥ 1`, to `-aʲ`, then it kills every complete homogeneous function of degree at least two:
`ψ(h_m) = 0` for `m ≥ 2`. Its two remaining values are `ψ(h_0) = 1` and `ψ(h_1) = -a`. -/
@[hjo "lem_h_neg_single"]
theorem completeHomog_neg_letter_eq_zero
    (ψ : F) (a : R) (h : ∀ j : ℕ, 0 < j → ψ (powerSum K j) = -a ^ j) {m : ℕ} (hm : 2 ≤ m) :
    ψ (completeHomog K m) = 0 := by
  have ha : ψ (MvPolynomial.X (0 : ℕ)) = -a := by
    rw [← CopPower.powerSum_one, h 1 Nat.one_pos, pow_one]
  have hsign : ∀ i : ℕ, ((-1 : R)) ^ i * (-1) ^ (i + 1) = -1 := fun i => by
    rw [← pow_add, show i + (i + 1) = 2 * i + 1 by omega, pow_succ, pow_mul]
    simp
  set θ : Lambda K →ₐ[K] Lambda K :=
    MvPolynomial.aeval fun i => (-1 : Lambda K) ^ i * MvPolynomial.X 0 ^ (i + 1) with hθ
  have hθX : ∀ i : ℕ,
      θ (MvPolynomial.X i) = (-1 : Lambda K) ^ i * MvPolynomial.X 0 ^ (i + 1) :=
    fun i => by rw [hθ, MvPolynomial.aeval_X]
  have hθC : ∀ r : K, θ (MvPolynomial.C r) = MvPolynomial.C r := fun r => by
    rw [hθ, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  -- `θ` is the negated letter `-p₁` of `Λ` itself, so `HAlphabet` kills its `h_m` for `m ≥ 2`
  have hθneg : ∀ i : ℕ, θ (MvPolynomial.X i) = -(-MvPolynomial.X (0 : ℕ) : Lambda K) ^ (i + 1) :=
    fun i => by rw [hθX i, neg_pow]; ring
  have hcomp : ((ψ : Lambda K →+* R).comp (θ : Lambda K →+* Lambda K))
      = (ψ : Lambda K →+* R) :=
    MvPolynomial.ringHom_ext (fun r => by simp only [RingHom.comp_apply, RingHom.coe_coe, hθC])
      fun i => by
        simp only [RingHom.comp_apply, RingHom.coe_coe, hθX i, map_mul, map_pow, map_neg,
          map_one, ha, neg_pow a (i + 1), ← mul_assoc, hsign i, neg_one_mul]
        exact (h (i + 1) i.succ_pos).symm
  have hψθ : ψ (θ (completeHomog K m)) = ψ (completeHomog K m) :=
    DFunLike.congr_fun hcomp (completeHomog K m)
  rw [← hψθ, (completeHomog_neg_single θ (-MvPolynomial.X (0 : ℕ)) hθneg).2.2 m hm, map_zero]

end Letter

/-! ### Sums of alphabets, over any commutative ring -/

section Add

variable {R : Type*} [CommRing R]

/-- **The complete homogeneous functions of a sum of alphabets.** If three homomorphisms
`φ, ψ, χ : Λ → R` satisfy `χ(p_j) = φ(p_j) + ψ(p_j)` on every power sum `p_j`, `j ≥ 1`, then the
complete homogeneous functions convolve: `χ(hₙ) = ∑_{s=0}ⁿ φ(h_{n-s}) ψ(h_s)`. -/
@[hjo "lem_pleth_add_h"]
theorem completeHomog_add_alphabet {F G H : Type*}
    [FunLike F (Lambda K) R] [RingHomClass F (Lambda K) R]
    [FunLike G (Lambda K) R] [RingHomClass G (Lambda K) R]
    [FunLike H (Lambda K) R] [RingHomClass H (Lambda K) R]
    (φ : F) (ψ : G) (χ : H)
    (h : ∀ j : ℕ, 0 < j → χ (powerSum K j) = φ (powerSum K j) + ψ (powerSum K j)) (n : ℕ) :
    χ (completeHomog K n)
      = ∑ s ∈ Finset.range (n + 1),
          φ (completeHomog K (n - s)) * ψ (completeHomog K s) := by
  let _ : Algebra ℚ R := RingHom.toAlgebra ((φ : Lambda K →+* R).comp (algebraMap ℚ (Lambda K)))
  exact completeHomog_of_add φ ψ χ
    (fun i => by rw [← CopPower.powerSum_succ]; exact h (i + 1) i.succ_pos) n

end Add

/-! ### Negated scalings and dilations, over a `ℚ`-algebra -/

section Dilate

variable {R : Type*} [CommRing R] [Algebra ℚ R] {F G : Type*}
  [FunLike F (Lambda K) R] [RingHomClass F (Lambda K) R]
  [FunLike G (Lambda K) R] [RingHomClass G (Lambda K) R]

/-- **The complete homogeneous functions of a negated scaled alphabet.** If two homomorphisms
`φ, ψ : Λ → R` satisfy `ψ(p_j) = -c^j φ(p_j)` on every power sum `p_j`, `j ≥ 1`, then `ψ` exchanges
the complete homogeneous family for the elementary one, up to sign and scale:
`ψ(hₙ) = (-1)ⁿ cⁿ φ(eₙ)`. -/
@[hjo "lem_h_neg_scale"]
theorem completeHomog_neg_scale_alphabet (φ : F) (ψ : G) (c : R)
    (h : ∀ j : ℕ, 0 < j → ψ (powerSum K j) = -(c ^ j * φ (powerSum K j))) (n : ℕ) :
    ψ (completeHomog K n) = (-1) ^ n * c ^ n * φ (elemSymm K n) := by
  have hG : PowerSeries.derivative R
        (PowerSeries.mk fun n => (-1) ^ n * c ^ n * φ (elemSymm K n))
      = (PowerSeries.mk fun k => ψ (powerSum K (k + 1)))
        * PowerSeries.mk fun n => (-1) ^ n * c ^ n * φ (elemSymm K n) := by
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        ψ (powerSum K (k + 1)) * ((-1) ^ (n - k) * c ^ (n - k) * φ (elemSymm K (n - k)))
          = (-1) ^ (n + 1) * c ^ (n + 1)
              * ((-1) ^ k * φ (powerSum K (k + 1)) * φ (elemSymm K (n - k))) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hc : (c ^ (n + 1) : R) = c ^ (k + 1) * c ^ (n - k) := by
        rw [← pow_add]
        congr 1
        omega
      have hsign : ((-1 : R)) ^ (n - k) = (-1) ^ n * (-1) ^ k := by
        rw [← pow_add, show n + k = (n - k) + 2 * k by omega, pow_add, pow_mul]
        simp
      rw [h (k + 1) k.succ_pos, hsign, hc, pow_succ ((-1 : R)) n]
      ring
    have hsum : ∑ k ∈ Finset.range (n + 1),
          ((-1 : R)) ^ k * φ (powerSum K (k + 1)) * φ (elemSymm K (n - k))
        = φ (∑ k ∈ Finset.range (n + 1),
            (-1) ^ k * powerSum K (k + 1) * elemSymm K (n - k)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => by
        rw [map_mul, map_mul, map_pow, map_neg, map_one]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum, ← natCast_mul_elemSymm, map_mul,
      map_add, map_natCast, map_one]
    ring
  have key : (PowerSeries.mk fun n => ψ (completeHomog K n))
      = PowerSeries.mk fun n => (-1) ^ n * c ^ n * φ (elemSymm K n) :=
    CopPower.powerSeries_ext_of_logDeriv (CopPower.derivative_mk_completeHomog ψ) hG
      (by simp [CopPower.completeHomog_zero, elemSymm_zero])
  simpa using congrArg (PowerSeries.coeff n) key

/-- **The complete homogeneous functions of a dilated alphabet.** If `ι, χ : Λ → R` are
homomorphisms with `χ(p_j) = (1 - c^j) ι(p_j)` on every power sum `p_j`, `j ≥ 1` -- so that `χ` is
the alphabet of `ι` dilated to `(1 - c)X` -- then the complete homogeneous functions of `χ` are the
alternating convolution `χ(hₙ) = ∑_{s=0}ⁿ (-1)^s c^s ι(h_{n-s}) ι(e_s)`. -/
@[hjo "lem_h_dilate"]
theorem completeHomog_dilate_alphabet (ι : F) (χ : G) (c : R)
    (h : ∀ j : ℕ, 0 < j → χ (powerSum K j) = (1 - c ^ j) * ι (powerSum K j)) (n : ℕ) :
    χ (completeHomog K n)
      = ∑ s ∈ Finset.range (n + 1),
          (-1) ^ s * c ^ s * ι (completeHomog K (n - s)) * ι (elemSymm K s) := by
  -- the dilation is `ι` with the negated scaling `-cX` of `ι` added
  set ψ : Lambda K →+* R := MvPolynomial.eval₂Hom ((ι : Lambda K →+* R).comp MvPolynomial.C)
    (fun i => -(c ^ (i + 1) * ι (MvPolynomial.X i))) with hψ
  have hψX : ∀ i : ℕ, ψ (MvPolynomial.X i) = -(c ^ (i + 1) * ι (MvPolynomial.X i)) := fun i => by
    rw [hψ, MvPolynomial.eval₂Hom_X']
  have hψp : ∀ j : ℕ, 0 < j → ψ (powerSum K j) = -(c ^ j * ι (powerSum K j)) := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hψX i]
  have hadd : ∀ j : ℕ, 0 < j →
      χ (powerSum K j) = ι (powerSum K j) + ψ (powerSum K j) := by
    intro j hj
    rw [h j hj, hψp j hj, sub_mul, one_mul, sub_eq_add_neg]
  rw [completeHomog_add_alphabet ι ψ χ hadd n]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [completeHomog_neg_scale_alphabet ι ψ c hψp s]
  ring

end Dilate

/-! ### The twisted alphabet on one letter -/

section Twist

/-- **The twisted alphabet on one letter.** If a homomorphism `φ : Λ → R` sends every power sum
`p_j`, `j ≥ 1`, to `(1 - q ^ j) x ^ j` -- so that `φ` is the alphabet `(1 - q)x`, the letter `x`
with the letter `qx` subtracted -- then it sends `h_b` to `(1 - q) x ^ b` for every `b ≥ 1`, one
and the same scalar `1 - q` in every positive degree. At `b = 0` the value is instead
`φ (h_0) = 1`. -/
@[hjo "lem_cm_h_one_letter_twist"]
theorem completeHomog_dilate_letter {R : Type*} [CommRing R] {F : Type*}
    [FunLike F (Lambda K) R] [RingHomClass F (Lambda K) R]
    (φ : F) (q x : R) (h : ∀ j : ℕ, 0 < j → φ (powerSum K j) = (1 - q ^ j) * x ^ j)
    {b : ℕ} (hb : 0 < b) :
    φ (completeHomog K b) = (1 - q) * x ^ b := by
  let _ : Algebra ℚ R := RingHom.toAlgebra ((φ : Lambda K →+* R).comp (algebraMap ℚ (Lambda K)))
  set base : K →+* R := (φ : Lambda K →+* R).comp MvPolynomial.C with hbase
  -- the letter `x`
  set ι : Lambda K →+* R := MvPolynomial.eval₂Hom base (fun i => x ^ (i + 1)) with hι
  have hιX : ∀ i : ℕ, ι (MvPolynomial.X i) = x ^ (i + 1) := fun i => by
    rw [hι, MvPolynomial.eval₂Hom_X']
  have hιh : ∀ n : ℕ, ι (completeHomog K n) = x ^ n := completeHomog_single ι x hιX
  -- the negated letter `qx`
  set ν : Lambda K →+* R := MvPolynomial.eval₂Hom base (fun i => -(q * x) ^ (i + 1)) with hν
  have hνX : ∀ i : ℕ, ν (MvPolynomial.X i) = -(q * x) ^ (i + 1) := fun i => by
    rw [hν, MvPolynomial.eval₂Hom_X']
  have hνp : ∀ j : ℕ, 0 < j → ν (powerSum K j) = -(q * x) ^ j := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hνX i]
  have hν0 : ν (completeHomog K 0) = 1 := by rw [CopPower.completeHomog_zero, map_one]
  have hν1 : ν (completeHomog K 1) = -(q * x) := by
    rw [CopPower.completeHomog_one, hνp 1 Nat.one_pos, pow_one]
  have hadd : ∀ j : ℕ, 0 < j → φ (powerSum K j) = ι (powerSum K j) + ν (powerSum K j) := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [h _ hj, CopPower.powerSum_succ, hιX i, hνX i, mul_pow, sub_mul, one_mul,
      sub_eq_add_neg]
  -- only the degrees `0` and `1` of the negated letter survive
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (b + 1) := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    simp only [Finset.mem_range]
    omega
  have hvanish : ∀ s ∈ Finset.range (b + 1), s ∉ ({0, 1} : Finset ℕ) →
      ι (completeHomog K (b - s)) * ν (completeHomog K s) = 0 := by
    intro s _ hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    rw [completeHomog_neg_letter_eq_zero ν (q * x) hνp (by omega), mul_zero]
  have hx : x ^ (b - 1) * x = x ^ b := by
    rw [← pow_succ]
    congr 1
    omega
  rw [completeHomog_add_alphabet ι ν φ hadd b, ← Finset.sum_subset hsub hvanish,
    Finset.sum_pair (by omega), Nat.sub_zero, hιh, hιh, hν0, hν1]
  linear_combination (-q) * hx

end Twist

end HJO.Sym
