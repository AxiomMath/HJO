/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.PlethysticAlphabet
public import HJO.CarlssonMellit.Parameters
public import HJO.Symmetric.CopPower
public meta import HJO.Attr

/-! # The kernel coefficients evaluate the complete homogeneous functions of a twisted letter

The alphabet `(q - 1)c` -- one letter `c`, dilated by `q` and then had the undilated letter
subtracted -- is the alphabet that appears whenever two of the Carlsson--Mellit displacements are
composed. On the power sums it is `p_j ↦ (q^j - 1)c^j`, and on the complete homogeneous functions
it is `h_s ↦ κ_s c^s`, where `κ` is `HJO.Sym.bkernel`. That single line is the whole reason the
kernel coefficients of `HJO.CarlssonMellit.Parameters` are the coefficients they are.

The proof is to split the alphabet as `qc` plus the negation of `c`, so that
`HJO.Sym.completeHomog_add_alphabet` convolves the two `h`-families,
`HJO.Sym.completeHomog_single_letter` evaluates the first at `(qc)^n`, and
`HJO.Sym.completeHomog_neg_letter_eq_zero` kills all but two terms of the second. The surviving
two terms are `(qc)^s` and `-(qc)^{s-1}c`, whose difference is `q^{s-1}(q-1)c^s`.

## Main results

* `HJO.Sym.completeHomog_twist_letter`: for a ring homomorphism `ψ : Λ → R` with
  `ψ(p_j) = (Q^j - 1)c^j` on every `p_j`, `j ≥ 1`, one has `ψ(h_s) = κ_s(Q) c^s`.
* `HJO.Sym.completeHomog_twist_letter_algHom`: the same statement for a `K`-algebra homomorphism
  and a scalar `q : K`, which is the form.

## Implementation notes

The hypothesis is placed on an arbitrary ring homomorphism rather than on a chosen construction:
the consumers of this lemma each have their own `ψ` (a composite of displacements, an evaluation of
a power series) and none of them is literally an `aeval`. Nothing about the base `K` is needed
beyond what `Λ` already requires, and the target `R` needs no algebra structure at all -- the
rational coefficients inside `h_s` travel along any ring homomorphism out of a `ℚ`-algebra. That is
why `Q` lives in `R`, not in `K`, in the primary statement; the `K`-algebra form is the corollary.

There is no truncated subtraction anywhere in the statement: `bkernel` is `1` at `0` and
`q ^ r * (q - 1)` at `r + 1`, and the two cases of the proof are exactly those two branches, so
the degenerate corner `s = 0` is checked rather than assumed.
-/

@[expose] public section

namespace HJO.Sym

section TwistLetter

variable {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R]

/-- **The complete homogeneous functions of the twisted one-letter alphabet `(q-1)c`.**
If a ring homomorphism `ψ : Λ → R` sends every power sum `p_j`, `j ≥ 1`, to `(Q^j - 1)c^j`, then it
sends the complete homogeneous function `h_s` to `κ_s c^s`, where `κ` is the kernel coefficient
`bkernel`: `κ_0 = 1` and `κ_{s+1} = Q^s(Q-1)`. -/
@[hjo "lem_cm_bkernel_hsymm"]
theorem completeHomog_twist_letter (ψ : Lambda K →+* R) (Q c : R)
    (h : ∀ j : ℕ, 0 < j → ψ (powerSum K j) = (Q ^ j - 1) * c ^ j) (s : ℕ) :
    ψ (completeHomog K s) = bkernel Q s * c ^ s := by
  -- The dilated letter `qc` and the negated letter `-c`, as ring homomorphisms out of `Λ`
  -- agreeing with `ψ` on the constants (which is more than the convolution lemma needs).
  set φ : Lambda K →+* R :=
    MvPolynomial.eval₂Hom (ψ.comp (MvPolynomial.C : K →+* Lambda K)) fun i => (Q * c) ^ (i + 1)
    with hφdef
  set χ : Lambda K →+* R :=
    MvPolynomial.eval₂Hom (ψ.comp (MvPolynomial.C : K →+* Lambda K)) fun i => -c ^ (i + 1)
    with hχdef
  have hφp : ∀ j : ℕ, 0 < j → φ (powerSum K j) = (Q * c) ^ j := by
    intro j hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hφdef, MvPolynomial.eval₂Hom_X']
  have hχp : ∀ j : ℕ, 0 < j → χ (powerSum K j) = -c ^ j := by
    intro j hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hχdef, MvPolynomial.eval₂Hom_X']
  -- The splitting hypothesis of the convolution lemma.
  have hsplit : ∀ j : ℕ, 0 < j →
      ψ (powerSum K j) = φ (powerSum K j) + χ (powerSum K j) := by
    intro j hj
    rw [h j hj, hφp j hj, hχp j hj, mul_pow]
    ring
  -- The two `h`-families of the split.
  have hφh : ∀ n : ℕ, φ (completeHomog K n) = (Q * c) ^ n :=
    fun n => completeHomog_single_letter φ (Q * c) hφp n
  have hχh0 : χ (completeHomog K 0) = 1 := by
    rw [CopPower.completeHomog_zero, map_one]
  have hχh1 : χ (completeHomog K 1) = -c := by
    rw [CopPower.completeHomog_one, hχp 1 Nat.one_pos, pow_one]
  have hχhz : ∀ t : ℕ, 2 ≤ t → χ (completeHomog K t) = 0 :=
    fun t ht => completeHomog_neg_letter_eq_zero χ c hχp ht
  rw [completeHomog_add_alphabet φ χ ψ hsplit s]
  -- Only the terms `t = 0` and `t = 1` survive.
  match s with
  | 0 =>
      rw [Finset.sum_range_one, hφh, hχh0, bkernel_zero]
      ring
  | m + 1 =>
      have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (m + 2) := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        simp only [Finset.mem_range]
        omega
      have hvan : ∀ t ∈ Finset.range (m + 2), t ∉ ({0, 1} : Finset ℕ) →
          φ (completeHomog K (m + 1 - t)) * χ (completeHomog K t) = 0 := by
        intro t _ ht
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
        rw [hχhz t (by omega), mul_zero]
      rw [← Finset.sum_subset hsub hvan, Finset.sum_pair (by omega : (0 : ℕ) ≠ 1),
        Nat.sub_zero, Nat.add_sub_cancel, hφh, hφh, hχh0, hχh1, bkernel_succ]
      ring

/-- **The form of the previous lemma.** For a commutative `K`-algebra `R`, a scalar
`q : K`, an element `c : R` and a `K`-algebra homomorphism `ψ : Λ → R` with
`ψ(p_j) = (q^j - 1)c^j` for every `j ≥ 1`, one has `ψ(h_s) = κ_s c^s` with `κ` the kernel
coefficients of `q`. -/
@[hjo "lem_cm_bkernel_hsymm"]
theorem completeHomog_twist_letter_algHom [Algebra K R] (ψ : Lambda K →ₐ[K] R) (q : K) (c : R)
    (h : ∀ j : ℕ, 0 < j → ψ (powerSum K j) = (algebraMap K R q ^ j - 1) * c ^ j) (s : ℕ) :
    ψ (completeHomog K s) = algebraMap K R (bkernel q s) * c ^ s := by
  have key := completeHomog_twist_letter (ψ : Lambda K →+* R) (algebraMap K R q) c h s
  rw [show algebraMap K R (bkernel q s) = bkernel (algebraMap K R q) s from ?_]
  · exact key
  · match s with
    | 0 => rw [bkernel_zero, bkernel_zero, map_one]
    | m + 1 => rw [bkernel_succ, bkernel_succ, map_mul, map_pow, map_sub, map_one]

end TwistLetter

end HJO.Sym
