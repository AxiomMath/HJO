/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.BkernelHsymm
public import HJO.CarlssonMellit.NegateHsymm
public meta import HJO.Attr

/-! # The Hall--Littlewood displacement of an elementary symmetric function

`HJO.Sym.plethHallLittlewood_elemSymm`: `β(e_n) = ∑_{r=0}^{n}(-1)^r ϰ_r z^{-r} e_{n-r}`, with `ϰ`
the kernel coefficients `HJO.Sym.bkernel` of `HJO.Sym.bkernel`.

## The proof is the convolution principle at two known alphabets

Composing `β` with the negation `ω₋` of the alphabet gives a homomorphism `χ` sending `p_k` to
`-p_k + (q^k-1)z^{-k}`, which splits as the sum of the negated alphabet `φ : p_k ↦ -p_k` and the
twisted one letter `ψ : p_k ↦ (q^k-1)z^{-k}`. So `HJO.Sym.completeHomog_add_alphabet` convolves the
two `h`-families: `HJO.Sym.plethNegate_completeHomog` gives `φ(h_m) = (-1)^m e_m`, and
`HJO.Sym.completeHomog_twist_letter` gives `ψ(h_s) = ϰ_s z^{-s}`. The other reading of the same
value, `χ(h_n) = β((-1)^n e_n)`, is again `HJO.Sym.plethNegate_completeHomog`, and comparing the two
is the claim once `(-1)^n(-1)^{n-s} = (-1)^s` is used.

## Implementation notes

The displacement is written in `w = z⁻¹`, so `z^{-r}` is `Polynomial.X ^ r` and the statement is an
identity of honest polynomials: the coefficient of `w^r` of `β(e_n)` is `(-1)^r ϰ_r e_{n-r}`, which
is what `HJO.Sym.coeff_plethHallLittlewood_elemSymm` reads off. The sum `∑_{r=0}^{n}`
is exhaustive: `β` raises no degree, so the coefficients beyond `r = n` vanish, and that is visible
in the statement rather than asserted separately.

The sign multiplication is done as `n + (n - s) = 2 * (n - s) + s`, valid because `s ≤ n` inside
the range, rather than as `2n - s` with a truncated subtraction: `(-1)^{2(n-s)+s} = (-1)^s` needs
no case analysis while `(-1)^{2n-s}` would.

## References

The lemma `HJO.Sym.plethHallLittlewood_elemSymm`, one of the Haglund--Morse--Zabrocki relations; and
the definitions `HJO.Sym.plethHallLittlewood`, `HJO.Sym.bkernel`, `HJO.Sym.plethNegate`,
`HJO.Sym.elemSymm`.
-/

@[expose] public section

namespace HJO.Sym

section Esymm

variable {K : Type*} [CommRing K] [Algebra ℚ K]

omit [Algebra ℚ K] in
/-- The kernel coefficient of the constant `q` read in `Λ[w]` is the constant of the kernel
coefficient of `q`: both branches of `HJO.Sym.bkernel` are built from `q` by ring operations, which
the two constant embeddings preserve. -/
private theorem bkernel_C_C (q : K) (s : ℕ) :
    bkernel (Polynomial.C (MvPolynomial.C q : Lambda K)) s
      = Polynomial.C (MvPolynomial.C (bkernel q s)) := by
  match s with
  | 0 => rw [bkernel_zero, bkernel_zero, map_one, map_one]
  | m + 1 => rw [bkernel_succ, bkernel_succ, map_mul, map_mul, map_pow, map_pow, map_sub, map_sub,
      map_one, map_one]

/-- **The displacement of an elementary symmetric function.**
`β(e_n) = ∑_{r=0}^{n}(-1)^r ϰ_r z^{-r} e_{n-r}`, written in `w = z⁻¹` so that `z^{-r}` is the
`r`-th power of the variable. -/
@[hjo "lem_cm_bshift_esymm"]
theorem plethHallLittlewood_elemSymm (q : K) (n : ℕ) :
    plethHallLittlewood q (elemSymm K n)
      = ∑ r ∈ Finset.range (n + 1),
          Polynomial.C ((-1) ^ r * MvPolynomial.C (bkernel q r) * elemSymm K (n - r)) *
            Polynomial.X ^ r := by
  set R := Polynomial (Lambda K) with hR
  -- `ω₋` read as a ring homomorphism, which is the shape the convolution principle composes with.
  have hnegp : ∀ j : ℕ, (plethNegate K : Lambda K →+* Lambda K) (powerSum K j)
      = -powerSum K j := fun j => plethNegate_powerSum K j
  have hnegh : ∀ m : ℕ, (plethNegate K : Lambda K →+* Lambda K) (completeHomog K m)
      = (-1) ^ m * elemSymm K m := fun m => plethNegate_completeHomog K m
  -- The negated alphabet, the twisted one letter, and their sum.
  set φ : Lambda K →+* R :=
    (Polynomial.C : Lambda K →+* R).comp (plethNegate K : Lambda K →+* Lambda K) with hφ
  set ψ : Lambda K →+* R :=
    MvPolynomial.eval₂Hom ((Polynomial.C : Lambda K →+* R).comp
      (MvPolynomial.C : K →+* Lambda K))
      (fun i => Polynomial.C (MvPolynomial.C (q ^ (i + 1) - 1) : Lambda K) *
        Polynomial.X ^ (i + 1)) with hψ
  set χ : Lambda K →+* R :=
    (plethHallLittlewood q : Lambda K →+* R).comp (plethNegate K : Lambda K →+* Lambda K) with hχ
  have hφp : ∀ j : ℕ, φ (powerSum K j) = -Polynomial.C (powerSum K j) := by
    intro j
    rw [hφ, RingHom.comp_apply, hnegp j, map_neg]
  have hψp : ∀ j : ℕ, 0 < j →
      ψ (powerSum K j)
        = Polynomial.C (MvPolynomial.C (q ^ j - 1) : Lambda K) * Polynomial.X ^ j := by
    intro j hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hψ, MvPolynomial.eval₂Hom_X']
  have hsplit : ∀ j : ℕ, 0 < j → χ (powerSum K j) = φ (powerSum K j) + ψ (powerSum K j) := by
    intro j hj
    rw [hχ, RingHom.comp_apply, hnegp j, map_neg, RingHom.coe_coe,
      plethHallLittlewood_powerSum q hj, hφp j, hψp j hj,
      show MvPolynomial.C (q ^ j - 1) = -MvPolynomial.C (1 - q ^ j) from by
        rw [map_sub, map_sub, map_one]; ring]
    rw [map_neg]
    ring
  -- The two `h`-families of the split.
  have hφh : ∀ m : ℕ, φ (completeHomog K m) = Polynomial.C ((-1) ^ m * elemSymm K m) := by
    intro m
    rw [hφ, RingHom.comp_apply, hnegh m]
  have hψtwist : ∀ j : ℕ, 0 < j →
      ψ (powerSum K j)
        = ((Polynomial.C (MvPolynomial.C q : Lambda K) : R) ^ j - 1) * (Polynomial.X : R) ^ j := by
    intro j hj
    have hQ : ((Polynomial.C (MvPolynomial.C q : Lambda K) : R) ^ j - 1)
        = Polynomial.C (MvPolynomial.C (q ^ j - 1) : Lambda K) := by
      simp only [map_sub, map_one, map_pow]
    rw [hψp j hj, hQ]
  have hψh : ∀ s : ℕ, ψ (completeHomog K s)
      = Polynomial.C (MvPolynomial.C (bkernel q s) : Lambda K) * Polynomial.X ^ s := by
    intro s
    have h := completeHomog_twist_letter ψ (Polynomial.C (MvPolynomial.C q : Lambda K))
      (Polynomial.X : R) hψtwist s
    rwa [bkernel_C_C] at h
  have hCneg : ∀ m : ℕ, ((-1 : R)) ^ m = Polynomial.C ((-1 : Lambda K) ^ m) := fun m => by
    rw [map_pow, map_neg, map_one]
  -- The convolution, and the other reading of the same value.
  have key : ((-1 : R)) ^ n * plethHallLittlewood q (elemSymm K n)
      = ∑ s ∈ Finset.range (n + 1),
          Polynomial.C ((-1) ^ (n - s) * elemSymm K (n - s)) *
            (Polynomial.C (MvPolynomial.C (bkernel q s) : Lambda K) * Polynomial.X ^ s) := by
    have hconv := completeHomog_add_alphabet φ ψ χ hsplit n
    have hleft : χ (completeHomog K n)
        = ((-1 : R)) ^ n * plethHallLittlewood q (elemSymm K n) := by
      rw [hχ, RingHom.comp_apply, hnegh n, RingHom.coe_coe, map_mul, map_pow, map_neg, map_one]
    rw [hleft] at hconv
    rw [hconv]
    exact Finset.sum_congr rfl fun s _ => by rw [hφh, hψh]
  -- Multiply by the unit `(-1)^n` and collapse the signs.
  have hsq : ((-1 : R)) ^ n * ((-1 : R)) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc plethHallLittlewood q (elemSymm K n)
      = ((-1 : R)) ^ n * (((-1 : R)) ^ n * plethHallLittlewood q (elemSymm K n)) := by
        rw [← mul_assoc, hsq, one_mul]
    _ = ((-1 : R)) ^ n *
          ∑ s ∈ Finset.range (n + 1),
            Polynomial.C ((-1) ^ (n - s) * elemSymm K (n - s)) *
              (Polynomial.C (MvPolynomial.C (bkernel q s) : Lambda K) * Polynomial.X ^ s) := by
        rw [key]
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [Finset.mem_range, Nat.lt_succ_iff] at hs
        have hsign : (-1 : Lambda K) ^ n * (-1) ^ (n - s) = (-1) ^ s := by
          rw [← pow_add, show n + (n - s) = 2 * (n - s) + s from by omega, pow_add, pow_mul,
            neg_one_sq, one_pow, one_mul]
        have hC : ((-1 : R)) ^ n *
              (Polynomial.C ((-1 : Lambda K) ^ (n - s) * elemSymm K (n - s)) *
                (Polynomial.C (MvPolynomial.C (bkernel q s) : Lambda K) * Polynomial.X ^ s))
            = Polynomial.C ((-1 : Lambda K) ^ n * ((-1) ^ (n - s) * elemSymm K (n - s)) *
                MvPolynomial.C (bkernel q s)) * Polynomial.X ^ s := by
          rw [hCneg n]
          simp only [map_mul]
          ring
        rw [hC, show (-1 : Lambda K) ^ n * ((-1) ^ (n - s) * elemSymm K (n - s)) *
            MvPolynomial.C (bkernel q s)
            = (-1) ^ s * MvPolynomial.C (bkernel q s) * elemSymm K (n - s) from by
          linear_combination (MvPolynomial.C (bkernel q s) * elemSymm K (n - s)) * hsign]

/-- **The coefficients of `HJO.Sym.plethHallLittlewood_elemSymm`**: the coefficient of `z^{-r}` in
`β(e_n)` is `(-1)^r ϰ_r e_{n-r}` for `r ≤ n` and `0` beyond, so the sum is exhaustive. -/
theorem coeff_plethHallLittlewood_elemSymm (q : K) (n r : ℕ) :
    (plethHallLittlewood q (elemSymm K n)).coeff r
      = if r ≤ n then (-1) ^ r * MvPolynomial.C (bkernel q r) * elemSymm K (n - r) else 0 := by
  rw [plethHallLittlewood_elemSymm, Polynomial.finsetSum_coeff]
  by_cases hr : r ≤ n
  · rw [ite_eq_left hr, Finset.sum_eq_single_of_mem r (Finset.mem_range.2 (by omega))]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_left rfl, mul_one]
    · intro s _ hsr
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        ite_eq_right (Ne.symm hsr), mul_zero]
  · rw [ite_eq_right hr, Finset.sum_eq_zero]
    intro s hs
    rw [Finset.mem_range, Nat.lt_succ_iff] at hs
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      ite_eq_right (show ¬(r = s) by omega), mul_zero]

end Esymm

end HJO.Sym
