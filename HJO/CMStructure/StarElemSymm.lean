/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.StarConjRel1
public meta import HJO.Attr

/-! # `d^*_+` on the elementary symmetric functions

`d^*_+` acts on the constants of the total space as the plethystic shift by the virtual alphabet
`quy_1 - uy_1` (`HJO.Sweep.dplusStar_C_eq_starGamma`), a difference of two one-letter alphabets.
On the power sums that shift is `p_r ↦ p_r + (q^r-1)(uy_1)^r`
(`HJO.Sweep.dplusStarAlg_C_powerSum`); this file computes it on the *elementary* family, which is
the basis the slope computations are carried out in, and records that `d^*_+` is multiplicative, so
that a product of elementary functions is the product of the values.

## Main results

* `HJO.Sweep.dplusStar_mul`, `HJO.Sweep.dplusStar_C_mul`, `HJO.Sweep.dplusStar_C_prod`:
  `d^*_+` is multiplicative — on all of the total space, at every level, with no condition on `q`
  or `u`. The linear reading `HJO.Sweep.dplusStar` does not record this; the algebra reading
  `HJO.Sweep.dplusStarAlg` is the same map (`HJO.Sweep.dplusStarAlg_eq_dplusStar`, a `rfl`) and
  does.
* `HJO.Sweep.starGammaNeg_C_elemSymm`: `Γ_+(-uy_1)(e_n) = ∑_{m≤n} (-uy_1)^m e_{n-m}`, removing the
  letter `uy_1` from the alphabet.
* `HJO.Sweep.dplusStar_C_elemSymm`: **the expansion**,
  `d^*_+(e_n) = e_n - (q-1)∑_{i<n} (-uy_1)^{i+1} e_{n-1-i}`, i.e.
  `e_n + (q-1)uy_1e_{n-1} - (q-1)(uy_1)^2e_{n-2} + ⋯`.
* `HJO.Sweep.dplusStar_C_elemSymm_one`, `_two`, `_three`: the three values the `(3,4)` instance of
  `HJO.Mellit.lhsRewrite_sweepWitness`'s base case reads.
* `HJO.Sweep.dplusStar_C_elemSymm_one_mul_two`: `d^*_+(e_1e_2)`, the remaining `(3,4)` value, off
  multiplicativity.
* `HJO.Sweep.dplusStar_C_prod_elemSymm`: the general `e`-monomial, `d^*_+(∏_i e_{d_i})`.

## The shape of the answer, and why there is no condition on `q` or `u`

`e_n[X + a - b]` reads off the generating function `∏(1 + tx_i)`, which the two letters multiply by
`(1+ta)/(1+tb)`; at `a = quy_1` and `b = uy_1` the coefficient of `t^m` for `m ≥ 1` is
`(-1)^{m-1}(q-1)(uy_1)^m`, which is the sum below. Nothing is inverted: the `1/(1+tb)` is a
*geometric series*, realised here by inverting the one-letter shift `Γ_+(uy_1)`, whose inverse
`Γ_+(-uy_1)` is proved unconditionally (`HJO.Sweep.starGammaNeg_starGammaPos`). So the expansion
holds at every `q` and every `u`, including `0` and `1`; the conditions
`q ∉ {0,1}`, `u ∉ {0,1}` enter only where it is used, from `HJO.Sweep.slopeOperator`'s `(qu)⁻¹`
and `HJO.Sym.Qop`'s `((1-q)(1-u))⁻¹`.

Cross-check against the power sums, which is how the sign was fixed rather than guessed: at
`n = 2`, `e_2 = (p_1^2 - p_2)/2` and `HJO.Sweep.dplusStarAlg_C_powerSum` give
`e_2 + (q-1)uy_1e_1 + ((q-1)^2 - (q^2-1))(uy_1)^2/2 = e_2 + (q-1)uy_1e_1 - (q-1)(uy_1)^2`; at
`n = 3`, `e_3 = (p_1^3 - 3p_1p_2 + 2p_3)/6` gives the `(uy_1)^3` coefficient
`((q-1)^3 - 3(q-1)(q^2-1) + 2(q^3-1))/6 = q-1`. Both agree with the formula.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L]

/-! ### `d^*_+` is multiplicative -/

section Mul

variable [Algebra ℚ L]

/-- **`d^*_+` is multiplicative**, on all of the total space, at every level, and with no condition
on `q` or `u`: it is the algebra map `HJO.Sweep.dplusStarAlg` read `𝕜`-linearly, and that reading is
a `rfl`. No membership in a piece `V_k` is needed — both factors of `d^*_+` are substitutions. -/
theorem dplusStar_mul (q u : L) (k : ℕ) (F G : Total L) :
    dplusStar q u k (F * G) = dplusStar q u k F * dplusStar q u k G := by
  rw [← dplusStarAlg_eq_dplusStar q u k (F * G), ← dplusStarAlg_eq_dplusStar q u k F,
    ← dplusStarAlg_eq_dplusStar q u k G, map_mul]

/-- **`d^*_+` of a product of constants is the product of the values.** The `Λ`-level reading of
`HJO.Sweep.dplusStar_mul`: `C` is a ring map, so a product in `Λ` is a product in the total
space. -/
theorem dplusStar_C_mul (q u : L) (k : ℕ) (f g : Sym.Lambda L) :
    dplusStar q u k (MvPolynomial.C (f * g))
      = dplusStar q u k (MvPolynomial.C f) * dplusStar q u k (MvPolynomial.C g) := by
  rw [show (MvPolynomial.C (f * g) : Total L)
      = (MvPolynomial.C f : Total L) * MvPolynomial.C g from map_mul _ _ _, dplusStar_mul]

/-- **`d^*_+` of a finite product of constants.** `HJO.Sweep.dplusStar_C_mul` at any number of
factors, which is what an `e`-monomial of arbitrary shape needs. -/
theorem dplusStar_C_prod {ι : Type*} (q u : L) (k : ℕ) (s : Finset ι) (f : ι → Sym.Lambda L) :
    dplusStar q u k (MvPolynomial.C (∏ i ∈ s, f i))
      = ∏ i ∈ s, dplusStar q u k (MvPolynomial.C (f i)) := by
  rw [show (MvPolynomial.C (∏ i ∈ s, f i) : Total L)
      = ∏ i ∈ s, (MvPolynomial.C (f i) : Total L) from map_prod _ _ _,
    ← dplusStarAlg_eq_dplusStar, map_prod]
  exact Finset.prod_congr rfl fun i _ => dplusStarAlg_eq_dplusStar q u k _

end Mul

/-! ### Removing the letter `uy_1` from the alphabet -/

section Neg

/-- `Γ_+(-uy_1)` fixes everything free of the alphabet. -/
theorem starGammaNeg_of_mem_auxSubalg (u : L) {Z : Total L} (hZ : Z ∈ auxSubalg L) :
    starGammaNeg u Z = Z := by
  rw [starGammaNeg_apply]
  exact alphabetShift_of_mem_auxSubalg _ hZ

/-- Pulling `-w` out of a shifted geometric sum. -/
private theorem sum_neg_pow_succ_mul (w : Total L) (n : ℕ) (g : ℕ → Total L) :
    ∑ i ∈ Finset.range n, (-w) ^ (i + 1) * g i
      = (-w) * ∑ i ∈ Finset.range n, (-w) ^ i * g i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_succ]
  ring

variable [Algebra ℚ L]

/-- **Removing one letter from the alphabet**: `e_n[X - w] = ∑_{m≤n} (-w)^me_{n-m}` at `w = uy_1`,
the geometric series `1/(1+tw)` read coefficientwise.

The proof does not apply the one-letter formula to `Γ_+(-uy_1)` — it cannot, since that shift's
family is `-(w^r)` and not `(-w)^r`. It *inverts* the one-letter formula instead: applying
`Γ_+(-uy_1)` to `Γ_+(uy_1)(e_{n+1}) = e_{n+1} + we_n` and using that the two shifts are mutually
inverse (`HJO.Sweep.starGammaNeg_starGammaPos`) turns the addition of the letter into the recursion
`E_{n+1} = e_{n+1} - wE_n`, whose solution is the alternating sum. -/
theorem starGammaNeg_C_elemSymm (u : L) (n : ℕ) :
    starGammaNeg u (MvPolynomial.C (Sym.elemSymm L n))
      = ∑ m ∈ Finset.range (n + 1),
          (-starLetter u) ^ m * MvPolynomial.C (Sym.elemSymm L (n - m)) := by
  induction n with
  | zero => simp [Sym.elemSymm_zero L]
  | succ n ih =>
    have hpos : starGammaPos u (MvPolynomial.C (Sym.elemSymm L (n + 1)))
        = MvPolynomial.C (Sym.elemSymm L (n + 1))
          + starLetter u * MvPolynomial.C (Sym.elemSymm L n) := by
      rw [starGammaPos_apply]
      exact alphabetShift_C_elemSymm_succ (starLetter u) n
    have happ := congrArg (starGammaNeg u) hpos
    rw [starGammaNeg_starGammaPos, map_add, map_mul,
      starGammaNeg_of_mem_auxSubalg u (starLetter_mem_auxSubalg u), ih] at happ
    have hval : starGammaNeg u (MvPolynomial.C (Sym.elemSymm L (n + 1)))
        = MvPolynomial.C (Sym.elemSymm L (n + 1))
          - starLetter u * ∑ m ∈ Finset.range (n + 1),
              (-starLetter u) ^ m * MvPolynomial.C (Sym.elemSymm L (n - m)) := by
      linear_combination -happ
    rw [hval, Finset.sum_range_succ'
      (fun m => (-starLetter u) ^ m * MvPolynomial.C (Sym.elemSymm L (n + 1 - m)))]
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right]
    rw [sum_neg_pow_succ_mul]
    ring

end Neg

/-! ### The expansion -/

section Expand

variable [Algebra ℚ L]

/-- **`d^*_+` on an elementary symmetric function**, at every level and with no condition on `q` or
`u`:
`d^*_+(e_n) = e_n - (q-1)∑_{i<n}(-uy_1)^{i+1}e_{n-1-i}`, that is,
`d^*_+(e_n) = e_n + (q-1)uy_1e_{n-1} - (q-1)(uy_1)^2e_{n-2} + ⋯ + (-1)^{n-1}(q-1)(uy_1)^n`.

`d^*_+` shifts the alphabet by `quy_1 - uy_1` (`HJO.Sweep.dplusStar_C_eq_starGamma`); adding the
dilated letter is `HJO.Sweep.alphabetShift_C_elemSymm_succ`, removing the undilated one is
`HJO.Sweep.starGammaNeg_C_elemSymm`, and the two geometric sums differ by the single factor
`q - 1`.

The level `k` is not read, exactly as in `HJO.Sweep.dplusStar_C_eq_starGamma`: on the constants
`d^*_+` is the same substitution at every level, so `d^*_+^{(0)} = d^*_+^{(1)}` here. -/
theorem dplusStar_C_elemSymm (q u : L) (k n : ℕ) :
    dplusStar q u k (MvPolynomial.C (Sym.elemSymm L n))
      = MvPolynomial.C (Sym.elemSymm L n)
        - scal (q - 1) * ∑ i ∈ Finset.range n,
            (-starLetter u) ^ (i + 1) * MvPolynomial.C (Sym.elemSymm L (n - 1 - i)) := by
  cases n with
  | zero =>
    rw [Sym.elemSymm_zero L, map_one, ← dplusStarAlg_eq_dplusStar, map_one]
    simp
  | succ m =>
    have hq : scal q * starLetter u ∈ auxSubalg L :=
      mul_mem (scal_mem_auxSubalg q) (starLetter_mem_auxSubalg u)
    have hQ : starGammaQ q u (MvPolynomial.C (Sym.elemSymm L (m + 1)))
        = MvPolynomial.C (Sym.elemSymm L (m + 1))
          + scal q * starLetter u * MvPolynomial.C (Sym.elemSymm L m) := by
      rw [starGammaQ_apply]
      exact alphabetShift_C_elemSymm_succ (scal q * starLetter u) m
    rw [dplusStar_C_eq_starGamma, hQ, map_add, map_mul, starGammaNeg_of_mem_auxSubalg u hq,
      starGammaNeg_C_elemSymm, starGammaNeg_C_elemSymm,
      Finset.sum_range_succ'
        (fun j => (-starLetter u) ^ j * MvPolynomial.C (Sym.elemSymm L (m + 1 - j)))]
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right, Nat.add_sub_cancel]
    rw [sum_neg_pow_succ_mul, scal_sub, scal_one]
    ring

/-- `d^*_+(e_1) = e_1 + (q-1)uy_1`. -/
theorem dplusStar_C_elemSymm_one (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (Sym.elemSymm L 1))
      = MvPolynomial.C (Sym.elemSymm L 1) + scal (q - 1) * starLetter u := by
  rw [dplusStar_C_elemSymm, Finset.sum_range_one]
  simp only [Nat.sub_self, Sym.elemSymm_zero L, map_one, mul_one]
  ring

/-- `d^*_+(e_2) = e_2 + (q-1)uy_1e_1 - (q-1)(uy_1)^2`. -/
theorem dplusStar_C_elemSymm_two (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (Sym.elemSymm L 2))
      = MvPolynomial.C (Sym.elemSymm L 2)
        + scal (q - 1) * starLetter u * MvPolynomial.C (Sym.elemSymm L 1)
        - scal (q - 1) * starLetter u ^ 2 := by
  rw [dplusStar_C_elemSymm, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [Sym.elemSymm_zero L]
  ring

/-- `d^*_+(e_3) = e_3 + (q-1)uy_1e_2 - (q-1)(uy_1)^2e_1 + (q-1)(uy_1)^3`. -/
theorem dplusStar_C_elemSymm_three (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (Sym.elemSymm L 3))
      = MvPolynomial.C (Sym.elemSymm L 3)
        + scal (q - 1) * starLetter u * MvPolynomial.C (Sym.elemSymm L 2)
        - scal (q - 1) * starLetter u ^ 2 * MvPolynomial.C (Sym.elemSymm L 1)
        + scal (q - 1) * starLetter u ^ 3 := by
  rw [dplusStar_C_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [Sym.elemSymm_zero L]
  ring

/-- **The `y_1`-graded form of `d^*_+(e_2) - e_2`**: `(q-1)ue_1·y_1 + (1-q)u^2·y_1^2`.

This is the element the second `z` of the slope word `β_{3,4} = yzyzy`
(`HJO.Mellit.slopeWord_three_four`) acts on, divided by the outer `y_1`, and it is the form
`HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C` reads: a sum of terms `y_1^m·Cf`. Its two
`y_1`-coefficients `(q-1)ue_1` and `(1-q)u^2` are exactly the pair the docstring of
`HJO/Shuffle/MellitQopThreeFour.lean` records from an exact-arithmetic `(3,4)` computation, so that
value is proved here. -/
theorem dplusStar_C_elemSymm_two_sub (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (Sym.elemSymm L 2)) - MvPolynomial.C (Sym.elemSymm L 2)
      = scal ((q - 1) * u) * (auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1)
        + scal ((1 - q) * u ^ 2) * (auxVar 1 : Total L) ^ 2 := by
  rw [dplusStar_C_elemSymm_two, starLetter]
  simp only [scal_mul, scal_sub, scal_one, scal_pow, mul_pow]
  ring

/-- **`d^*_+(e_1e_2)`**, the product value the `(3,4)` instance reads: the product of
`HJO.Sweep.dplusStar_C_elemSymm_one` and `HJO.Sweep.dplusStar_C_elemSymm_two`, off
multiplicativity. -/
theorem dplusStar_C_elemSymm_one_mul_two (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 2))
      = (MvPolynomial.C (Sym.elemSymm L 1) + scal (q - 1) * starLetter u)
        * (MvPolynomial.C (Sym.elemSymm L 2)
            + scal (q - 1) * starLetter u * MvPolynomial.C (Sym.elemSymm L 1)
            - scal (q - 1) * starLetter u ^ 2) := by
  rw [dplusStar_C_mul, dplusStar_C_elemSymm_one, dplusStar_C_elemSymm_two]

/-- **`d^*_+` on an arbitrary `e`-monomial**: the product over the factors of the expansion of each,
which is `HJO.Sweep.dplusStar_C_prod` at `HJO.Sweep.dplusStar_C_elemSymm`. -/
theorem dplusStar_C_prod_elemSymm {ι : Type*} (q u : L) (k : ℕ) (s : Finset ι) (d : ι → ℕ) :
    dplusStar q u k (MvPolynomial.C (∏ i ∈ s, Sym.elemSymm L (d i)))
      = ∏ i ∈ s, (MvPolynomial.C (Sym.elemSymm L (d i))
          - scal (q - 1) * ∑ j ∈ Finset.range (d i),
              (-starLetter u) ^ (j + 1) * MvPolynomial.C (Sym.elemSymm L (d i - 1 - j))) := by
  rw [dplusStar_C_prod]
  exact Finset.prod_congr rfl fun i _ => dplusStar_C_elemSymm q u k (d i)

end Expand

end HJO.Sweep
