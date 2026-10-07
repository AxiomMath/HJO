/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.CmCommutator

/-! # The displacement of an elementary symmetric function by one letter

`HJO.Sweep.qshift` adds the virtual letter `(q-1)y_i` to the alphabet. On the power sums that is
`p_r ↦ p_r + (q^r-1)y_i^r` by definition; on the *elementary* symmetric functions it is a finite
sum, and that sum is what every evaluation of `HJO.Sweep.dplus` on a vector with a `Λ`-coefficient
needs,
since `d_+` applies `τ_{k+1,k+1}` before the braid word.

The alternating form `Ω_n = (-1)^ne_n` is already proved as `HJO.Sweep.qshift_C_elemSymmAlt`
(`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`'s arithmetic). This file converts it to the `e_n`
the sweep's vectors are written in:

**`τ_{k,i}(e_n) = e_n + (1-q)∑_{j<n}(-y_i)^{j+1}e_{n-1-j}`**

(`HJO.Sweep.qshift_C_elemSymm`), at every index `i` and every `n`, and reads it off at `n = 1, 2, 3`
and `4`. At `n = 1` it is `e_1 + (q-1)y_i`, which is `HJO.Sweep.qshift_powerSum` at `r = 1` since
`e_1 = p_1`; the alternation of the signs starts at `n = 2`.

## Genericity

Nothing here reads a hypothesis: `HJO.Sweep.qshift` is an algebra map for every `q`, and the formula
is polynomial in `q`. In particular it is *not* false at `q = 1` — there it says `τ_{k,i}` fixes
every `e_n`, which is correct, the letter `(q-1)y_i` being empty. No statement mentions `u`.

## References

Transcribing E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §5.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial HJO.Sym

section Field

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- `(-1)^{m-1-j} = (-1)^m(-1)^{j+1}` for `j < m`: the two exponents differ by `2(j+1)`. This is the
whole of the sign bookkeeping between `Ω_n` and `e_n`. -/
private theorem neg_one_pow_sub_eq {m j : ℕ} (hj : j < m) :
    ((-1 : Total L) ^ (m - 1 - j)) = (-1) ^ m * (-1) ^ (j + 1) := by
  have h : (m - 1 - j) + 2 * (j + 1) = m + (j + 1) := by omega
  calc ((-1 : Total L) ^ (m - 1 - j))
      = (-1 : Total L) ^ (m - 1 - j) * (((-1 : Total L)) ^ 2) ^ (j + 1) := by simp
    _ = (-1 : Total L) ^ ((m - 1 - j) + 2 * (j + 1)) := by rw [← pow_mul, ← pow_add]
    _ = (-1 : Total L) ^ (m + (j + 1)) := by rw [h]
    _ = (-1 : Total L) ^ m * (-1) ^ (j + 1) := pow_add _ _ _

/-- `Ω_m = (-1)^me_m` read in the total space. -/
private theorem C_elemSymmAlt_natCast (m : ℕ) :
    (MvPolynomial.C (elemSymmAlt L (m : ℤ)) : Total L)
      = (-1) ^ m * MvPolynomial.C (elemSymm L m) := by
  rw [elemSymmAlt_natCast, map_mul, map_pow, map_neg, map_one]

/-- **`τ_{k,i}(e_n) = e_n + (1-q)∑_{j<n}(-y_i)^{j+1}e_{n-1-j}`**, at every index `i` and every `n`.

The displacement of `HJO.Sweep.qshift` on the elementary symmetric functions. It is
`HJO.Sweep.qshift_C_elemSymmAlt` — the same statement for `Ω_n = (-1)^ne_n`, where the signs are
absorbed into the coefficients — multiplied by `(-1)^n`; the `(-1)^{j+1}` that survives is packaged
into the base `-y_i`, which is what makes the two sides visibly alternate in the *variable* rather
than in a separate factor.

The letter being added is `(q-1)y_i`, and the leading correction is
`(1-q)(-y_i)e_{n-1} = (q-1)y_ie_{n-1}`, so the sign convention is that of Carlsson and Mellit.
Unconditional in `q`: at `q = 1` both sides are `e_n`. -/
theorem qshift_C_elemSymm (q : L) (i n : ℕ) :
    qshift q i (MvPolynomial.C (elemSymm L n) : Total L)
      = MvPolynomial.C (elemSymm L n)
        + scal (1 - q) * ∑ j ∈ Finset.range n,
            (-(auxVar i : Total L)) ^ (j + 1) * MvPolynomial.C (elemSymm L (n - 1 - j)) := by
  have key := qshift_C_elemSymmAlt (L := L) q i n
  have hterm : ∀ j ∈ Finset.range n,
      (auxVar i : Total L) ^ (j + 1)
          * MvPolynomial.C (elemSymmAlt L ((n : ℤ) - 1 - (j : ℤ)))
        = (-1 : Total L) ^ n * ((-(auxVar i : Total L)) ^ (j + 1)
            * MvPolynomial.C (elemSymm L (n - 1 - j))) := by
    intro j hj
    have hj' : j < n := Finset.mem_range.1 hj
    have hcast : ((n : ℤ) - 1 - (j : ℤ)) = ((n - 1 - j : ℕ) : ℤ) := by omega
    rw [hcast, C_elemSymmAlt_natCast, neg_one_pow_sub_eq (L := L) hj', neg_pow]
    ring
  have hne : ((-1 : Total L) ^ n) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have hqs : qshift q i ((-1 : Total L) ^ n * MvPolynomial.C (elemSymm L n))
      = (-1 : Total L) ^ n * qshift q i (MvPolynomial.C (elemSymm L n)) := by
    rw [map_mul, map_pow, map_neg, map_one]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, C_elemSymmAlt_natCast, hqs] at key
  refine mul_left_cancel₀ hne ?_
  rw [key]
  ring

/-- **`τ_{k,i}(e_1) = e_1 + (q-1)y_i`.** The `n = 1` case, which is also
`HJO.Sweep.qshift_powerSum` at `r = 1` because `e_1 = p_1`; the two routes agreeing is what fixes
the sign convention of `HJO.Sweep.qshift_C_elemSymm`. -/
theorem qshift_C_elemSymm_one (q : L) (i : ℕ) :
    qshift q i (MvPolynomial.C (elemSymm L 1) : Total L)
      = MvPolynomial.C (elemSymm L 1) + scal (q - 1) * auxVar i := by
  rw [qshift_C_elemSymm q i 1, Finset.sum_range_one]
  simp only [elemSymm_zero, map_one, mul_one, show (1 : ℕ) - 1 - 0 = 0 from rfl]
  rw [show (scal (1 - q) : Total L) = -scal (q - 1) from by
    rw [show (1 : L) - q = -(q - 1) from by ring, scal_neg]]
  ring

/-- **`τ_{k,i}(e_2) = e_2 + (q-1)(y_ie_1 - y_i^2)`.** -/
theorem qshift_C_elemSymm_two (q : L) (i : ℕ) :
    qshift q i (MvPolynomial.C (elemSymm L 2) : Total L)
      = MvPolynomial.C (elemSymm L 2)
        + scal (q - 1) * ((auxVar i : Total L) * MvPolynomial.C (elemSymm L 1)
            - (auxVar i : Total L) ^ 2) := by
  rw [qshift_C_elemSymm q i 2, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [elemSymm_zero, map_one, show (2 : ℕ) - 1 - 0 = 1 from rfl,
    show (2 : ℕ) - 1 - 1 = 0 from rfl, mul_one]
  rw [show (scal (1 - q) : Total L) = -scal (q - 1) from by
    rw [show (1 : L) - q = -(q - 1) from by ring, scal_neg]]
  ring

/-- **`τ_{k,i}(e_3) = e_3 + (q-1)(y_ie_2 - y_i^2e_1 + y_i^3)`**, the displacement of `e_3` — the
first coefficient a width-`3` vector of the sweep can carry. -/
theorem qshift_C_elemSymm_three (q : L) (i : ℕ) :
    qshift q i (MvPolynomial.C (elemSymm L 3) : Total L)
      = MvPolynomial.C (elemSymm L 3)
        + scal (q - 1) * ((auxVar i : Total L) * MvPolynomial.C (elemSymm L 2)
            - (auxVar i : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1)
            + (auxVar i : Total L) ^ 3) := by
  rw [qshift_C_elemSymm q i 3, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [elemSymm_zero, map_one, show (3 : ℕ) - 1 - 0 = 2 from rfl,
    show (3 : ℕ) - 1 - 1 = 1 from rfl, show (3 : ℕ) - 1 - 2 = 0 from rfl, mul_one]
  rw [show (scal (1 - q) : Total L) = -scal (q - 1) from by
    rw [show (1 : L) - q = -(q - 1) from by ring, scal_neg]]
  ring

/-- **`τ_{k,i}(e_4) = e_4 + (q-1)(y_ie_3 - y_i^2e_2 + y_i^3e_1 - y_i^4)`**, the displacement of
`e_4` — the first coefficient a width-`4` vector of the sweep can carry. -/
theorem qshift_C_elemSymm_four (q : L) (i : ℕ) :
    qshift q i (MvPolynomial.C (elemSymm L 4) : Total L)
      = MvPolynomial.C (elemSymm L 4)
        + scal (q - 1) * ((auxVar i : Total L) * MvPolynomial.C (elemSymm L 3)
            - (auxVar i : Total L) ^ 2 * MvPolynomial.C (elemSymm L 2)
            + (auxVar i : Total L) ^ 3 * MvPolynomial.C (elemSymm L 1)
            - (auxVar i : Total L) ^ 4) := by
  rw [qshift_C_elemSymm q i 4, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp only [elemSymm_zero, map_one, show (4 : ℕ) - 1 - 0 = 3 from rfl,
    show (4 : ℕ) - 1 - 1 = 2 from rfl, show (4 : ℕ) - 1 - 2 = 1 from rfl,
    show (4 : ℕ) - 1 - 3 = 0 from rfl, mul_one]
  rw [show (scal (1 - q) : Total L) = -scal (q - 1) from by
    rw [show (1 : L) - q = -(q - 1) from by ring, scal_neg]]
  ring

end Field

end HJO.Sweep

end
