/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.OperatorStable
public import HJO.Macdonald.SplitCoeff

/-! # The `q`-shift under `splitAt`

The `q`-shift `T_{q,x_i}` of `HJO.Mac.qShift` is an automorphism of the fraction field, but on
polynomials it is `MvPolynomial.rescaleEquiv (Pi.mulSingle i q)` (`HJO.Mac.qShift_algebraMap`), and
that is the form the operator identity `HJO.Mac.macOpNum` is written in. This file says what
`HJO.Mac.splitAt t` does to it, which is the `T_q` half of Step 2 of the proof of
`HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`:

* at the split letter, `T_{q,x_t}f = ∑_k q^k x_t^k g_k`, so the coefficient of `x_t^k` is scaled by
  `q^k` — `HJO.Mac.coeff_splitAt_rescaleEquiv_self`;
* at any other letter, `T_{q,x_i}` fixes `x_t` and carries the coefficient ring to itself, so
  `T_{q,x_i}f = ∑_k x_t^k T_{q,x_i}g_k` — `HJO.Mac.coeff_splitAt_rescaleEquiv_of_ne`, where the
  shift on the right is the rescaling of the small alphabet at the letter `⟨i, _⟩`.

Both are read off `HJO.Mac.splitAt_coeff_coeff` together with the coefficient law for a rescaling at
a single letter, `HJO.Mac.coeff_rescaleEquiv_mulSingle`, which is
`HJO.Mac.coeff_rescaleEquiv` with the product over the support collapsed: the factors away from `i`
are `1`, and at `i` the factor is `q^{e i}` whether or not `i` is in the support, since `e i = 0`
there.

## Main results

* `HJO.Mac.coeff_rescaleEquiv_mulSingle`: `coeff e (rescaleEquiv (Pi.mulSingle i q) p)`
  `= coeff e p * q^(e i)`.
* `HJO.Mac.coeff_splitAt_rescaleEquiv_self`.
* `HJO.Mac.coeff_splitAt_rescaleEquiv_of_ne`.

## References

The file supplies the `T_q` half of Step 2 of the proof of
`HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`, on the definition `HJO.Mac.qShift`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

variable {σ K : Type*} [Field K] [DecidableEq σ]

/-! ### Rescaling one variable, read on a coefficient -/

/-- **The coefficient law for a rescaling at a single letter.** `HJO.Mac.coeff_rescaleEquiv` with
the product over the support collapsed: away from `i` the factor is `1`, and at `i` it is
`q^(e i)` — which is also correct when `i` is outside the support, `e i` being `0` there. -/
theorem coeff_rescaleEquiv_mulSingle (q : Kˣ) (i : σ) (e : σ →₀ ℕ) (p : MvPolynomial σ K) :
    coeff e (rescaleEquiv (Pi.mulSingle i q) p) = coeff e p * (q : K) ^ e i := by
  rw [coeff_rescaleEquiv]
  congr 1
  rcases eq_or_ne (e i) 0 with h0 | h0
  · rw [h0, pow_zero, Finset.prod_eq_one]
    intro j hj
    rcases eq_or_ne j i with rfl | hji
    · exact absurd (Finsupp.mem_support_iff.1 hj) (by simpa using h0)
    · simp [hji]
  · rw [Finset.prod_eq_single i]
    · simp
    · exact fun j _ hji => by simp [hji]
    · exact fun hi => absurd (Finsupp.mem_support_iff.2 h0) hi

/-! ### The shift under the split -/

/-- **The shift at the split letter scales the coefficient of `x_t^k` by `q^k`.** This is
`T_{q,x_n}f = ∑_k q^k x_n^k g_k`, whose coefficient of `x_n^r` is `q^r g`. -/
theorem coeff_splitAt_rescaleEquiv_self (q : Kˣ) (t : σ) (p : MvPolynomial σ K) (k : ℕ) :
    Polynomial.coeff (splitAt t (rescaleEquiv (Pi.mulSingle t q) p)) k
      = (q : K) ^ k • Polynomial.coeff (splitAt t p) k := by
  refine MvPolynomial.ext _ _ fun m => ?_
  have he : (Finsupp.mapDomain Subtype.val m + Finsupp.single t k) t = k := by
    rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ (by simp),
      Finsupp.single_eq_same, zero_add]
  rw [splitAt_coeff_coeff, coeff_rescaleEquiv_mulSingle, he, coeff_smul, splitAt_coeff_coeff,
    smul_eq_mul, mul_comm]

/-- **The shift at any other letter acts on the coefficients.** `T_{q,x_i}` fixes `x_t` and carries
`𝕜[x_b : b ≠ t]` to itself, so the `T_{q,x_i}f = ∑_k x_n^k T_{q,x_i}g_k`; on the right
the shift is the rescaling of the small alphabet at `⟨i, _⟩`. -/
theorem coeff_splitAt_rescaleEquiv_of_ne (q : Kˣ) {i t : σ} (h : i ≠ t) (p : MvPolynomial σ K)
    (k : ℕ) :
    Polynomial.coeff (splitAt t (rescaleEquiv (Pi.mulSingle i q) p)) k
      = rescaleEquiv (Pi.mulSingle (⟨i, h⟩ : {b : σ // b ≠ t}) q)
          (Polynomial.coeff (splitAt t p) k) := by
  refine MvPolynomial.ext _ _ fun m => ?_
  have hmd : Finsupp.mapDomain Subtype.val m i = m ⟨i, h⟩ :=
    Finsupp.mapDomain_apply Subtype.val_injective m ⟨i, h⟩
  have he : (Finsupp.mapDomain Subtype.val m + Finsupp.single t k) i = m ⟨i, h⟩ := by
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne h, add_zero, hmd]
  simp only [coeff_rescaleEquiv_mulSingle, splitAt_coeff_coeff, he]

end HJO.Mac

end
