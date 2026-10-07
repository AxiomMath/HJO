/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.ShiftEsymm
public import HJO.Shuffle.MellitShiftDop
public meta import HJO.Attr

/-! # The kernel of the basic operator in closed form

The displacement `δ = f[X + M/z]` of `HJO.Sym.plethShift` carries an elementary symmetric function
to `δ(e_n) = ∑_{s ≤ n} e_{n-s} κ(e_s) w^s` (`HJO.Bglx.plethShift_elemSymm`), with `κ` the
parameter plethysm `HJO.Bglx.paramPleth` at `M = (1-q)(1-u)`. Everything a product `D_mD_n` of
two basic operators does is governed by that single family, and this file computes it:

`κ(e_0) = 1`, and `κ(e_{s+1}) = (-1)^s M h_s(q,u)` for `s ≥ 0`,

with `h_s(q,u) = ∑_{i ≤ s} q^i u^{s-i}` the complete homogeneous function of the two parameters.
Equivalently, the signed family `λ_r = (-1)^r κ(e_r)`, the one the *alternating* elementary family
`HJO.Sym.esymmSigned` of `HJO.Sym.DopInt` pairs against — is

`λ_0 = 1`, `λ_{r+1} = -M h_r(q,u)`,

which is the coefficientwise form of `(1-x)(1-qux)/((1-qx)(1-ux)) = 1 - Mx/((1-qx)(1-ux))`.

**This is where the factor `M` in the `(a,1)` column's identity comes from**: every member of the
kernel above the zeroth carries `M` as a factor, and nothing else in the operator algebra does.

## Main definitions

* `HJO.Sym.hsym2` — `h_s(q,u)`, the complete homogeneous function of the two parameters.
* `HJO.Sym.mkernel` — `λ_r`, the kernel of the displacement read against `HJO.Sym.esymmSigned`.

## Main results

* `HJO.Sym.paramPleth_elemSymm_eq_mkernel` — `κ(e_r) = (-1)^r λ_r`, the closed form. Proved from
  the three-term recursion `HJO.Bglx.paramPleth_elemSymm_add_two` by a two-step induction.
* `HJO.Sym.sum_pow_mul_mkernel` — the convolution `∑_{l ≤ n} (qu)^l λ_{n-l} = h_n - h_{n-1}`,
  the scalar identity the `(a,1)` column's bookkeeping runs on.
* `HJO.Sym.plethShift_esymmSigned` — the displacement of the alternating family:
  `δ(c_m) = ∑_r λ_r c_{m-r} w^r` at every **integer** `m`.
* `HJO.Sym.dopInt_mul_esymmSigned` — `D_i(A c_m) = ∑_r λ_r c_{m-r} D_{i+r}(A)`, which is the
  rule by which a product of two basic operators unfolds.

## Implementation notes

**No hypothesis on `q` or `u`, and no `M ≠ 0`.** Every statement here is a polynomial identity in
the two parameters; `M` occurs only as a factor, never as a denominator.

**The recursion is the known one.** `HJO.Bglx.paramPleth_elemSymm_zero` already gives
`κ(e_{n+2}) + (q+u)κ(e_{n+1}) + qu κ(e_n) = [n = 0] qu`; the closed form is that recursion
solved, and the solution is checked against the two known special values `κ(e_1) = M`
(`HJO.Bglx.paramPleth_elemSymm_one_eq`) and `κ(e_2) = -(q+u)M`
(`HJO.Bglx.paramPleth_elemSymm_two_eq`) rather than only at the base of the induction.

**The integer index is the point.** `HJO.Bglx.plethShift_elemSymm` is stated for `e_n` with
`n : ℕ`; `HJO.Sym.plethShift_esymmSigned` restates it for the family `HJO.Sym.esymmSigned` at an
arbitrary integer index, where the members below `0` vanish, so that the expansion has one shape at
every index and the negative indices of `HJO.Sym.DopInt` are covered.
-/

@[expose] public section

namespace HJO.Sym

open HJO.Bglx

/-! ### The complete homogeneous functions of the two parameters -/

section Hsym

variable {K : Type*} [CommRing K]

/-- `h_n(q,u) = ∑_{i=0}^{n} q^i u^{n-i}`, the complete homogeneous function of the two parameters:
the coefficient of `x^n` in `1/((1-qx)(1-ux))`. -/
def hsym2 (q u : K) (n : ℕ) : K := ∑ i ∈ Finset.range (n + 1), q ^ i * u ^ (n - i)

@[simp] theorem hsym2_zero (q u : K) : hsym2 q u 0 = 1 := by
  rw [hsym2, Finset.sum_range_one]
  simp

@[simp] theorem hsym2_one (q u : K) : hsym2 q u 1 = q + u := by
  rw [hsym2, Finset.sum_range_succ, Finset.sum_range_one]
  simp [add_comm]

/-- **Peeling off the top term**: `h_{n+1} = q^{n+1} + u h_n`. -/
theorem hsym2_succ (q u : K) (n : ℕ) : hsym2 q u (n + 1) = q ^ (n + 1) + u * hsym2 q u n := by
  rw [hsym2, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, add_comm, hsym2,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  rw [show n + 1 - i = (n - i) + 1 from by omega, pow_succ]
  ring

/-- **The three-term recursion**: `h_{n+2} = (q+u)h_{n+1} - qu h_n`, which is
`(1-qx)(1-ux) · ∑ h_n x^n = 1`. -/
theorem hsym2_add_two (q u : K) (n : ℕ) :
    hsym2 q u (n + 2) = (q + u) * hsym2 q u (n + 1) - q * u * hsym2 q u n := by
  have h1 : hsym2 q u (n + 2) = q ^ (n + 1 + 1) + u * hsym2 q u (n + 1) := by
    rw [show n + 2 = n + 1 + 1 from rfl]; exact hsym2_succ q u (n + 1)
  rw [h1, hsym2_succ q u n]
  ring

end Hsym

/-! ### The kernel of the displacement -/

section Mkernel

variable {K : Type*} [CommRing K]

/-- **The kernel of the displacement**, read against the *alternating* elementary family: `λ_0 = 1`
and `λ_{r+1} = -M h_r(q,u)` with `M = (1-q)(1-u)`.

These are the coefficients of `(1-x)(1-qux)/((1-qx)(1-ux)) = 1 - Mx/((1-qx)(1-ux))`, and
`HJO.Sym.paramPleth_elemSymm_eq_mkernel` identifies them with `(-1)^r κ(e_r)`. -/
def mkernel (q u : K) : ℕ → K
  | 0 => 1
  | r + 1 => -((1 - q) * (1 - u)) * hsym2 q u r

@[simp] theorem mkernel_zero (q u : K) : mkernel q u 0 = 1 := rfl

@[simp] theorem mkernel_succ (q u : K) (r : ℕ) :
    mkernel q u (r + 1) = -((1 - q) * (1 - u)) * hsym2 q u r := rfl

end Mkernel

/-! ### The closed form of the kernel -/

section Closed

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- **The kernel in closed form**: `κ(e_r) = (-1)^r λ_r`, i.e. `κ(e_0) = 1` and
`κ(e_{s+1}) = (-1)^s M h_s(q,u)`.

The three-term recursion `HJO.Bglx.paramPleth_elemSymm_zero`
(`HJO.Bglx.paramPleth_elemSymm_add_two`) determines the family from its two first members, and the
right-hand side satisfies the same recursion by `HJO.Sym.hsym2_add_two`; the induction is two-step,
carrying the statement at `r` and at `r+1` together. -/
@[hjo "lem_mellit_column_dop_zero"]
theorem paramPleth_elemSymm_eq_mkernel (q u : K) (r : ℕ) :
    paramPleth q u (elemSymm K r) = (-1 : K) ^ r * mkernel q u r := by
  suffices h : ∀ n : ℕ, paramPleth q u (elemSymm K n) = (-1 : K) ^ n * mkernel q u n
      ∧ paramPleth q u (elemSymm K (n + 1)) = (-1 : K) ^ (n + 1) * mkernel q u (n + 1) from
    (h r).1
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [paramPleth_elemSymm_zero, mkernel_zero, pow_zero, mul_one]
    · have h := paramPleth_elemSymm_one (K := K) q u
      rw [paramPleth_elemSymm_zero] at h
      rw [Nat.zero_add, mkernel_succ, hsym2_zero, pow_one]
      linear_combination h
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hrec := paramPleth_elemSymm_add_two (K := K) q u n
    have hn : paramPleth q u (elemSymm K (n + 1 + 1))
        = (if n = 0 then q * u else 0) - (q + u) * ((-1 : K) ^ (n + 1) * mkernel q u (n + 1))
          - q * u * ((-1 : K) ^ n * mkernel q u n) := by
      rw [← ih.1, ← ih.2, show n + 1 + 1 = n + 2 from rfl]
      linear_combination hrec
    rw [hn]
    match n with
    | 0 =>
      rw [mkernel_succ, mkernel_zero, hsym2_zero, mkernel_succ, hsym2_one]
      norm_num
      ring
    | t + 1 =>
      rw [show t + 1 + 1 + 1 = t + 1 + 2 from rfl, mkernel_succ, mkernel_succ, mkernel_succ,
        hsym2_add_two q u t, ite_eq_right (show ¬(t + 1 = 0) by omega)]
      rw [pow_succ, pow_succ]
      ring

end Closed

/-! ### The scalar convolution the column identity runs on -/

section Convolution

variable {K : Type*} [CommRing K]

/-- **The convolution of the kernel with the geometric series in `qu`**:
`∑_{l=0}^{n+1} (qu)^l λ_{n+1-l} = h_{n+1} - h_n`.

This is the coefficientwise form of `K_M(x)/(1-qux) = (1-x)/((1-qx)(1-ux))`, and it is the whole
scalar content of the `(a,1)` column's identity: the `M` carried by every `λ_{r+1}` is exactly
absorbed, leaving a difference of two complete homogeneous functions. -/
theorem sum_pow_mul_mkernel (q u : K) (n : ℕ) :
    ∑ l ∈ Finset.range (n + 2), (q * u) ^ l * mkernel q u (n + 1 - l)
      = hsym2 q u (n + 1) - hsym2 q u n := by
  induction n with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [hsym2_zero, hsym2_one]
    ring
  | succ n ih =>
    have hsplit : ∑ l ∈ Finset.range (n + 3), (q * u) ^ l * mkernel q u (n + 2 - l)
        = mkernel q u (n + 2)
          + (q * u) * ∑ l ∈ Finset.range (n + 2), (q * u) ^ l * mkernel q u (n + 1 - l) := by
      rw [Finset.sum_range_succ' (fun l => (q * u) ^ l * mkernel q u (n + 2 - l)) (n + 2),
        Finset.mul_sum, add_comm]
      congr 1
      · simp
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [show n + 2 - (l + 1) = n + 1 - l from by omega, pow_succ]
        ring
    rw [show n + 1 + 2 = n + 3 from rfl, hsplit, ih,
      show n + 1 + 1 = n + 2 from rfl, mkernel_succ, hsym2_add_two q u n]
    ring

end Convolution

/-! ### The displacement of the alternating elementary family -/

section Shift

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The displacement of the alternating elementary family at an integer index**:

`δ(c_m) = ∑_{r ≥ 0} λ_r c_{m-r} w^r`,

where `c` is `HJO.Sym.esymmSigned` — `(-1)^n e_n` above `0` and `0` below — and `λ` is
`HJO.Sym.mkernel`. Any range covering `m` gives the whole sum: the terms with `r > m` have
`c_{m-r} = 0`, and at `m < 0` both sides are `0`.

This is `HJO.Bglx.plethShift_elemSymm` with the signs folded in and the index extended to `ℤ`,
which
is the shape the integer-indexed `HJO.Sym.DopInt` of `HJO.Sym.DopInt` reads. -/
theorem plethShift_esymmSigned (q u : K) (m : ℤ) (R : ℕ) (hR : m ≤ (R : ℤ)) :
    plethShift q u (esymmSigned K m)
      = ∑ r ∈ Finset.range (R + 1),
          Polynomial.C (MvPolynomial.C (mkernel q u r) * esymmSigned K (m - r))
            * Polynomial.X ^ r := by
  rcases lt_or_ge m 0 with hm | hm
  · rw [esymmSigned_of_neg hm, map_zero, Finset.sum_eq_zero]
    intro r _
    rw [esymmSigned_of_neg (by omega : m - (r : ℤ) < 0), mul_zero, map_zero, zero_mul]
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
  have hnR : n ≤ R := by exact_mod_cast hR
  have htrunc : ∑ r ∈ Finset.range (R + 1),
        Polynomial.C (MvPolynomial.C (mkernel q u r) * esymmSigned K ((n : ℤ) - r))
          * Polynomial.X ^ r
      = ∑ r ∈ Finset.range (n + 1),
        Polynomial.C (MvPolynomial.C (mkernel q u r) * esymmSigned K ((n : ℤ) - r))
          * Polynomial.X ^ r := by
    have hsub : Finset.range (n + 1) ⊆ Finset.range (R + 1) := fun x hx =>
      Finset.mem_range.2 (by
        have := Finset.mem_range.1 hx
        omega)
    refine (Finset.sum_subset hsub ?_).symm
    intro r _ hr
    rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hr
    rw [esymmSigned_of_neg (by omega : (n : ℤ) - (r : ℤ) < 0), mul_zero, map_zero, zero_mul]
  rw [htrunc, esymmSigned_natCast, map_mul, map_pow, map_neg, map_one, plethShift_elemSymm q u n,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hr
  have hsign : (-1 : Lambda K) ^ n * (-1) ^ r = (-1) ^ (n - r) := by
    rw [← pow_add, show n + r = 2 * r + (n - r) from by omega, pow_add, pow_mul, neg_one_sq,
      one_pow, one_mul]
  have hc : esymmSigned K ((n : ℤ) - (r : ℤ))
      = (-1 : Lambda K) ^ (n - r) * elemSymm K (n - r) := by
    rw [show (n : ℤ) - (r : ℤ) = ((n - r : ℕ) : ℤ) from by omega, esymmSigned_natCast]
  have hCneg : ((-1 : Polynomial (Lambda K))) ^ n = Polynomial.C ((-1 : Lambda K) ^ n) := by
    rw [map_pow, map_neg, map_one]
  have hval : (-1 : Lambda K) ^ n
        * (elemSymm K (n - r) * MvPolynomial.C ((-1 : K) ^ r * mkernel q u r))
      = MvPolynomial.C (mkernel q u r) * ((-1 : Lambda K) ^ (n - r) * elemSymm K (n - r)) := by
    rw [map_mul, map_pow, map_neg, map_one]
    linear_combination (elemSymm K (n - r) * MvPolynomial.C (mkernel q u r)) * hsign
  rw [hCneg, hc, paramPleth_elemSymm_eq_mkernel q u r,
    show (Polynomial.C ((-1 : Lambda K) ^ n) : Polynomial (Lambda K))
        * (Polynomial.C (elemSymm K (n - r) * MvPolynomial.C ((-1 : K) ^ r * mkernel q u r))
            * Polynomial.X ^ r)
      = Polynomial.C ((-1 : Lambda K) ^ n
          * (elemSymm K (n - r) * MvPolynomial.C ((-1 : K) ^ r * mkernel q u r)))
        * Polynomial.X ^ r from by simp only [Polynomial.C_mul]; ring,
    hval]

end Shift

/-! ### A basic operator against a member of the alternating family -/

section Unfold

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The one rule by which a product of two basic operators unfolds**:

`D_i(A · c_m) = ∑_{r ≥ 0} λ_r c_{m-r} D_{i+r}(A)`,

for every `A ∈ Λ` and all integers `i, m`, with `c` the alternating elementary family
`HJO.Sym.esymmSigned` and `λ` the kernel `HJO.Sym.mkernel`. Any range covering `m` is the whole
sum.

The displacement is an algebra map, so it splits the product; `HJO.Sym.plethShift_esymmSigned`
expands the second factor as `∑_r λ_r c_{m-r} w^r`, and a factor `g w^r` pulled out of a pairing
takes `g` outside and reads the family `r` places further along
(`HJO.Sym.coeffPairing_C_mul_X_pow_mul`) — `r` places further along is the basic operator at the
index `i + r`. -/
theorem dopInt_mul_esymmSigned (q u : K) (i m : ℤ) (R : ℕ) (hR : m ≤ (R : ℤ))
    (A : Lambda K) :
    DopInt q u i (A * esymmSigned K m)
      = ∑ r ∈ Finset.range (R + 1),
          MvPolynomial.C (mkernel q u r) * esymmSigned K (m - r) * DopInt q u (i + r) A := by
  change coeffPairing (fun j : ℕ => esymmSigned K (i + j))
      (plethShift q u (A * esymmSigned K m)) = _
  rw [map_mul, plethShift_esymmSigned q u m R hR, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [show plethShift q u A
        * (Polynomial.C (MvPolynomial.C (mkernel q u r) * esymmSigned K (m - r))
          * Polynomial.X ^ r)
      = Polynomial.C (MvPolynomial.C (mkernel q u r) * esymmSigned K (m - r))
        * Polynomial.X ^ r * plethShift q u A from by ring,
    coeffPairing_C_mul_X_pow_mul _ _ r (fun j : ℕ => esymmSigned K (i + j))
      (fun j : ℕ => esymmSigned K (i + (r : ℤ) + j)) (fun j => by push_cast; ring_nf)]
  rfl

end Unfold

end HJO.Sym
