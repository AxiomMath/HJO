/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The elementary symmetric functions of a sum of alphabets

The kernel of the BGLX symbol is read off the elementary symmetric functions of the *parameter
alphabet* `M = (1 - q)(1 - u)`, and the only way to compute with it is to let the alphabet be
additive. This file supplies that calculus at the level of `HJO.Sym.Lambda K`: a plethysm at an
alphabet is a `K`-algebra homomorphism out of `Lambda K`, an alphabet *sum* is the homomorphism
whose value on every power sum `p_j` is the sum of the two values, and the elementary symmetric
functions of a sum convolve.

From the convolution and the two one-letter alphabets — `p_j ↦ c ^ j`, whose elementary
symmetric functions are `1, c, 0, 0, …`, and `p_j ↦ -c ^ j`, whose elementary symmetric functions
are the powers `(-c) ^ n` — the three-term recursion for the coefficients `κ(e_n)` of the
parameter alphabet follows with no closed form computed: the two auxiliary homomorphisms
`kappaShiftHom` and `thetaHom` sit between `paramPleth` and the constant `1 + (qu) ^ j`, and
the identity `(1 - q ^ j)(1 - u ^ j) + q ^ j + u ^ j = 1 + (qu) ^ j` is what makes the middle
step an alphabet sum.

## Main definitions

* `HJO.Bglx.paramPleth`: the plethysm `κ` at the parameter alphabet `M`, the `K`-algebra
  homomorphism `Lambda K → K` sending `p_j` to `(1 - q ^ j) (1 - u ^ j)`.
* `HJO.Bglx.geomHom`: the plethysm at the one-letter alphabet `c`, sending `p_j` to `c ^ j`.
* `HJO.Bglx.kappaShiftHom`, `HJO.Bglx.thetaHom`: the two intermediate alphabets `M + c` and
  `1 + qu`, through which the recursion is obtained.

## Main statements

* `HJO.Bglx.map_elemSymm_add`: the elementary symmetric functions of a sum of alphabets are the
  convolution `e_n(A + B) = ∑_{s} e_{n-s}(A) e_s(B)`.
* `HJO.Bglx.map_elemSymm_geom`: a one-letter alphabet has `e_0 = 1`, `e_1 = c` and `e_n = 0`
  for `n ≥ 2`.
* `HJO.Bglx.map_elemSymm_negGeom`: the alphabet `p_j ↦ -c ^ j` has `e_n = (-c) ^ n`.
* `HJO.Bglx.paramPleth_elemSymm_zero`, `HJO.Bglx.paramPleth_elemSymm_one`,
  `HJO.Bglx.paramPleth_elemSymm_add_two`: the three cases of the three-term recursion
  `κ(e_n) + (q + u) κ(e_{n-1}) + qu κ(e_{n-2}) = [n = 2] qu`, read with `κ(e_m) = 0` for `m < 0`.

## Implementation notes

Everything rests on `HJO.Bglx.natCast_mul_map_elemSymm`, Newton's identity
`n e_n = ∑_{k<n} (-1)^k p_{k+1} e_{n-1-k}` pushed through an algebra homomorphism. The
definition `HJO.Sym.elemSymm` divides by `n`, so the clean statement multiplies by `n` instead;
`HJO.Bglx.cancel_natCast` then cancels `n`, which is invertible in `R` because it is invertible
in `K` (the instance `Algebra ℚ K`) and `R` is a `K`-algebra. No `Algebra ℚ R` instance is
needed: the inverse is produced as `algebraMap K R (algebraMap ℚ K (n : ℚ)⁻¹)`.

The convolution is proved by verifying that both sides satisfy the *same* Newton recursion,
which is `HJO.Bglx.natCast_mul_conv`. That identity is the combinatorial heart: splitting
`χ(p_{k+1})` into `φ(p_{k+1}) + ψ(p_{k+1})` gives two sums over the triangle
`{(k, s) : k + s < n}`, and the two groupings of that triangle — by `s`, and by `k + s` — turn
each into Newton's identity for one of `φ`, `ψ`. The regroupings are `Finset.sum_comm'` and
`Finset.sum_range_diag_flip`; the resulting coefficients `n - s` and `s` add up to `n`.

`HJO.Bglx.sum_conv_geom_trunc` is the truncation that makes the recursion finite: convolving
against an alphabet with only two nonzero elementary symmetric functions leaves two terms.
It is stated at `n = m + 1` so that its left-hand side is literally the right-hand side of
`map_elemSymm_add`, which keeps the rewrites syntactic.

`paramPleth` is `noncomputable` only because `MvPolynomial.aeval` is. No condition on `q` and
`u` appears anywhere: all of this is a polynomial identity in the two parameters.

## References

The reference for the lemmas `HJO.Bglx.map_elemSymm_add`, `HJO.Bglx.map_elemSymm_geom`,
`HJO.Bglx.map_elemSymm_negGeom` and `HJO.Bglx.paramPleth_elemSymm_zero`, and for the definition
`HJO.Bglx.paramPleth`, is F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new
plethystic operators in the theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7**
(2016) 671--714.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

/-! ### Newton's identity through an algebra homomorphism -/

/-- The elementary symmetric function of degree `0` is `1`, the base case of the Newton
recursion defining `HJO.Sym.elemSymm`. -/
lemma elemSymm_zero_eq_one (K : Type*) [CommRing K] [Algebra ℚ K] : elemSymm K 0 = 1 := by
  rw [elemSymm]

/-- The successor `m + 1`, viewed in a `K`-algebra `R`, is invertible, with inverse the image of
the rational `(m + 1)⁻¹`. This is the one place the hypothesis `Algebra ℚ K` is used. -/
lemma natCast_mul_algebraMap_inv {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R]
    [Algebra K R] (m : ℕ) :
    ((m : R) + 1) * algebraMap K R (algebraMap ℚ K (((m : ℚ) + 1)⁻¹)) = 1 := by
  have h : algebraMap K R (algebraMap ℚ K ((m : ℚ) + 1)) = (m : R) + 1 := by simp
  rw [← h, ← map_mul, ← map_mul, mul_inv_cancel₀ (by positivity), map_one, map_one]

/-- A nonzero natural number may be cancelled in a `K`-algebra, `K` being a `ℚ`-algebra. -/
lemma cancel_natCast {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R]
    [Algebra K R] {n : ℕ} (hn : n ≠ 0) {x y : R} (h : (n : R) * x = (n : R) * y) : x = y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hc : ((m + 1 : ℕ) : R) = (m : R) + 1 := by push_cast; ring
  rw [hc] at h
  calc x = (((m : R) + 1) * algebraMap K R (algebraMap ℚ K (((m : ℚ) + 1)⁻¹))) * x := by
        rw [natCast_mul_algebraMap_inv, one_mul]
    _ = algebraMap K R (algebraMap ℚ K (((m : ℚ) + 1)⁻¹)) * (((m : R) + 1) * x) := by ring
    _ = algebraMap K R (algebraMap ℚ K (((m : ℚ) + 1)⁻¹)) * (((m : R) + 1) * y) := by rw [h]
    _ = (((m : R) + 1) * algebraMap K R (algebraMap ℚ K (((m : ℚ) + 1)⁻¹))) * y := by ring
    _ = y := by rw [natCast_mul_algebraMap_inv, one_mul]

variable {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R] [Algebra K R]

/-- **Newton's identity through an algebra homomorphism.** For every `K`-algebra homomorphism
`φ` out of `Lambda K` and every `n ≥ 1`,
`n φ(e_n) = ∑_{k < n} (-1) ^ k φ(p_{k+1}) φ(e_{n-1-k})`. Stated with the factor `n` on the left
because `HJO.Sym.elemSymm` is defined by dividing by it. -/
lemma natCast_mul_map_elemSymm (φ : Lambda K →ₐ[K] R) {n : ℕ} (hn : 1 ≤ n) :
    (n : R) * φ (elemSymm K n)
      = ∑ k ∈ Finset.range n,
          (-1) ^ k * φ (powerSum K (k + 1)) * φ (elemSymm K (n - 1 - k)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hdef : elemSymm K (m + 1) = MvPolynomial.C (algebraMap ℚ K (((m : ℚ) + 1)⁻¹)) *
      ∑ k ∈ Finset.range (m + 1),
        (-1) ^ k * powerSum K (k + 1) * elemSymm K (m - k) := by rw [elemSymm]
  have hC : φ (MvPolynomial.C (algebraMap ℚ K (((m : ℚ) + 1)⁻¹)))
      = algebraMap K R (algebraMap ℚ K (((m : ℚ) + 1)⁻¹)) := by
    rw [← MvPolynomial.algebraMap_eq]; exact φ.commutes _
  have hterm : ∀ k ∈ Finset.range (m + 1),
      φ ((-1) ^ k * powerSum K (k + 1) * elemSymm K (m - k))
        = (-1) ^ k * φ (powerSum K (k + 1)) * φ (elemSymm K (m - k)) := by
    intro k _
    rw [map_mul, map_mul, map_pow, map_neg, map_one]
  rw [hdef, map_mul, map_sum, hC, Finset.sum_congr rfl hterm, ← mul_assoc,
    show ((m + 1 : ℕ) : R) = (m : R) + 1 from by push_cast; ring,
    natCast_mul_algebraMap_inv, one_mul]

/-! ### The elementary symmetric functions of a sum of alphabets -/

/-- Both sides of the convolution identity satisfy the same Newton recursion. This is the
combinatorial heart of `HJO.Bglx.map_elemSymm_add`: the triangle `{(k, s) : k + s < n}` is
grouped once by `s`, giving Newton's identity for `φ` at `n - s`, and once by `k + s`, giving
Newton's identity for `ψ` at `k + s + 1`; the two coefficients `n - s` and `s` add to `n`. -/
lemma natCast_mul_conv (φ ψ χ : Lambda K →ₐ[K] R)
    (hp : ∀ j : ℕ, 1 ≤ j → χ (powerSum K j) = φ (powerSum K j) + ψ (powerSum K j)) (n : ℕ) :
    (n : R) * ∑ s ∈ Finset.range (n + 1), φ (elemSymm K (n - s)) * ψ (elemSymm K s)
      = ∑ k ∈ Finset.range n, (-1) ^ k * χ (powerSum K (k + 1)) *
          ∑ s ∈ Finset.range (n - 1 - k + 1),
            φ (elemSymm K (n - 1 - k - s)) * ψ (elemSymm K s) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have key : ∀ k ∈ Finset.range (m + 1),
      (-1 : R) ^ k * χ (powerSum K (k + 1)) *
          ∑ s ∈ Finset.range (m - k + 1), φ (elemSymm K (m - k - s)) * ψ (elemSymm K s)
        = (∑ s ∈ Finset.range (m + 1 - k), (-1 : R) ^ k * φ (powerSum K (k + 1)) *
              (φ (elemSymm K (m - k - s)) * ψ (elemSymm K s)))
          + ∑ s ∈ Finset.range (m + 1 - k), (-1 : R) ^ k * ψ (powerSum K (k + 1)) *
              (φ (elemSymm K (m - k - s)) * ψ (elemSymm K s)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [hp (k + 1) (by omega), show m + 1 - k = m - k + 1 from by omega,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hS1 : ∑ k ∈ Finset.range (m + 1), ∑ s ∈ Finset.range (m + 1 - k),
        (-1 : R) ^ k * φ (powerSum K (k + 1)) * (φ (elemSymm K (m - k - s)) * ψ (elemSymm K s))
      = ∑ s ∈ Finset.range (m + 1 + 1),
          ((m + 1 - s : ℕ) : R) * (φ (elemSymm K (m + 1 - s)) * ψ (elemSymm K s)) := by
    have hcomm : ∑ k ∈ Finset.range (m + 1), ∑ s ∈ Finset.range (m + 1 - k),
          (-1 : R) ^ k * φ (powerSum K (k + 1)) * (φ (elemSymm K (m - k - s)) * ψ (elemSymm K s))
        = ∑ s ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (m + 1 - s),
          (-1 : R) ^ k * φ (powerSum K (k + 1)) *
            (φ (elemSymm K (m - k - s)) * ψ (elemSymm K s)) :=
      Finset.sum_comm' (fun k s => by simp only [Finset.mem_range]; omega)
    rw [hcomm]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hs
    have hrw : ((m + 1 - s : ℕ) : R) * (φ (elemSymm K (m + 1 - s)) * ψ (elemSymm K s))
        = ((m + 1 - s : ℕ) : R) * φ (elemSymm K (m + 1 - s)) * ψ (elemSymm K s) := by ring
    rw [hrw, natCast_mul_map_elemSymm φ (n := m + 1 - s) (by omega), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show m + 1 - s - 1 - k = m - k - s from by omega]
    ring
  have hS2 : ∑ k ∈ Finset.range (m + 1), ∑ s ∈ Finset.range (m + 1 - k),
        (-1 : R) ^ k * ψ (powerSum K (k + 1)) * (φ (elemSymm K (m - k - s)) * ψ (elemSymm K s))
      = ∑ s ∈ Finset.range (m + 1 + 1),
          ((s : ℕ) : R) * (φ (elemSymm K (m + 1 - s)) * ψ (elemSymm K s)) := by
    have hflip : ∑ t ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (t + 1),
          (-1 : R) ^ k * ψ (powerSum K (k + 1)) *
            (φ (elemSymm K (m - k - (t - k))) * ψ (elemSymm K (t - k)))
        = ∑ k ∈ Finset.range (m + 1), ∑ s ∈ Finset.range (m + 1 - k),
          (-1 : R) ^ k * ψ (powerSum K (k + 1)) *
            (φ (elemSymm K (m - k - s)) * ψ (elemSymm K s)) :=
      Finset.sum_range_diag_flip (m + 1) fun a b =>
        (-1 : R) ^ a * ψ (powerSum K (a + 1)) *
          (φ (elemSymm K (m - a - b)) * ψ (elemSymm K b))
    rw [← hflip]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    rw [show m + 1 - (t + 1) = m - t from by omega]
    have hrw : ((t + 1 : ℕ) : R) * (φ (elemSymm K (m - t)) * ψ (elemSymm K (t + 1)))
        = ((t + 1 : ℕ) : R) * ψ (elemSymm K (t + 1)) * φ (elemSymm K (m - t)) := by ring
    rw [hrw, natCast_mul_map_elemSymm ψ (n := t + 1) (by omega), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show m - k - (t - k) = m - t from by omega, show t + 1 - 1 - k = t - k from by omega]
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, hS1, hS2, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hsum : ((m + 1 - s : ℕ) : R) + ((s : ℕ) : R) = ((m + 1 : ℕ) : R) := by
    rw [← Nat.cast_add, show m + 1 - s + s = m + 1 from by omega]
  rw [← add_mul, hsum]

/-- **The elementary symmetric functions of a sum of alphabets.** If the plethysm `χ` sends every
power sum `p_j` to the sum of its values under `φ` and `ψ` — that is, if `χ` is evaluation at the
alphabet sum of those of `φ` and `ψ` — then the elementary symmetric functions convolve:
`e_n(A + B) = ∑_{s ≤ n} e_{n-s}(A) e_s(B)`. -/
@[hjo "lem_bglx_esymm_add"]
theorem map_elemSymm_add {R : Type*} [CommRing R] [Algebra K R]
    (φ ψ χ : Lambda K →ₐ[K] R)
    (h : ∀ j : ℕ, 1 ≤ j → χ (powerSum K j) = φ (powerSum K j) + ψ (powerSum K j)) (n : ℕ) :
    χ (elemSymm K n)
      = ∑ s ∈ Finset.range (n + 1), φ (elemSymm K (n - s)) * ψ (elemSymm K s) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [elemSymm_zero_eq_one]
    | m + 1 =>
      refine cancel_natCast (K := K) (n := m + 1) (by omega) ?_
      rw [natCast_mul_map_elemSymm χ (n := m + 1) (by omega), natCast_mul_conv φ ψ χ h]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [ih (m + 1 - 1 - k) (by omega)]

/-! ### The one-letter alphabets -/

/-- The elementary symmetric functions of a one-letter alphabet vanish beyond degree `1`: the
higher Newton terms cancel in pairs. -/
lemma map_elemSymm_eq_zero_of_two_le (c : R) (φ : Lambda K →ₐ[K] R)
    (h : ∀ j : ℕ, 1 ≤ j → φ (powerSum K j) = c ^ j) (he0 : φ (elemSymm K 0) = 1)
    (he1 : φ (elemSymm K 1) = c) (n : ℕ) : 2 ≤ n → φ (elemSymm K n) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
    refine cancel_natCast (K := K) (n := m + 1 + 1) (by omega) ?_
    rw [natCast_mul_map_elemSymm φ (n := m + 1 + 1) (by omega), mul_zero]
    have hlow : ∀ k ∈ Finset.range m,
        (-1 : R) ^ k * φ (powerSum K (k + 1)) * φ (elemSymm K (m + 1 + 1 - 1 - k)) = 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [ih (m + 1 + 1 - 1 - k) (by omega) (by omega), mul_zero]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero hlow, zero_add,
      show m + 1 + 1 - 1 - m = 1 from by omega, show m + 1 + 1 - 1 - (m + 1) = 0 from by omega,
      he0, he1, h (m + 1) (by omega), h (m + 1 + 1) (by omega)]
    ring

/-- **The one-letter alphabet.** A plethysm sending `p_j` to `c ^ j` — evaluation at the
alphabet with the single letter `c` — has `e_0 = 1`, `e_1 = c` and `e_n = 0` for `n ≥ 2`. The
two low values are part of the statement, so no separate degree bookkeeping is needed
downstream. -/
@[hjo "lem_bglx_esymm_geom"]
theorem map_elemSymm_geom {R : Type*} [CommRing R] [Algebra K R] (c : R)
    (φ : Lambda K →ₐ[K] R) (h : ∀ j : ℕ, 1 ≤ j → φ (powerSum K j) = c ^ j) (n : ℕ) :
    φ (elemSymm K n) = if n = 0 then 1 else if n = 1 then c else 0 := by
  have he0 : φ (elemSymm K 0) = 1 := by rw [elemSymm_zero_eq_one, map_one]
  have he1 : φ (elemSymm K 1) = c := by
    refine cancel_natCast (K := K) (n := 1) one_ne_zero ?_
    rw [natCast_mul_map_elemSymm φ (n := 1) le_rfl, Finset.sum_range_one]
    norm_num [h 1 le_rfl, elemSymm_zero_eq_one]
  match n with
  | 0 => simpa using he0
  | 1 => simpa using he1
  | m + 2 =>
    rw [ite_eq_right (show ¬(m + 2 = 0) by omega), ite_eq_right (show ¬(m + 2 = 1) by omega),
      map_elemSymm_eq_zero_of_two_le c φ h he0 he1 (m + 2) (by omega)]

/-- **The negated one-letter alphabet.** A plethysm sending `p_j` to `-c ^ j` has
`e_n = (-c) ^ n`: every one of the `n` terms of Newton's identity contributes `(-c) ^ n`. -/
@[hjo "lem_bglx_esymm_negone"]
theorem map_elemSymm_negGeom {R : Type*} [CommRing R] [Algebra K R] (c : R)
    (ψ : Lambda K →ₐ[K] R) (h : ∀ j : ℕ, 1 ≤ j → ψ (powerSum K j) = -c ^ j) (n : ℕ) :
    ψ (elemSymm K n) = (-c) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [elemSymm_zero_eq_one]
    | m + 1 =>
      refine cancel_natCast (K := K) (n := m + 1) (by omega) ?_
      rw [natCast_mul_map_elemSymm ψ (n := m + 1) (by omega)]
      have hterm : ∀ k ∈ Finset.range (m + 1),
          (-1 : R) ^ k * ψ (powerSum K (k + 1)) * ψ (elemSymm K (m + 1 - 1 - k))
            = (-c) ^ (m + 1) := by
        intro k hk
        rw [Finset.mem_range] at hk
        obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
        rw [show k + j + 1 - 1 - k = j from by omega, ih j (by omega), h (k + 1) (by omega),
          neg_pow, neg_pow]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### The parameter alphabet and its kernel coefficients -/

/-- The plethysm `κ` at the parameter alphabet `M = (1 - q)(1 - u)`: the `K`-algebra
homomorphism `Lambda K → K` sending the power sum `p_{i+1}` to
`(1 - q ^ (i+1)) (1 - u ^ (i+1))`. Its values on the elementary symmetric functions are the
coefficients of the BGLX kernel. -/
@[hjo "def_bglx_param_plethysm"]
noncomputable def paramPleth (q u : K) : Lambda K →ₐ[K] K :=
  MvPolynomial.aeval fun i => (1 - q ^ (i + 1)) * (1 - u ^ (i + 1))

omit [Algebra ℚ K] in
/-- The plethysm at the parameter alphabet sends `p_j` to `(1 - q ^ j)(1 - u ^ j)` for every
`j ≥ 1`. The hypothesis `1 ≤ j` is what undoes the truncated subtraction in
`HJO.Sym.powerSum`. -/
@[simp] theorem paramPleth_powerSum (q u : K) {j : ℕ} (hj : 1 ≤ j) :
    paramPleth q u (powerSum K j) = (1 - q ^ j) * (1 - u ^ j) := by
  rw [paramPleth, powerSum, MvPolynomial.aeval_X, Nat.sub_add_cancel hj]

/-- The plethysm at the one-letter alphabet `c`: the `K`-algebra homomorphism `Lambda K → K`
sending `p_{i+1}` to `c ^ (i+1)`. -/
noncomputable def geomHom (c : K) : Lambda K →ₐ[K] K :=
  MvPolynomial.aeval fun i => c ^ (i + 1)

omit [Algebra ℚ K] in
/-- The one-letter plethysm sends `p_j` to `c ^ j` for every `j ≥ 1`. -/
@[simp] theorem geomHom_powerSum (c : K) {j : ℕ} (hj : 1 ≤ j) :
    geomHom c (powerSum K j) = c ^ j := by
  rw [geomHom, powerSum, MvPolynomial.aeval_X, Nat.sub_add_cancel hj]

/-- The plethysm at the alphabet `M + q`, the intermediate step of the kernel recursion: it
sends `p_{i+1}` to `(1 - q ^ (i+1))(1 - u ^ (i+1)) + q ^ (i+1)`. -/
noncomputable def kappaShiftHom (q u : K) : Lambda K →ₐ[K] K :=
  MvPolynomial.aeval fun i => (1 - q ^ (i + 1)) * (1 - u ^ (i + 1)) + q ^ (i + 1)

omit [Algebra ℚ K] in
/-- The plethysm at `M + q` sends `p_j` to `(1 - q ^ j)(1 - u ^ j) + q ^ j` for `j ≥ 1`. -/
@[simp] theorem kappaShiftHom_powerSum (q u : K) {j : ℕ} (hj : 1 ≤ j) :
    kappaShiftHom q u (powerSum K j) = (1 - q ^ j) * (1 - u ^ j) + q ^ j := by
  rw [kappaShiftHom, powerSum, MvPolynomial.aeval_X, Nat.sub_add_cancel hj]

/-- The plethysm at the alphabet `1 + qu`, the top of the kernel recursion: it sends `p_{i+1}`
to `1 + (qu) ^ (i+1)`. It is both `M + q + u` and the sum of the two one-letter alphabets `1`
and `qu`, and comparing those two readings is what produces the recursion. -/
noncomputable def thetaHom (q u : K) : Lambda K →ₐ[K] K :=
  MvPolynomial.aeval fun i => 1 + (q * u) ^ (i + 1)

omit [Algebra ℚ K] in
/-- The plethysm at `1 + qu` sends `p_j` to `1 + (qu) ^ j` for `j ≥ 1`. -/
@[simp] theorem thetaHom_powerSum (q u : K) {j : ℕ} (hj : 1 ≤ j) :
    thetaHom q u (powerSum K j) = 1 + (q * u) ^ j := by
  rw [thetaHom, powerSum, MvPolynomial.aeval_X, Nat.sub_add_cancel hj]

/-- The values of a one-letter plethysm on the elementary symmetric functions. -/
theorem geomHom_elemSymm (c : K) (n : ℕ) :
    geomHom c (elemSymm K n) = if n = 0 then 1 else if n = 1 then c else 0 :=
  map_elemSymm_geom c (geomHom c) (fun _ hj => geomHom_powerSum c hj) n

/-- A one-letter alphabet has `e_0 = 1`. -/
@[simp] theorem geomHom_elemSymm_zero (c : K) : geomHom c (elemSymm K 0) = 1 := by
  rw [geomHom_elemSymm]; norm_num

/-- A one-letter alphabet has `e_1 = c`. -/
@[simp] theorem geomHom_elemSymm_one (c : K) : geomHom c (elemSymm K 1) = c := by
  rw [geomHom_elemSymm]; norm_num

/-- A one-letter alphabet has `e_s = 0` for `s ≥ 2`. -/
theorem geomHom_elemSymm_of_two_le (c : K) {s : ℕ} (hs : 2 ≤ s) :
    geomHom c (elemSymm K s) = 0 := by
  rw [geomHom_elemSymm, ite_eq_right (show ¬(s = 0) by omega),
    ite_eq_right (show ¬(s = 1) by omega)]

/-- The truncation that makes the kernel recursion finite: convolving against an alphabet whose
elementary symmetric functions are `1, c, 0, 0, …` leaves exactly two terms. Stated at
`n = m + 1` so that its left-hand side is literally the right-hand side of
`HJO.Bglx.map_elemSymm_add`. -/
theorem sum_conv_geom_trunc (φ ψ : Lambda K →ₐ[K] R) (c : R)
    (hψ : ∀ n : ℕ, ψ (elemSymm K n) = if n = 0 then 1 else if n = 1 then c else 0) (m : ℕ) :
    ∑ s ∈ Finset.range (m + 1 + 1), φ (elemSymm K (m + 1 - s)) * ψ (elemSymm K s)
      = φ (elemSymm K (m + 1)) + c * φ (elemSymm K m) := by
  have hsub : Finset.range (1 + 1) ⊆ Finset.range (m + 1 + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hvan : ∀ x ∈ Finset.range (m + 1 + 1), x ∉ Finset.range (1 + 1) →
      φ (elemSymm K (m + 1 - x)) * ψ (elemSymm K x) = 0 := by
    intro x _ hx
    rw [Finset.mem_range] at hx
    rw [hψ x, ite_eq_right (show ¬(x = 0) by omega),
      ite_eq_right (show ¬(x = 1) by omega), mul_zero]
  rw [← Finset.sum_subset hsub hvan, Finset.sum_range_succ, Finset.sum_range_one, hψ 0, hψ 1,
    Nat.sub_zero, Nat.add_sub_cancel]
  norm_num
  ring

/-- The plethysm at the parameter alphabet has `κ(e_0) = 1`: the first case of the kernel
recursion, with `κ(e_m)` read as `0` for `m < 0`. -/
@[hjo "lem_bglx_kernel_coeff_recursion"]
theorem paramPleth_elemSymm_zero (q u : K) : paramPleth q u (elemSymm K 0) = 1 := by
  rw [elemSymm_zero_eq_one, map_one]

/-- The plethysm at `M + q` has `e_0 = 1`, being an algebra homomorphism. -/
theorem kappaShiftHom_elemSymm_zero (q u : K) : kappaShiftHom q u (elemSymm K 0) = 1 := by
  rw [elemSymm_zero_eq_one, map_one]

/-- The alphabet `M + q` is the sum of `M` and the one letter `q`, so its elementary symmetric
functions are `κ(e_n) + q κ(e_{n-1})`. -/
theorem kappaShiftHom_elemSymm_succ (q u : K) (m : ℕ) :
    kappaShiftHom q u (elemSymm K (m + 1))
      = paramPleth q u (elemSymm K (m + 1)) + q * paramPleth q u (elemSymm K m) := by
  have hadd : ∀ j : ℕ, 1 ≤ j → kappaShiftHom q u (powerSum K j)
      = paramPleth q u (powerSum K j) + geomHom q (powerSum K j) := fun j hj => by
    rw [kappaShiftHom_powerSum q u hj, paramPleth_powerSum q u hj, geomHom_powerSum q hj]
  rw [map_elemSymm_add (paramPleth q u) (geomHom q) (kappaShiftHom q u) hadd (m + 1),
    sum_conv_geom_trunc (paramPleth q u) (geomHom q) q (geomHom_elemSymm q) m]

/-- The alphabet `1 + qu` is `(M + q) + u`, so its elementary symmetric functions are those of
`M + q` convolved with the one letter `u`. The scalar identity behind the hypothesis is
`(1 - q ^ j)(1 - u ^ j) + q ^ j + u ^ j = 1 + (qu) ^ j`. -/
theorem thetaHom_elemSymm_succ_kappa (q u : K) (m : ℕ) :
    thetaHom q u (elemSymm K (m + 1))
      = kappaShiftHom q u (elemSymm K (m + 1)) + u * kappaShiftHom q u (elemSymm K m) := by
  have hadd : ∀ j : ℕ, 1 ≤ j → thetaHom q u (powerSum K j)
      = kappaShiftHom q u (powerSum K j) + geomHom u (powerSum K j) := fun j hj => by
    rw [thetaHom_powerSum q u hj, kappaShiftHom_powerSum q u hj, geomHom_powerSum u hj, mul_pow]
    ring
  rw [map_elemSymm_add (kappaShiftHom q u) (geomHom u) (thetaHom q u) hadd (m + 1),
    sum_conv_geom_trunc (kappaShiftHom q u) (geomHom u) u (geomHom_elemSymm u) m]

/-- The alphabet `1 + qu` is also the sum of the two one-letter alphabets `1` and `qu`, which
computes all of its elementary symmetric functions. -/
theorem thetaHom_elemSymm_succ_geom (q u : K) (m : ℕ) :
    thetaHom q u (elemSymm K (m + 1))
      = geomHom (1 : K) (elemSymm K (m + 1)) + q * u * geomHom (1 : K) (elemSymm K m) := by
  have hadd : ∀ j : ℕ, 1 ≤ j → thetaHom q u (powerSum K j)
      = geomHom (1 : K) (powerSum K j) + geomHom (q * u) (powerSum K j) := fun j hj => by
    rw [thetaHom_powerSum q u hj, geomHom_powerSum (1 : K) hj, geomHom_powerSum (q * u) hj,
      one_pow]
  rw [map_elemSymm_add (geomHom (1 : K)) (geomHom (q * u)) (thetaHom q u) hadd (m + 1),
    sum_conv_geom_trunc (geomHom (1 : K)) (geomHom (q * u)) (q * u)
      (geomHom_elemSymm (q * u)) m]

/-- The alphabet `1 + qu` has `e_1 = 1 + qu`. -/
theorem thetaHom_elemSymm_one (q u : K) : thetaHom q u (elemSymm K 1) = 1 + q * u := by
  have h := thetaHom_elemSymm_succ_geom q u 0
  rw [Nat.zero_add, geomHom_elemSymm_one, geomHom_elemSymm_zero] at h
  rw [h]; ring

/-- The alphabet `1 + qu` has `e_2 = qu` and `e_n = 0` for `n ≥ 3`: it has only two letters. -/
theorem thetaHom_elemSymm_add_two (q u : K) (n : ℕ) :
    thetaHom q u (elemSymm K (n + 1 + 1)) = if n = 0 then q * u else 0 := by
  rw [thetaHom_elemSymm_succ_geom q u (n + 1), geomHom_elemSymm, geomHom_elemSymm]
  rcases n with _ | t
  · norm_num
  · norm_num

/-- The kernel recursion at `n = 1`, with `κ(e_m)` read as `0` for `m < 0`: the `qu κ(e_{-1})`
term is absent and the right-hand side is `1 + qu`. -/
@[hjo "lem_bglx_kernel_coeff_recursion"]
theorem paramPleth_elemSymm_one (q u : K) :
    paramPleth q u (elemSymm K 1) + (q + u) * paramPleth q u (elemSymm K 0) = 1 + q * u := by
  have key := thetaHom_elemSymm_succ_kappa q u 0
  rw [kappaShiftHom_elemSymm_succ q u 0, kappaShiftHom_elemSymm_zero, Nat.zero_add,
    thetaHom_elemSymm_one, paramPleth_elemSymm_zero] at key
  rw [paramPleth_elemSymm_zero, key]
  ring

/-- **The kernel coefficient recursion.** For every `n`, the coefficients `κ(e_n)` of the
parameter alphabet satisfy
`κ(e_{n+2}) + (q + u) κ(e_{n+1}) + qu κ(e_n) = [n = 0] qu`.
Both sides are the value of the plethysm at `1 + qu` on `e_{n+2}`: read through `M + q` it is
the left-hand side, and read as the sum of the one-letter alphabets `1` and `qu` it is the
right-hand side. -/
@[hjo "lem_bglx_kernel_coeff_recursion"]
theorem paramPleth_elemSymm_add_two (q u : K) (n : ℕ) :
    paramPleth q u (elemSymm K (n + 2)) + (q + u) * paramPleth q u (elemSymm K (n + 1))
        + q * u * paramPleth q u (elemSymm K n) = if n = 0 then q * u else 0 := by
  have key := thetaHom_elemSymm_succ_kappa q u (n + 1)
  rw [kappaShiftHom_elemSymm_succ q u (n + 1), kappaShiftHom_elemSymm_succ q u n,
    thetaHom_elemSymm_add_two q u n] at key
  rw [show n + 2 = n + 1 + 1 from by omega, key]
  ring

end HJO.Bglx
