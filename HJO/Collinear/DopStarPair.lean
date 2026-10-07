/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.ShiftValues
public import HJO.Collinear.Commutation
public import HJO.CollinearCommutativity
public meta import HJO.Attr

/-! # The composite of an unstarred and a starred basic operator

The two families of basic operators are both pairings: `D_a f` pairs the coefficients of
`f[X + M/z]` against `(-1)^{a+i} e_{a+i}`, and `D*_k f` pairs those of `f[X - M̃/z]` against
`h_{k+i}`. Composing them therefore displaces the alphabet twice, and the two-variable
coefficients `f_{[s,r]}` are exactly what the composite is expressed in.

The mechanism is one pairing identity: a factor `g wʲ` pulled out of the argument of a pairing
takes the scalar `g` out and shifts the family by `j`, so that pairing against a shifted family is
pairing against the basic operator of the shifted index. Feeding the closed coefficients of the two
displacements -- `h_m[X + M/z]` and `eₛ[X - M̃/z]` -- through it turns `D_0(A h_m)` into a
combination of the `D_j A` and `D*_k(A eₛ)` into a combination of the `D*_{k+j} A`. Applying those
to the expansions of `D*_k f` and `D_0 f` gives the two displays of the composites.

Subtracting them, the leading sums cancel and the two remaining triple sums merge: substituting
`μ = s + j` in one and `μ = s - j` in the other, both summands become
`(-1)^μ (1 - (qu)^{μ-s}) f_{[s,r]} h_{n-μ} e_μ` with `n = s + r + k`, over complementary ranges of
`μ` whose one missing index contributes nothing. The merged sum splits into the alternating
convolution, which vanishes, and its dilated form, which is the axis generator; grouping the pairs
`(s,r)` by `s + r` and using that the weighted two-variable coefficients sum to zero off the
constant term leaves multiplication by `M (qu)^{k-1} U_k`.

Over a general field this carries `q u ≠ 0` and `q u ≠ 1`, which are automatic
over `ℚ(q,u)`. It does NOT need `M ≠ 0`: `M` occurs only as a numerator factor, and at
`u = 1` both sides of the commutator vanish.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### Pairing against a family -/

section Pairing

variable {K : Type*} [CommRing K]

/-- Pairing against a family, as a finite sum over any range covering the support. -/
theorem coeffPairing_eq_sum_range (c : ℕ → Lambda K) (P : Polynomial (Lambda K)) {N : ℕ}
    (hN : ∀ j : ℕ, N ≤ j → P.coeff j = 0) :
    coeffPairing c P = ∑ j ∈ range N, P.coeff j * c j := by
  have h0 : ∀ j : ℕ, (0 : Lambda K) * c j = 0 := fun j => zero_mul _
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · have hP : P = 0 := Polynomial.ext fun j => by
      rw [hN j (by omega), Polynomial.coeff_zero]
    rw [hP, map_zero, Finset.range_zero, Finset.sum_empty]
  · have hd : P.natDegree < N := by
      rcases eq_or_ne P 0 with rfl | hP
      · simpa using hNpos
      · by_contra hcon
        exact (Polynomial.leadingCoeff_ne_zero.mpr hP) (hN _ (by omega))
    change P.sum (fun j A => A * c j) = _
    rw [Polynomial.sum_over_range' _ h0 N hd]

/-- **A monomial factor shifts the family.** Extracting the coefficient of `zᵏ` from `g z^{-j} P`
takes `g` outside and reads the family `j` places further along. -/
theorem coeffPairing_C_mul_X_pow_mul (g : Lambda K) (P : Polynomial (Lambda K)) :
    ∀ (j : ℕ) (c d : ℕ → Lambda K), (∀ i : ℕ, d i = c (i + j)) →
      coeffPairing c (Polynomial.C g * Polynomial.X ^ j * P) = g * coeffPairing d P := by
  intro j
  induction j with
  | zero =>
    intro c d hd
    have hcd : d = c := funext fun i => by rw [hd i, Nat.add_zero]
    rw [hcd, pow_zero, mul_one, coeffPairing_C_mul]
  | succ j ih =>
    intro c d hd
    rw [show Polynomial.C g * Polynomial.X ^ (j + 1) * P
        = Polynomial.X * (Polynomial.C g * Polynomial.X ^ j * P) from by ring,
      coeffPairing_X_mul]
    refine ih (fun i => c (i + 1)) d fun i => ?_
    rw [hd i, show i + (j + 1) = i + j + 1 from by omega]

end Pairing

/-! ### The two families of basic operators as finite sums -/

section Expansion

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The basic operators in terms of displacement coefficients.** For any range covering the
support, `D_a f = ∑ₛ (-1)^{s+a} f_{[s]} e_{s+a}`. -/
@[hjo "lem_dop_expansion"]
theorem dop_eq_sum_range (q u : L) (a : ℕ) (f : Lambda L) {N : ℕ}
    (hN : ∀ s : ℕ, N ≤ s → shiftCoeff q u f s = 0) :
    Dop q u a f
      = ∑ s ∈ range N, shiftCoeff q u f s * ((-1) ^ (s + a) * elemSymm L (s + a)) := by
  rw [dop_apply, coeffPairing_eq_sum_range _ _ hN]
  exact Finset.sum_congr rfl fun s _ => by
    simp only [shiftCoeff]
    rw [show s + a = a + s from Nat.add_comm s a]

/-- **The starred operators in terms of displacement coefficients.** For
any range covering the support, `D*_k f = ∑ᵣ f*_{[r]} h_{r+k}`.

The sum is naturally `∑_{r ≥ 0}`, finitely supported by `HJO.Sym.exists_bound_plethShiftStar`; the
bound is taken as a hypothesis here, so that a consumer with a bound of its own -- the degree of a
homogeneous argument, say -- quotes the sum over its own range. Any `N` past the support gives the
same value, the extra terms being zero. -/
@[hjo "lem_dopstar_expansion"]
theorem dopStar_eq_sum_range (q u : L) (k : ℕ) (f : Lambda L) {N : ℕ}
    (hN : ∀ r : ℕ, N ≤ r → shiftStarCoeff q u f r = 0) :
    DopStar q u k f = ∑ r ∈ range N, shiftStarCoeff q u f r * completeHomog L (r + k) := by
  rw [dopStar_apply, coeffPairing_eq_sum_range _ _ hN]
  exact Finset.sum_congr rfl fun r _ => by
    simp only [shiftStarCoeff]
    rw [show r + k = k + r from Nat.add_comm r k]

end Expansion

/-! ### One operator against a basis element -/

section Products

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The unstarred operator against a complete homogeneous factor.** For `q u ≠ 1`,
`D_0(A h_m) = h_m D_0 A + ∑_{j=1}^{m} M(1-(qu)ʲ)/(1-qu) · h_{m-j} D_j A`: the displacement turns
the product into `A[X+M/z]` times the closed form of `h_m[X+M/z]`, and the factor `w^j` of the
`j`-th term shifts the extracted coefficient from `z⁰` to `zʲ`. -/
theorem dop_zero_mul_completeHomog (q u : L) (hqu : q * u ≠ 1) (m : ℕ) (A : Lambda L) :
    Dop q u 0 (A * completeHomog L m)
      = completeHomog L m * Dop q u 0 A
        + ∑ j ∈ Finset.Icc 1 m,
            MvPolynomial.C ((1 - q) * (1 - u) * (1 - (q * u) ^ j) / (1 - q * u))
              * completeHomog L (m - j) * Dop q u j A := by
  rw [dop_apply, map_mul, plethShift_completeHomog q u hqu m, mul_add, Finset.mul_sum, map_add,
    map_sum]
  congr 1
  · rw [mul_comm (plethShift q u A), coeffPairing_C_mul, dop_apply]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show plethShift q u A * (Polynomial.C (MvPolynomial.C
          ((1 - q) * (1 - u) * (1 - (q * u) ^ j) / (1 - q * u)) * completeHomog L (m - j))
            * Polynomial.X ^ j)
        = Polynomial.C (MvPolynomial.C ((1 - q) * (1 - u) * (1 - (q * u) ^ j) / (1 - q * u))
            * completeHomog L (m - j)) * Polynomial.X ^ j * plethShift q u A from by ring,
      coeffPairing_C_mul_X_pow_mul _ _ j _
        (fun i : ℕ => (-1 : Lambda L) ^ (j + i) * elemSymm L (j + i))
        (fun i => by rw [show j + i = 0 + (i + j) from by omega]),
      dop_apply, mul_assoc]

/-- **The starred operator against an elementary factor.** For `q`, `u` nonzero with `q u ≠ 1`,
`D*_k(A eₛ) = eₛ D*_k A - ∑_{j=1}^{s} (-1)ʲ M(1-(qu)^{-j})/(1-qu) · e_{s-j} D*_{k+j} A`. -/
theorem dopStar_mul_elemSymm (q u : L) (hq : q ≠ 0) (hu : u ≠ 0) (hqu : q * u ≠ 1) (k s : ℕ)
    (A : Lambda L) :
    DopStar q u k (A * elemSymm L s)
      = elemSymm L s * DopStar q u k A
        - ∑ j ∈ Finset.Icc 1 s,
            MvPolynomial.C ((-1) ^ j
                * ((1 - q) * (1 - u) * (1 - ((q * u) ^ j)⁻¹) / (1 - q * u)))
              * elemSymm L (s - j) * DopStar q u (k + j) A := by
  rw [dopStar_apply, map_mul, plethShiftStar_elemSymm q u hq hu hqu s, mul_sub, Finset.mul_sum,
    map_sub, map_sum]
  congr 1
  · rw [mul_comm (plethShiftStar q u A), coeffPairing_C_mul, dopStar_apply]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show plethShiftStar q u A * (Polynomial.C (MvPolynomial.C ((-1) ^ j
          * ((1 - q) * (1 - u) * (1 - ((q * u) ^ j)⁻¹) / (1 - q * u)))
            * elemSymm L (s - j)) * Polynomial.X ^ j)
        = Polynomial.C (MvPolynomial.C ((-1) ^ j
            * ((1 - q) * (1 - u) * (1 - ((q * u) ^ j)⁻¹) / (1 - q * u)))
              * elemSymm L (s - j)) * Polynomial.X ^ j * plethShiftStar q u A from by ring,
      coeffPairing_C_mul_X_pow_mul _ _ j _
        (fun i : ℕ => completeHomog L (k + j + i))
        (fun i => by rw [show k + j + i = k + (i + j) from by omega]),
      dopStar_apply, mul_assoc]

end Products

/-! ### The two composites -/

section Composite

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- A sign pulled out of an operator: `(-1)ˢ` is the image of a scalar, so every `L`-linear
endomorphism commutes with multiplication by it. -/
theorem neg_one_pow_mul_comm (T : Module.End L (Lambda L)) (s : ℕ) (g : Lambda L) :
    T ((-1 : Lambda L) ^ s * g) = (-1 : Lambda L) ^ s * T g := by
  rw [show ((-1 : Lambda L)) ^ s = MvPolynomial.C ((-1 : L) ^ s) from by
      rw [map_pow, map_neg, map_one],
    ← MvPolynomial.smul_eq_C_mul, map_smul, MvPolynomial.smul_eq_C_mul]

omit [Algebra ℚ L] in
/-- The scalar of the unstarred displacement, with the constant `M/(1 - qu)` split off. -/
theorem shiftScalar_split (q u : L) (j : ℕ) :
    (MvPolynomial.C ((1 - q) * (1 - u) * (1 - (q * u) ^ j) / (1 - q * u)) : Lambda L)
      = MvPolynomial.C ((1 - q) * (1 - u) / (1 - q * u))
        * MvPolynomial.C (1 - (q * u) ^ j) := by
  rw [← MvPolynomial.C_mul]
  congr 1
  ring

omit [Algebra ℚ L] in
/-- The scalar of the starred displacement, with the sign and the constant `M/(1 - qu)` split
off. -/
theorem shiftStarScalar_split (q u : L) (j : ℕ) :
    (MvPolynomial.C ((-1 : L) ^ j * ((1 - q) * (1 - u) * (1 - ((q * u) ^ j)⁻¹) / (1 - q * u)))
        : Lambda L)
      = (-1 : Lambda L) ^ j * (MvPolynomial.C ((1 - q) * (1 - u) / (1 - q * u))
          * MvPolynomial.C (1 - ((q * u) ^ j)⁻¹)) := by
  rw [show ((-1 : Lambda L)) ^ j = MvPolynomial.C ((-1 : L) ^ j) from by
      rw [map_pow, map_neg, map_one], ← MvPolynomial.C_mul, ← MvPolynomial.C_mul]
  congr 1
  ring

/-- **The unstarred operator applied second.** For `q u ≠ 1`, every `k ≥ 0` and every `f`, with `N`
any bound above which the two-variable coefficients vanish,
`D₀ D*_k f = ∑_{s,r} (-1)ˢ f_{[s,r]} h_{r+k} eₛ
  + M/(1-qu) ∑_{s,r} ∑_{j=1}^{r+k} (-1)^{s+j}(1-(qu)ʲ) f_{[s,r]} h_{r+k-j} e_{s+j}`.

The starred operator expands `f` along `h_{r+k}`, and the unstarred one then meets each product:
the constant term of `h_{r+k}[X+M/z]` contributes `h_{r+k} D₀`, and its `j`-th coefficient
contributes `h_{r+k-j}` against `D_j`, whose expansion is the inner sum over `s`. -/
@[hjo "lem_dop0_dopstar_left"]
theorem dop_zero_dopStar (q u : L) (hqu : q * u ≠ 1) (k : ℕ) (f : Lambda L) {N : ℕ}
    (hN : ∀ s r : ℕ, N ≤ s ∨ N ≤ r → shiftPairCoeff q u f s r = 0) :
    Dop q u 0 (DopStar q u k f)
      = ∑ s ∈ range N, ∑ r ∈ range N,
          (-1) ^ s * shiftPairCoeff q u f s r * completeHomog L (r + k) * elemSymm L s
        + MvPolynomial.C ((1 - q) * (1 - u) / (1 - q * u))
            * ∑ s ∈ range N, ∑ r ∈ range N, ∑ j ∈ Finset.Icc 1 (r + k),
                (-1) ^ (s + j) * MvPolynomial.C (1 - (q * u) ^ j)
                  * shiftPairCoeff q u f s r * completeHomog L (r + k - j)
                  * elemSymm L (s + j) := by
  have hNr : ∀ r : ℕ, N ≤ r → shiftStarCoeff q u f r = 0 := fun r hr => by
    rw [shiftStarCoeff_eq_shiftPairCoeff]
    exact hN 0 r (Or.inr hr)
  have hNs : ∀ r s : ℕ, N ≤ s → shiftCoeff q u (shiftStarCoeff q u f r) s = 0 :=
    fun r s hs => by
      rw [← shiftPairCoeff_eq_shiftCoeff]
      exact hN s r (Or.inl hs)
  have hdop : ∀ a r : ℕ, Dop q u a (shiftStarCoeff q u f r)
      = ∑ s ∈ range N,
          shiftPairCoeff q u f s r * ((-1) ^ (s + a) * elemSymm L (s + a)) := by
    intro a r
    rw [dop_eq_sum_range q u a _ (hNs r)]
    exact Finset.sum_congr rfl fun s _ => by rw [← shiftPairCoeff_eq_shiftCoeff]
  -- the composite, in the order the two expansions produce
  have hstep : Dop q u 0 (DopStar q u k f)
      = ∑ r ∈ range N,
          ((∑ s ∈ range N,
              (-1) ^ s * shiftPairCoeff q u f s r * completeHomog L (r + k) * elemSymm L s)
            + ∑ j ∈ Finset.Icc 1 (r + k), ∑ s ∈ range N,
                MvPolynomial.C ((1 - q) * (1 - u) / (1 - q * u))
                  * ((-1) ^ (s + j) * MvPolynomial.C (1 - (q * u) ^ j)
                      * shiftPairCoeff q u f s r * completeHomog L (r + k - j)
                      * elemSymm L (s + j))) := by
    rw [dopStar_eq_sum_range q u k f hNr, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [dop_zero_mul_completeHomog q u hqu (r + k) (shiftStarCoeff q u f r), hdop 0 r,
      Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun s _ => ?_
      simp only [Nat.add_zero]
      ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [hdop j r, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [shiftScalar_split]
      ring
  rw [hstep, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
  · simp only [Finset.mul_sum]
    rw [eq_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]

/-- **The starred operator applied second.** For `q`, `u` nonzero with `q u ≠ 1`, every `k ≥ 0` and
every `f`, with `N` any bound above which the two-variable coefficients vanish,
`D*_k D₀ f = ∑_{s,r} (-1)ˢ f_{[s,r]} h_{r+k} eₛ
  - M/(1-qu) ∑_{s,r} ∑_{j=1}^{s} (-1)^{s+j}(1-(qu)^{-j}) f_{[s,r]} h_{r+k+j} e_{s-j}`. -/
@[hjo "lem_dop0_dopstar_right"]
theorem dopStar_dop_zero (q u : L) (hq : q ≠ 0) (hu : u ≠ 0) (hqu : q * u ≠ 1) (k : ℕ)
    (f : Lambda L) {N : ℕ}
    (hN : ∀ s r : ℕ, N ≤ s ∨ N ≤ r → shiftPairCoeff q u f s r = 0) :
    DopStar q u k (Dop q u 0 f)
      = ∑ s ∈ range N, ∑ r ∈ range N,
          (-1) ^ s * shiftPairCoeff q u f s r * completeHomog L (r + k) * elemSymm L s
        - MvPolynomial.C ((1 - q) * (1 - u) / (1 - q * u))
            * ∑ s ∈ range N, ∑ r ∈ range N, ∑ j ∈ Finset.Icc 1 s,
                (-1) ^ (s + j) * MvPolynomial.C (1 - ((q * u) ^ j)⁻¹)
                  * shiftPairCoeff q u f s r * completeHomog L (r + k + j)
                  * elemSymm L (s - j) := by
  have hNs : ∀ s : ℕ, N ≤ s → shiftCoeff q u f s = 0 := fun s hs => by
    rw [shiftCoeff_eq_shiftPairCoeff]
    exact hN s 0 (Or.inl hs)
  have hNr : ∀ s r : ℕ, N ≤ r → shiftStarCoeff q u (shiftCoeff q u f s) r = 0 :=
    fun s r hr => by
      rw [← shiftPairCoeff_eq_shiftStarCoeff]
      exact hN s r (Or.inr hr)
  have hdopStar : ∀ a s : ℕ, DopStar q u a (shiftCoeff q u f s)
      = ∑ r ∈ range N, shiftPairCoeff q u f s r * completeHomog L (r + a) := by
    intro a s
    rw [dopStar_eq_sum_range q u a _ (hNr s)]
    exact Finset.sum_congr rfl fun r _ => by rw [← shiftPairCoeff_eq_shiftStarCoeff]
  have hstep : DopStar q u k (Dop q u 0 f)
      = ∑ s ∈ range N,
          ((∑ r ∈ range N,
              (-1) ^ s * shiftPairCoeff q u f s r * completeHomog L (r + k) * elemSymm L s)
            - ∑ j ∈ Finset.Icc 1 s, ∑ r ∈ range N,
                MvPolynomial.C ((1 - q) * (1 - u) / (1 - q * u))
                  * ((-1) ^ (s + j) * MvPolynomial.C (1 - ((q * u) ^ j)⁻¹)
                      * shiftPairCoeff q u f s r * completeHomog L (r + k + j)
                      * elemSymm L (s - j))) := by
    rw [dop_eq_sum_range q u 0 f hNs, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Nat.add_zero]
    have hpart1 : (-1 : Lambda L) ^ s * (elemSymm L s * DopStar q u k (shiftCoeff q u f s))
        = ∑ r ∈ range N,
            (-1) ^ s * shiftPairCoeff q u f s r * completeHomog L (r + k) * elemSymm L s := by
      rw [hdopStar k s, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    have hpart2 : (-1 : Lambda L) ^ s * (∑ j ∈ Finset.Icc 1 s,
          MvPolynomial.C ((-1 : L) ^ j
              * ((1 - q) * (1 - u) * (1 - ((q * u) ^ j)⁻¹) / (1 - q * u)))
            * elemSymm L (s - j) * DopStar q u (k + j) (shiftCoeff q u f s))
        = ∑ j ∈ Finset.Icc 1 s, ∑ r ∈ range N,
            MvPolynomial.C ((1 - q) * (1 - u) / (1 - q * u))
              * ((-1) ^ (s + j) * MvPolynomial.C (1 - ((q * u) ^ j)⁻¹)
                  * shiftPairCoeff q u f s r * completeHomog L (r + k + j)
                  * elemSymm L (s - j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hdopStar (k + j) s, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [shiftStarScalar_split, show r + (k + j) = r + k + j from by omega]
      ring
    rw [show shiftCoeff q u f s * ((-1 : Lambda L) ^ s * elemSymm L s)
        = (-1 : Lambda L) ^ s * (shiftCoeff q u f s * elemSymm L s) from by ring,
      neg_one_pow_mul_comm, dopStar_mul_elemSymm q u hq hu hqu k s (shiftCoeff q u f s),
      mul_sub, hpart1, hpart2]
  rw [hstep]
  simp only [Finset.sum_sub_distrib]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [eq_comm, Finset.sum_comm]

end Composite

/-! ### The commutator -/

section Commutator

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- A closed interval of naturals as a half-open one, so that the shifted-range sum lemmas
apply. -/
theorem Icc_eq_Ico_succ (a b : ℕ) : Finset.Icc a b = Finset.Ico a (b + 1) := by
  ext x
  simp

omit [Algebra ℚ L] in
/-- Cancelling a power of a nonzero parameter against the inverse of a larger power. -/
theorem pow_sub_mul_inv_pow {v : L} (hv0 : v ≠ 0) {a b : ℕ} (hab : b ≤ a) :
    v ^ (a - b) * (v ^ a)⁻¹ = (v ^ b)⁻¹ := by
  have h : v ^ a = v ^ (a - b) * v ^ b := by
    rw [← pow_add]
    congr 1
    omega
  rw [h, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hv0), one_mul]

omit [Algebra ℚ L] in
/-- Cancelling the inverse of a power against a larger power. -/
theorem pow_add_mul_inv_pow {v : L} (hv0 : v ≠ 0) (a b : ℕ) :
    v ^ (a + b) * (v ^ a)⁻¹ = v ^ b := by
  rw [pow_add, mul_comm (v ^ a) (v ^ b), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hv0),
    mul_one]

/-- The sign of a reflected index: `(-1)^{s + a}` is `(-1)^{s - a}`. -/
theorem neg_one_pow_add_eq_sub {R : Type*} [Monoid R] [HasDistribNeg R] {s a : ℕ} (h : a ≤ s) :
    ((-1 : R)) ^ (s + a) = (-1) ^ (s - a) := by
  rw [show s + a = (s - a) + 2 * a from by omega, pow_add, pow_mul]
  simp

/-- The summand the two inner sums of the commutator merge into: the alternating convolution of
the two bases in total degree `n`, weighted by `1 - (qu)^{μ-s}`. -/
noncomputable def mergeTerm (q u : L) (F : Lambda L) (s n μ : ℕ) : Lambda L :=
  (-1) ^ μ * MvPolynomial.C (1 - (q * u) ^ μ * ((q * u) ^ s)⁻¹) * F
    * completeHomog L (n - μ) * elemSymm L μ

/-- **The unstarred inner sum, reindexed.** Substituting `μ = s + j` carries the inner sum of
`HJO.Sym.dop_zero_dopStar` to the merged summand over `s + 1 ≤ μ ≤ s + r + k`. -/
theorem sum_Icc_eq_sum_mergeTerm_upper (q u : L) (hv0 : q * u ≠ 0) (s r k : ℕ) (F : Lambda L) :
    ∑ j ∈ Finset.Icc 1 (r + k),
        (-1) ^ (s + j) * MvPolynomial.C (1 - (q * u) ^ j) * F
          * completeHomog L (r + k - j) * elemSymm L (s + j)
      = ∑ μ ∈ Finset.Icc (s + 1) (s + r + k), mergeTerm q u F s (s + r + k) μ := by
  rw [Icc_eq_Ico_succ, Icc_eq_Ico_succ, Finset.sum_Ico_eq_sum_range,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, show s + r + k + 1 - (s + 1) = r + k from by omega]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mergeTerm, show s + 1 + i = s + (1 + i) from by omega,
    pow_add_mul_inv_pow hv0 s (1 + i),
    show s + r + k - (s + (1 + i)) = r + k - (1 + i) from by omega]

/-- **The starred inner sum, reindexed.** Substituting `μ = s - j` carries the inner sum of
`HJO.Sym.dopStar_dop_zero` to the merged summand over `0 ≤ μ ≤ s - 1`. -/
theorem sum_Icc_eq_sum_mergeTerm_lower (q u : L) (hv0 : q * u ≠ 0) (s r k : ℕ) (F : Lambda L) :
    ∑ j ∈ Finset.Icc 1 s,
        (-1) ^ (s + j) * MvPolynomial.C (1 - ((q * u) ^ j)⁻¹) * F
          * completeHomog L (r + k + j) * elemSymm L (s - j)
      = ∑ μ ∈ range s, mergeTerm q u F s (s + r + k) μ := by
  rw [Icc_eq_Ico_succ, Finset.sum_Ico_eq_sum_range,
    ← Finset.sum_range_reflect (fun μ => mergeTerm q u F s (s + r + k) μ) s]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun i hi => ?_
  have his : i < s := Finset.mem_range.mp hi
  rw [mergeTerm, show s - 1 - i = s - (1 + i) from by omega,
    neg_one_pow_add_eq_sub (show 1 + i ≤ s from by omega),
    pow_sub_mul_inv_pow hv0 (show 1 + i ≤ s from by omega),
    show s + r + k - (s - (1 + i)) = r + k + (1 + i) from by omega]

/-- Splitting a range at an index whose term vanishes. -/
theorem sum_Icc_add_sum_range {M : Type*} [AddCommMonoid M] {s n : ℕ} (hsn : s ≤ n)
    (G : ℕ → M) (hGs : G s = 0) :
    (∑ μ ∈ Finset.Icc (s + 1) n, G μ) + ∑ μ ∈ range s, G μ = ∑ μ ∈ range (n + 1), G μ := by
  have h1 : ∑ μ ∈ range (n + 1), G μ
      = (∑ μ ∈ Finset.Ico 0 s, G μ) + ∑ μ ∈ Finset.Ico s (n + 1), G μ := by
    rw [Finset.sum_Ico_consecutive G (Nat.zero_le s) (show s ≤ n + 1 from by omega),
      Finset.range_eq_Ico]
  have h2 : ∑ μ ∈ Finset.Ico s (n + 1), G μ = ∑ μ ∈ Finset.Icc (s + 1) n, G μ := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (show s < n + 1 from by omega), hGs, zero_add,
      Icc_eq_Ico_succ]
  rw [h1, h2, Finset.range_eq_Ico, add_comm]

/-- **The merged sum is the axis generator.** Splitting the weight `1 - (qu)^{μ-s}` leaves the
alternating convolution, which vanishes above degree zero, against its dilated form, which is the
axis generator. -/
theorem sum_mergeTerm (q u : L) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) {n : ℕ} (hn : 1 ≤ n)
    (s : ℕ) (F : Lambda L) :
    ∑ μ ∈ range (n + 1), mergeTerm q u F s n μ
      = -(MvPolynomial.C (((q * u) ^ s)⁻¹) * F
            * (MvPolynomial.C ((q * u - 1) * (q * u) ^ (n - 1)) * axisGen (q * u) n)) := by
  have hsplit : ∀ μ : ℕ, mergeTerm q u F s n μ
      = ((-1) ^ μ * completeHomog L (n - μ) * elemSymm L μ) * F
        - MvPolynomial.C (((q * u) ^ s)⁻¹) * F
            * ((-1) ^ μ * MvPolynomial.C ((q * u) ^ μ) * completeHomog L (n - μ)
                * elemSymm L μ) := by
    intro μ
    rw [mergeTerm, map_sub, map_one, map_mul]
    ring
  rw [Finset.sum_congr rfl fun μ _ => hsplit μ]
  simp only [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, sum_alternating_completeHomog_mul_elemSymm hn, zero_mul,
    ← Finset.mul_sum, sum_alternating_pow_completeHomog_mul_elemSymm hv0 hv1 hn, zero_sub]

/-- **Grouping a square of indices by the sum of the coordinates.** -/
theorem sum_square_eq_sum_of_add {M : Type*} [AddCommMonoid M] {N : ℕ}
    (g : ℕ → ℕ → M) (h0 : ∀ s r : ℕ, N ≤ s ∨ N ≤ r → g s r = 0) :
    ∑ s ∈ range N, ∑ r ∈ range N, g s r
      = ∑ m ∈ range (2 * N), ∑ s ∈ range (m + 1), g s (m - s) := by
  classical
  rw [← Finset.sum_product' (range N) (range N) g,
    ← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 + p.2) (t := range (2 * N))
      (fun p hp => by
        rw [Finset.mem_product] at hp
        have h1 := Finset.mem_range.mp hp.1
        have h2 := Finset.mem_range.mp hp.2
        exact Finset.mem_range.2 (by omega)) (fun p => g p.1 p.2)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun p : ℕ × ℕ => g p.1 p.2) m]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact Finset.HasAntidiagonal.mem_antidiagonal.2 hp.2
  · intro p hp hpn
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [Finset.mem_filter] at hpn
    have hsq : p ∉ range N ×ˢ range N := fun hc => hpn ⟨hc, hp⟩
    rw [Finset.mem_product] at hsq
    simp only [Finset.mem_range, not_and_or, not_lt] at hsq
    exact h0 p.1 p.2 hsq

/-- **The commutator of the unstarred and the starred operator.** For `q u` neither `0` nor `1`,
every `k ≥ 1` and every `f`, `D₀ D*_k f - D*_k D₀ f = M (qu)^{k-1} U_k f`.

Subtracting the two displays, the leading sums cancel and the two inner sums merge into the
alternating convolution weighted by `1 - (qu)^{μ-s}`; the unweighted half vanishes and the
weighted half is the axis generator. Grouping the pairs `(s,r)` by `s + r` and using that the
weighted two-variable coefficients sum to zero off the constant term, where they sum to `f`, leaves
multiplication by `M (qu)^{k-1} U_k`.

`M ≠ 0` is NOT needed: `M` occurs only as a numerator factor. What is needed over a general field
is `q u ≠ 0`, so that the inverse powers are what they say, and `q u ≠ 1`, so that the division by
`1 - q u` and the axis generator's factor `q u - 1` are legitimate. -/
@[hjo "lem_dop0_dopstar_comm"]
theorem dop_zero_dopStar_commutator (q u : L) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) {k : ℕ}
    (hk : 1 ≤ k) (f : Lambda L) :
    Dop q u 0 (DopStar q u k f) - DopStar q u k (Dop q u 0 f)
      = MvPolynomial.C ((1 - q) * (1 - u) * (q * u) ^ (k - 1)) * axisGen (q * u) k * f := by
  classical
  have hq : q ≠ 0 := left_ne_zero_of_mul hv0
  have hu : u ≠ 0 := right_ne_zero_of_mul hv0
  have hvsub : (1 : L) - q * u ≠ 0 := sub_ne_zero_of_ne (Ne.symm hv1)
  obtain ⟨N₀, hN₀, -⟩ := exists_bound_plethShiftPair q u f
  obtain ⟨N, hNpos, hN⟩ : ∃ N : ℕ, 0 < N ∧
      ∀ s r : ℕ, N ≤ s ∨ N ≤ r → shiftPairCoeff q u f s r = 0 := by
    refine ⟨N₀ + 1, by omega, fun s r h => ?_⟩
    rcases h with h | h
    · exact hN₀ s r (Or.inl (by omega))
    · exact hN₀ s r (Or.inr (by omega))
  -- the two inner sums of the two displays merge
  have hmerge : ∀ s r : ℕ,
      (∑ j ∈ Finset.Icc 1 (r + k),
          (-1) ^ (s + j) * MvPolynomial.C (1 - (q * u) ^ j) * shiftPairCoeff q u f s r
            * completeHomog L (r + k - j) * elemSymm L (s + j))
        + ∑ j ∈ Finset.Icc 1 s,
            (-1) ^ (s + j) * MvPolynomial.C (1 - ((q * u) ^ j)⁻¹) * shiftPairCoeff q u f s r
              * completeHomog L (r + k + j) * elemSymm L (s - j)
        = -(MvPolynomial.C (((q * u) ^ s)⁻¹) * shiftPairCoeff q u f s r
              * (MvPolynomial.C ((q * u - 1) * (q * u) ^ (s + r + k - 1))
                  * axisGen (q * u) (s + r + k))) := by
    intro s r
    have hzero : mergeTerm q u (shiftPairCoeff q u f s r) s (s + r + k) s = 0 := by
      rw [mergeTerm, mul_inv_cancel₀ (pow_ne_zero s hv0), sub_self, map_zero]
      simp
    rw [sum_Icc_eq_sum_mergeTerm_upper q u hv0 s r k _,
      sum_Icc_eq_sum_mergeTerm_lower q u hv0 s r k _,
      sum_Icc_add_sum_range (show s ≤ s + r + k from by omega) _ hzero,
      sum_mergeTerm q u hv0 hv1 (show 1 ≤ s + r + k from by omega) s _]
  -- the leading sums cancel and the rest is the merged double sum
  have hstep : Dop q u 0 (DopStar q u k f) - DopStar q u k (Dop q u 0 f)
      = MvPolynomial.C ((1 - q) * (1 - u) / (1 - q * u))
          * ∑ s ∈ range N, ∑ r ∈ range N,
              -(MvPolynomial.C (((q * u) ^ s)⁻¹) * shiftPairCoeff q u f s r
                  * (MvPolynomial.C ((q * u - 1) * (q * u) ^ (s + r + k - 1))
                      * axisGen (q * u) (s + r + k))) := by
    have hcancel : ∀ A X Y : Lambda L, A + X - (A - Y) = X + Y := fun A X Y => by ring
    rw [dop_zero_dopStar q u hv1 k f hN, dopStar_dop_zero q u hq hu hv1 k f hN, hcancel,
      ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => hmerge s r
  -- each anti-diagonal factors, and only the constant one survives
  have hterm : ∀ m : ℕ, (∑ s ∈ range (m + 1),
        -(MvPolynomial.C (((q * u) ^ s)⁻¹) * shiftPairCoeff q u f s (m - s)
            * (MvPolynomial.C ((q * u - 1) * (q * u) ^ (s + (m - s) + k - 1))
                * axisGen (q * u) (s + (m - s) + k))))
      = -(MvPolynomial.C ((q * u - 1) * (q * u) ^ (m + k - 1)) * axisGen (q * u) (m + k))
          * ∑ s ∈ range (m + 1),
              MvPolynomial.C (((q * u) ^ s)⁻¹) * shiftPairCoeff q u f s (m - s) := by
    intro m
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hsm : s ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [show s + (m - s) + k = m + k from by omega]
    ring
  have hgroup : (∑ s ∈ range N, ∑ r ∈ range N,
        -(MvPolynomial.C (((q * u) ^ s)⁻¹) * shiftPairCoeff q u f s r
            * (MvPolynomial.C ((q * u - 1) * (q * u) ^ (s + r + k - 1))
                * axisGen (q * u) (s + r + k))))
      = -(MvPolynomial.C ((q * u - 1) * (q * u) ^ (k - 1)) * axisGen (q * u) k) * f := by
    rw [sum_square_eq_sum_of_add _ fun s r h => by rw [hN s r h]; simp,
      Finset.sum_congr rfl fun m _ => hterm m,
      Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (by omega)) fun m _ hm0 => by
        rw [sum_inv_pow_mul_shiftPairCoeff q u hq hu f (show 1 ≤ m from by omega), mul_zero],
      Finset.range_one, Finset.sum_singleton, pow_zero, inv_one, map_one, one_mul, Nat.sub_zero,
      shiftPairCoeff_zero_zero, Nat.zero_add]
  have hC : (MvPolynomial.C ((1 - q) * (1 - u) / (1 - q * u)) : Lambda L)
      * -(MvPolynomial.C ((q * u - 1) * (q * u) ^ (k - 1)))
      = MvPolynomial.C ((1 - q) * (1 - u) * (q * u) ^ (k - 1)) := by
    rw [mul_neg, ← MvPolynomial.C_mul, ← MvPolynomial.C_neg]
    congr 1
    field_simp
    ring
  have hassoc : ∀ a b c d : Lambda L, a * (-(b * c) * d) = a * -b * c * d :=
    fun a b c d => by ring
  rw [hstep, hgroup, hassoc, hC]

end Commutator

end HJO.Sym
