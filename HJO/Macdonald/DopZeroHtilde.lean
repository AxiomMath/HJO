/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.DopStarPair
public import HJO.Macdonald.Htilde
public meta import HJO.Attr

/-! # Garsia--Haiman--Tesler's Section 4: the degree-zero operator on the modified family

The route from the construction of `HJO/Macdonald/Htilde.lean` to
Garsia--Haiman--Tesler's Theorem 1.2, equation (1.11) a).

## Main definitions

* `HJO.Sym.plethCreateQ`: the creation displacement `qs` of the first
  parameter, `p_k ↦ p_k - (1 - q^k) z^{-k}`, written in `w = z^{-1}`.
* `HJO.Sym.plethMulU`: the plethystic multiplication `𝒲`,
  `p_k ↦ (1 - u^{-k}) p_k`; the scalars are the reciprocals of those of `HJO.Sym.plethDivide`.
* `HJO.Sym.eop`: the plethystic form `ℰ` of Macdonald's operator,
  `ℰ(F) = ∑_m ([z^{-m}] qs(F)) 𝒲(h_m)`.

## Main results

* `HJO.Sym.coeff_zero_plethCreateQ`.
* `HJO.Sym.map_completeHomog_eq_elemSymm`.
* `HJO.Sym.plethShift_macSubst`, as one identity of ring
  homomorphisms rather than one coefficient at a time.
* `HJO.Sym.dop_zero_macSubst`.
* `HJO.Sym.paramUInv_dopZeroEigenvalue`.
* `HJO.Sym.one_sub_mul_sum_pow_mul_pow_rowLen`.
* `HJO.Sym.dop_zero_macHtilde` and its standing-field form
  `HJO.Standing.dop_zero_macHtilde_param`: `HJO.Standing.dop_zero_smul_macHtilde_param` reduced to
  the **single** residual `HJO.Sym.IsEopEigenJfun`, `HJO.Sym.isEopEigenJfun`.

## The reduction

Of the four Section 4 results standing between `HJO/Macdonald/Htilde.lean` and equation (1.11) a),
three are proved here --- `HJO.Sym.dop_zero_macSubst`, `HJO.Sym.paramUInv_dopZeroEigenvalue`,
`HJO.Sym.one_sub_mul_sum_pow_mul_pow_rowLen` --- together with two of their inputs,
`HJO.Sym.plethShift_macSubst` and `HJO.Sym.map_completeHomog_eq_elemSymm`, and the three definitions
`HJO.Sym.plethCreateQ`, `HJO.Sym.plethMulU`, `HJO.Sym.eop`. The fourth, `HJO.Sym.isEopEigenJfun`, is
the residual: it is `HJO.Sym.IsEopEigenJfun`, and `HJO.Sym.dop_zero_macHtilde` derives the whole of
(1.11) a) from it and nothing else.

The proof of `HJO.Sym.isEopEigenJfun` rests on `HJO.Mac.dop_pleth` (Garsia--Haiman--Tesler
(4.10)) and its chain in the finite alphabet --- `HJO.Mac.macCoeff`,
`HJO.Mac.prod_C_sub_macCoeff_eq_add`, `HJO.Mac.one_sub_mul_sum_macCoeff`,
`HJO.Mac.sub_one_mul_sum_macCoeff_mul_pow`, `HJO.Mac.mk_restrictFrac_plethMulU_mul_prod`,
`HJO.Mac.sum_restrictFrac_coeff_plethCreateQ`, `HJO.Sym.coeff_plethCreateQ_eq_zero`,
`HJO.Sym.eop_mem_lambdaComp` --- plus `HJO.Mac.restrictAlphabet_macPfun_partDiagram`. None of those
is in this file.

## Where genericity is spent, and the two degenerate corners that bite

Everything here is spent on one scalar identity, `HJO.Sym.one_sub_pow_mul_inv_one_sub_inv_pow`:
`(1 - u^k)(1 - u^{-k})^{-1} = -u^k`. The usual argument reads it off `1 - u^{-k} = -u^{-k}(1 - u^k)`
by dividing, and neither `HJO.Sym.plethShift_macSubst` nor `HJO.Sym.dop_zero_macSubst` is usually
stated with **any** hypothesis for it. Both degenerate corners bite:

* **`u` a root of unity.** The identity is false: at `u^k = 1` the left side is `0 · 0^{-1} = 0` and
  the right side is `-1`. And `HJO.Sym.dop_zero_macSubst` itself is false there, not just this proof
  of it: at `u = -1` and `F = p_2`, `𝒴(ȷ(p_2)) = 0` because `𝒴`'s scalar `(1-u^{-2})^{-1}` vanishes,
  so the left side is `0`, while `ℰ(p_2) = p_2 - 2(1-q^2)p_1^2` gives
  `𝒴(ȷ(ℰ p_2)) = -(1-q^2)p_1^2/2 ≠ 0`. So `hu1 : ∀ k, u^{k+1} ≠ 1` is a genuine hypothesis, though
  it is usually left out.
* **`u = 0`.** Also false, and again not only in the proof: at `u = 0` Lean's `0⁻¹ = 0` makes `𝒴`
  and `𝒲` the identity while the displacement keeps its `(1-q^k)` term, so at `F = p_2` the left is
  `p_2 + (1-q^2)e_2` and the right side `p_2 - (1-q^2)h_2`, differing by `(1-q^2)p_1^2`. So
  `hu0 : u ≠ 0` is genuine.

Both come from `hqu` at the point of use (`HJO.Standing.u_ne_zero`,
`HJO.Standing.u_pow_succ_ne_one`), so `dop_zero_macHtilde` carries no parameter hypothesis beyond
`AlgebraicIndependent ℤ ![q, u]`.

In the other direction, `HJO.Sym.one_sub_mul_sum_pow_mul_pow_rowLen` needs **nothing**. The usual
proof divides the row sum by `1-q`, the geometric sum being valid because `1-q ≠ 0`; but
`(1-q)∑_{j<m}q^j = 1-q^m` holds in every commutative ring, so `q = 1` is not a corner and no
genericity is spent --- that lemma and the row decomposition `HJO.Sym.cellSum_eq_sum_rows` it runs
on are accordingly stated over a commutative ring and not over `𝕜`. Nor is `n ≥ 1` needed in
`HJO.Sym.paramUInv_dopZeroEigenvalue`, where both sides are `1` at `n = 0`, and
`HJO.Sym.dop_zero_macSubst` needs no grading hypothesis on `F` at all.

## References

A. M. Garsia, M. Haiman and G. Tesler, *Explicit plethystic formulas for Macdonald (q,t)-Kostka
coefficients*, Sém. Lothar. Combin. **42** (1999), B42m, Section 4 and Theorem 1.2 (1.11) a); their
`t` is written `u` here. -/

@[expose] public section

open Finset

/-! ### Substituting `a * X` in a polynomial -/

namespace Polynomial

/-- Substituting `a * X` multiplies the coefficient of `X^n` by `a^n`. This is the companion of
`Polynomial.coeff_comp_neg_X`, at a general scalar rather than at `-1`. -/
theorem coeff_comp_C_mul_X {R : Type*} [CommRing R] (a : R) (Q : Polynomial R) (n : ℕ) :
    (Q.comp (Polynomial.C a * Polynomial.X)).coeff n = a ^ n * Q.coeff n := by
  induction Q using Polynomial.induction_on' with
  | add p r hp hr =>
      rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hr, Polynomial.coeff_add, mul_add]
  | monomial k b =>
      have h1 : (Polynomial.monomial k b).comp (Polynomial.C a * Polynomial.X)
          = Polynomial.monomial k (b * a ^ k) := by
        rw [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow,
          Polynomial.X_pow_eq_monomial, ← mul_assoc, ← Polynomial.C_mul,
          Polynomial.C_mul_monomial, mul_one]
      rw [h1, Polynomial.coeff_monomial, Polynomial.coeff_monomial]
      by_cases h : k = n
      · subst h; simp [mul_comm]
      · simp [h]

end Polynomial

namespace HJO.Sym

/-! ### A ring endomorphism of the coefficients fixes the rationals -/

section RatFix

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **A ring endomorphism of a `ℚ`-algebra field fixes `ℚ`.** The structure map `ℚ → K` is the
rational cast, a ring homomorphism preserves it, and there is nothing to assume: the condition
"`υ` fixes `ℚ`" is a theorem rather than a clause of `HJO.Sym.paramUInv`. -/
theorem ringHom_algebraMap_rat (υ : K →+* K) (r : ℚ) :
    υ (algebraMap ℚ K r) = algebraMap ℚ K r := by
  rw [show algebraMap ℚ K r = (r : K) from eq_ratCast (algebraMap ℚ K) r, map_ratCast]

end RatFix

/-! ### The three objects of Garsia--Haiman--Tesler's Section 4 -/

section Objects

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The creation displacement of the first parameter** `qs`: the `𝕜`-algebra
homomorphism from `Λ` to the Laurent polynomials sending `p_k` to `p_k - (1 - q^k) z^{-k}`, written
`F[X - (1-q)/z]`.

Only nonpositive powers of `z` occur, so as with `HJO.Sym.plethShift` the target is the polynomial
ring in `w = z^{-1}`; the coefficient `[z^{-m}] qs(F)` is `Polynomial.coeff` at `m`. The scalar
subtracted from `p_k` is `1 - q^k` and not `(1 - q)^k`, the alphabet removed being the virtual
difference of `1/z` and `q/z`. -/
@[hjo "def_ght3_qshift"]
noncomputable def plethCreateQ (q : K) : Lambda K →ₐ[K] Polynomial (Lambda K) :=
  MvPolynomial.aeval fun i => Polynomial.C (powerSum K (i + 1)) -
    Polynomial.C (MvPolynomial.C (1 - q ^ (i + 1))) * Polynomial.X ^ (i + 1)

omit [Algebra ℚ K] in
/-- The displacement on a generator: the defining clause, read through the index shift
`p_k = X_{k-1}`. The hypothesis `k ≥ 1` is the definition's own and is not removable, `p_0` being
the generator `p_1`. -/
theorem plethCreateQ_powerSum (q : K) {k : ℕ} (hk : 1 ≤ k) :
    plethCreateQ q (powerSum K k) = Polynomial.C (powerSum K k) -
      Polynomial.C (MvPolynomial.C (1 - q ^ k)) * Polynomial.X ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [powerSum, Nat.add_sub_cancel]
  exact MvPolynomial.aeval_X _ m

omit [Algebra ℚ K] in
/-- **The constant coefficient of the displacement is the argument itself.** Both sides are ring
homomorphisms of `Λ`; each generator's image has constant coefficient the generator, the displaced
term carrying a positive power of `w`. -/
@[hjo "lem_ght3_qshift_const"]
theorem coeff_zero_plethCreateQ (q : K) (F : Lambda K) : (plethCreateQ q F).coeff 0 = F := by
  have h : (Polynomial.constantCoeff (R := Lambda K)).comp (plethCreateQ q).toRingHom
      = RingHom.id (Lambda K) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        ← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq]
      simp
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        show (MvPolynomial.X i : Lambda K) = powerSum K (i + 1) by rw [powerSum,
          Nat.add_sub_cancel], plethCreateQ_powerSum q (Nat.le_add_left 1 i)]
      simp [Polynomial.constantCoeff_apply]
  exact RingHom.congr_fun h F

/-- **The plethystic multiplication by the second parameter** `𝒲`, written
`F[(1-1/u)X]`: the `𝕜`-algebra endomorphism of `Λ` sending `p_k` to `(1 - u^{-k}) p_k`. Its scalars
are the reciprocals of those of `HJO.Sym.plethDivide`. The alphabet `(1-1/u)X` is the difference of
`X` and `u^{-1}X`, so the scalar is `1 - u^{-k}` and not `(1 - u^{-1})^k`. -/
@[hjo "def_ght3_pleth_mul"]
noncomputable def plethMulU (u : K) : Lambda K →ₐ[K] Lambda K :=
  diagScale fun i => 1 - u⁻¹ ^ (i + 1)

omit [Algebra ℚ K] in
/-- The plethystic multiplication on a generator: the defining clause. -/
theorem plethMulU_powerSum (u : K) {k : ℕ} (hk : 1 ≤ k) :
    plethMulU u (powerSum K k) = MvPolynomial.C (1 - u⁻¹ ^ k) * powerSum K k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [plethMulU, diagScale_powerSum, Nat.add_sub_cancel]

/-- **The plethystic form of Macdonald's operator** `ℰ`:
`ℰ(F) = ∑_{m ≥ 0} ([z^{-m}] qs(F)) 𝒲(h_m)`, a finite sum because `qs(F)` is a polynomial in
`w = z^{-1}`. It is `𝕜`-linear, `qs` being a `𝕜`-algebra homomorphism and the pairing
`𝕜`-linear. -/
@[hjo "def_ght3_eop"]
noncomputable def eop (q u : K) : Module.End K (Lambda K) :=
  coeffPairing (fun m => plethMulU u (completeHomog K m)) ∘ₗ (plethCreateQ q).toLinearMap

/-- The plethystic form as the pairing it is, evaluated at an element. -/
theorem eop_apply (q u : K) (F : Lambda K) :
    eop q u F = coeffPairing (fun m => plethMulU u (completeHomog K m)) (plethCreateQ q F) := rfl

end Objects

/-! ### The scalar identity behind the two substitutions

One identity carries both `HJO.Sym.plethShift_macSubst` and the computation of `𝒴(ȷ(𝒲(p_k)))` in
`HJO.Sym.dop_zero_macSubst`: `(1 - u^k)(1 - u^{-k})^{-1} = -u^k`. It is the identity
`1 - u^{-k} = -u^{-k}(1-u^k)` divided through, and dividing through is exactly what needs the
hypothesis the usual argument does not carry. -/

section Scalar

variable {K : Type*} [Field K] {u : K}

/-- **`(1 - u^k)(1 - u^{-k})^{-1} = -u^k`.**

Two corners, both genuine. At `u = 0` and `k ≥ 1` the left side is `1 · 0 = 0` and the right side is
`0`, so the identity survives; but the *proof* divides by `u^k`, and the companion form used in
`HJO.Sym.inv_one_sub_pow_eq` is false there, so `u ≠ 0` is carried. At a root of unity, `u^k = 1`,
the left side is `0 · 0⁻¹ = 0` and the right side is `-1`: the identity is **false**, and `hu1` is
not decoration. This is the hypothesis usually left out of `HJO.Sym.plethShift_macSubst` and
`HJO.Sym.dop_zero_macSubst` -- reading "so `(1-u^k)(1-u^{-k})^{-1} = -u^k`" off
`1 - u^{-k} = -u^{-k}(1-u^k)` divides by a factor that vanishes at every root of unity. -/
theorem one_sub_pow_mul_inv_one_sub_inv_pow (hu0 : u ≠ 0) {k : ℕ} (hu1 : u ^ k ≠ 1) :
    (1 - u ^ k) * (1 - u⁻¹ ^ k)⁻¹ = -u ^ k := by
  have hk : u ^ k ≠ 0 := pow_ne_zero k hu0
  have hne : (1 : K) - u ^ k ≠ 0 := sub_ne_zero.mpr fun h => hu1 h.symm
  have hfac : (1 : K) - u⁻¹ ^ k = -u⁻¹ ^ k * (1 - u ^ k) := by
    rw [inv_pow, neg_mul, mul_sub, mul_one, inv_mul_cancel₀ hk, neg_sub]
  rw [hfac, mul_inv, mul_comm ((-u⁻¹ ^ k)⁻¹), ← mul_assoc, mul_inv_cancel₀ hne, one_mul,
    inv_neg, inv_pow, inv_inv]

end Scalar

/-! ### The complete homogeneous functions under a signed rescaling -/

section WmulHsymm

variable {K : Type*} [Field K] [Algebra ℚ K] {u : K}

omit [Algebra ℚ K] in
/-- Two scalar factors of a product of two terms collect into one. -/
theorem c_mul_mul_c_mul (a b : K) (f g : Lambda K) :
    MvPolynomial.C a * f * (MvPolynomial.C b * g) = MvPolynomial.C (a * b) * (f * g) := by
  rw [map_mul]; ring

omit [Algebra ℚ K] in
/-- Two nested scalar factors collect into one. -/
theorem c_mul_c_mul (a b : K) (f : Lambda K) :
    MvPolynomial.C a * (MvPolynomial.C b * f) = MvPolynomial.C (a * b) * f := by
  rw [map_mul, mul_assoc]

omit [Algebra ℚ K] in
/-- The sign of a truncated difference splits, the two signs agreeing in parity. -/
theorem neg_one_pow_sub {m j : ℕ} (hj : j ≤ m) :
    (-1 : K) ^ (m - j) = (-1 : K) ^ m * (-1 : K) ^ j := by
  obtain ⟨t, rfl⟩ : ∃ t, m = j + t := ⟨m - j, by omega⟩
  rw [Nat.add_sub_cancel_left, pow_add,
    show (-1 : K) ^ j * (-1 : K) ^ t * (-1 : K) ^ j
      = (-1 : K) ^ t * ((-1 : K) ^ j * (-1 : K) ^ j) from by ring, ← pow_add,
    show j + j = 2 * j from by omega, pow_mul]
  norm_num

/-- **The complete homogeneous functions under a signed rescaling**,
`HJO.Sym.map_completeHomog_eq_elemSymm`: a ring endomorphism `τ` of `Λ` fixing the rational
constants and sending `p_k` to `-u^k p_k` sends `h_r` to `(-1)^r u^r e_r`.

The lemma is usually stated for a `𝕜`-algebra endomorphism, but the composite it is applied to
(`𝒴 ∘ ȷ ∘ 𝒲`) is **not** `𝕜`-linear --- `ȷ` twists the coefficients by `υ` --- so the hypothesis
here is the weaker one the proof uses: `τ` fixes `ℚ`, which is what the two Newton
recursions need, their coefficients being rational. -/
@[hjo "lem_ght3_wmul_hsymm"]
theorem map_completeHomog_eq_elemSymm {τ : Lambda K →+* Lambda K}
    (hQ : ∀ r : ℚ, τ (MvPolynomial.C (algebraMap ℚ K r)) = MvPolynomial.C (algebraMap ℚ K r))
    (hp : ∀ k : ℕ, τ (powerSum K (k + 1)) = MvPolynomial.C (-u ^ (k + 1)) * powerSum K (k + 1)) :
    ∀ r : ℕ, τ (completeHomog K r) = MvPolynomial.C ((-1 : K) ^ r * u ^ r) * elemSymm K r
  | 0 => by
      rw [completeHomog, elemSymm, map_one, pow_zero, pow_zero, one_mul, map_one, mul_one]
  | n + 1 => by
      have hterm : ∀ k ∈ range (n + 1),
          τ (powerSum K (k + 1) * completeHomog K (n - k))
            = MvPolynomial.C ((-1 : K) ^ (n + 1) * u ^ (n + 1)) *
              ((-1 : Lambda K) ^ k * powerSum K (k + 1) * elemSymm K (n - k)) := by
        intro k hk
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hC : ((-1 : Lambda K)) ^ k = MvPolynomial.C ((-1 : K) ^ k) := by
          rw [map_pow, map_neg, map_one]
        have hupow : u ^ (k + 1) * u ^ (n - k) = u ^ (n + 1) := by
          rw [← pow_add]; congr 1; omega
        have hscal : -u ^ (k + 1) * ((-1 : K) ^ (n - k) * u ^ (n - k))
            = (-1 : K) ^ (n + 1) * u ^ (n + 1) * (-1 : K) ^ k := by
          rw [neg_one_pow_sub hkn, ← hupow, pow_succ ((-1 : K)) n]
          ring
        rw [map_mul, hp k, map_completeHomog_eq_elemSymm hQ hp (n - k), c_mul_mul_c_mul, hC,
          mul_assoc, c_mul_c_mul, hscal]
      rw [completeHomog, map_mul, hQ, map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        elemSymm]
      ring

end WmulHsymm

/-! ### The two substitutions carry the plethystic form to the degree-zero operator -/

section Transport

variable {K : Type*} [Field K] [Algebra ℚ K] {u : K} {υ : K →+* K}

/-- **The two substitutions of `HJO.Sym.macHtilde` as one ring endomorphism of `Λ`**: `F ↦ 𝒴(ȷ(F))`.
It is not `𝕜`-linear --- `ȷ` twists the coefficients by `υ` --- so it is a `RingHom` and not an
`AlgHom`, and that is exactly why `HJO.Sym.map_completeHomog_eq_elemSymm` is proved here for a ring
endomorphism fixing `ℚ`. -/
noncomputable def macSubst (υ : K →+* K) (u : K) : Lambda K →+* Lambda K :=
  (plethDivide u).toRingHom.comp (coeffSubst υ)

omit [Algebra ℚ K] in
/-- The composite as the two substitutions it is, evaluated at an element: `ȷ` first, then `𝒴`. -/
theorem macSubst_apply (F : Lambda K) : macSubst υ u F = plethDivide u (coeffSubst υ F) := rfl

omit [Algebra ℚ K] in
/-- The composite twists a scalar by `υ`, `𝒴` fixing the scalars. -/
theorem macSubst_C (a : K) : macSubst υ u (MvPolynomial.C a) = MvPolynomial.C (υ a) := by
  rw [macSubst_apply, coeffSubst_C, plethDivide, diagScale_C]

omit [Algebra ℚ K] in
/-- The composite on a generator: `ȷ` fixes `p_k` and `𝒴` scales it. -/
theorem macSubst_powerSum {k : ℕ} (hk : 1 ≤ k) :
    macSubst υ u (powerSum K k) = MvPolynomial.C ((1 - u⁻¹ ^ k)⁻¹) * powerSum K k := by
  rw [macSubst_apply, coeffSubst_powerSum, plethDivide_powerSum u hk]

/-- **Rescaling the displacement variable** `ρ`: the ring endomorphism of `Λ[w]`
sending `w` to `t w`. Read in `z`, it multiplies the coefficient of `z^{-m}` by `t^m`. -/
noncomputable def scaleW (t : K) : Polynomial (Lambda K) →+* Polynomial (Lambda K) :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.C (MvPolynomial.C t) * Polynomial.X)

omit [Algebra ℚ K] in
/-- The rescaling as the substitution `w ↦ t w` it is, evaluated at a polynomial. -/
theorem scaleW_apply (t : K) (P : Polynomial (Lambda K)) :
    scaleW t P = P.comp (Polynomial.C (MvPolynomial.C t) * Polynomial.X) := rfl

omit [Algebra ℚ K] in
/-- The rescaling multiplies the coefficient of `w^m` by `t^m`. -/
theorem coeff_scaleW (t : K) (P : Polynomial (Lambda K)) (m : ℕ) :
    (scaleW t P).coeff m = MvPolynomial.C (t ^ m) * P.coeff m := by
  rw [scaleW_apply, Polynomial.coeff_comp_C_mul_X, ← map_pow]

omit [Algebra ℚ K] in
/-- The rescaling fixes the coefficients, `w` occurring in none of them. -/
theorem scaleW_C (t : K) (g : Lambda K) : scaleW t (Polynomial.C g) = Polynomial.C g := by
  rw [scaleW_apply, Polynomial.C_comp]

omit [Algebra ℚ K] in
/-- The rescaling on a power of the displacement variable. -/
theorem scaleW_X_pow (t : K) (m : ℕ) :
    scaleW t ((Polynomial.X : Polynomial (Lambda K)) ^ m)
      = Polynomial.C (MvPolynomial.C (t ^ m)) * Polynomial.X ^ m := by
  rw [scaleW_apply, Polynomial.pow_comp, Polynomial.X_comp, mul_pow, ← map_pow, ← map_pow]

omit [Algebra ℚ K] in
/-- The displacement `qs` fixes the scalars, being an algebra map. -/
theorem plethCreateQ_C (q a : K) :
    plethCreateQ q (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  simp [MvPolynomial.algebraMap_eq]

omit [Algebra ℚ K] in
/-- The displacement on a generator, spelled out. -/
theorem plethShift_powerSum (q : K) {k : ℕ} (hk : 1 ≤ k) :
    plethShift q u (powerSum K k) = Polynomial.C (powerSum K k) +
      Polynomial.C (MvPolynomial.C ((1 - q ^ k) * (1 - u ^ k))) * Polynomial.X ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [powerSum, Nat.add_sub_cancel, plethShift]
  exact MvPolynomial.aeval_X _ m

omit [Algebra ℚ K] in
/-- **The two displacements after the two substitutions**,
`HJO.Sym.plethShift_macSubst`, as one identity of ring homomorphisms `Λ → Λ[w]` rather than one
coefficient at a time: `δ ∘ 𝒴 ∘ ȷ = ρ_u ∘ 𝒴̂ ∘ ȷ̂ ∘ qs`.

Taking the coefficient of `w^m` gives
`[z^{-m}] δ(𝒴(ȷ F)) = u^m 𝒴(ȷ([z^{-m}] qs F))` (`coeff_plethShift_macSubst`).

Both sides are ring homomorphisms restricting to `υ` on `𝕜`, so it is enough to compare them at a
scalar and at each `p_k`; at `p_k` the comparison is the single scalar identity
`(1 - u^k)(1 - u^{-k})^{-1} = -u^k`, whose hypotheses `hu0` and `hu1` are usually left out of the
statement. -/
@[hjo "lem_ght3_coefficient_transport"]
theorem plethShift_macSubst (hu0 : u ≠ 0) (hu1 : ∀ k : ℕ, u ^ (k + 1) ≠ 1) {q : K}
    (hυq : υ q = q) (hυu : υ u = u⁻¹) (F : Lambda K) :
    plethShift q u (macSubst υ u F) = scaleW u ((plethCreateQ q F).map (macSubst υ u)) := by
  have hυui : υ u⁻¹ = u := by rw [map_inv₀, hυu, inv_inv]
  have hgen : ∀ i : ℕ, plethShift q u (macSubst υ u (powerSum K (i + 1)))
      = scaleW u ((plethCreateQ q (powerSum K (i + 1))).map (macSubst υ u)) := by
    intro i
    have h1i : 1 ≤ i + 1 := Nat.le_add_left 1 i
    have hkey : (1 - u ^ (i + 1)) * (1 - u⁻¹ ^ (i + 1))⁻¹ = -u ^ (i + 1) :=
      one_sub_pow_mul_inv_one_sub_inv_pow hu0 (hu1 i)
    have hq : υ (1 - q ^ (i + 1)) = 1 - q ^ (i + 1) := by
      rw [map_sub, map_one, map_pow, hυq]
    have hscal : (1 - u⁻¹ ^ (i + 1))⁻¹ * ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))
        = -((1 - q ^ (i + 1)) * u ^ (i + 1)) := by
      rw [show (1 - u⁻¹ ^ (i + 1))⁻¹ * ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))
        = (1 - q ^ (i + 1)) * ((1 - u ^ (i + 1)) * (1 - u⁻¹ ^ (i + 1))⁻¹) from by ring, hkey]
      ring
    have hL : plethShift q u (macSubst υ u (powerSum K (i + 1)))
        = Polynomial.C (MvPolynomial.C ((1 - u⁻¹ ^ (i + 1))⁻¹) * powerSum K (i + 1))
          + Polynomial.C (MvPolynomial.C ((1 - u⁻¹ ^ (i + 1))⁻¹ *
              ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1))))) * Polynomial.X ^ (i + 1) := by
      rw [macSubst_powerSum h1i, map_mul, plethShift_C, plethShift_powerSum q h1i, mul_add,
        ← Polynomial.C_mul, ← mul_assoc, ← Polynomial.C_mul, ← MvPolynomial.C_mul]
    have hR : scaleW u ((plethCreateQ q (powerSum K (i + 1))).map (macSubst υ u))
        = Polynomial.C (MvPolynomial.C ((1 - u⁻¹ ^ (i + 1))⁻¹) * powerSum K (i + 1))
          - Polynomial.C (MvPolynomial.C ((1 - q ^ (i + 1)) * u ^ (i + 1))) *
              Polynomial.X ^ (i + 1) := by
      rw [plethCreateQ_powerSum q h1i, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, macSubst_C, hq,
        macSubst_powerSum h1i, map_sub (scaleW u), map_mul (scaleW u), scaleW_C, scaleW_C,
        scaleW_X_pow, ← mul_assoc, ← Polynomial.C_mul, ← MvPolynomial.C_mul]
    rw [hL, hR, hscal, map_neg, map_neg]
    ring
  have h : ((plethShift q u).toRingHom).comp (macSubst υ u)
      = (scaleW u).comp ((Polynomial.mapRingHom (macSubst υ u)).comp
          (plethCreateQ q).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, macSubst_C,
        plethShift_C, Polynomial.coe_mapRingHom, plethCreateQ_C, Polynomial.map_C, scaleW_C]
    · rw [show (MvPolynomial.X i : Lambda K) = powerSum K (i + 1) from by
        rw [powerSum, Nat.add_sub_cancel]]
      simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.coe_mapRingHom] using hgen i
  exact RingHom.congr_fun h F

omit [Algebra ℚ K] in
/-- **The coefficientwise form of `HJO.Sym.plethShift_macSubst`**, the display:
`[z^{-m}] δ(𝒴(ȷ F)) = u^m 𝒴(ȷ([z^{-m}] qs F))`. -/
theorem coeff_plethShift_macSubst (hu0 : u ≠ 0) (hu1 : ∀ k : ℕ, u ^ (k + 1) ≠ 1) {q : K}
    (hυq : υ q = q) (hυu : υ u = u⁻¹) (F : Lambda K) (m : ℕ) :
    (plethShift q u (macSubst υ u F)).coeff m
      = MvPolynomial.C (u ^ m) * macSubst υ u ((plethCreateQ q F).coeff m) := by
  rw [plethShift_macSubst hu0 hu1 hυq hυu F, coeff_scaleW, Polynomial.coeff_map]

/-- **`𝒴(ȷ(𝒲(h_r))) = (-1)^r u^r e_r`**, the identification made inside
`HJO.Sym.dop_zero_macSubst`: the composite `𝒴 ∘ ȷ ∘ 𝒲` is a ring endomorphism of `Λ` fixing `ℚ` and
sending `p_k` to `-u^k p_k`, so `HJO.Sym.map_completeHomog_eq_elemSymm` applies. -/
theorem macSubst_plethMulU_completeHomog (hu0 : u ≠ 0) (hu1 : ∀ k : ℕ, u ^ (k + 1) ≠ 1)
    (hυu : υ u = u⁻¹) (r : ℕ) :
    macSubst υ u (plethMulU u (completeHomog K r))
      = MvPolynomial.C ((-1 : K) ^ r * u ^ r) * elemSymm K r := by
  have hυui : υ u⁻¹ = u := by rw [map_inv₀, hυu, inv_inv]
  refine map_completeHomog_eq_elemSymm (τ := (macSubst υ u).comp (plethMulU u).toRingHom)
    (fun s => ?_) (fun k => ?_) r
  · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, plethMulU, diagScale_C,
      macSubst_C, ringHom_algebraMap_rat]
  · have h1k : 1 ≤ k + 1 := Nat.le_add_left 1 k
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, plethMulU_powerSum u h1k,
      map_mul, macSubst_C, macSubst_powerSum h1k, map_sub, map_one, map_pow, hυui, c_mul_c_mul,
      one_sub_pow_mul_inv_one_sub_inv_pow hu0 (hu1 k)]

/-- **The two substitutions carry the plethystic form to the degree-zero operator**,
`HJO.Sym.dop_zero_macSubst`: `D_0(𝒴(ȷ F)) = 𝒴(ȷ(ℰ F))`.

The identity is usually stated for `F ∈ Λ_d`; nothing here asks for that, and the statement is
proved for every `F ∈ Λ`. Both sides are the *same* finite sum term by term: the `j`-th coefficient
of the displaced `𝒴(ȷ F)` is `u^j 𝒴(ȷ(g_j))` (`coeff_plethShift_macSubst`) and the `j`-th factor of
`ℰ` is carried to `(-1)^j u^j e_j` (`macSubst_plethMulU_completeHomog`), so no grading and no
comparison of coefficients in a basis is needed.

The hypotheses `hu0` and `hu1` come from the scalar identity
`one_sub_pow_mul_inv_one_sub_inv_pow` and are the ones usually left out. -/
@[hjo "lem_ght3_transport"]
theorem dop_zero_macSubst (hu0 : u ≠ 0) (hu1 : ∀ k : ℕ, u ^ (k + 1) ≠ 1) {q : K}
    (hυq : υ q = q) (hυu : υ u = u⁻¹) (F : Lambda K) :
    Dop q u 0 (macSubst υ u F) = macSubst υ u (eop q u F) := by
  have htr := plethShift_macSubst hu0 hu1 hυq hυu F
  have hdegR : ∀ m : ℕ, (plethCreateQ q F).natDegree + 1 ≤ m → (plethCreateQ q F).coeff m = 0 :=
    fun m hm => Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hdegL : ∀ j : ℕ, (plethCreateQ q F).natDegree + 1 ≤ j →
      (plethShift q u (macSubst υ u F)).coeff j = 0 := by
    intro j hj
    rw [htr, coeff_scaleW, Polynomial.coeff_map, hdegR j hj, map_zero, mul_zero]
  rw [dop_apply, coeffPairing_eq_sum_range _ _ hdegL, eop_apply,
    coeffPairing_eq_sum_range _ _ hdegR, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [zero_add]
  rw [htr, coeff_scaleW, Polynomial.coeff_map, map_mul,
    macSubst_plethMulU_completeHomog hu0 hu1 hυu j,
    show ((-1 : Lambda K)) ^ j = MvPolynomial.C ((-1 : K) ^ j) from by
      rw [map_pow, map_neg, map_one], MvPolynomial.C_mul]
  ring

end Transport

/-! ### The eigenvalue after inverting the second parameter -/

section Eigenvalue

variable {K : Type*} [Field K] {u : K} {υ : K →+* K}

/-- **The eigenvalue after inverting the second parameter**,
`HJO.Sym.paramUInv_dopZeroEigenvalue`:
`υ(u^{-n}(1 - (1-u)E_n(μ))) = u^n + (1-u)∑_{i=1}^{n} u^{i-1} q^{μ_i}`.

The hypothesis `n ≥ 1` is not needed --- at `n = 0` both sides are `1` --- but `u ≠ 0` is: the
computation cancels `u^n` against `u^{-(n-1-i)}`, which is a division, and the statement
carries no hypothesis at all. -/
@[hjo "lem_ght3_eigenvalue_uinv"]
theorem paramUInv_dopZeroEigenvalue {q : K} (hυq : υ q = q) (hυu : υ u = u⁻¹) (hu0 : u ≠ 0)
    (μ : YoungDiagram) (n : ℕ) :
    υ (u⁻¹ ^ n * (1 - (1 - u) * macdonaldEigenvalue q u n μ))
      = u ^ n + (1 - u) * ∑ i ∈ range n, u ^ i * q ^ μ.rowLen i := by
  have hui : υ u⁻¹ = u := by rw [map_inv₀, hυu, inv_inv]
  have hterm : ∀ i ∈ range n, (1 - u⁻¹) * (u ^ n * υ (q ^ μ.rowLen i * u ^ (n - 1 - i)))
      = -((1 - u) * (u ^ i * q ^ μ.rowLen i)) := by
    intro i hi
    have hi : i < n := Finset.mem_range.mp hi
    have hsplit : u ^ n = u ^ (i + 1) * u ^ (n - 1 - i) := by
      rw [← pow_add]; congr 1; omega
    have hpow : u ^ n * u⁻¹ ^ (n - 1 - i) = u ^ (i + 1) := by
      rw [inv_pow, hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu0), mul_one]
    have hstep : u ^ (i + 1) * (1 - u⁻¹) = u ^ (i + 1) - u ^ i := by
      rw [mul_sub, mul_one, pow_succ, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
    rw [map_mul, map_pow, map_pow, hυq, hυu, show u ^ n * (q ^ μ.rowLen i * u⁻¹ ^ (n - 1 - i))
      = q ^ μ.rowLen i * (u ^ n * u⁻¹ ^ (n - 1 - i)) from by ring, hpow, mul_comm (1 - u⁻¹),
      mul_assoc, hstep, pow_succ]
    ring
  rw [macdonaldEigenvalue, map_mul, map_pow, hui, map_sub, map_one, map_mul, map_sub, map_one,
    hυu, map_sum, mul_sub, mul_one, ← mul_assoc, mul_comm (u ^ n), mul_assoc, Finset.mul_sum,
    Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, Finset.mul_sum]
  ring

end Eigenvalue

/-! ### The eigenvalue against the cell sum, over any commutative ring -/

section CellSum

variable {K : Type*} [CommRing K]

/-- **The cell sum by rows**: `B_μ = ∑_{i<n} u^i ∑_{j<μ_i} q^j` once `μ_n = 0`. The cells in row `i`
are the `(i,j)` with `j < μ_i`, and the rows beyond `n` are empty, `μ` being weakly decreasing. -/
theorem cellSum_eq_sum_rows (q u : K) {μ : YoungDiagram} {n : ℕ} (hn : μ.rowLen n = 0) :
    cellSum q u μ = ∑ i ∈ range n, ∑ j ∈ range (μ.rowLen i), q ^ j * u ^ i := by
  have hcells : μ.cells = (range n).biUnion fun i => {i} ×ˢ range (μ.rowLen i) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product, Finset.mem_singleton,
      YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
    constructor
    · refine fun hj => ⟨i, lt_of_not_ge fun hi => ?_, rfl, hj⟩
      exact absurd (Nat.le_zero.mp (hn ▸ μ.rowLen_anti n i hi) ▸ hj) (Nat.not_lt_zero j)
    · rintro ⟨a, -, rfl, hj⟩
      exact hj
  change ∑ c ∈ μ.cells, cellWeight q u c = _
  rw [hcells, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.singleton_product]
    simp [cellWeight]
  · intro a _ b _ hab
    simp only [Finset.disjoint_left, Finset.mem_product, Finset.mem_singleton]
    rintro ⟨x, y⟩ ⟨hx, -⟩ ⟨hx', -⟩
    exact hab (hx ▸ hx')

/-- **The eigenvalue against the cell sum**, `HJO.Sym.one_sub_mul_sum_pow_mul_pow_rowLen`:
`(1-u)∑_{i=1}^{n} u^{i-1} q^{μ_i} = -u^n - (M B_μ - 1)` when `μ_{n+1} = 0`.

**No hypothesis on the parameters at all, and no field.** The usual proof divides the row sum
by `1 - q`, the geometric sum being valid because `1 - q ≠ 0`; but the identity
`(1-q)∑_{j<m} q^j = 1-q^m` holds in every commutative ring, so nothing is spent here, and in
particular `q = 1` is not a corner. Both sides are polynomials in `q` and `u`, so the identity is
stated over a commutative ring: a caller over `ℤ[q, u]` uses it without embedding into a field. -/
@[hjo "lem_ght3_bmu_eigenvalue"]
theorem one_sub_mul_sum_pow_mul_pow_rowLen (q u : K) {μ : YoungDiagram} {n : ℕ}
    (hn : μ.rowLen n = 0) :
    (1 - u) * ∑ i ∈ range n, u ^ i * q ^ μ.rowLen i
      = -u ^ n - (paramProduct q u * cellSum q u μ - 1) := by
  have h2 : paramProduct q u * cellSum q u μ
      = (1 - u) * ∑ i ∈ range n, u ^ i * (1 - q ^ μ.rowLen i) := by
    rw [cellSum_eq_sum_rows q u hn, paramProduct, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, ← mul_neg_geom_sum q (μ.rowLen i)]
    ring
  have h5 : ∑ i ∈ range n, u ^ i * (1 - q ^ μ.rowLen i)
      = (∑ i ∈ range n, u ^ i) - ∑ i ∈ range n, u ^ i * q ^ μ.rowLen i := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [h2, h5, mul_sub, mul_neg_geom_sum u n]
  ring

end CellSum

/-! ### Equation (1.11) a), reduced to `HJO.Sym.isEopEigenJfun` -/

section Assembly

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

omit [Algebra ℚ K] in
/-- The two substitutions twist a scalar by `υ`: `ȷ` is not `𝕜`-linear, `𝒴` is. -/
theorem macSubst_smul {υ : K →+* K} (c : K) (F : Lambda K) :
    macSubst υ u (c • F) = υ c • macSubst υ u F := by
  rw [macSubst_apply, macSubst_apply, coeffSubst_smul, map_smul]

/-- **The one residual of Garsia--Haiman--Tesler's Section 4**: their equation (4.24),
`HJO.Sym.isEopEigenJfun`, `u^n ℰ(J_μ) = (1 - (1-u)E_n(μ)) J_μ` at `n = max(|μ|, 1)`, written
with the `u^n` divided across.

**This is a hypothesis, not a theorem.** It is a `Prop`: nothing below proves it. What it *is* is
the honest residual --- `HJO.Sym.dop_zero_macHtilde` proves
`HJO.Standing.dop_zero_smul_macHtilde_param` from this and nothing else, so the whole of (1.11) a)
rests on this single statement.

It is proved as `HJO.Sym.isEopEigenJfun`, whose proof rests on `HJO.Mac.dop_pleth` (their (4.10))
--- and through it `HJO.Mac.macCoeff`, `HJO.Mac.prod_C_sub_macCoeff_eq_add`,
`HJO.Mac.one_sub_mul_sum_macCoeff`, `HJO.Mac.sub_one_mul_sum_macCoeff_mul_pow`,
`HJO.Mac.mk_restrictFrac_plethMulU_mul_prod`, `HJO.Mac.sum_restrictFrac_coeff_plethCreateQ`,
`HJO.Sym.coeff_plethCreateQ_eq_zero` and `HJO.Sym.eop_mem_lambdaComp` --- together with
`HJO.Mac.restrictAlphabet_macPfun_partDiagram` and the eigen-equation of `HJO.Mac.macPpoly` in the
finite alphabet. None of those is in this file. -/
def IsEopEigenJfun (hqu : AlgebraicIndependent ℤ ![(q : K), u]) : Prop :=
  ∀ μ : YoungDiagram, eop (q : K) u (macJfun hqu μ)
    = (u⁻¹ ^ max μ.card 1 *
        (1 - (1 - u) * macdonaldEigenvalue (q : K) u (max μ.card 1) μ)) • macJfun hqu μ

/-- **Garsia--Haiman--Tesler, Theorem 1.2, equation (1.11) a)**, that is
`HJO.Standing.dop_zero_smul_macHtilde_param`: `D_0 H̃_μ = -(M B_μ - 1) H̃_μ`, reduced to
`IsEopEigenJfun`.

This is clause `(b)` of `HJO.Sym.IsUnnormalisedMacdonaldEigenbasis` for the constructed family, and
it is the hypothesis `hdop` of `HJO.Sym.hasUnnormalisedMacdonaldEigenbasis_macHtilde`.

The chain is the usual one, with nothing expanded in a basis: `H̃_μ = u^{n(μ)} 𝒴(ȷ(J_μ))` by
`HJO.Sym.macHtilde`, `D_0` is `𝕜`-linear, `HJO.Sym.dop_zero_macSubst` moves
`D_0` across the two substitutions onto `ℰ`, `IsEopEigenJfun` replaces `ℰ(J_μ)` by a scalar
multiple, the scalar comes back out twisted by `υ` (`macSubst_smul`), and
`HJO.Sym.paramUInv_dopZeroEigenvalue` followed by `HJO.Sym.one_sub_mul_sum_pow_mul_pow_rowLen`
identify that twisted scalar as `-(M B_μ - 1)`.

**Not the statement itself.** `heop` is a hypothesis `HJO.Standing.dop_zero_smul_macHtilde_param`
does not carry, so this declaration does not state that result --- the same relation as between
`HJO.Sym.elemSymm_one_mul_mem_of_dop_zero` and
`HJO.Standing.elemSymm_one_mul_mem_span_of_dop_zero_param`. What is missing for it is exactly
`IsEopEigenJfun`. The genericity `hqu` and the two defining properties of `υ` are a different
matter: they are not weakenings, `𝕜 = ℚ(q,u)` supplies both.

**`B_μ` is not expanded over cells here.** The only place the cells are touched is
`cellSum_eq_sum_rows`, inside `HJO.Sym.one_sub_mul_sum_pow_mul_pow_rowLen`, where the row
decomposition and `(1-q)∑_{j<m} q^j = 1-q^m` do the whole of it; the hook-length identities
`HJO.Sym.cellProd_eq_pow_sum_cellArm_mul_pow_sum_cellLeg`, `HJO.Sym.sum_cellLeg`,
`HJO.Sym.sum_cellArm`, `HJO.Sym.cellArm` and `HJO.Sym.cellLeg` are not on this route either.

Genericity is spent only through `hqu`, and only on `u ≠ 0` (`HJO.Standing.u_ne_zero`) and
`u^{k+1} ≠ 1` (`HJO.Standing.u_pow_succ_ne_one`); the second is the root-of-unity corner that makes
`HJO.Sym.dop_zero_macSubst` false without it. -/
theorem dop_zero_macHtilde {υ : K →+* K} (hυq : υ (q : K) = (q : K)) (hυu : υ u = u⁻¹)
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (heop : IsEopEigenJfun hqu) (μ : YoungDiagram) :
    Dop (q : K) u 0 (macHtilde υ hqu μ)
      = -(paramProduct (q : K) u * cellSum (q : K) u μ - 1) • macHtilde υ hqu μ := by
  have hu0 : u ≠ 0 := HJO.Standing.u_ne_zero hqu
  have hu1 : ∀ k : ℕ, u ^ (k + 1) ≠ 1 := HJO.Standing.u_pow_succ_ne_one hqu
  have hrow : μ.rowLen (max μ.card 1) = 0 :=
    HJO.Mac.rowLen_eq_zero_of_card_le (le_max_left _ _)
  have hval : υ (u⁻¹ ^ max μ.card 1 *
      (1 - (1 - u) * macdonaldEigenvalue (q : K) u (max μ.card 1) μ))
      = -(paramProduct (q : K) u * cellSum (q : K) u μ - 1) := by
    rw [paramUInv_dopZeroEigenvalue hυq hυu hu0 μ (max μ.card 1),
      one_sub_mul_sum_pow_mul_pow_rowLen (q : K) u hrow]
    ring
  have hH : macHtilde υ hqu μ = u ^ rowOffsetSum μ • macSubst υ u (macJfun hqu μ) := rfl
  rw [hH, map_smul, dop_zero_macSubst hu0 hu1 hυq hυu, heop μ, macSubst_smul, hval, smul_comm]

end Assembly

end HJO.Sym

/-! ### Equation (1.11) a) at the standing field -/

namespace HJO.Standing

open HJO.Ascent HJO.Sym

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- **Equation (1.11) a) at the standing field `𝕜 = ℚ(q, u)`**, in exactly the shape the hypothesis
`hdop` of `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param` asks for. The two
conditions on the inversion `υ` are theorems here
(`HJO.Sym.paramUInvHom_paramQ` and `HJO.Sym.paramUInvHom_paramU`), so the only hypothesis left is
the residual `HJO.Sym.IsEopEigenJfun`. Like `HJO.Sym.dop_zero_macHtilde`, it carries the
hypothesis `heop`, which equation (1.11) a) itself does not. -/
theorem dop_zero_macHtilde_param
    (heop : IsEopEigenJfun (algebraicIndependent_paramQUnit K)) (μ : YoungDiagram) :
    Dop (paramQ K) (paramU K) 0
        (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ)
      = -(paramProduct (paramQ K) (paramU K) * cellSum (paramQ K) (paramU K) μ - 1) •
          macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ :=
  dop_zero_macHtilde (paramUInvHom_paramQ K) (paramUInvHom_paramU K)
    (algebraicIndependent_paramQUnit K) heop μ

end HJO.Standing
