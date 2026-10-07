/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.DopZeroHtilde
public import HJO.Shuffle.Grading
public meta import HJO.Attr

/-! # Garsia--Haiman--Tesler's equation (4.24), and equation (1.11) a) unconditionally

`HJO/Macdonald/DopZeroHtilde.lean` reduced Garsia--Haiman--Tesler's Theorem 1.2, equation
(1.11) a) --- `HJO.Standing.dop_zero_smul_macHtilde_param` --- to the single residual
`HJO.Sym.IsEopEigenJfun`, `HJO.Sym.isEopEigenJfun`. This file proves that residual and
so closes (1.11) a).

## The route

Everything rests on one generating-function identity and one polynomial identity, both in the
finite alphabet.

* The `h`-series of an alphabet. The generating series `∑_m φ(h_m) w^m` of a homomorphism out of
  `Λ` is multiplicative in the alphabet (`HJO.Sym.completeHomog_of_add`, already proved), so the
  series of a *negated* finite alphabet is the polynomial `∏_j (1 - a_j w)`
  (`HJO.Sym.mk_completeHomog_alphabetHom_neg_one`) and the series of a positive one is its inverse
  (`HJO.Sym.mk_completeHomog_mul_prod_eq_one`). Subtracting `u^{-1}x` from `x` therefore gives
  `(∑_m res_n(𝒲(h_m)) w^m) ∏_i (1 - w x_i) = ∏_i (1 - u^{-1} w x_i)`
  (`HJO.Mac.mk_restrictFrac_plethMulU_mul_prod`).
* The partial fraction identity `HJO.Mac.prod_C_sub_eq_add`
  (`HJO.Mac.prod_C_sub_macCoeff_eq_add`): the difference of the two sides has degree below `n` and
  vanishes at the `n` distinct points `x_i^{-1}`.

Multiplying the second by the `h`-series and reading off the coefficient of `w^m` gives
`HJO.Mac.pow_card_mul_restrictFrac_plethMulU_completeHomog`,
`u^n res_n(𝒲(h_m)) = [m = 0] + (u-1) ∑_i A_i x_i^m`, which is `HJO.Mac.one_sub_mul_sum_macCoeff` and
`HJO.Mac.sub_one_mul_sum_macCoeff_mul_pow` at once. Pairing that against the displacement, whose
evaluation at `w = x_i` is the parameter shift `T_{q,x_i}` (`HJO.Mac.qShift_restrictFrac`,
`HJO.Mac.sum_restrictFrac_coeff_plethCreateQ`), gives `HJO.Mac.dop_pleth`, their (4.10). At
`F = J_μ` the eigen-property of `P_μ[X_{n_μ}]` from `HJO.Mac.macPpoly` turns that into (4.24), and
`HJO.Sym.restrictAlphabetComp_bijective` lifts it from the alphabet back to `Λ`, both sides lying in
`Λ_{|μ|}` by `HJO.Sym.eop_mem_lambdaComp`.

## Main results

* `HJO.Sym.isEopEigenJfun`: `HJO.Sym.IsEopEigenJfun`, their (4.24).
* `HJO.Standing.dop_zero_smul_macHtilde_param`: equation (1.11) a) at
  the standing field `𝕜 = ℚ(q,u)`, with **no hypothesis left**. This is exactly the hypothesis
  `hdop` of `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param`, and
  `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param_of_span` feeds it.
* `HJO.Mac.prod_C_sub_eq_add` (`HJO.Mac.prod_C_sub_macCoeff_eq_add`),
  `HJO.Mac.mk_restrictFrac_plethMulU_mul_prod`,
  `HJO.Mac.one_sub_mul_sum_macCoeff`,
  `HJO.Mac.sub_one_mul_sum_macCoeff_mul_pow`,
  `HJO.Mac.sum_restrictFrac_coeff_plethCreateQ`,
  `HJO.Sym.coeff_plethCreateQ_mem_lambdaComp`,
  `HJO.Sym.coeff_plethCreateQ_eq_zero`,
  `HJO.Sym.eop_mem_lambdaComp`,
  `HJO.Mac.dop_pleth`.

## Which hypotheses are needed

`u ≠ 0` is needed in three statements, and every one of them is **false** without it:
`HJO.Mac.one_sub_mul_sum_macCoeff`, `HJO.Mac.sub_one_mul_sum_macCoeff_mul_pow` and
`HJO.Mac.dop_pleth`. At `u = 0` Lean's `0⁻¹ = 0` makes `𝒲` the identity; in `HJO.Mac.dop_pleth` at
`n = 1` and `F = p_1` the identity then reads `T_{q,x_1}(x_1) = x_1`, that is `q x_1 = x_1`. The
invertibility enters at exactly one place, `HJO.Mac.pow_card_mul_map_completeHomog`, where the
numerator `∏_i (1 - u^{-1}w x_i)` of the `h`-series is multiplied by `u^n` to become the
`∏_i (u - w x_i)` of the partial fraction identity.

Dead hypotheses, in the other direction. `n ≥ 1` is not needed in
`HJO.Mac.prod_C_sub_macCoeff_eq_add`, `HJO.Mac.one_sub_mul_sum_macCoeff`,
`HJO.Mac.sub_one_mul_sum_macCoeff_mul_pow`, `HJO.Mac.mk_restrictFrac_plethMulU_mul_prod`,
`HJO.Mac.sum_restrictFrac_coeff_plethCreateQ` or `HJO.Mac.dop_pleth`: the empty alphabet is not a
corner in any of them. `HJO.Mac.mk_restrictFrac_plethMulU_mul_prod` needs nothing about `u` at all.
And `HJO.Mac.dop_pleth` needs **no grading hypothesis** on `F`:
`HJO.Mac.sum_restrictFrac_coeff_plethCreateQ` is used through `HJO.Mac.qShift_restrictFrac`, which
evaluates the displacement rather than truncating it at `d`, so `HJO.Sym.coeff_plethCreateQ_eq_zero`
and `HJO.Sym.coeff_plethCreateQ_mem_lambdaComp` are not on the route to (4.10) at all. They are
proved here anyway, being one line each from the grading of the displacement.

`m ≥ 1` in `HJO.Mac.sub_one_mul_sum_macCoeff_mul_pow` is genuine: at `m = 0` the two sides differ by
`1`.

## What is not on this route

`HJO.Mac.restrictAlphabet_macPfun_partDiagram` is not needed, and neither are
`HJO.Sym.killCompl_restrictAlphabet`, `HJO.Mac.killComplComp_macPpoly`,
`MvPolynomial.killComplComp_bijective` or `HJO.Sym.exists_basis_lambdaComp_macPfun`. Proving (4.24)
for every `n ≥ |μ|` would need `res_n(P_μ) = P_μ[X_n]` at each such `n`; `HJO.Sym.IsEopEigenJfun`
asks for the single `n = n_μ = max(|μ|,1)`, which is all
`HJO.Standing.dop_zero_smul_macHtilde_param` uses, and there `res_{n_μ}(P_μ) = P_μ[X_{n_μ}]` is
the *definition* of `P_μ` (`HJO.Sym.restrictAlphabet_macPfun`). `HJO.Laurent.nonpositive` is not
needed either: the displacement's target is already a polynomial ring in `w`.

## References

A. M. Garsia, M. Haiman and
G. Tesler, *Explicit plethystic formulas for Macdonald (q,t)-Kostka coefficients*, Sém. Lothar.
Combin. **42** (1999), B42m, Section 4, Theorem 4.2 and equations (4.10), (4.24) and (1.11) a);
their `t` is written `u` here.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### Generating series of the complete homogeneous functions -/

section Series

variable {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The `h`-series of a sum of two alphabets is the product of the two `h`-series: the series form
of `HJO.Sym.completeHomog_of_add`. -/
theorem mk_completeHomog_mul {F G H : Type*}
    [FunLike F (Lambda K) R] [RingHomClass F (Lambda K) R]
    [FunLike G (Lambda K) R] [RingHomClass G (Lambda K) R]
    [FunLike H (Lambda K) R] [RingHomClass H (Lambda K) R] (φ : F) (ψ : G) (χ : H)
    (h : ∀ i : ℕ, χ (MvPolynomial.X i) = φ (MvPolynomial.X i) + ψ (MvPolynomial.X i)) :
    (PowerSeries.mk fun m => χ (completeHomog K m))
      = (PowerSeries.mk fun m => φ (completeHomog K m)) *
          PowerSeries.mk fun m => ψ (completeHomog K m) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, completeHomog_of_add φ ψ χ h n,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsn : s ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  simp only [PowerSeries.coeff_mk]
  rw [show n + 1 - 1 - s = n - s from rfl, show n - (n - s) = s by omega]

/-- The `h`-series of the empty alphabet is `1`. -/
theorem mk_completeHomog_eq_one {F : Type*} [FunLike F (Lambda K) R] [RingHomClass F (Lambda K) R]
    (χ : F) (h : ∀ i : ℕ, χ (MvPolynomial.X i) = 0) :
    (PowerSeries.mk fun m => χ (completeHomog K m)) = 1 := by
  have hz : ∀ m : ℕ, χ (completeHomog K m) = (0 : R) ^ m :=
    completeHomog_single χ 0 (fun i => by rw [h i, zero_pow (by omega)])
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_mk, hz, PowerSeries.coeff_one]
  match n with
  | 0 => simp
  | k + 1 => simp [zero_pow]

/-- The `h`-series of a single negated letter `a` is the polynomial `1 - a w`. -/
theorem mk_completeHomog_neg_single [Algebra K R] {F : Type*} [FunLike F (Lambda K) R]
    [RingHomClass F (Lambda K) R] (ψ : F) (a : R)
    (h : ∀ i : ℕ, ψ (MvPolynomial.X i) = -a ^ (i + 1)) :
    (PowerSeries.mk fun m => ψ (completeHomog K m)) = 1 - PowerSeries.C a * PowerSeries.X := by
  obtain ⟨h0, h1, h2⟩ := completeHomog_neg_single ψ a h
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one, PowerSeries.coeff_X]
  match n with
  | 0 => rw [h0]; norm_num
  | 1 => rw [h1]; norm_num
  | k + 2 => simp [h2 (k + 2) (by omega)]

end Series

/-! ### The `h`-series of a finite alphabet -/

section FiniteAlphabet

variable {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R] [Algebra ℚ R]
  [Algebra K R] {ι : Type*}

/-- The algebra homomorphism `Λ → R` sending `p_k` to `± ∑_{j ∈ s} a_jᵏ`: the restriction of
the symmetric functions to the finite alphabet `{a_j : j ∈ s}`, negated when `ε = -1`. -/
noncomputable def alphabetHom (ε : R) (a : ι → R) (s : Finset ι) : Lambda K →ₐ[K] R :=
  MvPolynomial.aeval fun i => ε * ∑ j ∈ s, a j ^ (i + 1)

omit [Algebra ℚ K] [Algebra ℚ R] in
/-- The defining values of `HJO.Sym.alphabetHom` on the generators. -/
theorem alphabetHom_X (ε : R) (a : ι → R) (s : Finset ι) (i : ℕ) :
    alphabetHom (K := K) ε a s (MvPolynomial.X i) = ε * ∑ j ∈ s, a j ^ (i + 1) :=
  MvPolynomial.aeval_X _ i

/-- **The `h`-series of a negated finite alphabet is `∏_j (1 - a_j w)`.** Induction on the
alphabet: adding one negated letter multiplies the series by `1 - a_j w`. -/
theorem mk_completeHomog_alphabetHom_neg_one (a : ι → R) (s : Finset ι) :
    (PowerSeries.mk fun m => alphabetHom (K := K) (-1) a s (completeHomog K m))
      = ∏ j ∈ s, (1 - PowerSeries.C (a j) * PowerSeries.X) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty]
      exact mk_completeHomog_eq_one _ fun i => by
        rw [alphabetHom_X, Finset.sum_empty, mul_zero]
  | insert x s hx ih =>
      have hν : ∀ i : ℕ,
          alphabetHom (K := K) (-1) a (insert x s) (MvPolynomial.X i)
            = alphabetHom (K := K) (-1) a s (MvPolynomial.X i)
              + (MvPolynomial.aeval fun i : ℕ => -a x ^ (i + 1) :
                  Lambda K →ₐ[K] R) (MvPolynomial.X i) := by
        intro i
        rw [alphabetHom_X, alphabetHom_X, MvPolynomial.aeval_X, Finset.sum_insert hx]
        ring
      rw [mk_completeHomog_mul (alphabetHom (K := K) (-1) a s)
        (MvPolynomial.aeval fun i : ℕ => -a x ^ (i + 1) : Lambda K →ₐ[K] R) _ hν, ih,
        mk_completeHomog_neg_single _ (a x) (fun i => MvPolynomial.aeval_X _ i),
        Finset.prod_insert hx]
      ring

/-- **The `h`-series of a finite alphabet is the inverse of `∏_j (1 - a_j w)`.** The alphabet and
its negation add up to the empty alphabet, whose `h`-series is `1`. -/
theorem mk_completeHomog_mul_prod_eq_one {F : Type*} [FunLike F (Lambda K) R]
    [RingHomClass F (Lambda K) R] (φ : F) (a : ι → R) (s : Finset ι)
    (hφ : ∀ i : ℕ, φ (MvPolynomial.X i) = ∑ j ∈ s, a j ^ (i + 1)) :
    (PowerSeries.mk fun m => φ (completeHomog K m)) *
        ∏ j ∈ s, (1 - PowerSeries.C (a j) * PowerSeries.X) = 1 := by
  classical
  rw [← mk_completeHomog_alphabetHom_neg_one (K := K) a s,
    ← mk_completeHomog_mul φ (alphabetHom (K := K) (-1) a s)
      (alphabetHom (K := K) 0 a s) (fun i => by
        rw [alphabetHom_X, alphabetHom_X, hφ i]; ring)]
  exact mk_completeHomog_eq_one _ fun i => by rw [alphabetHom_X, zero_mul]

end FiniteAlphabet

/-! ### The geometric series -/

section Geom

variable {R : Type*} [CommRing R]

/-- **The geometric series inverts `1 - a w`.** -/
theorem one_sub_C_mul_X_mul_mk_pow (a : R) :
    (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.mk (fun m => a ^ m) = 1 := by
  refine PowerSeries.ext fun n => ?_
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]
  match n with
  | 0 => rw [PowerSeries.coeff_zero_X_mul]; simp
  | k + 1 =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, pow_succ]
      simp [mul_comm]

end Geom

end HJO.Sym

/-! ### The partial fraction identity behind Macdonald's coefficients -/

namespace HJO.Mac

namespace Acoef

/-! The linear factors `c - x w` and the top coefficient of their product. These are the degree
bookkeeping of `HJO.Mac.prod_C_sub_eq_add` and carry no mathematical content of their own. -/

section Linear

variable {L : Type*} [Field L]

/-- The linear factor `c - b w`, rewritten in the shape `Polynomial.degree_linear` wants. -/
theorem linear_eq (c b : L) :
    Polynomial.C c - Polynomial.C b * Polynomial.X
      = Polynomial.C (-b) * Polynomial.X + Polynomial.C c := by
  rw [map_neg]; ring

/-- A linear factor with nonzero slope has degree one. -/
theorem degree_linear {b : L} (hb : b ≠ 0) (c : L) :
    (Polynomial.C c - Polynomial.C b * Polynomial.X).degree = 1 := by
  rw [linear_eq]
  exact Polynomial.degree_linear (neg_ne_zero.mpr hb)

/-- A linear factor with nonzero slope has natural degree one. -/
theorem natDegree_linear {b : L} (hb : b ≠ 0) (c : L) :
    (Polynomial.C c - Polynomial.C b * Polynomial.X).natDegree = 1 :=
  Polynomial.natDegree_eq_of_degree_eq_some (degree_linear hb c)

/-- A linear factor with nonzero slope is nonzero. -/
theorem linear_ne_zero {b : L} (hb : b ≠ 0) (c : L) :
    Polynomial.C c - Polynomial.C b * Polynomial.X ≠ 0 := fun h => by
  have hd := degree_linear hb c
  rw [h, Polynomial.degree_zero] at hd
  exact absurd hd (by simp)

/-- The leading coefficient of `c - b w` is `-b`. -/
theorem leadingCoeff_linear {b : L} (hb : b ≠ 0) (c : L) :
    (Polynomial.C c - Polynomial.C b * Polynomial.X).leadingCoeff = -b := by
  rw [Polynomial.leadingCoeff, natDegree_linear hb c, linear_eq]
  simp

variable {σ : Type*} [Fintype σ]

/-- The product of the `n` linear factors `c - x_i w` has degree `n`. -/
theorem natDegree_prod_linear {x : σ → L} (hx0 : ∀ i, x i ≠ 0) (c : L) :
    (∏ i : σ, (Polynomial.C c - Polynomial.C (x i) * Polynomial.X)).natDegree
      = Fintype.card σ := by
  rw [Polynomial.natDegree_prod _ _ fun i _ => linear_ne_zero (hx0 i) c]
  simp [natDegree_linear (hx0 _) c, Finset.card_univ]

/-- The top coefficient of the product of the `n` linear factors `c - x_i w` is `∏_i (-x_i)`,
and in particular does not depend on `c`. -/
theorem coeff_prod_linear {x : σ → L} (hx0 : ∀ i, x i ≠ 0) (c : L) :
    (∏ i : σ, (Polynomial.C c - Polynomial.C (x i) * Polynomial.X)).coeff (Fintype.card σ)
      = ∏ i : σ, -(x i) := by
  rw [← natDegree_prod_linear hx0 c, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_prod]
  exact Finset.prod_congr rfl fun i _ => leadingCoeff_linear (hx0 i) c

end Linear

end Acoef

section PartialFraction

open Acoef

variable {L : Type*} [Field L] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **The partial fraction identity behind Macdonald's coefficients**, that is,
`HJO.Mac.prod_C_sub_macCoeff_eq_add`: in `L[w]`,
`∏_i (u - w x_i) = ∏_i (1 - w x_i) + (u-1) ∑_i A_i ∏_{j ≠ i} (1 - w x_j)`,
where `A_i = ∏_{j≠i}(u x_i - x_j)/(x_i - x_j)`.

No hypothesis `n ≥ 1` is needed --- at the empty alphabet both sides are `1`.
The letters must be nonzero and pairwise distinct, which is what the
field `𝕜(x_1,…,x_n)` supplies and what its proof uses when it evaluates at `w = x_i^{-1}`.

The proof: the difference of the two sides has degree below `n`, because the two
`n`-fold products have the same top coefficient `∏_i(-x_i)` whatever the constant `u` is, and it
vanishes at the `n` distinct points `x_i^{-1}`. -/
theorem prod_C_sub_eq_add {x : σ → L} (hx0 : ∀ i, x i ≠ 0) (hxinj : Function.Injective x)
    (u : L) :
    ∏ i : σ, (Polynomial.C u - Polynomial.C (x i) * Polynomial.X)
      = (∏ i : σ, (1 - Polynomial.C (x i) * Polynomial.X))
        + Polynomial.C (u - 1) * ∑ i : σ, Polynomial.C
            (∏ j ∈ Finset.univ.erase i, (u * x i - x j) / (x i - x j)) *
              ∏ j ∈ Finset.univ.erase i, (1 - Polynomial.C (x j) * Polynomial.X) := by
  classical
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · simp
  have hn1 : 1 ≤ Fintype.card σ := Fintype.card_pos
  have hdiff : ∀ i j : σ, j ≠ i → x i - x j ≠ 0 :=
    fun i j hij => sub_ne_zero.mpr fun h => hij (hxinj h.symm)
  -- a polynomial of degree below `n` vanishing at the `n` points `x_i⁻¹` is zero
  have key : ∀ Δ : Polynomial L, (∀ k : ℕ, Fintype.card σ ≤ k → Δ.coeff k = 0) →
      (∀ i : σ, Polynomial.eval (x i)⁻¹ Δ = 0) → Δ = 0 := by
    intro Δ hc hr
    have hnd : Δ.natDegree < Fintype.card σ := by
      by_cases h0 : Δ = 0
      · rw [h0, Polynomial.natDegree_zero]; omega
      · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr
          ((Polynomial.degree_lt_iff_coeff_zero Δ _).mpr hc)
    exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Δ
      (inv_injective.comp hxinj) hr hnd
  -- the second product, written so that `coeff_prod_linear` applies
  have hP1 : (∏ i : σ, (1 - Polynomial.C (x i) * Polynomial.X))
      = ∏ i : σ, (Polynomial.C (1 : L) - Polynomial.C (x i) * Polynomial.X) := by
    simp
  -- each term of the correction sum has degree at most `n - 1`
  have hSterm : ∀ i : σ, (Polynomial.C
      (∏ j ∈ Finset.univ.erase i, (u * x i - x j) / (x i - x j)) *
        ∏ j ∈ Finset.univ.erase i, (1 - Polynomial.C (x j) * Polynomial.X)).natDegree
      ≤ Fintype.card σ - 1 := by
    intro i
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, zero_add]
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun j _ => ?_) ?_
    · rw [show (1 : Polynomial L) - Polynomial.C (x j) * Polynomial.X
        = Polynomial.C (1 : L) - Polynomial.C (x j) * Polynomial.X by simp,
        natDegree_linear (hx0 j)]
    · rw [smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have hScoeff : ∀ k : ℕ, Fintype.card σ ≤ k →
      (∑ i : σ, Polynomial.C (∏ j ∈ Finset.univ.erase i, (u * x i - x j) / (x i - x j)) *
        ∏ j ∈ Finset.univ.erase i, (1 - Polynomial.C (x j) * Polynomial.X)).coeff k = 0 :=
    fun k hk => Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
      (Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => hSterm i) (by omega))
  rw [← sub_eq_zero]
  refine key _ (fun k hk => ?_) (fun i => ?_)
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rw [coeff_prod_linear hx0 u, hP1, coeff_prod_linear hx0 1, hScoeff _ le_rfl]
      ring
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (by rw [natDegree_prod_linear hx0 u]; omega), hP1,
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (by rw [natDegree_prod_linear hx0 1]; omega), hScoeff k hk]
      ring
  · have hxi : x i ≠ 0 := hx0 i
    have hone : x i * (x i)⁻¹ = 1 := mul_inv_cancel₀ hxi
    -- the first product, split at the letter `i`, whose factor becomes `u - 1`
    have h1 : Polynomial.eval (x i)⁻¹
        (∏ j : σ, (Polynomial.C u - Polynomial.C (x j) * Polynomial.X))
        = (u - 1) * ∏ j ∈ Finset.univ.erase i, (u - x j * (x i)⁻¹) := by
      rw [Polynomial.eval_prod]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hone]
    -- the second product vanishes, the letter `i` contributing the factor `1 - 1`
    have h2 : Polynomial.eval (x i)⁻¹
        (∏ j : σ, (1 - Polynomial.C (x j) * Polynomial.X)) = 0 := by
      rw [Polynomial.eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_one]
      rw [hone, sub_self]
    -- in the correction sum only the term at `i` survives, and it is the first product with the
    -- factor `u - 1` removed
    have hvan : ∀ l : σ, l ∈ Finset.univ → l ≠ i →
        (∏ j ∈ Finset.univ.erase l, (u * x l - x j) / (x l - x j)) *
          ∏ j ∈ Finset.univ.erase l, (1 - x j * (x i)⁻¹) = 0 := by
      intro l _ hli
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨fun h => hli (h ▸ rfl), Finset.mem_univ i⟩) ?_)
      rw [hone, sub_self]
    have h3 : Polynomial.eval (x i)⁻¹
        (∑ l : σ, Polynomial.C (∏ j ∈ Finset.univ.erase l, (u * x l - x j) / (x l - x j)) *
          ∏ j ∈ Finset.univ.erase l, (1 - Polynomial.C (x j) * Polynomial.X))
        = ∏ j ∈ Finset.univ.erase i, (u - x j * (x i)⁻¹) := by
      rw [Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
        Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
      rw [Finset.sum_eq_single i hvan (fun hi => absurd (Finset.mem_univ i) hi),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hd : x i - x j ≠ 0 := hdiff i j (Finset.ne_of_mem_erase hj)
      field_simp
    rw [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      h1, h2, h3]
    ring

end PartialFraction

/-! ### Macdonald's coefficients against a power of one variable -/

section Acoefficients

open HJO.Sym

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K] [Algebra ℚ K]

omit [DecidableEq σ] in
/-- **The `h`-series of a difference of two finite alphabets.** If `φ` restricts the symmetric
functions to the alphabet `x` and `ψ` restricts them to `x - v x`, then the `h`-series of `ψ` is the
`h`-series of `φ` times `∏_j (1 - v x_j w)`. -/
theorem mk_completeHomog_eq_mul_prod {L : Type*} [Field L] [Algebra ℚ L] [Algebra K L]
    (x : σ → L) (vv : L) (φ ψ : Lambda K →ₐ[K] L)
    (hφ : ∀ i : ℕ, φ (MvPolynomial.X i) = ∑ j : σ, x j ^ (i + 1))
    (hψ : ∀ i : ℕ, ψ (MvPolynomial.X i)
      = ∑ j : σ, x j ^ (i + 1) - ∑ j : σ, (vv * x j) ^ (i + 1)) :
    (PowerSeries.mk fun m => ψ (completeHomog K m))
      = (PowerSeries.mk fun m => φ (completeHomog K m)) *
        ∏ j : σ, (1 - PowerSeries.C (vv * x j) * PowerSeries.X) := by
  rw [← mk_completeHomog_alphabetHom_neg_one (K := K) (fun j => vv * x j) Finset.univ]
  refine mk_completeHomog_mul φ
    (alphabetHom (K := K) (-1) (fun j => vv * x j) Finset.univ) ψ (fun i => ?_)
  rw [alphabetHom_X, hψ i, hφ i, neg_one_mul]
  ring

omit [DecidableEq σ] in
/-- **The generating function of the twisted complete homogeneous functions**,
`HJO.Mac.mk_restrictFrac_plethMulU_mul_prod`:
`(∑_m res_n(𝒲(h_m)) w^m) ∏_i (1 - w x_i) = ∏_i (1 - v w x_i)`.

**No hypothesis at all.** No `n ≥ 1` is needed, and although `v` is meant as `u^{-1}`,
neither the invertibility of `u` nor anything else is used, both sides being generating functions of
`h`-series of finite alphabets. The power series in `𝕜[x_1,…,x_n][[w]]` is read here in
the fraction field, whose power series ring contains it. -/
theorem mk_completeHomog_mul_prod {L : Type*} [Field L] [Algebra ℚ L] [Algebra K L]
    (x : σ → L) (vv : L) (φ ψ : Lambda K →ₐ[K] L)
    (hφ : ∀ i : ℕ, φ (MvPolynomial.X i) = ∑ j : σ, x j ^ (i + 1))
    (hψ : ∀ i : ℕ, ψ (MvPolynomial.X i)
      = ∑ j : σ, x j ^ (i + 1) - ∑ j : σ, (vv * x j) ^ (i + 1)) :
    (PowerSeries.mk fun m => ψ (completeHomog K m)) *
        ∏ j : σ, (1 - PowerSeries.C (x j) * PowerSeries.X)
      = ∏ j : σ, (1 - PowerSeries.C (vv * x j) * PowerSeries.X) := by
  rw [mk_completeHomog_eq_mul_prod x vv φ ψ hφ hψ,
    show (PowerSeries.mk fun m => φ (completeHomog K m)) *
        (∏ j : σ, (1 - PowerSeries.C (vv * x j) * PowerSeries.X)) *
        ∏ j : σ, (1 - PowerSeries.C (x j) * PowerSeries.X)
      = ((PowerSeries.mk fun m => φ (completeHomog K m)) *
          ∏ j : σ, (1 - PowerSeries.C (x j) * PowerSeries.X)) *
          ∏ j : σ, (1 - PowerSeries.C (vv * x j) * PowerSeries.X) from by ring,
    mk_completeHomog_mul_prod_eq_one φ x Finset.univ hφ, one_mul]

/-- **Macdonald's coefficients against a power of one letter**,
`HJO.Mac.one_sub_mul_sum_macCoeff` and `HJO.Mac.sub_one_mul_sum_macCoeff_mul_pow` as one identity:
`u^n ψ(h_m) = [m = 0] + (u-1) ∑_i A_i x_i^m`, where `φ` restricts the symmetric functions to the
alphabet `x`, `ψ` restricts them to `(1 - u^{-1})x`, and `A_i = ∏_{j≠i}(u x_i - x_j)/(x_i - x_j)`.

At `m = 0` this is `HJO.Mac.one_sub_mul_sum_macCoeff`, `(1-u)∑_i A_i = 1 - u^n`; at `m ≥ 1` it is
`HJO.Mac.sub_one_mul_sum_macCoeff_mul_pow`, `(u-1)∑_i A_i x_i^m = u^n res_n(𝒲(h_m))`. Neither
`n ≥ 1` nor `m ≥ 1` is needed: the two cases are one identity and the empty alphabet is not a
corner.

What is *not* dead is the invertibility of `u`, carried here as `huv : u v = 1`: the `h`-series of
`ψ` is `∏_i (1 - v x_i w) / ∏_i (1 - x_i w)`, and multiplying its numerator by `u^n` to reach
`∏_i (u - x_i w)` --- which is the left side of the partial fraction identity --- is exactly where
`u v = 1` is used. -/
theorem pow_card_mul_map_completeHomog {L : Type*} [Field L] [Algebra ℚ L] [Algebra K L]
    {x : σ → L} (hx0 : ∀ i, x i ≠ 0) (hxinj : Function.Injective x) {uu vv : L}
    (huv : uu * vv = 1) (φ ψ : Lambda K →ₐ[K] L)
    (hφ : ∀ i : ℕ, φ (MvPolynomial.X i) = ∑ j : σ, x j ^ (i + 1))
    (hψ : ∀ i : ℕ, ψ (MvPolynomial.X i)
      = ∑ j : σ, x j ^ (i + 1) - ∑ j : σ, (vv * x j) ^ (i + 1)) (m : ℕ) :
    uu ^ Fintype.card σ * ψ (completeHomog K m)
      = (if m = 0 then 1 else 0) + (uu - 1) *
          ∑ i : σ, (∏ j ∈ Finset.univ.erase i, (uu * x i - x j) / (x i - x j)) * x i ^ m := by
  -- the `h`-series of `φ` inverts `∏_j (1 - x_j w)`
  have hHP : (PowerSeries.mk fun m => φ (completeHomog K m)) *
      ∏ j : σ, (1 - PowerSeries.C (x j) * PowerSeries.X) = 1 :=
    mk_completeHomog_mul_prod_eq_one φ x Finset.univ hφ
  -- the `h`-series of `ψ` factors off the numerator product
  have hG := mk_completeHomog_eq_mul_prod x vv φ ψ hφ hψ
  -- scaling the numerator product by `u^n` turns `1 - v x_j w` into `u - x_j w`
  have hnum : PowerSeries.C (uu ^ Fintype.card σ) *
      ∏ j : σ, (1 - PowerSeries.C (vv * x j) * PowerSeries.X)
      = ∏ j : σ, (PowerSeries.C uu - PowerSeries.C (x j) * PowerSeries.X) := by
    rw [map_pow, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [mul_sub, mul_one, ← mul_assoc, ← map_mul, ← mul_assoc, huv, one_mul]
  -- the partial fraction identity, read in the power series ring
  have hpf : (∏ j : σ, (PowerSeries.C uu - PowerSeries.C (x j) * PowerSeries.X))
      = (∏ j : σ, (1 - PowerSeries.C (x j) * PowerSeries.X))
        + PowerSeries.C (uu - 1) * ∑ i : σ, PowerSeries.C
            (∏ j ∈ Finset.univ.erase i, (uu * x i - x j) / (x i - x j)) *
              ∏ j ∈ Finset.univ.erase i, (1 - PowerSeries.C (x j) * PowerSeries.X) := by
    have h2 := congrArg (Polynomial.coeToPowerSeries.ringHom (R := L))
      (prod_C_sub_eq_add hx0 hxinj uu)
    simpa only [map_prod, map_sum, map_sub, map_mul, map_one, map_add, map_div₀,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X] using h2
  -- dividing the `i`-th Lagrange factor by `∏_j (1 - x_j w)` leaves the geometric series in `x_i`
  have hstep : ∀ i : σ, (PowerSeries.mk fun m => φ (completeHomog K m)) *
      ∏ j ∈ Finset.univ.erase i, (1 - PowerSeries.C (x j) * PowerSeries.X)
      = PowerSeries.mk (fun m => x i ^ m) := by
    intro i
    have hsplit : ∏ j : σ, (1 - PowerSeries.C (x j) * PowerSeries.X)
        = (1 - PowerSeries.C (x i) * PowerSeries.X) *
          ∏ j ∈ Finset.univ.erase i, (1 - PowerSeries.C (x j) * PowerSeries.X) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    calc (PowerSeries.mk fun m => φ (completeHomog K m)) *
          ∏ j ∈ Finset.univ.erase i, (1 - PowerSeries.C (x j) * PowerSeries.X)
        = ((PowerSeries.mk fun m => φ (completeHomog K m)) *
            ∏ j ∈ Finset.univ.erase i, (1 - PowerSeries.C (x j) * PowerSeries.X)) *
              ((1 - PowerSeries.C (x i) * PowerSeries.X) *
                PowerSeries.mk (fun m => x i ^ m)) := by
            rw [one_sub_C_mul_X_mul_mk_pow, mul_one]
      _ = ((PowerSeries.mk fun m => φ (completeHomog K m)) *
            ∏ j : σ, (1 - PowerSeries.C (x j) * PowerSeries.X)) *
              PowerSeries.mk (fun m => x i ^ m) := by rw [hsplit]; ring
      _ = PowerSeries.mk (fun m => x i ^ m) := by rw [hHP, one_mul]
  have hsum : (PowerSeries.mk fun m => φ (completeHomog K m)) *
      (∑ i : σ, PowerSeries.C (∏ j ∈ Finset.univ.erase i, (uu * x i - x j) / (x i - x j)) *
        ∏ j ∈ Finset.univ.erase i, (1 - PowerSeries.C (x j) * PowerSeries.X))
      = ∑ i : σ, PowerSeries.C (∏ j ∈ Finset.univ.erase i, (uu * x i - x j) / (x i - x j)) *
          PowerSeries.mk (fun m => x i ^ m) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_left_comm, hstep i]
  -- the identity of series
  have hmain : PowerSeries.C (uu ^ Fintype.card σ) *
      (PowerSeries.mk fun m => ψ (completeHomog K m))
      = 1 + PowerSeries.C (uu - 1) *
          ∑ i : σ, PowerSeries.C (∏ j ∈ Finset.univ.erase i, (uu * x i - x j) / (x i - x j)) *
            PowerSeries.mk (fun m => x i ^ m) := by
    have e1 : PowerSeries.C (uu ^ Fintype.card σ) *
        (PowerSeries.mk fun m => ψ (completeHomog K m))
        = (PowerSeries.mk fun m => φ (completeHomog K m)) *
          ∏ j : σ, (PowerSeries.C uu - PowerSeries.C (x j) * PowerSeries.X) := by
      rw [hG, ← hnum]; ring
    rw [e1, hpf, mul_add, hHP, mul_left_comm, hsum]
  have hc := congrArg (PowerSeries.coeff m) hmain
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one,
    map_sum] at hc
  exact hc

end Acoefficients

/-! ### Macdonald's coefficients in the rational function field -/

section RatFn

open HJO.Sym

variable {σ : Type*} [Fintype σ] [LinearOrder σ] {K : Type*} [Field K] [Algebra ℚ K] {u : K}

/-- The variable `x_i` read in the rational function field `𝕜(x_1, …, x_n)`. -/
noncomputable def fracX (K : Type*) [Field K] {σ : Type*} (i : σ) :
    FractionRing (MvPolynomial σ K) :=
  algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (MvPolynomial.X i)

/-- Distinct letters are distinct in the rational function field. -/
theorem fracX_injective {σ : Type*} {K : Type*} [Field K] :
    Function.Injective (fracX K : σ → FractionRing (MvPolynomial σ K)) :=
  fun _ _ h => MvPolynomial.X_injective
    (IsFractionRing.injective (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) h)

/-- Every letter is nonzero in the rational function field. -/
theorem fracX_ne_zero {σ : Type*} {K : Type*} [Field K] (i : σ) : fracX K i ≠ 0 := by
  rw [fracX, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  exact MvPolynomial.X_ne_zero i

/-- Restriction to the finite alphabet, read in the rational function field:
`res_n` followed by the inclusion of the polynomials into their fraction field. -/
noncomputable def restrictFrac (σ : Type*) [Fintype σ] (K : Type*) [Field K] [Algebra ℚ K] :
    Lambda K →ₐ[K] FractionRing (MvPolynomial σ K) :=
  (IsScalarTower.toAlgHom K (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))).comp
    (restrictAlphabet σ K)

omit [LinearOrder σ] in
/-- The restriction read in the fraction field, as the composite it is. -/
theorem restrictFrac_apply (f : Lambda K) :
    restrictFrac σ K f = algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
      (restrictAlphabet σ K f) := rfl

omit [LinearOrder σ] in
/-- The restriction of a generator is the power sum of the alphabet. -/
theorem restrictFrac_X (i : ℕ) :
    restrictFrac σ K (MvPolynomial.X i) = ∑ j : σ, fracX K j ^ (i + 1) := by
  rw [restrictFrac_apply, restrictAlphabet_powerSum', MvPolynomial.psum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_pow, fracX]

omit [LinearOrder σ] in
/-- A scalar restricts to itself. -/
theorem restrictFrac_C (a : K) :
    restrictFrac σ K (MvPolynomial.C a) = algebraMap K (FractionRing (MvPolynomial σ K)) a := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

omit [Algebra ℚ K] in
/-- **Macdonald's coefficient read in the alphabet**:
`A_i = ∏_{j≠i}(u x_i - x_j)/(x_i - x_j)`. -/
theorem macCoeff_eq_prod (u : K) (i : σ) :
    macCoeff u i = ∏ j ∈ Finset.univ.erase i,
      (algebraMap K (FractionRing (MvPolynomial σ K)) u * fracX K i - fracX K j) /
        (fracX K i - fracX K j) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_sub, map_sub, map_mul, fracX, fracX, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

omit [LinearOrder σ] in
/-- The restriction of the plethystic multiplication on a generator, as the difference of the two
alphabets `x` and `u^{-1}x` that `𝒲` subtracts. -/
theorem restrictFrac_plethMulU_X (i : ℕ) :
    ((restrictFrac σ K).comp (plethMulU u)) (MvPolynomial.X i)
      = ∑ j : σ, fracX K j ^ (i + 1) -
        ∑ j : σ, (algebraMap K (FractionRing (MvPolynomial σ K)) u⁻¹ * fracX K j) ^ (i + 1) := by
  rw [AlgHom.coe_comp, Function.comp_apply, plethMulU, diagScale_X, map_mul, restrictFrac_C,
    restrictFrac_X, map_sub, map_one, map_pow, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_pow]; ring

omit [LinearOrder σ] in
/-- **The generating function of the twisted complete homogeneous functions in a finite
alphabet**, `HJO.Mac.mk_restrictFrac_plethMulU_mul_prod`:
`(∑_m res_n(𝒲(h_m)) w^m) ∏_i (1 - w x_i) = ∏_i (1 - u^{-1} w x_i)`.

**No hypothesis at all**: the `n ≥ 1` is dead, and no invertibility of `u` is used ---
at `u = 0` Lean's `0⁻¹ = 0` makes both `𝒲` and the right-hand product trivial and the identity is
the inverse relation between the `h`-series of an alphabet and `∏_i(1 - w x_i)`. -/
@[hjo "lem_ght3_res_wmul_hsymm"]
theorem mk_restrictFrac_plethMulU_mul_prod :
    (PowerSeries.mk fun m => restrictFrac σ K (plethMulU u (completeHomog K m))) *
        ∏ i : σ, (1 - PowerSeries.C (fracX K i) * PowerSeries.X)
      = ∏ i : σ, (1 - PowerSeries.C
          (algebraMap K (FractionRing (MvPolynomial σ K)) u⁻¹ * fracX K i) * PowerSeries.X) :=
  mk_completeHomog_mul_prod (fracX K) _ (restrictFrac σ K)
    ((restrictFrac σ K).comp (plethMulU u)) restrictFrac_X restrictFrac_plethMulU_X

/-- **The restriction of the plethystic multiplication against Macdonald's coefficients**,
`HJO.Mac.one_sub_mul_sum_macCoeff` and `HJO.Mac.sub_one_mul_sum_macCoeff_mul_pow` in the rational
function field: `u^n res_n(𝒲(h_m)) = [m = 0] + (u-1) ∑_i A_i x_i^m`.

`u ≠ 0` is genuine; see
`HJO.Mac.pow_card_mul_map_completeHomog`. At `u = 0` Lean's `0⁻¹ = 0` makes `𝒲` the identity, so
the left side is `0` for `n ≥ 1` while the right side at `n = 1`, `m = 1` is `-x_1`. -/
theorem pow_card_mul_restrictFrac_plethMulU_completeHomog (hu0 : u ≠ 0) (m : ℕ) :
    algebraMap K (FractionRing (MvPolynomial σ K)) u ^ Fintype.card σ *
        restrictFrac σ K (plethMulU u (completeHomog K m))
      = (if m = 0 then 1 else 0) +
          (algebraMap K (FractionRing (MvPolynomial σ K)) u - 1) *
            ∑ i : σ, macCoeff u i * fracX K i ^ m := by
  have key := pow_card_mul_map_completeHomog (K := K)
    (L := FractionRing (MvPolynomial σ K)) fracX_ne_zero fracX_injective
    (uu := algebraMap K (FractionRing (MvPolynomial σ K)) u)
    (vv := algebraMap K (FractionRing (MvPolynomial σ K)) u⁻¹)
    (by rw [← map_mul, mul_inv_cancel₀ hu0, map_one]) (restrictFrac σ K)
    ((restrictFrac σ K).comp (plethMulU u)) restrictFrac_X restrictFrac_plethMulU_X m
  rw [AlgHom.coe_comp, Function.comp_apply] at key
  rw [key]
  refine congrArg (fun z => (if m = 0 then (1 : FractionRing (MvPolynomial σ K)) else 0) +
    (algebraMap K (FractionRing (MvPolynomial σ K)) u - 1) * z) ?_
  exact Finset.sum_congr rfl fun i _ => by rw [macCoeff_eq_prod]

omit [Algebra ℚ K] in
/-- **The partial fraction identity in the rational function field**,
`HJO.Mac.prod_C_sub_macCoeff_eq_add` at its own alphabet and its own coefficients `A_i`:
`∏_i (u - w x_i) = ∏_i (1 - w x_i) + (u-1) ∑_i A_i ∏_{j≠i} (1 - w x_j)`.

`HJO.Mac.prod_C_sub_eq_add` is this over any field, for any nonzero pairwise-distinct family; no
`n ≥ 1` is needed there and so none is here. -/
@[hjo "lem_ght3_acoef_partial_fraction"]
theorem prod_C_sub_macCoeff_eq_add (u : K) :
    ∏ i : σ, (Polynomial.C (algebraMap K (FractionRing (MvPolynomial σ K)) u)
        - Polynomial.C (fracX K i) * Polynomial.X)
      = (∏ i : σ, (1 - Polynomial.C (fracX K i) * Polynomial.X))
        + Polynomial.C (algebraMap K (FractionRing (MvPolynomial σ K)) u - 1) *
            ∑ i : σ, Polynomial.C (macCoeff u i) *
              ∏ j ∈ Finset.univ.erase i, (1 - Polynomial.C (fracX K j) * Polynomial.X) := by
  rw [prod_C_sub_eq_add fracX_ne_zero fracX_injective]
  refine congrArg ((∏ i : σ, (1 - Polynomial.C (fracX K i) * Polynomial.X)) + ·) ?_
  refine congrArg (Polynomial.C (algebraMap K (FractionRing (MvPolynomial σ K)) u - 1) * ·) ?_
  exact Finset.sum_congr rfl fun i _ => by rw [macCoeff_eq_prod]

/-- **The sum of Macdonald's coefficients**, `HJO.Mac.one_sub_mul_sum_macCoeff`:
`(1-u)∑_i A_i = 1 - u^n`. The `n ≥ 1` is dead; `u ≠ 0` is inherited from
`HJO.Mac.pow_card_mul_restrictFrac_plethMulU_completeHomog`. -/
@[hjo "lem_ght3_acoef_sum"]
theorem one_sub_mul_sum_macCoeff (hu0 : u ≠ 0) :
    (1 - algebraMap K (FractionRing (MvPolynomial σ K)) u) * ∑ i : σ, macCoeff u i
      = 1 - algebraMap K (FractionRing (MvPolynomial σ K)) u ^ Fintype.card σ := by
  have h := pow_card_mul_restrictFrac_plethMulU_completeHomog (σ := σ) hu0 0
  rw [CopPower.completeHomog_zero, map_one, map_one, mul_one,
    show (if (0 : ℕ) = 0 then (1 : FractionRing (MvPolynomial σ K)) else 0) = 1 from by simp] at h
  simp only [pow_zero, mul_one] at h
  linear_combination h

/-- **Macdonald's coefficients against a positive power of one letter**,
`HJO.Mac.sub_one_mul_sum_macCoeff_mul_pow`: `(u-1)∑_i A_i x_i^m = u^n res_n(𝒲(h_m))` for `m ≥ 1`.

The `m ≥ 1` is genuine --- at `m = 0` the left side is `u^n - 1` and the right side is
`u^n` --- while its `n ≥ 1` is dead. `u ≠ 0` is genuine too. -/
@[hjo "lem_ght3_acoef_power_sum"]
theorem sub_one_mul_sum_macCoeff_mul_pow (hu0 : u ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    (algebraMap K (FractionRing (MvPolynomial σ K)) u - 1) *
        ∑ i : σ, macCoeff u i * fracX K i ^ m
      = algebraMap K (FractionRing (MvPolynomial σ K)) u ^ Fintype.card σ *
          restrictFrac σ K (plethMulU u (completeHomog K m)) := by
  have h := pow_card_mul_restrictFrac_plethMulU_completeHomog (σ := σ) hu0 m
  rw [show (if m = 0 then (1 : FractionRing (MvPolynomial σ K)) else 0) = 0 from by
    simp [show m ≠ 0 from by omega], zero_add] at h
  exact h.symm

end RatFn

/-! ### Macdonald's operator in plethystic form -/

section DopPleth

open HJO.Sym

variable {σ : Type*} [Fintype σ] [LinearOrder σ] {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ}
  {u : K}

/-- **The creation displacement evaluated at one letter is the parameter shift of that letter**,
`HJO.Mac.sum_restrictFrac_coeff_plethCreateQ`: evaluating `res_n(qs(F))` at `w = x_i` gives
`T_{q,x_i}(res_n(F))`.

Stated for every `F ∈ Λ` and with the evaluation left as an evaluation rather than as a
sum truncated at `d`. That makes `HJO.Sym.coeff_plethCreateQ_eq_zero` --- and with
it the grading hypothesis `F ∈ Λ_d` --- unnecessary here: `qs(F)` is a polynomial in `w`, so
evaluating it is already a finite sum. -/
theorem qShift_restrictFrac (q : Kˣ) (i : σ) (F : Lambda K) :
    qShift q i (restrictFrac σ K F)
      = Polynomial.eval (fracX K i)
          (Polynomial.map (restrictFrac σ K).toRingHom (plethCreateQ (q : K) F)) := by
  have hgen : ∀ j : ℕ, qShift q i (restrictFrac σ K (MvPolynomial.X j))
      = Polynomial.eval (fracX K i) (Polynomial.map (restrictFrac σ K).toRingHom
          (plethCreateQ (q : K) (MvPolynomial.X j))) := by
    intro j
    have hX : (MvPolynomial.X j : Lambda K) = powerSum K (j + 1) := by
      rw [powerSum, Nat.add_sub_cancel]
    have hqs : plethCreateQ (q : K) (MvPolynomial.X j)
        = Polynomial.C (MvPolynomial.X j : Lambda K)
          - Polynomial.C (MvPolynomial.C (1 - (q : K) ^ (j + 1))) * Polynomial.X ^ (j + 1) := by
      rw [hX]
      exact plethCreateQ_powerSum (q : K) (Nat.le_add_left 1 j)
    rw [hqs, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [restrictFrac_C, restrictFrac_X, map_sum,
      ← Finset.sum_erase_add _ (fun l => qShift q i (fracX K l ^ (j + 1))) (Finset.mem_univ i),
      ← Finset.sum_erase_add (Finset.univ : Finset σ)
        (fun l => fracX K l ^ (j + 1)) (Finset.mem_univ i)]
    have hterm : ∀ l ∈ Finset.univ.erase i,
        qShift q i (fracX K l ^ (j + 1)) = fracX K l ^ (j + 1) := by
      intro l hl
      rw [map_pow, fracX, qShift_algebraMap_X_of_ne q (Finset.ne_of_mem_erase hl)]
    rw [Finset.sum_congr rfl hterm, map_pow, fracX, qShift_algebraMap_X_self,
      Algebra.smul_def, map_sub, map_one, map_pow, mul_pow]
    ring
  induction F using MvPolynomial.induction_on with
  | C a =>
      rw [plethCreateQ_C, Polynomial.map_C, Polynomial.eval_C]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [restrictFrac_C, AlgEquiv.commutes]
  | add p r hp hr =>
      rw [map_add, map_add, map_add, Polynomial.map_add, Polynomial.eval_add, hp, hr]
  | mul_X p j hp =>
      rw [map_mul, map_mul, map_mul, Polynomial.map_mul, Polynomial.eval_mul, hp, hgen j]

/-- **Macdonald's operator in plethystic form**, `HJO.Mac.dop_pleth`, which is
Garsia--Haiman--Tesler's equation (4.10) cleared of its denominator `1 - u`:
`(1-u) D^{(n)}_1(res_n F) = res_n F - u^n res_n(ℰ F)`.

**No grading hypothesis.** No `F ∈ Λ_d` is needed, because
`HJO.Mac.sum_restrictFrac_coeff_plethCreateQ` is used through `HJO.Mac.qShift_restrictFrac`, which
evaluates the displacement rather than truncating it at `d`. That also removes
`HJO.Sym.coeff_plethCreateQ_eq_zero` and `HJO.Sym.coeff_plethCreateQ_mem_lambdaComp` from the route.
The `n ≥ 1` is dead too: at the empty alphabet `D^{(n)}_1` is the zero operator and both sides read
`res_n F = res_n(ℰ F)`, which holds because restriction to no letters keeps only the constant term.

`u ≠ 0` is inherited from `HJO.Mac.pow_card_mul_restrictFrac_plethMulU_completeHomog` and is
genuine. -/
@[hjo "lem_ght3_dop_pleth"]
theorem dop_pleth (hu0 : u ≠ 0) (F : Lambda K) :
    (1 - algebraMap K (FractionRing (MvPolynomial σ K)) u) * macOp q u (restrictFrac σ K F)
      = restrictFrac σ K F - algebraMap K (FractionRing (MvPolynomial σ K)) u ^ Fintype.card σ *
          restrictFrac σ K (eop (q : K) u F) := by
  classical
  obtain ⟨G, hG⟩ : ∃ G : ℕ → FractionRing (MvPolynomial σ K),
      ∀ j, G j = restrictFrac σ K ((plethCreateQ (q : K) F).coeff j) := ⟨_, fun _ => rfl⟩
  set N := (plethCreateQ (q : K) F).natDegree + 1 with hNdef
  set uu := algebraMap K (FractionRing (MvPolynomial σ K)) u with huu
  have hdeg : ∀ j : ℕ, N ≤ j → (plethCreateQ (q : K) F).coeff j = 0 :=
    fun j hj => Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  -- the plethystic form as a finite sum, restricted to the alphabet
  have heop : restrictFrac σ K (eop (q : K) u F)
      = ∑ j ∈ Finset.range N, G j * restrictFrac σ K (plethMulU u (completeHomog K j)) := by
    rw [eop_apply, coeffPairing_eq_sum_range _ _ hdeg, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hG]
  -- the displacement evaluated at each letter
  have heval : ∀ i : σ, ∑ j ∈ Finset.range N, G j * fracX K i ^ j
      = qShift q i (restrictFrac σ K F) := by
    intro i
    rw [qShift_restrictFrac q i F,
      Polynomial.eval_eq_sum_range' (n := N) (lt_of_le_of_lt Polynomial.natDegree_map_le
        (by omega))]
    exact Finset.sum_congr rfl fun j _ => by rw [Polynomial.coeff_map, hG]; rfl
  -- the coefficient identity, term by term
  have hterm : ∀ j ∈ Finset.range N,
      uu ^ Fintype.card σ * (G j * restrictFrac σ K (plethMulU u (completeHomog K j)))
        = G j * (if j = 0 then 1 else 0) +
            (uu - 1) * ∑ i : σ, macCoeff u i * (G j * fracX K i ^ j) := by
    intro j _
    rw [show uu ^ Fintype.card σ * (G j * restrictFrac σ K (plethMulU u (completeHomog K j)))
      = G j * (uu ^ Fintype.card σ *
          restrictFrac σ K (plethMulU u (completeHomog K j))) from by ring, huu,
      pow_card_mul_restrictFrac_plethMulU_completeHomog hu0 j, mul_add, Finset.mul_sum,
      Finset.mul_sum]
    refine congrArg (G j * (if j = 0 then 1 else 0) + ·) ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- the term at `j = 0` is the restriction of `F` itself
  have hzero : ∑ j ∈ Finset.range N, G j * (if j = 0 then 1 else 0) = restrictFrac σ K F := by
    rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_range.mpr (by omega)) h),
      show (if (0 : ℕ) = 0 then (1 : FractionRing (MvPolynomial σ K)) else 0) = 1 from by simp,
      mul_one, hG, coeff_zero_plethCreateQ]
  -- and the remaining sum is Macdonald's operator
  have hrest : ∑ j ∈ Finset.range N, (uu - 1) * ∑ i : σ, macCoeff u i * (G j * fracX K i ^ j)
      = (uu - 1) * macOp q u (restrictFrac σ K F) := by
    rw [← Finset.mul_sum, Finset.sum_comm, macOp_apply]
    refine congrArg ((uu - 1) * ·) ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← heval i, Finset.mul_sum]
  have hmain : uu ^ Fintype.card σ * restrictFrac σ K (eop (q : K) u F)
      = restrictFrac σ K F + (uu - 1) * macOp q u (restrictFrac σ K F) := by
    rw [heop, Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hzero, hrest]
  rw [hmain]
  ring

end DopPleth

end HJO.Mac

/-! ### The plethystic form is graded -/

namespace HJO.Sym

section Graded

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- **The creation displacement of the first parameter is graded**: for `f ∈ Λ_d` the coefficient of
`wʲ` in `f[X - (1-q)/z]` lies in `Λ_{d-j}`. This is `HJO.Sym.coeff_plethCreateQ_mem_lambdaComp` and
`HJO.Sym.coeff_plethCreateQ_eq_zero` in one statement, read through `HJO.Sym.PolyComp`, and is the
same argument as for `HJO.Sym.plethCreate_mem_polyComp`. -/
theorem plethCreateQ_mem_polyComp {L : Type*} [Field L] [Algebra ℚ L] (q : L) {d : ℕ}
    {f : Lambda L} (hf : f ∈ LambdaComp L d) : plethCreateQ q f ∈ PolyComp L (d : ℤ) := by
  refine mem_of_mem_lambdaComp (PolyComp L) (one_mem_polyComp L)
    (fun hx hy => mul_mem_polyComp hx hy) (plethCreateQ q) (fun i => ?_) hf
  rw [plethCreateQ, MvPolynomial.aeval_X]
  have hcast : ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
  refine sub_mem (C_mem_polyComp ?_) ?_
  · rw [hcast, lambdaCompInt_natCast]
    exact powerSum_mem_lambdaComp L i
  · have hC : (MvPolynomial.C (1 - q ^ (i + 1)) : Lambda L) ∈ LambdaCompInt L 0 := by
      rw [lambdaCompInt_zero]
      exact C_mem_lambdaComp L _
    have h := mul_mem_polyComp (C_mem_polyComp hC) (X_pow_mem_polyComp L (i + 1))
    rwa [zero_add, ← hcast] at h

/-- **The displacement is graded**, `HJO.Sym.coeff_plethCreateQ_mem_lambdaComp`: for `F ∈ Λ_d` and
`m ≤ d`, `[z^{-m}] qs(F) ∈ Λ_{d-m}`. -/
@[hjo "lem_ght3_qshift_graded"]
theorem coeff_plethCreateQ_mem_lambdaComp {L : Type*} [Field L] [Algebra ℚ L] (q : L) {d m : ℕ}
    (hm : m ≤ d) {f : Lambda L} (hf : f ∈ LambdaComp L d) :
    (plethCreateQ q f).coeff m ∈ LambdaComp L (d - m) := by
  have h := plethCreateQ_mem_polyComp q hf m
  rwa [show (d : ℤ) - (m : ℤ) = ((d - m : ℕ) : ℤ) from by omega, lambdaCompInt_natCast] at h

/-- **The displacement stops at the degree**, `HJO.Sym.coeff_plethCreateQ_eq_zero`: for
`F ∈ Λ_d` and `m > d`, `[z^{-m}] qs(F) = 0`. -/
@[hjo "lem_ght3_qshift_vanish"]
theorem coeff_plethCreateQ_eq_zero {L : Type*} [Field L] [Algebra ℚ L] (q : L) {d m : ℕ}
    (hm : d < m) {f : Lambda L} (hf : f ∈ LambdaComp L d) : (plethCreateQ q f).coeff m = 0 :=
  eq_zero_of_mem_lambdaCompInt (by omega) (plethCreateQ_mem_polyComp q hf m)

/-- **The plethystic form is graded**, `HJO.Sym.eop_mem_lambdaComp`: `ℰ(Λ_d) ⊆ Λ_d`.

The `j`-th coefficient of the displacement lies in `Λ_{d-j}`, and `ℰ`'s `j`-th factor `𝒲(h_j)` lies
in `Λ_j`, `𝒲` being a diagonal substitution and `h_j ∈ Λ_j`; so every term of the pairing lies in
`Λ_d`. -/
@[hjo "lem_ght3_eop_graded"]
theorem eop_mem_lambdaComp {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {d : ℕ} {f : Lambda L}
    (hf : f ∈ LambdaComp L d) : eop q u f ∈ LambdaComp L d := by
  have hfam : ∀ j : ℕ, plethMulU u (completeHomog L j) ∈ LambdaCompInt L ((0 : ℤ) + (j : ℤ)) := by
    intro j
    rw [zero_add, lambdaCompInt_natCast, plethMulU]
    exact diagScale_mem_lambdaComp _ (completeHomog_mem_lambdaComp L j)
  have h := coeffPairing_mem_lambdaCompInt hfam (plethCreateQ_mem_polyComp q hf)
  rw [add_zero, lambdaCompInt_natCast] at h
  exact h

end Graded

end HJO.Sym

/-! ### The displacement evaluated at one letter, truncated at the degree -/

namespace HJO.Mac

section QshiftEval

open HJO.Sym

variable {σ : Type*} [Fintype σ] [LinearOrder σ] {K : Type*} [Field K] [Algebra ℚ K]

/-- **The displacement evaluated at one letter is the parameter shift of that letter**,
`HJO.Mac.sum_restrictFrac_coeff_plethCreateQ` in its own shape:
`∑_{m=0}^{d} res_n([z^{-m}] qs(F)) x_i^m = T_{q,x_i}(res_n F)` for `F ∈ Λ_d`.

The truncation is legitimate by `HJO.Sym.coeff_plethCreateQ_eq_zero`; the underlying identity, which
needs no grading, is `HJO.Mac.qShift_restrictFrac`. The `n ≥ 1` is dead. -/
@[hjo "lem_ght3_qshift_eval"]
theorem sum_restrictFrac_coeff_plethCreateQ (q : Kˣ) (i : σ) {d : ℕ} {F : Lambda K}
    (hF : F ∈ LambdaComp K d) :
    ∑ m ∈ Finset.range (d + 1),
        restrictFrac σ K ((plethCreateQ (q : K) F).coeff m) * fracX K i ^ m
      = qShift q i (restrictFrac σ K F) := by
  have hnd : (plethCreateQ (q : K) F).natDegree ≤ d :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm =>
      coeff_plethCreateQ_eq_zero (q : K) hm hF
  rw [qShift_restrictFrac q i F,
    Polynomial.eval_eq_sum_range' (n := d + 1)
      (lt_of_le_of_lt (le_trans Polynomial.natDegree_map_le hnd) (by omega))]
  exact Finset.sum_congr rfl fun m _ => by rw [Polynomial.coeff_map]; rfl

end QshiftEval

end HJO.Mac

/-! ### Garsia--Haiman--Tesler's equation (4.24) -/

namespace HJO.Sym

section EopJfun

open HJO.Mac

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

/-- **Garsia--Haiman--Tesler's equation (4.24)**, `HJO.Sym.isEopEigenJfun`:
`u^n ℰ(J_μ) = (1 - (1-u)E_n(μ)) J_μ` at `n = max(|μ|, 1)`, written with the `u^n` divided across.
This is exactly `HJO.Sym.IsEopEigenJfun`, the one residual of
`HJO.Sym.dop_zero_macHtilde` and of `HJO.Standing.dop_zero_macHtilde_param`, so with it the whole of
Theorem 1.2, equation (1.11) a) is proved.

The chain is read in the base alphabet `X_{n_μ}` of `HJO.Sym.macPfun` rather than at a
general `n ≥ |μ|`, which is what makes `HJO.Mac.restrictAlphabet_macPfun_partDiagram` unnecessary:
`res_{n_μ}(P_μ)` is `P_μ[X_{n_μ}]` by the *definition* of `P_μ`
(`HJO.Sym.restrictAlphabet_macPfun`). Macdonald's operator scales `res(J_μ)` by `E_n(μ)`
(`HJO.Mac.macPpoly`), `HJO.Mac.dop_pleth` turns that into
`u^n res(ℰ J_μ) = (1-(1-u)E_n(μ)) res(J_μ)`, and `HJO.Sym.restrictAlphabetComp_bijective` lifts it
from the alphabet back to `Λ`, both sides lying in `Λ_{|μ|}` by `HJO.Sym.eop_mem_lambdaComp`.

Genericity is spent only on `u ≠ 0` (`HJO.Standing.u_ne_zero`), which
`HJO.Mac.pow_card_mul_map_completeHomog` needs, and --- through
`macJfun` --- on the existence of `P_μ` itself. -/
@[hjo "lem_ght3_eop_jfun"]
theorem isEopEigenJfun (hqu : AlgebraicIndependent ℤ ![(q : K), u]) : IsEopEigenJfun hqu := by
  intro μ
  have hu0 : u ≠ 0 := HJO.Standing.u_ne_zero hqu
  have hcard : Fintype.card (baseAlphabet μ) = max μ.card 1 := Fintype.card_fin _
  set n := max μ.card 1 with hn
  set E := macdonaldEigenvalue (q : K) u n μ with hE
  set γ := normalisingProduct (q : K) u μ with hγ
  -- the restriction of `J_μ` to the base alphabet
  have hres : restrictAlphabet (baseAlphabet μ) K (macJfun hqu μ)
      = γ • (macPpoly hqu (baseIdx μ) : MvPolynomial (baseAlphabet μ) K) := by
    rw [macJfun, map_smul, restrictAlphabet_macPfun]
  -- Macdonald's operator scales that restriction by the eigenvalue
  have heig : macOp q u (restrictFrac (baseAlphabet μ) K (macJfun hqu μ))
      = E • restrictFrac (baseAlphabet μ) K (macJfun hqu μ) := by
    have hpp := macOpComp_macPpoly hqu (baseIdx μ)
    rw [partDiagram_baseIdx, hcard] at hpp
    have hstep : macOp q u (algebraMap (MvPolynomial (baseAlphabet μ) K)
          (FractionRing (MvPolynomial (baseAlphabet μ) K))
          (macPpoly hqu (baseIdx μ) : MvPolynomial (baseAlphabet μ) K))
        = E • algebraMap (MvPolynomial (baseAlphabet μ) K)
            (FractionRing (MvPolynomial (baseAlphabet μ) K))
            (macPpoly hqu (baseIdx μ) : MvPolynomial (baseAlphabet μ) K) := by
      rw [← algebraMap_macOpComp q u μ.card (macPpoly hqu (baseIdx μ)), hpp]
      exact HJO.Mac.algebraMap_smul E _
    rw [restrictFrac_apply, hres, HJO.Mac.algebraMap_smul, map_smul, hstep, smul_comm]
  -- the plethystic form, after `HJO.Mac.dop_pleth`
  have hpl := dop_pleth (σ := baseAlphabet μ) (q := q) hu0 (macJfun hqu μ)
  have hup : (algebraMap K (FractionRing (MvPolynomial (baseAlphabet μ) K)) u) ^
      Fintype.card (baseAlphabet μ)
      = (algebraMap K (FractionRing (MvPolynomial (baseAlphabet μ) K)) u) ^ n := by
    rw [hcard]
  rw [heig, hup] at hpl
  -- clear the scalars into one restriction
  have hkey : restrictAlphabet (baseAlphabet μ) K (u ^ n • eop (q : K) u (macJfun hqu μ))
      = restrictAlphabet (baseAlphabet μ) K ((1 - (1 - u) * E) • macJfun hqu μ) := by
    refine IsFractionRing.injective (MvPolynomial (baseAlphabet μ) K)
      (FractionRing (MvPolynomial (baseAlphabet μ) K)) ?_
    rw [← restrictFrac_apply, ← restrictFrac_apply, map_smul, map_smul, Algebra.smul_def,
      Algebra.smul_def, map_sub, map_one, map_mul, map_sub, map_one, map_pow]
    rw [Algebra.smul_def] at hpl
    linear_combination hpl
  have hmem1 : u ^ n • eop (q : K) u (macJfun hqu μ) ∈ LambdaComp K μ.card :=
    Submodule.smul_mem _ _ (eop_mem_lambdaComp (q : K) u (macJfun_mem hqu μ))
  have hmem2 : (1 - (1 - u) * E) • macJfun hqu μ ∈ LambdaComp K μ.card :=
    Submodule.smul_mem _ _ (macJfun_mem hqu μ)
  have hlift : u ^ n • eop (q : K) u (macJfun hqu μ) = (1 - (1 - u) * E) • macJfun hqu μ := by
    have hb := (restrictAlphabetComp_bijective (baseAlphabet μ) K
      (card_le_card_baseAlphabet μ)).1 (a₁ := ⟨_, hmem1⟩) (a₂ := ⟨_, hmem2⟩) (Subtype.ext hkey)
    exact congrArg Subtype.val hb
  -- divide by `u^n`
  have hun : (u ^ n)⁻¹ * u ^ n = 1 := inv_mul_cancel₀ (pow_ne_zero n hu0)
  calc eop (q : K) u (macJfun hqu μ)
      = ((u ^ n)⁻¹ * u ^ n) • eop (q : K) u (macJfun hqu μ) := by rw [hun, one_smul]
    _ = (u ^ n)⁻¹ • (u ^ n • eop (q : K) u (macJfun hqu μ)) := by rw [smul_smul]
    _ = (u ^ n)⁻¹ • ((1 - (1 - u) * E) • macJfun hqu μ) := by rw [hlift]
    _ = (u⁻¹ ^ n * (1 - (1 - u) * macdonaldEigenvalue (q : K) u (max μ.card 1) μ)) •
          macJfun hqu μ := by rw [smul_smul, inv_pow, hE, hn]

/-- **Garsia--Haiman--Tesler, Theorem 1.2, equation (1.11) a)**,
`HJO.Standing.dop_zero_smul_macHtilde_param`, now a theorem: `D_0 H̃_μ = -(M B_μ - 1) H̃_μ`.

This is `HJO.Sym.dop_zero_macHtilde` with its residual hypothesis `heop` discharged by
`HJO.Sym.isEopEigenJfun`. The hypotheses `hυq` and `hυu` on
the inversion, and the genericity `hqu`, are not part of equation (1.11) a) ---
`𝕜 = ℚ(q,u)` supplies all three, which is what
`HJO.Standing.dop_zero_smul_macHtilde_param` says. -/
theorem dop_zero_smul_macHtilde {υ : K →+* K} (hυq : υ (q : K) = (q : K)) (hυu : υ u = u⁻¹)
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : YoungDiagram) :
    Dop (q : K) u 0 (macHtilde υ hqu μ)
      = -(paramProduct (q : K) u * cellSum (q : K) u μ - 1) • macHtilde υ hqu μ :=
  dop_zero_macHtilde hυq hυu hqu (isEopEigenJfun hqu) μ

end EopJfun

end HJO.Sym

/-! ### Equation (1.11) a) at the standing field, unconditionally -/

namespace HJO.Standing

open HJO.Ascent HJO.Sym

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- **Equation (1.11) a) at the standing field `𝕜 = ℚ(q,u)`**,
`HJO.Standing.dop_zero_smul_macHtilde_param` with **no hypothesis left**:
`D_0 H̃_μ = -(M B_μ - 1) H̃_μ`.

`HJO.Standing.dop_zero_macHtilde_param` reduced this to `HJO.Sym.IsEopEigenJfun`;
`HJO.Sym.isEopEigenJfun` proves that, so this is equation (1.11) a) itself. It is exactly the
hypothesis `hdop` of `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param`, which
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param_of_span` below feeds it. -/
@[hjo "lem_mac_dop_zero_htilde"]
theorem dop_zero_smul_macHtilde_param (μ : YoungDiagram) :
    Dop (paramQ K) (paramU K) 0
        (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ)
      = -(HJO.Sym.paramProduct (paramQ K) (paramU K) * cellSum (paramQ K) (paramU K) μ - 1) •
          macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ :=
  dop_zero_macHtilde_param K (isEopEigenJfun (algebraicIndependent_paramQUnit K)) μ

/-- **The first residual hypothesis of the collinear goal, now resting on two statements.**
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param` asked for three; `hdop` is
discharged by `HJO.Standing.dop_zero_smul_macHtilde_param`, so what is left is that `H̃` spans `Λ`
(`HJO.Standing.exists_basis_macHtilde`) and `HJO.Sym.coeffSubst_macPfun`. It is a
reduction. -/
theorem hasUnnormalisedMacdonaldEigenbasis_macHtilde_param_of_span
    (hspan : Submodule.span K
      (Set.range (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K))) = ⊤)
    (hPι : ∀ μ : YoungDiagram,
      coeffSubst (paramQUInvHom K) (macPfun (algebraicIndependent_paramQUnit K) μ)
        = macPfun (algebraicIndependent_paramQUnit K) μ) :
    HasUnnormalisedMacdonaldEigenbasis (paramQUInvHom K) (paramQ K) (paramU K) :=
  hasUnnormalisedMacdonaldEigenbasis_macHtilde_param K hspan
    (dop_zero_smul_macHtilde_param K) hPι

end HJO.Standing
