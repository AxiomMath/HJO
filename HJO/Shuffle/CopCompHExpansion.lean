/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.AxisNewtonCompleteHomog

/-! # The creation seed of a general composition, on the `h`-basis and on the axis generators

`HJO.Mellit.copComp_singleton_apply_one` computes the creation seed at a one-part composition,
`C_{(r)}(1) = (-q)^{1-r}h_r`, and `HJO.Mellit.copComp_one_one_apply_one` computes it at `(1,1)`.
Neither computes it at a general `α`, and that element -- not the clause, not a datum carried
through an induction on the clause -- is what this file computes. Everything here is an identity
**in `Λ`**: no sweep operator, no slope homomorphism and no realisation occurs, so nothing below
is a restatement of `HJO.Mellit.LhsComputes` or of any of its append steps.

## The key identity

`HJO.CreationSeeds.plethCreate_elemSymm` computes the creation
displacement of an *elementary* symmetric function. Its `h`-side counterpart is
`HJO.CreationSeeds.plethCreate_completeHomog`:

  `h_n[X - (1 - q⁻¹)/z] = ∑_{j=0}^{n} c_j h_{n-j} wʲ`,  `c_0 = 1`,  `c_j = q^{-j} - q^{-(j-1)}`.

The route is that the alphabet `HJO.Sym.plethCreate` removes has **two** letters, not one: it
subtracts `(1 - q^{-k})wᵏ = wᵏ - (w/q)ᵏ` from `p_k`, so it is `{w} - {w/q}`, and the `h`-series of
its negative is the binomial `(1 - wt)/(1 - wt/q)` rather than a single linear factor.
`HJO.Sym.completeHomog_neg_single` (a negated letter, whose `h`-series is `1 - at`) and
`HJO.Sym.completeHomog_single` (a letter) therefore feed `HJO.Sym.completeHomog_of_add`, and in that
Cauchy product only the two top terms survive: that is
`HJO.CreationSeeds.dispAlphabet_completeHomog`, a single monomial in `w` of degree `m` in every
degree `m`. Everything else in this file is an evaluation or a transport of that one identity.

## What follows for the creation operators

* `HJO.CreationSeeds.cop_completeHomog`: `C_r(h_n) = (-q)^{1-r}∑_{j=0}^{n} c_j h_{n-j}h_{r+j}` --
  the `h`-analogue of `HJO.CreationSeeds.cop_elemSymm`.
* `HJO.CreationSeeds.cop_completeHomog_mul`: the same for a product `h_n h_m`, as a double sum over
  the two shifts. The displacement is an *algebra* homomorphism, so this is Leibniz, and it is the
  step that makes the recursion general: the `h`-monomials are closed under the creation operators,
  with coefficients that are products of the `c_j`.
* `HJO.Mellit.copComp_pair_apply_one`: the general two-part seed,
  `C_{(A,B)}(1) = (-q)^{2-A-B}∑_{j=0}^{B} c_j h_{B-j}h_{A+j}`.

`HJO.Mellit.copComp_one_one_apply_one_of_pair` is a consistency check: it re-derives the value
`q⁻¹e_1² + (1-q⁻¹)e_2` of `HJO.Mellit.copComp_one_one_apply_one` from the two-part formula,
through `h_1 = e_1` and `h_2 = e_1² - e_2` and nothing the proof of that value uses. A sign or an
off-by-one in `c_j` would separate the two.

## The general composition

The seed at a general `α` is not a closed form but an explicit recursion, and the recursion is run
on a *polynomial ring on the `h`-variables*, which is again `Λ` with `HJO.Sym.hVar` reading its
generator `p_m` as a variable standing for `h_m`:

* `HJO.Sym.hSub` substitutes `h_m` for that variable;
* `HJO.CreationSeeds.plethCreateH` is the creation displacement written on those variables -- the
  lift of `plethCreate_completeHomog` -- and `HJO.CreationSeeds.map_plethCreateH` says it is the
  creation displacement;
* `HJO.CreationSeeds.copH` is `HJO.Sym.Cop` with the `h`-variables in place of the `h`, and
  `HJO.CreationSeeds.hSub_copH` says it is `C_r`; `HJO.CreationSeeds.copCompH` is the composite over
  a composition and `HJO.CreationSeeds.hSub_copCompH` says it is `C_α`;
* hence `HJO.CreationSeeds.copComp_apply_one_eq_hSub`: `C_α(1) = hSub (copCompH q α 1)` for
  **every** composition `α`, with `copCompH q α 1` computed by
  `HJO.CreationSeeds.copH_apply_one` at the vacuum, `HJO.CreationSeeds.copH_hVar_succ` on a
  variable, `HJO.CreationSeeds.copH_mul_hVar` on a product of two, and `map_mul` beyond that.

What this transport adds beyond `plethCreate_completeHomog` is bookkeeping, and should be read as
such: the mathematics is in the displacement identity, and the transport turns it into a formula
that can be quantified over `α`. `HJO.Sym.hSub` is **not** proved injective here, so
`copComp_apply_one_eq_hSub` is an identity exhibiting an expansion, not a claim that it is the
unique one.

## In the axis generators

`HJO.Sym.completeHomog_smul_eq_sum_axisGen` is Newton's identity for the axis generators, in the
form `(1 - v^A)h_A = (v-1)v^{A-1}∑_{s=1}^{A}h_{A-s}U_s` that inverts nothing. Solved for `h_A` it
is `HJO.Sym.hU`, an element of `Λ` read as a polynomial in the variables the axis substitution
`HJO.Sym.axisSub` sends to the `U_k`, and `HJO.Sym.axisSub_hU` says the axis substitution sends it
to `h_A`. Composing, `HJO.Sym.axisSub_comp_hUSub` and
`HJO.CreationSeeds.copComp_apply_one_eq_axisSub` give, for every composition `α`,

  `C_α(1) = axisSub v (hUSub v (copCompH q α 1))`,   `v = qu`,

which is the creation seed written in the axis generators: the right-hand side's argument is an
explicit polynomial whose variable `p_k` stands for `U_k`.

## Genericity

`dispCoeff`, `dispAlphabet_completeHomog`, `plethCreate_completeHomog`, `cop_completeHomog`,
`cop_completeHomog_mul`, `copComp_pair_apply_one`, `copComp_one_one_apply_one_of_pair` and the whole
`h`-variable engine: **no hypothesis on `q`**. The spelling `c_j = q^{-j} - q^{-(j-1)}` of
`HJO.CreationSeeds.dispCoeff` is what buys that. At `q = 0` it reads `c_1 = -1` and `c_j = 0` for
`j ≥ 2`, which is the truth there -- the removed alphabet degenerates to the single letter `w` --
whereas the closed form `(1-q)q^{-j}` of `HJO.CreationSeeds.dispCoeff_succ_eq` reads `0` and is
false. So `dispCoeff_succ_eq` carries `q ≠ 0` and nothing else in the file does. This is not a claim
that `q = 0` is a sensible parameter: `HJO.Sym.Cop`'s own scalar `(-q)^{1-r}` is a totalisation
there, and `q ≠ 0` is spent wherever a value is read at a generic `q`.

`HJO.Sym.hU`, `HJO.Sym.axisSub_hU`, `HJO.Sym.axisSub_comp_hUSub` and
`copComp_apply_one_eq_axisSub`: `v ≠ 0` and `v^{j+1} ≠ 1` for every `j`, verbatim
`HJO.Sym.adjoin_axisGen_eq_top`'s, i.e. `v` is not a root of unity. At `v = qu` they read `q ≠ 0`,
`u ≠ 0` and `(qu)^k ≠ 1` for every `k ≥ 1`. None is decoration: `HJO.Sym.axisGen`'s normalising
scalar `v/(v-1)` collapses at `v = 1`, where every `U_k` is `0` (`HJO.Sym.axisGen_eq_zero`); at
`v = 0` the substitution `HJO.Sym.plethAxis` sends every `p_j` to `-p_j`; and `hU`'s scalar inverts
`1 - v^{A+1}`, which in a field is `0⁻¹ = 0` at an `(A+1)`-st root of unity, making `hU` the zero
element and the statement false rather than vacuous. Only `v^{j+1} ≠ 1` for `j < A` is used at `A`,
but the hypothesis is carried in the uniform shape so that it composes with
`adjoin_axisGen_eq_top`.

## What this does not give

No short closed form in `α`, and the recursion is the honest answer rather than a step towards one.
Run outside Lean, the `h`-expansion of `C_α(1)` has one monomial per shift matrix, and its support
is essentially the partitions of `N = |α|` with at most `ℓ(α)` parts: at
`α = (1), (1,1), (1,1,1), (1,1,1,1)` it has `1, 2, 3, 5` monomials, and at `(3,1,2)` it has `6` of
the `7` available. Feeding those through `hU` is worse, because the axis expansion of a single `h_A`
already has `p(A)` monomials with no cancellation, and `h_N` occurs in the support of every `C_α(1)`
computed. So a statement quantified over `α` has to be the recursion or nothing, exactly as for
`HJO.Sym.completeHomog_smul_eq_sum_axisGen`.

## References

This file works with `HJO.Sym.Cop`, `HJO.Sym.CopComp`, `HJO.CreationSeeds.cop_elemSymm`,
`HJO.CreationSeeds.plethCreate_elemSymm`, `HJO.Sym.plethCreate`, `HJO.Sym.completeHomog`,
`HJO.Sym.axisGen`, `HJO.Sym.axisSub`, `HJO.Sym.sum_alternating_completeHomog_mul_elemSymm`,
`HJO.Sym.sum_alternating_pow_completeHomog_mul_elemSymm` and `HJO.Sym.adjoin_axisGen_eq_top`.
-/

@[expose] public section

namespace HJO.CreationSeeds

open Finset

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The displacement coefficients -/

/-- The coefficient of `wʲ` in the creation displacement of a complete homogeneous function:
`c_0 = 1` and `c_j = q^{-j} - q^{-(j-1)}` for `j ≥ 1`. This spelling, rather than the closed form
`(1-q)q^{-j}` of `HJO.CreationSeeds.dispCoeff_succ_eq`, is what makes every statement below
unconditional in `q`; see the module docstring's genericity paragraph. -/
noncomputable def dispCoeff (q : L) : ℕ → L
  | 0 => 1
  | (j + 1) => (q ^ (j + 1))⁻¹ - (q ^ j)⁻¹

omit [Algebra ℚ L] in
@[simp] theorem dispCoeff_zero (q : L) : dispCoeff q 0 = 1 := rfl

omit [Algebra ℚ L] in
theorem dispCoeff_succ (q : L) (j : ℕ) :
    dispCoeff q (j + 1) = (q ^ (j + 1))⁻¹ - (q ^ j)⁻¹ := rfl

omit [Algebra ℚ L] in
theorem dispCoeff_one (q : L) : dispCoeff q 1 = q⁻¹ - 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, dispCoeff_succ]
  simp

omit [Algebra ℚ L] in
/-- **The closed form of the displacement coefficient**, `c_j = (1-q)q^{-j}`, which needs `q ≠ 0`:
at `q = 0` it reads `0` while `c_1 = -1`. -/
theorem dispCoeff_succ_eq (q : L) (hq : q ≠ 0) (j : ℕ) :
    dispCoeff q (j + 1) = (1 - q) * (q ^ (j + 1))⁻¹ := by
  rw [dispCoeff_succ, pow_succ]
  field_simp

/-! ### The creation displacement on a complete homogeneous function -/

/-- **The virtual alphabet the creation displacement removes**, as an algebra homomorphism:
`p_j ↦ -wʲ + (w/q)ʲ`. It is `{w/q} - {w}`, a difference of two letters, because
`HJO.Sym.plethCreate` subtracts `(1 - q^{-j})wʲ` and that is `wʲ - (w/q)ʲ`. -/
noncomputable def dispAlphabet (q : L) : Sym.Lambda L →ₐ[L] Polynomial (Sym.Lambda L) :=
  MvPolynomial.aeval fun i => -(Polynomial.X ^ (i + 1))
    + (Polynomial.C (MvPolynomial.C q⁻¹) * Polynomial.X) ^ (i + 1)

omit [Algebra ℚ L] in
theorem dispAlphabet_X (q : L) (i : ℕ) :
    dispAlphabet q (MvPolynomial.X i)
      = -(Polynomial.X ^ (i + 1))
        + (Polynomial.C (MvPolynomial.C q⁻¹) * Polynomial.X : Polynomial (Sym.Lambda L))
            ^ (i + 1) := by
  rw [dispAlphabet, MvPolynomial.aeval_X]

/-- **The removed alphabet is a difference of two letters, so its `h`-series is a binomial.**
`h_m` of `{w/q} - {w}` is the single monomial `(q^{-m} - q^{-(m-1)})wᵐ`.

`HJO.Sym.completeHomog_of_add` splits the alphabet into the negated letter `w`, whose `h`-series is
the polynomial `1 - wt` (`HJO.Sym.completeHomog_neg_single`: only `h_0` and `h_1` are nonzero), and
the letter `w/q`, whose `h`-series is geometric (`HJO.Sym.completeHomog_single`). In the Cauchy
product of the two only the terms with the negated letter at `h_0` and `h_1` survive, which leaves
the two monomials `(w/q)ᵐ` and `-w(w/q)^{m-1}`.

Unconditional: nothing is inverted, and at `q = 0` the statement reads `h_1 ↦ -w`, `h_m ↦ 0` for
`m ≥ 2`, which is the degeneration to the single letter `w`. -/
theorem dispAlphabet_completeHomog (q : L) (m : ℕ) :
    dispAlphabet q (Sym.completeHomog L m)
      = Polynomial.monomial m (MvPolynomial.C (dispCoeff q m)) := by
  set ν : Sym.Lambda L →ₐ[L] Polynomial (Sym.Lambda L) :=
    MvPolynomial.aeval fun i => -(Polynomial.X ^ (i + 1) : Polynomial (Sym.Lambda L)) with hν
  set μ : Sym.Lambda L →ₐ[L] Polynomial (Sym.Lambda L) :=
    MvPolynomial.aeval fun i =>
      (Polynomial.C (MvPolynomial.C q⁻¹) * Polynomial.X : Polynomial (Sym.Lambda L)) ^ (i + 1)
    with hμ
  have hνX : ∀ i : ℕ, ν (MvPolynomial.X i)
      = -(Polynomial.X : Polynomial (Sym.Lambda L)) ^ (i + 1) := fun i => by
    rw [hν, MvPolynomial.aeval_X]
  have hμX : ∀ i : ℕ, μ (MvPolynomial.X i)
      = (Polynomial.C (MvPolynomial.C q⁻¹) * Polynomial.X : Polynomial (Sym.Lambda L))
          ^ (i + 1) := fun i => by
    rw [hμ, MvPolynomial.aeval_X]
  obtain ⟨hν0, hν1, hνtop⟩ := Sym.completeHomog_neg_single ν Polynomial.X hνX
  have hμh : ∀ s : ℕ, μ (Sym.completeHomog L s)
      = (Polynomial.C (MvPolynomial.C q⁻¹) * Polynomial.X : Polynomial (Sym.Lambda L)) ^ s :=
    fun s => Sym.completeHomog_single μ _ hμX s
  have hadd : ∀ i : ℕ, dispAlphabet q (MvPolynomial.X i)
      = ν (MvPolynomial.X i) + μ (MvPolynomial.X i) := fun i => by
    rw [dispAlphabet_X, hνX i, hμX i]
  have hsum := Sym.completeHomog_of_add ν μ (dispAlphabet q) hadd m
  have hpow : ∀ k : ℕ,
      (Polynomial.C (MvPolynomial.C q⁻¹) * Polynomial.X : Polynomial (Sym.Lambda L)) ^ k
        = Polynomial.monomial k (MvPolynomial.C ((q ^ k)⁻¹)) := fun k => by
    rw [mul_pow, ← map_pow, ← map_pow, inv_pow, Polynomial.C_mul_X_pow_eq_monomial]
  -- only the two top terms of the `ν`-series survive
  rcases m with _ | m
  · rw [hsum, Finset.sum_range_one]
    simp [CopPower.completeHomog_zero, Polynomial.monomial_zero_left]
  · rw [hsum, Finset.sum_range_succ, Finset.sum_range_succ]
    have hzero : ∀ s ∈ range m,
        ν (Sym.completeHomog L (m + 1 - s)) * μ (Sym.completeHomog L s) = 0 := by
      intro s hs
      rw [hνtop _ (by simp only [Finset.mem_range] at hs; omega), zero_mul]
    rw [Finset.sum_eq_zero hzero, zero_add, show m + 1 - m = 1 from by omega, Nat.sub_self,
      hν0, hν1, hμh, hμh, one_mul, hpow, hpow, dispCoeff_succ, map_sub, map_sub]
    have hX : (Polynomial.X : Polynomial (Sym.Lambda L))
        * Polynomial.monomial m (MvPolynomial.C ((q ^ m)⁻¹))
        = Polynomial.monomial (m + 1) (MvPolynomial.C ((q ^ m)⁻¹)) :=
      Polynomial.X_mul_monomial m _
    linear_combination -hX

/-- **The creation displacement of a complete homogeneous function.**
`h_n[X - (1 - q⁻¹)/z] = ∑_{j=0}^{n} c_j h_{n-j}wʲ` in `w = z⁻¹`, with `c_0 = 1` and
`c_j = q^{-j} - q^{-(j-1)}`.

This is the `h`-side of `HJO.CreationSeeds.plethCreate_elemSymm`, and it
is the one new identity of this file: everything else is an evaluation or a transport of it. The
Cauchy product of `HJO.Sym.completeHomog_of_add` splits `X - (1-q⁻¹)/z` into `X` -- contributing
`h_{n-j}` -- and the removed alphabet, whose `h`-series is the single monomial of
`HJO.CreationSeeds.dispAlphabet_completeHomog`.

Unconditional in `q`. -/
theorem plethCreate_completeHomog (q : L) (n : ℕ) :
    Sym.plethCreate q (Sym.completeHomog L n)
      = ∑ j ∈ range (n + 1), Polynomial.monomial j
          (MvPolynomial.C (dispCoeff q j) * Sym.completeHomog L (n - j)) := by
  have hadd : ∀ i : ℕ, Sym.plethCreate q (MvPolynomial.X i)
      = (Polynomial.C : Sym.Lambda L →+* Polynomial (Sym.Lambda L)) (MvPolynomial.X i)
        + dispAlphabet q (MvPolynomial.X i) := by
    intro i
    rw [plethCreate_X, dispAlphabet_X, CopPower.powerSum_succ]
    have hp : ((Polynomial.C (MvPolynomial.C q⁻¹) : Polynomial (Sym.Lambda L))
          * Polynomial.X) ^ (i + 1)
        = Polynomial.C (MvPolynomial.C ((q ^ (i + 1))⁻¹)) * Polynomial.X ^ (i + 1) := by
      rw [mul_pow, ← map_pow, ← map_pow, inv_pow]
    have hc : (Polynomial.C (MvPolynomial.C (1 - (q ^ (i + 1))⁻¹))
          : Polynomial (Sym.Lambda L))
        = 1 - Polynomial.C (MvPolynomial.C ((q ^ (i + 1))⁻¹)) := by
      rw [map_sub, map_sub, map_one, map_one]
    rw [hp, hc]
    ring
  rw [Sym.completeHomog_of_add (Polynomial.C : Sym.Lambda L →+* Polynomial (Sym.Lambda L))
    (dispAlphabet q) (Sym.plethCreate q) hadd n]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [dispAlphabet_completeHomog, Polynomial.C_mul_monomial, mul_comm]

/-! ### The creation operators on the complete homogeneous basis -/

/-- **The `r`-th creation operator on a complete homogeneous function**:
`C_r(h_n) = (-q)^{1-r}∑_{j=0}^{n} c_j h_{n-j}h_{r+j}`.

The `h`-analogue of `HJO.CreationSeeds.cop_elemSymm`. `HJO.Sym.Cop` pairs the coefficient of `wʲ` in
the displaced element against `h_{r+j}`, and `HJO.CreationSeeds.plethCreate_completeHomog` says that
coefficient is `c_j h_{n-j}`; the whole content is that identity, so this is unconditional in `q` as
well. At `n = 0` it is the one-part seed `C_r(1) = (-q)^{1-r}h_r`. -/
theorem cop_completeHomog (q : L) (r n : ℕ) :
    Sym.Cop q r (Sym.completeHomog L n)
      = MvPolynomial.C ((-q) ^ (1 - (r : ℤ)))
        * ∑ j ∈ range (n + 1), MvPolynomial.C (dispCoeff q j) * Sym.completeHomog L (n - j)
            * Sym.completeHomog L (r + j) := by
  rw [Sym.Cop]
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  rw [plethCreate_completeHomog, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Sym.coeffPairing_monomial]
  ring

/-- **The `r`-th creation operator on a product of two complete homogeneous functions**:
`C_r(h_nh_m) = (-q)^{1-r}∑_{j,k} c_jc_k h_{n-j}h_{m-k}h_{r+j+k}`.

Leibniz: `HJO.Sym.plethCreate` is an *algebra* homomorphism, so the displacement of a product is the
product of the displacements, and the coefficient of `wʲ⁺ᵏ` in it is the convolution. This is the
step that makes the recursion in the composition general -- the span of the `h`-monomials is carried
into itself by every creation operator, with coefficients that are products of the `c_j` -- and it
is what a three-part composition needs, since the two-part seed is already a sum of products of two
`h`. Unconditional in `q`. -/
theorem cop_completeHomog_mul (q : L) (r n m : ℕ) :
    Sym.Cop q r (Sym.completeHomog L n * Sym.completeHomog L m)
      = MvPolynomial.C ((-q) ^ (1 - (r : ℤ)))
        * ∑ j ∈ range (n + 1), ∑ k ∈ range (m + 1),
            MvPolynomial.C (dispCoeff q j * dispCoeff q k)
              * (Sym.completeHomog L (n - j) * Sym.completeHomog L (m - k))
              * Sym.completeHomog L (r + (j + k)) := by
  rw [Sym.Cop]
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  rw [map_mul, plethCreate_completeHomog, plethCreate_completeHomog, Finset.sum_mul_sum,
    map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.monomial_mul_monomial, Sym.coeffPairing_monomial, MvPolynomial.C_mul]
  ring

end HJO.CreationSeeds

namespace HJO.Sym

open Finset

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### Transporting the coefficient pairing along a ring homomorphism -/

omit [Algebra ℚ L] in
/-- **The coefficient pairing transports along a ring homomorphism of `Λ`**: `φ` of the pairing
against `c` is the pairing against `φ ∘ c` of the coefficientwise image. Induction on the polynomial
through `HJO.Sym.coeffPairing_monomial`. -/
theorem coeffPairing_map (φ : Lambda L →+* Lambda L) (c : ℕ → Lambda L)
    (P : Polynomial (Lambda L)) :
    φ (coeffPairing c P) = coeffPairing (fun j => φ (c j)) (Polynomial.map φ P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [Polynomial.map_add, map_add, map_add, hP, hQ, map_add]
  | monomial k b =>
    rw [coeffPairing_monomial, Polynomial.map_monomial, coeffPairing_monomial, map_mul]

/-! ### The polynomial ring on the complete homogeneous functions -/

/-- The variable of `Λ` standing for `h_m`: the generator `p_m` for `m ≥ 1`, and `1` for `m = 0`.
Reading `Λ` as the polynomial ring on these variables is what lets the creation recursion be run
formally, before any `h` is substituted. -/
noncomputable def hVar (L : Type*) [CommRing L] : ℕ → Lambda L
  | 0 => 1
  | (m + 1) => MvPolynomial.X m

/-- The substitution sending the variable standing for `h_m` to `h_m`. It is an algebra
homomorphism and is not claimed here to be injective. -/
noncomputable def hSub (L : Type*) [Field L] [Algebra ℚ L] : Lambda L →ₐ[L] Lambda L :=
  MvPolynomial.aeval fun i => completeHomog L (i + 1)

theorem hSub_X (L : Type*) [Field L] [Algebra ℚ L] (i : ℕ) :
    hSub L (MvPolynomial.X i) = completeHomog L (i + 1) := by
  rw [hSub, MvPolynomial.aeval_X]

theorem hSub_C (L : Type*) [Field L] [Algebra ℚ L] (a : L) :
    hSub L (MvPolynomial.C a) = MvPolynomial.C a := by
  rw [hSub, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

theorem hSub_hVar (L : Type*) [Field L] [Algebra ℚ L] (m : ℕ) :
    hSub L (hVar L m) = completeHomog L m := by
  match m with
  | 0 => rw [hVar, map_one, CopPower.completeHomog_zero]
  | (m + 1) => rw [hVar, hSub_X]

/-! ### The complete homogeneous functions in the axis generators -/

/-- The axis expansion of `h_A`: the element of `Λ`, read as a polynomial in the variables that
`HJO.Sym.axisSub` sends to the axis generators, whose image under the axis substitution is `h_A`. It
is `HJO.Sym.completeHomog_smul_eq_sum_axisGen` solved for `h_A`, so it inverts `1 - v^{A+1}` and is
the zero element at a root of unity; see `HJO.Sym.axisSub_hU`. -/
noncomputable def hU (v : L) : ℕ → Lambda L
  | 0 => 1
  | (A + 1) => MvPolynomial.C ((v - 1) * v ^ A * (1 - v ^ (A + 1))⁻¹)
      * ∑ s ∈ range (A + 1), hU v (A - s) * powerSum L (s + 1)
  decreasing_by omega

omit [Algebra ℚ L] in
theorem hU_zero (v : L) : hU v 0 = 1 := by rw [hU]

omit [Algebra ℚ L] in
theorem hU_succ (v : L) (A : ℕ) :
    hU v (A + 1) = MvPolynomial.C ((v - 1) * v ^ A * (1 - v ^ (A + 1))⁻¹)
      * ∑ s ∈ range (A + 1), hU v (A - s) * powerSum L (s + 1) := by rw [hU]

/-- **`h_A` expanded in the axis generators**: the axis substitution sends `HJO.Sym.hU v A` to
`h_A`.

Induction on `A` through `HJO.Sym.completeHomog_smul_eq_sum_axisGen`, whose statement
`(1 - v^A)h_A = (v-1)v^{A-1}∑_s h_{A-s}U_s` inverts nothing; the inverse of `1 - v^{A+1}` is
introduced here, once, and cancelled against it. The sum reads `h_{A-s}`, so the induction is the
recursion's own and needs no auxiliary family.

Genericity: `v ≠ 0` and `v^{j+1} ≠ 1` for every `j`, `HJO.Sym.adjoin_axisGen_eq_top`'s. At `v = 1`
every `U_k` is zero and at a root of unity `hU` collapses, so these are the difference between true
and false, not between stated and vacuous. -/
theorem axisSub_hU {v : L} (hv0 : v ≠ 0) (hv1 : ∀ j : ℕ, v ^ (j + 1) ≠ 1) (A : ℕ) :
    axisSub v (hU v A) = completeHomog L A := by
  have hvone : v ≠ 1 := fun h => hv1 0 (by rw [h, one_pow])
  induction A using Nat.strong_induction_on with
  | _ A ih =>
    match A with
    | 0 => rw [hU_zero, map_one, CopPower.completeHomog_zero]
    | (A + 1) =>
      have hden : (1 : L) - v ^ (A + 1) ≠ 0 := sub_ne_zero.mpr (Ne.symm (hv1 A))
      set S : Lambda L := ∑ s ∈ range (A + 1), completeHomog L (A - s) * axisGen v (s + 1) with hS
      have hnewton : MvPolynomial.C ((1 : L) - v ^ (A + 1)) * completeHomog L (A + 1)
          = MvPolynomial.C ((v - 1) * v ^ A) * S := by
        have h := completeHomog_smul_eq_sum_axisGen (L := L) hv0 hvone (A + 1)
        rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, Nat.add_sub_cancel] at h
        rw [h, hS]
        refine congrArg _ (Finset.sum_congr rfl fun s _ => ?_)
        rw [show A + 1 - (s + 1) = A - s from by omega]
      have himg : axisSub v (hU v (A + 1))
          = MvPolynomial.C ((v - 1) * v ^ A * ((1 : L) - v ^ (A + 1))⁻¹) * S := by
        rw [hU_succ, map_mul, MvPolynomial.algHom_C, map_sum, hS]
        rw [show (algebraMap L (Lambda L)) ((v - 1) * v ^ A * ((1 : L) - v ^ (A + 1))⁻¹)
          = MvPolynomial.C ((v - 1) * v ^ A * ((1 : L) - v ^ (A + 1))⁻¹) from rfl]
        refine congrArg _ (Finset.sum_congr rfl fun s hs => ?_)
        rw [map_mul, ih (A - s) (by omega), axisSub_powerSum v (Nat.succ_pos s)]
      have hinv : MvPolynomial.C (((1 : L) - v ^ (A + 1))⁻¹)
          * MvPolynomial.C ((1 : L) - v ^ (A + 1)) = (1 : Lambda L) := by
        rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hden, MvPolynomial.C_1]
      rw [himg]
      calc MvPolynomial.C ((v - 1) * v ^ A * ((1 : L) - v ^ (A + 1))⁻¹) * S
          = MvPolynomial.C (((1 : L) - v ^ (A + 1))⁻¹)
              * (MvPolynomial.C ((v - 1) * v ^ A) * S) := by
            rw [← mul_assoc, ← MvPolynomial.C_mul,
              mul_comm (((1 : L) - v ^ (A + 1))⁻¹) ((v - 1) * v ^ A)]
        _ = MvPolynomial.C (((1 : L) - v ^ (A + 1))⁻¹)
              * (MvPolynomial.C ((1 : L) - v ^ (A + 1)) * completeHomog L (A + 1)) := by
            rw [hnewton]
        _ = completeHomog L (A + 1) := by rw [← mul_assoc, hinv, one_mul]

/-- The substitution sending the variable standing for `h_m` to the axis expansion `HJO.Sym.hU` of
`h_m`. Composed with the axis substitution it is `HJO.Sym.hSub`
(`HJO.Sym.axisSub_comp_hUSub`). -/
noncomputable def hUSub (v : L) : Lambda L →ₐ[L] Lambda L :=
  MvPolynomial.aeval fun i => hU v (i + 1)

omit [Algebra ℚ L] in
theorem hUSub_X (v : L) (i : ℕ) : hUSub v (MvPolynomial.X i) = hU v (i + 1) := by
  rw [hUSub, MvPolynomial.aeval_X]

/-- **The axis expansion factors the complete homogeneous substitution**:
`axisSub v ∘ hUSub v = hSub`. Both sides are algebra homomorphisms, so the claim is
`HJO.Sym.axisSub_hU` on the generators. -/
theorem axisSub_comp_hUSub {v : L} (hv0 : v ≠ 0) (hv1 : ∀ j : ℕ, v ^ (j + 1) ≠ 1) :
    (axisSub v).comp (hUSub v) = hSub L := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, hUSub_X, axisSub_hU hv0 hv1, hSub_X]

end HJO.Sym

namespace HJO.CreationSeeds

open Finset HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The creation operators on the polynomial ring of the `h`-variables -/

/-- The creation displacement written on the variables standing for the complete homogeneous
functions: the algebra homomorphism whose value on the variable for `h_{i+1}` is the right-hand side
of `HJO.CreationSeeds.plethCreate_completeHomog`. -/
noncomputable def plethCreateH (q : L) : Lambda L →ₐ[L] Polynomial (Lambda L) :=
  MvPolynomial.aeval fun i => ∑ j ∈ range (i + 2),
    Polynomial.monomial j (MvPolynomial.C (dispCoeff q j) * hVar L (i + 1 - j))

omit [Algebra ℚ L] in
theorem plethCreateH_X (q : L) (i : ℕ) :
    plethCreateH q (MvPolynomial.X i) = ∑ j ∈ range (i + 2),
      Polynomial.monomial j (MvPolynomial.C (dispCoeff q j) * hVar L (i + 1 - j)) := by
  rw [plethCreateH, MvPolynomial.aeval_X]

/-- **The displacement on the `h`-variables is the creation displacement.** Both sides are algebra
homomorphisms out of `Λ`, so `MvPolynomial.algHom_ext` reduces the claim to the generators, where it
is exactly `HJO.CreationSeeds.plethCreate_completeHomog`. This is where the content enters the
engine; everything after it is formal. -/
theorem map_plethCreateH (q : L) :
    (Polynomial.mapAlgHom (hSub L)).comp (plethCreateH q)
      = (Sym.plethCreate q).comp (hSub L) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hSub_X, plethCreateH_X,
    plethCreate_completeHomog, Polynomial.coe_mapAlgHom, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_monomial]
  simp only [RingHom.coe_coe, map_mul, hSub_C, hSub_hVar]

/-- The coefficient pairing transports along the complete homogeneous substitution. -/
theorem hSub_coeffPairing (c : ℕ → Lambda L) (P : Polynomial (Lambda L)) :
    hSub L (Sym.coeffPairing c P)
      = Sym.coeffPairing (fun j => hSub L (c j))
          (Polynomial.map (hSub L : Lambda L →+* Lambda L) P) :=
  coeffPairing_map (hSub L : Lambda L →+* Lambda L) c P

/-- The `r`-th creation operator written on the variables standing for the complete homogeneous
functions: `HJO.Sym.Cop` verbatim, with the `h`-variables in place of the `h`. -/
noncomputable def copH (q : L) (r : ℕ) : Module.End L (Lambda L) :=
  Sym.coeffPairing (fun j => MvPolynomial.C ((-q) ^ (1 - (r : ℤ))) * hVar L (r + j)) ∘ₗ
    (plethCreateH q).toLinearMap

/-- **The operator on the `h`-variables is the creation operator.** `HJO.Sym.Cop` is a pairing after
a displacement, so this is `HJO.CreationSeeds.map_plethCreateH` for the displacement and
`HJO.Sym.coeffPairing_map` for the pairing, with `HJO.Sym.hSub_hVar` identifying the two
families. -/
theorem hSub_copH (q : L) (r : ℕ) (f : Lambda L) :
    hSub L (copH q r f) = Sym.Cop q r (hSub L f) := by
  have hmap : Polynomial.map (hSub L : Lambda L →+* Lambda L) (plethCreateH q f)
      = Sym.plethCreate q (hSub L f) := by
    have h := congrArg (fun Φ : Lambda L →ₐ[L] Polynomial (Lambda L) => Φ f)
      (map_plethCreateH (L := L) q)
    simpa using h
  rw [copH, Sym.Cop]
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  have hfam : (fun j => hSub L (MvPolynomial.C ((-q) ^ (1 - (r : ℤ))) * hVar L (r + j)))
      = fun j => MvPolynomial.C ((-q) ^ (1 - (r : ℤ))) * Sym.completeHomog L (r + j) := by
    funext j
    rw [map_mul, hSub_C, hSub_hVar]
  rw [hSub_coeffPairing, hmap, hfam]

omit [Algebra ℚ L] in
/-- The operator on the `h`-variables, unfolded: the pairing of the displaced element against the
shifted family of `h`-variables. Since `HJO.CreationSeeds.plethCreateH` is an *algebra*
homomorphism, this is what makes the rule below extend from a single variable to a product of
them -- `plethCreateH q (f * g) = plethCreateH q f * plethCreateH q g` is `map_mul`. -/
theorem copH_eq_coeffPairing (q : L) (r : ℕ) (f : Lambda L) :
    copH q r f = Sym.coeffPairing
      (fun j => MvPolynomial.C ((-q) ^ (1 - (r : ℤ))) * hVar L (r + j)) (plethCreateH q f) :=
  rfl

omit [Algebra ℚ L] in
/-- **The operator on the `h`-variables at the vacuum.** -/
theorem copH_apply_one (q : L) (r : ℕ) :
    copH q r (1 : Lambda L) = MvPolynomial.C ((-q) ^ (1 - (r : ℤ))) * hVar L r := by
  rw [copH]
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  rw [map_one, show (1 : Polynomial (Lambda L)) = Polynomial.monomial 0 1 from by
      rw [Polynomial.monomial_zero_left, Polynomial.C_1],
    Sym.coeffPairing_monomial, one_mul, Nat.add_zero]

omit [Algebra ℚ L] in
/-- **The one-step rule on the `h`-variables**, the mirror of
`HJO.CreationSeeds.cop_completeHomog`: it is what makes `copCompH` computable without unfolding a
definition. Together with `map_mul` on `HJO.CreationSeeds.plethCreateH` it determines `copH` on
every element. -/
theorem copH_hVar_succ (q : L) (r m : ℕ) :
    copH q r (hVar L (m + 1)) = MvPolynomial.C ((-q) ^ (1 - (r : ℤ)))
      * ∑ j ∈ range (m + 2), MvPolynomial.C (dispCoeff q j) * hVar L (m + 1 - j)
          * hVar L (r + j) := by
  rw [copH]
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  rw [show hVar L (m + 1) = MvPolynomial.X m from by rw [hVar], plethCreateH_X, map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Sym.coeffPairing_monomial]
  ring

omit [Algebra ℚ L] in
/-- **The two-factor rule on the `h`-variables**, the mirror of
`HJO.CreationSeeds.cop_completeHomog_mul`: `copH` on a product of two variables is the double sum
over the two shifts. Leibniz again -- `HJO.CreationSeeds.plethCreateH` is an algebra homomorphism --
and it is what the three-part composition needs, since the two-part seed is already a sum of
products of two variables. -/
theorem copH_mul_hVar (q : L) (r n m : ℕ) :
    copH q r (hVar L (n + 1) * hVar L (m + 1)) = MvPolynomial.C ((-q) ^ (1 - (r : ℤ)))
      * ∑ j ∈ range (n + 2), ∑ k ∈ range (m + 2),
          MvPolynomial.C (dispCoeff q j * dispCoeff q k)
            * (hVar L (n + 1 - j) * hVar L (m + 1 - k)) * hVar L (r + (j + k)) := by
  rw [copH_eq_coeffPairing, map_mul,
    show hVar L (n + 1) = MvPolynomial.X n from by rw [hVar],
    show hVar L (m + 1) = MvPolynomial.X m from by rw [hVar],
    plethCreateH_X, plethCreateH_X, Finset.sum_mul_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.monomial_mul_monomial, Sym.coeffPairing_monomial, MvPolynomial.C_mul]
  ring

/-- The composite creation operator of a composition, written on the `h`-variables:
`HJO.Sym.CopComp` verbatim. -/
noncomputable def copCompH (q : L) (α : List ℕ) : Module.End L (Lambda L) :=
  (α.map (copH q)).prod

omit [Algebra ℚ L] in
theorem copCompH_cons (q : L) (r : ℕ) (β : List ℕ) :
    copCompH q (r :: β) = copH q r * copCompH q β := by
  rw [copCompH, copCompH, List.map_cons, List.prod_cons]

/-- **The composite operator on the `h`-variables is the composite creation operator.** Induction on
the composition, one `HJO.CreationSeeds.hSub_copH` per part. -/
theorem hSub_copCompH (q : L) (α : List ℕ) (f : Lambda L) :
    hSub L (copCompH q α f) = Sym.CopComp q α (hSub L f) := by
  induction α with
  | nil => simp [copCompH, Sym.CopComp]
  | cons r β ih =>
    rw [copCompH_cons, Module.End.mul_apply, hSub_copH, ih,
      show Sym.CopComp q (r :: β) = Sym.Cop q r * Sym.CopComp q β from by
        rw [Sym.CopComp, Sym.CopComp, List.map_cons, List.prod_cons],
      Module.End.mul_apply]

omit [Algebra ℚ L] in
/-- **The one-part case of the engine**, which through `HJO.CreationSeeds.hSub_copCompH` is
`HJO.Mellit.copComp_singleton_apply_one`. -/
theorem copCompH_singleton_apply_one (q : L) (A : ℕ) :
    copCompH q [A] (1 : Lambda L) = MvPolynomial.C ((-q) ^ (1 - (A : ℤ))) * hVar L A := by
  rw [show copCompH q [A] = copH q A from by rw [copCompH]; simp, copH_apply_one]

/-! ### The general expansion of the creation seed -/

/-- **The creation seed of a general composition, in the complete homogeneous basis.** For every
composition `α`, `C_α(1)` is the image under `HJO.Sym.hSub` of `copCompH q α 1`, an explicit element
of the polynomial ring on the `h`-variables computed from `HJO.CreationSeeds.copH_apply_one`,
`HJO.CreationSeeds.copH_hVar_succ` and `map_mul`.

Unconditional in `q`, and quantified over every composition. What it adds beyond
`HJO.CreationSeeds.plethCreate_completeHomog` is bookkeeping; `HJO.Sym.hSub` is not proved injective
here, so this exhibits an expansion rather than asserting it is the only one. -/
theorem copComp_apply_one_eq_hSub (q : L) (α : List ℕ) :
    Sym.CopComp q α (1 : Lambda L) = hSub L (copCompH q α 1) := by
  rw [hSub_copCompH, show hSub L (1 : Lambda L) = 1 from map_one _]

/-- **The creation seed of a general composition, in the axis generators.** For every composition
`α`, `C_α(1) = axisSub v (hUSub v (copCompH q α 1))`: the argument of the axis substitution is an
explicit polynomial whose variable `p_k` stands for `U_k`, obtained by substituting the axis
expansion `HJO.Sym.hU` of each `h` into the `h`-expansion of the seed.

This is the creation-side element the `hlhs` leg needs at a general `α`, in the generators on which
`Θ` is known. Genericity: `v ≠ 0` and `v^{j+1} ≠ 1` for every `j`, from `HJO.Sym.axisSub_hU`; at
`v = qu` they read `q ≠ 0`, `u ≠ 0` and `(qu)^k ≠ 1` for every `k ≥ 1`. Nothing further is spent on
`q`. -/
theorem copComp_apply_one_eq_axisSub (q : L) {v : L} (hv0 : v ≠ 0)
    (hv1 : ∀ j : ℕ, v ^ (j + 1) ≠ 1) (α : List ℕ) :
    Sym.CopComp q α (1 : Lambda L) = axisSub v (hUSub v (copCompH q α 1)) := by
  rw [copComp_apply_one_eq_hSub, ← axisSub_comp_hUSub (L := L) hv0 hv1, AlgHom.comp_apply]

end HJO.CreationSeeds

namespace HJO.Mellit

open Finset HJO.Sym HJO.CreationSeeds

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The creation seed of a two-part composition -/

/-- **The creation seed of a two-part composition, in the complete homogeneous basis**:
`C_{(A,B)}(1) = (-q)^{1-A}(-q)^{1-B}∑_{j=0}^{B} c_j h_{B-j}h_{A+j}`.

The inner operator gives `C_B(1) = (-q)^{1-B}h_B` (`HJO.Mellit.copComp_singleton_apply_one`), whose
scalar is a constant of `Λ` and so passes through the `L`-linear `C_A`; what is left is
`HJO.CreationSeeds.cop_completeHomog`. Note that the `j`-sum runs to `B` -- the *inner* part -- so
the second index never drops below `A`: the expansion is supported on the partitions `(B-j, A+j)`
and not on all partitions of `A + B`.

General in both parts and unconditional in `q`. -/
theorem copComp_pair_apply_one (q : L) (A B : ℕ) :
    CopComp q [A, B] (1 : Lambda L)
      = MvPolynomial.C ((-q) ^ (1 - (A : ℤ)) * (-q) ^ (1 - (B : ℤ)))
        * ∑ j ∈ range (B + 1), MvPolynomial.C (dispCoeff q j) * completeHomog L (B - j)
            * completeHomog L (A + j) := by
  have hcop : CopComp q [A, B] = Cop q A * Cop q B := by rw [CopComp]; simp
  have hB : Cop q B (1 : Lambda L)
      = MvPolynomial.C ((-q) ^ (1 - (B : ℤ))) * completeHomog L B := by
    have h := copComp_singleton_apply_one (L := L) q B
    rwa [show CopComp q [B] = Cop q B from by rw [CopComp]; simp] at h
  rw [hcop, Module.End.mul_apply, hB, ← MvPolynomial.smul_eq_C_mul, map_smul,
    cop_completeHomog, MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul]
  ring

/-- **Consistency check on the displacement coefficients.** At `A = B = 1` the two-part formula
reads `h_1² + (q⁻¹ - 1)h_2`, and `h_1 = e_1` with `h_2 = e_1² - e_2`
(`HJO.Sym.completeHomog_two_add_elemSymm_two`) turn that into `q⁻¹e_1² + (1-q⁻¹)e_2`, which is the
value `HJO.Mellit.copComp_one_one_apply_one`, proved there from
`HJO.CreationSeeds.cop_elemSymm` on the
*elementary* side and sharing nothing with the route here. A sign or an off-by-one in `dispCoeff`
would separate them, so this is the check on the normalisation of the whole file.

Unconditional in `q`: both sides are totalisations at `q = 0`. -/
theorem copComp_one_one_apply_one_of_pair (q : L) :
    CopComp q [1, 1] (1 : Lambda L)
      = MvPolynomial.C q⁻¹ * elemSymm L 1 ^ 2 + MvPolynomial.C (1 - q⁻¹) * elemSymm L 2 := by
  have h1 : completeHomog L 1 = elemSymm L 1 := by
    rw [CopPower.completeHomog_one, elemSymm_one]
  have h2 : completeHomog L 2 = elemSymm L 1 ^ 2 - elemSymm L 2 := by
    rw [← completeHomog_two_add_elemSymm_two L]; ring
  rw [copComp_pair_apply_one, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [dispCoeff_one, h1, h2, CopPower.completeHomog_zero]
  ring

end HJO.Mellit
