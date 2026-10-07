/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.EsymmAlphabet
public meta import HJO.Attr

/-! # The displacement of an elementary symmetric function

The plethystic displacement `δ = HJO.Sym.plethShift q u` adds the four letters
`M/z = (1 - q)(1 - u) w` to the alphabet, written in `w = z⁻¹`: it carries the power sum `p_j` to
`p_j + (1 - qʲ)(1 - uʲ) wʲ`. On the generators it is therefore the sum of two `K`-algebra
homomorphisms `Λ → Λ[w]`, the inclusion `φ` and the homomorphism `ψ` keeping only the `w`-part, so
the convolution formula for the elementary symmetric functions of a sum of alphabets applies and
gives `δ(e_r) = ∑_{s ≤ r} e_{r-s} ψ(e_s)`.

The second half of the argument computes `ψ`. On a monomial `p_λ` it multiplies by
`∏_i (1 - q^{λ_i})(1 - u^{λ_i})`, which is the value of the parameter plethysm `κ` on that same
monomial, and by `w^{|λ|}`; so on a weighted homogeneous element of degree `d`, the `w`-power being
the same for every monomial occurring, it is `κ(·) w^d`. The elementary symmetric function `e_s` is
weighted homogeneous of degree `s`, whence `ψ(e_s) = κ(e_s) w^s` and the convolution becomes the
expansion `δ(e_r) = ∑_{s ≤ r} e_{r-s} κ(e_s) w^s`.

## Main statements

* `HJO.Bglx.psiHom_of_isWeightedHomogeneous`: the `w`-part of the displacement on a weighted
  homogeneous element of degree `d` is its parameter plethysm times `w ^ d`.
* `HJO.Bglx.psiHom_elemSymm`: the `w`-part of the displacement on `e_s` is `κ(e_s) w^s`.
* `HJO.Bglx.plethShift_elemSymm`: the expansion `δ(e_r) = ∑_{s ≤ r} e_{r-s} κ(e_s) w^s`.
* `HJO.Bglx.coeff_plethShift_elemSymm`: the same expansion read off coefficient by coefficient —
  the coefficient of `w^s` is `e_{r-s} κ(e_s)` for `s ≤ r` and `0` beyond.

## Implementation notes

Everything here is a step inside the proof of `HJO.Bglx.shiftExtendElem_expAlphabet`, whose
statement is about the displacement of the whole exponential factor `E_k`.

The splitting `δ = φ + ψ` holds on the *generators*, not as homomorphisms, which is exactly the
hypothesis `HJO.Bglx.map_elemSymm_add` asks for; `HJO.Bglx.plethShift_powerSum_eq_add` records it
with the positivity hypothesis `1 ≤ j` that undoes the truncated subtraction in `HJO.Sym.powerSum`.

The computation of `ψ` on a monomial is `MvPolynomial.aeval_monomial` on both sides at once: the
same `Finsupp.prod` over the support of the exponent appears in `ψ` and in `κ`, and the powers of
`w` collected from the factors add up to `∑ i (i+1) e i`, which is the weight of the exponent. The
weighted homogeneity of `e_s` is reproved here rather than imported: it is three lines from Newton's
identity, and `HJO.PhiE.isWeightedHomogeneous_elemSymm` — the same fact for
`HJO.Multiplication.degWeight` — sits behind a long import chain.

The coefficient ring is `Lambda K` for `K` a commutative `ℚ`-algebra, and no hypothesis on `q` or
`u` is needed: all of this is a polynomial identity in the two parameters.

## References

The expansion of `δ(e_r)` is the one-variable step of the proof of
`HJO.Bglx.shiftExtendElem_expAlphabet`, for the definitions `HJO.Sym.plethShift` and
`HJO.Bglx.paramPleth`. The reference is F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some
remarkable new plethystic operators in the theory of Macdonald polynomials*, arXiv:1405.0316v1,
J. Comb. **7** (2016) 671--714.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-! ### The weight of an exponent and the homogeneity of the elementary functions -/

/-- The weighted degree of a monomial, the generator of index `i` weighing `i + 1`, written as a
sum over the support of the exponent vector. -/
lemma weight_eq_sum_support (e : ℕ →₀ ℕ) :
    Finsupp.weight (fun i => i + 1) e = ∑ i ∈ e.support, (i + 1) * e i := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]

omit [Algebra ℚ K] in
/-- The generator of index `i` is the power sum `p_{i+1}`. -/
lemma powerSum_succ_eq_X (i : ℕ) : powerSum K (i + 1) = MvPolynomial.X i := by
  rw [powerSum, Nat.add_sub_cancel]

/-- **The elementary symmetric functions are weighted homogeneous**, `e_n` of degree `n` with the
generator of index `i` weighing `i + 1`: Newton's identity writes `e_n` as a combination of the
products `p_{k+1} e_{n-1-k}`, whose two weights add up to `n`. -/
theorem isWeightedHomogeneous_elemSymm (K : Type*) [CommRing K] [Algebra ℚ K] (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun i => i + 1) (elemSymm K n) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      rw [elemSymm_zero_eq_one]
      exact MvPolynomial.isWeightedHomogeneous_one K fun i => i + 1
    | m + 1 =>
      rw [elemSymm]
      refine MvPolynomial.IsWeightedHomogeneous.C_mul
        (MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun k hk => ?_) _
      rw [Finset.mem_range] at hk
      have hX : MvPolynomial.IsWeightedHomogeneous (fun i => i + 1)
          (powerSum K (k + 1)) (k + 1) := by
        rw [powerSum_succ_eq_X]
        exact MvPolynomial.isWeightedHomogeneous_X (R := K) (fun i => i + 1) k
      have hmul := hX.mul (ih (m - k) (by omega))
      rw [show k + 1 + (m - k) = m + 1 from by omega] at hmul
      have hsign : ((-1 : Lambda K)) ^ k * powerSum K (k + 1) * elemSymm K (m - k)
          = MvPolynomial.C ((-1 : K) ^ k) * (powerSum K (k + 1) * elemSymm K (m - k)) := by
        rw [map_pow, map_neg, map_one, mul_assoc]
      rw [hsign]
      exact MvPolynomial.IsWeightedHomogeneous.C_mul hmul _

/-! ### The two halves of the displacement -/

/-- The inclusion `Λ → Λ[w]` as a `K`-algebra homomorphism, the part of the displacement that
leaves the alphabet alone. -/
noncomputable def phiHom (K : Type*) [CommRing K] : Lambda K →ₐ[K] Polynomial (Lambda K) :=
  Polynomial.CAlgHom

omit [Algebra ℚ K] in
/-- The inclusion is the constant embedding `Λ → Λ[w]`. -/
@[simp] theorem phiHom_apply (x : Lambda K) : phiHom K x = Polynomial.C x := rfl

/-- The `w`-part of the displacement: the `K`-algebra homomorphism `Λ → Λ[w]` sending `p_j` to
`(1 - qʲ)(1 - uʲ) wʲ`. It is the difference between the displacement and the inclusion, taken as a
homomorphism in its own right so that the convolution formula for a sum of alphabets applies. -/
noncomputable def psiHom (q u : K) : Lambda K →ₐ[K] Polynomial (Lambda K) :=
  MvPolynomial.aeval fun i =>
    Polynomial.C (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))) * Polynomial.X ^ (i + 1)

omit [Algebra ℚ K] in
/-- The value of the `w`-part on the generator of index `i`, which stands for `p_{i+1}`. -/
theorem psiHom_X (q u : K) (i : ℕ) :
    psiHom q u (MvPolynomial.X i)
      = Polynomial.C (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))) *
        Polynomial.X ^ (i + 1) :=
  MvPolynomial.aeval_X _ i

omit [Algebra ℚ K] in
/-- **The displacement splits on the generators.** For every `j ≥ 1` the displacement of the power
sum `p_j` is the sum of its inclusion and its `w`-part, which is the hypothesis the convolution
formula `HJO.Bglx.map_elemSymm_add` asks for. -/
theorem plethShift_powerSum_eq_add (q u : K) {j : ℕ} (hj : 1 ≤ j) :
    plethShift q u (powerSum K j)
      = phiHom K (powerSum K j) + psiHom q u (powerSum K j) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [powerSum_succ_eq_X, psiHom_X, phiHom_apply, plethShift, MvPolynomial.aeval_X,
    powerSum_succ_eq_X]

/-! ### The `w`-part on a weighted homogeneous element -/

omit [Algebra ℚ K] in
/-- The `w`-part of the displacement on a monomial: it multiplies by the parameter plethysm of that
monomial and by the power of `w` recording the monomial's weight. Both sides are
`MvPolynomial.aeval` of a monomial, over the same product across the support of the exponent. -/
theorem psiHom_monomial (q u : K) (e : ℕ →₀ ℕ) (a : K) :
    psiHom q u (MvPolynomial.monomial e a)
      = Polynomial.C (MvPolynomial.C (paramPleth q u (MvPolynomial.monomial e a)))
        * Polynomial.X ^ Finsupp.weight (fun i => i + 1) e := by
  have hterm : ∀ i ∈ e.support,
      ((Polynomial.C (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))) *
            Polynomial.X ^ (i + 1) : Polynomial (Lambda K))) ^ e i
        = Polynomial.C (MvPolynomial.C (((1 - q ^ (i + 1)) * (1 - u ^ (i + 1))) ^ e i)) *
          Polynomial.X ^ ((i + 1) * e i) := fun i _ => by
    rw [mul_pow, ← map_pow, ← map_pow, ← pow_mul]
  have hprod : (e.prod fun i k => (Polynomial.C (MvPolynomial.C
        ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))) *
          Polynomial.X ^ (i + 1) : Polynomial (Lambda K)) ^ k)
      = Polynomial.C (MvPolynomial.C
            (e.prod fun i k => ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1))) ^ k))
          * Polynomial.X ^ Finsupp.weight (fun i => i + 1) e := by
    rw [Finsupp.prod, Finsupp.prod, Finset.prod_congr rfl hterm, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, ← map_prod, ← map_prod, weight_eq_sum_support]
  rw [paramPleth, MvPolynomial.aeval_monomial, map_mul, map_mul, psiHom,
    MvPolynomial.aeval_monomial, hprod,
    show (algebraMap K (Polynomial (Lambda K))) a = Polynomial.C (MvPolynomial.C a) from rfl,
    show (algebraMap K K) a = a from rfl]
  ring

omit [Algebra ℚ K] in
/-- **The `w`-part of the displacement on a weighted homogeneous element.** If `x` is weighted
homogeneous of degree `d`, the generator of index `i` weighing `i + 1`, then `ψ(x) = κ(x) w^d`:
every monomial of `x` has weight `d`, so every one of them contributes the same power of `w`, and
what is left of `ψ` on each is the parameter plethysm. -/
theorem psiHom_of_isWeightedHomogeneous (q u : K) {d : ℕ} {x : Lambda K}
    (hx : MvPolynomial.IsWeightedHomogeneous (fun i => i + 1) x d) :
    psiHom q u x
      = Polynomial.C (MvPolynomial.C (paramPleth q u x)) * Polynomial.X ^ d := by
  classical
  rw [MvPolynomial.as_sum x]
  simp only [map_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [psiHom_monomial, hx (MvPolynomial.mem_support_iff.1 he)]

/-- **The `w`-part of the displacement on an elementary symmetric function**: `ψ(e_s) = κ(e_s) w^s`,
since `e_s` is weighted homogeneous of degree `s`. -/
theorem psiHom_elemSymm (q u : K) (s : ℕ) :
    psiHom q u (elemSymm K s)
      = Polynomial.C (MvPolynomial.C (paramPleth q u (elemSymm K s))) * Polynomial.X ^ s :=
  psiHom_of_isWeightedHomogeneous q u (isWeightedHomogeneous_elemSymm K s)

/-! ### The displacement of an elementary symmetric function -/

/-- **The expansion of the displacement of an elementary symmetric function**:
`δ(e_r) = ∑_{s ≤ r} e_{r-s} κ(e_s) w^s`.

The displacement splits on the generators as the inclusion plus the `w`-part, so its value on `e_r`
is the convolution of the two families of elementary symmetric functions; the `w`-part's family is
the single term `κ(e_s) w^s` in each degree. -/
theorem plethShift_elemSymm (q u : K) (r : ℕ) :
    plethShift q u (elemSymm K r)
      = ∑ s ∈ Finset.range (r + 1),
          Polynomial.C (elemSymm K (r - s) * MvPolynomial.C (paramPleth q u (elemSymm K s)))
            * Polynomial.X ^ s := by
  rw [map_elemSymm_add (phiHom K) (psiHom q u) (plethShift q u)
    (fun j hj => plethShift_powerSum_eq_add q u hj) r]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [phiHom_apply, psiHom_elemSymm, map_mul, mul_assoc]

/-- **The displacement of an elementary symmetric function**:
`δ(e_r) = ∑_{s ≤ r} e_{r-s} κ(e_s) w^s`, so the coefficient of `w^s` is `e_{r-s} κ(e_s)` for
`s ≤ r` and `0` beyond. -/
theorem coeff_plethShift_elemSymm (q u : K) (r s : ℕ) :
    Polynomial.coeff (plethShift q u (elemSymm K r)) s
      = if s ≤ r then elemSymm K (r - s) * MvPolynomial.C (paramPleth q u (elemSymm K s))
        else 0 := by
  have hterm : ∀ t ∈ Finset.range (r + 1),
      Polynomial.coeff (Polynomial.C (elemSymm K (r - t) *
            MvPolynomial.C (paramPleth q u (elemSymm K t))) * Polynomial.X ^ t) s
        = if s = t then elemSymm K (r - t) * MvPolynomial.C (paramPleth q u (elemSymm K t))
          else 0 := fun t _ => by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [plethShift_elemSymm, Polynomial.finsetSum_coeff, Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

end HJO.Bglx
