/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.PpolyTopEigen

/-! # `macOpNum` read in the greatest variable, and the eigenvalue it leaves

Step 3 of the proof of `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`, assembled.
`HJO/Macdonald/PpolyTopEigen.lean` computes the coefficient of `x_t^{n-1+r}` of each *summand*
of `HJO.Mac.macOpNum`; this file sums those computations, and the answer is that the whole
numerator of Macdonald's operator, read at that coefficient, is `(-1)^{n-1}` times the numerator of
Macdonald's operator **in the small alphabet** applied to the extracted coefficient, plus one
leftover term `𝒱_{N'}u^{n-1}q^r g`.

## Where every sign goes

The summand computations deliberately leave the sign `(-1)^{c_i}` of
`HJO.Mac.vandermondeProd_mul_macOp` outside, so all the signs are handled here, in one place, and
the two cases are:

* at `i = t` the sign is `(-1)^{\#\{k < t\}} = (-1)^{n-1}` — every letter is below the greatest
  one, which is `HJO.Mac.IsTopExtension.card_filter_lt_top` at `HJO.Mac.isTopExtension_subtypeVal`;
* at `i ≠ t` the sign is `(-1)^{\#\{k < i\}}`, and that count is the *same* in the two alphabets
  (`HJO.Mac.IsTopExtension.card_filter_lt`). This is what makes the reindexed sum carry the small
  alphabet's signs, and it is the crux of the assembly: the Vandermonde factor contributes a
  further `(-1)^{n-2}` and the numerator factor a further `-1`, and `Finset.card_erase_add_one`
  turns `(n-2) + 1` back into `n-1`, with no truncated subtraction anywhere.

## Splitting the sum without touching the summands

The sum over the alphabet is split at `t` with `Fintype.sum_eq_add_sum_subtype_ne`, which reindexes
the rest over `{b : σ // b ≠ t}` in one step. Rewriting `(univ : Finset σ).erase t` into an image
instead — the route `HJO.Mac.killCompl_macOpNum` takes — would also rewrite the `univ.erase t`
*inside* the summand at `t`, where it is the index set of the Vandermonde product and must stay.

## From the sum to the eigenvalue

`HJO.Mac.macOpNum_eq_vandermondeProd_mul` at `P_μ[X_n]` says the left-hand side is
`E_n(μ)·𝒱_N·P_μ[X_n]`; its coefficient of `x_t^{n-1+r}` is read by one application of
`Polynomial.coeff_mul_add_eq_of_natDegree_le` against
`HJO.Mac.natDegree_splitAt_vandermondeProd_univ` and
`HJO.Mac.natDegree_splitAt_macPpoly_le`. Cancelling `(-1)^{n-1}` and then `𝒱_{N'}` — both
nonzero in the domain `𝕜[x_b : b ≠ t]` — leaves
`D^{(n-1)}_1 g = (E_n(μ) - u^{n-1}q^{λ_1})g`, and `HJO.Sym.macdonaldEigenvalue_succ_peel` names the
scalar: it is the eigenvalue of `μ` with its first row removed.

Nothing here asks anything of `q` and `u` beyond the `hqu` that naming `HJO.Mac.macPpoly` already
costs: the degree statements are bounds together with the coefficient *at* the bound, which is what
makes them unconditional (see `HJO/Macdonald/SplitNumFactor.lean`).

## Main results

* `HJO.Mac.card_subtype_ne_add_one`, `HJO.Mac.macOpNum_eq_sum_univ`.
* `HJO.Mac.coeff_splitAt_macOpNum`: the sum assembly, for an arbitrary `f` of degree at most `r`
  in `x_t`.
* `HJO.Mac.rowLen_partDiagram_zero`: the least letter carries the first row.
* `HJO.Mac.macOpNum_coeff_partExp_splitAt_macPpoly` and
  `HJO.Mac.macOpComp_coeff_partExp_splitAt_macPpoly`: Step 3 of that proof, as a
  polynomial identity and as an eigenvector equation in `𝒮_{n-1,d-r}`.

## References

Macdonald's polynomials: Step 3 of the proof of Lemma `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`,
on the definitions `HJO.Mac.macOp`, `HJO.Sym.macdonaldEigenvalue` and `HJO.Mac.macPpoly` and Lemma
`HJO.Mac.vandermondeProd_mul_macOp`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

/-! ### The sum assembly -/

section Sum

variable {σ K : Type*} [Field K] [LinearOrder σ] [Fintype σ] {t : σ}

/-- **The small alphabet has one letter fewer**, written as an addition. `HJO.Mac.card_subtype_ne`
says `#σ' = #σ - 1` with a truncated subtraction; this says `#σ' + 1 = #σ`, which is the form the
eigenvalue peel `HJO.Sym.macdonaldEigenvalue_succ_peel` asks for. -/
theorem card_subtype_ne_add_one (t : σ) : Fintype.card {b : σ // b ≠ t} + 1 = Fintype.card σ := by
  classical
  have h : 1 ≤ Fintype.card σ := Fintype.card_pos_iff.2 ⟨t⟩
  rw [Fintype.card_subtype_compl (p := fun b => b = t), Fintype.card_subtype_eq t]
  omega

/-- **`HJO.Mac.macOpNum` is its defining sum**, one summand per letter. -/
theorem macOpNum_eq_sum_univ (q : Kˣ) (u : K) (f : MvPolynomial σ K) :
    macOpNum q u f = ∑ i : σ, (-1) ^ #{k ∈ (univ : Finset σ) | k < i} *
      ((univ : Finset σ).erase i).vandermondeProd X *
      (∏ j ∈ (univ : Finset σ).erase i, (C u * X i - X j)) *
      rescaleEquiv (Pi.mulSingle i q) f := rfl

omit [Fintype σ] in
/-- The sign of a summand of `HJO.Mac.macOpNum` is a constant in `x_t`, so it comes out of the
coefficient. The three remaining factors are kept together in the shape the summand computations of
`HJO/Macdonald/PpolyTopEigen.lean` are stated in. -/
private theorem coeff_splitAt_neg_one_pow_mul (t : σ) (c m : ℕ) (V A D : MvPolynomial σ K) :
    Polynomial.coeff (splitAt t ((-1) ^ c * V * A * D)) m
      = (-1) ^ c * Polynomial.coeff (splitAt t (V * A * D)) m := by
  rw [show ((-1 : MvPolynomial σ K) ^ c * V * A * D) = (-1) ^ c * (V * A * D) by ring, map_mul,
    show splitAt (R := K) t ((-1 : MvPolynomial σ K) ^ c)
      = Polynomial.C ((-1 : MvPolynomial {b : σ // b ≠ t} K) ^ c) by simp [map_pow],
    Polynomial.coeff_C_mul]

/-- **The numerator of Macdonald's operator, read at `x_t^{n-1+r}`.** For `f` of degree at most `r`
in `x_t`, the coefficient is `(-1)^{n-1}` times the sum of the leftover term `𝒱_{N'}u^{n-1}q^rg`
and the numerator of Macdonald's operator in the small alphabet applied to `g`, the coefficient of
`x_t^r` in `f`.

This is the Step 3 on the left-hand side of `HJO.Mac.vandermondeProd_mul_macOp`, with no
genericity and with `f` arbitrary: the only hypothesis is the degree bound, which is
Step 1 of the proof. -/
theorem coeff_splitAt_macOpNum (ht : IsTop t) (q : Kˣ) (u : K) {f : MvPolynomial σ K} {r : ℕ}
    (hf : (splitAt t f).natDegree ≤ r) :
    Polynomial.coeff (splitAt t (macOpNum q u f)) (Fintype.card {b : σ // b ≠ t} + r)
      = (-1) ^ Fintype.card {b : σ // b ≠ t} *
          ((univ : Finset {b : σ // b ≠ t}).vandermondeProd X *
              C u ^ Fintype.card {b : σ // b ≠ t} *
              ((q : K) ^ r • Polynomial.coeff (splitAt t f) r)
            + macOpNum q u (Polynomial.coeff (splitAt t f) r)) := by
  have hd := isTopExtension_subtypeVal ht
  rw [macOpNum_eq_sum_univ q u f, map_sum, Polynomial.finsetSum_coeff,
    Fintype.sum_eq_add_sum_subtype_ne _ t, mul_add,
    macOpNum_eq_sum_univ q u (Polynomial.coeff (splitAt t f) r), Finset.mul_sum]
  congr 1
  · rw [coeff_splitAt_neg_one_pow_mul, hd.card_filter_lt_top, coeff_splitAt_numTerm_top q u hf]
  · refine Finset.sum_congr rfl fun b _ => ?_
    have hsq : ((-1 : MvPolynomial {b : σ // b ≠ t} K)) ^
        ((univ : Finset {b : σ // b ≠ t}).erase b).card * (-1)
          = (-1) ^ Fintype.card {b : σ // b ≠ t} := by
      rw [← pow_succ, Finset.card_erase_add_one (Finset.mem_univ b), Finset.card_univ]
    rw [coeff_splitAt_neg_one_pow_mul, coeff_splitAt_numTerm ht q u b.2 hf,
      hd.card_filter_lt b, ← hsq]
    simp only [Subtype.coe_eta]
    ring_nf
    with_unfolding_all rfl

end Sum

/-! ### Step 3 at `P_μ[X_n]` -/

section Eigen

variable {σ K : Type*} [LinearOrder σ] [Fintype σ] [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}
  {d : ℕ} {t : σ}

/-- **The least letter carries the first row of the diagram**: `λ_1 = \bar\lambda_{i_0}`. The
increasing listing of the alphabet starts at its least letter, so the row of index `0` is the entry
of `\bar\lambda` there. -/
theorem rowLen_partDiagram_zero (μ : PartIdx σ d) {i₀ : σ} (hi₀ : IsBot i₀) :
    (partDiagram σ μ).rowLen 0 = partExp σ μ i₀ := by
  classical
  have hpos : 0 < Fintype.card σ := Fintype.card_pos_iff.2 ⟨i₀⟩
  have h0 : letterEquiv σ ⟨0, hpos⟩ = i₀ := by
    refine le_antisymm ?_ (hi₀ _)
    have hmono := (letterEquiv σ).monotone (show (⟨0, hpos⟩ : Fin (Fintype.card σ))
      ≤ (letterEquiv σ).symm i₀ from Fin.le_def.2 (Nat.zero_le _))
    rwa [OrderIso.apply_symm_apply] at hmono
  rw [rowLen_partDiagram, rowLenSeqOf_of_lt hpos, h0]

/-- **Step 3 of the proof of `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`, as a polynomial
identity.** The numerator of Macdonald's operator in the small alphabet, applied to the coefficient
`g` of `x_t^{λ_1}` in `P_μ[X_n]`, is `𝒱_{N'}` times `E_{n-1}(κ)g`, where `κ` is `μ` with its first
row removed.

`HJO.Mac.coeff_splitAt_macOpNum` reads the left-hand side of `HJO.Mac.vandermondeProd_mul_macOp` and
`Polynomial.coeff_mul_add_eq_of_natDegree_le` the right-hand side; the `(-1)^{n-1}` common to both
cancels, and `HJO.Sym.macdonaldEigenvalue_succ_peel` names what is left of the eigenvalue after the
leftover term `u^{n-1}q^{λ_1}g` is subtracted. -/
theorem macOpNum_coeff_partExp_splitAt_macPpoly (ht : IsTop t)
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : PartIdx σ d) {i₀ : σ} (hi₀ : IsBot i₀) :
    macOpNum q u
        (Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K)) (partExp σ μ i₀))
      = (univ : Finset {b : σ // b ≠ t}).vandermondeProd X *
          (C (HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card {b : σ // b ≠ t})
                (HJO.Sym.shiftRows (partDiagram σ μ))) *
            Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K))
              (partExp σ μ i₀)) := by
  classical
  have hdeg : (splitAt t (macPpoly hqu μ : MvPolynomial σ K)).natDegree ≤ partExp σ μ i₀ :=
    natDegree_splitAt_macPpoly_le hqu μ hi₀ t
  -- the operator identity of `HJO.Mac.vandermondeProd_mul_macOp`, with the denominators cleared
  have hkey : macOpNum q u (macPpoly hqu μ : MvPolynomial σ K)
      = (univ : Finset σ).vandermondeProd X *
        (HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ) •
          (macPpoly hqu μ : MvPolynomial σ K)) := by
    rw [macOpNum_eq_vandermondeProd_mul q u d (macPpoly hqu μ), macOpComp_macPpoly hqu μ]
    rfl
  -- the coefficient of `𝒱_N` at `x_t^{n-1}`
  have hlead := leadingCoeff_splitAt_vandermondeProd_univ (K := K) ht
  rw [Polynomial.leadingCoeff, natDegree_splitAt_vandermondeProd_univ ht] at hlead
  have hR : Polynomial.coeff (splitAt t ((univ : Finset σ).vandermondeProd X *
        (HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ) •
          (macPpoly hqu μ : MvPolynomial σ K))))
        (Fintype.card {b : σ // b ≠ t} + partExp σ μ i₀)
      = ((-1) ^ Fintype.card {b : σ // b ≠ t} *
            (univ : Finset {b : σ // b ≠ t}).vandermondeProd X) *
          (HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ) •
            Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K))
              (partExp σ μ i₀)) := by
    rw [map_mul, map_smul, Polynomial.coeff_mul_add_eq_of_natDegree_le
      (natDegree_splitAt_vandermondeProd_univ ht).le
      ((Polynomial.natDegree_smul_le _ _).trans hdeg), hlead, Polynomial.coeff_smul]
  have hL := coeff_splitAt_macOpNum ht q u hdeg
  rw [hkey, hR, smul_eq_C_mul, smul_eq_C_mul] at hL
  -- the eigenvalue with its first row peeled off
  have hE : HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ)
        - u ^ Fintype.card {b : σ // b ≠ t} * (q : K) ^ partExp σ μ i₀
      = HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card {b : σ // b ≠ t})
          (HJO.Sym.shiftRows (partDiagram σ μ)) := by
    rw [← card_subtype_ne_add_one t, HJO.Sym.macdonaldEigenvalue_succ_peel,
      rowLen_partDiagram_zero μ hi₀]
    ring
  refine mul_left_cancel₀ (a := ((-1 : MvPolynomial {b : σ // b ≠ t} K)) ^
    Fintype.card {b : σ // b ≠ t}) (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) ?_
  rw [← hE, map_sub, map_mul, map_pow]
  linear_combination -hL

/-- **Step 3 of the proof of `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`, as an eigenvector equation
in `𝒮_{n-1,d-λ_1}`.** The coefficient `g` of `x_t^{λ_1}` in `P_μ[X_n]` is an eigenvector of
Macdonald's operator in the small alphabet, with eigenvalue `E_{n-1}(κ)` for `κ` the diagram of `μ`
with its first row removed.

This is `macOpNum_coeff_partExp_splitAt_macPpoly` with `𝒱_{N'}` cancelled, following
`HJO.Mac.killCompl_macOpComp`: `HJO.Mac.vandermondeProd_univ_ne_zero` is what makes the
cancellation legitimate, the polynomial ring over a field being a domain. -/
theorem macOpComp_coeff_partExp_splitAt_macPpoly (ht : IsTop t)
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : PartIdx σ d) {i₀ : σ} (hi₀ : IsBot i₀) :
    macOpComp q u (d - partExp σ μ i₀)
        ⟨Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K)) (partExp σ μ i₀),
          coeff_partExp_splitAt_macPpoly_mem hqu μ i₀ t⟩
      = HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card {b : σ // b ≠ t})
            (HJO.Sym.shiftRows (partDiagram σ μ)) •
          ⟨Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K)) (partExp σ μ i₀),
            coeff_partExp_splitAt_macPpoly_mem hqu μ i₀ t⟩ := by
  refine Subtype.ext (mul_left_cancel₀ (vandermondeProd_univ_ne_zero
    (σ := {b : σ // b ≠ t}) (K := K)) ?_)
  rw [← macOpNum_eq_vandermondeProd_mul, macOpNum_coeff_partExp_splitAt_macPpoly ht hqu μ hi₀]
  exact congrArg _ (smul_eq_C_mul _ _).symm

end Eigen

end HJO.Mac

end
