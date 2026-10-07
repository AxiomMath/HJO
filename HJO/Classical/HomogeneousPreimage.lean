/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.PmonomialBasis
public meta import HJO.Attr

/-! # A realised homogeneous series comes from a graded piece

`HJO.Sym.mem_lambdaComp_of_coeff_iota`: if every monomial occurring in `ι(f)` has total degree `n`,
then `f` already lies in the graded piece `Λ_n`.

## Main results

* `HJO.Sym.degHom_of_coeff_iota_ne_zero`: the converse direction, which carries the proof — every
  monomial occurring in the realisation of a homogeneous symmetric function of degree `d` has total
  degree `d`.
* `HJO.Sym.mem_lambdaComp_of_coeff_iota`.

## Implementation notes

The "there are finitely many `d` with `f_d ≠ 0`" and its decomposition
`f = ∑_d f_d` are `HJO.Sym.sum_weightedHomogeneousComponent_range`, which sums the graded
components over the finite range cut off by the weighted total degree of `f`; the direct sum
decomposition `HJO.Sym.lambdaComp_isInternal` is not invoked in that form, the finite sum being
what the argument uses.

The "`ι(f_d)` is a `𝕜`-linear combination of monomials of total degree `d`" is
`degHom_of_coeff_iota_ne_zero`. It is proved not from the span description of `Λ_d` but from the
monomial expansion of `f_d` in `Λ = MvPolynomial ℕ 𝕜`: a monomial of `Λ` *is* a power-sum monomial
`p_λ` (`HJO.Sym.pmonomial_partitionOfExp`), and the coefficients of `ι(p_λ)` all sit in total degree
`|λ|` (`HJO.Sym.degHom_of_coeff_iota_pmonomial_ne_zero`). The two spellings of the grading are
matched by `HJO.Sym.degOfExp_eq_weight`.

"Grouping the monomials of an element of `𝒫` by their total degree" needs no separate construction:
the degree-`d` part of `ι(f)` is read off one coefficient at a time, and at an exponent vector of
total degree `d` every summand `ι(f_N)` with `N ≠ d` contributes `0`.

The hypotheses `CharZero` and `NoZeroDivisors` are exactly those of
`HJO.Sym.realisation_injective`, which is the only place either is
spent.

## References

This file formalises `HJO.Sym.mem_lambdaComp_of_coeff_iota`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Sym

variable {K : Type*} [CommRing K] {ι : Lambda K →ₐ[K] AlphabetSeries K}

/-- **A realised homogeneous symmetric function is supported in one total degree.** A monomial of
`Λ_d` is a power-sum monomial `p_λ` with `|λ| = d`, and every monomial occurring in `ι(p_λ)` has
total degree `|λ|`; so the same holds for a `𝕜`-linear combination of them. -/
theorem degHom_of_coeff_iota_ne_zero (hι : IsRealisation ι) {d : ℕ} {g : Lambda K}
    (hg : g ∈ LambdaComp K d) {α : ℕ →₀ ℕ}
    (h : MvPowerSeries.coeff α (ι g) ≠ 0) : degHom α = d := by
  classical
  have hexp : MvPowerSeries.coeff α (ι g) = ∑ e ∈ g.support, MvPolynomial.coeff e g *
      MvPowerSeries.coeff α (ι (MvPolynomial.monomial e (1 : K))) := by
    conv_lhs => rw [MvPolynomial.as_sum g]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [show MvPolynomial.monomial e (MvPolynomial.coeff e g)
        = MvPolynomial.coeff e g • MvPolynomial.monomial e (1 : K) from by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, MvPowerSeries.coeff_smul]
  rw [hexp] at h
  obtain ⟨e, he, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hmon : MvPowerSeries.coeff α (ι (pmonomial K (partitionOfExp (degOfExp e) e))) ≠ 0 := by
    rw [pmonomial_partitionOfExp K (rfl : degOfExp e = degOfExp e)]
    exact right_ne_zero_of_mul hne
  rw [degHom_of_coeff_iota_pmonomial_ne_zero hι _ hmon, degOfExp_eq_weight]
  exact mem_lambdaComp.1 hg (MvPolynomial.mem_support_iff.1 he)

/-- **A realised homogeneous series comes from a graded piece.**
Decompose `f` into its graded components `f_d`. Every monomial of `ι(f_d)` has total degree `d`, so
at an exponent vector of total degree `d` the only summand of `ι(f) = ∑_N ι(f_N)` contributing is
`ι(f_d)`; for `d ≠ n` the hypothesis makes that coefficient of `ι(f)` vanish, so `ι(f_d) = 0` and
`HJO.Sym.realisation_injective` gives `f_d = 0`. Hence `f = f_n ∈ Λ_n`. -/
@[hjo "lem_om_homogeneous_preimage"]
theorem mem_lambdaComp_of_coeff_iota [CharZero K] [NoZeroDivisors K] (hι : IsRealisation ι) {n : ℕ}
    {f : Lambda K} (hf : ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α (ι f) ≠ 0 → degHom α = n) :
    f ∈ LambdaComp K n := by
  classical
  have hsum : ∑ N ∈ Finset.range (weightedTotalDegree (fun i => i + 1) f + 1),
      ι (weightedHomogeneousComponent (fun i => i + 1) N f) = ι f := by
    rw [← map_sum, sum_weightedHomogeneousComponent_range f]
  have hzero : ∀ d : ℕ, d ≠ n → weightedHomogeneousComponent (fun i => i + 1) d f = 0 := by
    intro d hdn
    refine realisation_injective hι ?_
    rw [map_zero]
    by_cases hd : d ∈ Finset.range (weightedTotalDegree (fun i => i + 1) f + 1)
    · refine MvPowerSeries.ext fun α => ?_
      rw [map_zero]
      by_cases hα : degHom α = d
      · have h1 : MvPowerSeries.coeff α (ι f) = 0 :=
          by_contra fun hcon => hdn (hα.symm.trans (hf α hcon))
        have h2 : ∀ N ∈ Finset.range (weightedTotalDegree (fun i => i + 1) f + 1), N ≠ d →
            MvPowerSeries.coeff α (ι (weightedHomogeneousComponent (fun i => i + 1) N f)) = 0 :=
          fun N _ hN => by_contra fun hcon => hN ((degHom_of_coeff_iota_ne_zero hι
            (weightedHomogeneousComponent_mem _ f N) hcon).symm.trans hα)
        rwa [← hsum, map_sum, Finset.sum_eq_single_of_mem d hd h2] at h1
      · exact by_contra fun hcon => hα (degHom_of_coeff_iota_ne_zero hι
          (weightedHomogeneousComponent_mem _ f d) hcon)
    · rw [Finset.mem_range, Nat.lt_succ_iff, Nat.not_le] at hd
      rw [weightedHomogeneousComponent_eq_zero _ f hd, map_zero]
  rw [← sum_weightedHomogeneousComponent_range f]
  by_cases hn : n ∈ Finset.range (weightedTotalDegree (fun i => i + 1) f + 1)
  · rw [Finset.sum_eq_single_of_mem n hn fun N _ hN => hzero N hN]
    exact weightedHomogeneousComponent_mem _ f n
  · rw [Finset.sum_eq_zero fun N hN => hzero N fun h => hn (h ▸ hN)]
    exact zero_mem _

end HJO.Sym
