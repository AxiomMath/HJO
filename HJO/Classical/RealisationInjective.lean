/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import HJO.Classical.IotaPmonomial
public meta import HJO.Attr

/-! # The power sums are algebraically independent, and a realisation is injective

`HJO.Sym.algebraicIndependent_realisation_powerSum` and `HJO.Sym.realisation_injective`.

## Main definitions

* `HJO.Sym.partsOfExp`, `HJO.Sym.degOfExp`, `HJO.Sym.partitionOfExp`: the partition a monomial of
  `Λ` is, read off its exponent vector — `∏_i p_{i+1}^{e_i}` is `p_λ` for the partition `λ` with
  `e_i` parts equal to `i+1`.

## Main statements

* `HJO.Sym.realisation_injective`.
* `HJO.Sym.algebraicIndependent_realisation_powerSum`.

## Implementation notes

The usual argument proves the algebraic independence first, by splitting a polynomial relation into
weight-homogeneous components, and then deduces the injectivity from it. Here the two are *one*
statement: `Λ = MvPolynomial ℕ 𝕜` is the polynomial ring on the power sums, so
`AlgebraicIndependent` of their images is by definition the injectivity of the algebra map they
determine, and `MvPolynomial.aeval_unique` says that map is `ι`. The remark that a
`𝕜`-algebra homomorphism from a polynomial ring is injective exactly when the images of the
variables are algebraically independent is therefore not a step of the proof but the
definition, and no kernel-generation argument is needed.

What is left is the usual degree-splitting argument, in the form: a monomial of `Λ` *is* a
power-sum monomial `p_λ` (`pmonomial_partitionOfExp`), the coefficients of `ι(p_λ)` all sit in total
degree `|λ|` (`degHom_of_coeff_iota_pmonomial_ne_zero`), so the different degrees of a vanishing
`ι(f)` cannot interfere, and inside one degree
`HJO.Sym.linearIndependent_iota_pmonomial` finishes.

`partitionOfExp d e` is total, returning `default` off `degOfExp e = d`; every lemma about it
carries that hypothesis, which is what keeps the `Nat.Partition`-valued map out of dependent types
and lets it be summed over a `Finset`.

## References

This file proves `HJO.Sym.algebraicIndependent_realisation_powerSum` and
`HJO.Sym.realisation_injective`. -/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The partition behind a monomial of `Λ` -/

/-- **The parts of the monomial `∏_i p_{i+1}^{e_i}`**: the multiset with `e_i` copies of `i + 1`. -/
noncomputable def partsOfExp (e : ℕ →₀ ℕ) : Multiset ℕ :=
  e.sum fun i n => Multiset.replicate n (i + 1)

theorem partsOfExp_pos {e : ℕ →₀ ℕ} {x : ℕ} (hx : x ∈ partsOfExp e) : 0 < x := by
  obtain ⟨i, -, hxi⟩ := Multiset.mem_bind.mp hx
  rw [Multiset.eq_of_mem_replicate hxi]
  omega

/-- The weight of a monomial of `Λ`: the sum of its parts, i.e. `∑_i (i+1)e_i`. -/
noncomputable def degOfExp (e : ℕ →₀ ℕ) : ℕ := (partsOfExp e).sum

/-- **The partition a monomial of `Λ` is**, as a total function of the degree and the exponent
vector; off `degOfExp e = d` the value is junk, and every lemma below carries that hypothesis. -/
noncomputable def partitionOfExp (d : ℕ) (e : ℕ →₀ ℕ) : Nat.Partition d :=
  if h : degOfExp e = d then ⟨partsOfExp e, partsOfExp_pos, h⟩ else default

theorem parts_partitionOfExp {d : ℕ} {e : ℕ →₀ ℕ} (h : degOfExp e = d) :
    (partitionOfExp d e).parts = partsOfExp e := by
  rw [partitionOfExp, dite_eq_left h]

/-- **The multiplicity of the part `i + 1` is the exponent of `p_{i+1}`**: this is what makes the
exponent vector recoverable from the multiset of parts. -/
theorem count_partsOfExp (e : ℕ →₀ ℕ) (i : ℕ) : Multiset.count (i + 1) (partsOfExp e) = e i := by
  classical
  rw [partsOfExp, Finsupp.sum, Multiset.count_sum',
    Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi => ?_)]
  · simp
  · simp only [Multiset.count_replicate]
    exact ite_eq_right (by omega)
  · rw [Finsupp.notMem_support_iff.1 hi]
    simp

theorem partsOfExp_injective : Function.Injective partsOfExp := fun e e' h =>
  Finsupp.ext fun i => by rw [← count_partsOfExp e i, ← count_partsOfExp e' i, h]

/-- `partitionOfExp` is injective where it is honest: the multiset of parts determines the exponent
vector, the part `i + 1` occurring `e_i` times. -/
theorem partitionOfExp_injOn {d : ℕ} {e e' : ℕ →₀ ℕ} (h : degOfExp e = d) (h' : degOfExp e' = d)
    (heq : partitionOfExp d e = partitionOfExp d e') : e = e' :=
  partsOfExp_injective (by rw [← parts_partitionOfExp h, ← parts_partitionOfExp h', heq])

/-- Reading a sum of multisets of parts through the power sums turns it into a product. -/
theorem prod_map_powerSum_sum (K : Type*) [CommRing K] (t : Finset ℕ) (m : ℕ → Multiset ℕ) :
    (((∑ i ∈ t, m i).map (powerSum K)).prod) = ∏ i ∈ t, ((m i).map (powerSum K)).prod := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Multiset.map_add, Multiset.prod_add, ih]

/-- **A monomial of `Λ` is a power-sum monomial.** `∏_i p_{i+1}^{e_i} = p_λ` for the partition `λ`
with `e_i` parts equal to `i + 1`. -/
theorem pmonomial_partitionOfExp (K : Type*) [CommRing K] {d : ℕ} {e : ℕ →₀ ℕ}
    (h : degOfExp e = d) :
    pmonomial K (partitionOfExp d e) = MvPolynomial.monomial e (1 : K) := by
  rw [pmonomial, parts_partitionOfExp h, partsOfExp, Finsupp.sum, prod_map_powerSum_sum,
    MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Multiset.map_replicate, Multiset.prod_replicate, powerSum, Nat.add_sub_cancel]

/-! ### Injectivity -/

variable {K : Type*} [CommRing K] {ι : Lambda K →ₐ[K] AlphabetSeries K}

/-- **A realisation is injective.**

Expand `f` in the monomials of `Λ`, which are the power-sum monomials `p_λ`. Every coefficient of
`ι(p_λ)` sits in total degree `|λ|`, so a vanishing `ι(f)` vanishes degree by degree; and inside one
degree the `ι(p_λ)` are linearly independent. -/
@[hjo "lem_cm_realisation_injective"]
theorem realisation_injective [CharZero K] [NoZeroDivisors K] (hι : IsRealisation ι) :
    Function.Injective ι := by
  classical
  rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra hne
  obtain ⟨e₀, he₀⟩ := MvPolynomial.ne_zero_iff.1 hne
  set d := degOfExp e₀ with hd
  -- every coefficient of `ι` of a monomial sits in the weight of that monomial
  have hH : ∀ e α : ℕ →₀ ℕ,
      MvPowerSeries.coeff α (ι (MvPolynomial.monomial e (1 : K))) ≠ 0 → degHom α = degOfExp e := by
    intro e α hα
    rw [← pmonomial_partitionOfExp (d := degOfExp e) K rfl] at hα
    exact degHom_of_coeff_iota_pmonomial_ne_zero hι _ hα
  -- the monomial expansion of `f`, transported by `ι`
  have hexp : ∑ e ∈ f.support,
      MvPolynomial.coeff e f • ι (MvPolynomial.monomial e (1 : K)) = 0 := by
    rw [← hf]
    conv_rhs => rw [MvPolynomial.as_sum f]
    rw [map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  -- the degree-`d` part of that expansion vanishes on its own
  have hFzero : ∑ e ∈ f.support with degOfExp e = d,
      MvPolynomial.coeff e f • ι (MvPolynomial.monomial e (1 : K)) = 0 := by
    refine MvPowerSeries.ext fun α => ?_
    rw [map_sum, map_zero]
    by_cases hα : degHom α = d
    · have hdrop : ∀ e ∈ f.support, e ∉ {e ∈ f.support | degOfExp e = d} →
          MvPowerSeries.coeff α (MvPolynomial.coeff e f •
            ι (MvPolynomial.monomial e (1 : K))) = 0 := by
        intro e he hnot
        rw [mem_filter] at hnot
        rw [MvPowerSeries.coeff_smul]
        refine mul_eq_zero_of_right _ (by_contra fun hcon => hnot ⟨he, ?_⟩)
        rw [← hH e α hcon, hα]
      rw [Finset.sum_subset (filter_subset _ _) hdrop]
      have := congrArg (MvPowerSeries.coeff α) hexp
      rwa [map_sum, map_zero] at this
    · refine Finset.sum_eq_zero fun e he => ?_
      rw [mem_filter] at he
      rw [MvPowerSeries.coeff_smul]
      refine mul_eq_zero_of_right _ (by_contra fun hcon => hα ?_)
      rw [hH e α hcon, he.2]
  -- read it as a combination of the `ι(p_λ)` with `λ` a partition of `d`
  set c : Nat.Partition d → K := fun l =>
    ∑ e ∈ Finset.filter (fun e => partitionOfExp d e = l) {e ∈ f.support | degOfExp e = d},
      MvPolynomial.coeff e f with hc
  have hcomb : ∑ l : Nat.Partition d, c l • ι (pmonomial K l) = 0 := by
    rw [← hFzero]
    rw [← Finset.sum_fiberwise_of_maps_to (t := (univ : Finset (Nat.Partition d)))
      (g := partitionOfExp d) (fun e _ => mem_univ _)
      (fun e => MvPolynomial.coeff e f • ι (MvPolynomial.monomial e (1 : K)))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hc, Finset.sum_smul]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [mem_filter] at he
    rw [← he.2, pmonomial_partitionOfExp K (mem_filter.1 he.1).2]
  have hczero := (Fintype.linearIndependent_iff.1
    (linearIndependent_iota_pmonomial hι d)) c hcomb (partitionOfExp d e₀)
  rw [hc] at hczero
  simp only [Finset.filter_filter] at hczero
  rw [Finset.filter_congr (q := fun e => e = e₀) (fun e he => ?_), Finset.filter_eq' _ e₀,
    ite_eq_left (MvPolynomial.mem_support_iff.2 he₀), Finset.sum_singleton] at hczero
  · exact he₀ hczero
  · refine ⟨fun hcon => partitionOfExp_injOn hcon.1 hd.symm hcon.2, fun hcon => ?_⟩
    rw [hcon]
    exact ⟨hd.symm, rfl⟩

/-- **The power sums `∑_i x_i^r`, `r ≥ 1`, are algebraically
independent.**

`Λ` is the polynomial ring on the power sums, so the algebra map they determine *is* `ι`
(`MvPolynomial.aeval_unique`), and algebraic independence of a family is by definition the
injectivity of that map. -/
@[hjo "lem_power_sums_independent"]
theorem algebraicIndependent_realisation_powerSum [CharZero K] [NoZeroDivisors K]
    (hι : IsRealisation ι) :
    AlgebraicIndependent K fun r : ℕ => ι (powerSum K (r + 1)) := by
  have h : (MvPolynomial.aeval fun r : ℕ => ι (powerSum K (r + 1))
      : Lambda K →ₐ[K] AlphabetSeries K) = ι := by
    conv_rhs => rw [MvPolynomial.aeval_unique ι]
    congr 1
  change Function.Injective ⇑(MvPolynomial.aeval fun r : ℕ => ι (powerSum K (r + 1))
      : Lambda K →ₐ[K] AlphabetSeries K)
  rw [h]
  exact realisation_injective hι

end HJO.Sym
