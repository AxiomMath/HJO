/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.EsymmIndependent
public import HJO.Collinear.MonomialPairing
public meta import HJO.Attr

/-! # Steps 5 and 6: the coefficients of the symmetrised symbol, extracted one at a time

`HJO.Bglx.IsExpPairingSeparating` -- BGLX's equation (2.14) read as a separation property -- is
proved here, unconditionally in the parameters. With it the necessity half of the BGLX vanishing
criterion is complete, and so is the index shift.

What is available going in: the sum of equation (2.14) is finite because the
symmetrised symbol is bounded below in total degree
(`HJO.Bglx.symbolSym_eq_zero_of_coordSum_lt_neg_bound`); its coefficients are *scalars*
(`HJO.Bglx.scalar_symbolSym`); and it is symmetric (`HJO.Bglx.symbolSym_relabelExp`), so a
coefficient depends only on the multiset of coordinates of its exponent. What this file adds is the
independence of the elementary monomials, `HJO.Sym.linearIndependent_elemSymmMonomial`, and with it
the substitution `Φ : p_k ↦ e_k` of `HJO/Collinear/EsymmIndependent.lean`, which is what the
extraction is actually run through.

## The shape of the argument

Fix `l ≥ 1`. Equation (2.14) is a relation

`∑_{γ ∈ ℕ^m} (-1)^{γ₁+⋯+γ_m} e_{γ₁} ⋯ e_{γ_m} (Ξ_c)_{l𝟏-γ} = 0`

in `Λ`. Each `(Ξ_c)_{l𝟏-γ}` is a scalar `a_γ`, and `e_{γ₁} ⋯ e_{γ_m} = Φ(z^{w(γ)})` where `w(γ)` is
the exponent vector `HJO.Sym.wordExp γ`, so the relation reads `Φ(∑_γ b_γ z^{w(γ)}) = 0` with
`b_γ = (-1)^{|γ|}a_γ`. As `Φ` is injective, `∑_γ b_γ z^{w(γ)} = 0` in `Λ`, and the coefficient of
the monomial `z^{w(γ₀)}` gives `∑_{w(γ) = w(γ₀)} b_γ = 0`. Two words with the same exponent vector
are permutations of one another (`HJO.Sym.exists_perm_of_wordExp_eq`), so `b` is constant on that
fibre by the symmetry of `Ξ_c`; the fibre is nonempty and the base has characteristic zero, so
`b_{γ₀} = 0` and hence `(Ξ_c)_{l𝟏-γ₀} = 0`. That is Step 5. Step 6 reaches an arbitrary exponent
`α` by taking `l` larger than every coordinate of `α`, so that `l𝟏 - α ∈ ℕ^m`.

**This is where the Step 5 is repaired, not merely transcribed.** It appeals to the independence of
the `e_λ` as a relation over `Λ`, where independence is false -- `e_2 e_1 - e_1 e_2 = 0` -- and is
correct only because the coefficients of `Ξ_c` lie in the image of `𝕜 → Λ`. That is
`HJO.Bglx.scalar_symbolSym`, which the argument as usually written never states; it is used here at
the step that produces the scalars `a_γ`.

**Grouping by partitions is replaced by extracting one monomial coefficient.** The usual argument
groups the terms of (2.14) by the partition `λ(γ)` and counts the words in each class, producing the
multiplicities `N_λ`. Nothing here needs the value of `N_λ`, only that it is positive: the
coefficient of a single monomial of `Λ` already sums `b` over exactly the fibre of `w`, and the
fibre contains `γ₀`.

## Main statements

* `HJO.Bglx.symbolSym_nsmul_allOnes_sub_natExp_eq_zero`: Step 5.
* `HJO.Bglx.isExpPairingSeparating`: Steps 5 and 6 -- the residual, discharged.
* `HJO.Bglx.isExpPairingSeparating_forall`: the same, quantified over the coefficient field and
  over algebraically independent pairs of parameters.
* `HJO.Bglx.exists_isIndexShift`: the index shift, with no hypothesis beyond the algebraic
  independence of the parameters.
* `HJO.Bglx.criterionNecessary`: the necessity half of the BGLX vanishing criterion.
* `HJO.Bglx.isVanishingCriterion`: the criterion itself, both halves.

## References

The reference for Lemma `HJO.Bglx.criterionNecessary`, Steps 5 and 6 of its proof, and Lemma
`HJO.Sym.linearIndependent_elemSymmMonomial` is F. Bergeron, A. M.
Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the theory of Macdonald
polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, whose equation (2.14) this is, and
whose passage from it to the vanishing of every coefficient is the argument above.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {m : ℕ}

/-! ### Words read as exponents -/

/-- A word `γ ∈ ℕ^m`, read as an exponent in `ℤ^m`. The relations of equation (2.14) are indexed by
exponents, and their nonvanishing terms by words; this is the identification. -/
noncomputable def natExp (γ : Fin m → ℕ) : Fin m →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm fun i => (γ i : ℤ)

@[simp] lemma natExp_apply (γ : Fin m → ℕ) (i : Fin m) : natExp γ i = (γ i : ℤ) := rfl

/-- Distinct words give distinct exponents. -/
lemma natExp_injective : Function.Injective (natExp (m := m)) := fun γ δ h =>
  funext fun i => Int.natCast_inj.1 (by rw [← natExp_apply γ i, ← natExp_apply δ i, h])

/-- A word is a nonnegative exponent. -/
lemma natExp_nonneg (γ : Fin m → ℕ) : 0 ≤ natExp γ :=
  Finsupp.le_def.2 fun i => by simp

/-- The coordinate sum of a word's exponent is the sum of its letters. -/
lemma coordSum_natExp (γ : Fin m → ℕ) : coordSum (natExp γ) = ∑ i : Fin m, (γ i : ℤ) :=
  Finset.sum_congr rfl fun i _ => natExp_apply γ i

/-- Relabelling reads the coordinate at the inverse index. This is the companion of
`HJO.Bglx.relabelExp_symm_apply`, for the relabelling itself rather than its inverse. -/
lemma relabelExp_apply_symm_index (σ : Equiv.Perm (Fin m)) (α : Fin m →₀ ℤ) (i : Fin m) :
    relabelExp σ α i = α (σ.symm i) := by
  have h := relabelExp_apply_perm (τ := σ) (α := α) (σ.symm i)
  rwa [Equiv.apply_symm_apply] at h

/-- Relabelling a word's exponent is the exponent of the relabelled word. -/
lemma relabelExp_natExp (σ : Equiv.Perm (Fin m)) (γ : Fin m → ℕ) :
    relabelExp σ (natExp γ) = natExp (γ ∘ σ.symm) :=
  Finsupp.ext fun i => by rw [relabelExp_apply_symm_index]; rfl

/-- The coordinate sum of the symmetric exponent `l𝟏`. -/
lemma coordSum_nsmul_allOnes (l : ℕ) (m : ℕ) : coordSum (l • allOnes m) = (l : ℤ) * m := by
  rw [coordSum, Finset.sum_congr rfl fun (i : Fin m) _ =>
    show (l • allOnes m) i = (l : ℤ) from by
      rw [Finsupp.smul_apply, allOnes_apply, nsmul_eq_mul, mul_one],
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

/-- **The exponential factor's coefficient at a word**, in explicit form: it is
`(-1)^{γ₁+⋯+γ_m} e_{γ₁} ⋯ e_{γ_m}`. -/
lemma expAlphabetCoeff_natExp (γ : Fin m → ℕ) :
    expAlphabetCoeff L m (natExp γ)
      = (-1 : Lambda L) ^ (∑ i : Fin m, γ i) * ∏ i : Fin m, elemSymm L (γ i) := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [natExp_apply, ite_eq_left (Int.natCast_nonneg (γ i)), Int.toNat_natCast]

/-! ### The symmetry of the symmetrised symbol, read at words -/

/-- **A coefficient of the symmetrised symbol at a shifted word depends only on the word's exponent
vector.** Two words with the same exponent vector are permutations of one another, the exponent
`l𝟏` is fixed by every permutation, and the symmetrised symbol is symmetric. -/
theorem symbolSym_sub_natExp_eq_of_wordExp_eq (q u : L) (c : (Fin m → ℕ) →₀ L) (l : ℕ)
    {γ δ : Fin m → ℕ} (h : wordExp γ = wordExp δ) :
    symbolSym q u m c (l • allOnes m - natExp δ)
      = symbolSym q u m c (l • allOnes m - natExp γ) := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_wordExp_eq h
  have hδ : natExp δ = relabelExp σ.symm (natExp γ) := by
    rw [relabelExp_natExp]
    refine congrArg natExp (funext fun i => ?_)
    rw [hσ i, Equiv.symm_symm]
    rfl
  have hkey : l • allOnes m - natExp δ = relabelExp σ.symm (l • allOnes m - natExp γ) := by
    rw [map_sub, map_nsmul, relabelExp_allOnes, hδ]
  rw [hkey, symbolSym_relabelExp]

/-! ### Step 5: every coefficient at a shifted word vanishes -/

/-- **Step 5 of the proof of `HJO.Bglx.criterionNecessary`.** If the relations of
equation (2.14) hold for every `l ≥ 1`, then `(Ξ_c)_{l𝟏-γ} = 0` for every `l ≥ 1` and every word
`γ ∈ ℕ^m`.

The relation is pushed through the substitution `Φ : p_k ↦ e_k`, which is injective
(`HJO.Sym.elemSymmSub_injective`), turning it into a vanishing relation among monomials of `Λ`; the
coefficient of the monomial of `γ` then sums the scalars over the words with the same exponent
vector, which are the permutations of `γ`, on which the scalar is constant. -/
theorem symbolSym_nsmul_allOnes_sub_natExp_eq_zero (q u : L) (c : (Fin m → ℕ) →₀ L)
    (hsum : ∀ l : ℕ, 1 ≤ l → ∑ᶠ α : Fin m →₀ ℤ,
      expAlphabetCoeff L m α * symbolSym q u m c (l • allOnes m - α) = 0)
    {l : ℕ} (hl : 1 ≤ l) (γ₀ : Fin m → ℕ) :
    symbolSym q u m c (l • allOnes m - natExp γ₀) = 0 := by
  classical
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  set N := max (l * m + wordDegreeBound c) (Finset.univ.sup γ₀) with hN
  set T : Finset (Fin m → ℕ) := Fintype.piFinset fun _ => Finset.range (N + 1) with hT
  have hmemT : ∀ γ : Fin m → ℕ, (∀ i, γ i ≤ N) → γ ∈ T := fun γ hγ =>
    Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (Nat.lt_succ_of_le (hγ i))
  obtain ⟨a, hav⟩ : ∃ a : (Fin m → ℕ) → L, ∀ γ : Fin m → ℕ,
      symbolSym q u m c (l • allOnes m - natExp γ) = MvPolynomial.C (a γ) :=
    ⟨fun γ => (scalar_symbolSym q u m c (l • allOnes m - natExp γ)).choose,
      fun γ => (scalar_symbolSym q u m c (l • allOnes m - natExp γ)).choose_spec⟩
  -- the terms of equation (2.14) are supported on the words of `T`
  have hsupp : Function.support (fun α : Fin m →₀ ℤ =>
      expAlphabetCoeff L m α * symbolSym q u m c (l • allOnes m - α)) ⊆ ↑(T.image natExp) := by
    intro α hα
    rw [Function.mem_support] at hα
    have hnn : 0 ≤ α := by
      by_contra hc
      exact hα (by rw [expAlphabetCoeff_eq_zero_of_not_nonneg hc, zero_mul])
    have hnni : ∀ i : Fin m, 0 ≤ α i := fun i => by simpa using Finsupp.le_def.1 hnn i
    have hcs : coordSum α ≤ ((l * m + wordDegreeBound c : ℕ) : ℤ) := by
      by_contra hc
      rw [not_le] at hc
      refine hα (mul_eq_zero_of_right _
        (symbolSym_eq_zero_of_coordSum_lt_neg_bound q u m c ?_))
      rw [coordSum_sub, coordSum_nsmul_allOnes]
      push_cast at hc
      linarith
    have hαγ : natExp (fun i => (α i).toNat) = α :=
      Finsupp.ext fun i => Int.toNat_of_nonneg (hnni i)
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, hmemT _ fun i => ?_, hαγ⟩)
    have hle : α i ≤ coordSum α :=
      Finset.single_le_sum (f := fun j : Fin m => α j) (fun j _ => hnni j) (Finset.mem_univ i)
    have hN1 : l * m + wordDegreeBound c ≤ N := le_max_left _ _
    omega
  -- equation (2.14) as a finite sum over words
  have hfin := hsum l hl
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image fun _ _ _ _ hxy => natExp_injective hxy] at hfin
  -- each term is the image under `Φ` of a monomial of `Λ`
  have hC : ∀ x : L, elemSymmSub L (MvPolynomial.C x) = MvPolynomial.C x := fun x => by
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
  have hterm : ∀ γ : Fin m → ℕ,
      elemSymmSub L (MvPolynomial.monomial (wordExp γ) ((-1 : L) ^ (∑ i : Fin m, γ i) * a γ))
        = expAlphabetCoeff L m (natExp γ) * symbolSym q u m c (l • allOnes m - natExp γ) := by
    intro γ
    rw [show (MvPolynomial.monomial (wordExp γ) ((-1 : L) ^ (∑ i : Fin m, γ i) * a γ) :
          Lambda L)
        = MvPolynomial.C ((-1 : L) ^ (∑ i : Fin m, γ i) * a γ) *
          MvPolynomial.monomial (wordExp γ) 1 from by
      rw [MvPolynomial.C_mul_monomial, mul_one], map_mul, hC, elemSymmSub_monomial_wordExp,
      expAlphabetCoeff_natExp, hav γ, map_mul, map_pow, map_neg, map_one]
    ring
  -- so the monomials sum to zero, `Φ` being injective
  have hzero : (∑ γ ∈ T,
      MvPolynomial.monomial (wordExp γ) ((-1 : L) ^ (∑ i : Fin m, γ i) * a γ)) = 0 := by
    refine elemSymmSub_injective L ?_
    rw [map_sum, map_zero]
    exact (Finset.sum_congr rfl fun γ _ => hterm γ).trans hfin
  -- extract the coefficient of the monomial of `γ₀`
  have hcoeff := congrArg (MvPolynomial.coeff (wordExp γ₀)) hzero
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero,
    ← Finset.sum_filter_add_sum_filter_not T fun γ => wordExp γ = wordExp γ₀] at hcoeff
  have hγ₀T : γ₀ ∈ T := hmemT γ₀ fun i =>
    le_max_of_le_right (Finset.le_sup (f := γ₀) (Finset.mem_univ i))
  have hγ₀F : γ₀ ∈ T.filter fun γ => wordExp γ = wordExp γ₀ := Finset.mem_filter.2 ⟨hγ₀T, rfl⟩
  -- on the fibre of `γ₀` the coefficient is read off, and the scalar is constant there
  have hfibre : ∀ γ ∈ T.filter fun γ => wordExp γ = wordExp γ₀,
      MvPolynomial.coeff (wordExp γ₀) (MvPolynomial.monomial (wordExp γ)
          ((-1 : L) ^ (∑ i : Fin m, γ i) * a γ))
        = (-1 : L) ^ (∑ i : Fin m, γ₀ i) * a γ₀ := by
    intro γ hγ
    have hw : wordExp γ = wordExp γ₀ := (Finset.mem_filter.1 hγ).2
    obtain ⟨σ, hσ⟩ := exists_perm_of_wordExp_eq hw
    have hsum' : (∑ i : Fin m, γ₀ i) = ∑ i : Fin m, γ i :=
      (Finset.sum_congr rfl fun i _ => hσ i).trans (Equiv.sum_comp σ γ)
    have haa : a γ₀ = a γ := by
      have hs := symbolSym_sub_natExp_eq_of_wordExp_eq q u c l hw
      rw [hav γ₀, hav γ] at hs
      exact MvPolynomial.C_injective ℕ L hs
    rw [MvPolynomial.coeff_monomial, ite_eq_left hw, hsum', haa]
  -- off it the exponent is wrong, so the coefficient vanishes
  have houtside : ∀ γ ∈ T.filter fun γ => ¬ wordExp γ = wordExp γ₀,
      MvPolynomial.coeff (wordExp γ₀) (MvPolynomial.monomial (wordExp γ)
        ((-1 : L) ^ (∑ i : Fin m, γ i) * a γ)) = 0 := fun γ hγ => by
    rw [MvPolynomial.coeff_monomial, ite_eq_right (Finset.mem_filter.1 hγ).2]
  rw [Finset.sum_congr rfl hfibre, Finset.sum_eq_zero houtside, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_eq_zero] at hcoeff
  have hcard : ((T.filter fun γ => wordExp γ = wordExp γ₀).card : L) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hγ₀F)
  have hprod : (-1 : L) ^ (∑ i : Fin m, γ₀ i) * a γ₀ = 0 := hcoeff.resolve_left hcard
  have ha0 : a γ₀ = 0 := by
    rcases mul_eq_zero.1 hprod with hc | hc
    · exact absurd hc (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    · exact hc
  rw [hav γ₀, ha0, map_zero]

/-! ### Step 6: every exponent is reached -/

/-- **The residual of the necessity half is a theorem**, unconditionally in the parameters. Steps 5
and 6 of the proof of `HJO.Bglx.criterionNecessary`: Step 5 gives the vanishing of
`(Ξ_c)_{l𝟏-γ}` for every word `γ`, and Step 6 reaches an arbitrary exponent `α` by taking `l`
larger than every coordinate of `α`, so that `l𝟏 - α` is a word. -/
theorem isExpPairingSeparating (q u : L) : IsExpPairingSeparating q u := by
  intro m c hsum
  refine funext fun α => ?_
  set l := (Finset.univ.sup fun i : Fin m => (α i).toNat) + 1 with hl
  have hα : ∀ i : Fin m, α i ≤ (l : ℤ) := by
    intro i
    have h1 : (α i).toNat ≤ Finset.univ.sup fun j : Fin m => (α j).toNat :=
      Finset.le_sup (f := fun j : Fin m => (α j).toNat) (Finset.mem_univ i)
    have h2 : α i ≤ ((α i).toNat : ℤ) := Int.self_le_toNat _
    omega
  have hkey : l • allOnes m - natExp (fun i => ((l : ℤ) - α i).toNat) = α := by
    refine Finsupp.ext fun i => ?_
    rw [Finsupp.sub_apply, Finsupp.smul_apply, allOnes_apply, nsmul_eq_mul, mul_one, natExp_apply]
    have := hα i
    omega
  change symbolSym q u m c α = 0
  rw [← hkey]
  exact symbolSym_nsmul_allOnes_sub_natExp_eq_zero q u c hsum (Nat.le_add_left 1 _) _

/-- **The residual, quantified over the coefficient field** and over algebraically independent
pairs of parameters. The premise is not used: the separation property holds at every pair of
parameters. -/
theorem isExpPairingSeparating_forall :
    ∀ (L : Type) [Field L] [Algebra ℚ L] (q u : L),
      AlgebraicIndependent ℤ ![q, u] → IsExpPairingSeparating q u :=
  fun _ _ _ q u _ => isExpPairingSeparating q u

/-! ### What the residual was carrying -/

/-- **The necessity half of the BGLX vanishing criterion**, at parameters neither of which is a root
of unity. `HJO.Bglx.criterionNecessary_of_isExpPairingSeparating` with its hypothesis
discharged. -/
@[hjo "lem_bglx_criterion_necessary"]
theorem criterionNecessary (q u : L)
    (hκ : ∀ j : ℕ, 1 ≤ j → paramPleth q u (powerSum L j) ≠ 0) :
    IsVanishingCriterionNecessary q u :=
  criterionNecessary_of_isExpPairingSeparating q u hκ (isExpPairingSeparating q u)

/-- **The BGLX vanishing criterion** (BGLX, Theorem 2.1, equations (2.10) and (2.11)), at
parameters neither of which is a root of unity: a combination `∑_{k ≤ m} V (c k)` of words in the
operators `Dop q u j` acts by zero on the symmetric functions exactly when the symmetrised symbol
of each of its homogeneous parts vanishes. Sufficiency is unconditional and built into
`isVanishingCriterion_of_necessary`; `hκ` is consumed by the necessity half `criterionNecessary`
alone, and is not decoration, the criterion failing over `ℚ` at `q = u = 1`. -/
@[hjo "lem_bglx_vanishing_criterion"]
theorem isVanishingCriterion (q u : L)
    (hκ : ∀ j : ℕ, 1 ≤ j → paramPleth q u (powerSum L j) ≠ 0) :
    IsVanishingCriterion q u :=
  isVanishingCriterion_of_necessary q u (criterionNecessary q u hκ)

/-- **The index shift exists**, at algebraically independent parameters and with no further
hypothesis. `HJO.Bglx.exists_isIndexShift_of_isExpPairingSeparating` with its hypothesis
discharged. -/
theorem exists_isIndexShift (q u : L) (hqu : AlgebraicIndependent ℤ ![q, u]) :
    ∃ S : DopAlgebra q u →ₐ[L] DopAlgebra q u, IsIndexShift q u S :=
  exists_isIndexShift_of_isExpPairingSeparating q u hqu (isExpPairingSeparating q u)

end HJO.Bglx
