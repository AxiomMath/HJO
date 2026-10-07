/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.CriterionTopLevel
public import HJO.Collinear.FiniteAlphabet
public import HJO.Collinear.IndexShift
public import HJO.Evaluation.PhiPoly
public meta import HJO.Attr

/-! # Separating the top word length, and the residual of the necessity half

This is where the hypothesis of the necessity half is turned into a family of identities at the
top word length. Combining it with the descent of `HJO/Collinear/CriterionTopLevel.lean`, the
whole of `HJO.Bglx.criterionNecessary` — and with it the unconditional existence of an index shift
— is reduced to a single statement about one coefficient family, recorded here as
`HJO.Bglx.IsTopMonomialSeparating`.

The three steps are:

1. the hypothesis, read through the functional `⟨·⟩_k` of `HJO/Collinear/SymbolCT.lean`, says
   `∑_{k ≤ m} ⟨δ^{(k)}(F)⟩_k = 0` for every symmetric function `F`;
2. the same holds with the displacement `δ^{(k)}` replaced by the reciprocal finite alphabet `ζ_k`,
   by the transport identity `HJO.Bglx.smul_finiteAlphabet_powerSum` carried through an induction on
   `F` that keeps two multipliers;
3. at `F = e_m^{\,l}` with `l ≥ 1` every level `k < m` is silenced, because an alphabet of `k`
   letters has no `e_m`, and the level `m` term is the monomial `z_1^{-l} ⋯ z_m^{-l}`.

## Main definitions

* `HJO.Bglx.IsTopMonomialSeparating`: **the residual** — that the identities Step 3 produces force
  the symmetrised symbol to vanish. This is Steps 4 to 6 of the proof and nothing else.

## Main statements

* `HJO.Bglx.sum_symbolCT_plethShiftMulti_eq_zero`: Step 1.
* `HJO.Bglx.sum_symbolCT_mul_finiteAlphabet_eq_zero`: Step 2, in the form the induction proves.
* `HJO.Bglx.symbolCT_monomial_eq_zero`: Step 3.
* `HJO.Bglx.criterionNecessary_of_isTopMonomialSeparating`: the residual implies the whole of
  necessity, at parameters that are not roots of unity.
* `HJO.Bglx.exists_isIndexShift_of_isTopMonomialSeparating`: and therefore the index shift exists,
  at algebraically independent parameters — the shape the `hshift` hypothesis of
  `HJO.CollinearNarrowed.collinearCommute_of_structures` asks for.

## Implementation notes

**Step 2 is proved with two multipliers carried along.** The statement the induction on `F`
establishes is `∀ a G, ∑_{k ≤ m} ⟨a · δ^{(k)}(G) · ζ_k(F)⟩_k = 0`, with `a` and `G` symmetric
functions. The inductive step `F ↦ F p_j` multiplies by `ζ_k(p_j)`, and the transport identity turns
`κ(p_j) ζ_k(p_j)` into `δ^{(k)}(p_j) - p_j`: the first term is absorbed into `G` and the second into
`a`, so both halves are instances of the induction hypothesis. That is why neither an expansion over
subsets nor any bookkeeping with partitions appears.

**The hypothesis on the parameters is `κ(p_j) ≠ 0` for every `j ≥ 1`** and enters in exactly one
place, the division at the end of that inductive step.
`HJO.Bglx.paramPleth_powerSum_ne_zero_of_algebraicIndependent` supplies it from algebraic
independence, which is the hypothesis carried throughout the library.

## References

The reference for Steps 1, 2, 3 and 7 of the proof of `HJO.Bglx.criterionNecessary` is
F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the
theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, whose
equations (2.13) and (2.14) are Step 2 and the unpacking of Step 3.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {k : ℕ}

/-! ### Step 1: the hypothesis, read through the functional -/

/-- **Step 1**: the hypothesis that a combination of words of lengths at most `m` acts by zero,
read through the functional `⟨·⟩_k` at the displacement. -/
theorem sum_symbolCT_plethShiftMulti_eq_zero (q u : L) (m : ℕ) (c : ∀ k : ℕ, (Fin k → ℕ) →₀ L)
    (hsum : ∑ k ∈ Finset.range (m + 1), dopWordOperator q u k (c k) = 0) (F : Lambda L) :
    ∑ k ∈ Finset.range (m + 1), symbolCT q u k (c k) (plethShiftMulti q u k F) = 0 := by
  have h : ∑ k ∈ Finset.range (m + 1), dopWordOperator q u k (c k) F = 0 := by
    rw [← LinearMap.sum_apply, hsum, LinearMap.zero_apply]
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => (dopWordOperator_eq_symbolCT q u k (c k) F).symm

/-! ### Step 2: the displacement replaced by the finite alphabet -/

omit [Algebra ℚ L] in
/-- The finite alphabet fixes the scalars, being an algebra homomorphism. -/
lemma finiteAlphabet_C (b : L) :
    finiteAlphabet L k (MvPolynomial.C b) = algebraMap L (LaurentLambda L k) b := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

/-- **Step 2**, in the form the induction proves: for every symmetric function `F` and every pair of
multipliers `a` and `G`, the functional of `a · δ^{(k)}(G) · ζ_k(F)` sums to zero over the levels.
Taking `a = G = 1` gives Step 2 itself
(`HJO.Bglx.sum_symbolCT_finiteAlphabet_eq_zero`).

The multipliers are what make the induction go through: the step `F ↦ F p_j` splits, by the
transport identity, into one term absorbing `p_j` into `G` and one absorbing it into `a`. -/
theorem sum_symbolCT_mul_finiteAlphabet_eq_zero (q u : L) (m : ℕ)
    (c : ∀ k : ℕ, (Fin k → ℕ) →₀ L)
    (hκ : ∀ j : ℕ, 1 ≤ j → paramPleth q u (powerSum L j) ≠ 0)
    (hsum : ∑ k ∈ Finset.range (m + 1), dopWordOperator q u k (c k) = 0) :
    ∀ F a G : Lambda L,
      ∑ k ∈ Finset.range (m + 1), symbolCT q u k (c k)
          (laurentLambdaC L k a * plethShiftMulti q u k G * finiteAlphabet L k F) = 0 := by
  intro F
  induction F using MvPolynomial.induction_on with
  | C b =>
    intro a G
    have hterm : ∀ k ∈ Finset.range (m + 1), symbolCT q u k (c k)
        (laurentLambdaC L k a * plethShiftMulti q u k G * finiteAlphabet L k (MvPolynomial.C b))
          = b • (a * symbolCT q u k (c k) (plethShiftMulti q u k G)) := by
      intro k _
      rw [finiteAlphabet_C, show laurentLambdaC L k a * plethShiftMulti q u k G
            * algebraMap L (LaurentLambda L k) b
          = b • (laurentLambdaC L k a * plethShiftMulti q u k G) from by
        rw [Algebra.smul_def]; ring, symbolCT_smul, symbolCT_laurentLambdaC_mul]
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, ← Finset.mul_sum,
      sum_symbolCT_plethShiftMulti_eq_zero q u m c hsum G, mul_zero, smul_zero]
  | add p p' hp hp' =>
    intro a G
    have hterm : ∀ k ∈ Finset.range (m + 1), symbolCT q u k (c k)
        (laurentLambdaC L k a * plethShiftMulti q u k G * finiteAlphabet L k (p + p'))
          = symbolCT q u k (c k)
              (laurentLambdaC L k a * plethShiftMulti q u k G * finiteAlphabet L k p)
            + symbolCT q u k (c k)
              (laurentLambdaC L k a * plethShiftMulti q u k G * finiteAlphabet L k p') := by
      intro k _
      rw [map_add (finiteAlphabet L k), mul_add, symbolCT_add]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hp a G, hp' a G, add_zero]
  | mul_X p n hp =>
    intro a G
    have hj : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have hX : (MvPolynomial.X n : Lambda L) = powerSum L (n + 1) := by
      rw [powerSum, Nat.add_sub_cancel]
    have hterm : ∀ k ∈ Finset.range (m + 1),
        paramPleth q u (powerSum L (n + 1)) • symbolCT q u k (c k)
            (laurentLambdaC L k a * plethShiftMulti q u k G
              * finiteAlphabet L k (p * MvPolynomial.X n))
          = symbolCT q u k (c k) (laurentLambdaC L k a
              * plethShiftMulti q u k (G * powerSum L (n + 1)) * finiteAlphabet L k p)
            - symbolCT q u k (c k) (laurentLambdaC L k (a * powerSum L (n + 1))
              * plethShiftMulti q u k G * finiteAlphabet L k p) := by
      intro k _
      rw [← symbolCT_smul, ← symbolCT_sub]
      congr 1
      rw [hX, map_mul (finiteAlphabet L k), map_mul (plethShiftMulti q u k),
        map_mul (laurentLambdaC L k),
        show laurentLambdaC L k a * plethShiftMulti q u k G
              * (finiteAlphabet L k p * finiteAlphabet L k (powerSum L (n + 1)))
            = (laurentLambdaC L k a * plethShiftMulti q u k G * finiteAlphabet L k p)
              * finiteAlphabet L k (powerSum L (n + 1)) from by ring,
        ← mul_smul_comm, smul_finiteAlphabet_powerSum q u k hj]
      ring
    have hzero : paramPleth q u (powerSum L (n + 1)) •
        ∑ k ∈ Finset.range (m + 1), symbolCT q u k (c k)
          (laurentLambdaC L k a * plethShiftMulti q u k G
            * finiteAlphabet L k (p * MvPolynomial.X n)) = 0 := by
      rw [Finset.smul_sum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
        hp a (G * powerSum L (n + 1)), hp (a * powerSum L (n + 1)) G, sub_zero]
    calc ∑ k ∈ Finset.range (m + 1), symbolCT q u k (c k)
            (laurentLambdaC L k a * plethShiftMulti q u k G
              * finiteAlphabet L k (p * MvPolynomial.X n))
        = (paramPleth q u (powerSum L (n + 1)))⁻¹ • (paramPleth q u (powerSum L (n + 1)) •
            ∑ k ∈ Finset.range (m + 1), symbolCT q u k (c k)
              (laurentLambdaC L k a * plethShiftMulti q u k G
                * finiteAlphabet L k (p * MvPolynomial.X n))) := by
          rw [smul_smul, inv_mul_cancel₀ (hκ (n + 1) hj), one_smul]
      _ = 0 := by rw [hzero, smul_zero]

/-- **Step 2** of the proof: the hypothesis holds with the displacement replaced by the
reciprocal finite alphabet. -/
theorem sum_symbolCT_finiteAlphabet_eq_zero (q u : L) (m : ℕ) (c : ∀ k : ℕ, (Fin k → ℕ) →₀ L)
    (hκ : ∀ j : ℕ, 1 ≤ j → paramPleth q u (powerSum L j) ≠ 0)
    (hsum : ∑ k ∈ Finset.range (m + 1), dopWordOperator q u k (c k) = 0) (F : Lambda L) :
    ∑ k ∈ Finset.range (m + 1), symbolCT q u k (c k) (finiteAlphabet L k F) = 0 := by
  have h := sum_symbolCT_mul_finiteAlphabet_eq_zero q u m c hκ hsum F 1 1
  rw [Finset.sum_congr rfl fun k _ => congrArg (symbolCT q u k (c k))
    (show laurentLambdaC L k 1 * plethShiftMulti q u k 1 * finiteAlphabet L k F
        = finiteAlphabet L k F from by rw [map_one, map_one, one_mul, one_mul])] at h
  exact h

/-! ### Step 3: the top word length isolated -/

omit [Algebra ℚ L] in
/-- The monomial `z_1^{-l} z_2^{-l} ⋯ z_k^{-l}`, the `l`-th power of `z_1^{-1} ⋯ z_k^{-1}`. -/
lemma single_neg_allOnes_pow (k l : ℕ) :
    (AddMonoidAlgebra.single (-allOnes k) (1 : Lambda L)) ^ l
      = AddMonoidAlgebra.single (-(l • allOnes k)) 1 := by
  rw [AddMonoidAlgebra.single_pow, one_pow, smul_neg]

/-- **Step 3** of the proof: at the top word length the functional vanishes on every
monomial `z_1^{-l} ⋯ z_m^{-l}` with `l ≥ 1`. The finite alphabet of `k < m` letters kills `e_m`, so
every lower level of Step 2's identity is silenced at `F = e_m^{\,l}`, and the level `m` term is
that monomial. -/
theorem symbolCT_monomial_eq_zero (q u : L) (m : ℕ) (c : ∀ k : ℕ, (Fin k → ℕ) →₀ L)
    (hκ : ∀ j : ℕ, 1 ≤ j → paramPleth q u (powerSum L j) ≠ 0)
    (hsum : ∑ k ∈ Finset.range (m + 1), dopWordOperator q u k (c k) = 0) {l : ℕ} (hl : 1 ≤ l) :
    symbolCT q u m (c m) (AddMonoidAlgebra.single (-(l • allOnes m)) 1) = 0 := by
  have h := sum_symbolCT_finiteAlphabet_eq_zero q u m c hκ hsum (elemSymm L m ^ l)
  have hother : ∀ k ∈ Finset.range (m + 1), k ≠ m →
      symbolCT q u k (c k) (finiteAlphabet L k (elemSymm L m ^ l)) = 0 := by
    intro k hk hkm
    rw [Finset.mem_range] at hk
    rw [map_pow, finiteAlphabet_elemSymm_eq_zero (by omega), zero_pow (by omega), symbolCT_zero]
  rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.2 (Nat.lt_succ_self m)) hother] at h
  rwa [map_pow, finiteAlphabet_elemSymm_self, single_neg_allOnes_pow] at h

/-! ### The residual of the necessity half -/

/-- **The residual of the necessity half**: that the identities of Step 3 force the symmetrised
symbol to vanish. This is Steps 4 to 6 of the proof of `HJO.Bglx.criterionNecessary`
and nothing else; everything above and the descent of
`HJO.Bglx.criterionNecessary_of_topSymbolSymVanishing` is proved.

Unwinding the functional, the hypothesis says that for every `l ≥ 1`
`∑_{γ ∈ ℕ^m} (-1)^{γ₁+⋯+γ_m} e_{γ₁} ⋯ e_{γ_m} (Ξ_c)_{l𝟏-γ} = 0`, which is BGLX's equation
(2.14); what remains is to read off each coefficient, using that `Ξ_c` is symmetric
(`HJO.Bglx.relabel_symbolSym`), that its support is bounded below in total degree
(`HJO.Bglx.symbolSym_eq_zero_of_coordSum_lt`), and that the elementary monomials `e_λ` are linearly
independent. -/
def IsTopMonomialSeparating (q u : L) : Prop :=
  ∀ (m : ℕ) (c : (Fin m → ℕ) →₀ L),
    (∀ l : ℕ, 1 ≤ l → symbolCT q u m c (AddMonoidAlgebra.single (-(l • allOnes m)) 1) = 0) →
      symbolSym q u m c = 0

/-- **The residual gives the top-level case of necessity**, which is Steps 1 to 3 above. -/
theorem isTopSymbolSymVanishing_of_isTopMonomialSeparating (q u : L)
    (hκ : ∀ j : ℕ, 1 ≤ j → paramPleth q u (powerSum L j) ≠ 0)
    (h : IsTopMonomialSeparating q u) : IsTopSymbolSymVanishing q u :=
  fun m c hsum => h m (c m) fun _l hl => symbolCT_monomial_eq_zero q u m c hκ hsum hl

/-- **The residual gives the whole of the necessity half**, by Steps 1 to 3 above and the descent
of Step 7. -/
theorem criterionNecessary_of_isTopMonomialSeparating (q u : L)
    (hκ : ∀ j : ℕ, 1 ≤ j → paramPleth q u (powerSum L j) ≠ 0)
    (h : IsTopMonomialSeparating q u) : IsVanishingCriterionNecessary q u :=
  criterionNecessary_of_topSymbolSymVanishing q u
    (isTopSymbolSymVanishing_of_isTopMonomialSeparating q u hκ h)

/-! ### The genericity the hypothesis needs -/

/-- An algebraically independent parameter is not a root of unity: a positive power of the first
variable is not `1`, as one sees at `(0, 0)`. -/
theorem pow_ne_one_left_of_algebraicIndependent {R : Type*} [CommRing R] {q u : R}
    (hqu : AlgebraicIndependent ℤ ![q, u]) {j : ℕ} (hj : 1 ≤ j) : q ^ j ≠ 1 := fun h => by
  have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) ^ j = 1 :=
    PhiPoly.eq_of_aeval_eq hqu (by simp [h])
  have h1 := congrArg (MvPolynomial.aeval ![(0 : ℤ), 0]) h0
  rw [map_pow, map_one, MvPolynomial.aeval_X,
    show (![(0 : ℤ), 0] : Fin 2 → ℤ) 0 = 0 from rfl, zero_pow (by omega)] at h1
  exact zero_ne_one h1

/-- The same for the second parameter. -/
theorem pow_ne_one_right_of_algebraicIndependent {R : Type*} [CommRing R] {q u : R}
    (hqu : AlgebraicIndependent ℤ ![q, u]) {j : ℕ} (hj : 1 ≤ j) : u ^ j ≠ 1 := fun h => by
  have h0 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ) ^ j = 1 :=
    PhiPoly.eq_of_aeval_eq hqu (by simp [h])
  have h1 := congrArg (MvPolynomial.aeval ![(0 : ℤ), 0]) h0
  rw [map_pow, map_one, MvPolynomial.aeval_X,
    show (![(0 : ℤ), 0] : Fin 2 → ℤ) 1 = 0 from rfl, zero_pow (by omega)] at h1
  exact zero_ne_one h1

omit [Algebra ℚ L] in
/-- **Algebraic independence supplies the one hypothesis on the parameters that necessity needs**:
`κ(p_j) = (1 - q^j)(1 - u^j)` is nonzero for every `j ≥ 1`, neither parameter being a root of
unity. -/
theorem paramPleth_powerSum_ne_zero_of_algebraicIndependent {q u : L}
    (hqu : AlgebraicIndependent ℤ ![q, u]) {j : ℕ} (hj : 1 ≤ j) :
    paramPleth q u (powerSum L j) ≠ 0 := by
  rw [paramPleth_powerSum q u hj]
  exact mul_ne_zero
    (sub_ne_zero_of_ne (Ne.symm (pow_ne_one_left_of_algebraicIndependent hqu hj)))
    (sub_ne_zero_of_ne (Ne.symm (pow_ne_one_right_of_algebraicIndependent hqu hj)))

/-- **The index shift exists as soon as the residual does**, at algebraically independent
parameters. This is the shape the `hshift` hypothesis of
`HJO.CollinearNarrowed.collinearCommute_of_structures` asks for, conditional on
`HJO.Bglx.IsTopMonomialSeparating` and on nothing else. -/
theorem exists_isIndexShift_of_isTopMonomialSeparating (q u : L)
    (hqu : AlgebraicIndependent ℤ ![q, u]) (h : IsTopMonomialSeparating q u) :
    ∃ S : DopAlgebra q u →ₐ[L] DopAlgebra q u, IsIndexShift q u S :=
  exists_isIndexShift (raiseStableKernel_of_criterionNecessary q u
    (criterionNecessary_of_isTopMonomialSeparating q u
      (fun _j hj => paramPleth_powerSum_ne_zero_of_algebraicIndependent hqu hj) h))

end HJO.Bglx
