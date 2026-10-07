/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitLhsSlopeCompatN
public import HJO.Macdonald.DualityFacts
public import HJO.Shuffle.MellitTwoPartTwoThreeValue
public import HJO.CarlssonMellit.DpaStructure

/-! # Mellit's operator `∇'`, and the hypothesis `IsNOperator`

In Mellit's proof that conjugation by `∇` realises the shear `N = (1 1; 0 1)` (§3.7), the algebra
endomorphism `N` of `Ã` fixing `d_-`, `d_+^*`, the loops and the idempotents and sending
`d_+ ↦ c·z_1d_+` preserves the left ideal `𝓘` of the structure theorem `Ã𝟏_0/𝓘 ≅ V_*`, and so
induces an operator `∇'` on `V_* = ⨁_k V_k` with `∇'L = N(L)∇'`. This file does two things with it.

**The single-operator form is inconsistent.** `HJO.Sweep.IsNOperator` asks for one endomorphism
`𝒩'` of the total space restricting to `∇` on `V_0` and commuting with `d_-, d_+^*` out of `V_1`
and `V_2`. But the pieces `V_0 ⊆ V_1 ⊆ V_2` are nested in the total space, so a constant `f ∈ Λ` is
met both as a vector of `V_0` and as a vector of `V_1`. At `f = 1`, fixed by `d_+^*`, this forces
`∇1` to be fixed by the shift of the alphabet by the letter `(q-1)uy_1`, hence to be a constant;
for general `f` it forces `∇` to commute with `d_-` out of `V_1` on the constants, which is
`D_0` at `u = 0`. In degree two the conjugator clauses fix `∇` up to the constant `∇1`, and
commuting with `D_0|_{u=0}` at `e_1^2` then fails by `c M u (q-1) ≠ 0`. So no Macdonald conjugator
carries such an operator once `q` is not a root of unity and `u ∉ {0, 1}`; in particular
`HJO.Sweep.lhsSlope_add_left` has unsatisfiable hypotheses there.

**The repaired form holds, given the bar.** Mellit's `∇'` acts on each summand of the direct sum
separately. `HJO.Sweep.IsNOperatorOnPieces` asks for exactly that — `∇` on `V_0`, `𝒩'_1` on `V_1`,
`𝒩'_2` on `V_2`, each clause read between the pieces its arrow joins — and still carries the
clause of `HJO.Mellit.lhsRewrite_sweepWitness`'s base case along `N`. Through
`HJO.Sweep.dpaStructure` and `HJO.Dyck.Tilde.Atilde.conjTwist` the operator `∇'` is constructed, its
restrictions satisfy the repaired hypothesis over `∇ := ∇'|_{V_0}`, and `∇` fixes `1`, commutes with
`D_0` and turns `e_1·` into `-D_1`. Those three properties determine an endomorphism of `Λ`: both
clauses carry `D_k` to `Q_{k+1,k}`, and the vectors `D_{k_1}⋯D_{k_r}(1)` span `Λ`, by a
triangularity in the elementary basis ordered by the largest part. So `∇'|_{V_0}` is the Macdonald
conjugator normalised by `∇1 = 1` whenever that exists — Mellit's `∇' = ∇`, reached without the
characteristic functions and the conjugation operator of Carlsson–Mellit that his proof uses.

## Main definitions

* `HJO.Sweep.letterShift`: the shift `p_{j+1} ↦ p_{j+1} + a_jy_{i+1}^{j+1}` of the alphabet.
* `HJO.Sweep.IsNOperatorOnPieces`: an operator realising `N` on `V_0, V_1, V_2` separately.
* `HJO.Sym.IsSlopeConjugator`: the clauses of a Macdonald conjugator the slope recursion reads.
* `HJO.Sym.dopOrbit`: the span of the vectors `D_{k_1}⋯D_{k_r}(1)`.
* `HJO.Sweep.nvPiece`, `HJO.Sweep.nvTotal`, `HJO.Sweep.nvZero`: an endomorphism of `V_*` read on a
  summand, on the total space through the retraction onto a piece, and on `Λ`.

## Main results

* `HJO.Sweep.eq_C_of_letterShift_eq_C`: a symmetric function fixed by a one-letter shift of its
  alphabet is a constant.
* `HJO.Sweep.IsNOperator.nabla_one_eq_C`, `HJO.Sweep.IsNOperator.nabla_dop_q_zero`: what the nested
  pieces force on `∇`.
* `HJO.Sweep.IsMacdonaldConjugator.false_of_comm_dop_q_zero`: no Macdonald conjugator with `∇1 ∈ 𝕜`
  commutes with `D_0|_{u=0}`.
* `HJO.Sweep.not_exists_isNOperator`, `HJO.Sweep.not_exists_isNOperator_of_algebraicIndependent`:
  `HJO.Sweep.IsNOperator` cannot be met over a Macdonald conjugator.
* `HJO.Sweep.lhsSlope_of_coprime_of_isNOperatorOnPieces`: the clause at every positive coprime
  slope, given a slope conjugator and an operator realising `N` piece by piece.
* `HJO.Sym.dopOrbit_eq_top`: the basic operators reach all of `Λ` from `1`.
* `HJO.Sym.eq_of_slope_clauses`: commuting with `D_0`, turning `e_1·` into `-D_1` and the value at
  `1` determine an endomorphism of `Λ`.
* `HJO.Sweep.exists_intertwiner`: an endomorphism of `Ã` preserving `𝓘` induces an intertwiner of
  `V_*`.
* `HJO.Dyck.Tilde.Atilde.conjTwist_mem_mellitKernel`: Mellit's `N` preserves `𝓘`.
* `HJO.Sweep.exists_isNOperatorOnPieces_of_bar`: Mellit's `∇'` exists and realises `N` piece by
  piece.
* `HJO.Sweep.exists_isMacdonaldConjugator_isNOperatorOnPieces_of_bar`: over the normalised
  Macdonald conjugator, given that it exists.
* `HJO.Sweep.lhsSlope_of_coprime_of_bar`: the clause at every positive coprime slope, given the
  bar and the normalised Macdonald conjugator.

## Implementation notes

The scalar at `d_+` is `(qu)^{-1}`, not Mellit's `-(qt)^{-1}`: Mellit's `∇` carries the sign
`(-1)^{|λ|}` that `HJO.Sym.IsMacdonaldConjugator` does not, and the construction of `N` leaves the
scalar free. With it `N(y_1) = (qu)^{-1}z_1y_1` and `N(d_+) = -y_1d_+^*` out of `V_0`.

The structure theorem and the existence of `N` are proved under the hypotheses of
`HJO.Sym.paramInvLambda`, a ring involution of the base inverting `q` and `u`, and so is everything
built on them here.

The group structure of `V_*` is supplied as a local instance: instance search does not find it
through the summands in this file.

## References

* [A. Mellit, *Toric braids and (m,n)-parking functions*][mellit2016], §3.4 and §3.7.
* E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
  661--697, Theorem 7.2.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

variable {L : Type*} [Field L]

/-! ### A symmetric function fixed by a shift of its alphabet is a constant -/

section ShiftFixed

/-- The shift `p_{j+1} ↦ p_{j+1} + a_j y_i^{j+1}` of the alphabet by the letter `y_{i+1}`, from
`Λ` into the total space. -/
noncomputable def letterShift (a : ℕ → L) (i : ℕ) : Sym.Lambda L →ₐ[L] Total L :=
  aeval fun j => (C (X j) : Total L) + scal (a j) * X i ^ (j + 1)

/-- The shift by the letters `y_1, …, y_N` at once. -/
noncomputable def letterShiftSum (a : ℕ → L) (N : ℕ) : Sym.Lambda L →ₐ[L] Total L :=
  aeval fun j => (C (X j) : Total L) + scal (a j) * ∑ i ∈ Finset.range N, X i ^ (j + 1)

/-- Renaming the letters by `σ` carries the shift by `y_{i+1}` to the shift by `y_{σ i+1}`. -/
theorem rename_letterShift (a : ℕ → L) (σ : ℕ → ℕ) (i : ℕ) (g : Sym.Lambda L) :
    rename σ (letterShift a i g) = letterShift a (σ i) g := by
  have h : ((rename σ : Total L →ₐ[Sym.Lambda L] Total L).restrictScalars L).comp
      (letterShift a i) = letterShift a (σ i) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp [letterShift, scal]
  exact congrArg (fun φ : Sym.Lambda L →ₐ[L] Total L => φ g) h

/-- If `g` is fixed by the shift by `y_1`, then it is fixed by the shift by every letter. -/
theorem letterShift_eq_C_of_eq_C (a : ℕ → L) {g : Sym.Lambda L}
    (h : letterShift a 0 g = C g) (i : ℕ) : letterShift a i g = C g := by
  have := congrArg (rename (fun n => if n = 0 then i else n)) h
  rwa [rename_letterShift, rename_C, ite_eq_left rfl] at this

/-- If `g` is fixed by the shift by `y_1`, then it is fixed by the shift by `y_1, …, y_N`. -/
theorem letterShiftSum_eq_C_of_eq_C (a : ℕ → L) {g : Sym.Lambda L}
    (h : letterShift a 0 g = C g) (N : ℕ) : letterShiftSum a N g = C g := by
  induction N with
  | zero =>
    have : letterShiftSum a 0 = IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L) := by
      refine MvPolynomial.algHom_ext fun j => ?_
      simp [letterShiftSum]
    rw [this]; rfl
  | succ N ih =>
    set T : Total L →ₐ[L] Total L := aevalTower (letterShift a N) X with hT
    have hcomp : T.comp (letterShiftSum a N) = letterShiftSum a (N + 1) := by
      refine MvPolynomial.algHom_ext fun j => ?_
      simp only [AlgHom.comp_apply, letterShiftSum, aeval_X, map_add, map_mul, map_sum,
        map_pow, hT, aevalTower_C, aevalTower_X, Finset.sum_range_succ]
      simp [letterShift, scal]
      ring
    rw [← hcomp, AlgHom.comp_apply, ih, hT, aevalTower_C, letterShift_eq_C_of_eq_C a h N]

/-- Evaluation of the total space at the empty alphabet, with the letters `y_1, …, y_N` sent to
the variables of a finite alphabet and the later letters to `0`. -/
noncomputable def evalLetters (N : ℕ) : Total L →ₐ[L] MvPolynomial (Fin N) L :=
  aevalTower (aeval fun _ => (0 : MvPolynomial (Fin N) L))
    fun i => if h : i < N then X ⟨i, h⟩ else 0

/-- On a constant `g` of the total space, the evaluation is the constant term of `g`. -/
theorem evalLetters_C (N : ℕ) (g : Sym.Lambda L) :
    evalLetters N (C g : Total L) = C (constantCoeff g) := by
  rw [evalLetters, aevalTower_C]
  exact aeval_zero g

/-- Shifting by `y_1, …, y_N` and then evaluating is the diagonal scaling `p_{j+1} ↦ a_j p_{j+1}`
followed by restriction to the alphabet `Fin N`. -/
theorem evalLetters_comp_letterShiftSum (a : ℕ → L) (N : ℕ) :
    (evalLetters N).comp (letterShiftSum a N)
      = (Sym.restrictAlphabet (Fin N) L).comp (Sym.diagScale a) := by
  refine MvPolynomial.algHom_ext fun j => ?_
  have hsum : ∑ i ∈ Finset.range N,
      (if h : i < N then (X ⟨i, h⟩ : MvPolynomial (Fin N) L) else 0) ^ (j + 1)
      = ∑ i : Fin N, (X i : MvPolynomial (Fin N) L) ^ (j + 1) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (if h : i < N then
      (X ⟨i, h⟩ : MvPolynomial (Fin N) L) else 0) ^ (j + 1))]
    exact Finset.sum_congr rfl fun i _ => by rw [dite_eq_left_of_eq_true (eq_true i.2)]
  simp only [AlgHom.comp_apply, letterShiftSum, aeval_X, map_add, map_mul, map_sum, map_pow,
    evalLetters, aevalTower_C, aevalTower_X, Sym.diagScale, scal]
  rw [hsum]
  simp [Sym.restrictAlphabet, MvPolynomial.psum]

theorem eq_zero_of_forall_restrictAlphabet_eq_zero [Algebra ℚ L] {f : Sym.Lambda L}
    (h : ∀ N : ℕ, Sym.restrictAlphabet (Fin N) L f = 0) : f = 0 := by
  rw [← Sym.sum_weightedHomogeneousComponent_range f]
  refine Finset.sum_eq_zero fun d _ => ?_
  have hb := (Sym.restrictAlphabetComp_bijective (Fin d) L (d := d) (by simp)).1
  have hmem : weightedHomogeneousComponent (fun i => i + 1) d f ∈ Sym.LambdaComp L d :=
    weightedHomogeneousComponent_mem _ f d
  have h0 : Sym.restrictAlphabetComp (Fin d) L d ⟨_, hmem⟩ = 0 := by
    apply Subtype.ext
    rw [Sym.coe_restrictAlphabetComp, ← Sym.restrictAlphabet_homogeneousComponent, h d,
      map_zero]
    rfl
  have := hb (h0.trans (map_zero _).symm)
  simpa using congrArg Subtype.val this

/-- **A symmetric function fixed by a shift of its alphabet by one letter is a constant**: if
`g[X + ∑_j a_j y^{j+1}] = g` with every `a_j ≠ 0`, then `g ∈ 𝕜`. Shifting by the letters
`y_1, …, y_N` in turn and then emptying the alphabet, `g` restricted to `N` letters and rescaled by
`a` is the constant `g(0)`; restriction is injective in degree `≤ N`, and so is the rescaling. -/
theorem eq_C_of_letterShift_eq_C [Algebra ℚ L] {a : ℕ → L} (ha : ∀ j, a j ≠ 0) {g : Sym.Lambda L}
    (h : letterShift a 0 g = C g) : g = C (constantCoeff g) := by
  have key : ∀ N, Sym.restrictAlphabet (Fin N) L (Sym.diagScale a (g - C (constantCoeff g)))
      = 0 := by
    intro N
    have h1 := congrArg (evalLetters N) (letterShiftSum_eq_C_of_eq_C a h N)
    rw [← AlgHom.comp_apply, evalLetters_comp_letterShiftSum, evalLetters_C,
      AlgHom.comp_apply] at h1
    rw [map_sub, map_sub, h1, Sym.diagScale_C, MvPolynomial.algHom_C, algebraMap_eq, sub_self]
  have := eq_zero_of_forall_restrictAlphabet_eq_zero key
  rw [← map_zero (Sym.diagScale a)] at this
  exact sub_eq_zero.1 (Sym.diagScale_injective ha this)

end ShiftFixed

/-! ### Values of the operators of `Λ` in degree two -/

section DegreeTwo

variable [Algebra ℚ L]

theorem dopStar_apply_one (q u : L) (k : ℕ) :
    Sym.DopStar q u k (1 : Sym.Lambda L) = Sym.completeHomog L k := by
  rw [Sym.dopStar_apply, map_one, ← Polynomial.monomial_zero_one, Sym.coeffPairing_monomial,
    one_mul, add_zero]

/-- The modified lowering operator out of `V_1`, on a constant: `d_-(f) = D_0(f)|_{u = 0}`. -/
theorem dminus_one_C (q : L) (f : Sym.Lambda L) :
    dminus q 1 (C f : Total L) = C (Sym.Dop q 0 0 f) := by
  have h := dminus_auxVar_pow_mul_C q 0 0 f
  rw [Sym.bop_natCast, pow_zero, one_mul] at h
  exact h

end DegreeTwo

/-! ### The hypothesis `IsNOperator` is inconsistent -/

section Refutation

variable [Algebra ℚ L] {q u : L} {nabla : Module.End L (Sym.Lambda L)}
  {Nt : Module.End L (Total L)}

omit [Algebra ℚ L] in
/-- `d^*_+` out of `V_0`, on a constant, is the shift of the alphabet by the letter `(q-1)uy_1`. -/
theorem dplusStar_zero_C_eq_letterShift (q u : L) (g : Sym.Lambda L) :
    dplusStar q u 0 (C g) = letterShift (fun j => (q ^ (j + 1) - 1) * u ^ (j + 1)) 0 g := by
  have h : ((cycleShift u 0).restrictScalars L).comp
      ((qshift q 1).comp (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L)))
      = letterShift (fun j => (q ^ (j + 1) - 1) * u ^ (j + 1)) 0 := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp [letterShift, qshift, cycleShift, scal, auxVar]
    ring
  exact congrArg (fun φ : Sym.Lambda L →ₐ[L] Total L => φ g) h

/-- **An operator realising `N` forces `∇1` to be a constant.** The constant `1 ∈ V_0` is fixed by
`d^*_+`, so `𝒩'` sends it both to `C(∇1)` and to `d^*_+C(∇1)`, the shift of `∇1` by the letter
`(q-1)uy_1`; a symmetric function fixed by that shift is a constant. -/
theorem IsNOperator.nabla_one_eq_C (hN : IsNOperator q u nabla Nt) (hu : u ≠ 0)
    (hq : ∀ k : ℕ, 1 ≤ k → q ^ k ≠ 1) :
    nabla 1 = C (constantCoeff (nabla 1)) := by
  refine eq_C_of_letterShift_eq_C (a := fun j => (q ^ (j + 1) - 1) * u ^ (j + 1))
    (fun j => mul_ne_zero (sub_ne_zero.2 (hq _ (by omega))) (pow_ne_zero _ hu)) ?_
  rw [← dplusStar_zero_C_eq_letterShift]
  have h := hN.map_dplusStar 0 (by omega) (C 1) (C_mem_piece_zero 1)
  have h1 : dplusStar q u 0 (C (1 : Sym.Lambda L)) = C 1 := by
    rw [dplusStar_apply, map_one, map_one, map_one]
  rw [h1, hN.map_C] at h
  exact h.symm

/-- **An operator realising `N` forces `∇` to commute with `D_0|_{u=0}`.** A constant of `V_0` is
also a vector of `V_1`, where `𝒩'` must commute with `d_-`; and `d_-` out of `V_1` acts on the
constants as `D_0` at `u = 0` (`HJO.Sweep.dminus_one_C`). -/
theorem IsNOperator.nabla_dop_q_zero (hN : IsNOperator q u nabla Nt) (g : Sym.Lambda L) :
    nabla (Sym.Dop q 0 0 g) = Sym.Dop q 0 0 (nabla g) := by
  apply MvPolynomial.C_injective ℕ (Sym.Lambda L)
  have h := hN.map_dminus 0 (by omega) _ (piece_mono (by omega) (C_mem_piece_zero g))
  rw [zero_add, dminus_one_C, hN.map_C, hN.map_C, dminus_one_C] at h
  exact h

/-- **No Macdonald conjugator with `∇1 ∈ 𝕜` commutes with `D_0|_{u=0}`.** In degree two the
conjugator clauses fix `∇` up to the scalar `c = ∇1`: `∇(e_1^2) = c(e_1^2 - Me_2)` from
`∇(e_1·) = -D_1∇`, and `∇(e_1^2 - M̃h_2) = ce_1^2` from `∇D^*_1 = e_1∇`. Commuting `∇` with
`D_0|_{u=0}` at `e_1^2` and reading the coefficient of `p_2` then forces `cMu(q-1) = 0`. -/
theorem IsMacdonaldConjugator.false_of_comm_dop_q_zero (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) (hu1 : u ≠ 1) (hnab : Sym.IsMacdonaldConjugator q u nabla)
    (hA : ∀ g, nabla (Sym.Dop q 0 0 g) = Sym.Dop q 0 0 (nabla g)) {c : L}
    (hc : nabla 1 = C c) : False := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h := hnab.bijective.1 (hc.trans (by rw [map_zero, ← map_zero nabla]))
    exact one_ne_zero h
  have hc1 : (C c : Sym.Lambda L) = c • 1 := by rw [MvPolynomial.smul_eq_C_mul, mul_one]
  have hDu : ∀ k, Sym.Dop q u k (1 : Sym.Lambda L) = (-1) ^ k * Sym.elemSymm L k :=
    Sym.dop_apply_one q u
  have hD0 : ∀ k, Sym.Dop q 0 k (1 : Sym.Lambda L) = (-1) ^ k * Sym.elemSymm L k :=
    Sym.dop_apply_one q 0
  -- `∇e_1 = c e_1`
  have n1 : nabla (Sym.elemSymm L 1) = c • Sym.elemSymm L 1 := by
    have h := hnab.map_elemSymm_one_mul 1
    rw [mul_one, hc, hc1, map_smul, hDu 1] at h
    rw [h]; simp
  -- `∇(e_1^2) = c(e_1^2 - Me_2)`
  have n2 : nabla (Sym.elemSymm L 1 * Sym.elemSymm L 1)
      = c • (Sym.elemSymm L 1 * Sym.elemSymm L 1 - ((1 - q) * (1 - u)) • Sym.elemSymm L 2) := by
    have h := hnab.map_elemSymm_one_mul (Sym.elemSymm L 1)
    have hd := Sym.dop_elemSymm_one_mul q u 1 1
    rw [mul_one] at hd
    rw [n1, map_smul, hd, hDu 1, hDu 2] at h
    rw [h]; simp only [smul_eq_C_mul]; ring
  -- `∇(e_1^2 - M̃h_2) = c e_1^2`
  have n3 : nabla (Sym.elemSymm L 1 * Sym.elemSymm L 1
      - Sym.paramProduct q⁻¹ u⁻¹ • Sym.completeHomog L 2)
      = c • (Sym.elemSymm L 1 * Sym.elemSymm L 1) := by
    have h := hnab.map_dopStar_one (Sym.elemSymm L 1)
    have hd := Sym.dopStar_elemSymm_one_mul q u 1 1
    rw [mul_one] at hd
    have hh1 : Sym.completeHomog L 1 = Sym.elemSymm L 1 := by
      rw [HJO.CopPower.completeHomog_one, Sym.elemSymm_one_eq_X]; rfl
    rw [hd, dopStar_apply_one, dopStar_apply_one, hh1, n1] at h
    rw [h, mul_smul_comm]
  -- `D_0|_{u=0}` in degree two
  have A1 : Sym.Dop q 0 0 (Sym.elemSymm L 1 * Sym.elemSymm L 1)
      = (2 * q - 1) • (Sym.elemSymm L 1 * Sym.elemSymm L 1) + (1 - q) ^ 2 • Sym.elemSymm L 2 := by
    have h1 := Sym.dop_elemSymm_one_mul q 0 0 (Sym.elemSymm L 1)
    have h2 := Sym.dop_elemSymm_one_mul q 0 0 1
    have h3 := Sym.dop_elemSymm_one_mul q 0 1 1
    rw [mul_one] at h2 h3
    rw [h1, h2, h3, hD0 0, hD0 1, hD0 2]
    simp only [smul_eq_C_mul, Sym.elemSymm_zero_eq_one]
    simp only [map_sub, map_mul, map_one, map_ofNat, map_pow, sub_zero, mul_one]
    ring
  have A2 : Sym.Dop q 0 0 (Sym.elemSymm L 2)
      = (1 - q + q ^ 2) • Sym.elemSymm L 2 - (1 - q) • (Sym.elemSymm L 1 * Sym.elemSymm L 1) := by
    have h := Sym.bop_elemSymm_two_mul (L := L) q 0 1
    simp only [Sym.bop_natCast, mul_one] at h
    rw [h, hD0 0, hD0 1, hD0 2]
    simp only [smul_eq_C_mul, Sym.elemSymm_zero_eq_one]
    simp only [map_sub, map_mul, map_one, map_neg, map_add, map_pow]
    ring
  -- the commutation at `e_1^2`
  have E := hA (Sym.elemSymm L 1 * Sym.elemSymm L 1)
  rw [A1, map_add, map_smul, map_smul, n2, map_smul, map_sub, map_smul, A1, A2] at E
  -- `M̃∇e_2 = M̃∇(e_1^2) - ∇(e_1^2) + ce_1^2`, from `h_2 = e_1^2 - e_2`
  have hh2 : Sym.completeHomog L 2 = Sym.elemSymm L 1 * Sym.elemSymm L 1 - Sym.elemSymm L 2 := by
    rw [eq_sub_iff_add_eq, Sym.completeHomog_two_add_elemSymm_two, sq]
  have hN2 : Sym.paramProduct q⁻¹ u⁻¹ • nabla (Sym.elemSymm L 2)
      = Sym.paramProduct q⁻¹ u⁻¹ • nabla (Sym.elemSymm L 1 * Sym.elemSymm L 1)
        - nabla (Sym.elemSymm L 1 * Sym.elemSymm L 1)
        + c • (Sym.elemSymm L 1 * Sym.elemSymm L 1) := by
    rw [hh2, map_sub, map_smul, map_sub] at n3
    rw [← n3]; module
  rw [n2] at hN2
  -- read off the coefficient of `p_2`
  set φ : Sym.Lambda L →ₐ[L] L := aeval fun i => if i = 1 then 1 else 0 with hφ
  have φe1 : φ (Sym.elemSymm L 1) = 0 := by rw [Sym.elemSymm_one_eq_X, hφ, aeval_X]; simp
  have φe2 : φ (Sym.elemSymm L 2) = -(2 : L)⁻¹ := by
    rw [Sym.elemSymm_two_eq, hφ]
    simp [map_ofNat]
  have E' := congrArg φ E
  have hN2' := congrArg φ hN2
  simp only [map_add, map_sub, map_smul, map_mul, smul_eq_mul, φe1, φe2] at E' hN2'
  set x := φ (nabla (Sym.elemSymm L 2))
  have h2q : (1 - q) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 (Ne.symm hq1))
  have hx : x = c / 2 * (-1 + (1 - u) * (2 - q)) := by
    apply mul_left_cancel₀ h2q
    linear_combination E'
  have hMtq : Sym.paramProduct q⁻¹ u⁻¹ * (q * u) = (1 - q) * (1 - u) := by
    rw [Sym.paramProduct]; field_simp; ring
  have key : c * ((1 - q) * (1 - u)) * u * (q - 1) = 0 := by
    rw [hx] at hN2'
    linear_combination (norm := (field_simp; ring)) (2 * q * u) * hN2'
      - (c * (1 - q - 2 * u + q * u) - c * ((1 - q) * (1 - u))) * hMtq
  have hM0 : (1 - q) * (1 - u) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.2 (Ne.symm hq1)) (sub_ne_zero.2 (Ne.symm hu1))
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc0 hM0) hu0) (sub_ne_zero.2 hq1) key

/-- **`HJO.Sweep.IsNOperator` cannot be met over a Macdonald conjugator**, under the
nondegeneracy hypotheses `(1 - q^k)(1 - u^k) ≠ 0`, `q ≠ 0`, `u ≠ 0`. The graded pieces
`V_0 ⊆ V_1 ⊆ V_2` are nested inside the one total space, so a single operator `𝒩'` meets the
clauses of `IsNOperator` at a constant `f ∈ Λ` both as a vector of `V_0` and as a vector of `V_1`.
Read at `1`, this forces `∇1 ∈ 𝕜` (`HJO.Sweep.IsNOperator.nabla_one_eq_C`); read at `f`, it forces
`∇` to commute with `d_-` out of `V_1`, which acts on constants as `D_0|_{u=0}`
(`HJO.Sweep.IsNOperator.nabla_dop_q_zero`); and no Macdonald conjugator does both
(`HJO.Sweep.IsMacdonaldConjugator.false_of_comm_dop_q_zero`). -/
theorem not_exists_isNOperator (hM : ∀ k : ℕ, 1 ≤ k → (1 - q ^ k) * (1 - u ^ k) ≠ 0)
    (hq0 : q ≠ 0) (hu0 : u ≠ 0) :
    ¬ ∃ (nabla : Module.End L (Sym.Lambda L)) (Nt : Module.End L (Total L)),
      Sym.IsMacdonaldConjugator q u nabla ∧ IsNOperator q u nabla Nt := by
  rintro ⟨nabla, Nt, hnab, hN⟩
  have hq : ∀ k : ℕ, 1 ≤ k → q ^ k ≠ 1 := fun k hk h =>
    hM k hk (by rw [h, sub_self, zero_mul])
  have hu1 : u ≠ 1 := fun h => hM 1 le_rfl (by rw [h, one_pow, sub_self, mul_zero])
  exact IsMacdonaldConjugator.false_of_comm_dop_q_zero hq0 hu0
    (by simpa using hq 1 le_rfl) hu1 hnab hN.nabla_dop_q_zero (hN.nabla_one_eq_C hu0 hq)

omit [Algebra ℚ L] in
/-- Algebraically independent parameters are nondegenerate in the sense of
`HJO.Sweep.not_exists_isNOperator`: no positive power of either is `1`, and neither is `0`. -/
theorem nondegenerate_of_algebraicIndependent (hqu : AlgebraicIndependent ℤ ![q, u]) :
    (∀ k : ℕ, 1 ≤ k → (1 - q ^ k) * (1 - u ^ k) ≠ 0) ∧ q ≠ 0 ∧ u ≠ 0 := by
  refine ⟨fun k hk => mul_ne_zero (fun h => ?_) (fun h => ?_), fun h => ?_, fun h => ?_⟩
  · have h0 : (X 0 ^ k : MvPolynomial (Fin 2) ℤ) = 1 :=
      PhiPoly.eq_of_aeval_eq hqu (by simp [(sub_eq_zero.1 h).symm])
    have h1 := congrArg (aeval ![(0 : ℤ), 0]) h0
    simp [zero_pow (by omega : k ≠ 0)] at h1
  · have h0 : (X 1 ^ k : MvPolynomial (Fin 2) ℤ) = 1 :=
      PhiPoly.eq_of_aeval_eq hqu (by simp [(sub_eq_zero.1 h).symm])
    have h1 := congrArg (aeval ![(0 : ℤ), 0]) h0
    simp [zero_pow (by omega : k ≠ 0)] at h1
  · have h0 : (X 0 : MvPolynomial (Fin 2) ℤ) = 0 := PhiPoly.eq_of_aeval_eq hqu (by simp [h])
    have h1 := congrArg (aeval ![(1 : ℤ), 1]) h0
    simp at h1
  · have h0 : (X 1 : MvPolynomial (Fin 2) ℤ) = 0 := PhiPoly.eq_of_aeval_eq hqu (by simp [h])
    have h1 := congrArg (aeval ![(1 : ℤ), 1]) h0
    simp at h1

/-- `HJO.Sweep.not_exists_isNOperator` at algebraically independent parameters, the standing
genericity of `HJO.Mellit.lhsRewrite_sweepWitness`. -/
theorem not_exists_isNOperator_of_algebraicIndependent (hqu : AlgebraicIndependent ℤ ![q, u]) :
    ¬ ∃ (nabla : Module.End L (Sym.Lambda L)) (Nt : Module.End L (Total L)),
      Sym.IsMacdonaldConjugator q u nabla ∧ IsNOperator q u nabla Nt :=
  let h := nondegenerate_of_algebraicIndependent hqu
  not_exists_isNOperator h.1 h.2.1 h.2.2

end Refutation

end HJO.Sweep

/-! ### The two clauses of a Macdonald conjugator that the slope recursion reads -/

namespace HJO.Sym

section SlopeConjugator

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {nabla : Module.End L (Lambda L)}

/-- **A slope conjugator**: a bijective `∇` commuting with `D_0` and turning multiplication by
`e_1` into `-D_1`. -/
structure IsSlopeConjugator (q u : L) (nabla : Module.End L (Lambda L)) : Prop where
  /-- `∇` is bijective. -/
  bijective : Function.Bijective nabla
  /-- `∇(D_0 f) = D_0(∇ f)`. -/
  map_dop_zero : ∀ f : Lambda L, nabla (Dop q u 0 f) = Dop q u 0 (nabla f)
  /-- `∇(e_1 f) = -D_1(∇ f)`. -/
  map_elemSymm_one_mul : ∀ f : Lambda L, nabla (elemSymm L 1 * f) = -Dop q u 1 (nabla f)

/-- A Macdonald conjugator is a slope conjugator. -/
theorem IsMacdonaldConjugator.isSlopeConjugator (h : IsMacdonaldConjugator q u nabla) :
    IsSlopeConjugator q u nabla :=
  ⟨h.bijective, h.map_dop_zero, h.map_elemSymm_one_mul⟩

/-- `HJO.Sym.qop_succ_apply_nabla` for any `∇` meeting the two clauses of a slope conjugator,
bijective or not: `Q_{k+1,k}(∇f) = ∇(D_kf)`. -/
theorem qop_succ_apply_of_clauses
    (h0 : ∀ f : Lambda L, nabla (Dop q u 0 f) = Dop q u 0 (nabla f))
    (h1 : ∀ f : Lambda L, nabla (elemSymm L 1 * f) = -Dop q u 1 (nabla f))
    (hM : (1 - q) * (1 - u) ≠ 0) :
    ∀ (k : ℕ) (f : Lambda L), Qop q u (k + 1) k (nabla f) = nabla (Dop q u k f) := by
  have hcancel : ∀ X Y : Lambda L, -X - -(X + Y) = Y := fun X Y => by abel
  have hd1 : ∀ f, Dop q u 1 (nabla f) = -nabla (elemSymm L 1 * f) := fun f => by
    rw [h1 f, neg_neg]
  intro k
  induction k with
  | zero =>
    intro f
    rw [qop_one]
    exact (h0 f).symm
  | succ k ih =>
    intro f
    have hsucc : k + 1 - 1 = k := by omega
    have hq := LinearMap.congr_fun (qop_upper_rec q u (show 1 ≤ k + 1 by omega)) (nabla f)
    rw [hsucc] at hq
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] at hq
    rw [hq, ih f, hd1 (Dop q u k f), hd1 f, map_neg,
      ih (elemSymm L 1 * f), dop_elemSymm_one_mul q u k f, map_add, map_smul, hcancel,
      smul_smul, inv_mul_cancel₀ hM, one_smul]

/-- `HJO.Sym.qop_succ_apply_nabla` for a slope conjugator. -/
theorem IsSlopeConjugator.qop_succ_apply (h : IsSlopeConjugator q u nabla)
    (hM : (1 - q) * (1 - u) ≠ 0) :
    ∀ (k : ℕ) (f : Lambda L), Qop q u (k + 1) k (nabla f) = nabla (Dop q u k f) :=
  qop_succ_apply_of_clauses h.map_dop_zero h.map_elemSymm_one_mul hM

/-- `HJO.Sym.qop_add_apply_nabla` for a slope conjugator; the proof reads only its clauses. -/
theorem IsSlopeConjugator.qop_add_apply (h : IsSlopeConjugator q u nabla)
    (hM : (1 - q) * (1 - u) ≠ 0) :
    ∀ m : ℕ, 0 < m → ∀ n : ℕ, 0 < n → ∀ f : Lambda L,
      Qop q u (m + n) n (nabla f) = nabla (Qop q u m n f) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm n hn f
    rcases Nat.lt_or_ge m 2 with h1 | h1
    · have hm1 : m = 1 := by omega
      subst hm1
      rw [qop_one, Nat.add_comm 1 n]
      exact h.qop_succ_apply hM n f
    · have hm1 : 1 < m := by omega
      obtain ⟨hr1, hrm⟩ := one_le_slopeSplit_fst_lt hm1 hn
      have he := one_le_sub_slopeSplit_snd hm1 hn
      have hsn : (slopeSplit m n).2 < n := by omega
      have hc : ∀ g : Lambda L,
          Qop q u (m - (slopeSplit m n).1 + (n - (slopeSplit m n).2))
              (n - (slopeSplit m n).2) (nabla g) =
            nabla (Qop q u (m - (slopeSplit m n).1) (n - (slopeSplit m n).2) g) :=
        ih _ (by omega) (by omega) _ (by omega)
      have hr : ∀ g : Lambda L,
          Qop q u ((slopeSplit m n).1 + (slopeSplit m n).2) (slopeSplit m n).2 (nabla g) =
            nabla (Qop q u (slopeSplit m n).1 (slopeSplit m n).2 g) := by
        rcases Nat.eq_zero_or_pos (slopeSplit m n).2 with hs | hs
        · intro g
          rw [hs, slopeSplit_fst_eq_one hm1 hn hs, Nat.add_zero, qop_one]
          exact (h.map_dop_zero g).symm
        · exact ih _ hrm hr1 _ hs
      have hidx : m + n - ((slopeSplit m n).1 + (slopeSplit m n).2) =
          m - (slopeSplit m n).1 + (n - (slopeSplit m n).2) := by omega
      have hq := LinearMap.congr_fun
        (qop_rec q u (show 1 < m + n by omega) hn) (nabla f)
      rw [slopeSplit_up (by omega) hn] at hq
      dsimp only at hq
      rw [hidx] at hq
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] at hq
      have hf := LinearMap.congr_fun (qop_rec q u hm1 hn) f
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] at hf
      rw [hq, hr f, hc f, hc _, hr _, hf, map_smul, map_sub]

end SlopeConjugator

/-! ### `Λ` is reached from `1` by the basic operators -/

section DopOrbit

variable {L : Type*} [Field L] [Algebra ℚ L] (q u : L)

/-- The span of the vectors `D_{k_1}⋯D_{k_r}(1)` reached from `1` by the basic operators. -/
noncomputable def dopOrbit : Submodule L (Lambda L) :=
  Submodule.span L (Set.range fun w : List ℕ => (w.map (Dop q u)).prod (1 : Lambda L))

/-- `1` lies in the orbit span. -/
theorem one_mem_dopOrbit : (1 : Lambda L) ∈ dopOrbit q u :=
  Submodule.subset_span ⟨[], by simp⟩

/-- The orbit span is stable under every `D_k`. -/
theorem dop_mem_dopOrbit (k : ℕ) {f : Lambda L} (hf : f ∈ dopOrbit q u) :
    Dop q u k f ∈ dopOrbit q u := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨k :: w, by simp [Module.End.mul_apply]⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

omit [Algebra ℚ L] in
/-- The constant term of the displacement is the identity. -/
theorem coeff_zero_plethShift (f : Lambda L) : (plethShift q u f).coeff 0 = f := by
  have h : ((Polynomial.aeval (0 : Lambda L)).restrictScalars L).comp (plethShift q u)
      = AlgHom.id L (Lambda L) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [plethShift, powerSum]
  have := congrArg (fun φ : Lambda L →ₐ[L] Lambda L => φ f) h
  simpa [Polynomial.coeff_zero_eq_aeval_zero] using this

/-- The span of the elementary monomials `e_ν` with every part at most `k` and `|ν| = d`. -/
noncomputable def eMonSpan (k d : ℕ) : Submodule L (Lambda L) :=
  Submodule.span L {f | ∃ ν : Multiset ℕ, (∀ x ∈ ν, x ≤ k) ∧ ν.sum = d ∧
    f = elemSymmMonomial L ν}

/-- For `a ≤ k`, multiplication by `e_a` maps the degree-`d` span into the degree-`a + d` span. -/
theorem elemSymm_mul_mem_eMonSpan {k a d : ℕ} (ha : a ≤ k) {f : Lambda L}
    (hf : f ∈ eMonSpan (L := L) k d) : elemSymm L a * f ∈ eMonSpan (L := L) k (a + d) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ν, hν, hsum, rfl⟩ := hx
    refine Submodule.subset_span ⟨a ::ₘ ν, fun x hx => ?_, by rw [Multiset.sum_cons, hsum],
      (elemSymmMonomial_cons L a ν).symm⟩
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact ha
    · exact hν x hx
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-- The span of elementary monomials is stable under multiplication by constants. -/
theorem C_mul_mem_eMonSpan {k d : ℕ} (c : L) {f : Lambda L} (hf : f ∈ eMonSpan (L := L) k d) :
    MvPolynomial.C c * f ∈ eMonSpan (L := L) k d := by
  rw [← MvPolynomial.smul_eq_C_mul]; exact Submodule.smul_mem _ c hf

/-- **The coefficients of the displacement of an elementary monomial.** For `ν` with parts at most
`k`, the coefficient of `w^j` in `e_ν[X + M/z]` lies in the span of the elementary monomials with
parts at most `k` and degree `|ν| - j`, and vanishes for `j > |ν|`. -/
theorem coeff_plethShift_elemSymmMonomial (k : ℕ) :
    ∀ m : Multiset ℕ, (∀ x ∈ m, x ≤ k) → ∀ j : ℕ,
      (plethShift q u (elemSymmMonomial L m)).coeff j ∈ eMonSpan (L := L) k (m.sum - j)
        ∧ (m.sum < j → (plethShift q u (elemSymmMonomial L m)).coeff j = 0) := by
  intro m
  induction m using Multiset.induction_on with
  | empty =>
    intro _ j
    rw [elemSymmMonomial_zero, map_one, Polynomial.coeff_one]
    split_ifs with hj
    · subst hj
      exact ⟨Submodule.subset_span ⟨0, by simp, by simp, by simp⟩, fun h => by simp at h⟩
    · exact ⟨zero_mem _, fun _ => rfl⟩
  | cons a m ih =>
    intro hm j
    have hak : a ≤ k := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ x ∈ m, x ≤ k := fun x hx => hm x (Multiset.mem_cons_of_mem hx)
    rw [elemSymmMonomial_cons, map_mul, Polynomial.coeff_mul, Multiset.sum_cons]
    constructor
    · refine Submodule.sum_mem _ fun x hx => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [Bglx.coeff_plethShift_elemSymm q u a x.1]
      split_ifs with h1
      · by_cases h2 : x.2 ≤ m.sum
        · have := elemSymm_mul_mem_eMonSpan (L := L) (le_trans (Nat.sub_le a x.1) hak)
            (C_mul_mem_eMonSpan (Bglx.paramPleth q u (elemSymm L x.1)) (ih hm' x.2).1)
          rw [show a - x.1 + (m.sum - x.2) = a + m.sum - j from by omega] at this
          convert this using 1
          ring
        · rw [(ih hm' x.2).2 (by omega), mul_zero]; exact zero_mem _
      · rw [zero_mul]; exact zero_mem _
    · intro hj
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [Bglx.coeff_plethShift_elemSymm q u a x.1]
      split_ifs with h1
      · rw [(ih hm' x.2).2 (by omega), mul_zero]
      · rw [zero_mul]

/-- **Every elementary monomial is reached from `1` by the basic operators.** Induction on the
degree, and inside it downward on the largest part `k`:
`D_k(e_ν) = (-1)^ke_ke_ν + ∑_{j ≥ 1} e_{k+j}·(…)`, where the corrections are elementary monomials
of the same degree with largest part `k + j > k`. -/
theorem elemSymmMonomial_mem_dopOrbit : ∀ m : Multiset ℕ, elemSymmMonomial L m ∈ dopOrbit q u := by
  intro m
  induction hd : m.sum using Nat.strong_induction_on generalizing m with
  | _ d ihd =>
    -- downward induction on the largest part
    have key : ∀ n k : ℕ, d + 1 - k ≤ n → ∀ m : Multiset ℕ, m.sum = d → (∃ x ∈ m, k ≤ x) →
        elemSymmMonomial L m ∈ dopOrbit q u := by
      intro n
      induction n with
      | zero =>
        intro k hk m hm ⟨x, hx, hkx⟩
        have := Multiset.le_sum_of_mem hx
        omega
      | succ n ihn =>
        intro k hk m hm ⟨x, hx, hkx⟩
        by_cases hbig : ∃ y ∈ m, k + 1 ≤ y
        · exact ihn (k + 1) (by omega) m hm hbig
        push Not at hbig
        have hxk : x = k := by have := hbig x hx; omega
        subst hxk
        obtain ⟨m', rfl⟩ : ∃ m', m = x ::ₘ m' := ⟨m.erase x, (Multiset.cons_erase hx).symm⟩
        have hm' : ∀ y ∈ m', y ≤ x := fun y hy => by
          have := hbig y (Multiset.mem_cons_of_mem hy); omega
        rw [Multiset.sum_cons] at hm
        rcases Nat.eq_zero_or_pos x with hx0 | hx0
        · -- every part is zero
          have hall : ∀ y ∈ x ::ₘ m', y = 0 := fun y hy => by
            rcases Multiset.mem_cons.1 hy with rfl | hy
            · exact hx0
            · have := hm' y hy; omega
          have h1 : elemSymmMonomial L (x ::ₘ m') = 1 := by
            refine Multiset.prod_eq_one fun y hy => ?_
            obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
            rw [hall z hz, elemSymm_zero_eq_one]
          rw [h1]; exact one_mem_dopOrbit q u
        have hlow : elemSymmMonomial L m' ∈ dopOrbit q u := ihd m'.sum (by omega) m' rfl
        have hD := dop_mem_dopOrbit q u x hlow
        have hcoeff := coeff_plethShift_elemSymmMonomial q u x m' hm'
        rw [dop_apply, coeffPairing_eq_sum_range _ _ (N := m'.sum + 1)
          (fun j hj => (hcoeff j).2 (by omega)), Finset.sum_range_succ',
          coeff_zero_plethShift] at hD
        have hcorr : ∑ j ∈ Finset.range m'.sum,
            (plethShift q u (elemSymmMonomial L m')).coeff (j + 1) *
              ((-1) ^ (x + (j + 1)) * elemSymm L (x + (j + 1))) ∈ dopOrbit q u := by
          refine Submodule.sum_mem _ fun j hj => ?_
          rw [Finset.mem_range] at hj
          suffices H : ∀ g ∈ eMonSpan (L := L) x (m'.sum - (j + 1)),
              g * ((-1) ^ (x + (j + 1)) * elemSymm L (x + (j + 1))) ∈ dopOrbit q u from
            H _ (hcoeff (j + 1)).1
          intro g hg
          induction hg using Submodule.span_induction with
          | mem f hf =>
            obtain ⟨ν, hν, hsum, rfl⟩ := hf
            have hK : elemSymmMonomial L ((x + (j + 1)) ::ₘ ν) ∈ dopOrbit q u :=
              ihn (x + 1) (by omega) _ (by rw [Multiset.sum_cons]; omega)
                ⟨x + (j + 1), Multiset.mem_cons_self _ _, by omega⟩
            have he : elemSymmMonomial L ν * ((-1) ^ (x + (j + 1)) * elemSymm L (x + (j + 1)))
                = ((-1 : L) ^ (x + (j + 1))) • elemSymmMonomial L ((x + (j + 1)) ::ₘ ν) := by
              rw [elemSymmMonomial_cons, Algebra.smul_def, map_pow, map_neg, map_one]; ring
            rw [he]; exact Submodule.smul_mem _ _ hK
          | zero => rw [zero_mul]; exact zero_mem _
          | add f g _ _ hf hg => rw [add_mul]; exact add_mem hf hg
          | smul c f _ hf => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hf
        have hmain : (-1 : L) ^ x • (elemSymm L x * elemSymmMonomial L m') ∈ dopOrbit q u := by
          have := sub_mem hD hcorr
          rw [add_sub_cancel_left] at this
          convert this using 1
          rw [Algebra.smul_def, map_pow, map_neg, map_one]
          simp only [add_zero]
          ring
        have := Submodule.smul_mem _ ((-1 : L) ^ x) hmain
        rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul,
          ← elemSymmMonomial_cons] at this
        exact this
    rcases Multiset.empty_or_exists_mem m with rfl | ⟨x, hx⟩
    · rw [elemSymmMonomial_zero]; exact one_mem_dopOrbit q u
    · exact key (d + 1) 0 (by omega) m hd ⟨x, hx, Nat.zero_le x⟩

/-- **`Λ` is reached from `1` by the basic operators**: the vectors `D_{k_1}⋯D_{k_r}(1)` span. -/
theorem dopOrbit_eq_top : dopOrbit q u = (⊤ : Submodule L (Lambda L)) := by
  refine eq_top_iff.2 fun f _ => ?_
  rw [← sum_weightedHomogeneousComponent_range f]
  refine Submodule.sum_mem _ fun d _ => ?_
  obtain ⟨B, hB⟩ := exists_basis_lambdaComp_elemSymmMonomial L d
  have hmem : MvPolynomial.weightedHomogeneousComponent (fun i => i + 1) d f ∈ LambdaComp L d :=
    MvPolynomial.weightedHomogeneousComponent_mem _ f d
  have hspan := B.mem_span (⟨_, hmem⟩ : LambdaComp L d)
  have hle : Submodule.span L (Set.range B) ≤ (dopOrbit q u).comap (LambdaComp L d).subtype := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨μ, rfl⟩
    change (B μ : Lambda L) ∈ dopOrbit q u
    rw [hB]
    exact elemSymmMonomial_mem_dopOrbit q u μ.parts
  exact hle hspan

/-- **The two clauses and the value at `1` determine `∇`.** Two endomorphisms of `Λ` commuting
with `D_0`, turning `e_1·` into `-D_1` and agreeing at `1` agree on every `D_{k_1}⋯D_{k_r}(1)`,
since both carry `D_k` to `Q_{k+1,k}` (`HJO.Sym.qop_succ_apply_of_clauses`); and those vectors
span `Λ` (`HJO.Sym.dopOrbit_eq_top`). -/
theorem eq_of_slope_clauses {nabla nabla' : Module.End L (Lambda L)}
    (h0 : ∀ f : Lambda L, nabla (Dop q u 0 f) = Dop q u 0 (nabla f))
    (h1 : ∀ f : Lambda L, nabla (elemSymm L 1 * f) = -Dop q u 1 (nabla f))
    (h0' : ∀ f : Lambda L, nabla' (Dop q u 0 f) = Dop q u 0 (nabla' f))
    (h1' : ∀ f : Lambda L, nabla' (elemSymm L 1 * f) = -Dop q u 1 (nabla' f))
    (hone : nabla 1 = nabla' 1) (hM : (1 - q) * (1 - u) ≠ 0) : nabla = nabla' := by
  have hw : ∀ w : List ℕ,
      nabla ((w.map (Dop q u)).prod 1) = nabla' ((w.map (Dop q u)).prod 1) := by
    intro w
    induction w with
    | nil => simpa using hone
    | cons k w ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [← qop_succ_apply_of_clauses h0 h1 hM, ih, qop_succ_apply_of_clauses h0' h1' hM]
  refine LinearMap.ext fun f => ?_
  have hf : f ∈ dopOrbit q u := by rw [dopOrbit_eq_top]; trivial
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨w, rfl⟩ := hx; exact hw w
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, map_smul, hx]

end DopOrbit

end HJO.Sym

namespace HJO.Sweep

open MvPolynomial

variable {L : Type*} [Field L]

/-! ### The repaired hypothesis: one operator per graded piece -/

section Pieces

variable [Algebra ℚ L] {q u : L}

open Mellit (SlopeLetter)

omit [Algebra ℚ L] in
/-- A vector of `V_0` is a constant. -/
theorem exists_C_eq_of_mem_piece_zero {G : Total L} (hG : G ∈ piece L 0) :
    ∃ g : Sym.Lambda L, C g = G := by
  rw [piece, show (Set.Iio 0 : Set ℕ) = ∅ from
      Set.eq_empty_of_forall_notMem fun _ h => Nat.not_lt_zero _ h,
    MvPolynomial.supported_empty, Algebra.mem_bot] at hG
  obtain ⟨g, hg⟩ := hG
  exact ⟨g, by rw [← hg, MvPolynomial.algebraMap_eq]⟩

/-- **An operator realising Mellit's `N` on `V_0`, `V_1`, `V_2` separately**, over a given `∇`:
`∇` on `V_0`, `𝒩'_1` on `V_1` and `𝒩'_2` on `V_2`, with the clauses of
`HJO.Sweep.IsNOperator` each read between the pieces its arrow joins. This is the shape of
Mellit's `∇'`, an endomorphism of each `V_k` of the direct sum `V_* = ⨁_k V_k`; unlike
`HJO.Sweep.IsNOperator` it does not ask the operator on `V_1` to restrict to `∇` on the constants
`V_0 ⊆ V_1`, which no Macdonald conjugator allows (`HJO.Sweep.not_exists_isNOperator`). -/
structure IsNOperatorOnPieces (q u : L) (nabla : Module.End L (Sym.Lambda L))
    (N₁ N₂ : Module.End L (Total L)) : Prop where
  /-- `𝒩'_1 d^*_+ = d^*_+ ∇` out of `V_0`. -/
  map_dplusStar_zero : ∀ f : Sym.Lambda L,
    N₁ (dplusStar q u 0 (C f)) = dplusStar q u 0 (C (nabla f))
  /-- `𝒩'_2 d^*_+ = d^*_+ 𝒩'_1` out of `V_1`. -/
  map_dplusStar_one : ∀ F : Total L, F ∈ piece L 1 →
    N₂ (dplusStar q u 1 F) = dplusStar q u 1 (N₁ F)
  /-- `∇ d_- = d_- 𝒩'_1` out of `V_1`. -/
  map_dminus_one : ∀ F : Total L, F ∈ piece L 1 → ∀ f : Sym.Lambda L,
    dminus q 1 F = C f → dminus q 1 (N₁ F) = C (nabla f)
  /-- `𝒩'_1 d_- = d_- 𝒩'_2` out of `V_2`. -/
  map_dminus_two : ∀ F : Total L, F ∈ piece L 2 →
    N₁ (dminus q 2 F) = dminus q 2 (N₂ F)
  /-- `𝒩'_1 y_1 = (qu)^{-1}z_1y_1𝒩'_1` on `V_1`. -/
  map_auxVar_mul : ∀ F : Total L, F ∈ piece L 1 →
    N₁ ((auxVar 1 : Total L) * F) = ((q * u)⁻¹ • zop q u 1 1) ((auxVar 1 : Total L) * N₁ F)

namespace IsNOperatorOnPieces

variable {nabla : Module.End L (Sym.Lambda L)} {N₁ N₂ : Module.End L (Total L)}

/-- `𝒩'_1` commutes with `z_1` on `V_1`. -/
theorem map_zop_one (hN : IsNOperatorOnPieces q u nabla N₁ N₂) {F : Total L}
    (hF : F ∈ piece L 1) : N₁ (zop q u 1 1 F) = zop q u 1 1 (N₁ F) := by
  have h0 : dminus q 1 F ∈ piece L 0 := by simpa using dminus_mem_piece q 1 hF
  obtain ⟨f, hf⟩ := exists_C_eq_of_mem_piece_zero h0
  have h2 : dplusStar q u 1 F ∈ piece L 2 := dplusStar_mem_piece q u hF
  rw [zop_one_one_apply, zop_one_one_apply, map_smul, map_sub, ← hf, hN.map_dplusStar_zero,
    ← hN.map_dminus_one F hF f hf.symm, hN.map_dminus_two _ h2, hN.map_dplusStar_one F hF]

/-- `𝒩'_1` on a letter: it fixes `𝗓` and shears `𝗒` into `𝗒𝗓`. -/
theorem map_sweepLetter (hN : IsNOperatorOnPieces q u nabla N₁ N₂) (x : SlopeLetter)
    {F : Total L} (hF : F ∈ piece L 1) :
    N₁ (sweepLetter q u x F) = sweepWordOp q u (Mellit.addLeftSubst x) (N₁ F) := by
  cases x with
  | y =>
    change N₁ ((-LinearMap.mulLeft L (auxVar 1 : Total L)) F) = _
    rw [LinearMap.neg_apply, LinearMap.mulLeft_apply, map_neg, hN.map_auxVar_mul F hF]
    simp [Mellit.addLeftSubst, sweepWordOp, sweepLetter]
  | z =>
    change N₁ (((q * u)⁻¹ • zop q u 1 1) F) = _
    rw [LinearMap.smul_apply, map_smul, hN.map_zop_one hF]
    simp [Mellit.addLeftSubst, sweepWordOp, sweepLetter]

/-- `𝒩'_1` on a word: the word acting on `V_1` is carried to its shear `t[𝗒 ↦ 𝗒𝗓]`. -/
theorem map_sweepWordOp (hN : IsNOperatorOnPieces q u nabla N₁ N₂) :
    ∀ (t : List SlopeLetter) {F : Total L}, F ∈ piece L 1 →
      N₁ (sweepWordOp q u t F) = sweepWordOp q u (t.flatMap Mellit.addLeftSubst) (N₁ F) := by
  intro t
  induction t with
  | nil => intro F _; simp [sweepWordOp_nil]
  | cons x t ih =>
    intro F hF
    rw [sweepWordOp_cons, Module.End.mul_apply, ih (sweepLetter_mem_piece q u x hF),
      hN.map_sweepLetter x hF, List.flatMap_cons, sweepWordOp_append, Module.End.mul_apply]

/-- `𝒩'_1` on the argument of the clause: `𝒩'_1(y_1d^*_+Cg) = (qu)^{-1}z_1(y_1d^*_+C(∇g))`. -/
theorem map_slopeArg (hN : IsNOperatorOnPieces q u nabla N₁ N₂) (g : Sym.Lambda L) :
    N₁ (Mellit.slopeArg q u g) = sweepLetter q u .z (Mellit.slopeArg q u (nabla g)) := by
  rw [Mellit.slopeArg_def, hN.map_auxVar_mul _ (dplusStar_zero_C_mem_piece_one q u g),
    hN.map_dplusStar_zero, Mellit.slopeArg_def]
  rfl

/-- **The shadow on `V_0`**: `∇` commutes with `D_0 = d_-d^*_+`, the first clause of a Macdonald
conjugator, so the repaired hypothesis passes the check its predecessor passed. -/
theorem nabla_dop_zero (hN : IsNOperatorOnPieces q u nabla N₁ N₂) (f : Sym.Lambda L) :
    nabla (Sym.Dop q u 0 f) = Sym.Dop q u 0 (nabla f) := by
  apply MvPolynomial.C_injective ℕ (Sym.Lambda L)
  have h1 : dplusStar q u 0 (C f : Total L) ∈ piece L 1 := dplusStar_zero_C_mem_piece_one q u f
  have h := hN.map_dminus_one _ h1 (Sym.Dop q u 0 f) (dop_zero_eq_dminus_dplusStar q u f).symm
  rw [hN.map_dplusStar_zero, ← dop_zero_eq_dminus_dplusStar] at h
  exact h.symm

end IsNOperatorOnPieces

/-- **The clause of `HJO.Mellit.lhsRewrite_sweepWitness`'s base case is carried along Mellit's
`N`**, given an operator realising `N` piece by piece: `HJO.Mellit.LhsSlope` at a positive coprime
`(m,n)` implies it at `(m+n,n)`. The proof is that of `HJO.Sweep.lhsSlope_add_left`, with `∇` read
on `V_0` through `d_-` out of `V_1` instead of through a common operator on the nested pieces. -/
theorem lhsSlope_add_left_of_isNOperatorOnPieces {nabla : Module.End L (Sym.Lambda L)}
    {N₁ N₂ : Module.End L (Total L)} (hnab : Sym.IsSlopeConjugator q u nabla)
    (hN : IsNOperatorOnPieces q u nabla N₁ N₂) (hM : (1 - q) * (1 - u) ≠ 0) {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) (h : Mellit.LhsSlope q u m n) :
    Mellit.LhsSlope q u (m + n) n := by
  intro f
  obtain ⟨g, rfl⟩ := hnab.bijective.2 f
  have harg : Mellit.slopeArg q u g ∈ piece L 1 :=
    mul_mem (auxVar_mem_piece le_rfl le_rfl) (dplusStar_zero_C_mem_piece_one q u g)
  have hW : slopeOperator q u 1 m n (Mellit.slopeArg q u g) ∈ piece L 1 :=
    slopeOperator_mem_piece q u le_rfl harg
  have hF : (-1 : L) ^ (n + 1) • slopeOperator q u 1 m n (Mellit.slopeArg q u g) ∈ piece L 1 :=
    smul_mem_piece hW
  have hd := hN.map_dminus_one _ hF (Sym.Qop q u m n g) (by rw [h g, map_smul])
  rw [hnab.qop_add_apply hM m hm n hn g, ← hd, map_smul, map_smul,
    slopeOperator_eq_sweepWordOp, hN.map_sweepWordOp _ harg, hN.map_slopeArg,
    slopeOperator_eq_sweepWordOp, Mellit.reverse_slopeWord_add_left hmn hm hn, sweepWordOp_cons,
    Module.End.mul_apply]

/-- **The clause at every positive coprime slope, given an operator realising `N` piece by
piece.** Euclid's algorithm: `(a,b)` with `a < b` is the `S`-image of `(a,b-a)`
(`HJO.Sweep.lhsSlope_add_self`), `(a,b)` with `a > b` the `N`-image of `(a-b,b)`, and the descent
ends on the `(1,b)` row (`HJO.Mellit.lhsSlope_one_left`). -/
theorem lhsSlope_of_coprime_of_isNOperatorOnPieces {nabla : Module.End L (Sym.Lambda L)}
    {N₁ N₂ : Module.End L (Total L)} (hnab : Sym.IsSlopeConjugator q u nabla)
    (hN : IsNOperatorOnPieces q u nabla N₁ N₂)
    (hM : ∀ k : ℕ, 1 ≤ k → (1 - q ^ k) * (1 - u ^ k) ≠ 0)
    (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    ∀ a b : ℕ, Nat.Coprime a b → 1 ≤ a → 1 ≤ b → Mellit.LhsSlope q u a b := by
  have hM1 : (1 - q) * (1 - u) ≠ 0 := by simpa using hM 1 le_rfl
  intro a b
  induction h : a + b using Nat.strong_induction_on generalizing a b with
  | _ s ih =>
    intro hab ha hb
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · obtain rfl : a = 1 := by omega
      exact Mellit.lhsSlope_one_left q u hb
    rcases lt_trichotomy a b with hlt | heq | hgt
    · obtain ⟨c, rfl⟩ : ∃ c, b = c + a := ⟨b - a, by omega⟩
      have hac : Nat.Coprime a c := Nat.coprime_add_self_right.1 hab
      have hc : 1 ≤ c := by
        by_contra h0
        obtain rfl : c = 0 := by omega
        rw [zero_add, Nat.coprime_self] at hab
        omega
      exact lhsSlope_add_self hM hq0 hu0 hq1 hac ha hc
        (ih (a + c) (by omega) a c rfl hac ha hc)
    · subst heq
      rw [Nat.coprime_self] at hab
      omega
    · obtain ⟨c, rfl⟩ : ∃ c, a = c + b := ⟨a - b, by omega⟩
      have hcb : Nat.Coprime c b := Nat.coprime_add_self_left.1 hab
      have hc : 1 ≤ c := by omega
      exact lhsSlope_add_left_of_isNOperatorOnPieces hnab hN hM1 hcb hc hb
        (ih (c + b) (by omega) c b rfl hcb hc hb)

end Pieces

end HJO.Sweep

/-! ### Mellit's `N` preserves `𝓘` -/

namespace HJO.Dyck.Tilde.Atilde

section ConjTwistKernel

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]
  {bar : K ≃+* K} {σ : Atilde K q u →+ Atilde K q u}
  (h : IsStarSwap q bar (e K q u) (dPlus K q u) (dPlusStar K q u) (dMinus K q u) (Tg K q u) σ)
  (hbar : bar q = ⅟q)

include h hbar

/-- `N` on the corner elements `y_i` is their reading in the twisted raising family. -/
theorem conjTwist_yElt (c : K) (k i : ℕ) :
    conjTwist h hbar c (yElt K q u k i) = yTwist K q u c k i :=
  map_cornerOf (conjTwist h hbar c) q ⅟q ⅟(q - 1) (conjTwist_e h hbar c)
    (fun n => by rw [conjTwist_dPlus]; rfl) (conjTwist_dMinus h hbar c) (conjTwist_Tg h hbar c) k i

/-- `N` fixes the tower `d₊^{*m}𝟏_v`. -/
theorem conjTwist_dPlusStarPow (c : K) (v m : ℕ) :
    conjTwist h hbar c (dPlusStarPow K q u v m) = dPlusStarPow K q u v m := by
  induction m with
  | zero => exact conjTwist_e h hbar c v
  | succ m ih => rw [dPlusStarPow_succ, map_mul, conjTwist_dPlusStar, ih]

/-- **Mellit's `N` preserves the left ideal `𝓘` of the structure theorem.** It fixes the first
family of generators, and carries `(d₊ + q^ky_1d₊^*)d₊^{*k}𝟏_0` to
`c·z_1(d₊ + q^ky_1d₊^*)d₊^{*k}𝟏_0`,
because `N(y_1) = c·z_1y_1` (`HJO.Dyck.Tilde.Atilde.yTwist_one`). -/
theorem conjTwist_mem_mellitKernel (c : K) {x : Atilde K q u} (hx : x ∈ mellitKernel K q u) :
    conjTwist h hbar c x ∈ mellitKernel K q u := by
  have hle : mellitKernel K q u ≤ (mellitKernel K q u).comap (conjTwist h hbar c) := by
    refine Ideal.span_le.2 ?_
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · change conjTwist h hbar c _ ∈ mellitKernel K q u
      rw [map_mul, map_sub, map_mul, conjTwist_dMinus, conjTwist_dPlusStar, conjTwist_e,
        conjTwist_dPlusStarPow]
      exact Ideal.subset_span (Or.inl ⟨k, rfl⟩)
    · change conjTwist h hbar c _ ∈ mellitKernel K q u
      rw [map_mul, map_add, map_smul, map_mul, conjTwist_dPlus, conjTwist_dPlusStar,
        conjTwist_dPlusStarPow, conjTwist_yElt, yTwist_one h hbar c (by omega : 1 ≤ k + 1)]
      have hg : (dPlus K q u k + (q ^ k) • (yElt K q u (k + 1) 1 * dPlusStar K q u k)) *
          dPlusStarPow K q u 0 k ∈ mellitKernel K q u := Ideal.subset_span (Or.inr ⟨k, rfl⟩)
      have := Ideal.mul_mem_left _ (c • zElt K q u (k + 1) 1) hg
      convert this using 1
      simp only [smul_mul_assoc, mul_add, mul_smul_comm, add_mul, mul_assoc]
  exact hle hx

end ConjTwistKernel

end HJO.Dyck.Tilde.Atilde

namespace HJO.Sweep

open MvPolynomial

variable {L : Type*} [Field L]

/-! ### Mellit's `∇'`: the endomorphism of `V_*` induced by `N` -/

section NablaPrime

open Dyck.Tilde

variable [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]

/-- The additive group of `V_*`, supplied explicitly: instance search does not find it through
the summands here. -/
noncomputable local instance : AddCommGroup (Vstar L) :=
  @DirectSum.instAddCommGroup ℕ (fun k => pieceSub L k) (fun _ => Submodule.addCommGroup _)


omit [Algebra ℚ L] in
/-- **An endomorphism of `Ã` preserving `Ã𝟏_0` and `𝓘` induces an intertwiner of `V_*`.** When
`x ↦ x·1` maps `Ã𝟏_0` onto `V_*` with kernel inside `𝓘` (the structure theorem,
`HJO.Sweep.dpaStructure`), an algebra endomorphism `Φ` of `Ã` fixing `𝟏_0` and carrying `𝓘` into
itself induces `𝒩'` on `V_*` with `𝒩'(x·1) = Φ(x)·1`, hence `𝒩'ρ(a) = ρ(Φa)𝒩'` for every
`a ∈ Ã`. This is the first step of Mellit's proof that `∇L∇^{-1} = N(L)`. -/
theorem exists_intertwiner {ρ : Atilde L q u →ₐ[L] Module.End L (Vstar L)}
    (hρe : ∀ k : ℕ, ρ (Atilde.e L q u k) = pieceProj L k)
    (hsurj : ∀ v : Vstar L, ∃ x ∈ Atilde.atildeE0 L q u, evalOne ρ x = v)
    (hker : ∀ x ∈ Atilde.atildeE0 L q u, ∀ y ∈ Atilde.atildeE0 L q u,
      evalOne ρ x = evalOne ρ y → x - y ∈ Atilde.mellitKernel L q u)
    (hann : ∀ x ∈ Atilde.mellitKernel L q u, evalOne ρ x = 0)
    (Φ : Atilde L q u →ₐ[L] Atilde L q u) (hΦe : Φ (Atilde.e L q u 0) = Atilde.e L q u 0)
    (hΦI : ∀ x ∈ Atilde.mellitKernel L q u, Φ x ∈ Atilde.mellitKernel L q u) :
    ∃ Nv : Module.End L (Vstar L),
      (∀ (a : Atilde L q u) (v : Vstar L), Nv (ρ a v) = ρ (Φ a) (Nv v))
      ∧ Nv (oneVstar L) = oneVstar L := by
  have hE0 : ∀ x ∈ Atilde.atildeE0 L q u, Φ x ∈ Atilde.atildeE0 L q u := by
    intro x hx
    rw [Atilde.mem_atildeE0_iff] at hx ⊢
    rw [← hΦe, ← map_mul, hx]
  have hwd : ∀ x ∈ Atilde.atildeE0 L q u, ∀ y ∈ Atilde.atildeE0 L q u,
      evalOne ρ x = evalOne ρ y → evalOne ρ (Φ x) = evalOne ρ (Φ y) := by
    intro x hx y hy hxy
    have h0 := hann _ (hΦI _ (hker x hx y hy hxy))
    rw [show x = y + (x - y) from by abel, map_add, map_add, h0, add_zero]
  choose pre hpre hpreeq using hsurj
  have key : ∀ x ∈ Atilde.atildeE0 L q u,
      evalOne ρ (Φ (pre (evalOne ρ x))) = evalOne ρ (Φ x) := fun x hx =>
    hwd _ (hpre _) _ hx (hpreeq _)
  set Nv : Module.End L (Vstar L) :=
    { toFun := fun v => evalOne ρ (Φ (pre v))
      map_add' := fun v w => by
        have := key (pre v + pre w) (add_mem (hpre v) (hpre w))
        rw [map_add, hpreeq, hpreeq] at this
        rw [this, map_add, map_add]
      map_smul' := fun c v => by
        have := key (c • pre v) (Submodule.smul_mem _ c (hpre v))
        rw [map_smul, hpreeq] at this
        rw [this, map_smul, map_smul]; rfl } with hNv
  have hNv' : ∀ x ∈ Atilde.atildeE0 L q u, Nv (evalOne ρ x) = evalOne ρ (Φ x) := key
  refine ⟨Nv, fun a v => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ : ∃ x ∈ Atilde.atildeE0 L q u, evalOne ρ x = v :=
      ⟨pre v, hpre v, hpreeq v⟩
    have hax : a * x ∈ Atilde.atildeE0 L q u := by
      rw [Atilde.mem_atildeE0_iff, mul_assoc, (Atilde.mem_atildeE0_iff).1 hx]
    have h1 := hNv' _ hax
    rw [evalOne_mul] at h1
    rw [h1, map_mul, evalOne_mul, hNv' x hx]
  · have he0 : Atilde.e L q u 0 ∈ Atilde.atildeE0 L q u := by
      rw [Atilde.mem_atildeE0_iff, Atilde.e_mul_self]
    have h := hNv' _ he0
    rwa [hΦe, evalOne_e_zero ρ hρe] at h

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- The retraction of the total space onto `V_k`, killing the letters beyond `y_k`. -/
noncomputable def pieceRetractAlg (k : ℕ) : Total L →ₐ[Sym.Lambda L] Total L :=
  aeval fun j => if j < k then (X j : Total L) else 0

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- The retraction takes values in `V_k`. -/
theorem pieceRetractAlg_mem (k : ℕ) (F : Total L) : pieceRetractAlg k F ∈ piece L k := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [pieceRetractAlg, aeval_C, MvPolynomial.algebraMap_eq]
    exact piece_mono (Nat.zero_le k) (C_mem_piece_zero a)
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | mul_X p j hp =>
    rw [map_mul, pieceRetractAlg, aeval_X]
    split_ifs with hj
    · have hX : (X j : Total L) = auxVar (j + 1) := by rw [auxVar, Nat.add_sub_cancel]
      exact mul_mem hp (hX ▸ auxVar_mem_piece (by omega) (by omega))
    · rw [mul_zero]; exact zero_mem _

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- The retraction fixes every element of `V_k`. -/
theorem pieceRetractAlg_of_mem {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    pieceRetractAlg k F = F := by
  rw [piece, MvPolynomial.supported_eq_adjoin_X] at hF
  induction hF using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    simp [pieceRetractAlg, Set.mem_Iio.1 hj]
  | algebraMap r => exact AlgHom.commutes _ r
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- The retraction onto `V_k` as an `L`-linear map into the piece. -/
noncomputable def pieceRetract (k : ℕ) : Total L →ₗ[L] pieceSub L k :=
  ((pieceRetractAlg k).toLinearMap.restrictScalars L).codRestrict (pieceSub L k)
    (pieceRetractAlg_mem k)

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- The linear retraction sends an element of `V_k` to itself. -/
theorem pieceRetract_of_mem {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    pieceRetract k F = ⟨F, hF⟩ :=
  Subtype.ext (pieceRetractAlg_of_mem hF)

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- The constant term of the total space, as an `L`-linear map onto `Λ`. -/
noncomputable def constantCoeffLin : Total L →ₗ[L] Sym.Lambda L where
  toFun := constantCoeff
  map_add' := map_add _
  map_smul' c F := by
    rw [Algebra.smul_def, map_mul, RingHom.id_apply, Algebra.smul_def,
      MvPolynomial.algebraMap_apply, constantCoeff_C]

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- The constants of the total space, as an `L`-linear map out of `Λ`. -/
noncomputable def constLin : Sym.Lambda L →ₗ[L] Total L where
  toFun f := C f
  map_add' := map_add C
  map_smul' c f := by
    rw [Algebra.smul_def, map_mul, RingHom.id_apply, Algebra.smul_def,
      MvPolynomial.algebraMap_apply]
    rfl

variable (Nv : Module.End L (Vstar L))

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- An endomorphism of `V_*` read on its `k`-th summand. -/
noncomputable def nvPiece (k : ℕ) : pieceSub L k →ₗ[L] pieceSub L k :=
  toPiece L k ∘ₗ Nv ∘ₗ ofPiece L k

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- An endomorphism of `V_*` read on its `k`-th summand, extended to the total space through the
retraction onto `V_k`. -/
noncomputable def nvTotal (k : ℕ) : Module.End L (Total L) :=
  (pieceSub L k).subtype ∘ₗ nvPiece Nv k ∘ₗ pieceRetract k

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- An endomorphism of `V_*` read on `V_0 = Λ`. -/
noncomputable def nvZero : Module.End L (Sym.Lambda L) :=
  constantCoeffLin ∘ₗ nvTotal Nv 0 ∘ₗ constLin

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- On an element of `V_k`, the extension to the total space agrees with the `k`-th summand map. -/
theorem nvTotal_of_mem {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    nvTotal Nv k F = (nvPiece Nv k ⟨F, hF⟩ : Total L) := by
  rw [nvTotal, LinearMap.comp_apply, LinearMap.comp_apply, pieceRetract_of_mem hF]
  rfl

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- The endomorphism read on `V_0 = Λ`, viewed as constants, is the `0`-th summand map. -/
theorem C_nvZero (f : Sym.Lambda L) :
    (C (nvZero Nv f) : Total L) = (nvPiece Nv 0 ⟨C f, C_mem_piece_zero f⟩ : Total L) := by
  obtain ⟨g, hg⟩ := exists_C_eq_of_mem_piece_zero (nvPiece Nv 0 ⟨C f, C_mem_piece_zero f⟩).2
  have h : nvZero Nv f = g := by
    change constantCoeff (nvTotal Nv 0 (C f)) = g
    rw [nvTotal_of_mem Nv (C_mem_piece_zero f), ← hg, constantCoeff_C]
  rw [h, hg]

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- The inclusion of the `k`-th summand into `V_*` is injective. -/
theorem ofPiece_injective (k : ℕ) : Function.Injective (ofPiece L k) := fun F G h => by
  have := congrArg (toPiece L k) h
  rwa [toPiece_ofPiece, toPiece_ofPiece] at this

section Intertwiner

variable {ρ : Atilde L q u →ₐ[L] Module.End L (Vstar L)} {Φ : Atilde L q u →ₐ[L] Atilde L q u}
  {Nv : Module.End L (Vstar L)}
  (hρe : ∀ k : ℕ, ρ (Atilde.e L q u k) = pieceProj L k)
  (hΦe : ∀ k : ℕ, Φ (Atilde.e L q u k) = Atilde.e L q u k)
  (hNv : ∀ (a : Atilde L q u) (v : Vstar L), Nv (ρ a v) = ρ (Φ a) (Nv v))

include hρe hΦe hNv

omit [Algebra ℚ L] in
/-- An intertwiner of an endomorphism fixing the idempotents preserves each summand. -/
theorem nv_ofPiece (k : ℕ) (F : pieceSub L k) :
    Nv (ofPiece L k F) = ofPiece L k (nvPiece Nv k F) := by
  have h := hNv (Atilde.e L q u k) (ofPiece L k F)
  rw [hρe, pieceProj_ofPiece, hΦe, hρe, pieceProj_apply] at h
  exact h

omit [Algebra ℚ L] in
/-- An intertwiner commutes with a raising arrow the endomorphism fixes. -/
theorem nvPiece_raise {a : Atilde L q u} (ha : Φ a = a)
    {U : ∀ k : ℕ, pieceSub L k →ₗ[L] pieceSub L (k + 1)} {k : ℕ} (hU : ρ a = raiseVstar U k)
    (F : pieceSub L k) : nvPiece Nv (k + 1) (U k F) = U k (nvPiece Nv k F) := by
  have h := hNv a (ofPiece L k F)
  rw [ha, hU, raiseVstar_ofPiece, nv_ofPiece hρe hΦe hNv, nv_ofPiece hρe hΦe hNv,
    raiseVstar_ofPiece] at h
  exact ofPiece_injective (k + 1) h

omit [Algebra ℚ L] in
/-- An intertwiner commutes with a lowering arrow the endomorphism fixes. -/
theorem nvPiece_lower {a : Atilde L q u} (ha : Φ a = a)
    {D : ∀ k : ℕ, pieceSub L (k + 1) →ₗ[L] pieceSub L k} {k : ℕ} (hD : ρ a = lowerVstar D k)
    (F : pieceSub L (k + 1)) : nvPiece Nv k (D k F) = D k (nvPiece Nv (k + 1) F) := by
  have h := hNv a (ofPiece L (k + 1) F)
  rw [ha, hD, lowerVstar_ofPiece, nv_ofPiece hρe hΦe hNv, nv_ofPiece hρe hΦe hNv,
    lowerVstar_ofPiece] at h
  exact ofPiece_injective k h

end Intertwiner

omit [Algebra ℚ L] in
/-- `z_1` at the vertex `1` is `(q^{-1}-1)^{-1}(d₊^*d₋ - d₋d₊^*)`. -/
theorem zElt_one_one : Atilde.zElt L q u 1 1 = (-(q * ⅟(q - 1))) • (Atilde.e L q u 1 *
    (Atilde.dPlusStar L q u 0 * Atilde.dMinus L q u 0
      - Atilde.dMinus L q u 1 * Atilde.dPlusStar L q u 1) * Atilde.e L q u 1) := rfl

/-- **`z_1` acts on `V_1` as `HJO.Sweep.zop`**, for any action of `Ã` through the modified pair. -/
theorem map_zElt_one_one {ρ : Atilde L q u →ₐ[L] Module.End L (Vstar L)}
    (hρe : ∀ k : ℕ, ρ (Atilde.e L q u k) = pieceProj L k)
    (hρD : ∀ k : ℕ, ρ (Atilde.dMinus L q u k) = lowerVstar (dminusModPiece q) k)
    (hρS : ∀ k : ℕ, ρ (Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    (G : pieceSub L 1) :
    ρ (Atilde.zElt L q u 1 1) (ofPiece L 1 G)
      = ofPiece L 1 ⟨zop q u 1 1 G,
          zop_mem_piece q u 1 le_rfl le_rfl (show (G : Total L) ∈ piece L 1 from G.2)⟩ := by
  have hq1 : q - 1 ≠ 0 := Invertible.ne_zero (q - 1)
  have hc : (-(q * ⅟(q - 1)) : L) = q / (1 - q) := by
    rw [invOf_eq_inv, div_eq_mul_inv, ← neg_sub q 1, inv_neg]; ring
  have h1 : ρ (Atilde.dMinus L q u 1 * Atilde.dPlusStar L q u 1) (ofPiece L 1 G)
      = ofPiece L 1 (dminusModPiece q 1 (dplusStarPiece q u 1 G)) := by
    rw [map_mul, Module.End.mul_apply, hρS, hρD, raiseVstar_ofPiece, lowerVstar_ofPiece]
  have h2 : ρ (Atilde.dPlusStar L q u 0 * Atilde.dMinus L q u 0) (ofPiece L 1 G)
      = ofPiece L 1 (dplusStarPiece q u 0 (dminusModPiece q 0 G)) := by
    rw [map_mul, Module.End.mul_apply, hρS, hρD,
      lowerVstar_ofPiece (D := dminusModPiece q) 0 G, raiseVstar_ofPiece]
  rw [zElt_one_one, map_smul, map_mul, map_mul, hρe, LinearMap.smul_apply,
    Module.End.mul_apply, Module.End.mul_apply, pieceProj_ofPiece, map_sub, LinearMap.sub_apply,
    h1, h2, ← map_sub, pieceProj_ofPiece, ← map_smul]
  refine congrArg (ofPiece L 1) (Subtype.ext ?_)
  change _ = zop q u 1 1 (G : Total L)
  rw [SetLike.val_smul, Submodule.coe_sub, coe_dplusStarPiece, coe_dminusModPiece,
    coe_dminusModPiece, coe_dplusStarPiece, hc, zop_one_one_apply]

/-- **The intertwiner of an endomorphism of `Ã` realising `N` is an operator realising `N` piece by
piece.** If `Φ` fixes the idempotents, `d₋` and `d₊^*`, and sends `y_1` (at the vertex `1`) to
`(qu)^{-1}z_1y_1`, then any `𝒩'` with `𝒩'ρ(a) = ρ(Φa)𝒩'` satisfies
`HJO.Sweep.IsNOperatorOnPieces` over its own restriction to `V_0`. -/
theorem isNOperatorOnPieces_of_intertwiner {ρ : Atilde L q u →ₐ[L] Module.End L (Vstar L)}
    (hρe : ∀ k : ℕ, ρ (Atilde.e L q u k) = pieceProj L k)
    (hρT : ∀ k i : ℕ, ρ (Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
    (hρD : ∀ k : ℕ, ρ (Atilde.dMinus L q u k) = lowerVstar (dminusModPiece q) k)
    (hρU : ∀ k : ℕ, ρ (Atilde.dPlus L q u k) = raiseVstar (dplusModPiece q) k)
    (hρS : ∀ k : ℕ, ρ (Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    {Φ : Atilde L q u →ₐ[L] Atilde L q u}
    (hΦe : ∀ k : ℕ, Φ (Atilde.e L q u k) = Atilde.e L q u k)
    (hΦD : ∀ k : ℕ, Φ (Atilde.dMinus L q u k) = Atilde.dMinus L q u k)
    (hΦS : ∀ k : ℕ, Φ (Atilde.dPlusStar L q u k) = Atilde.dPlusStar L q u k)
    (hΦy : Φ (Atilde.yElt L q u 1 1)
      = (q * u)⁻¹ • (Atilde.zElt L q u 1 1 * Atilde.yElt L q u 1 1))
    {Nv : Module.End L (Vstar L)}
    (hNv : ∀ (a : Atilde L q u) (v : Vstar L), Nv (ρ a v) = ρ (Φ a) (Nv v)) :
    IsNOperatorOnPieces q u (nvZero Nv) (nvTotal Nv 1) (nvTotal Nv 2) where
  map_dplusStar_zero f := by
    have hmem : dplusStar q u 0 (C f : Total L) ∈ piece L 1 :=
      dplusStar_zero_C_mem_piece_one q u f
    rw [nvTotal_of_mem Nv hmem, C_nvZero]
    have h := nvPiece_raise hρe hΦe hNv (hΦS 0) (hρS 0) ⟨C f, C_mem_piece_zero f⟩
    have he : (⟨dplusStar q u 0 (C f), hmem⟩ : pieceSub L 1)
        = dplusStarPiece q u 0 ⟨C f, C_mem_piece_zero f⟩ := Subtype.ext rfl
    rw [he, h, coe_dplusStarPiece]
  map_dplusStar_one F hF := by
    have hmem : dplusStar q u 1 F ∈ piece L 2 := dplusStar_mem_piece q u hF
    rw [nvTotal_of_mem Nv hmem, nvTotal_of_mem Nv hF]
    have h := nvPiece_raise hρe hΦe hNv (hΦS 1) (hρS 1) ⟨F, hF⟩
    have he : (⟨dplusStar q u 1 F, hmem⟩ : pieceSub L 2) = dplusStarPiece q u 1 ⟨F, hF⟩ :=
      Subtype.ext rfl
    rw [he, h, coe_dplusStarPiece]
  map_dminus_one F hF f hf := by
    rw [nvTotal_of_mem Nv hF, C_nvZero]
    have h := nvPiece_lower hρe hΦe hNv (hΦD 0) (hρD 0) ⟨F, hF⟩
    have he : dminusModPiece q 0 ⟨F, hF⟩ = ⟨C f, C_mem_piece_zero f⟩ :=
      Subtype.ext (by rw [coe_dminusModPiece]; exact hf)
    rw [he] at h
    rw [h, coe_dminusModPiece]
  map_dminus_two F hF := by
    have hmem : dminus q 2 F ∈ piece L 1 := by simpa using dminus_mem_piece q 2 hF
    rw [nvTotal_of_mem Nv hmem, nvTotal_of_mem Nv hF]
    have h := nvPiece_lower hρe hΦe hNv (hΦD 1) (hρD 1) ⟨F, hF⟩
    have he : (⟨dminus q 2 F, hmem⟩ : pieceSub L 1) = dminusModPiece q 1 ⟨F, hF⟩ :=
      Subtype.ext rfl
    rw [he, h, coe_dminusModPiece]
  map_auxVar_mul F hF := by
    have hy1 : (auxVar 1 : Total L) ∈ piece L 1 := auxVar_mem_piece le_rfl le_rfl
    have hmem : (auxVar 1 : Total L) * F ∈ piece L 1 := mul_mem hy1 hF
    rw [nvTotal_of_mem Nv hmem, nvTotal_of_mem Nv hF]
    have hρy := map_yElt_atilde_eq_auxMulPiece hρe hρT hρD hρU (k := 1) (i := 1) le_rfl le_rfl
    have hyF : ρ (Atilde.yElt L q u 1 1) (ofPiece L 1 ⟨F, hF⟩)
        = ofPiece L 1 ⟨(auxVar 1 : Total L) * F, hmem⟩ := by
      rw [hρy, loopVstar_ofPiece]
      exact congrArg (ofPiece L 1) (Subtype.ext (coe_auxMulPiece le_rfl le_rfl _))
    have h := hNv (Atilde.yElt L q u 1 1) (ofPiece L 1 ⟨F, hF⟩)
    set G := nvPiece Nv 1 ⟨F, hF⟩ with hG
    have hyG : ρ (Atilde.yElt L q u 1 1) (ofPiece L 1 G)
        = ofPiece L 1 ⟨(auxVar 1 : Total L) * G, (mul_mem hy1
          (show (G : Total L) ∈ piece L 1 from G.2) : (auxVar 1 : Total L) * G ∈ piece L 1)⟩ := by
      rw [hρy, loopVstar_ofPiece]
      exact congrArg (ofPiece L 1) (Subtype.ext (coe_auxMulPiece le_rfl le_rfl _))
    rw [hyF, nv_ofPiece hρe hΦe hNv, nv_ofPiece hρe hΦe hNv, hΦy, map_smul, map_mul,
      LinearMap.smul_apply, Module.End.mul_apply, ← hG, hyG, map_zElt_one_one hρe hρD hρS,
      ← map_smul] at h
    have h' := congrArg Subtype.val (ofPiece_injective 1 h)
    rw [h']
    rfl

omit [Invertible q] [Invertible (q - 1)] in
/-- `d^♭_-d^♭_+` out of `V_0` is multiplication by `e_1`. -/
theorem dminus_dplus_C (q : L) (f : Sym.Lambda L) :
    dminus q 1 (dplus q 0 (C f : Total L)) = C (Sym.elemSymm L 1 * f) := by
  have hy : (auxVar 1 : Total L) = X 0 := by rw [auxVar]
  rw [dplus_apply, show trainUpEnd q 1 (0 + 1) = 1 from Braid.trainUp_self _ _ 1,
    Module.End.one_apply, dminus_apply, map_neg, map_mul, hy, qshiftNeg_auxVar, qshiftNeg_qshift,
    mul_comm, ← MvPolynomial.smul_eq_C_mul, map_neg, LinearMap.map_smul_of_tower,
    ← pow_one (X 0 : Total L), lowerCoeff_zero_X_pow, MvPolynomial.smul_eq_C_mul, map_mul]
  ring

/-- **Mellit's `∇'` exists, read piece by piece.** Under the hypotheses of `HJO.Sym.paramInvLambda`
(which the structure theorem and the existence of `N` on `Ã` carry), the endomorphism `N` of `Ã`
fixing `d₋, d₊^*, T_i` and the idempotents and sending `d₊ ↦ (qu)^{-1}z_1d₊` preserves `𝓘`, and so
induces on `V_* ≅ Ã𝟏_0/𝓘` an operator `∇'` with `∇'L = N(L)∇'`. Its restrictions to `V_0, V_1, V_2`
satisfy `HJO.Sweep.IsNOperatorOnPieces` over `∇ := ∇'|_{V_0}`; moreover `∇1 = 1`, and `∇` carries
multiplication by `e_1 = d_-d_+` to `-D_1 = -d_-y_1d_+^*`, the second clause of a Macdonald
conjugator, because `N(d_+) = (qu)^{-1}z_1d_+ = -y_1d^*_+` by the third mixed relation. (Its first
clause, commuting with `D_0`, is `HJO.Sweep.IsNOperatorOnPieces.nabla_dop_zero`.)

The scalar is `(qu)^{-1}` and not Mellit's `-(qt)^{-1}`: Mellit's `∇` carries the sign
`(-1)^{|λ|}` that `HJO.Sym.IsMacdonaldConjugator` does not, and the scalar at `d_+` is free in the
construction (`HJO.Dyck.Tilde.Atilde.exists_conjTwist`). -/
theorem exists_isNOperatorOnPieces_of_bar (hq1 : q + 1 ≠ 0) [Invertible u] {bar : L ≃+* L}
    (hbar : bar q = ⅟q) (hbaru : bar u = ⅟u) (hbb : ∀ c : L, bar (bar c) = c) :
    ∃ (nabla : Module.End L (Sym.Lambda L)) (N₁ N₂ : Module.End L (Total L)),
      IsNOperatorOnPieces q u nabla N₁ N₂ ∧ nabla 1 = 1
        ∧ ∀ f : Sym.Lambda L, nabla (Sym.elemSymm L 1 * f) = -Sym.Dop q u 1 (nabla f) := by
  obtain ⟨ρ, hρe, hρT, hρD, hρU, hρS, hker, eiso, heiso⟩ := dpaStructure q u hq1 hbar hbaru hbb
  obtain ⟨σ, hσ⟩ := Atilde.exists_isStarSwap (K := L) (q := q) (u := u) hbar hbaru hbb
  set c : L := (q * u)⁻¹ with hc
  set Φ := Atilde.conjTwist hσ hbar c with hΦ
  have hsurj : ∀ v : Vstar L, ∃ x ∈ Atilde.atildeE0 L q u, evalOne ρ x = v := by
    intro v
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (eiso.symm v)
    exact ⟨x, x.2, by rw [← heiso, hx, LinearEquiv.apply_symm_apply]⟩
  have hker' : ∀ x ∈ Atilde.atildeE0 L q u, ∀ y ∈ Atilde.atildeE0 L q u,
      evalOne ρ x = evalOne ρ y → x - y ∈ Atilde.mellitKernel L q u := by
    intro x hx y hy hxy
    have hmem : (⟨x - y, sub_mem hx hy⟩ : Atilde.atildeE0 L q u)
        ∈ LinearMap.ker ((evalOne ρ).domRestrict (Atilde.atildeE0 L q u)) := by
      rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, map_sub, hxy, sub_self]
    rw [hker] at hmem
    exact hmem
  have hann : ∀ x ∈ Atilde.mellitKernel L q u, evalOne ρ x = 0 := by
    intro x hx
    have hx0 : x ∈ Atilde.atildeE0 L q u := Atilde.mellitKernel_le_atildeE0 hx
    have hmem : (⟨x, hx0⟩ : Atilde.atildeE0 L q u)
        ∈ LinearMap.ker ((evalOne ρ).domRestrict (Atilde.atildeE0 L q u)) := by
      rw [hker]; exact hx
    exact hmem
  obtain ⟨Nv, hNv, hNv1⟩ := exists_intertwiner hρe hsurj hker' hann Φ
    (Atilde.conjTwist_e hσ hbar c 0) (fun x hx => Atilde.conjTwist_mem_mellitKernel hσ hbar c hx)
  have hΦe : ∀ k, Φ (Atilde.e L q u k) = Atilde.e L q u k := Atilde.conjTwist_e hσ hbar c
  have hΦy : Φ (Atilde.yElt L q u 1 1)
      = (q * u)⁻¹ • (Atilde.zElt L q u 1 1 * Atilde.yElt L q u 1 1) := by
    rw [hΦ, Atilde.conjTwist_yElt, Atilde.yTwist_one hσ hbar c le_rfl]
  refine ⟨nvZero Nv, nvTotal Nv 1, nvTotal Nv 2,
    isNOperatorOnPieces_of_intertwiner hρe hρT hρD hρU hρS hΦe
      (Atilde.conjTwist_dMinus hσ hbar c) (Atilde.conjTwist_dPlusStar hσ hbar c) hΦy hNv, ?_, ?_⟩
  · apply MvPolynomial.C_injective ℕ (Sym.Lambda L)
    rw [C_nvZero]
    have h1 : (⟨C 1, C_mem_piece_zero 1⟩ : pieceSub L 0) = ⟨1, one_mem (piece L 0)⟩ :=
      Subtype.ext (map_one _)
    have h := nv_ofPiece hρe hΦe hNv 0 ⟨1, one_mem (piece L 0)⟩
    rw [show ofPiece L 0 ⟨1, one_mem (piece L 0)⟩ = oneVstar L from rfl, hNv1] at h
    rw [h1, ofPiece_injective 0 h.symm, map_one]
  · intro f
    apply MvPolynomial.C_injective ℕ (Sym.Lambda L)
    have hmem : (C (Sym.elemSymm L 1 * f) : Total L) ∈ piece L 0 :=
      C_mem_piece_zero _
    have hlhs : ρ (Atilde.dMinus L q u 0 * Atilde.dPlus L q u 0)
        (ofPiece L 0 ⟨C f, C_mem_piece_zero f⟩)
        = ofPiece L 0 ⟨C (Sym.elemSymm L 1 * f), hmem⟩ := by
      rw [map_mul, Module.End.mul_apply, hρU, hρD, raiseVstar_ofPiece, lowerVstar_ofPiece]
      exact congrArg (ofPiece L 0) (Subtype.ext (dminus_dplus_C q f))
    have hΦdd : Φ (Atilde.dMinus L q u 0 * Atilde.dPlus L q u 0)
        = -(Atilde.dMinus L q u 0 * (Atilde.yElt L q u 1 1 * Atilde.dPlusStar L q u 0)) := by
      have hqu : q * u ≠ 0 :=
        mul_ne_zero (Invertible.ne_zero q) (Invertible.ne_zero u)
      rw [map_mul, Atilde.conjTwist_dMinus, Atilde.conjTwist_dPlus, Atilde.zElt_one_mul_dPlus,
        smul_neg, smul_smul]
      simp only [zero_add, pow_one]
      rw [show c * (u * q) = 1 from by rw [hc, mul_comm u q]; exact inv_mul_cancel₀ hqu,
        one_smul]
      exact mul_neg (Atilde.dMinus L q u 0) (Atilde.yElt L q u 1 1 * Atilde.dPlusStar L q u 0)
    have hrhs : ∀ g : Sym.Lambda L, ρ (Atilde.dMinus L q u 0 *
        (Atilde.yElt L q u 1 1 * Atilde.dPlusStar L q u 0)) (ofPiece L 0 ⟨C g, C_mem_piece_zero g⟩)
        = ofPiece L 0 ⟨C (Sym.Dop q u 1 g), C_mem_piece_zero _⟩ := by
      intro g
      have hρy := map_yElt_atilde_eq_auxMulPiece hρe hρT hρD hρU (k := 1) (i := 1) le_rfl le_rfl
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hρS, raiseVstar_ofPiece,
        hρy, loopVstar_ofPiece, hρD, lowerVstar_ofPiece]
      refine congrArg (ofPiece L 0) (Subtype.ext ?_)
      have hD1 := dop_succ_eq_dminus_auxVar_pow_dplusStar q u 0 g
      rw [zero_add, pow_one] at hD1
      change _ = (C (Sym.Dop q u 1 g) : Total L)
      rw [coe_dminusModPiece, coe_auxMulPiece le_rfl le_rfl, coe_dplusStarPiece, hD1]
    have h := hNv (Atilde.dMinus L q u 0 * Atilde.dPlus L q u 0)
      (ofPiece L 0 ⟨C f, C_mem_piece_zero f⟩)
    rw [hlhs, nv_ofPiece hρe hΦe hNv, nv_ofPiece hρe hΦe hNv, hΦdd, map_neg,
      LinearMap.neg_apply] at h
    have hf : nvPiece Nv 0 ⟨C f, C_mem_piece_zero f⟩
        = ⟨C (nvZero Nv f), C_mem_piece_zero _⟩ := Subtype.ext (C_nvZero Nv f).symm
    rw [hf, hrhs, ← map_neg] at h
    have h' := congrArg Subtype.val (ofPiece_injective 0 h)
    rw [C_nvZero, h', map_neg]
    rfl

/-- **Mellit's `∇'` is the Macdonald conjugator on `V_0`, and realises `N` piece by piece.** The
restriction `∇'|_{V_0}` fixes `1`, commutes with `D_0` and turns `e_1·` into `-D_1`
(`HJO.Sweep.exists_isNOperatorOnPieces_of_bar`), and these determine it
(`HJO.Sym.eq_of_slope_clauses`); so it is the Macdonald conjugator normalised by `∇1 = 1`,
whenever one exists. This is Mellit's `∇' = ∇` on `V_0`, reached without the characteristic
functions. -/
theorem exists_isMacdonaldConjugator_isNOperatorOnPieces_of_bar (hM : (1 - q) * (1 - u) ≠ 0)
    (hq1 : q + 1 ≠ 0) [Invertible u] {bar : L ≃+* L} (hbar : bar q = ⅟q) (hbaru : bar u = ⅟u)
    (hbb : ∀ c : L, bar (bar c) = c)
    (hnab : ∃ nabla : Module.End L (Sym.Lambda L),
      Sym.IsMacdonaldConjugator q u nabla ∧ nabla 1 = 1) :
    ∃ (nabla : Module.End L (Sym.Lambda L)) (N₁ N₂ : Module.End L (Total L)),
      Sym.IsMacdonaldConjugator q u nabla ∧ IsNOperatorOnPieces q u nabla N₁ N₂ := by
  obtain ⟨nabla₁, hnab₁, hone₁⟩ := hnab
  obtain ⟨nabla, N₁, N₂, hN, hone, he1⟩ := exists_isNOperatorOnPieces_of_bar hq1 hbar hbaru hbb
  obtain rfl : nabla = nabla₁ := Sym.eq_of_slope_clauses q u hN.nabla_dop_zero he1
    hnab₁.map_dop_zero hnab₁.map_elemSymm_one_mul (hone.trans hone₁.symm) hM
  exact ⟨nabla, N₁, N₂, hnab₁, hN⟩

/-- **The base-case clause of `HJO.Mellit.lhsRewrite_sweepWitness` at every positive coprime
slope**, under the hypotheses of `HJO.Sym.paramInvLambda` and the existence of the Macdonald
conjugator normalised by `∇1 = 1` (`HJO.Sym.exists_isMacdonaldConjugator`): Mellit's `∇'` realises
`N` piece by piece over it (`HJO.Sweep.exists_isMacdonaldConjugator_isNOperatorOnPieces_of_bar`),
and `HJO.Sweep.lhsSlope_of_coprime_of_isNOperatorOnPieces` applies. -/
theorem lhsSlope_of_coprime_of_bar (hM : ∀ k : ℕ, 1 ≤ k → (1 - q ^ k) * (1 - u ^ k) ≠ 0)
    (hq1 : q + 1 ≠ 0) [Invertible u] {bar : L ≃+* L} (hbar : bar q = ⅟q) (hbaru : bar u = ⅟u)
    (hbb : ∀ c : L, bar (bar c) = c)
    (hnab : ∃ nabla : Module.End L (Sym.Lambda L),
      Sym.IsMacdonaldConjugator q u nabla ∧ nabla 1 = 1) :
    ∀ a b : ℕ, Nat.Coprime a b → 1 ≤ a → 1 ≤ b → Mellit.LhsSlope q u a b := by
  obtain ⟨nabla, N₁, N₂, hnab', hN⟩ := exists_isMacdonaldConjugator_isNOperatorOnPieces_of_bar
    (by simpa using hM 1 le_rfl) hq1 hbar hbaru hbb hnab
  exact lhsSlope_of_coprime_of_isNOperatorOnPieces hnab'.isSlopeConjugator hN hM
    (Invertible.ne_zero q) (Invertible.ne_zero u) (sub_ne_zero.1 (Invertible.ne_zero (q - 1)))

end NablaPrime

end HJO.Sweep

