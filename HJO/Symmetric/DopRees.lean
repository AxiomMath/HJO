/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.ReesClosed

/-! # The basic operators lie in the order filtration

The coefficient of `wᵈ` in the plethystic displacement is an operator of differential order at
most `d`: the chain rule in `w` writes it through the coefficients of lower degree composed with
one partial derivative, because each application of the displacement costs at least one power of
`w`. Pairing those coefficients with the elementary symmetric functions presents the basic
operator as a locally finite sum of operators of increasing differential order.
-/

@[expose] public section

open Finset

namespace HJO.DopRees

open HJO.Sym HJO.ReesClosed

variable {L : Type*} [Field L]

/-- The scalar multiplying `w ^ (i + 1)` in the image of the generator `p_{i+1}` under the
plethystic displacement. -/
def shiftScalar (q u : L) (i : ℕ) : L := (1 - q ^ (i + 1)) * (1 - u ^ (i + 1))

/-- The weight attached to the index `i` by the chain rule for the displacement in `w`. -/
def chainScalar (q u : L) (i : ℕ) : L := (i + 1 : L) * shiftScalar q u i

/-- The coefficient of `wᵈ` of the plethystic displacement, as an `L`-linear endomorphism of the
ring of symmetric functions. -/
noncomputable def shiftCoeff (q u : L) (d : ℕ) : Module.End L (Lambda L) where
  toFun f := (plethShift q u f).coeff d
  map_add' f g := by rw [map_add, Polynomial.coeff_add]
  map_smul' a f := by simp [map_smul]

/-- The coefficient operator evaluates to the corresponding coefficient of the displacement. -/
@[simp] theorem shiftCoeff_apply (q u : L) (d : ℕ) (f : Lambda L) :
    shiftCoeff q u d f = (plethShift q u f).coeff d := rfl

/-- The displacement of the generator `p_{n+1}`. -/
theorem plethShift_X (q u : L) (n : ℕ) :
    plethShift q u (MvPolynomial.X n) =
      Polynomial.C (MvPolynomial.X n) +
        Polynomial.C (MvPolynomial.C (shiftScalar q u n)) * Polynomial.X ^ (n + 1) := by
  simp [plethShift, powerSum, shiftScalar]

/-- At `u = 1` the plethystic displacement is trivial. -/
theorem plethShift_eq_C (q : L) {u : L} (hu : u = 1) (f : Lambda L) :
    plethShift q u f = Polynomial.C f := by
  have h : (plethShift q u).toRingHom = (Polynomial.C : Lambda L →+* Polynomial (Lambda L)) :=
    MvPolynomial.ringHom_ext (fun r => by simp)
      fun i => by simp [plethShift_X, hu, shiftScalar]
  exact RingHom.congr_fun h f

/-- The coefficient of `wᵈ` in the displacement of `f * p_{n+1}`: the undisplaced generator
contributes the same degree, and the displaced one shifts the degree by `n + 1`. -/
theorem shiftCoeff_mul_X (q u : L) (g : Lambda L) (n d : ℕ) :
    shiftCoeff q u d (g * MvPolynomial.X n) =
      shiftCoeff q u d g * MvPolynomial.X n
        + (if n + 1 ≤ d then shiftCoeff q u (d - (n + 1)) g else 0)
            * MvPolynomial.C (shiftScalar q u n) := by
  rw [shiftCoeff_apply, map_mul, plethShift_X, mul_add, Polynomial.coeff_add,
    Polynomial.coeff_mul_C, ← mul_assoc (plethShift q u g), Polynomial.coeff_mul_X_pow',
    Polynomial.coeff_mul_C]
  simp only [shiftCoeff_apply]
  split_ifs <;> simp

/-- The partial derivative of `g * p_{n+1}`. -/
theorem pderiv_mul_X (i n : ℕ) (g : Lambda L) :
    MvPolynomial.pderiv i (g * MvPolynomial.X n)
      = MvPolynomial.pderiv i g * MvPolynomial.X n + (if i = n then g else 0) := by
  rw [MvPolynomial.pderiv_mul]
  rcases eq_or_ne i n with rfl | h
  · simp
  · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm h), h]

/-- The chain rule for the displacement in the variable `w`: differentiating once in `w` trades a
power of `w` for a partial derivative, so the coefficient of `w ^ (m + 1)` is a finite
combination of the coefficients of lower degree applied to first derivatives. -/
theorem succ_smul_shiftCoeff (q u : L) : ∀ (f : Lambda L) (m : ℕ),
    ((m : L) + 1) • shiftCoeff q u (m + 1) f
      = ∑ i ∈ range (m + 1), chainScalar q u i •
          shiftCoeff q u (m - i) (MvPolynomial.pderiv i f) := by
  intro f
  induction f using MvPolynomial.induction_on with
  | C a => intro m; simp
  | add f g hf hg =>
      intro m
      simp only [map_add, smul_add, Finset.sum_add_distrib]
      rw [hf m, hg m]
  | mul_X g n ih =>
      intro m
      have hsplit : ∑ i ∈ range (m + 1), chainScalar q u i •
            shiftCoeff q u (m - i) (MvPolynomial.pderiv i (g * MvPolynomial.X n))
          = (∑ i ∈ range (m + 1), chainScalar q u i •
                (shiftCoeff q u (m - i) (MvPolynomial.pderiv i g) * MvPolynomial.X n))
            + (∑ i ∈ range (m + 1), chainScalar q u i •
                ((if n + 1 ≤ m - i then
                    shiftCoeff q u (m - i - (n + 1)) (MvPolynomial.pderiv i g) else 0)
                  * MvPolynomial.C (shiftScalar q u n)))
            + (∑ i ∈ range (m + 1), chainScalar q u i •
                shiftCoeff q u (m - i) (if i = n then g else 0)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pderiv_mul_X, map_add, shiftCoeff_mul_X, smul_add, smul_add]
      have hS1 : ∑ i ∈ range (m + 1), chainScalar q u i •
            (shiftCoeff q u (m - i) (MvPolynomial.pderiv i g) * MvPolynomial.X n)
          = (((m : L) + 1) • shiftCoeff q u (m + 1) g) * MvPolynomial.X n := by
        rw [ih m, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (smul_mul_assoc _ _ _).symm
      have hS3 : ∑ i ∈ range (m + 1), chainScalar q u i •
            shiftCoeff q u (m - i) (if i = n then g else 0)
          = if n ≤ m then chainScalar q u n • shiftCoeff q u (m - n) g else 0 := by
        have hterm : ∀ i ∈ range (m + 1), chainScalar q u i •
              shiftCoeff q u (m - i) (if i = n then g else 0)
            = if i = n then chainScalar q u n • shiftCoeff q u (m - n) g else 0 := by
          intro i _
          rcases eq_or_ne i n with rfl | h
          · simp
          · simp [h]
        rw [Finset.sum_congr rfl hterm]
        simp [Finset.sum_ite_eq']
      have hS2 : ∑ i ∈ range (m + 1), chainScalar q u i •
            ((if n + 1 ≤ m - i then
                shiftCoeff q u (m - i - (n + 1)) (MvPolynomial.pderiv i g) else 0)
              * MvPolynomial.C (shiftScalar q u n))
          = (((m - n : ℕ) : L) • shiftCoeff q u (m - n) g)
              * MvPolynomial.C (shiftScalar q u n) := by
        by_cases hmn : m ≤ n
        · rw [Nat.sub_eq_zero_of_le hmn, Finset.sum_eq_zero]
          · simp
          · intro i hi
            simp only [Finset.mem_range] at hi
            have hif : ¬ n + 1 ≤ m - i := by omega
            simp [hif]
        · replace hmn : n < m := by omega
          obtain ⟨m', rfl⟩ : ∃ m', m = n + 1 + m' := ⟨m - n - 1, by omega⟩
          have hsub : range (m' + 1) ⊆ range (n + 1 + m' + 1) := by
            intro x hx
            simp only [Finset.mem_range] at hx ⊢
            omega
          have hout : ∀ i ∈ range (n + 1 + m' + 1), i ∉ range (m' + 1) →
              chainScalar q u i • ((if n + 1 ≤ n + 1 + m' - i then
                  shiftCoeff q u (n + 1 + m' - i - (n + 1)) (MvPolynomial.pderiv i g) else 0)
                * MvPolynomial.C (shiftScalar q u n)) = 0 := by
            intro i _ hi
            simp only [Finset.mem_range, not_lt] at hi
            have hif : ¬ n + 1 ≤ n + 1 + m' - i := by omega
            simp [hif]
          have hin : ∀ i ∈ range (m' + 1),
              chainScalar q u i • ((if n + 1 ≤ n + 1 + m' - i then
                  shiftCoeff q u (n + 1 + m' - i - (n + 1)) (MvPolynomial.pderiv i g) else 0)
                * MvPolynomial.C (shiftScalar q u n))
              = (chainScalar q u i • shiftCoeff q u (m' - i) (MvPolynomial.pderiv i g))
                  * MvPolynomial.C (shiftScalar q u n) := by
            intro i hi
            simp only [Finset.mem_range] at hi
            have hif : n + 1 ≤ n + 1 + m' - i := by omega
            have hsub2 : n + 1 + m' - i - (n + 1) = m' - i := by omega
            simp [hif, hsub2]
          rw [← Finset.sum_subset hsub hout, Finset.sum_congr rfl hin,
            show n + 1 + m' - n = m' + 1 from by omega, Nat.cast_add, Nat.cast_one, ih m',
            Finset.sum_mul]
      rw [shiftCoeff_mul_X, smul_add, ← smul_mul_assoc, hsplit, hS1, hS2, hS3, add_assoc]
      congr 1
      simp only [add_le_add_iff_right, Nat.add_sub_add_right]
      have hAC : ∀ A : Lambda L, A * MvPolynomial.C (shiftScalar q u n)
          = shiftScalar q u n • A := fun A => by
        rw [MvPolynomial.smul_eq_C_mul, mul_comm]
      split_ifs with h
      · rw [hAC, hAC, smul_smul, chainScalar, smul_smul, ← add_smul]
        congr 1
        rw [Nat.cast_sub h]
        ring
      · rw [Nat.sub_eq_zero_of_le (by omega : m ≤ n)]
        simp

/-- The displacement is the identity modulo `w`, so its constant coefficient is the identity
operator. -/
theorem shiftCoeff_zero_apply (q u : L) (f : Lambda L) : shiftCoeff q u 0 f = f := by
  have h : (Polynomial.evalRingHom (0 : Lambda L)).comp (plethShift q u).toRingHom
      = RingHom.id (Lambda L) :=
    MvPolynomial.ringHom_ext (fun r => by simp) fun i => by simp [plethShift_X]
  simpa [Polynomial.coeff_zero_eq_eval_zero] using RingHom.congr_fun h f

/-- The constant coefficient of the displacement is the identity operator. -/
theorem shiftCoeff_zero (q u : L) : shiftCoeff q u 0 = 1 :=
  LinearMap.ext (shiftCoeff_zero_apply q u)

/-- The chain rule as an identity between operators. -/
theorem succ_smul_shiftCoeff_eq (q u : L) (m : ℕ) :
    ((m : L) + 1) • shiftCoeff q u (m + 1)
      = ∑ i ∈ range (m + 1), chainScalar q u i • (shiftCoeff q u (m - i) * pderivEnd L i) := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.smul_apply, LinearMap.sum_apply, succ_smul_shiftCoeff q u f m]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- An operator of differential order zero lies in the order filtration: its expansion has the
single term of index zero. -/
theorem mem_rees_of_diffOrderAtMost_zero {u : L} {P : Module.End L (Lambda L)}
    (hP : HasDiffOrderAtMost 0 P) : P ∈ Rees u := by
  refine ⟨fun j => if j = 0 then P else 0, fun j => ?_, fun f => ⟨1, fun j hj => ?_, ?_⟩⟩
  · dsimp only
    rcases eq_or_ne j 0 with rfl | hj
    · simpa using hP
    · have hz : (if j = 0 then P else 0) = 0 := by simp [hj]
      rw [hz, hasDiffOrderAtMost_iff_mem]
      exact Submodule.zero_mem _
  · have hj0 : j ≠ 0 := by omega
    simp [hj0]
  · simp

section RationalAlgebra

variable [Algebra ℚ L]

/-- The coefficient of `wᵈ` of the displacement has differential order at most `d`: the chain rule
expresses it through coefficients of lower degree composed with one further derivative. -/
theorem shiftCoeff_mem_diffOrder (q u : L) (d : ℕ) : shiftCoeff q u d ∈ diffOrder L d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d with
    | 0 =>
      rw [shiftCoeff_zero]
      have h1 : (1 : Module.End L (Lambda L)) = LinearMap.mulLeft L (1 : Lambda L) :=
        LinearMap.ext fun x => by simp
      rw [h1]
      exact mulLeft_mem_diffOrder_zero _
    | m + 1 =>
      have hchar : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
      have hne : ((m : L) + 1) ≠ 0 := by
        have h : ((m + 1 : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
        push_cast at h
        exact h
      have key : shiftCoeff q u (m + 1)
          = ((m : L) + 1)⁻¹ • ∑ i ∈ range (m + 1), chainScalar q u i •
              (shiftCoeff q u (m - i) * pderivEnd L i) := by
        rw [← succ_smul_shiftCoeff_eq, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [key]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
      simp only [Finset.mem_range] at hi
      have hlist : pderivProd L [i] = pderivEnd L i := by simp [pderivProd_cons]
      rw [← hlist]
      exact diffOrder_mono (by simp only [List.length_singleton]; omega)
        (mul_pderivProd_mem (ih (m - i) (by omega)) [i])

/-- The `wᵈ`-piece of the basic operator: the coefficient of `wᵈ` of the displacement followed by
multiplication with the elementary symmetric function paired with that degree. -/
noncomputable def dopPiece (q u : L) (k d : ℕ) : Module.End L (Lambda L) :=
  LinearMap.mulLeft L ((-1) ^ (k + d) * elemSymm L (k + d)) * shiftCoeff q u d

/-- Evaluating a piece of the basic operator. -/
theorem dopPiece_apply (q u : L) (k d : ℕ) (f : Lambda L) :
    dopPiece q u k d f = ((-1) ^ (k + d) * elemSymm L (k + d)) * (plethShift q u f).coeff d := rfl

/-- Multiplication by a symmetric function does not raise the differential order, so the `wᵈ`-piece
has differential order at most `d`. -/
theorem dopPiece_mem_diffOrder (q u : L) (k d : ℕ) : dopPiece q u k d ∈ diffOrder L d :=
  mulLeft_mul_mem _ (shiftCoeff_mem_diffOrder q u d)

/-- A piece of high degree kills a fixed symmetric function, because the displacement of that
function is a polynomial in `w` of bounded degree. -/
theorem dopPiece_apply_eq_zero (q u : L) (k : ℕ) (f : Lambda L) {d : ℕ}
    (hd : (plethShift q u f).natDegree < d) : dopPiece q u k d f = 0 := by
  rw [dopPiece_apply, Polynomial.coeff_eq_zero_of_natDegree_lt hd, mul_zero]

/-- The basic operator is the finite sum of its pieces, the extraction being finite because the
displacement of a fixed symmetric function is a polynomial in `w`. -/
theorem dop_apply_eq_sum (q u : L) (k : ℕ) (f : Lambda L) {N : ℕ}
    (hN : (plethShift q u f).natDegree < N) :
    Dop q u k f = ∑ d ∈ range N, dopPiece q u k d f := by
  change (plethShift q u f).sum (fun j A => A * ((-1) ^ (k + j) * elemSymm L (k + j)))
      = ∑ d ∈ range N, dopPiece q u k d f
  rw [Polynomial.sum_over_range' _ (fun j => by rw [zero_mul]) N hN]
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

/-- At `u = 1` the basic operator is multiplication by `(-1) ^ k eₖ`. -/
theorem dop_eq_mulLeft (q : L) {u : L} (hu : u = 1) (k : ℕ) :
    Dop q u k = LinearMap.mulLeft L ((-1) ^ k * elemSymm L k) := by
  refine LinearMap.ext fun f => ?_
  rw [dop_apply_eq_sum q u k f (N := 1) (by rw [plethShift_eq_C q hu]; simp),
    Finset.sum_range_one, dopPiece_apply, plethShift_eq_C q hu]
  simp [mul_assoc]

/-- The basic operators lie in the order filtration: the coefficient of `wᵈ` of the displacement
has differential order at most `d`, multiplication by an elementary symmetric function does not
raise it, and only finitely many pieces act nontrivially on a fixed symmetric function.

The witness used here, `((1 - u) ^ d)⁻¹ • dopPiece q u k d`, has a pole at `u = 1`, and `Rees`
records no regularity of the coefficients; `HJO.DiffOrder.dop_mem_reesRegComm` gives the
membership in the filtration that does. -/
theorem dop_mem_rees (q u : L) (k : ℕ) : Dop q u k ∈ Rees u := by
  rcases eq_or_ne (1 - u : L) 0 with hu | hu
  · refine mem_rees_of_diffOrderAtMost_zero ?_
    rw [dop_eq_mulLeft q (eq_of_sub_eq_zero hu).symm k, hasDiffOrderAtMost_iff_mem]
    exact mulLeft_mem_diffOrder_zero _
  · refine ⟨fun d => ((1 - u) ^ d)⁻¹ • dopPiece q u k d, fun d => ?_, fun f => ?_⟩
    · rw [hasDiffOrderAtMost_iff_mem]
      exact Submodule.smul_mem _ _ (dopPiece_mem_diffOrder q u k d)
    · refine ⟨(plethShift q u f).natDegree + 1, fun d hd => ?_, ?_⟩
      · rw [LinearMap.smul_apply, dopPiece_apply_eq_zero q u k f (by omega), smul_zero]
      · rw [dop_apply_eq_sum q u k f (Nat.lt_succ_self _)]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ (pow_ne_zero d hu), one_smul]

end RationalAlgebra

end HJO.DopRees
