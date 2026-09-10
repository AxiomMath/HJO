/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import HJO.Symmetric.DiffOrder
public import HJO.Symmetric.Multiplication
public meta import HJO.Attr

/-! # The commutator filtration over a coefficient ring, and multiplicativity at `u = 1`

The order filtration measured by iterated commutators, with the expansion coefficients tracked over
a coefficient ring `R` mapping into the base field, is an algebra: it contains the identity and is
stable under sums, scalars from `R` and composition, the coefficient of a composite being the
antidiagonal sum of the coefficients of the factors. It is moreover stable under a commutator
divided by `(1 - q) * (1 - u)`, because a commutator of operators of orders `r` and `s` has order
`r + s - 1` rather than `r + s`, and that one-step drop is exactly what the division by `1 - u`
costs. Every slope operator is obtained from the basic operators by iterated such commutators, so
all of them lie in the filtration.

Read through a ring homomorphism on the coefficient ring carrying the parameter to `1`, an operator
of the filtration becomes multiplication by its own value on `1`. This is the source of the
multiplicativity statement proved at the end: the axis generators are a triangular change of
generators whose leading coefficients are units of the coefficient ring, so they generate the whole
ring of symmetric functions over that ring, and hence the operator attached by a slope homomorphism
to any symmetric function with coefficients in `R` specialises to a multiplication operator. The
specialisation is a homomorphism out of `R`, not out of the base field, and the parameter is not
`1` in either -- the last section exhibits an instance where it is not, along with an operator of
the filtration that is not a multiplication operator.
-/

@[expose] public section

open Finset

namespace HJO.DopCommutator

open MvPolynomial HJO.Sym HJO.ReesClosed HJO.ReesRegular HJO.DiffOrder
open HJO.DopRees HJO.Multiplication HJO.UkRegular

/-! ### The commutator filtration over the coefficient ring is an algebra -/

section Algebra

variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L]

/-- Multiplication by a symmetric function with coefficients in `R` has differential order zero
over `R`. -/
theorem hasDiffOrderReg_mulLeft (g : Lambda R) :
    HasDiffOrderReg R 0 (LinearMap.mulLeft L (coeffInc R L g)) :=
  ⟨hasDiffOrder_mulLeft _, fun f hf => by
    rw [LinearMap.mulLeft_apply]
    exact mul_mem_regSub (coeffInc_mem_regSub g) hf⟩

/-- Scaling by an element of the coefficient ring, written as an `R`-action, stays in the
filtration over that ring. -/
theorem hasDiffOrderReg_smul' {n : ℕ} (a : R) {P : Module.End L (Lambda L)}
    (hP : HasDiffOrderReg R n P) : HasDiffOrderReg R n (a • P) := by
  rw [← algebraMap_smul L a P]
  exact hasDiffOrderReg_smul a hP

/-- The zero operator lies in the commutator filtration over the coefficient ring. -/
theorem zero_mem_reesRegComm (u : R) : (0 : Module.End L (Lambda L)) ∈ ReesRegComm R L u :=
  ⟨fun _ => 0, fun _ => hasDiffOrderReg_zero _, fun _ => ⟨0, fun _ _ => rfl, by simp⟩⟩

/-- An operator of differential order zero over the coefficient ring lies in the filtration: its
expansion has the single term of index zero. -/
theorem mem_reesRegComm_of_hasDiffOrderReg_zero {u : R} {P : Module.End L (Lambda L)}
    (hP : HasDiffOrderReg R 0 P) : P ∈ ReesRegComm R L u := by
  refine ⟨fun j => if j = 0 then P else 0, fun j => ?_, fun f => ⟨1, fun j hj => ?_, ?_⟩⟩
  · dsimp only
    rcases eq_or_ne j 0 with rfl | hj
    · simpa using hP
    · simpa [hj] using hasDiffOrderReg_zero (R := R) (L := L) j
  · have hj0 : j ≠ 0 := by omega
    simp [hj0]
  · simp

/-- The identity operator lies in the commutator filtration over the coefficient ring: it is
multiplication by `1`, of differential order zero. -/
theorem one_mem_reesRegComm (u : R) : (1 : Module.End L (Lambda L)) ∈ ReesRegComm R L u := by
  have h : (1 : Module.End L (Lambda L)) = LinearMap.mulLeft L (coeffInc R L (1 : Lambda R)) := by
    rw [map_one]
    exact (LinearMap.ext fun x => by simp).symm
  rw [h]
  exact mem_reesRegComm_of_hasDiffOrderReg_zero (hasDiffOrderReg_mulLeft _)

/-- The commutator filtration over the coefficient ring is closed under addition: the expansions
may be added coefficientwise. -/
theorem add_mem_reesRegComm {u : R} {P Q : Module.End L (Lambda L)} (hP : P ∈ ReesRegComm R L u)
    (hQ : Q ∈ ReesRegComm R L u) : P + Q ∈ ReesRegComm R L u := by
  obtain ⟨Pc, hPord, hPsum⟩ := hP
  obtain ⟨Qc, hQord, hQsum⟩ := hQ
  refine ⟨fun j => Pc j + Qc j, fun j => hasDiffOrderReg_add (hPord j) (hQord j), fun f => ?_⟩
  obtain ⟨N₁, hz₁, hs₁⟩ := hPsum f
  obtain ⟨N₂, hz₂, hs₂⟩ := hQsum f
  refine ⟨max N₁ N₂, fun j hj => ?_, ?_⟩
  · rw [LinearMap.add_apply, hz₁ j (le_trans (le_max_left N₁ N₂) hj),
      hz₂ j (le_trans (le_max_right N₁ N₂) hj), add_zero]
  · rw [LinearMap.add_apply, expansion_extend (le_max_left N₁ N₂) hz₁ hs₁,
      expansion_extend (le_max_right N₁ N₂) hz₂ hs₂, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [LinearMap.add_apply, smul_add]

/-- The commutator filtration over the coefficient ring is closed under scaling by that ring. -/
theorem smul_mem_reesRegComm {u : R} (c : R) {P : Module.End L (Lambda L)}
    (hP : P ∈ ReesRegComm R L u) : c • P ∈ ReesRegComm R L u := by
  obtain ⟨Pc, hord, hsum⟩ := hP
  refine ⟨fun j => c • Pc j, fun j => hasDiffOrderReg_smul' c (hord j), fun f => ?_⟩
  obtain ⟨N, hz, hs⟩ := hsum f
  refine ⟨N, fun j hj => ?_, ?_⟩
  · rw [LinearMap.smul_apply, hz j hj, smul_zero]
  · rw [LinearMap.smul_apply, hs, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, smul_comm]

/-- The commutator filtration over the coefficient ring is closed under composition: the
`ℏ ^ m`-coefficient of a composite is the sum of the products of the coefficients over the
antidiagonal of `m`, and differential orders add under composition. -/
theorem mul_mem_reesRegComm {u : R} {P Q : Module.End L (Lambda L)} (hP : P ∈ ReesRegComm R L u)
    (hQ : Q ∈ ReesRegComm R L u) : P * Q ∈ ReesRegComm R L u := by
  classical
  obtain ⟨Pc, hPord, hPsum⟩ := hP
  obtain ⟨Qc, hQord, hQsum⟩ := hQ
  choose np hnpz hnpsum using hPsum
  choose nq hnqz hnqsum using hQsum
  refine ⟨fun m => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, Pc p.1 * Qc p.2, ?_, ?_⟩
  · intro m
    refine hasDiffOrderReg_sum fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    exact hasDiffOrderReg_mono (le_of_eq hp) (hasDiffOrderReg_mul (hPord p.1) (hQord p.2))
  · intro f
    obtain ⟨K₀, h2, h3⟩ : ∃ K₀ : ℕ, nq f ≤ K₀ ∧ ∀ j < nq f, np (Qc j f) ≤ K₀ :=
      ⟨max (nq f) ((range (nq f)).sup fun j => np (Qc j f)), le_max_left _ _,
        fun j hj => le_trans (Finset.le_sup (f := fun j => np (Qc j f))
          (Finset.mem_range.mpr hj)) (le_max_right _ _)⟩
    have hzero : ∀ i j : ℕ, K₀ + 1 ≤ i ∨ K₀ + 1 ≤ j → (Pc i * Qc j) f = 0 := by
      intro i j hij
      rw [Module.End.mul_apply]
      rcases lt_or_ge j (nq f) with hj | hj
      · have hi : K₀ + 1 ≤ i := by rcases hij with hi | hj' <;> omega
        exact hnpz (Qc j f) i (by have := h3 j hj; omega)
      · rw [hnqz f j hj, map_zero]
    have hPQ : ∀ j ∈ range (K₀ + 1), P (Qc j f)
        = ∑ i ∈ range (K₀ + 1), (1 - algebraMap R L u) ^ i • Pc i (Qc j f) := by
      intro j _
      rcases lt_or_ge j (nq f) with hj | hj
      · exact expansion_extend (by have := h3 j hj; omega) (hnpz (Qc j f)) (hnpsum (Qc j f))
      · rw [hnqz f j hj]
        simp
    have hQ0 : Q f = ∑ j ∈ range (K₀ + 1), (1 - algebraMap R L u) ^ j • Qc j f :=
      expansion_extend (by omega) (hnqz f) (hnqsum f)
    have hA : (P * Q) f = ∑ i ∈ range (K₀ + 1), ∑ j ∈ range (K₀ + 1),
        (1 - algebraMap R L u) ^ (i + j) • ((Pc i * Qc j) f) := by
      rw [Module.End.mul_apply, hQ0, map_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [map_smul, hPQ j hj, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← pow_add, add_comm j i, Module.End.mul_apply]
    have hsq : ∑ i ∈ range (K₀ + 1), ∑ j ∈ range (K₀ + 1),
          (1 - algebraMap R L u) ^ (i + j) • ((Pc i * Qc j) f)
        = ∑ n ∈ range (2 * (K₀ + 1)), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
            (1 - algebraMap R L u) ^ (p.1 + p.2) • ((Pc p.1 * Qc p.2) f) := by
      rw [← Finset.sum_product']
      exact (sum_antidiagonal_eq_sum_product
        (fun i j => (1 - algebraMap R L u) ^ (i + j) • ((Pc i * Qc j) f)) (K₀ + 1)
        fun i j hij => by rw [hzero i j hij, smul_zero]).symm
    have hin : ∀ n : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          (1 - algebraMap R L u) ^ (p.1 + p.2) • ((Pc p.1 * Qc p.2) f)
        = (1 - algebraMap R L u) ^ n •
            ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, Pc p.1 * Qc p.2) f) := by
      intro n
      rw [LinearMap.sum_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [hp]
    refine ⟨2 * (K₀ + 1), fun j hj => ?_, ?_⟩
    · rw [LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun p hp => hzero p.1 p.2
        (by rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp; omega)
    · rw [hA, hsq]
      exact Finset.sum_congr rfl fun n _ => hin n

end Algebra

/-! ### The filtration is closed under normalised commutators -/

section Commutator

variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L]

/-- Two operators of differential order zero over the coefficient ring commute, being
multiplication operators. -/
theorem commutator_eq_zero_of_hasDiffOrderReg_zero {P Q : Module.End L (Lambda L)}
    (hP : HasDiffOrderReg R 0 P) (hQ : HasDiffOrderReg R 0 Q) : P * Q - Q * P = 0 :=
  sub_eq_zero_of_eq (commute_of_hasDiffOrder_zero hP.1 hQ.1)

/-- The commutator filtration over the coefficient ring is closed under normalised commutators: if
`P` and `Q` admit `ℏ`-expansions whose `ℏ ^ j`-coefficient has differential order at most `j` and
is defined over `R`, then so does `M⁻¹ (P Q - Q P)` for `M = (1 - q) * (1 - u)`, provided `1 - q` is
a unit of the coefficient ring. The `ℏ ^ j`-coefficient of the commutator is a sum of commutators
`[Pᵣ, Q_s]` with `r + s = j + 1`, each of differential order at most `j` because a commutator drops
one below the sum of the orders, and dividing by `M` shifts that back into place without leaving
`R`. -/
theorem smul_commutator_mem_reesRegComm {q u : R} (hq : IsUnit (1 - q))
    {P Q : Module.End L (Lambda L)} (hP : P ∈ ReesRegComm R L u) (hQ : Q ∈ ReesRegComm R L u) :
    ((1 - algebraMap R L q) * (1 - algebraMap R L u))⁻¹ • (P * Q - Q * P) ∈ ReesRegComm R L u := by
  obtain ⟨v, hv⟩ := hq.exists_left_inv
  rcases eq_or_ne (1 - algebraMap R L u : L) 0 with hu | hu
  · rw [hu, mul_zero, inv_zero, zero_smul]
    exact zero_mem_reesRegComm u
  rcases eq_or_ne (1 - algebraMap R L q : L) 0 with hqz | hqz
  · rw [hqz, zero_mul, inv_zero, zero_smul]
    exact zero_mem_reesRegComm u
  have hvL : algebraMap R L v = (1 - algebraMap R L q)⁻¹ := by
    have hmul : algebraMap R L v * (1 - algebraMap R L q) = 1 := by
      have hmap := congrArg (algebraMap R L) hv
      rwa [map_mul, map_sub, map_one] at hmap
    exact eq_inv_of_mul_eq_one_left hmul
  obtain ⟨Pc, hPord, hPsum⟩ := hP
  obtain ⟨Qc, hQord, hQsum⟩ := hQ
  choose np hnpz hnpsum using hPsum
  choose nq hnqz hnqsum using hQsum
  refine ⟨fun m => v • ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
    (Pc p.1 * Qc p.2 - Qc p.2 * Pc p.1), ?_, ?_⟩
  · intro m
    refine hasDiffOrderReg_smul' v (hasDiffOrderReg_sum fun p hp => ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    exact hasDiffOrderReg_commutator (by omega) (hPord p.1) (hQord p.2)
  · intro f
    obtain ⟨K₀, h1, h2, h3, h4⟩ : ∃ K₀ : ℕ, np f ≤ K₀ ∧ nq f ≤ K₀ ∧
        (∀ j < nq f, np (Qc j f) ≤ K₀) ∧ (∀ i < np f, nq (Pc i f) ≤ K₀) := by
      refine ⟨max (max (np f) (nq f))
        (max ((range (nq f)).sup fun j => np (Qc j f))
          ((range (np f)).sup fun i => nq (Pc i f))), le_trans (le_max_left _ _) (le_max_left _ _),
        le_trans (le_max_right _ _) (le_max_left _ _), fun j hj => ?_, fun i hi => ?_⟩
      · exact le_trans (Finset.le_sup (f := fun j => np (Qc j f)) (Finset.mem_range.mpr hj))
          (le_trans (le_max_left _ _) (le_max_right _ _))
      · exact le_trans (Finset.le_sup (f := fun i => nq (Pc i f)) (Finset.mem_range.mpr hi))
          (le_trans (le_max_right _ _) (le_max_right _ _))
    have hzero : ∀ i j : ℕ, K₀ + 1 ≤ i ∨ K₀ + 1 ≤ j →
        (Pc i * Qc j - Qc j * Pc i) f = 0 := by
      intro i j hij
      have e1 : Pc i (Qc j f) = 0 := by
        rcases lt_or_ge j (nq f) with hj | hj
        · have hi : K₀ + 1 ≤ i := by rcases hij with hi | hj' <;> omega
          exact hnpz (Qc j f) i (by have := h3 j hj; omega)
        · rw [hnqz f j hj, map_zero]
      have e2 : Qc j (Pc i f) = 0 := by
        rcases lt_or_ge i (np f) with hi | hi
        · have hj : K₀ + 1 ≤ j := by rcases hij with hi' | hj <;> omega
          exact hnqz (Pc i f) j (by have := h4 i hi; omega)
        · rw [hnpz f i hi, map_zero]
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, e1, e2, sub_zero]
    have hPQ : ∀ j ∈ range (K₀ + 1), P (Qc j f)
        = ∑ i ∈ range (K₀ + 1), (1 - algebraMap R L u) ^ i • Pc i (Qc j f) := by
      intro j _
      rcases lt_or_ge j (nq f) with hj | hj
      · exact expansion_extend (by have := h3 j hj; omega) (hnpz (Qc j f)) (hnpsum (Qc j f))
      · rw [hnqz f j hj]
        simp
    have hQP : ∀ i ∈ range (K₀ + 1), Q (Pc i f)
        = ∑ j ∈ range (K₀ + 1), (1 - algebraMap R L u) ^ j • Qc j (Pc i f) := by
      intro i _
      rcases lt_or_ge i (np f) with hi | hi
      · exact expansion_extend (by have := h4 i hi; omega) (hnqz (Pc i f)) (hnqsum (Pc i f))
      · rw [hnpz f i hi]
        simp
    have hQ0 : Q f = ∑ j ∈ range (K₀ + 1), (1 - algebraMap R L u) ^ j • Qc j f :=
      expansion_extend (by omega) (hnqz f) (hnqsum f)
    have hP0 : P f = ∑ i ∈ range (K₀ + 1), (1 - algebraMap R L u) ^ i • Pc i f :=
      expansion_extend (by omega) (hnpz f) (hnpsum f)
    have hA : P (Q f) = ∑ i ∈ range (K₀ + 1), ∑ j ∈ range (K₀ + 1),
        (1 - algebraMap R L u) ^ (i + j) • Pc i (Qc j f) := by
      rw [hQ0, map_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [map_smul, hPQ j hj, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← pow_add, add_comm j i]
    have hB : Q (P f) = ∑ i ∈ range (K₀ + 1), ∑ j ∈ range (K₀ + 1),
        (1 - algebraMap R L u) ^ (i + j) • Qc j (Pc i f) := by
      rw [hP0, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_smul, hQP i hi, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← pow_add]
    have hlhs : (P * Q - Q * P) f = ∑ i ∈ range (K₀ + 1), ∑ j ∈ range (K₀ + 1),
        (1 - algebraMap R L u) ^ (i + j) • ((Pc i * Qc j - Qc j * Pc i) f) := by
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hA, hB,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_sub, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
    have hsq : ∑ i ∈ range (K₀ + 1), ∑ j ∈ range (K₀ + 1),
          (1 - algebraMap R L u) ^ (i + j) • ((Pc i * Qc j - Qc j * Pc i) f)
        = ∑ n ∈ range (2 * (K₀ + 1)), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
            (1 - algebraMap R L u) ^ (p.1 + p.2) • ((Pc p.1 * Qc p.2 - Qc p.2 * Pc p.1) f) := by
      rw [← Finset.sum_product']
      exact (sum_antidiagonal_eq_sum_product
        (fun i j => (1 - algebraMap R L u) ^ (i + j) • ((Pc i * Qc j - Qc j * Pc i) f)) (K₀ + 1)
        fun i j hij => by rw [hzero i j hij, smul_zero]).symm
    have hin : ∀ n : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          (1 - algebraMap R L u) ^ (p.1 + p.2) • ((Pc p.1 * Qc p.2 - Qc p.2 * Pc p.1) f)
        = (1 - algebraMap R L u) ^ n • ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
            (Pc p.1 * Qc p.2 - Qc p.2 * Pc p.1)) f) := by
      intro n
      rw [LinearMap.sum_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [hp]
    refine ⟨2 * K₀ + 1, fun j hj => ?_, ?_⟩
    · rw [LinearMap.smul_apply, LinearMap.sum_apply,
        Finset.sum_eq_zero fun p hp => hzero p.1 p.2
          (by rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp; omega), smul_zero]
    · rw [LinearMap.smul_apply, hlhs, hsq,
        Finset.sum_congr rfl fun n (_ : n ∈ range (2 * (K₀ + 1))) => hin n,
        show 2 * (K₀ + 1) = 2 * K₀ + 1 + 1 from by ring, Finset.sum_range_succ']
      have hz0 : ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0,
          (Pc p.1 * Qc p.2 - Qc p.2 * Pc p.1)) : Module.End L (Lambda L)) = 0 := by
        rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
        exact commutator_eq_zero_of_hasDiffOrderReg_zero (hPord 0) (hQord 0)
      rw [hz0, LinearMap.zero_apply, smul_zero, add_zero, Finset.smul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [LinearMap.smul_apply, ← algebraMap_smul_eq v
        ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1),
          (Pc p.1 * Qc p.2 - Qc p.2 * Pc p.1)) f), hvL]
      simp only [smul_smul]
      congr 1
      field_simp
      ring

end Commutator

/-! ### Reading the filtration through a specialisation of the coefficient ring -/

section Specialisation

variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L] {F : Type*} [CommRing F]

/-- The value on a symmetric function with coefficients in `R` of an operator of the filtration
again has coefficients in `R`. -/
theorem exists_coeffInc_apply_reesRegComm {u : R} {P : Module.End L (Lambda L)}
    (hP : P ∈ ReesRegComm R L u) (f : Lambda R) :
    ∃ g : Lambda R, P (coeffInc R L f) = coeffInc R L g := by
  obtain ⟨g, hg⟩ := mem_regSub.mp
    (apply_mem_regSub_of_mem_reesRegComm hP (coeffInc_mem_regSub (L := L) f))
  exact ⟨g, hg.symm⟩

/-- The value on `1` of an operator of the filtration has coefficients in `R`, so the witness the
specialisation statement asks for always exists. -/
theorem exists_coeffInc_apply_one_reesRegComm {u : R} {P : Module.End L (Lambda L)}
    (hP : P ∈ ReesRegComm R L u) : ∃ g₁ : Lambda R, P 1 = coeffInc R L g₁ := by
  obtain ⟨g₁, hg₁⟩ := exists_coeffInc_apply_reesRegComm hP (1 : Lambda R)
  exact ⟨g₁, by rwa [map_one] at hg₁⟩

/-- The specialisation of an operator of the commutator filtration over `R`: applying a ring
homomorphism `sp` with `sp u = 1` to the coefficients turns the operator into multiplication by the
specialised value on `1`. The positive-index terms of the expansion carry a factor `1 - u`, which
`sp` kills, and the constant coefficient is a multiplication operator over `R`. -/
theorem map_eq_mul_of_mem_reesRegComm (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F)
    {u : R} (hsp : sp u = 1) {P : Module.End L (Lambda L)} (hP : P ∈ ReesRegComm R L u)
    {f g g₁ : Lambda R} (hg : P (coeffInc R L f) = coeffInc R L g)
    (hg₁ : P 1 = coeffInc R L g₁) :
    MvPolynomial.map sp g = MvPolynomial.map sp g₁ * MvPolynomial.map sp f := by
  have hinc : Function.Injective (coeffInc R L) := coeffInc_injective hinj
  obtain ⟨Q, hord, hsum⟩ := hP
  obtain ⟨h, hh⟩ := exists_mulLeft_of_hasDiffOrderReg_zero (hord 0)
  have key : ∀ a b : Lambda R, P (coeffInc R L a) = coeffInc R L b →
      MvPolynomial.map sp b = MvPolynomial.map sp (h * a) := by
    intro a b hab
    obtain ⟨N, hz, heq⟩ := hsum (coeffInc R L a)
    have hcex : ∀ j, ∃ c : Lambda R, Q j (coeffInc R L a) = coeffInc R L c := by
      intro j
      obtain ⟨c, hc⟩ := mem_regSub.mp ((hord j).2 _ (coeffInc_mem_regSub a))
      exact ⟨c, hc.symm⟩
    choose c hc using hcex
    have hc0 : c 0 = h * a := by
      refine hinc ?_
      rw [← hc 0, hh, LinearMap.mulLeft_apply, map_mul]
    have hb : b = ∑ j ∈ range N, (1 - u) ^ j • c j := by
      refine hinc ?_
      rw [← hab, heq, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc j, map_smul, ← algebraMap_smul_eq ((1 - u) ^ j) (coeffInc R L (c j)), map_pow,
        map_sub, map_one]
    have hterm : ∀ j ∈ range N, MvPolynomial.map sp ((1 - u) ^ j • c j)
        = if j = 0 then MvPolynomial.map sp (c 0) else 0 := by
      intro j _
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_pow, map_sub, map_one, hsp,
        sub_self]
      rcases j with _ | j
      · simp
      · simp
    rw [← hc0, hb, map_sum, Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (range N) 0]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have hzero : c 0 = 0 := by
        refine hinc ?_
        rw [← hc 0, hz 0 le_rfl, map_zero]
      simp [hzero]
    · simp [Finset.mem_range, hN]
  have h1 : MvPolynomial.map sp g₁ = MvPolynomial.map sp h := by
    have hone : P (coeffInc R L (1 : Lambda R)) = coeffInc R L g₁ := by rwa [map_one]
    rw [key 1 g₁ hone, mul_one]
  rw [key f g hg, h1, map_mul]

/-- The specialisation packaged as a statement about every symmetric function with coefficients in
`R`: the value of `P` there has coefficients in `R`, and its specialisation is the specialisation of
the value on `1` times the specialisation of the argument. -/
theorem exists_map_eq_mul_of_mem_reesRegComm (hinj : Function.Injective (algebraMap R L))
    (sp : R →+* F) {u : R} (hsp : sp u = 1) {P : Module.End L (Lambda L)}
    (hP : P ∈ ReesRegComm R L u) {g₁ : Lambda R} (hg₁ : P 1 = coeffInc R L g₁) (f : Lambda R) :
    ∃ g : Lambda R, P (coeffInc R L f) = coeffInc R L g ∧
      MvPolynomial.map sp g = MvPolynomial.map sp g₁ * MvPolynomial.map sp f := by
  obtain ⟨g, hg⟩ := exists_coeffInc_apply_reesRegComm hP f
  exact ⟨g, hg, map_eq_mul_of_mem_reesRegComm hinj sp hsp hP hg hg₁⟩

end Specialisation

/-! ### The slope operators lie in the filtration over the coefficient ring -/

section Qop

variable {R : Type*} [CommRing R] [Algebra ℚ R] {L : Type*} [Field L] [Algebra ℚ L]
  [Algebra R L] [IsScalarTower ℚ R L]

/-- Every stage of the fuelled recursion computing the slope operators lies in the commutator
filtration over the coefficient ring: the base case is a basic operator, whose `ℏ ^ j`-coefficient
in the grading by number of derivatives has differential order at most `j` over `R`, and the
recursive case is a normalised commutator. -/
theorem qopAux_mem_reesRegComm {q u : R} (hq : IsUnit (1 - q)) (fuel m n : ℕ) :
    QopAux (algebraMap R L q) (algebraMap R L u) fuel m n ∈ ReesRegComm R L u := by
  induction fuel generalizing m n with
  | zero => rw [QopAux]; exact dop_mem_reesRegComm q u n
  | succ fuel ih =>
    rw [QopAux]
    split_ifs with _
    · exact dop_mem_reesRegComm q u n
    · exact smul_commutator_mem_reesRegComm hq (ih _ _) (ih _ _)

/-- The primitive evaluator lies in the commutator filtration over the coefficient ring. -/
theorem qopPrim_mem_reesRegComm {q u : R} (hq : IsUnit (1 - q)) (m n : ℕ) :
    QopPrim (algebraMap R L q) (algebraMap R L u) m n ∈ ReesRegComm R L u :=
  qopAux_mem_reesRegComm hq m m n

/-- The slope operators lie in the commutator filtration over the coefficient ring: each of the
three branches of `Qop` is either a basic operator or a normalised commutator of primitive
evaluators. -/
theorem qop_mem_reesRegComm {q u : R} (hq : IsUnit (1 - q)) (m n : ℕ) :
    Qop (algebraMap R L q) (algebraMap R L u) m n ∈ ReesRegComm R L u := by
  rw [Qop]
  split_ifs
  · exact dop_mem_reesRegComm q u n
  · exact qopPrim_mem_reesRegComm hq m n
  · exact smul_commutator_mem_reesRegComm hq (qopPrim_mem_reesRegComm hq _ _)
      (qopPrim_mem_reesRegComm hq _ _)

end Qop

/-! ### Triangularity over the coefficient ring -/

section Triangular

variable {R : Type*} [CommRing R]

/-- Subtracting off its linear term in the generator `p_{m+1}` leaves a weighted homogeneous
polynomial of degree `m + 1` supported on the earlier generators. Only the coefficient ring is
needed, no division. -/
theorem sub_linear_mem_supported_ring {P : Lambda R} {m : ℕ}
    (hP : IsWeightedHomogeneous degWeight P (m + 1)) :
    P - C (coeff (Finsupp.single m 1) P) * X m ∈ supported R {i : ℕ | i < m} := by
  rw [mem_supported]
  intro i hi
  rw [Finset.mem_coe, mem_vars_iff_mem_support] at hi
  obtain ⟨d, hd, hid⟩ := hi
  rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_C_mul, coeff_X] at hd
  have hdne : d ≠ Finsupp.single m 1 := by
    rintro rfl
    simp at hd
  have hd' : coeff d P ≠ 0 := by simpa [Ne.symm hdne] using hd
  have hw : Finsupp.weight degWeight d = m + 1 := hP hd'
  rw [Finsupp.mem_support_iff] at hid
  have him : i ≤ m := le_of_weight_eq hw hid
  have hne : i ≠ m := by
    rintro rfl
    exact hid (by by_contra h; exact hdne (eq_single_of_weight_eq hw h))
  rw [Set.mem_ofPred_eq]
  omega

/-- A family of polynomials whose `m`-th member is a unit multiple of the generator `p_{m+1}` modulo
the earlier generators generates the whole ring of symmetric functions: the change of generators is
inverted one step at a time, multiplying only by inverses of the leading coefficients, which exist
in the coefficient ring because those coefficients are units. -/
theorem eq_top_of_triangular_isUnit (A : Subalgebra R (Lambda R)) (g : ℕ → Lambda R) (c : ℕ → R)
    (hgA : ∀ m, g m ∈ A) (hc : ∀ m, IsUnit (c m))
    (hg : ∀ m, g m - C (c m) * X m ∈ supported R {i : ℕ | i < m}) : A = ⊤ := by
  have hX : ∀ m : ℕ, (X m : Lambda R) ∈ A := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      have hsub : supported R {i : ℕ | i < m} ≤ A := by
        rw [supported_eq_adjoin_X]
        refine Algebra.adjoin_le ?_
        rintro p ⟨i, hi, rfl⟩
        exact ih i hi
      have h1 : C (c m) * X m ∈ A := by
        have h2 := A.sub_mem (hgA m) (hsub (hg m))
        rwa [sub_sub_cancel] at h2
      obtain ⟨d, hd⟩ := (hc m).exists_left_inv
      have h3 : (X m : Lambda R) = C d * (C (c m) * X m) := by
        rw [← mul_assoc, ← C_mul, hd, C_1, one_mul]
      rw [h3]
      refine A.mul_mem ?_ h1
      rw [← MvPolynomial.algebraMap_eq]
      exact A.algebraMap_mem _
  refine top_unique ?_
  rw [← MvPolynomial.adjoin_range_X (R := R) (σ := ℕ)]
  exact Algebra.adjoin_le (by rintro p ⟨i, rfl⟩; exact hX i)

/-- Weighted homogeneity descends along an injective coefficientwise inclusion. -/
theorem isWeightedHomogeneous_of_coeffInc {L : Type*} [CommRing L] [Algebra R L]
    (hinj : Function.Injective (algebraMap R L)) {g : Lambda R} {n : ℕ}
    (h : IsWeightedHomogeneous degWeight (coeffInc R L g) n) :
    IsWeightedHomogeneous degWeight g n := by
  intro d hd
  refine h (d := d) ?_
  rw [coeffInc_apply, MvPolynomial.coeff_map]
  exact fun hz => hd (hinj (by rw [hz, map_zero]))

end Triangular

/-! ### Specialisation of a slope homomorphism to multiplication -/

section Assemble

variable {R : Type*} [CommRing R] [Algebra ℚ R] {L : Type*} [Field L] [Algebra ℚ L]
  [Algebra R L] [IsScalarTower ℚ R L]

/-- The symmetric functions with coefficients in `R` whose image under `Θ` lies in the commutator
filtration over `R`; a subalgebra over `R`, because the filtration is an algebra over `R`. -/
def slopeCoeffPreimage (u : R) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) :
    Subalgebra R (Lambda R) where
  carrier := {f | Θ (coeffInc R L f) ∈ ReesRegComm R L u}
  mul_mem' hf hg := by
    rw [Set.mem_ofPred_eq, map_mul, map_mul]
    exact mul_mem_reesRegComm hf hg
  one_mem' := by
    rw [Set.mem_ofPred_eq, map_one, map_one]
    exact one_mem_reesRegComm u
  add_mem' hf hg := by
    rw [Set.mem_ofPred_eq, map_add, map_add]
    exact add_mem_reesRegComm hf hg
  zero_mem' := by
    rw [Set.mem_ofPred_eq, map_zero, map_zero]
    exact zero_mem_reesRegComm u
  algebraMap_mem' r := by
    rw [Set.mem_ofPred_eq, AlgHom.commutes, IsScalarTower.algebraMap_apply R L (Lambda L),
      AlgHom.commutes, Algebra.algebraMap_eq_smul_one, algebraMap_smul]
    exact smul_mem_reesRegComm r (one_mem_reesRegComm u)

omit [Algebra ℚ R] [Algebra ℚ L] [IsScalarTower ℚ R L] in
/-- Membership in the preimage subalgebra is membership of the image in the filtration over `R`. -/
theorem mem_slopeCoeffPreimage {u : R} {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    {f : Lambda R} : f ∈ slopeCoeffPreimage u Θ ↔ Θ (coeffInc R L f) ∈ ReesRegComm R L u := Iff.rfl

/-- A slope homomorphism takes every symmetric function with coefficients in `R` into the commutator
filtration over `R`. The axis generators go to slope operators, which lie in the filtration because
the basic operators do and the filtration is closed under normalised commutators; and they are a
triangular change of generators whose leading coefficients are units of `R`, so they generate the
whole ring of symmetric functions over `R`. -/
theorem mem_reesRegComm_of_isSlopeHom {a b : ℕ} {q u : R} (hq : IsUnit (1 - q))
    (hinj : Function.Injective (algebraMap R L)) (Uk : ℕ → Lambda R)
    (hUk : ∀ k, 0 < k →
      coeffInc R L (Uk k) = axisGen (algebraMap R L q * algebraMap R L u) k)
    (hUnit : ∀ m, IsUnit (coeff (Finsupp.single m 1) (Uk (m + 1))))
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b (algebraMap R L q) (algebraMap R L u) Θ) (f : Lambda R) :
    Θ (coeffInc R L f) ∈ ReesRegComm R L u := by
  have htop : slopeCoeffPreimage u Θ = ⊤ := by
    refine eq_top_of_triangular_isUnit _ (fun m => Uk (m + 1))
      (fun m => coeff (Finsupp.single m 1) (Uk (m + 1))) (fun m => ?_) hUnit fun m => ?_
    · rw [mem_slopeCoeffPreimage, hUk (m + 1) (Nat.succ_pos m), hΘ (m + 1) (Nat.succ_pos m)]
      exact qop_mem_reesRegComm hq _ _
    · refine sub_linear_mem_supported_ring (isWeightedHomogeneous_of_coeffInc hinj ?_)
      rw [hUk (m + 1) (Nat.succ_pos m)]
      exact isWeightedHomogeneous_axisGen _ _
  have hmem : f ∈ slopeCoeffPreimage u Θ := by rw [htop]; exact Algebra.mem_top
  exact mem_slopeCoeffPreimage.mp hmem

/-- Specialisation of a slope homomorphism to multiplication. Let `Θ` be a slope homomorphism at
`(a, b)`, with parameters drawn from a coefficient ring `R` carrying the specialisation `sp` that
sends the parameter to `1`. For every symmetric function `f` with coefficients in `R`, the operator
`Θ f` lies in the order filtration over `R` -- so its `ℏ`-expansion has no negative powers and its
coefficients survive the specialisation -- it carries symmetric functions with coefficients in `R`
to symmetric functions with coefficients in `R`, and after specialisation it is multiplication by
the specialisation of its own value on `1`. -/
@[hjo "prop_multiplication"]
theorem slopeHom_specialisation {F : Type*} [CommRing F] {a b : ℕ} {q u : R} (hq : IsUnit (1 - q))
    (hinj : Function.Injective (algebraMap R L)) (sp : R →+* F) (hsp : sp u = 1)
    (Uk : ℕ → Lambda R)
    (hUk : ∀ k, 0 < k →
      coeffInc R L (Uk k) = axisGen (algebraMap R L q * algebraMap R L u) k)
    (hUnit : ∀ m, IsUnit (coeff (Finsupp.single m 1) (Uk (m + 1))))
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b (algebraMap R L q) (algebraMap R L u) Θ) (f : Lambda R) :
    Θ (coeffInc R L f) ∈ ReesRegComm R L u ∧
      ∃ g₁ : Lambda R, Θ (coeffInc R L f) 1 = coeffInc R L g₁ ∧
        ∀ h : Lambda R, ∃ g : Lambda R,
          Θ (coeffInc R L f) (coeffInc R L h) = coeffInc R L g ∧
            MvPolynomial.map sp g = MvPolynomial.map sp g₁ * MvPolynomial.map sp h := by
  have hmem := mem_reesRegComm_of_isSlopeHom hq hinj Uk hUk hUnit hΘ f
  obtain ⟨g₁, hg₁⟩ := exists_coeffInc_apply_one_reesRegComm hmem
  exact ⟨hmem, g₁, hg₁,
    fun h => exists_map_eq_mul_of_mem_reesRegComm hinj sp hsp hmem hg₁ h⟩

end Assemble

/-! ### The setting is not degenerate

The specialisation is a homomorphism out of the coefficient ring, not out of the base field, and
that distinction is what keeps the statement of the previous section from collapsing: a
homomorphism out of a field carrying the parameter to `1` forces either the target to be the zero
ring or the parameter to equal `1`, and at `u = 1` the deformation parameter `ℏ = 1 - u` vanishes
together with the normalisation of every commutator. This section records that the data the
statement asks for is available with `ℏ ≠ 0` in the base field, that the filtration there contains
an operator which is not a multiplication operator -- so specialising to multiplication is a
conclusion with content -- and that the triangularity hypotheses on the axis generators are
satisfiable.
-/

namespace Witness

open HJO.ReesRegular.Model

/-- The second parameter of the witness, the constant `2`. -/
noncomputable def q : Coeff := 2

/-- The complement `1 - q = -1` of the second parameter is a unit of the coefficient ring, so the
normalisation of a commutator does not leave that ring. -/
theorem isUnit_one_sub_q : IsUnit (1 - q) := by
  rw [show (1 - q : Coeff) = -1 from by rw [q]; ring]
  exact isUnit_one.neg

/-- The specialisation data is available at a parameter that is not `1`: the coefficient ring is the
polynomials in `u` over `ℚ`, the base field the rational functions in `u`, the specialisation is
evaluation at `u = 1` into the nontrivial ring `ℚ`, and the deformation parameter `ℏ = 1 - u` is
nonzero in the base field. -/
theorem nondegenerate_data :
    Function.Injective (algebraMap Coeff Base) ∧ sp u = 1 ∧ Nontrivial ℚ ∧ IsUnit (1 - q) ∧
      u ≠ 1 ∧ algebraMap Coeff Base u ≠ 1 ∧ (1 : Base) - algebraMap Coeff Base u ≠ 0 :=
  ⟨algebraMap_injective, sp_u, inferInstance, isUnit_one_sub_q, u_ne_one, algebraMap_u_ne_one,
    one_sub_algebraMap_u_ne_zero⟩

/-- Multiplication by a symmetric function with polynomial coefficients plus `ℏ` times one partial
derivative lies in the commutator filtration over the coefficient ring: its expansion has
multiplication in degree zero, of differential order zero, and one partial derivative in degree one,
of differential order one. -/
theorem op_mem_reesRegComm (g : Lambda Coeff) : op g ∈ ReesRegComm Coeff Base u := by
  refine ⟨opCoeff g, fun j => ?_, fun f => ⟨2, fun j hj => ?_, ?_⟩⟩
  · match j with
    | 0 => exact hasDiffOrderReg_mulLeft g
    | 1 => exact ⟨hasDiffOrder_pderivEnd 0, fun _ hx => pderivEnd_mem_regSub 0 hx⟩
    | (n + 2) => exact hasDiffOrderReg_zero _
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by omega⟩
    simp [opCoeff]
  · rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [op, opCoeff]

/-- The commutator filtration over the coefficient ring is strictly larger than the multiplication
operators at a parameter where `ℏ = 1 - u` is nonzero, so an operator of the filtration becoming
multiplication after specialisation is a genuine conclusion rather than an identity. -/
theorem exists_mem_reesRegComm_ne_mulLeft :
    ∃ P ∈ ReesRegComm Coeff Base u, ∀ h : Lambda Base, P ≠ LinearMap.mulLeft Base h :=
  ⟨op 0, op_mem_reesRegComm 0, fun h => op_ne_mulLeft 0 h⟩

/-- The reciprocal of the parameter is not defined over the coefficient ring. -/
theorem inv_algebraMap_u_notMem_regSub :
    MvPolynomial.C (algebraMap Coeff Base u)⁻¹ ∉ regSub Coeff Base := by
  intro hmem
  obtain ⟨g, hg⟩ := mem_regSub.mp hmem
  have hcoeff := congrArg (fun p : Lambda Base => MvPolynomial.coeff 0 p) hg
  simp only [coeffInc_apply, MvPolynomial.coeff_map, MvPolynomial.coeff_zero_C] at hcoeff
  have hu0 : algebraMap Coeff Base u ≠ 0 := fun h =>
    Polynomial.X_ne_zero (R := ℚ) (algebraMap_injective (by rw [map_zero]; exact h))
  have hone : algebraMap Coeff Base (MvPolynomial.coeff 0 g * u) = 1 := by
    rw [map_mul, hcoeff, inv_mul_cancel₀ hu0]
  have hmul : MvPolynomial.coeff 0 g * u = 1 := algebraMap_injective (by rw [hone, map_one])
  exact Polynomial.not_isUnit_X (R := ℚ)
    (isUnit_iff_exists_inv.mpr ⟨MvPolynomial.coeff 0 g, by rw [mul_comm]; exact hmul⟩)

/-- The filtration is a proper subset of the operators: an operator of the filtration carries
symmetric functions with coefficients in the coefficient ring to symmetric functions with
coefficients in that ring, and `1` is such a function, so multiplication by a scalar of the base
field that is not defined over the coefficient ring lies outside. Membership in the filtration is
therefore a real restriction. -/
theorem exists_notMem_reesRegComm :
    ∃ P : Module.End Base (Lambda Base), P ∉ ReesRegComm Coeff Base u := by
  refine ⟨LinearMap.mulLeft Base (MvPolynomial.C (algebraMap Coeff Base u)⁻¹), fun hP => ?_⟩
  refine inv_algebraMap_u_notMem_regSub ?_
  simpa using apply_mem_regSub_of_mem_reesRegComm hP (one_mem_regSub (R := Coeff) (L := Base))

/-- The elementary symmetric function of degree zero is `1`. -/
theorem elemSymm_zero {L : Type*} [Field L] [Algebra ℚ L] : elemSymm L 0 = 1 := by
  rw [elemSymm]

/-- The elementary symmetric function of degree one is the first power sum. -/
theorem elemSymm_one {L : Type*} [Field L] [Algebra ℚ L] : elemSymm L 1 = MvPolynomial.X 0 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, elemSymm]
  simp [powerSum, elemSymm_zero]

/-- The basic operator of index zero fixes `1`, the displacement of a constant being that
constant. -/
theorem dop_zero_apply_one {L : Type*} [Field L] [Algebra ℚ L] (q u : L) :
    Dop q u 0 (1 : Lambda L) = 1 := by
  rw [dop_apply_eq_sum q u 0 1 (N := 1) (by rw [map_one]; simp), Finset.sum_range_one,
    dopPiece_apply, map_one, elemSymm_zero]
  simp

/-- The value of the basic operator of index zero on the first power sum: the displaced generator
contributes the elementary symmetric function of the next degree, weighted by the scalar
`(1 - q) * (1 - u)` of the displacement. -/
theorem dop_zero_apply_X {L : Type*} [Field L] [Algebra ℚ L] (q u : L) :
    Dop q u 0 (MvPolynomial.X 0 : Lambda L)
      = MvPolynomial.X 0 * (1 - MvPolynomial.C ((1 - q) * (1 - u))) := by
  have hdeg : (plethShift q u (MvPolynomial.X 0 : Lambda L)).natDegree < 2 := by
    rw [plethShift_X]
    have hle : (Polynomial.C (MvPolynomial.X 0 : Lambda L) +
        Polynomial.C (MvPolynomial.C (shiftScalar q u 0)) * Polynomial.X ^ (0 + 1)).natDegree
          ≤ 1 := by compute_degree
    omega
  rw [dop_apply_eq_sum q u 0 (MvPolynomial.X 0) hdeg, Finset.sum_range_succ, Finset.sum_range_one,
    dopPiece_apply, dopPiece_apply, plethShift_X, elemSymm_zero, elemSymm_one]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, shiftScalar]
  ring_nf
  simp [mul_comm, mul_left_comm]
  ring

/-- The basic operator of index zero is not a multiplication operator wherever the deformation
parameter is nonzero: it fixes `1`, so a multiplication operator agreeing with it would be the
identity, while its value on the first power sum picks up the extra term of the displacement. So a
basic operator is a genuine differential operator and the filtration statement about it has
content. -/
theorem dop_zero_ne_mulLeft {L : Type*} [Field L] [Algebra ℚ L] {q u : L} (hq : 1 - q ≠ 0)
    (hu : 1 - u ≠ 0) (h : Lambda L) : Dop q u 0 ≠ LinearMap.mulLeft L h := by
  intro hop
  have h1 : h = 1 := by
    have := congrArg (fun P : Module.End L (Lambda L) => P 1) hop
    rw [dop_zero_apply_one] at this
    simpa using this.symm
  have h2 := congrArg (fun P : Module.End L (Lambda L) => P (MvPolynomial.X 0)) hop
  rw [dop_zero_apply_X] at h2
  simp only [h1, LinearMap.mulLeft_apply, one_mul] at h2
  have h3 : (MvPolynomial.X 0 : Lambda L) * MvPolynomial.C ((1 - q) * (1 - u)) = 0 := by
    have := h2
    rw [mul_sub, mul_one, sub_eq_self] at this
    exact this
  rcases mul_eq_zero.mp h3 with hz | hz
  · exact MvPolynomial.X_ne_zero (0 : ℕ) hz
  · rcases mul_eq_zero.mp (MvPolynomial.C_eq_zero.mp hz) with hz' | hz'
    · exact hq hz'
    · exact hu hz'

/-- The triangularity hypotheses on the axis generators are satisfiable: taking the coefficient ring
to be the base field itself, the axis generators represent themselves, and the coefficient of `p_k`
in `U_k` is nonzero -- hence a unit -- at a parameter that is nonzero and not a root of unity.

The hypothesis on the powers is the corrected one and cannot be relaxed to `v ≠ 0, 1`: the axis
alphabet attaches `v ^ (-k) - 1` to `p_k`, which vanishes at every `k`-th root of unity, so at
`v = -1` no axis generator involves `p₂` and no such family exists. This lemma is what keeps the
hypotheses of `slopeHom_specialisation` from being vacuous; it is instantiated at the parameters of
the power-series model in `HJO.PhiMul.Witness.exists_axisGen_witness`, where the geometric sums are
units of the coefficient ring rather than merely nonzero. -/
theorem exists_axisGen_witness {L : Type*} [Field L] [Algebra ℚ L] {v : L}
    (hv0 : v ≠ 0) (hv1 : ∀ j : ℕ, v ^ (j + 1) ≠ 1) :
    ∃ Uk : ℕ → Lambda L, (∀ k, 0 < k → coeffInc L L (Uk k) = axisGen v k) ∧
      ∀ m, IsUnit (coeff (Finsupp.single m 1) (Uk (m + 1))) := by
  have hchar : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  refine ⟨fun k => axisGen v k, fun k _ => ?_, fun m => ?_⟩
  · rw [coeffInc_apply, Algebra.algebraMap_self, MvPolynomial.map_id]
  · refine isUnit_iff_ne_zero.mpr ?_
    have h := (coeff_single_axisGen_ne_zero hv0 hv1 (k := m + 1) (Nat.le_add_left 1 m)).2
    rwa [Nat.add_sub_cancel] at h

end Witness

end HJO.DopCommutator
