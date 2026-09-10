/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.DopRees
public import HJO.Symmetric.ReesSpecial
public import HJO.Symmetric.UkRegular

/-! # Specialisation of a slope homomorphism to multiplication

The order filtration is an algebra: it contains the identity and is stable under sums, scalars
and composition, the `ℏ ^ j`-coefficient of a composite being the antidiagonal sum of the
coefficients of the factors. Every slope operator is built from the basic operators by iterated
normalised commutators, hence lies in the filtration, and the axis generators are a triangular
change of generators of the ring of symmetric functions, so the image of a slope homomorphism
lands in the filtration on the nose. Read through a ring homomorphism carrying the parameter to
`1`, such an operator is multiplication by its value on `1`. The last section measures what that
specialisation costs: the slope recursion divides by `(1 - q) * (1 - u)`, so the parameter cannot
be set to `1` inside the base field without collapsing the slope operators, and a ring
homomorphism out of a field cannot set it to `1` anywhere else.
-/

@[expose] public section

open Finset

namespace HJO.Multiplication

open MvPolynomial HJO.Sym HJO.ReesClosed HJO.DopRees HJO.ReesSpecial
open HJO.UkRegular

/-! ### Composition and the differential-order filtration -/

section DiffOrderMul

variable {K : Type*} [CommRing K]

/-- Composing with an iterated partial derivative on the left raises the differential order by at
most the number of derivatives. -/
theorem pderivProd_mul_mem {n : ℕ} {P : Module.End K (Lambda K)} (l : List ℕ)
    (hP : P ∈ diffOrder K n) : pderivProd K l * P ∈ diffOrder K (n + l.length) := by
  induction l with
  | nil => simpa using hP
  | cons i t ih =>
      rw [pderivProd_cons, mul_assoc]
      refine diffOrder_mono ?_ (pderivEnd_mul_mem i ih)
      simp only [List.length_cons]
      omega

/-- Differential orders add under composition: an operator of order `r` composed with one of order
`s` has order at most `r + s`. -/
theorem mul_mem_diffOrder {r s : ℕ} {P Q : Module.End K (Lambda K)} (hP : P ∈ diffOrder K r)
    (hQ : Q ∈ diffOrder K s) : P * Q ∈ diffOrder K (r + s) := by
  refine Submodule.span_induction₂ (p := fun P Q _ _ => P * Q ∈ diffOrder K (r + s))
    ?_ (by simp) (by simp) ?_ ?_ ?_ ?_ hP hQ
  · rintro A B ⟨f, l, hl, rfl⟩ ⟨g, m, hm, rfl⟩
    rw [mul_assoc]
    exact diffOrder_mono (show 0 + m.length + l.length ≤ r + s by omega)
      (mulLeft_mul_mem f (pderivProd_mul_mem l
        (mul_pderivProd_mem (mulLeft_mem_diffOrder_zero g) m)))
  · intro x y z _ _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro x y z _ _ _ hy hz
    rw [mul_add]
    exact Submodule.add_mem _ hy hz
  · intro a x y _ _ h
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ h
  · intro a x y _ _ h
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ h

end DiffOrderMul

/-! ### The order filtration is an algebra -/

section ReesAlgebra

variable {L : Type*} [Field L]

/-- The identity operator lies in the order filtration: it is multiplication by `1`, of
differential order zero. -/
theorem one_mem_rees {u : L} : (1 : Module.End L (Lambda L)) ∈ Rees u := by
  refine mem_rees_of_diffOrderAtMost_zero ?_
  have h : (1 : Module.End L (Lambda L)) = LinearMap.mulLeft L (1 : Lambda L) :=
    LinearMap.ext fun x => by simp
  rw [h, hasDiffOrderAtMost_iff_mem]
  exact mulLeft_mem_diffOrder_zero _

/-- The order filtration is closed under addition: the expansions may be added coefficientwise. -/
theorem add_mem_rees {u : L} {P Q : Module.End L (Lambda L)} (hP : P ∈ Rees u)
    (hQ : Q ∈ Rees u) : P + Q ∈ Rees u := by
  obtain ⟨Pc, hPord, hPsum⟩ := hP
  obtain ⟨Qc, hQord, hQsum⟩ := hQ
  refine ⟨fun j => Pc j + Qc j, fun j => Submodule.add_mem _ (hPord j) (hQord j), fun f => ?_⟩
  obtain ⟨N₁, hz₁, hs₁⟩ := hPsum f
  obtain ⟨N₂, hz₂, hs₂⟩ := hQsum f
  refine ⟨max N₁ N₂, fun j hj => ?_, ?_⟩
  · rw [LinearMap.add_apply, hz₁ j (le_trans (le_max_left N₁ N₂) hj),
      hz₂ j (le_trans (le_max_right N₁ N₂) hj), add_zero]
  · rw [LinearMap.add_apply, expansion_extend (le_max_left N₁ N₂) hz₁ hs₁,
      expansion_extend (le_max_right N₁ N₂) hz₂ hs₂, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [LinearMap.add_apply, smul_add]

/-- The order filtration is closed under scalar multiplication. -/
theorem smul_mem_rees {u : L} (c : L) {P : Module.End L (Lambda L)} (hP : P ∈ Rees u) :
    c • P ∈ Rees u := by
  obtain ⟨Pc, hord, hsum⟩ := hP
  refine ⟨fun j => c • Pc j, fun j => Submodule.smul_mem _ _ (hord j), fun f => ?_⟩
  obtain ⟨N, hz, hs⟩ := hsum f
  refine ⟨N, fun j hj => ?_, ?_⟩
  · rw [LinearMap.smul_apply, hz j hj, smul_zero]
  · rw [LinearMap.smul_apply, hs, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, smul_comm]

/-- The order filtration is closed under composition: the `ℏ ^ m`-coefficient of a composite is
the sum of the products of the coefficients over the antidiagonal of `m`, and a product of
operators of differential orders `r` and `s` has order at most `r + s`. -/
theorem mul_mem_rees {u : L} {P Q : Module.End L (Lambda L)} (hP : P ∈ Rees u)
    (hQ : Q ∈ Rees u) : P * Q ∈ Rees u := by
  classical
  obtain ⟨Pc, hPord, hPsum⟩ := hP
  obtain ⟨Qc, hQord, hQsum⟩ := hQ
  choose np hnpz hnpsum using hPsum
  choose nq hnqz hnqsum using hQsum
  refine ⟨fun m => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, Pc p.1 * Qc p.2, ?_, ?_⟩
  · intro m
    rw [hasDiffOrderAtMost_iff_mem]
    refine Submodule.sum_mem _ fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    exact diffOrder_mono (le_of_eq hp) (mul_mem_diffOrder (hPord p.1) (hQord p.2))
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
        = ∑ i ∈ range (K₀ + 1), (1 - u) ^ i • Pc i (Qc j f) := by
      intro j _
      rcases lt_or_ge j (nq f) with hj | hj
      · exact expansion_extend (by have := h3 j hj; omega) (hnpz (Qc j f)) (hnpsum (Qc j f))
      · rw [hnqz f j hj]
        simp
    have hQ0 : Q f = ∑ j ∈ range (K₀ + 1), (1 - u) ^ j • Qc j f :=
      expansion_extend (by omega) (hnqz f) (hnqsum f)
    have hA : (P * Q) f = ∑ i ∈ range (K₀ + 1), ∑ j ∈ range (K₀ + 1),
        (1 - u) ^ (i + j) • ((Pc i * Qc j) f) := by
      rw [Module.End.mul_apply, hQ0, map_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [map_smul, hPQ j hj, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← pow_add, add_comm j i, Module.End.mul_apply]
    have hsq : ∑ i ∈ range (K₀ + 1), ∑ j ∈ range (K₀ + 1),
          (1 - u) ^ (i + j) • ((Pc i * Qc j) f)
        = ∑ n ∈ range (2 * (K₀ + 1)), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
            (1 - u) ^ (p.1 + p.2) • ((Pc p.1 * Qc p.2) f) := by
      rw [← Finset.sum_product']
      exact (sum_antidiagonal_eq_sum_product
        (fun i j => (1 - u) ^ (i + j) • ((Pc i * Qc j) f)) (K₀ + 1)
        fun i j hij => by rw [hzero i j hij, smul_zero]).symm
    have hin : ∀ n : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          (1 - u) ^ (p.1 + p.2) • ((Pc p.1 * Qc p.2) f)
        = (1 - u) ^ n • ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, Pc p.1 * Qc p.2) f) := by
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

end ReesAlgebra

/-! ### The slope operators lie in the order filtration -/

section Qop

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- Every stage of the fuelled recursion computing the slope operators lies in the order
filtration: the base case is a basic operator, and the recursive case is a normalised
commutator. -/
theorem qopAux_mem_rees (q u : L) (fuel m n : ℕ) : QopAux q u fuel m n ∈ Rees u := by
  induction fuel generalizing m n with
  | zero => rw [QopAux]; exact dop_mem_rees q u n
  | succ fuel ih =>
      rw [QopAux]
      split_ifs with _
      · exact dop_mem_rees q u n
      · exact smul_commutator_mem_rees q u (ih _ _) (ih _ _)

/-- The primitive evaluator lies in the order filtration. -/
theorem qopPrim_mem_rees (q u : L) (m n : ℕ) : QopPrim q u m n ∈ Rees u :=
  qopAux_mem_rees q u m m n

/-- The slope operators lie in the order filtration: each of the three branches of `Qop` is
either a basic operator or a normalised commutator of primitive evaluators. -/
theorem qop_mem_rees (q u : L) (m n : ℕ) : Qop q u m n ∈ Rees u := by
  rw [Qop]
  split_ifs
  · exact dop_mem_rees q u n
  · exact qopPrim_mem_rees q u m n
  · exact smul_commutator_mem_rees q u (qopPrim_mem_rees q u _ _) (qopPrim_mem_rees q u _ _)

end Qop

/-! ### The axis generators are a triangular change of generators -/

section Triangular

/-- The weight assigning `k` to the generator `p_k`, that is, `i + 1` to the generator of
index `i`. -/
def degWeight : ℕ → ℕ := fun i => i + 1

@[simp] theorem degWeight_apply (i : ℕ) : degWeight i = i + 1 := rfl

/-- A monomial of weight zero is the trivial monomial. -/
theorem eq_zero_of_weight_eq_zero {d : ℕ →₀ ℕ} (hd : Finsupp.weight degWeight d = 0) : d = 0 := by
  ext i
  have h := Finsupp.le_weight degWeight (s := i) (by simp) d
  have hi : d i = 0 := by omega
  simpa using hi

/-- A monomial of weight `m + 1` involving the generator `p_{m+1}` is that generator: the
generator already exhausts the weight. -/
theorem eq_single_of_weight_eq {m : ℕ} {d : ℕ →₀ ℕ} (hd : Finsupp.weight degWeight d = m + 1)
    (hm : d m ≠ 0) : d = Finsupp.single m 1 := by
  have h := Finsupp.weight_sub_single_add (w := degWeight) hm
  have h0 : Finsupp.weight degWeight (d - Finsupp.single m 1) = 0 := by
    rw [hd, degWeight_apply] at h
    omega
  have hcancel := Finsupp.sub_add_single_one_cancel hm
  rw [eq_zero_of_weight_eq_zero h0, zero_add] at hcancel
  exact hcancel.symm

/-- A generator occurring in a monomial of weight `m + 1` has index at most `m`. -/
theorem le_of_weight_eq {m i : ℕ} {d : ℕ →₀ ℕ} (hd : Finsupp.weight degWeight d = m + 1)
    (hi : d i ≠ 0) : i ≤ m := by
  have h := Finsupp.le_weight_of_ne_zero' degWeight hi
  rw [hd, degWeight_apply] at h
  omega

/-- Scaling the alphabet multiplies the coefficient of a monomial by the corresponding power
of the scalar, so it introduces no new monomials. It can remove monomials, for example at scale
zero; if the scalar is a unit, it preserves the support. -/
theorem coeff_plethScale {K : Type*} [CommRing K] (c : K) (d : ℕ →₀ ℕ) (f : Lambda K) :
    coeff d (plethScale c f) = c ^ (∑ i ∈ d.support, (i + 1) * d i) * coeff d f := by
  rw [plethScale, coeff_diagScale, ← Finset.prod_pow_eq_pow_sum]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul]

/-- The complete homogeneous function `h_n` is weighted homogeneous of degree `n`, the generator
`p_k` weighing `k`. -/
theorem isWeightedHomogeneous_completeHomog (K : Type*) [CommRing K] [Algebra ℚ K] (n : ℕ) :
    IsWeightedHomogeneous degWeight (completeHomog K n) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      rw [completeHomog_zero]
      exact isWeightedHomogeneous_one K degWeight
    | m + 1 =>
      rw [completeHomog_succ]
      refine IsWeightedHomogeneous.C_mul (IsWeightedHomogeneous.sum _ _ _ fun k hk => ?_) _
      simp only [Finset.mem_range] at hk
      have hX : powerSum K (k + 1) = (X k : Lambda K) := by simp [powerSum]
      have hmul := (isWeightedHomogeneous_X (R := K) degWeight k).mul (ih (m - k) (by omega))
      rw [degWeight_apply, show k + 1 + (m - k) = m + 1 from by omega] at hmul
      rwa [hX]

/-- The axis generator `U_k` is weighted homogeneous of degree `k`: diagonal substitution
and multiplication by a constant introduce no new monomials, so every surviving monomial
retains degree `k`. -/
theorem isWeightedHomogeneous_axisGen {L : Type*} [Field L] [Algebra ℚ L] (v : L) (k : ℕ) :
    IsWeightedHomogeneous degWeight (axisGen v k) k := by
  refine IsWeightedHomogeneous.C_mul (fun d hd => ?_) _
  refine isWeightedHomogeneous_completeHomog L k ?_
  rw [plethAxis_eq_diagScale, coeff_diagScale] at hd
  exact right_ne_zero_of_mul hd

/-- Subtracting off its linear term in the generator `p_{m+1}` leaves a weighted homogeneous
polynomial of degree `m + 1` supported on the earlier generators. -/
theorem sub_linear_mem_supported {L : Type*} [Field L] {P : Lambda L} {m : ℕ}
    (hP : IsWeightedHomogeneous degWeight P (m + 1)) :
    P - C (coeff (Finsupp.single m 1) P) * X m ∈ supported L {i : ℕ | i < m} := by
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

/-- A family of polynomials whose `m`-th member is a nonzero multiple of the generator `p_{m+1}`
modulo the earlier generators generates the whole ring of symmetric functions: the change of
generators is inverted one step at a time, dividing only by the leading coefficients. -/
theorem eq_top_of_triangular {L : Type*} [Field L] (A : Subalgebra L (Lambda L))
    (g : ℕ → Lambda L) (c : ℕ → L) (hgA : ∀ m, g m ∈ A) (hc : ∀ m, c m ≠ 0)
    (hg : ∀ m, g m - C (c m) * X m ∈ supported L {i : ℕ | i < m}) : A = ⊤ := by
  have hX : ∀ m : ℕ, (X m : Lambda L) ∈ A := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      have hsub : supported L {i : ℕ | i < m} ≤ A := by
        rw [supported_eq_adjoin_X]
        refine Algebra.adjoin_le ?_
        rintro p ⟨i, hi, rfl⟩
        exact ih i hi
      have h1 : C (c m) * X m ∈ A := by
        have h2 := A.sub_mem (hgA m) (hsub (hg m))
        rwa [sub_sub_cancel] at h2
      have h3 : (X m : Lambda L) = C (c m)⁻¹ * (C (c m) * X m) := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (hc m), C_1, one_mul]
      rw [h3]
      refine A.mul_mem ?_ h1
      rw [← MvPolynomial.algebraMap_eq]
      exact A.algebraMap_mem _
  refine top_unique ?_
  rw [← MvPolynomial.adjoin_range_X (R := L) (σ := ℕ)]
  exact Algebra.adjoin_le (by rintro p ⟨i, rfl⟩; exact hX i)

/-- A subalgebra containing every axis generator at a parameter that is nonzero and not a root of
unity is the whole ring of symmetric functions, the coefficient of `p_k` in `U_k` being nonzero
there. The condition on the powers is not decoration: at `v = -1` the axis generators involve no
`p₂`, so they generate a proper subalgebra. -/
theorem eq_top_of_axisGen_mem {L : Type*} [Field L] [Algebra ℚ L] {v : L} (hv0 : v ≠ 0)
    (hv1 : ∀ j : ℕ, v ^ (j + 1) ≠ 1) (A : Subalgebra L (Lambda L))
    (hA : ∀ k : ℕ, 0 < k → axisGen v k ∈ A) :
    A = ⊤ := by
  have hchar : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  refine eq_top_of_triangular A (fun m => axisGen v (m + 1))
    (fun m => coeff (Finsupp.single m 1) (axisGen v (m + 1)))
    (fun m => hA (m + 1) (Nat.succ_pos m)) (fun m => ?_)
    (fun m => sub_linear_mem_supported (isWeightedHomogeneous_axisGen v (m + 1)))
  have h := (coeff_single_axisGen_ne_zero hv0 hv1 (k := m + 1) (Nat.le_add_left 1 m)).2
  rwa [Nat.add_sub_cancel] at h

end Triangular

/-! ### The order filtration read through a specialisation -/

section Specialisation

variable {L : Type*} [Field L] {F : Type*} [CommRing F]

/-- An element of the order filtration read through a ring homomorphism sending `u` to `1`: the
`spec`-image of `P g` is the `spec`-image of `P 1` times that of `g`, so the specialised operator
is multiplication by the specialised value on `1`. The terms of the expansion in `1 - u` with
positive index die under `spec`, and the constant coefficient is a multiplication operator. -/
theorem map_apply_eq_mul_of_mem_Rees (spec : L →+* F) {u : L} (hspec : spec u = 1)
    {P : Module.End L (Lambda L)} (hP : P ∈ Rees u) (g : Lambda L) :
    MvPolynomial.map spec (P g)
      = MvPolynomial.map spec (P 1) * MvPolynomial.map spec g := by
  obtain ⟨Q, hQord, hQsum⟩ := hP
  obtain ⟨c, hc⟩ := exists_mulLeft_of_hasDiffOrderAtMost_zero (hQord 0)
  have key : ∀ f : Lambda L, MvPolynomial.map spec (P f)
      = MvPolynomial.map spec c * MvPolynomial.map spec f := by
    intro f
    obtain ⟨N, hN, hPf⟩ := hQsum f
    have hzero : ∀ i : ℕ, MvPolynomial.map spec ((1 - u) ^ (i + 1) • Q (i + 1) f) = 0 := by
      intro i
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_pow, map_sub, map_one,
        hspec, sub_self, zero_pow (Nat.succ_ne_zero i), MvPolynomial.C_0, zero_mul]
    have h0 : MvPolynomial.map spec (P f) = MvPolynomial.map spec (Q 0 f) := by
      rcases N with _ | M
      · rw [hPf, hN 0 le_rfl]
        simp
      · rw [hPf, map_sum, Finset.sum_range_succ',
          Finset.sum_eq_zero (s := range M) fun i _ => hzero i, zero_add, pow_zero, one_smul]
    rw [h0, hc]
    simp
  rw [key g, key 1]
  simp

end Specialisation

/-! ### Specialisation of a slope homomorphism -/

section Assemble

variable {L : Type*} [Field L]

/-- The symmetric functions whose image under `Θ` lies in the order filtration; a subalgebra,
because the filtration is one. -/
def slopePreimage (u : L) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) :
    Subalgebra L (Lambda L) where
  carrier := {f | Θ f ∈ Rees u}
  mul_mem' hf hg := by
    rw [Set.mem_ofPred_eq, map_mul]
    exact mul_mem_rees hf hg
  one_mem' := by
    rw [Set.mem_ofPred_eq, map_one]
    exact one_mem_rees
  add_mem' hf hg := by
    rw [Set.mem_ofPred_eq, map_add]
    exact add_mem_rees hf hg
  zero_mem' := by
    rw [Set.mem_ofPred_eq, map_zero]
    exact zero_mem_rees u
  algebraMap_mem' r := by
    rw [Set.mem_ofPred_eq, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact smul_mem_rees r one_mem_rees

/-- Membership in the preimage subalgebra is membership of the image in the order filtration. -/
theorem mem_slopePreimage {u : L} {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} {f : Lambda L} :
    f ∈ slopePreimage u Θ ↔ Θ f ∈ Rees u := Iff.rfl

variable [Algebra ℚ L]

/-- A slope homomorphism takes every symmetric function into the order filtration: the axis
generators go to slope operators, which lie in the filtration, and they generate the whole ring
because the coefficient of `p_k` in `U_k` is nonzero. -/
theorem mem_rees_of_isSlopeHom {a b : ℕ} {q u : L} (hv0 : q * u ≠ 0)
    (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) (f : Lambda L) :
    Θ f ∈ Rees u := by
  have htop : slopePreimage u Θ = ⊤ :=
    eq_top_of_axisGen_mem hv0 hv1 _ fun k hk => by
      rw [mem_slopePreimage, hΘ k hk]
      exact qop_mem_rees q u (a * k) (b * k)
  have hmem : f ∈ slopePreimage u Θ := by rw [htop]; exact Algebra.mem_top
  exact mem_slopePreimage.mp hmem

/-- Read through a ring homomorphism sending `u` to `1`, the operator attached to `f` by a slope
homomorphism is multiplication by its own value on `1`: it lies in the order filtration, and the
specialisation kills every term of the expansion in `1 - u` above the constant one. -/
theorem slopeHom_map_apply {a b : ℕ} {q u : L} {F : Type*} [CommRing F] (spec : L →+* F)
    (hspec : spec u = 1) (hv0 : q * u ≠ 0) (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) (f g : Lambda L) :
    MvPolynomial.map spec (Θ f g)
      = MvPolynomial.map spec (Θ f 1) * MvPolynomial.map spec g :=
  map_apply_eq_mul_of_mem_Rees spec hspec (mem_rees_of_isSlopeHom hv0 hv1 hΘ f) g

/-- The equation `u = 1` in the base field gives the same conclusion in the sharper form of an
identity of operators. -/
theorem slopeHom_eq_mulLeft {a b : ℕ} {q u : L} (hu : u = 1) (hv0 : q * u ≠ 0)
    (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) (f : Lambda L) :
    Θ f = LinearMap.mulLeft L (Θ f 1) :=
  eq_mulLeft_of_mem_Rees hu (mem_rees_of_isSlopeHom hv0 hv1 hΘ f)

/-- The pointwise form of the previous statement: the operator attached to `f` sends `g` to
`(Θ f 1) * g`, so evaluating a composite on `1` is a product of values. -/
theorem slopeHom_apply {a b : ℕ} {q u : L} (hu : u = 1) (hv0 : q * u ≠ 0)
    (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) (f g : Lambda L) :
    Θ f g = Θ f 1 * g :=
  apply_eq_mul_of_mem_Rees hu (mem_rees_of_isSlopeHom hv0 hv1 hΘ f) g

end Assemble

/-! ### What the equation `u = 1` costs

Setting the parameter to `1` inside the base field is not a harmless normalisation: the slope
recursion divides by `(1 - q) * (1 - u)`, so the normalisation vanishes there and every slope
operator of first slope at least two with it. A slope homomorphism at `(a, b)` with `2 ≤ a` is
then a scalar multiple of the identity. Carrying the specialisation as a ring homomorphism does
not avoid this, since a ring homomorphism out of a field is injective unless its target is
trivial.
-/

section Degeneracy

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- A ring homomorphism out of a field with `spec u = 1` already forces `u = 1`, unless its target
is the trivial ring: the kernel is an ideal of a field, so it is trivial or everything. -/
theorem eq_one_of_map_eq_one {F : Type*} [CommRing F] [Nontrivial F] (spec : L →+* F) {u : L}
    (hspec : spec u = 1) : u = 1 := by
  by_contra h
  have hne : u - 1 ≠ 0 := sub_ne_zero_of_ne h
  have hz : spec (u - 1) = 0 := by rw [map_sub, hspec, map_one, sub_self]
  have h1 : (1 : F) = 0 := by
    rw [← map_one spec, ← mul_inv_cancel₀ hne, map_mul, hz, zero_mul]
  exact one_ne_zero h1

/-- At `u = 1` the normalisation `((1 - q) * (1 - u))⁻¹` of the slope recursion is zero, so every
slope operator whose first slope is at least two is the zero operator. -/
theorem qop_eq_zero (q : L) {u : L} (hu : u = 1) {m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    Qop q u m n = 0 := by
  by_cases h : Nat.Coprime m n
  · rw [qop_eq_qopPrim q u h, qopPrim_of_one_lt q u n (by omega), hu, sub_self, mul_zero,
      inv_zero, zero_smul]
  · rw [qop_of_not_coprime q u (by omega) h, hu, sub_self, mul_zero, inv_zero, zero_smul]

/-- Hence at `u = 1` a slope homomorphism at `(a, b)` with `2 ≤ a` kills every axis generator. -/
theorem isSlopeHom_axisGen_eq_zero {a b : ℕ} (ha : 2 ≤ a) {q u : L} (hu : u = 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) {k : ℕ}
    (hk : 0 < k) : Θ (axisGen (q * u) k) = 0 := by
  have hk1 : 1 ≤ k := hk
  have h1 : a * 1 ≤ a * k := Nat.mul_le_mul (le_refl a) hk1
  rw [mul_one] at h1
  rw [hΘ k hk]
  exact qop_eq_zero q hu (le_trans ha h1) _

/-- The symmetric functions that `Θ` sends to a scalar multiple of the identity; a subalgebra,
since the scalar operators form one. -/
def scalarPreimage (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) : Subalgebra L (Lambda L) where
  carrier := {f | ∃ c : L, Θ f = c • 1}
  mul_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, by rw [map_mul, hc, hd, smul_mul_assoc, one_mul, smul_smul]⟩
  one_mem' := ⟨1, by rw [map_one, one_smul]⟩
  add_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [map_add, hc, hd, add_smul]⟩
  zero_mem' := ⟨0, by rw [map_zero, zero_smul]⟩
  algebraMap_mem' r := ⟨r, by rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]⟩

/-- The degeneracy in full: at `u = 1` the axis generators are killed and they generate the ring,
so a slope homomorphism at `(a, b)` with `2 ≤ a` is a scalar multiple of the identity on every
symmetric function and records nothing about the slope. -/
theorem exists_smul_one_of_isSlopeHom {a b : ℕ} (ha : 2 ≤ a) {q u : L} (hu : u = 1)
    (hv0 : q * u ≠ 0) (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) (f : Lambda L) :
    ∃ c : L, Θ f = c • 1 := by
  have htop : scalarPreimage Θ = ⊤ :=
    eq_top_of_axisGen_mem hv0 hv1 _ fun k hk =>
      ⟨0, by rw [isSlopeHom_axisGen_eq_zero ha hu hΘ hk, zero_smul]⟩
  have hmem : f ∈ scalarPreimage Θ := by rw [htop]; exact Algebra.mem_top
  exact hmem

end Degeneracy

end HJO.Multiplication
