/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CylindricProduct.TransferTrace
public meta import HJO.Attr

/-! # Kernels of the same kind commute

Two lowering kernels commute, and so do two raising ones. Both follow from one observation about
the intermediate partitions of a pair of nested horizontal strips: for fixed `A` and `B` the
condition that `A/τ` and `τ/B` are both horizontal strips constrains each coordinate of `τ`
separately, to the interval

`max (A_{i+1}, B_i) ≤ τ_i ≤ min (A_i, B_{i-1})`,

reading `B_{-1} = ∞`. Reflecting every one of those intervals, `τ_i ↦ m_i + M_i - τ_i`, is an
involution of the constraint set, and it carries `|τ|` to `|A| + |B| - |τ|` because a minimum and
a maximum of the same two numbers sum to their total: the reindexing pairs `m_i` with `M_{i+1}`
and leaves `M_0 = A_0` over.

That involution exchanges the two exponents in the entry of a product of two kernels of the same
kind, which is the commutation. The lowering case runs the interval for the pair `(λ, ν)`; the
raising case is the same interval for the pair `(ν, λ)`, the strips being reversed.
-/

@[expose] public section

open Finset PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-! ### The interval cut out by a pair of nested strips -/

/-- The upper bound on the `i`-th part of a partition `τ` with `A/τ` and `τ/B` horizontal strips:
`min (A_i, B_{i-1})`, reading `B_{-1} = ∞`. -/
def upBd (A B : Part) : ℕ → ℕ
  | 0 => A.parts 0
  | (i + 1) => min (A.parts (i + 1)) (B.parts i)

/-- The lower bound on the `i`-th part of a partition `τ` with `A/τ` and `τ/B` horizontal strips:
`max (A_{i+1}, B_i)`. -/
def loBd (A B : Part) (i : ℕ) : ℕ := max (A.parts (i + 1)) (B.parts i)

/-- The upper bound at `i + 1` never exceeds the lower bound at `i`: they are the minimum and the
maximum of the same two numbers. -/
theorem upBd_succ_le_loBd (A B : Part) (i : ℕ) : upBd A B (i + 1) ≤ loBd A B i :=
  min_le_max

/-- The two strip conditions constrain the coordinates of `τ` separately, to the interval between
`loBd` and `upBd`. -/
theorem mem_interval_iff {A B tau : Part} :
    (IsHStrip A tau ∧ IsHStrip tau B) ↔
      ∀ i, loBd A B i ≤ tau.parts i ∧ tau.parts i ≤ upBd A B i := by
  constructor
  · rintro ⟨h1, h2⟩ i
    refine ⟨max_le (h1 i).2 (h2 i).1, ?_⟩
    match i with
    | 0 => exact (h1 0).1
    | (j + 1) => exact le_min (h1 (j + 1)).1 (h2 j).2
  · intro h
    refine ⟨fun i => ⟨?_, le_trans (le_max_left _ _) (h i).1⟩,
      fun i => ⟨le_trans (le_max_right _ _) (h i).1, ?_⟩⟩
    · match i with
      | 0 => exact (h 0).2
      | (j + 1) => exact le_trans (h (j + 1)).2 (min_le_left _ _)
    · exact le_trans (h (i + 1)).2 (min_le_right _ _)

/-- The set of intermediate partitions of the pair of nested strips at `(A, B)`. -/
def interval (A B : Part) : Set Part := {tau | IsHStrip A tau ∧ IsHStrip tau B}

theorem mem_interval {A B tau : Part} (h : tau ∈ interval A B) (i : ℕ) :
    loBd A B i ≤ tau.parts i ∧ tau.parts i ≤ upBd A B i :=
  mem_interval_iff.mp h i

/-- Beyond a common bound the parts of `A`, `B` and `τ` all vanish, and the bound may be taken
positive. -/
theorem exists_common_bound (A B tau : Part) :
    ∃ n, 1 ≤ n ∧ ∀ i, n ≤ i → A.parts i = 0 ∧ B.parts i = 0 ∧ tau.parts i = 0 := by
  obtain ⟨p, hp⟩ := A.vanish
  obtain ⟨q, hq⟩ := B.vanish
  obtain ⟨r, hr⟩ := tau.vanish
  refine ⟨max 1 (max p (max q r)), le_max_left _ _, fun i hi => ⟨hp i ?_, hq i ?_, hr i ?_⟩⟩
  · exact le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hi
  · exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right 1 _)) hi
  · exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right 1 _)) hi

/-- Beyond a common bound both bounds vanish. -/
theorem bounds_eq_zero {A B : Part} {n i : ℕ} (hn : 1 ≤ n)
    (h : ∀ j, n ≤ j → A.parts j = 0 ∧ B.parts j = 0) (hi : n ≤ i) :
    loBd A B i = 0 ∧ upBd A B i = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have h1 := (h (j + 1) hi).1
  have h2 := (h (j + 2) (by omega)).1
  have h3 := (h (j + 1) hi).2
  refine ⟨?_, ?_⟩
  · rw [loBd, h2, h3]; simp
  · rw [upBd, h1]; simp

/-! ### Reflecting the intervals -/

/-- The reflection of `τ` in the interval at `(A, B)`: each coordinate is reflected in its own
interval, `τ_i ↦ m_i + M_i - τ_i`. -/
def reflectFun (A B tau : Part) (i : ℕ) : ℕ := loBd A B i + upBd A B i - tau.parts i

/-- The reflection of an intermediate partition is a partition. -/
noncomputable def reflect {A B tau : Part} (h : tau ∈ interval A B) : Part where
  parts := reflectFun A B tau
  antitone' := antitone_nat_of_succ_le fun i => by
    have h1 := mem_interval h i
    have h2 := mem_interval h (i + 1)
    have h3 := upBd_succ_le_loBd A B i
    simp only [reflectFun]
    omega
  vanish' := by
    obtain ⟨n, hn, hall⟩ := exists_common_bound A B tau
    refine ⟨n, fun i hi => ?_⟩
    obtain ⟨hlo, hup⟩ := bounds_eq_zero (A := A) (B := B) hn
      (fun j hj => ⟨(hall j hj).1, (hall j hj).2.1⟩) hi
    simp only [reflectFun, hlo, hup, (hall i hi).2.2]

@[simp] theorem reflect_parts {A B tau : Part} (h : tau ∈ interval A B) (i : ℕ) :
    (reflect h).parts i = loBd A B i + upBd A B i - tau.parts i := rfl

/-- The reflection of an intermediate partition is again one. -/
theorem reflect_mem {A B tau : Part} (h : tau ∈ interval A B) : reflect h ∈ interval A B := by
  refine mem_interval_iff.mpr fun i => ?_
  have h1 := mem_interval h i
  simp only [reflect_parts]
  omega

/-- Reflection is an involution. -/
theorem reflect_reflect {A B tau : Part} (h : tau ∈ interval A B) :
    reflect (reflect_mem h) = tau := by
  refine Part.ext (funext fun i => ?_)
  have h1 := mem_interval h i
  simp only [reflect_parts]
  omega

/-- Reflection carries `|τ|` to `|A| + |B| - |τ|`: the reindexing pairs each maximum with the
minimum of the same two numbers and leaves `A_0` over. -/
theorem size_reflect_add {A B tau : Part} (h : tau ∈ interval A B) :
    (reflect h).size + tau.size = A.size + B.size := by
  obtain ⟨n, hn, hall⟩ := exists_common_bound A B tau
  have hAB : ∀ j, n ≤ j → A.parts j = 0 ∧ B.parts j = 0 :=
    fun j hj => ⟨(hall j hj).1, (hall j hj).2.1⟩
  have hrefl : (reflect h).size = ∑ i ∈ range (n + 1), (reflect h).parts i := by
    refine Part.size_eq_sum_range _ fun i hi => ?_
    obtain ⟨hlo, hup⟩ := bounds_eq_zero (A := A) (B := B) hn hAB (by omega : n ≤ i)
    simp only [reflect_parts, hlo, hup, (hall i (by omega)).2.2]
  have htau : tau.size = ∑ i ∈ range (n + 1), tau.parts i :=
    Part.size_eq_sum_range _ fun i hi => (hall i (by omega)).2.2
  have hA : A.size = ∑ i ∈ range (n + 1), A.parts i :=
    Part.size_eq_sum_range _ fun i hi => (hall i (by omega)).1
  have hB : B.size = ∑ i ∈ range n, B.parts i :=
    Part.size_eq_sum_range _ fun i hi => (hall i hi).2.1
  have hcomb : ∀ i ∈ range (n + 1),
      (reflect h).parts i + tau.parts i = loBd A B i + upBd A B i := by
    intro i _
    have h1 := mem_interval h i
    simp only [reflect_parts]
    omega
  rw [hrefl, htau, ← Finset.sum_add_distrib, Finset.sum_congr rfl hcomb,
    Finset.sum_add_distrib]
  have hlast : loBd A B n = 0 := (bounds_eq_zero (A := A) (B := B) hn hAB le_rfl).1
  have hlo : ∑ i ∈ range (n + 1), loBd A B i = ∑ i ∈ range n, loBd A B i := by
    rw [Finset.sum_range_succ, hlast, Nat.add_zero]
  have hup : ∑ i ∈ range (n + 1), upBd A B i
      = (∑ i ∈ range n, upBd A B (i + 1)) + A.parts 0 := by
    rw [Finset.sum_range_succ']
    rfl
  rw [hlo, hup, ← Nat.add_assoc, ← Finset.sum_add_distrib]
  have hpair : ∀ i ∈ range n, loBd A B i + upBd A B (i + 1) = A.parts (i + 1) + B.parts i := by
    intro i _
    simp only [loBd, upBd]
    omega
  rw [Finset.sum_congr rfl hpair, Finset.sum_add_distrib, hA, hB, Finset.sum_range_succ']
  omega

/-! ### The commutations -/

/-- The entries of a product of two lowering kernels vanish off the interval. -/
theorem support_gammaMinus_mul (m m' : ℕ) (lam nu : Part) :
    (Function.support fun tau => gammaMinus (X ^ m) lam tau * gammaMinus (X ^ m') tau nu)
      ⊆ interval lam nu := by
  intro tau htau
  simp only [Function.mem_support] at htau
  by_cases h1 : IsHStrip lam tau
  · by_cases h2 : IsHStrip tau nu
    · exact ⟨h1, h2⟩
    · exact absurd (by rw [gammaMinus_of_not h2, mul_zero]) htau
  · exact absurd (by rw [gammaMinus_of_not h1, zero_mul]) htau

/-- The entries of a product of two raising kernels vanish off the interval at the reversed
pair. -/
theorem support_gammaPlus_mul (m m' : ℕ) (lam nu : Part) :
    (Function.support fun tau => gammaPlus (X ^ m) lam tau * gammaPlus (X ^ m') tau nu)
      ⊆ interval nu lam := by
  intro tau htau
  simp only [Function.mem_support] at htau
  by_cases h1 : IsHStrip tau lam
  · by_cases h2 : IsHStrip nu tau
    · exact ⟨h2, h1⟩
    · exact absurd (by rw [gammaPlus_of_not h2, mul_zero]) htau
  · exact absurd (by rw [gammaPlus_of_not h1, zero_mul]) htau

/-- The reflection swaps the two exponents in the entry of a product of two lowering kernels. -/
theorem gammaMinus_mul_reflect (m m' : ℕ) {lam nu tau : Part} (h : tau ∈ interval lam nu) :
    gammaMinus (X ^ m) lam (reflect h) * gammaMinus (X ^ m') (reflect h) nu
      = gammaMinus (X ^ m') lam tau * gammaMinus (X ^ m) tau nu := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := reflect_mem (A := lam) (B := nu) ⟨h1, h2⟩
  have hs := size_reflect_add (A := lam) (B := nu) ⟨h1, h2⟩
  have e1 : lam.size - (reflect (A := lam) (B := nu) ⟨h1, h2⟩).size = tau.size - nu.size := by
    have := h1.size_le
    have := h2.size_le
    have := h1'.size_le
    have := h2'.size_le
    omega
  have e2 : (reflect (A := lam) (B := nu) ⟨h1, h2⟩).size - nu.size = lam.size - tau.size := by
    have := h1.size_le
    have := h2.size_le
    have := h1'.size_le
    have := h2'.size_le
    omega
  rw [gammaMinus_of h1', gammaMinus_of h2', gammaMinus_of h1, gammaMinus_of h2, e1, e2]
  ring

/-- The reflection swaps the two exponents in the entry of a product of two raising kernels. -/
theorem gammaPlus_mul_reflect (m m' : ℕ) {lam nu tau : Part} (h : tau ∈ interval nu lam) :
    gammaPlus (X ^ m) lam (reflect h) * gammaPlus (X ^ m') (reflect h) nu
      = gammaPlus (X ^ m') lam tau * gammaPlus (X ^ m) tau nu := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := reflect_mem (A := nu) (B := lam) ⟨h1, h2⟩
  have hs := size_reflect_add (A := nu) (B := lam) ⟨h1, h2⟩
  have e1 : (reflect (A := nu) (B := lam) ⟨h1, h2⟩).size - lam.size = nu.size - tau.size := by
    have := h1.size_le
    have := h2.size_le
    have := h1'.size_le
    have := h2'.size_le
    omega
  have e2 : nu.size - (reflect (A := nu) (B := lam) ⟨h1, h2⟩).size = tau.size - lam.size := by
    have := h1.size_le
    have := h2.size_le
    have := h1'.size_le
    have := h2'.size_le
    omega
  rw [gammaPlus_of h2', gammaPlus_of h1', gammaPlus_of h2, gammaPlus_of h1, e1, e2]
  ring

/-- The reflection as an involutive equivalence of the interval. -/
noncomputable def reflectEquiv (A B : Part) : interval A B ≃ interval A B where
  toFun tau := ⟨reflect tau.2, reflect_mem tau.2⟩
  invFun tau := ⟨reflect tau.2, reflect_mem tau.2⟩
  left_inv tau := Subtype.ext (reflect_reflect tau.2)
  right_inv tau := Subtype.ext (reflect_reflect tau.2)

/-- **Two lowering kernels commute.** -/
@[hjo "lem_gamma_same_commute"]
theorem gammaMinus_kmul_comm (m m' : ℕ) :
    kmul (gammaMinus (X ^ m)) (gammaMinus (X ^ m'))
      = kmul (gammaMinus (X ^ m')) (gammaMinus (X ^ m)) := by
  funext lam nu
  rw [kmul, kmul, ← tsum_subtype_eq_of_support_subset (support_gammaMinus_mul m m' lam nu),
    ← tsum_subtype_eq_of_support_subset (support_gammaMinus_mul m' m lam nu),
    ← (reflectEquiv lam nu).tsum_eq
      (fun tau : interval lam nu => gammaMinus (X ^ m) lam tau * gammaMinus (X ^ m') tau nu)]
  exact tsum_congr fun tau => gammaMinus_mul_reflect m m' tau.2

/-- **Two raising kernels commute.** -/
@[hjo "lem_gamma_same_commute"]
theorem gammaPlus_kmul_comm (m m' : ℕ) :
    kmul (gammaPlus (X ^ m)) (gammaPlus (X ^ m'))
      = kmul (gammaPlus (X ^ m')) (gammaPlus (X ^ m)) := by
  funext lam nu
  rw [kmul, kmul, ← tsum_subtype_eq_of_support_subset (support_gammaPlus_mul m m' lam nu),
    ← tsum_subtype_eq_of_support_subset (support_gammaPlus_mul m' m lam nu),
    ← (reflectEquiv nu lam).tsum_eq
      (fun tau : interval nu lam => gammaPlus (X ^ m) lam tau * gammaPlus (X ^ m') tau nu)]
  exact tsum_congr fun tau => gammaPlus_mul_reflect m m' tau.2

end HJO.CylindricProduct
