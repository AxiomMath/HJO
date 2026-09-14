/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CylindricProduct.Summable
public meta import HJO.Attr

/-! # The commutation relation `(1 - xy) Γ_+(x) Γ_-(y) = Γ_-(y) Γ_+(x)`

Fix partitions `μ` and `ν` and compare the entries at `(μ, ν)`.

On the left the entry sums `x^{|τ|-|μ|} y^{|τ|-|ν|}` over the `τ` with `τ/μ` and `τ/ν` both
horizontal strips, which by the definition of `IsHStrip` says
`max (μ_i, ν_i) ≤ τ_i ≤ min (μ_{i-1}, ν_{i-1})` for every `i`, the upper constraint being vacuous
at `i = 0`. On the right the entry sums `y^{|μ|-|σ|} x^{|ν|-|σ|}` over the `σ` with `μ/σ` and
`ν/σ` horizontal strips, that is `max (μ_{i+1}, ν_{i+1}) ≤ σ_i ≤ min (μ_i, ν_i)`.

Writing `M_i = min (μ_i, ν_i)` for the upper bound at `i + 1` and `m_i = max (μ_i, ν_i)` for the
lower bound at `i`, the two index sets are the products of the intervals `[m_i, M_{i-1}]` over
`i ≥ 0` and `[m_{i+1}, M_i]` over `i ≥ 0`. They therefore correspond after dropping the
coordinate `i = 0` of the first, whose interval is unbounded above, and reflecting the rest. This
file carries out that correspondence as one explicit bijection

`{τ} ≃ ℕ × {σ}`,  `τ ↦ (τ_0 - m_0, i ↦ M_i + m_{i+1} - τ_{i+1})`,

whose size relation is `|σ| + |τ| = |μ| + |ν| + k`, because a minimum and a maximum of the same
two numbers sum to their total. Under it the summand on the left is `(xy)^k` times the summand on
the right, so the left entry is the geometric series `∑_{k ≥ 0} (xy)^k` times the right entry;
multiplying by `1 - xy` gives the stated form, and no inverse is needed.
-/

@[expose] public section

open Finset Filter PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-! ### The geometric series -/

/-- A series of positive order has a geometric series, and `1 - q` inverts it. -/
theorem summable_pow_of_constantCoeff_eq_zero {q : ℤ⟦X⟧} (hq : constantCoeff q = 0) :
    Summable fun k : ℕ => q ^ k := by
  simpa using PowerSeries.DiscreteTopology.summable_mul_pow (f := fun _ => (1 : ℤ⟦X⟧)) hq

/-- **The geometric series inverts `1 - q`** for `q` of positive order. -/
theorem one_sub_mul_tsum_pow {q : ℤ⟦X⟧} (hq : constantCoeff q = 0) :
    (1 - q) * ∑' k : ℕ, q ^ k = 1 := by
  have hs := summable_pow_of_constantCoeff_eq_zero hq
  have htail : (∑' k : ℕ, q ^ (k + 1)) = q * ∑' k : ℕ, q ^ k := by
    rw [← hs.tsum_mul_left]
    exact tsum_congr fun k => by rw [pow_succ, mul_comm]
  have hstep : (∑' k : ℕ, q ^ k) = 1 + q * ∑' k : ℕ, q ^ k := by
    rw [← htail]
    simpa using hs.tsum_eq_zero_add
  rw [sub_mul, one_mul]
  nth_rewrite 1 [hstep]
  ring

/-! ### The two index sets and their bounds -/

/-- The lower bound on the `i`-th part of a partition dominating both `μ` and `ν` by a horizontal
strip: `max (μ_i, ν_i)`. -/
def loB (mu nu : Part) (i : ℕ) : ℕ := max (mu.parts i) (nu.parts i)

/-- The upper bound on the `(i+1)`-st part of a partition dominating both `μ` and `ν` by a
horizontal strip, and the upper bound on the `i`-th part of a partition dominated by both:
`min (μ_i, ν_i)`. -/
def upB (mu nu : Part) (i : ℕ) : ℕ := min (mu.parts i) (nu.parts i)

theorem upB_le_loB (mu nu : Part) (i : ℕ) : upB mu nu i ≤ loB mu nu i := min_le_max

theorem upB_add_loB (mu nu : Part) (i : ℕ) :
    upB mu nu i + loB mu nu i = mu.parts i + nu.parts i := by
  simp only [upB, loB]; omega

/-- The partitions `τ` with `τ/μ` and `τ/ν` both horizontal strips: the index set of the entry of
`Γ_+(x) Γ_-(y)`. -/
def outerSet (mu nu : Part) : Set Part := {tau | IsHStrip tau mu ∧ IsHStrip tau nu}

/-- The partitions `σ` with `μ/σ` and `ν/σ` both horizontal strips: the index set of the entry of
`Γ_-(y) Γ_+(x)`. -/
def innerSet (mu nu : Part) : Set Part := {sigma | IsHStrip mu sigma ∧ IsHStrip nu sigma}

theorem mem_outerSet_iff {mu nu tau : Part} :
    tau ∈ outerSet mu nu ↔
      ∀ i, loB mu nu i ≤ tau.parts i ∧ tau.parts (i + 1) ≤ upB mu nu i := by
  simp only [outerSet, Set.mem_ofPred_eq, IsHStrip, loB, upB]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨max_le (h1 i).1 (h2 i).1, le_min (h1 i).2 (h2 i).2⟩
  · intro h
    exact ⟨fun i => ⟨le_trans (le_max_left _ _) (h i).1, le_trans (h i).2 (min_le_left _ _)⟩,
      fun i => ⟨le_trans (le_max_right _ _) (h i).1, le_trans (h i).2 (min_le_right _ _)⟩⟩

theorem mem_innerSet_iff {mu nu sigma : Part} :
    sigma ∈ innerSet mu nu ↔
      ∀ i, loB mu nu (i + 1) ≤ sigma.parts i ∧ sigma.parts i ≤ upB mu nu i := by
  simp only [innerSet, Set.mem_ofPred_eq, IsHStrip, loB, upB]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨max_le (h1 i).2 (h2 i).2, le_min (h1 i).1 (h2 i).1⟩
  · intro h
    exact ⟨fun i => ⟨le_trans (h i).2 (min_le_left _ _), le_trans (le_max_left _ _) (h i).1⟩,
      fun i => ⟨le_trans (h i).2 (min_le_right _ _), le_trans (le_max_right _ _) (h i).1⟩⟩

/-- A bound beyond which both `μ` and `ν` vanish, taken positive. -/
theorem exists_bound (mu nu : Part) :
    ∃ N, 1 ≤ N ∧ ∀ i, N ≤ i → mu.parts i = 0 ∧ nu.parts i = 0 := by
  obtain ⟨p, hp⟩ := mu.vanish
  obtain ⟨r, hr⟩ := nu.vanish
  exact ⟨max 1 (max p r), le_max_left _ _, fun i hi =>
    ⟨hp i (le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hi),
      hr i (le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hi)⟩⟩

theorem pairBounds_eq_zero {mu nu : Part} {N i : ℕ}
    (h : ∀ j, N ≤ j → mu.parts j = 0 ∧ nu.parts j = 0) (hi : N ≤ i) :
    loB mu nu i = 0 ∧ upB mu nu i = 0 := by
  obtain ⟨h1, h2⟩ := h i hi
  simp only [loB, upB, h1, h2]
  omega

/-! ### The bijection -/

/-- The parts of the reflected shift of an element of `outerSet`. -/
def shrinkFun (mu nu tau : Part) (i : ℕ) : ℕ :=
  upB mu nu i + loB mu nu (i + 1) - tau.parts (i + 1)

/-- The reflected shift of an element of `outerSet`: drop the unbounded coordinate `τ_0` and
reflect every remaining coordinate in its own interval. -/
def shrink (mu nu : Part) {tau : Part} (h : tau ∈ outerSet mu nu) : Part where
  parts := shrinkFun mu nu tau
  antitone' := antitone_nat_of_succ_le fun i => by
    have h0 := (mem_outerSet_iff.mp h i).2
    have h1 := (mem_outerSet_iff.mp h (i + 1)).2
    have h2 := (mem_outerSet_iff.mp h (i + 1 + 1)).1
    have h3 := upB_le_loB mu nu (i + 1)
    simp only [shrinkFun]
    omega
  vanish' := by
    obtain ⟨N, _, hN⟩ := exists_bound mu nu
    refine ⟨N, fun i hi => ?_⟩
    obtain ⟨_, hup⟩ := pairBounds_eq_zero hN hi
    obtain ⟨hlo, _⟩ := pairBounds_eq_zero hN (by omega : N ≤ i + 1)
    simp only [shrinkFun, hup, hlo]
    omega

@[simp] theorem shrink_parts {mu nu tau : Part} (h : tau ∈ outerSet mu nu) (i : ℕ) :
    (shrink mu nu h).parts i = upB mu nu i + loB mu nu (i + 1) - tau.parts (i + 1) := rfl

theorem shrink_mem {mu nu tau : Part} (h : tau ∈ outerSet mu nu) :
    shrink mu nu h ∈ innerSet mu nu := by
  refine mem_innerSet_iff.mpr fun i => ?_
  have h1 := (mem_outerSet_iff.mp h i).2
  have h2 := (mem_outerSet_iff.mp h (i + 1)).1
  simp only [shrink_parts]
  omega

/-- The parts of the element of `outerSet` assembled from a natural number and an element of
`innerSet`. -/
def growFun (mu nu : Part) (k : ℕ) (sigma : Part) : ℕ → ℕ
  | 0 => loB mu nu 0 + k
  | (i + 1) => upB mu nu i + loB mu nu (i + 1) - sigma.parts i

/-- The inverse of `shrink`: restore the coordinate at `0` from `k` and unreflect the rest. -/
def grow (mu nu : Part) (k : ℕ) {sigma : Part} (h : sigma ∈ innerSet mu nu) : Part where
  parts := growFun mu nu k sigma
  antitone' := antitone_nat_of_succ_le fun i => by
    match i with
    | 0 =>
      have h1 := (mem_innerSet_iff.mp h 0).1
      have h2 := upB_le_loB mu nu 0
      simp only [growFun]
      omega
    | (j + 1) =>
      have h1 := (mem_innerSet_iff.mp h j).2
      have h2 := (mem_innerSet_iff.mp h (j + 1)).1
      have h3 := upB_le_loB mu nu (j + 1)
      simp only [growFun]
      omega
  vanish' := by
    obtain ⟨N, hN1, hN⟩ := exists_bound mu nu
    refine ⟨N + 1, fun i hi => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    obtain ⟨_, hup⟩ := pairBounds_eq_zero hN (by omega : N ≤ j)
    obtain ⟨hlo, _⟩ := pairBounds_eq_zero hN (by omega : N ≤ j + 1)
    simp only [growFun, hup, hlo]
    omega

@[simp] theorem grow_parts_zero {mu nu : Part} (k : ℕ) {sigma : Part}
    (h : sigma ∈ innerSet mu nu) : (grow mu nu k h).parts 0 = loB mu nu 0 + k := rfl

@[simp] theorem grow_parts_succ {mu nu : Part} (k : ℕ) {sigma : Part}
    (h : sigma ∈ innerSet mu nu) (i : ℕ) :
    (grow mu nu k h).parts (i + 1) = upB mu nu i + loB mu nu (i + 1) - sigma.parts i := rfl

theorem grow_mem {mu nu : Part} (k : ℕ) {sigma : Part} (h : sigma ∈ innerSet mu nu) :
    grow mu nu k h ∈ outerSet mu nu := by
  refine mem_outerSet_iff.mpr fun i => ?_
  refine ⟨?_, ?_⟩
  · match i with
    | 0 =>
      simp only [grow_parts_zero]
      omega
    | (j + 1) =>
      have h1 := (mem_innerSet_iff.mp h j).2
      simp only [grow_parts_succ]
      omega
  · match i with
    | 0 =>
      have h1 := (mem_innerSet_iff.mp h 0).1
      have h2 := upB_le_loB mu nu 0
      simp only [grow_parts_succ]
      omega
    | (j + 1) =>
      have h1 := (mem_innerSet_iff.mp h (j + 1)).1
      have h2 := upB_le_loB mu nu (j + 1)
      simp only [grow_parts_succ]
      omega

/-- **The index sets correspond.** An element of `outerSet` is exactly a natural number -- how far
its coordinate at `0` exceeds the lower bound -- together with an element of `innerSet`. -/
noncomputable def commEquiv (mu nu : Part) :
    ↥(outerSet mu nu) ≃ ℕ × ↥(innerSet mu nu) where
  toFun tau := (tau.1.parts 0 - loB mu nu 0, ⟨shrink mu nu tau.2, shrink_mem tau.2⟩)
  invFun p := ⟨grow mu nu p.1 p.2.2, grow_mem p.1 p.2.2⟩
  left_inv tau := by
    refine Subtype.ext (Part.ext (funext fun i => ?_))
    match i with
    | 0 =>
      have h1 := (mem_outerSet_iff.mp tau.2 0).1
      simp only [grow_parts_zero]
      omega
    | (j + 1) =>
      have h1 := (mem_outerSet_iff.mp tau.2 j).2
      have h2 := (mem_outerSet_iff.mp tau.2 (j + 1)).1
      simp only [grow_parts_succ, shrink_parts]
      omega
  right_inv p := by
    refine Prod.ext ?_ (Subtype.ext (Part.ext (funext fun i => ?_)))
    · simp
    · have h1 := (mem_innerSet_iff.mp p.2.2 i).2
      simp only [shrink_parts, grow_parts_succ]
      omega

/-! ### The size relation -/

/-- **The reflected shift moves the size the right way**: `|σ| + |τ| = |μ| + |ν| + k`, with `k`
the excess of `τ_0` over its lower bound. The proof pairs each minimum with the maximum of the
same two numbers and leaves the bound at `0` over, which the excess restores. -/
theorem size_shrink_add {mu nu tau : Part} (h : tau ∈ outerSet mu nu) :
    (shrink mu nu h).size + tau.size
      = mu.size + nu.size + (tau.parts 0 - loB mu nu 0) := by
  obtain ⟨N, hN1, hN⟩ := exists_bound mu nu
  have htauN : ∀ i, N + 1 ≤ i → tau.parts i = 0 := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have h1 := (mem_outerSet_iff.mp h j).2
    have h2 := (pairBounds_eq_zero hN (by omega : N ≤ j)).2
    omega
  have hsigmaN : ∀ i, N ≤ i → (shrink mu nu h).parts i = 0 := by
    intro i hi
    have h1 := (pairBounds_eq_zero hN hi).2
    have h2 := (pairBounds_eq_zero hN (by omega : N ≤ i + 1)).1
    simp only [shrink_parts, h1, h2]
    omega
  have hsig : (shrink mu nu h).size = ∑ i ∈ range N, (shrink mu nu h).parts i :=
    Part.size_eq_sum_range _ hsigmaN
  have htau : tau.size = ∑ i ∈ range (N + 1), tau.parts i := Part.size_eq_sum_range _ htauN
  have hmu : mu.size = ∑ i ∈ range N, mu.parts i :=
    Part.size_eq_sum_range _ fun i hi => (hN i hi).1
  have hnu : nu.size = ∑ i ∈ range N, nu.parts i :=
    Part.size_eq_sum_range _ fun i hi => (hN i hi).2
  have htausplit : ∑ i ∈ range (N + 1), tau.parts i
      = (∑ i ∈ range N, tau.parts (i + 1)) + tau.parts 0 := Finset.sum_range_succ' _ _
  have hpair : ∀ i ∈ range N,
      (shrink mu nu h).parts i + tau.parts (i + 1) = upB mu nu i + loB mu nu (i + 1) := by
    intro i _
    have h1 := (mem_outerSet_iff.mp h i).2
    have h2 := (mem_outerSet_iff.mp h (i + 1)).1
    simp only [shrink_parts]
    omega
  have hsum : (∑ i ∈ range N, (shrink mu nu h).parts i) + ∑ i ∈ range N, tau.parts (i + 1)
      = (∑ i ∈ range N, upB mu nu i) + ∑ i ∈ range N, loB mu nu (i + 1) := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hpair, Finset.sum_add_distrib]
  have hlosplit : (∑ i ∈ range N, loB mu nu (i + 1)) + loB mu nu 0
      = ∑ i ∈ range N, loB mu nu i := by
    rw [← Finset.sum_range_succ' (loB mu nu) N, Finset.sum_range_succ,
      (pairBounds_eq_zero hN le_rfl).1, Nat.add_zero]
  have htotal : (∑ i ∈ range N, upB mu nu i) + ∑ i ∈ range N, loB mu nu i
      = (∑ i ∈ range N, mu.parts i) + ∑ i ∈ range N, nu.parts i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => upB_add_loB mu nu i
  have hlo0 : loB mu nu 0 ≤ tau.parts 0 := (mem_outerSet_iff.mp h 0).1
  omega

/-! ### Summability of the two entries -/

theorem stepBdd_gammaPlus_of_dvd {x : ℤ⟦X⟧} (hx : (X : ℤ⟦X⟧) ∣ x) : StepBdd (gammaPlus x) := by
  intro lam nu
  by_cases h : IsHStrip nu lam
  · rw [gammaPlus_of h]
    refine dvd_trans (pow_dvd_pow _ ?_) (pow_dvd_pow_of_dvd hx _)
    have := h.size_le
    simp only [sizeDist]
    omega
  · rw [gammaPlus_of_not h]; exact dvd_zero _

theorem stepBdd_gammaMinus_of_dvd {y : ℤ⟦X⟧} (hy : (X : ℤ⟦X⟧) ∣ y) : StepBdd (gammaMinus y) := by
  intro lam nu
  by_cases h : IsHStrip lam nu
  · rw [gammaMinus_of h]
    refine dvd_trans (pow_dvd_pow _ ?_) (pow_dvd_pow_of_dvd hy _)
    have := h.size_le
    simp only [sizeDist]
    omega
  · rw [gammaMinus_of_not h]; exact dvd_zero _

/-- A power series of positive order is divisible by `q`. -/
theorem X_dvd_of_constantCoeff_eq_zero {f : ℤ⟦X⟧} (hf : constantCoeff f = 0) :
    (X : ℤ⟦X⟧) ∣ f := by
  rw [show (X : ℤ⟦X⟧) = X ^ 1 by rw [pow_one]]
  exact PowerSeries.X_pow_dvd_iff.mpr fun d hd => by
    rw [show d = 0 by omega, PowerSeries.coeff_zero_eq_constantCoeff, hf]

/-- One of `x` and `y` has positive order when `xy` does, the coefficient ring being a domain. -/
theorem X_dvd_or_of_constantCoeff_mul {x y : ℤ⟦X⟧} (hxy : constantCoeff (x * y) = 0) :
    (X : ℤ⟦X⟧) ∣ x ∨ (X : ℤ⟦X⟧) ∣ y := by
  rw [map_mul, mul_eq_zero] at hxy
  exact hxy.imp X_dvd_of_constantCoeff_eq_zero X_dvd_of_constantCoeff_eq_zero

/-- The intermediate sums of the two orders of the product are summable: whichever of `x` and `y`
has positive order bounds the size of the intermediate partition against a fixed one. -/
theorem summable_gamma_pair {x y : ℤ⟦X⟧} (hxy : constantCoeff (x * y) = 0) (K L : Kernel)
    (hKx : (X : ℤ⟦X⟧) ∣ x → StepBdd K) (hLy : (X : ℤ⟦X⟧) ∣ y → StepBdd L)
    (lam nu : Part) : Summable fun tau => K lam tau * L tau nu := by
  rcases X_dvd_or_of_constantCoeff_mul hxy with hx | hy
  · exact summable_of_dvd_of_finite (g := fun tau => sizeDist lam tau)
      (fun tau => Dvd.dvd.mul_right (hKx hx lam tau) _) (finite_sizeDist_le lam)
  · refine summable_of_dvd_of_finite (g := fun tau => sizeDist tau nu)
      (fun tau => Dvd.dvd.mul_left (hLy hy tau nu) _) fun n => ?_
    exact (finite_sizeDist_le nu n).subset fun tau htau => by
      simpa [sizeDist_comm tau nu] using htau

theorem summable_gammaPlus_gammaMinus {x y : ℤ⟦X⟧} (hxy : constantCoeff (x * y) = 0)
    (mu nu : Part) : Summable fun tau => gammaPlus x mu tau * gammaMinus y tau nu :=
  summable_gamma_pair hxy _ _ stepBdd_gammaPlus_of_dvd stepBdd_gammaMinus_of_dvd mu nu

theorem summable_gammaMinus_gammaPlus {x y : ℤ⟦X⟧} (hxy : constantCoeff (x * y) = 0)
    (mu nu : Part) : Summable fun sigma => gammaMinus y mu sigma * gammaPlus x sigma nu :=
  summable_gamma_pair (x := y) (y := x) (by rwa [mul_comm]) _ _
    stepBdd_gammaMinus_of_dvd stepBdd_gammaPlus_of_dvd mu nu

theorem support_gammaPlus_gammaMinus (x y : ℤ⟦X⟧) (mu nu : Part) :
    (Function.support fun tau => gammaPlus x mu tau * gammaMinus y tau nu) ⊆ outerSet mu nu := by
  intro tau htau
  simp only [Function.mem_support] at htau
  by_cases h1 : IsHStrip tau mu
  · by_cases h2 : IsHStrip tau nu
    · exact ⟨h1, h2⟩
    · exact absurd (by rw [gammaMinus_of_not h2, mul_zero]) htau
  · exact absurd (by rw [gammaPlus_of_not h1, zero_mul]) htau

theorem support_gammaMinus_gammaPlus (x y : ℤ⟦X⟧) (mu nu : Part) :
    (Function.support fun sigma => gammaMinus y mu sigma * gammaPlus x sigma nu)
      ⊆ innerSet mu nu := by
  intro sigma hsigma
  simp only [Function.mem_support] at hsigma
  by_cases h1 : IsHStrip mu sigma
  · by_cases h2 : IsHStrip nu sigma
    · exact ⟨h1, h2⟩
    · exact absurd (by rw [gammaPlus_of_not h2, mul_zero]) hsigma
  · exact absurd (by rw [gammaMinus_of_not h1, zero_mul]) hsigma

/-! ### The entries correspond -/

/-- Under the correspondence the summand on the left is `(xy)^k` times the summand on the
right. -/
theorem entry_eq {x y : ℤ⟦X⟧} {mu nu tau : Part} (h : tau ∈ outerSet mu nu) :
    gammaPlus x mu tau * gammaMinus y tau nu
      = (x * y) ^ (tau.parts 0 - loB mu nu 0) *
        (gammaMinus y mu (shrink mu nu h) * gammaPlus x (shrink mu nu h) nu) := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h3, h4⟩ := shrink_mem (mu := mu) (nu := nu) ⟨h1, h2⟩
  have hsize := size_shrink_add (mu := mu) (nu := nu) ⟨h1, h2⟩
  have e1 := h1.size_le
  have e2 := h2.size_le
  have e3 := h3.size_le
  have e4 := h4.size_le
  rw [gammaPlus_of h1, gammaMinus_of h2, gammaMinus_of h3, gammaPlus_of h4, mul_pow]
  have ex : tau.size - mu.size
      = (tau.parts 0 - loB mu nu 0) + (nu.size - (shrink mu nu ⟨h1, h2⟩).size) := by omega
  have ey : tau.size - nu.size
      = (tau.parts 0 - loB mu nu 0) + (mu.size - (shrink mu nu ⟨h1, h2⟩).size) := by omega
  rw [ex, ey, pow_add, pow_add]
  ring

/-! ### The commutation relation -/

/-- The entry of `Γ_-(y) Γ_+(x)` read as a sum over `innerSet`, the entries vanishing elsewhere. -/
theorem kmul_gammaMinus_gammaPlus_eq (x y : ℤ⟦X⟧) (mu nu : Part) :
    kmul (gammaMinus y) (gammaPlus x) mu nu
      = ∑' sigma : ↥(innerSet mu nu), gammaMinus y mu sigma * gammaPlus x sigma nu := by
  rw [kmul]
  exact (tsum_subtype_eq_of_support_subset (support_gammaMinus_gammaPlus x y mu nu)).symm

/-- **The entry of `Γ_+(x) Γ_-(y)` is the geometric series times the entry of
`Γ_-(y) Γ_+(x)`.** This is the commutation relation before `1 - xy` is cleared: the bijection
`commEquiv` turns the left sum into a sum over `ℕ × innerSet` whose summand factors. -/
theorem kmul_gammaPlus_gammaMinus_eq {x y : ℤ⟦X⟧} (hxy : constantCoeff (x * y) = 0)
    (mu nu : Part) :
    kmul (gammaPlus x) (gammaMinus y) mu nu
      = (∑' k : ℕ, (x * y) ^ k) * kmul (gammaMinus y) (gammaPlus x) mu nu := by
  have hsubS : Summable fun tau : ↥(outerSet mu nu) =>
      gammaPlus x mu tau * gammaMinus y tau nu :=
    (summable_gammaPlus_gammaMinus hxy mu nu).subtype _
  have hsubG : Summable fun sigma : ↥(innerSet mu nu) =>
      gammaMinus y mu sigma * gammaPlus x sigma nu :=
    (summable_gammaMinus_gammaPlus hxy mu nu).subtype _
  have hcongr : ∀ tau : ↥(outerSet mu nu),
      gammaPlus x mu tau * gammaMinus y tau nu
        = (fun p : ℕ × ↥(innerSet mu nu) =>
            (x * y) ^ p.1 * (gammaMinus y mu p.2 * gammaPlus x p.2 nu))
          (commEquiv mu nu tau) := fun tau => entry_eq tau.2
  have hprod : Summable fun p : ℕ × ↥(innerSet mu nu) =>
      (x * y) ^ p.1 * (gammaMinus y mu p.2 * gammaPlus x p.2 nu) :=
    (commEquiv mu nu).summable_iff.mp (hsubS.congr hcongr)
  rw [kmul_gammaMinus_gammaPlus_eq, kmul]
  calc ∑' tau : Part, gammaPlus x mu tau * gammaMinus y tau nu
      = ∑' tau : ↥(outerSet mu nu), gammaPlus x mu tau * gammaMinus y tau nu :=
        (tsum_subtype_eq_of_support_subset (support_gammaPlus_gammaMinus x y mu nu)).symm
    _ = ∑' tau : ↥(outerSet mu nu),
          (fun p : ℕ × ↥(innerSet mu nu) =>
            (x * y) ^ p.1 * (gammaMinus y mu p.2 * gammaPlus x p.2 nu))
            (commEquiv mu nu tau) := tsum_congr hcongr
    _ = ∑' p : ℕ × ↥(innerSet mu nu),
          (x * y) ^ p.1 * (gammaMinus y mu p.2 * gammaPlus x p.2 nu) :=
        (commEquiv mu nu).tsum_eq
          (fun p : ℕ × ↥(innerSet mu nu) =>
            (x * y) ^ p.1 * (gammaMinus y mu p.2 * gammaPlus x p.2 nu))
    _ = ∑' k : ℕ, ∑' sigma : ↥(innerSet mu nu),
          (x * y) ^ k * (gammaMinus y mu sigma * gammaPlus x sigma nu) := hprod.tsum_prod
    _ = ∑' k : ℕ, (x * y) ^ k *
          ∑' sigma : ↥(innerSet mu nu), gammaMinus y mu sigma * gammaPlus x sigma nu :=
        tsum_congr fun k => hsubG.tsum_mul_left _
    _ = (∑' k : ℕ, (x * y) ^ k) *
          ∑' sigma : ↥(innerSet mu nu), gammaMinus y mu sigma * gammaPlus x sigma nu :=
        (summable_pow_of_constantCoeff_eq_zero hxy).tsum_mul_right _

/-- **The commutation relation.** For `x` and `y` with `xy` of positive order,
`(1 - xy) Γ_+(x) Γ_-(y) = Γ_-(y) Γ_+(x)`, the inverse-free form of
`Γ_+(x) Γ_-(y) = (1 - xy)^{-1} Γ_-(y) Γ_+(x)`. -/
@[hjo "lem_gamma_commutation"]
theorem one_sub_mul_gammaPlus_kmul_gammaMinus {x y : ℤ⟦X⟧} (hxy : constantCoeff (x * y) = 0)
    (mu nu : Part) :
    (1 - x * y) * kmul (gammaPlus x) (gammaMinus y) mu nu
      = kmul (gammaMinus y) (gammaPlus x) mu nu := by
  rw [kmul_gammaPlus_gammaMinus_eq hxy, ← mul_assoc, one_sub_mul_tsum_pow hxy, one_mul]

end HJO.CylindricProduct
