/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Instances.ENat
public import HJO.CylindricProduct.TransferTrace
public meta import HJO.Attr

/-! # Positive powers of `q` make the kernel products and traces summable

A product of the three kernels `Γ_-(q^m)`, `Γ_+(q^m)`, `Q(q^m)` with `m ≥ 1` is defined, and if
one of the factors is a grading kernel then the product has a trace. The mechanism is a pair of
divisibility bounds that propagate through the kernel product:

* every one of the three kernels has its entry at `(λ, ν)` divisible by `q^{d(λ,ν)}`, with
  `d(λ,ν) = | |λ| - |ν| |` the distance between the sizes -- because `Γ_±(q^m)` is supported on
  the pairs where one size dominates the other and carries `q^{m||λ|-|ν||}` there, and `Q(q^m)` is
  supported on the diagonal where the distance is `0`;
* a product one of whose factors is a grading kernel has its entry at `(λ, ν)` divisible by
  `q^{|λ|}`, the grading factor contributing `q^{m|τ|}` at the partition `τ` standing at its
  position and the factors between `λ` and `τ` contributing `q^{||τ|-|λ||}`.

The first bound gives summability of the intermediate sum, because it forces every `τ`
contributing to the coefficient of `q^n` to satisfy `|τ| ≤ |λ| + n`, and there are finitely many
partitions of bounded size; the second gives summability of the diagonal sum, because it forces
`|λ| ≤ n`. This is where `m ≥ 1` is used: at `m = 0` the factor `Γ_±(1)` bounds nothing.
-/

@[expose] public section

open Finset Filter PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-! ### Finitely many partitions of each size -/

namespace Part

/-- Every part of a partition is at most its size. -/
theorem parts_le_size (l : Part) (i : ℕ) : l.parts i ≤ l.size := by
  obtain ⟨B, hB⟩ := l.vanish
  have hle : l.size = ∑ j ∈ range (max B (i + 1)), l.parts j :=
    size_eq_sum_range l fun j hj => hB j (le_trans (le_max_left _ _) hj)
  rw [hle]
  exact Finset.single_le_sum (f := l.parts) (fun _ _ => Nat.zero_le _)
    (mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_right _ _)))

/-- A partition of size at most `i` has its `i`-th part zero: were it positive, the `i + 1` parts
below it would all be positive and the size would exceed `i`. -/
theorem parts_eq_zero_of_size_le {l : Part} {i : ℕ} (h : l.size ≤ i) : l.parts i = 0 := by
  by_contra hcon
  obtain ⟨B, hB⟩ := l.vanish
  have hle : l.size = ∑ j ∈ range (max B (i + 1)), l.parts j :=
    size_eq_sum_range l fun j hj => hB j (le_trans (le_max_left _ _) hj)
  have hsub : ∑ j ∈ range (i + 1), l.parts j ≤ l.size := by
    rw [hle]
    exact Finset.sum_le_sum_of_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega)
  have hpos : ∀ j ∈ range (i + 1), 1 ≤ l.parts j := fun j hj =>
    le_trans (Nat.one_le_iff_ne_zero.mpr hcon) (l.antitone (Nat.lt_succ_iff.mp (mem_range.mp hj)))
  have hcard : (i + 1) * 1 ≤ ∑ j ∈ range (i + 1), l.parts j := by
    simpa using Finset.card_nsmul_le_sum (range (i + 1)) l.parts 1 hpos
  omega

end Part

/-- **Finitely many partitions of each size.** A partition of size at most `n` is determined by
its first `n + 1` parts, each of which is at most `n`. -/
theorem finite_size_le (n : ℕ) : {l : Part | l.size ≤ n}.Finite := by
  set f : Part → Fin (n + 1) → Fin (n + 1) :=
    fun l i => ⟨min (l.parts i) n, by omega⟩ with hf
  refine Set.Finite.of_finite_image (Set.toFinite (f '' {l : Part | l.size ≤ n})) ?_
  intro l hl m hm hlm
  refine Part.ext (funext fun i => ?_)
  by_cases hi : i < n + 1
  · have h := congrFun hlm ⟨i, hi⟩
    simp only [hf, Fin.mk.injEq] at h
    have h1 : l.parts i ≤ n := le_trans (l.parts_le_size i) hl
    have h2 : m.parts i ≤ n := le_trans (m.parts_le_size i) hm
    omega
  · rw [Part.parts_eq_zero_of_size_le (le_trans hl (by omega)),
      Part.parts_eq_zero_of_size_le (le_trans hm (by omega))]

/-! ### The distance between two sizes -/

/-- The distance `| |λ| - |ν| |` between the sizes of two partitions, written as a sum of two
truncated subtractions so that it stays in `ℕ`. -/
noncomputable def sizeDist (lam nu : Part) : ℕ := (lam.size - nu.size) + (nu.size - lam.size)

theorem sizeDist_comm (lam nu : Part) : sizeDist lam nu = sizeDist nu lam := by
  simp only [sizeDist]; omega

@[simp] theorem sizeDist_self (lam : Part) : sizeDist lam lam = 0 := by
  simp only [sizeDist]; omega

/-- The size of the second argument is bounded by the size of the first plus the distance. -/
theorem size_le_add_sizeDist (lam nu : Part) : nu.size ≤ lam.size + sizeDist lam nu := by
  simp only [sizeDist]; omega

/-- The triangle inequality for the size distance. -/
theorem sizeDist_le_add (lam tau nu : Part) :
    sizeDist lam nu ≤ sizeDist lam tau + sizeDist tau nu := by
  simp only [sizeDist]; omega

/-- Passing from `λ` to an intermediate `τ` and then reading the size of `τ` bounds the size of
`λ`; this is what makes a grading factor deep inside a product still bound the outer size. -/
theorem size_le_sizeDist_add (lam tau : Part) : lam.size ≤ sizeDist lam tau + tau.size := by
  simp only [sizeDist]; omega

/-- There are finitely many partitions at bounded size distance from a given one. -/
theorem finite_sizeDist_le (lam : Part) (n : ℕ) : {tau : Part | sizeDist lam tau ≤ n}.Finite :=
  (finite_size_le (lam.size + n)).subset fun tau htau =>
    le_trans (size_le_add_sizeDist lam tau) (Nat.add_le_add_left htau lam.size)

/-! ### Summability and divisibility -/

/-- **A divisibility bound with finite sublevel sets gives summability.** If the `i`-th member of
the family is divisible by `q^{g i}` and only finitely many `i` have `g i ≤ n`, for each `n`, then
each coefficient of `q` receives only finitely many nonzero contributions. -/
theorem summable_of_dvd_of_finite {ι : Type*} {f : ι → ℤ⟦X⟧} {g : ι → ℕ}
    (hdvd : ∀ i, (X : ℤ⟦X⟧) ^ g i ∣ f i) (hfin : ∀ n, {i | g i ≤ n}.Finite) : Summable f := by
  refine PowerSeries.DiscreteTopology.summable_of_order_tendsto_nhds_top ?_
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro n
  rw [eventually_cofinite]
  refine (hfin n).subset fun i hi => ?_
  simp only [Set.mem_ofPred_eq] at hi ⊢
  by_contra hcon
  refine hi (lt_of_lt_of_le ?_ (PowerSeries.nat_le_order (f i) (g i)
    fun j hj => PowerSeries.X_pow_dvd_iff.mp (hdvd i) j hj))
  exact_mod_cast Nat.lt_of_not_le hcon

/-- **A sum of series divisible by `q^k` is divisible by `q^k`.** The ideal generated by `q^k` is
a neighbourhood of `0`, hence an open and therefore closed additive subgroup, and every partial
sum lies in it. -/
theorem X_pow_dvd_tsum {ι : Type*} {f : ι → ℤ⟦X⟧} {k : ℕ} (hf : Summable f)
    (h : ∀ i, (X : ℤ⟦X⟧) ^ k ∣ f i) : (X : ℤ⟦X⟧) ^ k ∣ ∑' i, f i := by
  have hclosed : IsClosed
      (((Ideal.span {(X : ℤ⟦X⟧) ^ k}).toAddSubgroup : AddSubgroup ℤ⟦X⟧) : Set ℤ⟦X⟧) :=
    AddSubgroup.isClosed_of_isOpen _ (AddSubgroup.isOpen_of_mem_nhds _
      (PowerSeries.DiscreteTopology.span_X_pow_mem_nhds_zero k))
  have hmem : ∀ s : Finset ι, (∑ i ∈ s, f i) ∈ Ideal.span {(X : ℤ⟦X⟧) ^ k} :=
    fun s => Ideal.sum_mem _ fun i _ => Ideal.mem_span_singleton.mpr (h i)
  exact Ideal.mem_span_singleton.mp
    (hclosed.mem_of_tendsto hf.hasSum (Filter.Eventually.of_forall hmem))

/-! ### The two divisibility bounds on a kernel -/

/-- A kernel is **step-bounded** when its entry at `(λ, ν)` is divisible by `q^{| |λ| - |ν| |}`.
All three of `Γ_-`, `Γ_+` and `Q` are step-bounded when their argument is a positive power
of `q`: by `PowerSeries.X_pow_dvd_iff` the divisibility says that a nonzero coefficient of `q ^ n`
in `K λ ν` forces `| |λ| - |ν| | ≤ n`. -/
@[hjo "def_tame_kernel"]
def StepBdd (K : Kernel) : Prop := ∀ lam nu, (X : ℤ⟦X⟧) ^ sizeDist lam nu ∣ K lam nu

/-- A kernel is **grade-bounded** when its entry at `(λ, ν)` is divisible by `q^{|λ|}`. A product
containing a grading kernel is grade-bounded, and that is what makes its trace summable. This is
the *coercive* kernel: by `PowerSeries.X_pow_dvd_iff` the divisibility says that a
nonzero coefficient of `q ^ n` in `K λ ν` forces `|λ| ≤ n`. -/
@[hjo "def_coercive_kernel"]
def GradeBdd (K : Kernel) : Prop := ∀ lam nu, (X : ℤ⟦X⟧) ^ lam.size ∣ K lam nu

@[hjo "lem_gamma_tame"]
theorem StepBdd.gammaMinus {m : ℕ} (hm : 1 ≤ m) : StepBdd (gammaMinus (X ^ m)) := by
  intro lam nu
  by_cases h : IsHStrip lam nu
  · rw [gammaMinus_of h, ← pow_mul]
    refine pow_dvd_pow _ ?_
    have := h.size_le
    simp only [sizeDist]
    calc lam.size - nu.size + (nu.size - lam.size) = lam.size - nu.size := by omega
      _ ≤ m * (lam.size - nu.size) := Nat.le_mul_of_pos_left _ hm
  · rw [gammaMinus_of_not h]; exact dvd_zero _

@[hjo "lem_gamma_tame"]
theorem StepBdd.gammaPlus {m : ℕ} (hm : 1 ≤ m) : StepBdd (gammaPlus (X ^ m)) := by
  intro lam nu
  by_cases h : IsHStrip nu lam
  · rw [gammaPlus_of h, ← pow_mul]
    refine pow_dvd_pow _ ?_
    have := h.size_le
    simp only [sizeDist]
    calc lam.size - nu.size + (nu.size - lam.size) = nu.size - lam.size := by omega
      _ ≤ m * (nu.size - lam.size) := Nat.le_mul_of_pos_left _ hm
  · rw [gammaPlus_of_not h]; exact dvd_zero _

@[hjo "lem_grading_tame"]
theorem StepBdd.grading (u : ℤ⟦X⟧) : StepBdd (CylindricProduct.grading u) := by
  intro lam nu
  by_cases h : lam = nu
  · subst h; simp
  · rw [grading_of_ne h]; exact dvd_zero _

theorem StepBdd.kone : StepBdd CylindricProduct.kone := by
  intro lam nu
  by_cases h : lam = nu
  · subst h; simp
  · simp [CylindricProduct.kone, h]

@[hjo "lem_grading_coercive"]
theorem GradeBdd.grading {m : ℕ} (hm : 1 ≤ m) : GradeBdd (CylindricProduct.grading (X ^ m)) := by
  intro lam nu
  by_cases h : lam = nu
  · subst h
    rw [grading_diag, ← pow_mul]
    exact pow_dvd_pow _ (Nat.le_mul_of_pos_left _ hm)
  · rw [grading_of_ne h]; exact dvd_zero _

/-! ### The bounds propagate through an iterated product -/

/-- The intermediate sums of an iterated product of step-bounded kernels are summable. -/
@[hjo "lem_tame_product_defined"]
theorem summable_kmul {K L : Kernel} (hK : StepBdd K) (_hL : StepBdd L) (lam nu : Part) :
    Summable fun tau => K lam tau * L tau nu :=
  summable_of_dvd_of_finite (g := fun tau => sizeDist lam tau)
    (fun tau => Dvd.dvd.mul_right (hK lam tau) _) (finite_sizeDist_le lam)

/-- The product of two step-bounded kernels is step-bounded. -/
@[hjo "lem_tame_product_tame"]
theorem StepBdd.kmul {K L : Kernel} (hK : StepBdd K) (hL : StepBdd L) :
    StepBdd (CylindricProduct.kmul K L) := by
  intro lam nu
  rw [CylindricProduct.kmul]
  refine X_pow_dvd_tsum (summable_kmul hK hL lam nu) fun tau => ?_
  refine dvd_trans (pow_dvd_pow _ (sizeDist_le_add lam tau nu)) ?_
  rw [pow_add]
  exact mul_dvd_mul (hK lam tau) (hL tau nu)

/-- **An iterated product of step-bounded kernels is step-bounded.** -/
theorem StepBdd.klist {Ks : List Kernel} (h : ∀ K ∈ Ks, StepBdd K) :
    StepBdd (CylindricProduct.klist Ks) := by
  induction Ks with
  | nil => exact StepBdd.kone
  | cons K Ks ih =>
    exact StepBdd.kmul (h K List.mem_cons_self)
      (ih fun L hL => h L (List.mem_cons_of_mem _ hL))

/-- A product of a grade-bounded kernel with a step-bounded one is grade-bounded. -/
@[hjo "lem_tame_coercive_product"]
theorem GradeBdd.kmul_left {K L : Kernel} (hK : GradeBdd K) (hKs : StepBdd K)
    (hL : StepBdd L) :
    GradeBdd (CylindricProduct.kmul K L) := by
  intro lam nu
  rw [CylindricProduct.kmul]
  exact X_pow_dvd_tsum (summable_kmul hKs hL lam nu)
    fun tau => Dvd.dvd.mul_right (hK lam tau) _

/-- A product of a step-bounded kernel with a grade-bounded one is grade-bounded: the steps from
`λ` to the intermediate partition `τ` contribute `q^{||τ|-|λ||}` and the tail contributes
`q^{|τ|}`, and those exponents together are at least `|λ|`. -/
@[hjo "lem_tame_coercive_product"]
theorem GradeBdd.kmul_right {K L : Kernel} (hK : StepBdd K) (hL : GradeBdd L) (hLs : StepBdd L) :
    GradeBdd (CylindricProduct.kmul K L) := by
  intro lam nu
  rw [CylindricProduct.kmul]
  refine X_pow_dvd_tsum (summable_kmul hK hLs lam nu) fun tau => ?_
  refine dvd_trans (pow_dvd_pow _ (size_le_sizeDist_add lam tau)) ?_
  rw [pow_add]
  exact mul_dvd_mul (hK lam tau) (hL tau nu)

/-- **An iterated product with a grade-bounded factor is grade-bounded.** -/
theorem GradeBdd.klist {Ks : List Kernel} (hstep : ∀ K ∈ Ks, StepBdd K)
    (hgrade : ∃ K ∈ Ks, GradeBdd K) : GradeBdd (CylindricProduct.klist Ks) := by
  induction Ks with
  | nil => exact absurd hgrade (by simp)
  | cons K Ks ih =>
    have hKstep : StepBdd K := hstep K List.mem_cons_self
    have hKsstep : ∀ L ∈ Ks, StepBdd L := fun L hL => hstep L (List.mem_cons_of_mem _ hL)
    obtain ⟨L, hLmem, hL⟩ := hgrade
    rcases List.mem_cons.mp hLmem with rfl | hLmem'
    · exact GradeBdd.kmul_left hL hKstep (StepBdd.klist hKsstep)
    · exact GradeBdd.kmul_right hKstep (ih hKsstep ⟨L, hLmem', hL⟩) (StepBdd.klist hKsstep)

/-! ### The vertex operators -/

/-- The three kernels admitted as factors of the products considered here: `Γ_-(q^m)`, `Γ_+(q^m)`
and `Q(q^m)`, each with `m ≥ 1`. -/
inductive IsVertex : Kernel → Prop
  /-- A lowering kernel with a positive power of `q`. -/
  | minus (m : ℕ) (hm : 1 ≤ m) : IsVertex (gammaMinus (X ^ m))
  /-- A raising kernel with a positive power of `q`. -/
  | plus (m : ℕ) (hm : 1 ≤ m) : IsVertex (gammaPlus (X ^ m))
  /-- A grading kernel with a positive power of `q`. -/
  | grade (m : ℕ) (hm : 1 ≤ m) : IsVertex (grading (X ^ m))

theorem IsVertex.stepBdd {K : Kernel} (h : IsVertex K) : StepBdd K := by
  cases h with
  | minus m hm => exact StepBdd.gammaMinus hm
  | plus m hm => exact StepBdd.gammaPlus hm
  | grade m _ => exact StepBdd.grading _

/-! ### The two side conditions hold for products of vertex operators -/

/-- **The product of vertex operators is defined.** Each intermediate sum has, in each
coefficient of `q`, only finitely many nonzero contributions. -/
@[hjo "lem_kernel_summable"]
theorem mulSummable_klist {K : Kernel} (hK : IsVertex K) {Ks : List Kernel}
    (hKs : ∀ L ∈ Ks, IsVertex L) : MulSummable K (CylindricProduct.klist Ks) :=
  fun lam nu => summable_kmul hK.stepBdd
    (StepBdd.klist fun L hL => (hKs L hL).stepBdd) lam nu

/-- **A product of vertex operators with a grading factor has a trace.** The diagonal entry at
`λ` is divisible by `q^{|λ|}`, so only the finitely many partitions of size at most `n` reach the
coefficient of `q^n`. -/
@[hjo "lem_kernel_summable"]
theorem traceSummable_klist {Ks : List Kernel} (hKs : ∀ L ∈ Ks, IsVertex L)
    {m : ℕ} (hm : 1 ≤ m) (hmem : grading (X ^ m) ∈ Ks) :
    TraceSummable (CylindricProduct.klist Ks) :=
  summable_of_dvd_of_finite (g := fun lam : Part => lam.size)
    (fun lam => GradeBdd.klist (fun L hL => (hKs L hL).stepBdd)
      ⟨grading (X ^ m), hmem, GradeBdd.grading hm⟩ lam lam)
    finite_size_le

end HJO.CylindricProduct
