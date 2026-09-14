/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CylindricProduct.Algebra
public meta import HJO.Attr

/-! # A product of kernels read along paths, and its trace read around the cycle

A product of kernels can be read as a sum over paths: the entry of `K_0 ⋯ K_{n-1}` at
`(λ, ν)` is the sum, over the sequences `λ = τ_0, τ_1, …, τ_n = ν`, of `∏_i K_i(τ_i, τ_{i+1})`,
and its trace is the same sum over the *closed* sequences, the two ends identified. Neither is
available from `kmul` and `ktrace`: those build an `n`-fold product one intermediate partition at a
time, so the path reading is an `n`-fold interchange of sums and holds
only under a summability side condition. `HJO.CylindricProduct.Algebra` supplies the case `n = 2`
(`summable_kmul_pair`, and the Fubini argument inside `kmul_assoc`); this file supplies every `n`.

A path is written as a function `c : Fin (n+1) → Part`, and its endpoints are pinned not by a
subtype but by a factor `kone`, which is `1` when the path does end where it should and `0`
otherwise. That keeps the index of the sum a plain function type, so splitting off the first step
is the equivalence `pathConsEquiv` and the induction along the list is unobstructed.

The side condition is a divisibility bound with finite sublevel sets, as in
`HJO.CylindricProduct.Summable`, and **two** different ones are needed, because the two readings of
the cycle that the argument compares are bounded by different mechanisms:

* the *sorted* transfer kernel `transferKernel` has every argument a positive power of `q`,
  so every factor is `StepBdd`: its entry at `(λ, ν)` is divisible by `q^{||λ|-|ν||}`. The bound
  along a path is `pathDist`, the total distance travelled, and the triangle inequality
  `sizeDist_le_add` then confines every partition on the path to a bounded distance from its start;
* the *slot-ordered* reading keeps one grading per slot and therefore has strip factors with the
  argument `1`, and `Γ_±(1)` is **not** step-bounded. What it has instead is one grading in every
  factor, so every factor is `GradeBdd`: its entry at `(λ, ν)` is divisible by `q^{|λ|}`. The bound
  along a path is `pathSize`, the total of the sizes of the partitions the path enters, and that
  bounds each of them outright -- except the last, which nothing in the product bounds and which is
  pinned instead by the `kone` factor. That is why the grade-bounded half needs
  `summable_of_dvd_of_finite'`, the variant of `summable_of_dvd_of_finite` whose finiteness
  hypothesis may use the vanishing of the family.

Both halves feed one induction: `klist_apply_eq_tsum_of` takes the summability supply as a
hypothesis on a predicate `P`, and is instantiated at `StepBdd` and at `GradeBdd`.

For the trace the closed path is finally reindexed, from a path of `n+1` partitions whose first is
repeated at the end to a cyclic sequence of `n` partitions -- `cycProd`, whose `i`-th factor is
`K_i(c_i, c_{i+1})` with the successor taken modulo `n`. That is the shape the slice correspondence
needs, the slices of a diagonal function being indexed by the residues around the cycle.
-/

@[expose] public section

open Finset PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-! ### Paths and the product along them -/

/-- The product of the entries of the kernels `Ks` along the path `c`: the path visits
`c 0, c 1, …, c n`, and the `i`-th kernel is read at the pair `(c i, c (i+1))`. -/
noncomputable def pathProd (Ks : List Kernel) (c : Fin (Ks.length + 1) → Part) : ℤ⟦X⟧ :=
  ∏ i : Fin Ks.length, Ks.get i (c i.castSucc) (c i.succ)

/-- The total distance a path travels: the sum of the size distances of its steps. -/
noncomputable def pathDist (n : ℕ) (c : Fin (n + 1) → Part) : ℕ :=
  ∑ i : Fin n, sizeDist (c i.castSucc) (c i.succ)

/-- The total size of the partitions a path enters, the last one excluded. -/
noncomputable def pathSize (n : ℕ) (c : Fin (n + 1) → Part) : ℕ :=
  ∑ i : Fin n, (c i.castSucc).size

/-- The path that starts at `lam` and continues through the partitions of `p`. -/
def openPath {n : ℕ} (lam : Part) (p : Fin n → Part) : Fin (n + 1) → Part := Fin.cons lam p

@[simp] theorem openPath_zero {n : ℕ} (lam : Part) (p : Fin n → Part) :
    openPath lam p 0 = lam := Fin.cons_zero _ _

@[simp] theorem openPath_succ {n : ℕ} (lam : Part) (p : Fin n → Part) (i : Fin n) :
    openPath lam p i.succ = p i := Fin.cons_succ _ _ i

/-- **A path is its starting partition together with the rest of it.** This is the reindexing that
turns the interchange of the outer sum with the inner ones into a single sum over a product. -/
def pathConsEquiv (n : ℕ) : Part × (Fin n → Part) ≃ (Fin (n + 1) → Part) where
  toFun q := openPath q.1 q.2
  invFun c := (c 0, fun i => c i.succ)
  left_inv := fun ⟨_, _⟩ => by simp only [openPath_zero, openPath_succ]
  right_inv c := Fin.cons_self_tail c

@[simp] theorem pathConsEquiv_apply (n : ℕ) (q : Part × (Fin n → Part)) :
    pathConsEquiv n q = openPath q.1 q.2 := rfl

theorem pathProd_nil (c : Fin 1 → Part) : pathProd [] c = 1 := by
  rw [pathProd]; simp

/-- **Splitting off the first factor of a path product.** -/
theorem pathProd_cons (K : Kernel) (Ks : List Kernel) (c : Fin (Ks.length + 2) → Part) :
    pathProd (K :: Ks) c = K (c 0) (c 1) * pathProd Ks fun i => c i.succ := by
  have h1 : pathProd (K :: Ks) c
      = ∏ i : Fin (Ks.length + 1), (K :: Ks).get i (c i.castSucc) (c i.succ) := rfl
  rw [h1, Fin.prod_univ_succ, pathProd]
  congr 1

/-! ### The two divisibility bounds along a path -/

/-- The size distance from the start of a sequence to its `t`-th term is at most the total of the
distances of the first `t` steps: the triangle inequality, telescoped. -/
theorem sizeDist_le_sum_range (e : ℕ → Part) (t : ℕ) :
    sizeDist (e 0) (e t) ≤ ∑ s ∈ range t, sizeDist (e s) (e (s + 1)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    exact le_trans (sizeDist_le_add (e 0) (e t) (e (t + 1))) (Nat.add_le_add_right ih _)

/-- **A step bound confines every partition on a path.** The distance from the start of the path to
the partition at any index is at most the total distance travelled. -/
theorem sizeDist_le_pathDist {n : ℕ} (c : Fin (n + 1) → Part) (i : Fin (n + 1)) :
    sizeDist (c 0) (c i) ≤ pathDist n c := by
  obtain ⟨e, h0, hcast, hi⟩ : ∃ e : ℕ → Part, e 0 = c 0 ∧
      (∀ k : Fin n, e (k : ℕ) = c k.castSucc ∧ e ((k : ℕ) + 1) = c k.succ) ∧ e (i : ℕ) = c i := by
    refine ⟨fun t => c ⟨min t n, Nat.lt_succ_of_le (min_le_right t n)⟩, ?_, ?_, ?_⟩
    · exact congrArg c (Fin.ext (by simp))
    · intro k
      have hk := k.isLt
      exact ⟨congrArg c (Fin.ext (by simp)), congrArg c (Fin.ext (by simp))⟩
    · exact congrArg c (Fin.ext (by have := i.isLt; simp; omega))
  have hin : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
  calc sizeDist (c 0) (c i)
      = sizeDist (e 0) (e (i : ℕ)) := by rw [h0, hi]
    _ ≤ ∑ s ∈ range (i : ℕ), sizeDist (e s) (e (s + 1)) := sizeDist_le_sum_range e _
    _ ≤ ∑ s ∈ range n, sizeDist (e s) (e (s + 1)) := by
        refine Finset.sum_le_sum_of_subset fun s hs => ?_
        rw [mem_range] at hs ⊢
        omega
    _ = pathDist n c := by
        rw [pathDist, ← Fin.sum_univ_eq_sum_range]
        exact Finset.sum_congr rfl fun k _ => by rw [(hcast k).1, (hcast k).2]

/-- **A grade bound confines every partition a path enters.** -/
theorem size_le_pathSize {n : ℕ} (c : Fin (n + 1) → Part) (i : Fin n) :
    (c i.castSucc).size ≤ pathSize n c :=
  Finset.single_le_sum (f := fun k : Fin n => (c k.castSucc).size) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)

theorem finite_pathDist_le {n : ℕ} (lam : Part) (m : ℕ) :
    {p : Fin n → Part | pathDist n (openPath lam p) ≤ m}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin n => {tau : Part | sizeDist lam tau ≤ m})
    fun _ => finite_sizeDist_le lam m).subset fun p hp => Set.mem_univ_pi.mpr fun j => ?_
  have h := sizeDist_le_pathDist (openPath lam p) j.succ
  rw [openPath_zero, openPath_succ] at h
  exact le_trans h hp

/-- **The step bound propagates to a path product.** -/
theorem X_pow_pathDist_dvd_pathProd {Ks : List Kernel} (hKs : ∀ K ∈ Ks, StepBdd K)
    (c : Fin (Ks.length + 1) → Part) :
    (X : ℤ⟦X⟧) ^ pathDist Ks.length c ∣ pathProd Ks c := by
  rw [pathDist, pathProd, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => hKs _ (List.get_mem Ks i) _ _

/-- **The grade bound propagates to a path product.** -/
theorem X_pow_pathSize_dvd_pathProd {Ks : List Kernel} (hKs : ∀ K ∈ Ks, GradeBdd K)
    (c : Fin (Ks.length + 1) → Part) :
    (X : ℤ⟦X⟧) ^ pathSize Ks.length c ∣ pathProd Ks c := by
  rw [pathSize, pathProd, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => hKs _ (List.get_mem Ks i) _ _

/-- **A divisibility bound whose sublevel sets are finite where the family does not vanish gives
summability.** The variant of `summable_of_dvd_of_finite` that the grade bound needs: the final
partition of a path is not bounded by `pathSize` at all, and what confines it is the vanishing of
the summand off the paths that close up. -/
theorem summable_of_dvd_of_finite' {ι : Type*} {f : ι → ℤ⟦X⟧} {g : ι → ℕ}
    (hdvd : ∀ i, (X : ℤ⟦X⟧) ^ g i ∣ f i)
    (hfin : ∀ n, {i | g i ≤ n ∧ f i ≠ 0}.Finite) : Summable f := by
  refine PowerSeries.DiscreteTopology.summable_of_order_tendsto_nhds_top ?_
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro n
  rw [Filter.eventually_cofinite]
  refine (hfin n).subset fun i hi => ?_
  simp only [Set.mem_ofPred_eq] at hi ⊢
  refine ⟨?_, fun h0 => hi ?_⟩
  · by_contra hcon
    refine hi (lt_of_lt_of_le ?_ (PowerSeries.nat_le_order (f i) (g i)
      fun j hj => PowerSeries.X_pow_dvd_iff.mp (hdvd i) j hj))
    exact_mod_cast Nat.lt_of_not_le hcon
  · rw [h0, PowerSeries.order_zero]
    exact_mod_cast ENat.natCast_lt_top n

/-! ### The entry of a product as a sum over paths -/

/-- The weight of the open path from `lam` through `p`: the product of the entries of `Ks` along
it, killed by the `kone` factor unless the path does end at `nu`. -/
noncomputable def openWeight (Ks : List Kernel) (lam nu : Part) (p : Fin Ks.length → Part) :
    ℤ⟦X⟧ :=
  pathProd Ks (openPath lam p) * kone (openPath lam p (Fin.last Ks.length)) nu

theorem openWeight_eq_zero {Ks : List Kernel} {lam nu : Part} {p : Fin Ks.length → Part}
    (h : openPath lam p (Fin.last Ks.length) ≠ nu) : openWeight Ks lam nu p = 0 := by
  rw [openWeight, kone, ite_eq_right h, mul_zero]

/-- **The open paths of a step-bounded product are summable.** The `n`-step generalisation of
`summable_kmul_pair`: one triangle inequality confines all the intermediate partitions at once, so
the family lives in a product of finitely many finite sets. -/
theorem summable_openWeight {Ks : List Kernel} (hKs : ∀ K ∈ Ks, StepBdd K) (lam nu : Part) :
    Summable (openWeight Ks lam nu) :=
  summable_of_dvd_of_finite (g := fun p => pathDist Ks.length (openPath lam p))
    (fun _ => Dvd.dvd.mul_right (X_pow_pathDist_dvd_pathProd hKs _) _)
    fun m => finite_pathDist_le lam m

/-- **The open paths of a grade-bounded product are summable.** Here `pathSize` bounds every
partition the path enters except the last, and the last is `nu` wherever the summand is nonzero. -/
theorem summable_openWeight_of_grade {Ks : List Kernel} (hKs : ∀ K ∈ Ks, GradeBdd K)
    (lam nu : Part) : Summable (openWeight Ks lam nu) := by
  refine summable_of_dvd_of_finite' (g := fun p => pathSize Ks.length (openPath lam p))
    (fun _ => Dvd.dvd.mul_right (X_pow_pathSize_dvd_pathProd hKs _) _) fun m => ?_
  refine (Set.Finite.pi (t := fun _ : Fin Ks.length => {l : Part | l.size ≤ m} ∪ {nu})
    fun _ => (finite_size_le m).union (Set.finite_singleton nu)).subset
    fun p hp => Set.mem_univ_pi.mpr fun j => ?_
  simp only [Set.mem_ofPred_eq] at hp
  obtain ⟨hle, hne⟩ := hp
  have hj := j.isLt
  by_cases hlt : (j : ℕ) + 1 < Ks.length
  · refine Or.inl ?_
    have hcast : (⟨(j : ℕ) + 1, hlt⟩ : Fin Ks.length).castSucc = j.succ := Fin.ext rfl
    have h := size_le_pathSize (openPath lam p) ⟨(j : ℕ) + 1, hlt⟩
    rw [hcast, openPath_succ] at h
    exact le_trans h hle
  · refine Or.inr ?_
    have hlast : j.succ = Fin.last Ks.length := Fin.ext (by simp; omega)
    by_contra hc
    exact hne (openWeight_eq_zero (by rw [← hlast, openPath_succ]; exact hc))

theorem openWeight_cons {K : Kernel} {Ks : List Kernel} (lam nu : Part)
    (q : Part × (Fin Ks.length → Part)) :
    openWeight (K :: Ks) lam nu (pathConsEquiv Ks.length q)
      = K lam q.1 * openWeight Ks q.1 nu q.2 := by
  obtain ⟨tau, p⟩ := q
  have htail : (fun i : Fin (Ks.length + 1) => openPath lam (openPath tau p) i.succ)
      = openPath tau p := funext fun i => openPath_succ _ _ i
  have hlast : (Fin.last (K :: Ks).length : Fin ((K :: Ks).length + 1))
      = (Fin.last Ks.length).succ := Fin.ext rfl
  rw [pathConsEquiv_apply, openWeight, openWeight, pathProd_cons, openPath_zero,
    ← Fin.succ_zero_eq_one, openPath_succ, openPath_zero, htail, hlast,
    openPath_succ, mul_assoc]

/-- **The entry of a product of kernels is the sum over the paths joining its two arguments.**
The path is recorded as the sequence `p` of the partitions standing after each factor, and its last
member is forced to be `ν` by the `kone` factor of `openWeight`. The side condition is supplied as
summability for every list built from kernels satisfying `P`, so that the induction along the list
has it available for every tail. -/
theorem klist_apply_eq_tsum_of {P : Kernel → Prop}
    (hP : ∀ Ls : List Kernel, (∀ L ∈ Ls, P L) → ∀ lam nu, Summable (openWeight Ls lam nu))
    {Ks : List Kernel} (hKs : ∀ K ∈ Ks, P K) (lam nu : Part) :
    klist Ks lam nu = ∑' p : Fin Ks.length → Part, openWeight Ks lam nu p := by
  induction Ks generalizing lam nu with
  | nil =>
    rw [klist_nil]
    refine ((tsum_eq_single (fun _ => Part.zero)
      fun p hp => absurd (funext fun i => i.elim0) hp).trans ?_).symm
    have h0 : (Fin.last ([] : List Kernel).length : Fin (([] : List Kernel).length + 1)) = 0 :=
      Fin.ext rfl
    rw [openWeight, pathProd_nil, one_mul, h0, openPath_zero]
  | cons K Ks ih =>
    have hKs' : ∀ L ∈ Ks, P L := fun L hL => hKs L (List.mem_cons_of_mem _ hL)
    have hFsum : Summable fun q : Part × (Fin Ks.length → Part) =>
        K lam q.1 * openWeight Ks q.1 nu q.2 :=
      (((pathConsEquiv Ks.length).summable_iff).mpr
        (hP (K :: Ks) hKs lam nu)).congr (openWeight_cons lam nu)
    calc klist (K :: Ks) lam nu
        = ∑' tau, K lam tau * klist Ks tau nu := rfl
      _ = ∑' tau, K lam tau * ∑' p : Fin Ks.length → Part, openWeight Ks tau nu p :=
          tsum_congr fun tau => by rw [ih hKs' tau nu]
      _ = ∑' tau, ∑' p : Fin Ks.length → Part, K lam tau * openWeight Ks tau nu p :=
          tsum_congr fun tau => ((hP Ks hKs' tau nu).tsum_mul_left _).symm
      _ = ∑' q : Part × (Fin Ks.length → Part), K lam q.1 * openWeight Ks q.1 nu q.2 :=
          hFsum.tsum_prod.symm
      _ = ∑' p : Fin (Ks.length + 1) → Part, openWeight (K :: Ks) lam nu p := by
          rw [← (pathConsEquiv Ks.length).tsum_eq]
          exact tsum_congr fun q => (openWeight_cons lam nu q).symm

/-- **The path reading of a step-bounded product.** -/
theorem klist_apply_eq_tsum {Ks : List Kernel} (hKs : ∀ K ∈ Ks, StepBdd K) (lam nu : Part) :
    klist Ks lam nu = ∑' p : Fin Ks.length → Part, openWeight Ks lam nu p :=
  klist_apply_eq_tsum_of (fun _ h => summable_openWeight h) hKs lam nu

/-- **The path reading of a grade-bounded product.** -/
theorem klist_apply_eq_tsum_of_grade {Ks : List Kernel} (hKs : ∀ K ∈ Ks, GradeBdd K)
    (lam nu : Part) :
    klist Ks lam nu = ∑' p : Fin Ks.length → Part, openWeight Ks lam nu p :=
  klist_apply_eq_tsum_of (fun _ h => summable_openWeight_of_grade h) hKs lam nu

/-! ### The trace as a sum over closed paths -/

/-- The weight of a closed reading of the cycle, written as a path of `n + 1` partitions whose two
ends are identified by the `kone` factor. -/
noncomputable def cycWeight (Ks : List Kernel) (c : Fin (Ks.length + 1) → Part) : ℤ⟦X⟧ :=
  pathProd Ks c * kone (c (Fin.last Ks.length)) (c 0)

theorem cycWeight_eq_zero {Ks : List Kernel} {c : Fin (Ks.length + 1) → Part}
    (h : c (Fin.last Ks.length) ≠ c 0) : cycWeight Ks c = 0 := by
  rw [cycWeight, kone, ite_eq_right h, mul_zero]

/-- A kernel is **grade-and-step bounded** when its entry at `(λ, ν)` is divisible by
`q^{|λ| + d(λ,ν)}`. The grading kernel `Q(q^m)` with `m ≥ 1` is: it vanishes off the diagonal, and
on the diagonal the distance is `0`. This is the bound that makes the *closed* paths of a
step-bounded product summable -- the step bound alone leaves the whole cycle free to translate. -/
def GradeStepBdd (K : Kernel) : Prop :=
  ∀ lam nu, (X : ℤ⟦X⟧) ^ (lam.size + sizeDist lam nu) ∣ K lam nu

theorem GradeStepBdd.grading {m : ℕ} (hm : 1 ≤ m) :
    GradeStepBdd (CylindricProduct.grading (X ^ m)) := by
  intro lam nu
  by_cases h : lam = nu
  · subst h
    rw [grading_diag, sizeDist_self, Nat.add_zero, ← pow_mul]
    exact pow_dvd_pow _ (Nat.le_mul_of_pos_left _ hm)
  · rw [grading_of_ne h]; exact dvd_zero _

theorem GradeStepBdd.stepBdd {K : Kernel} (h : GradeStepBdd K) : StepBdd K := fun lam nu =>
  dvd_trans (pow_dvd_pow _ (Nat.le_add_left _ _)) (h lam nu)

theorem GradeStepBdd.gradeBdd {K : Kernel} (h : GradeStepBdd K) : GradeBdd K := fun lam nu =>
  dvd_trans (pow_dvd_pow _ (Nat.le_add_right _ _)) (h lam nu)

/-- **A grading factor pins a step-bounded cycle.** The factor at the grading slot contributes
`q^{|λ| + d}` where the others contribute only `q^{d}`, which is what bounds the whole cycle. -/
theorem X_pow_dvd_pathProd_of_grade {Ks : List Kernel} (hKs : ∀ K ∈ Ks, StepBdd K)
    {j : Fin Ks.length} (hj : GradeStepBdd (Ks.get j)) (c : Fin (Ks.length + 1) → Part) :
    (X : ℤ⟦X⟧) ^ ((c j.castSucc).size + pathDist Ks.length c) ∣ pathProd Ks c := by
  have hsum : (c j.castSucc).size + pathDist Ks.length c
      = ∑ i : Fin Ks.length, (sizeDist (c i.castSucc) (c i.succ)
          + if i = j then (c j.castSucc).size else 0) := by
    rw [Finset.sum_add_distrib, pathDist,
      Finset.sum_ite_eq' Finset.univ j fun _ => (c j.castSucc).size]
    simp [Nat.add_comm]
  rw [hsum, pathProd, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun i _ => ?_
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, Nat.add_comm]
    exact hj _ _
  · rw [ite_eq_right hij, Nat.add_zero]
    exact hKs _ (List.get_mem Ks i) _ _

theorem finite_size_add_pathDist_le {n : ℕ} (j : Fin (n + 1)) (m : ℕ) :
    {c : Fin (n + 1) → Part | (c j).size + pathDist n c ≤ m}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin (n + 1) => {l : Part | l.size ≤ 3 * m})
    fun _ => finite_size_le (3 * m)).subset fun c hc => Set.mem_univ_pi.mpr fun i => ?_
  simp only [Set.mem_ofPred_eq] at hc ⊢
  have h1 : sizeDist (c 0) (c i) ≤ pathDist n c := sizeDist_le_pathDist c i
  have h2 : sizeDist (c 0) (c j) ≤ pathDist n c := sizeDist_le_pathDist c j
  have h3 : (c i).size ≤ sizeDist (c i) (c 0) + (c 0).size := size_le_sizeDist_add _ _
  have h4 : (c 0).size ≤ sizeDist (c 0) (c j) + (c j).size := size_le_sizeDist_add _ _
  have h5 : sizeDist (c i) (c 0) = sizeDist (c 0) (c i) := sizeDist_comm _ _
  omega

/-- **The closed paths of a step-bounded product with a grading factor are summable.** -/
theorem summable_cycWeight {Ks : List Kernel} (hKs : ∀ K ∈ Ks, StepBdd K)
    {j : Fin Ks.length} (hj : GradeStepBdd (Ks.get j)) : Summable (cycWeight Ks) :=
  summable_of_dvd_of_finite (g := fun c => (c j.castSucc).size + pathDist Ks.length c)
    (fun c => Dvd.dvd.mul_right (X_pow_dvd_pathProd_of_grade hKs hj c) _)
    fun m => finite_size_add_pathDist_le j.castSucc m

/-- **The closed paths of a grade-bounded product are summable.** Every partition the cycle enters
is bounded by `pathSize`, and the one partition that is not -- the repeated end -- equals the start
wherever the summand is nonzero. -/
theorem summable_cycWeight_of_grade {Ks : List Kernel} (hKs : ∀ K ∈ Ks, GradeBdd K)
    (hne : 0 < Ks.length) : Summable (cycWeight Ks) := by
  refine summable_of_dvd_of_finite' (g := fun c => pathSize Ks.length c)
    (fun _ => Dvd.dvd.mul_right (X_pow_pathSize_dvd_pathProd hKs _) _) fun m => ?_
  refine (Set.Finite.pi (t := fun _ : Fin (Ks.length + 1) => {l : Part | l.size ≤ m})
    fun _ => finite_size_le m).subset fun c hc => Set.mem_univ_pi.mpr fun i => ?_
  simp only [Set.mem_ofPred_eq] at hc ⊢
  obtain ⟨hle, hnz⟩ := hc
  have hzero : (c 0).size ≤ m := by
    have h := size_le_pathSize c ⟨0, hne⟩
    rw [show (⟨0, hne⟩ : Fin Ks.length).castSucc = 0 from Fin.ext rfl] at h
    exact le_trans h hle
  by_cases hlt : (i : ℕ) < Ks.length
  · have h := size_le_pathSize c ⟨(i : ℕ), hlt⟩
    rw [show (⟨(i : ℕ), hlt⟩ : Fin Ks.length).castSucc = i from Fin.ext rfl] at h
    exact le_trans h hle
  · have hi : i = Fin.last Ks.length := Fin.ext (by have := i.isLt; simp; omega)
    by_cases hend : c (Fin.last Ks.length) = c 0
    · rw [hi, hend]; exact hzero
    · exact absurd (cycWeight_eq_zero hend) hnz

/-- **The trace of a product of kernels is the sum over its closed paths.** The path is written
with its starting partition repeated at the end, the `kone` factor of `cycWeight` forcing the two
to agree. -/
theorem ktrace_klist_eq_tsum_of {P : Kernel → Prop}
    (hP : ∀ Ls : List Kernel, (∀ L ∈ Ls, P L) → ∀ lam nu, Summable (openWeight Ls lam nu))
    {Ks : List Kernel} (hKs : ∀ K ∈ Ks, P K) (hcyc : Summable (cycWeight Ks)) :
    ktrace (klist Ks) = ∑' c : Fin (Ks.length + 1) → Part, cycWeight Ks c := by
  have hkey : ∀ q : Part × (Fin Ks.length → Part),
      cycWeight Ks (pathConsEquiv Ks.length q) = openWeight Ks q.1 q.1 q.2 := by
    rintro ⟨lam, p⟩
    rw [pathConsEquiv_apply, cycWeight, openWeight, openPath_zero]
  have hFsum : Summable fun q : Part × (Fin Ks.length → Part) => openWeight Ks q.1 q.1 q.2 :=
    (((pathConsEquiv Ks.length).summable_iff).mpr hcyc).congr hkey
  calc ktrace (klist Ks)
      = ∑' lam, klist Ks lam lam := rfl
    _ = ∑' lam, ∑' p : Fin Ks.length → Part, openWeight Ks lam lam p :=
        tsum_congr fun lam => klist_apply_eq_tsum_of hP hKs lam lam
    _ = ∑' q : Part × (Fin Ks.length → Part), openWeight Ks q.1 q.1 q.2 := hFsum.tsum_prod.symm
    _ = ∑' c : Fin (Ks.length + 1) → Part, cycWeight Ks c := by
        rw [← (pathConsEquiv Ks.length).tsum_eq]
        exact tsum_congr fun q => (hkey q).symm

/-- **The closed-path reading of the trace of a step-bounded product with a grading factor.** -/
theorem ktrace_klist_eq_tsum {Ks : List Kernel} (hKs : ∀ K ∈ Ks, StepBdd K)
    {j : Fin Ks.length} (hj : GradeStepBdd (Ks.get j)) :
    ktrace (klist Ks) = ∑' c : Fin (Ks.length + 1) → Part, cycWeight Ks c :=
  ktrace_klist_eq_tsum_of (fun _ h => summable_openWeight h) hKs (summable_cycWeight hKs hj)

/-- **The closed-path reading of the trace of a grade-bounded product.** -/
theorem ktrace_klist_eq_tsum_of_grade {Ks : List Kernel} (hKs : ∀ K ∈ Ks, GradeBdd K)
    (hne : 0 < Ks.length) :
    ktrace (klist Ks) = ∑' c : Fin (Ks.length + 1) → Part, cycWeight Ks c :=
  ktrace_klist_eq_tsum_of (fun _ h => summable_openWeight_of_grade h) hKs
    (summable_cycWeight_of_grade hKs hne)

/-! ### The closed path as a cyclic sequence -/

/-- The cyclic reading of a closed path: the `i`-th kernel is read at `(c i, c (i+1))`, the
successor taken modulo the length. -/
noncomputable def cycProd {n : ℕ} [NeZero n] (Ks : Fin n → Kernel) (c : Fin n → Part) : ℤ⟦X⟧ :=
  ∏ i : Fin n, Ks i (c i) (c (i + 1))

/-- Closing a cyclic sequence into a path: repeat its first partition at the end. -/
def closePath {n : ℕ} (c : Fin (n + 1) → Part) : Fin (n + 2) → Part := Fin.snoc c (c 0)

@[simp] theorem closePath_castSucc {n : ℕ} (c : Fin (n + 1) → Part) (i : Fin (n + 1)) :
    closePath c i.castSucc = c i := Fin.snoc_castSucc _ _ i

@[simp] theorem closePath_last {n : ℕ} (c : Fin (n + 1) → Part) :
    closePath c (Fin.last (n + 1)) = c 0 := Fin.snoc_last _ _

theorem closePath_zero {n : ℕ} (c : Fin (n + 1) → Part) : closePath c 0 = c 0 := by
  have h : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := Fin.ext rfl
  rw [h, closePath_castSucc]

/-- The successor along a closed path is the cyclic successor of the sequence: at the last index it
wraps around to the start, which is what the repeated end is for. -/
theorem closePath_succ {n : ℕ} (c : Fin (n + 1) → Part) (i : Fin (n + 1)) :
    closePath c i.succ = c (i + 1) := by
  by_cases h : i = Fin.last n
  · have h2 : (Fin.last n + 1 : Fin (n + 1)) = 0 :=
      Fin.ext (by rw [Fin.val_add_one, ite_eq_left rfl]; rfl)
    rw [h, Fin.succ_last, closePath_last, h2]
  · have hval : ((i + 1 : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := by
      rw [Fin.val_add_one, ite_eq_right h]
    have h1 : i.succ = (i + 1 : Fin (n + 1)).castSucc :=
      Fin.ext (by rw [Fin.val_succ, Fin.val_castSucc, hval])
    rw [h1, closePath_castSucc]

theorem injective_closePath {n : ℕ} : Function.Injective (closePath (n := n)) := by
  intro c c' h
  refine funext fun i => ?_
  have hi := congrFun h i.castSucc
  rwa [closePath_castSucc, closePath_castSucc] at hi

/-- A path whose two ends agree is a closed cyclic sequence. -/
theorem closePath_init {n : ℕ} (c : Fin (n + 2) → Part) (h : c (Fin.last (n + 1)) = c 0) :
    closePath (fun i => c i.castSucc) = c := by
  have h0 : c ((0 : Fin (n + 1)).castSucc) = c (Fin.last (n + 1)) := by
    rw [h]; exact congrArg c (Fin.ext rfl)
  rw [closePath, h0]
  exact Fin.snoc_init_self c

theorem cycWeight_closePath (K : Kernel) (Ks : List Kernel) (c : Fin (Ks.length + 1) → Part) :
    cycWeight (K :: Ks) (closePath c)
      = cycProd (fun i : Fin (Ks.length + 1) => (K :: Ks).get i) c := by
  have hlast : (Fin.last (K :: Ks).length : Fin ((K :: Ks).length + 1))
      = Fin.last (Ks.length + 1) := Fin.ext rfl
  have hprod : pathProd (K :: Ks) (closePath c)
      = ∏ i : Fin (Ks.length + 1),
          (K :: Ks).get i (closePath c i.castSucc) (closePath c i.succ) := rfl
  rw [cycWeight, hlast, closePath_last, closePath_zero, kone, ite_eq_left rfl, mul_one, hprod,
    cycProd]
  exact Finset.prod_congr rfl fun i _ => by rw [closePath_castSucc, closePath_succ]

/-- **The trace of a product of kernels is the sum over the closed cyclic sequences of
partitions.** This is the form the transfer-trace argument uses: the sum runs over the sequences
`c` of `d` partitions indexed cyclically, and the `i`-th kernel is read at `(c i, c (i+1))`. -/
theorem ktrace_klist_eq_tsum_cycProd_of {P : Kernel → Prop}
    (hP : ∀ Ls : List Kernel, (∀ L ∈ Ls, P L) → ∀ lam nu, Summable (openWeight Ls lam nu))
    {K : Kernel} {Ks : List Kernel} (hKs : ∀ L ∈ K :: Ks, P L)
    (hcyc : Summable (cycWeight (K :: Ks))) :
    ktrace (klist (K :: Ks))
      = ∑' c : Fin (Ks.length + 1) → Part,
          cycProd (fun i : Fin (Ks.length + 1) => (K :: Ks).get i) c := by
  have hsupp : Function.support (cycWeight (K :: Ks))
      ⊆ Set.range (closePath (n := Ks.length)) := by
    intro c hc
    have hlast : (Fin.last (K :: Ks).length : Fin ((K :: Ks).length + 1))
        = Fin.last (Ks.length + 1) := Fin.ext rfl
    refine ⟨fun i => c i.castSucc, closePath_init c ?_⟩
    by_contra hne
    rw [Function.mem_support, cycWeight, hlast, kone, ite_eq_right hne, mul_zero] at hc
    exact hc rfl
  rw [ktrace_klist_eq_tsum_of hP hKs hcyc]
  exact (Function.Injective.tsum_eq injective_closePath hsupp).symm.trans
    (tsum_congr fun c => cycWeight_closePath K Ks c)

/-- **The cyclic reading of the trace of a step-bounded product with a grading factor.** -/
theorem ktrace_klist_eq_tsum_cycProd {K : Kernel} {Ks : List Kernel}
    (hKs : ∀ L ∈ K :: Ks, StepBdd L) {j : Fin (K :: Ks).length}
    (hj : GradeStepBdd ((K :: Ks).get j)) :
    ktrace (klist (K :: Ks))
      = ∑' c : Fin (Ks.length + 1) → Part,
          cycProd (fun i : Fin (Ks.length + 1) => (K :: Ks).get i) c :=
  ktrace_klist_eq_tsum_cycProd_of (fun _ h => summable_openWeight h) hKs
    (summable_cycWeight hKs hj)

/-- **The cyclic reading of the trace of a grade-bounded product.** This is the one the
slot-ordered reading of the cycle needs: it keeps one grading per slot, so its strip factors carry
the argument `1` and are not step-bounded, while every slot factor is grade-bounded. -/
theorem ktrace_klist_eq_tsum_cycProd_of_grade {K : Kernel} {Ks : List Kernel}
    (hKs : ∀ L ∈ K :: Ks, GradeBdd L) :
    ktrace (klist (K :: Ks))
      = ∑' c : Fin (Ks.length + 1) → Part,
          cycProd (fun i : Fin (Ks.length + 1) => (K :: Ks).get i) c :=
  ktrace_klist_eq_tsum_cycProd_of (fun _ h => summable_openWeight_of_grade h) hKs
    (summable_cycWeight_of_grade hKs (Nat.succ_pos _))

/-! ### The form a concrete word uses -/

theorem cycProd_congr {n : ℕ} [NeZero n] {F G : Fin n → Kernel} (h : ∀ i, F i = G i)
    (c : Fin n → Part) : cycProd F c = cycProd G c := by
  rw [cycProd, cycProd]
  exact Finset.prod_congr rfl fun i _ => by rw [h]

/-- **The cyclic reading, with the word given as a family rather than a list.** A concrete word is
built as a list, so `Ks.length` is not syntactically the number of slots and `Ks.get` is not the
indexed family the argument wants to read; this form takes both identifications as hypotheses and
so applies to any word whose length is known. -/
theorem ktrace_klist_eq_tsum_cycProd_of_length {P : Kernel → Prop}
    (hP : ∀ Ls : List Kernel, (∀ L ∈ Ls, P L) → ∀ lam nu, Summable (openWeight Ls lam nu))
    {Ks : List Kernel} {n : ℕ} [NeZero n] (hn : Ks.length = n) (hKs : ∀ L ∈ Ks, P L)
    (hcyc : Summable (cycWeight Ks)) (F : Fin n → Kernel)
    (hF : ∀ i : Fin n, F i = Ks.get (Fin.cast hn.symm i)) :
    ktrace (klist Ks) = ∑' c : Fin n → Part, cycProd F c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  cases Ks with
  | nil => exact absurd hn (by simp)
  | cons K Ks =>
    have hlen : Ks.length = m := by simpa using hn
    subst hlen
    rw [ktrace_klist_eq_tsum_cycProd_of hP hKs hcyc]
    exact (tsum_congr fun c => cycProd_congr (fun i => by rw [hF]; rfl) c).symm

/-- **The cyclic reading of a step-bounded word with a grading factor, as a family.** -/
theorem ktrace_klist_eq_tsum_cycProd_length {Ks : List Kernel} {n : ℕ} [NeZero n]
    (hn : Ks.length = n) (hKs : ∀ L ∈ Ks, StepBdd L) {j : Fin Ks.length}
    (hj : GradeStepBdd (Ks.get j))
    (F : Fin n → Kernel) (hF : ∀ i : Fin n, F i = Ks.get (Fin.cast hn.symm i)) :
    ktrace (klist Ks) = ∑' c : Fin n → Part, cycProd F c :=
  ktrace_klist_eq_tsum_cycProd_of_length (fun _ h => summable_openWeight h) hn hKs
    (summable_cycWeight hKs hj) F hF

/-- **The cyclic reading of a grade-bounded word, as a family.** This is the form the slot-ordered
reading of the cycle uses. -/
theorem ktrace_klist_eq_tsum_cycProd_length_of_grade {Ks : List Kernel} {n : ℕ} [NeZero n]
    (hn : Ks.length = n) (hKs : ∀ L ∈ Ks, GradeBdd L) (F : Fin n → Kernel)
    (hF : ∀ i : Fin n, F i = Ks.get (Fin.cast hn.symm i)) :
    ktrace (klist Ks) = ∑' c : Fin n → Part, cycProd F c :=
  ktrace_klist_eq_tsum_cycProd_of_length (fun _ h => summable_openWeight_of_grade h) hn hKs
    (summable_cycWeight_of_grade hKs (by rw [hn]; exact Nat.pos_of_ne_zero (NeZero.ne n))) F hF

end HJO.CylindricProduct
