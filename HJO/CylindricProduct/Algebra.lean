/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CylindricProduct.Summable
public meta import HJO.Attr

/-! # The algebra of kernels: unit, associativity, concatenation and rotation

Products of kernels are naturally written without brackets, and factors are moved around the trace
freely. Neither is available from the definitions: `kmul` is a sum over the intermediate partition,
so associativity is an interchange of two such sums and holds only under a summability side
condition, and `klist` is bracketed to the right, so a product of two lists is not a product of
lists on the nose. This file supplies the four facts that make the bracket-free reading legitimate
for the kernels the argument uses, all of them under the step bound of
`HJO.CylindricProduct.Summable`:

* `kone` is a two-sided unit for `kmul`, with no side condition -- the sum collapses to one term;
* `kmul` is associative on step-bounded kernels, both bracketings being the sum of the double
  family `K(λ,τ)L(τ,σ)M(σ,ν)` over the pair `(τ, σ)`;
* `klist (Ks ++ Ls) = kmul (klist Ks) (klist Ls)`, so a list may be cut anywhere;
* the trace is invariant under rotating the list, provided some factor is grade-bounded, which is
  what makes the double family of the cyclic exchange summable.

The bound that does the work in each case is the same one as in
`HJO.CylindricProduct.Summable`: a step-bounded kernel forces the sizes of its two arguments
together, and a grade-bounded kernel forces the size of its first argument outright. The only new
point is the triangle inequality `sizeDist_le_add`, which bounds the *second* intermediate
partition of a triple product against the first, and is what makes the double family live in a
product of two finite sets.
-/

@[expose] public section

open Finset Filter PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-! ### The identity kernel is a unit -/

/-- The identity kernel is a left unit: the sum over the intermediate partition collapses to the
single term at the first argument. -/
theorem kone_kmul (K : Kernel) : kmul kone K = K := by
  funext lam nu
  rw [kmul]
  refine (tsum_eq_single lam fun tau htau => ?_).trans ?_
  · rw [kone, ite_eq_right (Ne.symm htau), zero_mul]
  · rw [kone, ite_eq_left rfl, one_mul]

/-- The identity kernel is a right unit. -/
theorem kmul_kone (K : Kernel) : kmul K kone = K := by
  funext lam nu
  rw [kmul]
  refine (tsum_eq_single nu fun tau htau => ?_).trans ?_
  · rw [kone, ite_eq_right htau, mul_zero]
  · rw [kone, ite_eq_left rfl, mul_one]

@[simp] theorem klist_nil : klist [] = kone := rfl

@[simp] theorem klist_cons (K : Kernel) (Ks : List Kernel) :
    klist (K :: Ks) = kmul K (klist Ks) := rfl

/-! ### Associativity -/

/-- **The double family of a triple product is summable.** The first factor bounds the size
distance from `λ` to the first intermediate partition and the second bounds the distance from there
to the second, so by the triangle inequality both intermediate partitions lie within a bounded
distance of `λ`, and there are finitely many of those. -/
theorem summable_kmul_pair {K L M : Kernel} (hK : StepBdd K) (hL : StepBdd L) (_hM : StepBdd M)
    (lam nu : Part) :
    Summable fun p : Part × Part => K lam p.1 * L p.1 p.2 * M p.2 nu := by
  refine summable_of_dvd_of_finite
    (g := fun p : Part × Part => sizeDist lam p.1 + sizeDist p.1 p.2) (fun p => ?_) fun n => ?_
  · rw [pow_add]
    exact Dvd.dvd.mul_right (mul_dvd_mul (hK lam p.1) (hL p.1 p.2)) _
  · refine ((finite_sizeDist_le lam n).prod (finite_sizeDist_le lam n)).subset ?_
    rintro ⟨tau, sigma⟩ h
    simp only [Set.mem_ofPred_eq] at h
    have htri : sizeDist lam sigma ≤ sizeDist lam tau + sizeDist tau sigma :=
      sizeDist_le_add lam tau sigma
    exact Set.mk_mem_prod (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega)

/-- **The kernel product is associative on step-bounded kernels.** Both bracketings are the sum of
`K(λ,τ)L(τ,σ)M(σ,ν)` over the pair of intermediate partitions, one summing `τ` first and the other
`σ`. -/
@[hjo "lem_tame_assoc"]
theorem kmul_assoc {K L M : Kernel} (hK : StepBdd K) (hL : StepBdd L) (hM : StepBdd M) :
    kmul (kmul K L) M = kmul K (kmul L M) := by
  funext lam nu
  have hpair : Summable fun p : Part × Part => K lam p.1 * L p.1 p.2 * M p.2 nu :=
    summable_kmul_pair hK hL hM lam nu
  have hfg : ∀ q : Part × Part,
      (fun p : Part × Part => K lam p.1 * L p.1 p.2 * M p.2 nu)
          ((Equiv.prodComm Part Part) q)
        = K lam q.2 * L q.2 q.1 * M q.1 nu := fun _ => rfl
  have hswap : Summable fun q : Part × Part => K lam q.2 * L q.2 q.1 * M q.1 nu :=
    ((Equiv.prodComm Part Part).summable_iff.mpr hpair).congr hfg
  have hleft : kmul (kmul K L) M lam nu
      = ∑' p : Part × Part, K lam p.1 * L p.1 p.2 * M p.2 nu := by
    calc kmul (kmul K L) M lam nu
        = ∑' sigma, (∑' tau, K lam tau * L tau sigma) * M sigma nu := rfl
      _ = ∑' sigma, ∑' tau, K lam tau * L tau sigma * M sigma nu :=
          tsum_congr fun sigma =>
            ((summable_kmul hK hL lam sigma).tsum_mul_right (M sigma nu)).symm
      _ = ∑' q : Part × Part, K lam q.2 * L q.2 q.1 * M q.1 nu := hswap.tsum_prod.symm
      _ = ∑' p : Part × Part, K lam p.1 * L p.1 p.2 * M p.2 nu :=
          (tsum_congr fun q => (hfg q).symm).trans
            ((Equiv.prodComm Part Part).tsum_eq
              fun p : Part × Part => K lam p.1 * L p.1 p.2 * M p.2 nu)
  have hright : kmul K (kmul L M) lam nu
      = ∑' p : Part × Part, K lam p.1 * L p.1 p.2 * M p.2 nu := by
    calc kmul K (kmul L M) lam nu
        = ∑' tau, K lam tau * ∑' sigma, L tau sigma * M sigma nu := rfl
      _ = ∑' tau, ∑' sigma, K lam tau * L tau sigma * M sigma nu :=
          tsum_congr fun tau =>
            (((summable_kmul hL hM tau nu).tsum_mul_left (K lam tau)).symm.trans
              (tsum_congr fun sigma => (mul_assoc _ _ _).symm))
      _ = ∑' p : Part × Part, K lam p.1 * L p.1 p.2 * M p.2 nu := hpair.tsum_prod.symm
  rw [hleft, hright]

/-! ### Cutting and concatenating a list -/

/-- **A list of kernels may be cut anywhere.** The product of a concatenation is the product of the
two products. -/
theorem klist_append {Ks Ls : List Kernel} (hKs : ∀ K ∈ Ks, StepBdd K)
    (hLs : ∀ L ∈ Ls, StepBdd L) :
    klist (Ks ++ Ls) = kmul (klist Ks) (klist Ls) := by
  induction Ks with
  | nil => rw [List.nil_append, klist_nil, kone_kmul]
  | cons K Ks ih =>
    have hK : StepBdd K := hKs K List.mem_cons_self
    have hKs' : ∀ L ∈ Ks, StepBdd L := fun L hL => hKs L (List.mem_cons_of_mem _ hL)
    rw [List.cons_append, klist_cons, ih hKs', klist_cons,
      kmul_assoc hK (StepBdd.klist hKs') (StepBdd.klist hLs)]

/-- Moving the head of a list to its tail, as a product of two kernels. -/
theorem klist_snoc {K : Kernel} (hK : StepBdd K) {Ks : List Kernel}
    (hKs : ∀ L ∈ Ks, StepBdd L) : klist (Ks ++ [K]) = kmul (klist Ks) K := by
  rw [klist_append hKs (fun L hL => by rwa [List.mem_singleton.mp hL]), klist_cons, klist_nil,
    kmul_kone]

/-! ### Rotating a list under the trace -/

/-- **The double family of a cyclic exchange is summable.** The grade-bounded factor forces the
size of the partition standing between the two kernels, and the step bound of the other factor then
forces the size of the partition standing outside them. -/
theorem summable_ktrace_pair {K L : Kernel} (hK : StepBdd K) (hL : GradeBdd L) :
    Summable fun p : Part × Part => K p.1 p.2 * L p.2 p.1 := by
  refine summable_of_dvd_of_finite
    (g := fun p : Part × Part => p.2.size + sizeDist p.1 p.2) (fun p => ?_) fun n => ?_
  · rw [pow_add, mul_comm ((X : ℤ⟦X⟧) ^ p.2.size)]
    exact mul_dvd_mul (hK p.1 p.2) (hL p.2 p.1)
  · refine ((finite_size_le n).prod (finite_size_le n)).subset ?_
    rintro ⟨tau, sigma⟩ h
    simp only [Set.mem_ofPred_eq] at h
    have hout : tau.size ≤ sizeDist tau sigma + sigma.size := size_le_sizeDist_add tau sigma
    exact Set.mk_mem_prod (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega)

/-- **The trace is invariant under rotating the list.** Moving the head of the list to its tail
leaves the trace unchanged; the side condition of `ktrace_kmul_comm` is met because the tail
contains a grading factor. -/
theorem ktrace_klist_rotate {K : Kernel} (hK : StepBdd K) {Ks : List Kernel}
    (hKs : ∀ L ∈ Ks, StepBdd L) (hgrade : ∃ L ∈ Ks, GradeBdd L) :
    ktrace (klist (K :: Ks)) = ktrace (klist (Ks ++ [K])) := by
  obtain ⟨L, hLmem, hL⟩ := hgrade
  rw [klist_cons, klist_snoc hK hKs,
    ktrace_kmul_comm (summable_ktrace_pair hK (GradeBdd.klist hKs ⟨L, hLmem, hL⟩))]

/-- **The trace is invariant under rotating a list of vertex operators.** The form of
`ktrace_klist_rotate` that the transfer trace uses: every factor is one of the three kernels with a
positive power of `q`, and one of the factors moved to the tail is a grading. -/
theorem ktrace_klist_rotate_vertex {K : Kernel} (hK : IsVertex K) {Ks : List Kernel}
    (hKs : ∀ L ∈ Ks, IsVertex L) {m : ℕ} (hm : 1 ≤ m) (hmem : grading (X ^ m) ∈ Ks) :
    ktrace (klist (K :: Ks)) = ktrace (klist (Ks ++ [K])) :=
  ktrace_klist_rotate hK.stepBdd (fun L hL => (hKs L hL).stepBdd)
    ⟨grading (X ^ m), hmem, GradeBdd.grading hm⟩

end HJO.CylindricProduct
