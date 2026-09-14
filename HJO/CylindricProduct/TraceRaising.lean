/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CylindricProduct.PartitionSum
public meta import HJO.Attr

/-! # The raising trace

`Tr(Q(q^d) Γ_+(x_1) ⋯ Γ_+(x_a)) = (q^d; q^d)_∞^{-1}`, written here without an inverse as
`(q^d; q^d)_∞ Tr(Q(q^d) Γ_+(x_1) ⋯ Γ_+(x_a)) = 1`.

Two steps. First, a product of raising kernels is the identity on the diagonal: a raising kernel
vanishes unless it increases the size, so a product of them vanishes at `(λ, ν)` whenever
`|ν| < |λ|`, and at `(λ, λ)` the only intermediate partition that survives both that vanishing and
the strip condition is `λ` itself, by `IsHStrip.eq_of_size_le`. Each surviving factor is then
`x^0 = 1`. So the trace collapses to `∑_λ q^{d|λ|}`, the grading kernel contributing `q^{d|λ|}` on
the diagonal.

Second, that sum is Euler's, and `selfQPochhammerInf_mul_partGF` evaluates it.

The arguments of the raising kernels play no role: the identity holds for an arbitrary list of
them, which covers in particular the arguments `x_{s'} = q^{d-1-s'}` of the sorted transfer
kernel.
-/

@[expose] public section

open Finset PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-! ### A product of raising kernels cannot lower the size -/

/-- **A product of raising kernels vanishes where it would lower the size.** Each factor is
supported on the pairs whose second partition dominates the first, so the product is supported on
the pairs `(λ, ν)` with `|λ| ≤ |ν|`. -/
theorem klist_gammaPlus_eq_zero (xs : List ℤ⟦X⟧) {lam nu : Part} (h : nu.size < lam.size) :
    klist (xs.map gammaPlus) lam nu = 0 := by
  induction xs generalizing lam with
  | nil =>
    have hne : lam ≠ nu := fun hh => absurd h (by rw [hh]; exact lt_irrefl _)
    simp only [List.map_nil, klist, kone]
    exact ite_eq_right hne
  | cons x xs ih =>
    simp only [List.map_cons, klist, kmul]
    refine (tsum_congr fun tau => ?_).trans tsum_zero
    by_cases h1 : IsHStrip tau lam
    · rw [ih (lt_of_lt_of_le h h1.size_le), mul_zero]
    · rw [gammaPlus_of_not h1, zero_mul]

/-- **A product of raising kernels is the identity on the diagonal.** Both the size bound and the
strip condition must hold at every intermediate partition, and together they force each step to be
trivial; a trivial step contributes `x^0 = 1`. -/
theorem klist_gammaPlus_diag (xs : List ℤ⟦X⟧) (lam : Part) :
    klist (xs.map gammaPlus) lam lam = 1 := by
  induction xs generalizing lam with
  | nil => simp only [List.map_nil, klist, kone, ite_true]
  | cons x xs ih =>
    simp only [List.map_cons, klist, kmul]
    refine (tsum_eq_single lam fun tau htau => ?_).trans ?_
    · by_cases h1 : IsHStrip tau lam
      · rcases le_or_gt tau.size lam.size with hle | hlt
        · exact absurd (h1.eq_of_size_le hle).symm htau
        · rw [klist_gammaPlus_eq_zero xs hlt, mul_zero]
      · rw [gammaPlus_of_not h1, zero_mul]
    · rw [gammaPlus_of (isHStrip_self lam), Nat.sub_self, pow_zero, ih, one_mul]

/-! ### The raising trace -/

/-- The trace of a grading kernel against raising kernels is the partition sum: on the diagonal the
raising factors contribute `1` and the grading factor contributes `q^{d|λ|}`. -/
theorem ktrace_grading_klist_gammaPlus (d : ℕ) (xs : List ℤ⟦X⟧) :
    ktrace (klist (grading (X ^ d) :: xs.map gammaPlus)) = partGF d := by
  rw [ktrace, partGF]
  refine tsum_congr fun lam => ?_
  rw [klist, grading_kmul, klist_gammaPlus_diag, mul_one, ← pow_mul]

/-- **The raising trace.** `(q^d; q^d)_∞ Tr(Q(q^d) Γ_+(x_1) ⋯ Γ_+(x_a)) = 1`, the inverse-free form
of `Tr(Q(q^d) Γ_+(x_1) ⋯ Γ_+(x_a)) = (q^d; q^d)_∞^{-1}`. The arguments of the raising kernels are
arbitrary; only the grading argument matters. -/
@[hjo "lem_trace_raising"]
theorem selfQPochhammerInf_mul_ktrace_raising {d : ℕ} (hd : 0 < d) (xs : List ℤ⟦X⟧) :
    ((X ^ d; X ^ d)_∞ : ℤ⟦X⟧) * ktrace (klist (grading (X ^ d) :: xs.map gammaPlus)) = 1 := by
  rw [ktrace_grading_klist_gammaPlus, selfQPochhammerInf_mul_partGF hd]

/-- **The raising trace at the arguments of the sorted transfer kernel.** The specialisation of
`selfQPochhammerInf_mul_ktrace_raising` to the raising slots of the rotated step word, which is the
factor of `transferKernel` standing to the right of the grading. -/
@[hjo "lem_trace_raising"]
theorem selfQPochhammerInf_mul_ktrace_raisingSlots {a b : ℕ} (hd : 0 < a + b) :
    ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧) *
        ktrace (klist (grading (X ^ (a + b)) ::
          ((raisingSlots a b).map fun s => gammaPlus (X ^ (a + b - 1 - s))))) = 1 := by
  have hmap : ((raisingSlots a b).map fun s => gammaPlus (X ^ (a + b - 1 - s)))
      = (((raisingSlots a b).map fun s => (X : ℤ⟦X⟧) ^ (a + b - 1 - s))).map gammaPlus := by
    rw [List.map_map]
    rfl
  rw [hmap]
  exact selfQPochhammerInf_mul_ktrace_raising hd _

end HJO.CylindricProduct
