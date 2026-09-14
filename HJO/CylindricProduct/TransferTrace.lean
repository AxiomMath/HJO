/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Finset.Sort
public import QSeriesLib.RingTheory.PowerSeries.DiscreteTopology
public import HJO.CylindricProduct.DiagSlices
public meta import HJO.Attr

/-! # Kernels on partitions, the vertex operators and the sorted transfer kernel

A *kernel* assigns a formal power series to each ordered pair of partitions. Kernels are
multiplied by summing over the intermediate partition and traced by summing over the diagonal.
Both sums are the unconditional sums of the coefficientwise topology on `ℤ⟦X⟧`; in that topology
a family is summable exactly when each coefficient receives only finitely many nonzero
contributions, and that is the side condition under which the product and the trace are defined.
The predicates `MulSummable` and `TraceSummable` name those conditions, so a statement that needs
them carries them as hypotheses rather than hiding them in the definition.

Three kernels are singled out: the lowering operator `Γ_-(y)`, supported on the pairs
`(λ, ν)` with `λ/ν` a horizontal strip, the raising operator `Γ_+(x)`, supported on the pairs with
`ν/λ` a horizontal strip, and the diagonal grading `Q(u)`.

The **sorted** transfer kernel is the one this development uses. The slot-ordered product is not
available: keeping one grading per slot forces the strip factors to carry the argument `1`, and
`Γ_±(1)` is not summable. Sorting the gradings out of the way produces the positive powers
`y_s = q^{s+1}` and `x_{s'} = q^{d-1-s'}`, at the cost of a prefactor -- which is why the sorted
form, and not the slot-ordered one, is the definition.
-/

@[expose] public section

open Finset PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

noncomputable instance : DecidableEq Part := Classical.decEq _

noncomputable instance instDecidableIsHStrip (ν μ : Part) : Decidable (IsHStrip ν μ) :=
  Classical.dec _

/-! ### Kernels, their product and their trace -/

/-- A **kernel**: an assignment of a formal power series in `q` to each ordered pair of
partitions. -/
@[hjo "def_partition_kernel"]
abbrev Kernel : Type := Part → Part → ℤ⟦X⟧

/-- The **kernel product** `(K L)(λ, ν) = ∑_τ K(λ, τ) L(τ, ν)`. The sum is the unconditional sum
of the coefficientwise topology of `ℤ⟦X⟧`, so it is the intended product exactly when the family
summed over `τ` is summable, i.e. when each coefficient of `q` receives only finitely many nonzero
contributions; see `MulSummable`. -/
@[hjo "def_kernel_mul"]
noncomputable def kmul (K L : Kernel) : Kernel := fun lam nu => ∑' tau, K lam tau * L tau nu

/-- The side condition of the kernel product: for every pair the family summed over the
intermediate partition is summable, i.e. each coefficient of `q` receives only finitely many
nonzero contributions. -/
def MulSummable (K L : Kernel) : Prop := ∀ lam nu, Summable fun tau => K lam tau * L tau nu

/-- The **kernel trace** `Tr K = ∑_λ K(λ, λ)`, again the unconditional sum of the coefficientwise
topology; see `TraceSummable` for the side condition under which it is the intended sum. -/
@[hjo "def_kernel_trace"]
noncomputable def ktrace (K : Kernel) : ℤ⟦X⟧ := ∑' lam, K lam lam

/-- The side condition of the kernel trace: the diagonal family is summable, i.e. each coefficient
of `q` receives only finitely many nonzero contributions. -/
def TraceSummable (K : Kernel) : Prop := Summable fun lam => K lam lam

/-- The identity kernel, the unit of the kernel product. -/
noncomputable def kone : Kernel := fun lam nu => if lam = nu then 1 else 0

/-- The ordered product of a list of kernels, the empty list giving the identity kernel. -/
noncomputable def klist : List Kernel → Kernel
  | [] => kone
  | K :: Ks => kmul K (klist Ks)

/-! ### The three kernels -/

/-- The **lowering kernel** `Γ_-(y)(λ, ν) = y^{|λ| - |ν|}` on the pairs where `λ/ν` is a
horizontal strip, and `0` elsewhere. -/
@[hjo "def_gamma_minus"]
noncomputable def gammaMinus (y : ℤ⟦X⟧) : Kernel := fun lam nu =>
  if IsHStrip lam nu then y ^ (lam.size - nu.size) else 0

/-- The **raising kernel** `Γ_+(x)(λ, ν) = x^{|ν| - |λ|}` on the pairs where `ν/λ` is a horizontal
strip, and `0` elsewhere. -/
@[hjo "def_gamma_plus"]
noncomputable def gammaPlus (x : ℤ⟦X⟧) : Kernel := fun lam nu =>
  if IsHStrip nu lam then x ^ (nu.size - lam.size) else 0

/-- The **grading kernel** `Q(u)(λ, ν) = u^{|λ|}` on the diagonal and `0` elsewhere. -/
@[hjo "def_grading_kernel"]
noncomputable def grading (u : ℤ⟦X⟧) : Kernel := fun lam nu =>
  if lam = nu then u ^ lam.size else 0

theorem gammaMinus_of {y : ℤ⟦X⟧} {lam nu : Part} (h : IsHStrip lam nu) :
    gammaMinus y lam nu = y ^ (lam.size - nu.size) := by simp [gammaMinus, h]

theorem gammaMinus_of_not {y : ℤ⟦X⟧} {lam nu : Part} (h : ¬ IsHStrip lam nu) :
    gammaMinus y lam nu = 0 := by simp [gammaMinus, h]

theorem gammaPlus_of {x : ℤ⟦X⟧} {lam nu : Part} (h : IsHStrip nu lam) :
    gammaPlus x lam nu = x ^ (nu.size - lam.size) := by simp [gammaPlus, h]

theorem gammaPlus_of_not {x : ℤ⟦X⟧} {lam nu : Part} (h : ¬ IsHStrip nu lam) :
    gammaPlus x lam nu = 0 := by simp [gammaPlus, h]

theorem grading_diag {u : ℤ⟦X⟧} (lam : Part) : grading u lam lam = u ^ lam.size := by
  simp [grading]

theorem grading_of_ne {u : ℤ⟦X⟧} {lam nu : Part} (h : lam ≠ nu) : grading u lam nu = 0 := by
  simp [grading, h]

/-! ### The grading kernel moves the arguments -/

/-- Multiplying by a diagonal kernel on the left picks out the diagonal entry. -/
theorem grading_kmul (u : ℤ⟦X⟧) (L : Kernel) (lam nu : Part) :
    kmul (grading u) L lam nu = u ^ lam.size * L lam nu := by
  rw [kmul]
  refine (tsum_eq_single lam fun tau htau => ?_).trans ?_
  · rw [grading_of_ne (Ne.symm htau), zero_mul]
  · rw [grading_diag]

/-- Multiplying by a diagonal kernel on the right picks out the diagonal entry. -/
theorem kmul_grading (u : ℤ⟦X⟧) (K : Kernel) (lam nu : Part) :
    kmul K (grading u) lam nu = K lam nu * u ^ nu.size := by
  rw [kmul]
  refine (tsum_eq_single nu fun tau htau => ?_).trans ?_
  · rw [grading_of_ne htau, mul_zero]
  · rw [grading_diag]

/-- **The grading moves the lowering argument**: `Q(q^k) Γ_-(q^m) = Γ_-(q^{k+m}) Q(q^k)`. Stated
for every `k` and `m`; no positivity of `k` or `m` is needed for this identity. -/
@[hjo "lem_grading_gamma_minus"]
theorem grading_kmul_gammaMinus (k m : ℕ) :
    kmul (grading (X ^ k)) (gammaMinus (X ^ m))
      = kmul (gammaMinus (X ^ (k + m))) (grading (X ^ k)) := by
  funext lam nu
  rw [grading_kmul, kmul_grading]
  by_cases h : IsHStrip lam nu
  · obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le h.size_le
    have hsub : lam.size - nu.size = s := by omega
    rw [gammaMinus_of h, gammaMinus_of h, hsub]
    simp only [← pow_mul, ← pow_add]
    congr 1
    rw [hs]; ring
  · rw [gammaMinus_of_not h, gammaMinus_of_not h, mul_zero, zero_mul]

/-- **The grading moves the raising argument**: `Γ_+(q^m) Q(q^k) = Q(q^k) Γ_+(q^{k+m})`. Stated
for every `k` and `m`; no positivity of `k` or `m` is needed for this identity. -/
@[hjo "lem_grading_gamma_plus"]
theorem gammaPlus_kmul_grading (k m : ℕ) :
    kmul (gammaPlus (X ^ m)) (grading (X ^ k))
      = kmul (grading (X ^ k)) (gammaPlus (X ^ (k + m))) := by
  funext lam nu
  rw [kmul_grading, grading_kmul]
  by_cases h : IsHStrip nu lam
  · obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le h.size_le
    have hsub : nu.size - lam.size = s := by omega
    rw [gammaPlus_of h, gammaPlus_of h, hsub]
    simp only [← pow_mul, ← pow_add]
    congr 1
    rw [hs]; ring
  · rw [gammaPlus_of_not h, gammaPlus_of_not h, mul_zero, zero_mul]

/-! ### The trace is cyclic -/

/-- **The trace is cyclic**: `Tr (K L) = Tr (L K)`. The hypothesis is that the double family
whose sum both traces are is summable, i.e. that each coefficient of `q` receives only finitely
many nonzero contributions in either order of summation. -/
@[hjo "lem_trace_cyclic"]
theorem ktrace_kmul_comm {K L : Kernel}
    (h : Summable fun p : Part × Part => K p.1 p.2 * L p.2 p.1) :
    ktrace (kmul K L) = ktrace (kmul L K) := by
  have hswap : ∀ p : Part × Part,
      (fun q : Part × Part => L q.1 q.2 * K q.2 q.1) ((Equiv.prodComm Part Part) p)
        = K p.1 p.2 * L p.2 p.1 := fun p => mul_comm _ _
  have h' : Summable fun q : Part × Part => L q.1 q.2 * K q.2 q.1 :=
    (Equiv.prodComm Part Part).summable_iff.mp (h.congr fun p => (hswap p).symm)
  calc ktrace (kmul K L)
      = ∑' p : Part × Part, K p.1 p.2 * L p.2 p.1 := (h.tsum_prod).symm
    _ = ∑' q : Part × Part, L q.1 q.2 * K q.2 q.1 :=
        ((Equiv.prodComm Part Part).tsum_eq
          (fun q : Part × Part => L q.1 q.2 * K q.2 q.1)).symm.trans
          (tsum_congr hswap) |>.symm
    _ = ktrace (kmul L K) := h'.tsum_prod

/-! ### The sorted transfer kernel -/

/-- The rotation offset `r`: the least `r` for which slot `d - 1 - r` is a lowering slot. When
some slot is lowering -- that is, when `b > 0` -- this is a genuine minimum, at most `d - 1`. -/
noncomputable def rotOffset (a b : ℕ) : ℕ := sInf {r | ¬ IsRaising a b (a + b - 1 - r)}

/-- Slot `t` of the step word rotated by `rotOffset a b`, so that slot `d - 1` of the rotated
word is the lowering slot `d - 1 - r` of the original. -/
noncomputable def rotSlot (a b t : ℕ) : ℕ := (t + (a + b) - rotOffset a b % (a + b)) % (a + b)

/-- The lowering slots of the rotated step word, in increasing order. -/
noncomputable def loweringSlots (a b : ℕ) : List ℕ :=
  ((range (a + b)).filter fun t => ¬ IsRaising a b (rotSlot a b t)).sort (· ≤ ·)

/-- The raising slots of the rotated step word, in increasing order. -/
noncomputable def raisingSlots (a b : ℕ) : List ℕ :=
  ((range (a + b)).filter fun t => IsRaising a b (rotSlot a b t)).sort (· ≤ ·)

/-- The **sorted transfer kernel** `S`: with `w` the step word rotated so that slot `d - 1` is
lowering, `y_s = q^{s+1}` at a lowering slot `s` and `x_{s'} = q^{d-1-s'}` at a raising slot `s'`,
this is the product of the `Γ_-(y_s)` over the lowering slots in increasing order, then `Q(q^d)`,
then the `Γ_+(x_{s'})` over the raising slots in increasing order.

The slot-ordered product is not available: keeping one grading per slot forces the strip factors
to carry the argument `1`, and `Γ_±(1)` is not summable. Sorting the gradings out is what makes
every argument here a positive power of `q`, and the cost of the sorting appears as a prefactor in
the identity for `C_c(q)`, not hidden in this definition. -/
@[hjo "def_transfer_kernel"]
noncomputable def transferKernel (a b : ℕ) : Kernel :=
  klist (((loweringSlots a b).map fun s => gammaMinus (X ^ (s + 1)))
    ++ grading (X ^ (a + b))
      :: ((raisingSlots a b).map fun s => gammaPlus (X ^ (a + b - 1 - s))))

end HJO.CylindricProduct
