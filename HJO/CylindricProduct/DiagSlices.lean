/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Determinant.DetCoeff
public import HJO.CylindricProduct.Partition
public import HJO.CylindricProduct.StepWord
public meta import HJO.Attr

/-! # Diagonal functions and their slices

A *diagonal function* at `(a, b)` is a finitely supported `W : ℕ → ℕ` with `W (w + a) ≤ W w` and
`W (w + b) ≤ W w`. Reading a cylindric partition of the balanced profile along its diagonals is a
bijection onto the diagonal functions carrying the volume to `∑_w W w`; that bijection is already
available in `HJO.Determinant.DetCoeff` in its bounded form, and this file removes the bound (a
finitely supported function of the naturals is automatically bounded) and packages the two
directions as an `Equiv`.

Cutting a diagonal function into the `d = a + b` arithmetic progressions modulo `d` produces its
*slices*: the slice at `t` is `i ↦ W (t + i d)`. Each slice is a partition, the slice sizes total
`∑_w W w`, and consecutive slices differ by a horizontal strip.

*Consecutive* is meant in the labelling by the step word, not in the labelling by the residue:
the shifts available to a diagonal function move the residue by `a` (or, what is the same thing
modulo `d`, by `-b`), so the slices ordered by the step word are those at the residues
`t * a % d` for `t = 0, 1, …, d - 1`. At a lowering slot `t` the residue advances by `a`, so
`W` decreases and the strip is `μ^t / μ^{t+1}`; at a raising slot it drops by `b`, so `W`
increases and the strip is `μ^{t+1} / μ^t`. This is the content of `isHStrip_slice_of_isRaising`
and `isHStrip_slice_of_not_isRaising`, which is why they read the slot's residue rather than the
slot itself.
-/

@[expose] public section

open Finset

namespace HJO.CylindricProduct

/-! ### Diagonal functions -/

/-- A **diagonal function**: a finitely supported function of the naturals that does not increase
when its argument is advanced by `a` or by `b`. -/
@[hjo "def_diag_fun"]
structure IsDiagFun (a b : ℕ) (W : ℕ → ℕ) : Prop where
  /-- Advancing the position by `a` does not increase the value. -/
  step_left : ∀ w, W (w + a) ≤ W w
  /-- Advancing the position by `b` does not increase the value. -/
  step_right : ∀ w, W (w + b) ≤ W w
  /-- The function vanishes at all large positions. -/
  vanish : ∃ B, ∀ w, B ≤ w → W w = 0

/-- A finitely supported function of the naturals is bounded, so a diagonal function is one of
the bounded diagonal functions of `HJO.Determinant.DetCoeff`. -/
theorem IsDiagFun.exists_bounded {a b : ℕ} {W : ℕ → ℕ} (hW : IsDiagFun a b W) :
    ∃ N, HJO.DetCoeff.IsDiagFun a b N W := by
  obtain ⟨B, hB⟩ := hW.vanish
  refine ⟨(range B).sup W, hW.step_left, hW.step_right, fun w => ?_, ⟨B, hB⟩⟩
  by_cases hw : w < B
  · exact Finset.le_sup (f := W) (mem_range.mpr hw)
  · rw [hB w (by omega)]; exact Nat.zero_le _

/-- Every cylindric partition has bounded entries: its rows are `a`-periodic and each is
weakly decreasing, so the finitely many first entries bound them all. -/
theorem exists_boundedBy {a b : ℕ} (ha : 0 < a) {l : ℕ → ℕ → ℕ}
    (hl : HJO.Cylindric.IsCylindric a (HJO.Cylindric.profile a b) l) :
    ∃ N, HJO.Cylindric.BoundedBy N l := by
  refine ⟨(range a).sup fun i => l i 0, fun i j => ?_⟩
  refine le_trans (hl.antitone i (Nat.zero_le j)) ?_
  rw [← HJO.DetCoeff.row_mod_eq hl.periodic i 0]
  exact Finset.le_sup (f := fun i => l i 0) (mem_range.mpr (Nat.mod_lt _ ha))

/-- The diagonal reading of a cylindric partition of the balanced profile is a diagonal
function. -/
theorem isDiagFun_diagOfCyl {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) {l : ℕ → ℕ → ℕ}
    (hl : HJO.Cylindric.IsCylindric a (HJO.Cylindric.profile a b) l) :
    IsDiagFun a b (HJO.DetCoeff.diagOfCyl a b l) := by
  obtain ⟨N, hbd⟩ := exists_boundedBy ha hl
  have h := HJO.DetCoeff.isDiagFun_diagOfCyl hab ha hl hbd
  exact ⟨h.step_left, h.step_right, h.vanish⟩

/-- The array read off a diagonal function is a cylindric partition of the balanced profile. -/
theorem isCylindric_cylOfDiag {a b : ℕ} (ha : 0 < a) {W : ℕ → ℕ} (hW : IsDiagFun a b W) :
    HJO.Cylindric.IsCylindric a (HJO.Cylindric.profile a b) (HJO.DetCoeff.cylOfDiag a b W) := by
  obtain ⟨N, hW'⟩ := hW.exists_bounded
  exact HJO.DetCoeff.isCylindric_cylOfDiag ha hW'

/-- **Cylindric partitions are diagonal functions.** Reading a cylindric partition of the
balanced profile along its diagonals is a bijection onto the diagonal functions; its inverse
assembles the array whose entry in row `i`, column `j` is the value at the diagonal position
`i b mod a + a j`. -/
@[hjo "lem_cyl_diag_bijection"]
noncomputable def cylDiagEquiv {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) :
    {l : ℕ → ℕ → ℕ // HJO.Cylindric.IsCylindric a (HJO.Cylindric.profile a b) l} ≃
      {W : ℕ → ℕ // IsDiagFun a b W} where
  toFun l := ⟨HJO.DetCoeff.diagOfCyl a b l.1, isDiagFun_diagOfCyl hab ha l.2⟩
  invFun W := ⟨HJO.DetCoeff.cylOfDiag a b W.1, isCylindric_cylOfDiag ha W.2⟩
  left_inv l := Subtype.ext (HJO.DetCoeff.cylOfDiag_diagOfCyl hab ha l.2.periodic)
  right_inv W := Subtype.ext (HJO.DetCoeff.diagOfCyl_cylOfDiag hab ha W.1)

/-- **The bijection preserves the volume**: the volume of a cylindric partition is the total of
the values of its diagonal function. -/
@[hjo "lem_cyl_diag_bijection"]
theorem cylVolume_eq_finsum {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) {l : ℕ → ℕ → ℕ}
    (hl : HJO.Cylindric.IsCylindric a (HJO.Cylindric.profile a b) l) :
    HJO.Cylindric.cylVolume a l = ∑ᶠ w, HJO.DetCoeff.diagOfCyl a b l w := by
  obtain ⟨N, hW'⟩ := (isDiagFun_diagOfCyl hab ha hl).exists_bounded
  have h := HJO.DetCoeff.cylVolume_cylOfDiag hab ha hW'
  rwa [HJO.DetCoeff.cylOfDiag_diagOfCyl hab ha hl.periodic] at h

/-! ### The slices of a diagonal function -/

/-- The slice `μ^t(W)` of a diagonal function: the sequence whose `i`-th term is `W (t + i d)`,
with `d = a + b`. -/
@[hjo "def_diag_slices"]
def sliceFun (a b : ℕ) (W : ℕ → ℕ) (t i : ℕ) : ℕ := W (t + (a + b) * i)

/-- Successive terms of a slice differ by a period, which is one step by `a` and one by `b`. -/
theorem sliceFun_succ (a b : ℕ) (W : ℕ → ℕ) (t i : ℕ) :
    sliceFun a b W t (i + 1) = W (t + (a + b) * i + a + b) := by
  rw [sliceFun, Nat.mul_add, Nat.mul_one]
  ring_nf

/-- **The slices are partitions.** The terms of a slice weakly decrease, each period being a step
by `a` followed by a step by `b`, and they vanish from some index on. -/
@[hjo "lem_slices_partition"]
noncomputable def slice {a b : ℕ} (hd : 0 < a + b) {W : ℕ → ℕ} (hW : IsDiagFun a b W) (t : ℕ) :
    Part where
  parts := sliceFun a b W t
  antitone' := antitone_nat_of_succ_le fun i => by
    rw [sliceFun_succ]
    exact le_trans (hW.step_right _) (hW.step_left _)
  vanish' := by
    obtain ⟨B, hB⟩ := hW.vanish
    refine ⟨B, fun i hi => hB _ ?_⟩
    have : i ≤ (a + b) * i := Nat.le_mul_of_pos_left i hd
    omega

@[simp] theorem slice_parts {a b : ℕ} (hd : 0 < a + b) {W : ℕ → ℕ} (hW : IsDiagFun a b W)
    (t i : ℕ) : (slice hd hW t).parts i = W (t + (a + b) * i) := rfl

/-- **The slice volumes sum to the total.** Every nonnegative integer is `t + i d` for exactly one
pair `(t, i)` with `t < d`, so summing the slice sizes recovers `∑_w W w`. -/
@[hjo "lem_slices_volume"]
theorem sum_size_slice {a b : ℕ} (hd : 0 < a + b) {W : ℕ → ℕ} (hW : IsDiagFun a b W) :
    ∑ t ∈ range (a + b), (slice hd hW t).size = ∑ᶠ w, W w := by
  obtain ⟨B, hB⟩ := hW.vanish
  have hslice : ∀ t ∈ range (a + b),
      (slice hd hW t).size = ∑ i ∈ range B, W (t + (a + b) * i) := by
    intro t _
    refine Part.size_eq_sum_range _ fun i hi => hB _ ?_
    have : i ≤ (a + b) * i := Nat.le_mul_of_pos_left i hd
    omega
  rw [Finset.sum_congr rfl hslice, Finset.sum_comm, ← HJO.DetCoeff.sum_range_mul_split]
  refine (finsum_eq_finsetSum_of_support_subset _ fun w hw => ?_).symm
  simp only [Function.mem_support] at hw
  rw [Finset.mem_coe, mem_range]
  by_contra hcon
  have hBle : B ≤ (a + b) * B := Nat.le_mul_of_pos_left B hd
  exact hw (hB w (by omega))

/-! ### Consecutive slices differ by a horizontal strip -/

/-- At a lowering slot the residue advances by `a`. -/
theorem succ_mul_mod_of_not_isRaising {a b : ℕ} (hd : 0 < a + b) {t : ℕ}
    (ht : ¬ IsRaising a b t) : (t + 1) * a % (a + b) = t * a % (a + b) + a := by
  have hlt : t * a % (a + b) < a + b := Nat.mod_lt _ hd
  have hstep : (t + 1) * a % (a + b) = (t * a % (a + b) + a) % (a + b) := by
    have h : (t + 1) * a = t * a % (a + b) + a + (a + b) * (t * a / (a + b)) := by
      have := Nat.mod_add_div (t * a) (a + b)
      rw [add_mul, one_mul]; omega
    rw [h, Nat.add_mul_mod_self_left]
  rw [IsRaising, not_le] at ht
  rw [hstep, Nat.mod_eq_of_lt (by omega)]

/-- At a raising slot the residue drops by `b`. -/
theorem succ_mul_mod_of_isRaising {a b : ℕ} (hd : 0 < a + b) {t : ℕ}
    (ht : IsRaising a b t) : (t + 1) * a % (a + b) = t * a % (a + b) - b := by
  have hlt : t * a % (a + b) < a + b := Nat.mod_lt _ hd
  have hstep : (t + 1) * a % (a + b) = (t * a % (a + b) + a) % (a + b) := by
    have h : (t + 1) * a = t * a % (a + b) + a + (a + b) * (t * a / (a + b)) := by
      have := Nat.mod_add_div (t * a) (a + b)
      rw [add_mul, one_mul]; omega
    rw [h, Nat.add_mul_mod_self_left]
  rw [IsRaising] at ht
  have hsub : t * a % (a + b) + a - (a + b) = t * a % (a + b) - b := by omega
  rw [hstep, Nat.mod_eq_sub_mod (by omega), hsub, Nat.mod_eq_of_lt (by omega)]

/-- At a **raising** slot the slice at the next slot contains the slice at this one, and the
difference is a horizontal strip: the residue drops by `b`, so `W` increases. -/
@[hjo "lem_slices_step"]
theorem isHStrip_slice_of_isRaising {a b : ℕ} (hd : 0 < a + b) {W : ℕ → ℕ}
    (hW : IsDiagFun a b W) {t : ℕ} (ht : IsRaising a b t) :
    IsHStrip (slice hd hW ((t + 1) * a % (a + b))) (slice hd hW (t * a % (a + b))) := by
  have hb : b ≤ t * a % (a + b) := ht
  have hnext : (t + 1) * a % (a + b) = t * a % (a + b) - b := succ_mul_mod_of_isRaising hd ht
  intro i
  refine ⟨?_, ?_⟩
  · simp only [slice_parts, hnext]
    have hkey : t * a % (a + b) + (a + b) * i = t * a % (a + b) - b + (a + b) * i + b := by omega
    rw [hkey]
    exact hW.step_right _
  · simp only [slice_parts, hnext]
    have hkey : t * a % (a + b) - b + (a + b) * (i + 1)
        = t * a % (a + b) + (a + b) * i + a := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [hkey]
    exact hW.step_left _

/-- At a **lowering** slot the slice at this slot contains the slice at the next one, and the
difference is a horizontal strip: the residue advances by `a`, so `W` decreases. -/
@[hjo "lem_slices_step"]
theorem isHStrip_slice_of_not_isRaising {a b : ℕ} (hd : 0 < a + b) {W : ℕ → ℕ}
    (hW : IsDiagFun a b W) {t : ℕ} (ht : ¬ IsRaising a b t) :
    IsHStrip (slice hd hW (t * a % (a + b))) (slice hd hW ((t + 1) * a % (a + b))) := by
  have hnext : (t + 1) * a % (a + b) = t * a % (a + b) + a := succ_mul_mod_of_not_isRaising hd ht
  intro i
  refine ⟨?_, ?_⟩
  · simp only [slice_parts, hnext]
    have hkey : t * a % (a + b) + a + (a + b) * i = t * a % (a + b) + (a + b) * i + a := by omega
    rw [hkey]
    exact hW.step_left _
  · simp only [slice_parts, hnext]
    have hkey : t * a % (a + b) + (a + b) * (i + 1)
        = t * a % (a + b) + a + (a + b) * i + b := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [hkey]
    exact hW.step_right _

end HJO.CylindricProduct
