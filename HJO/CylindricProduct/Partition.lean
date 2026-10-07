/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Order.Interval.Finset.Nat
public meta import HJO.Attr

/-! # Partitions and horizontal strips

The transfer-trace argument indexes its kernels by partitions, so this file fixes a type of them:
a partition is a weakly decreasing sequence of naturals with finitely many nonzero terms, and its
size is the total of its parts. The one relation between partitions that the argument needs is the
horizontal strip.
-/

@[expose] public section

open Finset

namespace HJO.CylindricProduct

/-! ### Partitions -/

/-- A partition: a weakly decreasing sequence of naturals, indexed from `0`, with finitely many
nonzero parts. -/
@[ext]
structure Part where
  /-- The parts of the partition, indexed from `0`. -/
  parts : ℕ → ℕ
  /-- The parts weakly decrease. -/
  antitone' : Antitone parts
  /-- Only finitely many parts are nonzero. -/
  vanish' : ∃ B, ∀ i, B ≤ i → parts i = 0

namespace Part

variable (l : Part)

/-- The parts of a partition weakly decrease. -/
theorem antitone : Antitone l.parts := l.antitone'

/-- A partition has finitely many nonzero parts. -/
theorem vanish : ∃ B, ∀ i, B ≤ i → l.parts i = 0 := l.vanish'

/-- The size `|λ|` of a partition: the total of its parts. -/
noncomputable def size : ℕ := ∑ᶠ i, l.parts i

/-- The size is the sum of the parts over any initial segment beyond which they vanish. -/
theorem size_eq_sum_range {B : ℕ} (hB : ∀ i, B ≤ i → l.parts i = 0) :
    l.size = ∑ i ∈ range B, l.parts i := by
  refine finsum_eq_finsetSum_of_support_subset _ fun i hi => ?_
  simp only [Function.mem_support] at hi
  rw [Finset.mem_coe, mem_range]
  by_contra hcon
  exact hi (hB i (by omega))

/-- The empty partition, all of whose parts are `0`. -/
def zero : Part where
  parts := fun _ => 0
  antitone' := fun _ _ _ => le_rfl
  vanish' := ⟨0, fun _ _ => rfl⟩

@[simp] theorem zero_parts (i : ℕ) : zero.parts i = 0 := rfl

@[simp] theorem size_zero : zero.size = 0 := by
  rw [size_eq_sum_range zero (B := 0) fun _ _ => rfl]
  simp

/-- A partition all of whose parts vanish is the empty one. -/
theorem eq_zero_of_parts_eq_zero {l : Part} (h : ∀ i, l.parts i = 0) : l = zero :=
  Part.ext (funext h)

/-- Sizes are monotone in the parts. -/
theorem size_le_size {l m : Part} (h : ∀ i, l.parts i ≤ m.parts i) : l.size ≤ m.size := by
  obtain ⟨B, hB⟩ := l.vanish
  obtain ⟨C, hC⟩ := m.vanish
  rw [size_eq_sum_range l (B := max B C) fun i hi => hB i (le_trans (le_max_left _ _) hi),
    size_eq_sum_range m (B := max B C) fun i hi => hC i (le_trans (le_max_right _ _) hi)]
  exact Finset.sum_le_sum fun i _ => h i

/-- Two partitions with the same size and one contained in the other are equal. -/
theorem eq_of_le_of_size_le {l m : Part} (h : ∀ i, l.parts i ≤ m.parts i)
    (hsize : m.size ≤ l.size) : l = m := by
  obtain ⟨B, hB⟩ := l.vanish
  obtain ⟨C, hC⟩ := m.vanish
  set D := max B C with hD
  have hl : l.size = ∑ i ∈ range D, l.parts i :=
    size_eq_sum_range l fun i hi => hB i (le_trans (le_max_left _ _) hi)
  have hm : m.size = ∑ i ∈ range D, m.parts i :=
    size_eq_sum_range m fun i hi => hC i (le_trans (le_max_right _ _) hi)
  have hsum : ∑ i ∈ range D, m.parts i ≤ ∑ i ∈ range D, l.parts i := by rw [← hl, ← hm]; exact hsize
  have hall : ∀ i ∈ range D, l.parts i = m.parts i :=
    Finset.sum_eq_sum_iff_of_le (fun i _ => h i) |>.mp
      (le_antisymm (Finset.sum_le_sum fun i _ => h i) hsum)
  refine Part.ext (funext fun i => ?_)
  by_cases hi : i < D
  · exact hall i (mem_range.mpr hi)
  · rw [hB i (by omega), hC i (by omega)]

end Part

/-! ### Horizontal strips -/

/-- `ν/μ` is a **horizontal strip**: `ν i ≥ μ i ≥ ν (i+1)` for every index `i`. The numerator is
the first argument. -/
@[hjo "def_hstrip"]
def IsHStrip (ν μ : Part) : Prop := ∀ i, μ.parts i ≤ ν.parts i ∧ ν.parts (i + 1) ≤ μ.parts i

/-- **A horizontal strip only grows a partition**: the denominator of a horizontal strip is
contained in its numerator, so its size is at most that of the numerator. This is what makes the
truncated exponent `|ν| - |μ|` of the raising and lowering kernels the true difference of the two
sizes. -/
@[hjo "lem_hstrip_size"]
theorem IsHStrip.size_le {ν μ : Part} (h : IsHStrip ν μ) : μ.size ≤ ν.size :=
  Part.size_le_size fun i => (h i).1

/-- Every partition is a horizontal strip over itself. -/
theorem isHStrip_self (l : Part) : IsHStrip l l := fun i => ⟨le_rfl, l.antitone (Nat.le_succ i)⟩

/-- A horizontal strip of size zero is trivial: the two partitions agree. -/
theorem IsHStrip.eq_of_size_le {ν μ : Part} (h : IsHStrip ν μ) (hsize : ν.size ≤ μ.size) :
    μ = ν :=
  Part.eq_of_le_of_size_le (fun i => (h i).1) hsize

end HJO.CylindricProduct
