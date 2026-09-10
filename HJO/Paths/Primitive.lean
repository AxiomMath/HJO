/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Series.Gaps
public import HJO.Paths.Basic
public import HJO.Defs

/-! # The heights of the primitive path of an order filter

An order filter of the gap set of `⟨a, b⟩` determines a below-diagonal `(a, b)`-path, the
single-block case `N = 1` of the height encoding. This file reads the heights of that path off the
counting formula below its endpoint, at its endpoint and at the origin, and shows that the
indices the heights count form an initial segment in each column.
-/

@[expose] public section

open Finset NumericalSemigroup

namespace HJO.Primitive

/-- Below the endpoint the height of the primitive path is the counting formula. -/
theorem ht_primitivePath_of_lt {a b : ℕ} (F : Finset ℕ) {r : ℕ} (hr : r < a) :
    Paths.ht (primitivePath a b F) r = primitiveHeight a b F r := by
  simp [Paths.ht, primitivePath, show ¬ r = a by omega]
  omega

/-- The primitive path finishes at height `b`. -/
theorem ht_primitivePath_self (a b : ℕ) (F : Finset ℕ) :
    Paths.ht (primitivePath a b F) a = b := by
  simp [Paths.ht, primitivePath]

/-- The primitive path starts at height `0`. -/
theorem ht_primitivePath_zero {a b : ℕ} (F : Finset ℕ) (ha : 0 < a) :
    Paths.ht (primitivePath a b F) 0 = 0 := by
  rw [ht_primitivePath_of_lt F ha, primitiveHeight, card_eq_zero, filter_eq_empty_iff]
  simp

/-- In an order filter the indices counted in a column form an initial segment: if `rb - ai`
lies in `F` and `rb - aj` is a gap for some `j ≤ i`, then `rb - aj` lies in `F` as well. -/
theorem sub_mem_of_le {a b : ℕ} {F : Finset ℕ} (hF : Gaps.IsOrderFilter a b F) {r i j : ℕ}
    (hij : j ≤ i) (hi : a * i ≤ r * b) (hmem : r * b - a * i ∈ F)
    (hgap : r * b - a * j ∈ (finspan {a, b}).gaps) : r * b - a * j ∈ F := by
  have hji : a * j ≤ a * i := Nat.mul_le_mul_left a hij
  have key : (i - j) * a + a * j = a * i := by
    rw [Nat.sub_mul, Nat.mul_comm i a, Nat.mul_comm j a]
    omega
  exact hF.2 _ hmem _ hgap ⟨i - j, 0, by omega⟩

end HJO.Primitive
