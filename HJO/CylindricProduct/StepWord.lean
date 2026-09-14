/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Nat
public meta import HJO.Attr

/-! # The step word of a balanced profile

For `d = a + b` the `d` slots `0 ≤ t < d` are split into *raising* and *lowering* ones by the
condition `t * a % d ≥ b`. This file records the three elementary facts about that split: the
definition, its Beatty form -- slot `t` is raising exactly where the sequence `⌊t a / d⌋`
increases -- and the counts, `a` raising slots and `b` lowering ones.

The counts come from the Beatty form by telescoping: `⌊t a / d⌋` runs from `0` at `t = 0` to `a`
at `t = d` in increments of `0` and `1`, so exactly `a` of the `d` increments are `1`.
-/

@[expose] public section

open Finset

namespace HJO.CylindricProduct

variable {a b : ℕ}

/-- Slot `t` is a **raising** slot when `t * a % d ≥ b`, with `d = a + b`, and a **lowering**
slot otherwise. -/
@[hjo "def_step_word"]
def IsRaising (a b t : ℕ) : Prop := b ≤ t * a % (a + b)

instance : DecidablePred (IsRaising a b) := fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-- Advancing the slot index by one adds `a` to the remainder and carries the overflow into the
quotient. -/
theorem succ_mul_div_eq_add (hd : 0 < a + b) (t : ℕ) :
    (t + 1) * a / (a + b) = (t * a % (a + b) + a) / (a + b) + t * a / (a + b) := by
  have h : (t + 1) * a = t * a % (a + b) + a + (a + b) * (t * a / (a + b)) := by
    have := Nat.mod_add_div (t * a) (a + b)
    rw [add_mul, one_mul]
    omega
  rw [h, Nat.add_mul_div_left _ _ hd]

/-- The overflow carried by one step is `1` at a raising slot and `0` at a lowering one. -/
theorem div_mod_add_eq (hd : 0 < a + b) (t : ℕ) :
    (t * a % (a + b) + a) / (a + b) = if IsRaising a b t then 1 else 0 := by
  have hlt : t * a % (a + b) < a + b := Nat.mod_lt _ hd
  split_ifs with h
  · rw [IsRaising] at h
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · rw [IsRaising, not_le] at h
    exact Nat.div_eq_of_lt (by omega)

/-- **The step word is a Beatty word.** Slot `t` is raising exactly when the integer sequence
`⌊t a / d⌋` strictly increases at `t`. -/
@[hjo "lem_step_word_beatty"]
theorem isRaising_iff_div_lt_div (hd : 0 < a + b) (t : ℕ) :
    IsRaising a b t ↔ t * a / (a + b) < (t + 1) * a / (a + b) := by
  rw [succ_mul_div_eq_add hd, div_mod_add_eq hd]
  by_cases h : IsRaising a b t <;> simp [h]

/-- The increment of `⌊t a / d⌋` at one step, as a difference: `1` at a raising slot and `0` at a
lowering one. -/
theorem sub_div_eq (hd : 0 < a + b) (t : ℕ) :
    (t + 1) * a / (a + b) - t * a / (a + b) = if IsRaising a b t then 1 else 0 := by
  rw [succ_mul_div_eq_add hd, div_mod_add_eq hd, Nat.add_sub_cancel]

/-- **The step word has `a` raising slots.** Exactly `a` of the `d` slots are raising. -/
@[hjo "lem_step_word_counts"]
theorem card_filter_isRaising (hd : 0 < a + b) :
    ((range (a + b)).filter (IsRaising a b)).card = a := by
  have hmono : Monotone fun t => t * a / (a + b) := fun s t hst =>
    Nat.div_le_div_right (Nat.mul_le_mul_right a hst)
  have hsum : ∑ t ∈ range (a + b), (if IsRaising a b t then 1 else 0)
      = (a + b) * a / (a + b) - 0 * a / (a + b) := by
    rw [← Finset.sum_range_tsub hmono]
    exact Finset.sum_congr rfl fun t _ => (sub_div_eq hd t).symm
  rw [Finset.card_filter, hsum, Nat.mul_div_cancel_left a hd]
  simp

/-- Exactly `b` of the `d` slots are lowering, the complement of the raising ones. -/
@[hjo "lem_step_word_counts"]
theorem card_filter_not_isRaising (hd : 0 < a + b) :
    ((range (a + b)).filter (fun t => ¬ IsRaising a b t)).card = b := by
  have h := Finset.card_filter_add_card_filter_not
    (s := range (a + b)) (p := IsRaising a b)
  rw [card_filter_isRaising hd, Finset.card_range] at h
  omega

end HJO.CylindricProduct
