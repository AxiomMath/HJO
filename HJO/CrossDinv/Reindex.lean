/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Int.Interval
public import HJO.RankOneDinv.Diagram
public meta import HJO.Attr

/-! # Reindexing the two window expansions into a hook-shaped alternating sum

The difference of the two window counts is a difference of two sums of cross tail counts, indexed
by the column shift `1 ≤ u ≤ a - 2` with the row shifts `β u`, `β u + 1`, `β (u - 1)` and
`β (u + 1) + 1`. The hook count is instead an alternating sum over `0 ≤ u ≤ a - 2` of the bracket
`φ (u, β u) - φ (u + 1, β u) - φ (u, β (u+1) + 1) + φ (u + 1, β (u+1) + 1)`, an
inclusion-exclusion in the column shift at a fixed pair of row shifts.

This file proves the two are equal, for any `φ` vanishing at column shifts `u ≥ a - 1`. The
argument is bookkeeping: shifting the index of the two sums whose first argument is `u + 1` moves
them onto `1 ≤ u ≤ a - 1`, where the top term vanishes by hypothesis, and the two sums whose first
argument is `u` give up their term at `u = 0`, which is `φ (0, 0)` because `β 0 = 0` and
`φ (0, β 1 + 1)`. Only the vanishing hypothesis is used, so nothing here is about tail counts.
-/

@[expose] public section

open Finset

namespace HJO.CrossDinv

variable {a b : ℕ}

/-! ### Sums over integer intervals -/

/-- Shifting the index of a sum over an integer interval. -/
theorem sum_Icc_succ (A : ℤ) (g : ℤ → ℤ) :
    ∑ u ∈ Finset.Icc (0 : ℤ) A, g (u + 1) = ∑ u ∈ Finset.Icc (1 : ℤ) (A + 1), g u := by
  refine Finset.sum_nbij' (fun u => u + 1) (fun u => u - 1) (fun u hu => ?_) (fun u hu => ?_)
    (fun u _ => by ring) (fun u _ => by ring) (fun u _ => rfl)
  · simp only [mem_Icc] at hu ⊢
    omega
  · simp only [mem_Icc] at hu ⊢
    omega

/-- Splitting the bottom term off a sum over an integer interval. -/
theorem sum_Icc_bot {A : ℤ} (hA : 0 ≤ A) (g : ℤ → ℤ) :
    ∑ u ∈ Finset.Icc (0 : ℤ) A, g u = g 0 + ∑ u ∈ Finset.Icc (1 : ℤ) A, g u := by
  rw [show Finset.Icc (0 : ℤ) A = insert 0 (Finset.Icc (1 : ℤ) A) from by
    ext x
    simp only [mem_insert, mem_Icc]
    omega]
  exact Finset.sum_insert (by simp only [mem_Icc]; omega)

/-- Splitting the top term off a sum over an integer interval. -/
theorem sum_Icc_top {A : ℤ} (hA : 1 ≤ A) (g : ℤ → ℤ) :
    ∑ u ∈ Finset.Icc (1 : ℤ) A, g u = g A + ∑ u ∈ Finset.Icc (1 : ℤ) (A - 1), g u := by
  rw [show Finset.Icc (1 : ℤ) A = insert A (Finset.Icc (1 : ℤ) (A - 1)) from by
    ext x
    simp only [mem_insert, mem_Icc]
    omega]
  exact Finset.sum_insert (by simp only [mem_Icc]; omega)

/-- Shifting the index of a sum whose summand vanishes at the top of the shifted range. -/
theorem sum_Icc_succ_of_top_eq_zero {A : ℤ} (hA : 0 ≤ A) (g : ℤ → ℤ) (hg : g (A + 1) = 0) :
    ∑ u ∈ Finset.Icc (0 : ℤ) A, g (u + 1) = ∑ u ∈ Finset.Icc (1 : ℤ) A, g u := by
  rw [sum_Icc_succ, sum_Icc_top (by omega) g, hg, add_sub_cancel_right, zero_add]

/-! ### The reindexing identity -/

/-- **The two window expansions reindex into the hook-shaped alternating sum**: for any `φ`
vanishing at column shifts `u ≥ a - 1`, the difference of the two bracketed expansions is the
alternating sum of the brackets over `0 ≤ u ≤ a - 2`. -/
@[hjo "lem_cross_tail_reindex"]
theorem sum_bracket_eq (ha : 1 < a) (φ : ℤ → ℤ → ℤ)
    (hφ : ∀ u v : ℤ, (a : ℤ) - 1 ≤ u → φ u v = 0) :
    (φ 0 0 + ∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2),
        (φ u (Gaps.beta a b u) + φ u (Gaps.beta a b u + 1)))
      - (φ 0 (Gaps.beta a b 1 + 1) + ∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2),
          (φ u (Gaps.beta a b (u - 1)) + φ u (Gaps.beta a b (u + 1) + 1)))
      = ∑ u ∈ Finset.Icc (0 : ℤ) ((a : ℤ) - 2),
          (φ u (Gaps.beta a b u) - φ (u + 1) (Gaps.beta a b u)
            - φ u (Gaps.beta a b (u + 1) + 1) + φ (u + 1) (Gaps.beta a b (u + 1) + 1)) := by
  have ha2 : (0 : ℤ) ≤ (a : ℤ) - 2 := by omega
  have e1 : ∑ u ∈ Finset.Icc (0 : ℤ) ((a : ℤ) - 2), φ u (Gaps.beta a b u)
      = φ 0 0 + ∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2), φ u (Gaps.beta a b u) := by
    rw [sum_Icc_bot ha2, show Gaps.beta a b 0 = 0 from by simp [Gaps.beta]]
  have e2 : ∑ u ∈ Finset.Icc (0 : ℤ) ((a : ℤ) - 2), φ (u + 1) (Gaps.beta a b u)
      = ∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2), φ u (Gaps.beta a b (u - 1)) := by
    have h := sum_Icc_succ_of_top_eq_zero ha2 (fun u => φ u (Gaps.beta a b (u - 1)))
      (hφ _ _ (by omega))
    simpa using h
  have e3 : ∑ u ∈ Finset.Icc (0 : ℤ) ((a : ℤ) - 2), φ u (Gaps.beta a b (u + 1) + 1)
      = φ 0 (Gaps.beta a b 1 + 1)
        + ∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2), φ u (Gaps.beta a b (u + 1) + 1) := by
    rw [sum_Icc_bot ha2]
    norm_num
  have e4 : ∑ u ∈ Finset.Icc (0 : ℤ) ((a : ℤ) - 2), φ (u + 1) (Gaps.beta a b (u + 1) + 1)
      = ∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2), φ u (Gaps.beta a b u + 1) :=
    sum_Icc_succ_of_top_eq_zero ha2 (fun u => φ u (Gaps.beta a b u + 1)) (hφ _ _ (by omega))
  have hsplit : ∑ u ∈ Finset.Icc (0 : ℤ) ((a : ℤ) - 2),
        (φ u (Gaps.beta a b u) - φ (u + 1) (Gaps.beta a b u)
          - φ u (Gaps.beta a b (u + 1) + 1) + φ (u + 1) (Gaps.beta a b (u + 1) + 1))
      = ((∑ u ∈ Finset.Icc (0 : ℤ) ((a : ℤ) - 2), φ u (Gaps.beta a b u))
            - ∑ u ∈ Finset.Icc (0 : ℤ) ((a : ℤ) - 2), φ (u + 1) (Gaps.beta a b u)
            - ∑ u ∈ Finset.Icc (0 : ℤ) ((a : ℤ) - 2), φ u (Gaps.beta a b (u + 1) + 1))
          + ∑ u ∈ Finset.Icc (0 : ℤ) ((a : ℤ) - 2), φ (u + 1) (Gaps.beta a b (u + 1) + 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [hsplit, e1, e2, e3, e4, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

end HJO.CrossDinv
