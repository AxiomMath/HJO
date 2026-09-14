/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Series.GapForms
public import HJO.CrossDinv.Diagram
public meta import HJO.Attr

/-! # The polarised form at a pair of indicator vectors

The polarised form `B` of the gap set is valued in `ℚ`, and genuinely so: on a single pair of
distinct gaps whose difference lies in the window `[0, a)` it is `1/2`. It is therefore `2 B`, not
`B`, that this file evaluates as a signed count of pairs of gaps, in the shape the cross-dinv
identity consumes:

`2 B (1_D, 1_E)` is the number of pairs of `D × E` whose difference lies in `[0, a)`, plus the
number of pairs of `E × D` in that window, minus the same two counts for the window `[b, a + b)`.
The symmetrised kernel `K (h - g) + K (g - h)` is what produces the two ordered products, one for
each summand, and `HJO.RankOneDinv.u_eq_window` is what evaluates each kernel value as the
difference of the two window indicators.
-/

@[expose] public section

open Finset NumericalSemigroup HJO.RankOneDinv

namespace HJO.CrossDinv

variable {a b : ℕ} {D E : Finset ℕ}

/-- **A kernel sum over a set of pairs is a signed count of windows**: summing `K (h - g)` over
any finite set of pairs of gaps counts the pairs in the window `[0, a)` and subtracts those in the
window `[b, a + b)`, the two ranges being disjoint because `a < b`. -/
theorem sum_u_eq_card_sub (hab : a < b) (S : Finset (ℕ × ℕ)) :
    ∑ p ∈ S, HJO.U a b ((p.2 : ℤ) - p.1)
      = #{p ∈ S | 0 ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < a}
        - #{p ∈ S | (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b} := by
  have e : ∀ p ∈ S, HJO.U a b ((p.2 : ℤ) - p.1)
      = (if 0 ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < a then 1 else 0)
        - (if (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b then 1 else 0) := by
    intro p _
    rw [u_eq_window hab]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]

/-- Reversing the difference is reversing the product: summing `K (g - h)` over `D × E` is
summing `K (h - g)` over `E × D`. -/
theorem sum_u_swap (S T : Finset ℕ) :
    ∑ p ∈ S ×ˢ T, HJO.U a b ((p.1 : ℤ) - p.2) = ∑ p ∈ T ×ˢ S, HJO.U a b ((p.2 : ℤ) - p.1) := by
  refine Finset.sum_nbij' Prod.swap Prod.swap (fun p hp => ?_) (fun p hp => ?_)
    (fun p _ => Prod.swap_swap p) (fun p _ => Prod.swap_swap p) (fun p _ => rfl)
  · simp only [mem_product, Prod.fst_swap, Prod.snd_swap] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · simp only [mem_product, Prod.fst_swap, Prod.snd_swap] at hp ⊢
    exact ⟨hp.2, hp.1⟩

/-- **The polarised form at a pair of indicators is a signed count of pairs**: twice
`B (1_D, 1_E)` is the number of pairs of `D × E` and of `E × D` whose difference lies in the
window `[0, a)`, less the number of those whose difference lies in the window `[b, a + b)`. -/
@[hjo "lem_bilinear_indicator_pairs"]
theorem two_mul_bilin_indicator (hab : a < b) (hD : D ⊆ (finspan {a, b}).gaps)
    (hE : E ⊆ (finspan {a, b}).gaps) :
    2 * HJO.Defs.bilin (finspan {a, b}).gaps a b (fun g => if (g : ℕ) ∈ D then 1 else 0)
        (fun h => if (h : ℕ) ∈ E then 1 else 0)
      = ((#{p ∈ D ×ˢ E | 0 ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < a}
          + #{p ∈ E ×ˢ D | 0 ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < a}
          - #{p ∈ D ×ˢ E | (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b}
          - #{p ∈ E ×ˢ D | (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b}
          : ℤ) : ℚ) := by
  rw [HJO.Defs.two_mul_bilin]
  congr 1
  have e1 : (∑ g : (finspan {a, b}).gaps, ∑ h : (finspan {a, b}).gaps,
        (HJO.U a b ((h : ℕ) - (g : ℕ)) + HJO.U a b ((g : ℕ) - (h : ℕ)))
          * (if (g : ℕ) ∈ D then 1 else 0) * (if (h : ℕ) ∈ E then 1 else 0))
      = ∑ g ∈ (finspan {a, b}).gaps, ∑ h ∈ (finspan {a, b}).gaps,
        (HJO.U a b ((h : ℤ) - (g : ℤ)) + HJO.U a b ((g : ℤ) - (h : ℤ)))
          * (if g ∈ D then 1 else 0) * (if h ∈ E then 1 else 0) := by
    rw [Finset.sum_coe_sort (finspan {a, b}).gaps fun g =>
      ∑ h : (finspan {a, b}).gaps, (HJO.U a b ((h : ℕ) - (g : ℤ)) + HJO.U a b ((g : ℤ) - (h : ℕ)))
        * (if g ∈ D then 1 else 0) * (if (h : ℕ) ∈ E then 1 else 0)]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_coe_sort (finspan {a, b}).gaps
      fun h => (HJO.U a b ((h : ℤ) - (g : ℤ)) + HJO.U a b ((g : ℤ) - (h : ℤ)))
        * (if g ∈ D then 1 else 0) * (if h ∈ E then 1 else 0)
  rw [e1, ← Finset.sum_product']
  have e2 : ∀ p ∈ (finspan {a, b}).gaps ×ˢ (finspan {a, b}).gaps,
      (HJO.U a b ((p.2 : ℤ) - p.1) + HJO.U a b ((p.1 : ℤ) - p.2))
          * (if p.1 ∈ D then 1 else 0) * (if p.2 ∈ E then 1 else 0)
        = if p.1 ∈ D ∧ p.2 ∈ E then
            HJO.U a b ((p.2 : ℤ) - p.1) + HJO.U a b ((p.1 : ℤ) - p.2) else 0 := by
    intro p _
    split_ifs with h1 h2 h3 <;> simp_all
  rw [Finset.sum_congr rfl e2, ← Finset.sum_filter]
  have e3 : {p ∈ (finspan {a, b}).gaps ×ˢ (finspan {a, b}).gaps | p.1 ∈ D ∧ p.2 ∈ E}
      = D ×ˢ E := by
    ext p
    simp only [mem_filter, mem_product]
    exact ⟨fun h => h.2, fun h => ⟨⟨hD h.1, hE h.2⟩, h⟩⟩
  rw [e3, Finset.sum_add_distrib, sum_u_swap, sum_u_eq_card_sub hab, sum_u_eq_card_sub hab]
  ring

end HJO.CrossDinv
