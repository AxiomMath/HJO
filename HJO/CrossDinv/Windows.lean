/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CrossDinv.Diagram
public meta import HJO.Attr

/-! # The two windows as sums of cross tail counts

The polarised form at a pair of indicators counts the pairs of gaps `(g, h) ∈ D × E` whose
difference lies in the window `[0, a)` or in the window `[b, a + b)`. This file expands both counts
over the cross tail counts of the two filter diagrams.

The mechanism is the gap-coordinate bijection: a pair of gaps is a pair of cells
`((r, i), (r', i'))` of `𝒟_D × 𝒟_E`, and with `u := r' - r` the difference is `h - g = ub + wa`
where `w := i - i'`. So `0 ≤ h - g - cb < a` says exactly `i' = i + β (u - c)` -- one row shift for
each column shift -- and grouping the counted pairs by `u` turns each window count into a sum of
cross tail counts over `-(a - 2) ≤ u ≤ a - 2`, the range outside which they vanish. The reflection
`β (-u) = -β u - 1` and the swap `T_{D,E}(u, v) = T_{E,D}(-u, -v)` then fold the negative column
shifts onto the positive ones, which is where the two ordered pairs `(D, E)` and `(E, D)` in the
statements come from.
-/

@[expose] public section

open Finset NumericalSemigroup HJO.RankOneDinv

namespace HJO.CrossDinv

variable {a b : ℕ} {D E : Finset ℕ}

/-! ### Shifted pairs of cells -/

/-- The pairs of cells of `𝒟_D × 𝒟_E` whose coordinates differ by the shift `(u, w)`. -/
def crossPairShift (a b : ℕ) (D E : Finset ℕ) (u w : ℤ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  {q ∈ ReturnPath.cellSet a b D ×ˢ ReturnPath.cellSet a b E |
    (q.2.1 : ℤ) = (q.1.1 : ℤ) + u ∧ (q.2.2 : ℤ) = (q.1.2 : ℤ) + w}

/-- Membership in the shifted pair set. -/
theorem mem_crossPairShift {u w : ℤ} {q : (ℕ × ℕ) × (ℕ × ℕ)} :
    q ∈ crossPairShift a b D E u w ↔
      (q.1 ∈ ReturnPath.cellSet a b D ∧ q.2 ∈ ReturnPath.cellSet a b E) ∧
        (q.2.1 : ℤ) = (q.1.1 : ℤ) + u ∧ (q.2.2 : ℤ) = (q.1.2 : ℤ) + w := by
  rw [crossPairShift, mem_filter, mem_product]

/-- **The shifted pairs are counted by the cross tail count**: forgetting the second cell of a
shifted pair is a bijection onto the cells counted by `T_{D,E}(u, w)`. -/
theorem card_crossPairShift (u w : ℤ) :
    #(crossPairShift a b D E u w) = crossTailCount a b D E u w := by
  rw [crossTailCount]
  refine Finset.card_nbij' (fun q => ((q.1.1 : ℤ), (q.1.2 : ℤ)))
    (fun z => ((z.1.toNat, z.2.toNat), ((z.1 + u).toNat, (z.2 + w).toNat))) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_coe, mem_crossPairShift] at hq
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq
    simp only [Finset.mem_coe, mem_filter, natCast_mem_cellZ]
    refine ⟨h1, ?_⟩
    rw [show ((q.1.1 : ℤ) + u, (q.1.2 : ℤ) + w) = ((q.2.1 : ℤ), (q.2.2 : ℤ)) from
      Prod.ext h3.symm h4.symm, natCast_mem_cellZ]
    exact h2
  · intro z hz
    simp only [Finset.mem_coe, mem_filter] at hz
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨r, i, hr, hi, hp⟩ := exists_natCast_of_mem_cellZ hz1
    obtain ⟨r', i', hr', hi', hp'⟩ := exists_natCast_of_mem_cellZ hz2
    simp only [Finset.mem_coe, mem_crossPairShift]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [show z.1.toNat = r from by omega, show z.2.toNat = i from by omega]
      exact hp
    · rw [show (z.1 + u).toNat = r' from by omega, show (z.2 + w).toNat = i' from by omega]
      exact hp'
    · omega
    · omega
  · intro q hq
    simp only [Finset.mem_coe, mem_crossPairShift] at hq
    obtain ⟨-, h3, h4⟩ := hq
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · change ((q.1.1 : ℤ)).toNat = q.1.1
      omega
    · change ((q.1.2 : ℤ)).toNat = q.1.2
      omega
    · change ((q.1.1 : ℤ) + u).toNat = q.2.1
      omega
    · change ((q.1.2 : ℤ) + w).toNat = q.2.2
      omega
  · intro z hz
    simp only [Finset.mem_coe, mem_filter] at hz
    obtain ⟨h1, -, h3, -⟩ := cellZ_bounds hz.1
    refine Prod.ext ?_ ?_
    · change ((z.1.toNat : ℕ) : ℤ) = z.1
      omega
    · change ((z.2.toNat : ℕ) : ℤ) = z.2
      omega

/-! ### A window count as a sum of cross tail counts -/

/-- **The pairs in a window, grouped by the column shift**: the pairs of `D × E` whose difference
lies in the window `[cb, cb + a)` are, in cell coordinates, the pairs whose row shift is
`β (u - c)` at column shift `u`, so the count is the sum of the cross tail counts at those
shifts. -/
theorem card_window_eq_sum (hco : a.Coprime b) (ha : 1 < a) (hD : D ⊆ (finspan {a, b}).gaps)
    (hE : E ⊆ (finspan {a, b}).gaps) (c : ℤ) :
    #{p ∈ D ×ˢ E | 0 ≤ (p.2 : ℤ) - p.1 - c * b ∧ (p.2 : ℤ) - p.1 - c * b < a}
      = ∑ u ∈ Finset.Icc (-((a : ℤ) - 2)) ((a : ℤ) - 2),
          crossTailCount a b D E u (Gaps.beta a b (u - c)) := by
  have ha0 : 0 < a := by omega
  have step1 : #{q ∈ ReturnPath.cellSet a b D ×ˢ ReturnPath.cellSet a b E |
        (q.2.2 : ℤ) - q.1.2 = Gaps.beta a b ((q.2.1 : ℤ) - q.1.1 - c)}
      = #{p ∈ D ×ˢ E | 0 ≤ (p.2 : ℤ) - p.1 - c * b ∧ (p.2 : ℤ) - p.1 - c * b < a} := by
    refine Finset.card_nbij (fun q => (label a b q.1, label a b q.2)) ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_coe, mem_filter, mem_product] at hq ⊢
      obtain ⟨⟨hq1, hq2⟩, hcond⟩ := hq
      obtain ⟨-, -, -, h1lt⟩ := (mem_gapDiagram ha0).mp (mem_filterDiagram.mp hq1).1
      obtain ⟨-, -, -, h2lt⟩ := (mem_gapDiagram ha0).mp (mem_filterDiagram.mp hq2).1
      have e1 := label_cast (a := a) (b := b) (p := q.1) (le_of_lt h1lt)
      have e2 := label_cast (a := a) (b := b) (p := q.2) (le_of_lt h2lt)
      have hw := (beta_window (b := b) ha0 ((q.2.1 : ℤ) - q.1.1 - c)
        (Gaps.beta a b ((q.2.1 : ℤ) - q.1.1 - c))).mpr rfl
      rw [← hcond] at hw
      exact ⟨⟨(mem_filterDiagram.mp hq1).2, (mem_filterDiagram.mp hq2).2⟩,
        by rw [e1, e2]; linarith [hw.1], by rw [e1, e2]; linarith [hw.2]⟩
    · intro q hq q' hq' heq
      simp only [Finset.mem_coe, mem_filter, mem_product] at hq hq'
      have h1 : q.1 = q'.1 :=
        label_injOn hco ha (Finset.mem_coe.mpr (mem_filterDiagram.mp hq.1.1).1)
          (Finset.mem_coe.mpr (mem_filterDiagram.mp hq'.1.1).1) (congrArg Prod.fst heq)
      have h2 : q.2 = q'.2 :=
        label_injOn hco ha (Finset.mem_coe.mpr (mem_filterDiagram.mp hq.1.2).1)
          (Finset.mem_coe.mpr (mem_filterDiagram.mp hq'.1.2).1) (congrArg Prod.snd heq)
      exact Prod.ext h1 h2
    · intro gh hgh
      simp only [Finset.mem_coe, mem_filter, mem_product] at hgh
      obtain ⟨⟨hg1, hg2⟩, hw1, hw2⟩ := hgh
      obtain ⟨p, hpD, hpl⟩ := label_surjOn hco ha (Finset.mem_coe.mpr (hD hg1))
      obtain ⟨p', hp'D, hp'l⟩ := label_surjOn hco ha (Finset.mem_coe.mpr (hE hg2))
      simp only [Finset.mem_coe] at hpD hp'D
      obtain ⟨-, -, -, h1lt⟩ := (mem_gapDiagram ha0).mp hpD
      obtain ⟨-, -, -, h2lt⟩ := (mem_gapDiagram ha0).mp hp'D
      have e1 := label_cast (a := a) (b := b) (p := p) (le_of_lt h1lt)
      have e2 := label_cast (a := a) (b := b) (p := p') (le_of_lt h2lt)
      rw [← hpl, ← hp'l, e1, e2] at hw1 hw2
      refine ⟨(p, p'), ?_, Prod.ext hpl hp'l⟩
      simp only [Finset.mem_coe, mem_filter, mem_product]
      refine ⟨⟨mem_filterDiagram.mpr ⟨hpD, hpl ▸ hg1⟩,
        mem_filterDiagram.mpr ⟨hp'D, hp'l ▸ hg2⟩⟩, ?_⟩
      exact (beta_window ha0 ((p'.1 : ℤ) - p.1 - c) ((p'.2 : ℤ) - p.2)).mp
        ⟨by linarith, by linarith⟩
  rw [← step1]
  have hmaps : Set.MapsTo (fun q : (ℕ × ℕ) × (ℕ × ℕ) => (q.2.1 : ℤ) - q.1.1)
      ↑{q ∈ ReturnPath.cellSet a b D ×ˢ ReturnPath.cellSet a b E |
        (q.2.2 : ℤ) - q.1.2 = Gaps.beta a b ((q.2.1 : ℤ) - q.1.1 - c)}
      ↑(Finset.Icc (-((a : ℤ) - 2)) ((a : ℤ) - 2)) := by
    intro q hq
    simp only [Finset.mem_coe, mem_filter, mem_product] at hq
    obtain ⟨c1, c2, -, -⟩ := (mem_gapDiagram ha0).mp (mem_filterDiagram.mp hq.1.1).1
    obtain ⟨d1, d2, -, -⟩ := (mem_gapDiagram ha0).mp (mem_filterDiagram.mp hq.1.2).1
    have c1' : (1 : ℤ) ≤ q.1.1 := by exact_mod_cast c1
    have d1' : (1 : ℤ) ≤ q.2.1 := by exact_mod_cast d1
    have c2' := cast_le_pred (a := a) ha0 c2
    have d2' := cast_le_pred (a := a) ha0 d2
    simp only [Finset.mem_coe, mem_Icc]
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [← card_crossPairShift]
  refine congrArg card ?_
  ext q
  simp only [mem_filter, mem_product, mem_crossPairShift]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    rw [show (q.2.1 : ℤ) - q.1.1 - c = u - c from by omega] at h3
    exact ⟨⟨h1, h2⟩, by omega, by omega⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    have h5 : (q.2.1 : ℤ) - q.1.1 - c = u - c := by omega
    exact ⟨⟨⟨h1, h2⟩, by rw [h5]; omega⟩, by omega⟩

/-! ### Folding the negative column shifts -/

/-- A sum over a symmetric range of shifts splits into the term at `0` and the pairs
`{u, -u}`. -/
theorem sum_shift_split {A : ℤ} (hA : 0 ≤ A) (f : ℤ → ℕ) :
    ∑ u ∈ Finset.Icc (-A) A, f u = f 0 + ∑ u ∈ Finset.Icc 1 A, (f u + f (-u)) := by
  have h1 : Finset.Icc (-A) A = Finset.Icc (-A) (-1) ∪ Finset.Icc 0 A := by
    ext x
    simp only [mem_union, mem_Icc]
    omega
  have h2 : Disjoint (Finset.Icc (-A) (-1)) (Finset.Icc (0 : ℤ) A) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_Icc] at hx hx'
    omega
  have h3 : Finset.Icc (0 : ℤ) A = insert 0 (Finset.Icc 1 A) := by
    ext x
    simp only [mem_insert, mem_Icc]
    omega
  have h4 : (0 : ℤ) ∉ Finset.Icc (1 : ℤ) A := by simp
  have h5 : ∑ u ∈ Finset.Icc (-A) (-1), f u = ∑ u ∈ Finset.Icc (1 : ℤ) A, f (-u) := by
    refine Finset.sum_nbij' (fun u => -u) (fun u => -u) (fun u hu => ?_) (fun u hu => ?_)
      (fun u _ => neg_neg u) (fun u _ => neg_neg u) (fun u _ => ?_)
    · simp only [mem_Icc] at hu ⊢
      omega
    · simp only [mem_Icc] at hu ⊢
      omega
    · rw [neg_neg]
  rw [h1, Finset.sum_union h2, h3, Finset.sum_insert h4, h5, Finset.sum_add_distrib]
  omega

/-- **The pairs in the first window**:
`#{(g, h) ∈ D × E : 0 ≤ h - g < a} = T_{D,E}(0, 0)
  + ∑_{u=1}^{a-2} (T_{D,E}(u, β u) + T_{E,D}(u, β u + 1))`. -/
@[hjo "lem_cross_pairs_near_diagonal"]
theorem card_window_zero (hco : a.Coprime b) (ha : 1 < a) (hD : D ⊆ (finspan {a, b}).gaps)
    (hE : E ⊆ (finspan {a, b}).gaps) :
    #{p ∈ D ×ˢ E | 0 ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < a}
      = crossTailCount a b D E 0 0
        + ∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2),
            (crossTailCount a b D E u (Gaps.beta a b u)
              + crossTailCount a b E D u (Gaps.beta a b u + 1)) := by
  have hw := card_window_eq_sum hco ha hD hE 0
  simp only [zero_mul, sub_zero] at hw
  rw [hw, sum_shift_split (by omega : (0 : ℤ) ≤ (a : ℤ) - 2)
    fun u => crossTailCount a b D E u (Gaps.beta a b u)]
  congr 1
  · rw [show Gaps.beta a b 0 = 0 from by simp [Gaps.beta]]
  · refine Finset.sum_congr rfl fun u hu => ?_
    simp only [mem_Icc] at hu
    have hnd : ¬ (a : ℤ) ∣ u := not_dvd_of_lt (by omega) (by omega)
    have key : crossTailCount a b D E (-u) (Gaps.beta a b (-u))
        = crossTailCount a b E D u (Gaps.beta a b u + 1) := by
      rw [beta_neg hco (by omega) hnd, crossTailCount_swap, neg_neg,
        show -(-Gaps.beta a b u - 1) = Gaps.beta a b u + 1 from by ring]
    rw [key]

/-- **The pairs in the second window**:
`#{(g, h) ∈ D × E : b ≤ h - g < a + b} = T_{E,D}(0, β 1 + 1)
  + ∑_{u=1}^{a-2} (T_{D,E}(u, β (u-1)) + T_{E,D}(u, β (u+1) + 1))`. -/
@[hjo "lem_cross_pairs_near_b"]
theorem card_window_b (hco : a.Coprime b) (ha : 1 < a) (hD : D ⊆ (finspan {a, b}).gaps)
    (hE : E ⊆ (finspan {a, b}).gaps) :
    #{p ∈ D ×ˢ E | (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b}
      = crossTailCount a b E D 0 (Gaps.beta a b 1 + 1)
        + ∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2),
            (crossTailCount a b D E u (Gaps.beta a b (u - 1))
              + crossTailCount a b E D u (Gaps.beta a b (u + 1) + 1)) := by
  have hw := card_window_eq_sum hco ha hD hE 1
  simp only [one_mul] at hw
  have hfilter : {p ∈ D ×ˢ E | (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b}
      = {p ∈ D ×ˢ E | 0 ≤ (p.2 : ℤ) - p.1 - b ∧ (p.2 : ℤ) - p.1 - b < a} :=
    Finset.filter_congr fun p _ => by omega
  rw [hfilter, hw, sum_shift_split (by omega : (0 : ℤ) ≤ (a : ℤ) - 2)
    fun u => crossTailCount a b D E u (Gaps.beta a b (u - 1))]
  congr 1
  · have hnd : ¬ (a : ℤ) ∣ (1 : ℤ) := not_dvd_of_lt (by omega) (by omega)
    rw [show (0 : ℤ) - 1 = -(1 : ℤ) from by ring, beta_neg hco (by omega) hnd,
      crossTailCount_swap, neg_zero,
      show -(-Gaps.beta a b 1 - 1) = Gaps.beta a b 1 + 1 from by ring]
  · refine Finset.sum_congr rfl fun u hu => ?_
    simp only [mem_Icc] at hu
    have hnd : ¬ (a : ℤ) ∣ (u + 1) := not_dvd_of_lt (by omega) (by omega)
    have key : crossTailCount a b D E (-u) (Gaps.beta a b (-u - 1))
        = crossTailCount a b E D u (Gaps.beta a b (u + 1) + 1) := by
      rw [show -u - 1 = -(u + 1) from by ring, beta_neg hco (by omega) hnd,
        crossTailCount_swap, neg_neg,
        show -(-Gaps.beta a b (u + 1) - 1) = Gaps.beta a b (u + 1) + 1 from by ring]
    rw [key]

end HJO.CrossDinv
