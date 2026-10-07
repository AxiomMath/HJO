/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.LabelCube
public import HJO.DyckInversions
public meta import HJO.Attr

/-! # The inversion number of a member of a class

Fix a partial Dyck path `π`, a no-attack labelling `w` of it with prescription `σ`, and two
consecutive letters `m`, `m + 1` one of which occurs among the entries of `σ`. The inversions of a
member `w'` of the class `K_m(π, σ, w)` split into those with both positions in the two-letter
support and those without. The second kind number `e`, whatever the member: the two letters being
consecutive, a letter from outside the support compares the same way with either of them, which is
`HJO.Dyck.card_filter_invSet_congr_of_covBy`. The first kind are the attacking pairs internal to the
support, and such a pair joins two *adjacent* indices of one run — one run by
`HJO.Sym.notMem_of_cutBlock_ne`, adjacent by `HJO.Dyck.notMem_attackSet_of_add_two_le` — and inverts
exactly when the earlier of the two carries `m + 1`, the letters alternating along a run. Counting
those run by run gives the formula.

## Main definitions

* `HJO.Dyck.safeWord`: a labelling read as a word whose letters outside the window avoid
  `{m, m+1}`.

## Main results

* `HJO.Sym.mem_Icc_iff_notMem_cutSet`: the non-cuts of the `t`-th block are the indices `c` with
  `a_t ≤ c ≤ a_t + l_t - 2`.
* `HJO.Dyck.card_filter_invSet_eq_of_labelSupport_eq` and
  `HJO.Dyck.card_filter_invSet_eq_of_mem_labelClass`: the inversions not internal to the support are
  the same in number for any two labellings with that support that agree off it — in particular for
  every member of the class, and for the relabelling `τ_m w`, which is not a member of it.
* `HJO.Dyck.card_filter_invSet_internal`: the inversions internal to the support are the runs'
  consecutive pairs whose earlier index carries `m + 1`.
* `HJO.Dyck.invNumber_eq_of_mem_labelClass`: the weight of a member of the class.

## Implementation notes

*`HJO.Dyck.safeWord` exists only because letters are indexed from `0`.* The word
`HJO.Dyck.wordOfFin w` carries the junk letter `0` at the positions from `N` on, and at `m = 0` that
junk lies in the pair `{m, m+1}`, so those positions would count as two-letter positions outside the
support — which is exactly the hypothesis `HJO.Dyck.card_filter_invSet_congr_of_covBy` needs, stated
for all of `ℕ`. Replacing the junk by `m + 2` repairs that, and changes no inversion: both positions
of an attacking pair lie in the window.

*The `e` is written as a cardinality of a filtered inversion set* rather than as the
set-builder `#{(i,j) ∈ At(π) : w_i > w_j, {i,j} ⊄ S_m(w)}`, so that it is literally the
quantity `HJO.Dyck.card_filter_invSet_congr_of_covBy` compares. The two agree by
`HJO.Dyck.mem_invSet`.

*`σ` is not assumed to have distinct entries*, and `m ≥ 1` is not assumed; what is needed is a `j₀`
with `σ j₀ ∈ {m, m+1}`, which makes the support nonempty and hence every run nonempty. Without it
the statement is junk at an empty support: `a_1 = 0` and `l_1 = 0` make the index window
`{a_1, …, a_1 + l_1 - 2}` the singleton `{0}` rather than empty, truncated subtraction in `ℕ` being
what it is.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4.
-/

@[expose] public section

open Finset

namespace HJO.Sym

variable {p : ℕ} {C : Finset ℕ} {t c : ℕ}

/-- **The non-cuts of a block are the indices at distance at most `l_t - 2` from its start.** An
index `c` of `{1, …, p}` lies in the `t`-th block and is not a cut exactly when both `c` and `c + 1`
lie in that block, which for the interval `{a_t, …, a_t + l_t - 1}` says `a_t ≤ c ≤ a_t + l_t - 2`.
These are the consecutive pairs internal to the block. -/
theorem mem_Icc_iff_notMem_cutSet (hp : 1 ≤ p) (hC : C ⊆ Ico 1 p) (ht : 1 ≤ t)
    (ht' : t ≤ #C + 1) (c : ℕ) :
    (c ∈ Ico 1 p ∧ c ∉ C ∧ cutBlockIdx C c = t) ↔
      (cutBlockMin p C t ≤ c ∧ c ≤ cutBlockMin p C t + #(cutBlock p C t) - 2) := by
  have hne := cutBlock_nonempty hp hC ht ht'
  have hl : 1 ≤ #(cutBlock p C t) := one_le_card_cutBlock hne
  have ha : 1 ≤ cutBlockMin p C t := one_le_cutBlockMin hne
  have hap : cutBlockMin p C t ≤ p := cutBlockMin_le_card hne
  constructor
  · rintro ⟨hcIco, hcC, hcidx⟩
    obtain ⟨h1, h2⟩ := mem_Ico.1 hcIco
    have hcblk : c ∈ cutBlock p C t := hcidx ▸ mem_cutBlock_cutBlockIdx h1 (by omega)
    obtain ⟨t'', hc'', hc1''⟩ := (exists_mem_cutBlock_and_succ_mem_iff_notMem h1 h2).2 hcC
    have ht'' : t'' = t := by rw [← cutBlockIdx_eq_of_mem hc'', hcidx]
    subst ht''
    rw [mem_cutBlock_iff_between hne] at hcblk hc1''
    omega
  · rintro ⟨hge, hle⟩
    have hcblk : c ∈ cutBlock p C t := (mem_cutBlock_iff_between hne).2 ⟨hge, by omega⟩
    have hc1blk : c + 1 ∈ cutBlock p C t :=
      (mem_cutBlock_iff_between hne).2 ⟨by omega, by omega⟩
    have hcp := (mem_cutBlock.1 hc1blk).1.2
    have h1 : 1 ≤ c := by omega
    have h2 : c < p := by omega
    exact ⟨mem_Ico.2 ⟨h1, h2⟩,
      (exists_mem_cutBlock_and_succ_mem_iff_notMem h1 h2).1 ⟨t, hcblk, hc1blk⟩,
      cutBlockIdx_eq_of_mem hcblk⟩

end HJO.Sym

namespace HJO.Dyck

open HJO.Sym

variable {N k : ℕ} {x : Fin N → ℕ} {σ : Fin k → ℕ} {m : ℕ} {w w' : Fin N → ℕ}

/-- A letter of `{m, m+1}` above another letter of `{m, m+1}` is `m + 1`. -/
private theorem eq_succ_of_lt {m u v : ℕ} (hu : u = m ∨ u = m + 1) (hv : v = m ∨ v = m + 1)
    (h : v < u) : u = m + 1 := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> omega

/-- Of two distinct letters of `{m, m+1}` the one that is `m + 1` is the larger. -/
private theorem lt_of_eq_succ {m u v : ℕ} (hv : v = m ∨ v = m + 1) (hu : u = m + 1) (h : v ≠ u) :
    v < u := by
  rcases hv with rfl | rfl <;> omega

/-! ### A labelling read as a word that avoids the two letters off the window -/

/-- The labelling `w` read as a word on all of `ℕ` whose letters outside the window of the `N`
positions avoid `{m, m+1}`. `HJO.Dyck.wordOfFin` carries the junk letter `0` there, which is `m`
itself when `m = 0`; the inversion comparison of `HJO.Dyck.card_filter_invSet_congr_of_covBy` asks
for the two-letter positions to be exactly a given finite set, so the junk must be moved out of the
pair. No inversion of an attack set reads it. -/
def safeWord (m : ℕ) {N : ℕ} (w : Fin N → ℕ) (q : ℕ) : ℕ :=
  if q < N then wordOfFin w q else m + 2

theorem safeWord_of_lt {q : ℕ} (h : q < N) : safeWord m w q = wordOfFin w q := by
  simp [safeWord, h]

/-- The positions carrying one of the two letters are exactly the two-letter support. -/
theorem safeWord_mem_pair_iff (m : ℕ) (w : Fin N → ℕ) (q : ℕ) :
    (safeWord m w q = m ∨ safeWord m w q = m + 1) ↔ q ∈ labelSupport m w := by
  rw [mem_labelSupport]
  by_cases h : q < N
  · rw [safeWord_of_lt h]
    simp [h]
  · simp [safeWord, h]

/-- The inversions of an attack set do not read the letters off the window. -/
theorem invSet_safeWord (x : Fin N → ℕ) (m : ℕ) (w : Fin N → ℕ) :
    invSet (attackSet x) (safeWord m w) = invSet (attackSet x) (wordOfFin w) := by
  refine invSet_congr fun q hq => ?_
  have h2 : q.2 < N := snd_lt_of_mem_attackSet hq
  have h1 : q.1 < N := lt_trans (fst_lt_snd_of_mem_attackSet hq) h2
  rw [safeWord_of_lt h1, safeWord_of_lt h2]

/-! ### The inversions not internal to the support -/

/-- **The inversions not internal to the support do not depend on the member of the class**: the `e`
of the module docstring. Both labellings carry one of the two letters exactly on the common support
and agree off it, and the two letters are consecutive, so a letter from outside the support compares
the same way with either of them. -/
theorem card_filter_invSet_eq_of_labelSupport_eq (hsupp : labelSupport m w' = labelSupport m w)
    (hoff : ∀ i : Fin N, (i : ℕ) ∉ labelSupport m w → w' i = w i) :
    #{q ∈ invSet (attackSet x) (wordOfFin w') |
        ¬(q.1 ∈ labelSupport m w ∧ q.2 ∈ labelSupport m w)} =
      #{q ∈ invSet (attackSet x) (wordOfFin w) |
        ¬(q.1 ∈ labelSupport m w ∧ q.2 ∈ labelSupport m w)} := by
  rw [← invSet_safeWord x m w, ← invSet_safeWord x m w']
  refine (card_filter_invSet_congr_of_covBy (Order.covBy_add_one m) (attackSet x)
    (labelSupport m w) (safeWord_mem_pair_iff m w) (fun q => ?_) (fun q hq => ?_)).symm
  · rw [safeWord_mem_pair_iff m w' q, hsupp]
  · by_cases hqN : q < N
    · rw [safeWord_of_lt hqN, safeWord_of_lt hqN, wordOfFin_of_lt _ hqN, wordOfFin_of_lt _ hqN]
      exact hoff ⟨q, hqN⟩ hq
    · simp [safeWord, hqN]

/-- The instance at a member of the class, which has both properties. -/
theorem card_filter_invSet_eq_of_mem_labelClass (hw' : w' ∈ labelClass x σ m w) :
    #{q ∈ invSet (attackSet x) (wordOfFin w') |
        ¬(q.1 ∈ labelSupport m w ∧ q.2 ∈ labelSupport m w)} =
      #{q ∈ invSet (attackSet x) (wordOfFin w) |
        ¬(q.1 ∈ labelSupport m w ∧ q.2 ∈ labelSupport m w)} :=
  card_filter_invSet_eq_of_labelSupport_eq hw'.2.1 hw'.2.2

/-! ### The inversions internal to the support -/

/-- Two adjacent indices of one run carry different letters, for a member of the class. -/
theorem wordOfFin_sortNth_ne_succ_of_mem_labelClass (hw' : w' ∈ labelClass x σ m w) {c t : ℕ}
    (hct : c ∈ labelRun x m w t) (hc1t : c + 1 ∈ labelRun x m w t) :
    wordOfFin w' (sortNth (labelSupport m w) (c + 1)) ≠
      wordOfFin w' (sortNth (labelSupport m w) c) := by
  intro heq
  rw [wordOfFin_sortNth_eq_iff_even_of_mem_labelClass hw' (by omega : c ≤ c + 1) hct hc1t] at heq
  omega

/-- **The inversions internal to the support are the runs' consecutive pairs starting at `m + 1`.**
An attacking pair inside the support joins two adjacent indices of one run, by
`HJO.Sym.notMem_of_cutBlock_ne` and `HJO.Dyck.notMem_attackSet_of_add_two_le`, and it is an
inversion exactly when the earlier of the two carries `m + 1`, the letters along a run alternating
between the two. -/
theorem card_filter_invSet_internal (hx : IsPartialDyck k N x) (hw : w ∈ noAttackLabellings x σ)
    (hw' : w' ∈ labelClass x σ m w) :
    #{q ∈ invSet (attackSet x) (wordOfFin w') |
        q.1 ∈ labelSupport m w ∧ q.2 ∈ labelSupport m w} =
      #{c ∈ Ico 1 #(labelSupport m w) | c ∉ labelCutSet x m w ∧
        wordOfFin w' (sortNth (labelSupport m w) c) = m + 1} := by
  have hR : IsTransitiveAttackSet N (attackSet x) := isTransitiveAttackSet_attackSet hx.mono
  refine (Finset.card_bij (fun c _ => (sortNth (labelSupport m w) c,
    sortNth (labelSupport m w) (c + 1))) ?_ ?_ ?_).symm
  · -- the map lands among the internal inversions
    intro c hc
    obtain ⟨hcIco, hcC, hcm⟩ := mem_filter.1 hc
    obtain ⟨hc1, hcp⟩ := mem_Ico.1 hcIco
    obtain ⟨t, hct, hc1t⟩ := (exists_mem_cutBlock_and_succ_mem_iff_notMem hc1 hcp).2 hcC
    have hmemR : (sortNth (labelSupport m w) c, sortNth (labelSupport m w) (c + 1))
        ∈ attackSet x := by
      by_contra hcon
      exact hcC (mem_cutSet_iff.2 ⟨hc1, hcp, hcon⟩)
    refine mem_filter.2 ⟨mem_invSet.2 ⟨hmemR, ?_⟩,
      sortNth_mem hc1 (by omega), sortNth_mem (by omega) (by omega)⟩
    exact lt_of_eq_succ
      (wordOfFin_mem_pair_of_mem_labelClass hw' (sortNth_mem (by omega) (by omega))) hcm
      (wordOfFin_sortNth_ne_succ_of_mem_labelClass hw' hct hc1t)
  · -- the map is injective
    intro c₁ h₁ c₂ h₂ heq
    obtain ⟨hc₁1, hc₁p⟩ := mem_Ico.1 (mem_filter.1 h₁).1
    obtain ⟨hc₂1, hc₂p⟩ := mem_Ico.1 (mem_filter.1 h₂).1
    exact sortNth_injOn hc₁1 (by omega) hc₂1 (by omega) (congrArg Prod.fst heq)
  · -- every internal inversion arises this way
    intro q hq
    obtain ⟨hqinv, hq1, hq2⟩ := mem_filter.1 hq
    obtain ⟨hqR, hqlt⟩ := mem_invSet.1 hqinv
    have hfst : q.1 < q.2 := fst_lt_snd_of_mem_attackSet hqR
    have hc1 : 1 ≤ sortIdx (labelSupport m w) q.1 := one_le_sortIdx _ _
    have hcp : sortIdx (labelSupport m w) q.1 ≤ #(labelSupport m w) := sortIdx_le_card hq1
    have hd1 : 1 ≤ sortIdx (labelSupport m w) q.2 := one_le_sortIdx _ _
    have hdp : sortIdx (labelSupport m w) q.2 ≤ #(labelSupport m w) := sortIdx_le_card hq2
    have hcd : sortIdx (labelSupport m w) q.1 < sortIdx (labelSupport m w) q.2 :=
      sortIdx_lt_sortIdx hq1 hfst
    have hsc : sortNth (labelSupport m w) (sortIdx (labelSupport m w) q.1) = q.1 :=
      sortNth_sortIdx hq1
    have hsd : sortNth (labelSupport m w) (sortIdx (labelSupport m w) q.2) = q.2 :=
      sortNth_sortIdx hq2
    have hqR' : (sortNth (labelSupport m w) (sortIdx (labelSupport m w) q.1),
        sortNth (labelSupport m w) (sortIdx (labelSupport m w) q.2)) ∈ attackSet x := by
      rw [hsc, hsd]; exact hqR
    have hcblk : sortIdx (labelSupport m w) q.1 ∈
        labelRun x m w (cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) q.1)) :=
      mem_cutBlock_cutBlockIdx hc1 hcp
    have hdblk : sortIdx (labelSupport m w) q.2 ∈
        labelRun x m w (cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) q.2)) :=
      mem_cutBlock_cutBlockIdx hd1 hdp
    have hsame : cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) q.2) =
        cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) q.1) := by
      by_contra hcon
      exact notMem_of_cutBlock_ne hR hc1 hcd hdp hcblk hdblk (Ne.symm hcon) hqR'
    rw [hsame] at hdblk
    have hsucc : sortIdx (labelSupport m w) q.2 = sortIdx (labelSupport m w) q.1 + 1 := by
      by_contra hcon
      exact notMem_attackSet_of_add_two_le hx.toIsSquareDyck hw (by omega) hcblk hdblk hqR'
    refine ⟨sortIdx (labelSupport m w) q.1, mem_filter.2 ⟨mem_Ico.2 ⟨hc1, by omega⟩, ?_, ?_⟩, ?_⟩
    · by_contra hcon
      exact (mem_cutSet_iff.1 hcon).2.2 (by rw [← hsucc]; exact hqR')
    · rw [hsc]
      exact eq_succ_of_lt (wordOfFin_eq_or_eq_of_mem_labelSupport (hw'.2.1.symm ▸ hq1))
        (wordOfFin_eq_or_eq_of_mem_labelSupport (hw'.2.1.symm ▸ hq2)) hqlt
    · rw [← hsucc, hsc, hsd]

/-! ### The inversion number of a member of a class -/

/-- **The weight of a member of the class.** With `e` the number of inversions of `w` not internal
to the two-letter support, the inversion number of any `w' ∈ K_m(π, σ, w)` is `e` plus, run by run,
the number of indices `c` with `a_t ≤ c ≤ a_t + l_t - 2` at which `w'` carries `m + 1`. The pairs
not internal to the support contribute `e` whatever the member, by
`HJO.Dyck.card_filter_invSet_congr_of_covBy`, and the pairs internal to it are the consecutive pairs
of a run. -/
@[hjo "lem_cm_class_weight"]
theorem invNumber_eq_of_mem_labelClass (hx : IsPartialDyck k N x)
    (hw : w ∈ noAttackLabellings x σ) {j₀ : Fin k} (hj₀ : σ j₀ = m ∨ σ j₀ = m + 1)
    (hw' : w' ∈ labelClass x σ m w) :
    invNumber (attackSet x) (wordOfFin w') =
      #{q ∈ invSet (attackSet x) (wordOfFin w) |
          ¬(q.1 ∈ labelSupport m w ∧ q.2 ∈ labelSupport m w)} +
        ∑ t ∈ Icc 1 (labelRunCount x m w),
          #{c ∈ Icc (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)
              (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t +
                #(labelRun x m w t) - 2) |
            wordOfFin w' (sortNth (labelSupport m w) c) = m + 1} := by
  have hp : 1 ≤ #(labelSupport m w) := one_le_card_labelSupport hx hw hj₀
  have hCsub : labelCutSet x m w ⊆ Ico 1 #(labelSupport m w) := cutSet_subset_Ico _ _
  -- the internal inversions, counted run by run
  have hfib : #{c ∈ Ico 1 #(labelSupport m w) | c ∉ labelCutSet x m w ∧
        wordOfFin w' (sortNth (labelSupport m w) c) = m + 1} =
      ∑ t ∈ Icc 1 (labelRunCount x m w),
        #{c ∈ Icc (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)
            (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t +
              #(labelRun x m w t) - 2) |
          wordOfFin w' (sortNth (labelSupport m w) c) = m + 1} := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := cutBlockIdx (labelCutSet x m w)) (t := Icc 1 (labelRunCount x m w))
      (fun c _ => mem_Icc.2 ⟨one_le_cutBlockIdx _ _, cutBlockIdx_le _ _⟩)]
    refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨ht1, htr⟩ := mem_Icc.1 ht
    congr 1
    refine Finset.ext fun c => ?_
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hcIco, hcC, hcm⟩, hcidx⟩
      exact ⟨(mem_Icc_iff_notMem_cutSet hp hCsub ht1 htr c).1 ⟨hcIco, hcC, hcidx⟩, hcm⟩
    · rintro ⟨hcbounds, hcm⟩
      obtain ⟨hcIco, hcC, hcidx⟩ := (mem_Icc_iff_notMem_cutSet hp hCsub ht1 htr c).2 hcbounds
      exact ⟨⟨hcIco, hcC, hcm⟩, hcidx⟩
  rw [invNumber, ← Finset.card_filter_add_card_filter_not
      (fun q : ℕ × ℕ => q.1 ∈ labelSupport m w ∧ q.2 ∈ labelSupport m w),
    card_filter_invSet_eq_of_mem_labelClass hw',
    card_filter_invSet_internal hx hw hw', hfib, Nat.add_comm]

end HJO.Dyck
