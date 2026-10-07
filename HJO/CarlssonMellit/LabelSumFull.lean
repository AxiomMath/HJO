/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.LabelSum
public meta import HJO.Attr

/-! # The class sum when neither label is special

Fix a partial Dyck path `π` of level `k`, a no-attack labelling `w` of it with prescription `σ`, and
two consecutive letters `m`, `m + 1` *neither* of which occurs among the entries of `σ`. Summing
`q^{inv(At(π), w')} z^{(k)}_{w'}` over the class `K_m(π, σ, w)` then gives

`q^e · g · ∏_{t=1}^{r} (a_m(l_t, 0) + a_m(l_t, 1))`,

the fully symmetric companion of `HJO.Dyck.finsum_labelClass`. The difference from that lemma is a
single observation: a position below the level carries a letter of `σ`, so under this hypothesis no
position of the two-letter support lies below the level, and nothing pins the letter at the
support's first position. The bit of the first run is therefore free, the class is the *whole* cube
`{0,1}^r` rather than a face of it, and every factor of the product carries both terms.

## Main results

* `HJO.Dyck.notMem_labelSupport_of_lt_level`: no position below the level carries either letter.
* `HJO.Dyck.ofRunBits_eq_of_mem_labelClass`: the bits of a member of the class recover it, so the
  bit map is injective on the class.
* `HJO.Dyck.mem_labelClass_ofRunBits`: every tuple of bits prescribes a member of the class.
* `HJO.Dyck.bijOn_runBit_univ`: the class is the whole cube.
* `HJO.Dyck.weight_eq_prod_runWeight_of_card_pos`: the weight of a member of the class.
* `HJO.Dyck.finsum_labelClass_full`: the class sum.
* `HJO.Dyck.finsum_labelClass_of_labelSupport_eq_empty`: the class sum at an empty two-letter
  support, the degenerate case the previous result excludes. The two together give the class sum
  for every support: `HJO.Dyck.finsum_labelClass_full` for `S_m(w) ≠ ∅` and this one for
  `S_m(w) = ∅`.

## Implementation notes

*The two-letter support is assumed nonempty*, as `1 ≤ #S_m(w)`. Here it does not follow from the
hypothesis on `σ` — under it no letter of `σ` is `m` or `m + 1`, so nothing forces `w` to carry
either letter at all — and it cannot be dropped: `HJO.Dyck.labelRunCount` is `#C + 1`, which is `1`
and not `0` at an empty support, so the product below would acquire a spurious factor
`a_m(0,0) + a_m(0,1) = 2` where the `∏_{t=1}^{r}` is the empty product over `r = 0`
blocks of the empty index range. The same nondegeneracy is what the hypothesis `σ j₀ ∈ {m, m+1}`
supplies for `HJO.Dyck.finsum_labelClass` and `HJO.Dyck.invNumber_eq_of_mem_labelClass`, whose
statements are junk at an empty support for the same reason.

*The statement at an empty support is nevertheless true, and is proved separately.*
`HJO.Dyck.finsum_labelClass_of_labelSupport_eq_empty` states it with the block product replaced by
the empty product over `r = 0` blocks, so the two theorems together cover every two-letter
support. The split exists only because the Lean encoding and the mathematical count disagree on the
number of blocks at an empty support: `HJO.Dyck.labelRunCount` counts `#C + 1` blocks, which is `1`
rather than the `0` runs of the empty set, so a single statement covering both cases would have to
case-split on the support anyway. At an empty support the class is the singleton `{w}` and the claim
is `q^{inv} z^{(k)}_w` on both sides, needing neither `π` a Dyck path nor a hypothesis on `σ`.

*The cube bijection is reproved here rather than reused.* `HJO.Dyck.bijOn_runBit` is stated only for
the face of the cube cut out by the forced first bit, and its hypothesis `σ j₀ ∈ {m, m+1}` is the
negation of the hypothesis of this file, so neither the bijection nor an unconstrained version
extractable from it is available. What the constrained proof establishes and this one repeats is the
part that mentions neither `σ` nor the level: that a tuple of bits prescribes a labelling separating
every attacking pair, and that the prescribed labelling has the same two-letter support. Factoring
that half out of `HJO.Dyck.bijOn_runBit` would let both faces and the whole cube share it.

*`HJO.Dyck.invNumber_eq_of_mem_labelClass` is likewise restated.*
`HJO.Dyck.invNumber_eq_of_mem_labelClass` and `HJO.Dyck.weight_eq_prod_runWeight` carry the
hypothesis `σ j₀ ∈ {m, m+1}` and use it only to produce `1 ≤ #S_m(w)`;
`HJO.Dyck.invNumber_eq_of_mem_labelClass_of_card_pos` and
`HJO.Dyck.weight_eq_prod_runWeight_of_card_pos` below are those statements with that hypothesis
replaced by the cardinality bound itself, so their proofs cite the same lemmas.

*The hypotheses are weaker than Carlsson and Mellit's*, as for the lemmas this one accompanies: `σ`
is not assumed to have pairwise distinct entries, and `m ≥ 1` is not assumed, letters being
`0`-based here.

## References

E. Carlsson and
A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697,
Section 4.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

open HJO.Sym

variable {N k : ℕ} {x : Fin N → ℕ} {σ : Fin k → ℕ} {m : ℕ} {w w' : Fin N → ℕ}

/-- Two letters of `{m, m+1}` that are `m` together are equal: the whole arithmetic of comparing a
prescribed letter with an actual one. -/
private theorem eq_of_eq_m_iff {m u v : ℕ} (hu : u = m ∨ u = m + 1) (hv : v = m ∨ v = m + 1)
    (h : u = m ↔ v = m) : u = v := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all

/-! ### No position below the level carries either letter -/

/-- **The two-letter support avoids the positions below the level** when neither `m` nor `m + 1`
occurs among the entries of `σ`: a position below the level carries the letter `σ` prescribes
there. -/
theorem notMem_labelSupport_of_lt_level (hx : IsPartialDyck k N x)
    (hw : w ∈ noAttackLabellings x σ) (hσ : ∀ j : Fin k, σ j ≠ m ∧ σ j ≠ m + 1) {q : ℕ}
    (hq : q < k) : q ∉ labelSupport m w := fun hmem => by
  have h : wordOfFin w q = σ ⟨q, hq⟩ := wordOfFin_eq_of_lt_level hx.le_length hw hq
  rcases wordOfFin_eq_or_eq_of_mem_labelSupport hmem with hm | hm
  · exact (hσ ⟨q, hq⟩).1 (by rw [← h]; exact hm)
  · exact (hσ ⟨q, hq⟩).2 (by rw [← h]; exact hm)

/-! ### The bits of a member of the class recover it -/

/-- **A member of the class is the labelling its own bits prescribe.** Off the support both sides
are `w`, and at a position of the support the prescribed letter and the actual one are both drawn
from `{m, m+1}` and are `m` under the same parity condition. Only the bits of the runs `1, …, r`
are read. -/
theorem ofRunBits_eq_of_mem_labelClass {ε : ℕ → Bool} (hw' : w' ∈ labelClass x σ m w)
    (hε : ∀ t, 1 ≤ t → t ≤ labelRunCount x m w → ε t = runBit x m w w' t) :
    ofRunBits x m w ε = w' := by
  funext i
  by_cases hi : (i : ℕ) ∈ labelSupport m w
  · have hc1 : 1 ≤ sortIdx (labelSupport m w) (i : ℕ) := one_le_sortIdx _ _
    have hcp : sortIdx (labelSupport m w) (i : ℕ) ≤ #(labelSupport m w) := sortIdx_le_card hi
    have hsc : sortNth (labelSupport m w) (sortIdx (labelSupport m w) (i : ℕ)) = (i : ℕ) :=
      sortNth_sortIdx hi
    have hct : sortIdx (labelSupport m w) (i : ℕ) ∈
        labelRun x m w (cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) (i : ℕ))) :=
      mem_cutBlock_cutBlockIdx hc1 hcp
    have hne : (labelRun x m w
        (cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) (i : ℕ)))).Nonempty := ⟨_, hct⟩
    have hεt : ε (cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) (i : ℕ)))
        = runBit x m w w' (cutBlockIdx (labelCutSet x m w)
          (sortIdx (labelSupport m w) (i : ℕ))) :=
      hε _ (one_le_cutBlockIdx _ _) (cutBlockIdx_le _ _)
    have hpair : w' i = m ∨ w' i = m + 1 := by
      simpa [wordOfFin_val] using wordOfFin_mem_pair_of_mem_labelClass hw' hi
    have hw'i : wordOfFin w' (sortNth (labelSupport m w)
        (sortIdx (labelSupport m w) (i : ℕ))) = w' i := by rw [hsc, wordOfFin_val]
    rw [ofRunBits_of_mem hi]
    refine eq_of_eq_m_iff (bitLetter_eq_or _ _ _ _ _) hpair ?_
    rw [bitLetter_eq_iff_of_mem hct, hεt,
      ← wordOfFin_sortNth_eq_iff_parity hw' hne hct, hw'i]
  · rw [ofRunBits_of_notMem hi]
    exact (hw'.2.2 i hi).symm

/-! ### Every tuple of bits prescribes a member of the class -/

/-- **The labelling a tuple of bits prescribes lies in the class** when neither `m` nor `m + 1`
occurs among the entries of `σ`. The two-letter support is unmoved, since off it the letters of `w`
avoid the pair; the prescription below the level is inherited from `w`, no position there lying in
the support; and an attacking pair gets distinct letters — both positions outside the support
because `w` is a no-attack labelling, exactly one outside because then one letter lies in the pair
and the other does not, and both inside because the two indices are then adjacent in one run, by
`HJO.Sym.notMem_of_cutBlock_ne` and `HJO.Dyck.notMem_attackSet_of_add_two_le`, and adjacent indices
of a run alternate. -/
theorem mem_labelClass_ofRunBits (hx : IsPartialDyck k N x) (hw : w ∈ noAttackLabellings x σ)
    (hσ : ∀ j : Fin k, σ j ≠ m ∧ σ j ≠ m + 1) (ε : ℕ → Bool) :
    ofRunBits x m w ε ∈ labelClass x σ m w := by
  have hR : IsTransitiveAttackSet N (attackSet x) := isTransitiveAttackSet_attackSet hx.mono
  have hpair : ∀ q ∈ labelSupport m w, wordOfFin (ofRunBits x m w ε) q = m ∨
      wordOfFin (ofRunBits x m w ε) q = m + 1 := fun q hq => by
    rw [wordOfFin_ofRunBits_of_mem hq]
    exact bitLetter_eq_or _ _ _ _ _
  have hsupp : labelSupport m (ofRunBits x m w ε) = labelSupport m w := by
    refine Finset.ext fun q => ?_
    rw [mem_labelSupport]
    refine ⟨fun hq => ?_, fun hq => ⟨mem_range.1 (labelSupport_subset_range w hq), hpair q hq⟩⟩
    by_contra hnot
    rw [wordOfFin_ofRunBits_of_notMem hnot] at hq
    obtain ⟨h1, h2⟩ := ne_and_ne_of_notMem_twoLetterSupport hq.1 hnot
    rcases hq.2 with h | h
    · exact h1 h
    · exact h2 h
  have hnoattack : ∀ i j : Fin N, ((i : ℕ), (j : ℕ)) ∈ attackSet x →
      ofRunBits x m w ε i ≠ ofRunBits x m w ε j := by
    intro i j hij
    by_cases hi : (i : ℕ) ∈ labelSupport m w
    · by_cases hj : (j : ℕ) ∈ labelSupport m w
      · have hc1 : 1 ≤ sortIdx (labelSupport m w) (i : ℕ) := one_le_sortIdx _ _
        have hcp : sortIdx (labelSupport m w) (i : ℕ) ≤ #(labelSupport m w) := sortIdx_le_card hi
        have hd1 : 1 ≤ sortIdx (labelSupport m w) (j : ℕ) := one_le_sortIdx _ _
        have hdp : sortIdx (labelSupport m w) (j : ℕ) ≤ #(labelSupport m w) := sortIdx_le_card hj
        have hlt : (i : ℕ) < (j : ℕ) := fst_lt_snd_of_mem_attackSet hij
        have hcd : sortIdx (labelSupport m w) (i : ℕ) < sortIdx (labelSupport m w) (j : ℕ) :=
          sortIdx_lt_sortIdx hi hlt
        have hsci : sortNth (labelSupport m w) (sortIdx (labelSupport m w) (i : ℕ)) = (i : ℕ) :=
          sortNth_sortIdx hi
        have hscj : sortNth (labelSupport m w) (sortIdx (labelSupport m w) (j : ℕ)) = (j : ℕ) :=
          sortNth_sortIdx hj
        have hijR : (sortNth (labelSupport m w) (sortIdx (labelSupport m w) (i : ℕ)),
            sortNth (labelSupport m w) (sortIdx (labelSupport m w) (j : ℕ))) ∈ attackSet x := by
          rw [hsci, hscj]; exact hij
        have hcblk : sortIdx (labelSupport m w) (i : ℕ) ∈
            labelRun x m w
              (cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) (i : ℕ))) :=
          mem_cutBlock_cutBlockIdx hc1 hcp
        have hdblk : sortIdx (labelSupport m w) (j : ℕ) ∈
            labelRun x m w
              (cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) (j : ℕ))) :=
          mem_cutBlock_cutBlockIdx hd1 hdp
        have hsame : cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) (j : ℕ)) =
            cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) (i : ℕ)) := by
          by_contra hcon
          exact notMem_of_cutBlock_ne hR hc1 hcd hdp hcblk hdblk (Ne.symm hcon) hijR
        rw [hsame] at hdblk
        have hsucc : sortIdx (labelSupport m w) (j : ℕ) =
            sortIdx (labelSupport m w) (i : ℕ) + 1 := by
          by_contra hcon
          exact notMem_attackSet_of_add_two_le hx.toIsSquareDyck hw (by omega) hcblk hdblk hijR
        rw [ofRunBits_of_mem hi, ofRunBits_of_mem hj, hsucc]
        exact bitLetter_ne_succ hcblk (by rw [← hsucc]; exact hdblk)
      · obtain ⟨h1, h2⟩ := ne_and_ne_of_notMem_twoLetterSupport j.isLt hj
        rw [wordOfFin_val] at h1 h2
        rw [ofRunBits_of_mem hi, ofRunBits_of_notMem hj]
        rcases bitLetter_eq_or #(labelSupport m w) (labelCutSet x m w) m ε
          (sortIdx (labelSupport m w) (i : ℕ)) with h | h
        · rw [h]; exact fun hc => h1 hc.symm
        · rw [h]; exact fun hc => h2 hc.symm
    · by_cases hj : (j : ℕ) ∈ labelSupport m w
      · obtain ⟨h1, h2⟩ := ne_and_ne_of_notMem_twoLetterSupport i.isLt hi
        rw [wordOfFin_val] at h1 h2
        rw [ofRunBits_of_notMem hi, ofRunBits_of_mem hj]
        rcases bitLetter_eq_or #(labelSupport m w) (labelCutSet x m w) m ε
          (sortIdx (labelSupport m w) (j : ℕ)) with h | h
        · rw [h]; exact h1
        · rw [h]; exact h2
      · rw [ofRunBits_of_notMem hi, ofRunBits_of_notMem hj]
        exact ne_of_mem_noAttackLabellings hw hij
  refine ⟨⟨fun i j hij => ?_, hnoattack⟩, hsupp, fun i hi => ofRunBits_of_notMem hi⟩
  rw [ofRunBits_of_notMem
    (notMem_labelSupport_of_lt_level hx hw hσ (by rw [hij]; exact j.isLt))]
  exact eq_of_mem_noAttackLabellings hw hij

/-- **The bits of the prescribed labelling are the given ones**: at the first index of a run the
parity condition is vacuous, so the prescribed letter there is `m` exactly when the run's bit is
`0`. -/
theorem runBit_ofRunBits (hp : 1 ≤ #(labelSupport m w)) (ε : ℕ → Bool) {t : ℕ} (ht : 1 ≤ t)
    (ht' : t ≤ labelRunCount x m w) : runBit x m w (ofRunBits x m w ε) t = ε t := by
  have hCsub : labelCutSet x m w ⊆ Ico 1 #(labelSupport m w) := cutSet_subset_Ico _ _
  have hne : (labelRun x m w t).Nonempty := cutBlock_nonempty hp hCsub ht ht'
  have hamemS : sortNth (labelSupport m w)
      (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t) ∈ labelSupport m w :=
    sortNth_mem (one_le_cutBlockMin hne) (cutBlockMin_le_card hne)
  rw [runBit, wordOfFin_ofRunBits_of_mem hamemS,
    sortIdx_sortNth (one_le_cutBlockMin hne) (cutBlockMin_le_card hne)]
  have hiff := bitLetter_cutBlockMin (p := #(labelSupport m w)) (C := labelCutSet x m w)
    (t := t) (m := m) (ε := ε) hne
  rcases bitLetter_eq_or #(labelSupport m w) (labelCutSet x m w) m ε
    (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t) with h | h
  · rw [h, hiff.1 h]; simp
  · have hεt : ε t = true := by
      rcases Bool.eq_false_or_eq_true (ε t) with hb | hb
      · exact hb
      · rw [hiff.2 hb] at h; omega
    rw [h, hεt]; simp

/-! ### The class is the whole cube -/

/-- **The class of a labelling is the whole cube** when neither `m` nor `m + 1` occurs among the
entries of `σ`. With `B_1, …, B_r` the runs of the two-letter support, `w' ↦ ε(w')` is a bijection
from `K_m(π, σ, w)` onto all of `{0,1}^r`: no bit is forced, the support lying entirely above the
level, where `σ` prescribes nothing. This is `HJO.Dyck.bijOn_runBit` with its face constraint
removed. -/
theorem bijOn_runBit_univ (hx : IsPartialDyck k N x) (hw : w ∈ noAttackLabellings x σ)
    (hσ : ∀ j : Fin k, σ j ≠ m ∧ σ j ≠ m + 1) (hp : 1 ≤ #(labelSupport m w)) :
    Set.BijOn (fun w' (j : Fin (labelRunCount x m w)) => runBit x m w w' ((j : ℕ) + 1))
      (labelClass x σ m w) Set.univ := by
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · intro v₁ hv₁ v₂ hv₂ hbits
    have hbit : ∀ t, 1 ≤ t → t ≤ labelRunCount x m w →
        runBit x m w v₁ t = runBit x m w v₂ t := fun t ht ht' => by
      have h := congrFun hbits (⟨t - 1, by omega⟩ : Fin (labelRunCount x m w))
      simpa [show t - 1 + 1 = t by omega] using h
    rw [← ofRunBits_eq_of_mem_labelClass hv₁ (fun _ _ _ => rfl),
      ofRunBits_eq_of_mem_labelClass hv₂ hbit]
  · intro ε' _
    obtain ⟨ε, hεj⟩ : ∃ ε : ℕ → Bool, ∀ j : Fin (labelRunCount x m w),
        ε ((j : ℕ) + 1) = ε' j := by
      refine ⟨fun t => ε' ⟨(t - 1) % labelRunCount x m w, Nat.mod_lt _ (Nat.succ_pos _)⟩,
        fun j => ?_⟩
      exact congrArg ε' (Fin.ext (by rw [Nat.add_sub_cancel]; exact Nat.mod_eq_of_lt j.isLt))
    refine ⟨ofRunBits x m w ε, mem_labelClass_ofRunBits hx hw hσ ε, funext fun j => ?_⟩
    have hjlt : (j : ℕ) < labelRunCount x m w := j.isLt
    change runBit x m w (ofRunBits x m w ε) ((j : ℕ) + 1) = ε' j
    rw [runBit_ofRunBits hp ε (by omega) (by omega), hεj j]

/-! ### The weight of a member of the class -/

/-- **The weight of a member of the class**, `HJO.Dyck.invNumber_eq_of_mem_labelClass` with the
hypothesis that a letter of `σ` lies in `{m, m+1}` replaced by the nonemptiness of the two-letter
support, which is all that hypothesis was used for. -/
theorem invNumber_eq_of_mem_labelClass_of_card_pos (hx : IsPartialDyck k N x)
    (hw : w ∈ noAttackLabellings x σ) (hp : 1 ≤ #(labelSupport m w))
    (hw' : w' ∈ labelClass x σ m w) :
    invNumber (attackSet x) (wordOfFin w') =
      #{q ∈ invSet (attackSet x) (wordOfFin w) |
          ¬(q.1 ∈ labelSupport m w ∧ q.2 ∈ labelSupport m w)} +
        ∑ t ∈ Icc 1 (labelRunCount x m w),
          #{c ∈ Icc (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)
              (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t +
                #(labelRun x m w t) - 2) |
            wordOfFin w' (sortNth (labelSupport m w) c) = m + 1} := by
  have hCsub : labelCutSet x m w ⊆ Ico 1 #(labelSupport m w) := cutSet_subset_Ico _ _
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

variable {K : Type*} [CommRing K]

/-- **The weight of a member of the class, run by run**: `q^e` and the monomial `g` of the positions
off the two-letter support times the product of the runs' weights. This is
`HJO.Dyck.weight_eq_prod_runWeight` with the hypothesis on `σ` replaced by the nonemptiness of the
support. -/
theorem weight_eq_prod_runWeight_of_card_pos (q : K) (hx : IsPartialDyck k N x)
    (hw : w ∈ noAttackLabellings x σ) (hp : 1 ≤ #(labelSupport m w))
    (hw' : w' ∈ labelClass x σ m w) :
    scalarSeries K k q ^ invNumber (attackSet x) (wordOfFin w') * zmon K k w' =
      scalarSeries K k q ^ #{p ∈ invSet (attackSet x) (wordOfFin w) |
            ¬(p.1 ∈ labelSupport m w ∧ p.2 ∈ labelSupport m w)} *
          (∏ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) ∉ labelSupport m w),
            zvar K k (w i)) *
          ∏ t ∈ Icc 1 (labelRunCount x m w),
            runWeightZvar q k m (#(labelRun x m w t)) (runBit x m w w' t) := by
  have hCsub : labelCutSet x m w ⊆ Ico 1 #(labelSupport m w) := cutSet_subset_Ico _ _
  have hprod : (∏ t ∈ Icc 1 (labelRunCount x m w),
        scalarSeries K k q ^ #{c ∈ Icc (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)
          (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t + #(labelRun x m w t) - 2) |
          wordOfFin w' (sortNth (labelSupport m w) c) = m + 1}) *
      (∏ t ∈ Icc 1 (labelRunCount x m w),
        ∏ c ∈ labelRun x m w t, zvar K k (wordOfFin w' (sortNth (labelSupport m w) c)))
      = ∏ t ∈ Icc 1 (labelRunCount x m w),
        runWeightZvar q k m (#(labelRun x m w t)) (runBit x m w w' t) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t ht => pow_mul_prod_run_eq_runWeight q hw'
      (cutBlock_nonempty hp hCsub (mem_Icc.1 ht).1 (mem_Icc.1 ht).2)
  rw [invNumber_eq_of_mem_labelClass_of_card_pos hx hw hp hw', pow_add, zmon_eq_prod_runs hw',
    ← Finset.prod_pow_eq_pow_sum, ← hprod]
  ring

/-! ### The class sum -/

/-- **The class sum factorises over the runs, with both terms in every factor.** When neither `m`
nor `m + 1` occurs among the entries of `σ`, summing `q^{inv} z^{(k)}_{w'}` over the class
`K_m(π, σ, w)` gives `q^e g` times, for *every* run, the sum of that run's two weights. The class is
the whole cube of `HJO.Dyck.bijOn_runBit_univ`, the weight of a member is the product of the runs'
weights, and summing a product over a cube factorises it — `Finset.prod_univ_sum`. -/
@[hjo "lem_cm_class_sum_full"]
theorem finsum_labelClass_full (q : K) (hx : IsPartialDyck k N x)
    (hw : w ∈ noAttackLabellings x σ) (hσ : ∀ j : Fin k, σ j ≠ m ∧ σ j ≠ m + 1)
    (hp : 1 ≤ #(labelSupport m w)) :
    ∑ᶠ w' ∈ labelClass x σ m w,
        scalarSeries K k q ^ invNumber (attackSet x) (wordOfFin w') * zmon K k w'
      = scalarSeries K k q ^ #{p ∈ invSet (attackSet x) (wordOfFin w) |
            ¬(p.1 ∈ labelSupport m w ∧ p.2 ∈ labelSupport m w)} *
          (∏ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) ∉ labelSupport m w),
            zvar K k (w i)) *
          ∏ t ∈ Icc 1 (labelRunCount x m w),
            (runWeightZvar q k m (#(labelRun x m w t)) false +
              runWeightZvar q k m (#(labelRun x m w t)) true) := by
  classical
  rw [prod_Icc_one_eq_prod_fin (labelRunCount x m w)
    (fun t => runWeightZvar q k m (#(labelRun x m w t)) false +
      runWeightZvar q k m (#(labelRun x m w t)) true)]
  have hbij := bijOn_runBit_univ hx hw hσ hp
  have hfin : (labelClass x σ m w).Finite := by
    refine Set.Finite.of_finite_image ?_ hbij.injOn
    rw [hbij.image_eq]
    exact Set.toFinite _
  -- the sum over the class is the sum over the whole cube
  have hstep : ∑ w' ∈ hfin.toFinset,
        (scalarSeries K k q ^ invNumber (attackSet x) (wordOfFin w') * zmon K k w')
      = ∑ ε : Fin (labelRunCount x m w) → Bool,
        (scalarSeries K k q ^ #{p ∈ invSet (attackSet x) (wordOfFin w) |
              ¬(p.1 ∈ labelSupport m w ∧ p.2 ∈ labelSupport m w)} *
            (∏ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) ∉ labelSupport m w),
              zvar K k (w i)) *
            ∏ j : Fin (labelRunCount x m w),
              runWeightZvar q k m (#(labelRun x m w ((j : ℕ) + 1))) (ε j)) := by
    refine Finset.sum_bij
      (fun w' _ (j : Fin (labelRunCount x m w)) => runBit x m w w' ((j : ℕ) + 1)) ?_ ?_ ?_ ?_
    · intro _ _
      exact mem_univ _
    · intro v₁ h₁ v₂ h₂ heq
      exact hbij.injOn (hfin.mem_toFinset.1 h₁) (hfin.mem_toFinset.1 h₂) heq
    · intro ε _
      obtain ⟨v, hv, hveq⟩ := hbij.surjOn (Set.mem_univ ε)
      exact ⟨v, hfin.mem_toFinset.2 hv, hveq⟩
    · intro v hv
      rw [weight_eq_prod_runWeight_of_card_pos q hx hw hp (hfin.mem_toFinset.1 hv),
        prod_Icc_one_eq_prod_fin (labelRunCount x m w)
          (fun t => runWeightZvar q k m (#(labelRun x m w t)) (runBit x m w v t))]
  -- the sum over the cube of a product over the runs is the product of the runs' two-term sums
  have hcube : ∏ j : Fin (labelRunCount x m w),
        (runWeightZvar q k m (#(labelRun x m w ((j : ℕ) + 1))) false +
          runWeightZvar q k m (#(labelRun x m w ((j : ℕ) + 1))) true)
      = ∑ ε : Fin (labelRunCount x m w) → Bool,
        ∏ j : Fin (labelRunCount x m w),
          runWeightZvar q k m (#(labelRun x m w ((j : ℕ) + 1))) (ε j) := by
    have hbool : ∀ j : Fin (labelRunCount x m w),
        runWeightZvar q k m (#(labelRun x m w ((j : ℕ) + 1))) false +
            runWeightZvar q k m (#(labelRun x m w ((j : ℕ) + 1))) true
          = ∑ b : Bool, runWeightZvar q k m (#(labelRun x m w ((j : ℕ) + 1))) b := fun j => by
      rw [Fintype.sum_bool]
      ring
    rw [Finset.prod_congr rfl (fun j _ => hbool j), Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, hstep, ← Finset.mul_sum, ← hcube]

/-! ### The class sum at an empty support -/

/-- At an empty two-letter support the class is the singleton `{w}`: the condition "agree with `w`
outside the support" is then a condition at every position. -/
private theorem labelClass_eq_singleton (hw : w ∈ noAttackLabellings x σ)
    (hs : labelSupport m w = ∅) : labelClass x σ m w = {w} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨mem_labelClass_self hw, fun _ hw' =>
    funext fun i => hw'.2.2 i (by rw [hs]; exact Finset.notMem_empty _)⟩

/-- **The class sum at an empty two-letter support.** There are then no blocks, so the
product `∏_{t=1}^{r}` is the empty product and the claim is `q^e g` on both sides: the class is the
singleton `{w}`, so the sum is the single weight of `w`; every inversion of `w` has an endpoint off
the support, so the exponent of `q` is the full inversion number; and the monomial of the positions
off the support is all of `z^{(k)}_w`. Together with `HJO.Dyck.finsum_labelClass_full` this covers
`HJO.Dyck.finsum_labelClass_full`. -/
@[hjo "lem_cm_class_sum_full"]
theorem finsum_labelClass_of_labelSupport_eq_empty (q : K) (hw : w ∈ noAttackLabellings x σ)
    (hs : labelSupport m w = ∅) :
    ∑ᶠ w' ∈ labelClass x σ m w,
        scalarSeries K k q ^ invNumber (attackSet x) (wordOfFin w') * zmon K k w'
      = scalarSeries K k q ^ #{p ∈ invSet (attackSet x) (wordOfFin w) |
            ¬(p.1 ∈ labelSupport m w ∧ p.2 ∈ labelSupport m w)} *
          ∏ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) ∉ labelSupport m w),
            zvar K k (w i) := by
  have hinv : {p ∈ invSet (attackSet x) (wordOfFin w) |
      ¬(p.1 ∈ labelSupport m w ∧ p.2 ∈ labelSupport m w)} = invSet (attackSet x) (wordOfFin w) :=
    Finset.filter_true_of_mem fun _ _ h => by
      rw [hs] at h; exact Finset.notMem_empty _ h.1
  have hoff : Finset.univ.filter (fun i : Fin N => (i : ℕ) ∉ labelSupport m w) = Finset.univ :=
    Finset.filter_true_of_mem fun _ _ => by rw [hs]; exact Finset.notMem_empty _
  rw [labelClass_eq_singleton hw hs, finsum_mem_singleton, hinv, hoff, invNumber, zmon]

end HJO.Dyck

