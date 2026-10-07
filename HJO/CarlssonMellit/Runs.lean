/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMBlocks
public import HJO.CarlssonMellit.NoAttack
public import HJO.CarlssonMellit.WordStatistics
public meta import HJO.Attr

/-! # The runs of a two-letter support

Fix a partial Dyck path `π`, a no-attack labelling `w` of it and two consecutive letters `m`,
`m + 1`. The positions carrying one of the two letters form the paper's `S_m(w)`, and the cut set
of that subset for the attack set of `π` breaks the index range `{1, …, p}` of its increasing
listing `s_1 < ⋯ < s_p` into the paper's *runs*. This file proves what the swapping proposition
needs about those runs:

* an attacking pair of indices attacks all the way along;
* indices in different runs do not attack;
* the letters alternate along a run, so a letter of a run is determined by the letter at the run's
  start and the parity of its distance from it;
* only consecutive indices of a run attack;
* the positions below the level form a nonempty initial segment of the first run.

## Main definitions

* `HJO.Sym.sortNth`: `s_a`, the `a`-th smallest element of a finite set, indexed from `1`.
* `HJO.Dyck.wordOfFin`: a labelling of the `N` positions read as a word on all of `ℕ`.
* `HJO.Dyck.labelSupport`: `S_m(w)`, the two-letter support of such a labelling.

## Main results

* `HJO.Sym.mem_of_mem_sortNth`, `HJO.Sym.notMem_of_cutBlock_ne`: the chain lemma and its
  consequence that different runs do not attack.
* `HJO.Dyck.mem_attackSet_of_lt_level`: below the level the attack set is the whole region above
  the diagonal, and `HJO.Dyck.mem_attackSet_level_of_lt`: the instance of that at the level's own
  row, every earlier position attacking the level.
* `HJO.Dyck.wordOfFin_sortNth_ne_succ`, `HJO.Dyck.wordOfFin_sortNth_eq_iff_even`: alternation along
  a run and the parity rule.
* `HJO.Dyck.notMem_attackSet_of_add_two_le`: only consecutive indices of a run attack.
* `HJO.Dyck.exists_initial_segment_lt_level`: the positions below the level are a nonempty initial
  segment of the index range, inside the first run.

## Implementation notes

*Positions are numbered from `0` and run indices from `1`.* The positions of a path are `0`-based
throughout this library, as are letters; the indices `a` of the listing `s_1 < ⋯ < s_p` keep a
`1`-based numbering, because `HJO.Sym.cutSet` and `HJO.Sym.cutBlock` already do — a cut `c`
is the step from the index `c` to the index `c + 1`. `HJO.Sym.sortNth S a` is `s_a`,
and unfolds to `S.sort.getD (a - 1) 0`, which is exactly the spelling `cutSet` uses.

*A labelling is a tuple `Fin N → ℕ`, as `HJO.Dyck.noAttackLabellings` requires, and is fed to the
word statistics through `HJO.Dyck.wordOfFin`.* `HJO.Sym.twoLetterSupport` takes a word on all of `ℕ`
and reads only the window `{0, …, N-1}`, so the value of `wordOfFin w` off the window is irrelevant
to `labelSupport`; it is `0` there, and no lemma below reads it.

*`exists_initial_segment_lt_level` assumes less than the lemma as usually stated.*
That statement hypothesises `σ` to have pairwise distinct entries, and uses distinctness only to
bound the initial segment by `2`, which its own conclusion does not record. The statement below
therefore asks only that some entry of `σ` be `m` or `m + 1`, which is what makes the segment
nonempty, and concludes that the positions below the level form a nonempty initial segment contained
in the first block. The bound is `HJO.Dyck.card_lt_level_le_two`, proved separately from the
injectivity of `σ` where a consumer needs it.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4. -/

@[expose] public section

open Finset

namespace HJO.Sym

open HJO.Dyck

/-! ### The increasing listing of a finite set of positions -/

/-- `s_a`, the `a`-th smallest element of `S`, with the index numbered from `1` as the paper
numbers the elements of a run: `sortNth S a = S.sort.getD (a - 1) 0`. This is the spelling
`HJO.Sym.cutSet` uses, so the cut `c` is the step from `sortNth S c` to `sortNth S (c + 1)`. Outside
`1 ≤ a ≤ #S` the value is the junk `0`. -/
def sortNth (S : Finset ℕ) (a : ℕ) : ℕ := S.sort.getD (a - 1) 0

variable {S : Finset ℕ} {R : Finset (ℕ × ℕ)}

theorem sortNth_mem {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ #S) : sortNth S a ∈ S :=
  Finset.getD_sort_mem S 0 (by omega)

theorem sortNth_lt_sortNth_iff {a b : ℕ} (ha : 1 ≤ a) (ha' : a ≤ #S) (hb : 1 ≤ b) (hb' : b ≤ #S) :
    sortNth S a < sortNth S b ↔ a < b := by
  rw [sortNth, sortNth, Finset.getD_sort_lt_getD_sort_iff S 0 (by omega) (by omega)]
  omega

theorem sortNth_lt_sortNth {a b : ℕ} (ha : 1 ≤ a) (hb' : b ≤ #S) (hab : a < b) :
    sortNth S a < sortNth S b :=
  (sortNth_lt_sortNth_iff ha (by omega) (by omega) hb').2 hab

theorem sortNth_le_sortNth {a b : ℕ} (ha : 1 ≤ a) (hb' : b ≤ #S) (hab : a ≤ b) :
    sortNth S a ≤ sortNth S b := by
  rcases eq_or_lt_of_le hab with rfl | h
  · exact le_rfl
  · exact (sortNth_lt_sortNth ha hb' h).le

theorem sortNth_injOn {a b : ℕ} (ha : 1 ≤ a) (ha' : a ≤ #S) (hb : 1 ≤ b) (hb' : b ≤ #S)
    (h : sortNth S a = sortNth S b) : a = b := by
  by_contra hne
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact absurd h (sortNth_lt_sortNth ha hb' hlt).ne
  · exact absurd h.symm (sortNth_lt_sortNth hb ha' (by omega)).ne

/-- Every element of `S` is one of the `sortNth S a` for `1 ≤ a ≤ #S`: the increasing listing
enumerates `S`. -/
theorem exists_sortNth {i : ℕ} (hi : i ∈ S) : ∃ a, 1 ≤ a ∧ a ≤ #S ∧ sortNth S a = i := by
  have hi' : i ∈ S.sort := (Finset.mem_sort _).2 hi
  obtain ⟨d, hd, hval⟩ := List.getElem_of_mem hi'
  have hdS : d < #S := by rwa [Finset.length_sort] at hd
  refine ⟨d + 1, by omega, by omega, ?_⟩
  rw [sortNth, Nat.add_sub_cancel, List.getD_eq_getElem _ _ hd, hval]

/-- Membership in the cut set, in terms of the increasing listing: the cuts are the indices `c` with
`1 ≤ c < #S` at which `s_c` does not attack `s_{c+1}`. -/
theorem mem_cutSet_iff {c : ℕ} :
    c ∈ cutSet R S ↔ 1 ≤ c ∧ c < #S ∧ (sortNth S c, sortNth S (c + 1)) ∉ R := by
  rw [mem_cutSet, sortNth, sortNth, Nat.add_sub_cancel]

/-- The index at which an element of `S` sits in the increasing listing is bounded by the number of
elements of `S` below a threshold exactly when the element is below the threshold: the small
elements of `S` are an initial segment of its listing. -/
theorem sortNth_lt_iff_le_card_inter_range {k c : ℕ} (hc : 1 ≤ c) (hc' : c ≤ #S) :
    sortNth S c < k ↔ c ≤ #(S ∩ range k) := by
  constructor
  · intro hlt
    have hmap : Set.MapsTo (sortNth S) ↑(Icc 1 c) ↑(S ∩ range k) := fun d hd => by
      simp only [Finset.coe_Icc, Set.mem_Icc] at hd
      simp only [Finset.mem_coe, mem_inter, mem_range]
      exact ⟨sortNth_mem hd.1 (by omega),
        lt_of_le_of_lt (sortNth_le_sortNth hd.1 hc' hd.2) hlt⟩
    have hinj : Set.InjOn (sortNth S) ↑(Icc 1 c) := fun d hd d' hd' h => by
      simp only [Finset.coe_Icc, Set.mem_Icc] at hd hd'
      exact sortNth_injOn hd.1 (by omega) hd'.1 (by omega) h
    have hcard := Finset.card_le_card_of_injOn (sortNth S) hmap hinj
    rw [Nat.card_Icc] at hcard
    omega
  · intro hle
    by_contra hge
    rw [Nat.not_lt] at hge
    have hsub : S ∩ range k ⊆ (Icc 1 (c - 1)).image (sortNth S) := fun i hi => by
      obtain ⟨hiS, hik⟩ := mem_inter.1 hi
      obtain ⟨d, hd1, hdS, rfl⟩ := exists_sortNth hiS
      refine mem_image.2 ⟨d, mem_Icc.2 ⟨hd1, ?_⟩, rfl⟩
      have hlt : sortNth S d < sortNth S c := lt_of_lt_of_le (mem_range.1 hik) hge
      have := (sortNth_lt_sortNth_iff hd1 hdS hc hc').1 hlt
      omega
    have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Nat.card_Icc] at hcard
    omega

/-! ### Attacking pairs along a listing -/

/-- **An attacking pair attacks all the way along.** If `s_a` attacks `s_b` for `a < b`, then each
consecutive pair `s_c`, `s_{c+1}` with `a ≤ c ≤ b-1` attacks: splitting an attacking pair at an
intermediate element of the listing is what a transitive attack set permits. The usual
hypothesis `a < b` is omitted, being implied by `a ≤ c` and `c < b`. -/
@[hjo "lem_cm_attack_chain"]
theorem mem_of_mem_sortNth {n : ℕ} (hR : IsTransitiveAttackSet n R) (S : Finset ℕ) {a b c : ℕ}
    (ha : 1 ≤ a) (hb : b ≤ #S)
    (hmem : (sortNth S a, sortNth S b) ∈ R) (hac : a ≤ c) (hcb : c < b) :
    (sortNth S c, sortNth S (c + 1)) ∈ R := by
  have hmemc : (sortNth S c, sortNth S b) ∈ R := by
    rcases eq_or_lt_of_le hac with rfl | hlt
    · exact hmem
    · exact hR.mem_upper (sortNth_lt_sortNth ha (by omega) hlt)
        (sortNth_lt_sortNth (by omega) hb hcb) hmem
  rcases eq_or_lt_of_le (show c + 1 ≤ b from hcb) with heq | hlt
  · rw [show c + 1 = b from heq]; exact hmemc
  · exact hR.mem_lower (sortNth_lt_sortNth (by omega) (by omega) (Nat.lt_succ_self c))
      (sortNth_lt_sortNth (by omega) hb hlt) hmemc

/-- Two attacking indices lie in the same run: no cut separates them, because every consecutive pair
between them attacks. -/
theorem mem_cutBlock_of_mem_sortNth {n : ℕ} (hR : IsTransitiveAttackSet n R) {a b t : ℕ}
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ #S)
    (hmem : (sortNth S a, sortNth S b) ∈ R) (hat : a ∈ cutBlock #S (cutSet R S) t) :
    b ∈ cutBlock #S (cutSet R S) t := by
  rw [mem_cutBlock] at hat ⊢
  refine ⟨⟨by omega, hb⟩, ?_⟩
  have hempty : cutSet R S ∩ Ico a b = ∅ := by
    refine eq_empty_of_forall_notMem fun c hc => ?_
    obtain ⟨hcC, hcIco⟩ := mem_inter.1 hc
    obtain ⟨hac, hcb⟩ := mem_Ico.1 hcIco
    exact (mem_cutSet_iff.1 hcC).2.2 (mem_of_mem_sortNth hR S ha hb hmem hac hcb)
  have hsplit : cutSet R S ∩ Ico 1 b = cutSet R S ∩ Ico 1 a := by
    rw [show Ico 1 b = Ico 1 a ∪ Ico a b from (Ico_union_Ico_eq_Ico (by omega) hab.le).symm,
      inter_union_distrib_left, hempty, union_empty]
  rw [hsplit]
  exact hat.2

/-- **Different runs do not attack.** If `a < b` lie in different `C(R, S)`-blocks of `{1, …, #S}`
then `s_a` does not attack `s_b`: an attacking pair would force every consecutive pair between them
to attack, hence no cut between them, hence one block. -/
@[hjo "lem_cm_run_cross"]
theorem notMem_of_cutBlock_ne {n : ℕ} (hR : IsTransitiveAttackSet n R) {a b t t' : ℕ}
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ #S)
    (hat : a ∈ cutBlock #S (cutSet R S) t) (hbt' : b ∈ cutBlock #S (cutSet R S) t')
    (htt' : t ≠ t') : (sortNth S a, sortNth S b) ∉ R := fun hmem =>
  htt' (by
    have h := mem_cutBlock_of_mem_sortNth hR ha hab hb hmem hat
    rw [mem_cutBlock] at h hbt'
    omega)

end HJO.Sym

namespace HJO.Dyck

open HJO.Sym

/-! ### The attack set below the level -/

/-- **The attack set below the level.** On a partial Dyck path of level `k`, a row `j < k` — the
one-based `1 ≤ j ≤ k` — attacks exactly the whole region above the diagonal in that row: `(i, j)` is
an attacking pair if and only if `i < j`. The `j`-th entry of the path being minimal, the row's
interval `{x_j, …, j-1}` is all of `{0, …, j-1}`. -/
@[hjo "lem_cm_partial_attack_low"]
theorem mem_attackSet_of_lt_level {k N : ℕ} {x : Fin N → ℕ} (hx : IsPartialDyck k N x) {i j : ℕ}
    (hj : j < k) : (i, j) ∈ attackSet x ↔ i < j := by
  have hjN : j < N := lt_of_lt_of_le hj hx.le_length
  rw [mem_attackSet]
  refine ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hjN, ?_, h⟩⟩
  rw [hx.eq_zero_of_lt_level ⟨j, hjN⟩ hj]
  exact Nat.zero_le i

/-- **Every earlier position attacks the level.** On a partial Dyck path of level `k = m + 1`, every
column `i < m` gives an attacking pair `(i, m)`: the level's own row is the last row the level
constrains, so the whole strip between the path and the main diagonal in that row attacks. This is
the one-based `(i, k) ∈ At(π)` for `1 ≤ i ≤ k - 1`, on rows and columns indexed from `0`, and it is
the row `j = m` of `HJO.Dyck.mem_attackSet_of_lt_level`, the side condition `k ≤ k` of the one-based
statement reading as `m < m + 1`. -/
@[hjo "lem_cm_partial_attack_last"]
theorem mem_attackSet_level_of_lt {m N : ℕ} {x : Fin N → ℕ} (hx : IsPartialDyck (m + 1) N x)
    {i : ℕ} (hi : i < m) : (i, m) ∈ attackSet x :=
  (mem_attackSet_of_lt_level hx (Nat.lt_succ_self m)).2 hi

/-! ### A labelling read as a word, and its two-letter support -/

/-- A labelling of the `N` positions read as a word on all of `ℕ`, so that the word statistics of
`HJO.Sym.WordStatistics` — which take a word on `ℕ` and read only a window — apply to it. The value
off the window is the junk `0`, which `HJO.Dyck.labelSupport` does not read. -/
def wordOfFin {N : ℕ} (w : Fin N → ℕ) : ℕ → ℕ := fun p => if h : p < N then w ⟨p, h⟩ else 0

theorem wordOfFin_of_lt {N : ℕ} (w : Fin N → ℕ) {p : ℕ} (h : p < N) :
    wordOfFin w p = w ⟨p, h⟩ := by
  simp only [wordOfFin, h, ↓reduceDIte]

@[simp]
theorem wordOfFin_val {N : ℕ} (w : Fin N → ℕ) (i : Fin N) : wordOfFin w (i : ℕ) = w i :=
  wordOfFin_of_lt w i.isLt

/-- `S_m(w)`, the paper's set of positions of the labelling `w` carrying one of the two consecutive
letters `m`, `m + 1`: the two-letter support of `HJO.Sym.twoLetterSupport` at the window of the `N`
positions. -/
abbrev labelSupport {N : ℕ} (m : ℕ) (w : Fin N → ℕ) : Finset ℕ :=
  twoLetterSupport N m (m + 1) (wordOfFin w)

theorem mem_labelSupport {N m : ℕ} {w : Fin N → ℕ} {p : ℕ} :
    p ∈ labelSupport m w ↔ p < N ∧ (wordOfFin w p = m ∨ wordOfFin w p = m + 1) :=
  mem_twoLetterSupport

theorem labelSupport_subset_range {N m : ℕ} (w : Fin N → ℕ) : labelSupport m w ⊆ range N :=
  twoLetterSupport_subset_range _ _ _ _

/-- Every position of the two-letter support carries one of the two letters, which is what makes the
alternation along a run a statement about a two-element set. -/
theorem wordOfFin_eq_or_eq_of_mem_labelSupport {N m : ℕ} {w : Fin N → ℕ} {p : ℕ}
    (hp : p ∈ labelSupport m w) : wordOfFin w p = m ∨ wordOfFin w p = m + 1 :=
  (mem_labelSupport.1 hp).2

/-- A position of the two-letter support named by its index in the increasing listing carries one of
the two letters. -/
theorem wordOfFin_sortNth_eq_or_eq {N m : ℕ} {w : Fin N → ℕ} {a : ℕ} (ha : 1 ≤ a)
    (ha' : a ≤ #(labelSupport m w)) :
    wordOfFin w (sortNth (labelSupport m w) a) = m ∨
      wordOfFin w (sortNth (labelSupport m w) a) = m + 1 :=
  wordOfFin_eq_or_eq_of_mem_labelSupport (sortNth_mem ha ha')

/-- Three letters drawn from the two-element set `{m, m+1}`, the first two distinct: the second
agrees with the third exactly when the first does not. This is the whole arithmetic of the parity
rule along a run. -/
private theorem eq_iff_not_eq_of_mem_pair {m u v z : ℕ} (hu : u = m ∨ u = m + 1)
    (hv : v = m ∨ v = m + 1) (hz : z = m ∨ z = m + 1) (huv : u ≠ v) : v = z ↔ ¬(u = z) := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hz with rfl | rfl <;> omega

/-! ### The no-attack condition, read on the word -/

variable {N k : ℕ} {x : Fin N → ℕ} {σ : Fin k → ℕ} {w : Fin N → ℕ}

/-- The no-attack condition of `U(π, σ)`, read on `wordOfFin w`: the two positions of an attacking
pair carry different letters. Both positions of an attacking pair lie in the window, so no junk
value is read. -/
theorem wordOfFin_ne_of_mem_attackSet (hw : w ∈ noAttackLabellings x σ) {p q : ℕ}
    (h : (p, q) ∈ attackSet x) : wordOfFin w p ≠ wordOfFin w q := by
  have hq : q < N := snd_lt_of_mem_attackSet h
  have hp : p < N := lt_trans (fst_lt_snd_of_mem_attackSet h) hq
  rw [wordOfFin_of_lt w hp, wordOfFin_of_lt w hq]
  exact ne_of_mem_noAttackLabellings hw (i := ⟨p, hp⟩) (j := ⟨q, hq⟩) h

/-- The prescription of `U(π, σ)`, read on `wordOfFin w`: below the level the word carries the
letters of `σ`. -/
theorem wordOfFin_eq_of_lt_level (hk : k ≤ N) (hw : w ∈ noAttackLabellings x σ) {p : ℕ}
    (hp : p < k) : wordOfFin w p = σ ⟨p, hp⟩ := by
  rw [wordOfFin_of_lt w (lt_of_lt_of_le hp hk)]
  exact eq_of_mem_noAttackLabellings hw rfl

/-! ### Alternation along a run -/

/-- **The letters alternate along a run.** If the indices `a` and `a + 1` lie in one run — one
`C(At(π), S_m(w))`-block — then the letters at `s_a` and `s_{a+1}` differ: no cut at `a` means
`s_a` attacks `s_{a+1}`, and a no-attack labelling separates an attacking pair. -/
@[hjo "lem_cm_run_alternate"]
theorem wordOfFin_sortNth_ne_succ (hw : w ∈ noAttackLabellings x σ) {m a t : ℕ} (ha : 1 ≤ a)
    (ha' : a < #(labelSupport m w))
    (hat : a ∈ cutBlock #(labelSupport m w) (cutSet (attackSet x) (labelSupport m w)) t)
    (hat' : a + 1 ∈ cutBlock #(labelSupport m w) (cutSet (attackSet x) (labelSupport m w)) t) :
    wordOfFin w (sortNth (labelSupport m w) a) ≠
      wordOfFin w (sortNth (labelSupport m w) (a + 1)) := by
  have hnot := (exists_mem_cutBlock_and_succ_mem_iff_notMem ha ha').1 ⟨t, hat, hat'⟩
  refine wordOfFin_ne_of_mem_attackSet hw ?_
  by_contra hc
  exact hnot (mem_cutSet_iff.2 ⟨ha, ha', hc⟩)

/-- **The letters along a run are determined by parity.** For `a ≤ b` in one run, the letter at
`s_b` is the letter at `s_a` exactly when `b - a` is even: each step along the run flips between the
two letters `m`, `m + 1`, and there is nothing else for the letter to be. -/
@[hjo "lem_cm_run_label"]
theorem wordOfFin_sortNth_eq_iff_even (hw : w ∈ noAttackLabellings x σ) {m a b t : ℕ} (hab : a ≤ b)
    (hat : a ∈ cutBlock #(labelSupport m w) (cutSet (attackSet x) (labelSupport m w)) t)
    (hbt : b ∈ cutBlock #(labelSupport m w) (cutSet (attackSet x) (labelSupport m w)) t) :
    wordOfFin w (sortNth (labelSupport m w) b) = wordOfFin w (sortNth (labelSupport m w) a) ↔
      (b - a) % 2 = 0 := by
  suffices h : ∀ c, a ≤ c →
      c ∈ cutBlock #(labelSupport m w) (cutSet (attackSet x) (labelSupport m w)) t →
      (wordOfFin w (sortNth (labelSupport m w) c) = wordOfFin w (sortNth (labelSupport m w) a) ↔
        (c - a) % 2 = 0) from h b hab hbt
  intro c hac
  induction c, hac using Nat.le_induction with
  | base => intro _; simp
  | succ c hac ih =>
    intro hc1t
    have hct := mem_cutBlock_of_le_of_le hat hc1t hac (Nat.le_succ c)
    have hc1 : 1 ≤ c := (mem_cutBlock.1 hct).1.1
    have hc1S : c + 1 ≤ #(labelSupport m w) := (mem_cutBlock.1 hc1t).1.2
    have hne := wordOfFin_sortNth_ne_succ hw hc1 (by omega) hct hc1t
    have hprev := ih hct
    have h1 := wordOfFin_sortNth_eq_or_eq (m := m) (w := w) hc1 (by omega)
    have h2 := wordOfFin_sortNth_eq_or_eq (m := m) (w := w) (a := c + 1) (by omega) hc1S
    have h3 := wordOfFin_sortNth_eq_or_eq (m := m) (w := w) (a := a)
      (mem_cutBlock.1 hat).1.1 (mem_cutBlock.1 hat).1.2
    rw [show ((c + 1 - a) % 2 = 0) ↔ ¬((c - a) % 2 = 0) from by omega, ← hprev]
    exact eq_iff_not_eq_of_mem_pair h1 h2 h3 hne

/-- **Only consecutive indices of a run attack.** For `a + 2 ≤ b` in one run, `s_a` does not attack
`s_b`: it would then attack `s_{a+2}`, which carries the same letter as `s_a` by the parity rule,
and a no-attack labelling forbids that. -/
@[hjo "lem_cm_run_consecutive"]
theorem notMem_attackSet_of_add_two_le (hx : IsSquareDyck N x) (hw : w ∈ noAttackLabellings x σ)
    {m a b t : ℕ} (hab : a + 2 ≤ b)
    (hat : a ∈ cutBlock #(labelSupport m w) (cutSet (attackSet x) (labelSupport m w)) t)
    (hbt : b ∈ cutBlock #(labelSupport m w) (cutSet (attackSet x) (labelSupport m w)) t) :
    (sortNth (labelSupport m w) a, sortNth (labelSupport m w) b) ∉ attackSet x := by
  intro hmem
  have hR : IsTransitiveAttackSet N (attackSet x) := isTransitiveAttackSet_attackSet hx.mono
  have ha1 : 1 ≤ a := (mem_cutBlock.1 hat).1.1
  have hbS : b ≤ #(labelSupport m w) := (mem_cutBlock.1 hbt).1.2
  have h2t := mem_cutBlock_of_le_of_le hat hbt (Nat.le_add_right a 2) hab
  have hmem2 : (sortNth (labelSupport m w) a, sortNth (labelSupport m w) (a + 2))
      ∈ attackSet x := by
    rcases eq_or_lt_of_le hab with heq | hlt
    · rw [heq]; exact hmem
    · exact hR.mem_lower (sortNth_lt_sortNth ha1 (by omega) (by omega))
        (sortNth_lt_sortNth (by omega) hbS hlt) hmem
  exact wordOfFin_ne_of_mem_attackSet hw hmem2
    ((wordOfFin_sortNth_eq_iff_even hw (Nat.le_add_right a 2) hat h2t).2 (by omega)).symm

/-! ### The positions below the level -/

/-- Every index of the initial segment below the level lies in the first run: below the level every
position attacks every earlier one, so there is no cut below the segment. -/
theorem mem_cutBlock_one_of_sortNth_lt_level {S : Finset ℕ} (hx : IsPartialDyck k N x) {c : ℕ}
    (hc : 1 ≤ c) (hc' : c ≤ #S) (hlt : sortNth S c < k) :
    c ∈ cutBlock #S (cutSet (attackSet x) S) 1 := by
  refine mem_cutBlock.2 ⟨⟨hc, hc'⟩, ?_⟩
  have hempty : cutSet (attackSet x) S ∩ Ico 1 c = ∅ := by
    refine eq_empty_of_forall_notMem fun d hd => ?_
    obtain ⟨hdC, hdIco⟩ := mem_inter.1 hd
    obtain ⟨hd1, hdc⟩ := mem_Ico.1 hdIco
    refine (mem_cutSet_iff.1 hdC).2.2 ?_
    have hd1k : sortNth S (d + 1) < k :=
      lt_of_le_of_lt (sortNth_le_sortNth (by omega) hc' (by omega)) hlt
    exact (mem_attackSet_of_lt_level hx hd1k).2 (sortNth_lt_sortNth hd1 (by omega) (by omega))
  rw [hempty, Finset.card_empty]

/-- **The positions below the level lie in the first run.** For a partial Dyck path of level `k`, a
no-attack labelling `w` and two consecutive letters `m`, `m + 1` one of which occurs among the
entries of `σ`, the indices `c` of the listing of `S_m(w)` with `s_c` below the level form a
nonempty initial segment `{1, …, r}` of `{1, …, #S_m(w)}`, and every index of that segment lies in
the first `C(At(π), S_m(w))`-block. -/
@[hjo "lem_cm_run_first"]
theorem exists_initial_segment_lt_level (hx : IsPartialDyck k N x)
    (hw : w ∈ noAttackLabellings x σ) {m : ℕ} {j₀ : Fin k} (hj₀ : σ j₀ = m ∨ σ j₀ = m + 1) :
    ∃ r, 1 ≤ r ∧ r ≤ #(labelSupport m w) ∧
      (∀ c, 1 ≤ c → c ≤ #(labelSupport m w) → (sortNth (labelSupport m w) c < k ↔ c ≤ r)) ∧
      ∀ c, 1 ≤ c → c ≤ r →
        c ∈ cutBlock #(labelSupport m w) (cutSet (attackSet x) (labelSupport m w)) 1 := by
  have hrle : #(labelSupport m w ∩ range k) ≤ #(labelSupport m w) :=
    Finset.card_le_card inter_subset_left
  have hj₀S : (j₀ : ℕ) ∈ labelSupport m w ∩ range k := by
    refine mem_inter.2 ⟨mem_labelSupport.2 ⟨lt_of_lt_of_le j₀.isLt hx.le_length, ?_⟩,
      mem_range.2 j₀.isLt⟩
    rw [wordOfFin_eq_of_lt_level hx.le_length hw j₀.isLt]
    simpa using hj₀
  refine ⟨#(labelSupport m w ∩ range k), Finset.card_pos.2 ⟨_, hj₀S⟩, hrle,
    fun c hc hc' => sortNth_lt_iff_le_card_inter_range hc hc', fun c hc hcr => ?_⟩
  exact mem_cutBlock_one_of_sortNth_lt_level hx hc (hcr.trans hrle)
    ((sortNth_lt_iff_le_card_inter_range hc (hcr.trans hrle)).2 hcr)

/-- At most two positions of the support lie below the level, the entries of `σ` there being
pairwise distinct and the only admissible ones being `m` and `m + 1`. This is the bound that the
proof by distinctness of `HJO.Dyck.exists_initial_segment_lt_level` derives and its statement does
not record. -/
theorem card_lt_level_le_two (hk : k ≤ N) (hw : w ∈ noAttackLabellings x σ) {m : ℕ}
    (hσ : Function.Injective σ) : #(labelSupport m w ∩ range k) ≤ 2 := by
  have hsub : labelSupport m w ∩ range k ⊆ ({m, m + 1} : Finset ℕ).biUnion
      fun v => {p ∈ range k | wordOfFin w p = v} := fun p hp => by
    obtain ⟨hpS, hpk⟩ := mem_inter.1 hp
    obtain h | h := wordOfFin_eq_or_eq_of_mem_labelSupport hpS
    · exact mem_biUnion.2 ⟨m, by simp, mem_filter.2 ⟨hpk, h⟩⟩
    · exact mem_biUnion.2 ⟨m + 1, by simp, mem_filter.2 ⟨hpk, h⟩⟩
  have hone : ∀ v : ℕ, #{p ∈ range k | wordOfFin w p = v} ≤ 1 := fun v => by
    refine Finset.card_le_one.2 fun p hp p' hp' => ?_
    obtain ⟨hpk, hpv⟩ := mem_filter.1 hp
    obtain ⟨hp'k, hp'v⟩ := mem_filter.1 hp'
    rw [wordOfFin_eq_of_lt_level hk hw (mem_range.1 hpk)] at hpv
    rw [wordOfFin_eq_of_lt_level hk hw (mem_range.1 hp'k)] at hp'v
    simpa using congrArg Fin.val (hσ (hpv.trans hp'v.symm))
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  rw [Finset.sum_pair (by omega : m ≠ m + 1)]
  have := hone m
  have := hone (m + 1)
  omega

end HJO.Dyck
