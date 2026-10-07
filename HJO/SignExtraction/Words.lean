/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Multiset.Sort
public import HJO.SignExtraction.DescentPoly
public meta import HJO.Attr

/-! # The ascending words and their count

The `S`-ascending words of `HJO.Sym.IsAscendingWord` are counted here: a word is recovered from
its exponent vector, so the words of length `n` in the first `m` letters are in bijection with the
exponent vectors of total degree `n` supported there; a word ends above its number of strict
steps, so there is no word at all when the letters are too few; the strict steps can be shifted
away, which reduces the count to the weakly increasing case; and that case is the stars-and-bars
count `C(M + n - 1, n)`. Together these identify the number of bounded words with the value of the
descent polynomial `D_{n, #S}` at the number of letters, which is the fact the sign-extraction
route uses.

The `0`-based conventions of `HJO.Sym.IsAscendingWord` are in force: a word of length `n` is a
tuple `Fin n → ℕ` whose letters are indexed from `0`, so the `1`-based bound `i_n ≤ m` reads
`w k < m` and the `1`-based lower bound `1 ≤ i_1` is vacuous. The `1`-based `i_n ≥ 1 + #S`
correspondingly reads `w (last) ≥ #S`. The descent set stays `1`-based: the step `j ∈ S` is the
step from position `j - 1` to position `j`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### Words and multisets of letters -/

/-- A tuple is monotone as soon as it does not decrease at any single step. -/
theorem monotone_of_le_succ {n : ℕ} {w : Fin n → ℕ}
    (h : ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → w k ≤ w l) : Monotone w := by
  cases n with
  | zero => exact fun a => a.elim0
  | succ N => exact Fin.monotone_iff_le_succ.2 fun i => h _ _ (by simp)

/-- **The letters of a word are the letters of its exponent vector**: the entries of `w`, read as
a multiset, are the letters of `𝐝(w)` with their multiplicities. -/
theorem coe_ofFn_eq_toMultiset : ∀ {n : ℕ} (w : Fin n → ℕ),
    (↑(List.ofFn w) : Multiset ℕ) = Finsupp.toMultiset (wordExponent w) := by
  intro n
  induction n with
  | zero => intro w; simp [wordExponent]
  | succ N ih =>
    intro w
    have h := ih fun k : Fin N => w k.succ
    have hsplit : wordExponent w
        = Finsupp.single (w 0) 1 + wordExponent fun k : Fin N => w k.succ := by
      rw [wordExponent, wordExponent, Fin.sum_univ_succ]
    rw [hsplit, map_add, Finsupp.toMultiset_single, ← h, List.ofFn_succ]
    simp

/-- The entry of the exponent vector of a word at a letter is the multiplicity of that letter
among the entries of the word. -/
theorem count_coe_ofFn {n : ℕ} (w : Fin n → ℕ) (i : ℕ) :
    Multiset.count i (↑(List.ofFn w) : Multiset ℕ) = wordExponent w i := by
  rw [coe_ofFn_eq_toMultiset, Finsupp.count_toMultiset]

/-- A monotone tuple is recovered from its exponent vector: the exponent vector determines the
multiset of entries, and a monotone tuple is the sorted list of that multiset. -/
theorem eq_of_monotone_of_wordExponent_eq {n : ℕ} {w w' : Fin n → ℕ} (hw : Monotone w)
    (hw' : Monotone w') (h : wordExponent w = wordExponent w') : w = w' := by
  refine List.ofFn_injective (List.Perm.eq_of_sortedLE hw.sortedLE_ofFn hw'.sortedLE_ofFn ?_)
  rw [← Multiset.coe_eq_coe, coe_ofFn_eq_toMultiset, coe_ofFn_eq_toMultiset, h]

/-- **A word is recovered from its exponent vector**: two `S`-ascending words of the same length
with the same exponent vector are equal. Only the weak monotonicity of the words is used, the
strict steps playing no role. -/
@[hjo "lem_word_exponent_injective"]
theorem eq_of_wordExponent_eq {n : ℕ} {S : Finset ℕ} {w w' : Fin n → ℕ}
    (hw : IsAscendingWord n S w) (hw' : IsAscendingWord n S w')
    (h : wordExponent w = wordExponent w') : w = w' :=
  eq_of_monotone_of_wordExponent_eq hw.monotone hw'.monotone h

/-! ### The word of an exponent vector -/

/-- The weakly increasing word whose letters are those of the exponent vector `d`: the sorted list
of the multiset of letters of `d`, read as a tuple of length `n`. When `d` has total degree `n`
this inverts `wordExponent` on the weakly increasing words, which is what makes the weakly
increasing words of length `n` in the first `m` letters equinumerous with the exponent vectors of
total degree `n` supported there. -/
noncomputable def wordOfExponent (n : ℕ) (d : ℕ →₀ ℕ) : Fin n → ℕ :=
  fun k => (Multiset.sort (Finsupp.toMultiset d) (· ≤ ·)).getD k 0

section WordOfExponent

variable {n : ℕ} {d : ℕ →₀ ℕ} (hd : Multiset.card (Finsupp.toMultiset d) = n)

include hd

/-- The word of an exponent vector of total degree `n`, read as a list, is the sorted list of the
letters of the vector. -/
theorem ofFn_wordOfExponent :
    List.ofFn (wordOfExponent n d) = Multiset.sort (Finsupp.toMultiset d) (· ≤ ·) := by
  have hlen : (Multiset.sort (Finsupp.toMultiset d) (· ≤ ·)).length = n := by
    rw [Multiset.length_sort, hd]
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  rw [List.getElem_ofFn, wordOfExponent, List.getD_eq_getElem _ _ h2]

/-- The word of an exponent vector is weakly increasing. -/
theorem monotone_wordOfExponent : Monotone (wordOfExponent n d) := by
  rw [← List.sortedLE_ofFn_iff, ofFn_wordOfExponent hd]
  exact List.Pairwise.sortedLE (Multiset.pairwise_sort _ _)

/-- **The word of an exponent vector has that vector as its exponent vector.** -/
theorem wordExponent_wordOfExponent : wordExponent (wordOfExponent n d) = d := by
  ext i
  rw [← count_coe_ofFn, ofFn_wordOfExponent hd, Multiset.sort_eq, Finsupp.count_toMultiset]

/-- Every letter of the word of an exponent vector is a letter of that vector. -/
theorem wordOfExponent_mem_support (k : Fin n) : wordOfExponent n d k ∈ d.support := by
  have h := (mem_support_wordExponent (wordOfExponent n d) (wordOfExponent n d k)).2 ⟨k, rfl⟩
  rwa [wordExponent_wordOfExponent hd] at h

end WordOfExponent

/-- An exponent vector of total degree `n` has `n` letters, counted with multiplicity. -/
theorem card_toMultiset_of_mem_finsuppAntidiag {m n : ℕ} {d : ℕ →₀ ℕ}
    (hd : d ∈ (range m).finsuppAntidiag n) : Multiset.card (Finsupp.toMultiset d) = n := by
  rw [Finsupp.card_toMultiset]
  exact (mem_finsuppAntidiag'.mp hd).1

/-! ### The strict steps of a descent set -/

/-- The number of strict steps a descent set `S` prescribes at or before the `0`-based position
`k`, that is the `1`-based count `s_{k+1} = #{s ∈ S : s < k + 1}`. Shifting a word down by this
count at each position is the bijection that removes the strict steps. -/
def stepCount (S : Finset ℕ) (k : ℕ) : ℕ := #{s ∈ S | s ≤ k}

section StepCount

variable {S : Finset ℕ}

/-- No strict step is prescribed before the first position, the elements of a descent set being
positive. -/
theorem stepCount_eq_zero (hS : ∀ s ∈ S, 1 ≤ s) : stepCount S 0 = 0 := by
  rw [stepCount, card_eq_zero, filter_eq_empty_iff]
  intro s hs
  have := hS s hs
  omega

/-- The step count grows by one across a step of the descent set. -/
theorem stepCount_succ_of_mem {k : ℕ} (h : k + 1 ∈ S) :
    stepCount S (k + 1) = stepCount S k + 1 := by
  have hins : {s ∈ S | s ≤ k + 1} = insert (k + 1) {s ∈ S | s ≤ k} := by
    ext s
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hsS, hsk⟩
      rcases Nat.lt_or_ge s (k + 1) with hlt | hge
      · exact Or.inr ⟨hsS, by omega⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨hsS, hsk⟩)
      · exact ⟨h, le_refl _⟩
      · exact ⟨hsS, by omega⟩
  rw [stepCount, stepCount, hins, card_insert_of_notMem (by simp)]

/-- The step count is unchanged across a step outside the descent set. -/
theorem stepCount_succ_of_notMem {k : ℕ} (h : k + 1 ∉ S) :
    stepCount S (k + 1) = stepCount S k := by
  rw [stepCount, stepCount]
  congr 1
  ext s
  simp only [mem_filter]
  constructor
  · rintro ⟨hsS, hsk⟩
    refine ⟨hsS, ?_⟩
    rcases Nat.lt_or_ge s (k + 1) with hlt | hge
    · omega
    · exact absurd (show s = k + 1 by omega) fun he => h (he ▸ hsS)
  · rintro ⟨hsS, hsk⟩
    exact ⟨hsS, by omega⟩

/-- **A step is where the count grows**: the number of strict steps at or before `k + 1` exceeds
the number at or before `k` exactly when `k + 1` is a step of the descent set. -/
theorem stepCount_lt_stepCount_succ_iff {k : ℕ} :
    stepCount S k < stepCount S (k + 1) ↔ k + 1 ∈ S := by
  by_cases h : k + 1 ∈ S
  · simp [stepCount_succ_of_mem h, h]
  · simp [stepCount_succ_of_notMem h, h]

/-- The count grows across the step from a position `k` into the position `l` after it exactly when
`l` is a step of the descent set. This is `stepCount_lt_stepCount_succ_iff` with the step presented
as an equation between positions, which is the form `IsAscendingWord` states its strict steps in. -/
theorem stepCount_lt_stepCount_iff_of_succ {k l : ℕ} (hkl : k + 1 = l) :
    stepCount S k < stepCount S l ↔ l ∈ S := by
  subst hkl; exact stepCount_lt_stepCount_succ_iff

/-- The step count never exceeds the size of the descent set. -/
theorem stepCount_le_card (k : ℕ) : stepCount S k ≤ #S :=
  card_filter_le _ _

/-- The step count grows with the position. -/
theorem stepCount_mono : Monotone (stepCount S) := fun _ _ hkl =>
  card_le_card fun _ hs =>
    mem_filter.mpr ⟨(mem_filter.mp hs).1, le_trans (mem_filter.mp hs).2 hkl⟩

/-- **At most one step per position**: the count grows by at most `d` across `d` positions, a step
counted at or before `l = k + d` being either counted at or before `k` or one of the `d` members of
`Finset.Ioc k l`. -/
theorem stepCount_le_stepCount_add {k d l : ℕ} (hkl : k + d = l) :
    stepCount S l ≤ stepCount S k + d := by
  have hsub : {s ∈ S | s ≤ l} ⊆ {s ∈ S | s ≤ k} ∪ Ioc k l := fun s hs => by
    simp only [mem_filter, mem_union, mem_Ioc] at hs ⊢
    exact (Nat.lt_or_ge k s).elim (fun h => Or.inr ⟨h, hs.2⟩) fun h => Or.inl ⟨hs.1, h⟩
  rw [stepCount, stepCount]
  refine le_trans (card_le_card hsub) (le_trans (card_union_le _ _) ?_)
  rw [Nat.card_Ioc]
  omega

/-- All the strict steps of a descent set on degree `n + 1` are prescribed by its last
position. -/
theorem stepCount_eq_card {n : ℕ} (hS : S ⊆ Ico 1 (n + 1)) : stepCount S n = #S := by
  rw [stepCount, filter_true_of_mem]
  intro s hs
  have := mem_Ico.mp (hS hs)
  omega

end StepCount

/-! ### A word ends above its number of strict steps -/

/-- Every position of an `S`-ascending word carries a letter at least the number of strict steps
prescribed at or before it: the letters start at `0`, and across one position the count rises by at
most one and only where the letter itself rises strictly. -/
theorem IsAscendingWord.stepCount_le {n : ℕ} {S : Finset ℕ} {w : Fin n → ℕ}
    (hw : IsAscendingWord n S w) (hS : S ⊆ Ico 1 n) :
    ∀ (k : ℕ) (hk : k < n), stepCount S k ≤ w ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [stepCount_eq_zero fun s hs => (mem_Ico.mp (hS hs)).1]
    exact Nat.zero_le _
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    have hle : w ⟨k, hkn⟩ ≤ w ⟨k + 1, hk⟩ := hw.monotone (by simp [Fin.le_def])
    have hlt : stepCount S k < stepCount S (k + 1) → w ⟨k, hkn⟩ < w ⟨k + 1, hk⟩ := fun h =>
      hw.lt_of_mem _ _ rfl (stepCount_lt_stepCount_succ_iff.mp h)
    have hgap : stepCount S (k + 1) ≤ stepCount S k + 1 := stepCount_le_stepCount_add rfl
    have hih := ih hkn
    omega

/-- **A word ends above its number of strict steps**: the last letter of an `S`-ascending word of
length `n + 1` is at least `#S`. The letters being indexed from `0`, this is the `1`-based
bound `i_n ≥ 1 + #S`. -/
@[hjo "lem_word_last_ge"]
theorem IsAscendingWord.card_le_last {n : ℕ} {S : Finset ℕ} {w : Fin (n + 1) → ℕ}
    (hw : IsAscendingWord (n + 1) S w) (hS : S ⊆ Ico 1 (n + 1)) : #S ≤ w (Fin.last n) := by
  have h : stepCount S n ≤ w (Fin.last n) := hw.stepCount_le hS n (by omega)
  rwa [stepCount_eq_card hS] at h

/-- **Too few letters for the strict steps**: there is no `S`-ascending word of length `n + 1` in
`m ≤ #S` letters, since its last letter would be both `< m` and `≥ #S`. -/
@[hjo "lem_bounded_word_empty"]
theorem boundedWords_eq_empty {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Ico 1 (n + 1)) {m : ℕ}
    (hm : m ≤ #S) : boundedWords (n + 1) S m = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro w hw
  rw [mem_boundedWords_succ] at hw
  have := hw.1.card_le_last hS
  omega

/-! ### Counting the words -/

/-- **Counting weakly increasing words**: the weakly increasing words of length `n` in the first
`M` letters are as many as the exponent vectors of total degree `n` supported there, namely
`C(M + n - 1, n)`. The hypothesis `n ≥ 1` is not needed: at `n = 0` both sides are `1`. -/
@[hjo "lem_weak_word_card"]
theorem card_boundedWords_empty (n M : ℕ) :
    #(boundedWords n ∅ M) = (M + n - 1).choose n := by
  have hcard : #((range M).finsuppAntidiag n) = (M + n - 1).choose n := by
    rw [Finset.card_finsuppAntidiag_nat_eq_choose, card_range]
  rw [← hcard]
  refine Finset.card_nbij' wordExponent (wordOfExponent n) ?_ ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_coe, mem_boundedWords] at hw
    exact Finset.mem_coe.mpr (wordExponent_mem_finsuppAntidiag w hw.2)
  · intro d hd
    rw [Finset.mem_coe] at hd
    have hcd := card_toMultiset_of_mem_finsuppAntidiag hd
    refine Finset.mem_coe.mpr (mem_boundedWords.mpr ⟨⟨monotone_wordOfExponent hcd,
      fun k l _ h => absurd h (notMem_empty _)⟩, fun k => ?_⟩)
    exact mem_range.mp ((mem_finsuppAntidiag.mp hd).2 (wordOfExponent_mem_support hcd k))
  · intro w hw
    rw [Finset.mem_coe, mem_boundedWords] at hw
    have hcd : Multiset.card (Finsupp.toMultiset (wordExponent w)) = n :=
      card_toMultiset_of_mem_finsuppAntidiag (wordExponent_mem_finsuppAntidiag w hw.2)
    exact eq_of_monotone_of_wordExponent_eq (monotone_wordOfExponent hcd) hw.1.monotone
      (wordExponent_wordOfExponent hcd)
  · intro d hd
    rw [Finset.mem_coe] at hd
    exact wordExponent_wordOfExponent (card_toMultiset_of_mem_finsuppAntidiag hd)

section Shift

variable {n : ℕ} {S : Finset ℕ}

/-- Shifting an `S`-ascending word down by the step count at each position gives a weakly
increasing word: the shift absorbs exactly the strict steps. -/
theorem isAscendingWord_sub_stepCount {w : Fin n → ℕ} (hw : IsAscendingWord n S w) :
    IsAscendingWord n ∅ (fun k => w k - stepCount S (k : ℕ)) where
  monotone := by
    refine monotone_of_le_succ fun k l hkl => ?_
    show w k - stepCount S (k : ℕ) ≤ w l - stepCount S (l : ℕ)
    have hle : w k ≤ w l := hw.monotone (by rw [Fin.le_def]; omega)
    have hlt : stepCount S (k : ℕ) < stepCount S (l : ℕ) → w k < w l := fun h =>
      hw.lt_of_mem k l hkl ((stepCount_lt_stepCount_iff_of_succ hkl).mp h)
    have hgap : stepCount S (l : ℕ) ≤ stepCount S (k : ℕ) + 1 := stepCount_le_stepCount_add hkl
    omega
  lt_of_mem := fun _ _ _ h => absurd h (notMem_empty _)

/-- Shifting a weakly increasing word up by the step count at each position gives an
`S`-ascending word: the shift creates exactly the strict steps of `S`. -/
theorem isAscendingWord_add_stepCount {v : Fin n → ℕ} (hv : IsAscendingWord n ∅ v) :
    IsAscendingWord n S (fun k => v k + stepCount S (k : ℕ)) where
  monotone := fun k l hkl =>
    Nat.add_le_add (hv.monotone hkl) (stepCount_mono (Fin.le_def.mp hkl))
  lt_of_mem := fun k l hkl hmem =>
    Nat.add_lt_add_of_le_of_lt (hv.monotone (by rw [Fin.le_def]; omega))
      ((stepCount_lt_stepCount_iff_of_succ hkl).mpr hmem)

/-- **Removing the strict steps**: the `S`-ascending words of length `n + 1` in `m` letters are as
many as the weakly increasing words of length `n + 1` in `m - #S` letters, the two being matched by
shifting each position by its step count. -/
@[hjo "lem_word_shift_card"]
theorem card_boundedWords (hS : S ⊆ Ico 1 (n + 1)) {m : ℕ} (hm : #S ≤ m) :
    #(boundedWords (n + 1) S m) = #(boundedWords (n + 1) ∅ (m - #S)) := by
  have hlast : stepCount S n = #S := stepCount_eq_card hS
  refine Finset.card_nbij' (fun w k => w k - stepCount S (k : ℕ))
    (fun v k => v k + stepCount S (k : ℕ)) ?_ ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_coe, mem_boundedWords_succ] at hw
    obtain ⟨hasc0, hlt⟩ := hw
    have hasc := isAscendingWord_sub_stepCount hasc0
    refine Finset.mem_coe.mpr (mem_boundedWords.mpr ⟨hasc, fun k => ?_⟩)
    change w k - stepCount S (k : ℕ) < m - #S
    have hklast : w k - stepCount S (k : ℕ)
        ≤ w (Fin.last n) - stepCount S ((Fin.last n : Fin (n + 1)) : ℕ) :=
      hasc.monotone (Fin.le_last k)
    rw [Fin.val_last, hlast] at hklast
    have h1 : stepCount S n ≤ w (Fin.last n) := hasc0.stepCount_le hS n (by omega)
    rw [hlast] at h1
    omega
  · intro v hv
    rw [Finset.mem_coe, mem_boundedWords] at hv
    refine Finset.mem_coe.mpr (mem_boundedWords.mpr
      ⟨isAscendingWord_add_stepCount hv.1, fun k => ?_⟩)
    change v k + stepCount S (k : ℕ) < m
    have h1 := hv.2 k
    have h2 : stepCount S (k : ℕ) ≤ #S := stepCount_le_card _
    omega
  · intro w hw
    rw [Finset.mem_coe, mem_boundedWords] at hw
    funext k
    change w k - stepCount S (k : ℕ) + stepCount S (k : ℕ) = w k
    have hk : stepCount S (k : ℕ) ≤ w k := hw.1.stepCount_le hS (k : ℕ) k.2
    omega
  · intro v hv
    funext k
    change v k + stepCount S (k : ℕ) - stepCount S (k : ℕ) = v k
    omega

end Shift

/-- **The bounded word count is the descent polynomial**: the number of `S`-ascending words of
length `n + 1` in `m` letters is the value of `D_{n+1, #S}` at `m`, read in `K`. Both cases of the
descent polynomial occur: below `#S` there is no word and the polynomial is at one of its roots,
and from `#S` on the count is the shifted binomial coefficient. -/
@[hjo "lem_bounded_word_card"]
theorem natCast_card_boundedWords (K : Type*) [CommRing K] [Algebra ℚ K] {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Ico 1 (n + 1)) (m : ℕ) :
    (#(boundedWords (n + 1) S m) : K) = (descentPoly K (n + 1) #S).eval (m : K) := by
  have hSn : #S ≤ n := by
    have h := card_le_card hS
    rwa [Nat.card_Ico] at h
  rcases Nat.lt_or_ge m #S with hlt | hge
  · rw [boundedWords_eq_empty hS (le_of_lt hlt), card_empty, Nat.cast_zero]
    have h := eval_descentPoly_intCast_eq_zero K (n + 1) #S (x := (m : ℤ))
      (by omega) (by omega)
    rw [Int.cast_natCast] at h
    exact h.symm
  · rw [card_boundedWords hS hge, card_boundedWords_empty,
      eval_descentPoly_natCast K (n + 1) hge]

end HJO.Sym
