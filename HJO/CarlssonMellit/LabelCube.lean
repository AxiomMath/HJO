/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.LabelClass
public meta import HJO.Attr

/-! # The class of a labelling is a cube

Fix a partial Dyck path `π` of level `k`, a no-attack labelling `w` of it with prescription `σ`, and
two consecutive letters `m`, `m + 1` one of which occurs among the entries of `σ`. The letters of a
member of the class `K_m(π, σ, w)` alternate along each run of the two-letter support, so such a
member is determined by one bit per run — which of the two letters stands at the run's first
position — and the bit of the first run is forced, that position lying below the level where `σ`
prescribes the letter. This file proves that the class is exactly that cube: `w' ↦ ε(w')` is a
bijection from `K_m(π, σ, w)` onto the face of `{0,1}^r` cut out by the value of the first bit.

Surjectivity is the substance. Given a tuple of bits one must *build* the labelling, and from a
position of the support that means recovering its index `c` in the increasing listing
`s_1 < ⋯ < s_p`, then the run `B_t` containing `c`, then that run's least index `a_t`, before the
parity prescription "`w'` carries `m` at `s_c` exactly when `c - a_t + ε_t` is even" can even be
written down; and then the result has to be checked to lie in `U(π, σ)`, which for an attacking pair
of positions splits into three cases against `HJO.Sym.notMem_of_cutBlock_ne` and
`HJO.Dyck.notMem_attackSet_of_add_two_le`.

## Main definitions

* `HJO.Sym.sortIdx`: the index of a position in the increasing listing of a finite set, inverse to
  `HJO.Sym.sortNth`.
* `HJO.Sym.cutBlockIdx`, `HJO.Sym.cutBlockMin`: the index of the block containing an index, and a
  block's least element — the `a_t` above.
* `HJO.Sym.bitLetter`: the letter a tuple of bits prescribes at a listing index.
* `HJO.Dyck.runBit`: `ε(w')_t`, the bit of the `t`-th run.
* `HJO.Dyck.ofRunBits`: the labelling a tuple of bits prescribes — the inverse map.

## Main results

* `HJO.Sym.cutBlock_nonempty`: the blocks indexed `1, …, #C + 1` are all nonempty.
* `HJO.Sym.cutBlock_eq_Icc`: a block is the interval `{a_t, …, a_t + l_t - 1}`.
* `HJO.Dyck.bijOn_runBit`: the class is a cube.

## Implementation notes

*The cube is indexed by `Fin r` and the runs by `1, …, r`.* Run indices follow the notation above
and start at `1`, as `HJO.Sym.cutBlock` requires, while a tuple in `{0,1}^r` is a function on
`Fin r`; the `j`-th bit is therefore the bit of the run `j + 1`, and the forced bit is the one at
`0`. A bit is a `Bool`, as in `HJO.Sym.runWeight`: `false` is the bit `0` and `true` the bit `1`.

*`HJO.Sym.cutBlockMin` is `sInf` of the block, hence noncomputable*, and so are the definitions
built on it. Nothing here is evaluated.

*The hypotheses are weaker than Carlsson and Mellit's.* There `σ` has pairwise distinct entries
and the letters are positive, so `m ≥ 1`; `HJO.Dyck.bijOn_runBit` uses neither. What the argument
needs of `σ` is that one of `m`, `m + 1` occurs among its entries — that is what forces the first
bit, through `HJO.Dyck.exists_initial_segment_lt_level` — and letters are indexed from `0` here, so
the condition `m ≥ 1` is no constraint.

## References

The lemma `HJO.Dyck.bijOn_runBit`, on swapping operators; E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The index of an element in the increasing listing -/

variable {S : Finset ℕ} {i j : ℕ}

/-- The index of the position `i` in the increasing listing `s_1 < ⋯ < s_p` of `S`: the number of
elements of `S` below `i`, plus one, so that `sortNth S (sortIdx S i) = i` for `i ∈ S`. -/
def sortIdx (S : Finset ℕ) (i : ℕ) : ℕ := #(S ∩ range i) + 1

theorem one_le_sortIdx (S : Finset ℕ) (i : ℕ) : 1 ≤ sortIdx S i := Nat.le_add_left 1 _

theorem card_inter_range_succ (hi : i ∈ S) :
    #(S ∩ range (i + 1)) = #(S ∩ range i) + 1 := by
  have he : S ∩ range (i + 1) = insert i (S ∩ range i) := by
    refine Finset.ext fun a => ?_
    simp only [mem_inter, mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨haS, hai⟩
      rcases Nat.lt_or_ge a i with h | h
      · exact Or.inr ⟨haS, h⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨haS, hai⟩)
      · exact ⟨hi, by omega⟩
      · exact ⟨haS, by omega⟩
  rw [he, Finset.card_insert_of_notMem (by simp)]

theorem sortIdx_le_card (hi : i ∈ S) : sortIdx S i ≤ #S := by
  have hsub : S ∩ range i ⊆ S.erase i := fun a ha => by
    obtain ⟨haS, hai⟩ := mem_inter.1 ha
    exact Finset.mem_erase.2 ⟨by simpa using (mem_range.1 hai).ne, haS⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hi] at hcard
  have hpos : 1 ≤ #S := Finset.card_pos.2 ⟨i, hi⟩
  simp only [sortIdx]
  omega

/-- The increasing listing and the index are inverse to each other: the `sortIdx S i`-th smallest
element of `S` is `i`. -/
theorem sortNth_sortIdx (hi : i ∈ S) : sortNth S (sortIdx S i) = i := by
  obtain ⟨c, hc1, hcS, rfl⟩ := exists_sortNth hi
  have h1 : c ≤ #(S ∩ range (sortNth S c + 1)) :=
    (sortNth_lt_iff_le_card_inter_range hc1 hcS).1 (Nat.lt_succ_self _)
  have h2 : ¬ (c ≤ #(S ∩ range (sortNth S c))) := fun h =>
    absurd ((sortNth_lt_iff_le_card_inter_range hc1 hcS).2 h) (lt_irrefl _)
  rw [card_inter_range_succ hi] at h1
  have : c = sortIdx S (sortNth S c) := by rw [sortIdx]; omega
  rw [← this]

theorem sortIdx_sortNth (ha : 1 ≤ i) (ha' : i ≤ #S) : sortIdx S (sortNth S i) = i :=
  sortNth_injOn (one_le_sortIdx _ _) (sortIdx_le_card (sortNth_mem ha ha')) ha ha'
    (sortNth_sortIdx (sortNth_mem ha ha'))

theorem sortIdx_lt_sortIdx (hi : i ∈ S) (hij : i < j) : sortIdx S i < sortIdx S j := by
  have hss : S ∩ range i ⊂ S ∩ range j := by
    refine ⟨fun a ha => ?_, fun h => ?_⟩
    · obtain ⟨haS, hai⟩ := mem_inter.1 ha
      exact mem_inter.2 ⟨haS, mem_range.2 (lt_trans (mem_range.1 hai) hij)⟩
    have : i ∈ S ∩ range i := h (mem_inter.2 ⟨hi, mem_range.2 hij⟩)
    simp at this
  have := Finset.card_lt_card hss
  simp only [sortIdx]
  omega

/-! ### The least element of a block -/

variable {p : ℕ} {C : Finset ℕ} {t a c : ℕ}

/-- The index of the block containing `a`: one more than the number of cuts strictly below `a`. -/
def cutBlockIdx (C : Finset ℕ) (a : ℕ) : ℕ := #(C ∩ Ico 1 a) + 1

theorem one_le_cutBlockIdx (C : Finset ℕ) (a : ℕ) : 1 ≤ cutBlockIdx C a := Nat.le_add_left 1 _

theorem cutBlockIdx_le (C : Finset ℕ) (a : ℕ) : cutBlockIdx C a ≤ #C + 1 := by
  have h : #(C ∩ Ico 1 a) ≤ #C :=
    Finset.card_le_card (fun b hb => (mem_inter.1 hb).1)
  simp only [cutBlockIdx]
  omega

theorem mem_cutBlock_cutBlockIdx (ha : 1 ≤ a) (ha' : a ≤ p) :
    a ∈ cutBlock p C (cutBlockIdx C a) :=
  mem_cutBlock.2 ⟨⟨ha, ha'⟩, rfl⟩

theorem cutBlockIdx_eq_of_mem (h : a ∈ cutBlock p C t) : cutBlockIdx C a = t :=
  (mem_cutBlock.1 h).2

theorem cutBlockIdx_one (C : Finset ℕ) : cutBlockIdx C 1 = 1 := by
  simp [cutBlockIdx]

/-- **Every block index between `1` and `#C + 1` names a nonempty block.** The cut count
`a ↦ #(C ∩ {1, …, a-1}) + 1` is `1` at `a = 1`, is `#C + 1` at `a = p`, and grows by at most one per
step, so it takes every value in between. -/
theorem cutBlock_nonempty (hp : 1 ≤ p) (hC : C ⊆ Ico 1 p) (ht : 1 ≤ t) (ht' : t ≤ #C + 1) :
    (cutBlock p C t).Nonempty := by
  have hstep : ∀ b, 1 ≤ b → cutBlockIdx C (b + 1) ≤ cutBlockIdx C b + 1 := fun b hb => by
    simp only [cutBlockIdx]
    by_cases h : b ∈ C
    · rw [inter_Ico_succ_of_mem hb h, Finset.card_insert_of_notMem (by simp)]
    · rw [inter_Ico_succ_of_notMem hb h]
      omega
  have hlast : cutBlockIdx C p = #C + 1 := by
    rw [cutBlockIdx, Finset.inter_eq_left.2 hC]
  have key : ∀ b, 1 ≤ b → t ≤ cutBlockIdx C b →
      (∀ b', 1 ≤ b' → b' < b → ¬ (t ≤ cutBlockIdx C b')) → cutBlockIdx C b = t := by
    intro b hb1 hbt hmin
    rcases eq_or_lt_of_le hb1 with heq | hlt
    · rw [← heq, cutBlockIdx_one] at hbt ⊢
      omega
    · have h1 := hmin (b - 1) (by omega) (by omega)
      have h2 := hstep (b - 1) (by omega)
      rw [show b - 1 + 1 = b by omega] at h2
      omega
  have hAne : {b ∈ Icc 1 p | t ≤ cutBlockIdx C b}.Nonempty :=
    ⟨p, mem_filter.2 ⟨mem_Icc.2 ⟨hp, le_rfl⟩, by omega⟩⟩
  obtain ⟨hbIcc, hbt⟩ := mem_filter.1 (Finset.min'_mem _ hAne)
  obtain ⟨hb1, hbp⟩ := mem_Icc.1 hbIcc
  refine ⟨_, mem_cutBlock.2 ⟨⟨hb1, hbp⟩, key _ hb1 hbt fun b' hb'1 hb'lt hb't => ?_⟩⟩
  have hb'p : b' ≤ p := le_trans hb'lt.le hbp
  have := Finset.min'_le {b ∈ Icc 1 p | t ≤ cutBlockIdx C b} b'
    (mem_filter.2 ⟨mem_Icc.2 ⟨hb'1, hb'p⟩, hb't⟩)
  omega

/-- The least index of the `t`-th `C`-block of `{1, …, p}`, the `a_t` of the module docstring; the
junk value `0` where the block is empty. -/
noncomputable def cutBlockMin (p : ℕ) (C : Finset ℕ) (t : ℕ) : ℕ :=
  sInf {a : ℕ | a ∈ cutBlock p C t}

theorem cutBlockMin_mem (hne : (cutBlock p C t).Nonempty) :
    cutBlockMin p C t ∈ cutBlock p C t :=
  Nat.sInf_mem (by obtain ⟨a, ha⟩ := hne; exact ⟨a, ha⟩)

theorem cutBlockMin_le (ha : a ∈ cutBlock p C t) : cutBlockMin p C t ≤ a :=
  Nat.sInf_le ha

theorem one_le_cutBlockMin (hne : (cutBlock p C t).Nonempty) : 1 ≤ cutBlockMin p C t :=
  (mem_cutBlock.1 (cutBlockMin_mem hne)).1.1

theorem cutBlockMin_le_card (hne : (cutBlock p C t).Nonempty) : cutBlockMin p C t ≤ p :=
  (mem_cutBlock.1 (cutBlockMin_mem hne)).1.2

theorem cutBlockIdx_cutBlockMin (hne : (cutBlock p C t).Nonempty) :
    cutBlockIdx C (cutBlockMin p C t) = t :=
  cutBlockIdx_eq_of_mem (cutBlockMin_mem hne)

/-- The first block starts at the index `1`. -/
theorem cutBlockMin_one (hp : 1 ≤ p) : cutBlockMin p C 1 = 1 := by
  have hmem : (1 : ℕ) ∈ cutBlock p C 1 := mem_cutBlock.2 ⟨⟨le_rfl, hp⟩, by simp⟩
  have h1 := one_le_cutBlockMin (p := p) (C := C) (t := 1) ⟨1, hmem⟩
  have h2 := cutBlockMin_le (p := p) (C := C) (t := 1) hmem
  omega

/-- **A block is the interval of length its cardinality starting at its least index**:
`B_t = {a_t, …, a_t + l_t - 1}`, where `l_t` is the length of `B_t`. -/
theorem cutBlock_eq_Icc (hne : (cutBlock p C t).Nonempty) :
    cutBlock p C t =
      Icc (cutBlockMin p C t) (cutBlockMin p C t + #(cutBlock p C t) - 1) := by
  have hmax : (cutBlock p C t).max' hne ∈ cutBlock p C t := Finset.max'_mem _ _
  have hIcc : cutBlock p C t = Icc (cutBlockMin p C t) ((cutBlock p C t).max' hne) := by
    refine Finset.ext fun b => ⟨fun hbB => mem_Icc.2 ⟨cutBlockMin_le hbB,
      Finset.le_max' _ _ hbB⟩, fun hb => ?_⟩
    obtain ⟨h1, h2⟩ := mem_Icc.1 hb
    exact mem_cutBlock_of_le_of_le (cutBlockMin_mem hne) hmax h1 h2
  have hle : cutBlockMin p C t ≤ (cutBlock p C t).max' hne := cutBlockMin_le hmax
  have hcard : #(cutBlock p C t) =
      (cutBlock p C t).max' hne + 1 - cutBlockMin p C t := by
    conv_lhs => rw [hIcc]
    rw [Nat.card_Icc]
  conv_lhs => rw [hIcc]
  congr 1
  omega

theorem mem_cutBlock_iff_between (hne : (cutBlock p C t).Nonempty) :
    c ∈ cutBlock p C t ↔
      cutBlockMin p C t ≤ c ∧ c ≤ cutBlockMin p C t + #(cutBlock p C t) - 1 := by
  conv_lhs => rw [cutBlock_eq_Icc hne]
  rw [mem_Icc]

theorem one_le_card_cutBlock (hne : (cutBlock p C t).Nonempty) : 1 ≤ #(cutBlock p C t) :=
  Finset.card_pos.2 hne

/-! ### The letter prescribed by a tuple of bits -/

/-- The letter prescribed at the listing index `c` by the tuple of bits `ε`: it is `m` when the
distance from `c` to the start of its block agrees in parity with the bit of that block, and
`m + 1` otherwise. -/
noncomputable def bitLetter (p : ℕ) (C : Finset ℕ) (m : ℕ) (ε : ℕ → Bool) (c : ℕ) : ℕ :=
  if (c - cutBlockMin p C (cutBlockIdx C c) + (if ε (cutBlockIdx C c) then 1 else 0)) % 2 = 0
    then m else m + 1

theorem bitLetter_eq_or (p : ℕ) (C : Finset ℕ) (m : ℕ) (ε : ℕ → Bool) (c : ℕ) :
    bitLetter p C m ε c = m ∨ bitLetter p C m ε c = m + 1 := by
  rw [bitLetter]
  by_cases h : (c - cutBlockMin p C (cutBlockIdx C c) +
      (if ε (cutBlockIdx C c) then 1 else 0)) % 2 = 0
  · exact Or.inl (by simp [h])
  · exact Or.inr (by simp [h])

theorem bitLetter_eq_iff_of_mem {m : ℕ} {ε : ℕ → Bool} (hct : c ∈ cutBlock p C t) :
    bitLetter p C m ε c = m ↔
      (c - cutBlockMin p C t + (if ε t then 1 else 0)) % 2 = 0 := by
  rw [bitLetter, cutBlockIdx_eq_of_mem hct]
  by_cases h : (c - cutBlockMin p C t + (if ε t then 1 else 0)) % 2 = 0 <;> simp [h]

/-- At the start of a block the prescribed letter is `m` exactly when the block's bit is `0`. -/
theorem bitLetter_cutBlockMin {m : ℕ} {ε : ℕ → Bool} (hne : (cutBlock p C t).Nonempty) :
    bitLetter p C m ε (cutBlockMin p C t) = m ↔ ε t = false := by
  rw [bitLetter_eq_iff_of_mem (cutBlockMin_mem hne), Nat.sub_self]
  cases h : ε t <;> simp_all

/-- **Consecutive indices of one block get different letters**, which is the no-attack condition
along a run: the two distances from the start of the block differ in parity. -/
theorem bitLetter_ne_succ {m : ℕ} {ε : ℕ → Bool} (hct : c ∈ cutBlock p C t)
    (hc1t : c + 1 ∈ cutBlock p C t) :
    bitLetter p C m ε c ≠ bitLetter p C m ε (c + 1) := by
  have hle : cutBlockMin p C t ≤ c := cutBlockMin_le hct
  rw [bitLetter, bitLetter, cutBlockIdx_eq_of_mem hct, cutBlockIdx_eq_of_mem hc1t]
  split_ifs <;> omega

end HJO.Sym

namespace HJO.Dyck

open HJO.Sym

variable {N k : ℕ} {x : Fin N → ℕ} {σ : Fin k → ℕ} {m : ℕ} {w w' : Fin N → ℕ}

/-! ### Three arithmetic facts about a two-element set of letters -/

/-- Two letters of `{m, m+1}` that are `m` together are equal. -/
private theorem eq_of_mem_pair_iff {m u v : ℕ} (hu : u = m ∨ u = m + 1) (hv : v = m ∨ v = m + 1)
    (h : u = m ↔ v = m) : u = v := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all

/-- Two letters of `{m, m+1}` that answer the test "is it `m + 1`?" alike are equal. -/
private theorem eq_of_decide_succ {m u v : ℕ} (hu : u = m ∨ u = m + 1) (hv : v = m ∨ v = m + 1)
    (h : decide (u = m + 1) = decide (v = m + 1)) : u = v := by
  rw [decide_eq_decide] at h
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all

/-- Two letters of `{m, m+1}` are equal when each agrees with a common reference letter under the
same condition: this is how the parity rule along a run determines a letter from the letter at the
run's start. -/
private theorem eq_of_pair_of_iff {P : Prop} {m u v ua va : ℕ} (hu : u = m ∨ u = m + 1)
    (hv : v = m ∨ v = m + 1) (hua : ua = m ∨ ua = m + 1) (hab : ua = va)
    (h1 : u = ua ↔ P) (h2 : v = va ↔ P) : u = v := by
  by_cases hP : P
  · rw [h1.2 hP, h2.2 hP, hab]
  · have hu' : u ≠ ua := fun h => hP (h1.1 h)
    have hv' : v ≠ va := fun h => hP (h2.1 h)
    subst hab
    rcases hua with rfl | rfl <;> rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> omega

/-- The parity prescription at the first run reproduces the reference letter: `e` is the bit of the
first run, read off the reference letter `u₁` at the first position, and `u` is the reference letter
at the index `c`. -/
private theorem parity_iff_of_first {m u u₁ c e : ℕ} (hu : u = m ∨ u = m + 1)
    (hu₁ : u₁ = m ∨ u₁ = m + 1) (he : u₁ = m + 1 → e = 1) (he' : u₁ = m → e = 0)
    (huiff : u = u₁ ↔ (c - 1) % 2 = 0) : (c - 1 + e) % 2 = 0 ↔ u = m := by
  rcases hu₁ with h1 | h1
  · rw [he' h1, Nat.add_zero, ← huiff, h1]
  · rw [he h1]
    rcases hu with h | h
    · rw [h]
      have hne : u ≠ u₁ := by rw [h, h1]; omega
      have hpar : ¬ ((c - 1) % 2 = 0) := fun hh => hne (huiff.2 hh)
      constructor <;> intro hh <;> omega
    · rw [h]
      have heq : u = u₁ := by rw [h, h1]
      have hpar : (c - 1) % 2 = 0 := huiff.1 heq
      constructor <;> intro hh <;> omega

/-! ### The runs of a labelling -/

/-- `C(At(π), S_m(w))`, the cut set whose blocks are the runs of `w`. -/
abbrev labelCutSet (x : Fin N → ℕ) (m : ℕ) (w : Fin N → ℕ) : Finset ℕ :=
  cutSet (attackSet x) (labelSupport m w)

/-- `B_t`, the `t`-th run of `w`: the `t`-th block of the index range `{1, …, p}` of the increasing
listing of `S_m(w)`. -/
abbrev labelRun (x : Fin N → ℕ) (m : ℕ) (w : Fin N → ℕ) (t : ℕ) : Finset ℕ :=
  cutBlock #(labelSupport m w) (labelCutSet x m w) t

/-- `r`, the number of runs of `w`: one more than the number of cuts. -/
abbrev labelRunCount (x : Fin N → ℕ) (m : ℕ) (w : Fin N → ℕ) : ℕ := #(labelCutSet x m w) + 1

/-! ### The bits of a labelling, and the labelling a tuple of bits prescribes -/

/-- **The bit of the run `t`**, `ε(w')_t`: `false` when the letter of `w'` at the first
position of the run is `m` and `true` when it is `m + 1`. The runs are those of the reference
labelling `w`, whose two-letter support every member of its class shares. -/
noncomputable def runBit (x : Fin N → ℕ) (m : ℕ) (w w' : Fin N → ℕ) (t : ℕ) : Bool :=
  decide (wordOfFin w' (sortNth (labelSupport m w)
    (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)) = m + 1)

/-- **The labelling prescribed by a tuple of bits**: off the two-letter support of `w` it is `w`,
and at the position of listing index `c` it is the letter `HJO.Sym.bitLetter` prescribes — `m`
exactly when the distance of `c` from the start of its run agrees in parity with that run's bit. -/
noncomputable def ofRunBits (x : Fin N → ℕ) (m : ℕ) (w : Fin N → ℕ) (ε : ℕ → Bool)
    (i : Fin N) : ℕ :=
  if (i : ℕ) ∈ labelSupport m w then
    bitLetter #(labelSupport m w) (labelCutSet x m w) m ε (sortIdx (labelSupport m w) (i : ℕ))
  else w i

theorem ofRunBits_of_mem {ε : ℕ → Bool} {i : Fin N} (hi : (i : ℕ) ∈ labelSupport m w) :
    ofRunBits x m w ε i =
      bitLetter #(labelSupport m w) (labelCutSet x m w) m ε
        (sortIdx (labelSupport m w) (i : ℕ)) := by
  simp only [ofRunBits, hi, ite_true]

theorem ofRunBits_of_notMem {ε : ℕ → Bool} {i : Fin N} (hi : (i : ℕ) ∉ labelSupport m w) :
    ofRunBits x m w ε i = w i := by
  simp only [ofRunBits, hi, ite_false]

theorem wordOfFin_ofRunBits_of_mem {ε : ℕ → Bool} {q : ℕ} (hq : q ∈ labelSupport m w) :
    wordOfFin (ofRunBits x m w ε) q =
      bitLetter #(labelSupport m w) (labelCutSet x m w) m ε (sortIdx (labelSupport m w) q) := by
  have hqN : q < N := mem_range.1 (labelSupport_subset_range w hq)
  rw [wordOfFin_of_lt _ hqN, ofRunBits_of_mem (i := (⟨q, hqN⟩ : Fin N)) hq]

theorem wordOfFin_ofRunBits_of_notMem {ε : ℕ → Bool} {q : ℕ} (hq : q ∉ labelSupport m w) :
    wordOfFin (ofRunBits x m w ε) q = wordOfFin w q := by
  by_cases hqN : q < N
  · rw [wordOfFin_of_lt _ hqN, wordOfFin_of_lt _ hqN,
      ofRunBits_of_notMem (i := (⟨q, hqN⟩ : Fin N)) hq]
  · simp [wordOfFin, hqN]

/-! ### What a member of the class inherits from the reference labelling -/

/-- The parity rule along a run, for a member of the class: the runs and the listing are those of
the reference labelling, whose support the member shares. -/
theorem wordOfFin_sortNth_eq_iff_even_of_mem_labelClass (hw' : w' ∈ labelClass x σ m w)
    {a b t : ℕ} (hab : a ≤ b) (hat : a ∈ labelRun x m w t) (hbt : b ∈ labelRun x m w t) :
    wordOfFin w' (sortNth (labelSupport m w) b) = wordOfFin w' (sortNth (labelSupport m w) a) ↔
      (b - a) % 2 = 0 := by
  have hS : labelSupport m w' = labelSupport m w := hw'.2.1
  simp only [labelRun, labelCutSet] at hat hbt
  rw [← hS] at hat hbt ⊢
  exact wordOfFin_sortNth_eq_iff_even hw'.1 hab hat hbt

/-- Every position of the common support carries one of the two letters, for a member of the
class. -/
theorem wordOfFin_mem_pair_of_mem_labelClass (hw' : w' ∈ labelClass x σ m w) {q : ℕ}
    (hq : q ∈ labelSupport m w) : wordOfFin w' q = m ∨ wordOfFin w' q = m + 1 :=
  wordOfFin_eq_or_eq_of_mem_labelSupport (hw'.2.1.symm ▸ hq)

/-- Below the level a member of the class carries the letters of the reference labelling, both
being prescribed by `σ` there. -/
theorem wordOfFin_eq_of_lt_level_of_mem_labelClass (hx : IsPartialDyck k N x)
    (hw : w ∈ noAttackLabellings x σ) (hw' : w' ∈ labelClass x σ m w) {q : ℕ} (hq : q < k) :
    wordOfFin w' q = wordOfFin w q := by
  rw [wordOfFin_eq_of_lt_level hx.le_length hw'.1 hq, wordOfFin_eq_of_lt_level hx.le_length hw hq]

/-- The support is nonempty when one of the two letters is prescribed. -/
theorem one_le_card_labelSupport (hx : IsPartialDyck k N x) (hw : w ∈ noAttackLabellings x σ)
    {j₀ : Fin k} (hj₀ : σ j₀ = m ∨ σ j₀ = m + 1) : 1 ≤ #(labelSupport m w) := by
  obtain ⟨r₀, hr₀1, hr₀le, -, -⟩ := exists_initial_segment_lt_level hx hw hj₀
  omega

/-- The first position of the support lies below the level. -/
theorem sortNth_one_lt_level (hx : IsPartialDyck k N x) (hw : w ∈ noAttackLabellings x σ)
    {j₀ : Fin k} (hj₀ : σ j₀ = m ∨ σ j₀ = m + 1) : sortNth (labelSupport m w) 1 < k := by
  obtain ⟨r₀, hr₀1, hr₀le, hiff, -⟩ := exists_initial_segment_lt_level hx hw hj₀
  exact (hiff 1 le_rfl (by omega)).2 hr₀1


/-! ### The class is a cube -/

/-- **The class of a labelling is a cube.** Let `π` be a partial Dyck path of level `k`, let `w` be
a no-attack labelling of it with prescription `σ`, and suppose one of the two consecutive letters
`m`, `m + 1` occurs among the entries of `σ`. Write `S_m(w) = {s_1 < ⋯ < s_p}` for the two-letter
support and let `B_1, …, B_r` be its runs, `a_t` the least index of `B_t`. Then `w' ↦ ε(w')`, the
tuple of bits recording for each run whether `w'` starts it with `m` or with `m + 1`, is a bijection
from the class `K_m(π, σ, w)` onto the face of the cube `{0,1}^r` on which the first bit is the one
`w` itself has.

The inverse is `HJO.Dyck.ofRunBits`: from a position of the support one recovers its listing index,
then the run containing that index, then the run's least index, and the parity prescription then
names the letter. -/
@[hjo "lem_cm_class_cube"]
theorem bijOn_runBit (hx : IsPartialDyck k N x) (hw : w ∈ noAttackLabellings x σ)
    {j₀ : Fin k} (hj₀ : σ j₀ = m ∨ σ j₀ = m + 1) :
    Set.BijOn (fun w' (j : Fin (labelRunCount x m w)) => runBit x m w w' ((j : ℕ) + 1))
      (labelClass x σ m w)
      {ε | ε 0 = decide (wordOfFin w (sortNth (labelSupport m w) 1) = m + 1)} := by
  have hp : 1 ≤ #(labelSupport m w) := one_le_card_labelSupport hx hw hj₀
  have hCsub : labelCutSet x m w ⊆ Ico 1 #(labelSupport m w) := cutSet_subset_Ico _ _
  have hne : ∀ t, 1 ≤ t → t ≤ labelRunCount x m w → (labelRun x m w t).Nonempty :=
    fun t ht ht' => cutBlock_nonempty hp hCsub ht ht'
  have hmin1 : cutBlockMin #(labelSupport m w) (labelCutSet x m w) 1 = 1 := cutBlockMin_one hp
  have hs1k : sortNth (labelSupport m w) 1 < k := sortNth_one_lt_level hx hw hj₀
  have hR : IsTransitiveAttackSet N (attackSet x) := isTransitiveAttackSet_attackSet hx.mono
  have h1blk : (1 : ℕ) ∈ labelRun x m w 1 := mem_cutBlock.2 ⟨⟨le_rfl, hp⟩, by simp⟩
  have h1memS : sortNth (labelSupport m w) 1 ∈ labelSupport m w := sortNth_mem le_rfl hp
  have hbit1 : ∀ v : Fin N → ℕ, runBit x m w v 1 =
      decide (wordOfFin v (sortNth (labelSupport m w) 1) = m + 1) := fun v => by
    rw [runBit, hmin1]
  refine ⟨?_, ?_, ?_⟩
  · -- the first bit of a member of the class is the first bit of the reference labelling
    intro v hv
    simp only [Set.mem_ofPred_eq, Fin.val_zero, Nat.zero_add, hbit1]
    rw [wordOfFin_eq_of_lt_level_of_mem_labelClass hx hw hv hs1k]
  · -- a member of the class is determined by its bits
    intro v₁ hv₁ v₂ hv₂ hbits
    have hbit : ∀ t, 1 ≤ t → t ≤ labelRunCount x m w →
        runBit x m w v₁ t = runBit x m w v₂ t := fun t ht ht' => by
      have h := congrFun hbits (⟨t - 1, by omega⟩ : Fin (labelRunCount x m w))
      simpa [show t - 1 + 1 = t by omega] using h
    funext i
    by_cases hi : (i : ℕ) ∈ labelSupport m w
    · have hc1 : 1 ≤ sortIdx (labelSupport m w) (i : ℕ) := one_le_sortIdx _ _
      have hcp : sortIdx (labelSupport m w) (i : ℕ) ≤ #(labelSupport m w) := sortIdx_le_card hi
      have hsc : sortNth (labelSupport m w) (sortIdx (labelSupport m w) (i : ℕ)) = (i : ℕ) :=
        sortNth_sortIdx hi
      have hct : sortIdx (labelSupport m w) (i : ℕ) ∈
          labelRun x m w (cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) (i : ℕ))) :=
        mem_cutBlock_cutBlockIdx hc1 hcp
      have hbne : (labelRun x m w
          (cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) (i : ℕ)))).Nonempty :=
        ⟨_, hct⟩
      have hamem := cutBlockMin_mem hbne
      have hale := cutBlockMin_le hct
      have hamemS : sortNth (labelSupport m w)
          (cutBlockMin #(labelSupport m w) (labelCutSet x m w)
            (cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) (i : ℕ))))
          ∈ labelSupport m w :=
        sortNth_mem (one_le_cutBlockMin hbne) (cutBlockMin_le_card hbne)
      have hb := hbit (cutBlockIdx (labelCutSet x m w) (sortIdx (labelSupport m w) (i : ℕ)))
        (one_le_cutBlockIdx _ _) (cutBlockIdx_le _ _)
      rw [runBit, runBit] at hb
      have hstart := eq_of_decide_succ (wordOfFin_mem_pair_of_mem_labelClass hv₁ hamemS)
        (wordOfFin_mem_pair_of_mem_labelClass hv₂ hamemS) hb
      have hval := eq_of_pair_of_iff
        (wordOfFin_mem_pair_of_mem_labelClass hv₁ (by rw [hsc]; exact hi))
        (wordOfFin_mem_pair_of_mem_labelClass hv₂ (by rw [hsc]; exact hi))
        (wordOfFin_mem_pair_of_mem_labelClass hv₁ hamemS) hstart
        (wordOfFin_sortNth_eq_iff_even_of_mem_labelClass hv₁ hale hamem hct)
        (wordOfFin_sortNth_eq_iff_even_of_mem_labelClass hv₂ hale hamem hct)
      rw [hsc, wordOfFin_val, wordOfFin_val] at hval
      exact hval
    · rw [hv₁.2.2 i hi, hv₂.2.2 i hi]
  · -- every point of the face is the tuple of bits of a member of the class
    intro ε' hε'
    obtain ⟨ε, hεj⟩ : ∃ ε : ℕ → Bool, ∀ j : Fin (labelRunCount x m w),
        ε ((j : ℕ) + 1) = ε' j := by
      refine ⟨fun t => ε' ⟨(t - 1) % labelRunCount x m w, Nat.mod_lt _ (Nat.succ_pos _)⟩,
        fun j => ?_⟩
      exact congrArg ε' (Fin.ext (by rw [Nat.add_sub_cancel]; exact Nat.mod_eq_of_lt j.isLt))
    have hε1 : ε 1 = decide (wordOfFin w (sortNth (labelSupport m w) 1) = m + 1) := by
      have h := hεj 0
      rw [Fin.val_zero, Nat.zero_add] at h
      rw [h]
      exact hε'
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
    have hpresw : ∀ i : Fin N, (i : ℕ) < k → ofRunBits x m w ε i = w i := by
      intro i hik
      by_cases hi : (i : ℕ) ∈ labelSupport m w
      · have hc1 : 1 ≤ sortIdx (labelSupport m w) (i : ℕ) := one_le_sortIdx _ _
        have hcp : sortIdx (labelSupport m w) (i : ℕ) ≤ #(labelSupport m w) := sortIdx_le_card hi
        have hsc : sortNth (labelSupport m w) (sortIdx (labelSupport m w) (i : ℕ)) = (i : ℕ) :=
          sortNth_sortIdx hi
        have hcblk : sortIdx (labelSupport m w) (i : ℕ) ∈ labelRun x m w 1 :=
          mem_cutBlock_one_of_sortNth_lt_level hx hc1 hcp (by rw [hsc]; exact hik)
        have hwi : w i =
            wordOfFin w (sortNth (labelSupport m w) (sortIdx (labelSupport m w) (i : ℕ))) := by
          rw [hsc, wordOfFin_val]
        rw [ofRunBits_of_mem hi, hwi]
        refine eq_of_mem_pair_iff (bitLetter_eq_or _ _ _ _ _)
          (wordOfFin_eq_or_eq_of_mem_labelSupport (by rw [hsc]; exact hi)) ?_
        rw [bitLetter_eq_iff_of_mem hcblk, hmin1]
        refine parity_iff_of_first
          (wordOfFin_eq_or_eq_of_mem_labelSupport (by rw [hsc]; exact hi))
          (wordOfFin_eq_or_eq_of_mem_labelSupport h1memS) ?_ ?_
          (wordOfFin_sortNth_eq_iff_even hw hc1 h1blk hcblk)
        · intro h; rw [hε1, h]; simp
        · intro h; rw [hε1, h]; simp
      · exact ofRunBits_of_notMem hi
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
    refine ⟨ofRunBits x m w ε, ⟨⟨fun i j hij => ?_, hnoattack⟩, hsupp,
      fun i hi => ofRunBits_of_notMem hi⟩, ?_⟩
    · rw [hpresw i (by rw [hij]; exact j.isLt)]
      exact eq_of_mem_noAttackLabellings hw hij
    · funext j
      have hjlt : (j : ℕ) < labelRunCount x m w := j.isLt
      have hbne := hne ((j : ℕ) + 1) (by omega) (by omega)
      have hamemS : sortNth (labelSupport m w)
          (cutBlockMin #(labelSupport m w) (labelCutSet x m w) ((j : ℕ) + 1))
          ∈ labelSupport m w :=
        sortNth_mem (one_le_cutBlockMin hbne) (cutBlockMin_le_card hbne)
      change runBit x m w (ofRunBits x m w ε) ((j : ℕ) + 1) = ε' j
      rw [runBit, wordOfFin_ofRunBits_of_mem hamemS,
        sortIdx_sortNth (one_le_cutBlockMin hbne) (cutBlockMin_le_card hbne), ← hεj j]
      have hiff := bitLetter_cutBlockMin (m := m) (ε := ε) hbne
      rcases bitLetter_eq_or #(labelSupport m w) (labelCutSet x m w) m ε
        (cutBlockMin #(labelSupport m w) (labelCutSet x m w) ((j : ℕ) + 1)) with h | h
      · rw [h, hiff.1 h]; simp
      · have hεt : ε ((j : ℕ) + 1) = true := by
          rcases Bool.eq_false_or_eq_true (ε ((j : ℕ) + 1)) with hb | hb
          · exact hb
          · have := hiff.2 hb; omega
        rw [h, hεt]; simp

end HJO.Dyck
