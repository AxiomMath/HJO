/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Interval.Finset.Nat
public meta import HJO.Attr

/-! # The blocks cut out of an interval, and adjacency inside one block

A set of cuts `C ⊆ {1, …, p-1}` breaks the interval `{1, …, p}` into consecutive pieces: listing
`C` as `c_1 < ⋯ < c_{r-1}` and putting `c_0 := 0`, `c_r := p`, the `C`-blocks of `{1, …, p}` are
the `r` intervals `B_t = {c_{t-1}+1, …, c_t}`, one more than there are cuts. For a cut set
`C = C(R, S)` coming from an attack set `R` and an enumerated subset `S = {s_1 < ⋯ < s_p}` this is
the decomposition of the index range into *runs*.

The blocks are given here as the fibres of the cut-counting function `a ↦ #(C ∩ {1, …, a-1}) + 1`,
which is what makes disjointness and "`a` and `b` lie in one block" immediate; it is the interval
form that then costs a lemma, and the three lemmas below are that cost. The first says that
adjacency inside a common block is the complement of the cut set, index by index — the
defining property of a run, that consecutive elements of a run attack each other. The second says
that a block is an interval: it contains every index lying between two of its own, the cut count
being monotone. The third reads the two together: a block, being an interval, contains no cut
strictly inside it.

## Main definitions

* `HJO.Sym.cutBlock`: the `t`-th `C`-block of `{1, …, p}`, as a `Finset ℕ`.

## Main results

* `HJO.Sym.exists_mem_cutBlock_and_succ_mem_iff_notMem`: for `1 ≤ a` and `a < p`, the indices `a`
  and `a + 1` lie in a common `C`-block of `{1, …, p}` if and only if `a ∉ C`.
* `HJO.Sym.mem_cutBlock_of_le_of_le`: a `C`-block of `{1, …, p}` is an interval — it contains
  every index lying between two of its own.
* `HJO.Sym.disjoint_Ico_of_mem_cutBlock`: if `a` and `b` lie in one `C`-block then `C` meets no
  index of `Finset.Ico a b`.

## Implementation notes

The index `t` follows the usual numbering and runs from `1`: `cutBlock p C 1` is `B_1`, the block of
`1`, and the blocks are the `cutBlock p C t` for `1 ≤ t ≤ #C + 1`. Outside that range the value is
the junk value `∅`, at `t = 0` because a count plus one is never `0`, and for `t > #C + 1` because
`C` has at most `#C` elements below anything.

`mem_cutBlock` is the only unfolding any proof here needs: membership in a block is a pair of
numerical facts, and the two lemmas that carry content are then arithmetic about the count
`#(C ∩ Finset.Ico 1 a)` — stepping it by one in `a`, which is the two `inter_Ico_succ_of_*` lemmas
and gives adjacency, and bounding it monotonically, which gives the interval form.
`disjoint_Ico_of_mem_cutBlock` reaches the count not at all: an interval containing `c` and `c + 1`
is not cut at `c`.

The range `1 ≤ a ≤ p - 1` in `exists_mem_cutBlock_and_succ_mem_iff_notMem` is written `1 ≤ a`
together with `a < p`, truncated subtraction in `ℕ` making `a ≤ p - 1` the wrong hypothesis at
`p = 0`; the condition `p ≥ 1` is then automatic. The hypothesis `a < b` one might expect in
`disjoint_Ico_of_mem_cutBlock` is not needed: for `b ≤ a` the window `Finset.Ico a b` is empty, so
the conclusion is vacuous there rather than false.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-- The `t`-th `C`-block of `{1, …, p}`: the set of `a ∈ {1, …, p}` having exactly `t - 1` cuts of
`C` strictly below them. For a cut set `C ⊆ {1, …, p-1}` listed as `c_1 < ⋯ < c_{r-1}`, with
`c_0 = 0` and `c_r = p`, this is the interval `B_t = {c_{t-1}+1, …, c_t}`; the blocks are
the values at `1 ≤ t ≤ #C + 1`, `cutBlock p C 1` is the block containing `1`, and the value is `∅`
for every other `t`. -/
@[hjo "def_cm_blocks"]
def cutBlock (p : ℕ) (C : Finset ℕ) (t : ℕ) : Finset ℕ :=
  {a ∈ Icc 1 p | #(C ∩ Ico 1 a) + 1 = t}

/-- Membership in a block is a pair of numerical facts: `a` lies in `{1, …, p}` and the number of
cuts below `a` is `t - 1`. -/
theorem mem_cutBlock {p C t a} :
    a ∈ cutBlock p C t ↔ (1 ≤ a ∧ a ≤ p) ∧ #(C ∩ Ico 1 a) + 1 = t := by
  simp [cutBlock, and_assoc]

/-- Extending the window by a cut adds that cut: the cuts below `a + 1` are the cuts below `a`
together with `a` itself, when `a` is one. -/
theorem inter_Ico_succ_of_mem {C : Finset ℕ} {a : ℕ} (ha : 1 ≤ a) (h : a ∈ C) :
    C ∩ Ico 1 (a + 1) = insert a (C ∩ Ico 1 a) := by
  rw [Ico_add_one_right_eq_Icc, ← Ico_insert_right ha, inter_insert_of_mem h]

/-- Extending the window by a non-cut adds nothing: the cuts below `a + 1` are the cuts below `a`,
when `a` is not a cut. -/
theorem inter_Ico_succ_of_notMem {C : Finset ℕ} {a : ℕ} (ha : 1 ≤ a) (h : a ∉ C) :
    C ∩ Ico 1 (a + 1) = C ∩ Ico 1 a := by
  rw [Ico_add_one_right_eq_Icc, ← Ico_insert_right ha, inter_insert_of_notMem h]

/-- **Adjacent indices in one block.** For `1 ≤ a < p`, the indices `a` and `a + 1` lie in one
`C`-block of `{1, …, p}` — that is, some `cutBlock p C t` contains both — if and only if `a` is
not a cut of `C`. Cutting at `a` is precisely what separates `a` from `a + 1`. -/
@[hjo "lem_cm_block_adjacent"]
theorem exists_mem_cutBlock_and_succ_mem_iff_notMem {p a : ℕ} {C : Finset ℕ} (ha : 1 ≤ a)
    (hap : a < p) :
    (∃ t, a ∈ cutBlock p C t ∧ a + 1 ∈ cutBlock p C t) ↔ a ∉ C := by
  constructor
  · rintro ⟨t, hat, hat1⟩ hC
    rw [mem_cutBlock] at hat hat1
    rw [inter_Ico_succ_of_mem ha hC, card_insert_of_notMem (by simp)] at hat1
    omega
  · intro hC
    exact ⟨#(C ∩ Ico 1 a) + 1, mem_cutBlock.mpr ⟨⟨ha, by omega⟩, rfl⟩,
      mem_cutBlock.mpr ⟨⟨by omega, by omega⟩, by rw [inter_Ico_succ_of_notMem ha hC]⟩⟩

/-- **A block is an interval**: if `a` and `b` lie in the same `C`-block of `{1, …, p}`, so does
every `c` between them. The cut counts at `a` and `b` agree and the count is monotone, so the count
at `c` is squeezed between them. -/
theorem mem_cutBlock_of_le_of_le {p : ℕ} {C : Finset ℕ} {t a b c : ℕ}
    (ha : a ∈ cutBlock p C t) (hb : b ∈ cutBlock p C t) (hac : a ≤ c) (hcb : c ≤ b) :
    c ∈ cutBlock p C t := by
  rw [mem_cutBlock] at ha hb ⊢
  have h₁ : #(C ∩ Ico 1 a) ≤ #(C ∩ Ico 1 c) :=
    card_le_card (inter_subset_inter_left (Ico_subset_Ico_right hac))
  have h₂ : #(C ∩ Ico 1 c) ≤ #(C ∩ Ico 1 b) :=
    card_le_card (inter_subset_inter_left (Ico_subset_Ico_right hcb))
  omega

/-- **Between two indices of one block there is no cut**: if `a` and `b` lie in the same
`C`-block of `{1, …, p}`, then `C` contains no `c` with `a ≤ c ≤ b - 1`. Being an interval, the
block holds both `c` and `c + 1`, which is what a cut at `c` would forbid. The hypothesis `a < b` is
not needed: for `b ≤ a` the window `Finset.Ico a b` is empty. -/
@[hjo "lem_cm_block_between"]
theorem disjoint_Ico_of_mem_cutBlock {p : ℕ} {C : Finset ℕ} {t a b : ℕ}
    (ha : a ∈ cutBlock p C t) (hb : b ∈ cutBlock p C t) :
    Disjoint C (Ico a b) := by
  rw [disjoint_left]
  intro c hcC hcIco
  obtain ⟨hac, hcb⟩ := mem_Ico.mp hcIco
  have hc : c ∈ cutBlock p C t := mem_cutBlock_of_le_of_le ha hb hac hcb.le
  have hc1 : c + 1 ∈ cutBlock p C t :=
    mem_cutBlock_of_le_of_le ha hb (hac.trans (Nat.le_succ c)) hcb
  exact (exists_mem_cutBlock_and_succ_mem_iff_notMem (mem_cutBlock.mp hc).1.1
    (mem_cutBlock.mp hc1).1.2).mp ⟨t, hc, hc1⟩ hcC

end HJO.Sym
