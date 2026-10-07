/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.GroupTheory.Perm.ClosureSwap
public import HJO.Classical.Kostka
public meta import HJO.Attr

/-! # The Bender--Knuth involution

`HJO.Sym.kostka_swap`: the Kostka number `K_D(α)` is unchanged when two adjacent entries of `α` are
interchanged. `HJO.Sym.kostka_comp`: hence it depends only on `α` up to a finitely-supported
permutation of the letters.

## Main definitions

* `HJO.Sym.lowCount`: the number of cells of a row whose entry is below a threshold.
* `HJO.Sym.bkSwap`: the Bender--Knuth involution at `i`.

## Main statements

* `HJO.Sym.lt_iff_lt_lowCount`: the cells of a row with entry below `v` are the first `lowCount`
  of them — the one structural fact about a semistandard row that everything here rests on.
* `HJO.Sym.bkSwap_bkSwap`: the involution is an involution.
* `HJO.Sym.kostka_swap`.
* `HJO.Sym.kostka_equivMapDomain`: `HJO.Sym.kostka_comp`.

## Implementation notes

**Everything is done with the three counting functions `lowCount T r i`, `lowCount T r (i+1)`,
`lowCount T r (i+2)`, and no cell is ever named.** A row of a semistandard tableau is nondecreasing,
so the cells of row `r` with entry below `v` form an *initial segment* of the row, of length
`lowCount T r v`; that is `HJO.Sym.lt_iff_lt_lowCount`, and it turns every statement about which
columns carry `i` into arithmetic. Writing `lo = lowCount T r i`, `mid = lowCount T r (i+1)` and
`hi = lowCount T r (i+2)`, the columns carrying `i` are `[lo, mid)` and those carrying `i+1` are
`[mid, hi)`; the involution replaces the *cut point* `mid` inside `[lo, hi)` by another cut point
`HJO.Sym.bkThr`, and that is the whole construction.

**The bound and free cells are not defined; only the *number* of bound cells is, and it
is given by a closed formula rather than by a count.** A cell `(r,j)` carrying `i` is bound when
`(r+1,j)` carries `i+1`. Column strictness makes `T (r+1) j ≥ i + 1` automatic there, so the
condition reduces to `j < lowCount T (r+1) (i+2)`: the bound cells of row `r` are
`[lo r, lowCount T (r+1) (i+2))`, visibly an initial segment of `[lo r, mid r)`, and their number is
`HJO.Sym.bkBound T i (r+1) = lowCount T (r+1) (i+2) - lo r`. The same formula is the number of bound
cells carrying `i+1` in row `r+1` — that is the bijection `(r,j) ↦ (r+1,j)`, and here it
is a definitional coincidence rather than a lemma. The three inequalities
`lowCount T (r+1) (v+1) ≤ lowCount T r v` (`HJO.Sym.lowCount_succ_le`) are all that is needed to
make the arithmetic go through, and `omega` does the rest.

**The content identity is a telescoping sum.** The new number of `i`'s in row `r` is
`bkThr - lo`, the old number of `i+1`'s is `hi - mid`, and the per-row identity
`(bkThr r - lo r) + bkBound r = bkBound (r+1) + (hi r - mid r)` telescopes over the rows to the
equality of the two contents, the boundary terms vanishing because `bkBound 0 = 0` and `bkBound r`
vanishes past the last row.

## References

This file proves `HJO.Sym.kostka_swap` and `HJO.Sym.kostka_comp`. -/

@[expose] public section

open Finset

namespace HJO.Sym

/-- **Counting the cells of a Young diagram row by row.** -/
theorem card_filter_eq_sum_row {μ : YoungDiagram} (P : ℕ × ℕ → Prop) [DecidablePred P]
    {N : ℕ} (hN : μ.colLen 0 ≤ N) :
    #{c ∈ μ.cells | P c} = ∑ r ∈ range N, #{j ∈ range (μ.rowLen r) | P (r, j)} := by
  classical
  have hmaps : Set.MapsTo Prod.fst (↑{c ∈ μ.cells | P c} : Set (ℕ × ℕ)) (↑(range N) : Set ℕ) := by
    rintro ⟨r, j⟩ hc
    rw [Finset.mem_coe, mem_filter, YoungDiagram.mem_cells] at hc
    exact Finset.mem_coe.2 (mem_range.2 (lt_of_lt_of_le
      (YoungDiagram.mem_iff_lt_colLen.1 (μ.up_left_mem le_rfl (Nat.zero_le j) hc.1)) hN))
  rw [card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun r _ => ?_
  have himg : {c ∈ {c ∈ μ.cells | P c} | c.1 = r}
      = Finset.image (fun j => (r, j)) {j ∈ range (μ.rowLen r) | P (r, j)} := by
    ext c
    obtain ⟨a, b⟩ := c
    simp only [mem_filter, mem_image, mem_range, YoungDiagram.mem_cells,
      YoungDiagram.mem_iff_lt_rowLen, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hb, hP⟩, rfl⟩
      exact ⟨b, ⟨hb, hP⟩, rfl, rfl⟩
    · rintro ⟨j, ⟨hj, hP⟩, rfl, rfl⟩
      exact ⟨⟨hj, hP⟩, rfl⟩
  rw [himg, Finset.card_image_of_injective _ fun j j' h => by simpa using h]

/-! ### The low counts of a row -/

variable {μ : YoungDiagram}

/-- **The number of cells of row `r` whose entry is below `v`.** -/
def lowCount (T : SemistandardYoungTableau μ) (r v : ℕ) : ℕ :=
  #{j ∈ range (μ.rowLen r) | T r j < v}

theorem filter_lt_eq_range (T : SemistandardYoungTableau μ) (r v : ℕ) :
    {j ∈ range (μ.rowLen r) | T r j < v} = range (lowCount T r v) := by
  rw [lowCount]
  set S := {j ∈ range (μ.rowLen r) | T r j < v} with hS
  have hdc : ∀ k ∈ S, ∀ k' ≤ k, k' ∈ S := by
    intro k hk k' hk'
    rw [hS, mem_filter, mem_range] at hk ⊢
    exact ⟨by omega, lt_of_le_of_lt
      (T.row_weak_of_le hk' (YoungDiagram.mem_iff_lt_rowLen.2 hk.1)) hk.2⟩
  rcases S.eq_empty_or_nonempty with h | hne
  · rw [h]
    simp
  · have hmax := S.max'_mem hne
    have heq : S = range (S.max' hne + 1) :=
      Finset.Subset.antisymm (fun k hk => mem_range.2 (Nat.lt_succ_of_le (S.le_max' k hk)))
        fun k hk => hdc _ hmax k (Nat.lt_succ_iff.1 (mem_range.1 hk))
    have hc : #S = S.max' hne + 1 := (congrArg Finset.card heq).trans (card_range _)
    rw [hc]
    exact heq

/-- **The cells of a row with entry below `v` are an initial segment of the row.** A row of a
semistandard tableau is nondecreasing, so the set of columns where it is below `v` is downward
closed. -/
theorem lt_iff_lt_lowCount {T : SemistandardYoungTableau μ} {r j v : ℕ} (hj : j < μ.rowLen r) :
    T r j < v ↔ j < lowCount T r v := by
  rw [← mem_range (n := lowCount T r v), ← filter_lt_eq_range T r v, mem_filter, mem_range]
  exact ⟨fun h => ⟨hj, h⟩, fun h => h.2⟩

theorem lowCount_le_rowLen (T : SemistandardYoungTableau μ) (r v : ℕ) :
    lowCount T r v ≤ μ.rowLen r := by
  rw [lowCount]
  exact le_trans (card_filter_le _ _) (le_of_eq (card_range _))

theorem lowCount_mono (T : SemistandardYoungTableau μ) (r : ℕ) {v v' : ℕ} (h : v ≤ v') :
    lowCount T r v ≤ lowCount T r v' := by
  refine card_le_card fun j hj => ?_
  rw [mem_filter] at hj ⊢
  exact ⟨hj.1, lt_of_lt_of_le hj.2 h⟩

theorem lowCount_eq_zero_of_colLen_le (T : SemistandardYoungTableau μ) {r : ℕ}
    (hr : μ.colLen 0 ≤ r) (v : ℕ) : lowCount T r v = 0 :=
  Nat.le_zero.1 ((lowCount_le_rowLen T r v).trans_eq
    (YoungDiagram.rowLen_eq_zero_of_colLen_le hr))

/-- **Moving one row down lowers the threshold by one**: column strictness. -/
theorem lowCount_succ_le (T : SemistandardYoungTableau μ) (r v : ℕ) :
    lowCount T (r + 1) (v + 1) ≤ lowCount T r v := by
  by_contra hcon
  rw [not_le] at hcon
  have hj1' : lowCount T r v < μ.rowLen (r + 1) :=
    lt_of_lt_of_le hcon (lowCount_le_rowLen T (r + 1) (v + 1))
  have hcell : ((r + 1, lowCount T r v) : ℕ × ℕ) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.2 hj1'
  have hjr : lowCount T r v < μ.rowLen r :=
    YoungDiagram.mem_iff_lt_rowLen.1 (μ.up_left_mem (Nat.le_succ r) le_rfl hcell)
  have h1 : T (r + 1) (lowCount T r v) < v + 1 := (lt_iff_lt_lowCount hj1').2 hcon
  have h2 : T r (lowCount T r v) < T (r + 1) (lowCount T r v) :=
    T.col_strict (Nat.lt_succ_self r) hcell
  exact absurd ((lt_iff_lt_lowCount hjr).1 (show T r (lowCount T r v) < v by omega)) (by omega)

/-- **The columns of a row carrying a given value form an interval.** -/
theorem filter_eq_Ico (T : SemistandardYoungTableau μ) (r v : ℕ) :
    {j ∈ range (μ.rowLen r) | T r j = v} = Finset.Ico (lowCount T r v) (lowCount T r (v + 1)) := by
  ext j
  rw [mem_filter, mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hj, rfl⟩
    exact ⟨Nat.not_lt.1 fun h => absurd ((lt_iff_lt_lowCount hj).2 h) (lt_irrefl _),
      (lt_iff_lt_lowCount hj).1 (Nat.lt_succ_self _)⟩
  · rintro ⟨h1, h2⟩
    have hj : j < μ.rowLen r := lt_of_lt_of_le h2 (lowCount_le_rowLen T r (v + 1))
    have h3 : T r j < v + 1 := (lt_iff_lt_lowCount hj).2 h2
    have h4 : ¬ T r j < v := fun h => absurd ((lt_iff_lt_lowCount hj).1 h) (by omega)
    exact ⟨hj, by omega⟩

/-- **A row carries a given value on `lowCount T r (v+1) - lowCount T r v` of its cells.** -/
theorem card_filter_eq (T : SemistandardYoungTableau μ) (r v : ℕ) :
    #{j ∈ range (μ.rowLen r) | T r j = v} = lowCount T r (v + 1) - lowCount T r v := by
  rw [filter_eq_Ico, Nat.card_Ico]

/-- **The content of a tableau, read row by row.** -/
theorem content_eq_sum_card_row (T : SemistandardYoungTableau μ) (a : ℕ) {N : ℕ}
    (hN : μ.colLen 0 ≤ N) :
    SemistandardYoungTableau.content T a
      = ∑ r ∈ range N, #{j ∈ range (μ.rowLen r) | T r j = a} := by
  rw [SemistandardYoungTableau.content, card_filter_eq_sum_row (fun c => T c.1 c.2 = a) hN]

theorem content_eq_sum_row (T : SemistandardYoungTableau μ) (a : ℕ) {N : ℕ}
    (hN : μ.colLen 0 ≤ N) :
    SemistandardYoungTableau.content T a
      = ∑ r ∈ range N, (lowCount T r (a + 1) - lowCount T r a) :=
  (content_eq_sum_card_row T a hN).trans (sum_congr rfl fun r _ => card_filter_eq T r a)

/-! ### The involution -/

theorem lt_of_lt_lowCount {T : SemistandardYoungTableau μ} {r j v : ℕ}
    (hj : j < lowCount T r v) : T r j < v :=
  (lt_iff_lt_lowCount (lt_of_lt_of_le hj (lowCount_le_rowLen T r v))).2 hj

theorem le_of_lowCount_le {T : SemistandardYoungTableau μ} {r j v : ℕ} (hjr : j < μ.rowLen r)
    (h : lowCount T r v ≤ j) : v ≤ T r j :=
  not_lt.1 fun hc => absurd ((lt_iff_lt_lowCount hjr).1 hc) (by omega)

/-- **The number of bound cells carrying `i+1` in row `r`.** A cell `(r,j)` carrying `i+1` is bound
when `(r-1,j)` carries `i`; column strictness makes `T (r-1) j ≤ i` automatic, so the condition is
`lowCount T (r-1) i ≤ j`, and the bound cells are the last `lowCount T r (i+2) - lowCount T (r-1) i`
of the row's `i+1`-cells. Row `0` has none. -/
def bkBound (T : SemistandardYoungTableau μ) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => lowCount T (r + 1) (i + 2) - lowCount T r i

/-- **The new cut point in row `r`**: the number of cells of row `r` that will carry an entry at
most `i`. It is the number of bound `i`-cells plus the number of free `i+1`-cells, offset by the
start of the block. -/
def bkThr (T : SemistandardYoungTableau μ) (i r : ℕ) : ℕ :=
  lowCount T r i + bkBound T i (r + 1) + (lowCount T r (i + 2) - lowCount T r (i + 1))
    - bkBound T i r

/-- **The entries of the Bender--Knuth swap at `i`**: inside the block of columns carrying `i` or
`i+1` the cut point is moved to `bkThr`, and elsewhere nothing changes. -/
def bkEntry (T : SemistandardYoungTableau μ) (i r j : ℕ) : ℕ :=
  if lowCount T r i ≤ j ∧ j < lowCount T r (i + 2) then (if j < bkThr T i r then i else i + 1)
  else T r j

variable (T : SemistandardYoungTableau μ) (i : ℕ)

/-- `HJO.Sym.lowCount_succ_le` in the shape the arithmetic below uses. -/
theorem lowCount_succ_le' (T : SemistandardYoungTableau μ) (i r : ℕ) :
    lowCount T (r + 1) (i + 2) ≤ lowCount T r (i + 1) := lowCount_succ_le T r (i + 1)

theorem bkBound_le (r : ℕ) :
    bkBound T i r ≤ lowCount T r (i + 2) - lowCount T r (i + 1) := by
  match r with
  | 0 => exact Nat.zero_le _
  | s + 1 =>
    rw [bkBound]
    have := lowCount_succ_le T s i
    have := lowCount_succ_le' T i s
    omega

theorem bkBound_succ_le (r : ℕ) :
    bkBound T i (r + 1) ≤ lowCount T r (i + 1) - lowCount T r i := by
  rw [bkBound]
  have := lowCount_succ_le' T i r
  omega

theorem lowCount_le_bkThr (r : ℕ) : lowCount T r i ≤ bkThr T i r := by
  rw [bkThr]
  have := bkBound_le T i r
  omega

theorem bkThr_le (r : ℕ) : bkThr T i r ≤ lowCount T r (i + 2) := by
  rw [bkThr]
  have h1 := bkBound_le T i r
  have h2 := bkBound_succ_le T i r
  have h3 := lowCount_mono T r (show i ≤ i + 1 by omega)
  have h4 := lowCount_mono T r (show i + 1 ≤ i + 2 by omega)
  omega

theorem bkEntry_of_lt {r j : ℕ} (hj : j < lowCount T r i) : bkEntry T i r j = T r j := by
  rw [bkEntry, ite_eq_right (by omega)]

theorem bkEntry_of_le {r j : ℕ} (hj : lowCount T r (i + 2) ≤ j) : bkEntry T i r j = T r j := by
  rw [bkEntry, ite_eq_right (by omega)]

theorem bkEntry_eq_self {r j : ℕ} (h1 : lowCount T r i ≤ j) (h2 : j < bkThr T i r) :
    bkEntry T i r j = i := by
  rw [bkEntry, ite_eq_left ⟨h1, lt_of_lt_of_le h2 (bkThr_le T i r)⟩, ite_eq_left h2]

theorem bkEntry_eq_succ {r j : ℕ} (h1 : bkThr T i r ≤ j) (h2 : j < lowCount T r (i + 2)) :
    bkEntry T i r j = i + 1 := by
  rw [bkEntry, ite_eq_left ⟨le_trans (lowCount_le_bkThr T i r) h1, h2⟩, ite_eq_right (by omega)]

theorem bkEntry_mem {r j : ℕ} (h1 : lowCount T r i ≤ j) (h2 : j < lowCount T r (i + 2)) :
    bkEntry T i r j = i ∨ bkEntry T i r j = i + 1 := by
  rcases lt_or_ge j (bkThr T i r) with h | h
  · exact Or.inl (bkEntry_eq_self T i h1 h)
  · exact Or.inr (bkEntry_eq_succ T i h h2)

theorem bkEntry_row_weak {r j₁ j₂ : ℕ} (hj : j₁ < j₂) (hcell : ((r, j₂) : ℕ × ℕ) ∈ μ) :
    bkEntry T i r j₁ ≤ bkEntry T i r j₂ := by
  have hj₂ : j₂ < μ.rowLen r := YoungDiagram.mem_iff_lt_rowLen.1 hcell
  have hj₁ : j₁ < μ.rowLen r := by omega
  have hcell₁ : ((r, j₁) : ℕ × ℕ) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.2 hj₁
  have hlo := lowCount_le_bkThr T i r
  have hhi := bkThr_le T i r
  rcases lt_or_ge j₂ (lowCount T r i) with h2 | h2
  · rw [bkEntry_of_lt T i (by omega), bkEntry_of_lt T i h2]
    exact T.row_weak hj hcell
  rcases lt_or_ge j₂ (lowCount T r (i + 2)) with h2' | h2'
  · rcases lt_or_ge j₁ (lowCount T r i) with h1 | h1
    · rw [bkEntry_of_lt T i h1]
      rcases bkEntry_mem T i h2 h2' with h | h <;> rw [h] <;>
        exact le_of_lt (lt_of_lt_of_le (lt_of_lt_lowCount h1) (by omega))
    · rcases lt_or_ge j₂ (bkThr T i r) with h | h
      · rw [bkEntry_eq_self T i h1 (by omega), bkEntry_eq_self T i h2 h]
      · rw [bkEntry_eq_succ T i h h2']
        rcases bkEntry_mem T i h1 (by omega) with h' | h'
        · rw [h']
          omega
        · rw [h']
  · rw [bkEntry_of_le T i h2']
    have hT2 : i + 2 ≤ T r j₂ := le_of_lowCount_le hj₂ h2'
    rcases lt_or_ge j₁ (lowCount T r i) with h1 | h1
    · rw [bkEntry_of_lt T i h1]
      have := lt_of_lt_lowCount h1
      omega
    rcases lt_or_ge j₁ (lowCount T r (i + 2)) with h1' | h1'
    · rcases bkEntry_mem T i h1 h1' with h' | h' <;> rw [h'] <;> omega
    · rw [bkEntry_of_le T i h1']
      exact T.row_weak hj hcell

theorem bkEntry_col_strict_succ {r j : ℕ} (hcell : ((r + 1, j) : ℕ × ℕ) ∈ μ) :
    bkEntry T i r j < bkEntry T i (r + 1) j := by
  have hj' : j < μ.rowLen (r + 1) := YoungDiagram.mem_iff_lt_rowLen.1 hcell
  have hcell₀ : ((r, j) : ℕ × ℕ) ∈ μ := μ.up_left_mem (Nat.le_succ r) le_rfl hcell
  have hj : j < μ.rowLen r := YoungDiagram.mem_iff_lt_rowLen.1 hcell₀
  have e1 : lowCount T (r + 1) (i + 1) ≤ lowCount T r i := lowCount_succ_le T r i
  have e2 : lowCount T (r + 1) (i + 2) ≤ lowCount T r (i + 1) := lowCount_succ_le' T i r
  have e3 : lowCount T (r + 1) i ≤ lowCount T (r + 1) (i + 1) :=
    lowCount_mono T (r + 1) (show i ≤ i + 1 by omega)
  have e4 : lowCount T r (i + 1) ≤ lowCount T r (i + 2) :=
    lowCount_mono T r (show i + 1 ≤ i + 2 by omega)
  have e5 : lowCount T r i ≤ lowCount T r (i + 1) :=
    lowCount_mono T r (show i ≤ i + 1 by omega)
  have hb1 : bkBound T i (r + 1) = lowCount T (r + 1) (i + 2) - lowCount T r i := by rw [bkBound]
  have hb2 := bkBound_le T i r
  have hb3 : bkBound T i (r + 2)
      ≤ lowCount T (r + 1) (i + 1) - lowCount T (r + 1) i := bkBound_succ_le T i (r + 1)
  have e6 : lowCount T (r + 1) (i + 1) ≤ lowCount T (r + 1) (i + 2) :=
    lowCount_mono T (r + 1) (show i + 1 ≤ i + 2 by omega)
  have ht1 : bkThr T i r
      = lowCount T r i + bkBound T i (r + 1) + (lowCount T r (i + 2) - lowCount T r (i + 1))
        - bkBound T i r := by rw [bkThr]
  have ht2 : bkThr T i (r + 1)
      = lowCount T (r + 1) i + bkBound T i (r + 2)
        + (lowCount T (r + 1) (i + 2) - lowCount T (r + 1) (i + 1)) - bkBound T i (r + 1) := by
    rw [bkThr]
  rcases lt_or_ge j (lowCount T (r + 1) i) with c1 | c1
  · rw [bkEntry_of_lt T i (show j < lowCount T r i by omega), bkEntry_of_lt T i c1]
    exact T.col_strict (Nat.lt_succ_self r) hcell
  rcases lt_or_ge j (lowCount T (r + 1) (i + 2)) with c2 | c2
  · rcases lt_or_ge j (lowCount T r i) with c3 | c3
    · rw [bkEntry_of_lt T i c3]
      have := lt_of_lt_lowCount c3
      rcases bkEntry_mem T i c1 c2 with h | h <;> rw [h] <;> omega
    · rw [bkEntry_eq_self T i c3 (by omega), bkEntry_eq_succ T i (by omega) c2]
      omega
  · rw [bkEntry_of_le T i c2]
    have hT : i + 2 ≤ T (r + 1) j := le_of_lowCount_le hj' c2
    rcases lt_or_ge j (lowCount T r i) with c3 | c3
    · rw [bkEntry_of_lt T i c3]
      have := lt_of_lt_lowCount c3
      omega
    rcases lt_or_ge j (lowCount T r (i + 2)) with c4 | c4
    · rcases bkEntry_mem T i c3 c4 with h | h <;> rw [h] <;> omega
    · rw [bkEntry_of_le T i c4]
      exact T.col_strict (Nat.lt_succ_self r) hcell

theorem colStrict_of_succ {E : ℕ → ℕ → ℕ}
    (h : ∀ r j, ((r + 1, j) : ℕ × ℕ) ∈ μ → E r j < E (r + 1) j) :
    ∀ {r₁ r₂ j : ℕ}, r₁ < r₂ → ((r₂, j) : ℕ × ℕ) ∈ μ → E r₁ j < E r₂ j := by
  intro r₁ r₂ j hr hcell
  induction r₂ with
  | zero => omega
  | succ s ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hlt | rfl
    · exact lt_trans (ih hlt (μ.up_left_mem (Nat.le_succ s) le_rfl hcell)) (h s j hcell)
    · exact h r₁ j hcell

theorem bkEntry_col_strict {r₁ r₂ j : ℕ} (hr : r₁ < r₂) (hcell : ((r₂, j) : ℕ × ℕ) ∈ μ) :
    bkEntry T i r₁ j < bkEntry T i r₂ j :=
  colStrict_of_succ (E := bkEntry T i) (fun _ _ hc => bkEntry_col_strict_succ T i hc) hr hcell

theorem bkEntry_zeros {r j : ℕ} (hc : ((r, j) : ℕ × ℕ) ∉ μ) : bkEntry T i r j = 0 := by
  rw [bkEntry_of_le T i (le_trans (lowCount_le_rowLen T r (i + 2))
    (not_lt.1 fun h => hc (YoungDiagram.mem_iff_lt_rowLen.2 h))), T.zeros hc]

/-- **The Bender--Knuth involution at `i`.** -/
def bkSwap (T : SemistandardYoungTableau μ) (i : ℕ) : SemistandardYoungTableau μ where
  entry := bkEntry T i
  row_weak' := bkEntry_row_weak T i
  col_strict' := bkEntry_col_strict T i
  zeros' := bkEntry_zeros T i

@[simp]
theorem bkSwap_apply (r j : ℕ) : bkSwap T i r j = bkEntry T i r j := rfl

/-! ### The contents of the swap -/

theorem card_filter_bkSwap_eq_self (r : ℕ) :
    #{j ∈ range (μ.rowLen r) | bkSwap T i r j = i} = bkThr T i r - lowCount T r i := by
  rw [show {j ∈ range (μ.rowLen r) | bkSwap T i r j = i}
      = Finset.Ico (lowCount T r i) (bkThr T i r) from ?_, Nat.card_Ico]
  ext j
  rw [mem_filter, mem_range, Finset.mem_Ico, bkSwap_apply]
  constructor
  · rintro ⟨hj, hE⟩
    refine ⟨?_, ?_⟩
    · by_contra hc
      rw [not_le] at hc
      rw [bkEntry_of_lt T i hc] at hE
      exact absurd (lt_of_lt_lowCount hc) (by omega)
    · by_contra hc
      rw [not_lt] at hc
      rcases lt_or_ge j (lowCount T r (i + 2)) with h | h
      · rw [bkEntry_eq_succ T i hc h] at hE
        omega
      · rw [bkEntry_of_le T i h] at hE
        exact absurd (le_of_lowCount_le hj h) (by omega)
  · rintro ⟨h1, h2⟩
    exact ⟨lt_of_lt_of_le h2 (le_trans (bkThr_le T i r) (lowCount_le_rowLen T r (i + 2))),
      bkEntry_eq_self T i h1 h2⟩

theorem card_filter_bkSwap_eq_succ (r : ℕ) :
    #{j ∈ range (μ.rowLen r) | bkSwap T i r j = i + 1} = lowCount T r (i + 2) - bkThr T i r := by
  rw [show {j ∈ range (μ.rowLen r) | bkSwap T i r j = i + 1}
      = Finset.Ico (bkThr T i r) (lowCount T r (i + 2)) from ?_, Nat.card_Ico]
  ext j
  rw [mem_filter, mem_range, Finset.mem_Ico, bkSwap_apply]
  constructor
  · rintro ⟨hj, hE⟩
    refine ⟨?_, ?_⟩
    · by_contra hc
      rw [not_le] at hc
      rcases lt_or_ge j (lowCount T r i) with h | h
      · rw [bkEntry_of_lt T i h] at hE
        exact absurd (lt_of_lt_lowCount h) (by omega)
      · rw [bkEntry_eq_self T i h hc] at hE
        omega
    · by_contra hc
      rw [not_lt] at hc
      rw [bkEntry_of_le T i hc] at hE
      exact absurd (le_of_lowCount_le hj hc) (by omega)
  · rintro ⟨h1, h2⟩
    exact ⟨lt_of_lt_of_le h2 (lowCount_le_rowLen T r (i + 2)), bkEntry_eq_succ T i h1 h2⟩

theorem card_filter_bkSwap_eq_other {a : ℕ} (h1 : a ≠ i) (h2 : a ≠ i + 1) (r : ℕ) :
    #{j ∈ range (μ.rowLen r) | bkSwap T i r j = a} = #{j ∈ range (μ.rowLen r) | T r j = a} := by
  refine congrArg Finset.card (Finset.filter_congr fun j hj => ?_)
  rw [mem_range] at hj
  rw [bkSwap_apply]
  rcases lt_or_ge j (lowCount T r i) with h | h
  · rw [bkEntry_of_lt T i h]
  rcases lt_or_ge j (lowCount T r (i + 2)) with h' | h'
  · have hT1 : i ≤ T r j := le_of_lowCount_le hj h
    have hT2 : T r j < i + 2 := lt_of_lt_lowCount h'
    rcases bkEntry_mem T i h h' with hb | hb <;> rw [hb] <;>
      exact ⟨fun hc => absurd hc (by omega), fun hc => absurd hc (by omega)⟩
  · rw [bkEntry_of_le T i h']

theorem bkBound_eq_zero_of_colLen_le {N : ℕ} (hN : μ.colLen 0 ≤ N) : bkBound T i N = 0 := by
  match N with
  | 0 => rfl
  | s + 1 => rw [bkBound, lowCount_eq_zero_of_colLen_le T hN (i + 2), Nat.zero_sub]

/-- **The telescoping identity.** The new number of `i`'s in a row differs from the old number of
`i+1`'s by the bound counts of that row and the next, and those cancel over the rows. -/
theorem sum_bkThr_sub (N : ℕ) :
    ∑ r ∈ range N, (bkThr T i r - lowCount T r i)
      = bkBound T i N + ∑ r ∈ range N, (lowCount T r (i + 2) - lowCount T r (i + 1)) := by
  induction N with
  | zero => rw [Finset.sum_range_zero, Finset.sum_range_zero, bkBound, add_zero]
  | succ s ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : bkThr T i s = lowCount T s i + bkBound T i (s + 1)
        + (lowCount T s (i + 2) - lowCount T s (i + 1)) - bkBound T i s := by rw [bkThr]
    have h2 := bkBound_le T i s
    omega

/-- **The swap interchanges the numbers of `i`'s and `i+1`'s.** -/
theorem content_bkSwap_self : SemistandardYoungTableau.content (bkSwap T i) i
    = SemistandardYoungTableau.content T (i + 1) := by
  rw [content_eq_sum_card_row (bkSwap T i) i (le_refl (μ.colLen 0)),
    sum_congr rfl fun r _ => card_filter_bkSwap_eq_self T i r, sum_bkThr_sub,
    bkBound_eq_zero_of_colLen_le T i (le_refl _), zero_add,
    show SemistandardYoungTableau.content T (i + 1)
      = ∑ r ∈ range (μ.colLen 0), (lowCount T r (i + 2) - lowCount T r (i + 1)) from
      content_eq_sum_row T (i + 1) (le_refl _)]

theorem content_bkSwap_succ : SemistandardYoungTableau.content (bkSwap T i) (i + 1)
    = SemistandardYoungTableau.content T i := by
  have hkey : ∑ r ∈ range (μ.colLen 0),
      ((bkThr T i r - lowCount T r i) + (lowCount T r (i + 2) - bkThr T i r))
        = ∑ r ∈ range (μ.colLen 0), ((lowCount T r (i + 1) - lowCount T r i)
          + (lowCount T r (i + 2) - lowCount T r (i + 1))) :=
    sum_congr rfl fun r _ => by
      have h1 := lowCount_le_bkThr T i r
      have h2 := bkThr_le T i r
      have h3 := lowCount_mono T r (show i ≤ i + 1 by omega)
      have h4 := lowCount_mono T r (show i + 1 ≤ i + 2 by omega)
      omega
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hkey
  have h5 : ∑ r ∈ range (μ.colLen 0), (bkThr T i r - lowCount T r i)
      = ∑ r ∈ range (μ.colLen 0), (lowCount T r (i + 2) - lowCount T r (i + 1)) := by
    rw [sum_bkThr_sub, bkBound_eq_zero_of_colLen_le T i (le_refl _), zero_add]
  rw [content_eq_sum_card_row (bkSwap T i) (i + 1) (le_refl (μ.colLen 0)),
    sum_congr rfl fun r _ => card_filter_bkSwap_eq_succ T i r,
    show SemistandardYoungTableau.content T i
      = ∑ r ∈ range (μ.colLen 0), (lowCount T r (i + 1) - lowCount T r i) from
      content_eq_sum_row T i (le_refl _)]
  omega

theorem content_bkSwap_other {a : ℕ} (h1 : a ≠ i) (h2 : a ≠ i + 1) :
    SemistandardYoungTableau.content (bkSwap T i) a = SemistandardYoungTableau.content T a := by
  rw [content_eq_sum_card_row (bkSwap T i) a (le_refl (μ.colLen 0)),
    content_eq_sum_card_row T a (le_refl (μ.colLen 0))]
  exact sum_congr rfl fun r _ => card_filter_bkSwap_eq_other T i h1 h2 r


/-! ### The swap is an involution -/

theorem lowCount_bkSwap_self (r : ℕ) : lowCount (bkSwap T i) r i = lowCount T r i := by
  refine congrArg Finset.card (Finset.filter_congr fun j hj => ?_)
  rw [mem_range] at hj
  rw [bkSwap_apply]
  rcases lt_or_ge j (lowCount T r i) with h | h
  · rw [bkEntry_of_lt T i h]
  rcases lt_or_ge j (lowCount T r (i + 2)) with h' | h'
  · have hT1 : i ≤ T r j := le_of_lowCount_le hj h
    rcases bkEntry_mem T i h h' with hb | hb <;> rw [hb] <;>
      exact ⟨fun hc => absurd hc (by omega), fun hc => absurd hc (by omega)⟩
  · rw [bkEntry_of_le T i h']

theorem lowCount_bkSwap_two (r : ℕ) :
    lowCount (bkSwap T i) r (i + 2) = lowCount T r (i + 2) := by
  refine congrArg Finset.card (Finset.filter_congr fun j hj => ?_)
  rw [mem_range] at hj
  rw [bkSwap_apply]
  rcases lt_or_ge j (lowCount T r i) with h | h
  · rw [bkEntry_of_lt T i h]
  rcases lt_or_ge j (lowCount T r (i + 2)) with h' | h'
  · have hT2 : T r j < i + 2 := lt_of_lt_lowCount h'
    rcases bkEntry_mem T i h h' with hb | hb <;> rw [hb] <;>
      exact ⟨fun _ => hT2, fun _ => by omega⟩
  · rw [bkEntry_of_le T i h']

theorem lowCount_bkSwap_succ (r : ℕ) : lowCount (bkSwap T i) r (i + 1) = bkThr T i r := by
  have hthr : bkThr T i r ≤ μ.rowLen r :=
    le_trans (bkThr_le T i r) (lowCount_le_rowLen T r (i + 2))
  rw [lowCount,
    show {j ∈ range (μ.rowLen r) | bkSwap T i r j < i + 1} = range (bkThr T i r) from ?_,
    card_range]
  ext j
  rw [mem_filter, mem_range, mem_range, bkSwap_apply]
  constructor
  · rintro ⟨hj, hE⟩
    by_contra hc
    rw [not_lt] at hc
    rcases lt_or_ge j (lowCount T r (i + 2)) with h | h
    · rw [bkEntry_eq_succ T i hc h] at hE
      omega
    · rw [bkEntry_of_le T i h] at hE
      exact absurd (le_of_lowCount_le hj h) (by omega)
  · intro hj
    refine ⟨by omega, ?_⟩
    rcases lt_or_ge j (lowCount T r i) with h | h
    · rw [bkEntry_of_lt T i h]
      exact lt_trans (lt_of_lt_lowCount h) (Nat.lt_succ_self i)
    · rw [bkEntry_eq_self T i h hj]
      exact Nat.lt_succ_self i

theorem bkBound_bkSwap (r : ℕ) : bkBound (bkSwap T i) i r = bkBound T i r := by
  match r with
  | 0 => rfl
  | s + 1 => rw [bkBound, bkBound, lowCount_bkSwap_two, lowCount_bkSwap_self]

theorem bkThr_bkSwap (r : ℕ) : bkThr (bkSwap T i) i r = lowCount T r (i + 1) := by
  rw [bkThr, bkBound_bkSwap, bkBound_bkSwap, lowCount_bkSwap_self, lowCount_bkSwap_two,
    lowCount_bkSwap_succ]
  have h1 : bkThr T i r = lowCount T r i + bkBound T i (r + 1)
      + (lowCount T r (i + 2) - lowCount T r (i + 1)) - bkBound T i r := by rw [bkThr]
  have h2 := bkBound_le T i r
  have h3 := bkBound_succ_le T i r
  have h4 := lowCount_mono T r (show i ≤ i + 1 by omega)
  have h5 := lowCount_mono T r (show i + 1 ≤ i + 2 by omega)
  omega

/-- **The Bender--Knuth swap is an involution.** Applying it twice restores the cut point: the new
count of bound cells is the old one, and the new cut point of the swapped tableau is the old
`lowCount T r (i+1)`. -/
theorem bkSwap_bkSwap : bkSwap (bkSwap T i) i = T := by
  refine SemistandardYoungTableau.ext fun r j => ?_
  rw [bkSwap_apply, bkEntry, lowCount_bkSwap_self, lowCount_bkSwap_two, bkThr_bkSwap]
  by_cases hz : lowCount T r i ≤ j ∧ j < lowCount T r (i + 2)
  · rw [ite_eq_left hz]
    have hj : j < μ.rowLen r := lt_of_lt_of_le hz.2 (lowCount_le_rowLen T r (i + 2))
    have hT1 : i ≤ T r j := le_of_lowCount_le hj hz.1
    have hT2 : T r j < i + 2 := lt_of_lt_lowCount hz.2
    by_cases hm : j < lowCount T r (i + 1)
    · rw [ite_eq_left hm]
      have := lt_of_lt_lowCount hm
      omega
    · rw [ite_eq_right hm]
      have := le_of_lowCount_le hj (not_lt.1 hm)
      omega
  · rw [ite_eq_right hz, bkSwap_apply, bkEntry, ite_eq_right hz]

theorem bkSwap_involutive : Function.Involutive fun T : SemistandardYoungTableau μ => bkSwap T i :=
  fun T => bkSwap_bkSwap T i


/-! ### The Kostka number is unchanged -/

theorem wt_bkSwap (α α' : ℕ →₀ ℕ) (h1 : α' i = α (i + 1)) (h2 : α' (i + 1) = α i)
    (h3 : ∀ a, a ≠ i → a ≠ i + 1 → α' a = α a) (hT : T.wt = α) : (bkSwap T i).wt = α' := by
  refine Finsupp.ext fun a => ?_
  rw [SemistandardYoungTableau.wt_apply]
  by_cases ha : a = i
  · subst ha
    rw [content_bkSwap_self, h1, ← hT, SemistandardYoungTableau.wt_apply]
  by_cases ha' : a = i + 1
  · subst ha'
    rw [content_bkSwap_succ, h2, ← hT, SemistandardYoungTableau.wt_apply]
  · rw [content_bkSwap_other T i ha ha', h3 a ha ha', ← hT, SemistandardYoungTableau.wt_apply]

/-- **Interchanging two adjacent multiplicities does not change the Kostka
number.** The Bender--Knuth involution at `i` is a bijection of `SSYT(D)` carrying the tableaux of
content `α` onto those of content `α'`. -/
@[hjo "lem_sf_bk_swap"]
theorem kostka_swap (μ : YoungDiagram) (i : ℕ) (α α' : ℕ →₀ ℕ) (h1 : α' i = α (i + 1))
    (h2 : α' (i + 1) = α i) (h3 : ∀ a, a ≠ i → a ≠ i + 1 → α' a = α a) :
    kostka μ α = kostka μ α' := by
  have himg : (fun T : SemistandardYoungTableau μ => bkSwap T i)
      '' {T : SemistandardYoungTableau μ | T.wt = α} = {S : SemistandardYoungTableau μ | S.wt = α'}
      := by
    refine Set.Subset.antisymm ?_ fun S hS => ?_
    · rintro S ⟨T, hT, rfl⟩
      exact wt_bkSwap T i α α' h1 h2 h3 hT
    · exact ⟨bkSwap S i,
        wt_bkSwap S i α' α h2.symm h1.symm (fun a ha ha' => (h3 a ha ha').symm) hS,
        bkSwap_bkSwap S i⟩
  rw [kostka, kostka, ← himg,
    Set.ncard_image_of_injective _ (bkSwap_involutive (μ := μ) i).injective]

/-- **The relabellings of the letters that the Kostka number does not notice.** -/
def kostkaStab (μ : YoungDiagram) : Submonoid (Equiv.Perm ℕ) where
  carrier := {σ | ∀ α : ℕ →₀ ℕ, kostka μ (Finsupp.equivMapDomain σ α) = kostka μ α}
  mul_mem' {σ τ} hσ hτ := fun α => by
    have h : Finsupp.equivMapDomain (σ * τ) α
        = Finsupp.equivMapDomain σ (Finsupp.equivMapDomain τ α) := by
      rw [← Finsupp.equivMapDomain_trans]
      rfl
    rw [h, hσ, hτ]
  one_mem' := fun α => by rw [Equiv.Perm.one_def, Finsupp.equivMapDomain_refl]

theorem mem_kostkaStab {μ : YoungDiagram} {σ : Equiv.Perm ℕ} :
    σ ∈ kostkaStab μ ↔ ∀ α : ℕ →₀ ℕ, kostka μ (Finsupp.equivMapDomain σ α) = kostka μ α := Iff.rfl

theorem swap_succ_mem_kostkaStab (μ : YoungDiagram) (i : ℕ) :
    Equiv.swap i (i + 1) ∈ kostkaStab μ := by
  refine mem_kostkaStab.2 fun α => (kostka_swap μ i α _ ?_ ?_ ?_).symm
  · rw [Finsupp.equivMapDomain_apply, Equiv.symm_swap, Equiv.swap_apply_left]
  · rw [Finsupp.equivMapDomain_apply, Equiv.symm_swap, Equiv.swap_apply_right]
  · intro a ha ha'
    rw [Finsupp.equivMapDomain_apply, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne ha ha']

theorem swap_add_mem_kostkaStab (μ : YoungDiagram) (a k : ℕ) :
    Equiv.swap a (a + k) ∈ kostkaStab μ := by
  induction k with
  | zero => rw [Nat.add_zero, Equiv.swap_self, ← Equiv.Perm.one_def]; exact one_mem _
  | succ k ih => exact SubmonoidClass.swap_mem_trans _ ih (swap_succ_mem_kostkaStab μ (a + k))

theorem swap_mem_kostkaStab (μ : YoungDiagram) (a b : ℕ) : Equiv.swap a b ∈ kostkaStab μ := by
  rcases le_total a b with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact swap_add_mem_kostkaStab μ a k
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Equiv.swap_comm]
    exact swap_add_mem_kostkaStab μ b k

/-- **The Kostka number depends only on the multiset of multiplicities below the window in which
two sequences differ.** The induction moves the correct multiplicity into position `k` by a single
transposition, which `HJO.Sym.kostka_swap` shows the Kostka number does not notice, and then
recurses on the shorter window. -/
theorem kostka_eq_of_map_range (μ : YoungDiagram) : ∀ (k : ℕ) (α β : ℕ →₀ ℕ),
    (∀ a, k ≤ a → α a = β a) →
      Multiset.map α (range k).val = Multiset.map β (range k).val → kostka μ α = kostka μ β := by
  intro k
  induction k with
  | zero => exact fun α β hag _ => by rw [Finsupp.ext fun a => hag a (Nat.zero_le a)]
  | succ k ih =>
    intro α β hag hmap
    have hmem : β k ∈ Multiset.map α (range (k + 1)).val := by
      rw [hmap]
      exact Multiset.mem_map.2 ⟨k, by rw [← Finset.mem_def, mem_range]; omega, rfl⟩
    obtain ⟨a, ha, hav⟩ := Multiset.mem_map.1 hmem
    rw [← Finset.mem_def, mem_range] at ha
    set α' := Finsupp.equivMapDomain (Equiv.swap a k) α with hα'
    have hval : ∀ b : ℕ, α' b = α (Equiv.swap a k b) := fun b => by
      rw [hα', Finsupp.equivMapDomain_apply, Equiv.symm_swap]
    have hk : α' k = β k := by rw [hval, Equiv.swap_apply_right, hav]
    have hag' : ∀ b, k ≤ b → α' b = β b := by
      intro b hb
      rcases eq_or_lt_of_le hb with rfl | hlt
      · exact hk
      · rw [hval, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
        exact hag b (by omega)
    have hswap : Multiset.map (Equiv.swap a k) (range (k + 1)).val = (range (k + 1)).val := by
      have hfin : Finset.map (Equiv.swap a k).toEmbedding (range (k + 1)) = range (k + 1) := by
        refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) (by rw [Finset.card_map])
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hx
        rw [mem_range] at hj ⊢
        rw [Equiv.coe_toEmbedding]
        rcases eq_or_ne j a with rfl | hja
        · rw [Equiv.swap_apply_left]; omega
        rcases eq_or_ne j k with rfl | hjk
        · rw [Equiv.swap_apply_right]; omega
        · rw [Equiv.swap_apply_of_ne_of_ne hja hjk]; omega
      rw [← Equiv.coe_toEmbedding (f := Equiv.swap a k), ← Finset.map_val, hfin]
    have hmap' : Multiset.map α' (range k).val = Multiset.map β (range k).val := by
      have h1 : Multiset.map α' (range (k + 1)).val = Multiset.map α (range (k + 1)).val := by
        rw [show (α' : ℕ → ℕ) = (α : ℕ → ℕ) ∘ (Equiv.swap a k : ℕ → ℕ) from funext hval,
          ← Multiset.map_map, hswap]
      have hrange : ∀ γ : ℕ →₀ ℕ, Multiset.map γ (range (k + 1)).val
          = γ k ::ₘ Multiset.map γ (range k).val := fun γ => by
        rw [Finset.range_val, Finset.range_val, Multiset.range_succ, Multiset.map_cons]
      have h2 : α' k ::ₘ Multiset.map α' (range k).val
          = β k ::ₘ Multiset.map β (range k).val := by
        rw [← hrange α', ← hrange β, h1, hmap]
      rw [hk] at h2
      exact (Multiset.cons_inj_right (β k)).1 h2
    exact ((swap_mem_kostkaStab μ a k) α).symm.trans (ih α' β hag' hmap')

/-- **The Kostka number depends only on the multiset of multiplicities.** A
permutation of the letters fixing all but finitely many of them permutes a window `range M`, so the
two sequences agree above the window and have the same multiset of entries inside it. -/
@[hjo "lem_sf_kostka_sort"]
theorem kostka_comp (μ : YoungDiagram) {σ : Equiv.Perm ℕ} {M : ℕ} (hσ : ∀ a, M ≤ a → σ a = a)
    (α α' : ℕ →₀ ℕ) (h : ∀ a, α' a = α (σ a)) : kostka μ α = kostka μ α' := by
  refine kostka_eq_of_map_range μ M α α' (fun a ha => ?_) ?_
  · rw [h a, hσ a ha]
  · have hfin : Finset.map σ.toEmbedding (range M) = range M := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) (by rw [Finset.card_map])
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hx
      rw [mem_range] at hj ⊢
      rw [Equiv.coe_toEmbedding]
      by_contra hc
      rw [not_lt] at hc
      exact absurd (σ.injective (hσ (σ j) hc)) (by omega)
    rw [show (α' : ℕ → ℕ) = (α : ℕ → ℕ) ∘ (σ : ℕ → ℕ) from funext h, ← Multiset.map_map,
      ← Equiv.coe_toEmbedding (f := σ), ← Finset.map_val, hfin]


end HJO.Sym
