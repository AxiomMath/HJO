/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepBalance
public import HJO.Shuffle.SweepPositions
public meta import HJO.Attr

/-! # The balance to the left of an event, and the widths summed over the heads

This file proves three of the four inputs that
`HJO.Paths.sum_sweepRight_add_leftEastCount_A_eq_sum_sweepWidth_sub_one_B` and
`HJO.Paths.sweepRight_add_leftEastCount_add_one` use. Two of them are about what the level line
through a swept point `P = (x, y)` does to the *left* of `P`:

* the columns `c < x` carrying a north step live at `P` are as many as the columns `c < x` whose
  east step the line crosses (`HJO.Paths.card_leftLiveCols_eq_card_leftEastCols`), and they
  interleave;
* hence `a^*_{P̂}(P)` counts the live north steps of column below `x`
  (`HJO.Paths.leftEastCount_eq_card_filter_fst_lt`), and at a type-`A` event the width splits as
  `a_{P̂}(P) + a^*_{P̂}(P)` (`HJO.Paths.sweepRight_add_leftEastCount`).

The third is the identity `∑_{P of type A or C} k_{P̂}(P) = #𝒜(P̂) + #S(P̂)`
(`HJO.Paths.sum_sweepWidth_head_eq_card_sweepAttack_add_card_sweepMarked`), the companion at the
heads of `HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one` at the feet.

## Main results

* `HJO.Paths.card_leftLiveCols_eq_card_leftEastCols`.
* `HJO.Paths.leftEastCount_eq_card_filter_fst_lt`.
* `HJO.Paths.sweepRight_add_leftEastCount`.
* `HJO.Paths.sum_sweepWidth_head_eq_card_sweepAttack_add_card_sweepMarked`.

## Implementation notes

**The alternation is a telescoping sum, not a parity argument.** The usual proof walks the
initial segment `V_0, …, V_T` of the path as a list, sets `ε_t = 1` exactly where the rank exceeds
`η`, observes `ε_0 = ε_T = 0`, and concludes from the alternation of the changes of `ε` that the
crossed segments run north, east, north, east, … None of that list is built here. Writing, for
`0 ≤ c ≤ x`,

* `A c` for `η < rk̂(c, ŷ_c)` — the bottom of the column at `c` outranks `P`, which is the
  indicator `ε` at the start of block `c`;
* `B c` for `η < rk̂(c, ŷ_{c+1})` — the top of that column outranks `P`;

the column at `c` carries a live north step exactly when `¬A c ∧ B c`, and the east step at `c` is
crossed exactly when `¬A (c+1) ∧ B c`. Since `ŷ_c ≤ ŷ_{c+1}` gives `A c → B c`, and the rank falls
along an east step (`HJO.Paths.abovePointRank_eastRight_lt_eastLeft`) gives `A (c+1) → B c`, *both*
count `B c`:
`[c live] + [A c] = [B c] = [c crossed] + [A (c+1)]`.
Summing that over `c < c₀` telescopes to
`#{live columns < c₀} = #{crossed columns < c₀} + [A c₀]`,
which at `c₀ = x` is `r = s` because `A 0` and `A x` both fail, and at a general `c₀` is the
interleaving. So the whole lemma is one induction on `c₀` over the identity above.

**The interleaving, stated without a listing.** The conclusion
`n_1 ≤ m_1 < n_2 ≤ m_2 < … < n_r ≤ m_r` is carried as the two counting inequalities

* `#{m < c} ≤ #{n < c}` for every `c`, which is `n_i ≤ m_i`, and
* `#{n ≤ c} ≤ #{m < c} + 1` for every `c`, which is `m_i < n_{i+1}`,

and those two are equivalent to the display: the first at `c = m_i + 1` gives `n_i ≤ m_i` and
conversely, the second at `c = n_{i+1}` gives `m_i < n_{i+1}` and conversely. The strictness on the
right of each `m_i` is what the second inequality's mixed `≤`/`<` records; the two inequalities are
*not* interchangeable for `<`/`≤`, and a symmetric pair of bounds would be strictly weaker than the
display. Nothing downstream reads the interleaving — `HJO.Paths.leftEastCount_eq_card_filter_fst_lt`
uses only `r = s` — but it is part of the statement and so is proved.

**Hypotheses.** The three lemmas about the left are stated with `eventType y P ≠ EventType.E` where
the statement is usually written for type `A`, `B` or `C`; on the swept region the five types are
exhaustive, so this admits type `D` as well, and the proof reads only `ŷ_x ≤ y`. `0 < b` is *not*
carried, although the proof uses it to make the rank fall along an east step: at `b = 0` the path
has no north step and the level line crosses no east step, so both column sets are empty and the
conclusion is trivial — that case is dispatched first rather than assumed away.

**`HJO.Paths.sum_sweepWidth_head_eq_card_sweepAttack_add_card_sweepMarked` mirrors
`HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one`.** The type-`A`-or-`C` points are the heads
of the north steps (`HJO.Paths.isSweepHead_iff_eventType`), and since `rk̂(head t) = rk̂(u_t) + ω`
the live set at `head t` is `{s : rk̂(u_t) < rk̂(u_s) ≤ rk̂(u_t) + ω}` — **the left end strict**, so
the step `t` is not live at its own head and no `- 1` appears in the statement, where
`HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one` needs one. That set splits disjointly by
whether the right end is strict: strict is `𝒜(P̂)`, equality is `S(P̂)`, the latter because equal
ranks at two feet of columns inside the strip force the points equal
(`HJO.Paths.abovePointRank_injOn`), which is same column and vertical adjacency. Summing over `t`
counts each pair of each set once, fiberwise on the **first** coordinate where
`HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one` went on the second.

## References

Lemmas `HJO.Paths.card_leftLiveCols_eq_card_leftEastCols`,
`HJO.Paths.leftEastCount_eq_card_filter_fst_lt`, `HJO.Paths.sweepRight_add_leftEastCount` and
`HJO.Paths.sum_sweepWidth_head_eq_card_sweepAttack_add_card_sweepMarked`, using
`HJO.Paths.IsAboveDiagonal`, `HJO.Paths.northSteps`, `HJO.ParkingFunctions.abovePointRank`,
`HJO.Paths.sweptRegion`, `HJO.Paths.liveSteps`, `HJO.Paths.attackWindow`, `HJO.Paths.eventType`,
`HJO.Paths.LevelCrosses`, `HJO.Paths.sweepRight`, `HJO.Paths.leftEastCount`, `HJO.Paths.sweepWidth`,
`HJO.Paths.sweepAttack` and `HJO.Paths.sweepMarked`. Transcribing A. Mellit, *Toric braids and
`(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### The rank along a column and across an east step -/

/-- The above-diagonal rank is monotone up a column: `rk̂(x, k) ≤ rk̂(x, k')` for `k ≤ k'`, the
iterated `HJO.Paths.abovePointRank_add` with a nonnegative window. -/
theorem abovePointRank_le_of_snd_le (a b N x : ℕ) {k k' : ℕ} (h : k ≤ k') :
    ParkingFunctions.abovePointRank a b N x k ≤ ParkingFunctions.abovePointRank a b N x k' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [abovePointRank_add]
  have : (0 : ℤ) ≤ (d : ℤ) * (attackWindow a N : ℤ) := by positivity
  linarith

/-- Moving one step east changes the rank by `1 - b(aN+1)N`, whatever the ordinate. Both signs of
that quantity are used: it is negative once the rectangle has a column and a row, which is
`HJO.Paths.abovePointRank_eastRight_lt_eastLeft`, and at `b = 0` it is `+1`, which is what makes the
level line cross no east step there. -/
theorem abovePointRank_succ_fst (a b N x k : ℕ) :
    ParkingFunctions.abovePointRank a b N (x + 1) k
      = ParkingFunctions.abovePointRank a b N x k + 1 - ((a : ℤ) * N + 1) * N * b := by
  simp only [ParkingFunctions.abovePointRank]
  push_cast
  ring

/-- **A level of the rank inside a column is attained by a north step of that column.** If the rank
at height `h₀` of the column at `c` is at most `η` and the rank at height `h₁` exceeds it, some
height `k` with `h₀ ≤ k < h₁` has `rk̂(c, k) ≤ η < rk̂(c, k + 1)`.

Proved by induction on `h₁`, taking the largest height whose rank is still at most `η`. No division
is involved, and the window's positivity is not needed: the two hypotheses already force `h₀ < h₁`
through the monotonicity of the rank up the column. -/
private theorem exists_snd_of_abovePointRank_between (a b N c h₀ : ℕ) {η : ℤ} (h₁ : ℕ)
    (hlo : ParkingFunctions.abovePointRank a b N c h₀ ≤ η)
    (hhi : η < ParkingFunctions.abovePointRank a b N c h₁) :
    ∃ k, h₀ ≤ k ∧ k < h₁ ∧ ParkingFunctions.abovePointRank a b N c k ≤ η ∧
      η < ParkingFunctions.abovePointRank a b N c (k + 1) := by
  induction h₁ with
  | zero =>
    have := abovePointRank_le_of_snd_le a b N c (Nat.zero_le h₀)
    omega
  | succ n ih =>
    by_cases hn : ParkingFunctions.abovePointRank a b N c n ≤ η
    · refine ⟨n, ?_, Nat.lt_succ_self n, hn, hhi⟩
      by_contra hcon
      have := abovePointRank_le_of_snd_le a b N c (show n + 1 ≤ h₀ by omega)
      omega
    · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih (by omega)
      exact ⟨k, hk1, by omega, hk3, hk4⟩

/-! ### The two sets of columns to the left of a point -/

/-- **The columns strictly left of `P` carrying a north step live at `P`**: the columns
`n_1 < … < n_r`, as a `Finset` rather than as a listing. By
`HJO.Paths.eq_of_mem_liveSteps_of_fst_eq` each such column carries exactly one live north step, so
this has the same size as the set of those steps (`HJO.Paths.card_leftLiveCols`). -/
def leftLiveCols (y : Heights a b N) (P : ℕ × ℕ) : Finset ℕ :=
  {u ∈ liveSteps y P | u.1 < P.1}.image Prod.fst

/-- **The columns strictly left of `P` whose east step the level line through `P` crosses**: the
columns `m_1 < … < m_s`, the crossing condition `rk̂(R_e) ≤ rk̂(P) < rk̂(L_e)` of
`HJO.Paths.leftEastCount` with the endpoints `L_e = (c, ŷ_{c+1})` and `R_e = (c + 1, ŷ_{c+1})`
written out. East steps are indexed by their abscissa, one to each, so this is also the set
`HJO.Paths.leftEastCount` counts (`HJO.Paths.leftEastCount_eq_card_leftEastCols`). -/
def leftEastCols (y : Heights a b N) (P : ℕ × ℕ) : Finset ℕ :=
  {c ∈ range P.1 |
    ParkingFunctions.abovePointRank a b N (c + 1) (ht y (c + 1)) ≤
        ParkingFunctions.abovePointRank a b N P.1 P.2 ∧
      ParkingFunctions.abovePointRank a b N P.1 P.2 <
        ParkingFunctions.abovePointRank a b N c (ht y (c + 1))}

theorem mem_leftLiveCols {y : Heights a b N} {P : ℕ × ℕ} {c : ℕ} :
    c ∈ leftLiveCols y P ↔ c < P.1 ∧ ∃ k, (c, k) ∈ liveSteps y P := by
  simp only [leftLiveCols, mem_image, mem_filter]
  constructor
  · rintro ⟨u, ⟨hu, hlt⟩, rfl⟩
    exact ⟨hlt, u.2, hu⟩
  · rintro ⟨hlt, k, hk⟩
    exact ⟨(c, k), ⟨hk, hlt⟩, rfl⟩

theorem mem_leftEastCols {y : Heights a b N} {P : ℕ × ℕ} {c : ℕ} :
    c ∈ leftEastCols y P ↔ c < P.1 ∧
      ParkingFunctions.abovePointRank a b N (c + 1) (ht y (c + 1)) ≤
          ParkingFunctions.abovePointRank a b N P.1 P.2 ∧
        ParkingFunctions.abovePointRank a b N P.1 P.2 <
          ParkingFunctions.abovePointRank a b N c (ht y (c + 1)) := by
  simp only [leftEastCols, mem_filter, mem_range]

/-- **The columns to the left with a live step are as many as those live steps.** The bijection is
`u ↦ x(u)`, injective on the live steps by `HJO.Paths.eq_of_mem_liveSteps_of_fst_eq`. -/
theorem card_leftLiveCols (y : Heights a b N) (P : ℕ × ℕ) :
    #(leftLiveCols y P) = #{u ∈ liveSteps y P | u.1 < P.1} := by
  rw [leftLiveCols, card_image_of_injOn]
  intro u hu v hv huv
  exact eq_of_mem_liveSteps_of_fst_eq (mem_filter.1 (mem_coe.1 hu)).1
    (mem_filter.1 (mem_coe.1 hv)).1 huv

/-- **`a^*_{P̂}(P)` counts the columns to the left whose east step is crossed.** The east steps with
`x(L_e) < x(P)` are exactly those of abscissa below `x(P)`, and `x(P) ≤ aN`, so the bound
`s < aN` of `HJO.Paths.leftEastCount` is implied by `s < x(P)` and drops out. -/
theorem leftEastCount_eq_card_leftEastCols {y : Heights a b N} {P : ℕ × ℕ} (hx : P.1 ≤ a * N) :
    leftEastCount y P = #(leftEastCols y P) := by
  unfold leftEastCount
  congr 1
  ext c
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · obtain ⟨-, h1, h2, h3⟩ := mem_filter.1 hc
    exact mem_leftEastCols.2 ⟨h3, h1, h2⟩
  · obtain ⟨h3, h1, h2⟩ := mem_leftEastCols.1 hc
    exact mem_filter.2 ⟨mem_range.2 (by omega), h1, h2, h3⟩

/-! ### The alternation -/

/-- A column strictly left of `P` carries a north step live at `P` exactly when the bottom of that
column is weakly and its top strictly outranked by `P` — the `¬ε` at the start of the
block and `ε` at its end.

One direction is the monotonicity of the rank up the column; the other locates the step with
`HJO.Paths.exists_snd_of_abovePointRank_between`. -/
theorem mem_leftLiveCols_iff {y : Heights a b N} {P : ℕ × ℕ} {c : ℕ} (hc : c < P.1)
    (hx : P.1 ≤ a * N) :
    c ∈ leftLiveCols y P ↔
      ParkingFunctions.abovePointRank a b N c (ht y c) ≤
          ParkingFunctions.abovePointRank a b N P.1 P.2 ∧
        ParkingFunctions.abovePointRank a b N P.1 P.2 <
          ParkingFunctions.abovePointRank a b N c (ht y (c + 1)) := by
  have hcN : c < a * N := by omega
  rw [mem_leftLiveCols]
  constructor
  · rintro ⟨-, k, hk⟩
    simp only [liveSteps, mem_filter] at hk
    obtain ⟨hkn, hr1, hr2⟩ := hk
    obtain ⟨-, hlo', hhi'⟩ := mem_northSteps_iff.1 hkn
    have hlo : ht y c ≤ k := hlo'
    have hhi : k + 1 ≤ ht y (c + 1) := hhi'
    refine ⟨le_trans (abovePointRank_le_of_snd_le a b N c hlo) hr1, ?_⟩
    have hup := abovePointRank_le_of_snd_le a b N c hhi
    rw [abovePointRank_succ] at hup
    omega
  · rintro ⟨hlo, hhi⟩
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
      exists_snd_of_abovePointRank_between a b N c (ht y c) (ht y (c + 1)) hlo hhi
    rw [abovePointRank_succ] at hk4
    refine ⟨hc, k, ?_⟩
    simp only [liveSteps, mem_filter]
    exact ⟨mem_northSteps_iff.2 ⟨hcN, hk1, hk2⟩, hk3, hk4⟩

/-- Splitting a count below `c + 1` into the count below `c` and the membership of `c`. -/
private theorem card_filter_lt_succ (s : Finset ℕ) (c : ℕ) :
    #{d ∈ s | d < c + 1} = #{d ∈ s | d < c} + (if c ∈ s then 1 else 0) := by
  have hsplit : {d ∈ s | d < c + 1} = {d ∈ s | d < c} ∪ {d ∈ s | d = c} := by
    ext d
    simp only [mem_union, mem_filter]
    constructor
    · rintro ⟨hd, hlt⟩
      rcases Nat.lt_or_ge d c with h | h
      · exact Or.inl ⟨hd, h⟩
      · exact Or.inr ⟨hd, by omega⟩
    · rintro (⟨hd, h⟩ | ⟨hd, h⟩) <;> exact ⟨hd, by omega⟩
  have hdisj : Disjoint {d ∈ s | d < c} {d ∈ s | d = c} := by
    refine disjoint_left.2 fun d hd hd' => ?_
    have h1 := (mem_filter.1 hd).2
    have h2 := (mem_filter.1 hd').2
    omega
  have heq : #{d ∈ s | d = c} = if c ∈ s then 1 else 0 := by
    split_ifs with hcs
    · have hset : {d ∈ s | d = c} = {c} := by
        ext d
        simp only [mem_filter, mem_singleton]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hcs, h⟩⟩
      rw [hset, card_singleton]
    · rw [card_eq_zero, filter_eq_empty_iff]
      exact fun {d} hd h => hcs (h ▸ hd)
  rw [hsplit, card_union_of_disjoint hdisj, heq]

/-- **The telescoping identity.** For every `c₀ ≤ x` the live columns below `c₀` outnumber the
crossed columns below `c₀` by `1` exactly when the bottom of the column at `c₀` outranks `P`.

This is the whole content of `HJO.Paths.card_leftLiveCols_eq_card_leftEastCols`. The induction step
is the identity `[c live] + [A c] = [B c] = [c crossed] + [A (c+1)]`, both readings of `B c` being
disjoint splittings because `A c → B c` (the rank rises up a column) and `A (c+1) → B c` (the rank
falls along an east step, which is where `0 < b` is spent). -/
private theorem card_leftLiveCols_lt (hb : 0 < b) {y : Heights a b N} (hy : IsAboveDiagonal y)
    {P : ℕ × ℕ} (hP : P ∈ sweptRegion y) (c : ℕ) (hc : c ≤ P.1) :
    #{d ∈ leftLiveCols y P | d < c}
      = #{d ∈ leftEastCols y P | d < c}
        + (if ParkingFunctions.abovePointRank a b N P.1 P.2 <
              ParkingFunctions.abovePointRank a b N c (ht y c) then 1 else 0) := by
  induction c with
  | zero =>
    have hzero : ¬ ParkingFunctions.abovePointRank a b N P.1 P.2 <
        ParkingFunctions.abovePointRank a b N 0 (ht y 0) := by
      obtain ⟨-, hdiag, -⟩ := mem_sweptRegion.1 hP
      have hd : (b : ℤ) * P.1 ≤ (a : ℤ) * P.2 := by exact_mod_cast hdiag
      have hx0 : (0 : ℤ) ≤ (P.1 : ℤ) := Int.natCast_nonneg _
      have hM : (0 : ℤ) ≤ ((a : ℤ) * N + 1) * N := by positivity
      simp only [ParkingFunctions.abovePointRank, hy.1, not_lt]
      push_cast
      nlinarith
    have h1 : {d ∈ leftLiveCols y P | d < 0} = ∅ :=
      filter_eq_empty_iff.2 fun {d} _ => by omega
    have h2 : {d ∈ leftEastCols y P | d < 0} = ∅ :=
      filter_eq_empty_iff.2 fun {d} _ => by omega
    rw [h1, h2, card_empty]
    split_ifs
    omega
  | succ c ih =>
    have hcP : c < P.1 := by omega
    have hcN : c < a * N := by
      have := (mem_sweptRegion.1 hP).1
      omega
    have h0 : 0 < a * N := by omega
    have hAB : ParkingFunctions.abovePointRank a b N c (ht y c) ≤
        ParkingFunctions.abovePointRank a b N c (ht y (c + 1)) :=
      abovePointRank_le_of_snd_le a b N c (ht_mono hy.2.2.1 (Nat.le_succ c))
    have hEast := abovePointRank_eastRight_lt_eastLeft y c hb h0
    simp only [eastLeft, eastRight] at hEast
    have hlive := mem_leftLiveCols_iff (y := y) (P := P) (c := c) hcP (mem_sweptRegion.1 hP).1
    have heast := mem_leftEastCols (y := y) (P := P) (c := c)
    rw [card_filter_lt_succ, card_filter_lt_succ, ih (by omega)]
    simp only [hlive, heast]
    split_ifs <;> omega

/-- Both column sets are empty when the rectangle has no row: there is no north step at all, and the
rank *rises* by one along an east step, so no level line crosses one. -/
private theorem leftCols_eq_empty_of_b_eq_zero {y : Heights a b N} (hb : b = 0) (P : ℕ × ℕ) :
    leftLiveCols y P = ∅ ∧ leftEastCols y P = ∅ := by
  constructor
  · refine eq_empty_iff_forall_notMem.2 fun c hc => ?_
    obtain ⟨-, k, hk⟩ := mem_leftLiveCols.1 hc
    obtain ⟨-, hlo', hhi'⟩ := mem_northSteps_iff.1 (liveSteps_subset y P hk)
    have hlo : ht y c ≤ k := hlo'
    have hhi : k < ht y (c + 1) := hhi'
    have hbN : b * N = 0 := by simp [hb]
    have h1 : ht y c ≤ b * N := ht_le_mul y c
    have h2 : ht y (c + 1) ≤ b * N := ht_le_mul y (c + 1)
    rw [hbN] at h1 h2
    omega
  · refine eq_empty_iff_forall_notMem.2 fun c hc => ?_
    obtain ⟨-, h1, h2⟩ := mem_leftEastCols.1 hc
    have hbz : (b : ℤ) = 0 := by exact_mod_cast hb
    have h3 := abovePointRank_succ_fst a b N c (ht y (c + 1))
    rw [hbz, mul_zero, sub_zero] at h3
    omega

/-- **The live north steps and the crossed east steps to the left of a swept point interleave.**
Writing `n_1 < … < n_r` for the columns `c < x` carrying a north step live at `P` and
`m_1 < … < m_s` for the columns `c < x` whose east step the level line through `P` crosses, `r = s`
and `n_1 ≤ m_1 < n_2 ≤ m_2 < … < n_r ≤ m_r`.

The interleaving is carried as the two counting inequalities equivalent to that display; see the
module docstring, which also gives the telescoping identity the whole proof consists of and explains
why the list `V_0, …, V_T` is never built.

Type `D` is admitted where the statement is usually written for `A`, `B` or `C` — the proof reads
only `ŷ_x ≤ y` — and `0 < b` is not carried, the case `b = 0` having both column sets empty. -/
@[hjo "lem_swb_crossing_alternate"]
theorem card_leftLiveCols_eq_card_leftEastCols {y : Heights a b N} (hy : IsAboveDiagonal y)
    {P : ℕ × ℕ} (hP : P ∈ sweptRegion y) (hE : eventType y P ≠ EventType.E) :
    #(leftLiveCols y P) = #(leftEastCols y P) ∧
      (∀ c, #{d ∈ leftEastCols y P | d < c} ≤ #{d ∈ leftLiveCols y P | d < c}) ∧
      (∀ c, #{d ∈ leftLiveCols y P | d ≤ c} ≤ #{d ∈ leftEastCols y P | d < c} + 1) := by
  rcases Nat.eq_zero_or_pos b with hb0 | hb
  · obtain ⟨h1, h2⟩ := leftCols_eq_empty_of_b_eq_zero (y := y) hb0 P
    rw [h1, h2]
    simp
  -- the bottom of the column at `x` is weakly outranked by `P`, its event type not being `E`
  have htop : ¬ ParkingFunctions.abovePointRank a b N P.1 P.2 <
      ParkingFunctions.abovePointRank a b N P.1 (ht y P.1) := by
    have hE' : ¬ P.2 < ht y P.1 := fun h => hE (eventType_eq_E_iff.2 h)
    rw [not_lt]
    exact abovePointRank_le_of_snd_le a b N P.1 (Nat.le_of_not_lt hE')
  have hsat : ∀ s : Finset ℕ, (∀ d ∈ s, d < P.1) → ∀ c, P.1 ≤ c → {d ∈ s | d < c} = s :=
    fun s hs c hcx => filter_eq_self.2 fun d hd => lt_of_lt_of_le (hs d hd) hcx
  have hliveP : ∀ d ∈ leftLiveCols y P, d < P.1 := fun d hd => (mem_leftLiveCols.1 hd).1
  have heastP : ∀ d ∈ leftEastCols y P, d < P.1 := fun d hd => (mem_leftEastCols.1 hd).1
  have hcardP := card_leftLiveCols_lt hb hy hP P.1 le_rfl
  rw [hsat _ hliveP P.1 le_rfl, hsat _ heastP P.1 le_rfl] at hcardP
  have hcard : #(leftLiveCols y P) = #(leftEastCols y P) := by
    split_ifs at hcardP
    omega
  refine ⟨hcard, fun c => ?_, fun c => ?_⟩
  · rcases Nat.lt_or_ge c (P.1 + 1) with hcx | hcx
    · have h := card_leftLiveCols_lt hb hy hP c (by omega)
      split_ifs at h <;> omega
    · rw [hsat _ hliveP c (by omega), hsat _ heastP c (by omega)]
      omega
  · have hsucc : {d ∈ leftLiveCols y P | d ≤ c} = {d ∈ leftLiveCols y P | d < c + 1} :=
      filter_congr fun d _ => by omega
    rw [hsucc]
    rcases Nat.lt_or_ge c P.1 with hcx | hcx
    · have h1 := card_leftLiveCols_lt hb hy hP (c + 1) (by omega)
      have h2 : #{d ∈ leftEastCols y P | d < c + 1}
          = #{d ∈ leftEastCols y P | d < c}
            + (if c < P.1 ∧
                ParkingFunctions.abovePointRank a b N (c + 1) (ht y (c + 1)) ≤
                    ParkingFunctions.abovePointRank a b N P.1 P.2 ∧
                  ParkingFunctions.abovePointRank a b N P.1 P.2 <
                    ParkingFunctions.abovePointRank a b N c (ht y (c + 1)) then 1 else 0) := by
        rw [card_filter_lt_succ]
        simp only [mem_leftEastCols]
      split_ifs at h1 h2 <;> omega
    · rw [hsat _ hliveP (c + 1) (by omega), hsat _ heastP c (by omega)]
      omega

/-! ### The live east-step count to the left -/

/-- **`a^*_{P̂}(P)` is the number of live north steps of column below that of `P`.**

The east steps with `x(L_e) < x(P)` are one for each abscissa below `x(P)`, so `a^*_{P̂}(P)` is the
size of the `{m_1, …, m_s}`; `HJO.Paths.card_leftLiveCols_eq_card_leftEastCols` gives `s = r`, and
`HJO.Paths.eq_of_mem_liveSteps_of_fst_eq` turns the `r` columns back into `r` steps. Only `r = s` is
used, not the interleaving. -/
@[hjo "lem_swb_left_east_north"]
theorem leftEastCount_eq_card_filter_fst_lt {y : Heights a b N} (hy : IsAboveDiagonal y)
    {P : ℕ × ℕ} (hP : P ∈ sweptRegion y) (hE : eventType y P ≠ EventType.E) :
    leftEastCount y P = #{u ∈ liveSteps y P | u.1 < P.1} := by
  rw [leftEastCount_eq_card_leftEastCols (mem_sweptRegion.1 hP).1, ← card_leftLiveCols,
    (card_leftLiveCols_eq_card_leftEastCols hy hP hE).1]

/-! ### The balance at a type-`A` event -/

/-- **The balance at a type-`A` event**: `a_{P̂}(P) + a^*_{P̂}(P) = k_{P̂}(P)`.

Split the live steps by whether their column is greater than, equal to, or smaller than `x`. The
first part is `a_{P̂}(P)` by `HJO.Paths.sweepRight` and the third is `a^*_{P̂}(P)` by
`HJO.Paths.leftEastCount_eq_card_filter_fst_lt`. The middle part is empty: by
`HJO.Paths.mem_liveSteps_iff_eq_of_fst_eq` a live north step of column `x` has foot `P`, and `P` is
no north step, its event type being `A` rather than `B` or `C`
(`HJO.Paths.mem_northSteps_iff_eventType`). -/
@[hjo "lem_swb_type_a_balance"]
theorem sweepRight_add_leftEastCount {y : Heights a b N} (hy : IsAboveDiagonal y) {P : ℕ × ℕ}
    (hP : P ∈ sweptRegion y) (hA : eventType y P = EventType.A) :
    sweepRight y P + leftEastCount y P = sweepWidth y P := by
  have hE : eventType y P ≠ EventType.E := by rw [hA]; simp
  have hmid : {u ∈ liveSteps y P | ¬ P.1 < u.1} = {u ∈ liveSteps y P | u.1 < P.1} := by
    refine filter_congr fun u hu => ?_
    simp only [not_lt]
    refine ⟨fun hle => lt_of_le_of_ne hle fun hcol => ?_, fun h => by omega⟩
    have hun : u ∈ northSteps y := liveSteps_subset y P hu
    have huP : u = P := (mem_liveSteps_iff_eq_of_fst_eq hun hcol).1 hu
    rcases (mem_northSteps_iff_eventType hP).1 (huP ▸ hun) with h | h <;> rw [hA] at h <;> simp at h
  rw [sweepWidth, sweepRight, leftEastCount_eq_card_filter_fst_lt hy hP hE, ← hmid]
  exact card_filter_add_card_filter_not _

/-! ### The widths summed over the heads of the north steps -/

/-- **The live set at the head of a north step.** By `abovePointRank_succ` the head of `t` outranks
its foot by the window, so a step `s` is live at `head t` exactly when
`rk̂(u_t) < rk̂(u_s) ≤ rk̂(u_t) + ω` — the left end strict, so `t` is not live at its own head. The
right end is strict for the steps attacking `t` and an equality for the marked pair above `t`, and
nothing else can occur. -/
private theorem liveSteps_stepHead {y : Heights a b N} (hy : IsAboveDiagonal y)
    (t : Fin (b * N)) :
    liveSteps y ((stepFoot y t).1, (stepFoot y t).2 + 1)
      = ({s ∈ (univ : Finset (Fin (b * N))) | (t, s) ∈ sweepAttack y}
          ∪ {s ∈ (univ : Finset (Fin (b * N))) | (t, s) ∈ sweepMarked y}).image (stepFoot y) := by
  have h0 : 0 < a * N := mul_pos_of_isAboveDiagonal hy t
  have ha : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have hω : (0 : ℤ) < (attackWindow a N : ℤ) := by
    exact_mod_cast attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
  have hhead : ParkingFunctions.abovePointRank a b N (stepFoot y t).1 ((stepFoot y t).2 + 1)
      = stepRank y t + attackWindow a N := abovePointRank_succ a b N _ _
  -- the marked pairs above `t` are exactly the steps of rank `rk̂(u_t) + ω`
  have hmarked : ∀ s : Fin (b * N),
      stepRank y s = stepRank y t + attackWindow a N ↔ (t, s) ∈ sweepMarked y := by
    intro s
    rw [mem_sweepMarked]
    constructor
    · intro heq
      have h1 : ParkingFunctions.abovePointRank a b N
            (ParkingFunctions.aboveColumn y (s : ℕ)) (s : ℕ)
          = ParkingFunctions.abovePointRank a b N
            (ParkingFunctions.aboveColumn y (t : ℕ)) ((t : ℕ) + 1) := by
        rw [abovePointRank_succ]
        exact heq
      obtain ⟨hc, hk⟩ := abovePointRank_injOn ha hN
        (ParkingFunctions.aboveColumn_le y (s : ℕ)) (ParkingFunctions.aboveColumn_le y (t : ℕ)) h1
      exact ⟨hc, hk⟩
    · rintro ⟨hc, hk⟩
      rw [stepRank, stepRank, hc, hk, abovePointRank_succ]
  ext u
  simp only [liveSteps, mem_filter, mem_image, mem_union, mem_univ, true_and,
    northSteps_eq_image hy, hhead]
  constructor
  · rintro ⟨hu, hu1, hu2⟩
    obtain ⟨s, rfl⟩ := hu
    rw [← stepRank_eq_abovePointRank_stepFoot] at hu1 hu2
    refine ⟨s, ?_, rfl⟩
    rcases lt_or_eq_of_le hu1 with hlt | heq
    · have hts : stepRank y t < stepRank y s := by omega
      exact Or.inl (mem_sweepAttack.2 ⟨hts, hlt⟩)
    · exact Or.inr ((hmarked s).1 heq)
  · rintro ⟨s, hs, rfl⟩
    rw [← stepRank_eq_abovePointRank_stepFoot]
    refine ⟨⟨s, rfl⟩, ?_, ?_⟩
    · rcases hs with h | h
      · have h1 : stepRank y s < stepRank y t + attackWindow a N := (mem_sweepAttack.1 h).2
        omega
      · rw [(hmarked s).2 h]
    · rcases hs with h | h
      · have h1 : stepRank y t < stepRank y s := (mem_sweepAttack.1 h).1
        omega
      · rw [(hmarked s).2 h]; omega

/-- **The width at the head of a north step splits into the attacking pairs and the marked pair.**
The two conditions are incompatible, one asking for a strict and the other for a non-strict
comparison of `rk̂(u_s)` with `rk̂(u_t) + ω`. -/
private theorem sweepWidth_stepHead {y : Heights a b N} (hy : IsAboveDiagonal y)
    (t : Fin (b * N)) :
    sweepWidth y ((stepFoot y t).1, (stepFoot y t).2 + 1)
      = #{s ∈ (univ : Finset (Fin (b * N))) | (t, s) ∈ sweepAttack y}
        + #{s ∈ (univ : Finset (Fin (b * N))) | (t, s) ∈ sweepMarked y} := by
  have hdisj : Disjoint {s ∈ (univ : Finset (Fin (b * N))) | (t, s) ∈ sweepAttack y}
      {s ∈ (univ : Finset (Fin (b * N))) | (t, s) ∈ sweepMarked y} := by
    refine disjoint_left.2 fun s hs hs' => ?_
    have h1 := mem_sweepAttack.1 (mem_filter.1 hs).2
    have h2 := (mem_filter.1 hs').2
    rw [mem_sweepMarked] at h2
    rw [stepRank, stepRank, h2.1, h2.2, abovePointRank_succ, ← stepRank] at h1
    omega
  rw [sweepWidth, liveSteps_stepHead hy t, card_image_of_injective _ (stepFoot_injective y),
    card_union_of_disjoint hdisj]

/-- **`∑_{P of type A or C} k_{P̂}(P) = #𝒜(P̂) + #S(P̂)`.**
`HJO.Paths.sum_sweepWidth_head_eq_card_sweepAttack_add_card_sweepMarked`.

The type-`A`-or-`C` points are the heads of the north steps (`HJO.Paths.isSweepHead_iff_eventType`);
at the head of `t` the live set splits into the steps attacking `t` and the marked pair above `t`,
and summing over `t` counts each pair of `𝒜(P̂)` and each pair of `S(P̂)` once by its first
coordinate. No `- 1` appears because `t` itself is not live at its own head: the window puts its
foot's rank strictly below. -/
@[hjo "lem_swb_head_sum"]
theorem sum_sweepWidth_head_eq_card_sweepAttack_add_card_sweepMarked {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.A ∨ eventType y P = EventType.C},
        sweepWidth y P = #(sweepAttack y) + #(sweepMarked y) := by
  have hinj : ∀ t : Fin (b * N), ∀ t' : Fin (b * N),
      ((stepFoot y t).1, (stepFoot y t).2 + 1) = ((stepFoot y t').1, (stepFoot y t').2 + 1) →
        t = t' := by
    intro t t' h
    have := congrArg Prod.snd h
    simp only [stepFoot_snd] at this
    exact Fin.val_injective (by omega)
  have hfilter : {P ∈ sweptRegion y | eventType y P = EventType.A ∨ eventType y P = EventType.C}
      = (univ : Finset (Fin (b * N))).image
        fun t => ((stepFoot y t).1, (stepFoot y t).2 + 1) := by
    ext P
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨hP, hev⟩
      obtain ⟨u, hu, huP⟩ := (isSweepHead_iff_eventType hy hP).2 hev
      rw [northSteps_eq_image hy, mem_image] at hu
      obtain ⟨t, -, rfl⟩ := hu
      exact ⟨t, huP⟩
    · rintro ⟨t, rfl⟩
      have hmem : stepFoot y t ∈ northSteps y := by
        rw [northSteps_eq_image hy]
        exact mem_image_of_mem _ (mem_univ t)
      have hsw := (mem_sweptRegion_of_mem_northSteps hy hmem).2
      exact ⟨hsw, (isSweepHead_iff_eventType hy hsw).1 ⟨stepFoot y t, hmem, rfl⟩⟩
  rw [hfilter, Finset.sum_image fun t _ t' _ h => hinj t t' h]
  have hattack : #(sweepAttack y)
      = ∑ t : Fin (b * N), #{s ∈ (univ : Finset (Fin (b * N))) | (t, s) ∈ sweepAttack y} := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
      (t := (univ : Finset (Fin (b * N)))) fun p _ => mem_univ p.1]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show {p ∈ sweepAttack y | p.1 = t}
        = {s ∈ (univ : Finset (Fin (b * N))) | (t, s) ∈ sweepAttack y}.image fun s => (t, s) from by
      ext p
      simp only [mem_filter, mem_image, mem_univ, true_and]
      exact ⟨fun h => ⟨p.2, h.2 ▸ h.1, by rw [← h.2]⟩, fun ⟨s, hs, hp⟩ => ⟨hp ▸ hs, by rw [← hp]⟩⟩,
      card_image_of_injective _ fun s s' h => by simpa using congrArg Prod.snd h]
  have hmarked : #(sweepMarked y)
      = ∑ t : Fin (b * N), #{s ∈ (univ : Finset (Fin (b * N))) | (t, s) ∈ sweepMarked y} := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
      (t := (univ : Finset (Fin (b * N)))) fun p _ => mem_univ p.1]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show {p ∈ sweepMarked y | p.1 = t}
        = {s ∈ (univ : Finset (Fin (b * N))) | (t, s) ∈ sweepMarked y}.image fun s => (t, s) from by
      ext p
      simp only [mem_filter, mem_image, mem_univ, true_and]
      exact ⟨fun h => ⟨p.2, h.2 ▸ h.1, by rw [← h.2]⟩, fun ⟨s, hs, hp⟩ => ⟨hp ▸ hs, by rw [← hp]⟩⟩,
      card_image_of_injective _ fun s s' h => by simpa using congrArg Prod.snd h]
  rw [hattack, hmarked, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => sweepWidth_stepHead hy t

end HJO.Paths
