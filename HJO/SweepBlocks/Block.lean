/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepEventCounts
public import HJO.SweepBlocks.PositionStep
public meta import HJO.Attr

/-! # The word blocks of the events, and that they partition the step word

To each event `P` of the sweep one attaches the block
`Blk_{P̂}(P) = {r : pos_{P̂}(P) - δ < r ≤ pos_{P̂}(P)}` of word positions, with `δ = 2` at a
type-`C` event and `δ = 1` otherwise, and two things are proved about the family: the blocks
descend with the rank, and they partition `{1, …, 2bN}`.

**Neither proof needs the rank-order listing `Q_1, …, Q_L`.** The direct argument runs both
through it — `HJO.Paths.lt_of_mem_wordBlock_of_rank_lt` by `ϖ_{l'} ≤ ϖ_{l+1} = ϖ_l - δ_l` and
`HJO.Paths.wordBlock_biUnion_eq` by telescoping the same recursion. What actually drives them is
that `δ` is itself a count:

`δ_P` is the number of north steps whose **foot** is `P` plus the number whose **head** is `P`
(`HJO.Paths.blockSize_eq_card_feet_add_card_heads`) — `1 + 0` at type `B`, `0 + 1` at type `A`,
`1 + 1` at type `C`. Both summands of `HJO.Paths.wordPosition` are counts over the north steps,
monotone in the rank, and each *gains* its indicator when the rank passes `P`. So
`pos(Q) + δ_P ≤ pos(P)` for **every** swept `Q` of smaller rank, with no adjacency hypothesis
(`HJO.Paths.wordPosition_add_blockSize_le`), and that inequality is
`HJO.Paths.lt_of_mem_wordBlock_of_rank_lt` outright. Disjointness follows from it, and the union is
then a cardinality count: the blocks are disjoint subsets of `{1, …, 2bN}` of total size
`#A + #B + 2#C`, which is `2bN` by `HJO.Paths.card_filter_eventType_A` — `#A = #B = c` and
`#C + c = bN`, with no truncated subtraction anywhere.

## Main definitions

* `HJO.Paths.blockSize`: the `δ`, `2` at type `C` and `1` otherwise.
* `HJO.Paths.wordBlock`: the word block `Blk_{P̂}(P)` (`HJO.Paths.wordBlock`).
* `HJO.Paths.eventPoints`: the swept points of event type `A`, `B` or `C` — the index set of the
  family, the `{Q_1, …, Q_L}` as a `Finset`.

## Main results

* `HJO.Paths.wordPosition_add_blockSize_le`: `pos(Q) + δ_P ≤ pos(P)` whenever `rk̂(Q) < rk̂(P)`.
* `HJO.Paths.lt_of_mem_wordBlock_of_rank_lt`.
* `HJO.Paths.wordBlock_biUnion_eq` and `HJO.Paths.disjoint_wordBlock`:
  `HJO.Paths.wordBlock_biUnion_eq`.
* `HJO.Paths.card_wordBlock`: the block at an event has exactly `δ` elements.

## Implementation notes

**The truncated subtraction is real and is discharged.** `wordBlock` is a `Finset ℕ` given by
`Finset.Ioc (pos - δ) pos`, where the block is usually written `{r ∈ ℤ : pos - δ < r ≤ pos}`. The
two agree only when `δ ≤ pos`, and that is `HJO.Paths.blockSize_le_wordPosition`, proved at every
event from the same indicator inequality: a type-`C` point is both a foot and a head, so both counts
of `pos` are at least `1` there and `pos ≥ 2 = δ`; a type-`A` or type-`B` point contributes to one
count and `pos ≥ 1 = δ`. Off the events the bound can fail — at a type-`D` or type-`E` point of
position `0` the `Finset.Ioc` is empty where the integer set has one element — so every statement
below that reads the lower endpoint carries the event hypothesis.

`HJO.Paths.wordBlock_biUnion_eq` is stated with `0 < a` and `0 < N`, which are usually left
implicit. They are what makes the above-diagonal rank injective on the strip
(`HJO.Paths.abovePointRank_injOn`), hence what makes two *distinct* events have distinct ranks and
so disjoint blocks. At `a * N = 0` above-diagonality forces `b * N = 0` and both sides of the
partition are empty, so nothing is lost; the hypotheses are not carried through the degenerate case
because `HJO.Paths.wordPosition_of_rankAdjacent` is stated on the same footing.

## References

This file formalises the definition `HJO.Paths.wordBlock` and the lemmas
`HJO.Paths.wordBlock_biUnion_eq` and `HJO.Paths.lt_of_mem_wordBlock_of_rank_lt`, using
`HJO.Paths.IsAboveDiagonal`, `HJO.ParkingFunctions.abovePointRank`, `HJO.Paths.sweptRegion`,
`HJO.Paths.eventType`, `HJO.Paths.wordPosition` and `HJO.Paths.card_filter_eventType_A`. A. Mellit,
*Toric braids and `(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### The block size, as a count -/

/-- The `δ`: the length of the word block at an event, `2` at a type-`C` event and `1`
otherwise. `HJO.Paths.blockSize_eq_card_feet_add_card_heads` is the reading that drives everything
below — at an event `δ` is the number of north steps beginning at the point plus the number ending
there. -/
def blockSize (y : Heights a b N) (P : ℕ × ℕ) : ℕ :=
  if eventType y P = EventType.C then 2 else 1

/-- **The word block of an event.** `Blk_{P̂}(P) = {r : pos_{P̂}(P) - δ < r ≤ pos_{P̂}(P)}`, the
half-open interval of word positions the sweep crosses at `P`, of length `δ = 2` at a type-`C`
event and `δ = 1` otherwise.

The subtraction is the `ℕ` one, where the set is cut out of `ℤ`; the two agree exactly
when `δ ≤ pos`, which is `HJO.Paths.blockSize_le_wordPosition` at every point of event type `A`,
`B` or `C`. Total in `P`, where the block is usually defined only for `P` of one of those three
types. -/
@[hjo "def_sweep_block"]
def wordBlock (y : Heights a b N) (P : ℕ × ℕ) : Finset ℕ :=
  Finset.Ioc (wordPosition y P - blockSize y P) (wordPosition y P)

@[simp]
theorem mem_wordBlock {y : Heights a b N} {P : ℕ × ℕ} {r : ℕ} :
    r ∈ wordBlock y P ↔ wordPosition y P - blockSize y P < r ∧ r ≤ wordPosition y P :=
  Finset.mem_Ioc

/-- The block size is positive. -/
theorem blockSize_pos (y : Heights a b N) (P : ℕ × ℕ) : 0 < blockSize y P := by
  rw [blockSize]; split_ifs <;> omega

/-- **At an event the block size is the number of north steps beginning at the point plus the
number ending there.** `1 + 0` at type `B`, `0 + 1` at type `A`, `1 + 1` at type `C`: a north step
is met at its foot, which is a type-`B` or type-`C` point
(`HJO.Paths.mem_northSteps_iff_eventType`), and finished at its head, which is a type-`A` or
type-`C` point (`HJO.Paths.isSweepHead_iff_eventType`). -/
theorem blockSize_eq_card_feet_add_card_heads {y : Heights a b N} (hy : IsAboveDiagonal y)
    {P : ℕ × ℕ} (hP : P ∈ sweptRegion y) (hD : eventType y P ≠ EventType.D)
    (hE : eventType y P ≠ EventType.E) :
    blockSize y P = #{u ∈ northSteps y | u = P} + #{u ∈ northSteps y | (u.1, u.2 + 1) = P} := by
  have hfoot := mem_northSteps_iff_eventType (y := y) (P := P) hP
  have hhead := isSweepHead_iff_eventType hy hP
  rw [blockSize]
  cases hev : eventType y P with
  | A =>
    rw [card_feet_of_notMem fun h => by simpa [hev] using hfoot.1 h,
      card_heads_of_isSweepHead (hhead.2 (Or.inl hev))]
    simp only [reduceCtorEq, reduceIte]
  | B =>
    rw [card_feet_of_mem (hfoot.2 (Or.inl hev)),
      card_heads_of_not_isSweepHead fun h => by simpa [hev] using hhead.1 h]
    simp only [reduceCtorEq, reduceIte]
  | C =>
    rw [card_feet_of_mem (hfoot.2 (Or.inr hev)),
      card_heads_of_isSweepHead (hhead.2 (Or.inr hev))]
    simp only [reduceIte]
  | D => exact absurd hev hD
  | E => exact absurd hev hE

/-! ### The two indicator inequalities -/

/-- **The word position at a point is at least the number of north steps beginning or ending
there.** A north step with foot `P` contributes to the first count of `HJO.Paths.wordPosition`,
because `rk̂(P) ≤ rk̂(P)`; a north step with head `P` contributes to the second, its foot having
rank `rk̂(P) - ω`. -/
theorem card_feet_add_card_heads_le_wordPosition (y : Heights a b N) (P : ℕ × ℕ) :
    #{u ∈ northSteps y | u = P} + #{u ∈ northSteps y | (u.1, u.2 + 1) = P} ≤ wordPosition y P := by
  have h1 : {u ∈ northSteps y | u = P} ⊆ {u ∈ northSteps y |
      ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
        ParkingFunctions.abovePointRank a b N P.1 P.2} := by
    refine monotone_filter_right _ fun u _ hu => ?_
    rw [hu]
  have h2 : {u ∈ northSteps y | (u.1, u.2 + 1) = P} ⊆ {u ∈ northSteps y |
      ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N ≤
        ParkingFunctions.abovePointRank a b N P.1 P.2} := by
    refine monotone_filter_right _ fun u _ hu => ?_
    rw [← abovePointRank_succ a b N u.1 u.2]
    have e1 : P.1 = u.1 := by rw [← hu]
    have e2 : P.2 = u.2 + 1 := by rw [← hu]
    rw [e1, e2]
  rw [wordPosition]
  exact Nat.add_le_add (card_le_card h1) (card_le_card h2)

/-- **At an event the block does not run off the left end of the word.** This is the fact that makes
`HJO.Paths.wordBlock` — an `ℕ`-valued `Finset.Ioc` — the set of integers, and not a
truncated shadow of it. -/
theorem blockSize_le_wordPosition {y : Heights a b N} (hy : IsAboveDiagonal y) {P : ℕ × ℕ}
    (hP : P ∈ sweptRegion y) (hD : eventType y P ≠ EventType.D)
    (hE : eventType y P ≠ EventType.E) : blockSize y P ≤ wordPosition y P := by
  rw [blockSize_eq_card_feet_add_card_heads hy hP hD hE]
  exact card_feet_add_card_heads_le_wordPosition y P

/-- **At an event the block has exactly `δ` elements.** -/
theorem card_wordBlock {y : Heights a b N} (hy : IsAboveDiagonal y) {P : ℕ × ℕ}
    (hP : P ∈ sweptRegion y) (hD : eventType y P ≠ EventType.D)
    (hE : eventType y P ≠ EventType.E) : #(wordBlock y P) = blockSize y P := by
  have h := blockSize_le_wordPosition hy hP hD hE
  rw [wordBlock, Nat.card_Ioc]
  omega

/-- **The word position of a strictly lower-ranked swept point, plus the block size at the higher
one, does not exceed the word position there.** No adjacency: both counts of
`HJO.Paths.wordPosition` are monotone in the rank, and each gains its own indicator at `P` — the
north step with foot `P` has `rk̂(Q) < rk̂(P) ≤ rk̂(P)`, and the one with head `P` has
`rk̂(Q) < rk̂(P) = rk̂(u) + ω ≤ rk̂(P)`. This single inequality is
`HJO.Paths.lt_of_mem_wordBlock_of_rank_lt`. -/
theorem wordPosition_add_blockSize_le {y : Heights a b N} (hy : IsAboveDiagonal y) {Q P : ℕ × ℕ}
    (hP : P ∈ sweptRegion y) (hD : eventType y P ≠ EventType.D)
    (hE : eventType y P ≠ EventType.E)
    (hlt : ParkingFunctions.abovePointRank a b N Q.1 Q.2 <
      ParkingFunctions.abovePointRank a b N P.1 P.2) :
    wordPosition y Q + blockSize y P ≤ wordPosition y P := by
  rw [blockSize_eq_card_feet_add_card_heads hy hP hD hE]
  -- the feet count
  have hsubF : {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
        ParkingFunctions.abovePointRank a b N Q.1 Q.2} ⊆
      {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
        ParkingFunctions.abovePointRank a b N P.1 P.2} :=
    monotone_filter_right _ fun u _ hu => hu.trans hlt.le
  have hFin : {u ∈ northSteps y | u = P} ⊆
      {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
          ParkingFunctions.abovePointRank a b N P.1 P.2} \
        {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
          ParkingFunctions.abovePointRank a b N Q.1 Q.2} := by
    intro u hu
    obtain ⟨hun, rfl⟩ := mem_filter.1 hu
    simp only [mem_sdiff, mem_filter, not_and, not_le]
    exact ⟨⟨hun, le_rfl⟩, fun _ => hlt⟩
  -- the heads count
  have hsubH : {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 +
        attackWindow a N ≤ ParkingFunctions.abovePointRank a b N Q.1 Q.2} ⊆
      {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 +
        attackWindow a N ≤ ParkingFunctions.abovePointRank a b N P.1 P.2} :=
    monotone_filter_right _ fun u _ hu => hu.trans hlt.le
  have hHin : {u ∈ northSteps y | (u.1, u.2 + 1) = P} ⊆
      {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N ≤
          ParkingFunctions.abovePointRank a b N P.1 P.2} \
        {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N ≤
          ParkingFunctions.abovePointRank a b N Q.1 Q.2} := by
    intro u hu
    obtain ⟨hun, hhead⟩ := mem_filter.1 hu
    have e1 : P.1 = u.1 := by rw [← hhead]
    have e2 : P.2 = u.2 + 1 := by rw [← hhead]
    have hPr : ParkingFunctions.abovePointRank a b N P.1 P.2 =
        ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N := by
      rw [e1, e2, abovePointRank_succ]
    simp only [mem_sdiff, mem_filter, not_and, not_le]
    refine ⟨⟨hun, hPr.ge⟩, fun _ => ?_⟩
    rwa [hPr] at hlt
  have hF := card_sdiff_add_card_eq_card hsubF
  have hH := card_sdiff_add_card_eq_card hsubH
  have hFc := card_le_card hFin
  have hHc := card_le_card hHin
  rw [wordPosition, wordPosition]
  omega

/-! ### The blocks descend with the rank -/

/-- **The word blocks descend with the rank.** `HJO.Paths.lt_of_mem_wordBlock_of_rank_lt`: at two
events, the block of the lower-ranked one lies entirely below the block of the higher-ranked one.

The greatest element of `Blk(P')` is `pos(P')`, the least element of `Blk(P)` is
`pos(P) - δ_P + 1`, and `HJO.Paths.wordPosition_add_blockSize_le` says `pos(P') ≤ pos(P) - δ_P`. -/
@[hjo "lem_sweep_block_order"]
theorem lt_of_mem_wordBlock_of_rank_lt {y : Heights a b N} (hy : IsAboveDiagonal y)
    {P P' : ℕ × ℕ} (hP : P ∈ sweptRegion y) (hD : eventType y P ≠ EventType.D)
    (hE : eventType y P ≠ EventType.E)
    (hlt : ParkingFunctions.abovePointRank a b N P'.1 P'.2 <
      ParkingFunctions.abovePointRank a b N P.1 P.2)
    {r r' : ℕ} (hr : r ∈ wordBlock y P) (hr' : r' ∈ wordBlock y P') : r' < r := by
  have hkey := wordPosition_add_blockSize_le hy hP hD hE hlt
  rw [mem_wordBlock] at hr hr'
  omega

/-! ### The events of the sweep -/

/-- The swept points of event type `A`, `B` or `C`: the events of the sweep, and the index set of
the family of word blocks. This is the `{Q_1, …, Q_L}` as a `Finset`, with no listing
chosen. -/
def eventPoints (y : Heights a b N) : Finset (ℕ × ℕ) :=
  {P ∈ sweptRegion y | eventType y P ≠ EventType.D ∧ eventType y P ≠ EventType.E}

@[simp]
theorem mem_eventPoints {y : Heights a b N} {P : ℕ × ℕ} :
    P ∈ eventPoints y ↔ P ∈ sweptRegion y ∧ eventType y P ≠ EventType.D ∧
      eventType y P ≠ EventType.E := mem_filter

/-- **The events split into the three types.** -/
theorem eventPoints_eq_union (y : Heights a b N) :
    eventPoints y = ({P ∈ sweptRegion y | eventType y P = EventType.A} ∪
        {P ∈ sweptRegion y | eventType y P = EventType.B}) ∪
      {P ∈ sweptRegion y | eventType y P = EventType.C} := by
  ext P
  simp only [mem_eventPoints, mem_union, mem_filter]
  constructor
  · rintro ⟨hP, hD, hE⟩
    cases hev : eventType y P with
    | A => exact Or.inl (Or.inl ⟨hP, rfl⟩)
    | B => exact Or.inl (Or.inr ⟨hP, rfl⟩)
    | C => exact Or.inr ⟨hP, rfl⟩
    | D => exact absurd hev hD
    | E => exact absurd hev hE
  · rintro ((⟨hP, hev⟩ | ⟨hP, hev⟩) | ⟨hP, hev⟩) <;> exact ⟨hP, by simp [hev], by simp [hev]⟩

/-- **There are `2bN` word positions in all, counted through the events.** `#A + #B + 2#C` is
`2c + 2(bN - c) = 2bN` by `HJO.Paths.card_filter_eventType_A`, taken in the form
`HJO.Paths.card_filter_eventType_C_add_card_riseColumns`, which carries no truncated
subtraction. -/
theorem sum_blockSize_eventPoints {y : Heights a b N} (hy : IsAboveDiagonal y) :
    ∑ P ∈ eventPoints y, blockSize y P = 2 * (b * N) := by
  classical
  have hdisj : ∀ S T : EventType, S ≠ T →
      Disjoint {P ∈ sweptRegion y | eventType y P = S} {P ∈ sweptRegion y | eventType y P = T} :=
    fun S T hST => Finset.disjoint_left.2 fun P hS hT => by
      rw [mem_filter] at hS hT
      exact hST (hS.2.symm.trans hT.2)
  have hdisjAB := hdisj EventType.A EventType.B (by simp)
  have hdisjC : Disjoint ({P ∈ sweptRegion y | eventType y P = EventType.A} ∪
      {P ∈ sweptRegion y | eventType y P = EventType.B})
      {P ∈ sweptRegion y | eventType y P = EventType.C} := by
    rw [disjoint_union_left]
    exact ⟨hdisj EventType.A EventType.C (by simp), hdisj EventType.B EventType.C (by simp)⟩
  have hsum : ∑ P ∈ eventPoints y, blockSize y P =
      (∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.A}, blockSize y P +
        ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.B}, blockSize y P) +
      ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.C}, blockSize y P := by
    rw [eventPoints_eq_union, sum_union hdisjC, sum_union hdisjAB]
  have hA : ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.A}, blockSize y P =
      #{P ∈ sweptRegion y | eventType y P = EventType.A} := by
    rw [sum_congr rfl fun P hP => show blockSize y P = 1 by
      rw [blockSize, (mem_filter.1 hP).2]; simp]
    simp
  have hB : ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.B}, blockSize y P =
      #{P ∈ sweptRegion y | eventType y P = EventType.B} := by
    rw [sum_congr rfl fun P hP => show blockSize y P = 1 by
      rw [blockSize, (mem_filter.1 hP).2]; simp]
    simp
  have hC : ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.C}, blockSize y P =
      2 * #{P ∈ sweptRegion y | eventType y P = EventType.C} := by
    rw [sum_congr rfl fun P hP => show blockSize y P = 2 by
      rw [blockSize, (mem_filter.1 hP).2]; simp]
    rw [sum_const, smul_eq_mul, mul_comm]
  rw [hsum, hA, hB, hC, card_filter_eventType_A hy, card_filter_eventType_B hy]
  have := card_filter_eventType_C_add_card_riseColumns hy
  omega

/-! ### The blocks partition the word -/

/-- **Distinct events have disjoint word blocks.** The rank is injective on the strip, so two
distinct swept points have distinct ranks, and then `HJO.Paths.lt_of_mem_wordBlock_of_rank_lt` puts
one block strictly below the other. -/
theorem disjoint_wordBlock {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a) (hN : 0 < N)
    {P P' : ℕ × ℕ} (hP : P ∈ eventPoints y) (hP' : P' ∈ eventPoints y) (hne : P ≠ P') :
    Disjoint (wordBlock y P) (wordBlock y P') := by
  obtain ⟨hPs, hPD, hPE⟩ := mem_eventPoints.1 hP
  obtain ⟨hP's, hP'D, hP'E⟩ := mem_eventPoints.1 hP'
  have hrkne : ParkingFunctions.abovePointRank a b N P.1 P.2 ≠
      ParkingFunctions.abovePointRank a b N P'.1 P'.2 := fun heq => by
    obtain ⟨h1, h2⟩ := abovePointRank_injOn (b := b) ha hN (mem_sweptRegion.1 hPs).1
      (mem_sweptRegion.1 hP's).1 heq
    exact hne (Prod.ext h1 h2)
  refine Finset.disjoint_left.2 fun r hr hr' => ?_
  rcases lt_or_gt_of_ne hrkne with hlt | hlt
  · exact absurd rfl (Nat.ne_of_lt
      (lt_of_mem_wordBlock_of_rank_lt hy hP's hP'D hP'E hlt hr' hr))
  · exact absurd rfl (Nat.ne_of_lt
      (lt_of_mem_wordBlock_of_rank_lt hy hPs hPD hPE hlt hr hr'))

/-- Every word position in a block of an event lies in `{1, …, 2bN}`: it is at most `pos(P)`, which
`HJO.Paths.wordPosition_le` bounds by `2bN`, and it exceeds `pos(P) - δ ≥ 0`, hence is at least
`1`. -/
theorem wordBlock_subset_Icc {y : Heights a b N} (hy : IsAboveDiagonal y) (P : ℕ × ℕ) :
    wordBlock y P ⊆ Finset.Icc 1 (2 * (b * N)) := by
  intro r hr
  rw [mem_wordBlock] at hr
  have hle : wordPosition y P ≤ 2 * (b * N) := by
    have := wordPosition_le y P
    rwa [card_northSteps hy] at this
  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩

/-- **The word blocks partition the word.** `HJO.Paths.wordBlock_biUnion_eq`: as `P` runs
over the swept points of event type `A`, `B` or `C`, the blocks `Blk_{P̂}(P)` are pairwise disjoint
(`HJO.Paths.disjoint_wordBlock`) and their union is `{1, 2, …, 2bN}`.

The union is a cardinality count, not a telescoping. The blocks are disjoint subsets of
`{1, …, 2bN}` whose sizes are the `δ_P`, so the union has `∑_P δ_P = 2bN` elements by
`HJO.Paths.sum_blockSize_eventPoints`, which is the cardinality of `{1, …, 2bN}`; a subset of the
same size is the whole. -/
@[hjo "lem_sweep_block_partition"]
theorem wordBlock_biUnion_eq {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a)
    (hN : 0 < N) : (eventPoints y).biUnion (wordBlock y) = Finset.Icc 1 (2 * (b * N)) := by
  classical
  refine Finset.eq_of_subset_of_card_le
    (Finset.biUnion_subset.2 fun P _ => wordBlock_subset_Icc hy P) ?_
  rw [Finset.card_biUnion fun P hP P' hP' hne => disjoint_wordBlock hy ha hN hP hP' hne]
  have hcard : ∑ P ∈ eventPoints y, #(wordBlock y P) = 2 * (b * N) := by
    rw [Finset.sum_congr rfl fun P hP => card_wordBlock hy (mem_eventPoints.1 hP).1
      (mem_eventPoints.1 hP).2.1 (mem_eventPoints.1 hP).2.2]
    exact sum_blockSize_eventPoints hy
  rw [hcard, Nat.card_Icc]
  omega

end HJO.Paths
