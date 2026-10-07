/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.Sweep
public meta import HJO.Attr

/-! # The four on-path event types partition the swept region

The sweep process registers an event at every lattice point weakly above the diagonal and weakly
below an above-diagonal path. The points strictly below the path carry the event type `E` and are
counted by `HJO.Paths.card_filter_eventType_E`; this file counts the other four, which are the
points *on* the path. With `c` the number of columns of the path that climb — the number of `x` with
`0 ≤ x ≤ aN - 1` and `ŷ_x < ŷ_{x+1}` — the counts are `c`, `bN - c` and `aN + 1 - c` for the
types `A`, `B`, `C` and `D`.

## Main definitions

* `HJO.Paths.riseColumns`: the columns at which the path climbs, whose cardinality is `c`.

## Main results

* `HJO.Paths.eventType_eq_A_iff`, `HJO.Paths.eventType_eq_B_iff`, `HJO.Paths.eventType_eq_C_iff`,
  `HJO.Paths.eventType_eq_D_iff`: the four on-path event types read off the heights, the companions
  of `HJO.Paths.eventType_eq_E_iff`.
* `HJO.Paths.riseColumns_eq_image_northSteps`: the columns at which the path climbs are exactly the
  columns carrying a north step, so `c` is the number of such columns — the form in which
  `HJO.Paths.sum_sweepRight_add_leftEastCount_A_eq_sum_sweepWidth_sub_one_B` uses this lemma.
* `HJO.Paths.card_filter_eventType_A`, `HJO.Paths.card_filter_eventType_B`,
  `HJO.Paths.card_filter_eventType_C`, `HJO.Paths.card_filter_eventType_D`: the four counts, which
  together make up `HJO.Paths.card_filter_eventType_A`. The two whose stated value is a
  difference are also
  recorded additively, as `HJO.Paths.card_filter_eventType_C_add_card_riseColumns` and
  `HJO.Paths.card_filter_eventType_D_add_card_riseColumns`, which is where the content is: the
  truncated subtraction of `ℕ` would make the difference form true for a trivial reason if `c`
  could exceed `bN`, and those two identities are what say it cannot.

## Implementation notes

### A fibrewise count, not the word

The direct proof lists the non-`E` points of `Sw(P̂)` as a staircase
`Q_0, …, Q_{aN+bN}`, reads off a word in `{N, E}` of length `aN + bN + 2` that begins and ends
with `E`, and counts the four consecutive pairs `NE`, `EN`, `NN`, `EE` in it by splitting the
`N`'s into maximal runs. Nothing of that word is formed here. The count is fibrewise over the
abscissa instead, in the manner of `HJO.Paths.card_filter_eventType_E`: above a fixed `x ≤ aN` the
non-`E` swept points are the ordinates `ŷ_x ≤ k ≤ ŷ⁺_x`, and reading `HJO.Paths.eventType` on that
interval gives, when `ŷ_x < ŷ⁺_x`,

* the bottom point `k = ŷ_x`, of type `B`;
* the interior points `ŷ_x < k < ŷ⁺_x`, of type `C`, there being `ŷ⁺_x - ŷ_x - 1` of them;
* the top point `k = ŷ⁺_x`, of type `A`;

and, when `ŷ_x = ŷ⁺_x`, the single point `k = ŷ_x`, of type `D`. The maximal runs of
`N`'s are exactly the climbing columns, and this is the same bookkeeping done one column at a time.
Summing the four column counts over `0 ≤ x ≤ aN` gives the four totals: the `C` total by the
telescoping `∑_x (ŷ_{x+1} - ŷ_x) = bN` of `Finset.sum_range_tsub`, corrected by one unit per
climbing column, and the `D` total because a column contributes one point of type `A` and one of
type `B` if it climbs and a single point of type `D` if it does not.

The column `x = aN` is where `HJO.Paths.IsAboveDiagonal` is read: there `ŷ⁺_{aN} = bN = ŷ_{aN}`, so
that column does not climb and contributes the one type-`D` point that makes the `D` count
`aN + 1 - c` rather than `aN - c`. It is also the point `(aN, bN)`, the corner at which the sweep
stops.

## References

A. Mellit, *Toric braids
and `(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### The four on-path event types, read off the heights -/

/-- The event type at `P = (x, k)` is `A` exactly when the point lies strictly above the foot `ŷ_x`
of its own column and its outgoing letter is `E`. This is `HJO.Paths.eventType` unfolded; like
`HJO.Paths.eventType_eq_E_iff` it needs no hypothesis on `P`, the five readings being a case split
on the definition itself. The guard `x ≤ aN - 1` of the outgoing letter is written `x < aN`. -/
theorem eventType_eq_A_iff {y : Heights a b N} {P : ℕ × ℕ} :
    eventType y P = EventType.A ↔
      ht y P.1 < P.2 ∧ ¬(P.1 < a * N ∧ P.2 < ht y (P.1 + 1)) := by
  rw [eventType]
  split_ifs <;> simp_all
  all_goals omega

/-- The event type at `P = (x, k)` is `B` exactly when the point is the foot `ŷ_x` of its own column
and its outgoing letter is `N`. -/
theorem eventType_eq_B_iff {y : Heights a b N} {P : ℕ × ℕ} :
    eventType y P = EventType.B ↔
      P.2 = ht y P.1 ∧ P.1 < a * N ∧ P.2 < ht y (P.1 + 1) := by
  rw [eventType]
  split_ifs <;> simp_all
  all_goals omega

/-- The event type at `P = (x, k)` is `C` exactly when the point lies strictly above the foot `ŷ_x`
of its own column and its outgoing letter is `N`: both letters are north, so the point is interior
to a run of north steps. -/
theorem eventType_eq_C_iff {y : Heights a b N} {P : ℕ × ℕ} :
    eventType y P = EventType.C ↔
      ht y P.1 < P.2 ∧ P.1 < a * N ∧ P.2 < ht y (P.1 + 1) := by
  rw [eventType]
  split_ifs <;> simp_all
  all_goals omega

/-- The event type at `P = (x, k)` is `D` exactly when the point is the foot `ŷ_x` of its own column
and its outgoing letter is `E`: both letters are east, so the path crosses `P` horizontally and the
column does not climb. -/
theorem eventType_eq_D_iff {y : Heights a b N} {P : ℕ × ℕ} :
    eventType y P = EventType.D ↔
      P.2 = ht y P.1 ∧ ¬(P.1 < a * N ∧ P.2 < ht y (P.1 + 1)) := by
  rw [eventType]
  split_ifs <;> simp_all
  all_goals omega

/-- `HJO.Paths.eventType_eq_A_iff` with the point written out as a pair, the shape the fibrewise
count below reads it in: `omega` sees the heights only once the projections are reduced. -/
private theorem eventType_mk_eq_A_iff {y : Heights a b N} {x k : ℕ} :
    eventType y (x, k) = EventType.A ↔ ht y x < k ∧ ¬(x < a * N ∧ k < ht y (x + 1)) :=
  eventType_eq_A_iff

/-- `HJO.Paths.eventType_eq_B_iff` with the point written out as a pair. -/
private theorem eventType_mk_eq_B_iff {y : Heights a b N} {x k : ℕ} :
    eventType y (x, k) = EventType.B ↔ k = ht y x ∧ x < a * N ∧ k < ht y (x + 1) :=
  eventType_eq_B_iff

/-- `HJO.Paths.eventType_eq_C_iff` with the point written out as a pair. -/
private theorem eventType_mk_eq_C_iff {y : Heights a b N} {x k : ℕ} :
    eventType y (x, k) = EventType.C ↔ ht y x < k ∧ x < a * N ∧ k < ht y (x + 1) :=
  eventType_eq_C_iff

/-- `HJO.Paths.eventType_eq_D_iff` with the point written out as a pair. -/
private theorem eventType_mk_eq_D_iff {y : Heights a b N} {x k : ℕ} :
    eventType y (x, k) = EventType.D ↔ k = ht y x ∧ ¬(x < a * N ∧ k < ht y (x + 1)) :=
  eventType_eq_D_iff

/-! ### The columns at which the path climbs -/

/-- The columns at which the path `y` climbs: the abscissae `0 ≤ x ≤ aN - 1` with `ŷ_x < ŷ_{x+1}`.
Its cardinality is the `c`, the number the four on-path event counts of
`HJO.Paths.card_filter_eventType_A` are expressed in. By `HJO.Paths.riseColumns_eq_image_northSteps`
these are exactly the columns carrying a north step, which is how
`HJO.Paths.sum_sweepRight_add_leftEastCount_A_eq_sum_sweepWidth_sub_one_B` names `c`. -/
def riseColumns (y : Heights a b N) : Finset ℕ :=
  {x ∈ range (a * N) | ht y x < ht y (x + 1)}

@[simp]
theorem mem_riseColumns {y : Heights a b N} {x : ℕ} :
    x ∈ riseColumns y ↔ x < a * N ∧ ht y x < ht y (x + 1) := by
  simp [riseColumns]

/-- The number of climbing columns, as a sum of indicators over the columns of the rectangle. -/
theorem card_riseColumns (y : Heights a b N) :
    #(riseColumns y) = ∑ x ∈ range (a * N), (if ht y x < ht y (x + 1) then 1 else 0) :=
  card_filter _ _

/-- The columns at which the path climbs are exactly the columns carrying a north step: column `x`
holds the north steps with feet at the heights `ŷ_x ≤ i < ŷ_{x+1}`, so it holds one exactly when it
climbs. Hence the `c` is the number of columns of `P̂` carrying a north step. -/
theorem riseColumns_eq_image_northSteps (y : Heights a b N) :
    riseColumns y = (northSteps y).image Prod.fst := by
  ext x
  simp only [mem_riseColumns, mem_image, mem_northSteps_iff]
  refine ⟨fun h => ⟨(x, ht y x), ⟨h.1, le_rfl, h.2⟩, rfl⟩, ?_⟩
  rintro ⟨u, ⟨hu1, hu2, hu3⟩, rfl⟩
  exact ⟨hu1, by omega⟩

/-- A column that climbs is a column of the rectangle. The content is at `x = aN`, where
`ŷ⁺_{aN} = bN = ŷ_{aN}`: the last column of an above-diagonal path does not climb. -/
private theorem lt_of_ht_lt_ht_succ {y : Heights a b N} (hy : IsAboveDiagonal y) {x : ℕ}
    (hx : x ≤ a * N) (h : ht y x < ht y (x + 1)) : x < a * N := by
  rcases Nat.lt_or_ge x (a * N) with hlt | hge
  · exact hlt
  · rw [le_antisymm hx hge, hy.2.1, ht_of_gt y (show a * N < a * N + 1 by omega)] at h
    omega

/-- A column of an above-diagonal path that does not climb has `ŷ⁺_x = ŷ_x`, the case `x = aN`
included: there `ŷ⁺_{aN} = bN = ŷ_{aN}` outright. -/
private theorem ht_succ_eq_of_not_lt {y : Heights a b N} (hy : IsAboveDiagonal y) {x : ℕ}
    (hx : x ≤ a * N) (h : ¬ht y x < ht y (x + 1)) : ht y (x + 1) = ht y x := by
  rcases Nat.lt_or_ge x (a * N) with hlt | hge
  · have := ht_mono hy.2.2.1 (Nat.le_add_right x 1)
    omega
  · rw [le_antisymm hx hge, hy.2.1, ht_of_gt y (show a * N < a * N + 1 by omega)]

/-! ### The events above one abscissa -/

/-- The swept points of a fixed abscissa `x` carrying a fixed non-`E` event type are the ordinates
`ŷ_x ≤ k ≤ ŷ⁺_x` carrying it: a non-`E` point is not strictly below the path, and every point of
that interval is swept, being weakly above the diagonal because `a ŷ_x ≥ b x`. This is the fibre the
four counts below are summed from. -/
private theorem card_fiber_eventType {y : Heights a b N} (hy : IsAboveDiagonal y) {x : ℕ}
    (hx : x ≤ a * N) {T : EventType} (hT : T ≠ EventType.E) :
    #{P ∈ {P ∈ sweptRegion y | eventType y P = T} | P.1 = x}
      = #{k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = T} := by
  have hset : {P ∈ {P ∈ sweptRegion y | eventType y P = T} | P.1 = x}
      = ({k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = T}).image fun k => (x, k) := by
    ext P
    simp only [mem_filter, mem_image, mem_Icc, mem_sweptRegion]
    constructor
    · rintro ⟨⟨⟨-, -, hup⟩, hev⟩, hxP⟩
      have hlow : ht y P.1 ≤ P.2 := by
        by_contra hcon
        exact hT (hev.symm.trans (eventType_eq_E_iff.2 (not_le.1 hcon)))
      refine ⟨P.2, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rw [← hxP]; exact hlow
      · rw [← hxP]; exact hup
      · rw [← hxP]; exact hev
      · rw [Prod.ext_iff]; exact ⟨hxP.symm, rfl⟩
    · rintro ⟨k, ⟨⟨hk1, hk2⟩, hev⟩, hP⟩
      have hP1 : P.1 = x := by simpa using (congrArg Prod.fst hP).symm
      have hP2 : P.2 = k := by simpa using (congrArg Prod.snd hP).symm
      refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, hP1⟩
      · rw [hP1]; exact hx
      · rw [hP1, hP2]; exact (hy.2.2.2 x hx).trans (Nat.mul_le_mul_left a hk1)
      · rw [hP1, hP2]; exact hk2
      · rw [← hP]; exact hev
  rw [hset, card_image_of_injective _ fun k k' h => by simpa using congrArg Prod.snd h]

/-- Above one abscissa there is exactly one type-`A` event if the column climbs and none if it does
not: the type-`A` point is the top `k = ŷ⁺_x` of the column. -/
private theorem card_filter_Icc_eventType_A {y : Heights a b N} (hy : IsAboveDiagonal y) {x : ℕ}
    (hx : x ≤ a * N) :
    #{k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = EventType.A}
      = if ht y x < ht y (x + 1) then 1 else 0 := by
  split_ifs with h
  · have hxlt := lt_of_ht_lt_ht_succ hy hx h
    have hs : {k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = EventType.A}
        = {ht y (x + 1)} := by
      ext k
      simp only [mem_filter, mem_Icc, mem_singleton, eventType_mk_eq_A_iff]
      omega
    rw [hs, card_singleton]
  · have heq := ht_succ_eq_of_not_lt hy hx h
    rw [card_eq_zero, filter_eq_empty_iff]
    intro k hk
    rw [mem_Icc] at hk
    rw [eventType_mk_eq_A_iff]
    omega

/-- Above one abscissa there is exactly one type-`B` event if the column climbs and none if it does
not: the type-`B` point is the foot `k = ŷ_x` of the column. -/
private theorem card_filter_Icc_eventType_B {y : Heights a b N} (hy : IsAboveDiagonal y) {x : ℕ}
    (hx : x ≤ a * N) :
    #{k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = EventType.B}
      = if ht y x < ht y (x + 1) then 1 else 0 := by
  split_ifs with h
  · have hxlt := lt_of_ht_lt_ht_succ hy hx h
    have hs : {k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = EventType.B}
        = {ht y x} := by
      ext k
      simp only [mem_filter, mem_Icc, mem_singleton, eventType_mk_eq_B_iff]
      omega
    rw [hs, card_singleton]
  · have heq := ht_succ_eq_of_not_lt hy hx h
    rw [card_eq_zero, filter_eq_empty_iff]
    intro k hk
    rw [mem_Icc] at hk
    rw [eventType_mk_eq_B_iff]
    omega

/-- Above one abscissa the type-`C` events are the interior points `ŷ_x < k < ŷ⁺_x` of the column,
of which there are `ŷ⁺_x - ŷ_x - 1`; the formula reads `0` on a column that does not climb, the
subtraction of `ℕ` being truncated. -/
private theorem card_filter_Icc_eventType_C {y : Heights a b N} (hy : IsAboveDiagonal y) {x : ℕ}
    (hx : x ≤ a * N) :
    #{k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = EventType.C}
      = ht y (x + 1) - ht y x - 1 := by
  by_cases h : ht y x < ht y (x + 1)
  · have hxlt := lt_of_ht_lt_ht_succ hy hx h
    have hs : {k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = EventType.C}
        = Ioo (ht y x) (ht y (x + 1)) := by
      ext k
      simp only [mem_filter, mem_Icc, mem_Ioo, eventType_mk_eq_C_iff]
      omega
    rw [hs, Nat.card_Ioo]
  · have heq := ht_succ_eq_of_not_lt hy hx h
    have hs : {k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = EventType.C} = ∅ := by
      refine filter_eq_empty_iff.2 fun {k} hk => ?_
      rw [mem_Icc] at hk
      rw [eventType_mk_eq_C_iff]
      omega
    rw [hs, card_empty, heq]
    omega

/-- Above one abscissa there is no type-`D` event if the column climbs and exactly one if it does
not: the single point `k = ŷ_x = ŷ⁺_x` of a column the path crosses horizontally. -/
private theorem card_filter_Icc_eventType_D {y : Heights a b N} (hy : IsAboveDiagonal y) {x : ℕ}
    (hx : x ≤ a * N) :
    #{k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = EventType.D}
      = if ht y x < ht y (x + 1) then 0 else 1 := by
  split_ifs with h
  · have hxlt := lt_of_ht_lt_ht_succ hy hx h
    rw [card_eq_zero, filter_eq_empty_iff]
    intro k hk
    rw [mem_Icc] at hk
    rw [eventType_mk_eq_D_iff]
    omega
  · have heq := ht_succ_eq_of_not_lt hy hx h
    have hs : {k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = EventType.D}
        = {ht y x} := by
      ext k
      simp only [mem_filter, mem_Icc, mem_singleton, eventType_mk_eq_D_iff]
      omega
    rw [hs, card_singleton]

/-! ### The four counts -/

/-- The count of climbing columns as a sum over every abscissa of the closed strip `0 ≤ x ≤ aN`, the
range the fibrewise counts below are summed over. The column `x = aN` contributes nothing, not
climbing. -/
private theorem sum_ite_ht_lt_ht_succ {y : Heights a b N} (hy : IsAboveDiagonal y) :
    ∑ x ∈ range (a * N + 1), (if ht y x < ht y (x + 1) then 1 else 0) = #(riseColumns y) := by
  have htop : ¬ht y (a * N) < ht y (a * N + 1) := by
    rw [hy.2.1, ht_of_gt y (show a * N < a * N + 1 by omega)]
    omega
  rw [card_riseColumns, Finset.sum_range_succ]
  simp [htop]

/-- The fibrewise decomposition every one of the four counts below starts from: a count over the
swept points of a fixed non-`E` event type is the sum over the abscissae `0 ≤ x ≤ aN` of the count
above that abscissa. -/
private theorem card_filter_eventType_eq_sum {y : Heights a b N} (hy : IsAboveDiagonal y)
    {T : EventType} (hT : T ≠ EventType.E) :
    #{P ∈ sweptRegion y | eventType y P = T}
      = ∑ x ∈ range (a * N + 1),
          #{k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = T} := by
  have hfib : ∀ x ∈ range (a * N + 1),
      #{P ∈ {P ∈ sweptRegion y | eventType y P = T} | P.1 = x}
        = #{k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = T} := fun x hx =>
    card_fiber_eventType hy (Nat.lt_succ_iff.1 (mem_range.1 hx)) hT
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := range (a * N + 1))
    fun P hP => mem_range.2 (by have := (mem_sweptRegion.1 (mem_filter.1 hP).1).1; omega),
    Finset.sum_congr rfl hfib]

/-- **The type-`A` events are one per climbing column.** Part of
`HJO.Paths.card_filter_eventType_A`: the number of points of `Sw(P̂)` of event type `A` is `c`, the
number of `x` with `0 ≤ x ≤ aN - 1` and `ŷ_x < ŷ_{x+1}`. -/
@[hjo "lem_sweep_event_counts"]
theorem card_filter_eventType_A {y : Heights a b N} (hy : IsAboveDiagonal y) :
    #{P ∈ sweptRegion y | eventType y P = EventType.A} = #(riseColumns y) := by
  have hfib : ∀ x ∈ range (a * N + 1),
      #{k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = EventType.A}
        = if ht y x < ht y (x + 1) then 1 else 0 := fun x hx =>
    card_filter_Icc_eventType_A hy (Nat.lt_succ_iff.1 (mem_range.1 hx))
  rw [card_filter_eventType_eq_sum hy (by simp), Finset.sum_congr rfl hfib,
    sum_ite_ht_lt_ht_succ hy]

/-- **The type-`B` events are one per climbing column.** Part of
`HJO.Paths.card_filter_eventType_A`: the number of points of `Sw(P̂)` of event type `B` is `c`, the
same count as for type `A` — each climbing column contributes its foot and its top. -/
@[hjo "lem_sweep_event_counts"]
theorem card_filter_eventType_B {y : Heights a b N} (hy : IsAboveDiagonal y) :
    #{P ∈ sweptRegion y | eventType y P = EventType.B} = #(riseColumns y) := by
  have hfib : ∀ x ∈ range (a * N + 1),
      #{k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = EventType.B}
        = if ht y x < ht y (x + 1) then 1 else 0 := fun x hx =>
    card_filter_Icc_eventType_B hy (Nat.lt_succ_iff.1 (mem_range.1 hx))
  rw [card_filter_eventType_eq_sum hy (by simp), Finset.sum_congr rfl hfib,
    sum_ite_ht_lt_ht_succ hy]

/-- The telescoping identity behind the type-`C` count: the climbs of the path sum to `bN`, and
discarding one unit per climbing column leaves the column counts of the type-`C` events. -/
private theorem sum_sub_one_add_card_riseColumns {y : Heights a b N} (hy : IsAboveDiagonal y) :
    ∑ x ∈ range (a * N + 1), (ht y (x + 1) - ht y x - 1) + #(riseColumns y) = b * N := by
  calc ∑ x ∈ range (a * N + 1), (ht y (x + 1) - ht y x - 1) + #(riseColumns y)
      = ∑ x ∈ range (a * N + 1), (ht y (x + 1) - ht y x - 1)
          + ∑ x ∈ range (a * N + 1), (if ht y x < ht y (x + 1) then 1 else 0) := by
        rw [sum_ite_ht_lt_ht_succ hy]
    _ = ∑ x ∈ range (a * N + 1),
          (ht y (x + 1) - ht y x - 1 + if ht y x < ht y (x + 1) then 1 else 0) :=
        Finset.sum_add_distrib.symm
    _ = ∑ x ∈ range (a * N + 1), (ht y (x + 1) - ht y x) :=
        Finset.sum_congr rfl fun x _ => by split_ifs <;> omega
    _ = b * N := by
        rw [Finset.sum_range_tsub (ht_mono hy.2.2.1), hy.1,
          ht_of_gt y (show a * N < a * N + 1 by omega), Nat.sub_zero]

/-- **The type-`C` events and the climbing columns together account for the `bN` north steps.** This
is the content of the type-`C` count: the path has `bN` north steps in all, and each climbing column
spends one of them on its own type-`B` foot, leaving the rest as interior type-`C` points. -/
theorem card_filter_eventType_C_add_card_riseColumns {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    #{P ∈ sweptRegion y | eventType y P = EventType.C} + #(riseColumns y) = b * N := by
  have hfib : ∀ x ∈ range (a * N + 1),
      #{k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = EventType.C}
        = ht y (x + 1) - ht y x - 1 := fun x hx =>
    card_filter_Icc_eventType_C hy (Nat.lt_succ_iff.1 (mem_range.1 hx))
  rw [card_filter_eventType_eq_sum hy (by simp), Finset.sum_congr rfl hfib]
  exact sum_sub_one_add_card_riseColumns hy

/-- **The type-`C` events are `bN - c`.** Part of `HJO.Paths.card_filter_eventType_A`, in its
own words; `HJO.Paths.card_filter_eventType_C_add_card_riseColumns` is the same fact without the
truncated subtraction of `ℕ`, and is what makes this one say something. -/
@[hjo "lem_sweep_event_counts"]
theorem card_filter_eventType_C {y : Heights a b N} (hy : IsAboveDiagonal y) :
    #{P ∈ sweptRegion y | eventType y P = EventType.C} = b * N - #(riseColumns y) :=
  Nat.eq_sub_of_add_eq (card_filter_eventType_C_add_card_riseColumns hy)

/-- **The type-`D` events and the climbing columns together account for the `aN + 1` abscissae of
the closed strip.** This is the content of the type-`D` count: each of the abscissae `0 ≤ x ≤ aN`
contributes a type-`D` point exactly when it does not climb, the abscissa `aN` never climbing. -/
theorem card_filter_eventType_D_add_card_riseColumns {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    #{P ∈ sweptRegion y | eventType y P = EventType.D} + #(riseColumns y) = a * N + 1 := by
  have hfib : ∀ x ∈ range (a * N + 1),
      #{k ∈ Icc (ht y x) (ht y (x + 1)) | eventType y (x, k) = EventType.D}
        = if ht y x < ht y (x + 1) then 0 else 1 := fun x hx =>
    card_filter_Icc_eventType_D hy (Nat.lt_succ_iff.1 (mem_range.1 hx))
  rw [card_filter_eventType_eq_sum hy (by simp), Finset.sum_congr rfl hfib]
  calc ∑ x ∈ range (a * N + 1), (if ht y x < ht y (x + 1) then 0 else 1) + #(riseColumns y)
      = ∑ x ∈ range (a * N + 1), (if ht y x < ht y (x + 1) then 0 else 1)
          + ∑ x ∈ range (a * N + 1), (if ht y x < ht y (x + 1) then 1 else 0) := by
        rw [sum_ite_ht_lt_ht_succ hy]
    _ = ∑ x ∈ range (a * N + 1),
          ((if ht y x < ht y (x + 1) then 0 else 1) + if ht y x < ht y (x + 1) then 1 else 0) :=
        Finset.sum_add_distrib.symm
    _ = ∑ _x ∈ range (a * N + 1), 1 := Finset.sum_congr rfl fun x _ => by split_ifs <;> omega
    _ = a * N + 1 := by simp

/-- **The type-`D` events are `aN + 1 - c`.** Part of `HJO.Paths.card_filter_eventType_A`, in
its own words; `HJO.Paths.card_filter_eventType_D_add_card_riseColumns` is the same fact without the
truncated subtraction of `ℕ`. -/
@[hjo "lem_sweep_event_counts"]
theorem card_filter_eventType_D {y : Heights a b N} (hy : IsAboveDiagonal y) :
    #{P ∈ sweptRegion y | eventType y P = EventType.D} = a * N + 1 - #(riseColumns y) :=
  Nat.eq_sub_of_add_eq (card_filter_eventType_D_add_card_riseColumns hy)

end HJO.Paths
