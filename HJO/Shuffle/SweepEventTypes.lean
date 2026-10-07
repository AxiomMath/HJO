/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepRankOrder
public import HJO.Shuffle.SweepWidth
public meta import HJO.Attr

/-! # The event types at the reveal points, and the attack set as a sum of widths

`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv` evaluates the
total power of `q` the sweep word produces as `ĥ(P̂) - max t̂dinv(P̂)`, and the whole of its proof
is bookkeeping between three ways of counting the same pairs of north steps: the attack set `𝒜(P̂)`,
the marked pairs `S(P̂)`, and the widths `k_{P̂}` at the swept points. This file carries the first
layer of that bookkeeping — the event type at each of the two kinds of reveal point, the type-`C`
events as the marked pairs, and `#𝒜(P̂)` as a sum of widths — together with the strict form of the
rank comparison those arguments read.

## Main results

* `HJO.Paths.abovePointRank_lt_iff`: the rank order on the strip is lexicographic in
  `(ay - bx, x)` — `HJO.Paths.abovePointRank_lt_iff`.
* `HJO.Paths.eventType_top_of_column`: the top of the column at `s` is swept, of type `A` when the
  path rises there and `D` when it does not — `HJO.Paths.eventType_top_of_column`.
* `HJO.Paths.eventType_head_of_mem_northSteps`: the head of a north step is swept, of type `A` when
  the step ends its column and `C` when it does not —
  `HJO.Paths.eventType_head_of_mem_northSteps`.
* `HJO.Paths.eventType_stepFoot_eq_C_iff`: a foot carries type `C` exactly when it is the upper
  member of a marked pair — `HJO.Paths.eventType_stepFoot_eq_C_iff`.
* `HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one`:
  `#𝒜(P̂) = ∑_{P of type B or C} (k_{P̂}(P) - 1)` —
  `HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one`.
* `HJO.Paths.aboveMaxTdinv_eq_card_sweepAttack`: `max t̂dinv(P̂) = #𝒜(P̂)` —
  `HJO.Paths.aboveMaxTdinv_eq_card_sweepAttack`.

## Implementation notes

### The rank comparison

`HJO.Paths.abovePointRank_lt_iff` is the strict-inequality form of the lexicographic reading of the
rank, stated here at the `HJO.Paths` level where `HJO.ParkingFunctions.abovePointRank` lives.
`HJO.Mellit.abovePointRank_le_iff` (`HJO/Shuffle/SweepWitnessAppend.lean`) is the
weak-inequality sibling, stated far downstream in the Mellit layer for the rectangle-comparison
argument there. The two are the same computation, proved separately: the Mellit file sits
above this one in the import order, and importing it would pull the whole Mellit layer into a
`HJO.Paths` file.

### Reveal points, stated as the conjunction

`HJO.Paths.revealPoint` names the reveal point of a step and the two lemmas say both that
the point is swept and what its event type is. Both are stated here as one conjunction, in the shape
`HJO.Paths.revealPoint_rank_ne_and_eventType` and
`HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount` read them: those consumers hold
the membership and the type together, and splitting them would make every call site pair two lemmas.
The east case is stated at `(s, ŷ_{s+1})` rather than at `HJO.Paths.revealPoint y (.east s)` — the
two are the same point by `HJO.Paths.revealPoint_east` — because the ordinate is what the event type
is read against.

### The attack set as a sum over feet

`HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one` sums over the swept points of type `B` or
`C`, which by `HJO.Paths.mem_northSteps_iff_eventType` are exactly `HJO.Paths.northSteps y`; the
identification of the two `Finset`s is the first step of the proof. The sum is then transported to
`Fin (bN)` along `HJO.Paths.stepFoot`, and at each `t` the live set at the foot of `t` is `{t}`
together with the steps attacking `t`, so the summand `k_{P̂} - 1` counts the attacking pairs with
second coordinate `t`. The truncated subtraction is harmless exactly because `t` is always live at
its own foot, which is where `0 < ω` enters.

### The maximum over labellings

`max t̂dinv(P̂)` is a `Finset.sup` over the above-diagonal parking functions on the path, so
`HJO.Paths.aboveMaxTdinv_eq_card_sweepAttack` is a bound plus a witness. The bound is that a
labelling only ever maps the pairs `t̂dinv` counts *into* `𝒜(P̂)` —
`HJO.Paths.aboveLabelRank_eq_stepRank` says the rank `t̂dinv` reads at a label is
`HJO.Paths.stepRank` at the step that label marks, so the two window conditions are the same
condition. The witness is `HJO.Paths.rankParking`, the labelling by position in the increasing-rank
listing: there the rank comparison *is* the comparison of labels, so the counted pairs are all of
`𝒜(P̂)`. That it is a legal labelling at all is `HJO.Paths.isAboveParkingLabelling_stepIndex`, whose
content is that the rank increases upwards along a column.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### The rank order on the strip, strictly -/

/-- **The rank order on the strip is lexicographic in `(ay - bx, x)`.** This is
`HJO.Paths.abovePointRank_lt_iff`: `rk̂(x,y) < rk̂(x',y')` exactly when the diagonal excess
`ay - bx` is smaller, or the excesses agree and the abscissa is smaller.

The rank is `M(ay - bx) + x` with `M = (aN+1)N`, and on the strip `|x - x'| ≤ aN < M`, so the
multiplier decides unless the excesses agree. `0 < N` is needed and is not decoration: at `N = 0`
the multiplier is `0` and the rank ignores the ordinate, the same corner that makes
`HJO.Paths.abovePointRank_injOn` carry it. -/
@[hjo "lem_sweep_rank_lex"]
theorem abovePointRank_lt_iff (hN : 0 < N) {x k x' k' : ℕ} (hx : x ≤ a * N) (hx' : x' ≤ a * N) :
    ParkingFunctions.abovePointRank a b N x k <
        ParkingFunctions.abovePointRank a b N x' k' ↔
      ((a : ℤ) * k - b * x < (a : ℤ) * k' - b * x' ∨
        ((a : ℤ) * k - b * x = (a : ℤ) * k' - b * x' ∧ x < x')) := by
  have h1 : (x : ℤ) ≤ (a : ℤ) * N := by exact_mod_cast hx
  have h2 : (x' : ℤ) ≤ (a : ℤ) * N := by exact_mod_cast hx'
  have h3 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have h4 : (0 : ℤ) ≤ (a : ℤ) * N := by positivity
  have h5 : (0 : ℤ) ≤ (x : ℤ) := Int.natCast_nonneg _
  have h6 : (0 : ℤ) ≤ (x' : ℤ) := Int.natCast_nonneg _
  have hc : (a : ℤ) * N + 1 ≤ ((a : ℤ) * N + 1) * N := by nlinarith
  simp only [ParkingFunctions.abovePointRank]
  constructor
  · intro h
    rcases lt_trichotomy ((a : ℤ) * k - b * x) ((a : ℤ) * k' - b * x') with hlt | heq | hgt
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      have : (x : ℤ) < x' := by nlinarith
      exact_mod_cast this
    · exact absurd h (by nlinarith)
  · rintro (hlt | ⟨heq, hxx⟩)
    · nlinarith
    · have hxz : (x : ℤ) < x' := by exact_mod_cast hxx
      nlinarith

/-! ### The event type at a reveal point -/

/-- **The top of a column is swept, and its type is `A` or `D`.** This is
`HJO.Paths.eventType_top_of_column`: for `s < aN` the point `(s, ŷ_{s+1})` — the left endpoint of
the east step at `s`, which is `HJO.Paths.revealPoint y (.east s)` — lies in `Sw(P̂)`, and its event
type is `A` when the path rises in the column at `s` and `D` when it does not.

Its outgoing letter is `E` whatever the heights do, the ordinate being `ŷ_{s+1}` itself, so only the
incoming letter is in question and that is the comparison `ŷ_s < ŷ_{s+1}`. -/
@[hjo "lem_sweep_reveal_east_type"]
theorem eventType_top_of_column {y : Heights a b N} (hy : IsAboveDiagonal y) {s : ℕ}
    (hs : s < a * N) :
    (s, ht y (s + 1)) ∈ sweptRegion y ∧
      eventType y (s, ht y (s + 1))
        = if ht y s < ht y (s + 1) then EventType.A else EventType.D := by
  have hmono : ht y s ≤ ht y (s + 1) := ht_mono hy.2.2.1 (Nat.le_succ s)
  refine ⟨mem_sweptRegion.2 ⟨hs.le, ?_, le_rfl⟩, ?_⟩
  · calc b * s ≤ b * (s + 1) := Nat.mul_le_mul_left b (by omega)
      _ ≤ a * ht y (s + 1) := hy.2.2.2 (s + 1) (by omega)
  · rw [eventType]
    split_ifs <;> simp_all <;> omega

/-- **The head of a north step is swept, and its type is `A` or `C`.** This is
`HJO.Paths.eventType_head_of_mem_northSteps`: for a north step `(c,i)` the point `(c, i+1)` — its
head, which is `HJO.Paths.revealPoint y (.north (c,i))` — lies in `Sw(P̂)`, and its event type is
`A` when the step ends its column, `i + 1 = ŷ_{c+1}`, and `C` when another north step follows it,
`i + 1 < ŷ_{c+1}`.

Its incoming letter is `N` whatever the heights do, the foot being at or above `ŷ_c`, so only the
outgoing letter is in question; the column bound `c < aN` of `HJO.Paths.northSteps` is what makes
that letter readable at all. The membership half is
`HJO.Paths.mem_sweptRegion_of_mem_northSteps`. -/
@[hjo "lem_sweep_reveal_north_type"]
theorem eventType_head_of_mem_northSteps {y : Heights a b N} (hy : IsAboveDiagonal y) {u : ℕ × ℕ}
    (hu : u ∈ northSteps y) :
    (u.1, u.2 + 1) ∈ sweptRegion y ∧
      eventType y (u.1, u.2 + 1)
        = if u.2 + 1 = ht y (u.1 + 1) then EventType.A else EventType.C := by
  obtain ⟨h1, h2, h3⟩ := mem_northSteps_iff.1 hu
  refine ⟨(mem_sweptRegion_of_mem_northSteps hy hu).2, ?_⟩
  rw [eventType]
  split_ifs <;> simp_all <;> omega

/-! ### The type-`C` events are the marked pairs -/

/-- **A foot carries type `C` exactly when it is the upper member of a marked pair.** This is
`HJO.Paths.eventType_stepFoot_eq_C_iff`: `ev_{P̂}(u_t) = C` iff `(s,t) ∈ S(P̂)` for some `s`.

By `HJO.Paths.mem_northSteps_iff_eventType` a foot has type `B` or `C`, and by
`HJO.Paths.isSweepHead_iff_eventType` it has type `A` or `C` exactly when it is the head of a north
step; so among the feet, type `C` *is* being a head, and being the head of a north step is
same-column vertical adjacency, which is what `HJO.Paths.sweepMarked` records. The `i < j` needs no
transporting: on the height indexing it is `t = s + 1`, which `HJO.Paths.sweepMarked` writes out. -/
@[hjo "lem_sweep_type_c_marked"]
theorem eventType_stepFoot_eq_C_iff {y : Heights a b N} (hy : IsAboveDiagonal y)
    (t : Fin (b * N)) :
    eventType y (stepFoot y t) = EventType.C ↔ ∃ s : Fin (b * N), (s, t) ∈ sweepMarked y := by
  have hmem : stepFoot y t ∈ northSteps y := by
    rw [northSteps_eq_image hy]
    exact mem_image_of_mem _ (mem_univ t)
  have hsw : stepFoot y t ∈ sweptRegion y := (mem_sweptRegion_of_mem_northSteps hy hmem).1
  have hfoot := (mem_northSteps_iff_eventType hsw).1 hmem
  have hhead := isSweepHead_iff_eventType hy hsw
  constructor
  · intro hC
    obtain ⟨w, hw, hwP⟩ := hhead.2 (Or.inr hC)
    rw [northSteps_eq_image hy] at hw
    obtain ⟨s, -, rfl⟩ := mem_image.1 hw
    refine ⟨s, ?_⟩
    simp only [sweepMarked, mem_filter, mem_univ, true_and]
    have e1 : ParkingFunctions.aboveColumn y (s : ℕ) = ParkingFunctions.aboveColumn y (t : ℕ) := by
      simpa using congrArg Prod.fst hwP
    have e2 : (s : ℕ) + 1 = (t : ℕ) := by simpa using congrArg Prod.snd hwP
    exact ⟨e1.symm, e2.symm⟩
  · rintro ⟨s, hs⟩
    simp only [sweepMarked, mem_filter, mem_univ, true_and] at hs
    have hsmem : stepFoot y s ∈ northSteps y := by
      rw [northSteps_eq_image hy]
      exact mem_image_of_mem _ (mem_univ s)
    have hhd : IsSweepHead y (stepFoot y t) := by
      refine ⟨stepFoot y s, hsmem, ?_⟩
      rw [stepFoot, stepFoot, Prod.ext_iff]
      exact ⟨hs.1.symm, by omega⟩
    rcases hhead.1 hhd with hA | hC
    · rcases hfoot with hB | hC'
      · rw [hA] at hB; exact absurd hB (by simp)
      · exact hC'
    · exact hC

/-! ### The attack set as a sum of widths over the feet -/

/-- **The live set at a foot is that step together with the steps attacking it.** The step `t` is
live at its own foot because the window is positive, and another step is live there exactly when it
is ranked below `t` and within the window of it — which is the defining condition of
`HJO.Paths.sweepAttack` at `(s,t)`. -/
private theorem liveSteps_stepFoot {y : Heights a b N} (hy : IsAboveDiagonal y)
    (t : Fin (b * N)) :
    liveSteps y (stepFoot y t)
      = ((insert t {s ∈ (univ : Finset (Fin (b * N))) | (s, t) ∈ sweepAttack y}).image
        (stepFoot y)) := by
  have h0 : 0 < a * N := mul_pos_of_isAboveDiagonal hy t
  have ha : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have hω : (0 : ℤ) < (attackWindow a N : ℤ) := by
    exact_mod_cast attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
  ext u
  simp only [liveSteps, mem_filter, mem_image, mem_insert, mem_univ, true_and, sweepAttack,
    northSteps_eq_image hy]
  constructor
  · rintro ⟨hu, hu1, hu2⟩
    obtain ⟨s, rfl⟩ := hu
    refine ⟨s, ?_, rfl⟩
    rcases eq_or_ne s t with rfl | hne
    · exact Or.inl rfl
    · refine Or.inr ⟨?_, ?_⟩
      · exact lt_of_le_of_ne hu1 fun hc =>
          hne (stepRank_injective_of_isAboveDiagonal hy hc)
      · exact hu2
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨s, rfl⟩, ?_, ?_⟩
    · rcases hs with rfl | ⟨h1, -⟩
      · exact le_rfl
      · exact h1.le
    · rcases hs with rfl | ⟨-, h2⟩
      · exact lt_add_of_pos_right _ hω
      · exact h2

/-- **The width at a foot is one more than the number of steps attacking it.** The `+1` is the step
itself, live at its own foot; the truncated subtraction of
`HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one` is therefore harmless. -/
private theorem sweepWidth_stepFoot {y : Heights a b N} (hy : IsAboveDiagonal y)
    (t : Fin (b * N)) :
    sweepWidth y (stepFoot y t)
      = #{s ∈ (univ : Finset (Fin (b * N))) | (s, t) ∈ sweepAttack y} + 1 := by
  have hnot : t ∉ {s ∈ (univ : Finset (Fin (b * N))) | (s, t) ∈ sweepAttack y} := by
    intro h
    have hat := (mem_filter.1 h).2
    rw [sweepAttack, mem_filter] at hat
    exact absurd hat.2.1 (lt_irrefl _)
  rw [sweepWidth, liveSteps_stepFoot hy t,
    card_image_of_injective _ (stepFoot_injective y), card_insert_of_notMem hnot]

/-- **`#𝒜(P̂)` is the sum of `k_{P̂}(P) - 1` over the swept points of type `B` or `C`.** This is
`HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one`.

Those points are exactly the feet of the north steps, by `HJO.Paths.mem_northSteps_iff_eventType`;
at the foot of `t` the live set is `{t}` together with the steps attacking `t`, so the summand
counts the attacking pairs whose second coordinate is `t`, and summing over `t` counts each pair of
`𝒜(P̂)` once. -/
@[hjo "lem_sweep_attack_feet"]
theorem card_sweepAttack_eq_sum_sweepWidth_sub_one {y : Heights a b N} (hy : IsAboveDiagonal y) :
    #(sweepAttack y)
      = ∑ P ∈ {P ∈ sweptRegion y |
          eventType y P = EventType.B ∨ eventType y P = EventType.C}, (sweepWidth y P - 1) := by
  have hfilter : {P ∈ sweptRegion y |
      eventType y P = EventType.B ∨ eventType y P = EventType.C} = northSteps y := by
    ext P
    simp only [mem_filter]
    constructor
    · rintro ⟨hP, hev⟩
      exact (mem_northSteps_iff_eventType hP).2 hev
    · intro hP
      have hs := (mem_sweptRegion_of_mem_northSteps hy hP).1
      exact ⟨hs, (mem_northSteps_iff_eventType hs).1 hP⟩
  rw [hfilter, northSteps_eq_image hy,
    Finset.sum_image fun s _ t _ h => stepFoot_injective y h]
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd)
    (t := (univ : Finset (Fin (b * N)))) fun p _ => mem_univ p.2]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [sweepWidth_stepFoot hy t, Nat.add_sub_cancel]
  have himg : {p ∈ sweepAttack y | p.2 = t}
      = {s ∈ (univ : Finset (Fin (b * N))) | (s, t) ∈ sweepAttack y}.image fun s => (s, t) := by
    ext p
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨hp, rfl⟩
      exact ⟨p.1, hp, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hs, rfl⟩
  rw [himg, card_image_of_injective _ fun s s' h => by simpa using congrArg Prod.fst h]

/-! ### The maximal temporary dinv is the size of the attack set

`max t̂dinv(P̂)` is the largest `t̂dinv` over the above-diagonal parking functions on the path.
`t̂dinv` counts pairs of *labels* satisfying the window condition, and a labelling turns that into a
count of pairs of *north steps*; the pairs it can produce are always inside `𝒜(P̂)`, and the
labelling by rank-order position produces all of them. So the maximum is `#𝒜(P̂)`. -/

section MaxTdinv

variable {a b N : ℕ}

/-- The rank `t̂dinv` reads at a label is the rank of the north step that label marks, which is
`HJO.Paths.stepRank` at that step: the two expressions are the same. -/
theorem aboveLabelRank_eq_stepRank (π : ParkingFunctions.AboveParkingFunction a b N)
    (i : Fin (b * N)) :
    ParkingFunctions.aboveLabelRank π i
      = stepRank (ParkingFunctions.abovePath π) (ParkingFunctions.aboveLabelStep π i) := rfl

/-- Naming a north step by its label is injective, `HJO.ParkingFunctions.aboveLabelStep` being the
inverse of a bijection. -/
theorem aboveLabelStep_injective (π : ParkingFunctions.AboveParkingFunction a b N) :
    Function.Injective (ParkingFunctions.aboveLabelStep π) :=
  Function.LeftInverse.injective (ParkingFunctions.aboveLabel_aboveLabelStep π)

/-- **Labelling the north steps by their rank-order position is an above-diagonal parking
labelling.** It is a bijection by `HJO.Paths.stepIndex_injective`, and it increases upwards along a
column because the rank does: two north steps of one column are compared by their ordinates. -/
theorem isAboveParkingLabelling_stepIndex {y : Heights a b N} (hy : IsAboveDiagonal y) :
    ParkingFunctions.IsAboveParkingLabelling y (stepIndex y) := by
  refine ⟨Finite.injective_iff_bijective.1 (stepIndex_injective hy), fun s t hst hcol => ?_⟩
  rw [stepIndex_lt_stepIndex_iff, stepRank, stepRank, hcol]
  have h0 : 0 < a * N := mul_pos_of_isAboveDiagonal hy s
  have ha : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at h0
  have ha' : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  have hM : (0 : ℤ) < ((a : ℤ) * N + 1) * N := by positivity
  have hlt : ((s : ℕ) : ℤ) < ((t : ℕ) : ℤ) := by exact_mod_cast (hst : (s : ℕ) < (t : ℕ))
  simp only [ParkingFunctions.abovePointRank]
  nlinarith [mul_pos hM (mul_pos ha' (sub_pos.2 hlt))]

/-- The above-diagonal parking function labelling each north step by its position in the
increasing-rank listing. This is the labelling the proof of
`HJO.Paths.aboveMaxTdinv_eq_card_sweepAttack` exhibits to attain the maximum. -/
def rankParking {y : Heights a b N} (hy : IsAboveDiagonal y) :
    ParkingFunctions.AboveParkingFunction a b N :=
  ⟨(y, stepIndex y), hy, isAboveParkingLabelling_stepIndex hy⟩

@[simp]
theorem abovePath_rankParking {y : Heights a b N} (hy : IsAboveDiagonal y) :
    ParkingFunctions.abovePath (rankParking hy) = y := rfl

@[simp]
theorem aboveLabel_rankParking {y : Heights a b N} (hy : IsAboveDiagonal y) (i : Fin (b * N)) :
    ParkingFunctions.aboveLabel (rankParking hy) i = stepIndex y i := rfl

/-- **Every labelling's `t̂dinv` is at most `#𝒜(P̂)`.** A pair of labels counted by `t̂dinv` gives,
through the steps those labels mark, a pair of north steps satisfying the defining condition of
`HJO.Paths.sweepAttack`; the assignment is injective because naming a step by its label is. -/
theorem aboveTdinv_le_card_sweepAttack (π : ParkingFunctions.AboveParkingFunction a b N) :
    ParkingFunctions.aboveTdinv π ≤ #(sweepAttack (ParkingFunctions.abovePath π)) := by
  rw [ParkingFunctions.aboveTdinv]
  refine Finset.card_le_card_of_injOn
    (fun p => (ParkingFunctions.aboveLabelStep π p.1, ParkingFunctions.aboveLabelStep π p.2))
    (fun p hp => ?_) (fun p hp q hq h => ?_)
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨-, h1, h2⟩ := hp
    rw [aboveLabelRank_eq_stepRank, aboveLabelRank_eq_stepRank] at h1 h2
    simp only [Finset.mem_coe, sweepAttack, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h1, by rw [cast_attackWindow]; exact h2⟩
  · have e1 := aboveLabelStep_injective π (congrArg Prod.fst h)
    have e2 := aboveLabelStep_injective π (congrArg Prod.snd h)
    exact Prod.ext e1 e2

/-- **The rank-order labelling attains `#𝒜(P̂)`.** At that labelling the step marked by the label
`i` is the `i`-th in the increasing-rank listing, so the rank comparison of `t̂dinv` *is* the
comparison `i < j` of labels; the counted pairs are then exactly `𝒜(P̂)`, read through the
bijection. -/
theorem aboveTdinv_rankParking {y : Heights a b N} (hy : IsAboveDiagonal y) :
    ParkingFunctions.aboveTdinv (rankParking hy) = #(sweepAttack y) := by
  have hback : ∀ q : Fin (b * N),
      ParkingFunctions.aboveLabelStep (rankParking hy) (stepIndex y q) = q := fun q => by
    have h := ParkingFunctions.aboveLabelStep_aboveLabel (rankParking hy) q
    rwa [aboveLabel_rankParking] at h
  have hstep : ∀ i : Fin (b * N),
      stepIndex y (ParkingFunctions.aboveLabelStep (rankParking hy) i) = i := fun i => by
    have h := ParkingFunctions.aboveLabel_aboveLabelStep (rankParking hy) i
    rwa [aboveLabel_rankParking] at h
  have hrank : ∀ i : Fin (b * N), ParkingFunctions.aboveLabelRank (rankParking hy) i
      = stepRank y (ParkingFunctions.aboveLabelStep (rankParking hy) i) := fun _ => rfl
  rw [ParkingFunctions.aboveTdinv]
  refine Finset.card_nbij'
    (fun p => (ParkingFunctions.aboveLabelStep (rankParking hy) p.1,
      ParkingFunctions.aboveLabelStep (rankParking hy) p.2))
    (fun q => (stepIndex y q.1, stepIndex y q.2)) (fun p hp => ?_) (fun q hq => ?_)
    (fun p hp => ?_) (fun q hq => ?_)
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨-, h1, h2⟩ := hp
    rw [hrank, hrank] at h1 h2
    simp only [Finset.mem_coe, sweepAttack, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h1, by rw [cast_attackWindow]; exact h2⟩
  · simp only [Finset.mem_coe, sweepAttack, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [cast_attackWindow] at hq2
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(stepIndex_lt_stepIndex_iff y q.1 q.2).2 hq1, ?_, ?_⟩
    · rw [hrank, hrank, hback, hback]
      exact hq1
    · rw [hrank, hrank, hback, hback]
      exact hq2
  · exact Prod.ext (hstep p.1) (hstep p.2)
  · exact Prod.ext (hback q.1) (hback q.2)

/-- **`max t̂dinv(P̂) = #𝒜(P̂)`.** `HJO.Paths.aboveMaxTdinv_eq_card_sweepAttack`: the largest
temporary dinv over the above-diagonal parking functions on a path is the size of its attack set.
Every labelling gives at most that many pairs, and the labelling by rank-order position gives all
of them. -/
@[hjo "lem_sweep_maxtdinv_attacks"]
theorem aboveMaxTdinv_eq_card_sweepAttack {y : Heights a b N} (hy : IsAboveDiagonal y) :
    ParkingFunctions.aboveMaxTdinv y = #(sweepAttack y) := by
  rw [ParkingFunctions.aboveMaxTdinv]
  refine le_antisymm (Finset.sup_le fun π hπ => ?_) ?_
  · have hpath : ParkingFunctions.abovePath π = y := (Finset.mem_filter.1 hπ).2
    have hle := aboveTdinv_le_card_sweepAttack π
    rwa [hpath] at hle
  · rw [← aboveTdinv_rankParking hy]
    exact Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)

end MaxTdinv

end HJO.Paths
