/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepBalanceLeft
public import HJO.Shuffle.SweepHookEvents
public meta import HJO.Attr

/-! # The power of `q` the sweep produces

The sweep process applies `q^{a_{P̂}(P)}` at a type-`D` event and `q^{-a_{P̂}(P)}` at a type-`C`
one, and nothing at the other three types, so the exponent it accumulates over a whole path is
`Σ_D - Σ_C`. This file proves that exponent to be `ĥ(P̂) - max t̂dinv(P̂)`, which is the form
`HJO.Mellit.sweepComputes` reads and the form Mellit's section states (as `dinv(π) - maxtdinv(π)`).

Three statements, in dependency order:

* `HJO.Paths.sweepRight_add_leftEastCount_add_one`: at a type-`C` event
  `a_{P̂}(P) + a^*_{P̂}(P) + 1 = k_{P̂}(P)`.
* `HJO.Paths.sum_sweepRight_add_leftEastCount_A_eq_sum_sweepWidth_sub_one_B`:
  `∑_A (a_{P̂} + a^*_{P̂}) = ∑_B (k_{P̂} - 1)`.
* `HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv`:
  `Σ_D - Σ_C = ĥ(P̂) - max t̂dinv(P̂)`.

## Main results

* `HJO.Paths.sweepRight_add_leftEastCount_add_one`.
* `HJO.Paths.sum_sweepRight_add_leftEastCount_A_eq_sum_sweepWidth_sub_one_B`:
  `HJO.Paths.sum_sweepRight_add_leftEastCount_A_eq_sum_sweepWidth_sub_one_B`.
* `HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv`:
  `HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv`.

## Implementation notes

**Where the subtractions go.** The corner balance is usually written as
`a_{P̂}(P) + a^*_{P̂}(P) = k_{P̂}(P) - 1`; here it is `… + 1 = k_{P̂}(P)`, which on `ℕ` says that
and also that `k_{P̂}(P) ≥ 1`, so nothing is weakened and the truncated subtraction of `ℕ` stays
out of a statement where it would be a trap. Inside a *sum* the `- 1` is harmless and is kept,
matching `HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one`; the one place the truncation
must be discharged is `HJO.Paths.sum_sweepWidth_eventType_C`, and what discharges it is the corner
balance itself.
`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv`'s own
difference is genuinely signed — it is negative on `ŷ = (0, 3, 3, 6, 6)` at `a = 2`, `b = 3`,
`N = 2` — so that statement is in `ℤ`.

**The corner balance is the type-`A` balance with the middle part a point instead of empty.** Split
`Live_{P̂}(P)` by whether a member's column is greater than, equal to, or smaller than `x`. The
outer two parts are `a_{P̂}(P)` by `HJO.Paths.sweepRight` and `a^*_{P̂}(P)` by
`HJO.Paths.leftEastCount_eq_card_filter_fst_lt`, as at type `A`. What differs is the middle: at type
`C` the point `P`
*is* a north step (`HJO.Paths.mem_northSteps_iff_eventType`), it is live at itself because `ω > 0`,
and by `HJO.Paths.mem_liveSteps_iff_eq_of_fst_eq` it is the only live step of its column — so the
middle part is `{P}` where at type `A` it was empty. The two lemmas are therefore one argument run
with two readings of `HJO.Paths.mem_liveSteps_iff_eq_of_fst_eq`.

**`ab_balance` is bulk accounting and cannot be made pointwise.** The two
index sets have equal size (`HJO.Paths.card_filter_eventType_A`) yet no term-by-term match exists:
pairing the type-`A` and type-`B` points in decreasing rank fails at 142 pairs of an enumeration. So
the proof is four cancelling identities — `HJO.Paths.sweepRight_add_leftEastCount` pointwise, then
`HJO.Paths.sum_sweepWidth_head_eq_card_sweepAttack_add_card_sweepMarked`,
`HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one` and
`HJO.Paths.card_sweepMarked_eq_card_filter_eventType_C` in bulk — and the type-`C` sums cancel
between the last three. Once the four are in hand `omega` finishes, which is the whole reason the
four were stated as sums over event-type filters rather than over listings.

**Where the hypotheses `0 < a`, `0 < b` of
`HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount` go.**
`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv` does not carry
them. Both degenerate cases collapse to `bN = 0` — for `b = 0` at once, and for `a = 0` because
`ŷ_0 = 0` and `ŷ_{aN} = bN` then say `bN = 0` — and there the path has no north step, so every
`a_{P̂}(P)` is `0`, `#𝒜(P̂)` is `0` for want of an index, and `ĥ(P̂)` is `0` because the cell window
`1 ≤ j ≤ bN` is empty. That case is dispatched in `HJO.Paths.qpower_of_mul_eq_zero` rather than
assumed away, so the two balances and the exponent identity hold on every height vector.

## References

A. Mellit, *Toric
braids and `(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### Splitting a sum over two event types -/

/-- A sum over the swept points of either of two distinct event types splits as the two sums. The
event types being constructors of an inductive type, the two index sets are disjoint. -/
theorem sum_filter_eventType_or {y : Heights a b N} {e f : EventType} (hef : e ≠ f)
    (g : ℕ × ℕ → ℕ) :
    ∑ P ∈ {P ∈ sweptRegion y | eventType y P = e ∨ eventType y P = f}, g P
      = (∑ P ∈ {P ∈ sweptRegion y | eventType y P = e}, g P)
        + ∑ P ∈ {P ∈ sweptRegion y | eventType y P = f}, g P := by
  have hdisj : Disjoint {P ∈ sweptRegion y | eventType y P = e}
      {P ∈ sweptRegion y | eventType y P = f} :=
    disjoint_left.2 fun P hP hP' =>
      hef ((mem_filter.1 hP).2.symm.trans (mem_filter.1 hP').2)
  have hunion : {P ∈ sweptRegion y | eventType y P = e ∨ eventType y P = f}
      = {P ∈ sweptRegion y | eventType y P = e} ∪ {P ∈ sweptRegion y | eventType y P = f} := by
    ext P
    simp only [mem_filter, mem_union]
    tauto
  rw [hunion, Finset.sum_union hdisj]

/-! ### The balance at a corner event -/

/-- **The balance at a corner event**: `a_{P̂}(P) + a^*_{P̂}(P) + 1 = k_{P̂}(P)`. This is the
usual `= k_{P̂}(P) - 1` with the truncated subtraction of `ℕ`
moved to the other side.

Split the live steps by whether their column is greater than, equal to, or smaller than `x`. The
first part is `a_{P̂}(P)` by `HJO.Paths.sweepRight` and the third is `a^*_{P̂}(P)` by
`HJO.Paths.leftEastCount_eq_card_filter_fst_lt`, as at a type-`A` event. The middle part is the
single point `P`: a type-`C` point is a north step (`HJO.Paths.mem_northSteps_iff_eventType`), it is
live at itself because the window is positive, and by `HJO.Paths.mem_liveSteps_iff_eq_of_fst_eq` no
other north step of its column is. -/
@[hjo "lem_sweep_corner_balance"]
theorem sweepRight_add_leftEastCount_add_one {y : Heights a b N} (hy : IsAboveDiagonal y)
    {P : ℕ × ℕ} (hP : P ∈ sweptRegion y) (hC : eventType y P = EventType.C) :
    sweepRight y P + leftEastCount y P + 1 = sweepWidth y P := by
  have hE : eventType y P ≠ EventType.E := by rw [hC]; decide
  have hPn : P ∈ northSteps y := (mem_northSteps_iff_eventType hP).2 (Or.inr hC)
  have hPlive : P ∈ liveSteps y P := (mem_liveSteps_iff_eq_of_fst_eq hPn rfl).2 rfl
  have hins : {u ∈ liveSteps y P | ¬ P.1 < u.1} = insert P {u ∈ liveSteps y P | u.1 < P.1} := by
    ext u
    simp only [mem_filter, mem_insert, not_lt]
    constructor
    · rintro ⟨hu, hle⟩
      rcases eq_or_lt_of_le hle with heq | hlt
      · exact Or.inl ((mem_liveSteps_iff_eq_of_fst_eq (liveSteps_subset y P hu) heq).1 hu)
      · exact Or.inr ⟨hu, hlt⟩
    · rintro (rfl | ⟨hu, hlt⟩)
      · exact ⟨hPlive, le_rfl⟩
      · exact ⟨hu, hlt.le⟩
  have hnot : P ∉ {u ∈ liveSteps y P | u.1 < P.1} := fun h =>
    absurd (mem_filter.1 h).2 (lt_irrefl _)
  have hsplit : #{u ∈ liveSteps y P | P.1 < u.1} + #{u ∈ liveSteps y P | ¬ P.1 < u.1}
      = #(liveSteps y P) := card_filter_add_card_filter_not _
  rw [hins, card_insert_of_notMem hnot] at hsplit
  rw [sweepWidth, sweepRight, leftEastCount_eq_card_filter_fst_lt hy hP hE]
  omega

/-- **The widths at the corner events, with the `- 1` discharged.** `∑_C k_{P̂}(P)` is
`∑_C (k_{P̂}(P) - 1)` plus the number of type-`C` points, because
`HJO.Paths.sweepRight_add_leftEastCount_add_one` makes every one of those widths at least `1`. This
is the only place the truncated subtraction of
`HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one` has to be undone. -/
theorem sum_sweepWidth_eventType_C {y : Heights a b N} (hy : IsAboveDiagonal y) :
    ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.C}, sweepWidth y P
      = (∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.C}, (sweepWidth y P - 1))
        + #{P ∈ sweptRegion y | eventType y P = EventType.C} := by
  rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hPs, hPC⟩ := mem_filter.1 hP
  have := sweepRight_add_leftEastCount_add_one hy hPs hPC
  omega

/-! ### The balance between the reveal and the release events -/

/-- **The balance between the reveal and release events**:
`∑_A (a_{P̂}(P) + a^*_{P̂}(P)) = ∑_B (k_{P̂}(P) - 1)`.
`HJO.Paths.sum_sweepRight_add_leftEastCount_A_eq_sum_sweepWidth_sub_one_B`.

The accounting is necessarily in bulk. The two index sets have the same size
(`HJO.Paths.card_filter_eventType_A`) but there is no term-by-term match — pairing
them in decreasing rank fails at `142` pairs of its enumeration. So:
`HJO.Paths.sweepRight_add_leftEastCount` rewrites the left side as `∑_A k_{P̂}(P)`;
`HJO.Paths.sum_sweepWidth_head_eq_card_sweepAttack_add_card_sweepMarked` gives
`∑_A k_{P̂} + ∑_C k_{P̂} = #𝒜(P̂) + #S(P̂)`; `HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one`
splits `#𝒜(P̂)` as `∑_B (k_{P̂} - 1) + ∑_C (k_{P̂} - 1)`; and
`HJO.Paths.card_sweepMarked_eq_card_filter_eventType_C` identifies `#S(P̂)` with the number of
type-`C` points, which is exactly what `HJO.Paths.sum_sweepWidth_eventType_C` needs to cancel the
type-`C` sums off both sides. -/
@[hjo "lem_sweep_ab_balance"]
theorem sum_sweepRight_add_leftEastCount_A_eq_sum_sweepWidth_sub_one_B {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.A},
        (sweepRight y P + leftEastCount y P)
      = ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.B}, (sweepWidth y P - 1) := by
  have hA : ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.A},
        (sweepRight y P + leftEastCount y P)
      = ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.A}, sweepWidth y P :=
    Finset.sum_congr rfl fun P hP => by
      obtain ⟨hPs, hPA⟩ := mem_filter.1 hP
      exact sweepRight_add_leftEastCount hy hPs hPA
  have hhead := sum_sweepWidth_head_eq_card_sweepAttack_add_card_sweepMarked hy
  rw [sum_filter_eventType_or (show EventType.A ≠ EventType.C by decide)] at hhead
  have hatk := card_sweepAttack_eq_sum_sweepWidth_sub_one hy
  rw [sum_filter_eventType_or (show EventType.B ≠ EventType.C by decide)] at hatk
  have hmk := card_sweepMarked_eq_card_filter_eventType_C hy
  have hCk := sum_sweepWidth_eventType_C hy
  rw [hA]
  omega

/-! ### The powers of `q` produced by the sweep -/

/-- The degenerate case of
`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv`, where the
rectangle has no row: the path has no north step, so every `a_{P̂}(P)` vanishes, `#𝒜(P̂)` vanishes
for want of an index, and `ĥ(P̂)` vanishes because the cell window `1 ≤ j ≤ bN` is empty. -/
theorem qpower_of_mul_eq_zero {y : Heights a b N} (hy : IsAboveDiagonal y) (hbN : b * N = 0) :
    ((∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.D}, sweepRight y P : ℕ) : ℤ) -
        ((∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.C}, sweepRight y P : ℕ) : ℤ) =
      (aboveHookCount y : ℤ) - (ParkingFunctions.aboveMaxTdinv y : ℤ) := by
  have hns : northSteps y = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun u hu => ?_
    obtain ⟨-, -, h2⟩ := mem_northSteps_iff.1 hu
    have := ht_le_mul y (u.1 + 1)
    omega
  have hlv : ∀ Q : ℕ × ℕ, liveSteps y Q = ∅ := fun Q =>
    subset_empty.1 (hns ▸ liveSteps_subset y Q)
  have hright : ∀ Q : ℕ × ℕ, sweepRight y Q = 0 := fun Q => by
    rw [sweepRight, hlv Q, filter_empty, card_empty]
  have hhook : aboveHookCount y = 0 := by
    rw [aboveHookCount, card_eq_zero]
    refine eq_empty_iff_forall_notMem.2 fun p hp => ?_
    obtain ⟨-, -, h3, h4⟩ := mem_aboveCells.1 (mem_filter.1 hp).1
    omega
  have hmax : ParkingFunctions.aboveMaxTdinv y = 0 := by
    rw [aboveMaxTdinv_eq_card_sweepAttack hy, card_eq_zero]
    refine eq_empty_iff_forall_notMem.2 fun p _ => ?_
    have := p.1.isLt
    omega
  rw [Finset.sum_eq_zero fun Q _ => hright Q, Finset.sum_eq_zero fun Q _ => hright Q, hhook, hmax]

/-- **The powers of `q` produced by the sweep**: with `Σ_C` and `Σ_D` the sums of `a_{P̂}(P)` over
the swept points of event type `C` and of event type `D`,
`Σ_D - Σ_C = ĥ(P̂) - max t̂dinv(P̂)`.
`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv`.

The difference is taken in `ℤ` and is genuinely signed: it is negative on the path
`ŷ = (0, 3, 3, 6, 6)` of `a = 2`, `b = 3`, `N = 2`.

`HJO.Paths.aboveMaxTdinv_eq_card_sweepAttack` turns `max t̂dinv(P̂)` into `#𝒜(P̂)` and
`HJO.Paths.card_sweepAttack_eq_sum_sweepWidth_sub_one` turns that into
`∑_B (k_{P̂} - 1) + ∑_C (k_{P̂} - 1)`;
`HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount` turns `ĥ(P̂)` into
`∑_{A,D} a_{P̂} + ∑_{A,C} a^*_{P̂}`. After the `∑_D a_{P̂}` on the two sides cancels, what is left
is `∑_A (a_{P̂} + a^*_{P̂}) + ∑_C (a_{P̂} + a^*_{P̂}) = ∑_B (k_{P̂} - 1) + ∑_C (k_{P̂} - 1)`, whose
type-`C` half is `HJO.Paths.sweepRight_add_leftEastCount_add_one` summed and whose type-`A` half is
`HJO.Paths.sum_sweepRight_add_leftEastCount_A_eq_sum_sweepWidth_sub_one_B`.

The `0 < a` and `0 < b` of `HJO.Paths.aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount` are
not carried: both collapse to `bN = 0`, and `HJO.Paths.qpower_of_mul_eq_zero` settles that case,
where every quantity in sight is `0`. -/
@[hjo "lem_sweep_qpower"]
theorem sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv
    {y : Heights a b N} (hy : IsAboveDiagonal y) :
    ((∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.D}, sweepRight y P : ℕ) : ℤ) -
        ((∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.C}, sweepRight y P : ℕ) : ℤ) =
      (aboveHookCount y : ℤ) - (ParkingFunctions.aboveMaxTdinv y : ℤ) := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · exact qpower_of_mul_eq_zero hy (by rw [hb, Nat.zero_mul])
  rcases Nat.eq_zero_or_pos a with ha | ha
  · refine qpower_of_mul_eq_zero hy ?_
    have h1 : a * N = 0 := by rw [ha, Nat.zero_mul]
    have h2 := hy.2.1
    rw [h1, hy.1] at h2
    exact h2.symm
  have hhook := aboveHookCount_eq_sum_sweepRight_add_sum_leftEastCount hy ha hb
  rw [sum_filter_eventType_or (show EventType.A ≠ EventType.D by decide),
    sum_filter_eventType_or (show EventType.A ≠ EventType.C by decide)] at hhook
  have hatk := card_sweepAttack_eq_sum_sweepWidth_sub_one hy
  rw [sum_filter_eventType_or (show EventType.B ≠ EventType.C by decide)] at hatk
  have hab := sum_sweepRight_add_leftEastCount_A_eq_sum_sweepWidth_sub_one_B hy
  rw [Finset.sum_add_distrib] at hab
  have hCk := sum_sweepWidth_eventType_C hy
  have hCb : (∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.C},
        (sweepRight y P + leftEastCount y P))
      + #{P ∈ sweptRegion y | eventType y P = EventType.C}
      = ∑ P ∈ {P ∈ sweptRegion y | eventType y P = EventType.C}, sweepWidth y P := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun P hP => ?_
    obtain ⟨hPs, hPC⟩ := mem_filter.1 hP
    exact sweepRight_add_leftEastCount_add_one hy hPs hPC
  rw [Finset.sum_add_distrib] at hCb
  rw [aboveMaxTdinv_eq_card_sweepAttack hy, hatk, hhook]
  omega

end HJO.Paths
