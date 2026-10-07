/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepTruncate

/-!
# The band interleaving, in closed form: the base's correction to the tail's widths

`HJO.Mellit.sweepAppend_of_forall_band` reduces `HJO.Mellit.SweepAppend` to a band identity, and
inside the band the events of the base path and the events of the appended tail **interleave**. The
rank order on the strip is lexicographic in `(ay - bx, x)` (`HJO.Mellit.abovePointRank_le_iff`), so
the band word runs through the excess levels `1, …, a·bA` and, within each level, through increasing
abscissa — which puts the base's points of that level (abscissa `< aN`) before the tail's (abscissa
`≥ aN`). The band word is therefore an alternating product of `2·a·bA` layers, and neither the base
layer nor the tail layer is the corresponding word of the path it comes from: each is read at widths
the *other* path has shifted.

`HJO/Shuffle/SweepTruncate.lean` computes one of the two shifts. This file computes the other,
and the point of it is that **the two windows are not the same window**.

## The two windows, and why they differ

Write `d = ay - bx` for the excess of the point the sweep is at.

* At a **base** point (`x < aN`) the tail's live north steps are those of excess in the half-open
  window `[d - a, d)` — `HJO.Paths.mem_liveSteps_iff_of_lt_fst`, whose hypothesis is
  `P.1 < u.1`, packaged as `HJO.Paths.tailLiveSteps` and counted by
  `HJO.Paths.card_liveSteps_high_appendHeights`.
* At a **tail** point (`x ≥ aN`) the base's live north steps are those of excess in
  `(d - a, d]` — `HJO.Paths.baseLiveSteps` below, the window closed at the *other* end.

The asymmetry is forced and is not a convention. Both conditions of `HJO.Paths.liveSteps` are
lexicographic comparisons whose tie-breaks are decided by the comparison of abscissae, and the
corner translation puts every base north step strictly left of every tail point and every tail north
step strictly right of every base point. So at a base point both tie-breaks fall one way and at a
tail point both fall the other, which slides the window by one end. That is
`HJO.Paths.mem_liveSteps_iff_of_fst_lt` against `HJO.Paths.mem_liveSteps_iff_of_lt_fst`.

## What this buys, and what it does not

It says the interleaving is a **two-way coupling through one integer per side per excess level, both
in closed form** — not an intractable entanglement. In particular the base's correction to a tail
point's width is a function of the base and the excess **alone**
(`HJO.Paths.card_liveSteps_low_appendHeights`, and its independence of the tail is immediate from
the definition, since `HJO.Paths.baseLiveSteps` does not mention the tail). That is the exact mirror
of `HJO.Paths.card_liveSteps_high_appendHeights_congr` and it is what any factorisation of the band
word into layers needs of the tail layers.

It does **not** prove the band identity. Knowing both shifts in closed form leaves the identity
itself — that the alternating product, summed over the fibre, is `HJO.Mellit.stageTotal` — entirely
untouched, and a shifted width is a *different operator* related to the old one by no scalar
(`HJO.Sweep.dplus_ne_conj_of_mapsTo_piece` and its siblings). What is removed is the suspicion that
the tail layers could not be described at all.

## References

This file concerns `HJO.Paths.liveSteps`, `HJO.Paths.sweepWidth`, `HJO.Paths.sweepRight`,
`HJO.ParkingFunctions.abovePointRank`, `HJO.Paths.abovePointRank_lt_iff`. Transcribing
A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 4.
-/

@[expose] public section

namespace HJO.Paths

open Finset ParkingFunctions

variable {a b N A : ℕ}

/-! ### Membership in the live set at a north step strictly to the left -/

/-- **Membership in `HJO.Paths.liveSteps` at a north step strictly to the *left* of the point, in
closed form.** The mirror of `HJO.Paths.mem_liveSteps_iff_of_lt_fst`, and the window comes out
closed at the other end: with `u.1 < P.1` the tie-break `u.1 ≤ P.1` of
`HJO.Mellit.abovePointRank_le_iff` is satisfied rather than violated, so each of the two comparisons
admits its boundary case instead of excluding it, and `[rk P - a, rk P)` becomes `(rk P - a, rk P]`.

This is the only place the asymmetry of the band interleaving comes from. -/
theorem mem_liveSteps_iff_of_fst_lt {M : ℕ} (hM : 0 < M) {y : Heights a b M} {u P : ℕ × ℕ}
    (hu : u ∈ northSteps y) (hP : P.1 ≤ a * M) (hlt : u.1 < P.1) :
    u ∈ liveSteps y P ↔
      (diagExcess a b P - a < diagExcess a b u ∧ diagExcess a b u ≤ diagExcess a b P) := by
  have hu1 : u.1 < a * M := (mem_northSteps_iff.1 hu).1
  have hle : u.1 ≤ P.1 := hlt.le
  have h1 : (abovePointRank a b M u.1 u.2 ≤ abovePointRank a b M P.1 P.2)
      ↔ diagExcess a b u ≤ diagExcess a b P := by
    rw [HJO.Mellit.abovePointRank_le_iff hM hu1.le hP]
    simp only [diagExcess, hle, and_true]
    omega
  have h2 : (abovePointRank a b M P.1 P.2 < abovePointRank a b M u.1 u.2 + attackWindow a M)
      ↔ diagExcess a b P - a < diagExcess a b u := by
    rw [← abovePointRank_succ a b M u.1 u.2, lt_iff_not_ge,
      HJO.Mellit.abovePointRank_le_iff hM hu1.le hP]
    simp only [diagExcess, hle, and_true, not_or, not_lt]
    push_cast
    constructor
    · rintro ⟨hlt', hne⟩
      rcases lt_or_eq_of_le hlt' with h | h
      · linarith
      · exact absurd h.symm hne
    · intro h
      exact ⟨by linarith, fun hcon => by linarith⟩
  simp only [liveSteps, Finset.mem_filter, h1, h2, hu, true_and]
  exact and_comm

/-! ### The base's north steps that a tail point's level line crosses -/

/-- **The north steps of a base path that the level line of diagonal excess `d` crosses**, read at a
point of the tail. The mirror of `HJO.Paths.tailLiveSteps`, with the window `(d - a, d]` closed at
the top instead of at the bottom — see `HJO.Paths.mem_liveSteps_iff_of_fst_lt` for why. -/
def baseLiveSteps (z : Heights a b N) (d : ℤ) : Finset (ℕ × ℕ) :=
  {p ∈ northSteps z | d - a < diagExcess a b p ∧ diagExcess a b p ≤ d}

/-- **Above the corner column, the base's live north steps at a point of the extension are the
base's own, in closed form.** The mirror of `HJO.Paths.liveSteps_high_appendHeights`: there the tail
contributes to a base point, here the base contributes to a tail point. No translation is needed on
this side — the base's north steps sit in the extension at their own coordinates. -/
theorem liveSteps_low_appendHeights {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) {P : ℕ × ℕ} (hP : a * N ≤ P.1)
    (hPM : P.1 ≤ a * (N + A)) (hN : 0 < N) :
    {u ∈ liveSteps (appendHeights z w) P | u.1 < a * N} = baseLiveSteps z (diagExcess a b P) := by
  have hMpos : 0 < N + A := by omega
  ext u
  simp only [baseLiveSteps, Finset.mem_filter]
  constructor
  · rintro ⟨hlive, hlt⟩
    have hun : u ∈ northSteps (appendHeights z w) := liveSteps_subset _ _ hlive
    have huz : u ∈ northSteps z := by
      have hsplit := hun
      rw [northSteps_appendHeights hz hw, Finset.mem_union, Finset.mem_image] at hsplit
      rcases hsplit with h | h
      · exact h
      · obtain ⟨p, -, hp⟩ := h
        have : u.1 = a * N + p.1 := by rw [← hp]
        omega
    exact ⟨huz, (mem_liveSteps_iff_of_fst_lt hMpos hun hPM (by omega)).1 hlive⟩
  · rintro ⟨huz, hwin⟩
    have hu1 : u.1 < a * N := (mem_northSteps_iff.1 huz).1
    have hun : u ∈ northSteps (appendHeights z w) := by
      rw [northSteps_appendHeights hz hw]
      exact Finset.mem_union_left _ huz
    exact ⟨(mem_liveSteps_iff_of_fst_lt hMpos hun hPM (by omega)).2 hwin, hu1⟩

/-- **The base's correction to a tail point's width, as a number.** -/
theorem card_liveSteps_low_appendHeights {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) {P : ℕ × ℕ} (hP : a * N ≤ P.1)
    (hPM : P.1 ≤ a * (N + A)) (hN : 0 < N) :
    #{u ∈ liveSteps (appendHeights z w) P | u.1 < a * N}
      = #(baseLiveSteps z (diagExcess a b P)) := by
  rw [liveSteps_low_appendHeights hz hw hP hPM hN]

/-- **The width at a tail point splits into a pure-tail part and a base correction in closed
form.** The mirror of `HJO.Paths.sweepWidth_appendHeights`. -/
theorem sweepWidth_appendHeights_of_le {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) {P : ℕ × ℕ} (hP : a * N ≤ P.1)
    (hPM : P.1 ≤ a * (N + A)) (hN : 0 < N) :
    sweepWidth (appendHeights z w) P
      = #{u ∈ liveSteps (appendHeights z w) P | a * N ≤ u.1}
        + #(baseLiveSteps z (diagExcess a b P)) := by
  have h := Finset.card_filter_add_card_filter_not (s := liveSteps (appendHeights z w) P)
    (fun u => u.1 < a * N)
  rw [card_liveSteps_low_appendHeights hz hw hP hPM hN] at h
  simp only [not_lt] at h
  have h' : sweepWidth (appendHeights z w) P
      = #(baseLiveSteps z (diagExcess a b P))
        + #{u ∈ liveSteps (appendHeights z w) P | a * N ≤ u.1} := h.symm
  omega

/-- **The base's correction to a tail point's width does not depend on the tail.** Immediate from
the definition — `HJO.Paths.baseLiveSteps` does not mention the tail at all — and stated because it
is what a factorisation of the band word into per-level layers needs of the tail layers. The mirror
of `HJO.Paths.card_liveSteps_high_appendHeights_congr`.

Note the contrast with `HJO.Paths.card_liveSteps_high_appendHeights_ne`: the *tail's* correction to
a base point genuinely varies across the fibre, so the two directions of the coupling are not
alike. -/
theorem card_liveSteps_low_appendHeights_congr {z : Heights a b N} {w w' : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hw' : IsAboveDiagonal w') {P : ℕ × ℕ}
    (hP : a * N ≤ P.1) (hPM : P.1 ≤ a * (N + A)) (hN : 0 < N) :
    #{u ∈ liveSteps (appendHeights z w) P | u.1 < a * N}
      = #{u ∈ liveSteps (appendHeights z w') P | u.1 < a * N} := by
  rw [card_liveSteps_low_appendHeights hz hw hP hPM hN,
    card_liveSteps_low_appendHeights hz hw' hP hPM hN]

/-! ### The two windows are genuinely different -/

/-- **The base window `(d - a, d]` is not the tail window `[d - a, d)`.** At `(a, b) = (1, 2)` with
base `HJO.Paths.baseEx` (`N = 1`) the base's north steps have excesses `0` and `1`, so at a tail
point of excess `2` the window `(1, 2]` catches nothing while `[1, 2)` would catch one step. So the
end at which each window is closed is load-bearing: reading the tail window at a tail point
would over-count the width by one here, and a width is an operator index. -/
theorem card_baseLiveSteps_ne_tail_window :
    #(baseLiveSteps baseEx 2) ≠ #{p ∈ northSteps baseEx | (2 : ℤ) - 1 ≤ diagExcess 1 2 p ∧
      diagExcess 1 2 p < 2} := by
  decide

end HJO.Paths

end
