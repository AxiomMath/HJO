/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendBandRounds
public import HJO.Shuffle.SweepPositions
public import HJO.Shuffle.SweepWidth
public meta import HJO.Attr

/-!
# The tail layer of a round, computed: the tail's own word at a raised index

`HJO.Mellit.roundSweepWord_split_fst` cuts a round of the band word at the corner abscissa `c = aN`
into a **base layer** (abscissa `< aN`) and a **tail layer** (abscissa `≥ aN`), the tail layer
standing rightmost and so applied first. `HJO/Shuffle/SweepLayerWidth.lean` computes the base
layer. This file computes the tail layer, and the answer is the exact mirror — with one asymmetry
that is not a convention.

## The tail layer is the tail's own round word, read at one raised index

Every statement below is about the corner translate `p ↦ (aN + p.1, bN + p.2)`, which moves a point
along the diagonal and so preserves `HJO.Paths.diagExcess` (`HJO.Paths.diagExcess_corner_add`).

* **The index set translates.** `HJO.Paths.sweptRegion_filter_le_appendHeights`: the swept points of
  the extension at or right of the corner column are exactly the corner translates of the tail's own
  swept points. With `HJO.Mellit.sweptAbove_eq_filter` this gives
  `HJO.Mellit.tailRoundList_appendHeights`: at a separating level and a *positive* excess the tail
  layer of round `e` is the translate of the tail's own round-`e` index set.
* **The order translates.** `HJO.Mellit.sortByRank_image_corner`: the rank order is lexicographic in
  `(excess, abscissa)` and the translate preserves both, so the extension lists the tail layer in
  the order the tail lists its own round.
* **The live steps translate, and the base's are all to the left.**
  `HJO.Paths.liveSteps_tail_appendHeights` is the mirror of
  `HJO.Paths.liveSteps_high_appendHeights`; together with
  `HJO.Paths.liveSteps_low_appendHeights` it splits the width at a tail point into the tail's own
  width and the base correction `#(baseLiveSteps z e)`, which depends on the base and the excess
  alone.
* **Hence the operator.** `HJO.Paths.sweepWidth_appendHeights_corner`:
  `k^{ext}(P) = k^w(p) + β_e` with `β_e = #(HJO.Paths.baseLiveSteps z e)`, constant on the round
  (`HJO.Mellit.sweepWidth_appendHeights_corner_of_diagExcess_eq`). And
  `HJO.Paths.sweepRight_appendHeights_corner`: `a^{ext}(P) = a^w(p)`, **unshifted** — the base's
  live steps at a tail point are all strictly to its left, so `HJO.Paths.sweepRight` misses every
  one of them.

## The asymmetry, and it is load-bearing

At a **base** point of round `e` both counts move, by the same `δ_e = #(tailLiveSteps w e)`
(`HJO.Mellit.sweepWidth_appendHeights_of_diagExcess_eq`,
`HJO.Mellit.sweepRight_appendHeights_of_diagExcess_eq`), so rule `D` there contributes a factor
`q^{δ_e}` and rule `C` a factor `q^{-δ_e}` that the base's own word does not carry. At a **tail**
point only the width moves. Hence `HJO.Mellit.sweepOperator_appendHeights_corner_of_eventType_D` and
`…_of_eventType_E`: at the two event types that read no width the extension's operator at a tail
point is **literally the tail's own**, with no scalar at all, and
`…_of_eventType_C` carries the tail's own exponent. So the whole discrepancy of the tail layer is
one integer of index shift, and **no power of `q`** — where the base layer's discrepancy was a
staircase *and* a power of `q` (`HJO.Mellit.exists_layerWord_shiftAux_of_sorted`).

## Where `a` enters: the window is `a` rounds wide

`HJO.Paths.tailLiveSteps w d` is the half-open window `[d - a, d)` in the tail's own excess, so
`HJO.Paths.mem_tailLiveSteps_iff_Ioc` says a tail north step of excess `f` is live exactly in the
rounds `d ∈ (f, f + a]` — **`a` consecutive rounds**. At `a = 1` each north step of the tail belongs
to exactly one round (`HJO.Paths.tailLiveSteps_one_left`) and consecutive `δ_e` share nothing; at
`a ≥ 2` the windows of consecutive rounds overlap in `a - 1` levels.

The inter-round recursion is `HJO.Paths.card_tailLiveSteps_succ`:

`δ_{d+1} + #{tail steps of excess d - a} = δ_d + #{tail steps of excess d}`,

which needs `0 < a` and nothing else. It is the precise statement of what the tail layer of a round
has to reconcile, and `HJO.Paths.card_tailLiveSteps_ne_succ` shows there is something to reconcile:
on the `2 × 4` rectangle the shifts of the four rounds are `1, 2, 1, 0`, so `δ` is **not** constant
across the rounds of a single tail. (The earlier
`HJO.Paths.card_liveSteps_high_appendHeights_ne` varies `δ` across the *fibre* at a fixed point,
which is a different statement and does not imply this one.)

## The inter-round reconciliation: its grading is automatic

`HJO.Paths.card_tailLiveSteps_succ_add_card_roundEvents_A` is the one statement here that is about
the reconciliation rather than about one layer:

`δ_{d+1} + #A_d = δ_d + #B_d`.

Rule `A` is `d_+` and raises the graded index by one, rule `B` is `d_-` and lowers it, and rules
`C`, `D`, `E` preserve it (`HJO.Mellit.nextWidth`). So the tail layer of round `d` changes the index
by **exactly** `δ_d - δ_{d+1}`: the shift the next round's base layer asks for is the shift this
tail layer produces. The grading obstruction to the termwise route
(`HJO/Shuffle/SweepAppendWidth.lean`: the stage raises the index by one however large `A` is,
while `δ` ranges over a whole band) therefore does **not** reappear at the round boundary.

It is proved by cancelling the type-`C` events between two identifications, both of which are about
the tail alone: the north steps of excess `d` are the type-`B`-or-`C` events of round `d`
(`HJO.Paths.filter_northSteps_eq_roundEvents`), and the north steps of excess `d - a` are the
type-`A`-or-`C` events of round `d`, by the head bijection `(x, y) ↦ (x, y + 1)`
(`HJO.Paths.filter_head_eq_image_northSteps`) — passing from a north step to its head raises the
excess by exactly the window width `a`. Nothing of the base, of `q`, of `u` or of coprimality
enters.

This is a **necessary** condition on the reconciliation, and it is proved here. It is not the
reconciliation.

## What this does not do

It does not transport the tail layer past `HJO.Sweep.shiftAux`. The base layer's transport
(`HJO.Mellit.exists_layerWord_shiftAux_of_sorted`) consumes a vector in the form `g·Σ_δF` with
`g ∈ V_δ` an `L`-polynomial in `y_1, …, y_δ`; that form is a **rank-one** condition on the vector,
and the tail layer's index shift is `β_e`, not `δ_e`, so the same machinery does not apply to it
verbatim. The two integers are genuinely different: on the worked instance
`HJO.Mellit.band_one_left_one_one` they agree at every round below the top and differ at the top,
and that instance is degenerate in three further ways — the base equals the tail, every intermediate
vector is a monomial, and `δ_e` is constant — so it is no guide to the general reconciliation.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Paths

open Finset ParkingFunctions

variable {a b N A : ℕ}

/-! ### Liveness as a trichotomy in the abscissa -/

/-- **`HJO.Paths.liveSteps` as a trichotomy**, collecting the three earlier cases into the one
statement a translation argument consumes: the level line through `P` crosses a north step `u`
according to a window in the diagonal excess whose closed end is decided by the comparison of
abscissae, and in the column of `P` itself only `P` is live.

Nothing about the rectangle survives beyond `0 < M` and the bound on `P`, which is what makes the
corner translate of `HJO.Paths.appendHeights` transparent to it. -/
theorem mem_liveSteps_iff_trichotomy {M : ℕ} (hM : 0 < M) {y : Heights a b M} {u P : ℕ × ℕ}
    (hu : u ∈ northSteps y) (hP : P.1 ≤ a * M) :
    u ∈ liveSteps y P ↔
      (if u.1 < P.1 then
          diagExcess a b P - a < diagExcess a b u ∧ diagExcess a b u ≤ diagExcess a b P
        else if P.1 < u.1 then
          diagExcess a b P - a ≤ diagExcess a b u ∧ diagExcess a b u < diagExcess a b P
        else u = P) := by
  split_ifs with h1 h2
  · exact mem_liveSteps_iff_of_fst_lt hM hu hP h1
  · exact mem_liveSteps_iff_of_lt_fst hM hu hP h2
  · exact mem_liveSteps_iff_eq_of_fst_eq hu (by omega)

/-! ### The height function at and above the corner column -/

/-- **At and above the corner column the extension's height function is the tail's, raised by
`bN`** — for *every* abscissa, the ones past the right endpoint included.
`HJO.Paths.ht_appendHeights_of_ge` stops at `a(N+A)`, where both sides are held at their maxima and
the identity continues to hold; the unrestricted form is what the event type at the corner column
needs, the guard of `HJO.Paths.eventType` reading `ht` one step to the right. -/
theorem ht_appendHeights_corner {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) {r : ℕ} (hr : a * N ≤ r) :
    ht (appendHeights z w) r = b * N + ht w (r - a * N) := by
  rcases le_or_gt r (a * (N + A)) with h | h
  · exact ht_appendHeights_of_ge hz.2.1 hw.1 hr h
  · have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
    rw [ht_of_gt _ h, ht_of_gt w (by omega), Nat.mul_add]

/-! ### The swept region at and above the corner column -/

/-- **The swept points of an extension at or right of the corner column are the corner translates of
the tail's own swept points.** The mirror of `HJO.Paths.sweptRegion_filter_lt_appendHeights`, and
the translation is forced: a swept point with `aN ≤ x` has `b·aN ≤ bx ≤ ay`, so `bN ≤ y`, and both
remaining clauses of `HJO.Paths.mem_sweptRegion` are invariant under subtracting the corner.

`0 < a` is read exactly once, to get `bN ≤ y` from `a·bN ≤ a·y`. -/
theorem sweptRegion_filter_le_appendHeights (ha : 0 < a) {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) :
    {P ∈ sweptRegion (appendHeights z w) | a * N ≤ P.1}
      = (sweptRegion w).image (fun p => (a * N + p.1, b * N + p.2)) := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have hkey : ∀ r : ℕ × ℕ, (((a * N + r.1, b * N + r.2) : ℕ × ℕ)
      ∈ sweptRegion (appendHeights z w)) ↔ r ∈ sweptRegion w := by
    intro r
    have e1 : b * (a * N + r.1) = b * (a * N) + b * r.1 := by ring
    have e2 : a * (b * N + r.2) = a * (b * N) + a * r.2 := by ring
    have e3 : b * (a * N) = a * (b * N) := by ring
    have e4 : ht (appendHeights z w) (a * N + r.1 + 1) = b * N + ht w (r.1 + 1) := by
      rw [ht_appendHeights_corner hz hw (by omega),
        show a * N + r.1 + 1 - a * N = r.1 + 1 from by omega]
    simp only [mem_sweptRegion, e4]
    omega
  ext P
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hP, hge⟩
    have h2 : b * P.1 ≤ a * P.2 := (mem_sweptRegion.1 hP).2.1
    have hbN : b * N ≤ P.2 := by
      have hmul : a * (b * N) ≤ a * P.2 := by
        have h5 : b * (a * N) ≤ b * P.1 := Nat.mul_le_mul_left b hge
        have e3 : b * (a * N) = a * (b * N) := by ring
        omega
      exact Nat.le_of_mul_le_mul_left hmul ha
    refine ⟨(P.1 - a * N, P.2 - b * N), ?_, ?_⟩
    · rw [← hkey]
      rwa [show a * N + ((P.1 - a * N, P.2 - b * N) : ℕ × ℕ).1 = P.1 from by simp; omega,
        show b * N + ((P.1 - a * N, P.2 - b * N) : ℕ × ℕ).2 = P.2 from by simp; omega]
    · simp only [Prod.ext_iff]
      omega
  · rintro ⟨r, hr, rfl⟩
    exact ⟨(hkey r).2 hr, by change a * N ≤ a * N + r.1; omega⟩

/-! ### The live steps at a tail point -/

/-- **The tail's live north steps at a point of the tail are the tail's own, translated.** The
mirror of `HJO.Paths.liveSteps_high_appendHeights`, which reads the tail's contribution at a
*base* point; here both the point and the steps are the tail's, and the corner translate preserves
every datum `HJO.Paths.mem_liveSteps_iff_trichotomy` reads — the diagonal excess by
`HJO.Paths.diagExcess_corner_add` and the comparison of abscissae because the translation is a shift
by one and the same `aN`. -/
theorem liveSteps_tail_appendHeights {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) (hA : 0 < A) {p : ℕ × ℕ}
    (hp1 : p.1 ≤ a * A) :
    {v ∈ liveSteps (appendHeights z w) (a * N + p.1, b * N + p.2) | a * N ≤ v.1}
      = (liveSteps w p).image (fun r => (a * N + r.1, b * N + r.2)) := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have hMpos : 0 < N + A := by omega
  have hPM : ((a * N + p.1, b * N + p.2) : ℕ × ℕ).1 ≤ a * (N + A) := by
    change a * N + p.1 ≤ a * (N + A); omega
  have hnorth : ∀ r : ℕ × ℕ, r ∈ northSteps w →
      ((a * N + r.1, b * N + r.2) : ℕ × ℕ) ∈ northSteps (appendHeights z w) := by
    intro r hr
    rw [northSteps_appendHeights hz hw]
    exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨r, hr, rfl⟩)
  have hkey : ∀ r : ℕ × ℕ, r ∈ northSteps w →
      (((a * N + r.1, b * N + r.2) : ℕ × ℕ)
          ∈ liveSteps (appendHeights z w) (a * N + p.1, b * N + p.2) ↔ r ∈ liveSteps w p) := by
    intro r hr
    rw [mem_liveSteps_iff_trichotomy hMpos (hnorth r hr) hPM,
      mem_liveSteps_iff_trichotomy hA hr hp1]
    simp only [diagExcess_corner_add, Nat.add_lt_add_iff_left, Prod.ext_iff, add_right_inj]
  ext v
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hlive, hhigh⟩
    have hvn : v ∈ northSteps (appendHeights z w) := liveSteps_subset _ _ hlive
    obtain ⟨r, hr, hrv⟩ : ∃ r ∈ northSteps w, (a * N + r.1, b * N + r.2) = v := by
      rw [northSteps_appendHeights hz hw, Finset.mem_union, Finset.mem_image] at hvn
      rcases hvn with h | h
      · exact absurd (mem_northSteps_iff.1 h).1 (by omega)
      · obtain ⟨s, hs, hsv⟩ := h
        exact ⟨s, hs, hsv⟩
    subst hrv
    exact ⟨r, (hkey r hr).1 hlive, rfl⟩
  · rintro ⟨r, hlive, rfl⟩
    exact ⟨(hkey r (liveSteps_subset _ _ hlive)).2 hlive, by change a * N ≤ a * N + r.1; omega⟩

/-- The corner translate is injective, so it does not change a cardinality. -/
theorem corner_add_injective (a b N : ℕ) :
    Function.Injective (fun p : ℕ × ℕ => ((a * N + p.1, b * N + p.2) : ℕ × ℕ)) := by
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (by omega) (by omega)

/-- **The tail's own width at a point of the tail, as a number.** -/
theorem card_liveSteps_tail_appendHeights {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) (hA : 0 < A) {p : ℕ × ℕ}
    (hp1 : p.1 ≤ a * A) :
    #{v ∈ liveSteps (appendHeights z w) (a * N + p.1, b * N + p.2) | a * N ≤ v.1}
      = sweepWidth w p := by
  rw [liveSteps_tail_appendHeights hz hw hN hA hp1,
    Finset.card_image_of_injective _ (corner_add_injective a b N), sweepWidth]

/-- **`HJO.Paths.sweepWidth` at a tail point of an extension, in closed form**: the tail's own width
plus the base's correction, and the correction reads the base and the diagonal excess alone
(`HJO.Paths.baseLiveSteps`). The mirror of `HJO.Paths.sweepWidth_appendHeights_eq`. -/
theorem sweepWidth_appendHeights_corner {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) (hA : 0 < A) {p : ℕ × ℕ}
    (hp1 : p.1 ≤ a * A) :
    sweepWidth (appendHeights z w) (a * N + p.1, b * N + p.2)
      = sweepWidth w p + #(baseLiveSteps z (diagExcess a b p)) := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  rw [sweepWidth_appendHeights_of_le hz hw (P := (a * N + p.1, b * N + p.2)) (by simp)
      (by simp; omega) hN,
    card_liveSteps_tail_appendHeights hz hw hN hA hp1, diagExcess_corner_add]

/-- **`HJO.Paths.sweepRight` at a tail point of an extension is the tail's own, UNSHIFTED.** Every
live north step of the base at a tail point lies strictly to its left — the base's columns are all
below `aN` — so `HJO.Paths.sweepRight`, which counts only what is strictly to the right, misses the
whole base correction.

This is the asymmetry with the base layer, where `HJO.Paths.sweepRight_appendHeights_eq` shifts the
count by the same `δ` as the width, putting a factor `q^{±δ}` on rules `C` and `D`. At a tail point
those two rules are the tail's own operator exactly. -/
theorem sweepRight_appendHeights_corner {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) (hA : 0 < A) {p : ℕ × ℕ}
    (hp1 : p.1 ≤ a * A) :
    sweepRight (appendHeights z w) (a * N + p.1, b * N + p.2) = sweepRight w p := by
  have hset : {v ∈ liveSteps (appendHeights z w) (a * N + p.1, b * N + p.2) | a * N + p.1 < v.1}
      = {r ∈ liveSteps w p | p.1 < r.1}.image (fun r => (a * N + r.1, b * N + r.2)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hlive, hlt⟩
      have hmem : v ∈ {v ∈ liveSteps (appendHeights z w) (a * N + p.1, b * N + p.2) |
          a * N ≤ v.1} := Finset.mem_filter.2 ⟨hlive, by omega⟩
      rw [liveSteps_tail_appendHeights hz hw hN hA hp1, Finset.mem_image] at hmem
      obtain ⟨r, hr, rfl⟩ := hmem
      exact ⟨r, ⟨hr, by simp only at hlt; omega⟩, rfl⟩
    · rintro ⟨r, ⟨hr, hlt⟩, rfl⟩
      have hmem : ((a * N + r.1, b * N + r.2) : ℕ × ℕ)
          ∈ {v ∈ liveSteps (appendHeights z w) (a * N + p.1, b * N + p.2) | a * N ≤ v.1} := by
        rw [liveSteps_tail_appendHeights hz hw hN hA hp1]
        exact Finset.mem_image.2 ⟨r, hr, rfl⟩
      exact ⟨(Finset.mem_filter.1 hmem).1, by change a * N + p.1 < a * N + r.1; omega⟩
  change #{v ∈ liveSteps (appendHeights z w) (a * N + p.1, b * N + p.2) | a * N + p.1 < v.1}
      = #{r ∈ liveSteps w p | p.1 < r.1}
  rw [hset, Finset.card_image_of_injective _ (corner_add_injective a b N)]

/-! ### The event type at a tail point -/

/-- **The event type at a tail point of an extension is the tail's own.** All four data
`HJO.Paths.eventType` reads translate: the two heights by
`HJO.Paths.ht_appendHeights_corner`, the ordinate by the corner shift, and the guard
`x + 1 ≤ a(N + A)` becomes the tail's own `x + 1 ≤ aA`.

Note that no above-diagonality of the *base* beyond `ht z (aN) = bN` is used, and none of the tail
beyond `ht w 0 = 0`: those are the two clauses that make the two halves of
`HJO.Paths.appendHeights` agree at the corner. -/
theorem eventType_appendHeights_corner {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (p : ℕ × ℕ) :
    eventType (appendHeights z w) (a * N + p.1, b * N + p.2) = eventType w p := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have h1 : ht (appendHeights z w) (a * N + p.1) = b * N + ht w p.1 := by
    rw [ht_appendHeights_corner hz hw (by omega), Nat.add_sub_cancel_left]
  have h2 : ht (appendHeights z w) (a * N + p.1 + 1) = b * N + ht w (p.1 + 1) := by
    rw [ht_appendHeights_corner hz hw (by omega),
      show a * N + p.1 + 1 - a * N = p.1 + 1 from by omega]
  simp only [eventType, h1, h2, Nat.add_lt_add_iff_left,
    show (a * N + p.1 + 1 ≤ a * (N + A)) = (p.1 + 1 ≤ a * A) from by
      simp only [eq_iff_iff]; omega]

/-! ### Where `a` enters: the window is `a` rounds wide -/

/-- **A tail north step is live in exactly `a` consecutive rounds.** `HJO.Paths.tailLiveSteps w d`
is the half-open window `[d - a, d)` in the tail's own diagonal excess, so a north step of excess
`f` belongs to it exactly for `d ∈ (f, f + a]`.

This is the *only* place the numerator `a` enters the round-grouping: every per-event and per-layer
statement of `HJO/Shuffle/SweepLayerWidth.lean` and of this file is parameter-free, and the
`a`-dependence is the width of this window. At `a = 1` the window is a single level and the rounds
partition the tail's north steps; at `a ≥ 2` consecutive rounds overlap in `a - 1` levels. -/
@[hjo "lem_sweep_round_window"]
theorem mem_tailLiveSteps_iff_Ioc {w : Heights a b A} {p : ℕ × ℕ} (hp : p ∈ northSteps w) (d : ℤ) :
    p ∈ tailLiveSteps w d ↔ d ∈ Finset.Ioc (diagExcess a b p) (diagExcess a b p + a) := by
  simp only [tailLiveSteps, Finset.mem_filter, Finset.mem_Ioc, hp, true_and]
  omega

/-- **At `a = 1` the rounds partition the tail's north steps**: the window `[d - 1, d)` is the
single level `d - 1`, so each north step of the tail is live in exactly one round. This is the
sense in which the rounds are independent at `a = 1` — the shifts of consecutive rounds are counts
of *disjoint* sets of north steps. -/
theorem tailLiveSteps_one_left {b A : ℕ} (w : Heights 1 b A) (d : ℤ) :
    tailLiveSteps w d = {p ∈ northSteps w | diagExcess 1 b p = d - 1} := by
  refine Finset.filter_congr fun p _ => ?_
  simp only [Nat.cast_one]
  omega

/-- **The inter-round recursion for the shift.** Passing from round `d` to round `d + 1` the window
`[d - a, d)` loses the level `d - a` and gains the level `d`:

`δ_{d+1} + #{tail steps of excess d - a} = δ_d + #{tail steps of excess d}`.

`0 < a` is what makes the two levels lie inside the two windows; at `a = 0` both windows are empty
and the identity is `0 = 0` only by accident of both sides vanishing. Nothing else is assumed — no
`q`, no `u`, no coprimality, no above-diagonality. -/
theorem card_tailLiveSteps_succ (ha : 0 < a) (w : Heights a b A) (d : ℤ) :
    #(tailLiveSteps w (d + 1)) + #{p ∈ northSteps w | diagExcess a b p = d - a}
      = #(tailLiveSteps w d) + #{p ∈ northSteps w | diagExcess a b p = d} := by
  have haz : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hlow : {p ∈ northSteps w | diagExcess a b p = d - a} ⊆ tailLiveSteps w d := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp only [tailLiveSteps, Finset.mem_filter, hp.1, true_and, hp.2]
    omega
  have hhigh : {p ∈ northSteps w | diagExcess a b p = d} ⊆ tailLiveSteps w (d + 1) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp only [tailLiveSteps, Finset.mem_filter, hp.1, true_and, hp.2]
    omega
  have hmid : tailLiveSteps w d \ {p ∈ northSteps w | diagExcess a b p = d - a}
      = tailLiveSteps w (d + 1) \ {p ∈ northSteps w | diagExcess a b p = d} := by
    ext p
    simp only [Finset.mem_sdiff, tailLiveSteps, Finset.mem_filter, not_and]
    constructor
    · rintro ⟨⟨hp, h1, h2⟩, hne⟩
      have hne' : diagExcess a b p ≠ d - a := hne hp
      exact ⟨⟨hp, by omega, by omega⟩, fun _ => by omega⟩
    · rintro ⟨⟨hp, h1, h2⟩, hne⟩
      have hne' : diagExcess a b p ≠ d := hne hp
      exact ⟨⟨hp, by omega, by omega⟩, fun _ => by omega⟩
  rw [← Finset.card_sdiff_add_card_eq_card hhigh, ← Finset.card_sdiff_add_card_eq_card hlow, hmid]
  omega

/-! ### The grading of the reconciliation is automatic -/

/-- The swept points of a fixed diagonal excess at which a given rule of `HJO.Mellit.sweepOperator`
fires: the events of one round, split by type. -/
def roundEvents {M : ℕ} (y : Heights a b M) (e : ℤ) (t : EventType) : Finset (ℕ × ℕ) :=
  {P ∈ sweptRegion y | diagExcess a b P = e ∧ eventType y P = t}

/-- Distinct rules fire at distinct points. -/
theorem roundEvents_disjoint {M : ℕ} (y : Heights a b M) (e : ℤ) {s t : EventType} (hst : s ≠ t) :
    Disjoint (roundEvents y e s) (roundEvents y e t) := by
  rw [Finset.disjoint_left]
  intro P hP hP'
  exact hst ((Finset.mem_filter.1 hP).2.2.symm.trans (Finset.mem_filter.1 hP').2.2)

/-- **The type-`A`-or-`C` events of round `e` are the heads of the north steps of excess `e - a`.**
A swept point is the head of a north step exactly at those two types
(`HJO.Paths.isSweepHead_iff_eventType`), and passing from a north step to its head raises the
diagonal excess by exactly `a` — the attack window's width, by
`HJO.Paths.abovePointRank_succ`. So the map `(x, y) ↦ (x, y + 1)` is the bijection. -/
theorem filter_head_eq_image_northSteps {M : ℕ} {y : Heights a b M} (hy : IsAboveDiagonal y)
    (e : ℤ) :
    {P ∈ sweptRegion y | diagExcess a b P = e ∧
        (eventType y P = EventType.A ∨ eventType y P = EventType.C)}
      = ({p ∈ northSteps y | diagExcess a b p = e - a}).image (fun p => (p.1, p.2 + 1)) := by
  ext P
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hP, hexc, htyp⟩
    obtain ⟨v, hv, rfl⟩ := (isSweepHead_iff_eventType hy hP).2 htyp
    refine ⟨v, ⟨hv, ?_⟩, rfl⟩
    simp only [diagExcess] at hexc ⊢
    push_cast at hexc ⊢
    linarith
  · rintro ⟨v, ⟨hv, hexc⟩, rfl⟩
    have hsw := (mem_sweptRegion_of_mem_northSteps hy hv).2
    refine ⟨hsw, ?_, (isSweepHead_iff_eventType hy hsw).1 ⟨v, hv, rfl⟩⟩
    simp only [diagExcess] at hexc ⊢
    push_cast at hexc ⊢
    linarith

/-- **The north steps of excess `e` are the type-`B`-or-`C` events of round `e`**, which is
`HJO.Paths.mem_northSteps_iff_eventType` read along a level. -/
theorem filter_northSteps_eq_roundEvents {M : ℕ} {y : Heights a b M} (hy : IsAboveDiagonal y)
    (e : ℤ) :
    {p ∈ northSteps y | diagExcess a b p = e}
      = roundEvents y e EventType.B ∪ roundEvents y e EventType.C := by
  ext P
  simp only [roundEvents, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hexc⟩
    have hsw := (mem_sweptRegion_of_mem_northSteps hy hp).1
    rcases (mem_northSteps_iff_eventType hsw).1 hp with h | h
    · exact Or.inl ⟨hsw, hexc, h⟩
    · exact Or.inr ⟨hsw, hexc, h⟩
  · rintro (⟨hsw, hexc, h⟩ | ⟨hsw, hexc, h⟩)
    · exact ⟨(mem_northSteps_iff_eventType hsw).2 (Or.inl h), hexc⟩
    · exact ⟨(mem_northSteps_iff_eventType hsw).2 (Or.inr h), hexc⟩

/-- **THE GRADING OF THE INTER-ROUND RECONCILIATION IS AUTOMATIC.**

`δ_{d+1} + #A_d = δ_d + #B_d`, with `A_d` and `B_d` the type-`A` and type-`B` events of the tail's
own round `d`.

Read as `δ_d - δ_{d+1} = #A_d - #B_d`, this says the tail layer of round `d` changes the graded
index by **exactly** the amount needed to turn `Σ_{δ_{d+1}}` into `Σ_{δ_d}`: rule `A` is `d_+` and
raises the index by one, rule `B` is `d_-` and lowers it by one, and rules `C`, `D`, `E` preserve it
(`HJO.Mellit.nextWidth`, `HJO.Mellit.sweepOperator_mem_piece`). So the shift the *next* round asks
for is the shift the *current* tail layer produces, and the reconciliation
`Σ_{δ_{d+1}} → Σ_{δ_d}` is not obstructed by the grading — which is the objection that killed the
termwise route (`HJO/Shuffle/SweepAppendWidth.lean`) and that the round-grouping has to
survive.

Three facts combine: the window recursion `HJO.Paths.card_tailLiveSteps_succ`, the identification of
the north steps of a level with its type-`B`-or-`C` events
(`HJO.Paths.filter_northSteps_eq_roundEvents`), and the head bijection
`HJO.Paths.filter_head_eq_image_northSteps`, which trades the north steps of excess `d - a` for the
type-`A`-or-`C` events of round `d`. The type-`C` events cancel from the two sides, which is why
neither `#C_d` nor any count of the base survives.

What it does **not** say is that the reconciliation holds: the grades agreeing is a necessary
condition on the vectors, not the identity between them. -/
@[hjo "lem_sweep_round_grading"]
theorem card_tailLiveSteps_succ_add_card_roundEvents_A (ha : 0 < a) {y : Heights a b A}
    (hy : IsAboveDiagonal y) (d : ℤ) :
    #(tailLiveSteps y (d + 1)) + #(roundEvents y d EventType.A)
      = #(tailLiveSteps y d) + #(roundEvents y d EventType.B) := by
  have h1 := card_tailLiveSteps_succ ha y d
  have h2 : #{p ∈ northSteps y | diagExcess a b p = d}
      = #(roundEvents y d EventType.B) + #(roundEvents y d EventType.C) := by
    rw [filter_northSteps_eq_roundEvents hy,
      Finset.card_union_of_disjoint (roundEvents_disjoint y d (by decide))]
  have hac : {P ∈ sweptRegion y | diagExcess a b P = d ∧
        (eventType y P = EventType.A ∨ eventType y P = EventType.C)}
      = roundEvents y d EventType.A ∪ roundEvents y d EventType.C := by
    ext P
    simp only [roundEvents, Finset.mem_union, Finset.mem_filter]
    tauto
  have h3 : #{p ∈ northSteps y | diagExcess a b p = d - a}
      = #(roundEvents y d EventType.A) + #(roundEvents y d EventType.C) := by
    rw [← Finset.card_image_of_injective {p ∈ northSteps y | diagExcess a b p = d - a}
        (f := fun p : ℕ × ℕ => ((p.1, p.2 + 1) : ℕ × ℕ))
        (fun p r h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 (by omega)),
      ← filter_head_eq_image_northSteps hy, hac,
      Finset.card_union_of_disjoint (roundEvents_disjoint y d (by decide))]
  omega

/-! ### The shift is not constant across the rounds of one tail -/

/-- **The four rounds of the `2 × 4` tail `HJO.Paths.tailEx1` have shifts `1, 2, 1, 0`.** Its north
steps have diagonal excesses `0, 1, 2` in column `0` and `1` in column `1`, and at `a = 1` the
shift of round `d` counts the steps of excess `d - 1` (`HJO.Paths.tailLiveSteps_one_left`). -/
theorem card_tailLiveSteps_tailEx1 :
    #(tailLiveSteps tailEx1 1) = 1 ∧ #(tailLiveSteps tailEx1 2) = 2 ∧
      #(tailLiveSteps tailEx1 3) = 1 ∧ #(tailLiveSteps tailEx1 4) = 0 := by decide

/-- **The shift of consecutive rounds of one and the same tail differs.** This is what the tail
layer between two rounds has to reconcile, and it is a *different* statement from the earlier
`HJO.Paths.card_liveSteps_high_appendHeights_ne`, which varies the shift across the fibre of tails
at one fixed point of the base. Neither implies the other, and it is this one that says the
round-by-round induction cannot carry a single `Σ_δ`.

Note that it happens at `a = 1`, where each north step of the tail is live in exactly one round
(`HJO.Paths.tailLiveSteps_one_left`): the rounds being independent does **not** make the shift
constant, since a round with two north steps of the same excess shifts by two. -/
@[hjo "not_sweep_round_shift_constant"]
theorem card_tailLiveSteps_ne_succ :
    #(tailLiveSteps tailEx1 1) ≠ #(tailLiveSteps tailEx1 (1 + 1)) := by decide

/-- **…and the grading identity holds there, non-trivially.** At round `1` of
`HJO.Paths.tailEx1` the tail layer is one type-`C` event and one type-`B` event, so it *lowers* the
graded index by one — which is exactly `δ_1 - δ_2 = 1 - 2`. So
`HJO.Paths.card_tailLiveSteps_succ_add_card_roundEvents_A` is not vacuous: both sides of it move. -/
theorem card_roundEvents_tailEx1 :
    #(roundEvents tailEx1 1 EventType.A) = 0 ∧ #(roundEvents tailEx1 1 EventType.B) = 1 := by
  decide

end HJO.Paths

namespace HJO.Mellit

open HJO.Sweep HJO.Paths Finset ParkingFunctions

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b N A : ℕ}

/-! ### The event operator at a raised width -/

/-- **`HJO.Mellit.sweepOperator` read at a width raised by `β`, with the path's own `q`-exponent.**
This is the operator the tail layer of a round of an extension is made of: by
`HJO.Paths.sweepWidth_appendHeights_corner` the width at a tail point moves by
`β = #(HJO.Paths.baseLiveSteps z e)`, and by `HJO.Paths.sweepRight_appendHeights_corner` the
exponent of rules `C` and `D` does **not** move at all.

Contrast `HJO.Mellit.sweepOperator` at a base point of the extension, where both move together and
rules `C` and `D` therefore acquire the extra factors `q^{∓δ_e}`. -/
noncomputable def sweepOperatorShifted (q u : L) {a b M : ℕ} (y : Heights a b M) (P : ℕ × ℕ)
    (β : ℕ) : Module.End L (Total L) :=
  match eventType y P with
  | EventType.A => dplus q (sweepWidth y P + β)
  | EventType.B => dminus q (sweepWidth y P + β)
  | EventType.C => q ^ (-(sweepRight y P : ℤ)) • corner q (sweepWidth y P + β)
  | EventType.D => q ^ sweepRight y P • (1 : Module.End L (Total L))
  | EventType.E => u • (1 : Module.End L (Total L))

/-- At shift `0` the raised operator is the path's own event operator. -/
theorem sweepOperatorShifted_zero (q u : L) {a b M : ℕ} (y : Heights a b M) (P : ℕ × ℕ) :
    sweepOperatorShifted q u y P 0 = sweepOperator q u y P := by
  rw [sweepOperatorShifted, sweepOperator]
  cases eventType y P <;> simp

/-! ### THE TAIL LAYER, COMPUTED: one event -/

/-- **THE EXTENSION'S EVENT OPERATOR AT A TAIL POINT IS THE TAIL'S OWN, AT A WIDTH RAISED BY THE
BASE'S LIVE COUNT — AND BY NOTHING ELSE.** For a point `p` of the tail's rectangle, the extension's
operator at the corner translate `(aN + p.1, bN + p.2)` is
`HJO.Mellit.sweepOperatorShifted q u w p β` with `β = #(HJO.Paths.baseLiveSteps z (excess p))`.

Three facts glue: `HJO.Paths.eventType_appendHeights_corner` (the rule is the tail's own),
`HJO.Paths.sweepWidth_appendHeights_corner` (the width is the tail's own plus `β`), and
`HJO.Paths.sweepRight_appendHeights_corner` (the exponent is the tail's own, unshifted, the base's
live steps lying strictly to the left of every tail point).

So **no power of `q` is introduced at a tail point**, and `q ≠ 0` is not read here at all — where
the base layer's transport had to add the `ℤ`-exponents of rules `C` and `D`
(`HJO.Mellit.exists_layerWord_shiftAux_of_sorted`). The entire discrepancy of the tail layer is one
integer of index shift. -/
theorem sweepOperator_appendHeights_corner {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) (hA : 0 < A) {p : ℕ × ℕ}
    (hp1 : p.1 ≤ a * A) :
    sweepOperator q u (appendHeights z w) (a * N + p.1, b * N + p.2)
      = sweepOperatorShifted q u w p (#(baseLiveSteps z (diagExcess a b p))) := by
  have htyp : eventType (appendHeights z w) (a * N + p.1, b * N + p.2) = eventType w p :=
    eventType_appendHeights_corner hz hw p
  have hwid : sweepWidth (appendHeights z w) (a * N + p.1, b * N + p.2)
      = sweepWidth w p + #(baseLiveSteps z (diagExcess a b p)) :=
    sweepWidth_appendHeights_corner hz hw hN hA hp1
  have hrig : sweepRight (appendHeights z w) (a * N + p.1, b * N + p.2) = sweepRight w p :=
    sweepRight_appendHeights_corner hz hw hN hA hp1
  rw [sweepOperatorShifted]
  cases hev : eventType w p with
  | A => rw [sweepOperator_of_eventType_A _ (htyp.trans hev), hwid]
  | B => rw [sweepOperator_of_eventType_B _ (htyp.trans hev), hwid]
  | C => rw [sweepOperator_of_eventType_C _ (htyp.trans hev), hwid, hrig]
  | D => rw [sweepOperator_of_eventType_D _ (htyp.trans hev), hrig]
  | E => rw [sweepOperator_of_eventType_E q u _ _ (htyp.trans hev)]

/-- **At rules `D` and `E` the extension's operator at a tail point is LITERALLY the tail's own.**
Those are the two rules that read no width, and the exponent of rule `D` is unshifted. -/
theorem sweepOperator_appendHeights_corner_of_eventType_D {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) (hA : 0 < A) {p : ℕ × ℕ}
    (hp1 : p.1 ≤ a * A) (hev : eventType w p = EventType.D) :
    sweepOperator q u (appendHeights z w) (a * N + p.1, b * N + p.2) = sweepOperator q u w p := by
  rw [sweepOperator_appendHeights_corner hz hw hN hA hp1, sweepOperatorShifted,
    sweepOperator_of_eventType_D _ hev, hev]

theorem sweepOperator_appendHeights_corner_of_eventType_E {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) (hA : 0 < A) {p : ℕ × ℕ}
    (hp1 : p.1 ≤ a * A) (hev : eventType w p = EventType.E) :
    sweepOperator q u (appendHeights z w) (a * N + p.1, b * N + p.2) = sweepOperator q u w p := by
  rw [sweepOperator_appendHeights_corner hz hw hN hA hp1, sweepOperatorShifted,
    sweepOperator_of_eventType_E q u _ _ hev, hev]

/-- **The shift is constant on a round.** `HJO.Paths.baseLiveSteps` reads the point only through its
diagonal excess, which is the constant `e` on a round, so the whole tail layer of round `e` is read
at widths raised by the single integer `β_e = #(baseLiveSteps z e)`. The mirror of
`HJO.Mellit.sweepWidth_appendHeights_of_diagExcess_eq`, and it needs nothing of the tail: unlike
`δ_e`, the integer `β_e` is a function of the base and the level alone
(`HJO.Paths.card_liveSteps_low_appendHeights_congr`). -/
theorem sweepOperator_appendHeights_corner_of_diagExcess_eq {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) (hA : 0 < A) {p : ℕ × ℕ}
    (hp1 : p.1 ≤ a * A) {e : ℤ} (he : diagExcess a b p = e) :
    sweepOperator q u (appendHeights z w) (a * N + p.1, b * N + p.2)
      = sweepOperatorShifted q u w p (#(baseLiveSteps z e)) := by
  rw [sweepOperator_appendHeights_corner hz hw hN hA hp1, he]

/-! ### THE TAIL LAYER, COMPUTED: the index set and its order -/

/-- **The corner translate preserves the rank order, so it preserves the rank listing.** The rank is
lexicographic in `(excess, abscissa)` (`HJO.Mellit.abovePointRank_le_iff`) and the corner translate
fixes the excess (`HJO.Paths.diagExcess_corner_add`) and shifts the abscissa by the constant `aN`,
so the extension lists the translate of a set in the order the tail lists the set itself.

This is the mirror of `HJO.Mellit.sortByRank_congr`, which handles a set already sitting in both
rectangles; here the set has to be moved. -/
theorem sortByRank_image_corner (ha : 0 < a) (hA : 0 < A) {w : Heights a b A}
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ sweptRegion w) :
    sortByRank a b (N + A) (S.image fun p => (a * N + p.1, b * N + p.2))
      = (sortByRank a b A S).map (fun p => (a * N + p.1, b * N + p.2)) := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have hMpos : 0 < N + A := by omega
  have hfinj : Function.Injective (fun p : ℕ × ℕ => ((a * N + p.1, b * N + p.2) : ℕ × ℕ)) :=
    corner_add_injective a b N
  have hbound : ∀ p ∈ S, p.1 ≤ a * A := fun p hp => (mem_sweptRegion.1 (hS hp)).1
  have hex : ∀ s : ℕ × ℕ, (a : ℤ) * ((b * N + s.2 : ℕ) : ℤ) - (b : ℤ) * ((a * N + s.1 : ℕ) : ℤ)
      = (a : ℤ) * s.2 - (b : ℤ) * s.1 := fun s => by push_cast; ring
  have hkey : ∀ p ∈ S, ∀ r ∈ S,
      (pointRank a b (N + A) ((a * N + p.1, b * N + p.2) : ℕ × ℕ)
          ≤ pointRank a b (N + A) ((a * N + r.1, b * N + r.2) : ℕ × ℕ)
        ↔ pointRank a b A p ≤ pointRank a b A r) := by
    intro p hp r hr
    have hbp := hbound p hp
    have hbr := hbound r hr
    rw [pointRank, pointRank, pointRank, pointRank,
      abovePointRank_le_iff hMpos
        (show ((a * N + p.1, b * N + p.2) : ℕ × ℕ).1 ≤ a * (N + A) from by omega)
        (show ((a * N + r.1, b * N + r.2) : ℕ × ℕ).1 ≤ a * (N + A) from by omega),
      abovePointRank_le_iff hA hbp hbr]
    simp only [hex, add_le_add_iff_left]
  refine (list_eq_of_perm_of_pairwise_key (K := pointRank a b (N + A)) ?_ ?_ ?_ ?_).symm
  · rw [← Multiset.coe_eq_coe, ← Multiset.map_coe,
      Multiset.coe_eq_coe.2 (sortByRank_perm a b A S), Finset.coe_toList,
      Multiset.coe_eq_coe.2 (sortByRank_perm a b (N + A)
        (S.image fun p => (a * N + p.1, b * N + p.2))),
      Finset.coe_toList, Finset.image_val_of_injOn hfinj.injOn]
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {p r} hp hr h => ?_) (sortByRank_pairwise a b A S)
    exact (hkey p (mem_sortByRank.1 hp) r (mem_sortByRank.1 hr)).2 h
  · exact sortByRank_pairwise a b (N + A) _
  · intro x hx y hy h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
    have hbp := hbound p (mem_sortByRank.1 hp)
    have hbr := hbound r (mem_sortByRank.1 hr)
    obtain ⟨e1, e2⟩ := abovePointRank_injOn (b := b) ha hMpos
      (show ((a * N + p.1, b * N + p.2) : ℕ × ℕ).1 ≤ a * (N + A) from by omega)
      (show ((a * N + r.1, b * N + r.2) : ℕ × ℕ).1 ≤ a * (N + A) from by omega) h
    exact Prod.ext e1 e2

/-- **The tail layer of a round is indexed by the corner translate of the tail's own round.** At a
separating level the index set is level-free (`HJO.Mellit.sweptAbove_eq_filter`), so on a round of
*positive* excess the level drops out on both sides and what is left is
`HJO.Paths.sweptRegion_filter_le_appendHeights`. The mirror of
`HJO.Mellit.baseRoundList_appendHeights`.

Positivity of `e` is not a convenience: at `e = 0` the tail's own round contains the points of the
tail on the diagonal, which the tail's own separating level does not select, while the extension's
level does not select them either — the two sides agree there only because both are empty of them,
and the argument below would have to be run separately. Every round of the band has `1 ≤ e`. -/
theorem tailRoundList_appendHeights (ha : 0 < a) {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) {η η'' : ℚ}
    (hη : SeparatesDiagonal a b (N + A) η) (hη'' : SeparatesDiagonal a b A η'') {e : ℤ}
    (he : 0 < e) :
    {P ∈ sweptAbove (appendHeights z w) η | diagExcess a b P = e ∧ a * N ≤ P.1}
      = ({p ∈ sweptAbove w η'' | diagExcess a b p = e}).image
          (fun p => (a * N + p.1, b * N + p.2)) := by
  have hreg := sweptRegion_filter_le_appendHeights (a := a) (b := b) (N := N) (A := A) ha hz hw
  rw [sweptAbove_eq_filter hη, sweptAbove_eq_filter hη'']
  ext P
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨hP, -⟩, hexc, hge⟩
    have hmem : P ∈ {P ∈ sweptRegion (appendHeights z w) | a * N ≤ P.1} :=
      Finset.mem_filter.2 ⟨hP, hge⟩
    rw [hreg, Finset.mem_image] at hmem
    obtain ⟨r, hr, rfl⟩ := hmem
    rw [diagExcess_corner_add] at hexc
    refine ⟨r, ⟨⟨hr, ?_⟩, hexc⟩, rfl⟩
    have hc1 : ((b * r.1 : ℕ) : ℤ) = (b : ℤ) * r.1 := by push_cast; ring
    have hc2 : ((a * r.2 : ℕ) : ℤ) = (a : ℤ) * r.2 := by push_cast; ring
    simp only [diagExcess] at hexc
    omega
  · rintro ⟨r, ⟨⟨hr, hlt⟩, hexc⟩, rfl⟩
    have hmem : ((a * N + r.1, b * N + r.2) : ℕ × ℕ)
        ∈ {P ∈ sweptRegion (appendHeights z w) | a * N ≤ P.1} := by
      rw [hreg]; exact Finset.mem_image.2 ⟨r, hr, rfl⟩
    refine ⟨⟨(Finset.mem_filter.1 hmem).1, ?_⟩, ?_, (Finset.mem_filter.1 hmem).2⟩
    · have e1 : b * (a * N + r.1) = b * (a * N) + b * r.1 := by ring
      have e2 : a * (b * N + r.2) = a * (b * N) + a * r.2 := by ring
      have e3 : b * (a * N) = a * (b * N) := by ring
      change b * (a * N + r.1) < a * (b * N + r.2)
      omega
    · rw [diagExcess_corner_add]; exact hexc

/-! ### THE TAIL LAYER, COMPUTED: the word -/

/-- **THE TAIL LAYER OF A ROUND OF AN EXTENSION IS THE TAIL'S OWN ROUND WORD, EVERY OPERATOR READ AT
A WIDTH RAISED BY THE ONE INTEGER `β_e`.** This is what
`HJO.Mellit.roundSweepWord_split_fst` cuts out at `c = aN`, computed: the same points as the tail's
own round `e` (`HJO.Mellit.tailRoundList_appendHeights`), in the same order
(`HJO.Mellit.sortByRank_image_corner`), with each operator the tail's own read at
`k^w(p) + β_e` and carrying the tail's own `q`-exponent
(`HJO.Mellit.sweepOperator_appendHeights_corner`).

The mirror of `HJO.Mellit.baseRoundWord_appendHeights`, and sharper than it in one respect: there
the residual was an index shift *and* a power of `q` on each of rules `C` and `D`; here it is an
index shift and nothing else. `q ≠ 0` is not read. -/
@[hjo "lem_sweep_tail_layer"]
theorem tailRoundWord_appendHeights (ha : 0 < a) (hN : 0 < N) (hA : 0 < A) {z : Heights a b N}
    {w : Heights a b A} (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) {η η'' : ℚ}
    (hη : SeparatesDiagonal a b (N + A) η) (hη'' : SeparatesDiagonal a b A η'') {e : ℤ}
    (he : 0 < e) :
    ((sortByRank a b (N + A) {P ∈ sweptAbove (appendHeights z w) η |
          diagExcess a b P = e ∧ a * N ≤ P.1}).map
        (sweepOperator q u (appendHeights z w))).prod
      = ((sortByRank a b A {p ∈ sweptAbove w η'' | diagExcess a b p = e}).map
          (fun p => sweepOperatorShifted q u w p (#(baseLiveSteps z e)))).prod := by
  have hsub : {p ∈ sweptAbove w η'' | diagExcess a b p = e} ⊆ sweptRegion w :=
    fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1
  rw [tailRoundList_appendHeights ha hz hw hη hη'' he,
    sortByRank_image_corner (N := N) ha hA hsub, List.map_map]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have hp' := mem_sortByRank.1 hp
  exact sweepOperator_appendHeights_corner_of_diagExcess_eq hz hw hN hA
    ((mem_sweptRegion.1 (hsub hp')).1) (Finset.mem_filter.1 hp').2

end HJO.Mellit
