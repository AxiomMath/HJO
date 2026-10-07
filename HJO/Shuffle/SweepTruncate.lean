/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWitnessAppend

/-! # Truncating an above-diagonal path at a return, and the fibres of that truncation

`HJO.Mellit.sweepAppend_iff_sum` reads `HJO.Mellit.SweepAppend` as an identity between a sum over
`HJO.Mellit.aboveReturnPaths a b (N+A) (α ++ (A))` and a sum over
`HJO.Mellit.aboveReturnPaths a b N α`, with `N = α.sum`. This file relates the two index sets.

## The splitting

An above-diagonal `(a(N+A), b(N+A))`-path of return composition `α ++ (A)` touches the diagonal at
`(aN, bN)`, because `N` is a partial sum of `α ++ (A)`. So it is exactly a pair: an above-diagonal
`(aN, bN)`-path of return composition `α`, followed by an above-diagonal `(aA, bA)`-path of return
composition `(A)` — the second read in its own rectangle, with the corner `(aN, bN)` as its origin.

* `HJO.Paths.truncHeights` is the first half, `HJO.Paths.tailHeights` the second, and
  `HJO.Paths.appendHeights` the inverse construction.
* `HJO.Paths.hasAboveReturns_truncHeights`, `HJO.Paths.hasAboveReturns_tailHeights` and
  `HJO.Paths.hasAboveReturns_appendHeights` are the transfers of `HJO.Paths.HasAboveReturns`, which
  is where the partial-sum arithmetic is spent.
* `HJO.Mellit.sum_aboveReturnPaths_append_singleton` is the conclusion: a sum over the big index
  set is a double sum, the inner one over `HJO.Mellit.aboveReturnPaths a b A (A)` **independently
  of the outer index**. That is the description of the fibres of the truncation — every fibre is
  one and the same set of tails — and it is what makes the two sums of
  `HJO.Mellit.sweepAppend_iff_sum` comparable at all.

No hypothesis is needed anywhere: `0 < A` and `α.sum = N` are both consequences of membership in
the index set, and when they fail both index sets are empty.

## One identity per base path

`HJO.Mellit.sweepAppend_iff_sum_split` reads the identity with both sums over the *same* index set,
the left one carrying an inner sum over the tails, and `HJO.Mellit.sweepAppend_of_forall_path` then
reduces `HJO.Mellit.SweepAppend` to one identity about **one base path at a time**. That is as far
as the index sets can take it.

## What the extension does to the sweep, exactly

The summand is `HJO.Mellit.partialSweepWord`, a product of the event operators of
`HJO.Mellit.sweepOperator` over `HJO.Mellit.sweptAbove`, and the event operator at a point reads
`HJO.Paths.eventType`, `HJO.Paths.sweepWidth` and `HJO.Paths.sweepRight`. Below the corner column
`x = aN` each of the four is settled here:

* the index set — `HJO.Mellit.sweptAbove_filter_lt_appendHeights`: at a separating level the base's
  index set is *exactly* the low-column part of the extension's, the corner column contributing
  nothing on the base side;
* the swept region — `HJO.Paths.sweptRegion_filter_lt_appendHeights`: unchanged;
* the event type — `HJO.Paths.eventType_appendHeights`: unchanged, since `HJO.Paths.eventType` reads
  the path only at `x` and `x + 1`;
* the width and the right count — `HJO.Paths.sweepWidth_appendHeights` and
  `HJO.Paths.sweepRight_appendHeights`: **shifted**, by exactly the number of live north steps the
  extension has at columns `≥ aN`.

The shift is real and is the whole obstruction. `HJO.Paths.northSteps_appendHeights`: the north
steps of `HJO.Paths.appendHeights z w` are those of `z` together with those of `w` translated by
`(aN, bN)`. `HJO.Paths.liveSteps` selects north steps by a window on the above-diagonal rank `a`
units of diagonal excess wide (`HJO.Paths.attackWindow`, via `HJO.Paths.abovePointRank_succ`), and
that window is rectangle-free on the strip (`HJO.Mellit.live_window_congr`) — so the base's own live
steps survive, and the translated ones, of diagonal excess `a·i - b·s ≥ 0`, are *added*.

The consequence for the word is stated rather than hoped for. At a type-`E` event the operator is
`u · id` and reads neither count, so it survives untouched
(`HJO.Mellit.sweepOperator_appendHeights_of_eventType_E`); at a type-`D` event it picks up exactly
`q` to the number of extra live steps (`HJO.Mellit.sweepOperator_appendHeights_of_eventType_D`). At
types `A`, `B` and `C` the operator is `d_+`, `d_-` or `Δ` read at the width, and a shifted width is
a **different operator**, related to the old one by no scalar. So there is no subword or termwise
comparison of the two sums, and absorbing that shift is what `HJO.Braid.trainDown`,
`HJO.Braid.trainUp` and the replicated letter of `HJO.Mellit.replicatedLetter` are in
`HJO.Mellit.stageTotal` to do.

## The shift in closed form

`HJO.Paths.liveSteps_high_appendHeights` computes it. For `P` strictly inside the strip the extra
live north steps are exactly the corner-translates of the tail's north steps whose **own** diagonal
excess lies in the half-open window `[rk P - a, rk P)`, where `rk = HJO.Paths.diagExcess a b`. Two
things make that clean: the corner translation moves a point *along* the diagonal, so it preserves
the excess (`HJO.Paths.diagExcess_corner_add`); and both tie-breaks of
`HJO.Mellit.abovePointRank_le_iff` are decided by `P.1 < u.1`, so the live-step condition collapses
from a lexicographic comparison to a plain interval (`HJO.Paths.mem_liveSteps_iff_of_lt_fst`), of
width exactly `a` because that is the attack window in excess units.

Three consequences, in increasing order of how much they constrain a proof.

* **The shift does not depend on the base path.** It is a function of the tail and of the single
  integer `rk P` (`HJO.Paths.card_liveSteps_high_appendHeights`,
  `HJO.Paths.card_liveSteps_high_appendHeights_congr`).
* **It is supported on a band.** Nothing on or below the diagonal
  (`HJO.Paths.tailLiveSteps_eq_empty_of_nonpos`), nothing above excess `a·bA`
  (`HJO.Paths.tailLiveSteps_eq_empty_of_gt`); outside `1 ≤ rk P ≤ a·bA` the two event operators are
  literally equal (`HJO.Mellit.sweepOperator_appendHeights_of_diagExcess_outside`).
* **It is *not* constant across the fibre.** `HJO.Paths.card_liveSteps_high_appendHeights_ne`
  exhibits, at `(a, b) = (1, 2)`, `N = 1`, `A = 2`, one point of the base's swept region at which
  the two tails of return composition `(2)` give corrections `2` and `1`. So no factor pulled
  out of the inner sum of `HJO.Mellit.sum_aboveReturnPaths_append_singleton` can absorb the shift:
  the sum over tails has to do it, which is what the power `(Z^{(k+1)}_{a,b})^{A-1}` in
  `HJO.Mellit.stageTotal` is there for.

## The index shift, and what it leaves

Closing the identity needs `d_+`, `d_-` and `Δ` at index `k + δ` related to the same operators at
index `k`. **That is proved** in `HJO/Shuffle/SweepIndexShift.lean`, and the three answers
are not alike:

* `HJO.Sweep.dminus_eq_of_mem_piece`: on `V_k` the lowering operator **does not see its index** —
  `d^♭_-{}^{(m+1)}F = d^♭_-{}^{(k+1)}F` for every `m ≥ k`, with no correction term and no hypothesis
  on `q` or `u`. The type-`B` half of the shift is an equality.
* `HJO.Sweep.dplus_succ_eq_dplus_add`: the raising operator does, and by exactly one Demazure term
  read inside the *same* ascending word both indices carry,
  `d^♭_+{}^{(k+1)}F = d^♭_+{}^{(k)}F + T_{[1,k]}((q-1)y_{k+1}∂_{k+1}(y_{k+1}τ_{k+1,k+1}F))`.
  `HJO.Sweep.dplus_split_prefix` is the same splitting at an arbitrary `δ`.
* `HJO.Sweep.corner_transport_split_prefix`: for the corner there is no separate argument to make.
  `HJO.Sweep.corner_transport_eq` already gives `Δ` in closed form at **every** width, for every
  `q ≠ 1` and with no `q ≠ 0`, and splitting its word at `k` is `HJO.Sweep.cmAscWord_split`.

**`HJO.Sweep.dplus` still carries its index twice** — in the ascending train `T_{1↗k+1}` and in the
variable `y_{k+1}` — so no scalar will do it, and that is not a gap in the bookkeeping:
`HJO.Sweep.dplus_apply_powerSum_not_mem_piece` exhibits `d_+^{(1)}(p_1) ∉ V_1` for every `q ≠ 1`
while `d_+^{(0)}` carries `V_0` into `V_1`, so no conjugation by grading-preserving operators is
`d_+^{(1)}` either. What the shift buys is the Demazure term, not a scalar.

**The braid operators do form a braid system**, and every relation below is proved, with axioms
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`:

* `HJO.Sweep.cmDPlus_braid`, `HJO/Shuffle/CMRaising.lean`;
  `HJO.Sweep.braid_one_cmDPlus_cmDPlus`, `CMRaising.lean`;
* `HJO.Sweep.braid_braid`, `HJO.Sweep.qshift_braid`, `HJO.Sweep.isBraidSystem_braidEnd` —
  `HJO/Shuffle/BraidRelations.lean`;
  `HJO.Sweep.braid_symmetric_mul` — `HJO/Shuffle/MellitShiftGenerators.lean`;
* `(HJO.Sweep.braidEnd q, HJO.Sweep.braidInvEnd q)` **is** a `HJO.Braid.IsBraidSystem k` for
  `q ≠ 0`: `HJO.Sweep.isBraidSystem_braidEnd`, `BraidRelations.lean`.

Lemmas also relate `HJO.Sweep.braidEnd` to the three generators.
`HJO.Sweep.dplus_mul_braidEnd_succ` (`HJO/CMStructure/VmodDplusRelations.lean`) is
`d^♭_+T_i = T_{i+1}d^♭_+`, `HJO.Sweep.braidEnd_mul_dminus`
(`HJO/CMStructure/VmodGenerators.lean`) is `T_id^♭_- = d^♭_-T_i`, and
`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` (`HJO/Shuffle/CornerClosedForm.lean`)
writes `Δ` itself as an ascending word. The bridge between the Carlsson--Mellit generators and the
sweep pair — `HJO.Sweep.dplus_transport` and `HJO.Sweep.dminus_transport`, in
`HJO/SweepBlocks/Transport.lean`, neither reading `q ≠ 0` — is proved too, and
`HJO.Sweep.braid_transport` (`Transport.lean`) carries the braid relations across it.

## What the identity still needs, and it is not on this side

With the index shift proved, what remains is the **round-grouping combinatorics**, not
the operator algebra. `HJO.Mellit.band_clause_one_left_one_one`
(`HJO/Shuffle/SweepAppendBandOneB.lean`) closes the band clause at `a = 1`, every `b > 0`,
`α = (1)`, `A = 1`; what stops the same argument at `a ≥ 2` or `A ≥ 2` is that the number of
nonempty excess levels varies with the tail and the fibre of
`HJO.Paths.card_liveSteps_high_appendHeights` stops being a singleton, so the grouping holds only
after summing over it — which is what the inner sum `(Z^{(k+1)}_{a,b})^{A-1}` of
`HJO.Mellit.stageTotal` is there for, as recorded above.

That the whole shuffle side is one statement is
`HJO.Mellit.sweepAppend_of_forall_band_uniform` (`HJO/Shuffle/SweepAppendNilBand.lean`):
`HJO.Mellit.SweepAppend` follows from the band identity alone, quantified over every composition
with positive parts, `α = []` included, the degenerate clause being
`HJO.Mellit.hzero_of_band_nil`.

Mellit's own route is worth knowing, and it is the same grouping: he runs the append-a-part
induction inside the braid monoid `𝔹⁺_{k+1}(𝕋_0)` and only afterwards applies the representation to
`d_+^{k+1}(1)`, so he never compares the sweep of an extended path with the sweep of its truncation
at all. The single step where his argument regrades —
`φ^*_+(B)d_+^{k+1}(1) = (-y_1d^*_+)Bd_+^k(1)`, i.e.
`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` together with
`HJO.Sweep.dplus_dplusIter` — rests on the Dyck-path-algebra relations proved in this library.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

/-! ### Partial sums of a composition with one part appended -/

/-- **A partial sum of `α ++ (A)` that does not exceed `α.sum` is a partial sum of `α`.** The list
of prefix sums of `α ++ (A)` is that of `α` with `α.sum + A` appended, and every prefix sum of `α`
is at most `α.sum`; so below `α.sum` the two lists have the same members. -/
theorem mem_scanl_append_singleton_iff {α : List ℕ} {A k : ℕ} (hk : k ≤ α.sum) :
    k ∈ (α ++ [A]).scanl (· + ·) 0 ↔ k ∈ α.scanl (· + ·) 0 := by
  rw [mem_scanl_add_iff, mem_scanl_add_iff]
  simp only [Nat.zero_add, List.length_append, List.length_cons, List.length_nil]
  constructor
  · rintro ⟨m, hm, hsum⟩
    rcases Nat.lt_or_ge m (α.length + 1) with h | h
    · exact ⟨m, by omega, by rwa [List.take_append_of_le_length (by omega)] at hsum⟩
    · have hm' : m = α.length + 1 := by omega
      subst hm'
      have hfull : ((α ++ [A]).take (α.length + 1)).sum = α.sum + A := by simp
      rw [hfull] at hsum
      exact ⟨α.length, le_rfl, by rw [List.take_length]; omega⟩
  · rintro ⟨m, hm, hsum⟩
    exact ⟨m, by omega, by rwa [List.take_append_of_le_length hm]⟩

/-- **The partial sums of `α ++ (A)` at or above `α.sum` are `α.sum` and `α.sum + A`.** Every
prefix sum of `α` is at most `α.sum`, so the only members of the prefix-sum list of `α ++ (A)` in
the window `[α.sum, α.sum + A]` are its two ends. This is the clause that turns the return
condition of `α ++ (A)` above the touch point `(aN, bN)` into the return condition of the one-part
composition `(A)`. -/
theorem mem_scanl_append_singleton_add_iff {α : List ℕ} {A j : ℕ} (hj : j ≤ A) :
    α.sum + j ∈ (α ++ [A]).scanl (· + ·) 0 ↔ (j = 0 ∨ j = A) := by
  rw [mem_scanl_add_iff]
  simp only [Nat.zero_add, List.length_append, List.length_cons, List.length_nil]
  constructor
  · rintro ⟨m, hm, hsum⟩
    rcases Nat.lt_or_ge m (α.length + 1) with h | h
    · rw [List.take_append_of_le_length (by omega)] at hsum
      have hle : (α.take m).sum ≤ α.sum := by
        have := List.monotone_sum_take α (show m ≤ α.length by omega)
        simpa using this
      omega
    · have hm' : m = α.length + 1 := by omega
      subst hm'
      have hfull : ((α ++ [A]).take (α.length + 1)).sum = α.sum + A := by simp
      rw [hfull] at hsum
      omega
  · rintro (rfl | rfl)
    · refine ⟨α.length, by omega, ?_⟩
      rw [List.take_append_of_le_length le_rfl, List.take_length]
      omega
    · exact ⟨α.length + 1, le_rfl, by simp⟩

/-! ### The rank window is rectangle-free on the strip -/

section RankOrder

variable {a b N : ℕ}

/-- The strict half of `HJO.Mellit.abovePointRank_le_congr`. -/
theorem abovePointRank_lt_congr {M : ℕ} (hN : 0 < N) (hM : 0 < M) {x y x' y' : ℕ}
    (hx : x ≤ a * N) (hx' : x' ≤ a * N) (hxM : x ≤ a * M) (hx'M : x' ≤ a * M) :
    (ParkingFunctions.abovePointRank a b N x y < ParkingFunctions.abovePointRank a b N x' y')
      ↔ (ParkingFunctions.abovePointRank a b M x y
          < ParkingFunctions.abovePointRank a b M x' y') := by
  rw [lt_iff_not_ge, lt_iff_not_ge, not_iff_not]
  exact abovePointRank_le_congr hN hM hx' hx hx'M hxM

/-- **The live-step window of `HJO.Paths.liveSteps` does not depend on the rectangle**, for a north
step and a point both in the strip `0 ≤ x ≤ aN`. The first inequality is
`HJO.Mellit.abovePointRank_le_congr`; the second is the same statement about the *head* of the north
step, by `HJO.Paths.abovePointRank_succ`, which is why the attack window needs no separate
treatment. -/
theorem live_window_congr {M : ℕ} (hN : 0 < N) (hM : 0 < M) {u P : ℕ × ℕ}
    (hu : u.1 ≤ a * N) (hPx : P.1 ≤ a * N) (huM : u.1 ≤ a * M) (hPM : P.1 ≤ a * M) :
    (ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
          ParkingFunctions.abovePointRank a b N P.1 P.2 ∧
        ParkingFunctions.abovePointRank a b N P.1 P.2 <
          ParkingFunctions.abovePointRank a b N u.1 u.2 + Paths.attackWindow a N)
      ↔ (ParkingFunctions.abovePointRank a b M u.1 u.2 ≤
            ParkingFunctions.abovePointRank a b M P.1 P.2 ∧
          ParkingFunctions.abovePointRank a b M P.1 P.2 <
            ParkingFunctions.abovePointRank a b M u.1 u.2 + Paths.attackWindow a M) := by
  rw [← Paths.abovePointRank_succ a b N u.1 u.2, ← Paths.abovePointRank_succ a b M u.1 u.2]
  exact and_congr (abovePointRank_le_congr hN hM hu hPx huM hPM)
    (abovePointRank_lt_congr hN hM hPx hu hPM huM)

end RankOrder

end HJO.Mellit

namespace HJO.Paths

variable {a b N A : ℕ}

/-! ### The truncation, the tail, and the path they come from -/

/-- **The truncation of a candidate `(a(N+A), b(N+A))`-path to the rectangle `aN × bN`.** The
height function is restricted to `r ≤ aN` and capped at `bN`, the cap being what makes the
definition total: on a path that touches the diagonal at `(aN, bN)` — the only case of interest,
and the hypothesis of `HJO.Paths.ht_truncHeights_eq` — no height below `aN` reaches past `bN`, so
nothing is cut. -/
def truncHeights (y : Heights a b (N + A)) : Heights a b N :=
  fun r => ⟨min (ht y (r : ℕ)) (b * N), Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- **The tail of a candidate `(a(N+A), b(N+A))`-path, read in the rectangle `aA × bA`.** The
height at `s` is the height of the original path at `aN + s`, measured from `bN`. Both the truncated
subtraction and the cap at `bA` are harmless on a path touching the diagonal at `(aN, bN)`, by
`HJO.Paths.ht_tailHeights_eq`. -/
def tailHeights (y : Heights a b (N + A)) : Heights a b A :=
  fun s => ⟨min (ht y (a * N + (s : ℕ)) - b * N) (b * A), Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- **Laying a candidate `(aA, bA)`-path on top of the corner of a candidate `(aN, bN)`-path.** The
inverse of the pair `(HJO.Paths.truncHeights, HJO.Paths.tailHeights)`, by
`HJO.Paths.appendHeights_truncHeights_tailHeights`. -/
def appendHeights (z : Heights a b N) (w : Heights a b A) : Heights a b (N + A) :=
  fun r => ⟨if (r : ℕ) ≤ a * N then ht z (r : ℕ) else b * N + ht w ((r : ℕ) - a * N), by
    have h1 : ht z (r : ℕ) ≤ b * N := ht_le_mul z _
    have h2 : ht w ((r : ℕ) - a * N) ≤ b * A := ht_le_mul w _
    have h3 : b * (N + A) = b * N + b * A := Nat.mul_add b N A
    split <;> omega⟩

/-! ### The height functions of the three maps -/

/-- The height function of the truncation, inside the small rectangle. -/
theorem ht_truncHeights_apply {y : Heights a b (N + A)} {r : ℕ} (hr : r ≤ a * N) :
    ht (truncHeights y) r = min (ht y r) (b * N) :=
  ht_coe (truncHeights y) ⟨r, by omega⟩

/-- The height function of the tail, inside its rectangle. -/
theorem ht_tailHeights_apply {y : Heights a b (N + A)} {s : ℕ} (hs : s ≤ a * A) :
    ht (tailHeights y) s = min (ht y (a * N + s) - b * N) (b * A) :=
  ht_coe (tailHeights y) ⟨s, by omega⟩

/-- The height function of a laid-on pair, inside the big rectangle. -/
theorem ht_appendHeights_apply {z : Heights a b N} {w : Heights a b A} {r : ℕ}
    (hr : r ≤ a * (N + A)) :
    ht (appendHeights z w) r = if r ≤ a * N then ht z r else b * N + ht w (r - a * N) := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  exact ht_coe (appendHeights z w) ⟨r, by omega⟩

/-- Below the corner, a laid-on pair is its first half. -/
theorem ht_appendHeights_of_le {z : Heights a b N} {w : Heights a b A} {r : ℕ} (hr : r ≤ a * N) :
    ht (appendHeights z w) r = ht z r := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  rw [ht_appendHeights_apply (show r ≤ a * (N + A) by omega)]
  split_ifs
  rfl

/-- **At and above the corner, a laid-on pair is its second half, raised by `bN`.** The two branches
of `HJO.Paths.appendHeights` agree at `r = aN` exactly when the first half ends at the corner and
the second half starts at its own origin, which is why both hypotheses appear. -/
theorem ht_appendHeights_of_ge {z : Heights a b N} {w : Heights a b A}
    (hz : ht z (a * N) = b * N) (hw : ht w 0 = 0) {r : ℕ} (h1 : a * N ≤ r)
    (h2 : r ≤ a * (N + A)) :
    ht (appendHeights z w) r = b * N + ht w (r - a * N) := by
  rw [ht_appendHeights_apply h2]
  split_ifs with h
  · obtain rfl : r = a * N := by omega
    rw [hz, Nat.sub_self, hw, Nat.add_zero]
  · rfl

/-- **On a path that returns to the diagonal at `(aN, bN)` the truncation cuts nothing.** -/
theorem ht_truncHeights_eq {y : Heights a b (N + A)} (hy : IsAboveDiagonal y)
    (htop : ht y (a * N) = b * N) {r : ℕ} (hr : r ≤ a * N) :
    ht (truncHeights y) r = ht y r := by
  have hmono : Monotone (ht y) := ht_mono hy.2.2.1
  have hle : ht y r ≤ b * N := by rw [← htop]; exact hmono hr
  rw [ht_truncHeights_apply hr, min_eq_left hle]

/-- **On a path that returns to the diagonal at `(aN, bN)` the tail is the honest difference.** -/
theorem ht_tailHeights_eq {y : Heights a b (N + A)} (hy : IsAboveDiagonal y)
    (htop : ht y (a * N) = b * N) {s : ℕ} (hs : s ≤ a * A) :
    ht (tailHeights y) s = ht y (a * N + s) - b * N := by
  have hbNA : b * (N + A) = b * N + b * A := Nat.mul_add b N A
  have hmono : Monotone (ht y) := ht_mono hy.2.2.1
  have hge : b * N ≤ ht y (a * N + s) := by
    rw [← htop]; exact hmono (Nat.le_add_right _ _)
  have hle : ht y (a * N + s) ≤ b * (N + A) := ht_le_mul y _
  rw [ht_tailHeights_apply hs, min_eq_left (by omega)]

/-- The height of the original path above the corner, in terms of its tail. -/
theorem ht_eq_add_ht_tailHeights {y : Heights a b (N + A)} (hy : IsAboveDiagonal y)
    (htop : ht y (a * N) = b * N) {s : ℕ} (hs : s ≤ a * A) :
    ht y (a * N + s) = b * N + ht (tailHeights y) s := by
  have hmono : Monotone (ht y) := ht_mono hy.2.2.1
  have hge : b * N ≤ ht y (a * N + s) := by
    rw [← htop]; exact hmono (Nat.le_add_right _ _)
  rw [ht_tailHeights_eq hy htop hs]
  omega

/-! ### The three maps are mutually inverse -/

/-- Laying on and then truncating returns the first half. -/
@[simp]
theorem truncHeights_appendHeights (z : Heights a b N) (w : Heights a b A) :
    truncHeights (appendHeights z w) = z := by
  funext r
  refine Fin.val_injective ?_
  have hr : (r : ℕ) ≤ a * N := by omega
  change min (ht (appendHeights z w) (r : ℕ)) (b * N) = ((z r : ℕ))
  rw [ht_appendHeights_of_le hr, ht_coe, min_eq_left (Nat.lt_succ_iff.1 (z r).isLt)]

/-- Laying on and then taking the tail returns the second half. -/
theorem tailHeights_appendHeights {z : Heights a b N} {w : Heights a b A} (hw : ht w 0 = 0) :
    tailHeights (appendHeights z w) = w := by
  funext s
  refine Fin.val_injective ?_
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have hs : (s : ℕ) ≤ a * A := by omega
  have hwb : ht w (s : ℕ) ≤ b * A := ht_le_mul w _
  change min (ht (appendHeights z w) (a * N + (s : ℕ)) - b * N) (b * A) = ((w s : ℕ))
  rcases Nat.eq_zero_or_pos (s : ℕ) with h0 | h0
  · rw [h0, Nat.add_zero, ht_appendHeights_of_le le_rfl]
    have h1 : ht z (a * N) ≤ b * N := ht_le_mul z _
    have h2 : ht w 0 = ((w s : ℕ)) := by rw [hw, ← ht_coe w s, h0, hw]
    omega
  · rw [ht_appendHeights_apply (by omega)]
    split_ifs with h
    · omega
    · rw [show a * N + (s : ℕ) - a * N = (s : ℕ) by omega, ht_coe]
      omega

/-- **Truncating and taking the tail loses nothing**, on a path that returns to the diagonal at
`(aN, bN)`. -/
theorem appendHeights_truncHeights_tailHeights {y : Heights a b (N + A)} (hy : IsAboveDiagonal y)
    (htop : ht y (a * N) = b * N) :
    appendHeights (truncHeights y) (tailHeights y) = y := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have htrunc : ht (truncHeights y) (a * N) = b * N := by
    rw [ht_truncHeights_eq hy htop le_rfl, htop]
  have htail : ht (tailHeights y) 0 = 0 := by
    rw [ht_tailHeights_eq hy htop (Nat.zero_le _), Nat.add_zero, htop, Nat.sub_self]
  funext r
  refine Fin.val_injective ?_
  have hr : (r : ℕ) ≤ a * (N + A) := by omega
  rw [← ht_coe (appendHeights _ _) r, ← ht_coe y r]
  rcases le_or_gt (r : ℕ) (a * N) with h | h
  · rw [ht_appendHeights_of_le h, ht_truncHeights_eq hy htop h]
  · obtain ⟨s, hs⟩ : ∃ s, (r : ℕ) = a * N + s := ⟨(r : ℕ) - a * N, by omega⟩
    rw [ht_appendHeights_of_ge htrunc htail h.le hr, hs, show a * N + s - a * N = s by omega]
    exact (ht_eq_add_ht_tailHeights hy htop (by omega)).symm

/-! ### The above-diagonal condition transfers -/

/-- The truncation of an above-diagonal path that returns at `(aN, bN)` is above-diagonal. -/
theorem isAboveDiagonal_truncHeights {y : Heights a b (N + A)} (hy : IsAboveDiagonal y)
    (htop : ht y (a * N) = b * N) : IsAboveDiagonal (truncHeights y) := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht_truncHeights_eq hy htop (Nat.zero_le _)]; exact hy.1
  · rw [ht_truncHeights_eq hy htop le_rfl, htop]
  · intro r hr
    rw [ht_truncHeights_eq hy htop hr.le, ht_truncHeights_eq hy htop (by omega)]
    exact hy.2.2.1 r (by omega)
  · intro r hr
    rw [ht_truncHeights_eq hy htop hr]
    exact hy.2.2.2 r (by omega)

/-- The tail of an above-diagonal path that returns at `(aN, bN)` is above-diagonal in its own
rectangle. The diagonal inequality is where the corner is subtracted off both sides: the tail's
`b·s ≤ a·ht s` is the original's `b(aN + s) ≤ a·ht(aN + s)` less `a·b·N = b·a·N`. -/
theorem isAboveDiagonal_tailHeights {y : Heights a b (N + A)} (hy : IsAboveDiagonal y)
    (htop : ht y (a * N) = b * N) : IsAboveDiagonal (tailHeights y) := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have hbNA : b * (N + A) = b * N + b * A := Nat.mul_add b N A
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht_tailHeights_eq hy htop (Nat.zero_le _), Nat.add_zero, htop, Nat.sub_self]
  · rw [ht_tailHeights_eq hy htop le_rfl, show a * N + a * A = a * (N + A) by omega, hy.2.1]
    omega
  · intro s hs
    rw [ht_tailHeights_eq hy htop hs.le, ht_tailHeights_eq hy htop (by omega)]
    have hstep := hy.2.2.1 (a * N + s) (by omega)
    rw [show a * N + s + 1 = a * N + (s + 1) by omega] at hstep
    omega
  · intro s hs
    rw [ht_tailHeights_eq hy htop hs, Nat.mul_sub]
    refine Nat.le_sub_of_add_le ?_
    calc b * s + a * (b * N) = b * (a * N + s) := by ring
      _ ≤ a * ht y (a * N + s) := hy.2.2.2 _ (by omega)

/-- Laying an above-diagonal path on the corner of another gives an above-diagonal path. -/
theorem isAboveDiagonal_appendHeights {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) :
    IsAboveDiagonal (appendHeights z w) := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have hbNA : b * (N + A) = b * N + b * A := Nat.mul_add b N A
  have hge : ∀ r : ℕ, a * N ≤ r → r ≤ a * (N + A) →
      ht (appendHeights z w) r = b * N + ht w (r - a * N) :=
    fun r h1 h2 => ht_appendHeights_of_ge hz.2.1 hw.1 h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht_appendHeights_of_le (Nat.zero_le _)]; exact hz.1
  · rw [hge _ (by omega) le_rfl, show a * (N + A) - a * N = a * A by omega, hw.2.1]
    omega
  · intro r hr
    rcases Nat.lt_or_ge r (a * N) with h | h
    · rw [ht_appendHeights_of_le h.le, ht_appendHeights_of_le (by omega)]
      exact hz.2.2.1 r h
    · rw [hge r h (by omega), hge (r + 1) (by omega) (by omega),
        show r + 1 - a * N = r - a * N + 1 by omega]
      have hstep := hw.2.2.1 (r - a * N) (by omega)
      omega
  · intro r hr
    rcases le_or_gt r (a * N) with h | h
    · rw [ht_appendHeights_of_le h]; exact hz.2.2.2 r h
    · rw [hge r h.le hr, Nat.mul_add]
      have hwr := hw.2.2.2 (r - a * N) (by omega)
      have hzN : b * (a * N) = a * (b * N) := by ring
      have hbr : b * r = b * (a * N) + b * (r - a * N) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      omega

/-! ### The return composition transfers -/

/-- A path of return composition `α ++ (A)` touches the diagonal at the corner `(aN, bN)`, `N`
being a partial sum. This is the one geometric fact the whole splitting rests on. -/
theorem ht_eq_of_hasAboveReturns_append {α : List ℕ} {y : Heights a b (N + A)}
    (h : HasAboveReturns (α ++ [A]) y) (hsum : α.sum = N) : ht y (a * N) = b * N := by
  refine (h.2.2.2 N (by omega)).2 ?_
  rw [HJO.Mellit.mem_scanl_append_singleton_iff (le_of_eq hsum.symm),
    HJO.Mellit.mem_scanl_add_iff]
  exact ⟨α.length, le_rfl, by rw [List.take_length]; omega⟩

/-- The appended composition determines `α.sum`. -/
theorem sum_eq_of_hasAboveReturns_append {α : List ℕ} {y : Heights a b (N + A)}
    (h : HasAboveReturns (α ++ [A]) y) : α.sum = N := by
  have hs := h.2.2.1
  rw [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] at hs
  omega

/-- **The truncation of a path of return composition `α ++ (A)` has return composition `α`.** The
returns below `aN` are the partial sums of `α ++ (A)` that do not exceed `N`, which are exactly the
partial sums of `α` (`HJO.Mellit.mem_scanl_append_singleton_iff`). -/
theorem hasAboveReturns_truncHeights {α : List ℕ} {y : Heights a b (N + A)}
    (h : HasAboveReturns (α ++ [A]) y) : HasAboveReturns α (truncHeights y) := by
  have hsum : α.sum = N := sum_eq_of_hasAboveReturns_append h
  have htop : ht y (a * N) = b * N := ht_eq_of_hasAboveReturns_append h hsum
  refine ⟨isAboveDiagonal_truncHeights h.1 htop, fun x hx => h.2.1 x (by simp [hx]), hsum, ?_⟩
  intro k hk
  have hak : a * k ≤ a * N := Nat.mul_le_mul_left a hk
  rw [ht_truncHeights_eq h.1 htop hak, h.2.2.2 k (by omega),
    HJO.Mellit.mem_scanl_append_singleton_iff (by omega)]

/-- **The tail of a path of return composition `α ++ (A)` has return composition `(A)`.** Above the
touch point the only returns of `α ++ (A)` are `N` and `N + A`
(`HJO.Mellit.mem_scanl_append_singleton_add_iff`), which is exactly the one-part condition. -/
theorem hasAboveReturns_tailHeights {α : List ℕ} {y : Heights a b (N + A)}
    (h : HasAboveReturns (α ++ [A]) y) : HasAboveReturns [A] (tailHeights y) := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have hsum : α.sum = N := sum_eq_of_hasAboveReturns_append h
  have htop : ht y (a * N) = b * N := ht_eq_of_hasAboveReturns_append h hsum
  refine ⟨isAboveDiagonal_tailHeights h.1 htop, ?_, by simp, ?_⟩
  · intro x hx
    exact h.2.1 x (by simp only [List.mem_singleton] at hx; simp [hx])
  · intro j hj
    have haj : a * j ≤ a * A := Nat.mul_le_mul_left a hj
    have hge : b * N ≤ ht y (a * N + a * j) := by
      rw [← htop]; exact ht_mono h.1.2.2.1 (Nat.le_add_right _ _)
    have hkey : ht y (a * N + a * j) = b * N + b * j ↔ N + j ∈ (α ++ [A]).scanl (· + ·) 0 := by
      rw [show a * N + a * j = a * (N + j) by ring, show b * N + b * j = b * (N + j) by ring]
      exact h.2.2.2 (N + j) (by omega)
    rw [ht_tailHeights_eq h.1 htop haj,
      show (ht y (a * N + a * j) - b * N = b * j) ↔
        (ht y (a * N + a * j) = b * N + b * j) from by omega,
      hkey, ← hsum, HJO.Mellit.mem_scanl_append_singleton_add_iff hj]
    simp

/-- **Laying a path of return composition `(A)` on one of return composition `α` gives a path of
return composition `α ++ (A)`.** -/
theorem hasAboveReturns_appendHeights {α : List ℕ} {z : Heights a b N} {w : Heights a b A}
    (hz : HasAboveReturns α z) (hw : HasAboveReturns [A] w) :
    HasAboveReturns (α ++ [A]) (appendHeights z w) := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have hbNA : b * (N + A) = b * N + b * A := Nat.mul_add b N A
  have hsum : α.sum = N := hz.2.2.1
  have hge : ∀ r : ℕ, a * N ≤ r → r ≤ a * (N + A) →
      ht (appendHeights z w) r = b * N + ht w (r - a * N) :=
    fun r h1 h2 => ht_appendHeights_of_ge hz.1.2.1 hw.1.1 h1 h2
  refine ⟨isAboveDiagonal_appendHeights hz.1 hw.1, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hz.2.1 x hx
    · exact hw.2.1 x hx
  · rw [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, hsum]
  · intro k hk
    rcases le_or_gt k N with h | h
    · have hak : a * k ≤ a * N := Nat.mul_le_mul_left a h
      rw [ht_appendHeights_of_le hak, hz.2.2.2 k h,
        HJO.Mellit.mem_scanl_append_singleton_iff (by omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, k = N + j := ⟨k - N, by omega⟩
      have hj : j ≤ A := by omega
      have haj : a * j ≤ a * A := Nat.mul_le_mul_left a hj
      rw [show a * (N + j) = a * N + a * j by ring, hge _ (by omega) (by omega),
        show a * N + a * j - a * N = a * j by omega, show b * (N + j) = b * N + b * j by ring,
        show (b * N + ht w (a * j) = b * N + b * j) ↔ (ht w (a * j) = b * j) from by omega,
        hw.2.2.2 j hj, ← hsum, HJO.Mellit.mem_scanl_append_singleton_add_iff hj]
      simp

/-! ### The north steps, and why no termwise comparison exists -/

/-- **The north steps of a laid-on pair are those of the first half together with those of the
second, translated by the corner.** This is the exact reason there is no subword comparison of the
two sums of `HJO.Mellit.sweepAppend_iff_sum`: the event operator of `HJO.Mellit.sweepOperator` at a
point reads `HJO.Paths.sweepWidth` and `HJO.Paths.sweepRight`, both counts of `HJO.Paths.liveSteps`
at that point, and `HJO.Paths.liveSteps` is a rank-window condition on *all* the north steps of the
path — the translated ones included. -/
theorem northSteps_appendHeights {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) :
    northSteps (appendHeights z w)
      = northSteps z ∪ (northSteps w).image (fun p => (a * N + p.1, b * N + p.2)) := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have hbNA : b * (N + A) = b * N + b * A := Nat.mul_add b N A
  have hge : ∀ r : ℕ, a * N ≤ r → r ≤ a * (N + A) →
      ht (appendHeights z w) r = b * N + ht w (r - a * N) :=
    fun r h1 h2 => ht_appendHeights_of_ge hz.2.1 hw.1 h1 h2
  ext P
  obtain ⟨x, k⟩ := P
  simp only [mem_northSteps_iff, Finset.mem_union, Finset.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases Nat.lt_or_ge x (a * N) with h | h
    · refine Or.inl ⟨h, ?_, ?_⟩
      · rwa [ht_appendHeights_of_le h.le] at h2
      · rwa [ht_appendHeights_of_le (by omega)] at h3
    · rw [hge x h (by omega)] at h2
      rw [hge (x + 1) (by omega) (by omega), show x + 1 - a * N = x - a * N + 1 by omega] at h3
      exact Or.inr ⟨x - a * N, k - b * N, ⟨by omega, by omega, by omega⟩, by omega, by omega⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨s, i, ⟨h1, h2, h3⟩, hs, hi⟩)
    · refine ⟨by omega, ?_, ?_⟩
      · rwa [ht_appendHeights_of_le h1.le]
      · rwa [ht_appendHeights_of_le (by omega)]
    · subst hs
      subst hi
      refine ⟨by omega, ?_, ?_⟩
      · rw [hge _ (by omega) (by omega), show a * N + s - a * N = s by omega]
        omega
      · rw [hge _ (by omega) (by omega), show a * N + s + 1 - a * N = s + 1 by omega]
        omega

/-! ### The event type is shared below the corner column, the width and the right count are not -/

/-- **Below the corner column the swept region of the extension is the swept region of the base.**
`HJO.Paths.sweptRegion` reads the path only at `x` and `x + 1`. -/
theorem sweptRegion_filter_lt_appendHeights {z : Heights a b N} {w : Heights a b A} :
    {p ∈ sweptRegion (appendHeights z w) | p.1 < a * N} = {p ∈ sweptRegion z | p.1 < a * N} := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  ext p
  simp only [Finset.mem_filter, mem_sweptRegion]
  constructor
  · rintro ⟨⟨_, h2, h3⟩, h4⟩
    rw [ht_appendHeights_of_le (show p.1 + 1 ≤ a * N by omega)] at h3
    exact ⟨⟨by omega, h2, h3⟩, h4⟩
  · rintro ⟨⟨_, h2, h3⟩, h4⟩
    refine ⟨⟨by omega, h2, ?_⟩, h4⟩
    rw [ht_appendHeights_of_le (show p.1 + 1 ≤ a * N by omega)]
    exact h3

/-- **Below the corner column the event type of `HJO.Paths.eventType` is unchanged by the
extension.** `HJO.Paths.eventType` reads the path only at `x` and `x + 1`, and the guard
`x + 1 ≤ aN` on the outgoing letter holds in both rectangles once `x + 1 ≤ aN`. So the *shape* of
the event operator is shared; what the extension changes is the index it is read at. -/
theorem eventType_appendHeights {z : Heights a b N} {w : Heights a b A} {P : ℕ × ℕ}
    (hP : P.1 + 1 ≤ a * N) : eventType (appendHeights z w) P = eventType z P := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have e1 : ht (appendHeights z w) P.1 = ht z P.1 := ht_appendHeights_of_le (by omega)
  have e2 : ht (appendHeights z w) (P.1 + 1) = ht z (P.1 + 1) := ht_appendHeights_of_le hP
  have h1 : P.1 + 1 ≤ a * (N + A) := by omega
  simp only [eventType, e1, e2, h1, hP, true_and]

/-- **Below the corner column the live north steps of the extension are those of the base.** The
window of `HJO.Paths.liveSteps` is rectangle-free on the strip (`HJO.Mellit.live_window_congr`) and
by `HJO.Paths.northSteps_appendHeights` the only other north steps of the extension sit at columns
`≥ aN`. -/
theorem liveSteps_filter_lt_appendHeights {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) {P : ℕ × ℕ}
    (hP : P.1 ≤ a * N) :
    {u ∈ liveSteps (appendHeights z w) P | u.1 < a * N} = liveSteps z P := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have hMpos : 0 < N + A := by omega
  ext u
  simp only [liveSteps, Finset.mem_filter, northSteps_appendHeights hz hw, Finset.mem_union,
    Finset.mem_image, Prod.exists]
  constructor
  · rintro ⟨⟨hun, hcond⟩, hlt⟩
    have huz : u ∈ northSteps z := by
      rcases hun with h | h
      · exact h
      · obtain ⟨s, i, _, hs⟩ := h
        have hu1 : u.1 = a * N + s := by rw [← hs]
        omega
    exact ⟨huz, (HJO.Mellit.live_window_congr hN hMpos hlt.le hP (by omega) (by omega)).2 hcond⟩
  · rintro ⟨huz, hcond⟩
    have hu1 : u.1 < a * N := (mem_northSteps_iff.1 huz).1
    exact ⟨⟨Or.inl huz, (HJO.Mellit.live_window_congr hN hMpos hu1.le hP (by omega)
      (by omega)).1 hcond⟩, hu1⟩

/-- **The width shift of `HJO.Paths.sweepWidth` under an extension, exactly.** At a point of the
strip the width of the extension is the width of the base *plus* the number of live north steps the
extension has at columns `≥ aN` — the translated north steps of the tail that the level line through
`P` crosses. This is the quantity the trains of `HJO.Braid.trainDown` and `HJO.Braid.trainUp` and
the replicated letter of `HJO.Mellit.replicatedLetter` are in `HJO.Mellit.stageTotal` to absorb. -/
theorem sweepWidth_appendHeights {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) {P : ℕ × ℕ}
    (hP : P.1 ≤ a * N) :
    sweepWidth (appendHeights z w) P
      = sweepWidth z P + #{u ∈ liveSteps (appendHeights z w) P | a * N ≤ u.1} := by
  have h := Finset.card_filter_add_card_filter_not (s := liveSteps (appendHeights z w) P)
    (fun u => u.1 < a * N)
  rw [liveSteps_filter_lt_appendHeights hz hw hN hP] at h
  simp only [not_lt] at h
  exact h.symm

/-- **The right-count shift of `HJO.Paths.sweepRight` under an extension, exactly.** Strictly inside
the strip every extra live north step is strictly to the right of `P`, so `HJO.Paths.sweepRight`
picks up the same correction as `HJO.Paths.sweepWidth`. -/
theorem sweepRight_appendHeights {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) {P : ℕ × ℕ}
    (hP : P.1 < a * N) :
    sweepRight (appendHeights z w) P
      = sweepRight z P + #{u ∈ liveSteps (appendHeights z w) P | a * N ≤ u.1} := by
  have key : {u ∈ liveSteps (appendHeights z w) P | P.1 < u.1}
      = {u ∈ liveSteps z P | P.1 < u.1} ∪
          {u ∈ liveSteps (appendHeights z w) P | a * N ≤ u.1} := by
    rw [← liveSteps_filter_lt_appendHeights hz hw hN hP.le]
    ext u
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hu, h1⟩
      rcases Nat.lt_or_ge u.1 (a * N) with h | h
      · exact Or.inl ⟨⟨hu, h⟩, h1⟩
      · exact Or.inr ⟨hu, h⟩
    · rintro (⟨⟨hu, _⟩, h1⟩ | ⟨hu, h⟩)
      · exact ⟨hu, h1⟩
      · exact ⟨hu, by omega⟩
  have hdisj : Disjoint {u ∈ liveSteps z P | P.1 < u.1}
      {u ∈ liveSteps (appendHeights z w) P | a * N ≤ u.1} := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    rw [Finset.mem_filter] at hu1 hu2
    have := (mem_northSteps_iff.1 (liveSteps_subset z P hu1.1)).1
    omega
  change #{u ∈ liveSteps (appendHeights z w) P | P.1 < u.1} = _
  rw [key, Finset.card_union_of_disjoint hdisj]
  rfl

/-! ### The width shift in closed form: a window in the tail's own diagonal excess -/

/-- **The diagonal excess `ay - bx` of a lattice point.** This is the quantity
`HJO.ParkingFunctions.abovePointRank` multiplies by the rectangle constant, and by
`HJO.Mellit.abovePointRank_le_iff` it is the *only* thing about a point the rank order sees on the
strip, apart from the abscissa tie-break. The attack window of `HJO.Paths.attackWindow` is `a` units
of it wide, by `HJO.Paths.abovePointRank_succ`. -/
def diagExcess (a b : ℕ) (P : ℕ × ℕ) : ℤ := (a : ℤ) * P.2 - (b : ℤ) * P.1

/-- The excess of a point translated by the corner `(aN, bN)` is its own excess: the translation
moves a point along the diagonal. This is what makes the tail's contribution readable in the tail's
own coordinates. -/
theorem diagExcess_corner_add (a b N : ℕ) (p : ℕ × ℕ) :
    diagExcess a b (a * N + p.1, b * N + p.2) = diagExcess a b p := by
  simp only [diagExcess]
  push_cast
  ring

/-- **Membership in `HJO.Paths.liveSteps` at a north step strictly to the right of the point, in
closed form.** Both tie-breaks of `HJO.Mellit.abovePointRank_le_iff` are decided by `P.1 < u.1`, so
what is left is a half-open window of width `a` in the diagonal excess: the level line through `P`
crosses `u` exactly when the excess of `u` lies in `[rk P - a, rk P)`. -/
theorem mem_liveSteps_iff_of_lt_fst {M : ℕ} (hM : 0 < M) {y : Heights a b M} {u P : ℕ × ℕ}
    (hu : u ∈ northSteps y) (hP : P.1 ≤ a * M) (hlt : P.1 < u.1) :
    u ∈ liveSteps y P ↔
      (diagExcess a b P - a ≤ diagExcess a b u ∧ diagExcess a b u < diagExcess a b P) := by
  have hu1 : u.1 < a * M := (mem_northSteps_iff.1 hu).1
  have hne : ¬ (u.1 ≤ P.1) := by omega
  have h1 : (ParkingFunctions.abovePointRank a b M u.1 u.2
        ≤ ParkingFunctions.abovePointRank a b M P.1 P.2)
      ↔ diagExcess a b u < diagExcess a b P := by
    rw [HJO.Mellit.abovePointRank_le_iff hM hu1.le hP]
    simp only [diagExcess, hne, and_false, or_false]
  have h2 : (ParkingFunctions.abovePointRank a b M P.1 P.2
        < ParkingFunctions.abovePointRank a b M u.1 u.2 + attackWindow a M)
      ↔ diagExcess a b P - a ≤ diagExcess a b u := by
    rw [← abovePointRank_succ a b M u.1 u.2, lt_iff_not_ge,
      HJO.Mellit.abovePointRank_le_iff hM hu1.le hP]
    simp only [diagExcess, hne, and_false, or_false, not_lt]
    push_cast
    constructor <;> intro h <;> linarith
  simp only [liveSteps, Finset.mem_filter, h1, h2, hu, true_and]
  exact and_comm

/-- **The north steps of a tail that the level line of diagonal excess `d` crosses**: those whose
own excess lies in the half-open window `[d - a, d)`. Nothing here mentions the base path, the
rectangle it lives in, or the level — only `w`, and the single integer `d`. -/
def tailLiveSteps {A : ℕ} (w : Heights a b A) (d : ℤ) : Finset (ℕ × ℕ) :=
  {p ∈ northSteps w | d - a ≤ diagExcess a b p ∧ diagExcess a b p < d}

/-- A tail's north step has nonnegative excess, its path being above-diagonal. -/
theorem le_diagExcess_of_mem_northSteps {A : ℕ} {w : Heights a b A} (hw : IsAboveDiagonal w)
    {p : ℕ × ℕ} (hp : p ∈ northSteps w) : 0 ≤ diagExcess a b p := by
  obtain ⟨h1, h2, _⟩ := mem_northSteps_iff.1 hp
  have hd := hw.2.2.2 p.1 h1.le
  have hmul : a * ht w p.1 ≤ a * p.2 := Nat.mul_le_mul_left a h2
  have : b * p.1 ≤ a * p.2 := hd.trans hmul
  simp only [diagExcess]
  omega

/-- **On and below the diagonal the extension adds nothing.** A tail's north steps all have
nonnegative excess, so the window `[d - a, d)` is empty of them once `d ≤ 0`. In particular the
`N + 1` diagonal points of `HJO.Mellit.diagPoints`, which a separating level has already passed,
carry no correction. -/
theorem tailLiveSteps_eq_empty_of_nonpos {A : ℕ} {w : Heights a b A} (hw : IsAboveDiagonal w)
    {d : ℤ} (hd : d ≤ 0) : tailLiveSteps w d = ∅ := by
  refine Finset.filter_eq_empty_iff.2 fun {p} hp => ?_
  have := le_diagExcess_of_mem_northSteps hw hp
  omega

/-- **Far above the diagonal the extension adds nothing either.** A tail's north step has excess at
most `a(bA - 1)`, so the window `[d - a, d)` is empty of them once `d > a·bA`. The correction is
therefore supported on the band `0 < d ≤ a·bA` of diagonal excess. -/
theorem tailLiveSteps_eq_empty_of_gt {A : ℕ} {w : Heights a b A} {d : ℤ}
    (hd : (a : ℤ) * (b * A) < d) : tailLiveSteps w d = ∅ := by
  refine Finset.filter_eq_empty_iff.2 fun {p} hp => ?_
  obtain ⟨_, _, h3⟩ := mem_northSteps_iff.1 hp
  have hb : p.2 + 1 ≤ b * A := h3.trans_le (ht_le_mul w _)
  have hcast : ((p.2 : ℤ) + 1) ≤ (b * A : ℕ) := by exact_mod_cast hb
  have ha : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg _
  have hbp : (0 : ℤ) ≤ (b : ℤ) * p.1 := by positivity
  simp only [diagExcess]
  push_cast at hcast ⊢
  intro hcon
  nlinarith [hcon.1, hbp]

/-- **The width correction of an extension, in closed form.** The live north steps of
`HJO.Paths.appendHeights z w` at columns `≥ aN` are exactly the corner-translates of the tail's
north steps whose own diagonal excess lies in the window `[rk P - a, rk P)`.

Read off the statement: **the correction does not mention the base path `z` at all.** It is a
function of the tail `w` and of the single integer `HJO.Paths.diagExcess a b P`. -/
theorem liveSteps_high_appendHeights {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) {P : ℕ × ℕ}
    (hP : P.1 < a * N) :
    {u ∈ liveSteps (appendHeights z w) P | a * N ≤ u.1}
      = (tailLiveSteps w (diagExcess a b P)).image fun p => (a * N + p.1, b * N + p.2) := by
  have hNA : a * (N + A) = a * N + a * A := Nat.mul_add a N A
  have hMpos : 0 < N + A := by omega
  have hPM : P.1 ≤ a * (N + A) := by omega
  ext u
  simp only [Finset.mem_filter, Finset.mem_image, tailLiveSteps, Prod.exists]
  constructor
  · rintro ⟨hlive, hhigh⟩
    have hun : u ∈ northSteps (appendHeights z w) := liveSteps_subset _ _ hlive
    rw [northSteps_appendHeights hz hw, Finset.mem_union, Finset.mem_image] at hun
    obtain ⟨p, hp, hpu⟩ : ∃ p ∈ northSteps w, (a * N + p.1, b * N + p.2) = u := by
      rcases hun with h | h
      · exact absurd (mem_northSteps_iff.1 h).1 (by omega)
      · simpa using h
    subst hpu
    have hwin := (mem_liveSteps_iff_of_lt_fst hMpos
      (northSteps_appendHeights hz hw ▸ Finset.mem_union_right _
        (Finset.mem_image.2 ⟨p, hp, rfl⟩)) hPM (by simp; omega)).1 hlive
    rw [diagExcess_corner_add] at hwin
    exact ⟨p.1, p.2, ⟨hp, hwin⟩, rfl⟩
  · rintro ⟨s, i, ⟨hp, hwin⟩, rfl⟩
    have hun : (a * N + s, b * N + i) ∈ northSteps (appendHeights z w) := by
      rw [northSteps_appendHeights hz hw]
      exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨(s, i), hp, rfl⟩)
    refine ⟨(mem_liveSteps_iff_of_lt_fst hMpos hun hPM (by simp; omega)).2 ?_, by simp⟩
    rw [show ((a * N + s, b * N + i) : ℕ × ℕ) = (a * N + (s, i).1, b * N + (s, i).2) from rfl,
      diagExcess_corner_add]
    exact hwin

/-- **The width correction of an extension, as a number.** -/
theorem card_liveSteps_high_appendHeights {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) {P : ℕ × ℕ}
    (hP : P.1 < a * N) :
    #{u ∈ liveSteps (appendHeights z w) P | a * N ≤ u.1}
      = #(tailLiveSteps w (diagExcess a b P)) := by
  rw [liveSteps_high_appendHeights hz hw hN hP,
    Finset.card_image_of_injective _ (fun p q h => ?_)]
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (by omega) (by omega)

/-- **`HJO.Paths.sweepWidth` at the extension, in closed form.** -/
theorem sweepWidth_appendHeights_eq {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) {P : ℕ × ℕ}
    (hP : P.1 < a * N) :
    sweepWidth (appendHeights z w) P
      = sweepWidth z P + #(tailLiveSteps w (diagExcess a b P)) := by
  rw [sweepWidth_appendHeights hz hw hN hP.le, card_liveSteps_high_appendHeights hz hw hN hP]

/-- **`HJO.Paths.sweepRight` at the extension, in closed form.** -/
theorem sweepRight_appendHeights_eq {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) {P : ℕ × ℕ}
    (hP : P.1 < a * N) :
    sweepRight (appendHeights z w) P
      = sweepRight z P + #(tailLiveSteps w (diagExcess a b P)) := by
  rw [sweepRight_appendHeights hz hw hN hP, card_liveSteps_high_appendHeights hz hw hN hP]

/-- **The width correction is independent of the base path.** Two above-diagonal `(aN, bN)`-paths
extended by the same tail take the same correction at the same point — this is
`HJO.Paths.card_liveSteps_high_appendHeights` read as a congruence, and it is the fact a factor
standing outside the sum over base paths would need. -/
theorem card_liveSteps_high_appendHeights_congr {z z' : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hz' : IsAboveDiagonal z') (hw : IsAboveDiagonal w) (hN : 0 < N)
    {P : ℕ × ℕ} (hP : P.1 < a * N) :
    #{u ∈ liveSteps (appendHeights z w) P | a * N ≤ u.1}
      = #{u ∈ liveSteps (appendHeights z' w) P | a * N ≤ u.1} := by
  rw [card_liveSteps_high_appendHeights hz hw hN hP,
    card_liveSteps_high_appendHeights hz' hw hN hP]

/-! ### The correction is *not* constant across the fibre

The correction is independent of the base path, but it is a genuine function of the tail, and the
fibre of the truncation over a base path is the whole set of tails. A witness at `(a, b) = (1, 2)`,
`N = 1`, `A = 2`: the fibre has exactly two elements, and at one and the same point of the base's
swept region they give different corrections. So no single operator factor standing *outside* the
inner sum of `HJO.Mellit.sum_aboveReturnPaths_append_singleton` can absorb the shift; the sum over
tails has to do the work, which is what the power `(Z^{(k+1)}_{a,b})^{A-1}` in
`HJO.Mellit.stageTotal` is for. -/

/-- The base path of return composition `(1)` in the `1 × 2` rectangle, heights `(0, 2)`. -/
def baseEx : Heights 1 2 1 := fun r => if (r : ℕ) = 0 then 0 else 2

/-- One of the two tails of return composition `(2)` in the `2 × 4` rectangle, heights `(0, 3, 4)`.
Its north steps have diagonal excesses `0, 1, 2` in column `0` and `1` in column `1`. -/
def tailEx1 : Heights 1 2 2 := fun r => if (r : ℕ) = 0 then 0 else if (r : ℕ) = 1 then 3 else 4

/-- The other tail of return composition `(2)` in that rectangle, heights `(0, 4, 4)`. Its north
steps have diagonal excesses `0, 1, 2, 3`, all in column `0`. -/
def tailEx2 : Heights 1 2 2 := fun r => if (r : ℕ) = 0 then 0 else 4

theorem hasAboveReturns_baseEx : HasAboveReturns [1] baseEx := by
  refine ⟨by decide, by decide, by decide, fun k hk => ?_⟩
  rw [show ([1] : List ℕ).scanl (· + ·) 0 = [0, 1] from by simp [List.scanl_cons, List.scanl_nil]]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  interval_cases k <;> decide

theorem hasAboveReturns_tailEx1 : HasAboveReturns [2] tailEx1 := by
  refine ⟨by decide, by decide, by decide, fun k hk => ?_⟩
  rw [show ([2] : List ℕ).scanl (· + ·) 0 = [0, 2] from by simp [List.scanl_cons, List.scanl_nil]]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  interval_cases k <;> decide

theorem hasAboveReturns_tailEx2 : HasAboveReturns [2] tailEx2 := by
  refine ⟨by decide, by decide, by decide, fun k hk => ?_⟩
  rw [show ([2] : List ℕ).scanl (· + ·) 0 = [0, 2] from by simp [List.scanl_cons, List.scanl_nil]]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  interval_cases k <;> decide

/-- The witness point is in the base's swept region. -/
theorem mem_sweptRegion_baseEx : ((0, 2) : ℕ × ℕ) ∈ sweptRegion baseEx := by decide

/-- …and strictly above the diagonal, so a separating level selects it: it really is one of the
points whose event operator `HJO.Mellit.partialSweepWord` multiplies in. -/
theorem diagExcess_pos_baseEx : 0 < diagExcess 1 2 ((0, 2) : ℕ × ℕ) := by decide

/-- **The two tails over one base path give different width corrections at one and the same point.**
Decisive for the shape of any proof of `HJO.Mellit.SweepAppend`: the shift `δ` varies over the inner
index set of `HJO.Mellit.sum_aboveReturnPaths_append_singleton`, so it cannot be absorbed by a
factor pulled out of that sum. Here the base's width at `(0,2)` is corrected by `2` through
`tailEx1` and by `1` through `tailEx2`. -/
theorem card_liveSteps_high_appendHeights_ne :
    #{u ∈ liveSteps (appendHeights baseEx tailEx1) ((0, 2) : ℕ × ℕ) | 1 * 1 ≤ u.1}
      ≠ #{u ∈ liveSteps (appendHeights baseEx tailEx2) ((0, 2) : ℕ × ℕ) | 1 * 1 ≤ u.1} := by
  rw [card_liveSteps_high_appendHeights hasAboveReturns_baseEx.1 hasAboveReturns_tailEx1.1
      (by norm_num) (by norm_num),
    card_liveSteps_high_appendHeights hasAboveReturns_baseEx.1 hasAboveReturns_tailEx2.1
      (by norm_num) (by norm_num)]
  decide

end HJO.Paths

namespace HJO.Mellit

open Paths

variable {a b N A : ℕ}

/-! ### The truncation on the index sets of `HJO.Mellit.sweepAppend_iff_sum` -/

/-- Membership in `HJO.Mellit.aboveReturnPaths` is the return condition, the above-diagonal clause
being part of it. -/
theorem mem_aboveReturnPaths_iff {α : List ℕ} {y : Heights a b N} :
    y ∈ aboveReturnPaths a b N α ↔ HasAboveReturns α y := by
  rw [aboveReturnPaths, Finset.mem_filter]
  exact ⟨fun h => h.2.2, fun h => ⟨Finset.mem_univ _, h.1, h⟩⟩

/-- The truncation maps the big index set to the small one. -/
theorem truncHeights_mem_aboveReturnPaths {α : List ℕ} {y : Heights a b (N + A)}
    (hy : y ∈ aboveReturnPaths a b (N + A) (α ++ [A])) :
    truncHeights y ∈ aboveReturnPaths a b N α :=
  mem_aboveReturnPaths_iff.2 (hasAboveReturns_truncHeights (mem_aboveReturnPaths_iff.1 hy))

/-- The tail maps the big index set to the index set of the one-part composition. -/
theorem tailHeights_mem_aboveReturnPaths {α : List ℕ} {y : Heights a b (N + A)}
    (hy : y ∈ aboveReturnPaths a b (N + A) (α ++ [A])) :
    tailHeights y ∈ aboveReturnPaths a b A [A] :=
  mem_aboveReturnPaths_iff.2 (hasAboveReturns_tailHeights (mem_aboveReturnPaths_iff.1 hy))

/-- Laying on maps the pair of index sets back into the big one. -/
theorem appendHeights_mem_aboveReturnPaths {α : List ℕ} {z : Heights a b N} {w : Heights a b A}
    (hz : z ∈ aboveReturnPaths a b N α) (hw : w ∈ aboveReturnPaths a b A [A]) :
    appendHeights z w ∈ aboveReturnPaths a b (N + A) (α ++ [A]) :=
  mem_aboveReturnPaths_iff.2
    (hasAboveReturns_appendHeights (mem_aboveReturnPaths_iff.1 hz) (mem_aboveReturnPaths_iff.1 hw))

/-- **The fibres of the truncation, as a reindexing of any sum over the big index set.** A sum over
the above-diagonal `(a(N+A), b(N+A))`-paths of return composition `α ++ (A)` is the double sum over
a path of return composition `α` and a path of return composition `(A)` laid on its corner — the
inner index set being *the same* whatever the outer index is. That independence is the description
of the fibres, and it is what the comparison of the two sums of `HJO.Mellit.sweepAppend_iff_sum`
needs of the index sets.

No hypothesis: `0 < A` and `α.sum = N` both come out of membership, and where they fail both sides
are empty sums. -/
theorem sum_aboveReturnPaths_append_singleton {M : Type*} [AddCommMonoid M] {α : List ℕ}
    (f : Heights a b (N + A) → M) :
    ∑ y ∈ aboveReturnPaths a b (N + A) (α ++ [A]), f y
      = ∑ z ∈ aboveReturnPaths a b N α,
          ∑ w ∈ aboveReturnPaths a b A [A], f (appendHeights z w) := by
  have hinv : ∀ y ∈ aboveReturnPaths a b (N + A) (α ++ [A]),
      appendHeights (truncHeights y) (tailHeights y) = y := by
    intro y hy
    have h := mem_aboveReturnPaths_iff.1 hy
    exact appendHeights_truncHeights_tailHeights h.1
      (ht_eq_of_hasAboveReturns_append h (sum_eq_of_hasAboveReturns_append h))
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun y => (truncHeights y, tailHeights y))
    (fun p => appendHeights p.1 p.2) (fun y hy => ?_) (fun p hp => ?_) (fun y hy => hinv y hy)
    (fun p hp => ?_) (fun y hy => by rw [hinv y hy])
  · exact Finset.mem_product.2
      ⟨truncHeights_mem_aboveReturnPaths hy, tailHeights_mem_aboveReturnPaths hy⟩
  · obtain ⟨hz, hw⟩ := Finset.mem_product.1 hp
    exact appendHeights_mem_aboveReturnPaths hz hw
  · obtain ⟨hz, hw⟩ := Finset.mem_product.1 hp
    exact Prod.ext (truncHeights_appendHeights _ _)
      (tailHeights_appendHeights (mem_aboveReturnPaths_iff.1 hw).1.1)

/-! ### `HJO.Mellit.SweepAppend` as one identity per base path -/

section Split

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

open HJO.Sweep

/-- **`HJO.Mellit.SweepAppend` with the two sums indexed by the *same* set.** The left sum of
`HJO.Mellit.sweepAppend_iff_sum` is reindexed by `HJO.Mellit.sum_aboveReturnPaths_append_singleton`,
so both sides are now sums over the above-diagonal `(aN, bN)`-paths of return composition `α`, the
left one having an inner sum over the tails. -/
theorem sweepAppend_iff_sum_split {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    SweepAppend q u a b ↔ ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
      ∑ z ∈ aboveReturnPaths a b α.sum α,
          ∑ w ∈ aboveReturnPaths a b A [A],
            partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
        = ∑ z ∈ aboveReturnPaths a b α.sum α,
            ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L)) := by
  rw [sweepAppend_iff_sum hab ha hb]
  constructor
  · intro h α A hpos hA
    rw [← sum_aboveReturnPaths_append_singleton (N := α.sum) (A := A) (α := α)
      (f := fun y => partialSweepWord q u y (sepLevel a (α.sum + A)) (1 : Total L))]
    exact h α A hpos hA
  · intro h α A hpos hA
    rw [sum_aboveReturnPaths_append_singleton (N := α.sum) (A := A) (α := α)
      (f := fun y => partialSweepWord q u y (sepLevel a (α.sum + A)) (1 : Total L))]
    exact h α A hpos hA

/-- **One identity per base path suffices for `HJO.Mellit.SweepAppend`.** Fix an above-diagonal
`(aN, bN)`-path `z` of return composition `α`. The claim is that the sum, over the above-diagonal
`(aA, bA)`-paths `w` of return composition `(A)`, of the partial sweep word of `z` extended by `w`
is the stage `G_{ℓ+1,A}` applied to the partial sweep word of `z`, up to the scalar of
`HJO.Mellit.braidRep_specialBraid_dplusIter`.

This is the sharpest reduction of `HJO.Mellit.SweepAppend` available without a comparison of the
event operators: the two sides no longer live over different index sets, and the remaining content
is one identity about **one** base path at a time. What it still needs is the relation between the
sweep of `z` and the sweep of `z` extended — and by `HJO.Paths.northSteps_appendHeights` those two
sweeps do not share their event operators, so the identity is not a subword identity and the
`HJO.Braid.trainDown`/`HJO.Braid.trainUp`/`HJO.Mellit.replicatedLetter` factors of
`HJO.Mellit.stageTotal` are what has to absorb the difference. -/
theorem sweepAppend_of_forall_path {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
      ∀ z ∈ aboveReturnPaths a b α.sum α,
        ∑ w ∈ aboveReturnPaths a b A [A],
            partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
          = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L))) :
    SweepAppend q u a b :=
  (sweepAppend_iff_sum_split hab ha hb).2 fun α A hpos hA =>
    Finset.sum_congr rfl (h α A hpos hA)

/-! ### What the extension does to the sweep word, term by term -/

/-- **At a separating level the index set of the base's partial sweep word is exactly the
low-column part of the extension's.** `HJO.Mellit.sweptAbove_eq_filter` makes both index sets
level-free, `HJO.Paths.sweptRegion_filter_lt_appendHeights` identifies them below the corner column,
and the corner column itself contributes nothing on the base side: there `ŷ⁺_{aN} = bN`, so a point
of `sweptRegion z` at `x = aN` is on the diagonal and a separating level does not select it. -/
theorem sweptAbove_filter_lt_appendHeights {a b N A : ℕ} {z : Heights a b N} {w : Heights a b A}
    {η η' : ℚ} (hη : SeparatesDiagonal a b (N + A) η) (hη' : SeparatesDiagonal a b N η') :
    {P ∈ sweptAbove (appendHeights z w) η | P.1 < a * N} = sweptAbove z η' := by
  have hreg := sweptRegion_filter_lt_appendHeights (z := z) (w := w)
  rw [Finset.ext_iff] at hreg
  rw [sweptAbove_eq_filter hη, sweptAbove_eq_filter hη']
  ext P
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨(Finset.mem_filter.1 ((hreg P).1 (Finset.mem_filter.2 ⟨h1, h3⟩))).1, h2⟩
  · rintro ⟨h1, h2⟩
    have hlt : P.1 < a * N := by
      rcases Nat.lt_or_ge P.1 (a * N) with h | h
      · exact h
      · exfalso
        have hle : P.1 ≤ a * N := (Paths.mem_sweptRegion.1 h1).1
        have hEq : P.1 = a * N := by omega
        have hz2 : P.2 ≤ ht z (P.1 + 1) := (Paths.mem_sweptRegion.1 h1).2.2
        rw [hEq, ht_of_gt z (by omega)] at hz2
        have hmul : a * P.2 ≤ a * (b * N) := Nat.mul_le_mul_left a hz2
        have hbn : b * (a * N) = a * (b * N) := by ring
        rw [hEq] at h2
        omega
    exact ⟨⟨(Finset.mem_filter.1 ((hreg P).2 (Finset.mem_filter.2 ⟨h1, hlt⟩))).1, h2⟩, hlt⟩

/-- Rule `D` of `HJO.Mellit.sweepOperator` written out, the shape the extension changes by a power
of `q`. -/
theorem sweepOperator_of_eventType_D {a b N : ℕ} (y : Heights a b N) {P : ℕ × ℕ}
    (hP : eventType y P = EventType.D) :
    sweepOperator q u y P = q ^ sweepRight y P • (1 : Module.End L (Total L)) := by
  rw [sweepOperator, hP]

/-- **A type-`E` event below the corner column survives the extension untouched.** Rule `E` is
`u · id`, which reads neither `HJO.Paths.sweepWidth` nor `HJO.Paths.sweepRight`, and by
`HJO.Paths.eventType_appendHeights` the type itself is unchanged. -/
theorem sweepOperator_appendHeights_of_eventType_E {a b N A : ℕ} {z : Heights a b N}
    {w : Heights a b A} {P : ℕ × ℕ} (hP : P.1 + 1 ≤ a * N) (hE : eventType z P = EventType.E) :
    sweepOperator q u (appendHeights z w) P = sweepOperator q u z P := by
  rw [sweepOperator_of_eventType_E q u _ P (by rw [eventType_appendHeights hP]; exact hE),
    sweepOperator_of_eventType_E q u z P hE]

/-- **A type-`D` event strictly inside the strip picks up exactly `q` to the number of extra live
north steps.** The only event type at which the difference between the two sweeps is a scalar: rules
`A`, `B` and `C` read `HJO.Paths.sweepWidth`, and `HJO.Paths.sweepWidth_appendHeights` shifts it, so
`d_+`, `d_-` and `Δ` are read at a *different index* and no scalar relates them. -/
theorem sweepOperator_appendHeights_of_eventType_D {a b N A : ℕ} {z : Heights a b N}
    {w : Heights a b A} (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N)
    {P : ℕ × ℕ} (hP : P.1 < a * N) (hD : eventType z P = EventType.D) :
    sweepOperator q u (appendHeights z w) P
      = q ^ #{v ∈ liveSteps (appendHeights z w) P | a * N ≤ v.1} • sweepOperator q u z P := by
  rw [sweepOperator_of_eventType_D _ (by rw [eventType_appendHeights (by omega)]; exact hD),
    sweepOperator_of_eventType_D z hD, sweepRight_appendHeights hz hw hN hP, pow_add, smul_smul,
    mul_comm]

/-! ### The extension's event operator in closed form, and where it is unchanged -/

/-- Rule `A` of `HJO.Mellit.sweepOperator` written out. -/
theorem sweepOperator_of_eventType_A {a b N : ℕ} (y : Heights a b N) {P : ℕ × ℕ}
    (hP : eventType y P = EventType.A) :
    sweepOperator q u y P = dplus q (sweepWidth y P) := by
  rw [sweepOperator, hP]

/-- Rule `B` of `HJO.Mellit.sweepOperator` written out. -/
theorem sweepOperator_of_eventType_B {a b N : ℕ} (y : Heights a b N) {P : ℕ × ℕ}
    (hP : eventType y P = EventType.B) :
    sweepOperator q u y P = dminus q (sweepWidth y P) := by
  rw [sweepOperator, hP]

/-- Rule `C` of `HJO.Mellit.sweepOperator` written out. -/
theorem sweepOperator_of_eventType_C {a b N : ℕ} (y : Heights a b N) {P : ℕ × ℕ}
    (hP : eventType y P = EventType.C) :
    sweepOperator q u y P = q ^ (-(sweepRight y P : ℤ)) • corner q (sweepWidth y P) := by
  rw [sweepOperator, hP]

/-- **Outside the band `0 < rk P ≤ a·bA` of diagonal excess the extension changes nothing.** By
`HJO.Paths.tailLiveSteps_eq_empty_of_nonpos` and `HJO.Paths.tailLiveSteps_eq_empty_of_gt` the width
correction vanishes there, and by `HJO.Paths.eventType_appendHeights` the event type never changed.
So the whole discrepancy between the two sweeps is confined to `1 ≤ rk P ≤ a·bA` — a band whose
width depends on the appended part `A` and not on the base path. -/
theorem sweepOperator_appendHeights_of_diagExcess_outside {a b N A : ℕ} {z : Heights a b N}
    {w : Heights a b A} (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) {P : ℕ × ℕ}
    (hP : P.1 + 1 ≤ a * N)
    (hd : diagExcess a b P ≤ 0 ∨ (a : ℤ) * (b * A) < diagExcess a b P) :
    sweepOperator q u (appendHeights z w) P = sweepOperator q u z P := by
  have hδ : #(tailLiveSteps w (diagExcess a b P)) = 0 := by
    rcases hd with h | h
    · rw [tailLiveSteps_eq_empty_of_nonpos hw h, Finset.card_empty]
    · rw [tailLiveSteps_eq_empty_of_gt h, Finset.card_empty]
  have hE : eventType (appendHeights z w) P = eventType z P := eventType_appendHeights hP
  have hW : sweepWidth (appendHeights z w) P = sweepWidth z P := by
    rw [sweepWidth_appendHeights_eq hz hw hN (by omega), hδ, Nat.add_zero]
  have hR : sweepRight (appendHeights z w) P = sweepRight z P := by
    rw [sweepRight_appendHeights_eq hz hw hN (by omega), hδ, Nat.add_zero]
  simp only [sweepOperator, hE, hW, hR]

/-- **Rule `A` at the extension, in closed form: `d_+` read `δ` higher.** This is the whole residual
obligation at a type-`A` event — nothing relates `d_+` at index `k` to `d_+` at index `k + δ` by a
scalar, since `HJO.Sweep.dplus` carries the index both in the ascending train `T_{1↗k+1}` and in the
variable `y_{k+1}`. -/
theorem sweepOperator_appendHeights_of_eventType_A {a b N A : ℕ} {z : Heights a b N}
    {w : Heights a b A} (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N)
    {P : ℕ × ℕ} (hP : P.1 < a * N) (hA : eventType z P = EventType.A) :
    sweepOperator q u (appendHeights z w) P
      = dplus q (sweepWidth z P + #(tailLiveSteps w (diagExcess a b P))) := by
  rw [sweepOperator_of_eventType_A _ (by rw [eventType_appendHeights (by omega)]; exact hA),
    sweepWidth_appendHeights_eq hz hw hN hP]

/-- **Rule `B` at the extension, in closed form: `d_-` read `δ` higher.** -/
theorem sweepOperator_appendHeights_of_eventType_B {a b N A : ℕ} {z : Heights a b N}
    {w : Heights a b A} (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N)
    {P : ℕ × ℕ} (hP : P.1 < a * N) (hB : eventType z P = EventType.B) :
    sweepOperator q u (appendHeights z w) P
      = dminus q (sweepWidth z P + #(tailLiveSteps w (diagExcess a b P))) := by
  rw [sweepOperator_of_eventType_B _ (by rw [eventType_appendHeights (by omega)]; exact hB),
    sweepWidth_appendHeights_eq hz hw hN hP]

/-- **Rule `C` at the extension, in closed form: `Δ` read `δ` higher, and `q` to the shifted right
count.** -/
theorem sweepOperator_appendHeights_of_eventType_C {a b N A : ℕ} {z : Heights a b N}
    {w : Heights a b A} (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N)
    {P : ℕ × ℕ} (hP : P.1 < a * N) (hC : eventType z P = EventType.C) :
    sweepOperator q u (appendHeights z w) P
      = q ^ (-((sweepRight z P + #(tailLiveSteps w (diagExcess a b P)) : ℕ) : ℤ)) •
          corner q (sweepWidth z P + #(tailLiveSteps w (diagExcess a b P))) := by
  rw [sweepOperator_of_eventType_C _ (by rw [eventType_appendHeights (by omega)]; exact hC),
    sweepWidth_appendHeights_eq hz hw hN hP, sweepRight_appendHeights_eq hz hw hN hP]

end Split

end HJO.Mellit

end
