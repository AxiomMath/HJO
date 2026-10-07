/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepRankOrder
public meta import HJO.Attr

/-! # What the sweep reads at a point: the live steps in a column, and the word position

Four statements of the sweep about a single point of the swept region, all of them consequences of
one arithmetic fact: along a column the above-diagonal rank goes up by exactly the attack window `ω`
per unit step (`HJO.Paths.abovePointRank_add`). Two are about which north steps of a column can be
live at a point, and two compute the word position `pos_{P̂}` at the two places the sweep word needs
it — at the top of the sweep and at the foot of a north step.

## Main results

* `HJO.Paths.abovePointRank_add`: `rk̂(x, k + d) = rk̂(x, k) + d ω`, the iterated form of
  `HJO.Paths.abovePointRank_succ`.
* `HJO.Paths.eq_of_mem_liveSteps_of_fst_eq`: at most one live north step in each column
  (`HJO.Paths.eq_of_mem_liveSteps_of_fst_eq`).
* `HJO.Paths.mem_liveSteps_iff_eq_of_fst_eq`: in the column of the point itself, the only live north
  step is the point (`HJO.Paths.mem_liveSteps_iff_eq_of_fst_eq`).
* `HJO.Paths.wordPosition_of_isMax`: the word position at the first point of the sweep is `2bN`
  (`HJO.Paths.wordPosition_of_isMax`).
* `HJO.Paths.wordPosition_stepFoot`: the word position at a north step is `x'_j + j - 1`
  (`HJO.Paths.wordPosition_stepFoot`).

## Implementation notes

The column lemmas are stated with the hypothesis `u ∈ northSteps y` and nothing else — not
above-diagonality, and not `P ∈ Sw(P̂)`. Neither `liveSteps` nor the rank reads either, and the
positivity of `ω` that both proofs need comes from the north step, whose abscissa is below `aN`.
This is the same economy as `HJO.Paths.mem_liveSteps_iff_levelCrosses`.

`wordPosition_of_isMax` takes the maximality as `∀ Q ∈ sweptRegion y, rk̂(Q) ≤ rk̂(P)`,
rather than as "`P` is the first element of the rank-order listing": the
listing is not needed, and the two ends of every north step being swept
(`HJO.Paths.mem_sweptRegion_of_mem_northSteps`) is what makes both counts of `pos_{P̂}` total.

`wordPosition_stepFoot` is where the relabelling of `HJO/Shuffle/SweepRankOrder.lean` is spent.
The formula is `pos_{P̂}(u_j) = x'_j + j - 1` with `j` the `1`-based position and `x'_j` the
`1`-based partner entry; on the `0`-based `p = stepIndex y i` that is
`pos = p + 1 + attackPartner (attackPositions y) p`, and the two `- 1`s of the formula cancel
against each other rather than being subtracted in `ℕ`. Nothing here truncates.

## References

The lemmas `HJO.Paths.eq_of_mem_liveSteps_of_fst_eq`, `HJO.Paths.mem_liveSteps_iff_eq_of_fst_eq`,
`HJO.Paths.wordPosition_of_isMax` and `HJO.Paths.wordPosition_stepFoot`, using
`HJO.Paths.liveSteps`, `HJO.Paths.wordPosition`, `HJO.Paths.sweepAttack` and
`HJO.Dyck.attackPartner`. Transcribing A. Mellit,
*Toric braids and `(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-- **The rank goes up by one window per unit step along a column**:
`rk̂(x, k + d) = rk̂(x, k) + dω`. The iterated form of `HJO.Paths.abovePointRank_succ`, and the one
arithmetic fact every statement in this file rests on. -/
theorem abovePointRank_add (a b N x k d : ℕ) :
    ParkingFunctions.abovePointRank a b N x (k + d) =
      ParkingFunctions.abovePointRank a b N x k + d * attackWindow a N := by
  simp only [ParkingFunctions.abovePointRank, cast_attackWindow]
  push_cast
  ring

/-! ### The live north steps in a column -/

/-- **At most one live north step in each column.** Two north steps of the same column that are both
live at `P` coincide: their ranks differ by a multiple of the window, and the half-open window
`rk̂(u) ≤ rk̂(P) < rk̂(u) + ω` admits only one of them.

Neither above-diagonality nor `P ∈ Sw(P̂)` is used; the positivity of `ω` comes from `u` being a
north step. -/
@[hjo "lem_swb_column_unique"]
theorem eq_of_mem_liveSteps_of_fst_eq {y : Heights a b N} {P u u' : ℕ × ℕ}
    (hu : u ∈ liveSteps y P) (hu' : u' ∈ liveSteps y P) (hcol : u.1 = u'.1) : u = u' := by
  have hun : u ∈ northSteps y := liveSteps_subset y P hu
  have h0 : 0 < a * N := lt_of_le_of_lt (Nat.zero_le _) (mem_northSteps_iff.1 hun).1
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 h0
  have hωz : (0 : ℤ) < attackWindow a N := by exact_mod_cast hω
  simp only [liveSteps, mem_filter] at hu hu'
  -- the key step, applied to whichever of the two heights is the smaller
  have key : ∀ v v' : ℕ × ℕ, v.1 = v'.1 → v.2 ≤ v'.2 →
      ParkingFunctions.abovePointRank a b N v'.1 v'.2 ≤
        ParkingFunctions.abovePointRank a b N P.1 P.2 →
      ParkingFunctions.abovePointRank a b N P.1 P.2 <
        ParkingFunctions.abovePointRank a b N v.1 v.2 + attackWindow a N → v.2 = v'.2 := by
    intro v v' hc hle h1 h2
    obtain ⟨d, hd⟩ : ∃ d, v'.2 = v.2 + d := ⟨v'.2 - v.2, by omega⟩
    have hr : ParkingFunctions.abovePointRank a b N v'.1 v'.2 =
        ParkingFunctions.abovePointRank a b N v.1 v.2 + d * attackWindow a N := by
      rw [hc.symm, hd, abovePointRank_add]
    rw [hr] at h1
    have hd0 : d = 0 := by
      by_contra hne
      have : (1 : ℤ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
      nlinarith
    omega
  rcases le_total u.2 u'.2 with hle | hle
  · exact Prod.ext hcol (key u u' hcol hle hu'.2.1 hu.2.2)
  · exact Prod.ext hcol (key u' u hcol.symm hle hu.2.1 hu'.2.2).symm

/-- **In the column of the point itself the only live north step is the point.** A north step whose
column is the abscissa of `P` is live at `P` exactly when its foot is `P`.

One direction is that `rk̂(P) < rk̂(P) + ω`; the other is the half-open window again, run in both
directions along the column. -/
@[hjo "lem_swb_own_column"]
theorem mem_liveSteps_iff_eq_of_fst_eq {y : Heights a b N} {P u : ℕ × ℕ}
    (hu : u ∈ northSteps y) (hcol : u.1 = P.1) : u ∈ liveSteps y P ↔ u = P := by
  have h0 : 0 < a * N := lt_of_le_of_lt (Nat.zero_le _) (mem_northSteps_iff.1 hu).1
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 h0
  have hωz : (0 : ℤ) < attackWindow a N := by exact_mod_cast hω
  simp only [liveSteps, mem_filter]
  constructor
  · rintro ⟨-, h1, h2⟩
    refine Prod.ext hcol ?_
    rcases le_total u.2 P.2 with hle | hle
    · obtain ⟨d, hd⟩ : ∃ d, P.2 = u.2 + d := ⟨P.2 - u.2, by omega⟩
      have hr : ParkingFunctions.abovePointRank a b N P.1 P.2 =
          ParkingFunctions.abovePointRank a b N u.1 u.2 + d * attackWindow a N := by
        rw [hcol.symm, hd, abovePointRank_add]
      rw [hr] at h2
      have hd0 : d = 0 := by
        by_contra hne
        have : (1 : ℤ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
        nlinarith
      omega
    · obtain ⟨d, hd⟩ : ∃ d, u.2 = P.2 + d := ⟨u.2 - P.2, by omega⟩
      have hr : ParkingFunctions.abovePointRank a b N u.1 u.2 =
          ParkingFunctions.abovePointRank a b N P.1 P.2 + d * attackWindow a N := by
        rw [hcol, hd, abovePointRank_add]
      rw [hr] at h1
      have hd0 : d = 0 := by
        by_contra hne
        have : (1 : ℤ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
        nlinarith
      omega
  · rintro rfl
    exact ⟨hu, le_rfl, by linarith⟩

/-! ### The word position at the first point of the sweep -/

/-- **The word position at the first point of the sweep is `2bN`.** At a point of maximal rank in
the swept region every north step has both its foot and its head outranked, so both counts of
`pos_{P̂}` are the whole of `northSteps`, of which there are `bN`.

The maximality is phrased as in the statement, a bound over the swept region; the rank-order
listing is not needed. What is needed is that both ends of a north step are swept, which is
`HJO.Paths.mem_sweptRegion_of_mem_northSteps`. -/
@[hjo "lem_sweep_position_top"]
theorem wordPosition_of_isMax {y : Heights a b N} (hy : IsAboveDiagonal y) {P : ℕ × ℕ}
    (hmax : ∀ Q ∈ sweptRegion y, ParkingFunctions.abovePointRank a b N Q.1 Q.2 ≤
      ParkingFunctions.abovePointRank a b N P.1 P.2) :
    wordPosition y P = 2 * (b * N) := by
  have h1 : {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
      ParkingFunctions.abovePointRank a b N P.1 P.2} = northSteps y :=
    filter_eq_self.2 fun u hu => hmax u (mem_sweptRegion_of_mem_northSteps hy hu).1
  have h2 : {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 +
      attackWindow a N ≤ ParkingFunctions.abovePointRank a b N P.1 P.2} = northSteps y := by
    refine filter_eq_self.2 fun u hu => ?_
    have := hmax (u.1, u.2 + 1) (mem_sweptRegion_of_mem_northSteps hy hu).2
    rwa [abovePointRank_succ a b N u.1 u.2] at this
  rw [wordPosition, h1, h2, card_northSteps hy, two_mul]

/-! ### The word position at the foot of a north step -/

/-- **A rank condition counted over the north steps is the same condition counted over the
heights.** The transport along `HJO.Paths.stepFoot`, which is a bijection onto `northSteps` for an
above-diagonal path. Both counts of `wordPosition` are of this shape. -/
theorem card_filter_northSteps {y : Heights a b N} (hy : IsAboveDiagonal y)
    (p : ℤ → Prop) [DecidablePred p] :
    #{u ∈ northSteps y | p (ParkingFunctions.abovePointRank a b N u.1 u.2)}
      = #(univ.filter fun t : Fin (b * N) => p (stepRank y t)) := by
  refine (card_nbij (stepFoot y) (fun t ht => ?_) (fun t _ t' _ h => stepFoot_injective y h)
    (fun u hu => ?_)).symm
  · exact mem_filter.2 ⟨(northSteps_eq_image hy) ▸ mem_image_of_mem _ (mem_univ t),
      (mem_filter.1 ht).2⟩
  · obtain ⟨hun, hQ⟩ := mem_filter.1 hu
    rw [northSteps_eq_image hy, mem_image] at hun
    obtain ⟨t, -, rfl⟩ := hun
    exact ⟨t, mem_filter.2 ⟨mem_univ t, hQ⟩, rfl⟩

/-- The number of north steps of strictly smaller rank than a given one is its `0`-based position in
the increasing-rank listing. The `≤` count is that plus one, which is `HJO.Braid.entryRank`; the
step itself is the one element between them, and the injectivity of the rank is what says there is
no other. -/
theorem card_filter_stepRank_lt {y : Heights a b N} (hy : IsAboveDiagonal y) (i : Fin (b * N)) :
    #(univ.filter fun t : Fin (b * N) => stepRank y t < stepRank y i) = (stepIndex y i : ℕ) := by
  have hnot : i ∉ univ.filter (fun t : Fin (b * N) => stepRank y t < stepRank y i) := by simp
  have hins : (univ.filter fun t : Fin (b * N) => stepRank y t ≤ stepRank y i)
      = insert i (univ.filter fun t : Fin (b * N) => stepRank y t < stepRank y i) := by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    refine ⟨fun h => (eq_or_lt_of_le h).imp (fun he => ?_) id,
      fun h => h.elim (fun he => he ▸ le_rfl) le_of_lt⟩
    exact stepRank_injective_of_isAboveDiagonal hy he
  have h1 : Braid.entryRank (stepRank y) i
      = #(univ.filter fun t : Fin (b * N) => stepRank y t < stepRank y i) + 1 :=
    (congrArg Finset.card hins).trans (card_insert_of_notMem hnot)
  have := stepIndex_val y i
  omega

/-- **The row of the attack set at a north step has `j - x'_j` cells.** Counted over the heights,
the north steps attacking `i` are as many as the cells of row `stepIndex y i` of the relabelled
attack set, and that row is the interval `{x'_j, …, j-1}` because the relabelled set is the attack
set of its own square partner (`HJO.Paths.isSquareDyck_partner`). -/
theorem card_filter_sweepAttack_snd {y : Heights a b N} (hy : IsAboveDiagonal y)
    (i : Fin (b * N)) :
    #(univ.filter fun t : Fin (b * N) => (t, i) ∈ sweepAttack y)
      = (stepIndex y i : ℕ) - Dyck.attackPartner (attackPositions y) (stepIndex y i) := by
  classical
  set x : Fin (b * N) → ℕ := fun p => Dyck.attackPartner (attackPositions y) (p : ℕ) with hx
  obtain ⟨-, hset⟩ := isSquareDyck_partner hy
  have hrow : #((attackPositions y).filter fun q => q.2 = (stepIndex y i : ℕ))
      = (stepIndex y i : ℕ) - x (stepIndex y i) := by
    rw [← hset, Dyck.attackSet_filter_snd x (stepIndex y i), card_product, card_singleton,
      Nat.card_Ico, mul_one]
  refine Eq.trans ?_ hrow
  refine card_nbij (fun t => ((stepIndex y t : ℕ), (stepIndex y i : ℕ))) (fun t ht => ?_)
    (fun t _ t' _ h => stepIndex_injective hy (Fin.val_injective (congrArg Prod.fst h)))
    (fun q hq => ?_)
  · exact mem_filter.2 ⟨(mem_attackPositions hy t i).2 (mem_filter.1 ht).2, rfl⟩
  · obtain ⟨hq1, hq2⟩ := mem_filter.1 hq
    obtain ⟨hm, hn, hmem⟩ := (mem_attackPositions_iff hy (m := q.1) (n := q.2)).1 hq1
    have hi : stepAt hy ⟨q.2, hn⟩ = i := by
      rw [show (⟨q.2, hn⟩ : Fin (b * N)) = stepIndex y i from Fin.val_injective hq2,
        stepAt_stepIndex]
    refine ⟨stepAt hy ⟨q.1, hm⟩, mem_filter.2 ⟨mem_univ _, by rw [← hi]; exact hmem⟩, ?_⟩
    exact Prod.ext (by simp only [stepIndex_stepAt]) hq2.symm

/-- **The word position at the foot of a north step is `x'_j + j - 1`.** With `j` the `1`-based
position of the step in the increasing-rank listing and `x'_j` the `1`-based entry of the square
partner, the formula reads `pos_{P̂}(u_j) = x'_j + j - 1`; on the `0`-based `p = stepIndex y i`
that is `p + 1 + attackPartner (attackPositions y) p`, the two `- 1`s cancelling, so
nothing is subtracted in `ℕ`.

The proof is in three counts. The first summand of `pos` counts the north steps of
rank at most `rk̂(u_j)`, which is `j`. In the second, a step of rank above `rk̂(u_j)` cannot
contribute because the window is positive, and among the steps of smaller rank the contributing ones
are exactly those *not* attacking `u_j` — that being the negation of the defining inequality of
`HJO.Paths.sweepAttack`. So the second summand is `j - 1` minus the size of row `j` of the attack
set, and that row is `{x'_j, …, j-1}` because the relabelled attack set is the attack set of its own
square partner. -/
@[hjo "lem_sweep_position_foot"]
theorem wordPosition_stepFoot {y : Heights a b N} (hy : IsAboveDiagonal y) (i : Fin (b * N)) :
    wordPosition y (stepFoot y i) =
      (stepIndex y i : ℕ) + 1 + Dyck.attackPartner (attackPositions y) (stepIndex y i) := by
  classical
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 (mul_pos_of_isAboveDiagonal hy i)
  have hωz : (0 : ℤ) < attackWindow a N := by exact_mod_cast hω
  -- the first count is `j = p + 1`
  have hc1 : #{u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
      stepRank y i} = (stepIndex y i : ℕ) + 1 := by
    rw [card_filter_northSteps hy fun r => r ≤ stepRank y i]
    exact (stepIndex_val y i).symm.trans rfl
  -- inside the steps of smaller rank, split by whether they attack `i`
  have hsplit : #(univ.filter fun t : Fin (b * N) => stepRank y t + attackWindow a N ≤
        stepRank y i) + #(univ.filter fun t : Fin (b * N) => (t, i) ∈ sweepAttack y)
      = (stepIndex y i : ℕ) := by
    rw [← card_filter_stepRank_lt hy i]
    have e1 : ((univ.filter fun t : Fin (b * N) => stepRank y t < stepRank y i).filter
          fun t => stepRank y t + attackWindow a N ≤ stepRank y i)
        = univ.filter fun t : Fin (b * N) => stepRank y t + attackWindow a N ≤ stepRank y i := by
      ext t; simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨by linarith, h⟩⟩
    have e2 : ((univ.filter fun t : Fin (b * N) => stepRank y t < stepRank y i).filter
          fun t => ¬(stepRank y t + attackWindow a N ≤ stepRank y i))
        = univ.filter fun t : Fin (b * N) => (t, i) ∈ sweepAttack y := by
      ext t
      simp only [mem_filter, mem_univ, true_and, sweepAttack, not_le]
    rw [← e1, ← e2]
    exact card_filter_add_card_filter_not _
  -- the second count is what is left of `j - 1` after removing the attacking steps
  have hc2 : #{u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 +
      attackWindow a N ≤ stepRank y i}
      = Dyck.attackPartner (attackPositions y) (stepIndex y i) := by
    rw [card_filter_northSteps hy fun r => r + attackWindow a N ≤ stepRank y i]
    have hrow := card_filter_sweepAttack_snd hy i
    have hle : Dyck.attackPartner (attackPositions y) (stepIndex y i) ≤ (stepIndex y i : ℕ) :=
      Dyck.attackPartner_le _ _
    omega
  rw [wordPosition, stepRank_eq_abovePointRank_stepFoot y i] at *
  rw [hc1, hc2]

/-! ### Value check

On the worked example (`HJO.Paths.example_1_2_2`: `a = 1`, `b = 2`, `N = 2`, heights
`(0, 2, 4)`) the four word positions at the feet are `1, 4, 2, 6`, listed by the height of the foot.
Read through the relabelling `stepIndex = [0, 2, 1, 3]` and the partner `(0, 0, 1, 2)`, the formula
`p + 1 + x'_p` gives `1, 4, 2, 6` in the same order. Both `+ 1`s and the relabelling are therefore
pinned: dropping the `+ 1` would give `0, 3, 1, 5`, and using the height in place of the position
would give `1, 2, 4, 6` — a different answer at two of the four steps. -/
theorem wordPosition_stepFoot_example : ∀ i : Fin 4,
    wordPosition example_1_2_2 (stepFoot example_1_2_2 i) = ![1, 4, 2, 6] i := by decide

end HJO.Paths
