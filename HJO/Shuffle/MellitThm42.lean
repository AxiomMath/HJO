/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ColouringTrace
public import HJO.Shuffle.ColouringLevelIndex
public import HJO.Shuffle.ColouringWidth
public meta import HJO.Attr

/-! # Mellit's Theorem 4.2, rules A, C and D

Three of the four rules of Mellit's Theorem 4.2 relate the invariant `D_{η,c}` of a colouring below
a level to the invariant of a *single* colouring above it, multiplied by the operator of the event
the level crossed:

* rule `A`: `D_{ηlo, c_{ηlo}(P̂)} = d₊ D_{ηhi, c_{ηhi}(P̂)}`;
* rule `C`: `D_{ηlo, c_{ηlo}(P̂)} = q^{-a_{P̂}(P)} Δ D_{ηhi, c_{ηhi}(P̂)}`;
* rule `D`: `D_{ηlo, c_{ηlo}(P̂)} = q^{a_{P̂}(P)} D_{ηhi, c_{ηhi}(P̂)}`.

`HJO.Mellit.partialSweepWord_eq_sweepOperator_mul` already says that lowering the level past `P`
appends the single factor `Φ_{P̂}(P)` to the partial sweep word of *one* path. What the three rules
add is the grouping of the traces at `ηlo` with colouring `c₋` over the traces at `ηhi` with
colouring `c₊`, and that is the whole content of this file.

## The grouping, and why it is not a bijection of paths

Two facts about this step, both proved here, shape the proof.

**There is no bijection of paths.** The fibre `{Q̂ : c_{ηhi}(Q̂) = c₊}` is strictly *larger* than
`{Q̂ : c_{ηlo}(Q̂) = c₋}`: a path may be coloured `c₊` above the level and be nowhere near `(X, Y)`
below it. The correspondence proved here is between *traces*, `τ ↦ τ.erase ((X,Y), ev, a)`, and the
extra paths are dealt with by the splice `HJO.Mellit.raiseFrom`, which pushes a path up to the
ordinate `Y` from the abscissa `X + 1` rightwards. That splice changes a path only strictly under
the level line, so the swept points above the level, their event types and their live counts — the
whole trace above the level — are untouched, while the event at `(X, Y)` becomes the reference
path's.

**The event type is load-bearing.** The colouring below the level determines the event at `(X, Y)`
among the four types on the path, because the two points `(X, Y)` and `(X, Y-1)` are coloured there
exactly according to the incoming and the outgoing letter:

| event | `ŷ_X` vs `Y` | `ŷ_{X+1}` vs `Y` | `(X,Y) ∈ c₋` | `(X,Y-1) ∈ c₋` |
| ----- | ------------ | ---------------- | ------------ | -------------- |
| `A`   | `<`          | `=`              | yes          | yes            |
| `B`   | `=`          | `>`              | no           | no             |
| `C`   | `<`          | `>`              | no           | yes            |
| `D`   | `=`          | `=`              | yes          | no             |

A point *strictly below* the path — event type `E` — colours neither, exactly as type `B` does,
which is why `B` and `E` cannot be separated and rule BE has to carry two predecessors. Rules `A`,
`C` and `D` are the three rows the colouring below the level does pin down, and the hypothesis they
share is that the event is not of type `B` or `E`: `ht ŷ X < Y ∨ ht ŷ (X+1) = Y`.

## Main definitions

* `HJO.Mellit.Isolates`: the bracketing hypothesis the four rules share, bundled.
* `HJO.Mellit.raiseFrom`: the splice that carries the fibre of `c₊` into the fibre of `c₋`.

## Main results

* `HJO.Mellit.ht_le_levelIndex_iff`: the colouring decides which side of the level the path is on in
  every column. This is what rules out the configuration that would break rule `A`.
* `HJO.Mellit.dsc_lo_eq_sweepOperator_dsc_hi`: the shared content of the three rules.
* `HJO.Mellit.dsc_lo_eq_dplus_dsc_hi`, `HJO.Mellit.dsc_lo_eq_corner_dsc_hi`,
  `HJO.Mellit.dsc_lo_eq_qpow_dsc_hi`: rules `A`, `C` and `D`.

## Implementation notes

`0 < a`, `0 < b` and `0 < N` are carried as explicit hypotheses. `0 < a` and `0 < N`
are what `HJO.Mellit.partialSweepWord_eq_sweepOperator_mul` and
`HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq` already need, the rank being injective on the
swept region only for `0 < a`. `0 < b` is new here: the proof needs the rank to *drop* strictly
along an east step, which is `HJO.Mellit.pointRank_succ_fst_lt`, and at `b = 0` the rank rises along
one instead. At `b = 0` the rectangle has no row, every path is the constant `0`, and every
colouring is empty, so nothing of the geometry survives to be proved.

The isolation hypothesis is the one the library already uses — it quantifies over the lattice points
of the rectangle without asking them to be above the diagonal
(`ay ≥ bx`). That makes the hypothesis formally stronger, and it is the form
`HJO.Mellit.exists_isolating_isAdmissibleLevel` supplies at every lattice point of the rectangle, so
no generality is lost; `HJO.Mellit.sweptAbove_eq_insert_of_isolating` is stated the same way.

## References

A. Mellit, *Toric braids and
`(m, n)`-parking functions*, Theorem 4.2.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The rank and the level index, moved one step -/

/-- The rank does not rise rightwards: an east step lowers it by `(aN+1)Nb - 1 ≥ 0`. -/
theorem pointRank_le_of_fst_le (hb : 0 < b) (hN : 0 < N) {x x' : ℕ} (h : x ≤ x') (i : ℕ) :
    pointRank a b N (x', i) ≤ pointRank a b N (x, i) := by
  induction x', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (pointRank_succ_fst_le hb hN a n i).trans ih

/-- The rank rises upwards and does not rise rightwards, so it is monotone for the order that
decreases the abscissa and increases the ordinate. -/
theorem pointRank_le_of_fst_le_of_snd_le (hb : 0 < b) (hN : 0 < N) {x x' i i' : ℕ}
    (hx : x ≤ x') (hi : i' ≤ i) :
    pointRank a b N (x', i') ≤ pointRank a b N (x, i) :=
  (pointRank_mono_snd a b N x' hi).trans (pointRank_le_of_fst_le hb hN hx i)

/-- **On a rectangle with a row and a column an east step lowers the rank strictly.** The drop is
`(aN+1)Nb - 1`, which is positive as soon as `a`, `b` and `N` are: this is the inequality that makes
the point left of `(X, Y)` outrank it and the point right of it be outranked, and it is exactly
where `0 < b` is spent. -/
theorem pointRank_succ_fst_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (x h : ℕ) :
    pointRank a b N (x + 1, h) < pointRank a b N (x, h) := by
  have hpos : 2 ≤ (((a * N + 1) * N * b : ℕ) : ℤ) := by
    have h1 : 1 ≤ a * N := Nat.one_le_iff_ne_zero.2 (by positivity)
    have : 2 ≤ (a * N + 1) * N * b := by
      calc 2 = 2 * 1 * 1 := by ring
      _ ≤ (a * N + 1) * N * b := Nat.mul_le_mul (Nat.mul_le_mul (by omega) hN) hb
    exact_mod_cast this
  have := pointRank_sub_pointRank_fst a b N x h
  omega

/-- A point strictly to the left of another, at the same height, strictly outranks it. -/
theorem pointRank_lt_of_lt_fst (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {x x' : ℕ} (h : x < x')
    (i : ℕ) : pointRank a b N (x', i) < pointRank a b N (x, i) :=
  lt_of_le_of_lt (pointRank_le_of_fst_le hb hN h i) (pointRank_succ_fst_lt ha hb hN x i)

/-- **The level index does not decrease rightwards.** The level line has positive slope `b/a` up to
the tie-breaking term, so the ordinate at which it meets the vertical lattice line rises with the
abscissa. -/
theorem levelIndex_le_levelIndex_succ (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) (x : ℕ) :
    levelIndex a b N η x ≤ levelIndex a b N η (x + 1) := by
  have hK : (1 : ℚ) ≤ (((a * N + 1) * N * b : ℕ) : ℚ) := by
    have : 1 ≤ (a * N + 1) * N * b := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have hM : (0 : ℚ) < (((a * N + 1) * N * a : ℕ) : ℚ) := by
    have : 0 < (a * N + 1) * N * a := by positivity
    exact_mod_cast this
  have hK' : (1 : ℚ) ≤ ((a : ℚ) * N + 1) * N * b := by push_cast at hK; exact hK
  refine Int.floor_le_floor ?_
  rw [div_le_div_iff_of_pos_right hM]
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℚ) x]

/-- The level index is monotone in the abscissa. -/
theorem levelIndex_le_of_fst_le (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) {x x' : ℕ}
    (h : x ≤ x') : levelIndex a b N η x ≤ levelIndex a b N η x' := by
  induction x', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact ih.trans (levelIndex_le_levelIndex_succ ha hb hN η n)

/-- **The colouring, restricted to the level's upper side, is the set of crossed east steps.** The
companion of `HJO.Mellit.filter_colouring_lt`: the two halves of `HJO.Mellit.colouring` are
separated by the level, so each of them is cut out of the colouring by a rank comparison and is
therefore a function of the colouring alone. -/
theorem filter_colouring_not_lt (y : Heights a b N) (η : ℚ) :
    {p ∈ colouring y η | ¬ ((pointRank a b N p : ℚ) < η)} = colouringEast y η := by
  rw [colouring_eq_union, Finset.filter_union,
    Finset.filter_false_of_mem (fun x hx => by simpa using (Finset.mem_filter.1 hx).2.1),
    Finset.filter_true_of_mem (fun x hx => not_lt.2 (le_of_lt (Finset.mem_filter.1 hx).2.2)),
    Finset.empty_union]

/-- **Membership in a colouring, read off the level index.** `HJO.Mellit.colouring` says that
`(x, i)` is coloured exactly when it is a north step of the path whose ordinate *is* the level index
of its column, or the east step of its column with the level index of that column below it and the
level index of the next column at or above it. Every hypothesis of the rules below is checked
against this form. -/
theorem mem_colouring_iff_levelIndex (ha : 0 < a) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (y : Heights a b N) (x i : ℕ) :
    (x, i) ∈ colouring y η ↔
      (x < a * N ∧ ht y x ≤ i ∧ i < ht y (x + 1) ∧ (i : ℤ) = levelIndex a b N η x) ∨
        (x < a * N ∧ i = ht y (x + 1) ∧ levelIndex a b N η x < (i : ℤ) ∧
          (i : ℤ) ≤ levelIndex a b N η (x + 1)) := by
  rw [colouring_eq_union, Finset.mem_union, mem_colouringNorth_iff ha hN hη,
    mem_colouringEast_iff ha hN hη]

/-- **The colouring decides, column by column, whether the path is under the level line.** Walking
rightwards, the side the path is on changes exactly at a crossed north step (upwards) or a crossed
east step (downwards), and both are recorded by the colouring; at the abscissa `0` both paths sit at
height `0`. So two above-diagonal paths with the same colouring are on the same side of the level in
every column.

This is what rules out the one configuration that would break rule `A`: a path in the fibre of `c₊`
whose height at `X` is *above* `Y`, which could not be spliced back into the fibre of `c₋` without
disturbing the trace above the level. -/
theorem ht_le_levelIndex_iff (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) {y₁ y₂ : Heights a b N}
    (h₁ : IsAboveDiagonal y₁) (h₂ : IsAboveDiagonal y₂)
    (hc : colouring y₁ η = colouring y₂ η) :
    ∀ x ≤ a * N, ((ht y₁ x : ℤ) ≤ levelIndex a b N η x ↔
      (ht y₂ x : ℤ) ≤ levelIndex a b N η x) := by
  have hnorth : colouringNorth y₁ η = colouringNorth y₂ η := by
    rw [← filter_colouring_lt, ← filter_colouring_lt, hc]
  have heast : colouringEast y₁ η = colouringEast y₂ η := by
    rw [← filter_colouring_not_lt, ← filter_colouring_not_lt, hc]
  intro x
  induction x with
  | zero => intro _; rw [h₁.1, h₂.1]
  | succ x ih =>
    intro hx
    have hx' : x < a * N := by omega
    have ihx := ih (by omega)
    have hn : (∃ i, (x, i) ∈ colouringNorth y₁ η) ↔ (∃ i, (x, i) ∈ colouringNorth y₂ η) := by
      rw [hnorth]
    have he : (∃ i, (x, i) ∈ colouringEast y₁ η) ↔ (∃ i, (x, i) ∈ colouringEast y₂ η) := by
      rw [heast]
    rw [colouringNorth_column_iff ha hN hη _ hx', colouringNorth_column_iff ha hN hη _ hx'] at hn
    rw [colouringEast_column_iff ha hN hη _ hx', colouringEast_column_iff ha hN hη _ hx'] at he
    have hm₁ : ht y₁ x ≤ ht y₁ (x + 1) := h₁.2.2.1 x hx'
    have hm₂ : ht y₂ x ≤ ht y₂ (x + 1) := h₂.2.2.1 x hx'
    have hI : levelIndex a b N η x ≤ levelIndex a b N η (x + 1) :=
      levelIndex_le_levelIndex_succ ha hb hN η x
    omega

/-- The two admissible levels `ηlo < rk̂(X, Y) < ηhi` isolate the rank of the lattice point `(X, Y)`
of the rectangle: no lattice point of the rectangle has its rank strictly between them unless that
rank is `rk̂(X, Y)`. This is the hypothesis the four rules of Mellit's Theorem 4.2 share, bundled;
`HJO.Mellit.exists_isolating_isAdmissibleLevel` produces such a pair at every lattice point of the
rectangle. -/
structure Isolates (a b N X Y : ℕ) (ηlo ηhi : ℚ) : Prop where
  /-- The lower level is admissible. -/
  lo : IsAdmissibleLevel ηlo
  /-- The upper level is admissible. -/
  hi : IsAdmissibleLevel ηhi
  /-- The lower level is under the rank of `(X, Y)`. -/
  ltP : ηlo < ((pointRank a b N (X, Y) : ℤ) : ℚ)
  /-- The upper level is over the rank of `(X, Y)`. -/
  Plt : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηhi
  /-- No other rank of the rectangle lies between the two levels. -/
  iso : ∀ Q : ℕ × ℕ, Q.1 ≤ a * N → Q.2 ≤ b * N →
      ηlo < ((pointRank a b N Q : ℤ) : ℚ) → ((pointRank a b N Q : ℤ) : ℚ) < ηhi →
      pointRank a b N Q = pointRank a b N (X, Y)
  /-- The point lies in the rectangle. -/
  xle : X ≤ a * N
  /-- The point lies in the rectangle. -/
  yle : Y ≤ b * N

/-! ### What the bracketing says about the level index -/

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-- The lower level is under the rank of `(X, Y)`, so the column's level index there is below `Y`.
-/
theorem levelIndex_lo_lt (ha : 0 < a) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) :
    levelIndex a b N ηlo X < (Y : ℤ) :=
  (lt_cast_pointRank_iff ha hN ηlo X Y).1 hI.ltP

/-- **Away from `(X, Y)` the two levels cut the rectangle in the same place.** This is
`HJO.Mellit.levelIndex_of_isolating` read off the bundled hypothesis. -/
theorem le_levelIndex_iff_of_ne (ha : 0 < a) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    {x j : ℕ} (hx : x ≤ a * N) (hj : j ≤ b * N) (hne : (x, j) ≠ (X, Y)) :
    ((j : ℤ) ≤ levelIndex a b N ηlo x ↔ (j : ℤ) ≤ levelIndex a b N ηhi x) :=
  levelIndex_of_isolating ha hN hI.lo hI.hi (le_of_lt (hI.ltP.trans hI.Plt)) hI.xle hI.iso hx hj hne

/-- **At the abscissa of `X` the upper level's index is `Y`**, as far as the ordinates of the
rectangle can tell: a point of that column is under the upper level exactly when its ordinate is at
most `Y`. -/
theorem le_levelIndex_hi_iff (ha : 0 < a) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    {j : ℕ} (hj : j ≤ b * N) : ((j : ℤ) ≤ levelIndex a b N ηhi X ↔ j ≤ Y) := by
  constructor
  · intro h
    by_contra hcon
    have hne : ((X, j) : ℕ × ℕ) ≠ (X, Y) := by simp only [ne_eq, Prod.mk.injEq]; omega
    have h1 := hI.le_levelIndex_iff_of_ne ha hN hI.xle hj hne
    have h2 := hI.levelIndex_lo_lt ha hN
    omega
  · intro h
    rw [← cast_pointRank_lt_iff ha hN hI.hi]
    refine lt_of_le_of_lt ?_ hI.Plt
    exact_mod_cast pointRank_mono_snd a b N X h

/-- **At the abscissa of `X` the lower level's index is `Y - 1`**: a point of that column is under
the lower level exactly when its ordinate is below `Y`. -/
theorem le_levelIndex_lo_iff (ha : 0 < a) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    {j : ℕ} (hj : j ≤ b * N) : ((j : ℤ) ≤ levelIndex a b N ηlo X ↔ j < Y) := by
  have h2 := hI.levelIndex_lo_lt ha hN
  constructor
  · intro h; omega
  · intro h
    have hne : ((X, j) : ℕ × ℕ) ≠ (X, Y) := by simp only [ne_eq, Prod.mk.injEq]; omega
    have h1 := hI.le_levelIndex_iff_of_ne ha hN hI.xle hj hne
    have h3 := hI.le_levelIndex_hi_iff ha hN hj
    omega

/-- **The point one step right of `(X, Y)` is under the lower level.** It is outranked by `(X, Y)`,
and the isolation leaves it no room between the two levels. -/
theorem le_levelIndex_lo_succ (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X + 1 ≤ a * N) :
    (Y : ℤ) ≤ levelIndex a b N ηlo (X + 1) := by
  rw [← cast_pointRank_lt_iff ha hN hI.lo]
  have hstrict := pointRank_succ_fst_lt (a := a) (b := b) (N := N) ha hb hN X Y
  have hne : ((pointRank a b N (X + 1, Y) : ℤ) : ℚ) ≠ ηlo :=
    cast_pointRank_ne_of_isAdmissibleLevel hI.lo a b N (X + 1, Y)
  rcases lt_or_ge ηlo ((pointRank a b N (X + 1, Y) : ℤ) : ℚ) with h | h
  · exfalso
    have hupper : ((pointRank a b N (X + 1, Y) : ℤ) : ℚ) < ηhi := by
      refine lt_of_lt_of_le ?_ hI.Plt.le
      exact_mod_cast hstrict
    have := hI.iso (X + 1, Y) hX hI.yle h hupper
    omega
  · exact lt_of_le_of_ne h hne

/-- **The point one step left of `(X, Y)` is over the upper level.** It outranks `(X, Y)`, and the
isolation leaves it no room between the two levels. -/
theorem not_le_levelIndex_hi_pred (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : 1 ≤ X) :
    ¬ ((Y : ℤ) ≤ levelIndex a b N ηhi (X - 1)) := by
  have hxle := hI.xle
  rw [← cast_pointRank_lt_iff ha hN hI.hi]
  have hstrict := pointRank_lt_of_lt_fst (a := a) (b := b) (N := N) ha hb hN
    (show X - 1 < X by omega) Y
  intro hcon
  have hgt : ηlo < ((pointRank a b N (X - 1, Y) : ℤ) : ℚ) := by
    refine lt_of_lt_of_le hI.ltP ?_
    exact_mod_cast hstrict.le
  have := hI.iso (X - 1, Y) (by omega) hI.yle hgt hcon
  omega

/-- **The point one step left of `(X, Y)` is over the lower level too.** -/
theorem not_le_levelIndex_lo_pred (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : 1 ≤ X) :
    ¬ ((Y : ℤ) ≤ levelIndex a b N ηlo (X - 1)) := by
  have hxle := hI.xle
  have h1 := hI.le_levelIndex_iff_of_ne ha hN (x := X - 1) (j := Y) (by omega) hI.yle
    (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have h2 := hI.not_le_levelIndex_hi_pred ha hb hN hX
  omega

end Isolates

/-! ### The colouring at the two levels, point by point -/

section Membership

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-- **Below the level, `(X, Y)` is coloured exactly when it is the east step of its column.** The
north half cannot supply it: at the lower level the crossed north step of the column of `X` has
ordinate `Y - 1`. -/
theorem mem_colouring_lo_at_point (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) :
    (X, Y) ∈ colouring y ηlo ↔ (X < a * N ∧ ht y (X + 1) = Y) := by
  rw [mem_colouring_iff_levelIndex ha hN hI.lo]
  have h2 := hI.levelIndex_lo_lt ha hN
  constructor
  · rintro (⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩)
    · omega
    · exact ⟨g1, g2.symm⟩
  · rintro ⟨g1, g2⟩
    exact Or.inr ⟨g1, g2.symm, h2, hI.le_levelIndex_lo_succ ha hb hN (by omega)⟩

/-- **Below the level, the point under `(X, Y)` is coloured exactly when it is a north step of the
path.** Its ordinate `Y - 1` is the lower level's index in that column. -/
theorem mem_colouring_lo_at_below (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) (hY : 1 ≤ Y) :
    (X, Y - 1) ∈ colouring y ηlo ↔ (X < a * N ∧ ht y X ≤ Y - 1 ∧ Y - 1 < ht y (X + 1)) := by
  have hyle := hI.yle
  rw [mem_colouring_iff_levelIndex ha hN hI.lo]
  have h1 := hI.le_levelIndex_lo_iff ha hN (j := Y - 1) (by omega)
  have h2 := hI.le_levelIndex_lo_iff ha hN (j := Y) hI.yle
  constructor
  · rintro (⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩)
    · exact ⟨g1, g2, g3⟩
    · omega
  · rintro ⟨g1, g2, g3⟩
    exact Or.inl ⟨g1, g2, g3, by omega⟩

/-- **Above the level, `(X, Y)` is coloured exactly when it is a north step of the path.** Its
ordinate `Y` is the upper level's index in that column, so the east half cannot supply it. -/
theorem mem_colouring_hi_at_point (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) :
    (X, Y) ∈ colouring y ηhi ↔ (X < a * N ∧ ht y X ≤ Y ∧ Y < ht y (X + 1)) := by
  rw [mem_colouring_iff_levelIndex ha hN hI.hi]
  have h2 := hI.le_levelIndex_hi_iff ha hN (j := Y) hI.yle
  have hub : ht y (X + 1) ≤ b * N := ht_le_mul y _
  have hyle := hI.yle
  rcases lt_or_ge Y (b * N) with hY | hY
  · have h3 := hI.le_levelIndex_hi_iff ha hN (j := Y + 1) (by omega)
    constructor
    · rintro (⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩)
      · exact ⟨g1, g2, g3⟩
      · omega
    · rintro ⟨g1, g2, g3⟩
      exact Or.inl ⟨g1, g2, g3, by omega⟩
  · constructor
    · rintro (⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩) <;> omega
    · rintro ⟨g1, g2, g3⟩; omega

/-- **Above the level, the point under `(X, Y)` is never coloured**: its ordinate is below the upper
level's index in that column, and it is not the top of the column either. -/
theorem not_mem_colouring_hi_at_below (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) (hY : 1 ≤ Y)
    (hsw : Y ≤ ht y (X + 1)) : (X, Y - 1) ∉ colouring y ηhi := by
  rw [mem_colouring_iff_levelIndex ha hN hI.hi]
  have h2 := hI.le_levelIndex_hi_iff ha hN (j := Y) hI.yle
  rintro (⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩) <;> omega

/-- **Below the level, the point left of `(X, Y)` is never coloured**: it is over the lower level,
and the east step of its column would have to reach the ordinate `Y`, which the lower level's index
at `X` forbids. -/
theorem not_mem_colouring_lo_at_left (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) (hX : 1 ≤ X) :
    (X - 1, Y) ∉ colouring y ηlo := by
  have hsub : X - 1 + 1 = X := by omega
  rw [mem_colouring_iff_levelIndex ha hN hI.lo, hsub]
  have h1 := hI.not_le_levelIndex_lo_pred ha hb hN hX
  have h2 := hI.levelIndex_lo_lt ha hN
  rintro (⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩) <;> omega

/-- **Above the level, the point left of `(X, Y)` is coloured exactly when the path passes through
`(X, Y)` on its way in** — that is, when the path's height at `X` is `Y`, so that the east step
arriving at `(X, Y)` is crossed. This is the one place where the colouring above the level sees the
incoming letter of the event. -/
theorem mem_colouring_hi_at_left (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) (hX : 1 ≤ X) :
    (X - 1, Y) ∈ colouring y ηhi ↔ ht y X = Y := by
  have hsub : X - 1 + 1 = X := by omega
  have hxle := hI.xle
  rw [mem_colouring_iff_levelIndex ha hN hI.hi, hsub]
  have h1 := hI.not_le_levelIndex_hi_pred ha hb hN hX
  have h2 := hI.le_levelIndex_hi_iff ha hN (j := Y) hI.yle
  constructor
  · rintro (⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩) <;> omega
  · intro h
    exact Or.inr ⟨by omega, h.symm, by omega, by omega⟩

/-- **The two colourings differ only at the three points of the event.** Away from `(X, Y)`, the
point under it and the point left of it, lowering the level past `(X, Y)` changes nothing: every
rank comparison the colouring makes is settled in a column whose level index did not move, or at an
ordinate the move did not cross. -/
theorem mem_colouring_iff_of_ne (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) {p : ℕ × ℕ}
    (h1 : p ≠ (X, Y)) (h2 : p ≠ (X, Y - 1)) (h3 : p ≠ (X - 1, Y)) :
    (p ∈ colouring y ηlo ↔ p ∈ colouring y ηhi) := by
  obtain ⟨x, i⟩ := p
  have hxle := hI.xle
  have hyle := hI.yle
  have hub : ht y (x + 1) ≤ b * N := ht_le_mul y _
  simp only [ne_eq, Prod.mk.injEq, not_and] at h1 h2 h3
  rw [mem_colouring_iff_levelIndex ha hN hI.lo, mem_colouring_iff_levelIndex ha hN hI.hi]
  by_cases hx : x < a * N
  · by_cases hxX : x = X
    · subst hxX
      have e1 : ∀ j : ℕ, j ≤ b * N →
          ((j : ℤ) ≤ levelIndex a b N ηlo x ↔ j < Y) := fun j hj =>
        hI.le_levelIndex_lo_iff ha hN hj
      have e3 : ∀ j : ℕ, j ≤ b * N →
          ((j : ℤ) ≤ levelIndex a b N ηhi x ↔ j ≤ Y) := fun j hj =>
        hI.le_levelIndex_hi_iff ha hN hj
      have f1 := fun (hj : i ≤ b * N) => e1 i hj
      have f2 := fun (hj : i + 1 ≤ b * N) => e1 (i + 1) hj
      have f3 := fun (hj : i ≤ b * N) => e3 i hj
      have f4 := fun (hj : i + 1 ≤ b * N) => e3 (i + 1) hj
      have f5 := fun (hj : i ≤ b * N) =>
        hI.le_levelIndex_iff_of_ne ha hN (x := x + 1) (j := i) (by omega) hj
          (by simp only [ne_eq, Prod.mk.injEq]; omega)
      omega
    · by_cases hxX1 : x + 1 = X
      · subst hxX1
        have f1 := fun (hj : i ≤ b * N) =>
          hI.le_levelIndex_iff_of_ne ha hN (x := x) (j := i) (by omega) hj
            (by simp only [ne_eq, Prod.mk.injEq]; omega)
        have f2 := fun (hj : i + 1 ≤ b * N) =>
          hI.le_levelIndex_iff_of_ne ha hN (x := x) (j := i + 1) (by omega) hj
            (by simp only [ne_eq, Prod.mk.injEq]; omega)
        have f3 := fun (hj : i ≤ b * N) => hI.le_levelIndex_lo_iff ha hN (j := i) hj
        have f4 := fun (hj : i ≤ b * N) => hI.le_levelIndex_hi_iff ha hN (j := i) hj
        have h3' : i ≠ Y := fun hiY => h3 (by omega) hiY
        omega
      · have f1 := fun (hj : i ≤ b * N) =>
          hI.le_levelIndex_iff_of_ne ha hN (x := x) (j := i) (by omega) hj
            (by simp only [ne_eq, Prod.mk.injEq]; omega)
        have f2 := fun (hj : i + 1 ≤ b * N) =>
          hI.le_levelIndex_iff_of_ne ha hN (x := x) (j := i + 1) (by omega) hj
            (by simp only [ne_eq, Prod.mk.injEq]; omega)
        have f5 := fun (hj : i ≤ b * N) =>
          hI.le_levelIndex_iff_of_ne ha hN (x := x + 1) (j := i) (by omega) hj
            (by simp only [ne_eq, Prod.mk.injEq]; omega)
        omega
  · constructor <;> rintro (⟨g1, -⟩ | ⟨g1, -⟩) <;> omega

/-- The event type at a lattice point reads only whether the path's height to its left is below it
or level with it, and whether its height to the right is above it or level with it. -/
theorem eventType_eq_of_ht_iff {y₁ y₂ : Heights a b N} {X Y : ℕ}
    (k1 : ht y₁ X ≤ Y) (k2 : Y ≤ ht y₁ (X + 1)) (k3 : ht y₂ X ≤ Y) (k4 : Y ≤ ht y₂ (X + 1))
    (k5 : ht y₁ X = Y ↔ ht y₂ X = Y) (k6 : ht y₁ (X + 1) = Y ↔ ht y₂ (X + 1) = Y) :
    eventType y₁ (X, Y) = eventType y₂ (X, Y) := by
  simp only [eventType]
  split_ifs <;> first | rfl | omega

/-- **Two paths with the same local shape and the same colouring below the level have the same
colouring above it.** The three points of the event are decided by the shape, and everywhere else
the two colourings of each path agree. -/
theorem colouring_hi_eq_of_colouring_lo_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y₁ y₂ : Heights a b N}
    (k1 : ht y₁ X ≤ Y) (k2 : Y ≤ ht y₁ (X + 1)) (k3 : ht y₂ X ≤ Y) (k4 : Y ≤ ht y₂ (X + 1))
    (k5 : ht y₁ X = Y ↔ ht y₂ X = Y) (k6 : ht y₁ (X + 1) = Y ↔ ht y₂ (X + 1) = Y)
    (hc : colouring y₁ ηlo = colouring y₂ ηlo) : colouring y₁ ηhi = colouring y₂ ηhi := by
  ext p
  by_cases hp1 : p = (X, Y)
  · subst hp1
    rw [mem_colouring_hi_at_point ha hN hI y₁, mem_colouring_hi_at_point ha hN hI y₂]
    omega
  · by_cases hp2 : p = (X, Y - 1)
    · subst hp2
      have hY : 1 ≤ Y := by
        rcases Nat.eq_zero_or_pos Y with rfl | h
        · simp at hp1
        · exact h
      exact iff_of_false (not_mem_colouring_hi_at_below ha hN hI y₁ hY k2)
        (not_mem_colouring_hi_at_below ha hN hI y₂ hY k4)
    · by_cases hp3 : p = (X - 1, Y)
      · subst hp3
        have hX : 1 ≤ X := by
          rcases Nat.eq_zero_or_pos X with rfl | h
          · simp at hp1
          · exact h
        rw [mem_colouring_hi_at_left ha hb hN hI y₁ hX, mem_colouring_hi_at_left ha hb hN hI y₂ hX]
        omega
      · rw [← mem_colouring_iff_of_ne ha hN hI y₁ hp1 hp2 hp3,
          ← mem_colouring_iff_of_ne ha hN hI y₂ hp1 hp2 hp3, hc]

/-- **Two paths with the same local shape and the same colouring above the level have the same
colouring below it.** The converse of `HJO.Mellit.colouring_hi_eq_of_colouring_lo_eq`, proved the
same way. -/
theorem colouring_lo_eq_of_colouring_hi_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y₁ y₂ : Heights a b N}
    (k1 : ht y₁ X ≤ Y) (k2 : Y ≤ ht y₁ (X + 1)) (k3 : ht y₂ X ≤ Y) (k4 : Y ≤ ht y₂ (X + 1))
    (k5 : ht y₁ X = Y ↔ ht y₂ X = Y) (k6 : ht y₁ (X + 1) = Y ↔ ht y₂ (X + 1) = Y)
    (hc : colouring y₁ ηhi = colouring y₂ ηhi) : colouring y₁ ηlo = colouring y₂ ηlo := by
  ext p
  by_cases hp1 : p = (X, Y)
  · subst hp1
    rw [mem_colouring_lo_at_point ha hb hN hI y₁, mem_colouring_lo_at_point ha hb hN hI y₂]
    omega
  · by_cases hp2 : p = (X, Y - 1)
    · subst hp2
      have hY : 1 ≤ Y := by
        rcases Nat.eq_zero_or_pos Y with rfl | h
        · simp at hp1
        · exact h
      rw [mem_colouring_lo_at_below ha hN hI y₁ hY, mem_colouring_lo_at_below ha hN hI y₂ hY]
      omega
    · by_cases hp3 : p = (X - 1, Y)
      · subst hp3
        have hX : 1 ≤ X := by
          rcases Nat.eq_zero_or_pos X with rfl | h
          · simp at hp1
          · exact h
        exact iff_of_false (not_mem_colouring_lo_at_left ha hb hN hI y₁ hX)
          (not_mem_colouring_lo_at_left ha hb hN hI y₂ hX)
      · rw [mem_colouring_iff_of_ne ha hN hI y₁ hp1 hp2 hp3,
          mem_colouring_iff_of_ne ha hN hI y₂ hp1 hp2 hp3, hc]

/-- **The colouring at the lower level pins the path down at the swept point.** If the reference
path has an event of type `A`, `C` or `D` at `(X, Y)` — which is what
`ht y₁ X < Y ∨ ht y₁ (X+1) = Y` says, the two event types the lower colouring cannot tell apart
being `B` and `E` — then every above-diagonal path with the same colouring at the lower level has
the same height data at `(X, Y)`, hence the same event there. -/
theorem shape_of_colouring_lo_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y₁ y₂ : Heights a b N}
    (hy₁ : IsAboveDiagonal y₁) (hy₂ : IsAboveDiagonal y₂) (hdiag : b * X ≤ a * Y)
    (k1 : ht y₁ X ≤ Y) (k2 : Y ≤ ht y₁ (X + 1))
    (kAB : ht y₁ X < Y ∨ ht y₁ (X + 1) = Y)
    (hc : colouring y₁ ηlo = colouring y₂ ηlo) :
    ht y₂ X ≤ Y ∧ Y ≤ ht y₂ (X + 1) ∧ (ht y₁ X = Y ↔ ht y₂ X = Y) ∧
      (ht y₁ (X + 1) = Y ↔ ht y₂ (X + 1) = Y) := by
  have hyle := hI.yle
  have hxle := hI.xle
  rcases eq_or_lt_of_le hxle with hXeq | hXlt
  · have hYeq : Y = b * N := by
      have h1 : a * (b * N) ≤ a * Y := by
        calc a * (b * N) = b * (a * N) := by ring
        _ = b * X := by rw [hXeq]
        _ ≤ a * Y := hdiag
      have := Nat.le_of_mul_le_mul_left h1 ha
      omega
    have h1 : ht y₁ X = b * N := by rw [hXeq]; exact hy₁.2.1
    have h2 : ht y₂ X = b * N := by rw [hXeq]; exact hy₂.2.1
    have h3 : ht y₁ (X + 1) = b * N := ht_of_gt y₁ (by omega)
    have h4 : ht y₂ (X + 1) = b * N := ht_of_gt y₂ (by omega)
    omega
  · have hmem1 : ((X, Y) ∈ colouring y₁ ηlo ↔ (X, Y) ∈ colouring y₂ ηlo) := by rw [hc]
    rw [mem_colouring_lo_at_point ha hb hN hI y₁,
      mem_colouring_lo_at_point ha hb hN hI y₂] at hmem1
    have hmono₂ : ht y₂ X ≤ ht y₂ (X + 1) := hy₂.2.2.1 X hXlt
    rcases Nat.eq_zero_or_pos Y with rfl | hY
    · omega
    · have hmem2 : ((X, Y - 1) ∈ colouring y₁ ηlo ↔ (X, Y - 1) ∈ colouring y₂ ηlo) := by rw [hc]
      rw [mem_colouring_lo_at_below ha hN hI y₁ hY,
        mem_colouring_lo_at_below ha hN hI y₂ hY] at hmem2
      omega

end Membership

/-! ### The splice -/

section Raise

/-- The path `ŷ` raised to the ordinate `Y` from the abscissa `X + 1` rightwards: the pointwise
maximum of `ŷ` with the path that sits at `0` up to `X` and at `Y` afterwards. This is the splice
that rule `A` needs — it changes `ŷ` only under the level line, so it leaves the trace above the
level alone, while forcing a type-`A` event at `(X, Y)`. -/
def raiseFrom (y : Heights a b N) (X : ℕ) (Y : Fin (b * N + 1)) : Heights a b N :=
  fun r => if (r : ℕ) ≤ X then y r else max (y r) Y

/-- Left of the splice the heights are untouched. -/
theorem ht_raiseFrom_of_le (y : Heights a b N) {X : ℕ} (Y : Fin (b * N + 1)) {r : ℕ}
    (hr : r ≤ X) (hX : X ≤ a * N) : ht (raiseFrom y X Y) r = ht y r := by
  have h : r < a * N + 1 := by omega
  rw [show r = ((⟨r, h⟩ : Fin (a * N + 1)) : ℕ) from rfl, ht_coe, ht_coe]
  simp [raiseFrom, hr]

/-- Right of the splice each height is raised to at least `Y`. -/
theorem ht_raiseFrom_of_gt (y : Heights a b N) {X : ℕ} (Y : Fin (b * N + 1)) {r : ℕ}
    (hr : X < r) : ht (raiseFrom y X Y) r = max (ht y r) (Y : ℕ) := by
  by_cases h : r < a * N + 1
  · rw [show r = ((⟨r, h⟩ : Fin (a * N + 1)) : ℕ) from rfl, ht_coe, ht_coe]
    simp [raiseFrom, Nat.not_le.2 hr, Fin.coe_max]
  · rw [ht_of_gt _ (by omega), ht_of_gt _ (by omega)]
    have : (Y : ℕ) ≤ b * N := Nat.lt_succ_iff.1 Y.isLt
    omega


/-- The splice of an above-diagonal path is an above-diagonal path: raising heights keeps them
monotone and keeps them over the diagonal, and `Y ≤ bN` keeps the right endpoint where it was. -/
theorem isAboveDiagonal_raiseFrom {y : Heights a b N} (hy : IsAboveDiagonal y) {X : ℕ}
    (hX : X ≤ a * N) (Y : Fin (b * N + 1)) :
    IsAboveDiagonal (raiseFrom y X Y) := by
  have hle : ∀ r, ht y r ≤ ht (raiseFrom y X Y) r := by
    intro r
    rcases Nat.lt_or_ge X r with h | h
    · rw [ht_raiseFrom_of_gt y Y h]; omega
    · rw [ht_raiseFrom_of_le y Y h hX]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht_raiseFrom_of_le y Y (by omega) hX]; exact hy.1
  · rcases Nat.lt_or_ge X (a * N) with h | h
    · rw [ht_raiseFrom_of_gt y Y h, hy.2.1]
      have : (Y : ℕ) ≤ b * N := Nat.lt_succ_iff.1 Y.isLt
      omega
    · rw [ht_raiseFrom_of_le y Y (by omega) hX]
      exact hy.2.1
  · intro r hr
    rcases Nat.lt_or_ge X (r + 1) with h | h
    · rcases Nat.lt_or_ge X r with h2 | h2
      · rw [ht_raiseFrom_of_gt y Y h2, ht_raiseFrom_of_gt y Y h]
        have := hy.2.2.1 r hr
        omega
      · rw [ht_raiseFrom_of_le y Y h2 hX, ht_raiseFrom_of_gt y Y h]
        have := hy.2.2.1 r hr
        omega
    · rw [ht_raiseFrom_of_le y Y (by omega) hX, ht_raiseFrom_of_le y Y (by omega) hX]
      exact hy.2.2.1 r hr
  · intro r hr
    exact (hy.2.2.2 r hr).trans (Nat.mul_le_mul_left a (hle r))

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-- A swept point above the upper level, weakly right of `(X, Y)`, is strictly above `Y`: the level
index does not decrease rightwards, and at the abscissa of `X` it is already `Y`. -/
theorem lt_snd_of_lt_pointRank (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {Q : ℕ × ℕ} (hQ1 : X ≤ Q.1)
    (hQ : ηhi < ((pointRank a b N Q : ℤ) : ℚ)) : Y < Q.2 := by
  have h1 : levelIndex a b N ηhi Q.1 < (Q.2 : ℤ) := (lt_cast_pointRank_iff ha hN ηhi Q.1 Q.2).1 hQ
  have h2 : (Y : ℤ) ≤ levelIndex a b N ηhi X :=
    (hI.le_levelIndex_hi_iff ha hN hI.yle).2 le_rfl
  have h3 := levelIndex_le_of_fst_le ha hb hN ηhi hQ1 (a := a) (b := b) (N := N)
  omega

/-- **The splice sweeps the same points above the level.** A swept point above the level and weakly
right of `X` has ordinate over `Y`, so raising the columns right of `X` to `Y` adds none and removes
none. -/
theorem sweptAbove_raiseFrom (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) {Y' : Fin (b * N + 1)}
    (hY' : (Y' : ℕ) = Y) : sweptAbove (raiseFrom y X Y') ηhi = sweptAbove y ηhi := by
  ext Q
  simp only [sweptAbove, Finset.mem_filter, mem_sweptRegion]
  constructor
  · rintro ⟨⟨g1, g2, g3⟩, g4⟩
    refine ⟨⟨g1, g2, ?_⟩, g4⟩
    rcases Nat.lt_or_ge X (Q.1 + 1) with hx | hx
    · have := lt_snd_of_lt_pointRank ha hb hN hI (Q := Q) (by omega) g4
      rw [ht_raiseFrom_of_gt y Y' hx, hY'] at g3
      omega
    · rwa [ht_raiseFrom_of_le y Y' hx hI.xle] at g3
  · rintro ⟨⟨g1, g2, g3⟩, g4⟩
    refine ⟨⟨g1, g2, ?_⟩, g4⟩
    rcases Nat.lt_or_ge X (Q.1 + 1) with hx | hx
    · rw [ht_raiseFrom_of_gt y Y' hx, hY']
      omega
    · rwa [ht_raiseFrom_of_le y Y' hx hI.xle]

/-- **The splice does not change the event at a swept point above the level.** There the path's own
height to the right is already over `Y`, so the splice leaves it alone, and the height to the left
is either left alone or raised to a value still under the point. -/
theorem eventType_raiseFrom (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) {Y' : Fin (b * N + 1)}
    (hY' : (Y' : ℕ) = Y) {Q : ℕ × ℕ} (hQ : Q ∈ sweptAbove y ηhi) :
    eventType (raiseFrom y X Y') Q = eventType y Q := by
  obtain ⟨hQsw, hQη⟩ := Finset.mem_filter.1 hQ
  obtain ⟨g1, g2, g3⟩ := mem_sweptRegion.1 hQsw
  have key : X ≤ Q.1 → Y < Q.2 := fun h => lt_snd_of_lt_pointRank ha hb hN hI h hQη
  have e1 : ht (raiseFrom y X Y') (Q.1 + 1) = ht y (Q.1 + 1) := by
    rcases Nat.lt_or_ge X (Q.1 + 1) with hx | hx
    · have := key (by omega)
      rw [ht_raiseFrom_of_gt y Y' hx, hY']
      omega
    · exact ht_raiseFrom_of_le y Y' hx hI.xle
  have e2 : (Q.2 < ht (raiseFrom y X Y') Q.1 ↔ Q.2 < ht y Q.1) ∧
      (ht (raiseFrom y X Y') Q.1 < Q.2 ↔ ht y Q.1 < Q.2) := by
    rcases Nat.lt_or_ge X Q.1 with hx | hx
    · have := key (by omega)
      rw [ht_raiseFrom_of_gt y Y' hx, hY']
      omega
    · rw [ht_raiseFrom_of_le y Y' hx hI.xle]
      exact ⟨Iff.rfl, Iff.rfl⟩
  simp only [eventType, e1]
  split_ifs <;> first | rfl | omega

/-- **The splice does not change the live north steps at a swept point above the level.** Every
north step the splice adds or removes has its head at or under `(X, Y)`, hence under the upper
level, so the level line through a point above the level crosses none of them. -/
theorem liveSteps_raiseFrom (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) {Y' : Fin (b * N + 1)}
    (hY' : (Y' : ℕ) = Y) {Q : ℕ × ℕ} (hQ : Q ∈ sweptAbove y ηhi) :
    liveSteps (raiseFrom y X Y') Q = liveSteps y Q := by
  obtain ⟨hQsw, hQη⟩ := Finset.mem_filter.1 hQ
  have hQrk : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ((pointRank a b N Q : ℤ) : ℚ) := hI.Plt.trans hQη
  have hQrk' : pointRank a b N (X, Y) < pointRank a b N Q := by exact_mod_cast hQrk
  have main : ∀ v : ℕ × ℕ, pointRank a b N Q < pointRank a b N (v.1, v.2 + 1) →
      ((ht (raiseFrom y X Y') v.1 ≤ v.2 ↔ ht y v.1 ≤ v.2) ∧
        (v.2 < ht (raiseFrom y X Y') (v.1 + 1) ↔ v.2 < ht y (v.1 + 1))) := by
    intro v hv5
    have hv : X ≤ v.1 → Y ≤ v.2 := by
      intro h1
      by_contra hcon
      have : pointRank a b N (v.1, v.2 + 1) ≤ pointRank a b N (X, Y) :=
        pointRank_le_of_fst_le_of_snd_le hb hN h1 (by omega)
      omega
    refine ⟨?_, ?_⟩
    · rcases Nat.lt_or_ge X v.1 with hx | hx
      · rw [ht_raiseFrom_of_gt y Y' hx, hY']
        have := hv (by omega)
        omega
      · rw [ht_raiseFrom_of_le y Y' hx hI.xle]
    · rcases Nat.lt_or_ge X (v.1 + 1) with hx | hx
      · rw [ht_raiseFrom_of_gt y Y' hx, hY']
        have := hv (by omega)
        omega
      · rw [ht_raiseFrom_of_le y Y' hx hI.xle]
  ext v
  simp only [liveSteps, Finset.mem_filter, mem_northSteps_iff]
  constructor <;> rintro ⟨⟨g1, g2, g3⟩, g4, g5⟩ <;>
    · have g5' : pointRank a b N Q < pointRank a b N (v.1, v.2 + 1) := by
        simp only [pointRank, abovePointRank_succ]
        exact g5
      obtain ⟨m1, m2⟩ := main v g5'
      exact ⟨⟨g1, by tauto, by tauto⟩, g4, g5⟩

/-- The splice does not change the live count to the right at a swept point above the level. -/
theorem sweepRight_raiseFrom (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) {Y' : Fin (b * N + 1)}
    (hY' : (Y' : ℕ) = Y) {Q : ℕ × ℕ} (hQ : Q ∈ sweptAbove y ηhi) :
    sweepRight (raiseFrom y X Y') Q = sweepRight y Q := by
  rw [sweepRight, sweepRight, liveSteps_raiseFrom hb hN hI y hY' hQ]

/-- **The splice leaves the trace above the level alone.** -/
theorem levelTrace_raiseFrom (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) {Y' : Fin (b * N + 1)}
    (hY' : (Y' : ℕ) = Y) :
    levelTrace (raiseFrom y X Y') ηhi = levelTrace y ηhi := by
  rw [levelTrace, levelTrace, sweptAbove_raiseFrom ha hb hN hI y hY']
  refine Finset.image_congr fun Q hQ => ?_
  have hQ' : Q ∈ sweptAbove y ηhi := hQ
  rw [eventType_raiseFrom ha hb hN hI y hY' hQ', sweepRight_raiseFrom hb hN hI y hY' hQ']

/-- **The splice leaves the colouring at the upper level alone.** -/
theorem colouring_hi_raiseFrom (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) {Y' : Fin (b * N + 1)}
    (hY' : (Y' : ℕ) = Y) :
    colouring (raiseFrom y X Y') ηhi = colouring y ηhi := by
  ext p
  obtain ⟨x, i⟩ := p
  rw [mem_colouring_iff_levelIndex ha hN hI.hi, mem_colouring_iff_levelIndex ha hN hI.hi]
  have hYI : (Y : ℤ) ≤ levelIndex a b N ηhi X := (hI.le_levelIndex_hi_iff ha hN hI.yle).2 le_rfl
  rcases Nat.lt_or_ge X (x + 1) with hx | hx
  · have hIx : levelIndex a b N ηhi X ≤ levelIndex a b N ηhi x :=
      levelIndex_le_of_fst_le ha hb hN ηhi (by omega)
    have hIx1 : levelIndex a b N ηhi X ≤ levelIndex a b N ηhi (x + 1) :=
      levelIndex_le_of_fst_le ha hb hN ηhi (by omega)
    have e1 : ht (raiseFrom y X Y') (x + 1) = max (ht y (x + 1)) Y := by
      rw [ht_raiseFrom_of_gt y Y' hx, hY']
    rcases Nat.lt_or_ge X x with hx2 | hx2
    · have e2 : ht (raiseFrom y X Y') x = max (ht y x) Y := by
        rw [ht_raiseFrom_of_gt y Y' hx2, hY']
      omega
    · have e2 : ht (raiseFrom y X Y') x = ht y x := ht_raiseFrom_of_le y Y' hx2 hI.xle
      omega
  · have e1 : ht (raiseFrom y X Y') (x + 1) = ht y (x + 1) := ht_raiseFrom_of_le y Y' hx hI.xle
    have e2 : ht (raiseFrom y X Y') x = ht y x := ht_raiseFrom_of_le y Y' (by omega) hI.xle
    rw [e1, e2]

end Raise

/-! ### The event operator, the trace, and the grouping -/

section Assembly

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-- **The live north steps at the swept point are the crossed north steps at the upper level.** The
level line of the rank through `(X, Y)` and the upper level cut the same north steps: a foot
outranked by `(X, Y)` is a foot under the upper level, and a head outranking `(X, Y)` is a head over
it, the isolation forbidding anything in between. This is what makes the width and the live count to
the right at `(X, Y)` readable off the colouring at the upper level. -/
theorem liveSteps_eq_colouringNorth (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) :
    liveSteps y (X, Y) = colouringNorth y ηhi := by
  ext v
  simp only [liveSteps, colouringNorth, Finset.mem_filter]
  have hp1 : pointRank a b N v = abovePointRank a b N v.1 v.2 := rfl
  have hp2 : pointRank a b N (X, Y) = abovePointRank a b N X Y := rfl
  have hsucc : pointRank a b N (v.1, v.2 + 1) =
      pointRank a b N v + (attackWindow a N : ℤ) := abovePointRank_succ a b N v.1 v.2
  have hcast : ((pointRank a b N (v.1, v.2 + 1) : ℤ) : ℚ) =
      ((pointRank a b N v : ℤ) : ℚ) + ((attackWindow a N : ℕ) : ℚ) := by
    rw [hsucc]; push_cast; ring
  have hne : ((pointRank a b N (v.1, v.2 + 1) : ℤ) : ℚ) ≠ ηhi :=
    cast_pointRank_ne_of_isAdmissibleLevel hI.hi a b N _
  have hnev : ((pointRank a b N v : ℤ) : ℚ) ≠ ηhi :=
    cast_pointRank_ne_of_isAdmissibleLevel hI.hi a b N _
  constructor
  · rintro ⟨hv, h1, h2⟩
    obtain ⟨hv1, hv2, hv3⟩ := mem_northSteps_iff.1 hv
    have hvb : v.2 + 1 ≤ b * N := by have := ht_le_mul y (v.1 + 1); omega
    refine ⟨hv, ?_, ?_⟩
    · refine lt_of_le_of_lt ?_ hI.Plt
      have : pointRank a b N v ≤ pointRank a b N (X, Y) := by omega
      exact_mod_cast this
    · have hlt : pointRank a b N (X, Y) < pointRank a b N (v.1, v.2 + 1) := by omega
      by_contra hcon
      have hle : ((pointRank a b N (v.1, v.2 + 1) : ℤ) : ℚ) ≤ ηhi := by
        rw [hcast]; exact not_lt.1 hcon
      have hgt : ηlo < ((pointRank a b N (v.1, v.2 + 1) : ℤ) : ℚ) := by
        refine hI.ltP.trans ?_
        exact_mod_cast hlt
      have := hI.iso (v.1, v.2 + 1) (by omega) hvb hgt (lt_of_le_of_ne hle hne)
      omega
  · rintro ⟨hv, h1, h2⟩
    obtain ⟨hv1, hv2, hv3⟩ := mem_northSteps_iff.1 hv
    have hvb : v.2 ≤ b * N := by have := ht_le_mul y (v.1 + 1); omega
    refine ⟨hv, ?_, ?_⟩
    · by_contra hcon
      have hgt : ηlo < ((pointRank a b N v : ℤ) : ℚ) := by
        refine hI.ltP.trans ?_
        have : pointRank a b N (X, Y) < pointRank a b N v := by omega
        exact_mod_cast this
      have := hI.iso v (by omega) hvb hgt h1
      omega
    · have h2' : ηhi < ((pointRank a b N (v.1, v.2 + 1) : ℤ) : ℚ) := by rw [hcast]; exact h2
      have h3 : pointRank a b N (X, Y) < pointRank a b N (v.1, v.2 + 1) := by
        have := hI.Plt.trans h2'
        exact_mod_cast this
      omega

/-- **The event operator at `(X, Y)` is read off the colouring above the level and the event type.**
The width and the live count to the right at `(X, Y)` count crossed north steps at the upper level,
which `HJO.Mellit.filter_colouring_lt` recovers from the colouring there. -/
theorem sweepOperator_eq_of_colouring_hi_eq {L : Type*} [Field L] [Algebra ℚ L] (q u : L)
    (hI : Isolates a b N X Y ηlo ηhi) {y₁ y₂ : Heights a b N}
    (hcol : colouring y₁ ηhi = colouring y₂ ηhi)
    (hev : eventType y₁ (X, Y) = eventType y₂ (X, Y)) :
    sweepOperator q u y₁ (X, Y) = sweepOperator q u y₂ (X, Y) := by
  have hn : colouringNorth y₁ ηhi = colouringNorth y₂ ηhi := by
    rw [← filter_colouring_lt, ← filter_colouring_lt, hcol]
  have hw : sweepWidth y₁ (X, Y) = sweepWidth y₂ (X, Y) := by
    rw [sweepWidth, sweepWidth, liveSteps_eq_colouringNorth hI,
      liveSteps_eq_colouringNorth hI, hn]
  have hr : sweepRight y₁ (X, Y) = sweepRight y₂ (X, Y) := by
    rw [sweepRight, sweepRight, liveSteps_eq_colouringNorth hI,
      liveSteps_eq_colouringNorth hI, hn]
  simp only [sweepOperator, hev, hw, hr]

/-- Lowering the level past the swept point adds exactly its own triple to the trace. -/
theorem levelTrace_lo_eq_insert_triple (ha : 0 < a) (hI : Isolates a b N X Y ηlo ηhi)
    {y : Heights a b N} (hPsw : (X, Y) ∈ sweptRegion y) :
    levelTrace y ηlo =
      insert (((X, Y) : ℕ × ℕ), eventType y (X, Y), sweepRight y (X, Y)) (levelTrace y ηhi) := by
  rw [levelTrace, levelTrace,
    sweptAbove_eq_insert_of_isolating ha hI.hi hI.ltP hI.Plt hI.iso hPsw,
    Finset.image_union, Finset.image_singleton, Finset.insert_eq]

/-- The swept point is under the upper level, so its triple is not in the trace there. -/
theorem notMem_levelTrace_hi (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N)
    (e : EventType) (r : ℕ) : (((X, Y) : ℕ × ℕ), e, r) ∉ levelTrace y ηhi := by
  simp only [levelTrace, Finset.mem_image, not_exists]
  rintro Q ⟨hQ, hQeq⟩
  have hQ1 : Q = (X, Y) := congrArg Prod.fst hQeq
  subst hQ1
  exact absurd (Finset.mem_filter.1 hQ).2 (not_lt.2 hI.Plt.le)

/-- The trace of a path is one of the traces its colouring admits. -/
theorem mem_traceIndex_of_colouring_eq (y : Heights a b N) (hy : IsAboveDiagonal y) (η : ℚ)
    {c : Finset (ℕ × ℕ)} (hc : colouring y η = c) : levelTrace y η ∈ traceIndex a b N η c := by
  simp only [traceIndex, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨y, ⟨hy, hc⟩, rfl⟩

/-- A trace admitted by a colouring is the trace of an above-diagonal path carrying that colouring.
-/
theorem exists_path_of_mem_traceIndex {η : ℚ} {c : Finset (ℕ × ℕ)}
    {τ : Finset ((ℕ × ℕ) × EventType × ℕ)} (hτ : τ ∈ traceIndex a b N η c) :
    ∃ y : Heights a b N, IsAboveDiagonal y ∧ colouring y η = c ∧ levelTrace y η = τ := by
  simp only [traceIndex, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hτ
  obtain ⟨y, ⟨hy, hc⟩, hyt⟩ := hτ
  exact ⟨y, hy, hc, hyt⟩

/-- **What the colouring at the upper level says about a path at the swept point.** -/
theorem shape_of_colouring_hi_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y₁ y₂ : Heights a b N}
    (hy₁ : IsAboveDiagonal y₁) (hy₂ : IsAboveDiagonal y₂) (hdiag : b * X ≤ a * Y)
    (k1 : ht y₁ X ≤ Y) (k2 : Y ≤ ht y₁ (X + 1))
    (hc : colouring y₂ ηhi = colouring y₁ ηhi) :
    ht y₂ X ≤ Y ∧ (ht y₁ X = Y ↔ ht y₂ X = Y) ∧ (ht y₁ (X + 1) = Y ↔ ht y₂ (X + 1) ≤ Y) := by
  have hstate := ht_le_levelIndex_iff ha hb hN hI.hi hy₂ hy₁ hc X hI.xle
  have ha1 := hI.le_levelIndex_hi_iff ha hN (j := ht y₂ X) (ht_le_mul y₂ X)
  have ha2 := hI.le_levelIndex_hi_iff ha hN (j := ht y₁ X) (ht_le_mul y₁ X)
  have haX : ht y₂ X ≤ Y := by omega
  refine ⟨haX, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos X with rfl | hX
    · rw [hy₁.1, hy₂.1]
    · rw [← mem_colouring_hi_at_left ha hb hN hI y₁ hX,
        ← mem_colouring_hi_at_left ha hb hN hI y₂ hX, hc]
  · rcases eq_or_lt_of_le hI.xle with hXeq | hXlt
    · have hYeq : Y = b * N := by
        have h1 : a * (b * N) ≤ a * Y := by
          calc a * (b * N) = b * (a * N) := by ring
          _ = b * X := by rw [hXeq]
          _ ≤ a * Y := hdiag
        have := Nat.le_of_mul_le_mul_left h1 ha
        have := hI.yle
        omega
      have e1 : ht y₁ (X + 1) = b * N := ht_of_gt y₁ (by omega)
      have e2 : ht y₂ (X + 1) = b * N := ht_of_gt y₂ (by omega)
      omega
    · have hmem : ((X, Y) ∈ colouring y₁ ηhi ↔ (X, Y) ∈ colouring y₂ ηhi) := by rw [hc]
      rw [mem_colouring_hi_at_point ha hN hI y₁, mem_colouring_hi_at_point ha hN hI y₂] at hmem
      omega

/-- **Every trace at the upper level in the fibre of `c₊` extends to the fibre of `c₋`.** This is
the surjectivity half of the grouping of traces: the splice `HJO.Mellit.raiseFrom` forces the
reference path's event at `(X, Y)` without disturbing the trace above the level. -/
theorem exists_colouring_lo_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {ŷ y' : Heights a b N}
    (hŷ : IsAboveDiagonal ŷ) (hy' : IsAboveDiagonal y') (hdiag : b * X ≤ a * Y)
    (k1 : ht ŷ X ≤ Y) (k2 : Y ≤ ht ŷ (X + 1))
    (hc : colouring y' ηhi = colouring ŷ ηhi) :
    ∃ y : Heights a b N, IsAboveDiagonal y ∧ colouring y ηlo = colouring ŷ ηlo ∧
      levelTrace y ηhi = levelTrace y' ηhi := by
  obtain ⟨s1, s2, s3⟩ := shape_of_colouring_hi_eq ha hb hN hI hŷ hy' hdiag k1 k2 hc
  have hyle := hI.yle
  refine ⟨raiseFrom y' X ⟨Y, by omega⟩,
    isAboveDiagonal_raiseFrom hy' hI.xle _, ?_,
    levelTrace_raiseFrom ha hb hN hI y' rfl⟩
  have e1 : ht (raiseFrom y' X ⟨Y, by omega⟩) X = ht y' X :=
    ht_raiseFrom_of_le y' _ le_rfl hI.xle
  have e2 : ht (raiseFrom y' X ⟨Y, by omega⟩) (X + 1) = max (ht y' (X + 1)) Y :=
    ht_raiseFrom_of_gt y' _ (Nat.lt_succ_self X)
  refine colouring_lo_eq_of_colouring_hi_eq ha hb hN hI (by omega) (by omega) k1 k2
    (by omega) (by omega) ?_
  rw [colouring_hi_raiseFrom ha hb hN hI y' rfl, hc]

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **What a path with the reference path's colouring at the lower level has in common with it.**
Every above-diagonal path coloured `c₋` at the lower level sweeps `(X, Y)`, has the same event
there, and is coloured `c₊` at the upper level. -/
theorem key_of_colouring_lo_eq (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {ŷ y : Heights a b N}
    (hŷ : IsAboveDiagonal ŷ) (hy : IsAboveDiagonal y) (hdiag : b * X ≤ a * Y)
    (k1 : ht ŷ X ≤ Y) (k2 : Y ≤ ht ŷ (X + 1))
    (hAB : ht ŷ X < Y ∨ ht ŷ (X + 1) = Y)
    (hcl : colouring y ηlo = colouring ŷ ηlo) :
    (X, Y) ∈ sweptRegion y ∧ colouring y ηhi = colouring ŷ ηhi ∧
      eventType y (X, Y) = eventType ŷ (X, Y) ∧
      sweepRight y (X, Y) = sweepRight ŷ (X, Y) ∧
      sweepOperator q u y (X, Y) = sweepOperator q u ŷ (X, Y) := by
  obtain ⟨s1, s2, s3, s4⟩ :=
    shape_of_colouring_lo_eq ha hb hN hI hŷ hy hdiag k1 k2 hAB hcl.symm
  have hsw : (X, Y) ∈ sweptRegion y := mem_sweptRegion.2 ⟨hI.xle, hdiag, s2⟩
  have hcol : colouring y ηhi = colouring ŷ ηhi :=
    colouring_hi_eq_of_colouring_lo_eq ha hb hN hI s1 s2 k1 k2 s3.symm s4.symm hcl
  have hev : eventType y (X, Y) = eventType ŷ (X, Y) :=
    eventType_eq_of_ht_iff s1 s2 k1 k2 s3.symm s4.symm
  have hn : colouringNorth y ηhi = colouringNorth ŷ ηhi := by
    rw [← filter_colouring_lt, ← filter_colouring_lt, hcol]
  refine ⟨hsw, hcol, hev, ?_, sweepOperator_eq_of_colouring_hi_eq q u hI hcol hev⟩
  rw [sweepRight, sweepRight, liveSteps_eq_colouringNorth hI, liveSteps_eq_colouringNorth hI, hn]

/-- **The shared content of rules `A`, `C` and `D` of Mellit's Theorem 4.2.** Lowering the level
past a swept point whose event is not of type `B` or `E` multiplies the invariant of the colouring
by that event's operator.

The traces at the lower level with colouring `c₋` correspond to the traces at the upper level with
colouring `c₊` by erasing the swept point's own triple. That correspondence is the whole content,
and it is **not** induced by a bijection of paths: the fibre of `c₊` over the above-diagonal paths
is strictly larger than the fibre of `c₋`, and the extra paths are carried into the fibre of `c₋` by
the splice `HJO.Mellit.raiseFrom`, which changes a path only under the level line and so leaves its
trace above the level alone. -/
theorem dsc_lo_eq_sweepOperator_dsc_hi (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {ŷ : Heights a b N} (hŷ : IsAboveDiagonal ŷ)
    (hPsw : (X, Y) ∈ sweptRegion ŷ) (hAB : ht ŷ X < Y ∨ ht ŷ (X + 1) = Y) :
    dsc q u a b N ηlo (colouring ŷ ηlo) =
      sweepOperator q u ŷ (X, Y) (dsc q u a b N ηhi (colouring ŷ ηhi)) := by
  obtain ⟨-, hdiag, k2⟩ := mem_sweptRegion.1 hPsw
  have k1 : ht ŷ X ≤ Y := by
    rcases hAB with h | h
    · omega
    · have : ht ŷ X ≤ ht ŷ (X + 1) := ht_mono hŷ.2.2.1 (Nat.le_succ X)
      omega
  obtain ⟨x₀, hx₀⟩ : ∃ x : (ℕ × ℕ) × EventType × ℕ,
      x = (((X, Y) : ℕ × ℕ), eventType ŷ (X, Y), sweepRight ŷ (X, Y)) := ⟨_, rfl⟩
  have hx₀not : ∀ y : Heights a b N, x₀ ∉ levelTrace y ηhi := by
    intro y
    rw [hx₀]
    exact notMem_levelTrace_hi hI y _ _
  have hins : ∀ y : Heights a b N, IsAboveDiagonal y → colouring y ηlo = colouring ŷ ηlo →
      levelTrace y ηlo = insert x₀ (levelTrace y ηhi) := by
    intro y hy hcl
    obtain ⟨hsw, hcol, hev, hr, -⟩ :=
      key_of_colouring_lo_eq q u ha hb hN hI hŷ hy hdiag k1 k2 hAB hcl
    have h := levelTrace_lo_eq_insert_triple ha hI hsw
    rwa [hev, hr, ← hx₀] at h
  have hlo : ∀ τ ∈ traceIndex a b N ηlo (colouring ŷ ηlo),
      IsAboveDiagonal (traceRep a b N ηlo (colouring ŷ ηlo) τ) ∧
        colouring (traceRep a b N ηlo (colouring ŷ ηlo) τ) ηhi = colouring ŷ ηhi ∧
        levelTrace (traceRep a b N ηlo (colouring ŷ ηlo) τ) ηhi = τ.erase x₀ ∧ x₀ ∈ τ ∧
        partialSweepWord q u (traceRep a b N ηlo (colouring ŷ ηlo) τ) ηlo =
          sweepOperator q u ŷ (X, Y) *
            partialSweepWord q u (traceRep a b N ηlo (colouring ŷ ηlo) τ) ηhi := by
    intro τ hτ
    obtain ⟨hy, hcl, htr⟩ := traceRep_spec hτ
    obtain ⟨hsw, hcol, hev, hr, hop⟩ :=
      key_of_colouring_lo_eq q u ha hb hN hI hŷ hy hdiag k1 k2 hAB hcl
    have h := hins _ hy hcl
    refine ⟨hy, hcol, ?_, ?_, ?_⟩
    · exact ((congrArg (fun s => Finset.erase s x₀) (htr.symm.trans h)).trans
        (Finset.erase_insert (hx₀not _))).symm
    · rw [← htr, h]
      exact Finset.mem_insert_self _ _
    · rw [partialSweepWord_eq_sweepOperator_mul q u ha hI.hi hI.ltP hI.Plt hI.iso hsw, hop]
  have hmapsto : ∀ τ ∈ traceIndex a b N ηlo (colouring ŷ ηlo),
      τ.erase x₀ ∈ traceIndex a b N ηhi (colouring ŷ ηhi) := by
    intro τ hτ
    obtain ⟨hy, hcol, h1, -, -⟩ := hlo τ hτ
    rw [← h1]
    exact mem_traceIndex_of_colouring_eq _ hy ηhi hcol
  rw [dsc, dsc, map_sum]
  refine Finset.sum_nbij' (fun τ => τ.erase x₀) (fun σ => insert x₀ σ) hmapsto ?_ ?_ ?_ ?_
  · intro σ hσ
    obtain ⟨y', hy', hcol', htr'⟩ := exists_path_of_mem_traceIndex hσ
    obtain ⟨y, hy, hcl, htr⟩ := exists_colouring_lo_eq ha hb hN hI hŷ hy' hdiag k1 k2 hcol'
    rw [← htr', ← htr, ← hins _ hy hcl]
    exact mem_traceIndex_of_colouring_eq _ hy ηlo hcl
  · intro τ hτ
    obtain ⟨-, -, -, h2, -⟩ := hlo τ hτ
    exact Finset.insert_erase h2
  · intro σ hσ
    obtain ⟨y', hy', hcol', htr'⟩ := exists_path_of_mem_traceIndex hσ
    rw [← htr']
    exact Finset.erase_insert (hx₀not y')
  · intro τ hτ
    obtain ⟨hy, hcol, h1, h2, h3⟩ := hlo τ hτ
    obtain ⟨hz1, hz2, hz3⟩ := traceRep_spec (hmapsto τ hτ)
    rw [h3, Module.End.mul_apply,
      partialSweepWord_eq_of_levelTrace_eq q u ha hN hy hz1 (by rw [h1, hz3])]

end Assembly

/-! ### The three rules -/

section Rules

/-- At an event of type `A`, `C` or `D` the path is level with or under the swept point on the left
and level with or over it on the right — which is what rules `A`, `C` and `D` need and what the
types `B` and `E` fail. -/
theorem ht_lt_or_ht_succ_eq_of_eventType (ha : 0 < a) {y : Heights a b N} {X Y : ℕ}
    (hPsw : (X, Y) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.A ∨ eventType y (X, Y) = EventType.C ∨
      eventType y (X, Y) = EventType.D) :
    ht y X < Y ∨ ht y (X + 1) = Y := by
  obtain ⟨h1', h2', h3'⟩ := mem_sweptRegion.1 hPsw
  have h1 : X ≤ a * N := h1'
  have h2 : b * X ≤ a * Y := h2'
  have h3 : Y ≤ ht y (X + 1) := h3'
  rcases eq_or_lt_of_le h1 with hXeq | hXlt
  · right
    have hYeq : Y = b * N := by
      have hle : a * (b * N) ≤ a * Y := by
        calc a * (b * N) = b * (a * N) := by ring
        _ = b * X := by rw [hXeq]
        _ ≤ a * Y := h2
      have := Nat.le_of_mul_le_mul_left hle ha
      have := ht_le_mul y (X + 1)
      omega
    rw [ht_of_gt y (show a * N < X + 1 by omega)]
    omega
  · simp only [eventType] at hev
    split_ifs at hev <;>
      first
        | (left; omega)
        | (right; omega)
        | exact absurd hev (by decide)

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **Mellit, Theorem 4.2, rule A.** -/
@[hjo "lem_mellit_thm42_a"]
theorem dsc_lo_eq_dplus_dsc_hi (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {P : ℕ × ℕ} {ηlo ηhi : ℚ} (hlo : IsAdmissibleLevel ηlo) (hhi : IsAdmissibleLevel ηhi)
    (hPlo : ηlo < ((pointRank a b N P : ℤ) : ℚ)) (hPhi : ((pointRank a b N P : ℤ) : ℚ) < ηhi)
    (hiso : ∀ Q : ℕ × ℕ, Q.1 ≤ a * N → Q.2 ≤ b * N →
      ηlo < ((pointRank a b N Q : ℤ) : ℚ) → ((pointRank a b N Q : ℤ) : ℚ) < ηhi →
      pointRank a b N Q = pointRank a b N P)
    {ŷ : Heights a b N} (hŷ : IsAboveDiagonal ŷ) (hPsw : P ∈ sweptRegion ŷ)
    (hev : eventType ŷ P = EventType.A) :
    dsc q u a b N ηlo (colouring ŷ ηlo) =
      dplus q (sweepWidth ŷ P) (dsc q u a b N ηhi (colouring ŷ ηhi)) := by
  obtain ⟨X, Y⟩ := P
  obtain ⟨hx', hd', hy2'⟩ := mem_sweptRegion.1 hPsw
  have hx : X ≤ a * N := hx'
  have hy2 : Y ≤ ht ŷ (X + 1) := hy2'
  have hI : Isolates a b N X Y ηlo ηhi :=
    ⟨hlo, hhi, hPlo, hPhi, hiso, hx, le_trans hy2 (ht_le_mul ŷ _)⟩
  rw [dsc_lo_eq_sweepOperator_dsc_hi q u ha hb hN hI hŷ hPsw
    (ht_lt_or_ht_succ_eq_of_eventType ha hPsw (Or.inl hev))]
  simp only [sweepOperator, hev]

/-- **Mellit, Theorem 4.2, rule C.** -/
@[hjo "lem_mellit_thm42_c"]
theorem dsc_lo_eq_corner_dsc_hi (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {P : ℕ × ℕ} {ηlo ηhi : ℚ} (hlo : IsAdmissibleLevel ηlo) (hhi : IsAdmissibleLevel ηhi)
    (hPlo : ηlo < ((pointRank a b N P : ℤ) : ℚ)) (hPhi : ((pointRank a b N P : ℤ) : ℚ) < ηhi)
    (hiso : ∀ Q : ℕ × ℕ, Q.1 ≤ a * N → Q.2 ≤ b * N →
      ηlo < ((pointRank a b N Q : ℤ) : ℚ) → ((pointRank a b N Q : ℤ) : ℚ) < ηhi →
      pointRank a b N Q = pointRank a b N P)
    {ŷ : Heights a b N} (hŷ : IsAboveDiagonal ŷ) (hPsw : P ∈ sweptRegion ŷ)
    (hev : eventType ŷ P = EventType.C) :
    dsc q u a b N ηlo (colouring ŷ ηlo) =
      q ^ (-(sweepRight ŷ P : ℤ)) •
        corner q (sweepWidth ŷ P) (dsc q u a b N ηhi (colouring ŷ ηhi)) := by
  obtain ⟨X, Y⟩ := P
  obtain ⟨hx', hd', hy2'⟩ := mem_sweptRegion.1 hPsw
  have hx : X ≤ a * N := hx'
  have hy2 : Y ≤ ht ŷ (X + 1) := hy2'
  have hI : Isolates a b N X Y ηlo ηhi :=
    ⟨hlo, hhi, hPlo, hPhi, hiso, hx, le_trans hy2 (ht_le_mul ŷ _)⟩
  rw [dsc_lo_eq_sweepOperator_dsc_hi q u ha hb hN hI hŷ hPsw
    (ht_lt_or_ht_succ_eq_of_eventType ha hPsw (Or.inr (Or.inl hev)))]
  simp only [sweepOperator, hev, LinearMap.smul_apply]

/-- **Mellit, Theorem 4.2, rule D.** -/
@[hjo "lem_mellit_thm42_d"]
theorem dsc_lo_eq_qpow_dsc_hi (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {P : ℕ × ℕ} {ηlo ηhi : ℚ} (hlo : IsAdmissibleLevel ηlo) (hhi : IsAdmissibleLevel ηhi)
    (hPlo : ηlo < ((pointRank a b N P : ℤ) : ℚ)) (hPhi : ((pointRank a b N P : ℤ) : ℚ) < ηhi)
    (hiso : ∀ Q : ℕ × ℕ, Q.1 ≤ a * N → Q.2 ≤ b * N →
      ηlo < ((pointRank a b N Q : ℤ) : ℚ) → ((pointRank a b N Q : ℤ) : ℚ) < ηhi →
      pointRank a b N Q = pointRank a b N P)
    {ŷ : Heights a b N} (hŷ : IsAboveDiagonal ŷ) (hPsw : P ∈ sweptRegion ŷ)
    (hev : eventType ŷ P = EventType.D) :
    dsc q u a b N ηlo (colouring ŷ ηlo) =
      q ^ sweepRight ŷ P • dsc q u a b N ηhi (colouring ŷ ηhi) := by
  obtain ⟨X, Y⟩ := P
  obtain ⟨hx', hd', hy2'⟩ := mem_sweptRegion.1 hPsw
  have hx : X ≤ a * N := hx'
  have hy2 : Y ≤ ht ŷ (X + 1) := hy2'
  have hI : Isolates a b N X Y ηlo ηhi :=
    ⟨hlo, hhi, hPlo, hPhi, hiso, hx, le_trans hy2 (ht_le_mul ŷ _)⟩
  rw [dsc_lo_eq_sweepOperator_dsc_hi q u ha hb hN hI hŷ hPsw
    (ht_lt_or_ht_succ_eq_of_eventType ha hPsw (Or.inr (Or.inr hev)))]
  simp only [sweepOperator, hev, LinearMap.smul_apply, Module.End.one_apply]

/-- **The hypotheses of the three rules are met**, and by one path at once: on the above-diagonal
`(2,3)`-path with height vector `(0, 2, 3)` the swept point `(0, 1)` carries an event of type `C`,
the swept point `(0, 2)` one of type `A`, and the corner `(2, 3)` one of type `D`. A bracketing pair
of admissible levels exists at each of them by `HJO.Mellit.exists_isolating_isAdmissibleLevel`, so
none of the three statements above is vacuous. -/
theorem eventType_example_ACD :
    IsAboveDiagonal (![0, 2, 3] : Heights 2 3 1) ∧
      (((0, 1) : ℕ × ℕ) ∈ sweptRegion (![0, 2, 3] : Heights 2 3 1) ∧
        eventType (![0, 2, 3] : Heights 2 3 1) (0, 1) = EventType.C) ∧
      (((0, 2) : ℕ × ℕ) ∈ sweptRegion (![0, 2, 3] : Heights 2 3 1) ∧
        eventType (![0, 2, 3] : Heights 2 3 1) (0, 2) = EventType.A) ∧
      (((2, 3) : ℕ × ℕ) ∈ sweptRegion (![0, 2, 3] : Heights 2 3 1) ∧
        eventType (![0, 2, 3] : Heights 2 3 1) (2, 3) = EventType.D) := by
  decide

end Rules

end HJO.Mellit
