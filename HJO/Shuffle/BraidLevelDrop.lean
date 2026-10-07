/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ColouringInversions
public import HJO.Shuffle.MellitThm42
public import HJO.Shuffle.SweepEventCounts
public import HJO.Shuffle.BraidSpecial
public meta import HJO.Attr

/-! # Moving a colouring's special-braid data down one admissible level

`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` asks how the special-braid data of
`HJO.Mellit.braidDataOfColouring` changes when the level drops past one lattice point `P = (X, Y)` —
the missing half of `HJO.Mellit.braidValueColouring_eq_dsc_floor`, whose four cited recursions
`HJO.Mellit.dsc_lo_eq_dplus_dsc_hi`, `HJO.Mellit.dsc_lo_eq_corner_dsc_hi`,
`HJO.Mellit.dsc_lo_eq_qpow_dsc_hi` and `HJO.Mellit.dsc_eq_dminus_add_smul` are recursions for the
left-hand side alone.

This file answers the combinatorial half of that question, and answers it **uniformly in the event
type**. The whole descent of a colouring past `P` is two `Finset` identities:

* `HJO.Mellit.Isolates.erase_colouringNorth` — the crossed north steps below and above agree once
  `(X, Y - 1)` is removed from the lower one and `(X, Y)` from the upper one;
* `HJO.Mellit.Isolates.erase_colouringEast` — the crossed east steps agree once `(X, Y)` is removed
  from the lower one and `(X - 1, Y)` from the upper one.

Neither mentions the event type: dropping the level past `P` lowers the crossed north step of the
column of `P` by one and shifts the crossed east step of ordinate `Y` one column to the right, and
the event type only decides *which of those four points is a step of the path at all*. So the
per-type statements are corollaries got by evaluating four memberships in `HJO.Paths.northSteps`
and `HJO.Paths.eastSteps`, which is what
`HJO.Mellit.Isolates.colouringNorth_lo_eq_insert_erase_of_eventType_C` and its siblings do.

## What this buys on the braid side

The data is `(v, α)` with `α_i = #X_i(c)` and `v_i` the fractional part of the top crossing. Both
have closed forms already: `HJO.Mellit.componentBotIndex_eq` and
`HJO.Mellit.componentTopIndex_eq` make the crossing-index interval of the `i`-th component run from
`x(u_i) + y(u_i) + 1` to `x(w_i) + y(w_i)`, so

* `HJO.Mellit.card_componentCrossingIndices_eq` — `α_i` is the antidiagonal index of the `i`-th
  crossed east step minus that of the `i`-th crossed north step; and
* `HJO.Mellit.sum_card_componentCrossingIndices` — `∑_i α_i` is a difference of two sums over the
  colouring, with no reference to the pairing at all.

The length of `HJO.Braid.specialMoveList`, i.e. the number of moves of `B_{s,v,α}`, is
`∑_i (α_i - 1) = ∑_i α_i - k`. Combining the last displayed formula with the two descent
identities gives that number's change across one level drop, with no operator theory:

| event | `k` | `∑ α` | moves of `B_{s,v,α}` |
| ----- | --- | ----- | -------------------- |
| `A`   | `+1`| `+1`  | `0` |
| `C`   | `0` | `+1`  | `+1` |
| `D`   | `0` | `+1`  | `+1` |
| `E`   | `0` | `0`   | `0` |

recorded as `HJO.Mellit.Isolates.moveCount_delta_eventType_A` and its siblings. **The type-`A` row
is a check on `HJO.Braid.specialBraid_mul_trainDown_one`, the only braid-side move stated**: that
lemma inserts a point with multiplicity `1`, contributing no letter, and rule `A` applies `d₊` and
no scalar. The type-`C` and type-`D` rows are the content written down nowhere else:
each adds exactly one move, and rule `C` contributes `q^{-a}Δ` and rule `D` the scalar `q^{a}`.

## Hypotheses

`HJO.Mellit.Isolates` is `HJO.Mellit.dsc_lo_eq_dplus_dsc_hi`'s own bundled hypothesis: two
admissible levels bracketing `rk̂(P)` and no other rank of the rectangle. `0 < a`, `0 < b`, `0 < N`
are carried as everywhere in this layer. The one extra fact the per-type corollaries need is
`X < a * N`, and `HJO.Mellit.Isolates.fst_lt` derives it from `aN < ηlo`, which every consumer has:
at `X = a * N` the rank of `(X, Y)` is at most `a * N` for every `Y ≤ b * N`.
-/

@[expose] public section

namespace HJO.Mellit

open Finset ParkingFunctions Paths Sweep

variable {a b N : ℕ}

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The rank comparison away from the isolated point -/

/-- **Away from `P` the two levels compare the same way against every rank.** A lattice point that
changed sides would supply a second rank in the window. This is
`HJO.Mellit.levelIndex_of_isolating` read in rank coordinates rather than level-index ones. -/
theorem cast_pointRank_lt_iff_of_ne (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {Q : ℕ × ℕ} (hQ1 : Q.1 ≤ a * N) (hQ2 : Q.2 ≤ b * N)
    (hne : Q ≠ (X, Y)) :
    (((pointRank a b N Q : ℤ) : ℚ) < ηlo ↔ ((pointRank a b N Q : ℤ) : ℚ) < ηhi) := by
  refine ⟨fun h => h.trans (hI.ltP.trans hI.Plt), fun h => ?_⟩
  by_contra hcon
  have hgt : ηlo < ((pointRank a b N Q : ℤ) : ℚ) :=
    lt_of_le_of_ne (not_lt.1 hcon)
      (Ne.symm (cast_pointRank_ne_of_isAdmissibleLevel hI.lo a b N Q))
  exact hne (pointRank_inj_of_le ha hN hQ1 hI.xle (hI.iso Q hQ1 hQ2 hgt h))

/-- **A lattice point outranked by `P` is under the lower level.** It is below the upper one because
it is below `P`, and the isolation leaves it no room in between. -/
theorem cast_pointRank_lt_lo (ha : 0 < a) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    {Q : ℕ × ℕ} (hQ1 : Q.1 ≤ a * N) (hQ2 : Q.2 ≤ b * N)
    (hlt : pointRank a b N Q < pointRank a b N (X, Y)) :
    ((pointRank a b N Q : ℤ) : ℚ) < ηlo := by
  have hlt' : ((pointRank a b N Q : ℤ) : ℚ) < ((pointRank a b N (X, Y) : ℤ) : ℚ) := by
    exact_mod_cast hlt
  refine (hI.cast_pointRank_lt_iff_of_ne ha hN hQ1 hQ2 ?_).2 (hlt'.trans hI.Plt)
  intro hQ
  rw [hQ] at hlt
  exact absurd hlt (lt_irrefl _)

/-- **A lattice point outranking `P` is over the upper level**, by the same argument read
upwards. -/
theorem lt_cast_pointRank_hi (ha : 0 < a) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    {Q : ℕ × ℕ} (hQ1 : Q.1 ≤ a * N) (hQ2 : Q.2 ≤ b * N)
    (hlt : pointRank a b N (X, Y) < pointRank a b N Q) :
    ηhi < ((pointRank a b N Q : ℤ) : ℚ) := by
  have hlt' : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ((pointRank a b N Q : ℤ) : ℚ) := by
    exact_mod_cast hlt
  have hne : Q ≠ (X, Y) := by
    intro hQ
    rw [hQ] at hlt
    exact absurd hlt (lt_irrefl _)
  have hnl : ¬ ((pointRank a b N Q : ℤ) : ℚ) < ηlo := fun h =>
    absurd (h.trans hI.ltP) (not_lt.2 hlt'.le)
  have hnh : ¬ ((pointRank a b N Q : ℤ) : ℚ) < ηhi :=
    fun h => hnl ((hI.cast_pointRank_lt_iff_of_ne ha hN hQ1 hQ2 hne).2 h)
  exact lt_of_le_of_ne (not_lt.1 hnh)
    (cast_pointRank_ne_of_isAdmissibleLevel hI.hi a b N Q).symm

/-- **The head of the north step with foot `(X, Y - 1)` is `(X, Y)`**, in rank coordinates: the
attack window is exactly the rank increment of one north step. This is the identity that makes the
point one below `P` the one whose *head* is `P`, and so the only crossed north step the descent can
create. -/
theorem pointRank_pred_add_attackWindow (a b N X : ℕ) {Y : ℕ} (hY : 0 < Y) :
    pointRank a b N (X, Y - 1) + (attackWindow a N : ℤ) = pointRank a b N (X, Y) := by
  have h := abovePointRank_succ a b N X (Y - 1)
  rw [show Y - 1 + 1 = Y from by omega] at h
  exact h.symm

/-- The same identity over `ℚ`, where the levels live. -/
theorem cast_pointRank_pred_add_attackWindow (a b N X : ℕ) {Y : ℕ} (hY : 0 < Y) :
    ((pointRank a b N (X, Y - 1) : ℤ) : ℚ) + ((attackWindow a N : ℕ) : ℚ)
      = ((pointRank a b N (X, Y) : ℤ) : ℚ) := by
  rw [← pointRank_pred_add_attackWindow a b N X hY]
  push_cast
  ring

/-! ### The isolated point is inside the rectangle -/

/-- **The isolated point is not in the last column**, once the lower level is above `aN`: at
`X = aN` the rank of `(X, Y)` is at most `aN` for every ordinate of the rectangle, so no level
above `aN` can sit below it. Every consumer of this layer carries `aN < η`. -/
theorem fst_lt (hI : Isolates a b N X Y ηlo ηhi)
    (hηa : ((a * N : ℕ) : ℚ) < ηlo) : X < a * N := by
  rcases lt_or_ge X (a * N) with h | h
  · exact h
  · exfalso
    have hX : X = a * N := le_antisymm hI.xle h
    have hY : (Y : ℚ) ≤ ((b * N : ℕ) : ℚ) := by exact_mod_cast hI.yle
    have hrk := cast_pointRank_eq a b N X Y
    have hMa : (0 : ℚ) ≤ (((a * N + 1) * N * a : ℕ) : ℚ) := Nat.cast_nonneg _
    have hprod : (((a * N + 1) * N * a : ℕ) : ℚ) * (Y : ℚ)
        ≤ (((a * N + 1) * N * a : ℕ) : ℚ) * ((b * N : ℕ) : ℚ) :=
      mul_le_mul_of_nonneg_left hY hMa
    have hkey : ((pointRank a b N (X, Y) : ℤ) : ℚ) ≤ ((a * N : ℕ) : ℚ) := by
      rw [hrk, hX]
      push_cast at hprod ⊢
      linarith [hprod]
    exact absurd (hηa.trans hI.ltP) (not_lt.2 hkey)

/-- **The isolated point is not on the bottom row**, once the lower level is nonnegative: the rank
of `(X, 0)` is at most `0`. -/
theorem pos_snd (hb : 0 < b) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    (hηa : (0 : ℚ) ≤ ηlo) : 0 < Y := by
  rcases Nat.eq_zero_or_pos Y with rfl | h
  · exfalso
    have hX : (0 : ℚ) ≤ (X : ℚ) := Nat.cast_nonneg _
    have h1 : (1 : ℚ) ≤ (((a * N + 1) * N * b : ℕ) : ℚ) := by
      have : 1 ≤ (a * N + 1) * N * b := Nat.one_le_iff_ne_zero.2 (by positivity)
      exact_mod_cast this
    have hkey : ((pointRank a b N (X, 0) : ℤ) : ℚ) ≤ 0 := by
      rw [cast_pointRank_eq a b N X 0]
      have hmul : (0 : ℚ) ≤ ((((a * N + 1) * N * b : ℕ) : ℚ) - 1) * (X : ℚ) :=
        mul_nonneg (by linarith) hX
      push_cast at hmul ⊢
      linarith [hmul]
    exact absurd (hηa.trans_lt hI.ltP) (not_lt.2 hkey)
  · exact h

/-! ### The crossed north steps away from the two moving points -/

/-- **Away from the column of `P` — and, in that column, away from the two ordinates `Y` and
`Y - 1` — the crossed north steps do not move.** Both the foot and the head of the step have to
stay on the same side of the level, which is two applications of
`HJO.Mellit.Isolates.le_levelIndex_iff_of_ne`. -/
theorem mem_colouringNorth_iff_of_ne (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) {x i : ℕ}
    (h1 : (x, i) ≠ (X, Y)) (h2 : (x, i + 1) ≠ (X, Y)) :
    ((x, i) ∈ colouringNorth y ηlo ↔ (x, i) ∈ colouringNorth y ηhi) := by
  rw [mem_colouringNorth_iff ha hN hI.lo, mem_colouringNorth_iff ha hN hI.hi]
  by_cases hx : x < a * N
  · by_cases hi : i < ht y (x + 1)
    · have hib : i ≤ b * N := le_trans hi.le (ht_le_mul y _)
      have hib' : i + 1 ≤ b * N := le_trans hi (ht_le_mul y _)
      have e1 := hI.le_levelIndex_iff_of_ne ha hN hx.le hib h1
      have e2 := hI.le_levelIndex_iff_of_ne ha hN hx.le hib' h2
      push_cast at e1 e2
      constructor <;> rintro ⟨-, hA, hB, hC⟩ <;> exact ⟨hx, hA, hB, by omega⟩
    · simp [hi]
  · simp [hx]

/-- **The isolated point is not a crossed north step at the lower level**: its rank is above that
level. -/
@[hjo "lem_braid_colouring_descent"]
theorem notMem_colouringNorth_lo (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) :
    ((X, Y) : ℕ × ℕ) ∉ colouringNorth y ηlo := by
  intro h
  exact absurd (Finset.mem_filter.1 h).2.1 (not_lt.2 hI.ltP.le)

/-- **The point one below the isolated point is not a crossed north step at the upper level**: its
head is `(X, Y)`, whose rank is below that level. -/
@[hjo "lem_braid_colouring_descent"]
theorem notMem_colouringNorth_pred_hi (hI : Isolates a b N X Y ηlo ηhi) (hY : 0 < Y)
    (y : Heights a b N) : ((X, Y - 1) : ℕ × ℕ) ∉ colouringNorth y ηhi := by
  intro h
  have hup : ηhi < ((pointRank a b N (X, Y - 1) : ℤ) : ℚ) + ((attackWindow a N : ℕ) : ℚ) :=
    (Finset.mem_filter.1 h).2.2
  rw [cast_pointRank_pred_add_attackWindow a b N X hY] at hup
  exact absurd hup (not_lt.2 hI.Plt.le)

/-- **The whole descent of the crossed north steps.** Erasing `(X, Y - 1)` below and `(X, Y)`
above leaves the same set: no other north step changes side, `(X, Y)` is never crossed below, and
`(X, Y - 1)` is never crossed above. The event type is nowhere used — it only decides which of the
two points is a north step of the path at all. -/
@[hjo "lem_braid_colouring_descent"]
theorem erase_colouringNorth (ha : 0 < a) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    (y : Heights a b N) :
    (colouringNorth y ηlo).erase (X, Y - 1) = (colouringNorth y ηhi).erase (X, Y) := by
  ext u
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hu1, hu2⟩
    have hne : u ≠ (X, Y) := fun h => (hI.notMem_colouringNorth_lo y) (h ▸ hu2)
    have hne2 : (u.1, u.2 + 1) ≠ (X, Y) := by
      intro h
      rw [Prod.ext_iff] at h
      exact hu1 (Prod.ext h.1 (by omega))
    refine ⟨hne, ?_⟩
    have := hI.mem_colouringNorth_iff_of_ne ha hN y (x := u.1) (i := u.2) hne hne2
    exact this.1 hu2
  · rintro ⟨hu1, hu2⟩
    rcases Nat.eq_zero_or_pos Y with rfl | hY
    · refine ⟨by simpa using hu1, ?_⟩
      have hne2 : (u.1, u.2 + 1) ≠ (X, 0) := by simp only [ne_eq, Prod.ext_iff]; omega
      exact (hI.mem_colouringNorth_iff_of_ne ha hN y (x := u.1) (i := u.2) hu1 hne2).2 hu2
    · have hne : u ≠ (X, Y - 1) := fun h =>
        (hI.notMem_colouringNorth_pred_hi hY y) (h ▸ hu2)
      have hne2 : (u.1, u.2 + 1) ≠ (X, Y) := by
        intro h
        rw [Prod.ext_iff] at h
        exact hne (Prod.ext h.1 (by omega))
      exact ⟨hne, (hI.mem_colouringNorth_iff_of_ne ha hN y (x := u.1) (i := u.2) hu1 hne2).2 hu2⟩

/-- **The point one below the isolated point is crossed at the lower level exactly when it is a
north step of the path.** Its foot is under the lower level because it is outranked by `(X, Y)`,
and its head is `(X, Y)`, which is above that level. So the event type enters only through the
membership on the right. -/
@[hjo "lem_braid_colouring_descent"]
theorem mem_colouringNorth_pred_lo_iff (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hY : 0 < Y) (y : Heights a b N) :
    ((X, Y - 1) : ℕ × ℕ) ∈ colouringNorth y ηlo ↔ ((X, Y - 1) : ℕ × ℕ) ∈ northSteps y := by
  have hstep := pointRank_pred_add_attackWindow a b N X (Y := Y) hY
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
  refine ⟨fun h => (Finset.mem_filter.1 h).1, fun h => Finset.mem_filter.2 ⟨h, ?_, ?_⟩⟩
  · refine hI.cast_pointRank_lt_lo ha hN hI.xle (by have := hI.yle; omega) ?_
    omega
  · show ηlo < ((pointRank a b N (X, Y - 1) : ℤ) : ℚ) + ((attackWindow a N : ℕ) : ℚ)
    rw [cast_pointRank_pred_add_attackWindow a b N X hY]
    exact hI.ltP

/-! ### The crossed east steps away from the two moving points -/

/-- **Away from the two columns the crossed east steps do not move.** An east step is crossed when
its own rank is above the level and the rank one column to the right is below it; both comparisons
are away from `P`. -/
theorem mem_colouringEast_iff_of_ne (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) {x i : ℕ}
    (h1 : (x, i) ≠ (X, Y)) (h2 : (x + 1, i) ≠ (X, Y)) :
    ((x, i) ∈ colouringEast y ηlo ↔ (x, i) ∈ colouringEast y ηhi) := by
  rw [mem_colouringEast_iff ha hN hI.lo, mem_colouringEast_iff ha hN hI.hi]
  by_cases hx : x < a * N
  · by_cases hi : i = ht y (x + 1)
    · have hib : i ≤ b * N := hi ▸ ht_le_mul y _
      have e1 := hI.le_levelIndex_iff_of_ne ha hN hx.le hib h1
      have e2 := hI.le_levelIndex_iff_of_ne ha hN (by omega : x + 1 ≤ a * N) hib h2
      constructor <;> rintro ⟨-, hA, hB, hC⟩ <;> exact ⟨hx, hA, by omega, by omega⟩
    · simp [hi]
  · simp [hx]

/-- **The isolated point is not a crossed east step at the upper level**: a crossed east step
outranks the level, and `(X, Y)` does not outrank `ηhi`. -/
@[hjo "lem_braid_colouring_descent"]
theorem notMem_colouringEast_hi (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) :
    ((X, Y) : ℕ × ℕ) ∉ colouringEast y ηhi := by
  intro h
  exact absurd (Finset.mem_filter.1 h).2.2 (not_lt.2 hI.Plt.le)

/-- **The point one column left of the isolated point is not a crossed east step at the lower
level**: the rank one column to its right is `rk̂(X, Y)`, which is above that level. -/
@[hjo "lem_braid_colouring_descent"]
theorem notMem_colouringEast_pred_lo (hI : Isolates a b N X Y ηlo ηhi) (hX : 0 < X)
    (y : Heights a b N) : ((X - 1, Y) : ℕ × ℕ) ∉ colouringEast y ηlo := by
  intro h
  have hdown : ((pointRank a b N (X - 1 + 1, Y) : ℤ) : ℚ) < ηlo := (Finset.mem_filter.1 h).2.1
  rw [show X - 1 + 1 = X from by omega] at hdown
  exact absurd hdown (not_lt.2 hI.ltP.le)

/-- **The whole descent of the crossed east steps.** Erasing `(X, Y)` below and `(X - 1, Y)` above
leaves the same set: dropping the level past `P` moves the crossed east step of ordinate `Y` one
column to the right, and nothing else changes. Again the event type is nowhere used. -/
@[hjo "lem_braid_colouring_descent"]
theorem erase_colouringEast (ha : 0 < a) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    (y : Heights a b N) :
    (colouringEast y ηlo).erase (X, Y) = (colouringEast y ηhi).erase (X - 1, Y) := by
  ext v
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hv1, hv2⟩
    have hvne : v ≠ (X - 1, Y) := by
      rcases Nat.eq_zero_or_pos X with rfl | hX
      · simpa using hv1
      · exact fun h => (hI.notMem_colouringEast_pred_lo hX y) (h ▸ hv2)
    have hne2 : (v.1 + 1, v.2) ≠ (X, Y) := by
      intro h
      rw [Prod.ext_iff] at h
      exact hvne (Prod.ext (by omega) h.2)
    exact ⟨hvne, (hI.mem_colouringEast_iff_of_ne ha hN y (x := v.1) (i := v.2) hv1 hne2).1 hv2⟩
  · rintro ⟨hv1, hv2⟩
    have hne : v ≠ (X, Y) := fun h => (hI.notMem_colouringEast_hi y) (h ▸ hv2)
    have hne2 : (v.1 + 1, v.2) ≠ (X, Y) := by
      intro h
      rw [Prod.ext_iff] at h
      exact hv1 (Prod.ext (by omega) h.2)
    exact ⟨hne, (hI.mem_colouringEast_iff_of_ne ha hN y (x := v.1) (i := v.2) hne hne2).2 hv2⟩

/-- **The isolated point is crossed as an east step at the lower level exactly when it is an east
step of the path.** The rank one column to its right is below `ηlo` because it is outranked by
`(X, Y)`, and `(X, Y)` itself outranks `ηlo`. -/
@[hjo "lem_braid_colouring_descent"]
theorem mem_colouringEast_lo_iff (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) :
    ((X, Y) : ℕ × ℕ) ∈ colouringEast y ηlo ↔ ((X, Y) : ℕ × ℕ) ∈ eastSteps y := by
  refine ⟨fun h => (Finset.mem_filter.1 h).1, fun h => Finset.mem_filter.2 ⟨h, ?_, hI.ltP⟩⟩
  have hx : X < a * N := (mem_eastSteps_iff.1 h).1
  exact hI.cast_pointRank_lt_lo ha hN (by omega) hI.yle
    (pointRank_succ_fst_lt ha hb hN X Y)

/-- **The point one column left of the isolated point is crossed as an east step at the upper level
exactly when it is an east step of the path.** The rank one column to its right is `rk̂(X, Y)`,
below `ηhi`, and its own rank outranks `(X, Y)` hence `ηhi`. -/
@[hjo "lem_braid_colouring_descent"]
theorem mem_colouringEast_pred_hi_iff (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : 0 < X) (y : Heights a b N) :
    ((X - 1, Y) : ℕ × ℕ) ∈ colouringEast y ηhi ↔ ((X - 1, Y) : ℕ × ℕ) ∈ eastSteps y := by
  have hdown : ((pointRank a b N (X - 1 + 1, Y) : ℤ) : ℚ) < ηhi := by
    rw [show X - 1 + 1 = X from by omega]
    exact hI.Plt
  refine ⟨fun h => (Finset.mem_filter.1 h).1, fun h => Finset.mem_filter.2 ⟨h, hdown, ?_⟩⟩
  · refine hI.lt_cast_pointRank_hi ha hN (by have := hI.xle; omega) hI.yle ?_
    have h2 := pointRank_succ_fst_lt (a := a) (b := b) (N := N) ha hb hN (X - 1) Y
    rwa [show X - 1 + 1 = X from by omega] at h2

/-- **The isolated point is crossed as a north step at the upper level exactly when it is a north
step of the path.** Its own rank is below `ηhi`, and its head `(X, Y + 1)` outranks `(X, Y)` hence
`ηhi`. The companion of `HJO.Mellit.Isolates.mem_colouringNorth_pred_lo_iff` at the other level. -/
@[hjo "lem_braid_colouring_descent"]
theorem mem_colouringNorth_hi_iff (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) :
    ((X, Y) : ℕ × ℕ) ∈ colouringNorth y ηhi ↔ ((X, Y) : ℕ × ℕ) ∈ northSteps y := by
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
  refine ⟨fun h => (Finset.mem_filter.1 h).1, fun h => Finset.mem_filter.2 ⟨h, hI.Plt, ?_⟩⟩
  have hY : Y + 1 ≤ b * N :=
    le_trans (mem_northSteps_iff.1 h).2.2 (ht_le_mul y _)
  have hstep := pointRank_pred_add_attackWindow a b N X (Y := Y + 1) (by omega)
  rw [show Y + 1 - 1 = Y from by omega] at hstep
  have := hI.lt_cast_pointRank_hi ha hN (Q := (X, Y + 1)) hI.xle hY (by omega)
  rw [show ((pointRank a b N (X, Y + 1) : ℤ) : ℚ)
    = ((pointRank a b N (X, Y) : ℤ) : ℚ) + ((attackWindow a N : ℕ) : ℚ) from by
      rw [← hstep]; push_cast; ring] at this
  exact this

end Isolates

/-! ### The column listing enumerates a column-injective set

Both halves of a colouring are column-injective, so `HJO.Mellit.colStep` restricted to
`Finset.range` of the cardinality is a bijection onto the set. That turns an index-wise sum over
the components — which is how the special-braid data is indexed — into a sum over the colouring,
where the two descent identities above can be read off directly. -/

/-- The column listing of a column-injective set is injective on the index range: distinct indices
give distinct columns. -/
theorem colStep_injOn {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) :
    Set.InjOn (colStep S) ((Finset.range #S : Finset ℕ) : Set ℕ) := by
  intro i hi j hj h
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd (congrArg Prod.fst h) (ne_of_lt (colStep_fst_lt hcol hj hlt))
  · exact heq
  · exact absurd (congrArg Prod.fst h.symm) (ne_of_lt (colStep_fst_lt hcol hi hgt))

/-- **The column listing enumerates the set**: its image over the index range is the set itself. -/
theorem image_range_colStep {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) :
    (Finset.range #S).image (colStep S) = S := by
  refine Finset.eq_of_subset_of_card_le (fun P hP => ?_) ?_
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP
    exact colStep_mem (Finset.mem_range.1 hi)
  · rw [Finset.card_image_of_injOn (colStep_injOn hcol), Finset.card_range]

/-- **A sum over the index range is a sum over the set.** -/
theorem sum_colStep {M : Type*} [AddCommMonoid M] {S : Finset (ℕ × ℕ)}
    (hcol : ColumnInjective S) (f : ℕ × ℕ → M) :
    ∑ i ∈ Finset.range #S, f (colStep S i) = ∑ P ∈ S, f P := by
  have key : ∑ P ∈ (Finset.range #S).image (colStep S), f P
      = ∑ i ∈ Finset.range #S, f (colStep S i) :=
    Finset.sum_image (fun i hi j hj hij =>
      colStep_injOn hcol (by simpa using hi) (by simpa using hj) hij)
  rw [image_range_colStep hcol] at key
  exact key.symm

/-! ### The multiplicities of the data, in closed form -/

/-- **A multiplicity of the special-braid data is a difference of antidiagonal indices**: `α_i` is
`x(w_i) + y(w_i)` minus `x(u_i) + y(u_i)`, the antidiagonal index of the `i`-th crossed east step
minus that of the `i`-th crossed north step.

This is `HJO.Mellit.componentBotIndex_eq` and `HJO.Mellit.componentTopIndex_eq` put together, with
the ordinate of a crossed north step recognised as the level index of its column. Nothing about the
level survives: `α_i` is a function of the colouring alone, which is what makes the descent below
a purely combinatorial statement. -/
@[hjo "lem_braid_descent_move_count"]
theorem card_componentCrossingIndices_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {i : ℕ} (hi : i < #(colouringNorth y η)) :
    (#(componentCrossingIndices a b N y η i) : ℤ) =
      (((colStep (colouringEast y η) i).1 : ℤ) + ((colStep (colouringEast y η) i).2 : ℤ))
        - (((colStep (colouringNorth y η) i).1 : ℤ)
          + ((colStep (colouringNorth y η) i).2 : ℤ)) := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηa
  have hk := card_colouringNorth_eq_card_colouringEast hb hN hη hηa hy
  have hiE : i < #(colouringEast y η) := hk ▸ hi
  have hle := componentBotIndex_le_componentTopIndex ha hb hN hη hηa hy hi
  have hlevel : ((colStep (colouringNorth y η) i).2 : ℤ)
      = levelIndex a b N η (colStep (colouringNorth y η) i).1 :=
    (mem_colouringNorth_spec ha hN hη y (colStep_mem hi)).2.2.2
  have hbot := componentBotIndex_eq ha hb hN hη hηpos y i
  have htop := componentTopIndex_eq ha hb hN hη hηpos hiE
  rw [componentCrossingIndices_eq_Icc, Int.card_Icc, Int.toNat_of_nonneg (by omega)]
  omega

/-- **The total number of crossings of a colouring with the antidiagonal**, `∑_i α_i`: the number of
points the special braid of `HJO.Mellit.braidDataOfColouring` carries, counted with multiplicity. -/
noncomputable def totalCrossings (a b N : ℕ) (y : Heights a b N) (η : ℚ) : ℕ :=
  ∑ i ∈ Finset.range #(colouringNorth y η), #(componentCrossingIndices a b N y η i)

/-- **The total number of crossings reads only the colouring**, as a difference of the antidiagonal
indices of its two halves, with the pairing gone. This is the form the descent identities apply
to. -/
@[hjo "lem_braid_descent_move_count"]
theorem cast_totalCrossings (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    (totalCrossings a b N y η : ℤ)
      = (∑ v ∈ colouringEast y η, ((v.1 : ℤ) + (v.2 : ℤ)))
        - ∑ u ∈ colouringNorth y η, ((u.1 : ℤ) + (u.2 : ℤ)) := by
  have hk := card_colouringNorth_eq_card_colouringEast hb hN hη hηa hy
  rw [totalCrossings, Nat.cast_sum,
    Finset.sum_congr rfl (fun i hi =>
      card_componentCrossingIndices_eq ha hb hN hη hηa hy (Finset.mem_range.1 hi)),
    Finset.sum_sub_distrib,
    sum_colStep (columnInjective_colouringNorth ha hN hη y) (fun P => ((P.1 : ℤ) + (P.2 : ℤ)))]
  congr 1
  rw [hk]
  exact sum_colStep (columnInjective_colouringEast ha hN hη y) (fun P => ((P.1 : ℤ) + (P.2 : ℤ)))

/-- For multiplicities all at least one, `∑_i (α_i - 1) + k = ∑_i α_i`: the truncated subtraction
is honest, so the move count and the width add to the total. -/
theorem sum_sub_one_add {k : ℕ} {α : Fin k → ℕ} (hone : ∀ i, 1 ≤ α i) :
    (∑ i : Fin k, (α i - 1)) + k = ∑ i : Fin k, α i := by
  calc (∑ i : Fin k, (α i - 1)) + k
      = (∑ i : Fin k, (α i - 1)) + ∑ _i : Fin k, 1 := by simp
    _ = ∑ i : Fin k, ((α i - 1) + 1) := Finset.sum_add_distrib.symm
    _ = ∑ i : Fin k, α i := Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hone i)

/-- **The special braid of a colouring has `∑_i α_i - k` moves.** Stated without subtraction: the
length of `HJO.Braid.specialMoveList` at the data of the colouring, plus the width `k`, is the total
number of crossings. So the two numbers tracked by the descent lemmas below — the total crossing
count and the width — determine the number of letters `π_k` is applied to. -/
@[hjo "lem_braid_descent_move_count"]
theorem length_specialMoveList_braidDataOfColouring (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {η : ℚ} (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    (Braid.specialMoveList
        (braidDataOfColouring a b N y η #(colouringNorth y η)).2).length
        + #(colouringNorth y η)
      = totalCrossings a b N y η := by
  rw [Braid.length_specialMoveList,
    sum_sub_one_add (isSpecialBraidData_braidDataOfColouring ha hb hN hη hηa hy).one_le_mult,
    totalCrossings, ← Fin.sum_univ_eq_sum_range
      (fun i => #(componentCrossingIndices a b N y η i)) #(colouringNorth y η)]
  exact Finset.sum_congr rfl fun i _ => braidDataOfColouring_snd a b N y η _ i


/-! ### A point that is not a step of the path is not in the colouring -/

/-- The crossed north steps are north steps, so a point that is not one is not crossed. -/
theorem notMem_colouringNorth_of_notMem_northSteps {y : Heights a b N} {η : ℚ} {P : ℕ × ℕ}
    (h : P ∉ northSteps y) : P ∉ colouringNorth y η :=
  fun hc => h (Finset.mem_filter.1 hc).1

/-- The crossed east steps are east steps, so a point that is not one is not crossed. -/
theorem notMem_colouringEast_of_notMem_eastSteps {y : Heights a b N} {η : ℚ} {P : ℕ × ℕ}
    (h : P ∉ eastSteps y) : P ∉ colouringEast y η :=
  fun hc => h (Finset.mem_filter.1 hc).1

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The event type at the isolated point, read off its coordinates

`HJO.Paths.eventType_eq_A_iff` and its siblings are stated with the point packed into a pair, and
`omega` cannot see the heights through the projections. These four restatements unpack them; each
holds by definitional unfolding of the projections. -/

/-- Type `A` at `(X, Y)`, unpacked. -/
theorem ht_lt_of_eventType_A {y : Heights a b N} {X Y : ℕ}
    (hev : eventType y (X, Y) = EventType.A) :
    ht y X < Y ∧ ¬(X < a * N ∧ Y < ht y (X + 1)) :=
  eventType_eq_A_iff.1 hev

/-- Type `C` at `(X, Y)`, unpacked. -/
theorem ht_lt_of_eventType_C {y : Heights a b N} {X Y : ℕ}
    (hev : eventType y (X, Y) = EventType.C) :
    ht y X < Y ∧ X < a * N ∧ Y < ht y (X + 1) :=
  eventType_eq_C_iff.1 hev

/-- Type `D` at `(X, Y)`, unpacked. -/
theorem ht_eq_of_eventType_D {y : Heights a b N} {X Y : ℕ}
    (hev : eventType y (X, Y) = EventType.D) :
    Y = ht y X ∧ ¬(X < a * N ∧ Y < ht y (X + 1)) :=
  eventType_eq_D_iff.1 hev

/-- Type `E` at `(X, Y)`, unpacked. -/
theorem lt_ht_of_eventType_E {y : Heights a b N} {X Y : ℕ}
    (hev : eventType y (X, Y) = EventType.E) : Y < ht y X :=
  eventType_eq_E_iff.1 hev

/-! ### The descent at each event type

Each of the following is `HJO.Mellit.Isolates.erase_colouringNorth` or
`HJO.Mellit.Isolates.erase_colouringEast` with the four memberships in `HJO.Paths.northSteps` and
`HJO.Paths.eastSteps` evaluated. The event type does nothing else. -/

/-- At an event of type `C` the crossed east steps are unchanged: neither `(X, Y)` nor `(X - 1, Y)`
is an east step of the path, the ordinate `Y` being strictly below `ht y (X + 1)` and strictly above
`ht y X`. -/
theorem colouringEast_eq_of_eventType_C (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.C) :
    colouringEast y ηlo = colouringEast y ηhi := by
  obtain ⟨hht, hX, hht'⟩ := ht_lt_of_eventType_C hev
  have hlo : ((X, Y) : ℕ × ℕ) ∉ colouringEast y ηlo :=
    notMem_colouringEast_of_notMem_eastSteps fun h => by
      have h2 : X < a * N ∧ Y = ht y (X + 1) := mem_eastSteps_iff.1 h
      omega
  have hhi : ((X - 1, Y) : ℕ × ℕ) ∉ colouringEast y ηhi := by
    rcases Nat.eq_zero_or_pos X with hX0 | hX0
    · subst hX0
      simpa using hI.notMem_colouringEast_hi y
    · refine notMem_colouringEast_of_notMem_eastSteps fun h => ?_
      have h2 : X - 1 < a * N ∧ Y = ht y (X - 1 + 1) := mem_eastSteps_iff.1 h
      rw [show X - 1 + 1 = X from by omega] at h2
      omega
  have h := hI.erase_colouringEast ha hN y
  rwa [Finset.erase_eq_self.2 hlo, Finset.erase_eq_self.2 hhi] at h

/-- At an event of type `C` the crossed north step of the column of `P` drops from `(X, Y)` to
`(X, Y - 1)` and nothing else moves. Both points are north steps: the column climbs through the
whole interval from `ht y X` to `ht y (X + 1)`, and `Y` is interior to it. -/
theorem colouringNorth_eq_of_eventType_C (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.C) :
    colouringNorth y ηlo = insert (X, Y - 1) ((colouringNorth y ηhi).erase (X, Y)) := by
  obtain ⟨hht, hX, hht'⟩ := ht_lt_of_eventType_C hev
  have hY : 0 < Y := by omega
  have hmem : ((X, Y - 1) : ℕ × ℕ) ∈ colouringNorth y ηlo := by
    rw [hI.mem_colouringNorth_pred_lo_iff ha hN hY y]
    have hfoot : ht y X ≤ Y - 1 := by omega
    have hhead : Y - 1 < ht y (X + 1) := by omega
    exact mem_northSteps_iff.2 ⟨hX, hfoot, hhead⟩
  rw [← hI.erase_colouringNorth ha hN y, Finset.insert_erase hmem]

/-- The isolated point is a crossed north step at the upper level at an event of type `C`. -/
theorem mem_colouringNorth_hi_of_eventType_C (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.C) :
    ((X, Y) : ℕ × ℕ) ∈ colouringNorth y ηhi := by
  obtain ⟨hht, hX, hht'⟩ := ht_lt_of_eventType_C hev
  have hfoot : ht y X ≤ Y := by omega
  rw [hI.mem_colouringNorth_hi_iff ha hN y]
  exact mem_northSteps_iff.2 ⟨hX, hfoot, hht'⟩

/-- At an event of type `C` the width is unchanged, one crossed north step being replaced by
another one lattice point lower in the same column. -/
theorem card_colouringNorth_of_eventType_C (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.C) :
    #(colouringNorth y ηlo) = #(colouringNorth y ηhi) := by
  obtain ⟨hht, hX, hht'⟩ := ht_lt_of_eventType_C hev
  have hY : 0 < Y := by omega
  have hhi := hI.mem_colouringNorth_hi_of_eventType_C ha hN hev
  have hne : ((X, Y - 1) : ℕ × ℕ) ∉ (colouringNorth y ηhi).erase (X, Y) := fun h =>
    (hI.notMem_colouringNorth_pred_hi hY y) (Finset.mem_of_mem_erase h)
  have hpos : 0 < #(colouringNorth y ηhi) := Finset.card_pos.2 ⟨_, hhi⟩
  rw [hI.colouringNorth_eq_of_eventType_C ha hN hev, Finset.card_insert_of_notMem hne,
    Finset.card_erase_of_mem hhi]
  omega

/-- **At an event of type `C` the total crossing count rises by exactly one.** The crossed north
step of the column of `P` drops one lattice point, so that component's bottom index drops one, so
its multiplicity `α_i` rises by one and no other does. With
`HJO.Mellit.Isolates.card_colouringNorth_of_eventType_C` and
`HJO.Mellit.length_specialMoveList_braidDataOfColouring` this says the special braid of the lower
colouring has exactly one more move than that of the upper one — the braid-side content rule `C` of
`HJO.Mellit.dsc_lo_eq_corner_dsc_hi` has to match, since that rule contributes the corner
`q^{-a}Δ`. -/
@[hjo "lem_braid_descent_move_count"]
theorem totalCrossings_of_eventType_C (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.C) :
    totalCrossings a b N y ηlo = totalCrossings a b N y ηhi + 1 := by
  obtain ⟨hht, hX, hht'⟩ := ht_lt_of_eventType_C hev
  have hY : 0 < Y := by omega
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlo := cast_totalCrossings ha hb hN hI.lo hηlo hy (y := y)
  have hhi := cast_totalCrossings ha hb hN hI.hi hηhi hy (y := y)
  have hhiN := hI.mem_colouringNorth_hi_of_eventType_C ha hN hev
  have hne : ((X, Y - 1) : ℕ × ℕ) ∉ (colouringNorth y ηhi).erase (X, Y) := fun h =>
    (hI.notMem_colouringNorth_pred_hi hY y) (Finset.mem_of_mem_erase h)
  have hYcast : ((Y - 1 : ℕ) : ℤ) = (Y : ℤ) - 1 := by omega
  rw [hI.colouringEast_eq_of_eventType_C ha hN hev,
    hI.colouringNorth_eq_of_eventType_C ha hN hev, Finset.sum_insert hne,
    Finset.sum_erase_eq_sub hhiN] at hlo
  push_cast at hlo
  rw [hYcast] at hlo
  omega

/-- At an event of type `D` the crossed north steps are unchanged: the column of `P` does not climb
at `Y`, so neither `(X, Y)` nor `(X, Y - 1)` is a north step of the path. -/
theorem colouringNorth_eq_of_eventType_D (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X < a * N) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.D) :
    colouringNorth y ηlo = colouringNorth y ηhi := by
  obtain ⟨hht, hout⟩ := ht_eq_of_eventType_D hev
  have hht' : ¬ Y < ht y (X + 1) := fun h => hout ⟨hX, h⟩
  have hlo : ((X, Y - 1) : ℕ × ℕ) ∉ colouringNorth y ηlo :=
    notMem_colouringNorth_of_notMem_northSteps fun h => by
      have h2 : X < a * N ∧ ht y X ≤ Y - 1 ∧ Y - 1 < ht y (X + 1) := mem_northSteps_iff.1 h
      omega
  have hhi : ((X, Y) : ℕ × ℕ) ∉ colouringNorth y ηhi :=
    notMem_colouringNorth_of_notMem_northSteps fun h => by
      have h2 : X < a * N ∧ ht y X ≤ Y ∧ Y < ht y (X + 1) := mem_northSteps_iff.1 h
      omega
  have h := hI.erase_colouringNorth ha hN y
  rwa [Finset.erase_eq_self.2 hlo, Finset.erase_eq_self.2 hhi] at h

/-- At an event of type `D` the crossed east step of ordinate `Y` moves one column right, from
`(X - 1, Y)` to `(X, Y)`: both are east steps of the path, the height being `Y` at both `X` and
`X + 1`. -/
theorem colouringEast_eq_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X < a * N) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) :
    colouringEast y ηlo = insert (X, Y) ((colouringEast y ηhi).erase (X - 1, Y)) := by
  obtain ⟨hht, hout⟩ := ht_eq_of_eventType_D hev
  have hmono : ht y X ≤ ht y (X + 1) := hy.2.2.1 X hX
  have hht' : ht y (X + 1) = Y := by
    have : ¬ Y < ht y (X + 1) := fun h => hout ⟨hX, h⟩
    omega
  have hmem : ((X, Y) : ℕ × ℕ) ∈ colouringEast y ηlo := by
    rw [hI.mem_colouringEast_lo_iff ha hb hN y]
    exact mem_eastSteps_iff.2 ⟨hX, hht'.symm⟩
  rw [← hI.erase_colouringEast ha hN y, Finset.insert_erase hmem]

/-- **At an event of type `D` the isolated point is not in the first column**, on an above-diagonal
path and for a level above `aN`: there `ht y 0 = 0`, so `X = 0` would force `Y = 0` and
`rk̂(0, 0) = 0`, which no level above `aN` can sit below. So the hypothesis `0 < X` the type-`D`
descent needs is automatic. -/
theorem pos_fst_of_eventType_D (hI : Isolates a b N X Y ηlo ηhi)
    (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.D) : 0 < X := by
  rcases Nat.eq_zero_or_pos X with hX0 | hX0
  · exfalso
    obtain ⟨hht, -⟩ := ht_eq_of_eventType_D hev
    have hY : Y = 0 := by rw [hX0, hy.1] at hht; exact hht
    have hrk : ((pointRank a b N (X, Y) : ℤ) : ℚ) = 0 := by
      rw [hX0, hY, cast_pointRank_eq a b N 0 0]
      push_cast
      ring
    have hnn : (0 : ℚ) ≤ ((a * N : ℕ) : ℚ) := Nat.cast_nonneg _
    have hlt := hI.ltP
    rw [hrk] at hlt
    linarith
  · exact hX0

/-- The crossed east step one column left of `P` is present at the upper level at an event of type
`D`: the height at `X` is `Y`, so `(X - 1, Y)` is an east step of the path. -/
theorem mem_colouringEast_pred_hi_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX0 : 0 < X) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.D) :
    ((X - 1, Y) : ℕ × ℕ) ∈ colouringEast y ηhi := by
  obtain ⟨hht, hout⟩ := ht_eq_of_eventType_D hev
  have hcol : X - 1 < a * N := by have := hI.xle; omega
  have hhead : Y = ht y (X - 1 + 1) := by
    rw [show X - 1 + 1 = X from by omega]; exact hht
  rw [hI.mem_colouringEast_pred_hi_iff ha hb hN hX0 y]
  exact mem_eastSteps_iff.2 ⟨hcol, hhead⟩

/-- **At an event of type `D` the total crossing count rises by exactly one**, the width being
unchanged. The crossed east step of the component ending at ordinate `Y` shifts one column right, so
that component's top index rises by one. Rule `D` of `HJO.Mellit.dsc_lo_eq_qpow_dsc_hi` multiplies
by the scalar `q^{a}`, so on the braid side exactly one extra move must be carried to a scalar. -/
@[hjo "lem_braid_descent_move_count"]
theorem totalCrossings_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.D) :
    totalCrossings a b N y ηlo = totalCrossings a b N y ηhi + 1 := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hX0 : 0 < X := hI.pos_fst_of_eventType_D hηlo hy hev
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlo := cast_totalCrossings ha hb hN hI.lo hηlo hy (y := y)
  have hhi := cast_totalCrossings ha hb hN hI.hi hηhi hy (y := y)
  have hhiE := hI.mem_colouringEast_pred_hi_of_eventType_D ha hb hN hX0 hev
  have hne : ((X, Y) : ℕ × ℕ) ∉ (colouringEast y ηhi).erase (X - 1, Y) := fun h =>
    (hI.notMem_colouringEast_hi y) (Finset.mem_of_mem_erase h)
  have hXcast : ((X - 1 : ℕ) : ℤ) = (X : ℤ) - 1 := by omega
  rw [hI.colouringNorth_eq_of_eventType_D ha hN hX hev,
    hI.colouringEast_eq_of_eventType_D ha hb hN hX hy hev, Finset.sum_insert hne,
    Finset.sum_erase_eq_sub hhiE] at hlo
  push_cast at hlo
  rw [hXcast] at hlo
  omega

/-- At an event of type `D` the width is unchanged. -/
theorem card_colouringNorth_of_eventType_D (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X < a * N) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.D) :
    #(colouringNorth y ηlo) = #(colouringNorth y ηhi) := by
  rw [hI.colouringNorth_eq_of_eventType_D ha hN hX hev]

/-- At an event of type `E` — a point strictly below the path — the crossed north steps are
unchanged. -/
theorem colouringNorth_eq_of_eventType_E (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.E) :
    colouringNorth y ηlo = colouringNorth y ηhi := by
  have hht : Y < ht y X := lt_ht_of_eventType_E hev
  have hlo : ((X, Y - 1) : ℕ × ℕ) ∉ colouringNorth y ηlo :=
    notMem_colouringNorth_of_notMem_northSteps fun h => by
      have h2 : X < a * N ∧ ht y X ≤ Y - 1 ∧ Y - 1 < ht y (X + 1) := mem_northSteps_iff.1 h
      omega
  have hhi : ((X, Y) : ℕ × ℕ) ∉ colouringNorth y ηhi :=
    notMem_colouringNorth_of_notMem_northSteps fun h => by
      have h2 : X < a * N ∧ ht y X ≤ Y ∧ Y < ht y (X + 1) := mem_northSteps_iff.1 h
      omega
  have h := hI.erase_colouringNorth ha hN y
  rwa [Finset.erase_eq_self.2 hlo, Finset.erase_eq_self.2 hhi] at h

/-- At an event of type `E` the crossed east steps are unchanged too. At `X = 0` the type is
impossible on an above-diagonal path, the height there being `0`. -/
theorem colouringEast_eq_of_eventType_E (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.E) :
    colouringEast y ηlo = colouringEast y ηhi := by
  have hht : Y < ht y X := lt_ht_of_eventType_E hev
  have hX0 : 0 < X := by
    rcases Nat.eq_zero_or_pos X with hX0 | hX0
    · subst hX0
      rw [hy.1] at hht
      omega
    · exact hX0
  have hlo : ((X, Y) : ℕ × ℕ) ∉ colouringEast y ηlo :=
    notMem_colouringEast_of_notMem_eastSteps fun h => by
      have h2 : X < a * N ∧ Y = ht y (X + 1) := mem_eastSteps_iff.1 h
      have hmono : ht y X ≤ ht y (X + 1) := hy.2.2.1 X h2.1
      omega
  have hhi : ((X - 1, Y) : ℕ × ℕ) ∉ colouringEast y ηhi :=
    notMem_colouringEast_of_notMem_eastSteps fun h => by
      have h2 : X - 1 < a * N ∧ Y = ht y (X - 1 + 1) := mem_eastSteps_iff.1 h
      rw [show X - 1 + 1 = X from by omega] at h2
      omega
  have h := hI.erase_colouringEast ha hN y
  rwa [Finset.erase_eq_self.2 hlo, Finset.erase_eq_self.2 hhi] at h

/-- **At an event of type `E` the total crossing count is unchanged**, both halves of the colouring
standing still. **So at type `E` the whole special-braid data stands still while rule `E` multiplies
the left-hand side by `u`.** That is why type `E` is not a recursion on its own, and why
`HJO.Mellit.dsc_eq_dminus_add_smul` states types `B` and `E` together, as a sum over two paths. -/
@[hjo "lem_braid_descent_move_count"]
theorem totalCrossings_of_eventType_E (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.E) :
    totalCrossings a b N y ηlo = totalCrossings a b N y ηhi := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlo := cast_totalCrossings ha hb hN hI.lo hηlo hy (y := y)
  have hhi := cast_totalCrossings ha hb hN hI.hi hηhi hy (y := y)
  rw [hI.colouringNorth_eq_of_eventType_E ha hN hev,
    hI.colouringEast_eq_of_eventType_E ha hN hy hev] at hlo
  omega

/-- At an event of type `A` the column of `P` gains the crossed north step `(X, Y - 1)`, the path
turning east at `Y`: the width goes up by one, which is the `d₊` of rule `A`. -/
theorem colouringNorth_eq_of_eventType_A (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X < a * N) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A) :
    colouringNorth y ηlo = insert (X, Y - 1) (colouringNorth y ηhi) := by
  obtain ⟨hht, hout⟩ := ht_lt_of_eventType_A hev
  have hsw : Y ≤ ht y (X + 1) := (mem_sweptRegion.1 hPsw).2.2
  have hht' : ht y (X + 1) = Y := by
    have : ¬ Y < ht y (X + 1) := fun h => hout ⟨hX, h⟩
    omega
  have hY : 0 < Y := by omega
  have hhi : ((X, Y) : ℕ × ℕ) ∉ colouringNorth y ηhi :=
    notMem_colouringNorth_of_notMem_northSteps fun h => by
      have h2 : X < a * N ∧ ht y X ≤ Y ∧ Y < ht y (X + 1) := mem_northSteps_iff.1 h
      omega
  have hmem : ((X, Y - 1) : ℕ × ℕ) ∈ colouringNorth y ηlo := by
    rw [hI.mem_colouringNorth_pred_lo_iff ha hN hY y]
    have hfoot : ht y X ≤ Y - 1 := by omega
    have hhead : Y - 1 < ht y (X + 1) := by omega
    exact mem_northSteps_iff.2 ⟨hX, hfoot, hhead⟩
  have h := hI.erase_colouringNorth ha hN y
  rw [Finset.erase_eq_self.2 hhi] at h
  rw [← h, Finset.insert_erase hmem]

/-- At an event of type `A` the crossed east steps gain `(X, Y)`, the east step the path takes at
`P`. -/
theorem colouringEast_eq_of_eventType_A (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X < a * N) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A) :
    colouringEast y ηlo = insert (X, Y) (colouringEast y ηhi) := by
  obtain ⟨hht, hout⟩ := ht_lt_of_eventType_A hev
  have hsw : Y ≤ ht y (X + 1) := (mem_sweptRegion.1 hPsw).2.2
  have hht' : ht y (X + 1) = Y := by
    have : ¬ Y < ht y (X + 1) := fun h => hout ⟨hX, h⟩
    omega
  have hhi : ((X - 1, Y) : ℕ × ℕ) ∉ colouringEast y ηhi := by
    rcases Nat.eq_zero_or_pos X with hX0 | hX0
    · subst hX0
      simpa using hI.notMem_colouringEast_hi y
    · refine notMem_colouringEast_of_notMem_eastSteps fun h => ?_
      have h2 : X - 1 < a * N ∧ Y = ht y (X - 1 + 1) := mem_eastSteps_iff.1 h
      rw [show X - 1 + 1 = X from by omega] at h2
      omega
  have hmem : ((X, Y) : ℕ × ℕ) ∈ colouringEast y ηlo := by
    rw [hI.mem_colouringEast_lo_iff ha hb hN y]
    exact mem_eastSteps_iff.2 ⟨hX, hht'.symm⟩
  have h := hI.erase_colouringEast ha hN y
  rw [Finset.erase_eq_self.2 hhi] at h
  rw [← h, Finset.insert_erase hmem]

/-- **At an event of type `A` the total crossing count rises by one and so does the width, so the
special braid gains no move at all.** The new component has crossed north step `(X, Y - 1)` and
crossed east step `(X, Y)`, whose antidiagonal indices differ by one, so its multiplicity is `α = 1`
and `HJO.Braid.specialMoveList` contributes nothing for it — which is exactly the shape of
`HJO.Braid.specialBraid_mul_trainDown_one`, the insertion of a point that performs no move, and
matches rule `A` of `HJO.Mellit.dsc_lo_eq_dplus_dsc_hi` applying `d₊` and no scalar. -/
@[hjo "lem_braid_descent_move_count"]
theorem totalCrossings_of_eventType_A (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.A) :
    totalCrossings a b N y ηlo = totalCrossings a b N y ηhi + 1 := by
  have hX : X < a * N := hI.fst_lt hηlo
  obtain ⟨hht, hout⟩ := ht_lt_of_eventType_A hev
  have hsw : Y ≤ ht y (X + 1) := (mem_sweptRegion.1 hPsw).2.2
  have hht' : ht y (X + 1) = Y := by
    have : ¬ Y < ht y (X + 1) := fun h => hout ⟨hX, h⟩
    omega
  have hY : 0 < Y := by omega
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlo := cast_totalCrossings ha hb hN hI.lo hηlo hy (y := y)
  have hhi := cast_totalCrossings ha hb hN hI.hi hηhi hy (y := y)
  have hnN : ((X, Y - 1) : ℕ × ℕ) ∉ colouringNorth y ηhi :=
    hI.notMem_colouringNorth_pred_hi hY y
  have hnE : ((X, Y) : ℕ × ℕ) ∉ colouringEast y ηhi := hI.notMem_colouringEast_hi y
  have hYcast : ((Y - 1 : ℕ) : ℤ) = (Y : ℤ) - 1 := by omega
  rw [hI.colouringNorth_eq_of_eventType_A ha hN hX hPsw hev,
    hI.colouringEast_eq_of_eventType_A ha hb hN hX hPsw hev,
    Finset.sum_insert hnN, Finset.sum_insert hnE] at hlo
  push_cast at hlo
  rw [hYcast] at hlo
  omega

/-- **At an event of type `A` the width rises by exactly one**, matching the `d₊` of rule `A`. -/
theorem card_colouringNorth_of_eventType_A (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hX : X < a * N) {y : Heights a b N}
    (hPsw : ((X, Y) : ℕ × ℕ) ∈ sweptRegion y) (hev : eventType y (X, Y) = EventType.A) :
    #(colouringNorth y ηlo) = #(colouringNorth y ηhi) + 1 := by
  obtain ⟨hht, hout⟩ := ht_lt_of_eventType_A hev
  have hsw : Y ≤ ht y (X + 1) := (mem_sweptRegion.1 hPsw).2.2
  have hht' : ht y (X + 1) = Y := by
    have : ¬ Y < ht y (X + 1) := fun h => hout ⟨hX, h⟩
    omega
  have hY : 0 < Y := by omega
  rw [hI.colouringNorth_eq_of_eventType_A ha hN hX hPsw hev,
    Finset.card_insert_of_notMem (hI.notMem_colouringNorth_pred_hi hY y)]

end Isolates

end HJO.Mellit
