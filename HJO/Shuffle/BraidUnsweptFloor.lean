/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidCrossingLattice
public import HJO.Shuffle.BraidTypeAObligations
public import HJO.Shuffle.MellitThm58Floor

/-! # The unswept clause of the braid recursions, above the floor

Let `(X, Y)` be a lattice point whose rank is isolated by two admissible levels `η₋ < η₊`, with
`aN < η₋`, and let `P̂` be an above-diagonal path that does not sweep `(X, Y)`. Then the braid
value `π_k(B_{θ,v,α}) d₊^k(1)` of the colouring of `P̂`, with its prefactor, is the same at `η₋`
and at `η₊`. This is clause (U) of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, floored at
`aN`.

Across the drop both halves of the colouring stand still, so the rank `k` is unchanged and every
position rises by one common amount `c = θ(η₊ − η₋)/(a(aN+1)N)`. What remains is:

* **the multiplicities do not move.** `α_i` is the antidiagonal index of the `i`-th crossed east
  step minus that of the `i`-th crossed north step, a function of the two halves alone;
* **no stage position crosses the puncture.** The `j`-th stage position of the `i`-th component is
  the fractional part of the crossing `j` indices below its top one. That crossing is realised by
  a lattice point `(x, y')` of the rectangle with `0 < y' ≤ ŷ_{x+1}`, weakly below the path, and
  the shift by `c` can carry its position across `θ` only if `(x, y' − 1)` has its rank bracketed
  by the two levels, i.e. only if `(x, y') = (X, Y + 1)`. But then `Y < ŷ_{X+1}`, and `(X, Y)`
  lies weakly above the diagonal because its rank exceeds `aN`, so `(X, Y)` would be swept.

So the stage positions straddle nothing, for every multiplicity: the geometric content is the
ordinate bound `y' ≤ ŷ_{x+1}` on the realising point, which is where the level line running below
the path inside a component is spent.

## Main results

* `HJO.Mellit.braidDataOfColouring_snd_eq_of_notMem_sweptRegion` — the multiplicities are
  unchanged.
* `HJO.Mellit.sameSide_iterate_of_notMem_sweptRegion` — no stage position crosses the puncture.
* `HJO.Mellit.braidValueColouring_sweepRecursionUnsweptFloor` — the floored unswept clause.

## References

The objects involved are `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`,
`HJO.Mellit.fract_crossingAbscissa_eq_levelPosition`, `HJO.Mellit.card_componentCrossingIndices_eq`,
`HJO.Mellit.braidDataOfColouring`, `HJO.Paths.sweptRegion`, `HJO.Paths.abovePointRank_injOn`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ} {X Y : ℕ} {ηlo ηhi : ℚ}

/-- A lattice point of the strip `x ≤ aN` whose rank is positive lies weakly above the diagonal:
otherwise `ay − bx ≤ −1` and the rank is at most `x − (aN+1)N < 0`. -/
theorem mul_le_mul_of_pos_pointRank (hN : 0 < N) {x yy : ℕ} (hx : x ≤ a * N)
    (h : (0 : ℚ) < ((pointRank a b N (x, yy) : ℤ) : ℚ)) : b * x ≤ a * yy := by
  by_contra hc
  have hlt : (a : ℚ) * yy + 1 ≤ (b : ℚ) * x := by
    have : a * yy + 1 ≤ b * x := by omega
    exact_mod_cast this
  have hx' : (x : ℚ) ≤ (a : ℚ) * N := by exact_mod_cast hx
  have hN' : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have hM : (0 : ℚ) ≤ ((a : ℚ) * N + 1) * N := by positivity
  rw [cast_pointRank_eq'] at h
  have hneg : ((a : ℚ) * N + 1) * N * ((a : ℚ) * yy - (b : ℚ) * x)
      ≤ -(((a : ℚ) * N + 1) * N) := by nlinarith
  nlinarith

/-- **At an unswept drop the multiplicities of the special-braid data do not move.** Each is the
antidiagonal index of a crossed east step minus that of a crossed north step
(`HJO.Mellit.card_componentCrossingIndices_eq`), and both halves of the colouring stand still. -/
theorem braidDataOfColouring_snd_eq_of_notMem_sweptRegion (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηa : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hsw : (X, Y) ∉ sweptRegion y) (k : ℕ)
    (hk : k = #(colouringEast y ηhi)) :
    (braidDataOfColouring a b N y ηlo k).2 = (braidDataOfColouring a b N y ηhi k).2 := by
  have hηa' : ((a * N : ℕ) : ℚ) < ηhi := hηa.trans (hI.ltP.trans hI.Plt)
  have hE := colouringEast_eq_of_notMem_sweptRegion ha hb hN hI hy hsw
  have hNo := colouringNorth_eq_of_notMem_sweptRegion ha hb hN hI hy hsw
  have hcard := card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηa' hy
  funext i
  have hi : (i : ℕ) < #(colouringNorth y ηhi) := hcard ▸ hk ▸ i.isLt
  have hilo : (i : ℕ) < #(colouringNorth y ηlo) := hNo ▸ hi
  have hlo := card_componentCrossingIndices_eq ha hb hN hI.lo hηa hy hilo
  have hhi := card_componentCrossingIndices_eq ha hb hN hI.hi hηa' hy hi
  rw [hE, hNo] at hlo
  rw [braidDataOfColouring_snd, braidDataOfColouring_snd]
  exact_mod_cast hlo.trans hhi.symm

/-- **At an unswept drop no stage position of the move sequence crosses the puncture.** For every
component `i` and every `j ≤ α_i − 1`, the `j`-th iterate of `nx_θ` at the upper position `v_i` and
its shift by `HJO.Mellit.levelDropShift` lie on the same side of `θ`.

The iterate is the fractional part of the crossing `j` indices below the top one
(`HJO.Mellit.iterate_nextCrossing_fract_crossingAbscissa`), which is the normalised rank of a
lattice point `(x, y')` with `0 < y' ≤ ŷ_{x+1}`
(`HJO.Mellit.exists_pointRank_of_le_componentTopIndex`). By
`HJO.Mellit.sameSide_levelDropShift_of_ne` the shift is harmless unless `(x, y') = (X, Y + 1)`, and
that would put `(X, Y)` in the swept region. -/
theorem sameSide_iterate_of_notMem_sweptRegion (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηa : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hsw : (X, Y) ∉ sweptRegion y) {k : ℕ}
    (hk : k = #(colouringEast y ηhi)) (i : Fin k) (j : ℕ)
    (hj : j ≤ (braidDataOfColouring a b N y ηhi k).2 i - 1) :
    SameSide (sweepTheta a b N) (levelDropShift a b N ηlo ηhi)
      ((nextCrossing (sweepTheta a b N))^[j] ((braidDataOfColouring a b N y ηhi k).1 i)) := by
  have hηa' : ((a * N : ℕ) : ℚ) < ηhi := hηa.trans (hI.ltP.trans hI.Plt)
  have hηpos : 0 < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηa'
  have hcard := card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηa' hy
  have hi : (i : ℕ) < #(colouringNorth y ηhi) := hcard ▸ hk ▸ i.isLt
  have hbt := componentBotIndex_le_componentTopIndex ha hb hN hI.hi hηa' hy hi
  rw [braidDataOfColouring_snd, componentCrossingIndices_eq_Icc, Int.card_Icc] at hj
  have hj' : componentBotIndex a b N y ηhi i ≤ componentTopIndex a b N y ηhi i - (j : ℤ) := by
    omega
  rw [braidDataOfColouring_fst,
    iterate_nextCrossing_fract_crossingAbscissa ha hb hN hI.hi hηpos y i hj']
  obtain ⟨x, yy, -, hx, hyy0, hyyht, -, hfr⟩ :=
    exists_pointRank_of_le_componentTopIndex ha hb hN hI.hi hηa' hy hi hj' (by omega)
  rw [hfr]
  refine sameSide_levelDropShift_of_ne ha hb hN hI hx.le
    ((hyyht.trans (ht_le_mul y _)).trans (Nat.le_succ _)) hyy0 ?_
  intro hxy
  obtain ⟨hxX, hyY⟩ := Prod.mk.inj hxy
  subst hxX hyY
  apply hsw
  have hpos : (0 : ℚ) < ((pointRank a b N (x, Y) : ℤ) : ℚ) :=
    (lt_of_le_of_lt (Nat.cast_nonneg _) hηa).trans hI.ltP
  have hYle : Y ≤ ht y (x + 1) := by omega
  exact Paths.mem_sweptRegion.2 ⟨hI.xle, mul_le_mul_of_pos_pointRank hN hI.xle hpos, hYle⟩

/-- **The braid value is unchanged across an unswept drop above the floor `aN`**, for every
multiplicity. `HJO.Mellit.braidValueColouring_eq_of_notMem_sweptRegion` with its two obligations
discharged by `HJO.Mellit.braidDataOfColouring_snd_eq_of_notMem_sweptRegion` and
`HJO.Mellit.sameSide_iterate_of_notMem_sweptRegion`. -/
theorem braidValueColouring_eq_of_notMem_sweptRegion_floor (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηa : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hsw : (X, Y) ∉ sweptRegion y) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi) :=
  braidValueColouring_eq_of_notMem_sweptRegion q u hq hq1 hqp hr ha hb hN hI
    (lt_of_le_of_lt (Nat.cast_nonneg _) hηa) hy hsw
    (braidDataOfColouring_snd_eq_of_notMem_sweptRegion ha hb hN hI hηa hy hsw _ rfl)
    (sameSide_iterate_of_notMem_sweptRegion ha hb hN hI hηa hy hsw rfl)

/-- **Clause (U) of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, above the floor `aN`**:
the braid value of a colouring satisfies `HJO.Mellit.SweepRecursionUnsweptFloor`. -/
theorem braidValueColouring_sweepRecursionUnsweptFloor (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) {a b N : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (_hab : a < b) :
    SweepRecursionUnsweptFloor a b N (braidValueColouring q u hq hq1 hqp hr a b N) :=
  fun _ _ _ _ hηa hI _ hy hsw =>
    braidValueColouring_eq_of_notMem_sweptRegion_floor q u hq hq1 hqp hr ha hb hN hI hηa hy hsw

end HJO.Mellit

end
