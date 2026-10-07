/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidValueColouring
public import HJO.Shuffle.BraidRigidShift
public import HJO.Shuffle.BraidLevelDrop
public import HJO.Shuffle.MellitUnsweptDrop
public import HJO.Shuffle.MellitProp57

/-! # The braid value at an unswept level drop

`HJO.Mellit.SweepRecursionUnswept` is the fourth clause of the level recursion: at a bracketed
lattice point the path does *not* sweep, the invariant is unchanged. It is not among the clauses of
the recursion as usually written — it is needed here because `HJO.Mellit.Isolates` isolates a rank
of the whole rectangle, so the chain of drops has to cross the ranks of points outside the swept
region, where the other three clauses have no instance. This file asks it of the braid value
`HJO.Mellit.braidValueColouring`.

## What is settled

The colouring itself stands still — that is `HJO.Mellit.colouring_eq_of_notMem_sweptRegion`,
already proved. What remains is what the drop does to the *braid data*, which reads the level
directly and not only through the colouring. Three things, all proved here:

* **The braid data is a function of the colouring.** `HJO.Mellit.braidDataOfColouring_congr`: the
  path enters `HJO.Mellit.braidDataOfColouring` only through `colouringNorth` and `colouringEast`,
  and those are the two rank-filters of the colouring (`HJO.Mellit.colouringNorth_congr`,
  `HJO.Mellit.colouringEast_congr`). Hence `HJO.Mellit.braidValueColouring_colouring`: the
  candidate's value at `colouring y η` is the braid value of `y` itself, whatever representative
  `HJO.Mellit.colouringRep` picked. Without this the candidate would be unusable in any clause.
* **Both halves stand still across an unswept drop**, by
  `HJO.Mellit.colouringNorth_eq_of_notMem_sweptRegion` and
  `HJO.Mellit.colouringEast_eq_of_notMem_sweptRegion`, so the rank `k` is the same on both sides.
  The reason is one fact — `HJO.Mellit.cast_pointRank_lt_lo_iff_of_notMem_sweptRegion` — that
  no coloured point has its rank between the two levels: it would then be `(X, Y)` by
  `HJO.Mellit.pointRank_inj_of_le`, and every coloured point of an above-diagonal path is swept
  (`HJO.Mellit.mem_sweptRegion_of_mem_colouring`).
* **The positions rise by one common amount, additively.**
  `HJO.Mellit.braidDataOfColouring_fst_eq_add_of_notMem_sweptRegion`: reading each position as the
  normalised rank of its crossed east step (`HJO.Mellit.fract_crossingAbscissa_eq_levelPosition`)
  and the east half being the same at both levels, `v_i^- = v_i^+ + HJO.Mellit.levelDropShift`,
  with **no fractional part taken**. This is stronger than
  `HJO.Mellit.braidDataOfColouring_fst_eq_fract_add_of_colouringEast_eq`,
  which is the same shift read through `Int.fract`, and it is what makes
  `HJO/Shuffle/BraidRigidShift.lean` applicable: a rotation that provably does not wrap.

## What the clause then reduces to, and what is still owed

`HJO.Mellit.braidValueOfPath_eq_of_notMem_sweptRegion` and
`HJO.Mellit.braidValueColouring_eq_of_notMem_sweptRegion` close the clause at one drop from exactly
two remaining hypotheses, together with `0 < ηlo` (which
`HJO.Mellit.fract_crossingAbscissa_eq_levelPosition` needs and `HJO.Mellit.Isolates` does not
supply):

1. `hmult` — the drop leaves the multiplicities alone.
2. `hside` — no stage position of the move sequence changes which side of the puncture it is on.

Neither is proved here, and it is worth saying precisely what they come to.

*On `hmult`.* `HJO.Mellit.componentCrossingIndices` is the integer interval from
`⌈(1+s)·componentLeft + levelIntercept⌉` to `HJO.Mellit.componentTopIndex`. The top index is
`x(w_i) + y(w_i)` by `HJO.Mellit.componentTopIndex_eq`, hence level-independent once the east half
is fixed. The lower end moves only if some integer `n` has `n·a(aN+1)N − D·x(u_i)` — which is the
rank of the lattice point `(x(u_i), n − x(u_i))` — between the two levels; and the `i`-th crossed
north step `u_i` is crossed at *both* levels, so `rk(u_i) < ηlo` and `ηhi < rk(u_i) + ω`, which
leaves no room for a rank in that column. So `hmult` is expected to be provable outright, with no
appeal to the isolating clause; the arithmetic is not carried out here.

*On `hside`.* This is the real obligation, and it is not formal. Reading positions as normalised
ranks, a stage position `p` straddles the puncture across the drop exactly when the crossing it sits
at has rank `rk(X, Y) + ω = rk(X, Y + 1)` — so the clause asks that `(X, Y + 1)` is never a
move-producing crossing of the colouring when `(X, Y)` is unswept. Where the crossing below it in
its component lies in the same column that is immediate, `(X, Y)` being then a crossing and hence
swept; the open case is a crossing that *wraps*, whose successor lies one column to the left. That
is also the case in which the letter would change from a `z` to a `ỹ`, and
`HJO.Braid.zCount_specialBraid_rotate_sub_card` would then separate the two braids — so a straddle
is not a slack hypothesis, it would refute the clause. An exhaustive search over all above-diagonal
paths and all unswept bracketed points for
`(a,b,N) ∈ {(2,3,1), (2,5,1), (3,4,1), (2,3,2), (3,5,1), (2,7,1), (3,7,1), (4,5,1)}` found no
straddle; that is evidence, not a proof, and it is recorded as such.

## Where the clause holds with nothing owed

Two corollaries, and between them they cover the great majority of the clause's range.

* `HJO.Mellit.braidValueColouring_eq_of_notMem_sweptRegion_of_mult_eq_one` — wherever every
  multiplicity is `1`. There the move sequence is empty, so by
  `HJO.Mellit.braidValueOfData_of_forall_mult_eq_one` the braid value is the bare `d_+^k(1)` and the
  positions, the only thing the drop moves, do not enter at all.
* `HJO.Mellit.braidValueColouring_eq_of_notMem_sweptRegion_of_eq_empty` — wherever the colouring is
  empty, where both sides are `1`. This is the dominant case: in the same search, of the unswept
  bracketed pairs at a unit bracket, 11 of 11, 27 of 27, 52 of 53, 452 of 471, 90 of 92 and 50 of 50
  respectively had empty colouring.

## Genericity

`0 < a`, `0 < b`, `0 < N` for the geometry, and `q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0`, `r * r = q` because
`HJO.Sweep.braidRepMellit` does not exist without them. `u ≠ 0` is *not* spent: the reduction never
evaluates a letter of `HJO.Sweep.braidRep`, it transports one braid to another, and the two
corollaries above are at the identity braid. A clause that actually moves a `z` letter will owe it.

## References

This file contributes to `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, using
`HJO.Mellit.fract_crossingAbscissa_eq_levelPosition`, `HJO.Mellit.sweepTheta_eq_div`,
`HJO.Mellit.Isolates.notMem_colouringNorth_lo`, `HJO.Mellit.card_componentCrossingIndices_eq`,
`HJO.Braid.zCount_mul`, `HJO.Mellit.braidDataOfColouring`, `HJO.Mellit.colouringComponent`,
`HJO.Braid.specialBraid`, `HJO.Paths.sweptRegion`, `HJO.Paths.abovePointRank_injOn`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ} {X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The two halves are read off the colouring -/

/-- Equal colourings have equal north halves. -/
theorem colouringNorth_congr {y z : Heights a b N} {η : ℚ} (h : colouring y η = colouring z η) :
    colouringNorth y η = colouringNorth z η := by
  rw [← filter_colouring_lt, ← filter_colouring_lt, h]

/-- Equal colourings have equal east halves. -/
theorem colouringEast_congr {y z : Heights a b N} {η : ℚ} (h : colouring y η = colouring z η) :
    colouringEast y η = colouringEast z η := by
  rw [← filter_colouring_not_lt, ← filter_colouring_not_lt, h]

/-! ### The braid data of a colouring reads only the colouring -/

/-- **The special-braid data of `HJO.Mellit.braidDataOfColouring` depends on the path only through
the two halves of its colouring.** -/
theorem braidDataOfColouring_congr {y z : Heights a b N} {η : ℚ} (k : ℕ)
    (hn : colouringNorth y η = colouringNorth z η) (he : colouringEast y η = colouringEast z η) :
    braidDataOfColouring a b N y η k = braidDataOfColouring a b N z η k := by
  simp only [braidDataOfColouring, componentTopIndex, componentCrossingIndices, componentLeft,
    componentRight, hn, he]

/-- **The braid value of a path reads only its colouring.** -/
theorem braidValueOfPath_congr (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) {y z : Heights a b N} {η : ℚ} (h : colouring y η = colouring z η) :
    braidValueOfPath q u hq hq1 hqp hr y η = braidValueOfPath q u hq hq1 hqp hr z η := by
  have he := colouringEast_congr h
  rw [braidValueOfPath, braidValueOfPath, he,
    braidDataOfColouring_congr _ (colouringNorth_congr h) he]

/-- **The candidate value at a realized colouring is the braid value of the path itself**: the
representative `HJO.Mellit.colouringRep` chooses is irrelevant. -/
theorem braidValueColouring_colouring (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) {y : Heights a b N} (hy : IsAboveDiagonal y) (η : ℚ) :
    braidValueColouring q u hq hq1 hqp hr a b N η (colouring y η)
      = braidValueOfPath q u hq hq1 hqp hr y η :=
  braidValueOfPath_congr q u hq hq1 hqp hr
    (colouringRep_spec (⟨y, hy, rfl⟩ : IsAdmissibleColouring a b N η (colouring y η))).2

/-! ### An unswept drop moves neither half of the colouring -/

/-- An east step of an above-diagonal path lies in its swept region. -/
theorem mem_sweptRegion_of_mem_eastSteps {y : Heights a b N} (hy : IsAboveDiagonal y)
    {p : ℕ × ℕ} (hp : p ∈ eastSteps y) : p ∈ sweptRegion y := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
  have hx' : x < a * N := Finset.mem_range.1 hx
  exact Paths.mem_sweptRegion.2 ⟨hx'.le,
    (hy.2.2.2 x hx'.le).trans (Nat.mul_le_mul_left a (hy.2.2.1 x hx')), le_rfl⟩

/-- A coloured point of an above-diagonal path lies in its swept region. -/
theorem mem_sweptRegion_of_mem_colouring {y : Heights a b N} (hy : IsAboveDiagonal y) {η : ℚ}
    {p : ℕ × ℕ} (hp : p ∈ colouring y η) : p ∈ sweptRegion y := by
  rcases Finset.mem_union.1 (colouring_subset y η hp) with h | h
  · exact (Paths.mem_sweptRegion_of_mem_northSteps hy h).1
  · exact mem_sweptRegion_of_mem_eastSteps hy h

/-- **At an unswept drop the two levels cut every coloured point on the same side.** This is what
makes both halves of the colouring stand still, and with them the rank `k`. -/
theorem cast_pointRank_lt_lo_iff_of_notMem_sweptRegion (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hsw : (X, Y) ∉ sweptRegion y) {p : ℕ × ℕ} (hp : p ∈ colouring y ηhi) :
    ((pointRank a b N p : ℤ) : ℚ) < ηlo ↔ ((pointRank a b N p : ℤ) : ℚ) < ηhi := by
  refine ⟨fun h => h.trans (hI.ltP.trans hI.Plt), fun h => ?_⟩
  by_contra hcon
  have hlt : ηlo < ((pointRank a b N p : ℤ) : ℚ) :=
    lt_of_le_of_ne (not_lt.1 hcon) (intCast_ne_of_isAdmissibleLevel hI.lo _).symm
  have hsr := mem_sweptRegion_of_mem_colouring hy hp
  obtain ⟨hx, -, hy2⟩ := Paths.mem_sweptRegion.1 hsr
  have hyb : p.2 ≤ b * N := hy2.trans (ht_le_mul y _)
  exact hsw (pointRank_inj_of_le ha hN hx hI.xle (hI.iso p hx hyb hlt h) ▸ hsr)

/-- **The north half of the colouring is unchanged at an unswept drop.** -/
theorem colouringNorth_eq_of_notMem_sweptRegion (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hsw : (X, Y) ∉ sweptRegion y) : colouringNorth y ηlo = colouringNorth y ηhi := by
  rw [← filter_colouring_lt, ← filter_colouring_lt,
    colouring_eq_of_notMem_sweptRegion ha hb hN hI hy hsw]
  exact Finset.filter_congr fun p hp =>
    by simp [cast_pointRank_lt_lo_iff_of_notMem_sweptRegion ha hN hI hy hsw hp]

/-- **The east half of the colouring is unchanged at an unswept drop.** -/
theorem colouringEast_eq_of_notMem_sweptRegion (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hsw : (X, Y) ∉ sweptRegion y) : colouringEast y ηlo = colouringEast y ηhi := by
  rw [← filter_colouring_not_lt, ← filter_colouring_not_lt,
    colouring_eq_of_notMem_sweptRegion ha hb hN hI hy hsw]
  exact Finset.filter_congr fun p hp =>
    by simp [cast_pointRank_lt_lo_iff_of_notMem_sweptRegion ha hN hI hy hsw hp]

/-! ### The rigid shift the drop performs on the positions -/

/-- The common amount `θ(η₊ − η₋)/(a(aN+1)N)` by which a level drop raises every position. -/
def levelDropShift (a b N : ℕ) (ηlo ηhi : ℚ) : ℚ :=
  sweepTheta a b N * ((ηhi - ηlo) / ((a : ℚ) * ((a : ℚ) * N + 1) * N))

theorem levelPosition_eq_add_levelDropShift (ηlo ηhi ρ : ℚ) :
    levelPosition a b N ηlo ρ
      = levelPosition a b N ηhi ρ + levelDropShift a b N ηlo ηhi := by
  have hsplit : ρ - ηlo = (ρ - ηhi) + (ηhi - ηlo) := by ring
  rw [levelPosition, levelPosition, levelDropShift, ← mul_add, ← add_div, ← hsplit]

/-- **At an unswept drop every position rises by the one amount
`HJO.Mellit.levelDropShift`.** No fractional part is taken: the shift is an honest addition, both
levels reading the same crossed east step off the unchanged east half. -/
theorem braidDataOfColouring_fst_eq_add_of_notMem_sweptRegion (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) (hlopos : 0 < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hsw : (X, Y) ∉ sweptRegion y) {k : ℕ} (i : Fin k)
    (hi : (i : ℕ) < #(colouringEast y ηhi)) :
    (braidDataOfColouring a b N y ηlo k).1 i
      = (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi := by
  have hE := colouringEast_eq_of_notMem_sweptRegion ha hb hN hI hy hsw
  have hhipos : 0 < ηhi := hlopos.trans (hI.ltP.trans hI.Plt)
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.lo hlopos i (by rwa [hE]),
    braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos i hi, hE,
    levelPosition_eq_add_levelDropShift]

/-! ### The braid value under a rigid shift -/

/-- **The special braid of a rigid shift, with the hypothesis read off the iterates.** -/
theorem specialBraid_congr_add_of_iterate {k : ℕ} (θ c : ℚ) (v : Fin k → ℚ) (α : Fin k → ℕ)
    (h : ∀ (i : Fin k) (j : ℕ), j ≤ α i - 1 → SameSide θ c ((nextCrossing θ)^[j] (v i))) :
    specialBraid θ (fun j => v j + c) α = specialBraid θ v α :=
  specialBraid_congr_add θ c v α fun l hl i => by
    rw [moveTuple_apply_eq_iterate]
    exact h i _ ((hl.sublist.count_le i).trans (count_specialMoveList α i).le)

/-- **The braid value is unchanged by a rigid shift of the positions that crosses the puncture
nowhere.** Both the prefactor `q^{(inv_fin − inv_ini)/2}` and the braid itself are invariant: the
first because the shift is order-preserving, the second because every letter of
`HJO.Braid.braidStep` reads only the order of the entries and the side of the puncture the moving
one is on. -/
theorem braidValueOfData_congr_add (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) (a b N : ℕ) {k : ℕ} (v : Fin k → ℚ) (α : Fin k → ℕ) (c : ℚ)
    (h : ∀ (i : Fin k) (j : ℕ), j ≤ α i - 1 →
      SameSide (sweepTheta a b N) c ((nextCrossing (sweepTheta a b N))^[j] (v i))) :
    braidValueOfData q u hq hq1 hqp hr a b N (fun j => v j + c) α
      = braidValueOfData q u hq hq1 hqp hr a b N v α := by
  rw [braidValueOfData, braidValueOfData, specialBraid_congr_add_of_iterate _ c v α h,
    invIni_congr_add, invFin_congr_add _ c v α fun i j hj => h i j (by omega)]

/-! ### The unswept clause, reduced to two obligations on the crossing lattice -/

/-- **The braid value is unchanged across an unswept drop**, given the two things the drop must do
to the special-braid data: leave the multiplicities alone, and move no stage position across the
puncture.

Both halves of the colouring are already known to stand still
(`HJO.Mellit.colouringEast_eq_of_notMem_sweptRegion`,
`HJO.Mellit.colouringNorth_eq_of_notMem_sweptRegion`), so the rank `k` is the same on the two sides
and the positions differ by the single shift `HJO.Mellit.levelDropShift`
(`HJO.Mellit.braidDataOfColouring_fst_eq_add_of_notMem_sweptRegion`). What is left is exactly
`hmult` and `hside`. -/
theorem braidValueOfPath_eq_of_notMem_sweptRegion (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hlopos : 0 < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hsw : (X, Y) ∉ sweptRegion y)
    (hmult : (braidDataOfColouring a b N y ηlo #(colouringEast y ηhi)).2
      = (braidDataOfColouring a b N y ηhi #(colouringEast y ηhi)).2)
    (hside : ∀ (i : Fin #(colouringEast y ηhi)) (j : ℕ),
      j ≤ (braidDataOfColouring a b N y ηhi #(colouringEast y ηhi)).2 i - 1 →
      SameSide (sweepTheta a b N) (levelDropShift a b N ηlo ηhi)
        ((nextCrossing (sweepTheta a b N))^[j]
          ((braidDataOfColouring a b N y ηhi #(colouringEast y ηhi)).1 i))) :
    braidValueOfPath q u hq hq1 hqp hr y ηlo = braidValueOfPath q u hq hq1 hqp hr y ηhi := by
  have hE := colouringEast_eq_of_notMem_sweptRegion ha hb hN hI hy hsw
  rw [braidValueOfPath, braidValueOfPath, hE,
    funext (fun i : Fin #(colouringEast y ηhi) =>
      braidDataOfColouring_fst_eq_add_of_notMem_sweptRegion ha hb hN hI hlopos hy hsw i i.isLt),
    hmult]
  exact braidValueOfData_congr_add q u hq hq1 hqp hr a b N _ _ _ hside

/-- **The unswept clause of the level recursion, for the braid value of a colouring**, at a drop
whose lower level is positive and subject to the two obligations of
`HJO.Mellit.braidValueOfPath_eq_of_notMem_sweptRegion`. This is the shape
`HJO.Mellit.SweepRecursionUnswept` asks for, at one drop. -/
theorem braidValueColouring_eq_of_notMem_sweptRegion (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hlopos : 0 < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hsw : (X, Y) ∉ sweptRegion y)
    (hmult : (braidDataOfColouring a b N y ηlo #(colouringEast y ηhi)).2
      = (braidDataOfColouring a b N y ηhi #(colouringEast y ηhi)).2)
    (hside : ∀ (i : Fin #(colouringEast y ηhi)) (j : ℕ),
      j ≤ (braidDataOfColouring a b N y ηhi #(colouringEast y ηhi)).2 i - 1 →
      SameSide (sweepTheta a b N) (levelDropShift a b N ηlo ηhi)
        ((nextCrossing (sweepTheta a b N))^[j]
          ((braidDataOfColouring a b N y ηhi #(colouringEast y ηhi)).1 i))) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi) := by
  rw [braidValueColouring_colouring q u hq hq1 hqp hr hy,
    braidValueColouring_colouring q u hq hq1 hqp hr hy]
  exact braidValueOfPath_eq_of_notMem_sweptRegion q u hq hq1 hqp hr ha hb hN hI hlopos hy hsw
    hmult hside

/-! ### Where the positions do not enter at all -/

/-- **At multiplicity `1` everywhere the braid value is the bare vacuum tower `d₊^k(1)`**, and in
particular does not depend on the positions: the move sequence of `HJO.Braid.specialBraid` is empty,
so the braid is the identity, and the two inversion counts coincide, so the prefactor is `1`. -/
theorem braidValueOfData_of_forall_mult_eq_one (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (a b N : ℕ) {k : ℕ} (v : Fin k → ℚ) {α : Fin k → ℕ}
    (h : ∀ i, α i = 1) :
    braidValueOfData q u hq hq1 hqp hr a b N v α = dplusIter q k := by
  rw [braidValueOfData, specialBraid_of_forall_eq_one h, map_one,
    invFin_eq_invIni_of_mult_eq_one _ v h]
  simp

/-- **The unswept clause holds outright wherever every multiplicity is `1`.** No hypothesis on the
crossing lattice beyond the two halves standing still, because at multiplicity `1` the braid value
is `d₊^k(1)` and the positions — the only thing the drop moves — do not enter. -/
theorem braidValueColouring_eq_of_notMem_sweptRegion_of_mult_eq_one (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hsw : (X, Y) ∉ sweptRegion y)
    (hlo : ∀ i, (braidDataOfColouring a b N y ηlo #(colouringEast y ηhi)).2 i = 1)
    (hhi : ∀ i, (braidDataOfColouring a b N y ηhi #(colouringEast y ηhi)).2 i = 1) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi) := by
  have hE := colouringEast_eq_of_notMem_sweptRegion ha hb hN hI hy hsw
  rw [braidValueColouring_colouring q u hq hq1 hqp hr hy,
    braidValueColouring_colouring q u hq hq1 hqp hr hy, braidValueOfPath, braidValueOfPath, hE,
    braidValueOfData_of_forall_mult_eq_one q u hq hq1 hqp hr a b N _ hlo,
    braidValueOfData_of_forall_mult_eq_one q u hq hq1 hqp hr a b N _ hhi]

/-- **The unswept clause holds outright wherever the colouring is empty**, which is the bulk of the
clause's range. The colouring at the upper level being empty forces the lower one to be too, by
`HJO.Mellit.colouring_eq_of_notMem_sweptRegion`. -/
theorem braidValueColouring_eq_of_notMem_sweptRegion_of_eq_empty (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hsw : (X, Y) ∉ sweptRegion y) (hemp : colouring y ηhi = ∅) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi) := by
  have hlo : colouring y ηlo = ∅ :=
    (colouring_eq_of_notMem_sweptRegion ha hb hN hI hy hsw).trans hemp
  rw [braidValueColouring_colouring q u hq hq1 hqp hr hy,
    braidValueColouring_colouring q u hq hq1 hqp hr hy,
    braidValueOfPath_of_colouring_eq_empty q u hq hq1 hqp hr hlo,
    braidValueOfPath_of_colouring_eq_empty q u hq hq1 hqp hr hemp]

end HJO.Mellit

end
