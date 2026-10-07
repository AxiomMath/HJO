/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidSweepRecursions
public meta import HJO.Attr

/-! # Positions are normalised ranks, and what that makes of the type-`A` clause

`HJO/Shuffle/BraidSweepRecursions.lean` shows that `HJO.Braid.specialBraid_mul_trainDown_one` is
*never* applicable to the braid data of a colouring: its hypothesis is an index with
`w_j = 1 - \theta`, and no position of `HJO.Mellit.braidDataOfColouring` is ever that number. The
natural replacement is `HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le`, which asks only
`w_j \le 1 - \theta` together with a **gap clause** — at every stage of the move sequence, the entry
about to be advanced satisfies `u_m < w_j + \theta`. The natural guess at the geometric statement
that would supply the gap is "the component created at a type-`A` event carries the topmost
position, within `\theta` of the start".

This file settles both halves, and the second half comes out the other way round.

## Positions are ranks

`HJO.Mellit.fract_crossingAbscissa_eq_levelPosition` is the identity everything else here is a
corollary of. If `(x, y)` is a lattice point over the level line with `(x+1, y)` under it — which is
exactly the membership condition of `HJO.Mellit.colouringEast`, and exactly the condition that the
crossing of antidiagonal index `x + y` sits in the column `x` — then

```
fract (crossingAbscissa η (x + y)) = θ · (rk̂(x, y) − η) / (a(aN+1)N).
```

Two immediate consequences.

* **`HJO.Mellit.braidDataOfColouring_fst_lt_one_sub_sweepTheta`: every position lies in
  `(0, 1 - \theta)`**, at every index, every admissible level and every path. The upper bound is the
  east step's own inequality `rk̂(x+1, y) < η` rescaled, since
  `θ·(b(aN+1)N − 1)/(a(aN+1)N) = θs = 1 − θ`. So the hypothesis `w_j \le 1 - \theta` of the general
  lemma is satisfied at **every** index — the parity obstruction kills only the equality
  `w_j = 1 - \theta` that `HJO.Braid.specialBraid_mul_trainDown_one` asks for.
* **Positions are ordered as ranks** (`HJO.Mellit.levelPosition_le_levelPosition`), and lowering a
  lattice point's ordinate by one lowers its position by exactly `\theta`
  (`HJO.Mellit.levelPosition_sub`). So one step of `HJO.Braid.nextCrossing` is one step down a
  column, in ranks.

## The type-`A` point is the BOTTOM of the configuration

The isolation clause of `HJO.Mellit.Isolates` says `rk̂(P)` is the **least** rank of the rectangle
above `η_-` (`HJO.Mellit.Isolates.pointRank_le`). Positions increase with the rank. Hence
`HJO.Mellit.Isolates.levelPosition_le_braidDataOfColouring_fst`: the position of `P` is `\le` every
position of the colouring at `η_-`. **The component created at a type-`A` event carries the
bottommost position, not the topmost.** The guess above is false, and false in the direction that
matters, because the gap clause of the general lemma wants `w_j` near the *top*: at
`w_j = 1 - \theta` the clause reads `u_m < 1` and is free.

## What the gap clause therefore costs

`HJO.Mellit.Isolates.not_lt_levelPosition_add_sweepTheta` is the sharp form. If any position of the
colouring at `η_-` exceeds `\theta`, the gap clause at the type-`A` index is **false**. The proof is
three lines of the above: a position above `\theta` means a rank above `η_- + a(aN+1)N`, so the
lattice point one row lower is still in the rectangle and still above `η_-`, so its rank is at least
`rk̂(P)`, so the original position is at least `levelPosition(rk̂(P)) + \theta`.

So the obligation the type-`A` clause actually owes is a **squeeze**:

> every crossing of `c_{η_-}` the move sequence advances has rank within `a(aN+1)N` of `rk̂(P)`,
> equivalently sits at a position below `\theta`.

Two readings of that, both worth recording. First, positions are below `1 - \theta` for free, so
when `s < 1` — that is `b \le a` — the *initial* positions are all below `\theta` automatically and
the first move of every component is safe; the squeeze can then only fail after a wrap. Second, two
crossings of one component in the same column differ by exactly `\theta` in position, so a component
with two crossings in one column and the upper one advanced breaks the squeeze outright. Since a
full column carries about `1 + s` crossings, for `b > a` a component spanning a full column has two
in one column, and the squeeze fails. Neither reading is proved or disproved here; what is
established is that the squeeze, and not "the topmost position", is the statement at issue.

## References

Declarations involved: `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`,
`HJO.Braid.specialBraid_mul_trainDown_one`, `HJO.Mellit.sweepTheta_eq_div`,
`HJO.Mellit.dsc_lo_eq_dplus_dsc_hi`, using `HJO.Mellit.braidDataOfColouring`,
`HJO.Braid.positionPair`, `HJO.Mellit.colouring`, `HJO.ParkingFunctions.abovePointRank`,
`HJO.Paths.eventType`. Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*,
section 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### Two pieces of pure algebra -/

/-- The algebra behind `HJO.Mellit.fract_crossingAbscissa_eq_levelPosition`: with `θ(s+1) = 1`, the
crossing abscissa `θ(X + Y − ι)` splits as `X` plus the normalised vertical distance. Stated over
abstract scalars so that no definition of the sweep is unfolded. -/
private theorem abscissa_split (θ s ι X Y M R : ℚ) (hM : M ≠ 0) (hθ : θ * (s + 1) = 1)
    (hkey : M * (Y - (s * X + ι)) = R) : θ * ((X + Y) - ι) = X + θ * (R / M) := by
  rw [← hkey, mul_div_cancel_left₀ _ hM]
  linear_combination X * hθ

/-- The algebra behind the bound `v_i < 1 − θ`: a normalised rank below `M s` is a position below
`θ s`. -/
private theorem pos_lt_of_lt (θ s M R : ℚ) (hM : 0 < M) (hθ : 0 < θ) (hR : R < M * s) :
    θ * (R / M) < θ * s :=
  mul_lt_mul_of_pos_left ((div_lt_iff₀ hM).2 (by linarith [mul_comm M s])) hθ

/-! ### The position a rank occupies -/

/-- **The position on the circle that a rank `r` above the level `η` occupies**:
`θ(r − η)/(a(aN+1)N)`. The scaling is the one of `HJO.Mellit.abovePointRank_sub_level`: dividing a
rank difference by `a(aN+1)N` turns it into the vertical distance from the level line, and
multiplying by `θ` turns that distance into the fractional part of the crossing abscissa. -/
def levelPosition (a b N : ℕ) (η r : ℚ) : ℚ :=
  sweepTheta a b N * ((r - η) / ((a : ℚ) * ((a : ℚ) * N + 1) * N))

/-- The denominator of `HJO.Mellit.levelPosition` is positive on a rectangle with a row and a
column. -/
theorem rankDen_pos (ha : 0 < a) (hN : 0 < N) :
    (0 : ℚ) < (a : ℚ) * ((a : ℚ) * N + 1) * N := by
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  positivity

/-- **`a(aN+1)N · s = b(aN+1)N − 1`**: clearing the denominator of `HJO.Mellit.sweepSlope`. -/
theorem rankDen_mul_sweepSlope (ha : 0 < a) (hN : 0 < N) :
    (a : ℚ) * ((a : ℚ) * N + 1) * N * sweepSlope a b N
      = (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  rw [sweepSlope]
  field_simp

/-- **`θ` times the slope is `1 − θ`.** -/
theorem sweepTheta_mul_sweepSlope (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    sweepTheta a b N * sweepSlope a b N = 1 - sweepTheta a b N := by
  have h := sweepTheta_mul (a := a) (b := b) (N := N) (one_add_sweepSlope_pos ha hb hN).ne'
  linarith [h]

/-- **`levelPosition` is monotone in the rank**: positions on the circle are ordered exactly as the
ranks they come from. -/
theorem levelPosition_le_levelPosition (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) {r r' : ℚ}
    (h : r ≤ r') : levelPosition a b N η r ≤ levelPosition a b N η r' := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hθ := (sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN).1
  rw [levelPosition, levelPosition]
  gcongr

/-- **A rank `a(aN+1)N` lower sits exactly `θ` lower on the circle.** Lowering the ordinate of a
lattice point by one lowers its rank by `a(aN+1)N`, so such a step is one application of
`HJO.Braid.nextCrossing` — which is what makes the trajectory of a component a walk down the
column. -/
theorem levelPosition_sub (ha : 0 < a) (hN : 0 < N) (η r : ℚ) :
    levelPosition a b N η (r - (a : ℚ) * ((a : ℚ) * N + 1) * N)
      = levelPosition a b N η r - sweepTheta a b N := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  rw [levelPosition, levelPosition]
  field_simp
  ring

/-! ### The fractional part of a crossing abscissa is a normalised rank -/

/-- **Stepping the abscissa of a lattice point lowers the rank by `b(aN+1)N − 1`.** -/
theorem cast_pointRank_succ_fst (a b N x y : ℕ) :
    ((pointRank a b N (x + 1, y) : ℤ) : ℚ)
      = ((pointRank a b N (x, y) : ℤ) : ℚ) - ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
  rw [cast_pointRank_eq', cast_pointRank_eq']
  push_cast
  ring

/-- **Lowering the ordinate of a lattice point lowers the rank by `a(aN+1)N`.** -/
theorem cast_pointRank_succ_snd (a b N x y : ℕ) :
    ((pointRank a b N (x, y + 1) : ℤ) : ℚ)
      = ((pointRank a b N (x, y) : ℤ) : ℚ) + (a : ℚ) * ((a : ℚ) * N + 1) * N := by
  rw [cast_pointRank_eq', cast_pointRank_eq']
  push_cast
  ring

/-- **THE CLOSED FORM: the fractional part of a crossing abscissa is a normalised rank.** If the
lattice point `(x, y)` lies over the level line and `(x + 1, y)` under it — which is exactly the
membership condition of `HJO.Mellit.colouringEast`, and exactly the condition that the crossing of
antidiagonal index `x + y` lies in the column `x` — then

```
fract (crossingAbscissa η (x + y)) = θ · (rk̂(x, y) − η) / (a(aN+1)N).
```

So every position `HJO.Mellit.braidDataOfColouring` reads is a **rank measured up from the level**,
rescaled; the order of the positions on the circle is the order of those ranks; and the position is
automatically in `[0, 1 − θ)`, which is `HJO.Mellit.fract_crossingAbscissa_lt_one_sub_sweepTheta`
below. This is the fact the whole type-`A` discussion runs on. -/
@[hjo "lem_braid_position_rank"]
theorem fract_crossingAbscissa_eq_levelPosition (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ)
    (x y : ℕ) (hlt : η < ((pointRank a b N (x, y) : ℤ) : ℚ))
    (hgt : ((pointRank a b N (x + 1, y) : ℤ) : ℚ) < η) :
    Int.fract (crossingAbscissa a b N η ((x : ℤ) + (y : ℤ)))
      = levelPosition a b N η ((pointRank a b N (x, y) : ℤ) : ℚ) := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hs := one_add_sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  have hθ1 := sweepTheta_mul (a := a) (b := b) (N := N) hs.ne'
  have hθpos := (sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN).1
  have hkey : (a : ℚ) * ((a : ℚ) * N + 1) * N *
      ((y : ℚ) - (sweepSlope a b N * (x : ℚ) + levelIntercept a N η))
      = ((pointRank a b N (x, y) : ℤ) : ℚ) - η := by
    rw [cast_pointRank_eq', abovePointRank_sub_level (b := b) ha.ne' hN.ne']
  have habs : crossingAbscissa a b N η ((x : ℤ) + (y : ℤ))
      = (x : ℚ) + levelPosition a b N η ((pointRank a b N (x, y) : ℤ) : ℚ) := by
    rw [crossingAbscissa_eq_sweepTheta_mul, levelPosition]
    have := abscissa_split (sweepTheta a b N) (sweepSlope a b N) (levelIntercept a N η)
      (x : ℚ) (y : ℚ) ((a : ℚ) * ((a : ℚ) * N + 1) * N)
      (((pointRank a b N (x, y) : ℤ) : ℚ) - η) hM.ne' hθ1 hkey
    push_cast
    convert this using 2
  have hpos : 0 ≤ levelPosition a b N η ((pointRank a b N (x, y) : ℤ) : ℚ) := by
    rw [levelPosition]
    have h1 : 0 ≤ (((pointRank a b N (x, y) : ℤ) : ℚ) - η) /
        ((a : ℚ) * ((a : ℚ) * N + 1) * N) := div_nonneg (by linarith) hM.le
    positivity
  have hub : levelPosition a b N η ((pointRank a b N (x, y) : ℤ) : ℚ) < 1 - sweepTheta a b N := by
    have hd : ((pointRank a b N (x, y) : ℤ) : ℚ) - η
        < (a : ℚ) * ((a : ℚ) * N + 1) * N * sweepSlope a b N := by
      rw [rankDen_mul_sweepSlope (b := b) ha hN, cast_pointRank_succ_fst a b N x y] at *
      linarith
    rw [levelPosition, ← sweepTheta_mul_sweepSlope ha hb hN]
    exact pos_lt_of_lt _ _ _ _ hM hθpos hd
  rw [habs]
  have hx : (((x : ℤ)) + ((y : ℤ)) : ℤ) = (((x + y : ℕ) : ℤ)) := by push_cast; ring
  rw [show ((x : ℚ)) = ((x : ℕ) : ℚ) from rfl, Int.fract_natCast_add, Int.fract_eq_self]
  exact ⟨hpos, by linarith⟩

/-- **Every crossing position lies strictly below `1 − θ`.** The upper bound comes from the east
step's own defining inequality `rk̂(x+1, y) < η`: a rank less than `b(aN+1)N − 1` above the level is
a position less than `θs = 1 − θ`. -/
@[hjo "lem_braid_position_below_start"]
theorem fract_crossingAbscissa_lt_one_sub_sweepTheta (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ)
    (x y : ℕ) (hlt : η < ((pointRank a b N (x, y) : ℤ) : ℚ))
    (hgt : ((pointRank a b N (x + 1, y) : ℤ) : ℚ) < η) :
    Int.fract (crossingAbscissa a b N η ((x : ℤ) + (y : ℤ))) < 1 - sweepTheta a b N := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hθpos := (sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN).1
  rw [fract_crossingAbscissa_eq_levelPosition ha hb hN η x y hlt hgt]
  have hd : ((pointRank a b N (x, y) : ℤ) : ℚ) - η
      < (a : ℚ) * ((a : ℚ) * N + 1) * N * sweepSlope a b N := by
    rw [rankDen_mul_sweepSlope (b := b) ha hN, cast_pointRank_succ_fst a b N x y] at *
    linarith
  rw [levelPosition, ← sweepTheta_mul_sweepSlope ha hb hN]
  exact pos_lt_of_lt _ _ _ _ hM hθpos hd

/-- `HJO.Mellit.fract_crossingAbscissa_eq_levelPosition` with the point packed into a pair, which is
the shape `HJO.Mellit.colouringEast` hands over. -/
@[hjo "lem_braid_position_rank"]
theorem fract_crossingAbscissa_eq_levelPosition' (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ)
    (P : ℕ × ℕ) (hlt : η < ((pointRank a b N P : ℤ) : ℚ))
    (hgt : ((pointRank a b N (P.1 + 1, P.2) : ℤ) : ℚ) < η) :
    Int.fract (crossingAbscissa a b N η ((P.1 : ℤ) + (P.2 : ℤ)))
      = levelPosition a b N η ((pointRank a b N P : ℤ) : ℚ) := by
  obtain ⟨x, y⟩ := P
  exact fract_crossingAbscissa_eq_levelPosition ha hb hN η x y hlt hgt

/-- `HJO.Mellit.fract_crossingAbscissa_lt_one_sub_sweepTheta` with the point packed into a pair. -/
@[hjo "lem_braid_position_below_start"]
theorem fract_crossingAbscissa_lt_one_sub_sweepTheta' (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (η : ℚ) (P : ℕ × ℕ) (hlt : η < ((pointRank a b N P : ℤ) : ℚ))
    (hgt : ((pointRank a b N (P.1 + 1, P.2) : ℤ) : ℚ) < η) :
    Int.fract (crossingAbscissa a b N η ((P.1 : ℤ) + (P.2 : ℤ))) < 1 - sweepTheta a b N := by
  obtain ⟨x, y⟩ := P
  exact fract_crossingAbscissa_lt_one_sub_sweepTheta ha hb hN η x y hlt hgt

/-! ### The positions of a colouring's braid data are normalised ranks -/

/-- The two rank inequalities a crossed east step carries, straight off the filter of
`HJO.Mellit.colouringEast`. -/
theorem pointRank_lt_of_mem_colouringEast {η : ℚ} {y : Heights a b N} {P : ℕ × ℕ}
    (hP : P ∈ colouringEast y η) :
    ((pointRank a b N (P.1 + 1, P.2) : ℤ) : ℚ) < η ∧ η < ((pointRank a b N P : ℤ) : ℚ) :=
  (Finset.mem_filter.1 hP).2

/-- **The position of the `i`-th component is the normalised rank of its crossed east step.** This
is `HJO.Mellit.braidDataOfColouring_fst_eq` read through
`HJO.Mellit.fract_crossingAbscissa_eq_levelPosition`: the integer `x(w_i) + y(w_i)` that the closed
form exposes is the antidiagonal index of a crossing sitting in the column `x(w_i)`, and that turns
the fractional part into a rank. -/
@[hjo "lem_braid_position_rank"]
theorem braidDataOfColouring_fst_eq_levelPosition (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) {y : Heights a b N} {k : ℕ} (i : Fin k)
    (hi : (i : ℕ) < #(colouringEast y η)) :
    (braidDataOfColouring a b N y η k).1 i
      = levelPosition a b N η
          ((pointRank a b N (colStep (colouringEast y η) (i : ℕ)) : ℤ) : ℚ) := by
  obtain ⟨hlo, hhi⟩ := pointRank_lt_of_mem_colouringEast (a := a) (b := b) (N := N) (colStep_mem hi)
  rw [braidDataOfColouring_fst_eq ha hb hN hη hηpos i hi]
  have hrw : sweepTheta a b N * ((((colStep (colouringEast y η) (i : ℕ)).1
        + (colStep (colouringEast y η) (i : ℕ)).2 : ℕ) : ℚ) - levelIntercept a N η)
      = crossingAbscissa a b N η (((colStep (colouringEast y η) (i : ℕ)).1 : ℤ)
        + ((colStep (colouringEast y η) (i : ℕ)).2 : ℤ)) := by
    rw [crossingAbscissa_eq_sweepTheta_mul]
    push_cast
    ring
  rw [hrw, fract_crossingAbscissa_eq_levelPosition' ha hb hN η _ hhi hlo]

/-- **Every position of a colouring's braid data lies strictly below `1 − θ`** — at every index,
every admissible level and every path.

This strictly strengthens `HJO.Mellit.braidDataOfColouring_fst_ne_one_sub_sweepTheta`, and it
strengthens it in the direction that matters: the hypothesis `w_j ≤ 1 - θ` of
`HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le` — the general lemma behind
`HJO.Braid.specialBraid_mul_trainDown_one` — is satisfied at **every** index of a colouring's braid
data, not violated. So the parity obstruction of `HJO/Shuffle/BraidSweepRecursions.lean` kills
the *equality* `w_j = 1 - θ` that `HJO.Braid.specialBraid_mul_trainDown_one` asks for while leaving
the inequality free. What is not free is the gap clause; see the next section. -/
@[hjo "lem_braid_position_below_start"]
theorem braidDataOfColouring_fst_lt_one_sub_sweepTheta (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {η : ℚ} (hη : IsAdmissibleLevel η) (hηpos : 0 < η) {y : Heights a b N} {k : ℕ} (i : Fin k)
    (hi : (i : ℕ) < #(colouringEast y η)) :
    (braidDataOfColouring a b N y η k).1 i < 1 - sweepTheta a b N := by
  obtain ⟨hlo, hhi⟩ := pointRank_lt_of_mem_colouringEast (a := a) (b := b) (N := N) (colStep_mem hi)
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hη hηpos i hi,
    ← fract_crossingAbscissa_eq_levelPosition' ha hb hN η _ hhi hlo]
  exact fract_crossingAbscissa_lt_one_sub_sweepTheta' ha hb hN η _ hhi hlo

/-! ### On the parameters the shuffle route needs, the window is strictly narrow -/

/-- **`s > 1` whenever `a < b`.** The numerator of `HJO.Mellit.sweepSlope` exceeds its denominator
by `(b-a)(aN+1)N - 1 \ge (aN+1)N - 1 \ge 1`. -/
theorem one_lt_sweepSlope (ha : 0 < a) (hN : 0 < N) (hab : a < b) : 1 < sweepSlope a b N := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have ha1 : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hN1 : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  have hab1 : (a : ℚ) + 1 ≤ (b : ℚ) := by exact_mod_cast hab
  have haN : (1 : ℚ) ≤ (a : ℚ) * N := by nlinarith
  have hMp : (2 : ℚ) ≤ ((a : ℚ) * N + 1) * N := by
    nlinarith [mul_le_mul haN hN1 zero_le_one (by linarith : (0 : ℚ) ≤ (a : ℚ) * N)]
  have hMnn : (0 : ℚ) ≤ ((a : ℚ) * N + 1) * N := by positivity
  rw [sweepSlope, lt_div_iff₀ (by nlinarith)]
  nlinarith [mul_le_mul_of_nonneg_right hab1 hMnn]

/-- **`θ < 1/2` whenever `a < b`**, since `θ(s+1) = 1` and `s > 1`. So on the parameters
`HJO.Mellit.shuffle_of_lhs_and_induction` quantifies over — its `hind` binder asks `1 < a` and
`a < b` — the window `(0, θ)` that the gap clause of
`HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le` confines the configuration to is
strictly narrower than the range `(0, 1 - θ)` the positions actually occupy
(`HJO.Mellit.braidDataOfColouring_fst_lt_one_sub_sweepTheta`). There is therefore no escape from the
squeeze of `HJO.Mellit.Isolates.not_lt_levelPosition_add_sweepTheta` by a hypothesis on the
parameters: the case `b \le a`, where `s < 1` puts every position below `θ` for free, is exactly the
case `HJO.Mellit.shuffle_of_lhs_and_induction` never needs. -/
theorem sweepTheta_lt_half (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : a < b) :
    sweepTheta a b N < 1 / 2 := by
  have hs := one_lt_sweepSlope (b := b) ha hN hab
  have hpos := one_add_sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  rw [sweepTheta, div_lt_div_iff₀ hpos (by norm_num)]
  linarith

/-- **`θ < 1 - θ` whenever `a < b`**: the gap clause's window is strictly inside the range of
positions. -/
@[hjo "lem_braid_typea_gap_window"]
theorem sweepTheta_lt_one_sub_sweepTheta (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : a < b) :
    sweepTheta a b N < 1 - sweepTheta a b N := by
  have := sweepTheta_lt_half (a := a) (b := b) (N := N) ha hb hN hab
  linarith

/-! ### The type-`A` point is the BOTTOM of the configuration, not the top -/

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-- **`rk̂(P)` is the least rank of the rectangle above the lower level.** This is the isolation
clause read the only way it can be read: a rectangle point whose rank exceeds `ηlo` either has rank
below `ηhi`, and then its rank *is* `rk̂(P)`, or has rank above `ηhi > rk̂(P)`. -/
@[hjo "lem_braid_typea_bottom"]
theorem pointRank_le (hI : Isolates a b N X Y ηlo ηhi) {Q : ℕ × ℕ} (hx : Q.1 ≤ a * N)
    (hy : Q.2 ≤ b * N) (h : ηlo < ((pointRank a b N Q : ℤ) : ℚ)) :
    ((pointRank a b N (X, Y) : ℤ) : ℚ) ≤ ((pointRank a b N Q : ℤ) : ℚ) := by
  by_cases hQ : ((pointRank a b N Q : ℤ) : ℚ) < ηhi
  · rw [hI.iso Q hx hy h hQ]
  · linarith [hI.Plt, not_lt.1 hQ]

/-- **The position of `P` is the bottom of the whole configuration at the lower level.** Every
crossed east step of `c_{η_-}` is a rectangle point of rank above `η_-`, so its rank is at least
`rk̂(P)`, and `HJO.Mellit.levelPosition_le_levelPosition` turns that into an inequality of
positions.

This corrects a natural guess. For the type-`A` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` one might expect, as the geometric statement
replacing `HJO.Braid.specialBraid_mul_trainDown_one`, that "the component created at a type-`A`
event carries the topmost position, within `θ` of the start". It carries the **bottommost**
position: `rk̂(P)` is the *least* rank above `η_-` by the isolation clause, and positions are
increasing in the rank. -/
@[hjo "lem_braid_typea_bottom"]
theorem levelPosition_le_braidDataOfColouring_fst (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηpos : 0 < ηlo) {y : Heights a b N} {k : ℕ} (i : Fin k)
    (hi : (i : ℕ) < #(colouringEast y ηlo)) :
    levelPosition a b N ηlo ((pointRank a b N (X, Y) : ℤ) : ℚ)
      ≤ (braidDataOfColouring a b N y ηlo k).1 i := by
  have hmem := colStep_mem (S := colouringEast y ηlo) hi
  obtain ⟨hlo, hhi⟩ := pointRank_lt_of_mem_colouringEast (a := a) (b := b) (N := N) hmem
  obtain ⟨hx, hy2, -, -⟩ := mem_colouringEast_spec ha hN hI.lo y hmem
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.lo hηpos i hi]
  exact levelPosition_le_levelPosition ha hb hN ηlo
    (hI.pointRank_le hx.le (hy2 ▸ ht_le_mul y _) hhi)

/-- **THE OBSTRUCTION: a position above `θ` refutes the gap clause outright.**

The natural route for the type-`A` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` is
`HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le`, whose hypotheses at the inserted index
`j` are `w_j ≤ 1 - θ` — free here, by `HJO.Mellit.braidDataOfColouring_fst_lt_one_sub_sweepTheta` —
and a **gap clause** `u_m < w_j + θ` on every entry the move sequence advances.

This says the gap clause is *false* at any index whose position exceeds `θ`. The reason is the one
fact of this file: if `v_i > θ` then the rank of the `i`-th crossed east step exceeds
`η_- + a(aN+1)N`, so the lattice point one step *lower*, `(x(w_i), y(w_i) - 1)`, still has rank
above `η_-`; it is still in the rectangle; so by `HJO.Mellit.Isolates.pointRank_le` its rank is at
least `rk̂(P)`, and translating back, `v_i ≥ levelPosition(rk̂(P)) + θ`.

So with `w_j` the position of `P` — which is what a type-`A` event inserts, `(X, Y)` being the east
step gained by `HJO.Mellit.Isolates.colouringEast_eq_of_eventType_A` — the gap clause forces
**every** position of the colouring at `η_-` to lie in the window `[v_j, v_j + θ)`, that is every
crossed east step's rank to lie within `a(aN+1)N` of `rk̂(P)`. That is the obligation the type-`A`
clause actually owes, and it is nothing like "the topmost position". -/
@[hjo "lem_braid_typea_gap_window"]
theorem not_lt_levelPosition_add_sweepTheta (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηpos : 0 < ηlo) {y : Heights a b N} {k : ℕ} (i : Fin k)
    (hi : (i : ℕ) < #(colouringEast y ηlo))
    (hgt : sweepTheta a b N < (braidDataOfColouring a b N y ηlo k).1 i) :
    ¬ ((braidDataOfColouring a b N y ηlo k).1 i
        < levelPosition a b N ηlo ((pointRank a b N (X, Y) : ℤ) : ℚ) + sweepTheta a b N) := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hθpos := (sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN).1
  have hmem := colStep_mem (S := colouringEast y ηlo) hi
  obtain ⟨-, hhi⟩ := pointRank_lt_of_mem_colouringEast (a := a) (b := b) (N := N) hmem
  obtain ⟨hx, hy2, -, -⟩ := mem_colouringEast_spec ha hN hI.lo y hmem
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.lo hηpos i hi] at hgt ⊢
  set w := colStep (colouringEast y ηlo) (i : ℕ) with hw
  -- `v_i > θ` says the rank of `w` exceeds `η_- + a(aN+1)N`
  have hrank : ηlo + (a : ℚ) * ((a : ℚ) * N + 1) * N < ((pointRank a b N w : ℤ) : ℚ) := by
    rw [levelPosition] at hgt
    have h1 : 1 < (((pointRank a b N w : ℤ) : ℚ) - ηlo) / ((a : ℚ) * ((a : ℚ) * N + 1) * N) := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith [mul_le_mul_of_nonneg_left hcon hθpos.le]
    have h2 := (one_lt_div hM).1 h1
    linarith
  -- so the point one row lower is still above the level, and still in the rectangle
  have ha1 : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hN1 : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  have hy1 : 1 ≤ w.2 := by
    by_contra h0
    have h0' : w.2 = 0 := by omega
    have hxle : (w.1 : ℚ) ≤ (a : ℚ) * N := by
      have h : ((w.1 : ℕ) : ℚ) ≤ ((a * N : ℕ) : ℚ) := Nat.cast_le.2 hx.le
      push_cast at h
      exact h
    have hrk : ((pointRank a b N w : ℤ) : ℚ) ≤ (w.1 : ℚ) := by
      rw [show w = (w.1, w.2) from rfl, cast_pointRank_eq', h0']
      have hmul : (0 : ℚ) ≤ (((a : ℚ) * N + 1) * N) * ((b : ℚ) * (w.1 : ℚ)) := by positivity
      push_cast
      nlinarith
    nlinarith
  have hQrank : ((pointRank a b N (w.1, w.2 - 1) : ℤ) : ℚ)
      = ((pointRank a b N w : ℤ) : ℚ) - (a : ℚ) * ((a : ℚ) * N + 1) * N := by
    have := cast_pointRank_succ_snd a b N w.1 (w.2 - 1)
    rw [show w.2 - 1 + 1 = w.2 from by omega] at this
    rw [show w = (w.1, w.2) from rfl] at *
    linarith
  have hQ : ((pointRank a b N (X, Y) : ℤ) : ℚ)
      ≤ ((pointRank a b N w : ℤ) : ℚ) - (a : ℚ) * ((a : ℚ) * N + 1) * N := by
    rw [← hQrank]
    exact hI.pointRank_le (Q := (w.1, w.2 - 1)) hx.le
      (by have := hy2 ▸ ht_le_mul (a := a) (b := b) (N := N) y (w.1 + 1); omega)
      (by rw [hQrank]; linarith)
  have hmono := levelPosition_le_levelPosition (b := b) ha hb hN ηlo hQ
  rw [levelPosition_sub (b := b) ha hN] at hmono
  linarith

end Isolates

end HJO.Mellit
