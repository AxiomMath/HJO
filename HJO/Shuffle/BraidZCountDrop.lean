/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidRotation
public import HJO.Shuffle.BraidDataLevelDrop
public meta import HJO.Attr

/-! # What one level drop does to the `z`-count of a colouring's braid

`HJO.Mellit.zCount_specialBraid_braidDataOfColouring` reads the `z`-count of
`HJO.Mellit.braidDataOfColouring` off the lattice:

`ζ(B_{s,v,α}) = ∑_i (⌊x_i^{top}⌋ - ⌊x_i^{bot}⌋)`,

one `z` for each integer the `i`-th component's crossing abscissa passes between its bottom
crossing and its top one. `HJO.Mellit.sweepTheta_eq_div` says a level drop moves every abscissa
right by the one common amount `(η_+ - η_-)/D`. Combining the two gives the residual obligation of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` that remains after `HJO.Braid.zCount_mul`: the
drop should change `ζ` by (the number of components whose **top** abscissa passes an integer) minus
(the number whose **bottom** does), an abscissa passes an integer exactly when the level line passes
a lattice point of that antidiagonal, and `HJO.Mellit.exists_isolating_isAdmissibleLevel` passes
exactly one point `P`.

This file proves that, and the answer is sharper than the obligation asked for.

## The rank lattice of an antidiagonal

Everything here rests on one identity, `HJO.Mellit.pointRank_eq_antidiagRank`: on the antidiagonal
`x + y = n` the above-diagonal rank is

`rk̂(x, y) = aM·n - D·x`,  `M = (aN+1)N`,  `D = (a+b)M - 1`,

so the ranks of the lattice points of one antidiagonal form an arithmetic progression of step `-D`
in the abscissa, while `HJO.Mellit.crossingAbscissa_eq_div` writes the crossing abscissa as
`(aM·n - η)/D`. The two are the same data: `HJO.Mellit.le_crossingAbscissa_iff` says
`j ≤ x_n(η) ↔ η ≤ rk̂` at the point of abscissa `j` on that antidiagonal, so **`⌊x_n(η)⌋` is the
abscissa of the last lattice point of the antidiagonal still at or above the level**, and the
abscissa passes an integer between two levels exactly when a lattice point of that antidiagonal has
its rank in the window. That is the first half of the obligation, and it needs no geometry.

## The change of `ζ` across the drop is carried by the indices, not by the rotation

The second half is where the answer turns. For the drop `η_- = η_+ - 1` past `P = (X, Y)` the
lattice point passed is `P` itself and the abscissa that passes it is the one of `P`'s own
antidiagonal `n_P = X + Y` (`HJO.Mellit.floor_crossingAbscissa_antidiag_lo` against
`HJO.Mellit.floor_crossingAbscissa_antidiag_hi`: that one floor rises from `X - 1` to `X`). But
`n_P` is **never** an endpoint index of a component at the level being dropped from:

* `HJO.Mellit.componentTopIndex_ne_antidiag` — a crossed east step `(x, i)` of `η_+` has
  `rk̂(x, i) > η_+ > rk̂(x + 1, i) = rk̂(x, i) - (bM - 1)`, so its rank sits within `bM - 1` of the
  level, while the next lattice point down its own antidiagonal is a full `D = aM + bM - 1` below
  it. There is no room for `P`;
* `HJO.Mellit.componentBotIndex_ne_antidiag` — the bottom index of a component is
  `x + I_x + 1`, and `rk̂(x, I_x + 1) > η_+ ≥ rk̂(x, I_x) = rk̂(x, I_x + 1) - aM`, so the same count
  with `aM` in place of `bM - 1`.

Hence `HJO.Mellit.floor_crossingAbscissa_componentTopIndex_congr` and its bottom twin: **the
rotation moves no component endpoint past a lattice point at all.** The two counts the obligation
asks for are both `0`, and the whole change of `ζ` across a level drop is carried by the *indices* —
by which crossings the components acquire and lose, i.e. by
`HJO.Mellit.Isolates.notMem_colouringNorth_lo`. That is `HJO.Mellit.zCount_sub_eq_sum_index_shift`,
which says exactly that, with both terms evaluated at the *lower* level.

## The two shapes of the descent, and the prediction

`HJO/Shuffle/BraidLevelDrop.lean` computes the index shift per event type. Two shapes occur:

* **`E`**: every index stands still — at type `E` both halves of the colouring do, and a column
  carrying a crossed north step at both levels would have to carry it at two different level
  indices, which is impossible, so no bottom index moves either. Then `ζ` is **unchanged**:
  `HJO.Mellit.zCount_eq_of_componentIndex_eq`.
* **`C`**: every top index stands still and one bottom index falls from `n_P + 1` to `n_P` (the
  crossed north step of `P`'s column drops to `(X, Y - 1)`). Then `ζ` is **unchanged** too:
  `HJO.Mellit.zCount_sub_eq_zero_of_componentBotIndex_descends`.
* **`D`**: every bottom index stands still and one top index rises from `n_P - 1` to `n_P` (the
  crossed east step of ordinate `Y` moves one column right). Then `ζ` rises by exactly **one**:
  `HJO.Mellit.zCount_sub_eq_one_of_componentTopIndex_ascends`.

So the obligation's "`0` or `±1`" is right, but it is not decided by whether `P`'s antidiagonal is a
component's top or bottom — at the upper level it is neither. It is decided by which endpoint index
moves, and the answer is `0` at `C` and `E` and `+1` at `D`. Read against the move-count table of
`HJO.Mellit.card_componentCrossingIndices_eq` (`A`: `0`, `C`: `+1`, `D`: `+1`, `E`: `0`) this splits
`C` from `D` on the braid side: **both add one move, but the move added at `C` is
a `ỹ` and the move added at `D` is a `z`.**

The two shapes are supplied as hypotheses on the index families rather than derived from the event
type: deriving them means transporting `HJO.Mellit.Isolates.erase_colouringNorth` and
`HJO.Mellit.Isolates.erase_colouringEast` through the column listing `HJO.Mellit.colStep`, which
is a separate obligation and is not done here.

## Hypotheses

`0 < a`, `0 < b`, `0 < N` throughout — the two inequalities every count below turns on are
`2 ≤ aM` and `aM + 1 ≤ D`, i.e. `2 ≤ bM`, and both fail on a degenerate rectangle. The level pair
is `η_- < rk̂(P) < η_+` with `η_+ = η_- + 1`, which is the pair
`HJO.Mellit.exists_isolating_isAdmissibleLevel` builds at every lattice point (`rk̂(P) ∓ 1/2`);
`HJO.Mellit.isolates_sub_half_add_half` records that it is an `HJO.Mellit.Isolates`, so nothing
here is vacuous. Admissibility of `η_-` is used once, to know that an integer rank is never *equal*
to a level. No hypothesis on `q` or `u` appears: `HJO.Braid.zCount` is a functional on the braid
monoid and carries no parameter.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

namespace HJO.Mellit

open Braid Finset ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The rank lattice of an antidiagonal -/

/-- The common denominator `D = (a+b)(aN+1)N - 1` of `HJO.Mellit.crossingDen`, as an integer: the
step by which the above-diagonal rank falls along an antidiagonal. -/
def crossingDenInt (a b N : ℕ) : ℤ := ((a + b) * (a * N + 1) * N : ℕ) - 1

/-- `aM = a(aN+1)N`, as an integer: the step by which the above-diagonal rank rises up a column,
and the step by which the crossing index shifts the numerator of an abscissa. -/
def crossingStepInt (a N : ℕ) : ℤ := ((a * (a * N + 1) * N : ℕ) : ℤ)

/-- **The rank of the lattice point of abscissa `j` on the antidiagonal `x + y = n`**: `aM·n - D·j`.
The point itself need not lie in the rectangle, and for `j` outside `[0, aN]` there is no point —
the expression is the arithmetic progression the ranks of one antidiagonal lie in, which is what
every count below uses. -/
def antidiagRank (a b N : ℕ) (n j : ℤ) : ℤ :=
  crossingStepInt a N * n - crossingDenInt a b N * j

theorem cast_crossingDenInt (a b N : ℕ) :
    ((crossingDenInt a b N : ℤ) : ℚ) = crossingDen a b N := by
  rw [crossingDenInt, crossingDen]
  push_cast
  ring

theorem cast_crossingStepInt (a N : ℕ) :
    ((crossingStepInt a N : ℤ) : ℚ) = ((a * (a * N + 1) * N : ℕ) : ℚ) := by
  rw [crossingStepInt]
  push_cast
  ring

theorem crossingDenInt_pos (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) : 0 < crossingDenInt a b N := by
  have h : (0 : ℚ) < crossingDen a b N := crossingDen_pos ha hb hN
  rw [← cast_crossingDenInt] at h
  exact_mod_cast h

/-- **`2 ≤ aM`.** A rectangle with a column has `M = (aN+1)N ≥ 2`. -/
theorem two_le_crossingStepInt (ha : 0 < a) (hN : 0 < N) : 2 ≤ crossingStepInt a N := by
  have h : 2 ≤ a * (a * N + 1) * N := by
    calc 2 = 1 * 2 * 1 := by ring
      _ ≤ a * (a * N + 1) * N := by
        refine Nat.mul_le_mul (Nat.mul_le_mul ha ?_) hN
        have : 1 ≤ a * N := Nat.one_le_iff_ne_zero.2 (by positivity)
        omega
  rw [crossingStepInt]
  exact_mod_cast h

/-- **`aM + 1 ≤ D`**, i.e. `2 ≤ bM`: one step up a column is strictly shorter than one step along an
antidiagonal, and by at least one. This is the inequality that keeps the level line from crossing a
lattice point at a component's bottom index. -/
theorem crossingStepInt_add_one_le_crossingDenInt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    crossingStepInt a N + 1 ≤ crossingDenInt a b N := by
  have h : 2 ≤ b * (a * N + 1) * N := by
    calc 2 = 1 * 2 * 1 := by ring
      _ ≤ b * (a * N + 1) * N := by
        refine Nat.mul_le_mul (Nat.mul_le_mul hb ?_) hN
        have : 1 ≤ a * N := Nat.one_le_iff_ne_zero.2 (by positivity)
        omega
  have hsplit : ((a + b) * (a * N + 1) * N : ℕ) = a * (a * N + 1) * N + b * (a * N + 1) * N := by
    ring
  rw [crossingStepInt, crossingDenInt, hsplit]
  push_cast
  have : (2 : ℤ) ≤ ((b * (a * N + 1) * N : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at this
  linarith

/-- The rank falls by `D` at each step right along an antidiagonal. -/
theorem antidiagRank_succ_right (a b N : ℕ) (n j : ℤ) :
    antidiagRank a b N n (j + 1) = antidiagRank a b N n j - crossingDenInt a b N := by
  rw [antidiagRank, antidiagRank]
  ring

/-- Two lattice points of one antidiagonal differ in rank by `D` times the difference of their
abscissae. -/
theorem antidiagRank_sub_antidiagRank (a b N : ℕ) (n j j' : ℤ) :
    antidiagRank a b N n j - antidiagRank a b N n j' = crossingDenInt a b N * (j' - j) := by
  rw [antidiagRank, antidiagRank]
  ring

/-- The rank rises by `aM` at each step up a column: passing from the antidiagonal `n` to `n + 1` at
a fixed abscissa. -/
theorem antidiagRank_succ_left (a b N : ℕ) (n j : ℤ) :
    antidiagRank a b N (n + 1) j = antidiagRank a b N n j + crossingStepInt a N := by
  rw [antidiagRank, antidiagRank]
  ring

/-- **The above-diagonal rank, read on the antidiagonal through the point**: `rk̂(x, y)` is the
value at abscissa `x` of the progression of the antidiagonal `x + y`. -/
theorem pointRank_eq_antidiagRank (a b N x y : ℕ) :
    pointRank a b N (x, y) = antidiagRank a b N ((x : ℤ) + (y : ℤ)) (x : ℤ) := by
  rw [antidiagRank, crossingStepInt, crossingDenInt, pointRank, abovePointRank]
  push_cast
  ring

/-- An admissible level is a half-integer, so no rank is ever equal to it. -/
theorem cast_antidiagRank_ne_of_isAdmissibleLevel {η : ℚ} (hη : IsAdmissibleLevel η) (a b N : ℕ)
    (n j : ℤ) : ((antidiagRank a b N n j : ℤ) : ℚ) ≠ η := by
  obtain ⟨m, hm⟩ := hη
  intro hcon
  rw [hm] at hcon
  have h2 : (2 * antidiagRank a b N n j : ℤ) = 2 * m + 1 := by
    have : ((2 * antidiagRank a b N n j : ℤ) : ℚ) = ((2 * m + 1 : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast this
  omega

/-! ### The crossing abscissa against the rank lattice -/

/-- The rank at abscissa `j` on the antidiagonal `n`, over `ℚ`, with both constants in the form
`HJO.Mellit.crossingAbscissa_eq_div` uses. -/
theorem cast_antidiagRank_eq (a b N : ℕ) (n j : ℤ) :
    ((antidiagRank a b N n j : ℤ) : ℚ)
      = ((a * (a * N + 1) * N : ℕ) : ℚ) * (n : ℚ) - crossingDen a b N * (j : ℚ) := by
  rw [antidiagRank, Int.cast_sub, Int.cast_mul, Int.cast_mul, cast_crossingDenInt,
    cast_crossingStepInt]

/-- **The crossing abscissa, measured from any lattice point of its antidiagonal**: the level line
meets the antidiagonal `n` at `j` plus `(rk̂ - η)/D`, where `rk̂` is the rank at abscissa `j` on
that antidiagonal. -/
theorem crossingAbscissa_eq_add_div (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) (n j : ℤ) :
    crossingAbscissa a b N η n
      = (j : ℚ) + (((antidiagRank a b N n j : ℤ) : ℚ) - η) / crossingDen a b N := by
  have hD : (0 : ℚ) < crossingDen a b N := crossingDen_pos ha hb hN
  rw [crossingAbscissa_eq_div ha hb hN, cast_antidiagRank_eq]
  field_simp
  ring

/-- **The level line passes to the left of a lattice point exactly when that point outranks the
level.** The two readings of the crossing data are the same. -/
theorem crossingAbscissa_lt_iff (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) (n j : ℤ) :
    crossingAbscissa a b N η n < (j : ℚ) ↔ ((antidiagRank a b N n j : ℤ) : ℚ) < η := by
  have hD : (0 : ℚ) < crossingDen a b N := crossingDen_pos ha hb hN
  rw [crossingAbscissa_eq_div ha hb hN, div_lt_iff₀ hD, cast_antidiagRank_eq]
  constructor <;> intro h <;> linarith

/-- The contrapositive form of `HJO.Mellit.crossingAbscissa_lt_iff`. -/
theorem le_crossingAbscissa_iff (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) (n j : ℤ) :
    (j : ℚ) ≤ crossingAbscissa a b N η n ↔ η ≤ ((antidiagRank a b N n j : ℤ) : ℚ) := by
  rw [← not_lt, ← not_lt, crossingAbscissa_lt_iff ha hb hN]

/-- **A lattice point at or above the level has abscissa at most the floor.** -/
theorem le_floor_crossingAbscissa (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ} {n j : ℤ}
    (h : η ≤ ((antidiagRank a b N n j : ℤ) : ℚ)) : j ≤ ⌊crossingAbscissa a b N η n⌋ :=
  Int.le_floor.2 ((le_crossingAbscissa_iff ha hb hN η n j).2 h)

/-- **`⌊x_n(η)⌋` is the abscissa of the last lattice point of the antidiagonal `n` at or above the
level**: it is `j` exactly when the rank at `j` is at least `η` and the rank at `j + 1` is below
it. -/
theorem floor_crossingAbscissa_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ} {n j : ℤ}
    (h0 : η ≤ ((antidiagRank a b N n j : ℤ) : ℚ))
    (h1 : ((antidiagRank a b N n (j + 1) : ℤ) : ℚ) < η) :
    ⌊crossingAbscissa a b N η n⌋ = j := by
  refine le_antisymm ?_ (le_floor_crossingAbscissa ha hb hN h0)
  have h := (crossingAbscissa_lt_iff ha hb hN η n (j + 1)).2 h1
  exact Int.lt_add_one_iff.1 (Int.floor_lt.2 (by push_cast at h ⊢; linarith))

/-- The rank at the floor is at or above the level. -/
theorem le_cast_antidiagRank_floor (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) (n : ℤ) :
    η ≤ ((antidiagRank a b N n ⌊crossingAbscissa a b N η n⌋ : ℤ) : ℚ) :=
  (le_crossingAbscissa_iff ha hb hN η n _).1 (Int.floor_le _)

/-- One abscissa further right the rank has fallen below the level. -/
theorem cast_antidiagRank_floor_add_one_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) (n : ℤ) :
    ((antidiagRank a b N n (⌊crossingAbscissa a b N η n⌋ + 1) : ℤ) : ℚ) < η :=
  (crossingAbscissa_lt_iff ha hb hN η n _).1 (by push_cast; exact Int.lt_floor_add_one _)

/-! ### When a level drop moves a floor

A drop from `η_+` to `η_- = η_+ - 1` moves the abscissa of every antidiagonal right by `1/D`, and
moves its floor exactly when the lattice point just right of the old floor has its rank in the
window. The next lemma is the criterion in the form the rest of the file uses: a *margin* below the
window at that point is enough to know the floor does not move. -/

/-- **The floor of an abscissa does not move when the next lattice point along is safely below the
lower level.** -/
theorem floor_crossingAbscissa_congr_of_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {ηlo ηhi : ℚ}
    (hle : ηlo ≤ ηhi) {n : ℤ}
    (h : ((antidiagRank a b N n (⌊crossingAbscissa a b N ηhi n⌋ + 1) : ℤ) : ℚ) < ηlo) :
    ⌊crossingAbscissa a b N ηlo n⌋ = ⌊crossingAbscissa a b N ηhi n⌋ :=
  floor_crossingAbscissa_eq ha hb hN
    ((le_cast_antidiagRank_floor ha hb hN ηhi n).trans' hle) h

/-! ### The floors at the antidiagonal of the isolated point

Write `r = rk̂(P)` and `n_P = X + Y`. The level pair `η_- < r < η_+ = η_- + 1` is the one
`HJO.Mellit.exists_isolating_isAdmissibleLevel` builds. On `P`'s own antidiagonal the floor rises
from `X - 1` to `X`: the drop carries the abscissa past `P`. On the two neighbouring antidiagonals
it does not move at all, which is what the type-`C` and type-`D` index shifts are measured
against. -/

section Antidiag

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-- **At the lower level the abscissa of `P`'s antidiagonal has passed `P`.** -/
@[hjo "lem_braid_drop_zcount"]
theorem floor_crossingAbscissa_antidiag_lo (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hltP : ηlo < ((pointRank a b N (X, Y) : ℤ) : ℚ))
    (hPlt : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηlo + 1) :
    ⌊crossingAbscissa a b N ηlo ((X : ℤ) + (Y : ℤ))⌋ = (X : ℤ) := by
  have hD : (1 : ℤ) ≤ crossingDenInt a b N := crossingDenInt_pos ha hb hN
  have hD' : (1 : ℚ) ≤ ((crossingDenInt a b N : ℤ) : ℚ) := by exact_mod_cast hD
  rw [pointRank_eq_antidiagRank] at hltP hPlt
  refine floor_crossingAbscissa_eq ha hb hN hltP.le ?_
  rw [antidiagRank_succ_right]
  push_cast
  linarith

/-- **At the upper level it has not.** The two floors differ by one: this single lattice point is
the one the drop passes, and `HJO.Mellit.floor_crossingAbscissa_congr_of_ne` says it is the only
one. -/
@[hjo "lem_braid_drop_zcount"]
theorem floor_crossingAbscissa_antidiag_hi (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hltP : ηhi - 1 < ((pointRank a b N (X, Y) : ℤ) : ℚ))
    (hPlt : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηhi) :
    ⌊crossingAbscissa a b N ηhi ((X : ℤ) + (Y : ℤ))⌋ = (X : ℤ) - 1 := by
  have hD : (1 : ℤ) ≤ crossingDenInt a b N := crossingDenInt_pos ha hb hN
  have hD' : (1 : ℚ) ≤ ((crossingDenInt a b N : ℤ) : ℚ) := by exact_mod_cast hD
  rw [pointRank_eq_antidiagRank] at hltP hPlt
  refine floor_crossingAbscissa_eq ha hb hN ?_ ?_
  · rw [show (X : ℤ) - 1 = (X : ℤ) - 1 from rfl,
      show antidiagRank a b N ((X : ℤ) + (Y : ℤ)) ((X : ℤ) - 1)
        = antidiagRank a b N ((X : ℤ) + (Y : ℤ)) (X : ℤ) + crossingDenInt a b N from by
        rw [antidiagRank, antidiagRank]; ring]
    push_cast
    linarith
  · rw [show (X : ℤ) - 1 + 1 = (X : ℤ) from by ring]
    exact hPlt

/-- **One antidiagonal up from `P`, the drop moves nothing.** The rank at the abscissa `X` there is
`r + aM`, a full `aM` above the window, and the next point along is `D - aM ≥ 1` below the lower
level. -/
theorem floor_crossingAbscissa_antidiag_succ_lo (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hltP : ηlo < ((pointRank a b N (X, Y) : ℤ) : ℚ))
    (hPlt : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηlo + 1) :
    ⌊crossingAbscissa a b N ηlo ((X : ℤ) + (Y : ℤ) + 1)⌋ = (X : ℤ) := by
  have hstep : (2 : ℤ) ≤ crossingStepInt a N := two_le_crossingStepInt ha hN
  have hDle : crossingStepInt a N + 1 ≤ crossingDenInt a b N :=
    crossingStepInt_add_one_le_crossingDenInt ha hb hN
  have hstep' : (2 : ℚ) ≤ ((crossingStepInt a N : ℤ) : ℚ) := by exact_mod_cast hstep
  have hDle' : ((crossingStepInt a N : ℤ) : ℚ) + 1 ≤ ((crossingDenInt a b N : ℤ) : ℚ) := by
    exact_mod_cast hDle
  rw [pointRank_eq_antidiagRank] at hltP hPlt
  refine floor_crossingAbscissa_eq ha hb hN ?_ ?_
  · rw [antidiagRank_succ_left]
    push_cast
    linarith
  · rw [antidiagRank_succ_left, antidiagRank_succ_right]
    push_cast
    linarith

/-- **One antidiagonal down from `P`, the drop moves nothing either.** -/
theorem floor_crossingAbscissa_antidiag_pred_lo (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hltP : ηlo < ((pointRank a b N (X, Y) : ℤ) : ℚ))
    (hPlt : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηlo + 1) :
    ⌊crossingAbscissa a b N ηlo ((X : ℤ) + (Y : ℤ) - 1)⌋ = (X : ℤ) - 1 := by
  have hstep : (2 : ℤ) ≤ crossingStepInt a N := two_le_crossingStepInt ha hN
  have hDle : crossingStepInt a N + 1 ≤ crossingDenInt a b N :=
    crossingStepInt_add_one_le_crossingDenInt ha hb hN
  have hstep' : (2 : ℚ) ≤ ((crossingStepInt a N : ℤ) : ℚ) := by exact_mod_cast hstep
  have hDle' : ((crossingStepInt a N : ℤ) : ℚ) + 1 ≤ ((crossingDenInt a b N : ℤ) : ℚ) := by
    exact_mod_cast hDle
  rw [pointRank_eq_antidiagRank] at hltP hPlt
  have hkey : ∀ j : ℤ, antidiagRank a b N ((X : ℤ) + (Y : ℤ) - 1) j
      = antidiagRank a b N ((X : ℤ) + (Y : ℤ)) j - crossingStepInt a N := by
    intro j
    rw [antidiagRank, antidiagRank]
    ring
  refine floor_crossingAbscissa_eq ha hb hN ?_ ?_
  · rw [hkey, show antidiagRank a b N ((X : ℤ) + (Y : ℤ)) ((X : ℤ) - 1)
        = antidiagRank a b N ((X : ℤ) + (Y : ℤ)) (X : ℤ) + crossingDenInt a b N from by
      rw [antidiagRank, antidiagRank]; ring]
    push_cast
    linarith
  · rw [hkey, show (X : ℤ) - 1 + 1 = (X : ℤ) from by ring]
    push_cast
    linarith

end Antidiag

/-! ### The level index, read on the rank lattice

The bottom index of a component is `x + I_x + 1` with `I_x` the level index of its column
(`HJO.Mellit.componentBotIndex_eq`), so the two bounds defining `I_x` as a floor are exactly the
statement that the lattice point `(x, I_x + 1)` outranks the level and `(x, I_x)` does not. -/

/-- **The lattice point at the level index does not outrank the level.** -/
theorem cast_antidiagRank_levelIndex_le (ha : 0 < a) (hN : 0 < N) (η : ℚ) (x : ℕ) :
    ((antidiagRank a b N ((x : ℤ) + levelIndex a b N η x) (x : ℤ) : ℤ) : ℚ) ≤ η := by
  have hA : (0 : ℚ) < (((a * N + 1) * N * a : ℕ) : ℚ) := by
    have h : 0 < (a * N + 1) * N * a := by positivity
    exact_mod_cast h
  have hfl : ((levelIndex a b N η x : ℤ) : ℚ)
      ≤ (η + ((((a * N + 1) * N * b : ℕ) : ℚ) - 1) * x) / (((a * N + 1) * N * a : ℕ) : ℚ) := by
    rw [levelIndex]
    exact Int.floor_le _
  rw [le_div_iff₀ hA] at hfl
  rw [cast_antidiagRank_eq, crossingDen]
  push_cast at hfl ⊢
  nlinarith [hfl]

/-- **The lattice point one step up from the level index does outrank the level.** -/
theorem lt_cast_antidiagRank_levelIndex_succ (ha : 0 < a) (hN : 0 < N) (η : ℚ) (x : ℕ) :
    η < ((antidiagRank a b N ((x : ℤ) + levelIndex a b N η x + 1) (x : ℤ) : ℤ) : ℚ) := by
  have hA : (0 : ℚ) < (((a * N + 1) * N * a : ℕ) : ℚ) := by
    have h : 0 < (a * N + 1) * N * a := by positivity
    exact_mod_cast h
  have hfl : (η + ((((a * N + 1) * N * b : ℕ) : ℚ) - 1) * x) / (((a * N + 1) * N * a : ℕ) : ℚ)
      < ((levelIndex a b N η x : ℤ) : ℚ) + 1 := by
    rw [levelIndex]
    exact Int.lt_floor_add_one _
  rw [div_lt_iff₀ hA] at hfl
  rw [cast_antidiagRank_eq, crossingDen]
  push_cast at hfl ⊢
  nlinarith [hfl]

/-! ### The rotation moves no component endpoint past a lattice point

This is the half of the obligation that decides it. Both proofs are the same count: the endpoint's
own antidiagonal has its next lattice point a full `D` further right, while the endpoint condition
pins the level to within `aM` (at a bottom) or `D - aM` (at a top) of the rank there. A rotation by
`1/D` cannot reach across the gap that is left. -/

/-- **A crossed east step's antidiagonal keeps its floor across the drop.** The east step `(x, i)`
of `η_+` has `rk̂(x, i) > η_+` and `rk̂(x + 1, i) = rk̂(x, i) - (D - aM) < η_+`, so the next lattice
point right of the floor on the antidiagonal `x + i` is below `η_+ - aM ≤ η_+ - 2`, and the drop by
`1` leaves the floor where it was. -/
theorem floor_crossingAbscissa_congr_of_mem_colouringEast (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {ηlo ηhi : ℚ} (hstep : ηhi = ηlo + 1) {y : Heights a b N} {x i : ℕ}
    (hmem : (x, i) ∈ colouringEast y ηhi) :
    ⌊crossingAbscissa a b N ηlo ((x : ℤ) + (i : ℤ))⌋
      = ⌊crossingAbscissa a b N ηhi ((x : ℤ) + (i : ℤ))⌋ := by
  have hD : (0 : ℤ) < crossingDenInt a b N := crossingDenInt_pos ha hb hN
  have hstep2 : (2 : ℤ) ≤ crossingStepInt a N := two_le_crossingStepInt ha hN
  have hD' : (0 : ℚ) < ((crossingDenInt a b N : ℤ) : ℚ) := by exact_mod_cast hD
  have hstep2' : (2 : ℚ) ≤ ((crossingStepInt a N : ℤ) : ℚ) := by exact_mod_cast hstep2
  obtain ⟨-, hne, hlt⟩ := Finset.mem_filter.1 hmem
  set n : ℤ := (x : ℤ) + (i : ℤ) with hn
  have hx : ((antidiagRank a b N n (x : ℤ) : ℤ) : ℚ) = ((pointRank a b N (x, i) : ℤ) : ℚ) := by
    rw [hn, ← pointRank_eq_antidiagRank]
  have hx1 : ((antidiagRank a b N n ((x : ℤ) + 1) : ℤ) : ℚ)
      = ((pointRank a b N (x, i) : ℤ) : ℚ) - ((crossingDenInt a b N : ℤ) : ℚ) := by
    rw [← hx, antidiagRank_succ_right]
    push_cast
    ring
  have heast : ((pointRank a b N (x + 1, i) : ℤ) : ℚ)
      = ((pointRank a b N (x, i) : ℤ) : ℚ) + ((crossingStepInt a N : ℤ) : ℚ)
        - ((crossingDenInt a b N : ℤ) : ℚ) := by
    rw [pointRank_eq_antidiagRank, pointRank_eq_antidiagRank]
    rw [show ((x + 1 : ℕ) : ℤ) + (i : ℤ) = ((x : ℤ) + (i : ℤ)) + 1 from by push_cast; ring,
      show ((x + 1 : ℕ) : ℤ) = (x : ℤ) + 1 from by push_cast; ring,
      antidiagRank_succ_left, antidiagRank_succ_right]
    push_cast
    ring
  -- the floor is at least `x`, the level being below the rank there
  have hxle : (x : ℤ) ≤ ⌊crossingAbscissa a b N ηhi n⌋ :=
    le_floor_crossingAbscissa ha hb hN (by rw [hx]; exact hlt.le)
  set j : ℤ := ⌊crossingAbscissa a b N ηhi n⌋ with hj
  have hgap : ((antidiagRank a b N n (j + 1) : ℤ) : ℚ)
      ≤ ((antidiagRank a b N n (x : ℤ) : ℤ) : ℚ) - ((crossingDenInt a b N : ℤ) : ℚ) := by
    have hone : (1 : ℤ) ≤ (j + 1) - (x : ℤ) := by omega
    have hkey := antidiagRank_sub_antidiagRank a b N n (x : ℤ) (j + 1)
    have hmul : crossingDenInt a b N * 1 ≤ crossingDenInt a b N * ((j + 1) - (x : ℤ)) :=
      mul_le_mul_of_nonneg_left hone hD.le
    have h2 : crossingDenInt a b N
        ≤ antidiagRank a b N n (x : ℤ) - antidiagRank a b N n (j + 1) := by linarith
    have h3 : ((crossingDenInt a b N : ℤ) : ℚ)
        ≤ ((antidiagRank a b N n (x : ℤ) - antidiagRank a b N n (j + 1) : ℤ) : ℚ) := by
      exact_mod_cast h2
    push_cast at h3
    linarith
  refine floor_crossingAbscissa_congr_of_lt ha hb hN (by rw [hstep]; linarith) ?_
  rw [hx] at hgap
  rw [heast] at hne
  linarith [hne, hgap, hstep2', hstep]

/-- **A column's bottom index keeps its floor across the drop.** The bottom index of the component
at column `x` is `x + I_x + 1`, and `rk̂(x, I_x + 1) > η_+ ≥ rk̂(x, I_x) = rk̂(x, I_x + 1) - aM`, so
the next lattice point right of the floor on that antidiagonal is at most `η_+ + aM - D ≤ η_+ - 1`
below — and never *equal* to `η_-` being admissible and the rank an integer. -/
theorem floor_crossingAbscissa_congr_of_levelIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {ηlo ηhi : ℚ} (hadm : IsAdmissibleLevel ηlo) (hstep : ηhi = ηlo + 1) (x : ℕ) :
    ⌊crossingAbscissa a b N ηlo ((x : ℤ) + levelIndex a b N ηhi x + 1)⌋
      = ⌊crossingAbscissa a b N ηhi ((x : ℤ) + levelIndex a b N ηhi x + 1)⌋ := by
  have hD : (0 : ℤ) < crossingDenInt a b N := crossingDenInt_pos ha hb hN
  have hDle : crossingStepInt a N + 1 ≤ crossingDenInt a b N :=
    crossingStepInt_add_one_le_crossingDenInt ha hb hN
  have hD' : (0 : ℚ) < ((crossingDenInt a b N : ℤ) : ℚ) := by exact_mod_cast hD
  have hDle' : ((crossingStepInt a N : ℤ) : ℚ) + 1 ≤ ((crossingDenInt a b N : ℤ) : ℚ) := by
    exact_mod_cast hDle
  set n : ℤ := (x : ℤ) + levelIndex a b N ηhi x + 1 with hn
  have hup : ηhi < ((antidiagRank a b N n (x : ℤ) : ℤ) : ℚ) :=
    lt_cast_antidiagRank_levelIndex_succ ha hN ηhi x
  have hdn : ((antidiagRank a b N n (x : ℤ) : ℤ) : ℚ) - ((crossingStepInt a N : ℤ) : ℚ) ≤ ηhi := by
    have h := cast_antidiagRank_levelIndex_le (b := b) ha hN ηhi x
    have hstepdown : antidiagRank a b N ((x : ℤ) + levelIndex a b N ηhi x) (x : ℤ)
        = antidiagRank a b N n (x : ℤ) - crossingStepInt a N := by
      rw [hn, show (x : ℤ) + levelIndex a b N ηhi x + 1
          = ((x : ℤ) + levelIndex a b N ηhi x) + 1 from by ring, antidiagRank_succ_left]
      ring
    rw [hstepdown] at h
    push_cast at h
    linarith
  have hxle : (x : ℤ) ≤ ⌊crossingAbscissa a b N ηhi n⌋ :=
    le_floor_crossingAbscissa ha hb hN hup.le
  set j : ℤ := ⌊crossingAbscissa a b N ηhi n⌋ with hj
  have hgap : ((antidiagRank a b N n (j + 1) : ℤ) : ℚ)
      ≤ ((antidiagRank a b N n (x : ℤ) : ℤ) : ℚ) - ((crossingDenInt a b N : ℤ) : ℚ) := by
    have hone : (1 : ℤ) ≤ (j + 1) - (x : ℤ) := by omega
    have hkey := antidiagRank_sub_antidiagRank a b N n (x : ℤ) (j + 1)
    have hmul : crossingDenInt a b N * 1 ≤ crossingDenInt a b N * ((j + 1) - (x : ℤ)) :=
      mul_le_mul_of_nonneg_left hone hD.le
    have h2 : crossingDenInt a b N
        ≤ antidiagRank a b N n (x : ℤ) - antidiagRank a b N n (j + 1) := by linarith
    have h3 : ((crossingDenInt a b N : ℤ) : ℚ)
        ≤ ((antidiagRank a b N n (x : ℤ) - antidiagRank a b N n (j + 1) : ℤ) : ℚ) := by
      exact_mod_cast h2
    push_cast at h3
    linarith
  refine floor_crossingAbscissa_congr_of_lt ha hb hN (by rw [hstep]; linarith) ?_
  have hle : ((antidiagRank a b N n (j + 1) : ℤ) : ℚ) ≤ ηlo := by
    rw [hstep] at hdn
    linarith
  exact lt_of_le_of_ne hle (cast_antidiagRank_ne_of_isAdmissibleLevel hadm a b N n (j + 1))

/-- **The top index of a component keeps its floor across the drop.** -/
theorem floor_crossingAbscissa_componentTopIndex_congr (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {ηlo ηhi : ℚ} (hhi : IsAdmissibleLevel ηhi) (hηhi : 0 < ηhi) (hstep : ηhi = ηlo + 1)
    {y : Heights a b N} {i : ℕ} (hi : i < #(colouringEast y ηhi)) :
    ⌊crossingAbscissa a b N ηlo (componentTopIndex a b N y ηhi i)⌋
      = ⌊crossingAbscissa a b N ηhi (componentTopIndex a b N y ηhi i)⌋ := by
  have hmem := colStep_mem hi
  rw [componentTopIndex_eq ha hb hN hhi hηhi hi]
  exact floor_crossingAbscissa_congr_of_mem_colouringEast ha hb hN hstep hmem

/-- **The bottom index of a component keeps its floor across the drop.** -/
theorem floor_crossingAbscissa_componentBotIndex_congr (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {ηlo ηhi : ℚ} (hlo : IsAdmissibleLevel ηlo) (hhi : IsAdmissibleLevel ηhi) (hηhi : 0 < ηhi)
    (hstep : ηhi = ηlo + 1) (y : Heights a b N) (i : ℕ) :
    ⌊crossingAbscissa a b N ηlo (componentBotIndex a b N y ηhi i)⌋
      = ⌊crossingAbscissa a b N ηhi (componentBotIndex a b N y ηhi i)⌋ := by
  rw [componentBotIndex_eq ha hb hN hhi hηhi y i]
  exact floor_crossingAbscissa_congr_of_levelIndex ha hb hN hlo hstep _

/-! ### `P`'s antidiagonal is not a component endpoint at the level dropped from

This is the obligation's disjunction, decided: neither. -/

section Endpoint

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-- **No component's top index is the antidiagonal of `P`.** If it were, the floor of that abscissa
would both move (it is `P`'s own antidiagonal, and the drop carries it past `P`) and stand still
(it is a component's top index). -/
@[hjo "lem_braid_drop_zcount"]
theorem componentTopIndex_ne_antidiag (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hhi : IsAdmissibleLevel ηhi) (hηhi : 0 < ηhi) (hstep : ηhi = ηlo + 1)
    (hltP : ηlo < ((pointRank a b N (X, Y) : ℤ) : ℚ))
    (hPlt : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηhi)
    {y : Heights a b N} {i : ℕ} (hi : i < #(colouringEast y ηhi)) :
    componentTopIndex a b N y ηhi i ≠ (X : ℤ) + (Y : ℤ) := by
  intro hcon
  have h := floor_crossingAbscissa_componentTopIndex_congr ha hb hN hhi hηhi hstep hi
  rw [hcon] at h
  rw [floor_crossingAbscissa_antidiag_lo ha hb hN hltP (by rw [hstep] at hPlt; linarith),
    floor_crossingAbscissa_antidiag_hi ha hb hN (by rw [hstep]; linarith) hPlt] at h
  omega

/-- **No component's bottom index is the antidiagonal of `P`** either. -/
@[hjo "lem_braid_drop_zcount"]
theorem componentBotIndex_ne_antidiag (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hlo : IsAdmissibleLevel ηlo) (hhi : IsAdmissibleLevel ηhi) (hηhi : 0 < ηhi)
    (hstep : ηhi = ηlo + 1)
    (hltP : ηlo < ((pointRank a b N (X, Y) : ℤ) : ℚ))
    (hPlt : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηhi)
    (y : Heights a b N) (i : ℕ) :
    componentBotIndex a b N y ηhi i ≠ (X : ℤ) + (Y : ℤ) := by
  intro hcon
  have h := floor_crossingAbscissa_componentBotIndex_congr ha hb hN hlo hhi hηhi hstep y i
  rw [hcon] at h
  rw [floor_crossingAbscissa_antidiag_lo ha hb hN hltP (by rw [hstep] at hPlt; linarith),
    floor_crossingAbscissa_antidiag_hi ha hb hN (by rw [hstep]; linarith) hPlt] at h
  omega

/-! ### Exactly one antidiagonal moves

`HJO.Mellit.exists_isolating_isAdmissibleLevel` says the window `(η_-, η_+)` holds the rank of one
lattice point of the rectangle. On the crossing lattice that says: the drop moves the floor of `P`'s
own antidiagonal and of no other. The proof below does **not** use the isolation hypothesis
`HJO.Mellit.Isolates`: two integers in a window of width `1` are equal, so the lattice point the
drop passes has the rank of `P` outright, and then `aM(n - n_P) = D(j - X)` with `M` coprime to `D`
and `a·(aN + bN) < D` forces `n = n_P`. Isolation is a consequence here, not an input. -/

/-- `a(aN + bN) < D`: the whole span of antidiagonal indices of the rectangle, multiplied by `a`,
still falls short of one step along an antidiagonal. -/
theorem mul_add_lt_crossingDenInt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    (a : ℤ) * ((a * N : ℤ) + (b * N : ℤ)) < crossingDenInt a b N := by
  have ha' : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
  have hN' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hD : (crossingDenInt a b N : ℤ)
      = ((a : ℤ) + (b : ℤ)) * ((a : ℤ) * (N : ℤ) + 1) * (N : ℤ) - 1 := by
    rw [crossingDenInt]
    push_cast
    ring
  have hN1 : (0 : ℤ) ≤ (N : ℤ) - 1 := by linarith
  have h1 : (0 : ℤ) ≤ (a : ℤ) * ((a : ℤ) + (b : ℤ)) * (N : ℤ) * ((N : ℤ) - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) hN1
  have h2 : (2 : ℤ) ≤ ((a : ℤ) + (b : ℤ)) * (N : ℤ) := by nlinarith
  have hkey : ((a : ℤ) + (b : ℤ)) * ((a : ℤ) * (N : ℤ) + 1) * (N : ℤ) - 1
      - (a : ℤ) * ((a * N : ℤ) + (b * N : ℤ))
      = (a : ℤ) * ((a : ℤ) + (b : ℤ)) * (N : ℤ) * ((N : ℤ) - 1)
        + (((a : ℤ) + (b : ℤ)) * (N : ℤ) - 1) := by
    ring
  rw [hD]
  linarith

/-- **The drop moves no floor but the one of `P`'s antidiagonal.** For an antidiagonal index `n` in
the range of the rectangle other than `n_P = X + Y`, the abscissa of `n` passes no lattice point:
the level line would otherwise cross a second point of rank inside the window, and the window holds
only `rk̂(P)`. -/
@[hjo "lem_braid_drop_zcount"]
theorem floor_crossingAbscissa_congr_of_ne (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {ηlo ηhi : ℚ}
    (hlo : IsAdmissibleLevel ηlo) (hstep : ηhi = ηlo + 1) {X Y : ℕ}
    (hltP : ηlo < ((pointRank a b N (X, Y) : ℤ) : ℚ))
    (hPlt : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηhi)
    (hX : X ≤ a * N) (hY : Y ≤ b * N) {n : ℤ}
    (hn0 : 0 ≤ n) (hn1 : n ≤ (a * N : ℤ) + (b * N : ℤ)) (hne : n ≠ (X : ℤ) + (Y : ℤ)) :
    ⌊crossingAbscissa a b N ηlo n⌋ = ⌊crossingAbscissa a b N ηhi n⌋ := by
  have hDpos : (0 : ℤ) < crossingDenInt a b N := crossingDenInt_pos ha hb hN
  set j : ℤ := ⌊crossingAbscissa a b N ηhi n⌋ + 1 with hj
  by_contra hcon
  -- the lattice point at `j` has its rank in the window
  have hupper : ((antidiagRank a b N n j : ℤ) : ℚ) < ηhi :=
    cast_antidiagRank_floor_add_one_lt ha hb hN ηhi n
  have hlower : ηlo < ((antidiagRank a b N n j : ℤ) : ℚ) := by
    rcases lt_or_ge ((antidiagRank a b N n j : ℤ) : ℚ) ηlo with h | h
    · exact absurd (floor_crossingAbscissa_congr_of_lt ha hb hN (by rw [hstep]; linarith) h) hcon
    · exact lt_of_le_of_ne h (Ne.symm (cast_antidiagRank_ne_of_isAdmissibleLevel hlo a b N n j))
  -- two integers in a window of width one are equal
  have hrank : antidiagRank a b N n j = pointRank a b N (X, Y) := by
    have h1 : ((antidiagRank a b N n j : ℤ) : ℚ) < ((pointRank a b N (X, Y) : ℤ) : ℚ) + 1 := by
      rw [hstep] at hupper; linarith
    have h2 : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ((antidiagRank a b N n j : ℤ) : ℚ) + 1 := by
      rw [hstep] at hPlt; linarith
    have h1' : antidiagRank a b N n j < pointRank a b N (X, Y) + 1 := by exact_mod_cast h1
    have h2' : pointRank a b N (X, Y) < antidiagRank a b N n j + 1 := by exact_mod_cast h2
    omega
  -- so `aM (n - n_P) = D (j - X)`, and `D` is coprime to `M`
  rw [pointRank_eq_antidiagRank, antidiagRank, antidiagRank, crossingStepInt] at hrank
  set d : ℤ := n - ((X : ℤ) + (Y : ℤ)) with hd
  set e : ℤ := j - (X : ℤ) with he
  have hkey : ((a : ℤ) * ((a * N : ℤ) + 1) * (N : ℤ)) * d = crossingDenInt a b N * e := by
    rw [hd, he]
    push_cast at hrank ⊢
    linarith
  have hcop : IsCoprime (crossingDenInt a b N) (((a * N : ℤ) + 1) * (N : ℤ)) := by
    refine ⟨-1, (a : ℤ) + (b : ℤ), ?_⟩
    rw [crossingDenInt]
    push_cast
    ring
  have hdvd : crossingDenInt a b N ∣ (a : ℤ) * d := by
    refine hcop.dvd_of_dvd_mul_right ⟨e, ?_⟩
    rw [← hkey]
    ring
  have hlt : |(a : ℤ) * d| < crossingDenInt a b N := by
    have hda : |d| ≤ (a * N : ℤ) + (b * N : ℤ) := by
      rw [hd, abs_le]
      have hX' : (X : ℤ) ≤ (a * N : ℤ) := by exact_mod_cast hX
      have hY' : (Y : ℤ) ≤ (b * N : ℤ) := by exact_mod_cast hY
      have hX0 : (0 : ℤ) ≤ (X : ℤ) := Int.natCast_nonneg _
      have hY0 : (0 : ℤ) ≤ (Y : ℤ) := Int.natCast_nonneg _
      constructor <;> omega
    have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg _
    calc |(a : ℤ) * d| = (a : ℤ) * |d| := by rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ (a : ℤ) * ((a * N : ℤ) + (b * N : ℤ)) := by
        exact mul_le_mul_of_nonneg_left hda ha0
      _ < crossingDenInt a b N := mul_add_lt_crossingDenInt ha hb hN
  have hzero : (a : ℤ) * d = 0 := by
    by_contra h0
    exact absurd (Int.le_of_dvd (abs_pos.2 h0) ((dvd_abs _ _).2 hdvd)) (not_le.2 hlt)
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  exact hne (by have : d = 0 := by
                  rcases mul_eq_zero.1 hzero with h | h
                  · exact absurd h ha0
                  · exact h
                omega)

/-- The canonical isolating pair at a lattice point is `rk̂(P) ∓ 1/2`, and it is an
`HJO.Mellit.Isolates`: two admissible levels a distance `1` apart, bracketing `rk̂(P)` and no other
rank. So the hypotheses of this file's theorems — a drop by exactly one, past one point — are the
ones `HJO.Mellit.exists_isolating_isAdmissibleLevel` supplies, and nothing here is vacuous. -/
theorem isolates_sub_half_add_half (a b N : ℕ) {X Y : ℕ} (hX : X ≤ a * N) (hY : Y ≤ b * N) :
    Isolates a b N X Y (((pointRank a b N (X, Y) : ℤ) : ℚ) - 1 / 2)
      (((pointRank a b N (X, Y) : ℤ) : ℚ) + 1 / 2) where
  lo := ⟨pointRank a b N (X, Y) - 1, by push_cast; ring⟩
  hi := ⟨pointRank a b N (X, Y), by norm_num⟩
  ltP := by norm_num
  Plt := by norm_num
  iso Q _ _ h1 h2 := by
    have h1' : pointRank a b N (X, Y) - 1 < pointRank a b N Q := by
      have : ((pointRank a b N (X, Y) - 1 : ℤ) : ℚ) < ((pointRank a b N Q : ℤ) : ℚ) := by
        push_cast
        linarith
      exact_mod_cast this
    have h2' : pointRank a b N Q < pointRank a b N (X, Y) + 1 := by
      have : ((pointRank a b N Q : ℤ) : ℚ) < ((pointRank a b N (X, Y) + 1 : ℤ) : ℚ) := by
        push_cast
        linarith
      exact_mod_cast this
    omega
  xle := hX
  yle := hY

end Endpoint

/-! ### The change of `ζ` across the drop

Putting the two halves together. The `z`-count is a sum over components of a difference of two
floors; the rotation moves none of those floors (the previous section); so the whole change is the
change of the *indices*, and it can be read entirely at the lower level. -/

section Ledger

variable {ηlo ηhi : ℚ} {y : Heights a b N}

/-- **The `z`-count of a level drop is carried by the component indices, not by the rotation.**

At two levels with the same number of components, the change of `ζ` across the drop is

`∑_i (⌊x_{T_i(η_-)}(η_-)⌋ - ⌊x_{T_i(η_+)}(η_-)⌋) - ∑_i (⌊x_{B_i(η_-)}(η_-)⌋ - ⌊x_{B_i(η_+)}(η_-)⌋)`,

**both terms evaluated at the lower level**: every floor of an index that does not move contributes
nothing, by `HJO.Mellit.floor_crossingAbscissa_componentTopIndex_congr` and
`HJO.Mellit.floor_crossingAbscissa_componentBotIndex_congr`. This is the residual obligation of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` discharged, in the sharp form: the rigid
rotation of `HJO.Mellit.sweepTheta_eq_div` is invisible to `HJO.Braid.zCount`, and what is left is
the combinatorial descent of `HJO.Mellit.Isolates.notMem_colouringNorth_lo`. -/
@[hjo "lem_braid_drop_zcount"]
theorem zCount_sub_eq_sum_index_shift (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hlo : IsAdmissibleLevel ηlo) (hhi : IsAdmissibleLevel ηhi)
    (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi = ηlo + 1) (hy : IsAboveDiagonal y)
    (hcard : #(colouringNorth y ηlo) = #(colouringNorth y ηhi))
    (hklo : 1 ≤ #(colouringNorth y ηlo)) (hkhi : 1 ≤ #(colouringNorth y ηhi)) :
    (zCount #(colouringNorth y ηlo) hklo (specialBraid (sweepTheta a b N)
        (braidDataOfColouring a b N y ηlo #(colouringNorth y ηlo)).1
        (braidDataOfColouring a b N y ηlo #(colouringNorth y ηlo)).2) : ℤ)
      - (zCount #(colouringNorth y ηhi) hkhi (specialBraid (sweepTheta a b N)
          (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).1
          (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).2) : ℤ)
      = ∑ i ∈ Finset.range #(colouringNorth y ηhi),
          ((⌊crossingAbscissa a b N ηlo (componentTopIndex a b N y ηlo i)⌋
              - ⌊crossingAbscissa a b N ηlo (componentTopIndex a b N y ηhi i)⌋)
            - (⌊crossingAbscissa a b N ηlo (componentBotIndex a b N y ηlo i)⌋
              - ⌊crossingAbscissa a b N ηlo (componentBotIndex a b N y ηhi i)⌋)) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := by rw [hstep]; linarith
  have hpos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  rw [zCount_specialBraid_braidDataOfColouring ha hb hN hlo hηlo hy hklo,
    zCount_specialBraid_braidDataOfColouring ha hb hN hhi hηhi hy hkhi,
    Fin.sum_univ_eq_sum_range (fun m : ℕ =>
        ⌊crossingAbscissa a b N ηlo (componentTopIndex a b N y ηlo m)⌋
          - ⌊crossingAbscissa a b N ηlo (componentBotIndex a b N y ηlo m)⌋)
      #(colouringNorth y ηlo),
    Fin.sum_univ_eq_sum_range (fun m : ℕ =>
        ⌊crossingAbscissa a b N ηhi (componentTopIndex a b N y ηhi m)⌋
          - ⌊crossingAbscissa a b N ηhi (componentBotIndex a b N y ηhi m)⌋)
      #(colouringNorth y ηhi),
    hcard, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < #(colouringNorth y ηhi) := Finset.mem_range.1 hi
  have hiE : i < #(colouringEast y ηhi) := by
    rw [← card_colouringNorth_eq_card_colouringEast hb hN hhi hηhi hy]
    exact hi'
  rw [← floor_crossingAbscissa_componentTopIndex_congr ha hb hN hhi hpos hstep hiE,
    ← floor_crossingAbscissa_componentBotIndex_congr ha hb hN hlo hhi hpos hstep y i]
  ring

/-- **A rigid rotation of the whole configuration costs no `z` letter: the type-`E` prediction.**

If the level drop leaves every component's crossing-index interval where it was — which by
`HJO.Mellit.Isolates.braidData_of_eventType_E` is what happens at an event of type `E`, both halves
of the colouring standing still there — then `ζ` is unchanged, even though the position tuple `v`
has rotated by `1/D` and `HJO.Braid.exists_rotation_specialBraid_ne` shows a rotation can be seen
by `ζ` in general. The rotation of a level drop is too small to carry any *endpoint* crossing past
a lattice point: that is
`HJO.Mellit.floor_crossingAbscissa_componentTopIndex_congr` and its bottom twin.

So `HJO.Braid.zCount` supplies **no** obstruction at type `E`: the `u` of rule `E` in
`HJO.Mellit.dsc_eq_dminus_add_smul` is not accounted for by a change in the number of `z` letters.
Whatever distinguishes the two sides there, it is not this functional. -/
@[hjo "lem_braid_drop_zcount"]
theorem zCount_eq_of_componentIndex_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hlo : IsAdmissibleLevel ηlo) (hhi : IsAdmissibleLevel ηhi)
    (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi = ηlo + 1) (hy : IsAboveDiagonal y)
    (hcard : #(colouringNorth y ηlo) = #(colouringNorth y ηhi))
    (hklo : 1 ≤ #(colouringNorth y ηlo)) (hkhi : 1 ≤ #(colouringNorth y ηhi))
    (htop : ∀ i < #(colouringNorth y ηhi),
      componentTopIndex a b N y ηlo i = componentTopIndex a b N y ηhi i)
    (hbot : ∀ i < #(colouringNorth y ηhi),
      componentBotIndex a b N y ηlo i = componentBotIndex a b N y ηhi i) :
    (zCount #(colouringNorth y ηlo) hklo (specialBraid (sweepTheta a b N)
        (braidDataOfColouring a b N y ηlo #(colouringNorth y ηlo)).1
        (braidDataOfColouring a b N y ηlo #(colouringNorth y ηlo)).2) : ℤ)
      = (zCount #(colouringNorth y ηhi) hkhi (specialBraid (sweepTheta a b N)
          (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).1
          (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).2) : ℤ) := by
  have h := zCount_sub_eq_sum_index_shift ha hb hN hlo hhi hηlo hstep hy hcard hklo hkhi
  rw [Finset.sum_eq_zero fun i hi => ?_] at h
  · linarith
  · have hi' : i < #(colouringNorth y ηhi) := Finset.mem_range.1 hi
    rw [htop i hi', hbot i hi']
    ring

variable {X Y : ℕ}

/-- **A bottom index descending onto `P`'s antidiagonal costs no `z` letter: the type-`C`
prediction.**

At an event of type `C` the crossed east steps stand still, so every top index does
(`HJO.Mellit.Isolates.colouringEast_eq_of_eventType_C` with `HJO.Mellit.componentTopIndex_eq`),
while the crossed north step of `P`'s column moves from `(X, Y)` to `(X, Y - 1)`, so the level index
of that column drops by one and, by `HJO.Mellit.componentBotIndex_eq`, the bottom index of the one
component sitting there falls from `n_P + 1` to `n_P`. Then

`ζ(B_{s,v',α'}) = ζ(B_{s,v,α})`:

the component gains one crossing at its bottom end and the crossing it gains passes no integer. Read
against `HJO.Mellit.card_componentCrossingIndices_eq`, whose type-`C` row is `+1` move: **the move
type `C` adds is a `ỹ` letter, not a `z`.** -/
@[hjo "lem_braid_drop_zcount"]
theorem zCount_sub_eq_zero_of_componentBotIndex_descends (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hlo : IsAdmissibleLevel ηlo) (hhi : IsAdmissibleLevel ηhi)
    (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi = ηlo + 1) (hy : IsAboveDiagonal y)
    (hcard : #(colouringNorth y ηlo) = #(colouringNorth y ηhi))
    (hklo : 1 ≤ #(colouringNorth y ηlo)) (hkhi : 1 ≤ #(colouringNorth y ηhi))
    (hltP : ηlo < ((pointRank a b N (X, Y) : ℤ) : ℚ))
    (hPlt : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηhi) {i₀ : ℕ}
    (htop : ∀ i < #(colouringNorth y ηhi),
      componentTopIndex a b N y ηlo i = componentTopIndex a b N y ηhi i)
    (hbot : ∀ i < #(colouringNorth y ηhi), i ≠ i₀ →
      componentBotIndex a b N y ηlo i = componentBotIndex a b N y ηhi i)
    (hbothi : componentBotIndex a b N y ηhi i₀ = (X : ℤ) + (Y : ℤ) + 1)
    (hbotlo : componentBotIndex a b N y ηlo i₀ = (X : ℤ) + (Y : ℤ)) :
    (zCount #(colouringNorth y ηlo) hklo (specialBraid (sweepTheta a b N)
        (braidDataOfColouring a b N y ηlo #(colouringNorth y ηlo)).1
        (braidDataOfColouring a b N y ηlo #(colouringNorth y ηlo)).2) : ℤ)
      - (zCount #(colouringNorth y ηhi) hkhi (specialBraid (sweepTheta a b N)
          (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).1
          (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).2) : ℤ) = 0 := by
  have hPlt' : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηlo + 1 := by rw [hstep] at hPlt; exact hPlt
  rw [zCount_sub_eq_sum_index_shift ha hb hN hlo hhi hηlo hstep hy hcard hklo hkhi]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i < #(colouringNorth y ηhi) := Finset.mem_range.1 hi
  rw [htop i hi']
  by_cases h : i = i₀
  · subst h
    rw [hbothi, hbotlo, floor_crossingAbscissa_antidiag_lo ha hb hN hltP hPlt',
      floor_crossingAbscissa_antidiag_succ_lo ha hb hN hltP hPlt']
    ring
  · rw [hbot i hi' h]
    ring

/-- **A top index ascending onto `P`'s antidiagonal costs exactly one `z` letter: the type-`D`
prediction.**

At an event of type `D` the crossed north steps stand still, so every bottom index does, while the
crossed east step of ordinate `Y` moves from `(X - 1, Y)` to `(X, Y)`
(`HJO.Mellit.Isolates.colouringEast_eq_of_eventType_D`), so one top index rises from `n_P - 1` to
`n_P`. Then

`ζ(B_{s,v',α'}) = ζ(B_{s,v,α}) + 1`:

the crossing the component gains at its top end is the one whose abscissa the drop has just carried
past the lattice point `P`. Read against `HJO.Mellit.card_componentCrossingIndices_eq`, whose
type-`D` row is also `+1` move: **the move type `D` adds is a `z` letter.** This is the statement
on the braid side that separates `C` from `D`; the letter count alone does not. -/
@[hjo "lem_braid_drop_zcount"]
theorem zCount_sub_eq_one_of_componentTopIndex_ascends (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hlo : IsAdmissibleLevel ηlo) (hhi : IsAdmissibleLevel ηhi)
    (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi = ηlo + 1) (hy : IsAboveDiagonal y)
    (hcard : #(colouringNorth y ηlo) = #(colouringNorth y ηhi))
    (hklo : 1 ≤ #(colouringNorth y ηlo)) (hkhi : 1 ≤ #(colouringNorth y ηhi))
    (hltP : ηlo < ((pointRank a b N (X, Y) : ℤ) : ℚ))
    (hPlt : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηhi) {i₀ : ℕ}
    (hi₀ : i₀ < #(colouringNorth y ηhi))
    (hbot : ∀ i < #(colouringNorth y ηhi),
      componentBotIndex a b N y ηlo i = componentBotIndex a b N y ηhi i)
    (htop : ∀ i < #(colouringNorth y ηhi), i ≠ i₀ →
      componentTopIndex a b N y ηlo i = componentTopIndex a b N y ηhi i)
    (htophi : componentTopIndex a b N y ηhi i₀ = (X : ℤ) + (Y : ℤ) - 1)
    (htoplo : componentTopIndex a b N y ηlo i₀ = (X : ℤ) + (Y : ℤ)) :
    (zCount #(colouringNorth y ηlo) hklo (specialBraid (sweepTheta a b N)
        (braidDataOfColouring a b N y ηlo #(colouringNorth y ηlo)).1
        (braidDataOfColouring a b N y ηlo #(colouringNorth y ηlo)).2) : ℤ)
      - (zCount #(colouringNorth y ηhi) hkhi (specialBraid (sweepTheta a b N)
          (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).1
          (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).2) : ℤ) = 1 := by
  have hPlt' : ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηlo + 1 := by rw [hstep] at hPlt; exact hPlt
  rw [zCount_sub_eq_sum_index_shift ha hb hN hlo hhi hηlo hstep hy hcard hklo hkhi,
    Finset.sum_eq_single_of_mem i₀ (Finset.mem_range.2 hi₀) ?_]
  · rw [hbot i₀ hi₀, htophi, htoplo,
      floor_crossingAbscissa_antidiag_lo ha hb hN hltP hPlt',
      floor_crossingAbscissa_antidiag_pred_lo ha hb hN hltP hPlt']
    ring
  · intro i hi hne
    have hi' : i < #(colouringNorth y ηhi) := Finset.mem_range.1 hi
    rw [htop i hi' hne, hbot i hi']
    ring

end Ledger

end HJO.Mellit

end
