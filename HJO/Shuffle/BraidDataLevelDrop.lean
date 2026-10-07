/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidLevelDrop
public import HJO.Shuffle.BraidRep
public meta import HJO.Attr

/-! # The position tuple of a colouring's braid data across one level drop

`HJO/Shuffle/BraidLevelDrop.lean` settles what the level drop of
`HJO.Mellit.Isolates.notMem_colouringNorth_lo` does to the *multiplicities* `α` of
`HJO.Mellit.braidDataOfColouring`, and hence to the number of letters of `B_{s,v,α}` — that is
`HJO.Mellit.card_componentCrossingIndices_eq`. It says nothing about the *positions* `v`, and the
four clauses of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` are identities between braids,
which read `v` as well.

This file supplies the missing half, and the answer is sharper than the shape of `v` suggests.

## The position tuple is an integer tuple rotated by the level

`HJO.Mellit.braidDataOfColouring_fst_eq` reads `v_i` off as

```
v_i = fract (θ · (x(w_i) + y(w_i)) − θ · (η / (a(aN+1)N)))
```

with `θ = sweepTheta a b N` and `w_i` the `i`-th crossed east step in column order. Two things
follow, and both bear directly on `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`.

* `v` reads the colouring **only** through the integers `n_i := x(w_i) + y(w_i)`, the antidiagonal
  indices of the crossed **east** steps. The crossed north steps do not enter `v` at all — they
  enter only `α`, through `HJO.Mellit.card_componentCrossingIndices_eq`.
* `v` reads the level **only** through the single number `θ · levelIntercept a N η`, *the same for
  every `i`*. So changing the level moves every entry of `v` by one common amount:
  `HJO.Mellit.braidDataOfColouring_fst_eq_fract_add_of_colouringEast_eq`. On the circle `ℝ/ℤ` in
  which `HJO.Braid.IsSpecialBraidData` reads the positions, a level drop is a **rigid rotation** of
  the point configuration.

## What that makes of the four clauses

The two descent identities of `HJO.Mellit.Isolates.notMem_colouringNorth_lo` then split the four
event types by
*which half of the colouring moves*, and the position tuple follows:

| event | north half | east half | `k` | `α` | `v` |
|---|---|---|---|---|---|
| A | gains `(X, Y−1)` | gains `(X, Y)` | `+1` | new entry `1` | rotation + one new entry |
| C | `(X,Y) ↦ (X,Y−1)` | **unchanged** | `=` | one entry `+1` | **rotation only** |
| D | **unchanged** | `(X−1,Y) ↦ (X,Y)` | `=` | one entry `+1` | rotation, and one entry `+θ` |
| E | **unchanged** | **unchanged** | `=` | **unchanged** | **rotation only** |

`HJO.Mellit.Isolates.braidData_fst_of_eventType_C`,
`HJO.Mellit.Isolates.braidData_fst_of_eventType_E`,
`HJO.Mellit.Isolates.braidData_snd_of_eventType_E` and
`HJO.Mellit.crossingAbscissa_succ_eq_add` are those rows in Lean. So:

* **Type E** isolates the rotation and nothing else. The rank and every multiplicity are literally
  equal at the two levels (`HJO.Mellit.Isolates.braidData_snd_of_eventType_E`); only `v` rotates.
  Type `E` is not a clause on its own — `HJO.Mellit.dsc_eq_dminus_add_smul` pairs it with `B` as a
  sum over two paths — but its contribution `u R_+^{\widehat Q}` to that sum is related to `R_-` by
  the rotation alone, so *how a rigid rotation acts on `HJO.Braid.specialBraid`* is precisely what
  that term needs, and it is a lemma in its own right.
* **Type C** needs the same rotation lemma *plus* one extra move on the component whose
  multiplicity rose — a move added at the **bottom** of the component, the top crossing `n_i` and
  hence `v_i` being untouched by anything but the rotation.
* **Type D** needs the same rotation lemma *plus* one extra move on a component whose top crossing
  rose by one, so whose position advanced by exactly one step of `θ` on top of the rotation:
  `HJO.Mellit.crossingAbscissa_succ_eq_add`.

**None of this is the shape of `HJO.Braid.specialBraid_mul_trainDown_one`.** That lemma relates
`B_{s,w,β}` to `B_{s,v,α}` at a *common* `θ` with `w` obtained from `v` by **inserting** one entry
and `β` from `α` by inserting the multiplicity `1` — the type-`A` row, where the rank rises. At
types C, D and E the rank is unchanged, no entry is inserted or deleted, and the tuple is not a
subtuple of the other: *every* entry moves, by the rotation. So the missing analogues are not
`HJO.Braid.specialBraid_mul_trainDown_one` at another index. The rotation lemma is a separate
obligation and it is common to all three of C, D and E, which is why those three are hard for the
same reason — not, as the count of letters alone suggests, because C and D each add a move.

## The degenerate parameters of the operator side

`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` passes from a braid identity to an operator
one through `π_k` of `HJO.Sweep.braidRep`, and three of the definitions on that side carry an
inverse, which in a field is `0` at the bad parameter rather than undefined. The section "The
degenerate parameters" below evaluates each:

* `HJO.Sweep.corner_of_eq_one` — `Δ = 0` at `q = 1`, so the type-`C` clause reads `R_- = 0` there;
* `HJO.Sweep.zopOneStar_of_eq_one` — `z_1 = 0` at `q = 1` as well, independently;
* `HJO.Sweep.braidRepLetterTotal_z1_of_mul_eq_zero` — `π_k(z_1) = 0` whenever `qu = 0`, so in
  particular at `u = 0`;
* `HJO.Sweep.braidRepLetterTotal_T_of_eq_zero` — `π_k(T_i) = 0` at `q^{1/2} = 0`.

So `q ≠ 0`, `q ≠ 1` and **`u ≠ 0`** are all real hypotheses of any clause whose braid carries a `z`
letter, and `u ≠ 0` has to be carried explicitly. `z`-letters
are not avoidable: `HJO.Braid.braidStep` contributes a `z` at every move of a point below the
puncture.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5, for
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`,
`HJO.Mellit.Isolates.notMem_colouringNorth_lo` and `HJO.Mellit.card_componentCrossingIndices_eq`,
using `HJO.Mellit.braidDataOfColouring`, `HJO.Braid.specialBraid`, `HJO.Braid.braidStep`,
`HJO.Sweep.braidRep`, `HJO.Sweep.corner` and `HJO.Sweep.zop`.
-/

@[expose] public section

namespace HJO.Mellit

open Finset ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The crossing abscissae are an arithmetic progression of step `θ` -/

/-- **A crossing abscissa is `θ` times the distance from the level intercept.** Unfolding
`HJO.Mellit.braidDataOfColouring`'s ambient line: the `n`-th crossing sits at `θ(n − η/(a(aN+1)N))`,
so the abscissae of a level form an arithmetic progression of step `θ` whose offset is the only
thing the level contributes.

No hypothesis on the slope: both sides divide by `1 + s`, so on a degenerate rectangle both are
`0`. -/
theorem crossingAbscissa_eq_sweepTheta_mul (a b N : ℕ) (η : ℚ) (n : ℤ) :
    crossingAbscissa a b N η n = sweepTheta a b N * ((n : ℚ) - levelIntercept a N η) := by
  rw [crossingAbscissa, sweepTheta, div_mul_eq_mul_div, one_mul]

/-- **Two levels give the same crossing abscissa up to one common shift**, independent of `n`: the
shift is `θ` times the difference of the two level intercepts. -/
theorem crossingAbscissa_eq_add (a b N : ℕ) (ηlo ηhi : ℚ) (n : ℤ) :
    crossingAbscissa a b N ηlo n
      = crossingAbscissa a b N ηhi n
        + sweepTheta a b N * (levelIntercept a N ηhi - levelIntercept a N ηlo) := by
  rw [crossingAbscissa_eq_sweepTheta_mul, crossingAbscissa_eq_sweepTheta_mul]
  ring

/-- `fract` absorbs an inner `fract`: `fract (fract x + d) = fract (x + d)`. -/
theorem fract_fract_add (x d : ℚ) : Int.fract (Int.fract x + d) = Int.fract (x + d) := by
  have h : Int.fract x + d = (x + d) + ((-⌊x⌋ : ℤ) : ℚ) := by
    rw [Int.fract]; push_cast; ring
  rw [h]
  exact Int.fract_add_intCast (x + d) (-⌊x⌋)

/-! ### The crossing lattice, with `θ` eliminated

Writing `M := (aN+1)N` and `D := (a+b)M − 1`, the two definitions `HJO.Mellit.sweepSlope` and
`HJO.Mellit.levelIntercept` cancel down to `θ = aM/D` and `crossingAbscissa η n = (aMn − η)/D`.
That kills every fraction on the geometric side and makes the *size* of the rotation visible, which
is what decides whether the type-`C`, `D` and `E` clauses of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` can treat it as a no-op. They cannot; see
`HJO.Mellit.exists_pos_crossingAbscissa_sub`. -/

/-- The common denominator: `D = (a+b)(aN+1)N − 1`. -/
def crossingDen (a b N : ℕ) : ℚ := ((a + b) * (a * N + 1) * N : ℕ) - 1

/-- `D > 0` on a rectangle with a column. -/
theorem crossingDen_pos (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) : 0 < crossingDen a b N := by
  have h : 2 ≤ (a + b) * (a * N + 1) * N := by
    have h1 : 2 ≤ a + b := by omega
    have h2 : 1 ≤ (a * N + 1) * N := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc 2 = 2 * 1 := by ring
      _ ≤ (a + b) * ((a * N + 1) * N) := Nat.mul_le_mul h1 h2
      _ = (a + b) * (a * N + 1) * N := by ring
  have : (2 : ℚ) ≤ ((a + b) * (a * N + 1) * N : ℕ) := by exact_mod_cast h
  rw [crossingDen]; linarith

/-- **`θ = a(aN+1)N / D`.** -/
@[hjo "lem_braid_position_descent"]
theorem sweepTheta_eq_div (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    sweepTheta a b N = ((a * (a * N + 1) * N : ℕ) : ℚ) / crossingDen a b N := by
  have hD := (crossingDen_pos ha hb hN).ne'
  have haM : ((a * (a * N + 1) * N : ℕ) : ℚ) ≠ 0 := by positivity
  rw [sweepTheta, sweepSlope, crossingDen] at *
  push_cast at hD haM ⊢
  field_simp
  ring

/-- **A crossing abscissa with every fraction cleared**: the `n`-th crossing of the level `η` sits
at `(a(aN+1)N · n − η)/D`. The level enters only as the additive constant `−η`, and the index only
as the integer multiple of `a(aN+1)N`. -/
@[hjo "lem_braid_position_descent"]
theorem crossingAbscissa_eq_div (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) (n : ℤ) :
    crossingAbscissa a b N η n
      = (((a * (a * N + 1) * N : ℕ) : ℚ) * (n : ℚ) - η) / crossingDen a b N := by
  have hD := (crossingDen_pos ha hb hN).ne'
  have haN : ((a : ℚ) * (a * N + 1) * N) ≠ 0 := by positivity
  rw [crossingAbscissa_eq_sweepTheta_mul, sweepTheta_eq_div ha hb hN, levelIntercept, crossingDen]
    at *
  push_cast at hD haN ⊢
  field_simp

/-- **The rotation is `(η₊ − η₋)/D`, the same for every crossing index.** This is the exact size of
the shift that `HJO.Mellit.braidDataOfColouring_fst_eq_fract_add_of_colouringEast_eq` applies to
every entry of the position tuple. -/
@[hjo "lem_braid_position_descent"]
theorem crossingAbscissa_sub_crossingAbscissa (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (ηlo ηhi : ℚ) (n : ℤ) :
    crossingAbscissa a b N ηlo n - crossingAbscissa a b N ηhi n
      = (ηhi - ηlo) / crossingDen a b N := by
  have hD := (crossingDen_pos ha hb hN).ne'
  rw [crossingAbscissa_eq_div ha hb hN, crossingAbscissa_eq_div ha hb hN]
  field_simp
  ring

/-- **Every crossing abscissa is an odd multiple of `1/(2D)`.** With `η = m + 1/2` an admissible
level of `HJO.Mellit.IsAdmissibleColouring`, the numerator `a(aN+1)N·n − η` is a half-integer, so
the crossings of one level lie on the *odd* sublattice of `(1/(2D))ℤ`, whose consecutive points are
`1/D` apart. Neither `0` nor the puncture `θ = a(aN+1)N/D` lies on it, which is the quantitative
form of `HJO.Mellit.fract_crossingAbscissa_ne_sweepTheta` and of the `(0,1)` clause of
`HJO.Mellit.isSpecialBraidData_braidDataOfColouring`. -/
@[hjo "lem_braid_position_descent"]
theorem exists_crossingAbscissa_eq_odd (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (n : ℤ) :
    ∃ m : ℤ, crossingAbscissa a b N η n
      = (2 * (m : ℚ) + 1) / (2 * crossingDen a b N) := by
  obtain ⟨j, hj⟩ := hη
  have hD := (crossingDen_pos ha hb hN).ne'
  refine ⟨(a * (a * N + 1) * N : ℕ) * n - j - 1, ?_⟩
  rw [crossingAbscissa_eq_div ha hb hN, hj]
  push_cast
  field_simp
  ring

/-- **Two admissible levels differ by a positive integer**, so the rotation of
`HJO.Mellit.crossingAbscissa_sub_crossingAbscissa` is `m/D` with `m ≥ 1` — never infinitesimal, and
never smaller than the `1/D` spacing of the odd lattice the crossings lie on
(`HJO.Mellit.exists_crossingAbscissa_eq_odd`). `HJO.Mellit.IsAdmissibleColouring` makes every
admissible level a half-integer, which is where the integrality comes from.

**What this settles, and what it does not.** It settles that the rotation is a whole step of the
position lattice, so the type-`C`, `D` and `E` clauses of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` cannot dispose of it by a continuity or
smallness argument: on the circle `ℝ/ℤ` that `HJO.Braid.IsSpecialBraidData` reads, a whole-step
shift can carry a point past `0` — changing `HJO.Braid.entryRank` and hence the train `T_{a'↘a}` of
`HJO.Braid.braidStep` — and past the puncture `θ`, which flips its branch between its `z`
letter and its `ỹ` letter. Whether it does so in a given instance depends on the configuration, and
nothing here decides that.

It does not settle whether the rotation is invisible to `HJO.Braid.specialBraid`. But it makes the
alternative precise, which is the useful part. Suppose it were invisible. At type `E` both halves of
the colouring stand still (`HJO.Mellit.Isolates.braidData_of_eventType_E`), and
`HJO.Mellit.dsc_eq_dminus_add_smul` supplies `c_{η_-}(P̂) = c_{η_-}(Q̂)`, so — the data reading only
the colouring and the level, by `HJO.Mellit.braidDataOfColouring_fst_eq` — the braid data behind
`R_+^{Q̂}` is the data behind `R_-` rotated, and `R_+^{Q̂} = R_-`. The `BE` clause would then
collapse to the single-path identity `(1 − u) R_- = d_- R_+^{P̂}`. The left-hand side does **not**
collapse the same way: `HJO.Mellit.dsc` reads the level as well as the colouring, so `D_{η_-,c}` and
`D_{η_+,c}` are different terms at the same `c`. So under
`HJO.Mellit.braidValueColouring_eq_dsc_floor` an invisible rotation would force
`D_{η_-,c} = D_{η_+,c}` at every type-`E` colouring, and would introduce a `u ≠ 1` into a rule that
carries no such hypothesis. That is a consequence worth testing and not a disproof of anything. -/
@[hjo "lem_braid_position_descent"]
theorem exists_pos_crossingAbscissa_sub (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {ηlo ηhi : ℚ}
    (hlo : IsAdmissibleLevel ηlo) (hhi : IsAdmissibleLevel ηhi) (hlt : ηlo < ηhi) (n : ℤ) :
    ∃ m : ℕ, 0 < m ∧
      crossingAbscissa a b N ηlo n - crossingAbscissa a b N ηhi n
        = (m : ℚ) / crossingDen a b N := by
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  have hij : i < j := by
    by_contra hcon
    have : (j : ℚ) ≤ (i : ℚ) := by exact_mod_cast Int.not_lt.1 hcon
    rw [hi, hj] at hlt; linarith
  refine ⟨(j - i).toNat, by omega, ?_⟩
  have hcast : (((j - i).toNat : ℕ) : ℚ) = (j : ℚ) - (i : ℚ) := by
    rw [show (((j - i).toNat : ℕ) : ℚ) = ((((j - i).toNat : ℕ) : ℤ) : ℚ) by push_cast; ring,
      Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ j - i)]
    push_cast
    ring
  rw [crossingAbscissa_sub_crossingAbscissa ha hb hN, hi, hj, hcast]
  ring_nf

/-! ### The position tuple in closed form -/

/-- **The position tuple of `HJO.Mellit.braidDataOfColouring` in closed form**: `v_i` is the
fractional part of `θ` times the antidiagonal index of the `i`-th crossed east step, less `θ` times
the level intercept.

Two readings, both used below. First, `v` sees the colouring only through the integers
`x(w_i) + y(w_i)` of its **east** half; the north half enters only the multiplicities, through
`HJO.Mellit.card_componentCrossingIndices_eq`. Second, `v` sees the level only through
`θ · levelIntercept a N η`, which does not depend on `i`. -/
@[hjo "lem_braid_position_descent"]
theorem braidDataOfColouring_fst_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) {y : Heights a b N} {k : ℕ} (i : Fin k)
    (hi : (i : ℕ) < #(colouringEast y η)) :
    (braidDataOfColouring a b N y η k).1 i =
      Int.fract (sweepTheta a b N *
        ((((colStep (colouringEast y η) (i : ℕ)).1 + (colStep (colouringEast y η) (i : ℕ)).2 : ℕ)
            : ℚ) - levelIntercept a N η)) := by
  rw [braidDataOfColouring_fst, componentTopIndex_eq ha hb hN hη hηpos hi,
    crossingAbscissa_eq_sweepTheta_mul]
  push_cast
  ring_nf

/-- **A level drop rotates the whole position tuple by one common amount**, whenever the crossed
east steps are the same at the two levels — which by `HJO.Mellit.Isolates.notMem_colouringNorth_lo`
is exactly what happens at an event of type `C` or `E`.

The shift `θ(c(η_+) − c(η_-))` does not depend on `i`. This is the statement that a level drop acts
on the configuration `HJO.Braid.IsSpecialBraidData` reads as a **rigid rotation** of the circle
`ℝ/ℤ`, and it is the obligation common to the type-`C`, type-`D` and type-`E` clauses of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`. -/
@[hjo "lem_braid_position_descent"]
theorem braidDataOfColouring_fst_eq_fract_add_of_colouringEast_eq (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) {ηlo ηhi : ℚ} (hlo : IsAdmissibleLevel ηlo) (hhi : IsAdmissibleLevel ηhi)
    (hlopos : 0 < ηlo) (hhipos : 0 < ηhi) {y : Heights a b N} {k : ℕ} (i : Fin k)
    (hE : colouringEast y ηlo = colouringEast y ηhi) (hi : (i : ℕ) < #(colouringEast y ηhi)) :
    (braidDataOfColouring a b N y ηlo k).1 i =
      Int.fract ((braidDataOfColouring a b N y ηhi k).1 i
        + sweepTheta a b N * (levelIntercept a N ηhi - levelIntercept a N ηlo)) := by
  have hilo : (i : ℕ) < #(colouringEast y ηlo) := by rw [hE]; exact hi
  rw [braidDataOfColouring_fst_eq ha hb hN hlo hlopos i hilo,
    braidDataOfColouring_fst_eq ha hb hN hhi hhipos i hi, hE, fract_fract_add]
  ring_nf

/-! ### The three rows: what the drop does to the data at types C, D and E -/

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-- **At an event of type `C` the position tuple only rotates.** The crossed east steps are
unchanged there — `HJO.Mellit.Isolates.colouringEast_eq_of_eventType_C` — so every entry of `v`
moves by the one common shift and nothing else happens to it. What changes is a single
multiplicity, by `HJO.Mellit.Isolates.totalCrossings_of_eventType_C` together with
`HJO.Mellit.Isolates.card_colouringNorth_of_eventType_C`. -/
theorem braidData_fst_of_eventType_C (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hlopos : 0 < ηlo) (hhipos : 0 < ηhi)
    {y : Heights a b N} {k : ℕ} (i : Fin k)
    (hev : eventType y (X, Y) = EventType.C) (hi : (i : ℕ) < #(colouringEast y ηhi)) :
    (braidDataOfColouring a b N y ηlo k).1 i =
      Int.fract ((braidDataOfColouring a b N y ηhi k).1 i
        + sweepTheta a b N * (levelIntercept a N ηhi - levelIntercept a N ηlo)) :=
  braidDataOfColouring_fst_eq_fract_add_of_colouringEast_eq ha hb hN hI.lo hI.hi hlopos hhipos i
    (hI.colouringEast_eq_of_eventType_C ha hN hev) hi

/-- **At an event of type `E` the position tuple only rotates**, and for the stronger reason that
*both* halves of the colouring stand still. -/
theorem braidData_fst_of_eventType_E (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hlopos : 0 < ηlo) (hhipos : 0 < ηhi)
    {y : Heights a b N} (hy : IsAboveDiagonal y) {k : ℕ} (i : Fin k)
    (hev : eventType y (X, Y) = EventType.E) (hi : (i : ℕ) < #(colouringEast y ηhi)) :
    (braidDataOfColouring a b N y ηlo k).1 i =
      Int.fract ((braidDataOfColouring a b N y ηhi k).1 i
        + sweepTheta a b N * (levelIntercept a N ηhi - levelIntercept a N ηlo)) :=
  braidDataOfColouring_fst_eq_fract_add_of_colouringEast_eq ha hb hN hI.lo hI.hi hlopos hhipos i
    (hI.colouringEast_eq_of_eventType_E ha hN hy hev) hi

/-- **At an event of type `E` the multiplicities are literally unchanged**, entry by entry — not
merely their sum, which is `HJO.Mellit.Isolates.totalCrossings_of_eventType_E`. Both halves of the
colouring stand still, so `HJO.Mellit.card_componentCrossingIndices_eq` gives the same closed form
at the two levels. -/
theorem braidData_snd_of_eventType_E (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y) {k : ℕ} (i : Fin k)
    (hev : eventType y (X, Y) = EventType.E) (hi : (i : ℕ) < #(colouringNorth y ηhi)) :
    (braidDataOfColouring a b N y ηlo k).2 i = (braidDataOfColouring a b N y ηhi k).2 i := by
  have hhi : ((a * N : ℕ) : ℚ) < ηhi := hlo.trans (hI.ltP.trans hI.Plt)
  have hN' := hI.colouringNorth_eq_of_eventType_E ha hN hev
  have hE' := hI.colouringEast_eq_of_eventType_E ha hN hy hev
  have hilo : (i : ℕ) < #(colouringNorth y ηlo) := by rw [hN']; exact hi
  have h1 := card_componentCrossingIndices_eq ha hb hN hI.lo hlo hy hilo
  have h2 := card_componentCrossingIndices_eq ha hb hN hI.hi hhi hy hi
  rw [braidDataOfColouring_snd, braidDataOfColouring_snd]
  rw [hN', hE'] at h1
  omega

/-- **At an event of type `E` the whole special-braid data stands still except for the rotation.**
The rank and the multiplicities are equal and the positions differ by one common shift, so the
type-`E` clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` is exactly the assertion
that a rigid rotation of the position tuple leaves `HJO.Braid.specialBraid` alone. Rule `E` of
`HJO.Mellit.dsc_eq_dminus_add_smul` multiplies the left-hand side by `u`, which is why type `E` is
not a clause on its own; but the
*braid-side* content of the pair is this rotation invariance and nothing more. -/
theorem braidData_of_eventType_E (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.E) :
    #(colouringNorth y ηlo) = #(colouringNorth y ηhi) ∧
      (∀ i : Fin #(colouringNorth y ηhi),
        (braidDataOfColouring a b N y ηhi #(colouringNorth y ηhi)).2 i
          = (braidDataOfColouring a b N y ηlo #(colouringNorth y ηhi)).2 i) := by
  have hhi : ((a * N : ℕ) : ℚ) < ηhi := hlo.trans (hI.ltP.trans hI.Plt)
  refine ⟨by rw [hI.colouringNorth_eq_of_eventType_E ha hN hev], fun i => ?_⟩
  exact (braidData_snd_of_eventType_E ha hb hN hI hlo hy i hev i.isLt).symm

end Isolates

/-- **The type-`D` entry advances by exactly one `θ` step beyond the rotation.** At an event of type
`D` the north half of the colouring stands still and one crossed east step moves from `(X − 1, Y)`
to `(X, Y)` — `HJO.Mellit.Isolates.colouringNorth_eq_of_eventType_D` and
`HJO.Mellit.Isolates.colouringEast_eq_of_eventType_D` — so by
`HJO.Mellit.componentTopIndex_eq` that component's top antidiagonal index rises by one while every
other stays put. Its abscissa therefore moves by `θ` *on top of* the common rotation, which is what
this identity records.

So the type-`C` and type-`D` rows differ in exactly one way, and it is not the number of letters —
both add one move. At `C` the extra crossing appears at the *bottom* of the component and the
position is untouched but for the rotation
(`HJO.Mellit.Isolates.braidData_fst_of_eventType_C`); at `D` it appears at the *top* and the
position advances a step. That is the asymmetry the left side records as `q^{-a}Δ` against the bare
`q^{a}`. -/
theorem crossingAbscissa_succ_eq_add (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (ηlo ηhi : ℚ) (n : ℤ) :
    crossingAbscissa a b N ηlo (n + 1)
      = crossingAbscissa a b N ηhi n + sweepTheta a b N
        + (ηhi - ηlo) / crossingDen a b N := by
  have hs := one_add_sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  have hrot := crossingAbscissa_sub_crossingAbscissa ha hb hN ηlo ηhi n
  rw [crossingAbscissa_succ hs.ne', sweepTheta]
  linarith

end HJO.Mellit

/-! ### The degenerate parameters of the operator side

`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` ends by applying `π_k` of
`HJO.Sweep.braidRep`, and `HJO.Sweep.braidRep`, `HJO.Sweep.corner` and `HJO.Sweep.zop` each carry an
inverse. In a field `0⁻¹ = 0`, so at a bad parameter the letter is not undefined — it is the **zero
map**, and a clause of the recursion reads `0 = something`. Each of the four lemmas below sets one
parameter to its bad value and reads off the zero. -/

namespace HJO.Sweep

open Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`Δ = 0` at `q = 1`.** `HJO.Sweep.corner` divides by `q − 1`, and `(1 − 1)⁻¹ = 0` in a field.
So the type-`C` clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, whose factor is
`q^{-a}Δ`, asserts `R_- = 0` at `q = 1`: `q ≠ 1` is a real hypothesis of that clause and not a
normalisation. -/
theorem corner_of_eq_one (k : ℕ) : corner (1 : L) k = 0 := by
  rw [corner]
  simp

/-- **`z_1 = 0` at `q = 1`**, independently of `Δ`: `HJO.Sweep.zop` carries the factor
`q^k/(1 − q)`. Since `HJO.Braid.braidStep` contributes a `z` letter at every move of a point below
the puncture, this kills the braid side of any clause with a move, again at `q = 1`. -/
theorem zopOneStar_of_eq_one (u : L) (k : ℕ) : zopOneStar (1 : L) u k = 0 := by
  rw [zopOneStar]
  simp

/-- **`π_k(z_1) = 0` whenever `qu = 0`**, in particular at `u = 0`: `HJO.Sweep.braidRep` sends `z_1`
to `(qu)^{-1}z_1`. So `u ≠ 0` is a real hypothesis of every clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` whose braid carries a `z` letter, and it has
to be carried explicitly. -/
theorem braidRepLetterTotal_z1_of_mul_eq_zero (q u r : L) {k : ℕ} (hk : 1 ≤ k)
    (h : q * u = 0) : braidRepLetterTotal q u r k Letter.z1 = 0 := by
  rw [braidRepLetterTotal_z1 q u r hk, h, inv_zero, zero_smul]

/-- **`π_k(T_i) = 0` at `q^{1/2} = 0`**: `HJO.Sweep.braidRep` sends `T_i` to `q^{-1/2}T_i`. With
`r * r = q` this is the case `q = 0`, so `q ≠ 0` is real too, and for the `T` letters alone — before
any `z` is reached. -/
theorem braidRepLetterTotal_T_of_eq_zero (q u : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    braidRepLetterTotal q u (0 : L) k (Letter.T i) = 0 := by
  rw [braidRepLetterTotal_T q u (0 : L) hi hik, inv_zero, zero_smul]

end HJO.Sweep

end
