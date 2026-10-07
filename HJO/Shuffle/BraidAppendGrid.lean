/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidAppendOffset
public meta import HJO.Attr

/-! # The grid the colouring's positions live on, and the isotopy clause

`HJO.Braid.gap_of_grid` discharges the isotopy clause of
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` from a grid: if every position of the
special-braid data and **every one of its `nx_θ`-iterates** is a multiple of `1/n`, and the offset
`δ` of the appended entry is at most `1/n`, then no iterate of another component can separate the
appended entry from `1 - θ`.

`HJO.Mellit.appendOffset_sepLevel` supplied the arithmetic half at `n = 2D`: the offset is exactly
`1/(2D)` at `HJO.Mellit.sepLevel`. What was missing was the grid clause itself, and specifically the
clause **for the iterates**. This file supplies it, and the reason it is cheap is that `nx_θ` cannot
leave a grid the shift `θ` itself lies on: `HJO.Braid.nextCrossing` sends `x` to `x - θ` or to
`x + 1 - θ`, and if `x·n`, `θ·n` and `n` are all integers then so is the result's.

## Main results

* `HJO.Braid.exists_int_iterate_nextCrossing_mul` — **the grid is `nx_θ`-invariant.** For `n : ℕ`,
  if `θ·n` and `x·n` are integers then so is `(nx_θ^i x)·n`, for every `i`. This is the clause the
  previous pass left open, and it needs nothing about the data: no admissibility, no ordering, no
  bound on `i`.
* `HJO.Mellit.exists_int_braidDataOfColouring_fst_mul_gridDen` — every position of a composition
  colouring is a multiple of `1/(2D)`. Immediate from the closed form
  `HJO.Mellit.braidDataOfColouring_fst_hasAboveReturns` together with `IsAdmissibleLevel`, which
  says every admissible level is a half-integer; the `2` in `2D` is exactly that half.
* `HJO.Mellit.sweepTheta_mul_gridDen` — `θ·2D = 2a(aN+1)N`, from
  `HJO.Mellit.sweepTheta_mul_rankSpan`. So `θ` lies on the grid too, which is what lets the previous
  item propagate along the iterates.
* `HJO.Mellit.braidDataOfColouring_gap` — **`hgap`, discharged.** The isotopy clause of
  `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` at the composition colouring, at the offset
  `HJO.Mellit.appendOffset`, in the `Fin.castSucc`/`Fin.last` shape
  `HJO.Mellit.sweepIn_braidRep_specialBraid_rotateLast_appendOffset` asks for.
* `HJO.Mellit.eq_sepLevel_of_le` — the level is *pinned*: an admissible `η > aN` with
  `η ≤ aN + 1/2` is `HJO.Mellit.sepLevel` on the nose. So the boundary case of
  `HJO.Braid.gap_of_grid` is not merely the live one, it is the only one.

## The two `hgap`s

The gap clause refuted in `HJO/Shuffle/BraidTypeAGapRefuted.lean` is the **type-A** clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, whose route was a rank squeeze on a *type-A*
event: there the inserted point is the point of **least** rank, and another component's iterate is
free to sit above it. The clause proved here is the `(‡)` of
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` at the **appended** entry, which is the point
of **greatest** rank (`HJO.Mellit.braidDataOfColouring_fst_castSucc_lt_last`). The two are different
statements about different events, and the refutation says nothing about this one. What is proved
below is the second.

## Nothing generic is spent

As in `HJO/Shuffle/BraidAppendOffset.lean`: no `q`, no `u`, no field, no representation. The
hypotheses are `0 < a`, `0 < b`, `0 < N`, `Nat.Coprime a b`, admissibility and separation of `η`
with `η > aN`, and `HJO.Mellit.HasAboveReturns`. `a ≤ b` is used nowhere.
-/

@[expose] public section

namespace HJO.Braid

/-! ### `nx_θ` cannot leave a grid that carries `θ` -/

/-- **A `1/n`-grid carrying `θ` is `nx_θ`-invariant.** `HJO.Braid.nextCrossing` is `x ↦ x - θ` above
`θ` and `x ↦ x + 1 - θ` below it; scaling by `n` turns both into `x·n` plus an integer combination
of `θ·n` and `n`. So the grid clause of `HJO.Braid.gap_of_grid` — which is asked at every iterate,
not just at the positions — follows from the positions alone, by induction on the number of steps.

Note what is *not* needed: nothing about `HJO.Braid.IsSpecialBraidData`, nothing about where `x`
sits relative to `θ`, and no bound on `i`. The case split of `HJO.Braid.nextCrossing` is discharged
uniformly. -/
theorem exists_int_iterate_nextCrossing_mul {θ : ℚ} {n : ℕ} {mθ : ℤ}
    (hθ : θ * (n : ℚ) = (mθ : ℚ)) {x : ℚ} {m : ℤ} (hx : x * (n : ℚ) = (m : ℚ)) (i : ℕ) :
    ∃ m' : ℤ, (nextCrossing θ)^[i] x * (n : ℚ) = (m' : ℚ) := by
  induction i with
  | zero => exact ⟨m, by simpa using hx⟩
  | succ i ih =>
    obtain ⟨m', h⟩ := ih
    rw [Function.iterate_succ_apply']
    simp only [nextCrossing]
    split_ifs with h1
    · exact ⟨m' - mθ, by push_cast; linear_combination h - hθ⟩
    · exact ⟨m' + (n : ℤ) - mθ, by push_cast; linear_combination h - hθ⟩

end HJO.Braid

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {a b N : ℕ}

/-! ### The grid denominator `2D`, as a natural number -/

/-- The rank span `D = a(aN+1)N + b(aN+1)N - 1` as a natural number. The truncated subtraction is
honest: `a(aN+1)N ≥ 2` already for `a, N ≥ 1`. -/
def rankSpanNat (a b N : ℕ) : ℕ := a * (a * N + 1) * N + b * (a * N + 1) * N - 1

/-- **The grid denominator**: `2D`. The `2` is the half-integrality of the level — every
`HJO.Mellit.IsAdmissibleLevel` is `n + 1/2` — and it is also exactly the factor that makes
`HJO.Mellit.appendOffset` equal to one grid step at `HJO.Mellit.sepLevel`. -/
def gridDen (a b N : ℕ) : ℕ := 2 * rankSpanNat a b N

theorem two_le_rankDen_nat (ha : 0 < a) (hN : 0 < N) : 2 ≤ a * (a * N + 1) * N := by
  have h1 : 1 ≤ a * N := Nat.one_le_iff_ne_zero.2 (by positivity)
  have := Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ a from ha) (show 2 ≤ a * N + 1 by omega))
    (show 1 ≤ N from hN)
  simpa using this

theorem cast_rankSpanNat (ha : 0 < a) (hN : 0 < N) :
    ((rankSpanNat a b N : ℕ) : ℚ)
      = (a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 := by
  have h := two_le_rankDen_nat (a := a) (N := N) ha hN
  rw [rankSpanNat, Nat.cast_sub (by omega)]
  push_cast
  ring

theorem cast_gridDen (ha : 0 < a) (hN : 0 < N) :
    ((gridDen a b N : ℕ) : ℚ)
      = 2 * ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
  rw [gridDen, Nat.cast_mul, cast_rankSpanNat (b := b) ha hN]
  norm_num

theorem gridDen_pos (ha : 0 < a) (hN : 0 < N) : 0 < gridDen a b N := by
  have h := two_le_rankDen_nat (a := a) (N := N) ha hN
  rw [gridDen, rankSpanNat]
  omega

/-! ### `θ` lies on the grid -/

/-- **`θ·2D = 2a(aN+1)N`**, an integer: the shift `HJO.Braid.nextCrossing` subtracts is itself on
the `1/(2D)`-grid, which is what carries the grid along the iterates through
`HJO.Braid.exists_int_iterate_nextCrossing_mul`. Restated from
`HJO.Mellit.sweepTheta_mul_rankSpan`. -/
theorem sweepTheta_mul_gridDen (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    sweepTheta a b N * ((gridDen a b N : ℕ) : ℚ) = ((2 * (a * (a * N + 1) * N) : ℕ) : ℚ) := by
  rw [cast_gridDen (b := b) ha hN,
    show sweepTheta a b N *
        (2 * ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1))
      = 2 * (sweepTheta a b N *
          ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)) from by ring,
    sweepTheta_mul_rankSpan ha hb hN]
  push_cast
  ring

/-! ### Every position of a composition colouring lies on the grid -/

/-- **THE GRID CLAUSE AT THE POSITIONS.** Every position of the special-braid data of a composition
colouring is a multiple of `1/(2D)`. The closed form
`HJO.Mellit.braidDataOfColouring_fst_hasAboveReturns` writes the position as
`(b(aN+1)N + aA_{i+1} - 1 - η)/D` with everything but `η` an integer, and `η = n + 1/2` by
`HJO.Mellit.IsAdmissibleLevel`; multiplying by `2D` clears both denominators at once and leaves
`2(b(aN+1)N + aA_{i+1} - 1 - n) - 1`, an **odd** integer. -/
theorem exists_int_braidDataOfColouring_fst_mul_gridDen (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) {k : ℕ} (i : Fin k)
    (hi : (i : ℕ) < α.length) :
    ∃ m : ℤ, (braidDataOfColouring a b N y η k).1 i * ((gridDen a b N : ℕ) : ℚ) = (m : ℚ) := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  obtain ⟨nη, hnη⟩ := hηa
  refine ⟨2 * ((b : ℤ) * ((a : ℤ) * N + 1) * N + (a : ℤ) * ((α.take ((i : ℕ) + 1)).sum : ℕ) - 1
    - nη) - 1, ?_⟩
  rw [braidDataOfColouring_fst_hasAboveReturns ha hb hN hab ⟨nη, hnη⟩ hηs hηN hret i hi,
    cast_gridDen (b := b) ha hN, div_mul_eq_mul_div, div_eq_iff hD.ne', hnη]
  generalize (α.take ((i : ℕ) + 1)).sum = A
  push_cast
  ring

/-! ### The offset is one grid step, and the level is pinned -/

/-- `δ·2D = 2(η - aN)`, the shape both halves of the grid criterion read: `≤ 1` is
`η ≤ aN + 1/2`. -/
theorem appendOffset_mul_gridDen (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) :
    appendOffset a b N η * ((gridDen a b N : ℕ) : ℚ) = 2 * (η - (a : ℚ) * N) := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  rw [appendOffset, cast_gridDen (b := b) ha hN, div_mul_eq_mul_div, div_eq_iff hD.ne']
  ring

/-- **The level is pinned to `HJO.Mellit.sepLevel`.** An admissible level is a half-integer, so
`η > aN` already forces `η ≥ aN + 1/2`; asking in addition that the offset be at most one grid step
— `η ≤ aN + 1/2` — leaves exactly `η = HJO.Mellit.sepLevel a N`. So the boundary case of
`HJO.Braid.gap_of_grid` is the only case, and the grid criterion is available at one level and not a
range of them. -/
theorem eq_sepLevel_of_le {η : ℚ} (hηa : IsAdmissibleLevel η) (hηN : ((a * N : ℕ) : ℚ) < η)
    (hηle : η ≤ sepLevel a N) : η = sepLevel a N := by
  obtain ⟨n, rfl⟩ := hηa
  rw [sepLevel] at hηle ⊢
  push_cast at hηN
  have h1 : ((a * N : ℕ) : ℤ) ≤ n := by
    have : ((a * N : ℕ) : ℚ) < ((n : ℤ) : ℚ) + 1 := by push_cast at hηN ⊢; linarith
    have : ((a * N : ℕ) : ℤ) < n + 1 := by exact_mod_cast this
    omega
  have h2 : (n : ℤ) ≤ ((a * N : ℕ) : ℤ) := by
    have : ((n : ℤ) : ℚ) ≤ ((a * N : ℕ) : ℚ) := by push_cast at hηle ⊢; linarith
    exact_mod_cast this
  have : n = ((a * N : ℕ) : ℤ) := le_antisymm h2 h1
  rw [this]
  push_cast
  ring

/-! ### `hgap`, discharged -/

/-- **`hgap`: THE ISOTOPY CLAUSE OF `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`, DISCHARGED
AT THE COMPOSITION COLOURING.** No `nx_θ`-iterate of any other component of the colouring reaches up
into `[v_ℓ, 1 - θ)`, so lowering the appended entry from `1 - θ` to `1 - θ - δ` costs nothing.

The route is `HJO.Braid.gap_of_grid` at `n = 2D`, and all three of its inputs are now values:

* the grid at the positions is `HJO.Mellit.exists_int_braidDataOfColouring_fst_mul_gridDen`;
* the grid at the **iterates** — the clause that was open — is
  `HJO.Braid.exists_int_iterate_nextCrossing_mul` together with
  `HJO.Mellit.sweepTheta_mul_gridDen`;
* `δ·2D ≤ 1` is `HJO.Mellit.appendOffset_mul_gridDen` at `η ≤ aN + 1/2`, and by
  `HJO.Mellit.eq_sepLevel_of_le` that hypothesis pins `η = HJO.Mellit.sepLevel a N`.

This is the `(‡)` of the append clause, **not** the type-A gap clause refuted in
`HJO/Shuffle/BraidTypeAGapRefuted.lean`: the appended entry is the point of greatest rank
(`HJO.Mellit.braidDataOfColouring_fst_castSucc_lt_last`), where the refutation's witness turns on
the inserted point being the point of least rank. -/
theorem braidDataOfColouring_gap (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : Nat.Coprime a b)
    {η : ℚ} (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η)
    (hηN : ((a * N : ℕ) : ℚ) < η) (hηle : η ≤ sepLevel a N) {α : List ℕ} {y : Heights a b N}
    (hret : HasAboveReturns α y) {k : ℕ} (hlen : α.length = k + 1) :
    ∀ (t : Fin k) (i : ℕ),
      i + 1 < (braidDataOfColouring a b N y η (k + 1)).2 t.castSucc →
      (nextCrossing (sweepTheta a b N))^[i]
          ((braidDataOfColouring a b N y η (k + 1)).1 t.castSucc) <
        (braidDataOfColouring a b N y η (k + 1)).1 (Fin.last k) + sweepTheta a b N := by
  have hdata := (isSpecialBraidData_braidDataOfColouring_succ ha hb hN hab hηa hηs hηN
    hret hlen).comp_rotateLast
  have hθ := sweepTheta_mul_gridDen (a := a) (b := b) (N := N) ha hb hN
  have key := gap_of_grid (δ := appendOffset a b N η) (n := gridDen a b N) hdata
    (gridDen_pos (b := b) ha hN)
    (fun t i => by
      obtain ⟨m, hm⟩ := exists_int_braidDataOfColouring_fst_mul_gridDen ha hb hN hab hηa hηs hηN
        hret (rotateLast k t) (by rw [hlen]; exact (rotateLast k t).isLt)
      exact fun _ => exists_int_iterate_nextCrossing_mul hθ hm i)
    (appendOffset_pos ha hb hN hηN).le
    (by
      rw [appendOffset_mul_gridDen ha hb hN]
      rw [sepLevel] at hηle
      linarith)
    (by
      rw [comp_rotateLast_zero]
      exact braidDataOfColouring_fst_last_succ_eq ha hb hN hab hηa hηs hηN hret hlen)
  intro t i hi
  have := key t i (by simpa only [Function.comp_apply, rotateLast_succ] using hi)
  simpa only [Function.comp_apply, rotateLast_succ, rotateLast_zero] using this

end HJO.Mellit

end
