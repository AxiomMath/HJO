/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidDataLevelDrop
public import HJO.Shuffle.ColouringInversions
public import HJO.Shuffle.MellitProp57
public meta import HJO.Attr

/-! # Two obstructions under `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`

`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` asserts that the right-hand side of
`HJO.Mellit.braidValueColouring_eq_dsc_floor` —
`R_\pm = \pi_{k_\pm}(B_{s,v_\pm,\alpha_\pm})\,d_+^{k_\pm}(1)` — is related across one level drop by
the *same* factor `\Phi` of `HJO.Mellit.sweepOperator` that relates the left-hand sides. Two tools
suggest themselves for proving it: `HJO.Braid.specialBraid_mul_trainDown_one`, and the vanishing of
the `q`-exponent at a separating level. This file shows that neither is available, and both are
checkable facts rather than judgements.

## 1. `HJO.Braid.specialBraid_mul_trainDown_one` never applies to a colouring's braid data

That lemma — Mellit's Proposition 5.7, the natural braid-side move for the type-`A` clause — takes
an index `j` with `w_j = 1 - \theta`, a point at the *start* of its trajectory. No position of
`HJO.Mellit.braidDataOfColouring` is ever that number.

The reason is a parity count in the crossing lattice, and both halves of it are proved elsewhere.
Write `M := (aN+1)N` and `D := (a+b)M - 1`. Then `HJO.Mellit.exists_crossingAbscissa_eq_odd` says
every crossing abscissa of an admissible level is an *odd* multiple of `1/(2D)`, and taking the
fractional part subtracts an integer multiple of `2D/(2D)`, so the numerator stays odd. But
`HJO.Mellit.sweepTheta_eq_div` gives `\theta = aM/D`, so
`1 - \theta = (D - aM)/D = 2(D - aM)/(2D)` has an *even* numerator. An odd integer is not an even
one, so `v_i \ne 1 - \theta` — at every index, every level, every path.

`HJO.Mellit.braidDataOfColouring_fst_ne_one_sub_sweepTheta` and
`HJO.Mellit.not_exists_braidDataOfColouring_fst_eq_one_sub_sweepTheta` are that statement. The
consequence is that `HJO.Braid.specialBraid_mul_trainDown_one` serves the level recursion at *no*
event type: it cannot serve `C`, `D` or `E`, since the rank is equal there and nothing is inserted,
and it cannot serve `A` either.

**Where a repair would have to come from.** The general lemma behind
`HJO.Braid.specialBraid_mul_trainDown_one` is
`HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le`, which takes `w_j \le 1 - \theta`
together with a gap hypothesis — `u_m < w_j + \theta` at every stage of the move sequence, that is,
no other point sitting between `w_j` and the start. At `w_j = 1 - \theta` the gap is free, which is
why `HJO.Braid.specialBraid_mul_trainDown_one` states only that value. So the type-`A` clause could
only be reached through a further geometric statement about the crossing lattice — the natural guess
being that the component created at a type-`A` event carries the topmost position, within `\theta`
of the start — and not through `HJO.Braid.specialBraid_mul_trainDown_one` as stated. That guess is
false: `HJO/Shuffle/BraidPositionWindow.lean` shows the created component carries the *bottommost*
position, and works out what the gap hypothesis costs instead.

## 2. The separating-level simplification is unavailable: a bracketing pair never both separate

One might hope that the recursion is only ever needed at a separating level, because its user
`HJO.Mellit.mellitInduction_sweepWitness` carries `SeparatesDiagonal` in its own definition, and
that at such a level `HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal` makes the two inversion
counts equal, so that the `q^{1/2(...)}` of `HJO.Mellit.braidValueColouring_eq_dsc_floor` is `1`.
That conflates the one separating level of `HJO.Mellit.mellitInduction_sweepWitness` with the *pair*
of levels internal to the sweep that the recursion quantifies over, and the pair cannot both
separate the diagonal.

`HJO.Mellit.Isolates.not_and_separatesDiagonal` is the proof, and it is three lines from the
definition. With `P = (X, Y)` a point of the rectangle on or above the diagonal and
`\eta_- < \hat{rk}(P) < \eta_+`: if `\eta_-` separates then `bX < aY`
(`HJO.Mellit.Isolates.lt_of_separatesDiagonal_lo`), while if `\eta_+` separates then `bX = aY`
(`HJO.Mellit.Isolates.eq_of_separatesDiagonal_hi`). So at most one of the two levels separates, and
which one it can be is decided by whether `P` lies on the diagonal.

`HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal` therefore applies to at most one of `R_-`, `R_+`,
and the exponent `\frac12(\mathrm{inv_{fin}} - \mathrm{inv_{ini}})` of
`HJO.Mellit.braidValueColouring_eq_dsc_floor` is not known to agree at the two levels. Since
`D_{\eta_\pm, c_\pm} = q^{e_\pm} R_\pm`, the recursion with factor exactly `\Phi` and no power of
`q` carries the implicit obligation `e_- = e_+`, and the separating-level argument does not supply
it.

That obligation is not formal. `HJO.Braid.exists_rotation_invFin_sub_invIni_ne` exhibits a
multiplicity tuple and a rigid rotation of the positions — the very move
`HJO.Mellit.sweepTheta_eq_div` shows a level drop to be — across which
`\mathrm{inv_{fin}} - \mathrm{inv_{ini}}` changes, from `1` to `0`. So the exponent is not a
rotation invariant, and a clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` must
either predict it or carry it.

## Main results

* `HJO.Mellit.fract_crossingAbscissa_ne_one_sub_sweepTheta`,
  `HJO.Mellit.braidDataOfColouring_fst_ne_one_sub_sweepTheta`,
  `HJO.Mellit.not_exists_braidDataOfColouring_fst_eq_one_sub_sweepTheta` — `1 - \theta` is not a
  position of a colouring's braid data, so `HJO.Braid.specialBraid_mul_trainDown_one` has no
  instance here.
* `HJO.Mellit.Isolates.lt_of_separatesDiagonal_lo`,
  `HJO.Mellit.Isolates.eq_of_separatesDiagonal_hi`,
  `HJO.Mellit.Isolates.not_and_separatesDiagonal` — a bracketing pair of levels never both
  separate the diagonal.
* `HJO.Braid.exists_rotation_invFin_sub_invIni_ne` — the `q`-exponent of
  `HJO.Mellit.braidValueColouring_eq_dsc_floor` is not invariant under a rigid rotation of the
  positions.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### `1 - θ` is not a crossing -/

/-- **The start position `1 - θ` is never the fractional part of a crossing abscissa.** The
crossings of an admissible level are the odd multiples of `1/(2D)`
(`HJO.Mellit.exists_crossingAbscissa_eq_odd`) and taking the fractional part subtracts an integer,
which is an even multiple of `1/(2D)`; while `θ = aM/D` makes `1 - θ = 2(D - aM)/(2D)`, an even one.
So the two cannot be equal, and the hypothesis `w_j = 1 - θ` of
`HJO.Braid.specialBraid_mul_trainDown_one` is unsatisfiable by a colouring's braid data. -/
theorem fract_crossingAbscissa_ne_one_sub_sweepTheta (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {η : ℚ} (hη : IsAdmissibleLevel η) (n : ℤ) :
    Int.fract (crossingAbscissa a b N η n) ≠ 1 - sweepTheta a b N := by
  intro hcon
  obtain ⟨m, hm⟩ := exists_crossingAbscissa_eq_odd ha hb hN hη n
  have hD : (0 : ℚ) < crossingDen a b N := crossingDen_pos ha hb hN
  have hθ : sweepTheta a b N * crossingDen a b N = ((a * (a * N + 1) * N : ℕ) : ℚ) := by
    rw [sweepTheta_eq_div ha hb hN]; field_simp
  have hx : 2 * crossingDen a b N * crossingAbscissa a b N η n = 2 * (m : ℚ) + 1 := by
    rw [hm]; field_simp
  rw [Int.fract] at hcon
  have h := congrArg (fun z : ℚ => 2 * crossingDen a b N * z) hcon
  simp only [mul_sub, mul_one] at h
  rw [hx] at h
  have key : 2 * (m : ℚ) + 1 - 2 * crossingDen a b N * (⌊crossingAbscissa a b N η n⌋ : ℚ)
      = 2 * crossingDen a b N - 2 * ((a * (a * N + 1) * N : ℕ) : ℚ) := by
    linear_combination h - 2 * hθ
  rw [crossingDen] at key
  push_cast at key
  obtain ⟨t, ht⟩ : ∃ t : ℤ, 2 * m + 1 = 2 * t := by
    refine ⟨((((a + b) * (a * N + 1) * N : ℕ) : ℤ) - 1) * ⌊crossingAbscissa a b N η n⌋
      + ((((a + b) * (a * N + 1) * N : ℕ) : ℤ) - 1) - ((a * (a * N + 1) * N : ℕ) : ℤ), ?_⟩
    have h2 : ((2 * m + 1 : ℤ) : ℚ)
        = ((2 * (((((a + b) * (a * N + 1) * N : ℕ) : ℤ) - 1) * ⌊crossingAbscissa a b N η n⌋
            + ((((a + b) * (a * N + 1) * N : ℕ) : ℤ) - 1)
            - ((a * (a * N + 1) * N : ℕ) : ℤ)) : ℤ) : ℚ) := by
      push_cast
      linear_combination key
    exact_mod_cast h2
  omega

/-- **No position of a colouring's braid data is the start `1 - θ`.**
`HJO.Mellit.braidDataOfColouring` reads each `v_i` as the fractional part of a crossing abscissa, so
this is `HJO.Mellit.fract_crossingAbscissa_ne_one_sub_sweepTheta` at the top index of the `i`-th
component. -/
theorem braidDataOfColouring_fst_ne_one_sub_sweepTheta (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {η : ℚ} (hη : IsAdmissibleLevel η) (y : Heights a b N) {k : ℕ} (i : Fin k) :
    (braidDataOfColouring a b N y η k).1 i ≠ 1 - sweepTheta a b N := by
  rw [braidDataOfColouring_fst]
  exact fract_crossingAbscissa_ne_one_sub_sweepTheta ha hb hN hη _

/-- **`HJO.Braid.specialBraid_mul_trainDown_one` has no instance on a colouring's braid data.** Its
hypothesis is an index `j` with `w_j = 1 - θ` and `β_j = 1`; the first clause alone is
unsatisfiable, so the lemma cannot serve any clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` — including the type-`A` clause, whose rank
rise and multiplicity-`1` insertion do fit its shape in every other respect. See the module
docstring for where the usable general lemma is. -/
theorem not_exists_braidDataOfColouring_fst_eq_one_sub_sweepTheta (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η) (y : Heights a b N) {k : ℕ} :
    ¬ ∃ j : Fin k, (braidDataOfColouring a b N y η k).1 j = 1 - sweepTheta a b N :=
  fun ⟨j, hj⟩ => braidDataOfColouring_fst_ne_one_sub_sweepTheta ha hb hN hη y j hj

/-! ### A bracketing pair of levels never both separate the diagonal -/

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-- **If the lower level separates the diagonal the point is strictly above it.**
`HJO.Mellit.SeparatesDiagonal` makes `η < rk̂(x,y)` equivalent to `bx < ay` on the region, and the
lower level of a bracketing pair is under `rk̂(P)`. -/
theorem lt_of_separatesDiagonal_lo (hI : Isolates a b N X Y ηlo ηhi)
    (hdiag : (b : ℤ) * X ≤ (a : ℤ) * Y) (hsep : SeparatesDiagonal a b N ηlo) :
    (b : ℤ) * X < (a : ℤ) * Y :=
  (hsep X Y hI.xle hI.yle hdiag).1 hI.ltP

/-- **If the upper level separates the diagonal the point is on it.** The upper level of a
bracketing pair is over `rk̂(P)`, so the equivalence of `HJO.Mellit.SeparatesDiagonal` refuses
`bX < aY`. -/
theorem eq_of_separatesDiagonal_hi (hI : Isolates a b N X Y ηlo ηhi)
    (hdiag : (b : ℤ) * X ≤ (a : ℤ) * Y) (hsep : SeparatesDiagonal a b N ηhi) :
    (b : ℤ) * X = (a : ℤ) * Y := by
  have hrk : pointRank a b N (X, Y) = abovePointRank a b N X Y := rfl
  have hPlt := hI.Plt
  rw [hrk] at hPlt
  have hnot : ¬ ((b : ℤ) * X < (a : ℤ) * Y) := fun hlt =>
    absurd ((hsep X Y hI.xle hI.yle hdiag).2 hlt) (by linarith)
  exact le_antisymm hdiag (not_lt.1 hnot)

/-- **The two levels of a bracketing pair never both separate the diagonal.** One would put the
point strictly above the diagonal and the other on it.

This is what rules out the separating-level simplification for
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`: that the recursion is only needed at a
separating level, so that `HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal` makes both inversion
counts of `HJO.Mellit.braidValueColouring_eq_dsc_floor` vanish and the `q^{1/2}` factor is `1`. At
most one of the two levels can be separating, so at most one of the two exponents is known to
vanish, and the claim that `R_-` and `R_+` are related by the factor `Φ` *alone* carries the
implicit obligation that the two exponents agree. -/
theorem not_and_separatesDiagonal (hI : Isolates a b N X Y ηlo ηhi)
    (hdiag : (b : ℤ) * X ≤ (a : ℤ) * Y) :
    ¬ (SeparatesDiagonal a b N ηlo ∧ SeparatesDiagonal a b N ηhi) := by
  rintro ⟨hlo, hhi⟩
  exact absurd (eq_of_separatesDiagonal_hi hI hdiag hhi)
    (ne_of_lt (lt_of_separatesDiagonal_lo hI hdiag hlo))

end Isolates

end HJO.Mellit

namespace HJO.Braid

/-! ### The `q`-exponent of `HJO.Mellit.braidValueColouring_eq_dsc_floor` is not a rotation
invariant -/

/-- **A rigid rotation of the positions changes `inv_fin - inv_ini`.** At `θ = 2/5`, rank `2` and
multiplicities `(2, 1)`, the data `v = (1/5, 3/5)` has `inv_ini = 0` and `inv_fin = 1`, while its
rotation by `3/5` — entrywise `v'_i = {v_i + 3/5}`, which is `(4/5, 1/5)` — has
`inv_ini = inv_fin = 1`. So the exponent of `HJO.Mellit.braidValueColouring_eq_dsc_floor` moves from
`1` to `0` under exactly the move `HJO.Mellit.sweepTheta_eq_div` shows a level drop to be.

The witness is not itself a level drop — that would need positions on the crossing lattice of a
rectangle — but it settles the shape of the question: the exponent is not a formal invariant of the
rotation, so a clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` owes it. -/
theorem exists_rotation_invFin_sub_invIni_ne :
    ∃ (θ c : ℚ) (v v' : Fin 2 → ℚ) (α : Fin 2 → ℕ),
      0 < θ ∧ θ < 1 ∧ 0 < c ∧ c < 1 ∧ (∀ i, v' i = Int.fract (v i + c)) ∧
        ((invFin θ v' α : ℤ) - (invIni θ v' α : ℤ))
          ≠ ((invFin θ v α : ℤ) - (invIni θ v α : ℤ)) := by
  refine ⟨2 / 5, 3 / 5, fun i => if i = 0 then 1 / 5 else 3 / 5,
    fun i => if i = 0 then 4 / 5 else 1 / 5, fun i => if i = 0 then 2 else 1,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

end HJO.Braid

end
