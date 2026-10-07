/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidInversions
public import HJO.Shuffle.ColouringBraidData
public import HJO.Shuffle.MellitRem41Level
public meta import HJO.Attr

/-! # `HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal`: the two label inversion counts of a
minimal-gap colouring

`HJO.Braid.invIni` and `HJO.Braid.invFin` count the inversions of the initial and the final
position tuple of a piece of special-braid data, and the `q`-power of
`HJO.Mellit.braidValueColouring_eq_dsc_floor` is `q^{(inv_fin - inv_ini)/2}`. This file proves that
the two counts agree for the data of a colouring at a level that separates the diagonal — the
minimal-gap case — so that the power is `1`.

## The mechanism, which is not the one of the argument usually given

Both position tuples are fractional parts of crossing abscissae, and the file rests on one
identity: the crossing of index `x + w` lies in the column of `x`, at the height the rank of
`(x, w)` measures, so its fractional part is `(rk̂(x, w) - η) / ((a+b)(aN+1)N - 1)`. That is
`HJO.Mellit.fract_crossingAbscissa_natCast_add`.

`componentTopIndex` is `x(w_i) + y(w_i)` and `componentBotIndex` is `x(u_i) + I_{x(u_i)} + 1`, so
both tuples are ranks read through that formula: the initial tuple is the rank of the crossed east
step `w_i`, and the final tuple the rank of the lattice point of the column of `u_i` just above the
level line. At a separating level the first is `b(aN+1)N + x(w_i)` and the second is `ω + x(u_i)`
with `ω` the attack window, because a separating level pins a crossed step onto the diagonal. Both
are therefore **strictly increasing** along the column listing, so *both* counts are `0`.

**That is not what the argument usually given says, and that argument is wrong about it.** It reads:
"at a colouring with minimal gaps all the points are clustered near the start in the initial
position and near the finish in the final position, with their labels in the opposite order in both,
so both counts are `binom(ℓ,2)`". The labels are in the *same* order in the two positions, not
opposite: both tuples increase with the index, so both counts are `0` and not `binom(ℓ,2)`. The
conclusion `inv_fin = inv_ini` — all the statement asserts, and all
`HJO.Mellit.mellitInduction_sweepWitness` uses — is unaffected, and
`HJO.Mellit.invIni_eq_zero_of_separates`, `HJO.Mellit.invFin_eq_zero_of_separates` record the value
the argument above gives.

## Main results

* `HJO.Mellit.fract_crossingAbscissa_natCast_add` — the rank formula for the fractional part of a
  crossing abscissa.
* `HJO.Mellit.fract_crossingAbscissa_componentTopIndex`,
  `HJO.Mellit.fract_crossingAbscissa_componentBotIndex` — the two tuples as ranks. Neither needs
  the level to separate the diagonal; the windows they need are exactly the two inequalities
  `HJO.Mellit.colouring` puts on a crossed step.
* `HJO.Mellit.pointRank_of_mem_colouringNorth`, `HJO.Mellit.pointRank_of_mem_colouringEast` — a
  separating level pins a crossed step onto the diagonal, which is what makes the ranks affine in
  the column.
* `HJO.Mellit.invIni_eq_zero_of_separates`, `HJO.Mellit.invFin_eq_zero_of_separates` — each count
  is `0`.
* `HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal` — the statement.
* `HJO.Mellit.invFin_eq_invIni_compColouring` — the statement in the `c_α` wording.

## Hypotheses

The statement's hypothesis on the level is `HJO.Mellit.SeparatesDiagonal`: "a lattice point `(x,y)`
with `0 ≤ x ≤ aN`, `0 ≤ y ≤ bN` and `ay ≥ bx` satisfies `rk̂(x,y) > η` if and only if `ay > bx`".
`0 < a`, `0 < b` and `0 < N` are carried explicitly; the standing hypothesis of the setting is
`1 < a < b` with `N ≥ 1`. They are needed: at `N = 0` there
are no crossings to count, and `(a+b)(aN+1)N - 1` is the denominator of every formula here.

No coprimality of `a` and `b` is spent, and the colouring is not identified with `c_α`:
`HJO.Mellit.colouring_eq_compColouring_iff` says the colouring of an above-diagonal path at a
separating admissible level *is* `c_α` for `α` the path's return composition, so the statement's
restriction to `c_α` is no restriction, and the statement below quantifies over the path instead.

## References

This file proves `HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal`, using
`HJO.Braid.IsSpecialBraidData`, `HJO.Braid.invIni`, `HJO.Braid.invFin`,
`HJO.ParkingFunctions.abovePointRank`, `HJO.Mellit.IsAdmissibleLevel`, `HJO.Mellit.compColouring`,
`HJO.Mellit.braidDataOfColouring`, `HJO.Mellit.colouringComponent`, `HJO.Braid.positionPair`.
-/

@[expose] public section

open Finset

namespace HJO.Braid

/-- **A strictly increasing tuple has no inversion.** `HJO.Braid.tupleInversions_eq_card_lt` drops
the ranks, and an increasing tuple has no pair `i < j` with `w_j < w_i`. -/
theorem tupleInversions_eq_zero_of_strictMono {k : ℕ} {w : Fin k → ℚ}
    (h : ∀ i j : Fin k, i < j → w i < w j) : tupleInversions w = 0 := by
  rw [tupleInversions_eq_card_lt, Finset.card_eq_zero]
  refine Finset.filter_eq_empty_iff.2 ?_
  rintro p -
  rintro ⟨hlt, hw⟩
  exact absurd (h p.1 p.2 hlt) (not_lt.2 hw.le)

end HJO.Braid

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The denominator of a crossing abscissa

`HJO.Mellit.crossingAbscissa` divides by `1 + s_{a,b,N}`, whose numerator over the common
denominator `a(aN+1)N` of `HJO.Mellit.sweepSlope` and `HJO.Mellit.levelIntercept` is
`(a+b)(aN+1)N - 1`. Every fractional part below is a rank over that integer. -/

/-- The integer `(a+b)(aN+1)N - 1`: the denominator of the fractional part of a crossing abscissa,
equal to `a(aN+1)N (1 + s_{a,b,N})`. -/
def crossDen (a b N : ℕ) : ℚ := ((a + b) * (a * N + 1) * N : ℕ) - 1

/-- The denominator is positive once the rectangle has a column and a row. -/
theorem crossDen_pos (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) : 0 < crossDen a b N := by
  have h : 2 ≤ (a + b) * (a * N + 1) * N :=
    calc 2 = 2 * 1 * 1 := by norm_num
      _ ≤ (a + b) * (a * N + 1) * N :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hN
  have h' : (2 : ℚ) ≤ (((a + b) * (a * N + 1) * N : ℕ) : ℚ) := by exact_mod_cast h
  rw [crossDen]
  linarith

/-- The attack window is at most the crossing denominator: `ω = a(aN+1)N` and `(a+b)(aN+1)N - 1`
differ by `b(aN+1)N - 1 ≥ 0`. -/
theorem cast_attackWindow_le_crossDen (hb : 0 < b) (hN : 0 < N) :
    ((attackWindow a N : ℕ) : ℚ) ≤ crossDen a b N := by
  have haw : attackWindow a N = a * (a * N + 1) * N := by
    simp only [attackWindow]; ring
  have hsplit : (a + b) * (a * N + 1) * N = a * (a * N + 1) * N + b * (a * N + 1) * N := by ring
  have h1 : 1 ≤ b * (a * N + 1) * N := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h : attackWindow a N + 1 ≤ (a + b) * (a * N + 1) * N := by
    rw [haw, hsplit]
    exact Nat.add_le_add_left h1 _
  have h' : ((attackWindow a N : ℕ) : ℚ) + 1 ≤ (((a + b) * (a * N + 1) * N : ℕ) : ℚ) := by
    exact_mod_cast h
  rw [crossDen]
  linarith

/-- `b(aN+1)N - 1` is at most the crossing denominator: it is the amount by which one step east
lowers the rank. -/
theorem cast_bMN_sub_one_le_crossDen :
    (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 ≤ crossDen a b N := by
  have h : b * (a * N + 1) * N ≤ (a + b) * (a * N + 1) * N :=
    Nat.mul_le_mul (Nat.mul_le_mul (by omega) (le_refl _)) (le_refl _)
  have h' : (((b * (a * N + 1) * N : ℕ)) : ℚ) ≤ (((a + b) * (a * N + 1) * N : ℕ) : ℚ) := by
    exact_mod_cast h
  push_cast at h'
  rw [crossDen]
  push_cast
  linarith

/-- The crossing denominator is `a(aN+1)N` times `1 + s_{a,b,N}`. -/
theorem crossDen_eq_mul (ha : 0 < a) (hN : 0 < N) :
    crossDen a b N = ((a : ℚ) * ((a : ℚ) * N + 1) * N) * (1 + sweepSlope a b N) := by
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hM : ((a : ℚ) * N + 1) ≠ 0 := by positivity
  rw [crossDen, sweepSlope]
  push_cast
  field_simp
  ring

/-! ### The fractional part of a crossing abscissa is a rank -/

/-- **The crossing of index `x + w` lies in the column of `x`, at the height the rank of `(x, w)`
measures.** This is the one identity the file rests on: rescaling by `a(aN+1)N` turns
`crossingAbscissa a b N η (x + w) - x` into `(rk̂(x, w) - η) / ((a+b)(aN+1)N - 1)`. -/
theorem crossDen_mul_crossingAbscissa_natCast_add_sub (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (η : ℚ) (x w : ℕ) :
    crossDen a b N * (crossingAbscissa a b N η ((x : ℤ) + (w : ℤ)) - (x : ℚ)) =
      ((abovePointRank a b N x w : ℤ) : ℚ) - η := by
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hM : ((a : ℚ) * N + 1) ≠ 0 := by positivity
  have hs : (1 : ℚ) + sweepSlope a b N ≠ 0 := (one_add_sweepSlope_pos ha hb hN).ne'
  have hval : (1 + sweepSlope a b N) *
      crossingAbscissa a b N η ((x : ℤ) + (w : ℤ)) + levelIntercept a N η =
      (((x : ℤ) + (w : ℤ) : ℤ) : ℚ) := by
    rw [crossingAbscissa, mul_div_cancel₀ _ hs]
    ring
  have hDi : ((a : ℚ) * ((a : ℚ) * N + 1) * N) * levelIntercept a N η = η := by
    rw [levelIntercept]
    field_simp
  have hDs : ((a : ℚ) * ((a : ℚ) * N + 1) * N) * sweepSlope a b N =
      (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 := by
    rw [sweepSlope]
    field_simp
  rw [abovePointRank]
  push_cast at hval ⊢
  linear_combination (crossingAbscissa a b N η ((x : ℤ) + (w : ℤ)) - (x : ℚ)) *
      crossDen_eq_mul (b := b) ha hN +
    ((a : ℚ) * ((a : ℚ) * N + 1) * N) * hval - hDi - (x : ℚ) * hDs

/-- The division form of `HJO.Mellit.crossDen_mul_crossingAbscissa_natCast_add_sub`. -/
theorem crossingAbscissa_natCast_add_sub (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ)
    (x w : ℕ) :
    crossingAbscissa a b N η ((x : ℤ) + (w : ℤ)) - (x : ℚ) =
      (((abovePointRank a b N x w : ℤ) : ℚ) - η) / crossDen a b N := by
  rw [eq_div_iff (crossDen_pos ha hb hN).ne', mul_comm]
  exact crossDen_mul_crossingAbscissa_natCast_add_sub ha hb hN η x w

/-- **The fractional part of the crossing of index `x + w`**, when the rank of `(x, w)` lies in the
window `(η, η + (a+b)(aN+1)N - 1)` that puts the crossing inside the column of `x`. -/
theorem fract_crossingAbscissa_natCast_add (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    {x w : ℕ} (h1 : η < ((abovePointRank a b N x w : ℤ) : ℚ))
    (h2 : ((abovePointRank a b N x w : ℤ) : ℚ) < η + crossDen a b N) :
    Int.fract (crossingAbscissa a b N η ((x : ℤ) + (w : ℤ))) =
      (((abovePointRank a b N x w : ℤ) : ℚ) - η) / crossDen a b N := by
  have hE := crossDen_pos (a := a) (b := b) (N := N) ha hb hN
  have key := crossingAbscissa_natCast_add_sub (a := a) (b := b) (N := N) ha hb hN η x w
  have hlow : (0 : ℚ) < (((abovePointRank a b N x w : ℤ) : ℚ) - η) / crossDen a b N :=
    div_pos (by linarith) hE
  have hhigh : (((abovePointRank a b N x w : ℤ) : ℚ) - η) / crossDen a b N < 1 :=
    (div_lt_one hE).2 (by linarith)
  have hfl : ⌊crossingAbscissa a b N η ((x : ℤ) + (w : ℤ))⌋ = (x : ℤ) := by
    rw [Int.floor_eq_iff]
    refine ⟨by push_cast; linarith, by push_cast; linarith⟩
  rw [Int.fract, hfl]
  push_cast
  linarith

/-! ### The two position tuples as ranks -/

/-- **The initial position tuple is the rank of the crossed east step.** The top index of the
`i`-th component is `x(w_i) + y(w_i)` by `HJO.Mellit.componentTopIndex_eq`, and the two conditions
`HJO.Mellit.colouring` puts on a crossed east step are exactly the window
`HJO.Mellit.fract_crossingAbscissa_natCast_add` needs: `η < rk̂(w_i)` is its lower end, and
`rk̂(w_i + (1,0)) < η` its upper one, the two ranks differing by `b(aN+1)N - 1`. -/
theorem fract_crossingAbscissa_componentTopIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) {y : Heights a b N} {i : ℕ}
    (hi : i < #(colouringEast y η)) :
    Int.fract (crossingAbscissa a b N η (componentTopIndex a b N y η i)) =
      (((pointRank a b N (colStep (colouringEast y η) i) : ℤ) : ℚ) - η) / crossDen a b N := by
  obtain ⟨-, hup, hdown⟩ := Finset.mem_filter.1 (colStep_mem hi)
  set Q := colStep (colouringEast y η) i with hQ
  have hup' : ((abovePointRank a b N Q.1 Q.2 : ℤ) : ℚ)
      < η + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
    have hshift : ((abovePointRank a b N (Q.1 + 1) Q.2 : ℤ) : ℚ)
        = ((abovePointRank a b N Q.1 Q.2 : ℤ) : ℚ) + 1
          - (b : ℚ) * ((a : ℚ) * N + 1) * N := by
      simp only [abovePointRank]
      push_cast
      ring
    have : ((abovePointRank a b N (Q.1 + 1) Q.2 : ℤ) : ℚ) < η := hup
    rw [hshift] at this
    linarith
  have hbnd := cast_bMN_sub_one_le_crossDen (a := a) (b := b) (N := N)
  rw [componentTopIndex_eq ha hb hN hη hηpos hi, ← hQ,
    fract_crossingAbscissa_natCast_add ha hb hN (x := Q.1) (w := Q.2) hdown (by linarith)]
  simp only [pointRank]

/-- **The final position tuple is the rank of the lattice point just above the level line in the
column of the crossed north step.** The bottom index of the `i`-th component is
`x(u_i) + I_{x(u_i)} + 1` by `HJO.Mellit.componentBotIndex_eq`, and the ordinate of a crossed north
step *is* the level index of its column, so that index is `x(u_i) + y(u_i) + 1`; the two conditions
on a crossed north step are the window, the head of the step outranking the foot by exactly the
attack window. -/
theorem fract_crossingAbscissa_componentBotIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) {y : Heights a b N} {i : ℕ}
    (hi : i < #(colouringNorth y η)) :
    Int.fract (crossingAbscissa a b N η (componentBotIndex a b N y η i)) =
      (((pointRank a b N (colStep (colouringNorth y η) i) : ℤ) : ℚ)
        + ((attackWindow a N : ℕ) : ℚ) - η) / crossDen a b N := by
  have hlevel : ((colStep (colouringNorth y η) i).2 : ℤ)
      = levelIndex a b N η (colStep (colouringNorth y η) i).1 :=
    (mem_colouringNorth_spec ha hN hη y (colStep_mem hi)).2.2.2
  obtain ⟨-, hdown, hup⟩ := Finset.mem_filter.1 (colStep_mem hi)
  set P := colStep (colouringNorth y η) i with hP
  have hsucc : ((abovePointRank a b N P.1 (P.2 + 1) : ℤ) : ℚ)
      = ((abovePointRank a b N P.1 P.2 : ℤ) : ℚ) + ((attackWindow a N : ℕ) : ℚ) := by
    rw [abovePointRank_succ a b N P.1 P.2]
    push_cast
    ring
  have hbot : componentBotIndex a b N y η i = ((P.1 : ℕ) : ℤ) + ((P.2 + 1 : ℕ) : ℤ) := by
    rw [componentBotIndex_eq ha hb hN hη hηpos y i, ← hP, ← hlevel]
    push_cast
    ring
  have hwin := cast_attackWindow_le_crossDen (a := a) (b := b) (N := N) hb hN
  have hdown' : ((abovePointRank a b N P.1 P.2 : ℤ) : ℚ) < η := hdown
  have hup' : η < ((abovePointRank a b N P.1 P.2 : ℤ) : ℚ) + ((attackWindow a N : ℕ) : ℚ) := hup
  rw [hbot, fract_crossingAbscissa_natCast_add ha hb hN (x := P.1) (w := P.2 + 1)
    (by rw [hsucc]; linarith) (by rw [hsucc]; linarith), hsucc]
  simp only [pointRank]

/-! ### A separating level pins a crossed step onto the diagonal -/

/-- **A crossed north step of a separating level stands on the diagonal**, so its rank is its
abscissa: the two conditions of `HJO.Mellit.colouring` put the foot below the level, and a point
of the region below a separating level is not strictly above the diagonal. -/
theorem pointRank_of_mem_colouringNorth {η : ℚ}
    (hηs : SeparatesDiagonal a b N η) {y : Heights a b N} (hy : IsAboveDiagonal y) {P : ℕ × ℕ}
    (hP : P ∈ colouringNorth y η) : pointRank a b N P = (P.1 : ℤ) := by
  obtain ⟨hns, hdown, -⟩ := Finset.mem_filter.1 hP
  obtain ⟨h1, h2, h3⟩ := mem_northSteps_iff.1 hns
  have hx : P.1 ≤ a * N := h1.le
  have hy2 : P.2 ≤ b * N := le_trans h3.le (ht_le_mul y _)
  have hdiag : b * P.1 ≤ a * P.2 :=
    le_trans (hy.2.2.2 P.1 hx) (Nat.mul_le_mul_left a h2)
  have hnot : ¬ b * P.1 < a * P.2 := fun hc =>
    absurd ((lt_pointRank_iff hηs hx hy2 hdiag).2 hc) (not_lt.2 hdown.le)
  have heq : (a : ℤ) * P.2 - (b : ℤ) * P.1 = 0 := by
    have : b * P.1 = a * P.2 := by omega
    have h' : (b : ℤ) * P.1 = (a : ℤ) * P.2 := by exact_mod_cast this
    omega
  simp only [pointRank, abovePointRank, heq]
  ring

/-- **A crossed east step of a separating level arrives on the diagonal**, so its rank is
`b(aN+1)N + x`: the first condition of `HJO.Mellit.colouring` puts the head of the step below the
level, and a point of the region below a separating level is not strictly above the diagonal. -/
theorem pointRank_of_mem_colouringEast {η : ℚ}
    (hηs : SeparatesDiagonal a b N η) {y : Heights a b N} (hy : IsAboveDiagonal y) {P : ℕ × ℕ}
    (hP : P ∈ colouringEast y η) :
    pointRank a b N P = ((a : ℤ) * N + 1) * N * b + (P.1 : ℤ) := by
  obtain ⟨hes, hdown, -⟩ := Finset.mem_filter.1 hP
  obtain ⟨h1, h2⟩ := mem_eastSteps_iff.1 hes
  have hx : P.1 + 1 ≤ a * N := by omega
  have hy2 : P.2 ≤ b * N := h2 ▸ ht_le_mul y _
  have hdiag : b * (P.1 + 1) ≤ a * P.2 := by
    rw [h2]
    exact hy.2.2.2 (P.1 + 1) hx
  have hnot : ¬ b * (P.1 + 1) < a * P.2 := fun hc =>
    absurd ((lt_pointRank_iff hηs (P := (P.1 + 1, P.2)) hx hy2 hdiag).2 hc)
      (not_lt.2 hdown.le)
  have heq : (a : ℤ) * P.2 - (b : ℤ) * P.1 = (b : ℤ) := by
    have hnat : b * (P.1 + 1) = a * P.2 := by omega
    have h' : (b : ℤ) * ((P.1 : ℤ) + 1) = (a : ℤ) * P.2 := by exact_mod_cast hnat
    linarith
  simp only [pointRank, abovePointRank, heq]

/-! ### Both counts vanish -/

/-- A separating admissible level exceeds `aN`, the rank of the top corner of the rectangle. This is
the hypothesis the crossing layer of `HJO/Shuffle/ColouringBraidData.lean` carries. -/
theorem cast_mul_lt_of_separatesDiagonal {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) : ((a * N : ℕ) : ℚ) < η := by
  have heqz : (b : ℤ) * ((a * N : ℕ) : ℤ) = (a : ℤ) * ((b * N : ℕ) : ℤ) := by push_cast; ring
  have hiff := hηs (a * N) (b * N) le_rfl le_rfl heqz.le
  have hnot : ¬ η < ((abovePointRank a b N (a * N) (b * N) : ℤ) : ℚ) := fun hc => by
    rw [heqz] at hiff
    exact absurd (hiff.1 hc) (lt_irrefl _)
  rw [abovePointRank_diag a b N N] at hnot
  have hle : ((a * N : ℕ) : ℚ) ≤ η := by
    have := not_lt.1 hnot
    push_cast at this ⊢
    linarith
  refine lt_of_le_of_ne hle ?_
  have hne := intCast_ne_of_isAdmissibleLevel hηa ((a * N : ℕ) : ℤ)
  push_cast at hne ⊢
  exact hne

/-- **The initial count is `0`**: at a separating level the rank of the `i`-th crossed east step is
`b(aN+1)N + x(w_i)`, and the columns increase along the listing. -/
theorem invIni_eq_zero_of_separates (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    Braid.invIni (sweepTheta a b N)
        (braidDataOfColouring a b N y η #(colouringNorth y η)).1
        (braidDataOfColouring a b N y η #(colouringNorth y η)).2 = 0 := by
  have hηN := cast_mul_lt_of_separatesDiagonal (a := a) (b := b) (N := N) hηa hηs
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηN
  have hE := crossDen_pos (a := a) (b := b) (N := N) ha hb hN
  have hk : #(colouringNorth y η) = #(colouringEast y η) :=
    card_colouringNorth_eq_card_colouringEast hb hN hηa hηN hy
  rw [Braid.invIni_eq_tupleInversions]
  refine Braid.tupleInversions_eq_zero_of_strictMono fun i j hij => ?_
  have hiE : (i : ℕ) < #(colouringEast y η) := hk ▸ i.isLt
  have hjE : (j : ℕ) < #(colouringEast y η) := hk ▸ j.isLt
  rw [braidDataOfColouring_fst, braidDataOfColouring_fst,
    fract_crossingAbscissa_componentTopIndex ha hb hN hηa hηpos hiE,
    fract_crossingAbscissa_componentTopIndex ha hb hN hηa hηpos hjE,
    pointRank_of_mem_colouringEast hηs hy (colStep_mem hiE),
    pointRank_of_mem_colouringEast hηs hy (colStep_mem hjE),
    div_lt_div_iff_of_pos_right hE]
  have hcol : (colStep (colouringEast y η) i).1 < (colStep (colouringEast y η) j).1 :=
    colStep_fst_lt (columnInjective_colouringEast ha hN hηa y) hjE hij
  have hcol' : ((colStep (colouringEast y η) i).1 : ℚ)
      < ((colStep (colouringEast y η) j).1 : ℚ) := by exact_mod_cast hcol
  push_cast
  linarith

/-- The final position tuple of the data of a colouring is the fractional part of the crossing of
the *bottom* index of each component: the multiplicity counts the indices from the bottom to the
top, so `α_i - 1` iterates of `HJO.Braid.nextCrossing` take the top crossing to the bottom one. -/
theorem positionPair_snd_braidDataOfColouring (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηN : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (i : Fin #(colouringNorth y η)) :
    (Braid.nextCrossing (sweepTheta a b N))^[
        (braidDataOfColouring a b N y η #(colouringNorth y η)).2 i - 1]
      ((braidDataOfColouring a b N y η #(colouringNorth y η)).1 i) =
      Int.fract (crossingAbscissa a b N η (componentBotIndex a b N y η i)) := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηN
  have hBT := componentBotIndex_le_componentTopIndex ha hb hN hη hηN hy i.isLt
  have hcard : (braidDataOfColouring a b N y η #(colouringNorth y η)).2 i =
      (componentTopIndex a b N y η i + 1 - componentBotIndex a b N y η i).toNat := by
    rw [braidDataOfColouring_snd, componentCrossingIndices_eq_Icc, Int.card_Icc]
  have hidx : componentTopIndex a b N y η i -
      (((braidDataOfColouring a b N y η #(colouringNorth y η)).2 i - 1 : ℕ) : ℤ) =
      componentBotIndex a b N y η i := by
    rw [hcard]
    omega
  rw [braidDataOfColouring_fst,
    iterate_nextCrossing_fract_crossingAbscissa ha hb hN hη hηpos y i (by rw [hidx]), hidx]

/-- **The final count is `0`**: at a separating level the rank of the lattice point just above the
level line in the column of the `i`-th crossed north step is `ω + x(u_i)`, and the columns increase
along the listing. -/
theorem invFin_eq_zero_of_separates (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    Braid.invFin (sweepTheta a b N)
        (braidDataOfColouring a b N y η #(colouringNorth y η)).1
        (braidDataOfColouring a b N y η #(colouringNorth y η)).2 = 0 := by
  have hηN := cast_mul_lt_of_separatesDiagonal (a := a) (b := b) (N := N) hηa hηs
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηN
  have hE := crossDen_pos (a := a) (b := b) (N := N) ha hb hN
  rw [Braid.invFin_eq_tupleInversions]
  refine Braid.tupleInversions_eq_zero_of_strictMono fun i j hij => ?_
  rw [positionPair_snd_braidDataOfColouring ha hb hN hηa hηN hy i,
    positionPair_snd_braidDataOfColouring ha hb hN hηa hηN hy j,
    fract_crossingAbscissa_componentBotIndex ha hb hN hηa hηpos i.isLt,
    fract_crossingAbscissa_componentBotIndex ha hb hN hηa hηpos j.isLt,
    pointRank_of_mem_colouringNorth hηs hy (colStep_mem i.isLt),
    pointRank_of_mem_colouringNorth hηs hy (colStep_mem j.isLt),
    div_lt_div_iff_of_pos_right hE]
  have hcol : (colStep (colouringNorth y η) i).1 < (colStep (colouringNorth y η) j).1 :=
    colStep_fst_lt (columnInjective_colouringNorth ha hN hηa y) j.isLt hij
  have hcol' : ((colStep (colouringNorth y η) i).1 : ℚ)
      < ((colStep (colouringNorth y η) j).1 : ℚ) := by exact_mod_cast hcol
  push_cast
  linarith

/-! ### The statement -/

/-- **The inversion counts of a minimal-gap colouring agree**: for the special-braid data
`(v, α^br)` of the colouring of an above-diagonal path at an admissible level separating the
diagonal, `inv_fin(v, α^br) = inv_ini(v, α^br)`.

Both counts are `0`, by `HJO.Mellit.invIni_eq_zero_of_separates` and
`HJO.Mellit.invFin_eq_zero_of_separates`; the argument usually given asserts that both are
`binom(ℓ,2)`, which is false — see the module docstring. The conclusion is the stated one.

The colouring is written as that of a path rather than as `c_α` because
`HJO.Mellit.braidDataOfColouring` reads the components off the path; by
`HJO.Mellit.colouring_eq_compColouring_iff` an above-diagonal path is coloured `c_α` at such a level
exactly when its return composition is `α`, so this is the statement with its `c_α` unfolded, and
`HJO.Mellit.invFin_eq_invIni_compColouring` states it with the colouring named `c_α`. -/
@[hjo "lem_mellit_inv_balanced"]
theorem invFin_eq_invIni_of_separatesDiagonal (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    Braid.invFin (sweepTheta a b N)
        (braidDataOfColouring a b N y η #(colouringNorth y η)).1
        (braidDataOfColouring a b N y η #(colouringNorth y η)).2 =
      Braid.invIni (sweepTheta a b N)
        (braidDataOfColouring a b N y η #(colouringNorth y η)).1
        (braidDataOfColouring a b N y η #(colouringNorth y η)).2 := by
  rw [invFin_eq_zero_of_separates ha hb hN hηa hηs hy,
    invIni_eq_zero_of_separates ha hb hN hηa hηs hy]

/-- **The statement in its own wording**: the colouring is named as `c_α` for a composition
`α` of `N` with positive parts. The hypothesis `colouring y η = c_α` is not used — by
`HJO.Mellit.colouring_eq_compColouring_iff` it holds for some such `α` whenever the path is
above-diagonal and the level separates the diagonal, so it restricts nothing — and is carried only
so that this statement has its stated form. -/
theorem invFin_eq_invIni_compColouring (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {α : List ℕ} (_hpos : ∀ x ∈ α, 0 < x) (_hsum : α.sum = N)
    (_hc : colouring y η = compColouring a b α) :
    Braid.invFin (sweepTheta a b N)
        (braidDataOfColouring a b N y η #(colouringNorth y η)).1
        (braidDataOfColouring a b N y η #(colouringNorth y η)).2 =
      Braid.invIni (sweepTheta a b N)
        (braidDataOfColouring a b N y η #(colouringNorth y η)).1
        (braidDataOfColouring a b N y η #(colouringNorth y η)).2 :=
  invFin_eq_invIni_of_separatesDiagonal ha hb hN hηa hηs hy

/-! ### The statement at two components, and the value refuted -/

/-- The colouring of the above-diagonal `(4,6)`-path of heights `(0,2,3,5,6)` at the separating
level `η = 4 + 1/2`: its two returns below the top are `0` and `1`, so it has exactly two
components. -/
theorem colouringNorth_example :
    colouringNorth (![0, 2, 3, 5, 6] : Heights 2 3 2) (sepLevel 2 2) = {(0, 0), (2, 3)} := by
  have hn : northSteps (![0, 2, 3, 5, 6] : Heights 2 3 2) =
      {(0, 0), (0, 1), (1, 2), (2, 3), (2, 4), (3, 5)} := by decide
  rw [colouringNorth, hn]
  norm_num [pointRank, abovePointRank, attackWindow, sepLevel, Finset.filter_insert,
    Finset.filter_singleton]

/-- **The statement is not vacuous at two components, and the *value* is refuted there.**
On the above-diagonal `(4,6)`-path of heights `(0,2,3,5,6)` — the path of return composition
`(1,1)` — the colouring at `η = 4 + 1/2` has two components, and *both* inversion counts are `0`.
The argument usually given asserts that both are `binom(ℓ,2)`, which here is `1`. So the counts
agree, as the statement says, but not at the value that argument gives. -/
theorem invBalanced_example :
    #(colouringNorth (![0, 2, 3, 5, 6] : Heights 2 3 2) (sepLevel 2 2)) = 2 ∧
      Braid.invIni (sweepTheta 2 3 2)
          (braidDataOfColouring 2 3 2 (![0, 2, 3, 5, 6] : Heights 2 3 2) (sepLevel 2 2) 2).1
          (braidDataOfColouring 2 3 2 (![0, 2, 3, 5, 6] : Heights 2 3 2) (sepLevel 2 2) 2).2 = 0 ∧
      Braid.invFin (sweepTheta 2 3 2)
          (braidDataOfColouring 2 3 2 (![0, 2, 3, 5, 6] : Heights 2 3 2) (sepLevel 2 2) 2).1
          (braidDataOfColouring 2 3 2 (![0, 2, 3, 5, 6] : Heights 2 3 2) (sepLevel 2 2) 2).2
        = 0 := by
  have hcard : #(colouringNorth (![0, 2, 3, 5, 6] : Heights 2 3 2) (sepLevel 2 2)) = 2 := by
    rw [colouringNorth_example]
    decide
  have hy : IsAboveDiagonal (![0, 2, 3, 5, 6] : Heights 2 3 2) := by decide
  have hi := invIni_eq_zero_of_separates (a := 2) (b := 3) (N := 2) (by norm_num) (by norm_num)
    (by norm_num) (isAdmissibleLevel_sepLevel 2 2) (separatesDiagonal_sepLevel (by norm_num)) hy
  have hf := invFin_eq_zero_of_separates (a := 2) (b := 3) (N := 2) (by norm_num) (by norm_num)
    (by norm_num) (isAdmissibleLevel_sepLevel 2 2) (separatesDiagonal_sepLevel (by norm_num)) hy
  rw [hcard] at hi hf
  exact ⟨hcard, hi, hf⟩

end HJO.Mellit
