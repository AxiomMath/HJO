/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ColouringStepCounts

/-! # The colouring, read off one integer per column

A colouring is defined by two rank inequalities per step, and the usual arguments about it are
carried out by comparing ranks. This file replaces that by a single integer per
column: the **level index** `I_x(η)`, the largest ordinate `i` with `rk̂(x, i) < η`. It is the
ordinate at which the level line crosses the vertical lattice line `x`, rounded down, and it
depends on `η` and `x` alone — not on the path.

Against it the whole of `HJO.Mellit.colouring` collapses to two inequalities between natural
numbers. Writing `m_x := ŷ_x` for the height of the path at `x`:

* the north step `(x, i)` is crossed exactly when `i = I_x` and `m_x ≤ i < m_{x+1}`;
* the east step at `x`, which is the point `(x, m_{x+1})`, is crossed exactly when
  `I_x < m_{x+1} ≤ I_{x+1}`.

So a colouring is a statement about the two sequences `m` and `I`, and nothing else. In particular
**the crossed north step in a column is determined by the column** — its ordinate is `I_x`,
independent of the path — and **the crossed east step carries the height `m_{x+1}` outright**.

## Main results

* `HJO.Mellit.levelIndex` — `I_x(η)`.
* `HJO.Mellit.lt_cast_pointRank_iff` and `HJO.Mellit.cast_pointRank_lt_iff` — the level index
  decides both rank comparisons, the second using that an admissible level is no rank.
* `HJO.Mellit.mem_colouringNorth_iff`, `HJO.Mellit.mem_colouringEast_iff` — the two displays above.
* `HJO.Mellit.colouringNorth_column_iff` and `HJO.Mellit.colouringEast_column_iff` — the two
  conditions as predicates on the column alone.
* `HJO.Mellit.levelIndex_of_isolating` — lowering the level past one lattice point leaves every
  other column's index alone, so the colouring can move only in that point's column.

## Implementation notes

`I_x(η) = ⌊(η + ((aN+1)Nb - 1)x) / ((aN+1)Na)⌋`, obtained by solving
`rk̂(x, i) = (aN+1)Na·i - ((aN+1)Nb - 1)x < η` for `i`. The strict comparison
`η < rk̂(x, i)` is equivalent to `I_x < i` with no hypothesis at all beyond `0 < a` and `0 < N`
(which make the coefficient positive); the other comparison `rk̂(x, i) < η` needs `η` to be no rank,
which is admissibility.

## References

Built on `HJO.Mellit.colouring`, `HJO.Mellit.eastSteps`, `HJO.Paths.northSteps`,
`HJO.ParkingFunctions.abovePointRank`, `HJO.Paths.attackWindow`, `HJO.Mellit.IsAdmissibleLevel`,
`HJO.Mellit.card_colouringNorth_eq_card_colouringEast` and `HJO.Mellit.colouringComponent`. -/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The level index -/

/-- **The level index `I_x(η)`**: the largest ordinate `i` with `rk̂(x, i) < η`, that is the floor
of the ordinate at which the level line meets the vertical lattice line through `x`.

It reads the level and the column and *not* the path, which is what makes
`HJO.Mellit.mem_colouringNorth_iff` say that the crossed north step of a column is the same point
for every path that has one there. -/
def levelIndex (a b N : ℕ) (η : ℚ) (x : ℕ) : ℤ :=
  ⌊(η + ((((a * N + 1) * N * b : ℕ) : ℚ) - 1) * x) / (((a * N + 1) * N * a : ℕ) : ℚ)⌋

/-- The above-diagonal rank written out over `ℚ`: `rk̂(x, i) = (aN+1)Na·i - ((aN+1)Nb - 1)x`. -/
theorem cast_pointRank_eq (a b N x i : ℕ) :
    ((pointRank a b N (x, i) : ℤ) : ℚ) =
      (((a * N + 1) * N * a : ℕ) : ℚ) * i - ((((a * N + 1) * N * b : ℕ) : ℚ) - 1) * x := by
  simp only [pointRank, abovePointRank]
  push_cast
  ring

/-- **The level index decides the upper comparison**, with no hypothesis on `η`: the rank at
`(x, i)` exceeds `η` exactly when `i` exceeds the level index. -/
theorem lt_cast_pointRank_iff (ha : 0 < a) (hN : 0 < N) (η : ℚ) (x i : ℕ) :
    η < ((pointRank a b N (x, i) : ℤ) : ℚ) ↔ levelIndex a b N η x < (i : ℤ) := by
  have hpos : (0 : ℚ) < (((a * N + 1) * N * a : ℕ) : ℚ) := by
    have : 0 < (a * N + 1) * N * a := by positivity
    exact_mod_cast this
  rw [levelIndex, Int.floor_lt, div_lt_iff₀ hpos, cast_pointRank_eq]
  push_cast
  constructor <;> intro h <;> linarith

/-- **The level index decides the lower comparison.** Admissibility of the level is what turns the
negation of `HJO.Mellit.lt_cast_pointRank_iff` into a strict inequality: a rank equal to `η` would
satisfy neither side. -/
theorem cast_pointRank_lt_iff (ha : 0 < a) (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η)
    (x i : ℕ) :
    ((pointRank a b N (x, i) : ℤ) : ℚ) < η ↔ (i : ℤ) ≤ levelIndex a b N η x := by
  have hne := cast_pointRank_ne_of_isAdmissibleLevel hη a b N (x, i)
  have hiff := lt_cast_pointRank_iff (a := a) (b := b) (N := N) ha hN η x i
  constructor
  · intro h
    by_contra hcon
    exact absurd (hiff.2 (by omega)) (not_lt.2 h.le)
  · intro h
    rcases lt_trichotomy (((pointRank a b N (x, i) : ℤ) : ℚ)) η with h1 | h1 | h1
    · exact h1
    · exact absurd h1 hne
    · exact absurd (hiff.1 h1) (by omega)

/-- Read at the head of a north step: the level index bounds the whole column. -/
theorem lt_cast_pointRank_succ_iff (ha : 0 < a) (hN : 0 < N) (η : ℚ) (x i : ℕ) :
    η < ((pointRank a b N (x, i) : ℤ) : ℚ) + ((attackWindow a N : ℕ) : ℚ) ↔
      levelIndex a b N η x < (i : ℤ) + 1 := by
  have hsucc : ((pointRank a b N (x, i + 1) : ℤ) : ℚ) =
      ((pointRank a b N (x, i) : ℤ) : ℚ) + ((attackWindow a N : ℕ) : ℚ) := by
    rw [show pointRank a b N (x, i + 1) = pointRank a b N (x, i) + (attackWindow a N : ℤ) from
      abovePointRank_succ a b N x i]
    push_cast
    ring
  rw [← hsucc, lt_cast_pointRank_iff ha hN]
  push_cast
  exact Iff.rfl

/-! ### The colouring in terms of the level index -/

/-- **The crossed north steps.** The north step `(x, i)` of the path is crossed exactly when its
ordinate *is* the level index of its column. In particular the crossed north step of a column is
the same point for every path that has one there. -/
theorem mem_colouringNorth_iff (ha : 0 < a) (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η)
    (y : Heights a b N) (x i : ℕ) :
    (x, i) ∈ colouringNorth y η ↔
      x < a * N ∧ ht y x ≤ i ∧ i < ht y (x + 1) ∧ (i : ℤ) = levelIndex a b N η x := by
  rw [colouringNorth, Finset.mem_filter, mem_northSteps_iff]
  simp only [cast_pointRank_lt_iff ha hN hη, lt_cast_pointRank_succ_iff ha hN]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨h1, h2, h3, by omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, h3⟩, by omega, by omega⟩

/-- **The crossed east steps.** The east step at column `x` is the point `(x, ŷ_{x+1})`, and it is
crossed exactly when `I_x < ŷ_{x+1} ≤ I_{x+1}`. So a crossed east step carries the height of the
path at `x + 1` outright. -/
theorem mem_colouringEast_iff (ha : 0 < a) (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η)
    (y : Heights a b N) (x i : ℕ) :
    (x, i) ∈ colouringEast y η ↔
      x < a * N ∧ i = ht y (x + 1) ∧ levelIndex a b N η x < (i : ℤ) ∧
        (i : ℤ) ≤ levelIndex a b N η (x + 1) := by
  rw [colouringEast, Finset.mem_filter, mem_eastSteps_iff]
  simp only [cast_pointRank_lt_iff ha hN hη, lt_cast_pointRank_iff ha hN]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, h4, h3⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2⟩, h4, h3⟩

/-- **A column carries a crossed north step exactly when its level index is one of the ordinates the
path climbs through there**, and then that step is `(x, I_x)`. -/
theorem colouringNorth_column_iff (ha : 0 < a) (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η)
    (y : Heights a b N) {x : ℕ} (hx : x < a * N) :
    (∃ i, (x, i) ∈ colouringNorth y η) ↔
      ((ht y x : ℤ) ≤ levelIndex a b N η x ∧ levelIndex a b N η x < (ht y (x + 1) : ℤ)) := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨-, h2, h3, h4⟩ := (mem_colouringNorth_iff ha hN hη y x i).1 hi
    omega
  · rintro ⟨h1, h2⟩
    have hnn : 0 ≤ levelIndex a b N η x := le_trans (Int.natCast_nonneg _) h1
    refine ⟨(levelIndex a b N η x).toNat, (mem_colouringNorth_iff ha hN hη y x _).2
      ⟨hx, ?_, ?_, ?_⟩⟩
    · omega
    · omega
    · omega

/-- **A column carries a crossed east step exactly when the path's height just right of it lies
strictly above this column's level index and weakly below the next one.** -/
theorem colouringEast_column_iff (ha : 0 < a) (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η)
    (y : Heights a b N) {x : ℕ} (hx : x < a * N) :
    (∃ i, (x, i) ∈ colouringEast y η) ↔
      (levelIndex a b N η x < (ht y (x + 1) : ℤ) ∧
        (ht y (x + 1) : ℤ) ≤ levelIndex a b N η (x + 1)) := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨-, h2, h3, h4⟩ := (mem_colouringEast_iff ha hN hη y x i).1 hi
    exact ⟨h2 ▸ h3, h2 ▸ h4⟩
  · rintro ⟨h1, h2⟩
    exact ⟨ht y (x + 1), (mem_colouringEast_iff ha hN hη y x _).2 ⟨hx, rfl, h1, h2⟩⟩

/-! ### Moving the level past one lattice point -/

/-- **Lowering the level past a lattice point leaves every other column's index alone.** The two
levels bracket the rank of `P` and no other rank of the rectangle, so a lattice point whose side of
the index changed would supply a second rank in the window. This is the statement that makes each
rule of the level recursion (Mellit's Theorem 4.2) a finite case analysis in the single column of
`P`: outside it the colouring cannot move at all. -/
theorem levelIndex_of_isolating (ha : 0 < a) (hN : 0 < N) {ηlo ηhi : ℚ}
    (hlo : IsAdmissibleLevel ηlo) (hhi : IsAdmissibleLevel ηhi) (hle : ηlo ≤ ηhi)
    {x i : ℕ} (hx : x ≤ a * N)
    (hiso : ∀ Q : ℕ × ℕ, Q.1 ≤ a * N → Q.2 ≤ b * N →
      ηlo < ((pointRank a b N Q : ℤ) : ℚ) → ((pointRank a b N Q : ℤ) : ℚ) < ηhi →
      pointRank a b N Q = pointRank a b N (x, i))
    {x' j : ℕ} (hx' : x' ≤ a * N) (hj : j ≤ b * N) (hne : (x', j) ≠ (x, i)) :
    ((j : ℤ) ≤ levelIndex a b N ηlo x' ↔ (j : ℤ) ≤ levelIndex a b N ηhi x') := by
  rw [← cast_pointRank_lt_iff ha hN hlo, ← cast_pointRank_lt_iff ha hN hhi]
  refine ⟨fun h => lt_of_lt_of_le h hle, fun h => ?_⟩
  by_contra hcon
  have hgt : ηlo < ((pointRank a b N (x', j) : ℤ) : ℚ) :=
    lt_of_le_of_ne (not_lt.1 hcon)
      (Ne.symm (cast_pointRank_ne_of_isAdmissibleLevel hlo a b N (x', j)))
  exact hne (pointRank_inj_of_le ha hN hx' hx (hiso (x', j) hx' hj hgt h))

end HJO.Mellit
