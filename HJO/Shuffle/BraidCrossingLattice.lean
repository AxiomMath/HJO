/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidColStepInsert
public import HJO.Shuffle.BraidPositionWindow

/-! # Every crossing of a component is realised by a lattice point of the rectangle

`HJO.Mellit.fract_crossingAbscissa_eq_levelPosition` turns the position of a crossing into a
normalised rank *provided* the crossing sits inside the column of a crossed east step. That covers
the top crossing of a component and nothing else, and the intermediate crossings — the ones the
iterates of `HJO.Braid.nextCrossing` walk through — were left with no named column. This file names
it.

## The column is the floor of the abscissa

For **any** index `n` and **any** pair of naturals `x + yy = n`,

```
crossingAbscissa η n − x = levelPosition η (rk̂ (x, yy)),
```

which is `HJO.Mellit.crossingAbscissa_sub_natCast` — pure algebra, no hypothesis on the position of
the crossing at all. Taking `x = ⌊crossingAbscissa η n⌋` makes the left side the fractional part, so
the candidate point is forced: it is `(⌊A_n⌋, n − ⌊A_n⌋)` and there is nothing to choose. The work
is entirely in the four bounds that make it a point of the rectangle above the level, and those are
what `HJO.Mellit.exists_pointRank_of_le_componentTopIndex` supplies.

**This is weaker than east-step membership, and the difference is the whole point.** The realising
point is *not* in general a crossed east step. At `a = 2`, `b = 5`, `N = 1` and `η = 9/2` the
crossing of index `4` has abscissa `39/40` and hence position `39/40`, which exceeds
`1 − θ = 7/10`; by `HJO.Mellit.fract_crossingAbscissa_lt_one_sub_sweepTheta` no crossed east step of
*any* path at that level has coordinate sum `4`, which is
`HJO.Mellit.sum_ne_of_mem_colouringEast_example`. The reason is visible in the abscissa: it passes a
vertical lattice line between `n = 4` and `n = 5`, so the crossing of index `4`
lies in the column of `(0, 4)` while `rk̂ (1, 4) = 10 > η` leaves `(0, 4)` short of the east-step
condition. The *rank* reading survives that; the east-step reading does not, and that is why this
file cannot be got from `HJO.Mellit.fract_crossingAbscissa_eq_levelPosition`.

On the above-diagonal path with heights `(0, 5, 5)` that index really is an interior crossing of a
component — its crossed north step is `(0, 0)`, its crossed east step is `(1, 5)`, and the component
carries the six crossings `n = 1, …, 6`. That last sentence is a hand computation and is not checked
here; the three declarations at the end of this file are.

## The ordinate bound needs the level line to stay below the path

The abscissa bound is cheap: the crossing is weakly right of the component's left end, which is a
column, and strictly left of one more than the column of its crossed east step.

The ordinate bound is not. `⌊A_n⌋ = x` gives only `yy − 1 < s(x+1) + η/(aM)`, one short of what is
wanted, and closing the gap needs to know that the level line runs *below the path* across the whole
component — `HJO.Mellit.levelIndex_lt_ht_of_mem_component`. That is proved here by a descent from
the component's east end: a column strictly inside the component carries no crossed north step, so
the level line there is either below the path or weakly above `ŷ_{c+1}`; the second alternative at
the rightmost column contradicts the defining inequality of the crossed east step, and at any other
column it contradicts the same statement one column to the right, the level index being monotone.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The crossing abscissa minus a column is a normalised rank -/

/-- **The algebraic heart: for any splitting `n = x + yy` of an index into two naturals, the
crossing abscissa of `n` less `x` is the normalised rank of `(x, yy)`.**

No hypothesis places the crossing anywhere: both sides are `θ(yy − s x − η/(aM))` after clearing
denominators, the right side by `HJO.Mellit.abovePointRank_sub_level`. Everything geometric in this
file is the question of *which* splitting makes the left side the fractional part, and the answer is
forced to be `x = ⌊crossingAbscissa η n⌋`. -/
theorem crossingAbscissa_sub_natCast (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) (x yy : ℕ) :
    crossingAbscissa a b N η ((x : ℤ) + (yy : ℤ)) - (x : ℚ)
      = levelPosition a b N η ((pointRank a b N (x, yy) : ℤ) : ℚ) := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hM' : ((a : ℚ) * ((a : ℚ) * N + 1) * N) ≠ 0 := hM.ne'
  have hs := one_add_sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  have hs' : (1 + sweepSlope a b N) ≠ 0 := hs.ne'
  have hkey : ((a : ℚ) * ((a : ℚ) * N + 1) * N) *
      ((yy : ℚ) - (sweepSlope a b N * (x : ℚ) + levelIntercept a N η))
      = ((pointRank a b N (x, yy) : ℤ) : ℚ) - η := by
    rw [cast_pointRank_eq', abovePointRank_sub_level (b := b) ha.ne' hN.ne']
  rw [levelPosition, ← hkey, crossingAbscissa, sweepTheta]
  push_cast
  field_simp
  ring

/-! ### Inside a component the level line runs below the path -/

/-- **A column strictly inside a component carries no crossed north step.** The columns of the
crossed north steps are listed strictly increasingly, and the `i`-th crossed east step is strictly
left of the `(i+1)`-st crossed north step — `HJO.Mellit.eastCol_lt_northCol_succ` — so a column
strictly right of the `i`-th north column and weakly left of the `i`-th east column is neither. -/
theorem fst_ne_of_mem_colouringNorth_of_mem_component (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {η : ℚ} (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {i : ℕ} (hi : i < #(colouringNorth y η)) {c : ℕ}
    (hLc : (colStep (colouringNorth y η) i).1 < c)
    (hcW : c ≤ (colStep (colouringEast y η) i).1) {P : ℕ × ℕ} (hP : P ∈ colouringNorth y η) :
    P.1 ≠ c := by
  intro hPc
  obtain ⟨j, hj, hje⟩ := exists_colStep hP
  rcases le_or_gt j i with hji | hij
  · have hle := colStep_fst_le (columnInjective_colouringNorth ha hN hη y) hi hji
    rw [hje, hPc] at hle
    omega
  · have hstep := eastCol_lt_northCol_succ ha hb hN hη hηa hy (i := i) (by omega)
    have hle := colStep_fst_le (columnInjective_colouringNorth ha hN hη y) hj (by omega : i + 1 ≤ j)
    rw [hje, hPc] at hle
    omega

/-- **Inside a component the level line runs below the path.** For every column `c` strictly right
of the `i`-th crossed north step and weakly left of the `i`-th crossed east step, the level index of
`c` is strictly below `ŷ_c` — the level line crosses the vertical lattice line through `c` below
every north step of the path in that column.

This is the fact the ordinate bound of
`HJO.Mellit.exists_pointRank_of_le_componentTopIndex` is missing, and it is proved by descent from
the east end. Such a `c` carries no crossed north step, so `(c, I_c(η))` is not a north step of the
path: either `I_c(η) < ŷ_c`, which is the claim, or `ŷ_{c+1} ≤ I_c(η)`. The second alternative is
impossible at `c = x(w_i)`, where the crossed east step gives `I_c(η) < y(w_i) = ŷ_{c+1}`, and at
any smaller `c` it contradicts the claim one column to the right, since
`I_c(η) ≤ I_{c+1}(η) < ŷ_{c+1}`. -/
theorem levelIndex_lt_ht_of_mem_component (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {i : ℕ} (hi : i < #(colouringNorth y η)) {c : ℕ}
    (hLc : (colStep (colouringNorth y η) i).1 < c)
    (hcW : c ≤ (colStep (colouringEast y η) i).1) :
    levelIndex a b N η c < (ht y c : ℤ) := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηa
  have hk : #(colouringNorth y η) = #(colouringEast y η) :=
    card_colouringNorth_eq_card_colouringEast hb hN hη hηa hy
  have hiE : i < #(colouringEast y η) := hk ▸ hi
  obtain ⟨hW1, hW2, hW3, -⟩ := mem_colouringEast_spec ha hN hη y (colStep_mem hiE)
  -- the dichotomy at a column strictly inside the component
  have hdich : ∀ d : ℕ, (colStep (colouringNorth y η) i).1 < d →
      d ≤ (colStep (colouringEast y η) i).1 →
      levelIndex a b N η d < (ht y d : ℤ) ∨ (ht y (d + 1) : ℤ) ≤ levelIndex a b N η d := by
    intro d hLd hdW
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hnn : 0 ≤ levelIndex a b N η d := levelIndex_nonneg (b := b) ha hb hN hηpos d
    have hmem : (d, (levelIndex a b N η d).toNat) ∈ colouringNorth y η := by
      refine (mem_colouringNorth_iff ha hN hη y d _).2 ⟨by omega, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
    exact fst_ne_of_mem_colouringNorth_of_mem_component ha hb hN hη hηa hy hi hLd hdW hmem rfl
  -- descent from the east end
  have key : ∀ d e : ℕ, e + d = (colStep (colouringEast y η) i).1 →
      (colStep (colouringNorth y η) i).1 < e → levelIndex a b N η e < (ht y e : ℤ) := by
    intro d
    induction d with
    | zero =>
      intro e he hLe
      rcases hdich e hLe (by omega) with h | h
      · exact h
      · rw [show e = (colStep (colouringEast y η) i).1 by omega] at h
        omega
    | succ d ih =>
      intro e he hLe
      rcases hdich e hLe (by omega) with h | h
      · exact h
      · have hnext := ih (e + 1) (by omega) (by omega)
        have hmono := levelIndex_le_levelIndex (a := a) (b := b) (N := N) ha hb hN η
          (show e ≤ e + 1 by omega)
        omega
  exact key ((colStep (colouringEast y η) i).1 - c) c (by omega) hLc

/-! ### The realising lattice point -/

/-- **Every crossing of a component is realised by a lattice point of the rectangle.** For an index
`n` between the two endpoint indices of the `i`-th component there are naturals `x + yy = n` with

* `x < aN`, so the point lies in a column of the rectangle;
* `1 ≤ yy ≤ ŷ_{x+1} ≤ bN`, so it lies in a row of the rectangle, weakly below the path;
* `η < rk̂ (x, yy)`, so it lies above the level; and
* `fract (crossingAbscissa η n) = levelPosition η (rk̂ (x, yy))`.

The point is `(⌊crossingAbscissa η n⌋, n − ⌊crossingAbscissa η n⌋)`; the identity is
`HJO.Mellit.crossingAbscissa_sub_natCast` and the four bounds are the content. This is exactly the
input that `HJO.Mellit.lt_levelPosition_of_ne` and `HJO.Mellit.sameSide_levelDropShift_of_ne` take,
with the ordinate bound in the sharper form `yy ≤ ŷ_{x+1}` — sharper because it is what rules out
the excluded point `(X, Y + 1)` at a type-`A` event, where `ŷ_{X+1} ≤ Y`. -/
theorem exists_pointRank_of_le_componentTopIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {i : ℕ} (hi : i < #(colouringNorth y η)) {n : ℤ}
    (hn1 : componentBotIndex a b N y η i ≤ n) (hn2 : n ≤ componentTopIndex a b N y η i) :
    ∃ x yy : ℕ, (x : ℤ) + (yy : ℤ) = n ∧ x < a * N ∧ 0 < yy ∧ yy ≤ ht y (x + 1) ∧
      η < ((pointRank a b N (x, yy) : ℤ) : ℚ) ∧
      Int.fract (crossingAbscissa a b N η n)
        = levelPosition a b N η ((pointRank a b N (x, yy) : ℤ) : ℚ) := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηa
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hθ := (sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN).1
  have hs := one_add_sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  have hk : #(colouringNorth y η) = #(colouringEast y η) :=
    card_colouringNorth_eq_card_colouringEast hb hN hη hηa hy
  have hiE : i < #(colouringEast y η) := hk ▸ hi
  obtain ⟨hW1, hW2, -, -⟩ := mem_colouringEast_spec ha hN hη y (colStep_mem hiE)
  obtain ⟨hR1, hR2⟩ := eastCol_lt_componentRight ha hb hN hη hηpos hiE
  have hAeq : (1 + sweepSlope a b N) * crossingAbscissa a b N η n + levelIntercept a N η
      = (n : ℚ) :=
    one_add_sweepSlope_mul_crossingAbscissa hs.ne' η n
  -- the two ends bracket the crossing
  have hCL : componentLeft y η i = (((colStep (colouringNorth y η) i).1 : ℕ) : ℚ) := rfl
  have hLA : (((colStep (colouringNorth y η) i).1 : ℕ) : ℚ) ≤ crossingAbscissa a b N η n := by
    rw [← hCL]; exact componentLeft_le_crossingAbscissa hs y η i hn1
  have hAW : crossingAbscissa a b N η n < (((colStep (colouringEast y η) i).1 : ℕ) : ℚ) + 1 :=
    lt_of_le_of_lt (crossingAbscissa_le_componentRight hs y η i hn2) hR2
  -- the column of the crossing is the floor of its abscissa
  have hA0 : (0 : ℚ) ≤ crossingAbscissa a b N η n := le_trans (Nat.cast_nonneg _) hLA
  have hfl0 : (0 : ℤ) ≤ ⌊crossingAbscissa a b N η n⌋ := Int.le_floor.2 (by exact_mod_cast hA0)
  obtain ⟨x, hxZ⟩ : ∃ x : ℕ, ((x : ℤ)) = ⌊crossingAbscissa a b N η n⌋ :=
    ⟨(⌊crossingAbscissa a b N η n⌋).toNat, Int.toNat_of_nonneg hfl0⟩
  have hxQ : ((x : ℕ) : ℚ) = ((⌊crossingAbscissa a b N η n⌋ : ℤ) : ℚ) := by
    rw [← hxZ]; push_cast; ring
  have hxle : ((x : ℕ) : ℚ) ≤ crossingAbscissa a b N η n := by rw [hxQ]; exact Int.floor_le _
  have hxlt : crossingAbscissa a b N η n < ((x : ℕ) : ℚ) + 1 := by
    rw [hxQ]; exact Int.lt_floor_add_one _
  -- no crossing sits on a vertical lattice line, so the floor is strict
  have hxlt' : ((x : ℕ) : ℚ) < crossingAbscissa a b N η n := by
    refine lt_of_le_of_ne hxle fun hcon => ?_
    refine levelOrd_ne_intCast (b := b) ha hb hN hη hηpos x (n - (x : ℤ)) ?_
    rw [← hcon] at hAeq
    push_cast
    linarith
  -- the abscissa bound
  have hxW : x ≤ (colStep (colouringEast y η) i).1 := by
    have h : ((x : ℕ) : ℚ) < ((((colStep (colouringEast y η) i).1 + 1 : ℕ)) : ℚ) := by
      push_cast; linarith [hxle.trans_lt hAW]
    exact Nat.lt_succ_iff.1 (by exact_mod_cast h)
  have hLx : (colStep (colouringNorth y η) i).1 ≤ x := by
    have h : ((((colStep (colouringNorth y η) i).1 : ℕ)) : ℚ) < ((x : ℕ) : ℚ) + 1 :=
      hLA.trans_lt hxlt
    have h' : (((colStep (colouringNorth y η) i).1 : ℕ) : ℚ) < (((x + 1 : ℕ)) : ℚ) := by
      push_cast; linarith
    exact Nat.lt_succ_iff.1 (by exact_mod_cast h')
  -- the ordinate is positive
  have hlp := levelOrd_pos (b := b) ha hb hN hηpos x
  have hprod : 0 < (1 + sweepSlope a b N) * (crossingAbscissa a b N η n - ((x : ℕ) : ℚ)) :=
    mul_pos hs (by linarith)
  have hnxZ : ((x : ℤ)) < n := by
    have hQ : ((x : ℕ) : ℚ) < (n : ℚ) := by nlinarith
    exact_mod_cast hQ
  obtain ⟨yy, hyyZ⟩ : ∃ yy : ℕ, ((yy : ℤ)) = n - (x : ℤ) :=
    ⟨(n - (x : ℤ)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hsum : ((x : ℤ)) + ((yy : ℤ)) = n := by omega
  have hyyQ : ((yy : ℕ) : ℚ) = (n : ℚ) - ((x : ℕ) : ℚ) := by
    have := hyyZ
    have h : (((yy : ℤ)) : ℚ) = ((n - (x : ℤ) : ℤ) : ℚ) := by exact_mod_cast this
    push_cast at h
    linarith
  -- the position of the crossing is the normalised rank of `(x, yy)`
  have hid : crossingAbscissa a b N η n - ((x : ℕ) : ℚ)
      = levelPosition a b N η ((pointRank a b N (x, yy) : ℤ) : ℚ) := by
    have h := crossingAbscissa_sub_natCast (a := a) (b := b) (N := N) ha hb hN η x yy
    rwa [hsum] at h
  -- the rank is above the level
  have hrk : η < ((pointRank a b N (x, yy) : ℤ) : ℚ) := by
    have hp : 0 < levelPosition a b N η ((pointRank a b N (x, yy) : ℤ) : ℚ) := by
      rw [← hid]; linarith
    by_contra hc
    have h1 := levelPosition_le_levelPosition (a := a) (b := b) (N := N) ha hb hN η (not_lt.1 hc)
    have h2 : levelPosition a b N η η = 0 := by rw [levelPosition]; simp
    linarith
  -- the ordinate bound
  have hfloor : ((yy : ℤ) - 1) ≤ levelIndex a b N η (x + 1) := by
    rw [levelIndex_eq_floor ha hN]
    refine Int.le_floor.2 ?_
    push_cast
    rw [hyyQ]
    linarith [mul_lt_mul_of_pos_left hxlt hs]
  have hyyle : yy ≤ ht y (x + 1) := by
    rcases eq_or_lt_of_le hxW with hxeq | hxlt2
    · have htop := componentTopIndex_eq ha hb hN hη hηpos hiE
      rw [htop, hW2] at hn2
      rw [hxeq]
      omega
    · have hbelow := levelIndex_lt_ht_of_mem_component ha hb hN hη hηa hy hi
        (c := x + 1) (by omega) (by omega)
      omega
  refine ⟨x, yy, hsum, lt_of_le_of_lt hxW hW1, ?_, hyyle, hrk, ?_⟩
  · omega
  · rw [Int.fract, ← hxQ, hid]

/-! ### The realising point need not be a crossed east step -/

/-- At `a = 2`, `b = 5`, `N = 1` and `η = 9/2` the crossing of index `4` has abscissa `39/40`. -/
theorem crossingAbscissa_example : crossingAbscissa 2 5 1 (9 / 2) 4 = 39 / 40 := by
  rw [crossingAbscissa, sweepSlope, levelIntercept]
  norm_num

/-- That abscissa is its own fractional part, so the position of the crossing is `39/40`. -/
theorem fract_crossingAbscissa_example :
    Int.fract (crossingAbscissa 2 5 1 (9 / 2) 4) = 39 / 40 := by
  rw [crossingAbscissa_example, Int.fract_eq_self.2 ⟨by norm_num, by norm_num⟩]

/-- **The realising point of an interior crossing need not be a crossed east step.** At `a = 2`,
`b = 5`, `N = 1` and `η = 9/2` the position of the crossing of index `4` is `39/40`, above
`1 − θ = 7/10`, so by `HJO.Mellit.fract_crossingAbscissa_lt_one_sub_sweepTheta'` no crossed east
step of any path at that level has coordinate sum `4`.

So the hypothesis of `HJO.Mellit.fract_crossingAbscissa_eq_levelPosition` is unavailable at that
index however the path is chosen, while
`HJO.Mellit.exists_pointRank_of_le_componentTopIndex` still produces `(0, 4)`: a lattice point of
the rectangle above the level whose normalised rank is the position. The two readings of a crossing
are genuinely different, and it is the weaker one that
`HJO.Mellit.lt_levelPosition_of_ne` and `HJO.Mellit.sameSide_levelDropShift_of_ne` need. -/
theorem sum_ne_of_mem_colouringEast_example (y : Heights 2 5 1) {P : ℕ × ℕ}
    (hP : P ∈ colouringEast y (9 / 2)) : (P.1 : ℤ) + (P.2 : ℤ) ≠ 4 := by
  intro hsum
  obtain ⟨h1, h2⟩ := pointRank_lt_of_mem_colouringEast hP
  have hlt := fract_crossingAbscissa_lt_one_sub_sweepTheta' (a := 2) (b := 5) (N := 1)
    (by norm_num) (by norm_num) (by norm_num) (9 / 2) P h2 h1
  rw [hsum, fract_crossingAbscissa_example, sweepTheta, sweepSlope] at hlt
  norm_num at hlt

end HJO.Mellit

end
