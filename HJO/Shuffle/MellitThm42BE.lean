/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ColouringTrace
public import HJO.Shuffle.ColouringLevelIndex
public import HJO.Shuffle.ColouringWidth
public import HJO.Shuffle.SweepEventCounts
public import HJO.Shuffle.SweepTruncate
public meta import HJO.Attr

/-! # Mellit's Theorem 4.2, rule BE: the one recursion with two predecessors

Three of the four rules of Mellit's Theorem 4.2 relate the invariant of a colouring below a level to
the invariant of *one* colouring above it. This file carries the fourth,
`HJO.Mellit.dsc_eq_dminus_add_smul`: at a lattice point `P` that is the foot of a north step of one
path and lies strictly below another, the colouring below the level has two predecessors above it,
and

`D_{ηlo, c_{ηlo}(P̂)} = d_- D_{ηhi, c_{ηhi}(P̂)} + u D_{ηhi, c_{ηhi}(Q̂)}`.

## The shape of the proof

`HJO.Mellit.partialSweepWord_eq_sweepOperator_mul` already says that lowering the level past `P`
appends the single factor `Φ_{P̂}(P)` to the partial sweep word. The content of the rule is
therefore the *grouping* of the traces, and the remark under `HJO.Mellit.dsc_lo_eq_dplus_dsc_hi`
says what one may not do: the grouping cannot come from a bijection of paths, since the fibre above
the level is in general the larger one. Here it is obtained instead as follows.

The level index `I_x(η)` of `HJO.Mellit.levelIndex` turns a colouring into two inequalities per
column between the path's heights and one integer read off the level. Against it:

* `HJO.Mellit.lt_ht_succ_iff_of_colouring_eq` — **the colouring decides, column by column, whether
  the level line passes under the path.** This is the fact no single column of the colouring
  records, and it is what keeps a second path of the fibre from having `P` above its own path, where
  no event happens at all. The proof is an induction along the columns: the crossed north step at
  `x` and the crossed east step at `x` are the two boundary indicators of the predicate, and the
  colouring records both.
* `HJO.Mellit.Isolated.colouring_hi_eq_of_eventType_B` and
  `HJO.Mellit.Isolated.colouring_hi_eq_of_eventType_E` — raising the level past `P` adds the two
  points `P` and `(x-1, j)` to the colouring at an event of type `B`, and changes nothing at an
  event of type `E`. Every other column is untouched because
  `HJO.Mellit.levelIndex_of_isolating` leaves every comparison but the one at `P` alone.
* `HJO.Mellit.fibre_split` — every above-diagonal path with the same colouring as the type-`B`
  witness below the level has event type `B` or `E` at `P`: types `C` and `A` would put the crossed
  north step `(x, j-1)` into the colouring, type `D` the crossed east step `P`, and the type-`B`
  witness has neither.
* `HJO.Mellit.mem_fibre_of_colouring_hi_eq_B` — and, in the other direction, the fibre *above* the
  level of the type-`B` colouring is no larger: the gained point `(x-1, j)` is the east step
  arriving at `P` and pins the path's height at `x` down to `j`. This is why rule `BE` needs no
  correction where the other three rules do.

The two classes are then summed separately. `HJO.Mellit.sum_partialSweepWord_hi` is the regrouping:
dropping `P`'s own triple from a trace is a bijection from the traces below the level of one event
type onto the traces above the level of the corresponding colouring, and
`HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq` makes the summand depend on the trace alone.

## Main results

* `HJO.Mellit.dsc_eq_dminus_add_smul`.
* `HJO.Mellit.dsc_eq_dminus_add_smul_example` — the rule at an explicit instance, showing that the
  hypotheses are jointly satisfiable.

## Implementation notes

### The isolation hypothesis is the one the level supplier provides

A natural statement of rule `BE` lists `a y(P) ≥ b x(P)` among its hypotheses on `P` and then asks
that `rk̂(P)` be the only rank taken "on such lattice points" between the levels, which reads as
quantifying over the points weakly above the diagonal. The hypothesis carried here quantifies over
every lattice point of the rectangle, with no diagonal condition. That is the form
`HJO.Mellit.exists_isolating_isAdmissibleLevel` supplies — its own hypothesis list has no diagonal
condition — and the form the sibling `HJO.Mellit.partialSweepWord_eq_sweepOperator_mul` already
carries, so the two compose. It is also needed: the proof compares the level against `(x, j-1)` and
`(x+1, j)`, and neither need lie above the diagonal.

The diagonal condition itself is not assumed, being implied by `P ∈ Sw(P̂)`; nor is `P ∈ Sw(Q̂)`,
which follows from `ev_{Q̂}(P) = E`.

### The nondegeneracy hypotheses

`0 < a`, `0 < b` and `0 < N` are carried as explicit hypotheses; they hold in the
standing range `1 < a < b` with `N ≥ 1`, so nothing is lost. The rank is injective on the
rectangle only for `0 < a` and `0 < N`; and `0 < b` is what makes an east step lower the rank, which
is what separates the column to the left of `P` from `P` itself — without it the two gained points
of the type-`B` colouring could not be told apart.

## References

A. Mellit, *Toric braids
and `(m, n)`-parking functions*, Theorem 4.2, rules B) and E).
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The two halves of a colouring are read off the colouring -/

/-- The crossed north steps are the members of the colouring whose ordinate *is* the level index of
their column, and the crossed east steps are the rest. Neither side of the description mentions the
path, so two paths with the same colouring have the same two halves. -/
theorem colouringNorth_eq_filter (ha : 0 < a) (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η)
    (y : Heights a b N) :
    colouringNorth y η = {p ∈ colouring y η | (p.2 : ℤ) = levelIndex a b N η p.1} := by
  ext p
  obtain ⟨x, i⟩ := p
  simp only [Finset.mem_filter, colouring_eq_union, Finset.mem_union]
  refine ⟨fun h => ⟨Or.inl h, ((mem_colouringNorth_iff ha hN hη y x i).1 h).2.2.2⟩, ?_⟩
  rintro ⟨h | h, h2⟩
  · exact h
  · exact absurd ((mem_colouringEast_iff ha hN hη y x i).1 h).2.2.1 (by omega)

/-- The crossed east steps are the members of the colouring whose ordinate is *not* the level index
of their column. -/
theorem colouringEast_eq_filter (ha : 0 < a) (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η)
    (y : Heights a b N) :
    colouringEast y η = {p ∈ colouring y η | (p.2 : ℤ) ≠ levelIndex a b N η p.1} := by
  ext p
  obtain ⟨x, i⟩ := p
  simp only [Finset.mem_filter, colouring_eq_union, Finset.mem_union]
  refine ⟨fun h => ⟨Or.inr h, ?_⟩, ?_⟩
  · have := ((mem_colouringEast_iff ha hN hη y x i).1 h).2.2.1
    omega
  · rintro ⟨h | h, h2⟩
    · exact absurd ((mem_colouringNorth_iff ha hN hη y x i).1 h).2.2.2 h2
    · exact h

/-- Two paths with the same colouring have the same crossed north steps. -/
theorem colouringNorth_eq_of_colouring_eq (ha : 0 < a) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) {y₁ y₂ : Heights a b N} (h : colouring y₁ η = colouring y₂ η) :
    colouringNorth y₁ η = colouringNorth y₂ η := by
  rw [colouringNorth_eq_filter ha hN hη, colouringNorth_eq_filter ha hN hη, h]

/-- Two paths with the same colouring have the same crossed east steps. -/
theorem colouringEast_eq_of_colouring_eq (ha : 0 < a) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) {y₁ y₂ : Heights a b N} (h : colouring y₁ η = colouring y₂ η) :
    colouringEast y₁ η = colouringEast y₂ η := by
  rw [colouringEast_eq_filter ha hN hη, colouringEast_eq_filter ha hN hη, h]

/-! ### Monotonicity of the level index -/

/-- The level index rises with the level. -/
theorem levelIndex_mono_level (a b N x : ℕ) {η η' : ℚ} (h : η ≤ η') :
    levelIndex a b N η x ≤ levelIndex a b N η' x := by
  exact Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) (by positivity))

/-- The level index rises with the column, on a rectangle with a row and a column. -/
theorem levelIndex_le_succ (hb : 0 < b) (hN : 0 < N) (a : ℕ) (η : ℚ) (x : ℕ) :
    levelIndex a b N η x ≤ levelIndex a b N η (x + 1) := by
  refine Int.floor_le_floor ?_
  have hW : (1 : ℚ) ≤ (((a * N + 1) * N * b : ℕ) : ℚ) := by
    have : 1 ≤ (a * N + 1) * N * b := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hx : (0 : ℚ) ≤ (x : ℚ) := Nat.cast_nonneg _
  push_cast at hW ⊢
  nlinarith

/-- The level index is monotone in the column. -/
theorem levelIndex_mono_col (hb : 0 < b) (hN : 0 < N) (a : ℕ) (η : ℚ) {x x' : ℕ} (h : x ≤ x') :
    levelIndex a b N η x ≤ levelIndex a b N η x' := by
  induction x', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact ih.trans (levelIndex_le_succ hb hN a η n)

/-! ### The colouring decides whether the level line passes under the path -/

/-- **The colouring decides, column by column, whether the level line passes under the path.**
Writing `I_x` for the level index and `ŷ_{x+1}` for the height of the path just right of `x`, the
proposition `I_x < ŷ_{x+1}` — the line at column `x` is strictly below the top of that column, so
the line is inside the figure there — is a function of the colouring alone.

This is the one fact about a colouring that no single column of it records, and the reason the four
rules of Mellit's Theorem 4.2 can be read off a witnessing path: it is what forbids a second path
with the same colouring from having the swept point `P` above its own path, where no event of the
sweep happens at all.

The induction is the bookkeeping of the components of the colouring. Write `h_x` for `I_x < ŷ_x`. A
crossed north step at `x` says `¬h_x ∧ (I_x < ŷ_{x+1})` and a crossed east step at `x` says
`(I_x < ŷ_{x+1}) ∧ ¬h_{x+1}`; since `I` and `ŷ` are both monotone, `h_x` implies `I_x < ŷ_{x+1}` and
`h_{x+1}` implies `I_{x+1} < ŷ_{x+2}`. So `I_x < ŷ_{x+1}` is `h_x` or a north crossing, and
`h_{x+1}` is `(I_x < ŷ_{x+1})` and no east crossing — and the crossings are recorded. The base is
`ŷ_0 = 0`, which every above-diagonal path shares. -/
theorem lt_ht_succ_iff_of_colouring_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) {y₁ y₂ : Heights a b N} (hy₁ : IsAboveDiagonal y₁)
    (hy₂ : IsAboveDiagonal y₂) (hcol : colouring y₁ η = colouring y₂ η) :
    ∀ x < a * N, (levelIndex a b N η x < (ht y₁ (x + 1) : ℤ) ↔
      levelIndex a b N η x < (ht y₂ (x + 1) : ℤ)) := by
  have hNeq := colouringNorth_eq_of_colouring_eq ha hN hη hcol
  have hEeq := colouringEast_eq_of_colouring_eq ha hN hη hcol
  have hn : ∀ x, x < a * N → (((ht y₁ x : ℤ) ≤ levelIndex a b N η x ∧
        levelIndex a b N η x < (ht y₁ (x + 1) : ℤ)) ↔
      ((ht y₂ x : ℤ) ≤ levelIndex a b N η x ∧
        levelIndex a b N η x < (ht y₂ (x + 1) : ℤ))) := fun x hx => by
    rw [← colouringNorth_column_iff ha hN hη y₁ hx, ← colouringNorth_column_iff ha hN hη y₂ hx,
      hNeq]
  have he : ∀ x, x < a * N → ((levelIndex a b N η x < (ht y₁ (x + 1) : ℤ) ∧
        (ht y₁ (x + 1) : ℤ) ≤ levelIndex a b N η (x + 1)) ↔
      (levelIndex a b N η x < (ht y₂ (x + 1) : ℤ) ∧
        (ht y₂ (x + 1) : ℤ) ≤ levelIndex a b N η (x + 1))) := fun x hx => by
    rw [← colouringEast_column_iff ha hN hη y₁ hx, ← colouringEast_column_iff ha hN hη y₂ hx,
      hEeq]
  intro x
  induction x with
  | zero =>
    intro hx
    have h0 := hn 0 hx
    rw [hy₁.1, hy₂.1] at h0
    push_cast at h0
    constructor <;> intro hgt
    · rcases le_or_gt 0 (levelIndex a b N η 0) with hnn | hneg
      · exact (h0.1 ⟨hnn, hgt⟩).2
      · exact lt_of_lt_of_le hneg (Int.natCast_nonneg _)
    · rcases le_or_gt 0 (levelIndex a b N η 0) with hnn | hneg
      · exact (h0.2 ⟨hnn, hgt⟩).2
      · exact lt_of_lt_of_le hneg (Int.natCast_nonneg _)
  | succ x ih =>
    intro hx
    have hxlt : x < a * N := by omega
    have ihx := ih hxlt
    have hIle : levelIndex a b N η x ≤ levelIndex a b N η (x + 1) := levelIndex_le_succ hb hN a η x
    have hm₁ : ht y₁ (x + 1) ≤ ht y₁ (x + 1 + 1) := ht_mono hy₁.2.2.1 (Nat.le_succ _)
    have hm₂ : ht y₂ (x + 1) ≤ ht y₂ (x + 1 + 1) := ht_mono hy₂.2.2.1 (Nat.le_succ _)
    have hm₁' : (ht y₁ (x + 1) : ℤ) ≤ (ht y₁ (x + 1 + 1) : ℤ) := by exact_mod_cast hm₁
    have hm₂' : (ht y₂ (x + 1) : ℤ) ≤ (ht y₂ (x + 1 + 1) : ℤ) := by exact_mod_cast hm₂
    have hex := he x hxlt
    have hnx := hn (x + 1) hx
    -- the level line at column `x + 1` is below the top of column `x`
    have hstep : levelIndex a b N η (x + 1) < (ht y₁ (x + 1) : ℤ) ↔
        levelIndex a b N η (x + 1) < (ht y₂ (x + 1) : ℤ) := by
      constructor <;> intro hh
      · by_contra hcon
        exact absurd (hex.2 ⟨ihx.1 (lt_of_le_of_lt hIle hh), by omega⟩).2 (by omega)
      · by_contra hcon
        exact absurd (hex.1 ⟨ihx.2 (lt_of_le_of_lt hIle hh), by omega⟩).2 (by omega)
    constructor <;> intro hgt
    · rcases lt_or_ge (levelIndex a b N η (x + 1)) (ht y₁ (x + 1) : ℤ) with hh | hh
      · exact lt_of_lt_of_le (hstep.1 hh) hm₂'
      · exact (hnx.1 ⟨by omega, hgt⟩).2
    · rcases lt_or_ge (levelIndex a b N η (x + 1)) (ht y₂ (x + 1) : ℤ) with hh | hh
      · exact lt_of_lt_of_le (hstep.2 hh) hm₁'
      · exact (hnx.2 ⟨by omega, hgt⟩).2

/-! ### Strict rank comparisons -/

/-- Climbing a column strictly raises the rank. -/
theorem pointRank_lt_pointRank_snd (ha : 0 < a) (hN : 0 < N) (b x : ℕ) {i j : ℕ} (hij : i < j) :
    pointRank a b N (x, i) < pointRank a b N (x, j) := by
  have hd := pointRank_sub_pointRank_snd a b N x i j
  have h1 : (1 : ℤ) ≤ (((a * N + 1) * N : ℕ) : ℤ) := by
    have : 1 ≤ (a * N + 1) * N := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have h2 : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  have h3 : (1 : ℤ) ≤ (j : ℤ) - i := by
    have : (i : ℤ) < (j : ℤ) := by exact_mod_cast hij
    omega
  have h5 : 0 < (((a * N + 1) * N : ℕ) : ℤ) * a * ((j : ℤ) - i) :=
    mul_pos (mul_pos (by omega) (by omega)) (by omega)
  linarith

/-- An east step strictly lowers the rank, on a rectangle with a row and a column. -/
theorem pointRank_lt_pointRank_fst (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (x h : ℕ) :
    pointRank a b N (x + 1, h) < pointRank a b N (x, h) := by
  have hd := pointRank_sub_pointRank_fst a b N x h
  have h2 : (2 : ℤ) ≤ (((a * N + 1) * N * b : ℕ) : ℤ) := by
    have haN : 1 ≤ a * N := Nat.one_le_iff_ne_zero.2 (by positivity)
    have : 2 ≤ (a * N + 1) * N * b := by
      calc 2 = 2 * 1 * 1 := by norm_num
        _ ≤ (a * N + 1) * N * b := Nat.mul_le_mul (Nat.mul_le_mul (by omega) hN) hb
    exact_mod_cast this
  omega

/-! ### An isolated lattice point between two levels -/

/-- The hypothesis the four rules of Mellit's Theorem 4.2 share: the lattice point `(x, j)` of the
rectangle has rank strictly between the admissible levels `ηlo` and `ηhi`, and no lattice point of
the rectangle has rank strictly between them other than by having the rank of `(x, j)` itself. -/
structure Isolated (a b N : ℕ) (ηlo ηhi : ℚ) (x j : ℕ) : Prop where
  /-- The point lies in the rectangle's columns. -/
  fst_le : x ≤ a * N
  /-- The point lies in the rectangle's rows. -/
  snd_le : j ≤ b * N
  /-- The lower level is admissible. -/
  adm_lo : IsAdmissibleLevel ηlo
  /-- The upper level is admissible. -/
  adm_hi : IsAdmissibleLevel ηhi
  /-- The point outranks the lower level. -/
  lt_rank : ηlo < ((pointRank a b N (x, j) : ℤ) : ℚ)
  /-- The upper level outranks the point. -/
  rank_lt : ((pointRank a b N (x, j) : ℤ) : ℚ) < ηhi
  /-- No other rank of the rectangle lies between the two levels. -/
  iso : ∀ Q : ℕ × ℕ, Q.1 ≤ a * N → Q.2 ≤ b * N →
    ηlo < ((pointRank a b N Q : ℤ) : ℚ) → ((pointRank a b N Q : ℤ) : ℚ) < ηhi →
    pointRank a b N Q = pointRank a b N (x, j)

namespace Isolated

variable {ηlo ηhi : ℚ} {x j : ℕ}

/-- A lattice point of the rectangle outranked by the isolated point has rank below the lower
level: its rank is not between the levels, and an admissible level is no rank. -/
theorem cast_pointRank_lt (h : Isolated a b N ηlo ηhi x j) {Q : ℕ × ℕ} (hQ1 : Q.1 ≤ a * N)
    (hQ2 : Q.2 ≤ b * N) (hlt : pointRank a b N Q < pointRank a b N (x, j)) :
    ((pointRank a b N Q : ℤ) : ℚ) < ηlo := by
  rcases le_or_gt ((pointRank a b N Q : ℤ) : ℚ) ηlo with hle | hgt
  · exact lt_of_le_of_ne hle (cast_pointRank_ne_of_isAdmissibleLevel h.adm_lo a b N Q)
  · have hltQ : ((pointRank a b N Q : ℤ) : ℚ) < ηhi :=
      lt_trans (by exact_mod_cast hlt) h.rank_lt
    exact absurd (h.iso Q hQ1 hQ2 hgt hltQ) (by omega)

/-- A lattice point of the rectangle outranking the isolated point has rank above the upper
level. -/
theorem lt_cast_pointRank (h : Isolated a b N ηlo ηhi x j) {Q : ℕ × ℕ} (hQ1 : Q.1 ≤ a * N)
    (hQ2 : Q.2 ≤ b * N) (hlt : pointRank a b N (x, j) < pointRank a b N Q) :
    ηhi < ((pointRank a b N Q : ℤ) : ℚ) := by
  rcases le_or_gt ηhi ((pointRank a b N Q : ℤ) : ℚ) with hle | hgt
  · exact lt_of_le_of_ne hle (Ne.symm (cast_pointRank_ne_of_isAdmissibleLevel h.adm_hi a b N Q))
  · have hgtQ : ηlo < ((pointRank a b N Q : ℤ) : ℚ) := lt_trans h.lt_rank (by exact_mod_cast hlt)
    exact absurd (h.iso Q hQ1 hQ2 hgtQ hgt) (by omega)

/-- The level index of the point's column at the lower level is below its ordinate. -/
theorem levelIndex_lo_lt (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) (hN : 0 < N) :
    levelIndex a b N ηlo x < (j : ℤ) :=
  (lt_cast_pointRank_iff ha hN ηlo x j).1 h.lt_rank

/-- The level index of the point's column at the lower level is at least one less than its
ordinate: the point below it in the same column is outranked, so its rank is below `ηlo`. -/
theorem le_levelIndex_lo (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) (hN : 0 < N) (hj : 0 < j) :
    (j : ℤ) - 1 ≤ levelIndex a b N ηlo x := by
  have hlt : pointRank a b N (x, j - 1) < pointRank a b N (x, j) :=
    pointRank_lt_pointRank_snd ha hN b x (by omega)
  have := (cast_pointRank_lt_iff ha hN h.adm_lo x (j - 1)).1
    (h.cast_pointRank_lt h.fst_le (by have := h.snd_le; omega) hlt)
  have hcast : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
  omega

/-- The level index of the point's column at the upper level is at least its ordinate. -/
theorem le_levelIndex_hi (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) (hN : 0 < N) :
    (j : ℤ) ≤ levelIndex a b N ηhi x :=
  (cast_pointRank_lt_iff ha hN h.adm_hi x j).1 h.rank_lt

/-- The level index of the point's column at the upper level is below one more than its ordinate,
provided the point above it in the same column lies in the rectangle. -/
theorem levelIndex_hi_lt (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) (hN : 0 < N)
    (hj : j + 1 ≤ b * N) : levelIndex a b N ηhi x < (j : ℤ) + 1 := by
  have hlt : pointRank a b N (x, j) < pointRank a b N (x, j + 1) :=
    pointRank_lt_pointRank_snd ha hN b x (by omega)
  have := (lt_cast_pointRank_iff ha hN ηhi x (j + 1)).1
    (h.lt_cast_pointRank h.fst_le hj hlt)
  push_cast at this
  omega

/-- The level index of the column to the left, at the upper level, is below the ordinate: the point
one column to the left at the same height outranks the isolated point, so its rank is above
`ηhi`. -/
theorem levelIndex_hi_pred_lt (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hx : 0 < x) : levelIndex a b N ηhi (x - 1) < (j : ℤ) := by
  have hx' : x - 1 + 1 = x := by omega
  have hlt : pointRank a b N (x, j) < pointRank a b N (x - 1, j) := by
    have := pointRank_lt_pointRank_fst (a := a) (b := b) (N := N) ha hb hN (x - 1) j
    rwa [hx'] at this
  exact (lt_cast_pointRank_iff ha hN ηhi (x - 1) j).1
    (h.lt_cast_pointRank (by have := h.fst_le; omega) h.snd_le hlt)

/-- The level index of the column to the right, at the lower level, is at least the ordinate. -/
theorem le_levelIndex_lo_succ (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hx : x + 1 ≤ a * N) : (j : ℤ) ≤ levelIndex a b N ηlo (x + 1) :=
  (cast_pointRank_lt_iff ha hN h.adm_lo (x + 1) j).1
    (h.cast_pointRank_lt hx h.snd_le (pointRank_lt_pointRank_fst ha hb hN x j))

/-- **Lowering the level past the isolated point leaves every other comparison alone.** This is
`HJO.Mellit.levelIndex_of_isolating` read off the bundled hypothesis. -/
theorem levelIndex_iff (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) (hN : 0 < N) {x' i : ℕ}
    (hx' : x' ≤ a * N) (hi : i ≤ b * N) (hne : (x', i) ≠ (x, j)) :
    ((i : ℤ) ≤ levelIndex a b N ηlo x' ↔ (i : ℤ) ≤ levelIndex a b N ηhi x') :=
  levelIndex_of_isolating ha hN h.adm_lo h.adm_hi
    (le_of_lt (lt_trans h.lt_rank h.rank_lt)) h.fst_le h.iso hx' hi hne

/-! ### The colouring moves only in the isolated point's column and the one to its left -/

/-- Off the isolated point's column the crossed north steps do not move: both conditions defining
one are comparisons of the level index of that column with an ordinate of the rectangle, and
`HJO.Mellit.levelIndex_of_isolating` leaves every such comparison alone. -/
theorem mem_colouringNorth_hi_iff (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) (hN : 0 < N)
    (y : Heights a b N) {x' i : ℕ} (hne : x' ≠ x) :
    ((x', i) ∈ colouringNorth y ηhi ↔ (x', i) ∈ colouringNorth y ηlo) := by
  rw [mem_colouringNorth_iff ha hN h.adm_hi, mem_colouringNorth_iff ha hN h.adm_lo]
  have hkey : ∀ hx' : x' < a * N, ∀ hlt : i < ht y (x' + 1),
      ((i : ℤ) = levelIndex a b N ηhi x' ↔ (i : ℤ) = levelIndex a b N ηlo x') := by
    intro hx' hlt
    have hle := ht_le_mul y (x' + 1)
    have e1 := h.levelIndex_iff ha hN (le_of_lt hx') (show i ≤ b * N by omega)
      (by simp [hne])
    have e2 := h.levelIndex_iff ha hN (le_of_lt hx') (show i + 1 ≤ b * N by omega)
      (by simp [hne])
    push_cast at e2
    omega
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, (hkey h1 h3).1 h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, (hkey h1 h3).2 h4⟩

/-- Off the isolated point's column and the one to its left the crossed east steps do not move. -/
theorem mem_colouringEast_hi_iff (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) (hN : 0 < N)
    (y : Heights a b N) {x' i : ℕ} (hne : x' ≠ x) (hne' : x' + 1 ≠ x) :
    ((x', i) ∈ colouringEast y ηhi ↔ (x', i) ∈ colouringEast y ηlo) := by
  rw [mem_colouringEast_iff ha hN h.adm_hi, mem_colouringEast_iff ha hN h.adm_lo]
  have hkey : ∀ hx' : x' < a * N, ∀ heq : i = ht y (x' + 1),
      ((levelIndex a b N ηhi x' < (i : ℤ) ∧ (i : ℤ) ≤ levelIndex a b N ηhi (x' + 1)) ↔
        (levelIndex a b N ηlo x' < (i : ℤ) ∧ (i : ℤ) ≤ levelIndex a b N ηlo (x' + 1))) := by
    intro hx' heq
    have hib : i ≤ b * N := heq ▸ ht_le_mul y (x' + 1)
    have e1 := h.levelIndex_iff ha hN (le_of_lt hx') hib (by simp [hne])
    have e2 := h.levelIndex_iff ha hN (show x' + 1 ≤ a * N by omega) hib (by simp [hne'])
    omega
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, (hkey h1 h2).1 ⟨h3, h4⟩⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, (hkey h1 h2).2 ⟨h3, h4⟩⟩

/-- **At an event of type `B` the colouring gains exactly two members when the level is raised.**
Crossing the isolated point `P = (x, j)` downwards merges the component of the level line that ends
at the east step arriving at `P` with the one that starts at the north step leaving `P`: above the
point both are recorded, below it neither is.

The two points gained are `P` itself, as the crossed north step of its column, and `(x-1, j)`, as
the crossed east step of the column to its left. Every other column is untouched by
`HJO.Mellit.mem_colouringNorth_hi_iff` and `HJO.Mellit.mem_colouringEast_hi_iff`. -/
theorem colouring_hi_eq_of_eventType_B (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (h : Isolated a b N ηlo ηhi x j) (hx0 : 0 < x) (hxa : x + 1 ≤ a * N) (hj0 : 0 < j)
    {y : Heights a b N} (hfoot : ht y x = j) (htop : j < ht y (x + 1)) :
    colouring y ηhi = insert (x, j) (insert (x - 1, j) (colouring y ηlo)) := by
  have hjb : j + 1 ≤ b * N := by
    have := ht_le_mul y (x + 1); omega
  have hIlo : levelIndex a b N ηlo x = (j : ℤ) - 1 := by
    have h1 := h.levelIndex_lo_lt ha hN
    have h2 := h.le_levelIndex_lo ha hN hj0
    omega
  have hIhi : levelIndex a b N ηhi x = (j : ℤ) := by
    have h1 := h.le_levelIndex_hi ha hN
    have h2 := h.levelIndex_hi_lt ha hN hjb
    omega
  have hIhiP := h.levelIndex_hi_pred_lt ha hb hN hx0
  have hIloP : levelIndex a b N ηlo (x - 1) < (j : ℤ) :=
    lt_of_le_of_lt (levelIndex_mono_level a b N (x - 1) (le_of_lt (h.lt_rank.trans h.rank_lt)))
      hIhiP
  have hIloS := h.le_levelIndex_lo_succ ha hb hN hxa
  have hIhiS : (j : ℤ) ≤ levelIndex a b N ηhi (x + 1) :=
    hIloS.trans (levelIndex_mono_level a b N (x + 1) (le_of_lt (h.lt_rank.trans h.rank_lt)))
  ext p
  obtain ⟨x', i⟩ := p
  simp only [Finset.mem_insert, Prod.mk.injEq, colouring_eq_union, Finset.mem_union]
  rcases eq_or_ne x' x with rfl | hne
  · -- the point's own column: the crossed north step `P` appears
    rw [mem_colouringNorth_iff ha hN h.adm_hi, mem_colouringNorth_iff ha hN h.adm_lo,
      mem_colouringEast_iff ha hN h.adm_hi, mem_colouringEast_iff ha hN h.adm_lo]
    have hEast : ∀ _ : i ≤ b * N, ((i : ℤ) ≤ levelIndex a b N ηlo (x' + 1) ↔
        (i : ℤ) ≤ levelIndex a b N ηhi (x' + 1)) := fun hib =>
      h.levelIndex_iff ha hN (by omega) hib (by simp)
    constructor
    · rintro (⟨-, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · exact Or.inl ⟨rfl, by omega⟩
      · refine Or.inr (Or.inr (Or.inr ⟨h1, h2, by omega, ?_⟩))
        exact (hEast (by have := ht_le_mul y (x' + 1); omega)).2 h4
    · rintro (⟨-, rfl⟩ | ⟨hc, -⟩ | ⟨-, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
      · exact absurd hc (by omega)
      · exact absurd h4 (by omega)
      · refine Or.inr ⟨h1, h2, by omega, ?_⟩
        exact (hEast (by have := ht_le_mul y (x' + 1); omega)).1 h4
  rcases eq_or_ne (x' + 1) x with hsucc | hne'
  · -- the column to the left: the crossed east step `(x-1, j)` appears
    have hx'eq : x' = x - 1 := by omega
    have hIhiP' : levelIndex a b N ηhi x' < (j : ℤ) := by rw [hx'eq]; exact hIhiP
    have hIloP' : levelIndex a b N ηlo x' < (j : ℤ) := by rw [hx'eq]; exact hIloP
    rw [mem_colouringEast_iff ha hN h.adm_hi, mem_colouringEast_iff ha hN h.adm_lo,
      mem_colouringNorth_hi_iff h ha hN y hne]
    constructor
    · rintro (hnorth | ⟨h1, h2, h3, h4⟩)
      · exact Or.inr (Or.inr (Or.inl hnorth))
      · refine Or.inr (Or.inl ⟨hx'eq, ?_⟩)
        rw [hsucc] at h2
        omega
    · rintro (⟨hc, -⟩ | ⟨-, rfl⟩ | hnorth | ⟨h1, h2, h3, h4⟩)
      · exact absurd hc hne
      · refine Or.inr ⟨by omega, by rw [hsucc]; omega, by omega, by rw [hsucc]; omega⟩
      · exact Or.inl hnorth
      · exfalso
        rw [hsucc] at h2 h4
        omega
  · -- every other column
    rw [mem_colouringNorth_hi_iff h ha hN y hne, mem_colouringEast_hi_iff h ha hN y hne hne']
    have h1 : ¬ (x' = x) := hne
    have h2 : ¬ (x' = x - 1) := by omega
    simp only [h1, h2, false_and, false_or]

/-- **At an event of type `E` the colouring does not move.** The isolated point lies strictly below
the path, so it is neither a north step nor an east step of it, and the column to its left has its
east step at a height the level line already passed: raising the level past `P` changes no crossing
at all. -/
theorem colouring_hi_eq_of_eventType_E (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (h : Isolated a b N ηlo ηhi x j) (hx0 : 0 < x) (hxa : x + 1 ≤ a * N) (hj0 : 0 < j)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hfoot : j < ht y x) :
    colouring y ηhi = colouring y ηlo := by
  have hjb : j + 1 ≤ b * N := by
    have := ht_le_mul y x; omega
  have hIlo : levelIndex a b N ηlo x = (j : ℤ) - 1 := by
    have h1 := h.levelIndex_lo_lt ha hN
    have h2 := h.le_levelIndex_lo ha hN hj0
    omega
  have hIhi : levelIndex a b N ηhi x = (j : ℤ) := by
    have h1 := h.le_levelIndex_hi ha hN
    have h2 := h.levelIndex_hi_lt ha hN hjb
    omega
  have hIloS := h.le_levelIndex_lo_succ ha hb hN hxa
  have hmono : ht y x ≤ ht y (x + 1) := ht_mono hy.2.2.1 (Nat.le_succ _)
  ext p
  obtain ⟨x', i⟩ := p
  simp only [colouring_eq_union, Finset.mem_union]
  rcases eq_or_ne x' x with rfl | hne
  · rw [mem_colouringNorth_iff ha hN h.adm_hi, mem_colouringNorth_iff ha hN h.adm_lo,
      mem_colouringEast_iff ha hN h.adm_hi, mem_colouringEast_iff ha hN h.adm_lo]
    have hEast : ∀ _ : i ≤ b * N, ((i : ℤ) ≤ levelIndex a b N ηlo (x' + 1) ↔
        (i : ℤ) ≤ levelIndex a b N ηhi (x' + 1)) := fun hib =>
      h.levelIndex_iff ha hN (by omega) hib (by simp)
    constructor
    · rintro (⟨-, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · exact absurd h4 (by omega)
      · exact Or.inr ⟨h1, h2, by omega,
          (hEast (by have := ht_le_mul y (x' + 1); omega)).2 h4⟩
    · rintro (⟨-, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · exact absurd h4 (by omega)
      · exact Or.inr ⟨h1, h2, by omega,
          (hEast (by have := ht_le_mul y (x' + 1); omega)).1 h4⟩
  rcases eq_or_ne (x' + 1) x with hsucc | hne'
  · rw [mem_colouringEast_iff ha hN h.adm_hi, mem_colouringEast_iff ha hN h.adm_lo,
      mem_colouringNorth_hi_iff h ha hN y hne]
    constructor
    · rintro (hnorth | ⟨h1, h2, h3, h4⟩)
      · exact Or.inl hnorth
      · exfalso
        rw [hsucc] at h2 h4
        omega
    · rintro (hnorth | ⟨h1, h2, h3, h4⟩)
      · exact Or.inl hnorth
      · exfalso
        rw [hsucc] at h2 h4
        omega
  · rw [mem_colouringNorth_hi_iff h ha hN y hne, mem_colouringEast_hi_iff h ha hN y hne hne']

/-! ### The event type at the isolated point is `B` or `E` -/

/-- **Given one witness of type `B`, every path with the same colouring below the level has event
type `B` or `E` at the isolated point.** The three other possibilities are each excluded by a member
the colouring would then have in the point's own column, and which the type-`B` witness does not
have there: types `C` and `A` by the crossed north step `(x, j-1)`, type `D` by the crossed east
step `(x, j)`. The remaining possibility, that the point lies strictly *above* the path so that no
event happens at it, is excluded by
`HJO.Mellit.lt_ht_succ_iff_of_colouring_eq` — that is what the colouring knows and no column of it
records. -/
theorem ht_eq_or_lt_of_colouring_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (h : Isolated a b N ηlo ηhi x j) (hxa : x + 1 ≤ a * N) (hj0 : 0 < j)
    {yB y : Heights a b N} (hyB : IsAboveDiagonal yB) (hy : IsAboveDiagonal y)
    (hfootB : ht yB x = j) (htopB : j < ht yB (x + 1))
    (hcol : colouring y ηlo = colouring yB ηlo) :
    (ht y x = j ∧ j < ht y (x + 1)) ∨ j < ht y x := by
  have hjb : j + 1 ≤ b * N := by have := ht_le_mul yB (x + 1); omega
  have hIlo : levelIndex a b N ηlo x = (j : ℤ) - 1 := by
    have h1 := h.levelIndex_lo_lt ha hN
    have h2 := h.le_levelIndex_lo ha hN hj0
    omega
  have hIloS := h.le_levelIndex_lo_succ ha hb hN hxa
  have hmono : ht y x ≤ ht y (x + 1) := ht_mono hy.2.2.1 (Nat.le_succ _)
  have hunder : levelIndex a b N ηlo x < (ht y (x + 1) : ℤ) :=
    (lt_ht_succ_iff_of_colouring_eq ha hb hN h.adm_lo hy hyB hcol x (by omega)).2
      (by omega)
  -- the two members of the colouring the type-`B` witness does not have in the column of `P`
  have hnotpred : ((x, j - 1) : ℕ × ℕ) ∉ colouring yB ηlo := by
    rw [colouring_eq_union, Finset.mem_union]
    rintro (hc | hc)
    · exact absurd ((mem_colouringNorth_iff ha hN h.adm_lo yB x (j - 1)).1 hc).2.1 (by omega)
    · exact absurd ((mem_colouringEast_iff ha hN h.adm_lo yB x (j - 1)).1 hc).2.1 (by omega)
  have hnotpt : ((x, j) : ℕ × ℕ) ∉ colouring yB ηlo := by
    rw [colouring_eq_union, Finset.mem_union]
    rintro (hc | hc)
    · exact absurd ((mem_colouringNorth_iff ha hN h.adm_lo yB x j).1 hc).2.2.2 (by omega)
    · exact absurd ((mem_colouringEast_iff ha hN h.adm_lo yB x j).1 hc).2.1 (by omega)
  rcases lt_trichotomy (ht y x) j with hlt | heq | hgt
  · refine absurd ?_ hnotpred
    rw [← hcol, colouring_eq_union]
    exact Finset.mem_union_left _ ((mem_colouringNorth_iff ha hN h.adm_lo y x (j - 1)).2
      ⟨by omega, by omega, by omega, by omega⟩)
  · rcases lt_or_ge j (ht y (x + 1)) with hlt2 | hge2
    · exact Or.inl ⟨heq, hlt2⟩
    · refine absurd ?_ hnotpt
      rw [← hcol, colouring_eq_union]
      exact Finset.mem_union_right _ ((mem_colouringEast_iff ha hN h.adm_lo y x j).2
        ⟨by omega, by omega, by omega, by omega⟩)
  · exact Or.inr hgt

/-! ### The fibres at the upper level -/

/-- **Above the level the type-`B` colouring pins the path down at the isolated point.** The two
members `(x-1, j)` and `(x, j)` that the colouring gains on raising the level — the east step
arriving at `P` and the north step leaving it — force the path of any other member of the upper
fibre to arrive at `P` and leave it upwards. This is why the upper fibre of the type-`B` colouring
is not larger than the lower fibre, in contrast with the other three rules. -/
theorem ht_eq_of_colouring_hi_eq_B (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (h : Isolated a b N ηlo ηhi x j) (hx0 : 0 < x) (hxa : x + 1 ≤ a * N)
    {yB y : Heights a b N} (hfootB : ht yB x = j) (htopB : j < ht yB (x + 1))
    (hcol : colouring y ηhi = colouring yB ηhi) :
    ht y x = j ∧ j < ht y (x + 1) := by
  have hjb : j + 1 ≤ b * N := by have := ht_le_mul yB (x + 1); omega
  have hIhi : levelIndex a b N ηhi x = (j : ℤ) := by
    have h1 := h.le_levelIndex_hi ha hN
    have h2 := h.levelIndex_hi_lt ha hN hjb
    omega
  have hIhiP := h.levelIndex_hi_pred_lt ha hb hN hx0
  have hx1 : x - 1 + 1 = x := by omega
  -- the crossed east step of the column to the left carries the height of the path at `x`
  have heast : ((x - 1, j) : ℕ × ℕ) ∈ colouring yB ηhi :=
    Finset.mem_union_right _ ((mem_colouringEast_iff ha hN h.adm_hi yB (x - 1) j).2
      ⟨by omega, by rw [hx1]; omega, by omega, by rw [hx1]; omega⟩)
  have hnorth : ((x, j) : ℕ × ℕ) ∈ colouring yB ηhi :=
    Finset.mem_union_left _ ((mem_colouringNorth_iff ha hN h.adm_hi yB x j).2
      ⟨by omega, by omega, by omega, by omega⟩)
  rw [← hcol, colouring_eq_union, Finset.mem_union] at heast hnorth
  refine ⟨?_, ?_⟩
  · rcases heast with hc | hc
    · exact absurd ((mem_colouringNorth_iff ha hN h.adm_hi y (x - 1) j).1 hc).2.2.2 (by omega)
    · have := ((mem_colouringEast_iff ha hN h.adm_hi y (x - 1) j).1 hc).2.1
      rw [hx1] at this
      omega
  · rcases hnorth with hc | hc
    · exact ((mem_colouringNorth_iff ha hN h.adm_hi y x j).1 hc).2.2.1
    · exact absurd ((mem_colouringEast_iff ha hN h.adm_hi y x j).1 hc).2.2.1 (by omega)

/-- **Above the level the type-`E` colouring keeps the isolated point strictly below the path.** -/
theorem lt_ht_of_colouring_hi_eq_E (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (h : Isolated a b N ηlo ηhi x j) (hxa : x + 1 ≤ a * N)
    {yE y : Heights a b N} (hyE : IsAboveDiagonal yE) (hy : IsAboveDiagonal y)
    (hbelow : j < ht yE x) (hjb : j + 1 ≤ b * N)
    (hcol : colouring y ηhi = colouring yE ηhi) :
    j < ht y x := by
  have hIhi : levelIndex a b N ηhi x = (j : ℤ) := by
    have h1 := h.le_levelIndex_hi ha hN
    have h2 := h.levelIndex_hi_lt ha hN hjb
    omega
  have hmonoE : ht yE x ≤ ht yE (x + 1) := ht_mono hyE.2.2.1 (Nat.le_succ _)
  have hunder : levelIndex a b N ηhi x < (ht y (x + 1) : ℤ) :=
    (lt_ht_succ_iff_of_colouring_eq ha hb hN h.adm_hi hy hyE hcol x (by omega)).2
      (by omega)
  by_contra hcon
  have hmem : ((x, j) : ℕ × ℕ) ∈ colouring y ηhi :=
    Finset.mem_union_left _ ((mem_colouringNorth_iff ha hN h.adm_hi y x j).2
      ⟨by omega, by omega, by omega, by omega⟩)
  rw [hcol, colouring_eq_union, Finset.mem_union] at hmem
  rcases hmem with hc | hc
  · exact absurd ((mem_colouringNorth_iff ha hN h.adm_hi yE x j).1 hc).2.1 (by omega)
  · exact absurd ((mem_colouringEast_iff ha hN h.adm_hi yE x j).1 hc).2.1 (by omega)

/-! ### The live north steps at the isolated point -/

/-- The isolated point is the lowest-ranked swept point above the lower level: a swept point of
smaller rank would have rank below `ηlo`. -/
theorem min_sweptAbove (h : Isolated a b N ηlo ηhi x j) {y : Heights a b N}
    (hP : ((x, j) : ℕ × ℕ) ∈ sweptRegion y) :
    ((x, j) : ℕ × ℕ) ∈ sweptAbove y ηlo ∧
      ∀ R ∈ sweptAbove y ηlo, pointRank a b N (x, j) ≤ pointRank a b N R := by
  refine ⟨Finset.mem_filter.2 ⟨hP, h.lt_rank⟩, fun R hR => ?_⟩
  obtain ⟨hRS, hRη⟩ := Finset.mem_filter.1 hR
  by_contra hcon
  obtain ⟨hR1, -, hR3⟩ := mem_sweptRegion.1 hRS
  exact absurd (h.cast_pointRank_lt hR1 (hR3.trans (ht_le_mul y _)) (by omega))
    (not_lt.2 hRη.le)

/-- **The live north steps at the isolated point are the steps the lower level crosses, together
with the isolated point itself when that is a north step.** The balance of
`HJO.Mellit.sdiff_liveSteps_colouringNorth` and `HJO.Mellit.sdiff_colouringNorth_liveSteps` at the
lowest swept point above the level, with the head correction vanishing because the point below the
isolated one in its column is not a north step — which is what the event types `B` and `E` have in
common. -/
theorem liveSteps_eq_union (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) (hN : 0 < N)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hP : ((x, j) : ℕ × ℕ) ∈ sweptRegion y) (hfoot : j ≤ ht y x) :
    liveSteps y (x, j) = {u ∈ northSteps y | u = ((x, j) : ℕ × ℕ)} ∪ colouringNorth y ηlo := by
  obtain ⟨hmem, hmin⟩ := h.min_sweptAbove hP
  have hhead : {u ∈ northSteps y | (u.1, u.2 + 1) = ((x, j) : ℕ × ℕ)} = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun {u} hu heq => ?_
    obtain ⟨-, h2, -⟩ := mem_northSteps_iff.1 hu
    have e1 : u.1 = x := congrArg Prod.fst heq
    have e2 : u.2 + 1 = j := congrArg Prod.snd heq
    rw [e1] at h2
    omega
  have h1 := sdiff_liveSteps_colouringNorth hy ha hN h.adm_lo hmem hmin
  have h2 := sdiff_colouringNorth_liveSteps hy ha hN h.adm_lo hmem hmin
  rw [hhead] at h2
  rw [← h1, Finset.sdiff_union_of_subset (Finset.sdiff_eq_empty_iff_subset.1 h2)]

/-- The isolated point is no crossed north step of the lower level: it outranks the level. -/
theorem notMem_colouringNorth (h : Isolated a b N ηlo ηhi x j) (y : Heights a b N) :
    ((x, j) : ℕ × ℕ) ∉ colouringNorth y ηlo := fun hc =>
  absurd (Finset.mem_filter.1 hc).2.1 (not_lt.2 h.lt_rank.le)

/-- **At an event of type `B` the width at the isolated point is one more than the number of steps
the lower level crosses.** -/
theorem sweepWidth_eq_of_eventType_B (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) (hN : 0 < N)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hP : ((x, j) : ℕ × ℕ) ∈ sweptRegion y) (hfoot : ht y x = j) (htop : j < ht y (x + 1))
    (hxa : x + 1 ≤ a * N) :
    sweepWidth y (x, j) = #(colouringNorth y ηlo) + 1 := by
  have hmemN : ((x, j) : ℕ × ℕ) ∈ northSteps y := by
    simp only [mem_northSteps_iff]
    omega
  have hfil : {u ∈ northSteps y | u = ((x, j) : ℕ × ℕ)} = {((x, j) : ℕ × ℕ)} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun hv => hv.2, fun hv => ⟨hv ▸ hmemN, hv⟩⟩
  rw [sweepWidth, h.liveSteps_eq_union ha hN hy hP (by omega), hfil, Finset.singleton_union,
    Finset.card_insert_of_notMem (h.notMem_colouringNorth y)]

/-- **At an event of type `E` the width at the isolated point is the number of steps the lower level
crosses**: the point is not a north step of the path at all. -/
theorem sweepWidth_eq_of_eventType_E (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) (hN : 0 < N)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hP : ((x, j) : ℕ × ℕ) ∈ sweptRegion y) (hbelow : j < ht y x) :
    sweepWidth y (x, j) = #(colouringNorth y ηlo) := by
  have hnot : ((x, j) : ℕ × ℕ) ∉ northSteps y := by
    simp only [mem_northSteps_iff]
    omega
  have hfil : {u ∈ northSteps y | u = ((x, j) : ℕ × ℕ)} = ∅ :=
    Finset.filter_eq_empty_iff.2 fun {u} hu hv => hnot (hv ▸ hu)
  rw [sweepWidth, h.liveSteps_eq_union ha hN hy hP (by omega), hfil, Finset.empty_union]

/-- **The live count to the right of the isolated point is read off the crossed north steps of the
lower level alone**, at both event types: the only step the two sets differ by is the isolated point
itself, which sits in the point's own column and so is not counted to its right. -/
theorem sweepRight_eq_card (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) (hN : 0 < N)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hP : ((x, j) : ℕ × ℕ) ∈ sweptRegion y) (hfoot : j ≤ ht y x) :
    sweepRight y (x, j) = #{u ∈ colouringNorth y ηlo | x < u.1} := by
  have hempty : {u ∈ {v ∈ northSteps y | v = ((x, j) : ℕ × ℕ)} | (x, j).1 < u.1} = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun {u} hu => ?_
    rw [(Finset.mem_filter.1 hu).2]
    simp
  rw [sweepRight, h.liveSteps_eq_union ha hN hy hP hfoot, Finset.filter_union, hempty,
    Finset.empty_union]

/-! ### The colouring below the level, recovered from the one above it -/

/-- **At an event of type `B` the colouring below the level is the one above it with the two gained
members removed.** The converse reading of `HJO.Mellit.Isolated.colouring_hi_eq_of_eventType_B`, and
what shows that the upper fibre of a type-`B` colouring is contained in the lower one. -/
theorem colouring_lo_eq_sdiff_of_eventType_B (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (h : Isolated a b N ηlo ηhi x j) (hx0 : 0 < x) (hxa : x + 1 ≤ a * N) (hj0 : 0 < j)
    {y : Heights a b N} (hfoot : ht y x = j) (htop : j < ht y (x + 1)) :
    colouring y ηlo = colouring y ηhi \ {((x, j) : ℕ × ℕ), ((x - 1, j) : ℕ × ℕ)} := by
  have hIlo : levelIndex a b N ηlo x = (j : ℤ) - 1 := by
    have h1 := h.levelIndex_lo_lt ha hN
    have h2 := h.le_levelIndex_lo ha hN hj0
    omega
  have hIhiP := h.levelIndex_hi_pred_lt ha hb hN hx0
  have hIloP : levelIndex a b N ηlo (x - 1) < (j : ℤ) :=
    lt_of_le_of_lt (levelIndex_mono_level a b N (x - 1) (le_of_lt (h.lt_rank.trans h.rank_lt)))
      hIhiP
  have hnot1 : ((x, j) : ℕ × ℕ) ∉ colouring y ηlo := by
    rw [colouring_eq_union, Finset.mem_union]
    rintro (hc | hc)
    · exact absurd ((mem_colouringNorth_iff ha hN h.adm_lo y x j).1 hc).2.2.2 (by omega)
    · exact absurd ((mem_colouringEast_iff ha hN h.adm_lo y x j).1 hc).2.1 (by omega)
  have hnot2 : ((x - 1, j) : ℕ × ℕ) ∉ colouring y ηlo := by
    rw [colouring_eq_union, Finset.mem_union]
    rintro (hc | hc)
    · exact absurd ((mem_colouringNorth_iff ha hN h.adm_lo y (x - 1) j).1 hc).2.2.2 (by omega)
    · have := ((mem_colouringEast_iff ha hN h.adm_lo y (x - 1) j).1 hc).2.2.2
      rw [show x - 1 + 1 = x by omega] at this
      omega
  rw [h.colouring_hi_eq_of_eventType_B ha hb hN hx0 hxa hj0 hfoot htop]
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · intro hz
    exact ⟨Or.inr (Or.inr hz), fun hc => hnot1 (hc ▸ hz), fun hc => hnot2 (hc ▸ hz)⟩
  · rintro ⟨h1 | h1 | h1, h2, h3⟩
    · exact absurd h1 h2
    · exact absurd h1 h3
    · exact h1

/-! ### The trace below the level and the trace above it -/

/-- **Lowering the level past the isolated point adds exactly its own triple to the trace.** -/
theorem levelTrace_lo_eq_insert (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a)
    {y : Heights a b N} (hP : ((x, j) : ℕ × ℕ) ∈ sweptRegion y) :
    levelTrace y ηlo =
      insert (((x, j) : ℕ × ℕ), eventType y (x, j), sweepRight y (x, j)) (levelTrace y ηhi) := by
  rw [levelTrace, sweptAbove_eq_insert_of_isolating ha h.adm_hi h.lt_rank h.rank_lt h.iso hP,
    Finset.image_union, Finset.image_singleton, levelTrace, Finset.singleton_union]

/-- The isolated point is not swept above the upper level: the upper level outranks it. -/
theorem notMem_sweptAbove_hi (h : Isolated a b N ηlo ηhi x j) (y : Heights a b N) :
    ((x, j) : ℕ × ℕ) ∉ sweptAbove y ηhi := fun hc =>
  absurd (Finset.mem_filter.1 hc).2 (not_lt.2 h.rank_lt.le)

/-- **The trace above the level is the trace below it with the isolated point's triple dropped.** -/
theorem levelTrace_hi_eq_filter (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a)
    {y : Heights a b N} (hP : ((x, j) : ℕ × ℕ) ∈ sweptRegion y) :
    {z ∈ levelTrace y ηlo | z.1 ≠ ((x, j) : ℕ × ℕ)} = levelTrace y ηhi := by
  rw [h.levelTrace_lo_eq_insert ha hP, Finset.filter_insert, ite_eq_right (by simp)]
  refine Finset.filter_true_of_mem fun z hz => ?_
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hz
  exact fun hc => h.notMem_sweptAbove_hi y (hc ▸ hQ)

/-- The triple of the isolated point is a member of the trace below the level. -/
theorem mem_levelTrace_lo (h : Isolated a b N ηlo ηhi x j) (ha : 0 < a) {y : Heights a b N}
    (hP : ((x, j) : ℕ × ℕ) ∈ sweptRegion y) :
    (((x, j) : ℕ × ℕ), eventType y (x, j), sweepRight y (x, j)) ∈ levelTrace y ηlo := by
  rw [h.levelTrace_lo_eq_insert ha hP]
  exact Finset.mem_insert_self _ _

/-- A triple of the trace at the isolated point records that point's event type and live count. -/
theorem eq_of_mem_levelTrace {y : Heights a b N} {η : ℚ} {e : EventType} {n : ℕ}
    (hmem : (((x, j) : ℕ × ℕ), e, n) ∈ levelTrace y η) :
    eventType y (x, j) = e ∧ sweepRight y (x, j) = n := by
  obtain ⟨Q, -, hQ⟩ := Finset.mem_image.1 hmem
  have h1 : Q = ((x, j) : ℕ × ℕ) := congrArg Prod.fst hQ
  refine ⟨?_, ?_⟩
  · have := congrArg (fun t => t.2.1) hQ
    rwa [h1] at this
  · have := congrArg (fun t => t.2.2) hQ
    rwa [h1] at this

end Isolated

/-- Membership in the index set of `HJO.Mellit.dsc`, unfolded. -/
theorem mem_traceIndex_iff {η : ℚ} {c : Finset (ℕ × ℕ)}
    {σ : Finset ((ℕ × ℕ) × Paths.EventType × ℕ)} :
    σ ∈ traceIndex a b N η c ↔
      ∃ y : Heights a b N, IsAboveDiagonal y ∧ colouring y η = c ∧ levelTrace y η = σ := by
  simp only [traceIndex, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨y, ⟨h1, h2⟩, h3⟩ => ⟨y, h1, h2, h3⟩, fun ⟨y, h1, h2, h3⟩ => ⟨y, ⟨h1, h2⟩, h3⟩⟩

/-- `HJO.Paths.eventType_eq_B_iff` with the point written out as a pair, so that `omega` sees the
heights. -/
private theorem eventType_mk_eq_B_iff {y : Heights a b N} {x k : ℕ} :
    eventType y (x, k) = EventType.B ↔ k = ht y x ∧ x < a * N ∧ k < ht y (x + 1) :=
  eventType_eq_B_iff

/-- `HJO.Paths.eventType_eq_E_iff` with the point written out as a pair. -/
private theorem eventType_mk_eq_E_iff {y : Heights a b N} {x k : ℕ} :
    eventType y (x, k) = EventType.E ↔ k < ht y x :=
  eventType_eq_E_iff

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The fibre below the level splits into the two event types -/

/-- **The fibre of the colouring below the level splits into the type-`B` paths and the type-`E`
paths.** Every above-diagonal path with the same colouring as the type-`B` witness at the lower
level sweeps the isolated point, has the same live count to its right, and has event type either `B`
— in which case its width at the point and its colouring above the level are those of the `B`
witness — or `E` — in which case its colouring above the level is that of the `E` witness.

This is the grouping the proof of rule `BE` uses, and the two facts it rests on that no single
column of a colouring records: `HJO.Mellit.lt_ht_succ_iff_of_colouring_eq`, which puts the point
under the path, and `HJO.Mellit.Isolated.sweepRight_eq_card`, which reads the live count off the
crossed north steps. -/
theorem fibre_split (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {ηlo ηhi : ℚ} {x j : ℕ}
    (h : Isolated a b N ηlo ηhi x j) (hx0 : 0 < x) (hxa : x + 1 ≤ a * N) (hj0 : 0 < j)
    {yB yE : Heights a b N} (hyB : IsAboveDiagonal yB) (hyE : IsAboveDiagonal yE)
    (hPB : ((x, j) : ℕ × ℕ) ∈ sweptRegion yB) (hfootB : ht yB x = j)
    (htopB : j < ht yB (x + 1)) (hbelowE : j < ht yE x)
    (hcolBE : colouring yB ηlo = colouring yE ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hc : colouring y ηlo = colouring yB ηlo) :
    ((x, j) : ℕ × ℕ) ∈ sweptRegion y ∧ sweepRight y (x, j) = sweepRight yB (x, j) ∧
      ((eventType y (x, j) = EventType.B ∧ sweepWidth y (x, j) = sweepWidth yB (x, j) ∧
          colouring y ηhi = colouring yB ηhi) ∨
        (eventType y (x, j) = EventType.E ∧ colouring y ηhi = colouring yE ηhi)) := by
  have hdiag : b * x ≤ a * j := (mem_sweptRegion.1 hPB).2.1
  have hcN : colouringNorth y ηlo = colouringNorth yB ηlo :=
    colouringNorth_eq_of_colouring_eq ha hN h.adm_lo hc
  have hdich :=
    h.ht_eq_or_lt_of_colouring_eq ha hb hN hxa hj0 hyB hy hfootB htopB hc
  have hmono : ht y x ≤ ht y (x + 1) := ht_mono hy.2.2.1 (Nat.le_succ _)
  have hfoot : j ≤ ht y x := by rcases hdich with ⟨he, -⟩ | he <;> omega
  have hPy : ((x, j) : ℕ × ℕ) ∈ sweptRegion y := by
    simp only [mem_sweptRegion]
    exact ⟨by omega, hdiag, by omega⟩
  refine ⟨hPy, ?_, ?_⟩
  · rw [h.sweepRight_eq_card ha hN hy hPy hfoot,
      h.sweepRight_eq_card ha hN hyB hPB (by omega), hcN]
  · rcases hdich with ⟨hfe, hte⟩ | hlt
    · refine Or.inl ⟨eventType_mk_eq_B_iff.2 ⟨hfe.symm, by omega, hte⟩, ?_, ?_⟩
      · rw [h.sweepWidth_eq_of_eventType_B ha hN hy hPy hfe hte hxa,
          h.sweepWidth_eq_of_eventType_B ha hN hyB hPB hfootB htopB hxa, hcN]
      · rw [h.colouring_hi_eq_of_eventType_B ha hb hN hx0 hxa hj0 hfe hte,
          h.colouring_hi_eq_of_eventType_B ha hb hN hx0 hxa hj0 hfootB htopB, hc]
    · refine Or.inr ⟨eventType_mk_eq_E_iff.2 hlt, ?_⟩
      rw [h.colouring_hi_eq_of_eventType_E ha hb hN hx0 hxa hj0 hy hlt,
        h.colouring_hi_eq_of_eventType_E ha hb hN hx0 hxa hj0 hyE hbelowE, hc, hcolBE]

/-- **The upper fibre of the type-`B` colouring is the type-`B` part of the lower fibre.** -/
theorem mem_fibre_of_colouring_hi_eq_B (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {ηlo ηhi : ℚ}
    {x j : ℕ} (h : Isolated a b N ηlo ηhi x j) (hx0 : 0 < x) (hxa : x + 1 ≤ a * N) (hj0 : 0 < j)
    {yB y : Heights a b N} (hfootB : ht yB x = j) (htopB : j < ht yB (x + 1))
    (hcol : colouring y ηhi = colouring yB ηhi) :
    colouring y ηlo = colouring yB ηlo ∧ ht y x = j ∧ j < ht y (x + 1) := by
  obtain ⟨hfoot, htop⟩ :=
    h.ht_eq_of_colouring_hi_eq_B ha hb hN hx0 hxa hfootB htopB hcol
  refine ⟨?_, hfoot, htop⟩
  rw [h.colouring_lo_eq_sdiff_of_eventType_B ha hb hN hx0 hxa hj0 hfoot htop,
    h.colouring_lo_eq_sdiff_of_eventType_B ha hb hN hx0 hxa hj0 hfootB htopB, hcol]

/-- **The upper fibre of the type-`E` colouring is the type-`E` part of the lower fibre.** -/
theorem mem_fibre_of_colouring_hi_eq_E (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {ηlo ηhi : ℚ}
    {x j : ℕ} (h : Isolated a b N ηlo ηhi x j) (hx0 : 0 < x) (hxa : x + 1 ≤ a * N) (hj0 : 0 < j)
    {yE y : Heights a b N} (hyE : IsAboveDiagonal yE) (hy : IsAboveDiagonal y)
    (hbelowE : j < ht yE x) (hjb : j + 1 ≤ b * N)
    (hcol : colouring y ηhi = colouring yE ηhi) :
    colouring y ηlo = colouring yE ηlo ∧ j < ht y x := by
  have hbelow := h.lt_ht_of_colouring_hi_eq_E ha hb hN hxa hyE hy hbelowE hjb hcol
  refine ⟨?_, hbelow⟩
  rw [← h.colouring_hi_eq_of_eventType_E ha hb hN hx0 hxa hj0 hy hbelow,
    ← h.colouring_hi_eq_of_eventType_E ha hb hN hx0 hxa hj0 hyE hbelowE]
  exact hcol

/-! ### Regrouping the traces -/

/-- **The traces below the level carrying a given event type at the isolated point are, after the
point's own triple is dropped, exactly the traces above the level of the corresponding colouring.**
This is the regrouping the proof performs, stated so that both rules of `BE` use it: the
map drops the triple of `P`, and its inverse puts it back, the triple being the same for every path
of the fibre with that event type.

The hypotheses say that the fibre of `cLo` below the level, restricted to the event type `e`, and
the fibre of `cHi` above it are the same set of paths. -/
theorem sum_partialSweepWord_hi (q u : L) (ha : 0 < a) (hN : 0 < N) {ηlo ηhi : ℚ} {x j : ℕ}
    (h : Isolated a b N ηlo ηhi x j) {cLo cHi : Finset (ℕ × ℕ)} {e : EventType} {r : ℕ}
    (hfwd : ∀ y : Heights a b N, IsAboveDiagonal y → colouring y ηlo = cLo →
      eventType y (x, j) = e → ((x, j) : ℕ × ℕ) ∈ sweptRegion y ∧ colouring y ηhi = cHi)
    (hbwd : ∀ y : Heights a b N, IsAboveDiagonal y → colouring y ηhi = cHi →
      colouring y ηlo = cLo ∧ ((x, j) : ℕ × ℕ) ∈ sweptRegion y ∧
        eventType y (x, j) = e ∧ sweepRight y (x, j) = r) :
    ∑ τ ∈ {τ ∈ traceIndex a b N ηlo cLo | (((x, j) : ℕ × ℕ), e, r) ∈ τ},
        partialSweepWord q u (traceRep a b N ηlo cLo τ) ηhi (1 : Total L)
      = dsc q u a b N ηhi cHi := by
  classical
  have hbase : ∀ τ ∈ {τ ∈ traceIndex a b N ηlo cLo | (((x, j) : ℕ × ℕ), e, r) ∈ τ},
      IsAboveDiagonal (traceRep a b N ηlo cLo τ) ∧
        colouring (traceRep a b N ηlo cLo τ) ηhi = cHi ∧
        levelTrace (traceRep a b N ηlo cLo τ) ηhi = {z ∈ τ | z.1 ≠ ((x, j) : ℕ × ℕ)} ∧
        τ = insert (((x, j) : ℕ × ℕ), e, r) {z ∈ τ | z.1 ≠ ((x, j) : ℕ × ℕ)} := by
    intro τ hτ
    obtain ⟨hτT, hτe⟩ := Finset.mem_filter.1 hτ
    obtain ⟨hy, hcy, hty⟩ := traceRep_spec hτT
    have hmemtr : (((x, j) : ℕ × ℕ), e, r) ∈ levelTrace (traceRep a b N ηlo cLo τ) ηlo := by
      rw [hty]; exact hτe
    obtain ⟨hev, hsr⟩ := Isolated.eq_of_mem_levelTrace hmemtr
    obtain ⟨hPy, hch⟩ := hfwd _ hy hcy hev
    have hfil : levelTrace (traceRep a b N ηlo cLo τ) ηhi = {z ∈ τ | z.1 ≠ ((x, j) : ℕ × ℕ)} :=
      (h.levelTrace_hi_eq_filter ha hPy).symm.trans (by rw [hty])
    refine ⟨hy, hch, hfil, ?_⟩
    have hins : τ = insert (((x, j) : ℕ × ℕ), e, r)
        (levelTrace (traceRep a b N ηlo cLo τ) ηhi) :=
      hty.symm.trans (by rw [h.levelTrace_lo_eq_insert ha hPy, hev, hsr])
    exact hins.trans (by rw [hfil])
  refine Finset.sum_bij (fun τ _ => {z ∈ τ | z.1 ≠ ((x, j) : ℕ × ℕ)}) ?_ ?_ ?_ ?_
  · intro τ hτ
    obtain ⟨hy, hch, hfil, -⟩ := hbase τ hτ
    exact mem_traceIndex_iff.2 ⟨_, hy, hch, hfil⟩
  · intro τ₁ h₁ τ₂ h₂ heq
    obtain ⟨-, -, -, hins₁⟩ := hbase τ₁ h₁
    obtain ⟨-, -, -, hins₂⟩ := hbase τ₂ h₂
    calc τ₁ = insert (((x, j) : ℕ × ℕ), e, r) {z ∈ τ₁ | z.1 ≠ ((x, j) : ℕ × ℕ)} := hins₁
      _ = insert (((x, j) : ℕ × ℕ), e, r) {z ∈ τ₂ | z.1 ≠ ((x, j) : ℕ × ℕ)} := by rw [heq]
      _ = τ₂ := hins₂.symm
  · intro σ hσ
    obtain ⟨y, hy, hch, hty⟩ := mem_traceIndex_iff.1 hσ
    obtain ⟨hcy, hPy, hev, hsr⟩ := hbwd y hy hch
    refine ⟨levelTrace y ηlo, Finset.mem_filter.2
      ⟨mem_traceIndex_iff.2 ⟨y, hy, hcy, rfl⟩, ?_⟩, ?_⟩
    · rw [h.levelTrace_lo_eq_insert ha hPy, hev, hsr]
      exact Finset.mem_insert_self _ _
    · rw [h.levelTrace_hi_eq_filter ha hPy]
      exact hty
  · intro τ hτ
    obtain ⟨hy, hch, hfil, -⟩ := hbase τ hτ
    obtain ⟨hy2, -, ht2⟩ := traceRep_spec (mem_traceIndex_iff.2 ⟨_, hy, hch, hfil⟩)
    rw [partialSweepWord_eq_of_levelTrace_eq q u ha hN hy hy2 (hfil.trans ht2.symm)]

/-! ### Mellit's Theorem 4.2, rule BE -/

/-- **Mellit's Theorem 4.2, rule `BE`.** `HJO.Mellit.dsc_eq_dminus_add_smul`: with
`ηlo < rk̂(P) < ηhi` isolating the rank of a lattice point `P` of the rectangle, and `P̂`, `Q̂` two
above-diagonal `(aN, bN)`-paths sweeping `P` with `ev_{P̂}(P) = B`, `ev_{Q̂}(P) = E` and the same
colouring at `ηlo`,
`D_{ηlo, c_{ηlo}(P̂)} = d_- D_{ηhi, c_{ηhi}(P̂)} + u D_{ηhi, c_{ηhi}(Q̂)}`,
the lowering operator being read at the width of the sweep at `P`, as `HJO.Mellit.sweepOperator`
reads it.

This is the one rule of the theorem with two predecessors, and the proof is Mellit's: the
traces below the level split into those whose event at `P` has type `B` and those whose event has
type `E`, the extra factor of `HJO.Mellit.sweepOperator` is `d_-` on the first class and `u` on the
second, and dropping `P`'s own triple identifies each class with the traces above the level of the
corresponding colouring (`HJO.Mellit.sum_partialSweepWord_hi`).

That the split is exhaustive is `HJO.Mellit.fibre_split`; that each class is *all* of the upper
fibre — so that no path above the level is missed — is
`HJO.Mellit.mem_fibre_of_colouring_hi_eq_B` and `HJO.Mellit.mem_fibre_of_colouring_hi_eq_E`.

`0 < a`, `0 < b` and `0 < N` are carried as explicit hypotheses; they hold in the standing
range `1 < a < b` with `N ≥ 1`, so nothing is lost. They are needed: the rank
is injective on the rectangle only for `0 < a` and `0 < N`, and the column to the left of `P` is
separated from `P` by the level only because an east step lowers the rank, which needs `0 < b`. -/
@[hjo "lem_mellit_thm42_be"]
theorem dsc_eq_dminus_add_smul (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {P : ℕ × ℕ}
    {ηlo ηhi : ℚ} (hlo : IsAdmissibleLevel ηlo) (hhi : IsAdmissibleLevel ηhi)
    (hP1 : P.1 ≤ a * N) (hP2 : P.2 ≤ b * N)
    (hrlo : ηlo < ((pointRank a b N P : ℤ) : ℚ)) (hrhi : ((pointRank a b N P : ℤ) : ℚ) < ηhi)
    (hiso : ∀ Q : ℕ × ℕ, Q.1 ≤ a * N → Q.2 ≤ b * N →
      ηlo < ((pointRank a b N Q : ℤ) : ℚ) → ((pointRank a b N Q : ℤ) : ℚ) < ηhi →
      pointRank a b N Q = pointRank a b N P)
    {yB yE : Heights a b N} (hyB : IsAboveDiagonal yB) (hyE : IsAboveDiagonal yE)
    (hPB : P ∈ sweptRegion yB) (hevB : eventType yB P = EventType.B)
    (hevE : eventType yE P = EventType.E) (hcolBE : colouring yB ηlo = colouring yE ηlo) :
    dsc q u a b N ηlo (colouring yB ηlo)
      = dminus q (sweepWidth yB P) (dsc q u a b N ηhi (colouring yB ηhi))
        + u • dsc q u a b N ηhi (colouring yE ηhi) := by
  classical
  obtain ⟨x, j⟩ := P
  obtain ⟨hjfootB, hxlt, htopB⟩ := eventType_mk_eq_B_iff.1 hevB
  have hfootB : ht yB x = j := hjfootB.symm
  have hbelowE : j < ht yE x := eventType_mk_eq_E_iff.1 hevE
  have hxa : x + 1 ≤ a * N := by omega
  have hdiag : b * x ≤ a * j := (mem_sweptRegion.1 hPB).2.1
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [hyE.1] at hbelowE; omega
    · exact hx
  have hj0 : 0 < j := by
    by_contra hcon
    rw [show j = 0 by omega, Nat.mul_zero] at hdiag
    exact absurd (Nat.le_zero.1 hdiag) (Nat.mul_pos hb hx0).ne'
  have hjb : j + 1 ≤ b * N := by have := ht_le_mul yB (x + 1); omega
  have h : Isolated a b N ηlo ηhi x j := ⟨hP1, hP2, hlo, hhi, hrlo, hrhi, hiso⟩
  have key := fun (y : Heights a b N) (hy : IsAboveDiagonal y)
      (hc : colouring y ηlo = colouring yB ηlo) =>
    fibre_split ha hb hN h hx0 hxa hj0 hyB hyE hPB hfootB htopB hbelowE hcolBE hy hc
  -- the four halves of the fibre correspondence
  have hfwdB : ∀ y : Heights a b N, IsAboveDiagonal y → colouring y ηlo = colouring yB ηlo →
      eventType y (x, j) = EventType.B →
      ((x, j) : ℕ × ℕ) ∈ sweptRegion y ∧ colouring y ηhi = colouring yB ηhi := by
    intro y hy hcy hev
    obtain ⟨hPy, -, hcase⟩ := key _ hy hcy
    refine ⟨hPy, ?_⟩
    rcases hcase with ⟨-, -, hch⟩ | ⟨hevE', -⟩
    · exact hch
    · exact absurd (hev.symm.trans hevE') (by simp)
  have hbwdB : ∀ y : Heights a b N, IsAboveDiagonal y → colouring y ηhi = colouring yB ηhi →
      colouring y ηlo = colouring yB ηlo ∧ ((x, j) : ℕ × ℕ) ∈ sweptRegion y ∧
        eventType y (x, j) = EventType.B ∧ sweepRight y (x, j) = sweepRight yB (x, j) := by
    intro y hy hch
    obtain ⟨hcy, hfoot, htop⟩ :=
      mem_fibre_of_colouring_hi_eq_B ha hb hN h hx0 hxa hj0 hfootB htopB hch
    obtain ⟨hPy, hry, -⟩ := key _ hy hcy
    exact ⟨hcy, hPy, eventType_mk_eq_B_iff.2 ⟨hfoot.symm, by omega, htop⟩, hry⟩
  have hfwdE : ∀ y : Heights a b N, IsAboveDiagonal y → colouring y ηlo = colouring yB ηlo →
      eventType y (x, j) = EventType.E →
      ((x, j) : ℕ × ℕ) ∈ sweptRegion y ∧ colouring y ηhi = colouring yE ηhi := by
    intro y hy hcy hev
    obtain ⟨hPy, -, hcase⟩ := key _ hy hcy
    refine ⟨hPy, ?_⟩
    rcases hcase with ⟨hevB', -, -⟩ | ⟨-, hch⟩
    · exact absurd (hev.symm.trans hevB') (by simp)
    · exact hch
  have hbwdE : ∀ y : Heights a b N, IsAboveDiagonal y → colouring y ηhi = colouring yE ηhi →
      colouring y ηlo = colouring yB ηlo ∧ ((x, j) : ℕ × ℕ) ∈ sweptRegion y ∧
        eventType y (x, j) = EventType.E ∧ sweepRight y (x, j) = sweepRight yB (x, j) := by
    intro y hy hch
    obtain ⟨hcy, hbelow⟩ :=
      mem_fibre_of_colouring_hi_eq_E ha hb hN h hx0 hxa hj0 hyE hy hbelowE hjb hch
    have hcy' : colouring y ηlo = colouring yB ηlo := hcy.trans hcolBE.symm
    obtain ⟨hPy, hry, -⟩ := key _ hy hcy'
    exact ⟨hcy', hPy, eventType_mk_eq_E_iff.2 hbelow, hry⟩
  -- the event type at `P` of the representative of a trace is read off the trace
  have hmemiff : ∀ τ ∈ traceIndex a b N ηlo (colouring yB ηlo), ∀ e : EventType,
      ((((x, j) : ℕ × ℕ), e, sweepRight yB (x, j)) ∈ τ ↔
        eventType (traceRep a b N ηlo (colouring yB ηlo) τ) (x, j) = e) := by
    intro τ hτ e
    obtain ⟨hy, hcy, hty⟩ := traceRep_spec hτ
    obtain ⟨hPy, hry, -⟩ := key _ hy hcy
    constructor
    · intro hme
      have hme' : (((x, j) : ℕ × ℕ), e, sweepRight yB (x, j)) ∈
          levelTrace (traceRep a b N ηlo (colouring yB ηlo) τ) ηlo := by rw [hty]; exact hme
      exact (Isolated.eq_of_mem_levelTrace hme').1
    · intro hev
      have hin := h.mem_levelTrace_lo ha hPy
      rw [hev, hry, hty] at hin
      exact hin
  -- the type-`E` traces are those that are not of type `B`
  have hfilteq : {τ ∈ traceIndex a b N ηlo (colouring yB ηlo) |
        ¬ (((x, j) : ℕ × ℕ), EventType.B, sweepRight yB (x, j)) ∈ τ}
      = {τ ∈ traceIndex a b N ηlo (colouring yB ηlo) |
        (((x, j) : ℕ × ℕ), EventType.E, sweepRight yB (x, j)) ∈ τ} := by
    refine Finset.filter_congr fun τ hτ => ?_
    obtain ⟨hy, hcy, -⟩ := traceRep_spec hτ
    obtain ⟨-, -, hcase⟩ := key _ hy hcy
    rw [hmemiff τ hτ, hmemiff τ hτ]
    rcases hcase with ⟨hev, -, -⟩ | ⟨hev, -⟩ <;> rw [hev] <;> simp
  -- the extra factor on each class
  have hsumB : ∀ τ ∈ {τ ∈ traceIndex a b N ηlo (colouring yB ηlo) |
        (((x, j) : ℕ × ℕ), EventType.B, sweepRight yB (x, j)) ∈ τ},
      partialSweepWord q u (traceRep a b N ηlo (colouring yB ηlo) τ) ηlo (1 : Total L)
        = dminus q (sweepWidth yB (x, j))
            (partialSweepWord q u (traceRep a b N ηlo (colouring yB ηlo) τ) ηhi 1) := by
    intro τ hτ
    obtain ⟨hτT, hτB⟩ := Finset.mem_filter.1 hτ
    obtain ⟨hy, hcy, -⟩ := traceRep_spec hτT
    have hev := (hmemiff τ hτT EventType.B).1 hτB
    obtain ⟨hPy, -, hcase⟩ := key _ hy hcy
    have hw : sweepWidth (traceRep a b N ηlo (colouring yB ηlo) τ) (x, j)
        = sweepWidth yB (x, j) := by
      rcases hcase with ⟨-, hw, -⟩ | ⟨hevE', -⟩
      · exact hw
      · exact absurd (hev.symm.trans hevE') (by simp)
    rw [partialSweepWord_eq_sweepOperator_mul q u ha h.adm_hi h.lt_rank h.rank_lt h.iso hPy,
      Module.End.mul_apply, sweepOperator_of_eventType_B _ hev, hw]
  have hsumE : ∀ τ ∈ {τ ∈ traceIndex a b N ηlo (colouring yB ηlo) |
        (((x, j) : ℕ × ℕ), EventType.E, sweepRight yB (x, j)) ∈ τ},
      partialSweepWord q u (traceRep a b N ηlo (colouring yB ηlo) τ) ηlo (1 : Total L)
        = u • partialSweepWord q u (traceRep a b N ηlo (colouring yB ηlo) τ) ηhi 1 := by
    intro τ hτ
    obtain ⟨hτT, hτE⟩ := Finset.mem_filter.1 hτ
    obtain ⟨hy, hcy, -⟩ := traceRep_spec hτT
    have hev := (hmemiff τ hτT EventType.E).1 hτE
    obtain ⟨hPy, -, -⟩ := key _ hy hcy
    rw [partialSweepWord_eq_sweepOperator_mul q u ha h.adm_hi h.lt_rank h.rank_lt h.iso hPy,
      Module.End.mul_apply, sweepOperator_of_eventType_E q u _ _ hev]
    simp
  -- split the sum and evaluate both halves
  have hlhs : dsc q u a b N ηlo (colouring yB ηlo)
      = (∑ τ ∈ {τ ∈ traceIndex a b N ηlo (colouring yB ηlo) |
            (((x, j) : ℕ × ℕ), EventType.B, sweepRight yB (x, j)) ∈ τ},
          partialSweepWord q u (traceRep a b N ηlo (colouring yB ηlo) τ) ηlo (1 : Total L))
        + ∑ τ ∈ {τ ∈ traceIndex a b N ηlo (colouring yB ηlo) |
            ¬ (((x, j) : ℕ × ℕ), EventType.B, sweepRight yB (x, j)) ∈ τ},
          partialSweepWord q u (traceRep a b N ηlo (colouring yB ηlo) τ) ηlo (1 : Total L) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hlhs, Finset.sum_congr rfl hsumB, ← map_sum,
    sum_partialSweepWord_hi q u ha hN h hfwdB hbwdB, hfilteq, Finset.sum_congr rfl hsumE,
    ← Finset.smul_sum, sum_partialSweepWord_hi q u ha hN h hfwdE hbwdE]

/-! ### The rule at an explicit instance

The hypotheses of rule `BE` ask for two above-diagonal paths differing at one point of the swept
region and agreeing in their colouring below the level. They are satisfiable, and the smallest
coprime rectangle already carries an instance: on the `2 × 3` rectangle the paths `(0,2,3)` and
`(0,3,3)` both have colouring `{(0,0), (1,3)}` at the level `7/2`, and the lattice point `(1,2)`,
of rank `4`, is the foot of a north step of the first and lies strictly below the second. -/

/-- **The two witnesses agree below the level.** Both `(0,2,3)` and `(0,3,3)` are coloured
`{(0,0), (1,3)}` at `7/2` on the `2 × 3` rectangle: the crossed north step is the one leaving the
origin and the crossed east step is the one arriving at the corner. The computation is on the
explicit `Finset`s, the rational level being outside the reach of the kernel's arithmetic. -/
theorem colouring_thm42_be_witness :
    colouring (![0, 2, 3] : Heights 2 3 1) (7 / 2) = {(0, 0), (1, 3)} ∧
      colouring (![0, 3, 3] : Heights 2 3 1) (7 / 2) = {(0, 0), (1, 3)} := by
  constructor
  · have hn : northSteps (![0, 2, 3] : Heights 2 3 1) = {(0, 0), (0, 1), (1, 2)} := by decide
    have he : eastSteps (![0, 2, 3] : Heights 2 3 1) = {(0, 2), (1, 3)} := by decide
    rw [colouring, hn, he]
    norm_num [pointRank, abovePointRank, attackWindow, Finset.filter_insert,
      Finset.filter_singleton]
  · have hn : northSteps (![0, 3, 3] : Heights 2 3 1) = {(0, 0), (0, 1), (0, 2)} := by decide
    have he : eastSteps (![0, 3, 3] : Heights 2 3 1) = {(0, 3), (1, 3)} := by decide
    rw [colouring, hn, he]
    norm_num [pointRank, abovePointRank, attackWindow, Finset.filter_insert,
      Finset.filter_singleton]

/-- **Rule `BE` at an explicit instance.** Every hypothesis of
`HJO.Mellit.dsc_eq_dminus_add_smul` is discharged by computation here, so the statement is
not vacuous: the configuration it describes — one lattice point, two above-diagonal paths, event
types `B` and `E`, the same colouring below the level — does occur. -/
theorem dsc_eq_dminus_add_smul_example (q u : L) :
    dsc q u 2 3 1 (7 / 2) (colouring (![0, 2, 3] : Heights 2 3 1) (7 / 2))
      = dminus q (sweepWidth (![0, 2, 3] : Heights 2 3 1) (1, 2))
          (dsc q u 2 3 1 (9 / 2) (colouring (![0, 2, 3] : Heights 2 3 1) (9 / 2)))
        + u • dsc q u 2 3 1 (9 / 2) (colouring (![0, 3, 3] : Heights 2 3 1) (9 / 2)) := by
  have hrank : pointRank 2 3 1 (1, 2) = 4 := by norm_num [pointRank, abovePointRank]
  refine dsc_eq_dminus_add_smul q u (by norm_num) (by norm_num) (by norm_num)
    ⟨3, by norm_num⟩ ⟨4, by norm_num⟩ (by norm_num) (by norm_num) ?_ ?_ ?_ (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  · rw [hrank]; norm_num
  · rw [hrank]; norm_num
  · intro Q _ _ h1 h2
    rw [hrank] at *
    have hr1 : (3 : ℤ) < pointRank 2 3 1 Q := by
      have h : ((3 : ℤ) : ℚ) < ((pointRank 2 3 1 Q : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast h
    have hr2 : pointRank 2 3 1 Q < 5 := by
      have h : ((pointRank 2 3 1 Q : ℤ) : ℚ) < ((5 : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast h
    omega
  · rw [colouring_thm42_be_witness.1, colouring_thm42_be_witness.2]

end HJO.Mellit
