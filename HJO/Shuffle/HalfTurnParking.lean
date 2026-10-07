/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.HalfTurn
public meta import HJO.Attr

/-! # The half turn of the rectangle, on parking functions

The half turn sends the north step of a below-diagonal path whose foot is at height `s` to the
north step of the reflected path whose foot is at height `bN - 1 - s`, and complements the label
`ℓ` to `bN + 1 - ℓ`. On the encoding of `HJO.ParkingFunctions` both operations are `Fin.rev`, so
the half turn of a parking function is

  `halfTurnPf π = ⟨halfTurn (path π), fun i => (label π i.rev).rev⟩`

and it is an involution up to the two orientations, hence an equivalence
`HJO.ParkingFunctions.halfTurnPfEquiv`.

What the half turn preserves is not the rank but the rank *comparisons*. The two ranks are
`M (ay - bx) + x` for `M = aN + 1` below and `M' = (aN+1)N` above, and for every `M > aN` the sign
of `M D + e` with `|e| ≤ aN` is decided by `(D, e)` alone
(`HJO.ParkingFunctions.mul_add_pos_iff`), as is the window condition `0 < M D + e < M a`
(`HJO.ParkingFunctions.mul_add_mem_window_iff`). Applying the second at `M` and at `M'` with the
*same* `(D, e)` is what makes the temporary dinv agree; applying the first is what makes the rank
order reverse.

## Main results

* `HJO.ParkingFunctions.halfTurnPfEquiv`: the half turn is a bijection from the parking functions
  onto the above-diagonal ones (`HJO.ParkingFunctions.halfTurnPfEquiv`,
  `HJO.ParkingFunctions.filter_abovePath_eq_image`), and it matches return composition `α.reverse`
  with `α` (`HJO.ParkingFunctions.mem_aboveWithReturns_halfTurnPf`).
* `HJO.ParkingFunctions.aboveTdinv_halfTurnPf`, `aboveMaxTdinv_halfTurn`,
  `aboveDinv_halfTurnPf`: the three dinv statistics are preserved.
* `HJO.ParkingFunctions.aboveIdes_halfTurnPf`: the inverse descent set is *complemented*,
  `ideŝ(π̂) = ides(π)^{∨bN}`.

## Implementation notes

`AboveReadBefore` breaks ties upwards and `ReadBefore` downwards, so the two reading orders are
exact mirrors of each other only once the tie-breaks are known to be vacuous. They are, for
`0 < a`: `HJO.ParkingFunctions.stepRank_injective` is `HJO.ParkingFunctions.stepRank_injective` at
`M = aN+1`, and the above-diagonal case at `M = (aN+1)N` is got from it through
`HJO.ParkingFunctions.aboveStepRank_halfTurnPf_eq_iff`. Every statement below that mentions a
reading word therefore carries `0 < a` and `0 < N`, which the standing conventions
supply.

## References

This file concerns the definition `HJO.ParkingFunctions.halfTurnPf` and the lemmas
`HJO.ParkingFunctions.mul_add_pos_iff`, `HJO.ParkingFunctions.mul_add_eq_zero_iff`,
`HJO.ParkingFunctions.mul_add_mem_window_iff`, `HJO.ParkingFunctions.aboveStepRank_halfTurnPf`,
`HJO.ParkingFunctions.aboveStepRank_halfTurnPf_lt_iff`,
`HJO.ParkingFunctions.aboveTdinv_halfTurnPf`, `HJO.ParkingFunctions.aboveMaxTdinv_halfTurn`,
`HJO.ParkingFunctions.aboveDinv_halfTurnPf`, `HJO.ParkingFunctions.stepRank_injective`,
`HJO.ParkingFunctions.aboveReadingWord_halfTurnPf`, `HJO.ParkingFunctions.aboveIdes_halfTurnPf`,
`HJO.ParkingFunctions.aboveColumn_halfTurn`, `HJO.ParkingFunctions.halfTurnPfEquiv`,
`HJO.ParkingFunctions.filter_abovePath_eq_image` and
`HJO.ParkingFunctions.mem_aboveWithReturns_halfTurnPf`.
-/

@[expose] public section

open Finset

namespace HJO.ParkingFunctions

/-! ### The sign of a coarse offset

Every rank in play is `M D + e` with `M > aN` and `|e| ≤ aN`, the coarse part `D` being a
difference of diagonal offsets and the fine part `e` a difference of abscissae. The three lemmas
here say that the sign, the vanishing and the window membership of such a quantity depend on
`(D, e)` and not on `M`. That is the whole content of "the half turn preserves the comparisons but
not the rank".
-/

section RankArithmetic

variable {c M D e A : ℤ}

/-- **The sign of a coarse offset.** For `c < M` and `|e| ≤ c`, the quantity `M D + e` is positive
exactly when `D ≥ 1`, or `D = 0` and `e > 0`. -/
@[hjo "lem_rank_offset_sign"]
theorem mul_add_pos_iff (hM : c < M) (he₁ : -c ≤ e) (he₂ : e ≤ c) :
    0 < M * D + e ↔ (1 ≤ D ∨ (D = 0 ∧ 0 < e)) := by
  have hc : 0 ≤ c := by linarith
  constructor
  · intro h
    rcases lt_trichotomy D 0 with hD | hD | hD
    · exfalso
      have h1 : M * (D + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      nlinarith
    · exact Or.inr ⟨hD, by simpa [hD] using h⟩
    · exact Or.inl hD
  · rintro (hD | ⟨rfl, he⟩)
    · have h1 : 0 ≤ M * (D - 1) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    · simpa using he

/-- **A vanishing coarse offset.** For `c < M` and `|e| ≤ c`, the quantity `M D + e` vanishes
exactly when both parts do. -/
@[hjo "lem_rank_offset_zero"]
theorem mul_add_eq_zero_iff (hM : c < M) (he₁ : -c ≤ e) (he₂ : e ≤ c) :
    M * D + e = 0 ↔ (D = 0 ∧ e = 0) := by
  refine ⟨fun h => ?_, fun ⟨hD, he⟩ => by rw [hD, he]; ring⟩
  have h1 := (mul_add_pos_iff (D := D) (e := e) hM he₁ he₂).not
  have h2 := (mul_add_pos_iff (D := -D) (e := -e) hM (by linarith) (by linarith)).not
  have h3 : ¬ (0 < M * D + e) := by omega
  have h4 : ¬ (0 < M * (-D) + -e) := by
    have : M * (-D) + -e = -(M * D + e) := by ring
    rw [this, h]; omega
  have h5 := h1.1 h3
  have h6 := h2.1 h4
  omega

/-- **The rank window in terms of the diagonal offset.** For `1 ≤ A`, `c < M` and `|e| ≤ c`, the
window condition `0 < M D + e < M A` is one and the same condition on `(D, e)` for every such `M`:
either `1 ≤ D ≤ A - 1`, or `D = 0` with `e > 0`, or `D = A` with `e < 0`. -/
@[hjo "lem_rank_window_criterion"]
theorem mul_add_mem_window_iff (hA : 1 ≤ A) (hM : c < M) (he₁ : -c ≤ e) (he₂ : e ≤ c) :
    (0 < M * D + e ∧ M * D + e < M * A) ↔
      ((1 ≤ D ∧ D ≤ A - 1) ∨ (D = 0 ∧ 0 < e) ∨ (D = A ∧ e < 0)) := by
  have hleft := mul_add_pos_iff (c := c) (M := M) (D := D) (e := e) hM he₁ he₂
  have hright := mul_add_pos_iff (c := c) (M := M) (D := A - D) (e := -e) hM
    (by linarith) (by linarith)
  have hrw : M * D + e < M * A ↔ 0 < M * (A - D) + -e := by
    constructor <;> intro h <;> nlinarith [mul_sub M A D]
  rw [hrw, hleft, hright]
  omega

end RankArithmetic

/-! ### The half turn on the columns of the north steps -/

variable {a b N : ℕ}

theorem isBelowDiagonal_path (π : ParkingFunction a b N) : Paths.IsBelowDiagonal (path π) := π.2.1

theorem isParkingLabelling_path (π : ParkingFunction a b N) :
    IsParkingLabelling (path π) (label π) := π.2.2

theorem isAboveDiagonal_abovePath (π : AboveParkingFunction a b N) :
    Paths.IsAboveDiagonal (abovePath π) := π.2.1

theorem isAboveParkingLabelling_abovePath (π : AboveParkingFunction a b N) :
    IsAboveParkingLabelling (abovePath π) (aboveLabel π) := π.2.2

@[simp]
theorem label_labelStep (π : ParkingFunction a b N) (i : Fin (b * N)) :
    label π (labelStep π i) = i :=
  Fintype.rightInverse_bijInv _ i

@[simp]
theorem labelStep_label (π : ParkingFunction a b N) (s : Fin (b * N)) :
    labelStep π (label π s) = s :=
  Fintype.leftInverse_bijInv _ s

theorem column_le (y : Paths.Heights a b N) (s : ℕ) : column y s ≤ a * N := by
  have := ReturnPath.firstReach_lt y (s + 1); rw [column]; omega

theorem aboveColumn_le (y : Paths.Heights a b N) (i : ℕ) : aboveColumn y i ≤ a * N :=
  Paths.lastBelow_le y (i + 1)

/-- **The half turn on north steps.** The north step of `P` whose foot is at height `s` goes to the
north step of `P̂` whose foot is at height `bN - 1 - s`, and its column `x` goes to `aN - x`. -/
@[hjo "lem_half_turn_steps"]
theorem aboveColumn_halfTurn {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    (i : Fin (b * N)) :
    aboveColumn (Paths.halfTurn y) (i : ℕ) = a * N - column y (i.rev : ℕ) := by
  have hi := i.isLt
  have hrev : (i.rev : ℕ) = b * N - 1 - (i : ℕ) := by rw [Fin.val_rev]; omega
  have hj : b * N + 1 - (b * N - (i : ℕ)) = (i : ℕ) + 1 := by omega
  rw [aboveColumn, column, hrev, ← hj,
    Paths.lastBelow_halfTurn hy (i := b * N - (i : ℕ)) (by omega) (by omega)]
  congr 2
  omega

/-- The same statement read in the other direction, which is what makes the inverse half turn of an
above-diagonal parking function legal. -/
theorem column_halfTurn {y : Paths.Heights a b N} (hy : Paths.IsAboveDiagonal y)
    (s : Fin (b * N)) :
    column (Paths.halfTurn y) (s : ℕ) = a * N - aboveColumn y (s.rev : ℕ) := by
  have h := aboveColumn_halfTurn (Paths.isBelowDiagonal_halfTurn hy) s.rev
  rw [Paths.halfTurn_halfTurn, Fin.rev_rev] at h
  have h1 := column_le (Paths.halfTurn y) (s : ℕ)
  have h2 := aboveColumn_le y (s.rev : ℕ)
  omega

/-! ### The half turn of a parking function -/

/-- **The half turn of a parking function.** The north step `(x, y)` of `P_π` carrying the label `ℓ`
goes to the north step `(aN - x, bN - y - 1)` of `P̂`, carrying the label `bN + 1 - ℓ`. On the
`Fin (bN)`-indexed encoding both reflections are `Fin.rev`, and the complementation of the label is
what turns increase-upwards into increase-upwards again: the column order and the label order are
both reversed. -/
@[hjo "def_half_turn_pf"]
def halfTurnPf (π : ParkingFunction a b N) : AboveParkingFunction a b N :=
  ⟨(Paths.halfTurn (path π), fun i => (label π i.rev).rev), by
    refine ⟨Paths.isAboveDiagonal_halfTurn (isBelowDiagonal_path π), Fin.rev_bijective.comp
      ((bijective_label π).comp Fin.rev_bijective), fun s t hst hcol => ?_⟩
    have hcol' : aboveColumn (Paths.halfTurn (path π)) (s : ℕ)
        = aboveColumn (Paths.halfTurn (path π)) (t : ℕ) := hcol
    rw [aboveColumn_halfTurn (isBelowDiagonal_path π) s,
      aboveColumn_halfTurn (isBelowDiagonal_path π) t] at hcol'
    have h1 := column_le (path π) (s.rev : ℕ)
    have h2 := column_le (path π) (t.rev : ℕ)
    change (label π s.rev).rev < (label π t.rev).rev
    exact Fin.rev_lt_rev.2
      ((isParkingLabelling_path π).2 t.rev s.rev (Fin.rev_lt_rev.2 hst) (by omega))⟩

/-- The inverse half turn, on an above-diagonal parking function. -/
def halfTurnPfInv (π : AboveParkingFunction a b N) : ParkingFunction a b N :=
  ⟨(Paths.halfTurn (abovePath π), fun s => (aboveLabel π s.rev).rev), by
    refine ⟨Paths.isBelowDiagonal_halfTurn (isAboveDiagonal_abovePath π), Fin.rev_bijective.comp
      ((bijective_aboveLabel π).comp Fin.rev_bijective), fun s t hst hcol => ?_⟩
    have hcol' : column (Paths.halfTurn (abovePath π)) (s : ℕ)
        = column (Paths.halfTurn (abovePath π)) (t : ℕ) := hcol
    rw [column_halfTurn (isAboveDiagonal_abovePath π) s,
      column_halfTurn (isAboveDiagonal_abovePath π) t] at hcol'
    have h1 := aboveColumn_le (abovePath π) (s.rev : ℕ)
    have h2 := aboveColumn_le (abovePath π) (t.rev : ℕ)
    change (aboveLabel π s.rev).rev < (aboveLabel π t.rev).rev
    exact Fin.rev_lt_rev.2
      ((isAboveParkingLabelling_abovePath π).2 t.rev s.rev (Fin.rev_lt_rev.2 hst) (by omega))⟩

@[simp]
theorem abovePath_halfTurnPf (π : ParkingFunction a b N) :
    abovePath (halfTurnPf π) = Paths.halfTurn (path π) := rfl

@[simp]
theorem aboveLabel_halfTurnPf (π : ParkingFunction a b N) (i : Fin (b * N)) :
    aboveLabel (halfTurnPf π) i = (label π i.rev).rev := rfl

@[simp]
theorem path_halfTurnPfInv (π : AboveParkingFunction a b N) :
    path (halfTurnPfInv π) = Paths.halfTurn (abovePath π) := rfl

@[simp]
theorem label_halfTurnPfInv (π : AboveParkingFunction a b N) (s : Fin (b * N)) :
    label (halfTurnPfInv π) s = (aboveLabel π s.rev).rev := rfl

theorem halfTurnPfInv_halfTurnPf (π : ParkingFunction a b N) :
    halfTurnPfInv (halfTurnPf π) = π := by
  refine Subtype.ext (Prod.ext ?_ (funext fun s => ?_))
  · change Paths.halfTurn (Paths.halfTurn (path π)) = path π
    exact Paths.halfTurn_halfTurn (path π)
  · change ((label π s.rev.rev).rev).rev = label π s
    simp

theorem halfTurnPf_halfTurnPfInv (π : AboveParkingFunction a b N) :
    halfTurnPf (halfTurnPfInv π) = π := by
  refine Subtype.ext (Prod.ext ?_ (funext fun i => ?_))
  · change Paths.halfTurn (Paths.halfTurn (abovePath π)) = abovePath π
    exact Paths.halfTurn_halfTurn (abovePath π)
  · change ((aboveLabel π i.rev.rev).rev).rev = aboveLabel π i
    simp

/-- **The half turn is a bijection from the parking functions of the `aN × bN` rectangle onto the
above-diagonal ones**, with `P̂_π̂ = P̂_π` on underlying paths. -/
@[hjo "lem_half_turn_pf_legal"]
def halfTurnPfEquiv : ParkingFunction a b N ≃ AboveParkingFunction a b N where
  toFun := halfTurnPf
  invFun := halfTurnPfInv
  left_inv := halfTurnPfInv_halfTurnPf
  right_inv := halfTurnPf_halfTurnPfInv

theorem aboveLabelStep_halfTurnPf (π : ParkingFunction a b N) (i : Fin (b * N)) :
    aboveLabelStep (halfTurnPf π) i = (labelStep π i.rev).rev := by
  have h : aboveLabel (halfTurnPf π) ((labelStep π i.rev).rev) = i := by
    rw [aboveLabel_halfTurnPf, Fin.rev_rev, label_labelStep, Fin.rev_rev]
  calc aboveLabelStep (halfTurnPf π) i
      = aboveLabelStep (halfTurnPf π)
          (aboveLabel (halfTurnPf π) ((labelStep π i.rev).rev)) := by rw [h]
    _ = (labelStep π i.rev).rev := aboveLabelStep_aboveLabel _ _

/-! ### The half turn reverses the rank order

Both ranks are `M ⬝ (diagonal offset) + (abscissa)`, with `M = aN+1` below the diagonal and
`M = (aN+1)N` above it. The half turn negates the offset up to the constant `-a`
(`HJO.ParkingFunctions.aboveStepRank_halfTurnPf`) and reflects the abscissa, so the *difference* of
two ranks on either side is `M D + e` for one and the same pair `(D, e)`. The comparison is then
decided by `(D, e)` alone.
-/

/-- The diagonal offset `a s - b x` of the north step whose foot is at height `s`, `x` being its
column. Both ranks are `M ⬝ stepOffset + x`. -/
def stepOffset (y : Paths.Heights a b N) (s : ℕ) : ℤ := (a : ℤ) * s - b * column y s

theorem column_cast_nonneg (y : Paths.Heights a b N) (s : ℕ) : (0 : ℤ) ≤ column y s :=
  Int.natCast_nonneg _

theorem column_cast_le (y : Paths.Heights a b N) (s : ℕ) :
    ((column y s : ℤ)) ≤ (a : ℤ) * N := by
  have h : ((column y s : ℕ) : ℤ) ≤ ((a * N : ℕ) : ℤ) := Int.ofNat_le.2 (column_le y s)
  push_cast at h; exact h

theorem stepRank_eq (π : ParkingFunction a b N) (s : Fin (b * N)) :
    stepRank π s
      = ((a : ℤ) * N + 1) * stepOffset (path π) (s : ℕ) + (column (path π) (s : ℕ) : ℤ) := by
  rw [stepRank, pointRank, stepOffset]

/-- **The half turn negates the diagonal offset**, up to the constant `-a`: the above-diagonal rank
of the image of the north step whose foot is at height `s` is
`(aN+1)N(-offset - a) + (aN - x)`. -/
@[hjo "lem_half_turn_offset"]
theorem aboveStepRank_halfTurnPf (π : ParkingFunction a b N) (s : Fin (b * N)) :
    aboveStepRank (halfTurnPf π) s.rev
      = ((a : ℤ) * N + 1) * N * (-stepOffset (path π) (s : ℕ) - a)
        + ((a : ℤ) * N - (column (path π) (s : ℕ) : ℤ)) := by
  have hx := column_le (path π) (s : ℕ)
  have hs := s.isLt
  rw [aboveStepRank, abovePath_halfTurnPf, aboveColumn_halfTurn (isBelowDiagonal_path π) s.rev,
    Fin.rev_rev, abovePointRank, stepOffset]
  have h1 : ((a * N - column (path π) (s : ℕ) : ℕ) : ℤ)
      = (a : ℤ) * N - (column (path π) (s : ℕ) : ℤ) := by
    rw [Nat.cast_sub hx]; push_cast; ring
  have h2 : ((s.rev : ℕ) : ℤ) = (b : ℤ) * N - 1 - (s : ℕ) := by
    rw [Fin.val_rev, Nat.cast_sub (by omega : (s : ℕ) + 1 ≤ b * N)]; push_cast; ring
  rw [h1, h2]
  ring

/-- The difference of two above-diagonal ranks after the half turn, as `M' D + e`. -/
theorem aboveStepRank_halfTurnPf_sub (π : ParkingFunction a b N) (s t : Fin (b * N)) :
    aboveStepRank (halfTurnPf π) s.rev - aboveStepRank (halfTurnPf π) t.rev
      = ((a : ℤ) * N + 1) * N
          * (stepOffset (path π) (t : ℕ) - stepOffset (path π) (s : ℕ))
        + ((column (path π) (t : ℕ) : ℤ) - (column (path π) (s : ℕ) : ℤ)) := by
  rw [aboveStepRank_halfTurnPf, aboveStepRank_halfTurnPf]; ring

/-- The difference of two below-diagonal ranks, as `M D + e` with the *same* `(D, e)`. -/
theorem stepRank_sub (π : ParkingFunction a b N) (s t : Fin (b * N)) :
    stepRank π t - stepRank π s
      = ((a : ℤ) * N + 1)
          * (stepOffset (path π) (t : ℕ) - stepOffset (path π) (s : ℕ))
        + ((column (path π) (t : ℕ) : ℤ) - (column (path π) (s : ℕ) : ℤ)) := by
  rw [stepRank_eq, stepRank_eq]; ring

/-- **The half turn reverses the rank order.** -/
@[hjo "lem_half_turn_rank_order"]
theorem aboveStepRank_halfTurnPf_lt_iff (hN : 0 < N) (π : ParkingFunction a b N)
    (u v : Fin (b * N)) :
    aboveStepRank (halfTurnPf π) u < aboveStepRank (halfTurnPf π) v ↔
      stepRank π v.rev < stepRank π u.rev := by
  have hc1 : (a : ℤ) * N < ((a : ℤ) * N + 1) * N := by
    have h : (1 : ℤ) ≤ N := by exact_mod_cast hN
    have h2 : (0 : ℤ) ≤ (a : ℤ) * N :=
      mul_nonneg (Int.natCast_nonneg a) (Int.natCast_nonneg N)
    nlinarith [mul_nonneg h2 (by linarith : (0 : ℤ) ≤ (N : ℤ) - 1)]
  have hc2 : (a : ℤ) * N < (a : ℤ) * N + 1 := by linarith
  have he₁ : -((a : ℤ) * N)
      ≤ (column (path π) ((u.rev : Fin (b * N)) : ℕ) : ℤ)
        - (column (path π) ((v.rev : Fin (b * N)) : ℕ) : ℤ) := by
    have := column_cast_nonneg (path π) ((u.rev : Fin (b * N)) : ℕ)
    have := column_cast_le (path π) (a := a) (b := b) (N := N) ((v.rev : Fin (b * N)) : ℕ)
    linarith
  have he₂ : (column (path π) ((u.rev : Fin (b * N)) : ℕ) : ℤ)
        - (column (path π) ((v.rev : Fin (b * N)) : ℕ) : ℤ) ≤ (a : ℤ) * N := by
    have := column_cast_nonneg (path π) ((v.rev : Fin (b * N)) : ℕ)
    have := column_cast_le (path π) (a := a) (b := b) (N := N) ((u.rev : Fin (b * N)) : ℕ)
    linarith
  have hP1 := aboveStepRank_halfTurnPf_sub π v.rev u.rev
  have hP2 := stepRank_sub π v.rev u.rev
  rw [Fin.rev_rev, Fin.rev_rev] at hP1
  rw [← sub_pos, hP1, mul_add_pos_iff hc1 he₁ he₂,
    ← mul_add_pos_iff (M := (a : ℤ) * N + 1) hc2 he₁ he₂, ← hP2, sub_pos]

/-- Two ranks whose difference is `M D + e` compare the same way, for every `M > c`. -/
theorem aboveStepRank_halfTurnPf_eq_iff (hN : 0 < N) (π : ParkingFunction a b N)
    (u v : Fin (b * N)) :
    aboveStepRank (halfTurnPf π) u = aboveStepRank (halfTurnPf π) v ↔
      stepRank π u.rev = stepRank π v.rev := by
  have h1 := aboveStepRank_halfTurnPf_lt_iff hN π u v
  have h2 := aboveStepRank_halfTurnPf_lt_iff hN π v u
  omega

/-! ### Ranks of distinct north steps differ -/

/-- **Ranks of distinct north steps differ**, at `M = aN + 1`: for `0 < a` the rank of a north step
determines the step. In particular the tie-breaking clause of `ReadBefore` never fires. -/
@[hjo "lem_rank_injective"]
theorem stepRank_injective (ha : 0 < a) (π : ParkingFunction a b N) :
    Function.Injective (stepRank π) := by
  intro s t h
  have hc2 : (a : ℤ) * N < (a : ℤ) * N + 1 := by linarith
  have he₁ : -((a : ℤ) * N)
      ≤ (column (path π) (t : ℕ) : ℤ) - (column (path π) (s : ℕ) : ℤ) := by
    have := column_cast_nonneg (path π) (t : ℕ)
    have := column_cast_le (path π) (a := a) (b := b) (N := N) (s : ℕ)
    linarith
  have he₂ : (column (path π) (t : ℕ) : ℤ) - (column (path π) (s : ℕ) : ℤ) ≤ (a : ℤ) * N := by
    have := column_cast_nonneg (path π) (s : ℕ)
    have := column_cast_le (path π) (a := a) (b := b) (N := N) (t : ℕ)
    linarith
  have hsub := stepRank_sub π s t
  rw [h, sub_self] at hsub
  obtain ⟨hD, he⟩ := (mul_add_eq_zero_iff hc2 he₁ he₂).1 hsub.symm
  have hcol : (column (path π) (t : ℕ) : ℤ) = (column (path π) (s : ℕ) : ℤ) := by linarith
  rw [stepOffset, stepOffset, hcol] at hD
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have h3 : (a : ℤ) * ((t : ℕ) : ℤ) = (a : ℤ) * ((s : ℕ) : ℤ) := by linarith
  exact Fin.ext (by exact_mod_cast (mul_left_cancel₀ (ne_of_gt ha') h3).symm)

/-- **The half turn reverses the reading order.** Both tie-breaking clauses are vacuous, so the
order `AboveReadBefore` of `π̂` is the order `ReadBefore` of `π` read through `Fin.rev` and
reversed. -/
theorem aboveReadBefore_halfTurnPf_iff (ha : 0 < a) (hN : 0 < N) (π : ParkingFunction a b N)
    (s t : Fin (b * N)) :
    AboveReadBefore (halfTurnPf π) s t ↔ ReadBefore π t.rev s.rev := by
  have hinj := stepRank_injective ha π
  rw [AboveReadBefore, ReadBefore, aboveStepRank_halfTurnPf_lt_iff hN,
    aboveStepRank_halfTurnPf_eq_iff hN]
  constructor
  · rintro (h | ⟨h, hlt⟩)
    · exact Or.inl h
    · exact absurd (Fin.rev_inj.1 (hinj h)) (ne_of_lt hlt)
  · rintro (h | ⟨h, hlt⟩)
    · exact Or.inl h
    · exact absurd (hinj h.symm) (ne_of_lt hlt)

/-! ### The half turn preserves the three dinv statistics -/

/-- Two rank windows whose differences are `M₁ D + e` and `M₂ D + e` for one and the same `(D, e)`
select the same pairs, whenever both `M₁` and `M₂` exceed the bound `c` on `|e|`. -/
private theorem window_transfer {c M₁ M₂ A D e As At Bs Bt : ℤ} (hA : 1 ≤ A) (hc₁ : c < M₁)
    (hc₂ : c < M₂) (he₁ : -c ≤ e) (he₂ : e ≤ c) (h₁ : As - At = M₁ * D + e)
    (h₂ : Bt - Bs = M₂ * D + e) :
    (At < As ∧ As < At + M₁ * A) ↔ (Bs < Bt ∧ Bt < Bs + M₂ * A) := by
  have hw₁ := mul_add_mem_window_iff (A := A) (c := c) (M := M₁) (D := D) (e := e) hA hc₁ he₁ he₂
  have hw₂ := mul_add_mem_window_iff (A := A) (c := c) (M := M₂) (D := D) (e := e) hA hc₂ he₁ he₂
  constructor
  · rintro ⟨p₁, p₂⟩
    obtain ⟨q₁, q₂⟩ := hw₂.2 (hw₁.1 ⟨by linarith, by linarith⟩)
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨p₁, p₂⟩
    obtain ⟨q₁, q₂⟩ := hw₁.2 (hw₂.1 ⟨by linarith, by linarith⟩)
    exact ⟨by linarith, by linarith⟩

theorem aboveLabelRank_halfTurnPf (π : ParkingFunction a b N) (m : Fin (b * N)) :
    aboveLabelRank (halfTurnPf π) m
      = aboveStepRank (halfTurnPf π) ((labelStep π m.rev).rev) := by
  rw [aboveLabelRank, aboveLabelStep_halfTurnPf]

/-- The window condition of `aboveTdinv` at the pair `(i, j)` and the window condition of `tdinv`
at the pair `(j.rev, i.rev)` are the same condition. -/
theorem tdinv_window_iff (ha : 0 < a) (hN : 0 < N) (π : ParkingFunction a b N)
    (i j : Fin (b * N)) :
    (aboveLabelRank (halfTurnPf π) i < aboveLabelRank (halfTurnPf π) j ∧
        aboveLabelRank (halfTurnPf π) j
          < aboveLabelRank (halfTurnPf π) i + ((a : ℤ) * N + 1) * ((a : ℤ) * N))
      ↔ (labelRank π j.rev < labelRank π i.rev ∧
          labelRank π i.rev < labelRank π j.rev + ((a : ℤ) * N + 1) * (a : ℤ)) := by
  have hc₁ : (a : ℤ) * N < ((a : ℤ) * N + 1) * N := by
    have h : (1 : ℤ) ≤ N := by exact_mod_cast hN
    have h2 : (0 : ℤ) ≤ (a : ℤ) * N :=
      mul_nonneg (Int.natCast_nonneg a) (Int.natCast_nonneg N)
    nlinarith [mul_nonneg h2 (by linarith : (0 : ℤ) ≤ (N : ℤ) - 1)]
  have hc₂ : (a : ℤ) * N < (a : ℤ) * N + 1 := by linarith
  have hA : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have he₁ : -((a : ℤ) * N)
      ≤ (column (path π) ((labelStep π i.rev : Fin (b * N)) : ℕ) : ℤ)
        - (column (path π) ((labelStep π j.rev : Fin (b * N)) : ℕ) : ℤ) := by
    have := column_cast_nonneg (path π) ((labelStep π i.rev : Fin (b * N)) : ℕ)
    have := column_cast_le (path π) (a := a) (b := b) (N := N)
      ((labelStep π j.rev : Fin (b * N)) : ℕ)
    linarith
  have he₂ : (column (path π) ((labelStep π i.rev : Fin (b * N)) : ℕ) : ℤ)
        - (column (path π) ((labelStep π j.rev : Fin (b * N)) : ℕ) : ℤ) ≤ (a : ℤ) * N := by
    have := column_cast_nonneg (path π) ((labelStep π j.rev : Fin (b * N)) : ℕ)
    have := column_cast_le (path π) (a := a) (b := b) (N := N)
      ((labelStep π i.rev : Fin (b * N)) : ℕ)
    linarith
  rw [aboveLabelRank_halfTurnPf, aboveLabelRank_halfTurnPf, labelRank, labelRank,
    show ((a : ℤ) * N + 1) * ((a : ℤ) * N) = (((a : ℤ) * N + 1) * N) * (a : ℤ) from by ring]
  exact window_transfer hA hc₁ hc₂ he₁ he₂
    (aboveStepRank_halfTurnPf_sub π (labelStep π j.rev) (labelStep π i.rev))
    (stepRank_sub π (labelStep π j.rev) (labelStep π i.rev))

/-- **The half turn preserves temporary dinv**: `tdinv̂(π̂) = tdinv(π)`. The bijection of label
pairs is `(i, j) ↦ (j^∨, i^∨)`, which reverses the order of a pair and carries the above-diagonal
window onto the below-diagonal one. -/
@[hjo "lem_half_turn_tdinv"]
theorem aboveTdinv_halfTurnPf (ha : 0 < a) (hN : 0 < N) (π : ParkingFunction a b N) :
    aboveTdinv (halfTurnPf π) = tdinv π := by
  rw [aboveTdinv, tdinv]
  refine Finset.card_nbij' (fun p => (p.2.rev, p.1.rev)) (fun q => (q.2.rev, q.1.rev))
    (fun p hp => ?_) (fun q hq => ?_) (fun p _ => ?_) (fun q _ => ?_)
  · simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨Fin.rev_lt_rev.2 hp.1, (tdinv_window_iff ha hN π p.1 p.2).1 hp.2⟩
  · simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hq ⊢
    refine ⟨Fin.rev_lt_rev.2 hq.1, (tdinv_window_iff ha hN π q.2.rev q.1.rev).2 ?_⟩
    rw [Fin.rev_rev, Fin.rev_rev]
    exact hq.2
  · simp
  · simp

/-- **The half turn is a bijection from the parking functions with underlying path `P` onto the
above-diagonal parking functions with underlying path `P̂`**, here in the form the maximum over that
fibre needs: the fibre above `P̂` is the image of the fibre above `P` under the half turn. -/
@[hjo "lem_half_turn_pf_path_bij"]
theorem filter_abovePath_eq_image (y : Paths.Heights a b N) :
    ((univ : Finset (AboveParkingFunction a b N)).filter
        fun π => abovePath π = Paths.halfTurn y)
      = ((univ : Finset (ParkingFunction a b N)).filter fun π => path π = y).image
          halfTurnPf := by
  ext π
  simp only [mem_filter, mem_univ, true_and, mem_image]
  constructor
  · intro h
    refine ⟨halfTurnPfInv π, ?_, halfTurnPf_halfTurnPfInv π⟩
    rw [path_halfTurnPfInv, h, Paths.halfTurn_halfTurn]
  · rintro ⟨π', h, rfl⟩
    rw [abovePath_halfTurnPf, h]

/-- **The half turn preserves maximal temporary dinv.** -/
@[hjo "lem_half_turn_maxtdinv"]
theorem aboveMaxTdinv_halfTurn (ha : 0 < a) (hN : 0 < N) (y : Paths.Heights a b N) :
    aboveMaxTdinv (Paths.halfTurn y) = maxTdinv y := by
  rw [aboveMaxTdinv, maxTdinv, filter_abovePath_eq_image, Finset.sup_image]
  exact Finset.sup_congr rfl fun π _ => aboveTdinv_halfTurnPf ha hN π

/-- **The half turn preserves dinv**: `dinv̂(π̂) = dinv(π)`. -/
@[hjo "lem_half_turn_dinv"]
theorem aboveDinv_halfTurnPf (ha : 0 < a) (hN : 0 < N) (π : ParkingFunction a b N) :
    aboveDinv (halfTurnPf π) = dinv π := by
  rw [aboveDinv, dinv, abovePath_halfTurnPf,
    Paths.aboveHookCount_halfTurn (isBelowDiagonal_path π),
    aboveTdinv_halfTurnPf ha hN, aboveMaxTdinv_halfTurn ha hN]

/-! ### The half turn matches the reversed composition -/

/-- **The half turn is a bijection from `PF^{α^rev}` onto `PF̂^{α}`.** The reversal of the
composition is forced here, by `HJO.Paths.hasAboveReturns_halfTurn`; it is not an adjustment. -/
@[hjo "lem_half_turn_pf_bij"]
theorem mem_aboveWithReturns_halfTurnPf (α : List ℕ) (π : ParkingFunction a b N) :
    halfTurnPf π ∈ aboveWithReturns α a b N ↔ π ∈ withReturns α.reverse a b N := by
  rw [aboveWithReturns, withReturns, mem_filter, mem_filter]
  simp only [mem_univ, true_and, abovePath_halfTurnPf]
  rw [← List.reverse_reverse α, Paths.hasAboveReturns_halfTurn, List.reverse_reverse]

end HJO.ParkingFunctions
