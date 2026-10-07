/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.RankOneDinv.Basic
public import HJO.Shuffle.AboveParking
public meta import HJO.Attr

/-! # The half turn of the rectangle, on paths

The half turn of the `aN × bN` rectangle sends `(x, y)` to `(aN - x, bN - y)`. On the height
sequence of a path this is `y_r ↦ bN - y_{aN - r}`, which on the encoding
`HJO.Paths.Heights a b N = Fin (aN+1) → Fin (bN+1)` is `Fin.rev` on both the source and the target:
`halfTurn y = fun r => (y r.rev).rev`. It is therefore an involution for free, and the
below-diagonal and above-diagonal paths are exchanged by it.

This file carries the path half of the half turn: that it is an involution exchanging the two
orientations, that it preserves the area, that it reverses the return composition, and that it
carries the cells below a path to the cells above its image with the arm and the leg unchanged, so
that the hook count is preserved.

## Main results

* `HJO.Paths.halfTurn_halfTurn`, `HJO.Paths.isAboveDiagonal_halfTurn`: the half turn is an
  involution carrying the below-diagonal paths onto the above-diagonal ones, hence a bijection
  between them (`HJO.Paths.halfTurn_bijOn`).
* `HJO.Paths.aboveArea_halfTurn`: `âea(P̂) = area(P)`.
* `HJO.Paths.hasAboveReturns_halfTurn`: the return composition is *reversed*.
* `HJO.Paths.aboveHookCount_halfTurn`: `ĥ(P̂) = h(P)`.

## References

Part of the proof of the compositional rational shuffle identity: Definition `HJO.Paths.halfTurn`
and Lemmas `HJO.Paths.isAboveDiagonal_halfTurn`, `HJO.Paths.halfTurn_bijOn`,
`HJO.Paths.aboveArea_halfTurn`, `HJO.Comp.reverse_reverse`, `HJO.Paths.hasAboveReturns_halfTurn`,
`HJO.Paths.mem_aboveCells_halfTurn`, `HJO.Paths.aboveArm_halfTurn`, `HJO.Paths.aboveLeg_halfTurn`,
`HJO.Paths.aboveHookCount_halfTurn`.
-/

@[expose] public section

open Finset

/-! ### Two facts about prefix sums -/

/-- Membership in the list of prefix sums of `l` offset by `c`: the members are exactly the
`c + (take m l).sum`. -/
private theorem List.mem_scanl_add_iff (l : List ℕ) (c k : ℕ) :
    k ∈ l.scanl (· + ·) c ↔ ∃ m ≤ l.length, c + (l.take m).sum = k := by
  induction l generalizing c with
  | nil => simp; omega
  | cons x l ih =>
    rw [List.scanl_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨m, hm, hsum⟩)
      · exact ⟨0, Nat.zero_le _, by simp⟩
      · refine ⟨m + 1, by simpa using hm, ?_⟩
        simp only [List.take_succ_cons, List.sum_cons]; omega
    · rintro ⟨m, hm, hsum⟩
      match m with
      | 0 => simp at hsum; omega
      | (m + 1) =>
        refine Or.inr ⟨m, by simpa using hm, ?_⟩
        simp only [List.take_succ_cons, List.sum_cons] at hsum; omega

/-- Reversing a list reflects its prefix sums in the total: for `k ≤ l.sum`, the value `k` is a
prefix sum of `l.reverse` exactly when `l.sum - k` is a prefix sum of `l`. This is what makes the
half turn *reverse* the return composition. -/
private theorem List.mem_scanl_reverse_iff (l : List ℕ) {k : ℕ} (hk : k ≤ l.sum) :
    k ∈ l.reverse.scanl (· + ·) 0 ↔ l.sum - k ∈ l.scanl (· + ·) 0 := by
  rw [List.mem_scanl_add_iff, List.mem_scanl_add_iff, List.length_reverse]
  constructor
  · rintro ⟨m, hm, hsum⟩
    refine ⟨l.length - m, by omega, ?_⟩
    rw [List.take_reverse, List.sum_reverse] at hsum
    have h1 : (l.take (l.length - m)).sum + (l.drop (l.length - m)).sum = l.sum := by
      conv_rhs => rw [← List.take_append_drop (l.length - m) l]
      rw [List.sum_append]
    omega
  · rintro ⟨m, hm, hsum⟩
    refine ⟨l.length - m, by omega, ?_⟩
    rw [List.take_reverse, List.sum_reverse]
    have h1 : (l.take m).sum + (l.drop m).sum = l.sum := by
      conv_rhs => rw [← List.take_append_drop m l]
      rw [List.sum_append]
    have h2 : l.length - (l.length - m) = m := by omega
    rw [h2]; omega

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### The half turn of a path -/

/-- The half turn `P ↦ P̂` of the `aN × bN` rectangle, read on height vectors:
`ŷ_r = bN - y_{aN-r}`. On the encoding `Heights a b N = Fin (aN+1) → Fin (bN+1)` this is
`Fin.rev` on the abscissa and `Fin.rev` on the height, so it is manifestly an involution. -/
@[hjo "def_half_turn_path"]
def halfTurn (y : Heights a b N) : Heights a b N := fun r => (y r.rev).rev

@[simp]
theorem halfTurn_halfTurn (y : Heights a b N) : halfTurn (halfTurn y) = y := by
  funext r; simp [halfTurn]

theorem halfTurn_involutive : Function.Involutive (halfTurn (a := a) (b := b) (N := N)) :=
  halfTurn_halfTurn

theorem halfTurn_bijective : Function.Bijective (halfTurn (a := a) (b := b) (N := N)) :=
  halfTurn_involutive.bijective

/-- The heights of the half turn, read through `ht`: `ŷ_r = bN - y_{aN-r}` on the rectangle. -/
theorem ht_halfTurn {y : Heights a b N} {r : ℕ} (hr : r ≤ a * N) :
    ht (halfTurn y) r = b * N - ht y (a * N - r) := by
  have h1 : r < a * N + 1 := by omega
  have h2 : a * N - r < a * N + 1 := by omega
  have hrev : (⟨r, h1⟩ : Fin (a * N + 1)).rev = ⟨a * N - r, h2⟩ := by
    ext; simp only [Fin.val_rev]; omega
  rw [ht, dite_eq_left h1, ht, dite_eq_left h2, halfTurn, hrev, Fin.val_rev]
  have := (y ⟨a * N - r, h2⟩).isLt
  omega

/-! ### The half turn exchanges the two orientations -/

/-- **The half turn of a below-diagonal path is an above-diagonal path.** -/
@[hjo "lem_half_turn_path_above"]
theorem isAboveDiagonal_halfTurn {y : Heights a b N} (hy : IsBelowDiagonal y) :
    IsAboveDiagonal (halfTurn y) := by
  obtain ⟨h0, hend, hmono, hdiag⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht_halfTurn (Nat.zero_le _), Nat.sub_zero, hend, Nat.sub_self]
  · rw [ht_halfTurn le_rfl, Nat.sub_self, h0, Nat.sub_zero]
  · intro r hr
    rw [ht_halfTurn (by omega), ht_halfTurn (by omega)]
    have h : a * N - r = (a * N - (r + 1)) + 1 := by omega
    have := hmono (a * N - (r + 1)) (by omega)
    rw [← h] at this
    omega
  · intro r hr
    rw [ht_halfTurn hr, Nat.mul_sub]
    have h1 : a * ht y (a * N - r) ≤ b * (a * N - r) := hdiag _ (by omega)
    have h2 : b * (a * N - r) = b * (a * N) - b * r := by rw [Nat.mul_sub]
    have h3 : b * r ≤ b * (a * N) := Nat.mul_le_mul_left _ hr
    have h4 : b * (a * N) = a * (b * N) := by ring
    omega

/-- The half turn of an above-diagonal path is a below-diagonal path: the same computation read in
the other direction, which with `halfTurn_halfTurn` is the surjectivity half of
`HJO.Paths.halfTurn_bijOn`. -/
theorem isBelowDiagonal_halfTurn {y : Heights a b N} (hy : IsAboveDiagonal y) :
    IsBelowDiagonal (halfTurn y) := by
  obtain ⟨h0, hend, hmono, hdiag⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht_halfTurn (Nat.zero_le _), Nat.sub_zero, hend, Nat.sub_self]
  · rw [ht_halfTurn le_rfl, Nat.sub_self, h0, Nat.sub_zero]
  · intro r hr
    rw [ht_halfTurn (by omega), ht_halfTurn (by omega)]
    have h : a * N - r = (a * N - (r + 1)) + 1 := by omega
    have := hmono (a * N - (r + 1)) (by omega)
    rw [← h] at this
    omega
  · intro r hr
    rw [ht_halfTurn hr, Nat.mul_sub]
    have h1 : b * (a * N - r) ≤ a * ht y (a * N - r) := hdiag _ (by omega)
    have h2 : b * (a * N - r) = b * (a * N) - b * r := by rw [Nat.mul_sub]
    have h3 : b * r ≤ b * (a * N) := Nat.mul_le_mul_left _ hr
    have h4 : b * (a * N) = a * (b * N) := by ring
    have h5 : a * ht y (a * N - r) ≤ a * (b * N) :=
      Nat.mul_le_mul_left _ (ht_le_mul y _)
    omega

/-- The half turn is a below-diagonal path exactly when its argument is above-diagonal, and
conversely. -/
theorem isAboveDiagonal_halfTurn_iff {y : Heights a b N} :
    IsAboveDiagonal (halfTurn y) ↔ IsBelowDiagonal y :=
  ⟨fun h => by simpa using isBelowDiagonal_halfTurn h, isAboveDiagonal_halfTurn⟩

/-- **The half turn is a bijection from the below-diagonal `(aN, bN)`-paths onto the
above-diagonal ones.** -/
@[hjo "lem_half_turn_path_bij"]
theorem halfTurn_bijOn :
    Set.BijOn (halfTurn (a := a) (b := b) (N := N)) {y | IsBelowDiagonal y}
      {y | IsAboveDiagonal y} := by
  refine ⟨fun y hy => isAboveDiagonal_halfTurn hy, halfTurn_bijective.injective.injOn, ?_⟩
  intro y hy
  exact ⟨halfTurn y, isBelowDiagonal_halfTurn hy, halfTurn_halfTurn y⟩

/-! ### The half turn preserves the area -/

/-- **The half turn preserves the area**: `âea(P̂) = area(P)`. The `r`-th summand above the image
is the `(aN-r)`-th summand below the original, by `Nat.mul_sub_div_add_mul_ceilDiv`, and
`r ↦ aN - r` is an involution of `{1, …, aN-1}`. -/
@[hjo "lem_half_turn_area"]
theorem aboveArea_halfTurn (y : Heights a b N) : aboveArea (halfTurn y) = area y := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [aboveArea, area]
  rw [aboveArea, area]
  refine Finset.sum_nbij' (fun r => a * N - r) (fun s => a * N - s)
    (fun r hr => ?_) (fun s hs => ?_) (fun r hr => ?_) (fun s hs => ?_) (fun r hr => ?_)
  · rw [mem_Ico] at hr ⊢; omega
  · rw [mem_Ico] at hs ⊢; omega
  · rw [mem_Ico] at hr; omega
  · rw [mem_Ico] at hs; omega
  · rw [mem_Ico] at hr
    rw [ht_halfTurn (by omega)]
    have hfc := Nat.mul_sub_div_add_mul_ceilDiv (a := a) (b := b) (N := N) (r := r) ha (by omega)
    have := ht_le_mul y (a * N - r)
    omega

/-! ### The half turn reverses the return composition -/

/-- **The half turn reverses the return composition**: `P` has return composition `α` exactly when
`P̂` has return composition `α.reverse`. This reversal is *forced*, at
the first step of the derivation of `HJO.External.Shuffle`, and is not an adjustment made to fit the
later statements. -/
@[hjo "lem_half_turn_returns"]
theorem hasAboveReturns_halfTurn {α : List ℕ} {y : Heights a b N} :
    HasAboveReturns α.reverse (halfTurn y) ↔ HasReturns α y := by
  unfold HasAboveReturns HasReturns
  rw [isAboveDiagonal_halfTurn_iff]
  simp only [List.mem_reverse, List.sum_reverse]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun hsum => ?_
  have key : ∀ k ≤ N,
      (ht (halfTurn y) (a * k) = b * k ↔ ht y (a * (N - k)) = b * (N - k)) := by
    intro k hk
    rw [ht_halfTurn (Nat.mul_le_mul_left _ hk)]
    have hsub : a * N - a * k = a * (N - k) := by rw [Nat.mul_sub]
    rw [hsub]
    have hle := ht_le_mul y (a * (N - k))
    have hb : b * (N - k) = b * N - b * k := by rw [Nat.mul_sub]
    have hbk : b * k ≤ b * N := Nat.mul_le_mul_left _ hk
    omega
  have rev : ∀ k ≤ N,
      (k ∈ α.reverse.scanl (· + ·) 0 ↔ N - k ∈ α.scanl (· + ·) 0) := by
    intro k hk
    rw [List.mem_scanl_reverse_iff α (by omega), hsum]
  constructor
  · intro h j hj
    have h' := h (N - j) (by omega)
    rw [key _ (by omega), rev _ (by omega)] at h'
    have hj' : N - (N - j) = j := by omega
    rwa [hj'] at h'
  · intro h k hk
    rw [key _ hk, rev _ hk]
    exact h (N - k) (by omega)

/-! ### The half turn on the diagram of a path

The half turn carries the cell `(r, i)` below `P` to the cell `(aN - r, bN + 1 - i)` above `P̂`,
and the row-length maximum `Â` of the image is the reflection `aN - A` of the row-start minimum
`A` of the original. Both the arm and the leg are therefore unchanged, and since the hook
condition is literally the same pair of inequalities on the two sides, the hook count is
unchanged.
-/

/-- The reflected row bound: `Â_{bN+1-i}` of the half turn is `aN - A_i`. The maximum on the left
and the minimum on the right are taken over sets exchanged by `s ↦ aN - s`. -/
theorem lastBelow_halfTurn {y : Heights a b N} (hy : IsBelowDiagonal y) {i : ℕ}
    (_hi1 : 1 ≤ i) (hi : i ≤ b * N) :
    lastBelow (halfTurn y) (b * N + 1 - i) = a * N - firstReach y i := by
  have hPiff : ∀ s ≤ a * N, (ht (halfTurn y) s < b * N + 1 - i ↔ i ≤ ht y (a * N - s)) := by
    intro s hs
    rw [ht_halfTurn hs]
    have := ht_le_mul y (a * N - s)
    omega
  have hfrle : firstReach y i ≤ a * N := by have := ReturnPath.firstReach_lt y i; omega
  have hfr : i ≤ ht y (firstReach y i) :=
    ReturnPath.le_ht_firstReach y (by rw [hy.2.1]; exact hi)
  have hlow : a * N - firstReach y i ≤ lastBelow (halfTurn y) (b * N + 1 - i) := by
    refine le_lastBelow (by omega) ?_
    rw [hPiff _ (by omega)]
    have h : a * N - (a * N - firstReach y i) = firstReach y i := by omega
    rw [h]; exact hfr
  have hup : lastBelow (halfTurn y) (b * N + 1 - i) ≤ a * N - firstReach y i := by
    have hle := lastBelow_le (halfTurn y) (b * N + 1 - i)
    have hspec := (isAboveDiagonal_halfTurn hy).ht_lastBelow_lt (j := b * N + 1 - i) (by omega)
    exact Nat.le_sub_of_add_le (by
      have := ReturnPath.firstReach_le y (i := i)
        (r := a * N - lastBelow (halfTurn y) (b * N + 1 - i)) (by omega)
        ((hPiff _ hle).1 hspec)
      omega)
  omega

/-- **The half turn preserves the arm**: `âm(aN - r, bN + 1 - i) = arm(r, i)`. -/
@[hjo "lem_half_turn_arm"]
theorem aboveArm_halfTurn {y : Heights a b N} (hy : IsBelowDiagonal y) {r i : ℕ}
    (hr : r ≤ a * N) (hi1 : 1 ≤ i) (hi : i ≤ b * N) :
    aboveArm (halfTurn y) (a * N - r) (b * N + 1 - i) = arm y r i := by
  have hfrle : firstReach y i ≤ a * N := by have := ReturnPath.firstReach_lt y i; omega
  rw [aboveArm, lastBelow_halfTurn hy hi1 hi, arm]
  omega

/-- **The half turn preserves the leg**: `lêg(aN - r, bN + 1 - i) = leg(r, i)`. -/
@[hjo "lem_half_turn_leg"]
theorem aboveLeg_halfTurn {y : Heights a b N} {r i : ℕ} (hr : r ≤ a * N) (_hi : i ≤ b * N) :
    aboveLeg (halfTurn y) (a * N - r) (b * N + 1 - i) = leg y r i := by
  have hsub : a * N - (a * N - r) = r := by omega
  rw [aboveLeg, ht_halfTurn (by omega), hsub, leg]
  have := ht_le_mul y r
  omega

/-- **The half turn is a bijection on cells**: the map `(r, i) ↦ (aN - r, bN + 1 - i)` sends the
cell `(r, i)` of the diagram below `P` to a cell of the diagram above `P̂`, and only those — for
`(r, i)` in the abscissa window of a cell, the image lies in `aboveCells P̂` exactly when `i ≤ y_r`,
which is the condition cutting the cells of `P` out of that window. Being an equivalence rather than
an implication, this is both halves of the bijection: the map is injective on the window because
`(r, i) ↦ (aN - r, bN + 1 - i)` is an involution of it, and surjective because a cell `(s, j)` above
`P̂` is the image of `(aN - s, bN + 1 - j)`.

The statement asks only for `1 ≤ i ≤ y_r`; the ordinate bound `i ≤ bN` is not needed: `y_r ≤ bN`
for every height vector, so for `i > bN` the right side already fails, while the left side fails
because `bN + 1 - i` truncates to `0`, which no cell has. No hypothesis on `P` is needed either;
`IsBelowDiagonal` enters only in the arm (`aboveArm_halfTurn`), through the attainment of `A_i`. -/
@[hjo "lem_half_turn_cells"]
theorem mem_aboveCells_halfTurn {y : Heights a b N} {p : ℕ × ℕ}
    (hr1 : 1 ≤ p.1) (hr2 : p.1 < a * N) (hi1 : 1 ≤ p.2) :
    (a * N - p.1, b * N + 1 - p.2) ∈ aboveCells (halfTurn y) ↔ p.2 ≤ ht y p.1 := by
  have hsub : a * N - (a * N - p.1) = p.1 := by omega
  rw [mem_aboveCells, ht_halfTurn (by omega), hsub]
  have := ht_le_mul y p.1
  omega

/-- **The half turn preserves the hook count**: `ĥ(P̂) = h(P)`. The two definitions impose
literally the same two inequalities on the arm and the leg of a cell, and the half turn is a
bijection of cells leaving both unchanged. -/
@[hjo "lem_half_turn_hook"]
theorem aboveHookCount_halfTurn {y : Heights a b N} (hy : IsBelowDiagonal y) :
    aboveHookCount (halfTurn y) = hookCount y := by
  rw [aboveHookCount, hookCount]
  refine (Finset.card_nbij' (fun p => (a * N - p.1, b * N + 1 - p.2))
    (fun q => (a * N - q.1, b * N + 1 - q.2)) (fun p hp => ?_) (fun q hq => ?_)
    (fun p hp => ?_) (fun q hq => ?_)).symm
  · simp only [Finset.mem_coe, mem_filter] at hp ⊢
    obtain ⟨hp, hle, hhook⟩ := hp
    rw [mem_product, mem_Ico, mem_Icc] at hp
    refine ⟨(mem_aboveCells_halfTurn hp.1.1 hp.1.2 hp.2.1).2 hle, ?_⟩
    rw [aboveArm_halfTurn hy (by omega) hp.2.1 hp.2.2,
      aboveLeg_halfTurn (by omega) hp.2.2]
    exact hhook
  · simp only [Finset.mem_coe, mem_filter] at hq ⊢
    obtain ⟨hq, hhook⟩ := hq
    rw [mem_aboveCells] at hq
    obtain ⟨h1, h2, h3, h4⟩ := hq
    have hsub : a * N - (a * N - q.1) = q.1 := by omega
    have hht := ht_le_mul y (a * N - q.1)
    rw [ht_halfTurn (by omega)] at h3
    have hmem : (a * N - q.1, b * N + 1 - q.2) ∈ Ico 1 (a * N) ×ˢ Icc 1 (b * N) := by
      rw [mem_product, mem_Ico, mem_Icc]; exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    refine ⟨hmem, by omega, ?_⟩
    rw [mem_product, mem_Ico, mem_Icc] at hmem
    rw [← aboveArm_halfTurn hy (b := b) (by omega) hmem.2.1 hmem.2.2,
      ← aboveLeg_halfTurn (y := y) (by omega) hmem.2.2, hsub]
    have h5 : b * N + 1 - (b * N + 1 - q.2) = q.2 := by omega
    rw [h5]; exact hhook
  · simp only [Finset.mem_coe, mem_filter, mem_product, mem_Ico, mem_Icc] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, -⟩ := hp
    refine Prod.ext ?_ ?_ <;> simp only [] <;> omega
  · simp only [Finset.mem_coe, mem_filter, mem_aboveCells] at hq
    obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := hq
    refine Prod.ext ?_ ?_ <;> simp only [] <;> omega

end HJO.Paths
