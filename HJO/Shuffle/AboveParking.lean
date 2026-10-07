/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Paths.Defs
public import HJO.Shuffle.AboveDiagonal
public meta import HJO.Attr

/-! # Above-diagonal rational parking functions and their statistics

The above-diagonal parking functions are what the compositional rational shuffle identity, as stated
in §4.2 (The compositional theorem and sign extraction) of *Rogers-Ramanujan identities from the
geometry of `X^a = Y^b`*, sums over. This file gives them, and their four statistics —
above-diagonal rank, temporary dinv and its maximum, rational dinv, and inverse descent set — on the
*same* encoding `HJO.ParkingFunctions.ParkingFunction` uses for the below-diagonal ones: a height
vector together with a labelling of `Fin (bN)`, the north step whose foot is at height `s` being
indexed by `s`.

Sharing the encoding is the point. The half turn of the rectangle then acts on a parking function
as `Fin.rev` on both the abscissa and the label, so the bijection of `HJO/Shuffle/HalfTurn.lean`
needs no change of representation and no coercion between two notions of "labelled path".

## Main definitions

* `HJO.ParkingFunctions.AboveParkingFunction`: the above-diagonal parking functions.
* `HJO.ParkingFunctions.aboveWithReturns`: those whose path has a given return composition.
* `HJO.ParkingFunctions.abovePointRank`, `HJO.ParkingFunctions.aboveLabelRank`: the
  above-diagonal rank of a lattice point and of a label.
* `HJO.ParkingFunctions.aboveTdinv`, `HJO.ParkingFunctions.aboveMaxTdinv`,
  `HJO.ParkingFunctions.aboveDinv`: the temporary dinv, its maximum over a path, and the
  rational dinv.
* `HJO.ParkingFunctions.aboveIdes`: the inverse descent set of the above-diagonal reading word.

## Main results

* `HJO.ParkingFunctions.aboveTdinv_le_aboveMaxTdinv`: `tdinv̂(π̂) ≤ max tdinv̂(P̂_π̂)`.
* `HJO.ParkingFunctions.aboveDinv_le_aboveHookCount`: `dinv̂(π̂) ≤ ĥ(P̂_π̂)`, with equality exactly
  at the maximisers of `tdinv̂` — the two together are what make the correction term of `dinv̂` a
  deficiency, readable without unfolding `aboveDinv`.
* `HJO.ParkingFunctions.mem_northSteps_iff_eq_aboveColumn`,
  `HJO.ParkingFunctions.northSteps_eq_image_aboveColumn`: on an above-diagonal path the north
  steps are exactly the points `(Â_{i+1}, i)` for `i < bN`, which is what makes a labelling of
  `Fin (bN)` a labelling of the north steps.

## Implementation notes

The above-diagonal rank of `(x, y)` is `(aN+1)N(ay - bx) + x`, that paper's rank
`R_i = aN y - bN x + x/(aN+1)` cleared of its denominator. It is **not** `pointRank` with the sign
of `ay - bx` flipped: the two differ by a further factor `N` on the leading term as soon as `N ≥ 2`,
and for `N ≥ 2` neither is an affine function of the other. What the half turn preserves is not the
rank but the rank *comparisons*, and the window criterion of `HJO/Shuffle/HalfTurn.lean` is where
that is isolated: the two windows `(aN+1)a` and `(aN+1)aN` are `M a` for the respective `M`, and for
every `M > aN` the condition `0 < M D + e < M a` is one and the same condition on the diagonal
offset `D` and the abscissa difference `e`.

`aboveColumn y i` is `HJO.Paths.lastBelow y (i + 1)`, the *largest* `r` with `ŷ_r ≤ i`, mirroring
`HJO.ParkingFunctions.column`, which is the *smallest* `r` with `y_r > s`. On an above-diagonal
path that is exactly the column of the north step whose foot is at height `i`.

The tie-breaking clause of `AboveReadBefore` reads a column upwards, `s < t`, where
`HJO.ParkingFunctions.ReadBefore` reads it downwards, `t < s`; both are
vacuous on a parking function with `0 < a`, where the ranks of distinct north steps differ
(`HJO.ParkingFunctions.stepRank_injective` and its above-diagonal sibling). They are retained
because without them the reading word is not defined by the shape of the definition alone.

## References

This file formalises Definitions `HJO.ParkingFunctions.AboveParkingFunction`,
`HJO.ParkingFunctions.abovePointRank`, `HJO.ParkingFunctions.aboveTdinv`,
`HJO.ParkingFunctions.aboveMaxTdinv`, `HJO.ParkingFunctions.aboveDinv` and
`HJO.ParkingFunctions.aboveIdes`, together with `HJO.ParkingFunctions.aboveTdinv_le_aboveMaxTdinv`,
`HJO.ParkingFunctions.aboveDinv_le_aboveHookCount`,
`HJO.ParkingFunctions.mem_northSteps_iff_eq_aboveColumn` and
`HJO.ParkingFunctions.northSteps_eq_image_aboveColumn`, mirroring the below-diagonal declarations of
`HJO/Defs.lean`.
-/

@[expose] public section

open Finset

namespace HJO.ParkingFunctions

/-- The above-diagonal rank `P̂(x,y) = (aN + 1)N(a*y - b*x) + x` of a lattice point. This is the
rank `R_i = aN y - bN x + x/(aN+1)` of §4.2 of *Rogers-Ramanujan identities from the geometry of
`X^a = Y^b`* multiplied by the positive integer `aN + 1`, which clears the
denominator without changing any comparison between two ranks; the window of `aboveTdinv` is
scaled by the same factor. It is not `pointRank` with the sign of `a*y - b*x` flipped: the two
differ by a further factor `N` on the leading term as soon as `N ≥ 2`. -/
@[hjo "def_above_rank"]
def abovePointRank (a b N x y : ℕ) : ℤ := (a * N + 1) * N * (a * y - b * x) + x

variable {a b N : ℕ}

/-- For an above-diagonal path `y` and `i < bN`, the horizontal coordinate of the north step whose
foot is at height `i`: the greatest `r` with `ŷ_r ≤ i`. Outside that domain the definition uses the
totalized `lastBelow`, with fallback `0` when no such coordinate exists. This is the mirror of
`column` under the half turn of the rectangle. -/
def aboveColumn (y : Paths.Heights a b N) (i : ℕ) : ℕ := Paths.lastBelow y (i + 1)

/-- On an above-diagonal path the north steps are named by the height of their feet: `(x, i)` is a
north step exactly when `i < bN` and `x` is the column `Â_{i+1}` of the step at height `i`. -/
theorem mem_northSteps_iff_eq_aboveColumn {y : Paths.Heights a b N}
    (hy : Paths.IsAboveDiagonal y) {x i : ℕ} :
    (x, i) ∈ Paths.northSteps y ↔ i < b * N ∧ x = aboveColumn y i := by
  have hmono : ∀ {r s : ℕ}, r ≤ s → s ≤ a * N → Paths.ht y r ≤ Paths.ht y s := by
    intro r s hrs
    induction s, hrs using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ n hn ih => intro hle; exact (ih (by omega)).trans (hy.2.2.1 n (by omega))
  have hlb := Paths.lastBelow_le y (i + 1)
  have hlt : Paths.ht y (Paths.lastBelow y (i + 1)) < i + 1 := hy.ht_lastBelow_lt (by omega)
  simp only [Paths.mem_northSteps_iff]
  unfold aboveColumn
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨lt_of_lt_of_le h3 (le_of_le_of_eq (hmono (by omega) le_rfl) hy.2.1), ?_⟩
    refine le_antisymm (Paths.le_lastBelow (by omega) (by omega)) ?_
    rcases Nat.lt_or_ge x (Paths.lastBelow y (i + 1)) with hx | hx
    · have := hmono (r := x + 1) (s := Paths.lastBelow y (i + 1)) (by omega) hlb
      omega
    · exact hx
  · rintro ⟨h2, rfl⟩
    have h1 : Paths.lastBelow y (i + 1) < a * N := by
      rcases Nat.lt_or_ge (Paths.lastBelow y (i + 1)) (a * N) with h | h
      · exact h
      · have heq : Paths.lastBelow y (i + 1) = a * N := le_antisymm hlb h
        rw [heq, hy.2.1] at hlt
        omega
    refine ⟨h1, by omega, ?_⟩
    rcases Nat.lt_or_ge i (Paths.ht y (Paths.lastBelow y (i + 1) + 1)) with h | h
    · exact h
    · have := Paths.le_lastBelow (y := y) (r := Paths.lastBelow y (i + 1) + 1) (j := i + 1)
        (by omega) (by omega)
      omega

/-- The `bN` north steps of an above-diagonal path are exactly the points `(Â_{i+1}, i)` for
`i < bN`: indexing a north step by the height of its foot is a bijective indexing of
`HJO.Paths.northSteps` by `Fin (bN)`, which is what makes a labelling of `Fin (bN)` a labelling of
the north steps. -/
theorem northSteps_eq_image_aboveColumn {y : Paths.Heights a b N}
    (hy : Paths.IsAboveDiagonal y) :
    Paths.northSteps y = (range (b * N)).image fun i => (aboveColumn y i, i) := by
  ext q
  obtain ⟨x, i⟩ := q
  simp only [mem_image, mem_range, Prod.mk.injEq, mem_northSteps_iff_eq_aboveColumn hy]
  constructor
  · rintro ⟨h1, rfl⟩
    exact ⟨i, h1, rfl, rfl⟩
  · rintro ⟨j, hj, rfl, rfl⟩
    exact ⟨hj, rfl⟩

/-- `lab` labels the `bN` north steps of the above-diagonal path `y` bijectively by `1, …, bN`, the
step whose foot is at height `i` carrying the label `lab i + 1`, in a way that increases upwards
along each column. -/
def IsAboveParkingLabelling (y : Paths.Heights a b N) (lab : Fin (b * N) → Fin (b * N)) : Prop :=
  Function.Bijective lab ∧
    ∀ s t : Fin (b * N), s < t → aboveColumn y (s : ℕ) = aboveColumn y (t : ℕ) → lab s < lab t

instance instDecidableIsAboveParkingLabelling (y : Paths.Heights a b N)
    (lab : Fin (b * N) → Fin (b * N)) : Decidable (IsAboveParkingLabelling y lab) := by
  unfold IsAboveParkingLabelling; infer_instance

/-- An above-diagonal parking function in the `aN × bN` rectangle: an above-diagonal
`(aN, bN)`-path together with a bijective labelling of its `bN` north steps by `1, …, bN` that
increases upwards along each column. The north step whose foot is at height `i` is indexed by
`i`. -/
@[hjo "def_above_parking"]
abbrev AboveParkingFunction (a b N : ℕ) : Type :=
  {p : Paths.Heights a b N × (Fin (b * N) → Fin (b * N)) //
    Paths.IsAboveDiagonal p.1 ∧ IsAboveParkingLabelling p.1 p.2}

/-- The path `P̂_π̂` underlying the above-diagonal parking function `π̂`. -/
def abovePath (π : AboveParkingFunction a b N) : Paths.Heights a b N := π.val.1

/-- The labelling of `π̂`: the north step whose foot is at height `i` carries the label
`aboveLabel π̂ i + 1`. -/
def aboveLabel (π : AboveParkingFunction a b N) (i : Fin (b * N)) : Fin (b * N) := π.val.2 i

/-- The labelling of an above-diagonal parking function is a bijection. -/
theorem bijective_aboveLabel (π : AboveParkingFunction a b N) :
    Function.Bijective (aboveLabel π) := π.2.2.1

/-- The north step of `π̂` carrying the label `i + 1`, indexed by the height of its foot. -/
def aboveLabelStep (π : AboveParkingFunction a b N) (i : Fin (b * N)) : Fin (b * N) :=
  Fintype.bijInv (bijective_aboveLabel π) i

@[simp]
theorem aboveLabel_aboveLabelStep (π : AboveParkingFunction a b N) (i : Fin (b * N)) :
    aboveLabel π (aboveLabelStep π i) = i :=
  Fintype.rightInverse_bijInv _ i

@[simp]
theorem aboveLabelStep_aboveLabel (π : AboveParkingFunction a b N) (s : Fin (b * N)) :
    aboveLabelStep π (aboveLabel π s) = s :=
  Fintype.leftInverse_bijInv _ s

/-- `PF̂^α_{aN, bN}`, the above-diagonal parking functions in the `aN × bN` rectangle whose
underlying path has return composition `α`. -/
def aboveWithReturns (α : List ℕ) (a b N : ℕ) : Finset (AboveParkingFunction a b N) :=
  (univ : Finset (AboveParkingFunction a b N)).filter fun π =>
    Paths.HasAboveReturns α (abovePath π)

/-- The above-diagonal rank of the north step of `π̂` indexed by `i`: the above-diagonal rank of
the lattice point `(aboveColumn, i)` at its foot. -/
def aboveStepRank (π : AboveParkingFunction a b N) (i : Fin (b * N)) : ℤ :=
  abovePointRank a b N (aboveColumn (abovePath π) (i : ℕ)) (i : ℕ)

/-- The above-diagonal rank of the label `i + 1` of `π̂`: the above-diagonal rank of the lattice
point at the foot of the north step that this label marks. -/
@[hjo "def_above_rank"]
def aboveLabelRank (π : AboveParkingFunction a b N) (i : Fin (b * N)) : ℤ :=
  aboveStepRank π (aboveLabelStep π i)

/-- `tdinv̂(π̂)`, the number of pairs of labels `i < j` with
`rk̂(i) < rk̂(j) < rk̂(i) + (aN + 1)aN`.
Both ends are strict, and the window `(aN + 1)aN` is the window `aN` of the temporary dinv in §4.2
of *Rogers-Ramanujan identities from the geometry of `X^a = Y^b`*, scaled by the same factor
`aN + 1` that clears the denominator in `abovePointRank`. -/
@[hjo "def_above_tdinv"]
def aboveTdinv (π : AboveParkingFunction a b N) : ℕ :=
  #{p ∈ (univ : Finset (Fin (b * N) × Fin (b * N))) | p.1 < p.2 ∧
      aboveLabelRank π p.1 < aboveLabelRank π p.2 ∧
      aboveLabelRank π p.2 < aboveLabelRank π p.1 + (a * N + 1) * (a * N)}

/-- `max tdinv̂(P̂)`, the largest `tdinv̂` of an above-diagonal parking function whose underlying
path is `y`. It is `0` when no above-diagonal parking function has underlying path `y`, that is,
when `y` is not an above-diagonal path. -/
@[hjo "def_above_maxtdinv"]
def aboveMaxTdinv (y : Paths.Heights a b N) : ℕ :=
  ((univ : Finset (AboveParkingFunction a b N)).filter fun π => abovePath π = y).sup aboveTdinv

/-- `dinv̂(π̂) = ĥ(P̂_π̂) + tdinv̂(π̂) - max tdinv̂(P̂_π̂)`, taken in `ℤ` because the difference of
the last two terms is genuine and need not be non-negative on its own. -/
@[hjo "def_above_dinv"]
def aboveDinv (π : AboveParkingFunction a b N) : ℤ :=
  (Paths.aboveHookCount (abovePath π) : ℤ) + aboveTdinv π - aboveMaxTdinv (abovePath π)

/-- A labelling's temporary dinv is at most the maximum over its own path: the fibre of
`abovePath` over `P̂_π̂` contains `π̂`. -/
theorem aboveTdinv_le_aboveMaxTdinv (π : AboveParkingFunction a b N) :
    aboveTdinv π ≤ aboveMaxTdinv (abovePath π) :=
  Finset.le_sup (f := aboveTdinv) (mem_filter.2 ⟨mem_univ _, rfl⟩)

/-- `dinv̂(π̂) ≤ ĥ(P̂_π̂)`: the correction term is a deficiency, so the hook count of the path
bounds the dinv of every labelling of it, with equality exactly at the maximisers of `tdinv̂`. -/
theorem aboveDinv_le_aboveHookCount (π : AboveParkingFunction a b N) :
    aboveDinv π ≤ (Paths.aboveHookCount (abovePath π) : ℤ) := by
  have h := aboveTdinv_le_aboveMaxTdinv π
  rw [aboveDinv]
  omega

/-- The north step `s` of `π̂` is read before the step `t`: its foot has the larger above-diagonal
rank, or the two ranks agree and `s` is the lower step, which is the tie-break "reading
a column upwards". For `0 < a` the second clause never fires: the above-diagonal ranks of distinct
north steps differ. -/
def AboveReadBefore (π : AboveParkingFunction a b N) (s t : Fin (b * N)) : Prop :=
  aboveStepRank π t < aboveStepRank π s ∨ (aboveStepRank π s = aboveStepRank π t ∧ s < t)

instance instDecidableAboveReadBefore (π : AboveParkingFunction a b N) (s t : Fin (b * N)) :
    Decidable (AboveReadBefore π s t) := by unfold AboveReadBefore; infer_instance

/-- The above-diagonal reading word of `π̂`: the word in `1, …, bN` listing its labels in
decreasing order of the above-diagonal rank of the north step each one marks. -/
def aboveReadingWord (π : AboveParkingFunction a b N) : List ℕ :=
  ((List.finRange (b * N)).mergeSort fun s t => !decide (AboveReadBefore π t s)).map
    fun s => (aboveLabel π s : ℕ) + 1

/-- `ideŝ(π̂)`, the set of those `i` in `1, …, bN - 1` such that `i + 1` precedes `i` in the
above-diagonal reading word of `π̂`. -/
@[hjo "def_above_ides"]
def aboveIdes (π : AboveParkingFunction a b N) : Finset ℕ :=
  {i ∈ Ico 1 (b * N) | (aboveReadingWord π).idxOf (i + 1) < (aboveReadingWord π).idxOf i}

/-- `ideŝ(π̂)` is a descent set on degree `bN`: it is a subset of `1, …, bN - 1`. -/
theorem aboveIdes_subset (π : AboveParkingFunction a b N) : aboveIdes π ⊆ Ico 1 (b * N) :=
  filter_subset _ _

end HJO.ParkingFunctions
