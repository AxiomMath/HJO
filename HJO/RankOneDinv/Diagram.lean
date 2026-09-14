/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Rat.Floor
public import HJO.Paths.ReturnPath
public meta import HJO.Attr

/-! # The combinatorial objects of the rank-one dinv identity

The objects the rank-one dinv identity is stated with that the development does not already
carry: the diagonal floor `β u = ⌊u * b / a⌋`, the gap diagram `𝒟` of cells `(r, i)` cut out by
`1 ≤ r ≤ a - 1`, `i ≥ 1` and `r * b - a * i > 0`, and the tail count `E_P(u, v)` of the cells of
a below-diagonal path whose arm and leg exceed given thresholds.

`β` is Lean's integer division `u * b / a`, which is `Int.ediv` and hence the floor because the
divisor `a` is a natural number; `beta_eq_floor` records that reading, `le_beta_iff` and
`beta_lt_iff` are the two halves of the floor characterisation that consumers use in place of
unfolding, and `beta_natCast` is the bridge to the natural division `b * r / a` in which the
diagonal already appears in `HJO.Paths.area`. Negative arguments are genuinely used -- the
reflection `β (-u) = -β u - 1` -- so the argument is an integer while `a` and `b` stay natural,
as everywhere else in the development.

The gap diagram is a `Finset`, not a `Set`: every consumer counts its subsets. Its cells are
pairs of naturals, matching `HJO.Paths.hookCount` and `HJO.ReturnPath.cellSet`, so the positive
linear form `r * b - a * i` is a natural number and its positivity is written as the strict
inequality `a * i < r * b` to avoid truncated subtraction. Finiteness is built in by confining
`i` to `Icc 1 b`, a bound the three defining inequalities already force, and `mem_gapDiagram`
recovers the description in which that bound is left implicit.

The subdiagram `𝒟_F` of the cells whose linear form lands in a prescribed set `F` of gaps is
*not* introduced here: it is `HJO.ReturnPath.cellSet a b F`, around which the cell-sum,
column-splitting and row-splitting API already exists, and `cellSet_eq_filter_gapDiagram` is that
identification. Being an order filter is a hypothesis of the lemmas about `𝒟_F`, never part of
it.

The tail count counts the same cells as `HJO.Paths.hookCount`, namely the pairs `(r, i)` with
`1 ≤ r < a * N` and `1 ≤ i ≤ y_r`, and like every statistic in `HJO.Paths` it is total on all
candidate height vectors.
-/

@[expose] public section

open Finset

namespace HJO.Gaps

/-! ### The diagonal floor -/

/-- The diagonal floor `β u = ⌊u * b / a⌋`, the height of the line of slope `b / a` above the
horizontal coordinate `u`. Lean's `/` on `ℤ` is `Int.ediv`, which rounds towards `-∞` for the
nonnegative divisor `a`; at `a = 0` the value is `0`. -/
@[hjo "def_beta"]
def beta (a b : ℕ) (u : ℤ) : ℤ := u * b / a

/-- `β u` is the floor of the rational number `u * b / a`. -/
@[hjo "def_beta"]
theorem beta_eq_floor (a b : ℕ) (u : ℤ) : beta a b u = ⌊(u * b : ℚ) / (a : ℚ)⌋ := by
  rw [beta, ← Rat.floor_intCast_div_natCast (u * b) a]
  norm_cast

variable {a b : ℕ}

/-- The lower half of the floor characterisation: `v ≤ β u` exactly when the point `(u, v)` lies
weakly below the line of slope `b / a`. -/
theorem le_beta_iff (ha : 0 < a) {u v : ℤ} : v ≤ beta a b u ↔ v * a ≤ u * b :=
  Int.le_ediv_iff_mul_le (by exact_mod_cast ha)

/-- The upper half of the floor characterisation: `β u < v` exactly when the point `(u, v)` lies
strictly above the line of slope `b / a`. -/
theorem beta_lt_iff (ha : 0 < a) {u v : ℤ} : beta a b u < v ↔ u * b < v * a :=
  Int.ediv_lt_iff_lt_mul (by exact_mod_cast ha)

/-- On a nonnegative argument `β` is the truncated division of naturals, the form in which the
diagonal appears in `HJO.Paths.area`. -/
theorem beta_natCast (a b r : ℕ) : beta a b (r : ℤ) = (b * r / a : ℕ) := by
  rw [beta, Int.natCast_ediv, Nat.cast_mul, mul_comm (b : ℤ)]

/-! ### The gap diagram -/

/-- The gap diagram `𝒟` of `⟨a, b⟩`: the cells `(r, i)` with `1 ≤ r ≤ a - 1`, `i ≥ 1` and
`r * b - a * i > 0`, the last condition written as `a * i < r * b` to avoid truncated
subtraction. Confining `i` to `Icc 1 b` makes the diagram finite and costs nothing: the three
defining inequalities already force `i < b`, see `mem_gapDiagram` and
`snd_lt_of_mem_gapDiagram`. -/
@[hjo "def_gap_diagram"]
def gapDiagram (a b : ℕ) : Finset (ℕ × ℕ) :=
  {p ∈ Ico 1 a ×ˢ Icc 1 b | a * p.2 < p.1 * b}

/-- **Membership in the gap diagram**: its cells are exactly the pairs `(r, i)` with `1 ≤ r < a`,
`1 ≤ i` and `a * i < r * b`. The bound `i ≤ b` present in the definition is a consequence of
those three inequalities. -/
@[simp, hjo "def_gap_diagram"]
theorem mem_gapDiagram {p : ℕ × ℕ} :
    p ∈ gapDiagram a b ↔ 1 ≤ p.1 ∧ p.1 < a ∧ 1 ≤ p.2 ∧ a * p.2 < p.1 * b := by
  simp only [gapDiagram, mem_filter, mem_product, mem_Ico, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, -⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hab : p.1 * b ≤ a * b := Nat.mul_le_mul h2.le (le_refl b)
    exact ⟨⟨⟨h1, h2⟩, h3, (lt_of_mul_lt_mul_left (h4.trans_le hab) (Nat.zero_le a)).le⟩, h4⟩

/-- Every cell of the gap diagram lies strictly below row `b`. -/
theorem snd_lt_of_mem_gapDiagram {p : ℕ × ℕ} (hp : p ∈ gapDiagram a b) : p.2 < b := by
  rw [mem_gapDiagram] at hp
  have hab : p.1 * b ≤ a * b := Nat.mul_le_mul hp.2.1.le (le_refl b)
  exact lt_of_mul_lt_mul_left (hp.2.2.2.trans_le hab) (Nat.zero_le a)

end HJO.Gaps

namespace HJO.ReturnPath

/-! ### The filtered gap diagram -/

/-- A cell lies in the diagram of a set of gaps exactly when it lies in the gap diagram and its
linear form `r * b - a * i` lies in that set. -/
theorem mem_cellSet_iff_mem_gapDiagram {a b : ℕ} {F : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ cellSet a b F ↔ p ∈ Gaps.gapDiagram a b ∧ p.1 * b - a * p.2 ∈ F := by
  simp only [cellSet, mem_filter, mem_product, mem_Ico, mem_Icc, Gaps.mem_gapDiagram]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, -⟩, h4, h5⟩
    exact ⟨⟨h1, h2, h3, h4⟩, h5⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    have hab : p.1 * b ≤ a * b := Nat.mul_le_mul h2.le (le_refl b)
    exact ⟨⟨⟨h1, h2⟩, h3, (lt_of_mul_lt_mul_left (h4.trans_le hab) (Nat.zero_le a)).le⟩, h4, h5⟩

/-- The subdiagram `𝒟_F` of the cells whose linear form lands in a set `F` of gaps: the cells of
the diagram of a set of gaps are exactly the cells of the gap diagram with `r * b - a * i ∈ F`,
so `HJO.ReturnPath.cellSet a b F` is that subdiagram. -/
@[hjo "def_filter_diagram"]
theorem cellSet_eq_filter_gapDiagram (a b : ℕ) (F : Finset ℕ) :
    cellSet a b F = {p ∈ Gaps.gapDiagram a b | p.1 * b - a * p.2 ∈ F} := by
  ext p
  rw [mem_filter]
  exact mem_cellSet_iff_mem_gapDiagram

/-- The subdiagram cut out by a set of gaps is a subdiagram of the gap diagram. -/
theorem cellSet_subset_gapDiagram (a b : ℕ) (F : Finset ℕ) :
    cellSet a b F ⊆ Gaps.gapDiagram a b := fun _ hp =>
  (mem_cellSet_iff_mem_gapDiagram.mp hp).1

end HJO.ReturnPath

namespace HJO.Paths

/-! ### The tail count of a path -/

variable {a b N : ℕ}

/-- The tail count `E_P(u, v)`: the number of cells `(r, i)` of the below-diagonal path `y`
whose arm is at least `u` and whose leg is at least `v`. The cells are the pairs with
`1 ≤ r < a * N` and `1 ≤ i ≤ y_r`, as in `HJO.Paths.hookCount`. -/
@[hjo "def_tail_count"]
def tailCount (y : Heights a b N) (u v : ℕ) : ℕ :=
  #{p ∈ Ico 1 (a * N) ×ˢ Icc 1 (b * N) |
      p.2 ≤ ht y p.1 ∧ u ≤ arm y p.1 p.2 ∧ v ≤ leg y p.1 p.2}

/-- The tail count is antitone in both thresholds. -/
theorem tailCount_le_tailCount (y : Heights a b N) {u u' v v' : ℕ} (hu : u ≤ u') (hv : v ≤ v') :
    tailCount y u' v' ≤ tailCount y u v := by
  simp only [tailCount]
  refine card_le_card fun p hp => ?_
  simp only [mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, hu.trans hp.2.2.1, hv.trans hp.2.2.2⟩

/-- At threshold zero the tail count counts every cell of the path. -/
theorem tailCount_zero_zero (y : Heights a b N) :
    tailCount y 0 0 = #{p ∈ Ico 1 (a * N) ×ˢ Icc 1 (b * N) | p.2 ≤ ht y p.1} := by
  simp [tailCount]

end HJO.Paths
