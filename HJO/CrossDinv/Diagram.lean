/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Int.Interval
public import HJO.RankOneDinv.Basic
public meta import HJO.Attr

/-! # The cross-dinv identity: two filter diagrams at once

The cross-dinv identity is the rank-one dinv identity run with two order filters instead of one:
the arm of a cell is measured in the diagram of the first filter, its leg in the diagram of the
second. This file sets up the geometry that carries the argument -- the cross tail count
`T_{D,E}(u, v)` of the cells of `𝒟_D` whose shift by `(u, v)` lands in `𝒟_E`, the cross arm sets
`A^D_u` and cross leg sets `L^E_v`, and the four facts about them the counting needs: the tail
count is symmetric under swapping the two filters and negating the shift, it vanishes once the
column shift exceeds the width, it is the size of an intersection of an arm set with a leg set,
and the two families shrink as their shifts grow, reducing at shift `0` to the diagram itself.

Two conventions matter, both inherited from `HJO.RankOneDinv`. The arm displaces the COLUMN index
and the leg displaces the ROW index, so `A^D_u` and `L^E_v` are two *separate* memberships,
`(r - u, i) ∈ 𝒟_D` and `(r, i + v) ∈ 𝒟_E`; their conjunction is strictly weaker than membership
of `(r - u, i + v)`, which is why the tail count is an intersection of two families rather than
one shifted diagram. And the shifts are integers of either sign -- the reflection
`β (-u) = -β u - 1` folds the pairs with `r' < r` onto the pairs with `r' > r` -- so the cells are
read as pairs of integers here: `cellZ a b F` is `HJO.ReturnPath.cellSet a b F` in integer
coordinates, and `natCast_mem_cellZ` is the dictionary between the two.

The row ranges confining the arm and leg sets to a `Finset` cost nothing. A cell of `A^D_u` has
its own row index constrained by `(r - u, i) ∈ 𝒟_D`, so `i ≤ b` is free; a cell of `L^E_v` has
its *shifted* row index constrained, so the free bound is `i ≤ b - v`, which is what the
definition uses -- at a negative leg shift the bound `i ≤ b` would cut the set down and make the
definition unfaithful.
-/

@[expose] public section

open Finset NumericalSemigroup HJO.RankOneDinv

namespace HJO.CrossDinv

variable {a b : ℕ} {D E F : Finset ℕ}

/-! ### The filter diagram in integer coordinates -/

/-- The filter diagram `𝒟_F` in integer coordinates: the cells of `HJO.ReturnPath.cellSet a b F`
read as pairs of integers, so that a cell shifted by an integer vector can be spoken of. The
image of an injection, so nothing is added or lost; `natCast_mem_cellZ` is the dictionary. -/
def cellZ (a b : ℕ) (F : Finset ℕ) : Finset (ℤ × ℤ) :=
  (ReturnPath.cellSet a b F).image fun p => ((p.1 : ℤ), (p.2 : ℤ))

/-- A pair of naturals lies in the integer diagram exactly when it lies in the diagram. -/
@[simp]
theorem natCast_mem_cellZ {r i : ℕ} :
    ((r : ℤ), (i : ℤ)) ∈ cellZ a b F ↔ (r, i) ∈ ReturnPath.cellSet a b F := by
  simp only [cellZ, mem_image, Prod.mk.injEq]
  refine ⟨fun h => ?_, fun h => ⟨(r, i), h, rfl, rfl⟩⟩
  obtain ⟨p, hp, h1, h2⟩ := h
  have hpe : p = (r, i) := Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
  rwa [hpe] at hp

/-- Every cell of the integer diagram has natural coordinates. -/
theorem exists_natCast_of_mem_cellZ {r i : ℤ} (h : (r, i) ∈ cellZ a b F) :
    ∃ r' i' : ℕ, r = (r' : ℤ) ∧ i = (i' : ℤ) ∧ (r', i') ∈ ReturnPath.cellSet a b F := by
  simp only [cellZ, mem_image, Prod.mk.injEq] at h
  obtain ⟨p, hp, h1, h2⟩ := h
  exact ⟨p.1, p.2, h1.symm, h2.symm, hp⟩

/-- **The frame of a cell**: a cell of a filter diagram has `1 ≤ r ≤ a - 1` and `1 ≤ i < b`. -/
theorem cellZ_bounds {r i : ℤ} (h : (r, i) ∈ cellZ a b F) :
    1 ≤ r ∧ r ≤ (a : ℤ) - 1 ∧ 1 ≤ i ∧ i < (b : ℤ) := by
  obtain ⟨r', i', rfl, rfl, hp⟩ := exists_natCast_of_mem_cellZ h
  have hg := (ReturnPath.mem_cellSet_iff_mem_gapDiagram.mp hp).1
  have hlt := Gaps.snd_lt_of_mem_gapDiagram hg
  rw [Gaps.mem_gapDiagram] at hg
  obtain ⟨h1, h2, h3, -⟩ := hg
  refine ⟨by exact_mod_cast h1, by omega, by exact_mod_cast h3, by exact_mod_cast hlt⟩

/-- **The integer diagram is closed to the right**: if `(r, i)` lies in `𝒟_F` and
`r + 1 ≤ a - 1` then `(r + 1, i)` lies in `𝒟_F`. -/
theorem mem_cellZ_add_one (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hF : Gaps.IsOrderFilter a b F) {r i : ℤ} (h : (r, i) ∈ cellZ a b F)
    (hlt : r + 1 ≤ (a : ℤ) - 1) : (r + 1, i) ∈ cellZ a b F := by
  obtain ⟨r', i', rfl, rfl, hp⟩ := exists_natCast_of_mem_cellZ h
  have h2 : (r' + 1, i') ∈ ReturnPath.cellSet a b F :=
    mem_filterDiagram_succ hco ha hb hF (p := (r', i')) hp (show r' + 1 ≤ a - 1 from by omega)
  have h3 := natCast_mem_cellZ (a := a) (b := b) (F := F) (r := r' + 1) (i := i') |>.mpr h2
  push_cast at h3
  exact h3

/-- **An integer diagram column is an initial segment**: if `(r, i)` lies in `𝒟_F` and
`1 ≤ j ≤ i` then `(r, j)` lies in `𝒟_F`. -/
theorem mem_cellZ_of_le (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hF : Gaps.IsOrderFilter a b F) {r i j : ℤ} (h : (r, i) ∈ cellZ a b F)
    (hj1 : 1 ≤ j) (hj2 : j ≤ i) : (r, j) ∈ cellZ a b F := by
  obtain ⟨r', i', rfl, rfl, hp⟩ := exists_natCast_of_mem_cellZ h
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = (j' : ℤ) := ⟨j.toNat, by omega⟩
  have h2 : (r', j') ∈ ReturnPath.cellSet a b F :=
    mem_filterDiagram_of_le hco ha hb hF (p := (r', i')) hp (show 1 ≤ j' from by omega)
      (show j' ≤ i' from by omega)
  exact natCast_mem_cellZ.mpr h2

/-! ### Cross tail counts, cross arm sets and cross leg sets -/

/-- **The cross tail count** `T_{D,E}(u, v)`: the number of cells of `𝒟_D` whose shift by
`(u, v)` is a cell of `𝒟_E`. -/
@[hjo "def_cross_tail_count"]
def crossTailCount (a b : ℕ) (D E : Finset ℕ) (u v : ℤ) : ℕ :=
  #{q ∈ cellZ a b D | (q.1 + u, q.2 + v) ∈ cellZ a b E}

/-- Membership in the set counted by the cross tail count. -/
@[simp]
theorem mem_crossTailSet {u v : ℤ} {q : ℤ × ℤ} :
    q ∈ {q ∈ cellZ a b D | (q.1 + u, q.2 + v) ∈ cellZ a b E} ↔
      q ∈ cellZ a b D ∧ (q.1 + u, q.2 + v) ∈ cellZ a b E := mem_filter

/-- **The cross arm set** `A^D_u`: the cells `(r, i)` of the frame whose displacement by `u` in
the column index lands in `𝒟_D`. The row range `i ≤ b` is forced by that membership, so
confining the set to it costs nothing. -/
@[hjo "def_cross_arm_set"]
noncomputable def crossArmSet (a b : ℕ) (D : Finset ℕ) (u : ℤ) : Finset (ℤ × ℤ) :=
  {q ∈ Finset.Icc 1 ((a : ℤ) - 1) ×ˢ Finset.Icc 1 (b : ℤ) | (q.1 - u, q.2) ∈ cellZ a b D}

/-- **Membership in the cross arm set**: its cells are exactly the pairs `(r, i)` with
`1 ≤ r ≤ a - 1`, `1 ≤ i` and `(r - u, i) ∈ 𝒟_D`. The row bound present in the definition is
a consequence of the displaced membership. -/
@[simp]
theorem mem_crossArmSet {u : ℤ} {q : ℤ × ℤ} :
    q ∈ crossArmSet a b D u ↔
      1 ≤ q.1 ∧ q.1 ≤ (a : ℤ) - 1 ∧ 1 ≤ q.2 ∧ (q.1 - u, q.2) ∈ cellZ a b D := by
  simp only [crossArmSet, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, -⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨-, -, -, h5⟩ := cellZ_bounds h4
    exact ⟨⟨⟨h1, h2⟩, h3, by omega⟩, h4⟩

/-- **The cross leg set** `L^E_v`: the cells `(r, i)` of the frame whose displacement by `v` in
the row index lands in `𝒟_E`. The row range is `i ≤ b - v`, not `i ≤ b`: it is the *shifted* row
index that the membership bounds, so at a negative leg shift the tighter bound would cut the set
down. -/
@[hjo "def_cross_leg_set"]
noncomputable def crossLegSet (a b : ℕ) (E : Finset ℕ) (v : ℤ) : Finset (ℤ × ℤ) :=
  {q ∈ Finset.Icc 1 ((a : ℤ) - 1) ×ˢ Finset.Icc 1 ((b : ℤ) - v) | (q.1, q.2 + v) ∈ cellZ a b E}

/-- **Membership in the cross leg set**: its cells are exactly the pairs `(r, i)` with
`1 ≤ r ≤ a - 1`, `1 ≤ i` and `(r, i + v) ∈ 𝒟_E`. The row bound present in the definition is
a consequence of the displaced membership. -/
@[simp]
theorem mem_crossLegSet {v : ℤ} {q : ℤ × ℤ} :
    q ∈ crossLegSet a b E v ↔
      1 ≤ q.1 ∧ q.1 ≤ (a : ℤ) - 1 ∧ 1 ≤ q.2 ∧ (q.1, q.2 + v) ∈ cellZ a b E := by
  simp only [crossLegSet, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, -⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨-, -, -, h5⟩ := cellZ_bounds h4
    exact ⟨⟨⟨h1, h2⟩, h3, by omega⟩, h4⟩

/-! ### The three counting identities for cross tail counts -/

/-- **Swapping the two filters negates the shift**: `T_{D,E}(u, v) = T_{E,D}(-u, -v)`. -/
@[hjo "lem_cross_tail_swap"]
theorem crossTailCount_swap (u v : ℤ) :
    crossTailCount a b D E u v = crossTailCount a b E D (-u) (-v) := by
  simp only [crossTailCount]
  refine Finset.card_nbij' (fun q => (q.1 + u, q.2 + v)) (fun q => (q.1 - u, q.2 - v))
    ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_coe, mem_filter] at hq ⊢
    exact ⟨hq.2, by simpa using hq.1⟩
  · intro q hq
    simp only [Finset.mem_coe, mem_filter] at hq ⊢
    exact ⟨by simpa [sub_eq_add_neg] using hq.2, by simpa using hq.1⟩
  · intro q _
    exact Prod.ext (by ring) (by ring)
  · intro q _
    exact Prod.ext (by ring) (by ring)

/-- **The cross tail count vanishes beyond the width**: `T_{D,E}(u, v) = 0` once
`|u| ≥ a - 1`. -/
@[hjo "lem_cross_tail_vanishes"]
theorem crossTailCount_eq_zero {u v : ℤ} (hu : (a : ℤ) - 1 ≤ |u|) :
    crossTailCount a b D E u v = 0 := by
  rw [crossTailCount, card_eq_zero, filter_eq_empty_iff]
  intro q hq hshift
  obtain ⟨h1, h2, -, -⟩ := cellZ_bounds hq
  obtain ⟨h3, h4, -, -⟩ := cellZ_bounds hshift
  rw [le_abs] at hu
  omega

/-- **The cross tail count is the size of an intersection**:
`T_{D,E}(u, v) = #(A^D_u ∩ L^E_v)`. The displacement of the column index by `u` is the
bijection. -/
@[hjo "lem_cross_tail_intersection"]
theorem crossTailCount_eq_card_inter (u v : ℤ) :
    crossTailCount a b D E u v = #(crossArmSet a b D u ∩ crossLegSet a b E v) := by
  simp only [crossTailCount]
  refine (Finset.card_nbij' (fun q => (q.1 - u, q.2)) (fun q => (q.1 + u, q.2)) ?_ ?_ ?_ ?_).symm
  · intro q hq
    simp only [Finset.mem_coe, mem_inter, mem_crossArmSet, mem_crossLegSet] at hq
    simp only [Finset.mem_coe, mem_filter]
    exact ⟨hq.1.2.2.2, by simpa using hq.2.2.2.2⟩
  · intro q hq
    simp only [Finset.mem_coe, mem_filter] at hq
    obtain ⟨-, -, e3, -⟩ := cellZ_bounds hq.1
    obtain ⟨f1, f2, -, -⟩ := cellZ_bounds hq.2
    simp only [Finset.mem_coe, mem_inter, mem_crossArmSet, mem_crossLegSet]
    exact ⟨⟨f1, f2, e3, by simpa using hq.1⟩, ⟨f1, f2, e3, hq.2⟩⟩
  · intro q _
    exact Prod.ext (by ring) rfl
  · intro q _
    exact Prod.ext (by ring) rfl

/-! ### The two families shrink as their shifts grow -/

/-- **The cross arm sets are nested**: `A^D_{u+1} ⊆ A^D_u` for `u ≥ 0`. -/
@[hjo "lem_cross_arm_set_nested"]
theorem crossArmSet_succ_subset (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hD : Gaps.IsOrderFilter a b D) {u : ℤ} (hu : 0 ≤ u) :
    crossArmSet a b D (u + 1) ⊆ crossArmSet a b D u := by
  intro q hq
  simp only [mem_crossArmSet] at hq ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hq
  refine ⟨h1, h2, h3, ?_⟩
  have h5 := mem_cellZ_add_one hco ha hb hD h4 (by omega)
  rwa [show q.1 - (u + 1) + 1 = q.1 - u from by ring] at h5

/-- **The cross arm sets are antitone**: `A^D_{u₁} ⊆ A^D_{u₀}` for `0 ≤ u₀ ≤ u₁`. -/
@[hjo "lem_cross_arm_set_monotone"]
theorem crossArmSet_subset (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hD : Gaps.IsOrderFilter a b D) {u₀ u₁ : ℤ} (h0 : 0 ≤ u₀) (h : u₀ ≤ u₁) :
    crossArmSet a b D u₁ ⊆ crossArmSet a b D u₀ := by
  induction u₁, h using Int.leInduction with
  | base => exact subset_rfl
  | succ n hn ih => exact (crossArmSet_succ_subset hco ha hb hD (h0.trans hn)).trans ih

/-- **The cross leg sets are antitone**: `L^E_{v₁} ⊆ L^E_{v₀}` for `0 ≤ v₀ ≤ v₁`. -/
@[hjo "lem_cross_leg_set_nested"]
theorem crossLegSet_subset (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hE : Gaps.IsOrderFilter a b E) {v₀ v₁ : ℤ} (h0 : 0 ≤ v₀) (h : v₀ ≤ v₁) :
    crossLegSet a b E v₁ ⊆ crossLegSet a b E v₀ := by
  intro q hq
  simp only [mem_crossLegSet] at hq ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hq
  exact ⟨h1, h2, h3, mem_cellZ_of_le hco ha hb hE h4 (by omega) (by omega)⟩

/-- **The cross arm set at shift zero is the diagram**: `A^D_0 = 𝒟_D`. -/
@[hjo "lem_cross_arm_set_zero"]
theorem crossArmSet_zero : crossArmSet a b D 0 = cellZ a b D := by
  ext q
  simp only [mem_crossArmSet, sub_zero]
  refine ⟨fun h => h.2.2.2, fun h => ?_⟩
  obtain ⟨h1, h2, h3, -⟩ := cellZ_bounds h
  exact ⟨h1, h2, h3, h⟩

/-- **The cross leg set at shift zero is the diagram**: `L^E_0 = 𝒟_E`. -/
@[hjo "lem_cross_leg_set_zero"]
theorem crossLegSet_zero : crossLegSet a b E 0 = cellZ a b E := by
  ext q
  simp only [mem_crossLegSet, add_zero]
  refine ⟨fun h => h.2.2.2, fun h => ?_⟩
  obtain ⟨h1, h2, h3, -⟩ := cellZ_bounds h
  exact ⟨h1, h2, h3, h⟩

end HJO.CrossDinv
