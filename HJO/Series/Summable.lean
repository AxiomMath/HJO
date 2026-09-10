/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import QSeriesLib.NumberTheory.QTheory.Defs
public import QSeriesLib.RingTheory.PowerSeries.DiscreteTopology
public import HJO.Defs
public meta import HJO.Attr

/-! # Summability of the cylindric volume generating functions

For `0 < a` the family `q^{|λ|}`, indexed by the cylindric partitions of a fixed profile
either with all entries at most `N` or with no bound at all, is summable in `ℤ⟦X⟧`. Both
reduce to the statement that only finitely many such cylinders have volume below a given
bound, which holds because a nonzero entry far along a weakly decreasing row costs volume.

The two conclusions are deliberately NOT named `HJO.Cylindric.summable_boundedGF` and
`HJO.Cylindric.summable_unboundedGF`, the names the challenge file gives these statements: those
names are the *contract*, and `Solution/Basic.lean` is what must carry them. A library declaration
under a contract name collides with the solution's, and there is then nothing for the comparator
to compare.
-/

@[expose] public section

open Finset Filter PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJO.Summable

open HJO.Cylindric

/-- A row whose entries vanish from `J` on has an honest `Finset` sum for its `finsum`. -/
theorem rowSum_eq_sum {l : ℕ → ℕ → ℕ} {i J : ℕ} (hJ : ∀ j, J ≤ j → l i j = 0) :
    ∑ᶠ j, l i j = ∑ j ∈ range J, l i j :=
  finsum_eq_sum_of_support_subset _ fun j hj => by
    simp only [coe_range, Set.mem_Iio]
    by_contra h
    exact hj (hJ j (not_lt.mp h))

/-- A weakly decreasing row with a nonzero entry at position `j` has row sum at least
`j + 1`, since its entries at positions `0, …, j` are then all at least one. -/
theorem succ_le_rowSum {l : ℕ → ℕ → ℕ} {i j : ℕ} (hmono : Antitone (l i))
    (hz : ∃ J, ∀ j, J ≤ j → l i j = 0) (hj : l i j ≠ 0) : j + 1 ≤ ∑ᶠ k, l i k := by
  obtain ⟨J, hJ⟩ := hz
  rw [rowSum_eq_sum (J := max J (j + 1)) fun k hk => hJ k ((le_max_left _ _).trans hk)]
  calc j + 1 = ∑ _k ∈ range (j + 1), 1 := by simp
    _ ≤ ∑ k ∈ range (j + 1), l i k := by
        refine Finset.sum_le_sum fun k hk => ?_
        have := hmono (show k ≤ j by simpa [Nat.lt_succ_iff] using hk)
        omega
    _ ≤ ∑ k ∈ range (max J (j + 1)), l i k :=
        Finset.sum_le_sum_of_subset fun x hx =>
          mem_range.mpr ((mem_range.mp hx).trans_le (le_max_right _ _))

/-- A single entry of a row is at most that row's sum. -/
theorem le_rowSum {l : ℕ → ℕ → ℕ} {i : ℕ} (hz : ∃ J, ∀ j, J ≤ j → l i j = 0) (j : ℕ) :
    l i j ≤ ∑ᶠ k, l i k := by
  obtain ⟨J, hJ⟩ := hz
  rw [rowSum_eq_sum (J := max J (j + 1)) fun k hk => hJ k ((le_max_left _ _).trans hk)]
  exact Finset.single_le_sum (f := l i) (fun _ _ => Nat.zero_le _)
    (mem_range.mpr ((Nat.lt_succ_self j).trans_le (le_max_right _ _)))

/-- The sum of one of the `a` fundamental rows is at most the volume of the cylinder. -/
theorem rowSum_le_cylVolume {a : ℕ} (l : ℕ → ℕ → ℕ) {i : ℕ} (hi : i < a) :
    ∑ᶠ j, l i j ≤ cylVolume a l :=
  show ∑ᶠ j, l i j ≤ ∑ i ∈ range a, ∑ᶠ j, l i j from
    Finset.single_le_sum (f := fun i => ∑ᶠ j, l i j) (fun _ _ => Nat.zero_le _) (mem_range.mpr hi)

/-- Shifting the row index by a multiple of `a` leaves a periodic family unchanged. -/
theorem periodic_add_mul {a : ℕ} {l : ℕ → ℕ → ℕ} (hp : ∀ i j, l (i + a) j = l i j) (i n j : ℕ) :
    l (i + a * n) j = l i j := by
  induction n with
  | zero => simp
  | succ n ih => rw [show i + a * (n + 1) = i + a * n + a by ring, hp, ih]

/-- Every row of a periodic family agrees with the row indexed by its residue modulo `a`. -/
theorem periodic_mod {a : ℕ} {l : ℕ → ℕ → ℕ} (hp : ∀ i j, l (i + a) j = l i j) (i j : ℕ) :
    l i j = l (i % a) j := by
  conv_lhs => rw [show i = i % a + a * (i / a) from (Nat.mod_add_div i a).symm]
  exact periodic_add_mul hp _ _ _

/-- A cylinder of volume below `y` has every entry at position `y` or later equal to zero. -/
theorem eq_zero_of_cylVolume_lt {a y : ℕ} {c : ℕ → ℕ} {l : ℕ → ℕ → ℕ} (ha : 0 < a)
    (h : IsCylindric a c l) (hy : cylVolume a l < y) {i j : ℕ} (hj : y ≤ j) : l i j = 0 := by
  rw [periodic_mod h.periodic]
  by_contra hne
  have h1 := succ_le_rowSum (h.antitone (i % a)) (h.eventually_zero (i % a)) hne
  have h2 := rowSum_le_cylVolume l (Nat.mod_lt i ha)
  omega

/-- A single entry of a cylinder is at most its volume. -/
theorem le_cylVolume {a : ℕ} {c : ℕ → ℕ} {l : ℕ → ℕ → ℕ} (ha : 0 < a) (h : IsCylindric a c l)
    (i j : ℕ) : l i j ≤ cylVolume a l := by
  rw [periodic_mod h.periodic]
  exact (le_rowSum (h.eventually_zero (i % a)) j).trans (rowSum_le_cylVolume l (Nat.mod_lt i ha))

/-- A cylinder of volume below `y` has all of its entries bounded by `y`. -/
theorem boundedBy_of_cylVolume_lt {a y : ℕ} {c : ℕ → ℕ} {l : ℕ → ℕ → ℕ} (ha : 0 < a)
    (h : IsCylindric a c l) (hy : cylVolume a l < y) : BoundedBy y l :=
  fun i j => (le_cylVolume ha h i j).trans hy.le

/-- Only finitely many cylinders with entries at most `N` have volume below `y`: below that
volume the entries from position `y` on vanish, so the cylinder is determined by its `a`
fundamental rows truncated at `y`, each entry lying in `{0, …, N}`. -/
theorem finite_setOf_cylVolume_lt (a N y : ℕ) (c : ℕ → ℕ) (ha : 0 < a) :
    {l : ℕ → ℕ → ℕ | (IsCylindric a c l ∧ BoundedBy N l) ∧ cylVolume a l < y}.Finite := by
  refine Set.Finite.of_finite_image (f := fun l (i : Fin a) (j : Fin y) =>
    (⟨min (l i j) N, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (N + 1)))
    (Set.toFinite _) ?_
  rintro l₁ ⟨⟨hc₁, hb₁⟩, hv₁⟩ l₂ ⟨⟨hc₂, hb₂⟩, hv₂⟩ heq
  funext i j
  rcases lt_or_ge j y with hjy | hjy
  · have h4 := congrFun (congrFun heq ⟨i % a, Nat.mod_lt i ha⟩) ⟨j, hjy⟩
    have h3 : min (l₁ (i % a) j) N = min (l₂ (i % a) j) N := congrArg Fin.val h4
    have e1 := hb₁ (i % a) j
    have e2 := hb₂ (i % a) j
    rw [periodic_mod hc₁.periodic, periodic_mod hc₂.periodic]
    omega
  · rw [eq_zero_of_cylVolume_lt ha hc₁ hv₁ hjy, eq_zero_of_cylVolume_lt ha hc₂ hv₂ hjy]

/-- The bounded cylindric series is a genuine sum: for `0 < a` the family `q^{|λ|}` indexed
by the cylindric partitions of profile `c` with all entries at most `N` is summable. -/
@[hjo "lem_summable_bounded"]
theorem summable_boundedGF (a b N : ℕ) (ha : 0 < a) :
    Summable fun l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l ∧ BoundedBy N l} =>
      (X : ℤ⟦X⟧) ^ cylVolume a l.val := by
  have hu : Filter.Unbounded (cylVolume a ∘
      Subtype.val (p := fun l => IsCylindric a (profile a b) l ∧ BoundedBy N l)) :=
    Filter.Unbounded.comp_subtypeVal_iff.mpr fun y =>
      (finite_setOf_cylVolume_lt a N y (profile a b) ha).subset fun l hl =>
        ⟨hl.1, not_le.mp hl.2⟩
  simpa using hu.summable_mul_pow (f := fun _ => (1 : ℤ⟦X⟧)) (q := (X : ℤ⟦X⟧))

/-- The cylindric series is a genuine sum: for `0 < a` the family `q^{|λ|}` indexed by the
cylindric partitions of profile `c` with no bound on their entries is summable. -/
@[hjo "lem_summable_unbounded"]
theorem summable_unboundedGF (a b : ℕ) (ha : 0 < a) :
    Summable fun l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l} =>
      (X : ℤ⟦X⟧) ^ cylVolume a l.val := by
  have hu : Filter.Unbounded (cylVolume a ∘
      Subtype.val (p := fun l => IsCylindric a (profile a b) l)) :=
    Filter.Unbounded.comp_subtypeVal_iff.mpr fun y =>
      (finite_setOf_cylVolume_lt a y y (profile a b) ha).subset fun l hl =>
        ⟨⟨hl.1, boundedBy_of_cylVolume_lt ha hl.1 (not_le.mp hl.2)⟩, not_le.mp hl.2⟩
  simpa using hu.summable_mul_pow (f := fun _ => (1 : ℤ⟦X⟧)) (q := (X : ℤ⟦X⟧))

end HJO.Summable
