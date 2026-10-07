/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Int.Interval
public import HJO.RankOneDinv.Diagram
public import HJO.Paths.ReturnPath
public meta import HJO.Attr

/-! # The rank-one dinv identity: gap coordinates, tail counts and hooks

For coprime `1 < a < b` every gap of `⟨a, b⟩` is uniquely `rb - ai` with `1 ≤ r ≤ a - 1` and
`i ≥ 1`, which identifies the gap set with the staircase diagram `HJO.Gaps.gapDiagram`, the gap
order with the reverse product order, and an order filter `F` with the cell set of its primitive
path `P_F`, namely `HJO.ReturnPath.cellSet a b F`. This file builds that dictionary and relates
the two counts it converts into each other: the tail counts `E_P(u, v)` of the cells of a path
whose arm is at least `u` and whose leg is at least `v`, and the signed count of pairs of gaps
computed by the quadratic form at the indicator vector of `F`.

The staircase bound `β u = ⌊ub/a⌋` of `HJO.Gaps.beta` runs through everything. The hook
condition at a cell is exactly `β (arm) ≤ leg ≤ β (arm + 1)`, so the hook count is an
alternating sum of tail counts by inclusion-exclusion on the arm; a pair of gaps lies in the
window `[0, a)` exactly when its coordinates satisfy `i' = i + β (r' - r)`, and in the window
`[b, a + b)` exactly when `i' = i + β (r' - r - 1)`, so each signed count is likewise a sum of
tail counts. The reflection `β (-u) = -β u - 1` folds the pairs with `r' < r` onto the pairs
with `r' > r`.

Two conventions matter. The arm displaces the COLUMN index and the leg displaces the ROW index,
so `le_arm_iff` and `le_leg_iff` are two separate memberships, `(r - u, i)` and `(r, i + v)`;
their conjunction is strictly weaker than membership of `(r - u, i + v)`. And the staircase
bound is defined on all of `ℤ`, since the reflection and the second window evaluate it at
negative arguments, while the tail count thresholds are naturals, so a threshold `β u` is
written `(β u).toNat`, faithful because `β u ≥ 0` at every `u ≥ 0` used here.
-/

@[expose] public section

open Finset NumericalSemigroup

namespace HJO.RankOneDinv

/-! ### Integer representations of a gap -/

variable {a b : ℕ}

/-- Coprimality of two naturals gives coprimality of their integer images. -/
theorem isCoprime_intCast (hco : a.Coprime b) : IsCoprime (a : ℤ) (b : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  simpa [Int.gcd] using hco

/-- **Integer representations differ by a shift.** If `xa + yb = x'a + y'b` then
`x' = x + kb` and `y' = y - ka` for a single integer `k`. -/
@[hjo "lem_representation_shift"]
theorem exists_shift (hco : a.Coprime b) (ha : 0 < a) {x y x' y' : ℤ}
    (h : x * a + y * b = x' * a + y' * b) : ∃ k : ℤ, x' = x + k * b ∧ y' = y - k * a := by
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hdvd : (a : ℤ) ∣ y - y' := by
    refine (isCoprime_intCast hco).dvd_of_dvd_mul_right ⟨x' - x, ?_⟩
    linarith
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨k, ?_, by linarith⟩
  have h2 : (x' - x) * a = (y - y') * b := by linarith
  rw [hk] at h2
  have h3 : (x' - x) * a = (k * b) * a := by rw [h2]; ring
  have := mul_right_cancel₀ (b := (a : ℤ)) (by omega) h3
  linarith

/-- Because `b` is invertible modulo `a`, every residue class modulo `a` is that of `rb` for
some `r < a`. -/
theorem exists_residue (hco : a.Coprime b) (ha : 0 < a) (g : ℕ) :
    ∃ j, j < a ∧ g % a = j * b % a := by
  have hinj : ∀ j ∈ range a, ∀ j' ∈ range a, j * b % a = j' * b % a → j = j' := by
    intro j hj j' hj' hjj
    rw [mem_range] at hj hj'
    have h1 : j * b ≡ j' * b [MOD a] := hjj
    have h2 := Nat.ModEq.cancel_right_of_coprime
      (by simpa [Nat.Coprime, Nat.gcd_comm] using hco) h1
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at h2
  obtain ⟨j, hj, hjeq⟩ := Finset.surj_on_of_inj_on_of_card_le (s := range a) (t := range a)
    (f := fun j _ => j * b % a) (fun j _ => mem_range.mpr (Nat.mod_lt _ ha))
    (fun j j' hj hj' => hinj j hj j' hj') le_rfl (g % a) (mem_range.mpr (Nat.mod_lt _ ha))
  exact ⟨j, mem_range.mp hj, hjeq⟩

/-- A gap is positive: `0 = 0 a + 0 b` lies in the semigroup. -/
theorem pos_of_mem_gaps (hco : a.Coprime b) {g : ℕ} (hg : g ∈ (finspan {a, b}).gaps) : 0 < g := by
  rcases Nat.eq_zero_or_pos g with rfl | h
  · rw [Gaps.mem_gaps_iff_not_exists a b hco] at hg
    exact absurd ⟨0, 0, by simp⟩ hg
  · exact h

/-- **Every gap is a column value.** A gap `g` is `rb - ai` with `1 ≤ r ≤ a - 1` and
`i ≥ 1`. -/
@[hjo "lem_gap_column_form"]
theorem exists_column_form (hco : a.Coprime b) (ha : 0 < a) {g : ℕ}
    (hg : g ∈ (finspan {a, b}).gaps) :
    ∃ r i : ℕ, 1 ≤ r ∧ r ≤ a - 1 ∧ 1 ≤ i ∧ (g : ℤ) = r * b - a * i := by
  obtain ⟨j, hja, hmod⟩ := exists_residue hco ha g
  have hgap := hg
  rw [Gaps.mem_gaps_iff_not_exists a b hco,
    Nat.exists_mul_add_mul_eq_iff_mul_le_of_coprime hco hja hmod] at hgap
  have hjb : g < j * b := by omega
  obtain ⟨i, hi⟩ := (Nat.modEq_iff_dvd' (le_of_lt hjb)).mp hmod
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · simp at hjb
    · exact h
  refine ⟨j, i, hj1, by omega, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos i with rfl | h
    · omega
    · exact h
  · have h4 : ((j * b - g : ℕ) : ℤ) = ((a * i : ℕ) : ℤ) := by rw [hi]
    push_cast [Nat.cast_sub (le_of_lt hjb)] at h4
    linarith

/-- Membership in `HJO.Gaps.gapDiagram`, with the column bound written `r ≤ a - 1` rather
than `r < a`, the shape in which the gap diagram `𝒟` is cut out in
`HJO/RankOneDinv/Diagram.lean`. -/
theorem mem_gapDiagram (ha : 0 < a) {p : ℕ × ℕ} :
    p ∈ Gaps.gapDiagram a b ↔ 1 ≤ p.1 ∧ p.1 ≤ a - 1 ∧ 1 ≤ p.2 ∧ a * p.2 < p.1 * b := by
  rw [Gaps.mem_gapDiagram]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, by omega, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, by omega, h3, h4⟩

/-- **The window characterising the staircase bound**: `0 ≤ ub - va < a` exactly when
`v = β u`. -/
@[hjo "lem_beta_window"]
theorem beta_window (ha : 0 < a) (u v : ℤ) :
    (0 ≤ u * b - v * a ∧ u * b - v * a < a) ↔ v = Gaps.beta a b u := by
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  rw [Gaps.beta]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : v ≤ u * b / a := (Int.le_ediv_iff_mul_le ha').mpr (by linarith)
    have h4 : u * b / a < v + 1 := (Int.ediv_lt_iff_lt_mul ha').mpr (by linarith)
    omega
  · rintro rfl
    have h3 : u * b / a * a ≤ u * b := (Int.le_ediv_iff_mul_le ha').mp le_rfl
    have h4 : u * b < (u * b / a + 1) * a := (Int.ediv_lt_iff_lt_mul ha').mp (by omega)
    exact ⟨by linarith, by linarith⟩

/-- The staircase bound is nonnegative at a nonnegative argument. -/
theorem beta_nonneg (ha : 0 < a) {u : ℤ} (hu : 0 ≤ u) : 0 ≤ Gaps.beta a b u :=
  Int.ediv_nonneg (mul_nonneg hu (by positivity)) (by positivity)

/-- **The staircase bound is never attained exactly**: if `a ∤ u` then `β u * a ≠ ub`. -/
@[hjo "lem_beta_not_integer"]
theorem beta_mul_ne (hco : a.Coprime b) {u : ℤ} (hu : ¬ (a : ℤ) ∣ u) :
    Gaps.beta a b u * a ≠ u * b := by
  intro h
  exact hu ((isCoprime_intCast hco).dvd_of_dvd_mul_right ⟨Gaps.beta a b u, by linarith⟩)

/-- **The reflection of the staircase bound**: `β (-u) = -β u - 1` whenever `a ∤ u`. -/
@[hjo "lem_beta_reflection"]
theorem beta_neg (hco : a.Coprime b) (ha : 0 < a) {u : ℤ} (hu : ¬ (a : ℤ) ∣ u) :
    Gaps.beta a b (-u) = -Gaps.beta a b u - 1 := by
  obtain ⟨h1, h2⟩ := (beta_window (b := b) ha u (Gaps.beta a b u)).mpr rfl
  have h3 : Gaps.beta a b u * a < u * b := lt_of_le_of_ne (by linarith) (beta_mul_ne hco hu)
  refine ((beta_window ha (-u) (-Gaps.beta a b u - 1)).mp ⟨?_, ?_⟩).symm
  · have : -u * b - (-Gaps.beta a b u - 1) * a = a - (u * b - Gaps.beta a b u * a) := by ring
    rw [this]; linarith
  · have : -u * b - (-Gaps.beta a b u - 1) * a = a - (u * b - Gaps.beta a b u * a) := by ring
    rw [this]; linarith

/-- **The staircase bound stays below `b`**: `β r ≤ b - 1` for `1 ≤ r ≤ a - 1`. -/
@[hjo "lem_beta_lt_b"]
theorem beta_le_sub_one (ha : 0 < a) (hb : 0 < b) {r : ℤ} (_hr1 : 1 ≤ r) (hr : r ≤ a - 1) :
    Gaps.beta a b r ≤ b - 1 := by
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  obtain ⟨h1, h2⟩ := (beta_window (b := b) ha r (Gaps.beta a b r)).mpr rfl
  have h3 : r * b ≤ ((a : ℤ) - 1) * b := by nlinarith
  have h4 : Gaps.beta a b r * a < (b : ℤ) * a := by nlinarith
  have h5 := lt_of_mul_lt_mul_right h4 (le_of_lt ha')
  omega

/-- **The row index of a diagram cell is bounded**: `i ≤ β r` for `(r, i) ∈ 𝒟`. -/
@[hjo "lem_diagram_index_bound"]
theorem le_beta_of_mem (ha : 0 < a) {p : ℕ × ℕ} (hp : p ∈ Gaps.gapDiagram a b) :
    (p.2 : ℤ) ≤ Gaps.beta a b p.1 := by
  obtain ⟨-, -, -, h4⟩ := (mem_gapDiagram ha).mp hp
  have h5 : (a : ℤ) * p.2 < (p.1 : ℤ) * b := by exact_mod_cast h4
  rw [Gaps.beta]
  exact (Int.le_ediv_iff_mul_le (by exact_mod_cast ha)).mpr (by linarith)

/-- The bound `r ≤ a - 1`, whose subtraction is truncated in `ℕ`, read in `ℤ`. -/
theorem cast_le_pred (ha : 0 < a) {r : ℕ} (h : r ≤ a - 1) : (r : ℤ) ≤ (a : ℤ) - 1 := by
  have h1 : (r : ℤ) ≤ ((a - 1 : ℕ) : ℤ) := Nat.cast_le.mpr h
  rwa [Nat.cast_sub ha, Nat.cast_one] at h1

/-- The gap labelled by a diagram cell: `label (r, i) = rb - ai`. The natural subtraction is
harmless on the diagram, where `ai < rb`. -/
def label (a b : ℕ) (p : ℕ × ℕ) : ℕ := p.1 * b - a * p.2

/-- The label of a cell, read in `ℤ` with no truncation. -/
theorem label_cast {p : ℕ × ℕ} (h : a * p.2 ≤ p.1 * b) :
    ((label a b p : ℕ) : ℤ) = (p.1 : ℤ) * b - a * p.2 := by
  rw [label, Nat.cast_sub h]
  push_cast
  ring

/-- The label of a diagram cell is a gap. -/
theorem label_mem_gaps (hco : a.Coprime b) (ha : 0 < a) {p : ℕ × ℕ} (hp : p ∈ Gaps.gapDiagram a b) :
    label a b p ∈ (finspan {a, b}).gaps := by
  obtain ⟨h1, h2, h3, h4⟩ := (mem_gapDiagram ha).mp hp
  exact ReturnPath.mem_gaps_of_sub hco (by omega) h3 h4

/-- Distinct diagram cells carry distinct labels: `a ∣ r - r'` is impossible for
`|r - r'| ≤ a - 2`. -/
theorem label_injOn (hco : a.Coprime b) (ha : 1 < a) :
    Set.InjOn (label a b) (Gaps.gapDiagram a b) := by
  intro p hp q hq h
  simp only [Finset.mem_coe] at hp hq
  obtain ⟨hp1, hp2, hp3, hp4⟩ := (mem_gapDiagram (by omega : 0 < a)).mp hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := (mem_gapDiagram (by omega : 0 < a)).mp hq
  have hz : (p.1 : ℤ) * b - a * p.2 = (q.1 : ℤ) * b - a * q.2 := by
    rw [← label_cast (le_of_lt hp4), ← label_cast (le_of_lt hq4), h]
  obtain ⟨k, hk⟩ : (a : ℤ) ∣ ((p.1 : ℤ) - q.1) :=
    (isCoprime_intCast hco).dvd_of_dvd_mul_right ⟨(p.2 : ℤ) - q.2, by linarith⟩
  have ha2 : (2 : ℤ) ≤ a := by exact_mod_cast ha
  have hp2' := cast_le_pred (a := a) (by omega) hp2
  have hq2' := cast_le_pred (a := a) (by omega) hq2
  have hp1' : (1 : ℤ) ≤ p.1 := by exact_mod_cast hp1
  have hq1' : (1 : ℤ) ≤ q.1 := by exact_mod_cast hq1
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with h1 | h1 | h1
    · nlinarith
    · exact h1
    · nlinarith
  rw [hk0, mul_zero] at hk
  have hfst : p.1 = q.1 := by exact_mod_cast sub_eq_zero.mp hk
  have ha0 : (0 : ℤ) < a := by omega
  have hsnd : p.2 = q.2 := by
    have : (a : ℤ) * p.2 = (a : ℤ) * q.2 := by
      rw [hfst] at hz
      linarith
    exact_mod_cast mul_left_cancel₀ (by omega : (a : ℤ) ≠ 0) this
  exact Prod.ext hfst hsnd

/-- Every gap is the label of a diagram cell. -/
theorem label_surjOn (hco : a.Coprime b) (ha : 1 < a) :
    Set.SurjOn (label a b) (Gaps.gapDiagram a b) ((finspan {a, b}).gaps) := by
  intro g hg
  simp only [Finset.mem_coe] at hg
  obtain ⟨r, i, hr1, hr2, hi1, heq⟩ := exists_column_form hco (by omega) hg
  have hgpos : (0 : ℤ) < (g : ℤ) := by exact_mod_cast pos_of_mem_gaps hco hg
  have hlt : a * i < r * b := by
    have h1 : (a : ℤ) * i < (r : ℤ) * b := by linarith
    exact_mod_cast h1
  refine ⟨(r, i), (mem_gapDiagram (by omega : 0 < a)).mpr ⟨hr1, hr2, hi1, hlt⟩, ?_⟩
  have hc := label_cast (a := a) (b := b) (p := (r, i)) (le_of_lt hlt)
  have : ((label a b (r, i) : ℕ) : ℤ) = ((g : ℕ) : ℤ) := by rw [hc]; push_cast; linarith
  exact_mod_cast this

/-- **The gap coordinates are a bijection**: `(r, i) ↦ rb - ai` is a bijection from the gap
diagram onto the gap set. -/
@[hjo "lem_gap_coordinates"]
theorem bijOn_label (hco : a.Coprime b) (ha : 1 < a) :
    Set.BijOn (label a b) (Gaps.gapDiagram a b) ((finspan {a, b}).gaps) :=
  ⟨fun _ hp => label_mem_gaps hco (by omega) hp, label_injOn hco ha, label_surjOn hco ha⟩

/-- **The gap order is the reverse product order**: `rb - ai ≼ r'b - ai'` exactly when
`r ≤ r'` and `i' ≤ i`. -/
@[hjo "lem_diagram_order"]
theorem gapLE_label_iff (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    {p q : ℕ × ℕ} (hp : p ∈ Gaps.gapDiagram a b) (hq : q ∈ Gaps.gapDiagram a b) :
    Gaps.GapLE a b (label a b p) (label a b q) ↔ p.1 ≤ q.1 ∧ q.2 ≤ p.2 := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := (mem_gapDiagram (by omega : 0 < a)).mp hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := (mem_gapDiagram (by omega : 0 < a)).mp hq
  have ep := label_cast (a := a) (b := b) (p := p) (le_of_lt hp4)
  have eq' := label_cast (a := a) (b := b) (p := q) (le_of_lt hq4)
  constructor
  · rintro ⟨x, y, hxy⟩
    have hz : ((p.2 : ℤ) - q.2) * a + ((q.1 : ℤ) - p.1) * b = (x : ℤ) * a + (y : ℤ) * b := by
      have h1 : ((label a b p + (x * a + y * b) : ℕ) : ℤ) = ((label a b q : ℕ) : ℤ) := by
        rw [hxy]
      push_cast [ep, eq'] at h1
      linarith
    obtain ⟨k, hk1, hk2⟩ := exists_shift hco (by omega : 0 < a) hz
    have hp2b : (p.2 : ℤ) ≤ (b : ℤ) - 1 := by
      refine (le_beta_of_mem (by omega : 0 < a) hp).trans ?_
      exact beta_le_sub_one (by omega) hb (by exact_mod_cast hp1)
        (cast_le_pred (a := a) (by omega) hp2)
    have hq2' := cast_le_pred (a := a) (by omega) hq2
    have hp1' : (1 : ℤ) ≤ p.1 := by exact_mod_cast hp1
    have hq1' : (1 : ℤ) ≤ q.2 := by exact_mod_cast hq3
    have hx0 : (0 : ℤ) ≤ x := by positivity
    have hy0 : (0 : ℤ) ≤ y := by positivity
    have ha0 : (0 : ℤ) < a := by omega
    have hb0 : (0 : ℤ) < b := by exact_mod_cast hb
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with h1 | h1 | h1
      · nlinarith
      · exact h1
      · nlinarith
    rw [hk0] at hk1 hk2
    constructor
    · have : (0 : ℤ) ≤ (q.1 : ℤ) - p.1 := by linarith
      exact_mod_cast Int.le_of_sub_nonneg this
    · have : (0 : ℤ) ≤ (p.2 : ℤ) - q.2 := by linarith
      exact_mod_cast Int.le_of_sub_nonneg this
  · rintro ⟨h1, h2⟩
    refine ⟨p.2 - q.2, q.1 - p.1, ?_⟩
    have e3 : ((p.2 - q.2 : ℕ) : ℤ) = (p.2 : ℤ) - q.2 := Nat.cast_sub h2
    have e4 : ((q.1 - p.1 : ℕ) : ℤ) = (q.1 : ℤ) - p.1 := Nat.cast_sub h1
    have key : ((label a b p + ((p.2 - q.2) * a + (q.1 - p.1) * b) : ℕ) : ℤ)
        = ((label a b q : ℕ) : ℤ) := by
      push_cast [e3, e4, ep, eq']
      ring
    exact_mod_cast key

/-- A cell of the gap diagram has row index at most `b`. -/
theorem snd_le_of_mem {p : ℕ × ℕ} (hp : p ∈ Gaps.gapDiagram a b) : p.2 ≤ b :=
  (Gaps.snd_lt_of_mem_gapDiagram hp).le

/-! ### The diagram of an order filter -/

/-- Membership in the filter diagram `HJO.ReturnPath.cellSet`: a cell of the gap diagram whose
label lies in the filter. -/
theorem mem_filterDiagram {F : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ ReturnPath.cellSet a b F ↔ p ∈ Gaps.gapDiagram a b ∧ label a b p ∈ F :=
  ReturnPath.mem_cellSet_iff_mem_gapDiagram

variable {F : Finset ℕ}

/-- **A filter diagram column is an initial segment**: if `(r, i)` lies in `𝒟_F` and
`1 ≤ i' ≤ i` then `(r, i')` lies in `𝒟_F`. -/
@[hjo "lem_filter_column_segment"]
theorem mem_filterDiagram_of_le (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hF : Gaps.IsOrderFilter a b F) {p : ℕ × ℕ} (hp : p ∈ ReturnPath.cellSet a b F) {i : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i ≤ p.2) : (p.1, i) ∈ ReturnPath.cellSet a b F := by
  obtain ⟨hpD, hpF⟩ := mem_filterDiagram.mp hp
  obtain ⟨h1, h2, h3, h4⟩ := (mem_gapDiagram (by omega : 0 < a)).mp hpD
  have hmem : (p.1, i) ∈ Gaps.gapDiagram a b := by
    refine (mem_gapDiagram (by omega : 0 < a)).mpr ⟨h1, h2, hi1, ?_⟩
    change a * i < p.1 * b
    have : a * i ≤ a * p.2 := Nat.mul_le_mul_left a hi2
    omega
  refine mem_filterDiagram.mpr ⟨hmem, hF.2 _ hpF _ (label_mem_gaps hco (by omega) hmem) ?_⟩
  exact (gapLE_label_iff hco ha hb hpD hmem).mpr ⟨le_rfl, hi2⟩

/-- **The filter diagram is closed to the right**: if `(r, i)` lies in `𝒟_F` and
`r + 1 ≤ a - 1` then `(r + 1, i)` lies in `𝒟_F`. -/
@[hjo "lem_filter_row_shift"]
theorem mem_filterDiagram_succ (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hF : Gaps.IsOrderFilter a b F) {p : ℕ × ℕ} (hp : p ∈ ReturnPath.cellSet a b F)
    (hlt : p.1 + 1 ≤ a - 1) : (p.1 + 1, p.2) ∈ ReturnPath.cellSet a b F := by
  obtain ⟨hpD, hpF⟩ := mem_filterDiagram.mp hp
  obtain ⟨h1, h2, h3, h4⟩ := (mem_gapDiagram (by omega : 0 < a)).mp hpD
  have hmem : (p.1 + 1, p.2) ∈ Gaps.gapDiagram a b := by
    refine (mem_gapDiagram (by omega : 0 < a)).mpr ⟨by omega, hlt, h3, ?_⟩
    change a * p.2 < (p.1 + 1) * b
    have : (p.1 + 1) * b = p.1 * b + b := by ring
    omega
  refine mem_filterDiagram.mpr ⟨hmem, hF.2 _ hpF _ (label_mem_gaps hco (by omega) hmem) ?_⟩
  exact (gapLE_label_iff hco ha hb hpD hmem).mpr ⟨by omega, le_rfl⟩

/-- **The cells of the primitive path are the filter diagram**: for `1 ≤ r ≤ a - 1` and
`i ≥ 1`, the pair `(r, i)` lies in `𝒟_F` exactly when `i ≤ y_r`, where `y` is the height vector
of `P_F`. -/
@[hjo "lem_filter_diagram_heights"]
theorem mem_filterDiagram_iff_le_ht (hco : a.Coprime b) (ha : 1 < a)
    (hF : Gaps.IsOrderFilter a b F) {r i : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ a - 1) (hi1 : 1 ≤ i) :
    (r, i) ∈ ReturnPath.cellSet a b F ↔ i ≤ Paths.ht (Primitive.primitivePath a b F) r := by
  rw [Primitive.ht_primitivePath_of_lt F (by omega : r < a),
    ReturnPath.le_primitiveHeight_iff hco hF (by omega : r < a) hi1, mem_filterDiagram]
  constructor
  · intro h
    obtain ⟨-, -, -, h4⟩ := (mem_gapDiagram (by omega : 0 < a)).mp h.1
    exact ⟨snd_le_of_mem h.1, h4, h.2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(mem_gapDiagram (by omega : 0 < a)).mpr ⟨hr1, hr2, hi1, h2⟩, h3⟩

/-- **The primitive path stays below the diagonal**: `y_r ≤ β r` for `1 ≤ r ≤ a - 1`. -/
@[hjo "lem_primitive_path_below_diagonal"]
theorem ht_le_beta (hco : a.Coprime b) (ha : 1 < a) (hF : Gaps.IsOrderFilter a b F) {r : ℕ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ a - 1) :
    (Paths.ht (Primitive.primitivePath a b F) r : ℤ) ≤ Gaps.beta a b r := by
  rcases Nat.eq_zero_or_pos (Paths.ht (Primitive.primitivePath a b F) r) with h | h
  · rw [h]
    simpa using beta_nonneg (a := a) (b := b) (by omega) (by positivity : (0 : ℤ) ≤ (r : ℤ))
  · have hmem := (mem_filterDiagram_iff_le_ht hco ha hF hr1 hr2 h).mpr le_rfl
    exact le_beta_of_mem (by omega) (mem_filterDiagram.mp hmem).1

/-- **The primitive path is nondecreasing**: `y_r ≤ y_{r+1}` for `r ≤ a - 1`. -/
@[hjo "lem_primitive_path_monotone"]
theorem ht_le_ht_succ (hco : a.Coprime b) (ha : 1 < a) (hF : Gaps.IsOrderFilter a b F) {r : ℕ}
    (hr : r ≤ a - 1) : Paths.ht (Primitive.primitivePath a b F) r
      ≤ Paths.ht (Primitive.primitivePath a b F) (r + 1) :=
  (ReturnPath.isBelowDiagonal_primitivePath hco (by omega) hF).2.2.1 r (by omega)

/-- A height of a candidate path never exceeds `bN`. -/
theorem ht_le_mul {N : ℕ} (y : Paths.Heights a b N) (r : ℕ) : Paths.ht y r ≤ b * N := by
  rw [Paths.ht]
  split_ifs with h
  · exact Nat.lt_succ_iff.mp (y ⟨r, h⟩).isLt
  · exact le_rfl

/-- The heights of a below-diagonal path are monotone in the column index, the constant value
`bN` past the last column included. -/
theorem ht_mono {N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y) {j k : ℕ}
    (hjk : j ≤ k) : Paths.ht y j ≤ Paths.ht y k := by
  induction k with
  | zero =>
    obtain rfl : j = 0 := by omega
    exact le_rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hjk with h | h
    · subst h
      exact le_rfl
    · rcases Nat.lt_or_ge k (a * N) with hk | hk
      · exact (ih (by omega)).trans (hy.2.2.1 k hk)
      · have hlast : Paths.ht y (k + 1) = b * N := by
          rw [Paths.ht]
          split_ifs with h'
          · exact absurd h' (by omega)
          · rfl
        rw [hlast]
        exact ht_le_mul y j

/-- A positive row of a below-diagonal path is first reached at a positive column, the path
starting at height `0`. -/
theorem one_le_firstReach {N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    {r i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ Paths.ht y r) : 1 ≤ Paths.firstReach y i := by
  have hle : i ≤ Paths.ht y (a * N) := by
    rw [hy.2.1]
    exact le_trans hi (ht_le_mul y r)
  have h2 := ReturnPath.le_ht_firstReach y hle
  rcases Nat.eq_zero_or_pos (Paths.firstReach y i) with h | h
  · rw [h, hy.1] at h2
    omega
  · exact h

/-! ### Arms, legs and the hook criterion -/

/-- **The arm is bounded by the width**: a cell of a below-diagonal `(a, b)`-path has
`arm ≤ a - 2`, the lower bound `0 ≤ arm` being automatic in `ℕ`. -/
@[hjo "lem_arm_bound"]
theorem arm_le {y : Paths.Heights a b 1} (hy : Paths.IsBelowDiagonal y) {r i : ℕ} (hr : r < a)
    (hi1 : 1 ≤ i) (hi : i ≤ Paths.ht y r) : Paths.arm y r i ≤ a - 2 := by
  have h1 := ReturnPath.firstReach_le y (by omega : r ≤ a * 1) hi
  have h2 := one_le_firstReach hy hi1 hi
  rw [Paths.arm]
  omega

/-- **The hook criterion**: at a cell of a below-diagonal `(a, b)`-path the two hook
conditions `b·arm ≤ a (leg + 1)` and `a·leg < b (arm + 1)` hold exactly when
`β (arm) ≤ leg ≤ β (arm + 1)`. -/
@[hjo "lem_hook_criterion"]
theorem hook_iff_beta (hco : a.Coprime b) (ha : 1 < a) {y : Paths.Heights a b 1}
    (hy : Paths.IsBelowDiagonal y) {r i : ℕ} (hr : r < a) (hi1 : 1 ≤ i)
    (hi : i ≤ Paths.ht y r) :
    (b * Paths.arm y r i ≤ a * (Paths.leg y r i + 1) ∧
        a * Paths.leg y r i < b * (Paths.arm y r i + 1)) ↔
      Gaps.beta a b (Paths.arm y r i) ≤ (Paths.leg y r i : ℤ) ∧
        (Paths.leg y r i : ℤ) ≤ Gaps.beta a b (Paths.arm y r i + 1) := by
  have ha0 : (0 : ℤ) < a := by exact_mod_cast (by omega : 0 < a)
  have hA := arm_le hy hr hi1 hi
  set A : ℕ := Paths.arm y r i with hAdef
  set L : ℕ := Paths.leg y r i with hLdef
  have hA0 : (0 : ℤ) ≤ (A : ℤ) := by positivity
  have hA2 : (A : ℤ) ≤ (a : ℤ) - 2 := by
    have h1 : (A : ℤ) ≤ ((a - 2 : ℕ) : ℤ) := Nat.cast_le.mpr hA
    have h2 : ((a - 2 : ℕ) : ℤ) = (a : ℤ) - 2 := by
      rcases Nat.lt_or_ge a 2 with h | h
      · omega
      · rw [Nat.cast_sub h]; norm_num
    omega
  have hL0 : (0 : ℤ) ≤ (L : ℤ) := by positivity
  have ne1 : (b : ℤ) * A ≠ (a : ℤ) * ((L : ℤ) + 1) := by
    intro heq
    have hdvd : (a : ℤ) ∣ (A : ℤ) :=
      (isCoprime_intCast hco).dvd_of_dvd_mul_right ⟨(L : ℤ) + 1, by linarith⟩
    obtain ⟨m, hm⟩ := hdvd
    rcases eq_or_lt_of_le hA0 with h | h
    · rw [← h] at heq
      simp only [mul_zero] at heq
      nlinarith
    · have hm1 : 1 ≤ m := by nlinarith
      nlinarith
  have ne2 : (a : ℤ) * L ≠ (b : ℤ) * ((A : ℤ) + 1) := by
    intro heq
    have hdvd : (a : ℤ) ∣ ((A : ℤ) + 1) :=
      (isCoprime_intCast hco).dvd_of_dvd_mul_right ⟨(L : ℤ), by linarith⟩
    obtain ⟨m, hm⟩ := hdvd
    have hm1 : 1 ≤ m := by nlinarith
    nlinarith
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (b : ℤ) * A ≤ (a : ℤ) * ((L : ℤ) + 1) := by exact_mod_cast h1
    have h2' : (a : ℤ) * L < (b : ℤ) * ((A : ℤ) + 1) := by exact_mod_cast h2
    refine ⟨?_, ?_⟩
    · rw [Gaps.beta]
      have h3 : (A : ℤ) * b < ((L : ℤ) + 1) * a := by
        have := lt_of_le_of_ne h1' ne1
        nlinarith
      have h4 := (Int.ediv_lt_iff_lt_mul ha0).mpr h3
      omega
    · rw [Gaps.beta]
      exact (Int.le_ediv_iff_mul_le ha0).mpr (by nlinarith)
  · rintro ⟨h1, h2⟩
    rw [Gaps.beta] at h1 h2
    have h3 : (A : ℤ) * b < ((L : ℤ) + 1) * a := (Int.ediv_lt_iff_lt_mul ha0).mp (by omega)
    have h4 : (L : ℤ) * a ≤ ((A : ℤ) + 1) * b := (Int.le_ediv_iff_mul_le ha0).mp h2
    refine ⟨?_, ?_⟩
    · have : (b : ℤ) * A ≤ (a : ℤ) * ((L : ℤ) + 1) := by nlinarith
      exact_mod_cast this
    · have h5 : (a : ℤ) * L ≤ (b : ℤ) * ((A : ℤ) + 1) := by nlinarith
      have : (a : ℤ) * L < (b : ℤ) * ((A : ℤ) + 1) := lt_of_le_of_ne h5 ne2
      exact_mod_cast this

/-- The height criterion in the shape used for a pair variable. -/
theorem mem_filterDiagram_iff_le_ht' (hco : a.Coprime b) (ha : 1 < a)
    (hF : Gaps.IsOrderFilter a b F) {p : ℕ × ℕ} (h1 : 1 ≤ p.1) (h2 : p.1 ≤ a - 1)
    (h3 : 1 ≤ p.2) :
    p ∈ ReturnPath.cellSet a b F ↔ p.2 ≤ Paths.ht (Primitive.primitivePath a b F) p.1 := by
  simpa using mem_filterDiagram_iff_le_ht hco ha hF (r := p.1) (i := p.2) h1 h2 h3

/-- A cell of a filter diagram is a cell of the primitive path of that filter. -/
theorem cell_of_mem (hco : a.Coprime b) (ha : 1 < a) (hF : Gaps.IsOrderFilter a b F) {p : ℕ × ℕ}
    (hp : p ∈ ReturnPath.cellSet a b F) :
    1 ≤ p.1 ∧ p.1 ≤ a - 1 ∧ 1 ≤ p.2 ∧ p.2 ≤ Paths.ht (Primitive.primitivePath a b F) p.1 := by
  obtain ⟨h1, h2, h3, -⟩ := (mem_gapDiagram (by omega : 0 < a)).mp (mem_filterDiagram.mp hp).1
  exact ⟨h1, h2, h3, (mem_filterDiagram_iff_le_ht' hco ha hF h1 h2 h3).mp hp⟩

/-- The cell set of the primitive path of an order filter is its filter diagram. -/
theorem cells_eq (hco : a.Coprime b) (ha : 1 < a) (hF : Gaps.IsOrderFilter a b F) :
    {p ∈ Ico 1 (a * 1) ×ˢ Icc 1 (b * 1) | p.2 ≤ Paths.ht (Primitive.primitivePath a b F) p.1}
      = ReturnPath.cellSet a b F := by
  ext p
  simp only [mem_filter, mem_product, mem_Ico, mem_Icc, Nat.mul_one]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
    exact (mem_filterDiagram_iff_le_ht' hco ha hF h1 (by omega) h3).mpr h5
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := cell_of_mem hco ha hF h
    exact ⟨⟨⟨h1, by omega⟩, h3, snd_le_of_mem (mem_filterDiagram.mp h).1⟩, h4⟩

/-- **The leg condition as membership**: at a cell `(r, i)` of `P_F` and for `v ≥ 0`,
`leg (r, i) ≥ v` exactly when `(r, i + v)` lies in `𝒟_F`. -/
@[hjo "lem_leg_as_membership"]
theorem le_leg_iff (hco : a.Coprime b) (ha : 1 < a) (hF : Gaps.IsOrderFilter a b F) {r i : ℕ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ a - 1) (hi1 : 1 ≤ i)
    (hi : i ≤ Paths.ht (Primitive.primitivePath a b F) r) (v : ℕ) :
    v ≤ Paths.leg (Primitive.primitivePath a b F) r i ↔ (r, i + v) ∈ ReturnPath.cellSet a b F := by
  rw [mem_filterDiagram_iff_le_ht hco ha hF hr1 hr2 (by omega : 1 ≤ i + v), Paths.leg]
  omega

/-- **The arm condition as membership**: at a cell `(r, i)` of `P_F` and for `u ≥ 0`,
`arm (r, i) ≥ u` exactly when `r - u ≥ 1` and `(r - u, i)` lies in `𝒟_F`. The displaced
coordinate is the column index, where the leg condition displaces the row index; the
conjunction of the two conditions is strictly weaker than membership of `(r - u, i + v)`. -/
@[hjo "lem_arm_as_membership"]
theorem le_arm_iff (hco : a.Coprime b) (ha : 1 < a) (hF : Gaps.IsOrderFilter a b F) {r i : ℕ}
    (_hr1 : 1 ≤ r) (hr2 : r ≤ a - 1) (hi1 : 1 ≤ i)
    (hi : i ≤ Paths.ht (Primitive.primitivePath a b F) r) (u : ℕ) :
    u ≤ Paths.arm (Primitive.primitivePath a b F) r i ↔
      u + 1 ≤ r ∧ (r - u, i) ∈ ReturnPath.cellSet a b F := by
  have hbd : Paths.IsBelowDiagonal (Primitive.primitivePath a b F) :=
    ReturnPath.isBelowDiagonal_primitivePath hco (by omega) hF
  have h1 : Paths.firstReach (Primitive.primitivePath a b F) i ≤ r :=
    ReturnPath.firstReach_le _ (by omega : r ≤ a * 1) hi
  have h2 : 1 ≤ Paths.firstReach (Primitive.primitivePath a b F) i :=
    one_le_firstReach hbd hi1 hi
  have h3 : i ≤ Paths.ht (Primitive.primitivePath a b F)
      (Paths.firstReach (Primitive.primitivePath a b F) i) := by
    refine ReturnPath.le_ht_firstReach _ ?_
    rw [hbd.2.1]
    exact le_trans hi (ht_le_mul _ r)
  rw [Paths.arm]
  constructor
  · intro h
    refine ⟨by omega, ?_⟩
    rw [mem_filterDiagram_iff_le_ht hco ha hF (by omega) (by omega) hi1]
    exact le_trans h3 (ht_mono hbd (by omega))
  · rintro ⟨hru, hmem⟩
    rw [mem_filterDiagram_iff_le_ht hco ha hF (by omega) (by omega) hi1] at hmem
    have := ReturnPath.firstReach_le _ (by omega : r - u ≤ a * 1) hmem
    omega

/-- **The tail counts count shifted pairs of cells**:
`E_{P_F}(u, v) = #{(r, i) ∈ 𝒟_F : (r + u, i + v) ∈ 𝒟_F}`. -/
@[hjo "lem_tail_count_as_pairs"]
theorem tailCount_eq_card (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hF : Gaps.IsOrderFilter a b F) (u v : ℕ) :
    Paths.tailCount (Primitive.primitivePath a b F) u v
      = #{p ∈ ReturnPath.cellSet a b F | (p.1 + u, p.2 + v) ∈ ReturnPath.cellSet a b F} := by
  rw [Paths.tailCount, ← filter_filter, cells_eq hco ha hF]
  refine Finset.card_nbij' (fun p => (p.1 - u, p.2)) (fun p => (p.1 + u, p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, mem_filter] at hp ⊢
    obtain ⟨hpD, hu, hv⟩ := hp
    obtain ⟨c1, c2, c3, c4⟩ := cell_of_mem hco ha hF hpD
    obtain ⟨hru, hmem⟩ := (le_arm_iff hco ha hF c1 c2 c3 c4 u).mp hu
    have hleg := (le_leg_iff hco ha hF c1 c2 c3 c4 v).mp hv
    refine ⟨hmem, ?_⟩
    rw [show p.1 - u + u = p.1 from by omega]
    exact hleg
  · intro q hq
    simp only [Finset.mem_coe, mem_filter] at hq ⊢
    obtain ⟨hqD, hshift⟩ := hq
    obtain ⟨c1, c2, c3, c4⟩ := cell_of_mem hco ha hF hqD
    have hpD : (q.1 + u, q.2) ∈ ReturnPath.cellSet a b F := by
      have h := mem_filterDiagram_of_le hco ha hb hF (p := (q.1 + u, q.2 + v)) hshift
        (i := q.2) c3 (by omega)
      simpa using h
    obtain ⟨d1, d2, d3, d4⟩ := cell_of_mem hco ha hF hpD
    refine ⟨hpD, ?_, ?_⟩
    · refine (le_arm_iff hco ha hF d1 d2 d3 d4 u).mpr ⟨by omega, ?_⟩
      simpa using hqD
    · exact (le_leg_iff hco ha hF d1 d2 d3 d4 v).mpr hshift
  · intro p hp
    simp only [Finset.mem_coe, mem_filter] at hp
    obtain ⟨hpD, hu, hv⟩ := hp
    obtain ⟨c1, c2, c3, c4⟩ := cell_of_mem hco ha hF hpD
    obtain ⟨hru, -⟩ := (le_arm_iff hco ha hF c1 c2 c3 c4 u).mp hu
    refine Prod.ext ?_ rfl
    change p.1 - u + u = p.1
    omega
  · intro q hq
    refine Prod.ext ?_ rfl
    change q.1 + u - u = q.1
    omega

/-- **The tail counts vanish beyond the width**: `E_P(u, v) = 0` for `u ≥ a - 1`. -/
@[hjo "lem_tail_count_vanishes"]
theorem tailCount_eq_zero (ha : 1 < a) {y : Paths.Heights a b 1} (hy : Paths.IsBelowDiagonal y)
    {u v : ℕ} (hu : a - 1 ≤ u) : Paths.tailCount y u v = 0 := by
  rw [Paths.tailCount, card_eq_zero, filter_eq_empty_iff]
  intro p hp
  simp only [mem_product, mem_Ico, mem_Icc, Nat.mul_one] at hp
  rintro ⟨h1, h2, -⟩
  have h3 := arm_le hy (r := p.1) (i := p.2) hp.1.2 hp.2.1 h1
  omega

/-! ### The quadratic form as a signed count of pairs -/

/-- **The kernel is the difference of two window indicators**: `K s = 1` on `[0, a)`,
`K s = -1` on `[b, a + b)`, and `K s = 0` elsewhere. -/
@[hjo "lem_kernel_window"]
theorem u_eq_window (hab : a < b) (s : ℤ) :
    HJO.U a b s =
      if 0 ≤ s ∧ s < a then 1 else if (b : ℤ) ≤ s ∧ s < (a : ℤ) + b then -1 else 0 := by
  have hab' : (a : ℤ) < b := by exact_mod_cast hab
  rw [Gaps.u_eq_kernel]
  split_ifs <;> omega

/-- **The form at an indicator is a signed count of pairs**: `Q (1_F)` counts the pairs of `F`
whose difference lies in `[0, a)` minus those whose difference lies in `[b, a + b)`. -/
@[hjo "lem_quadratic_form_indicator"]
theorem q_indicator_eq (hab : a < b) (hF : F ⊆ (finspan {a, b}).gaps) :
    HJO.Q a b (fun g => if (g : ℕ) ∈ F then 1 else 0) =
      #{p ∈ F ×ˢ F | 0 ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < a} -
        #{p ∈ F ×ˢ F | (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b} := by
  have hab' : (a : ℤ) < b := by exact_mod_cast hab
  have e1 : HJO.Q a b (fun g => if (g : ℕ) ∈ F then 1 else 0)
      = ∑ g ∈ (finspan {a, b}).gaps, ∑ h ∈ (finspan {a, b}).gaps,
          HJO.U a b ((h : ℤ) - (g : ℤ)) * (if g ∈ F then 1 else 0) *
            (if h ∈ F then 1 else 0) := by
    rw [Gaps.q_eq_sum_sum, Finset.sum_coe_sort (finspan {a, b}).gaps fun g =>
      ∑ h : (finspan {a, b}).gaps, HJO.U a b ((h : ℕ) - (g : ℤ)) *
        (if g ∈ F then 1 else 0) * (if (h : ℕ) ∈ F then 1 else 0)]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_coe_sort (finspan {a, b}).gaps
      fun h => HJO.U a b ((h : ℤ) - (g : ℤ)) * (if g ∈ F then 1 else 0) *
        (if h ∈ F then 1 else 0)
  rw [e1, ← Finset.sum_product']
  have e2 : ∀ p ∈ (finspan {a, b}).gaps ×ˢ (finspan {a, b}).gaps,
      HJO.U a b ((p.2 : ℤ) - p.1) * (if p.1 ∈ F then 1 else 0) * (if p.2 ∈ F then 1 else 0)
        = if p.1 ∈ F ∧ p.2 ∈ F then HJO.U a b ((p.2 : ℤ) - p.1) else 0 := by
    intro p _
    split_ifs with h1 h2 h3 <;> simp_all
  rw [Finset.sum_congr rfl e2, ← Finset.sum_filter]
  have e3 : {p ∈ (finspan {a, b}).gaps ×ˢ (finspan {a, b}).gaps | p.1 ∈ F ∧ p.2 ∈ F} = F ×ˢ F := by
    ext p
    simp only [mem_filter, mem_product]
    exact ⟨fun h => h.2, fun h => ⟨⟨hF h.1, hF h.2⟩, h⟩⟩
  rw [e3]
  have e4 : ∀ p ∈ F ×ˢ F, HJO.U a b ((p.2 : ℤ) - p.1)
      = (if 0 ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < a then 1 else 0)
        - (if (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b then 1 else 0) := by
    intro p _
    rw [u_eq_window hab]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl e4, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]

/-! ### The two windows as sums of tail counts -/

/-- The pairs of cells of `𝒟_F` whose coordinates differ by the shift `(u, w)`. -/
def pairShift (a b : ℕ) (F : Finset ℕ) (u w : ℤ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  {q ∈ ReturnPath.cellSet a b F ×ˢ ReturnPath.cellSet a b F |
    (q.2.1 : ℤ) = (q.1.1 : ℤ) + u ∧ (q.2.2 : ℤ) = (q.1.2 : ℤ) + w}

/-- Membership in the shifted pair set. -/
theorem mem_pairShift {u w : ℤ} {q : (ℕ × ℕ) × (ℕ × ℕ)} :
    q ∈ pairShift a b F u w ↔ (q.1 ∈ ReturnPath.cellSet a b F ∧ q.2 ∈ ReturnPath.cellSet a b F) ∧
      (q.2.1 : ℤ) = (q.1.1 : ℤ) + u ∧ (q.2.2 : ℤ) = (q.1.2 : ℤ) + w := by
  rw [pairShift, mem_filter, mem_product]

/-- A nonnegative shift is counted by the shifted cells of the first coordinate. -/
theorem card_pairShift_nat (u w : ℕ) :
    #(pairShift a b F u w)
      = #{p ∈ ReturnPath.cellSet a b F | (p.1 + u, p.2 + w) ∈ ReturnPath.cellSet a b F} := by
  refine Finset.card_nbij' (fun q => q.1) (fun p => (p, (p.1 + u, p.2 + w))) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_coe, mem_pairShift] at hq
    simp only [Finset.mem_coe, mem_filter]
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq
    refine ⟨h1, ?_⟩
    have e : (q.1.1 + u, q.1.2 + w) = q.2 :=
      Prod.ext (by exact_mod_cast h3.symm) (by exact_mod_cast h4.symm)
    rw [e]
    exact h2
  · intro p hp
    simp only [Finset.mem_coe, mem_filter] at hp
    simp only [Finset.mem_coe, mem_pairShift]
    exact ⟨⟨hp.1, hp.2⟩, by push_cast; ring, by push_cast; ring⟩
  · intro q hq
    simp only [Finset.mem_coe, mem_pairShift] at hq
    obtain ⟨-, h3, h4⟩ := hq
    refine Prod.ext rfl ?_
    change (q.1.1 + u, q.1.2 + w) = q.2
    exact Prod.ext (by exact_mod_cast h3.symm) (by exact_mod_cast h4.symm)
  · intro p hp
    rfl

/-- A nonnegative shift is counted by a tail count. -/
theorem card_pairShift_eq_tailCount (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hF : Gaps.IsOrderFilter a b F) {u w : ℤ} (hu : 0 ≤ u) (hw : 0 ≤ w) :
    #(pairShift a b F u w)
      = Paths.tailCount (Primitive.primitivePath a b F) u.toNat w.toNat := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, u = (n : ℤ) := ⟨u.toNat, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, w = (m : ℤ) := ⟨w.toNat, by omega⟩
  rw [Int.toNat_natCast, Int.toNat_natCast, tailCount_eq_card hco ha hb hF,
    card_pairShift_nat]

/-- Reversing a shift is a bijection of pairs: swapping the two cells negates the shift. This
is what folds the pairs with `r' < r` onto the pairs with `r' > r`. -/
theorem card_pairShift_neg (u w : ℤ) :
    #(pairShift a b F (-u) (-w)) = #(pairShift a b F u w) := by
  refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ (fun q _ => Prod.swap_swap q)
    (fun q _ => Prod.swap_swap q)
  · intro q hq
    simp only [Finset.mem_coe, mem_pairShift, Prod.fst_swap, Prod.snd_swap] at hq ⊢
    exact ⟨⟨hq.1.2, hq.1.1⟩, by omega, by omega⟩
  · intro q hq
    simp only [Finset.mem_coe, mem_pairShift, Prod.fst_swap, Prod.snd_swap] at hq ⊢
    exact ⟨⟨hq.1.2, hq.1.1⟩, by omega, by omega⟩

/-- A positive integer below `a` is not divisible by `a`. -/
theorem not_dvd_of_lt {u : ℤ} (h1 : 1 ≤ u) (h2 : u < a) : ¬ (a : ℤ) ∣ u := by
  rintro ⟨k, hk⟩
  by_cases h : k ≤ 0
  · nlinarith
  · nlinarith

/-- A sum over a symmetric range of shifts splits into the term at `0` and the pairs
`{u, -u}`. -/
theorem sum_shift_split (A : ℕ) (f : ℤ → ℕ) :
    ∑ u ∈ Finset.Icc (-(A : ℤ)) (A : ℤ), f u
      = f 0 + ∑ u ∈ Finset.Icc 1 A, (f (u : ℤ) + f (-(u : ℤ))) := by
  have h1 : Finset.Icc (-(A : ℤ)) (A : ℤ)
      = Finset.Icc (-(A : ℤ)) (-1) ∪ Finset.Icc 0 (A : ℤ) := by
    ext x
    simp only [mem_union, mem_Icc]
    omega
  have h2 : Disjoint (Finset.Icc (-(A : ℤ)) (-1)) (Finset.Icc (0 : ℤ) (A : ℤ)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_Icc] at hx hx'
    omega
  have h3 : Finset.Icc (0 : ℤ) (A : ℤ) = insert 0 (Finset.Icc 1 (A : ℤ)) := by
    ext x
    simp only [mem_insert, mem_Icc]
    omega
  have h4 : (0 : ℤ) ∉ Finset.Icc (1 : ℤ) (A : ℤ) := by simp
  have h5 : ∑ u ∈ Finset.Icc (-(A : ℤ)) (-1), f u = ∑ u ∈ Finset.Icc 1 A, f (-(u : ℤ)) := by
    refine Finset.sum_nbij' (fun u => (-u).toNat) (fun u => -(u : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      simp only [mem_Icc] at hu ⊢
      omega
    · intro u hu
      simp only [mem_Icc] at hu ⊢
      omega
    · intro u hu
      simp only [mem_Icc] at hu
      omega
    · intro u hu
      simp only [mem_Icc] at hu
      omega
    · intro u hu
      simp only [mem_Icc] at hu
      rw [show -((-u).toNat : ℤ) = u from by omega]
  have h6 : ∑ u ∈ Finset.Icc (1 : ℤ) (A : ℤ), f u = ∑ u ∈ Finset.Icc 1 A, f (u : ℤ) := by
    refine Finset.sum_nbij' (fun u => u.toNat) (fun u => (u : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      simp only [mem_Icc] at hu ⊢
      omega
    · intro u hu
      simp only [mem_Icc] at hu ⊢
      omega
    · intro u hu
      simp only [mem_Icc] at hu
      omega
    · intro u hu
      simp only [mem_Icc] at hu
      omega
    · intro u hu
      simp only [mem_Icc] at hu
      rw [show ((u.toNat : ℤ)) = u from by omega]
  rw [h1, Finset.sum_union h2, h3, Finset.sum_insert h4, h5, h6, Finset.sum_add_distrib]
  omega

/-- The pairs of gaps of `F` whose difference lies in the window `[cb, cb + a)`, counted in
cell coordinates: grouping by the column shift `u = r' - r`, the window condition says exactly
that the row shift is `β (u - c)`. -/
theorem card_window_eq_sum (hco : a.Coprime b) (ha : 1 < a)
    (hFg : F ⊆ (finspan {a, b}).gaps) (c : ℤ) :
    #{p ∈ F ×ˢ F | 0 ≤ (p.2 : ℤ) - p.1 - c * b ∧ (p.2 : ℤ) - p.1 - c * b < a}
      = ∑ u ∈ Finset.Icc (-((a : ℤ) - 2)) ((a : ℤ) - 2),
          #(pairShift a b F u (Gaps.beta a b (u - c))) := by
  have ha0 : 0 < a := by omega
  have step1 : #{q ∈ ReturnPath.cellSet a b F ×ˢ ReturnPath.cellSet a b F |
        (q.2.2 : ℤ) - q.1.2 = Gaps.beta a b ((q.2.1 : ℤ) - q.1.1 - c)}
      = #{p ∈ F ×ˢ F | 0 ≤ (p.2 : ℤ) - p.1 - c * b ∧ (p.2 : ℤ) - p.1 - c * b < a} := by
    refine Finset.card_nbij (fun q => (label a b q.1, label a b q.2)) ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_coe, mem_filter, mem_product] at hq ⊢
      obtain ⟨⟨hq1, hq2⟩, hcond⟩ := hq
      obtain ⟨-, -, -, h1lt⟩ := (mem_gapDiagram ha0).mp (mem_filterDiagram.mp hq1).1
      obtain ⟨-, -, -, h2lt⟩ := (mem_gapDiagram ha0).mp (mem_filterDiagram.mp hq2).1
      have e1 := label_cast (a := a) (b := b) (p := q.1) (le_of_lt h1lt)
      have e2 := label_cast (a := a) (b := b) (p := q.2) (le_of_lt h2lt)
      have hw := (beta_window (b := b) ha0 ((q.2.1 : ℤ) - q.1.1 - c)
        (Gaps.beta a b ((q.2.1 : ℤ) - q.1.1 - c))).mpr rfl
      rw [← hcond] at hw
      exact ⟨⟨(mem_filterDiagram.mp hq1).2, (mem_filterDiagram.mp hq2).2⟩,
        by rw [e1, e2]; linarith [hw.1], by rw [e1, e2]; linarith [hw.2]⟩
    · intro q hq q' hq' heq
      simp only [Finset.mem_coe, mem_filter, mem_product] at hq hq'
      have h1 : q.1 = q'.1 :=
        label_injOn hco ha (Finset.mem_coe.mpr (mem_filterDiagram.mp hq.1.1).1)
          (Finset.mem_coe.mpr (mem_filterDiagram.mp hq'.1.1).1) (congrArg Prod.fst heq)
      have h2 : q.2 = q'.2 :=
        label_injOn hco ha (Finset.mem_coe.mpr (mem_filterDiagram.mp hq.1.2).1)
          (Finset.mem_coe.mpr (mem_filterDiagram.mp hq'.1.2).1) (congrArg Prod.snd heq)
      exact Prod.ext h1 h2
    · intro gh hgh
      simp only [Finset.mem_coe, mem_filter, mem_product] at hgh
      obtain ⟨⟨hg1, hg2⟩, hw1, hw2⟩ := hgh
      obtain ⟨p, hpD, hpl⟩ := label_surjOn hco ha (Finset.mem_coe.mpr (hFg hg1))
      obtain ⟨p', hp'D, hp'l⟩ := label_surjOn hco ha (Finset.mem_coe.mpr (hFg hg2))
      simp only [Finset.mem_coe] at hpD hp'D
      obtain ⟨-, -, -, h1lt⟩ := (mem_gapDiagram ha0).mp hpD
      obtain ⟨-, -, -, h2lt⟩ := (mem_gapDiagram ha0).mp hp'D
      have e1 := label_cast (a := a) (b := b) (p := p) (le_of_lt h1lt)
      have e2 := label_cast (a := a) (b := b) (p := p') (le_of_lt h2lt)
      rw [← hpl, ← hp'l, e1, e2] at hw1 hw2
      refine ⟨(p, p'), ?_, Prod.ext hpl hp'l⟩
      simp only [Finset.mem_coe, mem_filter, mem_product]
      refine ⟨⟨mem_filterDiagram.mpr ⟨hpD, hpl ▸ hg1⟩,
        mem_filterDiagram.mpr ⟨hp'D, hp'l ▸ hg2⟩⟩, ?_⟩
      exact (beta_window ha0 ((p'.1 : ℤ) - p.1 - c) ((p'.2 : ℤ) - p.2)).mp
        ⟨by linarith, by linarith⟩
  rw [← step1]
  have hmaps : Set.MapsTo (fun q : (ℕ × ℕ) × (ℕ × ℕ) => (q.2.1 : ℤ) - q.1.1)
      ↑{q ∈ ReturnPath.cellSet a b F ×ˢ ReturnPath.cellSet a b F |
        (q.2.2 : ℤ) - q.1.2 = Gaps.beta a b ((q.2.1 : ℤ) - q.1.1 - c)}
      ↑(Finset.Icc (-((a : ℤ) - 2)) ((a : ℤ) - 2)) := by
    intro q hq
    simp only [Finset.mem_coe, mem_filter, mem_product] at hq
    obtain ⟨c1, c2, -, -⟩ := (mem_gapDiagram ha0).mp (mem_filterDiagram.mp hq.1.1).1
    obtain ⟨d1, d2, -, -⟩ := (mem_gapDiagram ha0).mp (mem_filterDiagram.mp hq.1.2).1
    have c1' : (1 : ℤ) ≤ q.1.1 := by exact_mod_cast c1
    have d1' : (1 : ℤ) ≤ q.2.1 := by exact_mod_cast d1
    have c2' := cast_le_pred (a := a) ha0 c2
    have d2' := cast_le_pred (a := a) ha0 d2
    simp only [Finset.mem_coe, mem_Icc]
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun u hu => congrArg card ?_
  ext q
  simp only [mem_filter, mem_product, mem_pairShift]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    have h5 : (q.2.1 : ℤ) - q.1.1 - c = u - c := by omega
    rw [h5] at h3
    exact ⟨⟨h1, h2⟩, by omega, by omega⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    have h5 : (q.2.1 : ℤ) - q.1.1 - c = u - c := by omega
    exact ⟨⟨⟨h1, h2⟩, by rw [h5]; omega⟩, by omega⟩

/-- **The pairs in the first window**:
`#{(g, h) ∈ F × F : 0 ≤ h - g < a} = E(0, 0) + ∑_{u=1}^{a-2} (E(u, β u) + E(u, β u + 1))`. -/
@[hjo "lem_pairs_near_diagonal"]
theorem card_window_zero (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hF : Gaps.IsOrderFilter a b F) (hFg : F ⊆ (finspan {a, b}).gaps) :
    #{p ∈ F ×ˢ F | 0 ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < a}
      = Paths.tailCount (Primitive.primitivePath a b F) 0 0
        + ∑ u ∈ Finset.Icc 1 (a - 2),
            (Paths.tailCount (Primitive.primitivePath a b F) u (Gaps.beta a b (u : ℤ)).toNat
              + Paths.tailCount (Primitive.primitivePath a b F) u
                  ((Gaps.beta a b (u : ℤ)).toNat + 1)) := by
  have hcast : ((a : ℤ) - 2) = ((a - 2 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ a)]
    norm_num
  have hw := card_window_eq_sum hco ha hFg 0
  simp only [zero_mul, sub_zero] at hw
  rw [hw, hcast, sum_shift_split (a - 2) fun u => #(pairShift a b F u (Gaps.beta a b u))]
  congr 1
  · rw [show Gaps.beta a b 0 = 0 from by simp [Gaps.beta],
      card_pairShift_eq_tailCount hco ha hb hF le_rfl le_rfl]
    norm_num
  · refine Finset.sum_congr rfl fun u hu => ?_
    simp only [mem_Icc] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hu0 : (0 : ℤ) ≤ (u : ℤ) := by positivity
    have hnd : ¬ (a : ℤ) ∣ (u : ℤ) := not_dvd_of_lt (by omega) (by omega)
    have hbeta : 0 ≤ Gaps.beta a b (u : ℤ) := beta_nonneg (by omega) hu0
    have htn : (Gaps.beta a b (u : ℤ) + 1).toNat = (Gaps.beta a b (u : ℤ)).toNat + 1 := by omega
    have hneg := card_pairShift_neg (a := a) (b := b) (F := F) (u : ℤ)
      (Gaps.beta a b (u : ℤ) + 1)
    rw [card_pairShift_eq_tailCount hco ha hb hF hu0 hbeta, beta_neg hco (by omega) hnd,
      show -Gaps.beta a b (u : ℤ) - 1 = -(Gaps.beta a b (u : ℤ) + 1) from by ring, hneg,
      card_pairShift_eq_tailCount hco ha hb hF hu0 (by omega)]
    simp only [Int.toNat_natCast, htn]

/-- **The pairs in the second window**: `#{(g, h) ∈ F × F : b ≤ h - g < a + b}` equals
`E(0, β 1 + 1) + ∑_{u=1}^{a-2} (E(u, β (u-1)) + E(u, β (u+1) + 1))`. -/
@[hjo "lem_pairs_near_b"]
theorem card_window_b (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hF : Gaps.IsOrderFilter a b F) (hFg : F ⊆ (finspan {a, b}).gaps) :
    #{p ∈ F ×ˢ F | (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b}
      = Paths.tailCount (Primitive.primitivePath a b F) 0 ((Gaps.beta a b 1).toNat + 1)
        + ∑ u ∈ Finset.Icc 1 (a - 2),
            (Paths.tailCount (Primitive.primitivePath a b F) u
                (Gaps.beta a b ((u : ℤ) - 1)).toNat
              + Paths.tailCount (Primitive.primitivePath a b F) u
                  ((Gaps.beta a b ((u : ℤ) + 1)).toNat + 1)) := by
  have hcast : ((a : ℤ) - 2) = ((a - 2 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ a)]
    norm_num
  have hw := card_window_eq_sum hco ha hFg 1
  simp only [one_mul] at hw
  have hfilter : {p ∈ F ×ˢ F | (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b}
      = {p ∈ F ×ˢ F | 0 ≤ (p.2 : ℤ) - p.1 - b ∧ (p.2 : ℤ) - p.1 - b < a} :=
    Finset.filter_congr fun p _ => by omega
  rw [hfilter, hw, hcast,
    sum_shift_split (a - 2) fun u => #(pairShift a b F u (Gaps.beta a b (u - 1)))]
  have hbeta1 : 0 ≤ Gaps.beta a b 1 := beta_nonneg (by omega) (by omega)
  congr 1
  · have hnd : ¬ (a : ℤ) ∣ (1 : ℤ) := not_dvd_of_lt (by omega) (by omega)
    have hneg := card_pairShift_neg (a := a) (b := b) (F := F) 0 (Gaps.beta a b 1 + 1)
    rw [neg_zero] at hneg
    rw [show (0 : ℤ) - 1 = -(1 : ℤ) from by ring, beta_neg hco (by omega) hnd,
      show -Gaps.beta a b 1 - 1 = -(Gaps.beta a b 1 + 1) from by ring, hneg,
      card_pairShift_eq_tailCount hco ha hb hF le_rfl (by omega),
      show (Gaps.beta a b 1 + 1).toNat = (Gaps.beta a b 1).toNat + 1 from by omega]
    norm_num
  · refine Finset.sum_congr rfl fun u hu => ?_
    simp only [mem_Icc] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hu0 : (0 : ℤ) ≤ (u : ℤ) := by positivity
    have hnd : ¬ (a : ℤ) ∣ ((u : ℤ) + 1) := not_dvd_of_lt (by omega) (by omega)
    have hb1 : 0 ≤ Gaps.beta a b ((u : ℤ) - 1) := beta_nonneg (by omega) (by omega)
    have hb2 : 0 ≤ Gaps.beta a b ((u : ℤ) + 1) := beta_nonneg (by omega) (by omega)
    have htn : (Gaps.beta a b ((u : ℤ) + 1) + 1).toNat
        = (Gaps.beta a b ((u : ℤ) + 1)).toNat + 1 := by omega
    have hneg := card_pairShift_neg (a := a) (b := b) (F := F) (u : ℤ)
      (Gaps.beta a b ((u : ℤ) + 1) + 1)
    rw [card_pairShift_eq_tailCount hco ha hb hF hu0 hb1,
      show -(u : ℤ) - 1 = -((u : ℤ) + 1) from by ring, beta_neg hco (by omega) hnd,
      show -Gaps.beta a b ((u : ℤ) + 1) - 1 = -(Gaps.beta a b ((u : ℤ) + 1) + 1) from by ring,
      hneg, card_pairShift_eq_tailCount hco ha hb hF hu0 (by omega)]
    simp only [Int.toNat_natCast, htn]

/-! ### The hook count as an alternating sum of tail counts -/

/-- A filter whose predicate is a disjunction of two exclusive cases splits as a sum of
cards. -/
theorem card_filter_split {α : Type*} {s : Finset α} {p q r : α → Prop}
    [DecidablePred p] [DecidablePred q] [DecidablePred r] (h : ∀ x ∈ s, p x ↔ (q x ∨ r x))
    (hd : Disjoint {x ∈ s | q x} {x ∈ s | r x}) :
    #{x ∈ s | p x} = #{x ∈ s | q x} + #{x ∈ s | r x} := by
  classical
  rw [Finset.filter_congr h, Finset.filter_or, Finset.card_union_of_disjoint hd]

/-- The staircase bound is monotone. -/
theorem beta_le_succ (ha : 0 < a) (u : ℤ) : Gaps.beta a b u ≤ Gaps.beta a b (u + 1) := by
  rw [Gaps.beta, Gaps.beta]
  exact Int.ediv_le_ediv (by exact_mod_cast ha) (by nlinarith [Nat.cast_nonneg (α := ℤ) b])

/-- The number of cells with arm exactly `u` and leg at least `v`. -/
def armLeg {a b N : ℕ} (y : Paths.Heights a b N) (u v : ℕ) : ℕ :=
  #{p ∈ Ico 1 (a * N) ×ˢ Icc 1 (b * N) | p.2 ≤ Paths.ht y p.1 ∧
    Paths.arm y p.1 p.2 = u ∧ v ≤ Paths.leg y p.1 p.2}

/-- A tail count splits into the cells with arm exactly `u` and the next tail count. -/
theorem tailCount_eq_armLeg_add {N : ℕ} (y : Paths.Heights a b N) (u v : ℕ) :
    Paths.tailCount y u v = armLeg y u v + Paths.tailCount y (u + 1) v := by
  rw [Paths.tailCount, armLeg, Paths.tailCount]
  refine card_filter_split (fun x _ => by omega) ?_
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [mem_filter] at hx hx'
  omega

/-- **The hook count as an alternating sum of tail counts**:
`h(P) = ∑_{u=0}^{a-2} (E(u, β u) - E(u+1, β u) - E(u, β (u+1) + 1) + E(u+1, β (u+1) + 1))`. -/
@[hjo "lem_hook_count_tails"]
theorem hookCount_eq_sum (hco : a.Coprime b) (ha : 1 < a) {y : Paths.Heights a b 1}
    (hy : Paths.IsBelowDiagonal y) :
    (Paths.hookCount y : ℤ) = ∑ u ∈ Finset.Icc 0 (a - 2),
      ((Paths.tailCount y u (Gaps.beta a b (u : ℤ)).toNat : ℤ)
        - (Paths.tailCount y (u + 1) (Gaps.beta a b (u : ℤ)).toNat : ℤ)
        - (Paths.tailCount y u ((Gaps.beta a b ((u : ℤ) + 1)).toNat + 1) : ℤ)
        + (Paths.tailCount y (u + 1) ((Gaps.beta a b ((u : ℤ) + 1)).toNat + 1) : ℤ)) := by
  have hS : Paths.hookCount y = #{p ∈ Ico 1 (a * 1) ×ˢ Icc 1 (b * 1) | p.2 ≤ Paths.ht y p.1 ∧
      (Gaps.beta a b (Paths.arm y p.1 p.2) ≤ (Paths.leg y p.1 p.2 : ℤ) ∧
        (Paths.leg y p.1 p.2 : ℤ) ≤ Gaps.beta a b ((Paths.arm y p.1 p.2 : ℤ) + 1))} := by
    rw [Paths.hookCount]
    refine congrArg card (Finset.filter_congr fun p hp => ?_)
    simp only [mem_product, mem_Ico, mem_Icc] at hp
    exact and_congr_right fun hi => hook_iff_beta hco ha hy (by omega) hp.2.1 hi
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => Paths.arm y p.1 p.2)
      ↑{p ∈ Ico 1 (a * 1) ×ˢ Icc 1 (b * 1) | p.2 ≤ Paths.ht y p.1 ∧
        (Gaps.beta a b (Paths.arm y p.1 p.2) ≤ (Paths.leg y p.1 p.2 : ℤ) ∧
          (Paths.leg y p.1 p.2 : ℤ) ≤ Gaps.beta a b ((Paths.arm y p.1 p.2 : ℤ) + 1))}
      ↑(Finset.Icc 0 (a - 2)) := by
    intro p hp
    simp only [Finset.mem_coe, mem_filter, mem_product, mem_Ico, mem_Icc] at hp
    have h3 := arm_le hy (r := p.1) (i := p.2) (by omega) (by omega) hp.2.1
    simp only [Finset.mem_coe, mem_Icc]
    omega
  rw [hS, Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  refine Finset.sum_congr rfl fun u hu => ?_
  simp only [mem_Icc] at hu
  have hmono : Gaps.beta a b (u : ℤ) ≤ Gaps.beta a b ((u : ℤ) + 1) := beta_le_succ (by omega) _
  have hb1 : 0 ≤ Gaps.beta a b (u : ℤ) := beta_nonneg (by omega) (by positivity)
  have hb2 : 0 ≤ Gaps.beta a b ((u : ℤ) + 1) := beta_nonneg (by omega) (by positivity)
  have e1 := tailCount_eq_armLeg_add y u (Gaps.beta a b (u : ℤ)).toNat
  have e2 := tailCount_eq_armLeg_add y u ((Gaps.beta a b ((u : ℤ) + 1)).toNat + 1)
  have e3 : armLeg y u (Gaps.beta a b (u : ℤ)).toNat
      = #{p ∈ Ico 1 (a * 1) ×ˢ Icc 1 (b * 1) | (p.2 ≤ Paths.ht y p.1 ∧
          (Gaps.beta a b (Paths.arm y p.1 p.2) ≤ (Paths.leg y p.1 p.2 : ℤ) ∧
            (Paths.leg y p.1 p.2 : ℤ) ≤ Gaps.beta a b ((Paths.arm y p.1 p.2 : ℤ) + 1))) ∧
          Paths.arm y p.1 p.2 = u}
        + armLeg y u ((Gaps.beta a b ((u : ℤ) + 1)).toNat + 1) := by
    rw [armLeg, armLeg]
    refine card_filter_split (fun x _ => ?_) ?_
    · by_cases hax : Paths.arm y x.1 x.2 = u
      · rw [hax]
        omega
      · omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [mem_filter] at hx hx'
      rw [hx.2.2] at hx
      omega
  rw [Finset.filter_filter]
  omega

end HJO.RankOneDinv
