/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendOneB
public import HJO.Shuffle.CornerClosedForm
public import HJO.CMStructure.StarConjRel2
public import HJO.CMStructure.ZBraid

/-!
# The first band identity at a nonempty composition: `a = 1`, `α = (1)`, `A = 1`

Every other worked instance of `HJO.Mellit.SweepAppend` — `HJO.Mellit.sweepAppend_nil_one_one_b`,
`HJO.Mellit.sweepAppend_nil_two_three_one`, `HJO.Mellit.sweepAppend_nil_one_two_two` — sits at
`α = []`, which is the `hzero` clause of `HJO.Mellit.sweepAppend_of_forall_band`. This file settles
the smallest instance of the *other* clause, `hband`, at `0 < α.sum`: `a = 1`, every `b > 0`,
`α = (1)`, `A = 1`.

## Why this instance is tractable, and what it exhibits

The fibre is a singleton. `HJO.Mellit.aboveReturnPaths_one_b` pins the `1 × b` rectangle's only
above-diagonal path as `HJO.Mellit.baseOne b`, so both the base `z` and the tail `w` are that path
and the appended path is the staircase `HJO.Mellit.stairOne b` with heights `(0, b, 2b)`. No
multi-path rational-Catalan sum enters — that is the difficulty of `hzero`, not of this clause.

The band is the whole word. At the threshold `d = a·bA = b` **every** swept point of either path
has diagonal excess at most `b` (`HJO.Mellit.diagExcess_le_of_mem_sweptRegion_stairOne` and its
base sibling), so `HJO.Mellit.outerSweepWord` is the empty product on both sides and the band
identity is the bare per-path identity.

What the instance exhibits is precisely the obstruction the module docstring of
`HJO/Shuffle/SweepAppendBandInterleave.lean` names. In the `2 × 2b` rectangle the rank order
runs through the excess levels `b, b-1, …, 1`, and at each level it visits the tail point
`(1, b+j)` before the base point `(0, j)` — the interleaving, here with one point of each kind per
level. The base's own word is `Δ^{(1)b-1}d_+^{(0)}` (`HJO.Mellit.partialSweepWord_baseOne`), and
**no factor of it survives in the appended word**, which is
`q^{-(b-1)}(Δ^{(2)}Δ^{(2)})^{b-1}d_+^{(1)}d_+^{(0)}`: every width has moved, the width-`1` corner
has become a width-`2` corner, and the type-`A` event at the top of the base column has become
`d_+^{(1)}` rather than `d_+^{(0)}`. The two words are related by no scalar and no conjugation.

They nevertheless agree after the stage is applied, and both sides come out as the single monomial
`y_1^by_2^b`.

## `q ≠ 0` is a real exclusion here, not an artefact

`HJO.Mellit.not_sweepAppend_nil_two_three_one_of_q_zero` records that the `α = []` clause fails at
`q = 0` as soon as `2 ≤ a`, and its docstring says that at `a = 1` "no event has a live north step
to its right and the slope word has no letter `z`, so no negative power of `q` occurs anywhere".
**That is true only of the one-column rectangle.** On the staircase the base point `(0, j)` has the
tail's north step `(1, b+j-1)` live and strictly to its right, so
`HJO.Mellit.sweepRight_stairOne_base = 1` and each of the `b - 1` type-`C` events at a base carries
`q^{-1}`. At `q = 0` those letters are the zero map while the right-hand side is the nonzero
monomial `y_1^by_2^b`, so `HJO.Mellit.not_band_one_left_one_one_of_q_zero` refutes the `hband`
clause at `q = 0` for every `b ≥ 2` and every `u` — at `a = 1`, which the `α = []` refutation does
not reach.
`u` enters neither side: `HJO.Sweep.dplusStar_auxVar_pow` is `u`-free on a power of `y_1`, the slope
word of `(1, b)` has no `z` letter (`HJO.Mellit.slopeWord_one_left`), no event of either path is of
type `E`, and the scalar `(qu)^{1-A}` is `1` at `A = 1`. So this instance says nothing about the
necessity of `u ≠ 0`.

## References

Declarations involved: `HJO.Paths.sweptRegion`, `HJO.Paths.liveSteps`, `HJO.Paths.sweepWidth`,
`HJO.Paths.sweepRight`, `HJO.Paths.eventType`, `HJO.Mellit.sweepOperator`,
`HJO.Mellit.partialSweepWord`, `HJO.Mellit.stage`, `HJO.Mellit.slopeWord`. Transcribing A.
Mellit, *Toric braids and `(m, n)`-parking functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep Paths Finset

/-! ### Half-integer windows isolate one rank -/

/-- **A window of width one about an integer contains only that integer.** Every level below is a
half-integer, and every window used is `(m - 1/2, m + 1/2)`; this is the whole of the isolation
hypothesis of `HJO.Mellit.partialSweepWord_eq_sweepOperator_mul` at such a window. -/
theorem int_eq_of_half_window {m r : ℤ} (hlo : (m : ℚ) - 1 / 2 < (r : ℚ))
    (hup : (r : ℚ) < (m : ℚ) + 1 / 2) : r = m := by
  have h1 : ((m - 1 : ℤ) : ℚ) < ((r : ℤ) : ℚ) := by push_cast; linarith
  have h2 : ((r : ℤ) : ℚ) < ((m + 1 : ℤ) : ℚ) := by push_cast; linarith
  have h1' : m - 1 < r := by exact_mod_cast h1
  have h2' : r < m + 1 := by exact_mod_cast h2
  omega

/-- Two levels with the same set of outranking swept points give the same partial word. -/
theorem partialSweepWord_congr_of_sweptAbove_eq {L : Type*} [Field L] [Algebra ℚ L] (q u : L)
    {a b N : ℕ} (y : Heights a b N) {η η' : ℚ} (h : sweptAbove y η = sweptAbove y η') :
    partialSweepWord q u y η = partialSweepWord q u y η' := by
  rw [partialSweepWord, partialSweepWord, h]

/-! ### The band at a threshold above every excess -/

section Band

variable {L : Type*} [Field L] [Algebra ℚ L] {a b M : ℕ}

/-- **Above every excess of the swept region the outer word is empty.** -/
theorem outerSweepWord_eq_one_of_forall_le (q u : L) (y : Heights a b M) (η : ℚ) (d : ℤ)
    (h : ∀ P ∈ sweptRegion y, diagExcess a b P ≤ d) : outerSweepWord q u y η d = 1 := by
  have hempty : {P ∈ sweptAbove y η | d < diagExcess a b P} = (∅ : Finset (ℕ × ℕ)) :=
    Finset.filter_eq_empty_iff.2 fun {P} hP => not_lt.2 (h P (sweptAbove_subset y η hP))
  rw [outerSweepWord, hempty, sortByRank_empty, List.map_nil, List.prod_nil]

/-- **Above every excess of the swept region the band word is the whole partial word.** -/
theorem bandSweepWord_eq_partialSweepWord_of_forall_le (q u : L) (y : Heights a b M) (η : ℚ)
    (d : ℤ) (h : ∀ P ∈ sweptRegion y, diagExcess a b P ≤ d) :
    bandSweepWord q u y η d = partialSweepWord q u y η := by
  have hall : {P ∈ sweptAbove y η | diagExcess a b P ≤ d} = sweptAbove y η :=
    Finset.filter_true_of_mem fun {P} hP => h P (sweptAbove_subset y η hP)
  rw [bandSweepWord, partialSweepWord, hall]

end Band

/-! ### The staircase path of the `2 × 2b` rectangle -/

variable {b : ℕ}

/-- **The staircase `(2, 2b)`-path**, heights `(0, b, 2b)`: the forced path of the `1 × b` rectangle
laid on top of itself. It is the only above-diagonal path of the `2 × 2b` rectangle whose return
composition is `(1, 1)`, and it is the appended path of the band identity at `α = (1)`, `A = 1`. -/
def stairOne (b : ℕ) : Heights 1 b (1 + 1) := appendHeights (baseOne b) (baseOne b)

theorem ht_baseOne_top : ht (baseOne b) (1 * 1) = b * 1 := by
  rw [Nat.mul_one, Nat.mul_one, ht_baseOne_of_ne_zero one_ne_zero]

/-- **The heights of the staircase**: `ŷ_r = b·min(r, 2)`. -/
theorem ht_stairOne (r : ℕ) : ht (stairOne b) r = b * min r 2 := by
  rcases Nat.lt_or_ge 2 r with hr | hr
  · rw [min_eq_right hr.le, ht_of_gt (stairOne b) (by omega)]
  · rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rw [stairOne, ht_appendHeights_of_le (by omega), ht_baseOne_zero]
      simp
    · rw [stairOne, ht_appendHeights_of_ge ht_baseOne_top ht_baseOne_zero (by omega) (by omega)]
      rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
      · rw [show 1 - 1 * 1 = 0 from by omega, ht_baseOne_zero, min_eq_left (by omega)]
        omega
      · rw [show 2 - 1 * 1 = 1 from by omega, ht_baseOne_of_ne_zero one_ne_zero,
          min_eq_right (by omega)]
        omega

@[simp] theorem ht_stairOne_zero : ht (stairOne b) 0 = 0 := by rw [ht_stairOne]; simp

theorem ht_stairOne_one : ht (stairOne b) 1 = b := by rw [ht_stairOne]; simp

theorem ht_stairOne_two : ht (stairOne b) 2 = b * 2 := by rw [ht_stairOne]; simp

theorem ht_stairOne_of_le {r : ℕ} (hr : r ≤ 2) : ht (stairOne b) r = b * r := by
  rw [ht_stairOne, min_eq_left hr]

theorem isAboveDiagonal_stairOne : IsAboveDiagonal (stairOne b) :=
  isAboveDiagonal_appendHeights isAboveDiagonal_baseOne isAboveDiagonal_baseOne

/-! ### The rank in the `2 × 2b` rectangle -/

/-- **The above-diagonal rank of the `2 × 2b` rectangle**: `rk̂(x, y) = 6(y - bx) + x`. The scale
is `(aN+1)Na = 3·2·1 = 6`, which is also the attack window. -/
theorem abovePointRank_one_b_two (x y : ℕ) :
    ParkingFunctions.abovePointRank 1 b (1 + 1) x y = 6 * ((y : ℤ) - b * x) + x := by
  rw [ParkingFunctions.abovePointRank]
  push_cast
  ring

theorem pointRank_one_b_two (P : ℕ × ℕ) :
    pointRank 1 b (1 + 1) P = 6 * ((P.2 : ℤ) - b * P.1) + P.1 := by
  rw [pointRank, abovePointRank_one_b_two]

theorem attackWindow_one_two : attackWindow 1 (1 + 1) = 6 := rfl

/-! ### The swept region and the north steps of the staircase -/

theorem mem_sweptRegion_stairOne_iff {P : ℕ × ℕ} :
    P ∈ sweptRegion (stairOne b) ↔
      P.1 ≤ 2 ∧ b * P.1 ≤ P.2 ∧ P.2 ≤ b * min (P.1 + 1) 2 := by
  rw [mem_sweptRegion, ht_stairOne]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, by omega, h3⟩

/-- **Every swept point of the staircase has diagonal excess at most `b`.** This is what makes the
band at the threshold `a·bA = b` the whole partial word and the outer word empty. -/
theorem diagExcess_le_of_mem_sweptRegion_stairOne {P : ℕ × ℕ}
    (hP : P ∈ sweptRegion (stairOne b)) : diagExcess 1 b P ≤ (1 : ℤ) * (b * 1) := by
  obtain ⟨h1, h2, h3⟩ := mem_sweptRegion_stairOne_iff.1 hP
  have hkey : P.2 ≤ b * P.1 + b := by
    rcases (by omega : P.1 = 0 ∨ P.1 = 1 ∨ P.1 = 2) with h | h | h
    · rw [h, show min (0 + 1) 2 = 1 from rfl] at h3
      rw [h]; omega
    · rw [h, show min (1 + 1) 2 = 2 from rfl] at h3
      rw [h]; omega
    · rw [h, show min (2 + 1) 2 = 2 from rfl] at h3
      rw [h]; omega
  have hz : (P.2 : ℤ) ≤ (b : ℤ) * P.1 + b := by exact_mod_cast hkey
  simp only [diagExcess]
  push_cast
  linarith

/-- **Every swept point of the `1 × b` path has diagonal excess at most `b`.** -/
theorem diagExcess_le_of_mem_sweptRegion_baseOne {P : ℕ × ℕ}
    (hP : P ∈ sweptRegion (baseOne b)) : diagExcess 1 b P ≤ (1 : ℤ) * (b * 1) := by
  obtain ⟨h1, h2⟩ := snd_le_of_mem_sweptRegion_baseOne hP
  have hb0 : (0 : ℤ) ≤ (b : ℤ) * P.1 := by positivity
  have h2' : (P.2 : ℤ) ≤ (b : ℤ) := by exact_mod_cast h2
  simp only [diagExcess]
  push_cast
  linarith

theorem mem_northSteps_stairOne_iff {P : ℕ × ℕ} :
    P ∈ northSteps (stairOne b) ↔ P.1 < 2 ∧ b * P.1 ≤ P.2 ∧ P.2 < b * (P.1 + 1) := by
  rw [mem_northSteps_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [ht_stairOne_of_le (by omega)] at h2
    rw [ht_stairOne_of_le (by omega)] at h3
    exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, ?_, ?_⟩
    · rw [ht_stairOne_of_le (by omega)]; exact h2
    · rw [ht_stairOne_of_le (by omega)]; exact h3

/-! ### The live north steps of the staircase, in closed form -/

/-- **Membership in `HJO.Paths.liveSteps` on the staircase.** The window `[rk u, rk u + 6)` about
the rank `6d + x` of a point of excess `d` and abscissa `x` admits a north step of excess `e` and
abscissa `y` exactly when `e = d` for `y ≤ x` and `e = d - 1` for `y > x`: both comparisons of
`HJO.Paths.liveSteps` are decided by the excess to within the tie-break `x - y`, and
`|x - y| ≤ 2 < 6`.

This is the two-window asymmetry of `HJO/Shuffle/SweepAppendBandInterleave.lean` at `a = 1`,
where the half-open windows `[d - a, d)` and `(d - a, d]` are the single excesses `d - 1` and `d`.
-/
theorem mem_liveSteps_stairOne_iff {P Q : ℕ × ℕ} (hP1 : P.1 ≤ 2) :
    Q ∈ liveSteps (stairOne b) P ↔
      (Q.1 < 2 ∧ b * Q.1 ≤ Q.2 ∧ Q.2 < b * (Q.1 + 1)) ∧
        ((Q.1 ≤ P.1 ∧ (Q.2 : ℤ) - b * Q.1 = (P.2 : ℤ) - b * P.1) ∨
          (P.1 < Q.1 ∧ (Q.2 : ℤ) - b * Q.1 = (P.2 : ℤ) - b * P.1 - 1)) := by
  rw [liveSteps, Finset.mem_filter, mem_northSteps_stairOne_iff, attackWindow_one_two,
    abovePointRank_one_b_two, abovePointRank_one_b_two]
  constructor
  · rintro ⟨hQ, h1, h2⟩
    refine ⟨hQ, ?_⟩
    have hQ1 : (Q.1 : ℤ) ≤ 1 := by exact_mod_cast (by omega : Q.1 ≤ 1)
    have hP1' : (P.1 : ℤ) ≤ 2 := by exact_mod_cast hP1
    have hQ0 : (0 : ℤ) ≤ (Q.1 : ℤ) := Int.natCast_nonneg _
    have hP0 : (0 : ℤ) ≤ (P.1 : ℤ) := Int.natCast_nonneg _
    push_cast at h1 h2
    rcases Nat.lt_or_ge P.1 Q.1 with hlt | hge
    · refine Or.inr ⟨hlt, ?_⟩
      have hlt' : (P.1 : ℤ) < Q.1 := by exact_mod_cast hlt
      omega
    · refine Or.inl ⟨hge, ?_⟩
      have hge' : (Q.1 : ℤ) ≤ P.1 := by exact_mod_cast hge
      omega
  · rintro ⟨hQ, hcase⟩
    refine ⟨hQ, ?_, ?_⟩ <;> push_cast <;>
      rcases hcase with ⟨hle, he⟩ | ⟨hlt, he⟩
    · have hle' : (Q.1 : ℤ) ≤ P.1 := by exact_mod_cast hle
      have hP1' : (P.1 : ℤ) ≤ 2 := by exact_mod_cast hP1
      have hQ0 : (0 : ℤ) ≤ (Q.1 : ℤ) := Int.natCast_nonneg _
      omega
    · have hlt' : (P.1 : ℤ) < Q.1 := by exact_mod_cast hlt
      have hQ1 : (Q.1 : ℤ) ≤ 1 := by exact_mod_cast (by omega : Q.1 ≤ 1)
      have hP0 : (0 : ℤ) ≤ (P.1 : ℤ) := Int.natCast_nonneg _
      omega
    · have hle' : (Q.1 : ℤ) ≤ P.1 := by exact_mod_cast hle
      have hP1' : (P.1 : ℤ) ≤ 2 := by exact_mod_cast hP1
      have hQ0 : (0 : ℤ) ≤ (Q.1 : ℤ) := Int.natCast_nonneg _
      omega
    · have hlt' : (P.1 : ℤ) < Q.1 := by exact_mod_cast hlt
      have hQ1 : (Q.1 : ℤ) ≤ 1 := by exact_mod_cast (by omega : Q.1 ≤ 1)
      have hP0 : (0 : ℤ) ≤ (P.1 : ℤ) := Int.natCast_nonneg _
      omega

/-! ### The live sets, widths and event types at the four families of swept points -/

theorem mem_sweptRegion_stairOne_base {k : ℕ} (hkb : k ≤ b) :
    ((0, k) : ℕ × ℕ) ∈ sweptRegion (stairOne b) := by
  refine mem_sweptRegion_stairOne_iff.2 ⟨by omega, by omega, ?_⟩
  rw [show min ((0 : ℕ) + 1) 2 = 1 from rfl]
  omega

theorem mem_sweptRegion_stairOne_tail {k : ℕ} (hkb : k ≤ b) :
    ((1, b + k) : ℕ × ℕ) ∈ sweptRegion (stairOne b) := by
  refine mem_sweptRegion_stairOne_iff.2 ⟨by omega, by omega, ?_⟩
  rw [show min ((1 : ℕ) + 1) 2 = 2 from rfl]
  omega

/-- **The live set at a base point**, below the top of the base column: the base's own north step of
the same excess and the tail's north step one excess lower. -/
theorem liveSteps_stairOne_base_of_lt {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    liveSteps (stairOne b) ((0, k) : ℕ × ℕ)
      = {((0, k) : ℕ × ℕ), ((1, b + k - 1) : ℕ × ℕ)} := by
  ext Q
  rw [mem_liveSteps_stairOne_iff (by omega), Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, hc⟩
    rcases hc with ⟨hle, he⟩ | ⟨hlt, he⟩
    · have hQ1 : Q.1 = 0 := by omega
      rw [hQ1] at he h2 h3
      push_cast at he
      exact Or.inl (Prod.ext_iff.2 ⟨hQ1, by omega⟩)
    · have hQ1 : Q.1 = 1 := by omega
      rw [hQ1] at he h2 h3
      push_cast at he
      exact Or.inr (Prod.ext_iff.2 ⟨hQ1, by omega⟩)
  · rintro (rfl | rfl) <;> dsimp only
    · exact ⟨⟨by omega, by omega, by omega⟩, Or.inl ⟨by omega, by omega⟩⟩
    · exact ⟨⟨by omega, by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩

/-- **The live set at the top of the base column**: only the tail's north step one excess lower, the
base having no north step of excess `b`. This is the width that the appended path drops to `1` where
the base path drops to `0`. -/
theorem liveSteps_stairOne_base_top (hb : 0 < b) :
    liveSteps (stairOne b) ((0, b) : ℕ × ℕ) = {((1, b + b - 1) : ℕ × ℕ)} := by
  ext Q
  rw [mem_liveSteps_stairOne_iff (by omega), Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, hc⟩
    rcases hc with ⟨hle, he⟩ | ⟨hlt, he⟩
    · have hQ1 : Q.1 = 0 := by omega
      rw [hQ1] at he h2 h3
      push_cast at he
      omega
    · have hQ1 : Q.1 = 1 := by omega
      rw [hQ1] at he h2 h3
      push_cast at he
      exact Prod.ext_iff.2 ⟨hQ1, by omega⟩
  · rintro rfl
    dsimp only
    exact ⟨⟨by omega, by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩

/-- **The live set at a tail point**, below the corner: the two north steps of the same excess, one
of the base and one of the tail. Nothing lies to the right of a tail point. -/
theorem liveSteps_stairOne_tail_of_lt {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    liveSteps (stairOne b) ((1, b + k) : ℕ × ℕ)
      = {((0, k) : ℕ × ℕ), ((1, b + k) : ℕ × ℕ)} := by
  ext Q
  rw [mem_liveSteps_stairOne_iff (by omega), Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, hc⟩
    rcases hc with ⟨hle, he⟩ | ⟨hlt, he⟩
    · rcases (by omega : Q.1 = 0 ∨ Q.1 = 1) with hQ1 | hQ1 <;> rw [hQ1] at he h2 h3 <;>
        push_cast at he
      · exact Or.inl (Prod.ext_iff.2 ⟨hQ1, by omega⟩)
      · exact Or.inr (Prod.ext_iff.2 ⟨hQ1, by omega⟩)
    · omega
  · rintro (rfl | rfl) <;> dsimp only <;>
      exact ⟨⟨by omega, by omega, by omega⟩, Or.inl ⟨by omega, by omega⟩⟩

/-- **The live set at the corner of the tail column is empty**: nothing has excess `b`. -/
theorem liveSteps_stairOne_tail_top :
    liveSteps (stairOne b) ((1, b + b) : ℕ × ℕ) = ∅ := by
  ext Q
  rw [mem_liveSteps_stairOne_iff (by omega)]
  simp only [Finset.notMem_empty, iff_false, not_and]
  rintro ⟨h1, h2, h3⟩ hc
  rcases hc with ⟨hle, he⟩ | ⟨hlt, he⟩
  · rcases (by omega : Q.1 = 0 ∨ Q.1 = 1) with hQ1 | hQ1 <;> rw [hQ1] at he h2 h3 <;>
      push_cast at he <;> omega
  · omega

theorem sweepWidth_stairOne_base_of_lt {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    sweepWidth (stairOne b) ((0, k) : ℕ × ℕ) = 2 := by
  rw [sweepWidth, liveSteps_stairOne_base_of_lt hk0 hkb, Finset.card_insert_of_notMem (by simp),
    Finset.card_singleton]

theorem sweepWidth_stairOne_base_top (hb : 0 < b) :
    sweepWidth (stairOne b) ((0, b) : ℕ × ℕ) = 1 := by
  rw [sweepWidth, liveSteps_stairOne_base_top hb, Finset.card_singleton]

theorem sweepWidth_stairOne_tail_of_lt {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    sweepWidth (stairOne b) ((1, b + k) : ℕ × ℕ) = 2 := by
  rw [sweepWidth, liveSteps_stairOne_tail_of_lt hk0 hkb, Finset.card_insert_of_notMem (by simp),
    Finset.card_singleton]

theorem sweepWidth_stairOne_tail_top :
    sweepWidth (stairOne b) ((1, b + b) : ℕ × ℕ) = 0 := by
  rw [sweepWidth, liveSteps_stairOne_tail_top, Finset.card_empty]

/-- **At a base point the tail's live north step is strictly to the right.** This single fact is
what makes `q ≠ 0` necessary: it puts a `q^{-1}` on every type-`C` event of the base column, where
the `α = []` analysis at `a = 1` found none. -/
theorem sweepRight_stairOne_base_of_lt {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    sweepRight (stairOne b) ((0, k) : ℕ × ℕ) = 1 := by
  rw [sweepRight, liveSteps_stairOne_base_of_lt hk0 hkb]
  rw [show {P ∈ ({((0, k) : ℕ × ℕ), ((1, b + k - 1) : ℕ × ℕ)} : Finset (ℕ × ℕ)) |
      ((0, k) : ℕ × ℕ).1 < P.1} = {((1, b + k - 1) : ℕ × ℕ)} from ?_,
    Finset.card_singleton]
  ext P
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hP | hP, hlt⟩
    · rw [hP] at hlt; simp at hlt
    · exact hP
  · rintro rfl
    exact ⟨Or.inr rfl, by simp⟩

theorem sweepRight_stairOne_tail_of_lt {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    sweepRight (stairOne b) ((1, b + k) : ℕ × ℕ) = 0 := by
  rw [sweepRight, liveSteps_stairOne_tail_of_lt hk0 hkb]
  refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 ?_)
  intro P hP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with rfl | rfl <;> simp

theorem sweepRight_stairOne_tail_top :
    sweepRight (stairOne b) ((1, b + b) : ℕ × ℕ) = 0 := by
  rw [sweepRight, liveSteps_stairOne_tail_top]
  simp

theorem eventType_stairOne_base_of_lt {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    eventType (stairOne b) ((0, k) : ℕ × ℕ) = EventType.C := by
  have h0 : ht (stairOne b) 0 = 0 := ht_stairOne_zero
  have h1 : ht (stairOne b) (0 + 1) = b := ht_stairOne_one
  change (if k < ht (stairOne b) 0 then EventType.E
    else if ht (stairOne b) 0 < k then
      (if 0 + 1 ≤ 1 * (1 + 1) ∧ k < ht (stairOne b) (0 + 1) then EventType.C else EventType.A)
    else if 0 + 1 ≤ 1 * (1 + 1) ∧ k < ht (stairOne b) (0 + 1) then EventType.B
      else EventType.D) = EventType.C
  rw [h0, h1]
  split_ifs with h h' <;> first | rfl | omega

theorem eventType_stairOne_base_top (hb : 0 < b) :
    eventType (stairOne b) ((0, b) : ℕ × ℕ) = EventType.A := by
  have h0 : ht (stairOne b) 0 = 0 := ht_stairOne_zero
  have h1 : ht (stairOne b) (0 + 1) = b := ht_stairOne_one
  change (if b < ht (stairOne b) 0 then EventType.E
    else if ht (stairOne b) 0 < b then
      (if 0 + 1 ≤ 1 * (1 + 1) ∧ b < ht (stairOne b) (0 + 1) then EventType.C else EventType.A)
    else if 0 + 1 ≤ 1 * (1 + 1) ∧ b < ht (stairOne b) (0 + 1) then EventType.B
      else EventType.D) = EventType.A
  rw [h0, h1]
  split_ifs with h h' <;> first | rfl | omega

theorem eventType_stairOne_tail_of_lt {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    eventType (stairOne b) ((1, b + k) : ℕ × ℕ) = EventType.C := by
  have h0 : ht (stairOne b) 1 = b := ht_stairOne_one
  have h1 : ht (stairOne b) (1 + 1) = b * 2 := ht_stairOne_two
  change (if b + k < ht (stairOne b) 1 then EventType.E
    else if ht (stairOne b) 1 < b + k then
      (if 1 + 1 ≤ 1 * (1 + 1) ∧ b + k < ht (stairOne b) (1 + 1) then EventType.C
        else EventType.A)
    else if 1 + 1 ≤ 1 * (1 + 1) ∧ b + k < ht (stairOne b) (1 + 1) then EventType.B
      else EventType.D) = EventType.C
  rw [h0, h1]
  split_ifs with h h' <;> first | rfl | omega

theorem eventType_stairOne_tail_top (hb : 0 < b) :
    eventType (stairOne b) ((1, b + b) : ℕ × ℕ) = EventType.A := by
  have h0 : ht (stairOne b) 1 = b := ht_stairOne_one
  have h1 : ht (stairOne b) (1 + 1) = b * 2 := ht_stairOne_two
  change (if b + b < ht (stairOne b) 1 then EventType.E
    else if ht (stairOne b) 1 < b + b then
      (if 1 + 1 ≤ 1 * (1 + 1) ∧ b + b < ht (stairOne b) (1 + 1) then EventType.C
        else EventType.A)
    else if 1 + 1 ≤ 1 * (1 + 1) ∧ b + b < ht (stairOne b) (1 + 1) then EventType.B
      else EventType.D) = EventType.A
  rw [h0, h1]
  split_ifs with h h' <;> first | rfl | omega

/-! ### The four event operators -/

section Operators

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The base column's events carry `q^{-1}`**: a type-`C` event of width `2` with the tail's north
step live to its right. -/
theorem sweepOperator_stairOne_base_of_lt (q u : L) {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    sweepOperator q u (stairOne b) ((0, k) : ℕ × ℕ) = q ^ (-1 : ℤ) • corner q 2 := by
  rw [sweepOperator, eventType_stairOne_base_of_lt hk0 hkb, sweepWidth_stairOne_base_of_lt hk0 hkb,
    sweepRight_stairOne_base_of_lt hk0 hkb]
  norm_num

/-- **The top of the base column is `d_+^{(1)}`, not `d_+^{(0)}`**: the width has moved, because the
tail's north step of excess `b - 1` is live there. -/
theorem sweepOperator_stairOne_base_top (q u : L) (hb : 0 < b) :
    sweepOperator q u (stairOne b) ((0, b) : ℕ × ℕ) = dplus q 1 := by
  rw [sweepOperator, eventType_stairOne_base_top hb, sweepWidth_stairOne_base_top hb]

theorem sweepOperator_stairOne_tail_of_lt (q u : L) {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    sweepOperator q u (stairOne b) ((1, b + k) : ℕ × ℕ) = corner q 2 := by
  rw [sweepOperator, eventType_stairOne_tail_of_lt hk0 hkb, sweepWidth_stairOne_tail_of_lt hk0 hkb,
    sweepRight_stairOne_tail_of_lt hk0 hkb]
  norm_num

theorem sweepOperator_stairOne_tail_top (q u : L) (hb : 0 < b) :
    sweepOperator q u (stairOne b) ((1, b + b) : ℕ × ℕ) = dplus q 0 := by
  rw [sweepOperator, eventType_stairOne_tail_top hb, sweepWidth_stairOne_tail_top]

end Operators

/-! ### The rank bound, the rank gaps, and the peeling -/

/-- **Every swept point of the staircase has rank at most `6b + 1`**, attained at the corner of the
tail column `(1, 2b)`. -/
theorem pointRank_le_stairOne (hb : 0 < b) {P : ℕ × ℕ} (hP : P ∈ sweptRegion (stairOne b)) :
    pointRank 1 b (1 + 1) P ≤ 6 * (b : ℤ) + 1 := by
  obtain ⟨h1, h2, h3⟩ := mem_sweptRegion_stairOne_iff.1 hP
  rw [pointRank_one_b_two]
  rcases (by omega : P.1 = 0 ∨ P.1 = 1 ∨ P.1 = 2) with h | h | h
  · rw [h, show min ((0 : ℕ) + 1) 2 = 1 from rfl] at h3
    rw [h]; omega
  · rw [h, show min ((1 : ℕ) + 1) 2 = 2 from rfl] at h3
    rw [h]; omega
  · rw [h, show min ((2 : ℕ) + 1) 2 = 2 from rfl] at h3
    rw [h]; omega

/-- Two levels with the same outranking swept points, from the absence of a swept rank between. -/
theorem sweptAbove_eq_of_no_rank_between {a b N : ℕ} (y : Heights a b N) {η η' : ℚ}
    (hle : η ≤ η')
    (h : ∀ P ∈ sweptRegion y, ¬(η < ((pointRank a b N P : ℤ) : ℚ) ∧
      ((pointRank a b N P : ℤ) : ℚ) ≤ η')) :
    sweptAbove y η = sweptAbove y η' := by
  ext P
  simp only [sweptAbove, Finset.mem_filter]
  refine ⟨fun hP => ⟨hP.1, ?_⟩, fun hP => ⟨hP.1, lt_of_le_of_lt hle hP.2⟩⟩
  rcases lt_or_ge η' ((pointRank a b N P : ℤ) : ℚ) with h1 | h1
  · exact h1
  · exact absurd ⟨hP.2, h1⟩ (h P hP.1)

theorem add_one_le_of_half_lt {n r : ℤ} (h : (n : ℚ) + 1 / 2 < (r : ℚ)) : n + 1 ≤ r := by
  have h1 : ((n : ℤ) : ℚ) < ((r : ℤ) : ℚ) := by linarith
  have h2 : n < r := by exact_mod_cast h1
  omega

theorem le_of_le_half_add {n r : ℤ} (h : (r : ℚ) ≤ (n : ℚ) + 1 / 2) : r ≤ n := by
  have h1 : ((r : ℤ) : ℚ) < ((n : ℤ) : ℚ) + 1 := by linarith
  have h2 : r < n + 1 := by exact_mod_cast h1
  omega

/-- **The rank gap between two excess levels of the staircase.** Between the tail point of excess
`k` and the base point of excess `k + 1` the four intervening integers are `≡ 2, 3, 4, 5 (mod 6)`;
only `≡ 2` can be a rank at all, and then the point lies in the column `x = 2`, which the rectangle
stops at the corner `(2, 2b)` of rank `2`. So for `1 ≤ k` nothing is swept there. -/
theorem sweptAbove_stairOne_gap {k : ℕ} (hk : 0 < k) :
    sweptAbove (stairOne b) (((6 * (k : ℤ) + 1 : ℤ) : ℚ) + 1 / 2)
      = sweptAbove (stairOne b) (((6 * (k : ℤ) + 5 : ℤ) : ℚ) + 1 / 2) := by
  refine sweptAbove_eq_of_no_rank_between (stairOne b) (by push_cast; linarith) ?_
  rintro P hP ⟨hlo, hup⟩
  obtain ⟨h1, h2, h3⟩ := mem_sweptRegion_stairOne_iff.1 hP
  have hge := add_one_le_of_half_lt hlo
  have hle := le_of_le_half_add hup
  rw [pointRank_one_b_two] at hge hle
  rcases (by omega : P.1 = 0 ∨ P.1 = 1 ∨ P.1 = 2) with h | h | h
  · rw [h, show min ((0 : ℕ) + 1) 2 = 1 from rfl] at h3
    rw [h] at hge hle; omega
  · rw [h, show min ((1 : ℕ) + 1) 2 = 2 from rfl] at h3
    rw [h] at hge hle; omega
  · rw [h, show min ((2 : ℕ) + 1) 2 = 2 from rfl] at h3
    rw [h] at hge hle; omega

/-- **The separating level and the level just under the lowest excess agree.** The ranks strictly
between `5/2` and `11/2` are `3, 4, 5`, none of which is `≡ 0, 1, 2 (mod 6)`. -/
theorem sweptAbove_stairOne_sepLevel :
    sweptAbove (stairOne b) (sepLevel 1 (1 + 1))
      = sweptAbove (stairOne b) (((6 * (1 : ℤ) - 1 : ℤ) : ℚ) + 1 / 2) := by
  have hsep : sepLevel 1 (1 + 1) = ((2 : ℤ) : ℚ) + 1 / 2 := by
    rw [sepLevel]; push_cast; ring
  rw [hsep]
  refine sweptAbove_eq_of_no_rank_between (stairOne b) (by push_cast; linarith) ?_
  rintro P hP ⟨hlo, hup⟩
  obtain ⟨h1, h2, h3⟩ := mem_sweptRegion_stairOne_iff.1 hP
  have hge := add_one_le_of_half_lt hlo
  have hle := le_of_le_half_add hup
  rw [pointRank_one_b_two] at hge hle
  rcases (by omega : P.1 = 0 ∨ P.1 = 1 ∨ P.1 = 2) with h | h | h <;> rw [h] at hge hle <;> omega

theorem pointRank_stairOne_base (k : ℕ) :
    pointRank 1 b (1 + 1) ((0, k) : ℕ × ℕ) = 6 * (k : ℤ) := by
  rw [pointRank_one_b_two]; push_cast; ring

theorem pointRank_stairOne_tail (k : ℕ) :
    pointRank 1 b (1 + 1) ((1, b + k) : ℕ × ℕ) = 6 * (k : ℤ) + 1 := by
  rw [pointRank_one_b_two]; push_cast; ring

section Peel

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **One event of the staircase, peeled.** The window `(m - 1/2, m + 1/2)` about the rank `m` of
the point contains no other integer, so `HJO.Mellit.int_eq_of_half_window` discharges the isolation
hypothesis outright — no enumeration of the rectangle's ranks is needed. -/
theorem partialSweepWord_stairOne_step (q u : L) {m : ℤ} {P : ℕ × ℕ}
    (hP : P ∈ sweptRegion (stairOne b)) (hrk : pointRank 1 b (1 + 1) P = m) :
    partialSweepWord q u (stairOne b) (((m - 1 : ℤ) : ℚ) + 1 / 2)
      = sweepOperator q u (stairOne b) P
        * partialSweepWord q u (stairOne b) ((m : ℚ) + 1 / 2) := by
  refine partialSweepWord_eq_sweepOperator_mul q u one_pos ⟨m, rfl⟩ ?_ ?_ ?_ hP
  · rw [hrk]; push_cast; linarith
  · rw [hrk]; linarith
  · intro Q _ _ hlo hup
    rw [hrk]
    refine int_eq_of_half_window ?_ hup
    push_cast at hlo
    linarith

/-- Above the highest rank of the `2 × 2b` rectangle's swept region the partial word is empty. -/
theorem partialSweepWord_stairOne_top (q u : L) (hb : 0 < b) :
    partialSweepWord q u (stairOne b) (((6 * (b : ℤ) + 1 : ℤ) : ℚ) + 1 / 2) = 1 := by
  refine partialSweepWord_of_forall_le q u (stairOne b) _ fun P hP => ?_
  have h2 : ((pointRank 1 b (1 + 1) P : ℤ) : ℚ) ≤ ((6 * (b : ℤ) + 1 : ℤ) : ℚ) :=
    Int.cast_le.2 (pointRank_le_stairOne hb hP)
  refine le_trans h2 ?_
  linarith

/-- **The staircase's word, `j` excess levels down from the top.** Each level contributes the pair
`Δ^{(2)}` (at the tail point) and `q^{-1}Δ^{(2)}` (at the base point), and the two type-`A` events
at the top contribute `d_+^{(1)}d_+^{(0)}`. -/
theorem partialSweepWord_stairOne_aux (q u : L) (hb : 0 < b) :
    ∀ j : ℕ, j + 1 ≤ b →
      partialSweepWord q u (stairOne b) (((6 * ((b - j : ℕ) : ℤ) - 1 : ℤ) : ℚ) + 1 / 2)
        = (q ^ (-1 : ℤ) • (corner q 2 * corner q 2) : Module.End L (Total L)) ^ j
          * (dplus q 1 * dplus q 0) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [Nat.sub_zero,
      partialSweepWord_stairOne_step q u (mem_sweptRegion_stairOne_base (le_refl b))
        (pointRank_stairOne_base b),
      show ((6 * (b : ℤ) : ℤ) : ℚ) + 1 / 2 = (((6 * (b : ℤ) + 1) - 1 : ℤ) : ℚ) + 1 / 2 from by
        push_cast; ring,
      partialSweepWord_stairOne_step q u (mem_sweptRegion_stairOne_tail (le_refl b))
        (pointRank_stairOne_tail b),
      partialSweepWord_stairOne_top q u hb, sweepOperator_stairOne_base_top q u hb,
      sweepOperator_stairOne_tail_top q u hb, pow_zero, one_mul, mul_one]
  | succ n ih =>
    intro hn
    have hk0 : 0 < b - (n + 1) := by omega
    have hkb : b - (n + 1) < b := by omega
    have hcast : ((b - n : ℕ) : ℤ) = ((b - (n + 1) : ℕ) : ℤ) + 1 := by omega
    rw [partialSweepWord_stairOne_step q u (mem_sweptRegion_stairOne_base (by omega))
        (pointRank_stairOne_base (b - (n + 1))),
      show ((6 * ((b - (n + 1) : ℕ) : ℤ) : ℤ) : ℚ) + 1 / 2
        = (((6 * ((b - (n + 1) : ℕ) : ℤ) + 1) - 1 : ℤ) : ℚ) + 1 / 2 from by push_cast; ring,
      partialSweepWord_stairOne_step q u (mem_sweptRegion_stairOne_tail (by omega))
        (pointRank_stairOne_tail (b - (n + 1))),
      partialSweepWord_congr_of_sweptAbove_eq q u (stairOne b) (sweptAbove_stairOne_gap hk0),
      show ((6 * ((b - (n + 1) : ℕ) : ℤ) + 5 : ℤ) : ℚ) + 1 / 2
        = ((6 * ((b - n : ℕ) : ℤ) - 1 : ℤ) : ℚ) + 1 / 2 from by rw [hcast]; push_cast; ring,
      ih (by omega), sweepOperator_stairOne_base_of_lt q u hk0 hkb,
      sweepOperator_stairOne_tail_of_lt q u hk0 hkb, pow_succ']
    simp only [smul_mul_assoc, mul_assoc]

/-- **The staircase's word at the separating level.** `b - 1` pairs of width-`2` corners above the
two type-`A` events, each pair carrying one `q^{-1}`. -/
theorem partialSweepWord_stairOne (q u : L) (hb : 0 < b) :
    partialSweepWord q u (stairOne b) (sepLevel 1 (1 + 1))
      = (q ^ (-1 : ℤ) • (corner q 2 * corner q 2) : Module.End L (Total L)) ^ (b - 1)
        * (dplus q 1 * dplus q 0) := by
  have hcast : ((b - (b - 1) : ℕ) : ℤ) = 1 := by omega
  have h := partialSweepWord_stairOne_aux q u hb (b - 1) (by omega)
  rw [hcast] at h
  rw [partialSweepWord_congr_of_sweptAbove_eq q u (stairOne b) sweptAbove_stairOne_sepLevel]
  exact h

end Peel

/-! ### The two braid values, and the width-`2` corner on the band's vectors -/

section Braid

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

omit [Algebra ℚ L] in
/-- **`T_1` fixes a symmetric monomial in `y_1, y_2`.** -/
theorem braid_one_X_pow_mul_X_pow (q : L) (m : ℕ) :
    braid q 1 ((MvPolynomial.X 0 : Total L) ^ m * MvPolynomial.X 1 ^ m)
      = (MvPolynomial.X 0 : Total L) ^ m * MvPolynomial.X 1 ^ m := by
  refine braid_of_swapAux_eq q ?_
  rw [map_mul, map_pow, map_pow, swapAux_X, swapAux_X]
  simp only [show (1 : ℕ) - 1 = 0 from rfl, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

omit [Algebra ℚ L] in
/-- **`T_1(y_1^my_2^{m+1}) = qy_1^{m+1}y_2^m`.** The divided difference of the one-step-unbalanced
monomial is the balanced one, so the braid operator returns the transposed monomial with the factor
`q`. This is the value that the corner's ascending word contributes at each tail point of the
band. -/
theorem braid_one_X_pow_mul_X_pow_succ (q : L) (m : ℕ) :
    braid q 1 ((MvPolynomial.X 0 : Total L) ^ m * MvPolynomial.X 1 ^ (m + 1))
      = scal q * ((MvPolynomial.X 0 : Total L) ^ (m + 1) * MvPolynomial.X 1 ^ m) := by
  have hdd : dividedDiff 1 ((MvPolynomial.X 0 : Total L) ^ m * MvPolynomial.X 1 ^ (m + 1))
      = (MvPolynomial.X 0 : Total L) ^ m * MvPolynomial.X 1 ^ m := by
    refine (dividedDiff_unique (i := 1) le_rfl ?_).symm
    rw [map_mul, map_pow, map_pow, swapAux_X, swapAux_X]
    simp only [show (1 : ℕ) - 1 = 0 from rfl, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  have hq : (scal q : Total L) = 1 + scal (q - 1) := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  rw [braid_apply, hdd, map_mul, map_pow, map_pow, swapAux_X, swapAux_X]
  simp only [show (1 : ℕ) - 1 = 0 from rfl, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [hav, hq]
  ring

omit [Algebra ℚ L] in
theorem transportScalar_two :
    transportScalar L 2 = (MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 := by
  rw [transportScalar, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero,
    show (auxVar (0 + 1) : Total L) = MvPolynomial.X 0 from rfl,
    show (auxVar (1 + 1) : Total L) = MvPolynomial.X 1 from rfl]
  ring

/-- **`Δ^{(2)}((y_1y_2)^{m+1}) = -qy_1^{m+2}y_2^{m+1}`.** `HJO.Sweep.corner_transport_eq` at width
`2`, whose transport scalar is `y_1y_2`; only `q ≠ 1` is needed, the `q ≠ 0` of
`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` being avoidable because every vector of the band lies
in `y_1y_2V_2`. -/
theorem corner_two_balanced (hq : q ≠ 1) (m : ℕ) :
    corner q 2 (((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1) ^ (m + 1))
      = -(scal q * ((MvPolynomial.X 0 : Total L) ^ (m + 2) * MvPolynomial.X 1 ^ (m + 1))) := by
  have hmem : (((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1) ^ m) ∈ piece L (1 + 1) :=
    pow_mem (mul_mem (X_mem_piece (by omega)) (X_mem_piece (by omega))) m
  have hbe : ∀ G : Total L, braidEnd q 1 G = braid q 1 G := fun _ => rfl
  have h := corner_transport_eq hq 1 hmem
  rw [show (1 : ℕ) + 1 = 2 from rfl, transport_apply, transportScalar_two,
    show (auxVar 2 : Total L) = MvPolynomial.X 1 from rfl, cmAscWord_self, hbe,
    show (MvPolynomial.X 1 : Total L) * ((MvPolynomial.X 0 * MvPolynomial.X 1) ^ m)
      = (MvPolynomial.X 0 : Total L) ^ m * MvPolynomial.X 1 ^ (m + 1) from by ring,
    braid_one_X_pow_mul_X_pow_succ] at h
  rw [show (((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1) ^ (m + 1))
      = (MvPolynomial.X 0 : Total L) * MvPolynomial.X 1
        * ((MvPolynomial.X 0 * MvPolynomial.X 1) ^ m) from by ring, h]
  ring

/-- **`Δ^{(2)}(y_1^{m+2}y_2^{m+1}) = -(y_1y_2)^{m+2}`.** The second of the two corner letters of an
excess level; here the ascending word acts on a symmetric monomial and contributes no `q`. -/
theorem corner_two_unbalanced (hq : q ≠ 1) (m : ℕ) :
    corner q 2 ((MvPolynomial.X 0 : Total L) ^ (m + 2) * MvPolynomial.X 1 ^ (m + 1))
      = -(((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1) ^ (m + 2)) := by
  have hmem : ((MvPolynomial.X 0 : Total L) ^ (m + 1) * MvPolynomial.X 1 ^ m) ∈ piece L (1 + 1) :=
    mul_mem (pow_mem (X_mem_piece (by omega)) _) (pow_mem (X_mem_piece (by omega)) _)
  have hbe : ∀ G : Total L, braidEnd q 1 G = braid q 1 G := fun _ => rfl
  have h := corner_transport_eq hq 1 hmem
  rw [show (1 : ℕ) + 1 = 2 from rfl, transport_apply, transportScalar_two,
    show (auxVar 2 : Total L) = MvPolynomial.X 1 from rfl, cmAscWord_self, hbe,
    show (MvPolynomial.X 1 : Total L)
        * ((MvPolynomial.X 0 : Total L) ^ (m + 1) * MvPolynomial.X 1 ^ m)
      = (MvPolynomial.X 0 : Total L) ^ (m + 1) * MvPolynomial.X 1 ^ (m + 1) from by ring,
    braid_one_X_pow_mul_X_pow] at h
  rw [show ((MvPolynomial.X 0 : Total L) ^ (m + 2) * MvPolynomial.X 1 ^ (m + 1))
      = (MvPolynomial.X 0 : Total L) * MvPolynomial.X 1
        * ((MvPolynomial.X 0 : Total L) ^ (m + 1) * MvPolynomial.X 1 ^ m) from by ring, h]
  ring

/-- **The paired corner letters of the band, iterated**:
`(Δ^{(2)}Δ^{(2)})^k(y_1y_2) = q^k(y_1y_2)^{k+1}`. Each excess level multiplies by `-q y_1` and then
by `-y_2`, so the two signs cancel and one `q` accumulates — exactly the `q` that the `q^{-1}` of
the base point's type-`C` event will cancel. -/
theorem corner_two_sq_pow_apply (hq : q ≠ 1) (k : ℕ) :
    ((corner q 2 * corner q 2) ^ k) ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1)
      = scal (q ^ k) * ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hstep : ((corner q 2 * corner q 2) ^ (n + 1))
        ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1)
        = corner q 2 (corner q 2 (((corner q 2 * corner q 2) ^ n)
          ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1))) := by
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    rw [hstep, ih, ← smul_eq_scal_mul, map_smul, corner_two_balanced hq n, smul_neg, map_neg,
      map_smul, ← smul_eq_scal_mul, map_smul, corner_two_unbalanced hq n, smul_neg, smul_neg,
      neg_neg, smul_smul, ← pow_succ, smul_eq_scal_mul]

end Braid

/-! ### The two sides of the band identity, evaluated -/

section Sides

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
theorem neg_one_pow_total (n : ℕ) : ((-1 : Total L)) ^ n = scal ((-1 : L) ^ n) := by
  rw [scal_pow, scal_neg, scal_one]

/-- **The left-hand side of the band identity is `y_1^by_2^b`.** The `b - 1` factors of `q^{-1}`
from the base column's type-`C` events cancel the `q^{b-1}` that the corner iteration accumulates.
This is the only place `q ≠ 0` is used, and `HJO.Mellit.not_band_one_left_one_one_of_q_zero` shows
it cannot be dropped. -/
theorem partialSweepWord_stairOne_apply_one (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hb : 0 < b) :
    partialSweepWord q u (stairOne b) (sepLevel 1 (1 + 1)) (1 : Total L)
      = (MvPolynomial.X 0 : Total L) ^ b * MvPolynomial.X 1 ^ b := by
  have hcancel : ((q ^ (-1 : ℤ)) ^ (b - 1) : L) * q ^ (b - 1) = 1 := by
    rw [zpow_neg_one, ← mul_pow, inv_mul_cancel₀ hq0, one_pow]
  rw [partialSweepWord_stairOne q u hb, smul_pow, Module.End.mul_apply, Module.End.mul_apply,
    dplus_zero_one, map_neg, dplus_one_X_zero, neg_neg,
    show (MvPolynomial.X 0 : Total L) * MvPolynomial.X 1
      = (MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 from rfl,
    LinearMap.smul_apply, corner_two_sq_pow_apply hq1 (b - 1), ← smul_eq_scal_mul, smul_smul,
    hcancel, one_smul, show b - 1 + 1 = b from by omega]
  ring

/-- **The right-hand side of the band identity is `y_1^by_2^b` too.** The stage at `a = 1` sends
`y_1^b` to `-(-1)^{b-1}y_1^by_2^b`: `d^*_+` moves the variable up one index
(`HJO.Sweep.dplusStar_auxVar_pow`, which is `u`-free), the slope word of `(1, b)` is `b - 1` letters
`y` and no letter `z` (`HJO.Mellit.slopeWord_one_left`), and `T_{2↘1}` fixes the resulting symmetric
monomial. -/
theorem stageTotal_one_left_auxVar_pow (q u : L) (m : ℕ) :
    stageTotal q u 1 (m + 1) 1 1 ((MvPolynomial.X 0 : Total L) ^ (m + 1))
      = -(((-1 : L) ^ m) • ((MvPolynomial.X 0 : Total L) ^ (m + 1)
          * MvPolynomial.X 1 ^ (m + 1))) := by
  have hav1 : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hav2 : (auxVar 2 : Total L) = MvPolynomial.X 1 := rfl
  have hstar : dplusStar q u 1 ((MvPolynomial.X 0 : Total L) ^ (m + 1))
      = (MvPolynomial.X 1 : Total L) ^ (m + 1) := by
    rw [← hav1, ← hav2]
    exact dplusStar_auxVar_pow q u le_rfl le_rfl (m + 1)
  have hslope : ∀ G : Total L, slopeOperator q u (1 + 1) 1 (m + 1) G
      = (-(MvPolynomial.X 0 : Total L)) ^ m * G := by
    intro G
    rw [slopeOperator_eq_slopeEval, slopeEval_one_left _ _ (by omega : 1 ≤ m + 1),
      neg_mulLeft_pow_apply, hav1, Nat.add_sub_cancel]
  have hbe : ∀ G : Total L, braidEnd q 1 G = braid q 1 G := fun _ => rfl
  rw [stageTotal_one, Module.End.mul_apply, replOneTotal, LinearMap.smul_apply,
    Module.End.mul_apply, LinearMap.neg_apply, Module.End.mul_apply, hstar,
    LinearMap.mulLeft_apply, hav1, hslope, trainDownEnd_succ_self,
    show (-(MvPolynomial.X 0 : Total L)) ^ m
        * -((MvPolynomial.X 0 : Total L) * (MvPolynomial.X 1 : Total L) ^ (m + 1))
      = -(((-1 : Total L)) ^ m
          * ((MvPolynomial.X 0 : Total L) ^ (m + 1) * MvPolynomial.X 1 ^ (m + 1))) from by
      rw [neg_pow]; ring,
    neg_one_pow_total, ← smul_eq_scal_mul, Nat.sub_self, pow_zero, one_smul, map_neg,
    map_smul, hbe, braid_one_X_pow_mul_X_pow]

end Sides

/-! ### The band identity at `a = 1`, `α = (1)`, `A = 1`, and its failure at `q = 0` -/

section Identity

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The fibre sum of the band identity is one partial word.** The index set is the singleton
`{HJO.Mellit.baseOne b}` (`HJO.Mellit.aboveReturnPaths_one_b`), the appended path is the staircase,
the outer word is empty and the band word is the whole partial word. -/
theorem band_sum_eq_partialSweepWord (q u : L) :
    ∑ w ∈ aboveReturnPaths 1 b 1 [1],
        bandSweepWord q u (appendHeights (baseOne b) w) (sepLevel 1 (1 + 1)) ((1 : ℤ) * (b * 1))
          (outerSweepWord q u (baseOne b) (sepLevel 1 1) ((1 : ℤ) * (b * 1)) (1 : Total L))
      = partialSweepWord q u (stairOne b) (sepLevel 1 (1 + 1)) (1 : Total L) := by
  rw [aboveReturnPaths_one_b, Finset.sum_singleton,
    show appendHeights (baseOne b) (baseOne b) = stairOne b from rfl,
    outerSweepWord_eq_one_of_forall_le q u (baseOne b) _ _
      (fun P hP => diagExcess_le_of_mem_sweptRegion_baseOne hP),
    Module.End.one_apply,
    bandSweepWord_eq_partialSweepWord_of_forall_le q u (stairOne b) _ _
      (fun P hP => diagExcess_le_of_mem_sweptRegion_stairOne hP)]

theorem corner_one_pow_dplus_zero_one (q : L) (hq1 : q ≠ 1) (hb : 0 < b) :
    (corner q 1 ^ (b - 1)) (dplus q 0 (1 : Total L))
      = -(((-1 : L) ^ (b - 1)) • (MvPolynomial.X 0 : Total L) ^ b) := by
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have h1 : dplus q 0 (1 : Total L) = -((auxVar 1 : Total L) ^ 1) := by
    rw [pow_one, hav, dplus_zero_one]
  rw [h1, map_neg, corner_one_pow_auxVar_pow q hq1 (b - 1) 1, neg_one_pow_total,
    ← smul_eq_scal_mul, show 1 + (b - 1) = b from by omega, hav]

/-- **The vector the base path contributes**, `(-1)^{b}y_1^b`, unconditional in `q` beyond
`q ≠ 1`. -/
theorem band_base_eq (q u : L) (hq1 : q ≠ 1) (hb : 0 < b) :
    bandSweepWord q u (baseOne b) (sepLevel 1 1) ((1 : ℤ) * (b * 1))
        (outerSweepWord q u (baseOne b) (sepLevel 1 1) ((1 : ℤ) * (b * 1)) (1 : Total L))
      = -(((-1 : L) ^ (b - 1)) • (MvPolynomial.X 0 : Total L) ^ b) := by
  rw [outerSweepWord_eq_one_of_forall_le q u (baseOne b) _ _
      (fun P hP => diagExcess_le_of_mem_sweptRegion_baseOne hP),
    Module.End.one_apply,
    bandSweepWord_eq_partialSweepWord_of_forall_le q u (baseOne b) _ _
      (fun P hP => diagExcess_le_of_mem_sweptRegion_baseOne hP),
    partialSweepWord_baseOne q u hb, Module.End.mul_apply,
    corner_one_pow_dplus_zero_one q hq1 hb]

/-- **The `hband` clause of `HJO.Mellit.sweepAppend_of_forall_band` holds at `a = 1`, `α = (1)`,
`A = 1`, for every `b > 0`, every `u`, and every `q ∉ {0, 1}`.**

This is the first instance of that clause at `0 < α.sum`; every earlier worked case of
`HJO.Mellit.SweepAppend` — `HJO.Mellit.sweepAppend_nil_one_one_b`,
`HJO.Mellit.sweepAppend_nil_two_three_one`, `HJO.Mellit.sweepAppend_nil_one_two_two` — was the
`hzero` clause at `α = []`.

Both sides are the single monomial `y_1^by_2^b`. On the left the `b` excess levels of the band each
contribute a width-`2` corner at the tail point and a width-`2` corner carrying `q^{-1}` at the base
point, plus the two type-`A` events `d_+^{(1)}d_+^{(0)}` at the top; the `q^{b-1}` the corners
accumulate cancels the `q^{-(b-1)}` of the type-`C` events. On the right the base path's own word is
`Δ^{(1)b-1}d_+^{(0)}`, giving `(-y_1)^b`, and the stage multiplies by `y_2^b` up to sign. **No
factor of the base's word occurs in the appended word**: the widths have all moved, which is the
obstruction `HJO/Shuffle/SweepAppendBandInterleave.lean` names, and the identity holds
anyway. -/
theorem band_one_left_one_one (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hb : 0 < b) :
    ∑ w ∈ aboveReturnPaths 1 b 1 [1],
        bandSweepWord q u (appendHeights (baseOne b) w) (sepLevel 1 (1 + 1)) ((1 : ℤ) * (b * 1))
          (outerSweepWord q u (baseOne b) (sepLevel 1 1) ((1 : ℤ) * (b * 1)) (1 : Total L))
      = ((-1 : L) ^ ((1 - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) •
          stageTotal q u 1 b 1 1
            (bandSweepWord q u (baseOne b) (sepLevel 1 1) ((1 : ℤ) * (b * 1))
              (outerSweepWord q u (baseOne b) (sepLevel 1 1) ((1 : ℤ) * (b * 1))
                (1 : Total L))) := by
  obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
  have hsq : ((-1 : L) ^ m) * ((-1 : L) ^ m) = 1 := by rw [← mul_pow]; norm_num
  rw [band_sum_eq_partialSweepWord q u, partialSweepWord_stairOne_apply_one q u hq0 hq1 hb,
    band_base_eq q u hq1 hb, Nat.add_sub_cancel, map_neg, map_smul,
    stageTotal_one_left_auxVar_pow q u m,
    show ((-1 : L) ^ ((1 - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) = 1 from by norm_num,
    one_smul, smul_neg, smul_smul, hsq, one_smul, neg_neg]

/-- **At `q = 0` the left-hand side collapses.** Each of the `b - 1` type-`C` events of the base
column carries `q^{-1}`, which is the zero map at `q = 0`. -/
theorem partialSweepWord_stairOne_apply_one_q_zero (u : L) (hb : 2 ≤ b) :
    partialSweepWord (0 : L) u (stairOne b) (sepLevel 1 (1 + 1)) (1 : Total L) = 0 := by
  rw [partialSweepWord_stairOne (0 : L) u (by omega), smul_pow,
    show ((0 : L) ^ (-1 : ℤ)) ^ (b - 1) = 0 from by
      rw [zpow_neg_one, inv_zero]; exact zero_pow (by omega),
    zero_smul, zero_mul, LinearMap.zero_apply]

/-- **The `hband` clause is FALSE at `q = 0`, for `a = 1`, every `b ≥ 2`, `α = (1)`, `A = 1` and
every `u`.** So `q ≠ 0` is a real exclusion in `hband` and not an artefact of
`HJO.Mellit.band_one_left_one_one`'s proof.

This reaches where `HJO.Mellit.not_sweepAppend_nil_two_three_one_of_q_zero` cannot. That refutation
needs `2 ≤ a`, and its docstring records why: at `a = 1` on the *one-column* rectangle no event has
a live north step to its right, so no negative power of `q` occurs. Once `0 < α.sum` that stops
being true at `a = 1` as well — the tail's north step of excess `j - 1` is live at the base point of
excess `j` and strictly to its right (`HJO.Mellit.sweepRight_stairOne_base_of_lt`) — while the
right-hand side is untouched by `q = 0`, the slope word of `(1, b)` having no letter `z`. -/
theorem not_band_one_left_one_one_of_q_zero (u : L) (hb : 2 ≤ b) :
    ∑ w ∈ aboveReturnPaths 1 b 1 [1],
        bandSweepWord (0 : L) u (appendHeights (baseOne b) w) (sepLevel 1 (1 + 1))
            ((1 : ℤ) * (b * 1))
          (outerSweepWord (0 : L) u (baseOne b) (sepLevel 1 1) ((1 : ℤ) * (b * 1)) (1 : Total L))
      ≠ ((-1 : L) ^ ((1 - 1) * 1) * ((0 : L) * u) ^ (1 - ((1 : ℕ) : ℤ))) •
          stageTotal (0 : L) u 1 b 1 1
            (bandSweepWord (0 : L) u (baseOne b) (sepLevel 1 1) ((1 : ℤ) * (b * 1))
              (outerSweepWord (0 : L) u (baseOne b) (sepLevel 1 1) ((1 : ℤ) * (b * 1))
                (1 : Total L))) := by
  obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
  have hsq : ((-1 : L) ^ m) * ((-1 : L) ^ m) = 1 := by rw [← mul_pow]; norm_num
  have hne : ((MvPolynomial.X 0 : Total L) ^ (m + 1) * MvPolynomial.X 1 ^ (m + 1)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (MvPolynomial.X_ne_zero 0))
      (pow_ne_zero _ (MvPolynomial.X_ne_zero 1))
  rw [band_sum_eq_partialSweepWord (0 : L) u, partialSweepWord_stairOne_apply_one_q_zero u hb,
    band_base_eq (0 : L) u (by norm_num) (by omega), Nat.add_sub_cancel, map_neg, map_smul,
    stageTotal_one_left_auxVar_pow (0 : L) u m,
    show ((-1 : L) ^ ((1 - 1) * 1) * ((0 : L) * u) ^ (1 - ((1 : ℕ) : ℤ))) = 1 from by norm_num,
    one_smul, smul_neg, smul_smul, hsq, one_smul, neg_neg]
  exact hne.symm

/-- **The same identity in the literal shape of the `hband` hypothesis** of
`HJO.Mellit.sweepAppend_of_forall_band`, read at `α = (1)`, `A = 1`, `a = 1`: the quantifier over
`z` and the arithmetic of `α.sum` and `α.length` spelled as that hypothesis spells them, so that the
match is checkable without unfolding anything. -/
theorem band_clause_one_left_one_one (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hb : 0 < b) :
    ∀ z ∈ aboveReturnPaths 1 b (([1] : List ℕ)).sum ([1] : List ℕ),
      ∑ w ∈ aboveReturnPaths 1 b 1 [1],
          bandSweepWord q u (appendHeights z w) (sepLevel 1 ((([1] : List ℕ)).sum + 1))
              ((1 : ℤ) * (b * 1))
            (outerSweepWord q u z (sepLevel 1 (([1] : List ℕ)).sum) ((1 : ℤ) * (b * 1))
              (1 : Total L))
        = ((-1 : L) ^ ((1 - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) •
            stageTotal q u 1 b (([1] : List ℕ)).length 1
              (bandSweepWord q u z (sepLevel 1 (([1] : List ℕ)).sum) ((1 : ℤ) * (b * 1))
                (outerSweepWord q u z (sepLevel 1 (([1] : List ℕ)).sum) ((1 : ℤ) * (b * 1))
                  (1 : Total L))) := by
  intro z hz
  obtain rfl : z = baseOne b := eq_baseOne (mem_aboveReturnPaths_iff.1 hz).1
  exact band_one_left_one_one q u hq0 hq1 hb

end Identity

end HJO.Mellit

end
