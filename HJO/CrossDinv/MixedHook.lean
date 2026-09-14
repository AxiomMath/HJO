/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import HJO.CrossDinv.Diagram
public meta import HJO.Attr

/-! # The mixed arm, the mixed leg and the mixed hook condition

The cross-dinv statistic measures the arm of a cell in one filter diagram and its leg in another,
so neither statistic is the arm or leg of a single path: `arm_D (r, i)` counts the shifts
`1 ≤ u ≤ a` at which `(r, i)` still lies in the cross arm set `A^D_u`, and `leg_E (r, i)` counts
the shifts `1 ≤ v ≤ b` at which it still lies in the cross leg set `L^E_v`.

Counting the shifts is what makes the two statistics usable: the arm sets shrink as the shift
grows and reduce at shift `0` to the diagram itself, so the set of admissible shifts is an initial
segment `{1, …, arm}` of the positive integers -- `eq_Icc_card` is that step -- and therefore
`arm_D (r, i) ≥ u` is equivalent to membership of `A^D_u`. That equivalence, and its analogue for
the leg, are the only things the counting argument uses; the same argument gives the bound
`arm_D (r, i) ≤ a - 2`, since a shift of `u` needs `r - u ≥ 1` and `r ≤ a - 1`.

The mixed hook condition is the statement that the two mixed hook slopes straddle `a / b`:
`arm / (leg + 1) < a / b` and, unless the leg vanishes, `a / b < (arm + 1) / leg`. The disjunct at
`leg = 0` is not a convention -- the second quotient is undefined there -- and the asymmetry
between the two clauses is genuine: the transposed pair of conditions is vacuous at `arm = 0`
instead, and states something else. `isMixedHook_iff` clears the denominators and
`isMixedHook_iff_beta` converts the result into the staircase window
`β (arm) ≤ leg ≤ β (arm + 1)`, which is the shape the alternating sum of cross tail counts
produces.
-/

@[expose] public section

open Finset NumericalSemigroup HJO.RankOneDinv

namespace HJO.CrossDinv

variable {a b : ℕ} {D E : Finset ℕ}

/-! ### Downward-closed sets of positive integers -/

/-- A set of positive integers closed downwards is the initial segment of length its own
cardinality. -/
theorem eq_Icc_card {S : Finset ℤ} (hS : ∀ u ∈ S, 1 ≤ u)
    (hdc : ∀ u ∈ S, ∀ u' : ℤ, 1 ≤ u' → u' ≤ u → u' ∈ S) : S = Finset.Icc 1 (#S : ℤ) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨M, hM1, hSeq⟩ : ∃ M : ℤ, 1 ≤ M ∧ S = Finset.Icc 1 M :=
      ⟨S.max' hne, hS _ (S.max'_mem hne), by
        ext u
        simp only [Finset.mem_Icc]
        exact ⟨fun h => ⟨hS u h, S.le_max' u h⟩, fun h => hdc _ (S.max'_mem hne) u h.1 h.2⟩⟩
    subst hSeq
    rw [Int.card_Icc]
    congr 1
    omega

/-! ### The mixed arm and the mixed leg -/

/-- **The mixed arm** `arm_D (r, i)`: the number of column shifts `1 ≤ u ≤ a` at which `(r, i)`
lies in the cross arm set `A^D_u`. -/
@[hjo "def_mixed_arm"]
noncomputable def mixedArm (a b : ℕ) (D : Finset ℕ) (q : ℤ × ℤ) : ℕ :=
  #{u ∈ Finset.Icc (1 : ℤ) (a : ℤ) | q ∈ crossArmSet a b D u}

/-- **The mixed leg** `leg_E (r, i)`: the number of row shifts `1 ≤ v ≤ b` at which `(r, i)` lies
in the cross leg set `L^E_v`. -/
@[hjo "def_mixed_leg"]
noncomputable def mixedLeg (a b : ℕ) (E : Finset ℕ) (q : ℤ × ℤ) : ℕ :=
  #{v ∈ Finset.Icc (1 : ℤ) (b : ℤ) | q ∈ crossLegSet a b E v}

/-- A column shift admitted by a cell is at most `a - 2`: the shifted cell needs `r - u ≥ 1`
while `r ≤ a - 1`. -/
theorem le_of_mem_crossArmSet {u : ℤ} {q : ℤ × ℤ} (h : q ∈ crossArmSet a b D u) :
    u ≤ (a : ℤ) - 2 := by
  rw [mem_crossArmSet] at h
  obtain ⟨-, h2, -, h4⟩ := h
  obtain ⟨h5, -, -, -⟩ := cellZ_bounds h4
  omega

/-- A row shift admitted by a cell is at most `b - 2`: the shifted cell needs `i + v < b`
while `i ≥ 1`. -/
theorem le_of_mem_crossLegSet {v : ℤ} {q : ℤ × ℤ} (h : q ∈ crossLegSet a b E v) :
    v ≤ (b : ℤ) - 2 := by
  rw [mem_crossLegSet] at h
  obtain ⟨-, -, h3, h4⟩ := h
  obtain ⟨-, -, -, h5⟩ := cellZ_bounds h4
  omega

/-- The column shifts admitted by a cell of `𝒟_D` form the initial segment `{1, …, arm_D}`. -/
theorem crossArmSet_filter_eq (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hD : Gaps.IsOrderFilter a b D) (q : ℤ × ℤ) :
    {u ∈ Finset.Icc (1 : ℤ) (a : ℤ) | q ∈ crossArmSet a b D u}
      = Finset.Icc 1 (mixedArm a b D q : ℤ) := by
  refine eq_Icc_card (fun u hu => (mem_Icc.mp (mem_filter.mp hu).1).1) fun u hu u' h1 h2 => ?_
  obtain ⟨hu1, hu2⟩ := hu |> mem_filter.mp
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨h1, ?_⟩, ?_⟩
  · exact h2.trans (mem_Icc.mp hu1).2
  · exact crossArmSet_subset hco ha hb hD (by omega) h2 hu2

/-- The row shifts admitted by a cell of `𝒟_E` form the initial segment `{1, …, leg_E}`. -/
theorem crossLegSet_filter_eq (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hE : Gaps.IsOrderFilter a b E) (q : ℤ × ℤ) :
    {v ∈ Finset.Icc (1 : ℤ) (b : ℤ) | q ∈ crossLegSet a b E v}
      = Finset.Icc 1 (mixedLeg a b E q : ℤ) := by
  refine eq_Icc_card (fun v hv => (mem_Icc.mp (mem_filter.mp hv).1).1) fun v hv v' h1 h2 => ?_
  obtain ⟨hv1, hv2⟩ := hv |> mem_filter.mp
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨h1, ?_⟩, ?_⟩
  · exact h2.trans (mem_Icc.mp hv1).2
  · exact crossLegSet_subset hco ha hb hE (by omega) h2 hv2

/-- **The mixed arm is bounded by the width**: `arm_D (r, i) ≤ a - 2` at a cell of `𝒟_D`. -/
@[hjo "lem_mixed_arm_bound"]
theorem mixedArm_le (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hD : Gaps.IsOrderFilter a b D) {q : ℤ × ℤ} (_hq : q ∈ cellZ a b D) :
    (mixedArm a b D q : ℤ) ≤ (a : ℤ) - 2 := by
  rcases Nat.eq_zero_or_pos (mixedArm a b D q) with h | h
  · rw [h]
    omega
  · have hmem : (mixedArm a b D q : ℤ) ∈ Finset.Icc 1 (mixedArm a b D q : ℤ) :=
      mem_Icc.mpr ⟨by omega, le_rfl⟩
    rw [← crossArmSet_filter_eq hco ha hb hD q, mem_filter] at hmem
    exact le_of_mem_crossArmSet hmem.2

/-- **The mixed arm as membership**: at a cell of `𝒟_D` and for `u ≥ 0`, `arm_D (r, i) ≥ u`
exactly when `(r, i)` lies in `A^D_u`. -/
@[hjo "lem_mixed_arm_ge"]
theorem le_mixedArm_iff (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hD : Gaps.IsOrderFilter a b D) {q : ℤ × ℤ} (hq : q ∈ cellZ a b D) {u : ℤ} (hu : 0 ≤ u) :
    u ≤ (mixedArm a b D q : ℤ) ↔ q ∈ crossArmSet a b D u := by
  have hS := crossArmSet_filter_eq hco ha hb hD q
  rcases eq_or_lt_of_le hu with rfl | hu1
  · refine ⟨fun _ => ?_, fun _ => by positivity⟩
    rw [crossArmSet_zero]
    exact hq
  · constructor
    · intro h
      have h2 : u ∈ Finset.Icc (1 : ℤ) (mixedArm a b D q : ℤ) := mem_Icc.mpr ⟨by omega, h⟩
      rw [← hS, mem_filter] at h2
      exact h2.2
    · intro h
      have h3 := le_of_mem_crossArmSet h
      have h2 : u ∈ {u ∈ Finset.Icc (1 : ℤ) (a : ℤ) | q ∈ crossArmSet a b D u} :=
        mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, h⟩
      rw [hS, mem_Icc] at h2
      exact h2.2

/-- **The mixed leg as membership**: at a cell of `𝒟_E` and for `v ≥ 0`, `leg_E (r, i) ≥ v`
exactly when `(r, i)` lies in `L^E_v`. -/
@[hjo "lem_mixed_leg_ge"]
theorem le_mixedLeg_iff (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hE : Gaps.IsOrderFilter a b E) {q : ℤ × ℤ} (hq : q ∈ cellZ a b E) {v : ℤ} (hv : 0 ≤ v) :
    v ≤ (mixedLeg a b E q : ℤ) ↔ q ∈ crossLegSet a b E v := by
  have hS := crossLegSet_filter_eq hco ha hb hE q
  rcases eq_or_lt_of_le hv with rfl | hv1
  · refine ⟨fun _ => ?_, fun _ => by positivity⟩
    rw [crossLegSet_zero]
    exact hq
  · constructor
    · intro h
      have h2 : v ∈ Finset.Icc (1 : ℤ) (mixedLeg a b E q : ℤ) := mem_Icc.mpr ⟨by omega, h⟩
      rw [← hS, mem_filter] at h2
      exact h2.2
    · intro h
      have h3 := le_of_mem_crossLegSet h
      have h2 : v ∈ {v ∈ Finset.Icc (1 : ℤ) (b : ℤ) | q ∈ crossLegSet a b E v} :=
        mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, h⟩
      rw [hS, mem_Icc] at h2
      exact h2.2

/-! ### The mixed hook condition -/

/-- The mixed hook condition at a cell: the two mixed hook slopes straddle `a / b`, the quotients
being taken in `ℚ`. The disjunct at `leg = 0` is forced -- the second quotient is undefined
there -- and the asymmetry between the two clauses is genuine, the transposed pair of conditions
being vacuous at `arm = 0` instead. -/
def IsMixedHook (a b : ℕ) (D E : Finset ℕ) (q : ℤ × ℤ) : Prop :=
  (mixedArm a b D q : ℚ) / ((mixedLeg a b E q : ℚ) + 1) < (a : ℚ) / (b : ℚ) ∧
    (mixedLeg a b E q = 0 ∨
      (a : ℚ) / (b : ℚ) < ((mixedArm a b D q : ℚ) + 1) / (mixedLeg a b E q : ℚ))

/-- **The mixed hook set** `H_{D,E}`: the cells whose mixed hook slopes straddle `a / b`. -/
@[hjo "def_mixed_hook_set"]
def mixedHookSet (a b : ℕ) (D E : Finset ℕ) : Set (ℤ × ℤ) := {q | IsMixedHook a b D E q}

/-- Membership in the mixed hook set is the mixed hook condition. -/
theorem mem_mixedHookSet {q : ℤ × ℤ} : q ∈ mixedHookSet a b D E ↔ IsMixedHook a b D E q := Iff.rfl

/-- The mixed hook condition is decidable, the mixed arm and leg being cardinalities. The instance
is noncomputable because they are defined by `Finset.Icc` on `ℤ`, whose interval instance is. -/
noncomputable instance instDecidableMemMixedHookSet (a b : ℕ) (D E : Finset ℕ) :
    DecidablePred (· ∈ mixedHookSet a b D E) := fun _ => Classical.dec _

/-- **The mixed hook condition with the denominators cleared**: `(r, i)` lies in `H_{D,E}` exactly
when `b·arm < a (leg + 1)` and `a·leg < b (arm + 1)`. -/
@[hjo "lem_mixed_hook_integer"]
theorem isMixedHook_iff (hb : 0 < b) (q : ℤ × ℤ) :
    IsMixedHook a b D E q ↔
      b * mixedArm a b D q < a * (mixedLeg a b E q + 1) ∧
        a * mixedLeg a b E q < b * (mixedArm a b D q + 1) := by
  have hb' : (0 : ℚ) < (b : ℚ) := by positivity
  set A := mixedArm a b D q with hA
  set L := mixedLeg a b E q with hL
  have hL1 : (0 : ℚ) < (L : ℚ) + 1 := by positivity
  have e1 : ((A : ℚ) / ((L : ℚ) + 1) < (a : ℚ) / (b : ℚ)) ↔ b * A < a * (L + 1) := by
    rw [div_lt_div_iff₀ hL1 hb']
    constructor
    · intro h
      have h2 : ((b * A : ℕ) : ℚ) < ((a * (L + 1) : ℕ) : ℚ) := by push_cast; linarith
      exact_mod_cast h2
    · intro h
      have h2 : ((b * A : ℕ) : ℚ) < ((a * (L + 1) : ℕ) : ℚ) := by exact_mod_cast h
      push_cast at h2
      linarith
  rw [IsMixedHook, e1]
  refine and_congr_right fun _ => ?_
  rcases Nat.eq_zero_or_pos L with h | h
  · refine ⟨fun _ => ?_, fun _ => Or.inl h⟩
    rw [h]
    simpa using Nat.mul_pos hb (Nat.succ_pos A)
  · have hL0 : (0 : ℚ) < (L : ℚ) := by exact_mod_cast h
    rw [or_iff_right (by omega), div_lt_div_iff₀ hb' hL0]
    constructor
    · intro h2
      have h3 : ((a * L : ℕ) : ℚ) < ((b * (A + 1) : ℕ) : ℚ) := by push_cast; linarith
      exact_mod_cast h3
    · intro h2
      have h3 : ((a * L : ℕ) : ℚ) < ((b * (A + 1) : ℕ) : ℚ) := by exact_mod_cast h2
      push_cast at h3
      linarith

/-- **The mixed hook criterion**: at a cell of `𝒟_D`, the mixed hook condition is the staircase
window `β (arm_D) ≤ leg_E ≤ β (arm_D + 1)`. -/
@[hjo "lem_cross_hook_criterion"]
theorem isMixedHook_iff_beta (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hD : Gaps.IsOrderFilter a b D) {q : ℤ × ℤ} (hq : q ∈ cellZ a b D) :
    IsMixedHook a b D E q ↔
      Gaps.beta a b (mixedArm a b D q) ≤ (mixedLeg a b E q : ℤ) ∧
        (mixedLeg a b E q : ℤ) ≤ Gaps.beta a b ((mixedArm a b D q : ℤ) + 1) := by
  have ha0 : 0 < a := by omega
  have hAle := mixedArm_le hco ha hb hD hq
  rw [isMixedHook_iff hb]
  set A := mixedArm a b D q with hA
  set L := mixedLeg a b E q with hL
  have key1 : b * A < a * (L + 1) ↔ (A : ℤ) * b < ((L : ℤ) + 1) * a := by
    constructor
    · intro h
      have h2 : ((b * A : ℕ) : ℤ) < ((a * (L + 1) : ℕ) : ℤ) := by exact_mod_cast h
      push_cast at h2
      linarith
    · intro h
      have h2 : ((b * A : ℕ) : ℤ) < ((a * (L + 1) : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast h2
  have key2 : a * L < b * (A + 1) ↔ (L : ℤ) * a < ((A : ℤ) + 1) * b := by
    constructor
    · intro h
      have h2 : ((a * L : ℕ) : ℤ) < ((b * (A + 1) : ℕ) : ℤ) := by exact_mod_cast h
      push_cast at h2
      linarith
    · intro h
      have h2 : ((a * L : ℕ) : ℤ) < ((b * (A + 1) : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast h2
  have hbeta1 : Gaps.beta a b (A : ℤ) ≤ (L : ℤ) ↔ (A : ℤ) * b < ((L : ℤ) + 1) * a := by
    rw [← not_lt, Int.lt_iff_add_one_le, Gaps.le_beta_iff ha0, not_le]
  have hne : (L : ℤ) * a ≠ ((A : ℤ) + 1) * b := by
    intro heq
    have hdvd : (a : ℤ) ∣ ((A : ℤ) + 1) :=
      (isCoprime_intCast hco).dvd_of_dvd_mul_right ⟨(L : ℤ), by linarith⟩
    exact not_dvd_of_lt (by omega) (by omega) hdvd
  have hbeta2 : (L : ℤ) ≤ Gaps.beta a b ((A : ℤ) + 1) ↔ (L : ℤ) * a < ((A : ℤ) + 1) * b := by
    rw [Gaps.le_beta_iff ha0]
    exact ⟨fun h => lt_of_le_of_ne h hne, le_of_lt⟩
  rw [key1, key2, hbeta1, hbeta2]

end HJO.CrossDinv
