/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CrossDinv.Bilinear
public import HJO.CrossDinv.MixedHook
public import HJO.CrossDinv.Reindex
public import HJO.CrossDinv.Windows
public meta import HJO.Attr

/-! # The cross-dinv identity

Huang's identity: the polarised form at a pair of order filters is the cross-dinv statistic,
`B (1_D, 1_E) = ½ (N_{D,E} + N_{E,D})`, where `N_{D,E}` counts the cells of `𝒟_D ∩ 𝒟_E` whose arm
is measured in the first diagram, whose leg is measured in the second, and whose two mixed hook
slopes straddle `a / b`.

It is `2 B` that is a cardinality, not `B`: the two halves `N_{D,E}` and `N_{E,D}` differ in
general, so `B (1_D, 1_E)` is a genuine half-integer on many pairs. What the coercivity bound
consumes is only `B (1_D, 1_E) ≥ 0`, which follows in one step since `N` is a cardinality.

The argument is the rank-one argument run with two diagrams. The two window counts expand over the
same cross tail counts, the reindexing into the hook-shaped alternating sum is unchanged, and the
bracket at each arm shift `u` -- an inclusion-exclusion between the arm shifts `u`, `u + 1` and the
leg shifts `β u`, `β (u+1) + 1` -- is the number of cells of the intersection whose arm in the
first diagram is exactly `u` and whose leg in the second lies in `[β u, β (u+1)]`. Two facts make
that identification work: the arm and leg sets shrink as their shifts grow, and each family reduces
at shift `0` to the diagram itself, which is why the bracket needs no separate hypothesis confining
it to the intersection.
-/

@[expose] public section

open Finset NumericalSemigroup HJO.RankOneDinv

namespace HJO.CrossDinv

variable {a b : ℕ} {D E : Finset ℕ}

/-! ### Splitting an intersection along a subset -/

/-- An intersection splits along a subset of one of its factors. -/
theorem card_inter_split {α : Type*} [DecidableEq α] {S S' T : Finset α} (hS : S' ⊆ S) :
    #(S ∩ T) = #((S \ S') ∩ T) + #(S' ∩ T) := by
  rw [← Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_inter, mem_sdiff] at hx hx'
    exact hx.1.2 hx'.1)]
  refine congrArg card ?_
  ext x
  have hS' : x ∈ S' → x ∈ S := fun h => hS h
  simp only [mem_union, mem_inter, mem_sdiff]
  tauto

/-- **Inclusion-exclusion in both factors**: the alternating sum of the four intersections is the
intersection of the two differences. -/
theorem card_inter_four {α : Type*} [DecidableEq α] {S S' T T' : Finset α}
    (hS : S' ⊆ S) (hT : T' ⊆ T) :
    (#(S ∩ T) : ℤ) - #(S' ∩ T) - #(S ∩ T') + #(S' ∩ T') = #((S \ S') ∩ (T \ T')) := by
  have h1 := card_inter_split (T := T) hS
  have h2 := card_inter_split (T := T') hS
  have h3 : #((S \ S') ∩ T) = #((S \ S') ∩ (T \ T')) + #((S \ S') ∩ T') := by
    rw [Finset.inter_comm (S \ S') T, Finset.inter_comm (S \ S') (T \ T'),
      Finset.inter_comm (S \ S') T', card_inter_split hT]
  omega

/-! ### The bracket at one arm shift -/

/-- The cells of `𝒟_D ∩ 𝒟_E` whose arm in the first diagram is exactly `u` and whose leg in the
second lies in the staircase window `[β u, β (u+1)]`. -/
noncomputable def crossBracketSet (a b : ℕ) (D E : Finset ℕ) (u : ℤ) : Finset (ℤ × ℤ) :=
  {q ∈ cellZ a b D ∩ cellZ a b E | (mixedArm a b D q : ℤ) = u ∧
    Gaps.beta a b u ≤ (mixedLeg a b E q : ℤ) ∧ (mixedLeg a b E q : ℤ) ≤ Gaps.beta a b (u + 1)}

/-- **The bracket at an arm shift counts the cells with that arm and leg in the window**: the
inclusion-exclusion between the arm shifts `u`, `u + 1` and the leg shifts `β u`, `β (u+1) + 1`
counts the cells of `𝒟_D ∩ 𝒟_E` with `arm_D = u` and `β u ≤ leg_E ≤ β (u+1)`. -/
@[hjo "lem_cross_bracket_count"]
theorem bracket_count (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hD : Gaps.IsOrderFilter a b D) (hE : Gaps.IsOrderFilter a b E) {u : ℤ} (hu : 0 ≤ u) :
    (crossTailCount a b D E u (Gaps.beta a b u) : ℤ)
        - crossTailCount a b D E (u + 1) (Gaps.beta a b u)
        - crossTailCount a b D E u (Gaps.beta a b (u + 1) + 1)
        + crossTailCount a b D E (u + 1) (Gaps.beta a b (u + 1) + 1)
      = #(crossBracketSet a b D E u) := by
  have hv0 : 0 ≤ Gaps.beta a b u := beta_nonneg (by omega) hu
  have hmono : Gaps.beta a b u ≤ Gaps.beta a b (u + 1) := beta_le_succ (by omega) u
  have hAsub : crossArmSet a b D (u + 1) ⊆ crossArmSet a b D u :=
    crossArmSet_succ_subset hco ha hb hD hu
  have hLsub : crossLegSet a b E (Gaps.beta a b (u + 1) + 1)
      ⊆ crossLegSet a b E (Gaps.beta a b u) :=
    crossLegSet_subset hco ha hb hE hv0 (by omega)
  have hset : (crossArmSet a b D u \ crossArmSet a b D (u + 1))
        ∩ (crossLegSet a b E (Gaps.beta a b u) \ crossLegSet a b E (Gaps.beta a b (u + 1) + 1))
      = crossBracketSet a b D E u := by
    ext q
    simp only [crossBracketSet, mem_inter, mem_sdiff, mem_filter]
    constructor
    · rintro ⟨⟨hAu, hAu1⟩, hLv0, hLv1⟩
      have hqD : q ∈ cellZ a b D := by
        have h := crossArmSet_subset hco ha hb hD le_rfl hu hAu
        rwa [crossArmSet_zero] at h
      have hqE : q ∈ cellZ a b E := by
        have h := crossLegSet_subset hco ha hb hE le_rfl hv0 hLv0
        rwa [crossLegSet_zero] at h
      have h1 : u ≤ (mixedArm a b D q : ℤ) := (le_mixedArm_iff hco ha hb hD hqD hu).mpr hAu
      have h2 : ¬ u + 1 ≤ (mixedArm a b D q : ℤ) := fun h =>
        hAu1 ((le_mixedArm_iff hco ha hb hD hqD (by omega)).mp h)
      have h3 : Gaps.beta a b u ≤ (mixedLeg a b E q : ℤ) :=
        (le_mixedLeg_iff hco ha hb hE hqE hv0).mpr hLv0
      have h4 : ¬ Gaps.beta a b (u + 1) + 1 ≤ (mixedLeg a b E q : ℤ) := fun h =>
        hLv1 ((le_mixedLeg_iff hco ha hb hE hqE (by omega)).mp h)
      exact ⟨⟨hqD, hqE⟩, by omega, h3, by omega⟩
    · rintro ⟨⟨hqD, hqE⟩, harm, hleg1, hleg2⟩
      refine ⟨⟨(le_mixedArm_iff hco ha hb hD hqD hu).mp (by omega), fun h => ?_⟩,
        (le_mixedLeg_iff hco ha hb hE hqE hv0).mp hleg1, fun h => ?_⟩
      · have h5 := (le_mixedArm_iff hco ha hb hD hqD (by omega : (0 : ℤ) ≤ u + 1)).mpr h
        omega
      · have h5 := (le_mixedLeg_iff hco ha hb hE hqE
          (by omega : (0 : ℤ) ≤ Gaps.beta a b (u + 1) + 1)).mpr h
        omega
  rw [crossTailCount_eq_card_inter, crossTailCount_eq_card_inter, crossTailCount_eq_card_inter,
    crossTailCount_eq_card_inter, card_inter_four hAsub hLsub, hset]

/-! ### The cross-dinv statistic -/

/-- **The asymmetric cross-dinv count** `N_{D,E}`: the number of cells of `𝒟_D ∩ 𝒟_E` whose mixed
hook slopes straddle `a / b`, the arm being measured in `𝒟_D` and the leg in `𝒟_E`. -/
@[hjo "def_cross_dinv_asym"]
noncomputable def crossDinvAsym (a b : ℕ) (D E : Finset ℕ) : ℕ :=
  #{q ∈ cellZ a b D ∩ cellZ a b E | q ∈ mixedHookSet a b D E}

/-- **The cross-dinv statistic** `dinv_× (D, E) = ½ (N_{D,E} + N_{E,D})`, a half-integer: the two
halves differ in general, so the value is genuinely rational. -/
@[hjo "def_cross_dinv"]
noncomputable def crossDinv (a b : ℕ) (D E : Finset ℕ) : ℚ :=
  ((crossDinvAsym a b D E : ℚ) + (crossDinvAsym a b E D : ℚ)) / 2

/-- **The asymmetric cross-dinv count splits over the arm**: `N_{D,E}` is the sum over
`0 ≤ u ≤ a - 2` of the number of cells with `arm_D = u` and `β u ≤ leg_E ≤ β (u+1)`. -/
@[hjo "lem_cross_dinv_asym_partition"]
theorem crossDinvAsym_eq_sum (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hD : Gaps.IsOrderFilter a b D) (_hE : Gaps.IsOrderFilter a b E) :
    crossDinvAsym a b D E
      = ∑ u ∈ Finset.Icc (0 : ℤ) ((a : ℤ) - 2), #(crossBracketSet a b D E u) := by
  have hmaps : Set.MapsTo (fun q : ℤ × ℤ => (mixedArm a b D q : ℤ))
      ↑{q ∈ cellZ a b D ∩ cellZ a b E | q ∈ mixedHookSet a b D E}
      ↑(Finset.Icc (0 : ℤ) ((a : ℤ) - 2)) := by
    intro q hq
    simp only [Finset.mem_coe, mem_filter, mem_inter] at hq
    simp only [Finset.mem_coe, mem_Icc]
    exact ⟨by positivity, mixedArm_le hco ha hb hD hq.1.1⟩
  rw [crossDinvAsym, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun u hu => congrArg card ?_
  ext q
  simp only [crossBracketSet, mem_filter, mem_inter]
  constructor
  · rintro ⟨⟨⟨hqD, hqE⟩, hhook⟩, harm⟩
    have harm' : (mixedArm a b D q : ℤ) = u := harm
    rw [mem_mixedHookSet, isMixedHook_iff_beta hco ha hb hD hqD, harm'] at hhook
    exact ⟨⟨hqD, hqE⟩, harm, hhook.1, hhook.2⟩
  · rintro ⟨⟨hqD, hqE⟩, harm, h1, h2⟩
    have harm' : (mixedArm a b D q : ℤ) = u := harm
    refine ⟨⟨⟨hqD, hqE⟩, ?_⟩, harm⟩
    rw [mem_mixedHookSet, isMixedHook_iff_beta hco ha hb hD hqD, harm']
    exact ⟨h1, h2⟩

/-! ### The identity -/

/-- **The cross-dinv identity**: `2 B (1_D, 1_E) = N_{D,E} + N_{E,D}`. -/
@[hjo "lem_cross_dinv_identity"]
theorem two_mul_bilin_eq (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    (hD : Gaps.IsOrderFilter a b D) (hE : Gaps.IsOrderFilter a b E) :
    2 * HJO.Defs.bilin (finspan {a, b}).gaps a b (fun g => if (g : ℕ) ∈ D then 1 else 0)
        (fun h => if (h : ℕ) ∈ E then 1 else 0)
      = (crossDinvAsym a b D E : ℚ) + (crossDinvAsym a b E D : ℚ) := by
  have hb : 0 < b := by omega
  set φ : ℤ → ℤ → ℤ :=
    fun u v => (crossTailCount a b D E u v : ℤ) + (crossTailCount a b E D u v : ℤ) with hφdef
  have hzero : ∀ u v : ℤ, (a : ℤ) - 1 ≤ u → φ u v = 0 := by
    intro u v hu
    have habs : (a : ℤ) - 1 ≤ |u| := by
      rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ u)]
      exact hu
    simp only [hφdef, crossTailCount_eq_zero habs, Nat.cast_zero, add_zero]
  have hcomb1 : (∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2),
          ((crossTailCount a b D E u (Gaps.beta a b u) : ℤ)
            + (crossTailCount a b E D u (Gaps.beta a b u + 1) : ℤ)))
        + (∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2),
          ((crossTailCount a b E D u (Gaps.beta a b u) : ℤ)
            + (crossTailCount a b D E u (Gaps.beta a b u + 1) : ℤ)))
      = ∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2),
          (φ u (Gaps.beta a b u) + φ u (Gaps.beta a b u + 1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by simp only [hφdef]; ring
  have hcomb2 : (∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2),
          ((crossTailCount a b D E u (Gaps.beta a b (u - 1)) : ℤ)
            + (crossTailCount a b E D u (Gaps.beta a b (u + 1) + 1) : ℤ)))
        + (∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2),
          ((crossTailCount a b E D u (Gaps.beta a b (u - 1)) : ℤ)
            + (crossTailCount a b D E u (Gaps.beta a b (u + 1) + 1) : ℤ)))
      = ∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2),
          (φ u (Gaps.beta a b (u - 1)) + φ u (Gaps.beta a b (u + 1) + 1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by simp only [hφdef]; ring
  have hint : ((#{p ∈ D ×ˢ E | 0 ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < a} : ℤ)
        + #{p ∈ E ×ˢ D | 0 ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < a}
        - #{p ∈ D ×ˢ E | (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b}
        - #{p ∈ E ×ˢ D | (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b})
      = (crossDinvAsym a b D E : ℤ) + (crossDinvAsym a b E D : ℤ) := by
    calc ((#{p ∈ D ×ˢ E | 0 ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < a} : ℤ)
          + #{p ∈ E ×ˢ D | 0 ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < a}
          - #{p ∈ D ×ˢ E | (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b}
          - #{p ∈ E ×ˢ D | (b : ℤ) ≤ (p.2 : ℤ) - p.1 ∧ (p.2 : ℤ) - p.1 < (a : ℤ) + b})
        = (φ 0 0 + ∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2),
              (φ u (Gaps.beta a b u) + φ u (Gaps.beta a b u + 1)))
            - (φ 0 (Gaps.beta a b 1 + 1) + ∑ u ∈ Finset.Icc (1 : ℤ) ((a : ℤ) - 2),
              (φ u (Gaps.beta a b (u - 1)) + φ u (Gaps.beta a b (u + 1) + 1))) := by
          rw [card_window_zero hco ha hD.1 hE.1, card_window_zero hco ha hE.1 hD.1,
            card_window_b hco ha hD.1 hE.1, card_window_b hco ha hE.1 hD.1]
          push_cast
          rw [← hcomb1, ← hcomb2]
          simp only [hφdef]
          ring
      _ = ∑ u ∈ Finset.Icc (0 : ℤ) ((a : ℤ) - 2),
            (φ u (Gaps.beta a b u) - φ (u + 1) (Gaps.beta a b u)
              - φ u (Gaps.beta a b (u + 1) + 1) + φ (u + 1) (Gaps.beta a b (u + 1) + 1)) :=
          sum_bracket_eq ha φ hzero
      _ = ∑ u ∈ Finset.Icc (0 : ℤ) ((a : ℤ) - 2),
            ((#(crossBracketSet a b D E u) : ℤ) + (#(crossBracketSet a b E D u) : ℤ)) :=
          Finset.sum_congr rfl fun u hu => by
            simp only [mem_Icc] at hu
            have h1 := bracket_count hco ha hb hD hE hu.1
            have h2 := bracket_count hco ha hb hE hD hu.1
            simp only [hφdef]
            linarith
      _ = (crossDinvAsym a b D E : ℤ) + (crossDinvAsym a b E D : ℤ) := by
          rw [crossDinvAsym_eq_sum hco ha hb hD hE, crossDinvAsym_eq_sum hco ha hb hE hD]
          push_cast
          rw [Finset.sum_add_distrib]
  rw [two_mul_bilin_indicator hab hD.1 hE.1, hint]
  push_cast
  ring

/-- **The polarised form is the cross-dinv statistic**:
`B (1_D, 1_E) = dinv_× (D, E)`. -/
@[hjo "lem_cross_dinv_eq"]
theorem bilin_eq_crossDinv (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    (hD : Gaps.IsOrderFilter a b D) (hE : Gaps.IsOrderFilter a b E) :
    HJO.Defs.bilin (finspan {a, b}).gaps a b (fun g => if (g : ℕ) ∈ D then 1 else 0)
        (fun h => if (h : ℕ) ∈ E then 1 else 0)
      = crossDinv a b D E := by
  have h := two_mul_bilin_eq hco ha hab hD hE
  rw [crossDinv]
  linarith

/-- **The polarised form is nonnegative at a pair of indicators**, the inequality the coercivity
bound consumes: it is half a cardinality. -/
@[hjo "lem_cross_dinv_nonneg"]
theorem bilin_nonneg (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    (hD : Gaps.IsOrderFilter a b D) (hE : Gaps.IsOrderFilter a b E) :
    0 ≤ HJO.Defs.bilin (finspan {a, b}).gaps a b (fun g => if (g : ℕ) ∈ D then 1 else 0)
        (fun h => if (h : ℕ) ∈ E then 1 else 0) := by
  rw [bilin_eq_crossDinv hco ha hab hD hE, crossDinv]
  positivity

end HJO.CrossDinv
