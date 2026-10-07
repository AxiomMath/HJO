/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Coercivity.Bilinear
public import HJO.Coercivity.Layers
public import HJO.Coercivity.RankOne
public import HJO.CrossDinv.Identity
public import HJO.Discharged.External
public meta import HJO.Attr

/-! # The quadratic form dominates the sum of the squared layer multiplicities

This is the arithmetic core of coercivity on the monotonicity cone. A cone vector `𝐧` is the
integer combination `∑_E m_E(𝐧) 𝟙_E` of the indicators of its layers, so expanding the quadratic
form along that decomposition gives

`Q(𝐧) = ∑_E ∑_{E'} m_E(𝐧) m_{E'}(𝐧) B(𝟙_E, 𝟙_{E'})`,

and then two facts about the individual terms finish it. Every term is nonnegative, because a
subset with a positive multiplicity is a layer and hence an order filter, and the polarised form is
nonnegative on a pair of order filters; so discarding the off-diagonal terms only decreases the
value. And each diagonal term is at least `m_E(𝐧)^2`, because `B(𝟙_E, 𝟙_E) = Q(𝟙_E) ≥ 1` for a
nonempty order filter `E`.

Two inputs come from outside this subtree, and both are proved in this library rather than
assumed: Huang's rank-one identity, as `HJO.ExternalDischarged.rankOneDinv` from the rank-one
subtree, and the nonnegativity of the polarised form on a pair of order filters, as
`HJO.CrossDinv.bilin_nonneg` from the cross-dinv identity. So the bound below is unconditional —
it assumes nothing, quoted or otherwise.

The layers live in the gap *type* and `HJO.Gaps.IsOrderFilter` is stated for subsets of `ℕ`, so
`indicator_image` converts between the two readings of an indicator vector; it is an identity of
functions, not a bridge between two notions.
-/

@[expose] public section

open Finset NumericalSemigroup

namespace HJO.Coercivity

variable {a b : ℕ}

/-- The indicator of a subset of the gap type, read through the subset's image in `ℕ`, is the same
vector as the indicator read directly. -/
theorem indicator_image (E : Finset (finspan {a, b}).gaps) :
    (fun g : (finspan {a, b}).gaps =>
        if (g : ℕ) ∈ E.image (fun h : (finspan {a, b}).gaps => (h : ℕ)) then (1 : ℤ) else 0)
      = fun g => if g ∈ E then 1 else 0 := by
  funext g
  have hiff : ((g : ℕ) ∈ E.image (fun h : (finspan {a, b}).gaps => (h : ℕ))) ↔ g ∈ E := by
    simp only [Finset.mem_image]
    refine ⟨fun h => ?_, fun h => ⟨g, h, rfl⟩⟩
    obtain ⟨i, hi, hig⟩ := h
    exact Subtype.ext hig ▸ hi
  simp only [hiff]

/-! ### The expansion along the layers -/

/-- **Expansion along the layers**:
`Q(𝐧) = ∑_E ∑_{E'} m_E(𝐧) m_{E'}(𝐧) B(𝟙_E, 𝟙_{E'})` for every `𝐧` in the monotonicity cone. The
polarised form is rational valued, so the integer value of the quadratic form is cast into `ℚ`. -/
@[hjo "lem_quadratic_layer_expansion"]
theorem q_eq_sum_sum_layerMult (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    {n : (finspan {a, b}).gaps → ℤ} (hn : n ∈ HJO.cone a b) :
    ((HJO.Q a b n : ℤ) : ℚ)
      = ∑ E : Finset (finspan {a, b}).gaps, ∑ E' : Finset (finspan {a, b}).gaps,
          ((Defs.layerMult a b n E * Defs.layerMult a b n E' : ℤ) : ℚ) *
            Defs.bilin ((finspan {a, b}).gaps) a b (fun g => if g ∈ E then 1 else 0)
              (fun g => if g ∈ E' then 1 else 0) := by
  have harg : (fun g : (finspan {a, b}).gaps =>
        ∑ E : Finset (finspan {a, b}).gaps,
          (Defs.layerMult a b n E : ℤ) * (if g ∈ E then 1 else 0)) = n :=
    funext fun g => sum_layerMult_mul_indicator hco ha hab hn g
  have h := q_sum_eq_sum_sum_bilin a b (Finset.univ : Finset (Finset (finspan {a, b}).gaps))
    (fun E => (Defs.layerMult a b n E : ℤ)) (fun E g => if g ∈ E then (1 : ℤ) else 0)
  rw [harg] at h
  exact h

/-! ### Discarding the cross terms -/

/-- **Discarding the cross terms**: `Q(𝐧) ≥ ∑_E m_E(𝐧)^2` for every `𝐧` in the monotonicity cone.

Unconditional. Both results it rests on are proved in this library rather than assumed: Huang's
rank-one identity is `HJO.ExternalDischarged.rankOneDinv`, and the nonnegativity of the polarised
form on a pair of order filters is `HJO.CrossDinv.bilin_nonneg`, from the cross-dinv identity. -/
@[hjo "lem_quadratic_ge_multiplicity_squares"]
theorem sum_layerMult_sq_le_q
    (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) {n : (finspan {a, b}).gaps → ℤ}
    (hn : n ∈ HJO.cone a b) :
    (∑ E : Finset (finspan {a, b}).gaps, (Defs.layerMult a b n E : ℤ) ^ 2) ≤ HJO.Q a b n := by
  -- a subset with a positive multiplicity is a nonempty order filter
  have hfilt : ∀ E : Finset (finspan {a, b}).gaps, 1 ≤ Defs.layerMult a b n E →
      Gaps.IsOrderFilter a b (E.image (fun h : (finspan {a, b}).gaps => (h : ℕ)))
        ∧ (E.image (fun h : (finspan {a, b}).gaps => (h : ℕ))).Nonempty := by
    intro E hE
    obtain ⟨t, ht, rfl⟩ := exists_layer_eq hE
    refine ⟨isOrderFilter_layer hco hn t, ?_⟩
    exact ⟨_, Finset.mem_image_of_mem (fun h : (finspan {a, b}).gaps => (h : ℕ))
      (frobeniusGap_mem_layer hco ha hab n (Finset.mem_Icc.mp ht).2)⟩
  -- every term of the double sum is nonnegative
  have hterm : ∀ E E' : Finset (finspan {a, b}).gaps,
      0 ≤ ((Defs.layerMult a b n E * Defs.layerMult a b n E' : ℤ) : ℚ) *
        Defs.bilin ((finspan {a, b}).gaps) a b (fun g => if g ∈ E then 1 else 0)
          (fun g => if g ∈ E' then 1 else 0) := by
    intro E E'
    rcases Nat.eq_zero_or_pos (Defs.layerMult a b n E) with h | h
    · simp [h]
    rcases Nat.eq_zero_or_pos (Defs.layerMult a b n E') with h' | h'
    · simp [h']
    refine mul_nonneg (by positivity) ?_
    rw [← indicator_image E, ← indicator_image E']
    exact CrossDinv.bilin_nonneg hco ha hab (hfilt E h).1 (hfilt E' h').1
  -- each diagonal term is at least the squared multiplicity
  have hdiag : ∀ E : Finset (finspan {a, b}).gaps,
      ((Defs.layerMult a b n E : ℤ) : ℚ) ^ 2 ≤
        ((Defs.layerMult a b n E * Defs.layerMult a b n E : ℤ) : ℚ) *
          Defs.bilin ((finspan {a, b}).gaps) a b (fun g => if g ∈ E then 1 else 0)
            (fun g => if g ∈ E then 1 else 0) := by
    intro E
    rcases Nat.eq_zero_or_pos (Defs.layerMult a b n E) with h | h
    · simp [h]
    have hQ1 := one_le_q_indicator ExternalDischarged.rankOneDinv hco ha hab
      (hfilt E h).1 (hfilt E h).2
    rw [indicator_image E] at hQ1
    have hB : (1 : ℚ) ≤ Defs.bilin ((finspan {a, b}).gaps) a b
        (fun g => if g ∈ E then 1 else 0) (fun g => if g ∈ E then 1 else 0) := by
      rw [bilin_self]
      exact_mod_cast hQ1
    calc ((Defs.layerMult a b n E : ℤ) : ℚ) ^ 2
        = ((Defs.layerMult a b n E : ℤ) : ℚ) ^ 2 * 1 := by ring
      _ ≤ ((Defs.layerMult a b n E : ℤ) : ℚ) ^ 2 *
            Defs.bilin ((finspan {a, b}).gaps) a b (fun g => if g ∈ E then 1 else 0)
              (fun g => if g ∈ E then 1 else 0) :=
          mul_le_mul_of_nonneg_left hB (sq_nonneg _)
      _ = _ := by push_cast; ring
  have hmain : (∑ E : Finset (finspan {a, b}).gaps, ((Defs.layerMult a b n E : ℤ) : ℚ) ^ 2)
      ≤ ((HJO.Q a b n : ℤ) : ℚ) := by
    rw [q_eq_sum_sum_layerMult hco ha hab hn]
    refine Finset.sum_le_sum fun E _ => ?_
    exact (hdiag E).trans (Finset.single_le_sum (fun E' _ => hterm E E') (Finset.mem_univ E))
  exact_mod_cast hmain

end HJO.Coercivity
