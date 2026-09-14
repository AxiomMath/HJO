/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Coercivity.Chain
public import HJO.GoodTraverse.Basic
public meta import HJO.Attr

/-! # The layers of a cone vector and their multiplicities

A point `𝐧` of the monotonicity cone is recovered from its layers
`D_t(𝐧) = HJO.Defs.layer n t = {g ∈ G | n_g ≥ t}`, and this file proves the four structural facts
about them and the three counting facts about their multiplicities
`m_E(𝐧) = HJO.Defs.layerMult a b n E` that the coercivity bound consumes.

The structure: a layer is an order filter, because the cone condition propagates the defining
inequality upwards; the layers are nested, because the defining inequality weakens as the level
drops; and the Frobenius gap lies in every layer at a level below `n_f`, so every layer that occurs
is nonempty.

The counting is all one lemma, `sum_layerMult_mul_ite`: for any predicate `P` on subsets of `G`,
`∑_E m_E(𝐧) 1_{P(E)}` counts the levels `1 ≤ t ≤ n_f` whose layer satisfies `P`, because the level
sets of `t ↦ D_t(𝐧)` partition those levels. Taking `P` always true gives
`∑_E m_E(𝐧) = n_f`; taking `P E` to be `g ∈ E` gives the layer decomposition
`∑_E m_E(𝐧) (𝟙_E)_g = n_g`, which is what exhibits `𝐧` as an integer combination of indicators.

The multiplicities are `ℕ`-valued and the coordinates are `ℤ`-valued, so the two counting
identities are stated with the multiplicities cast into `ℤ`. The support bound is
`card_le_card_of_chain` applied to the layers that occur: nonempty subsets of `G`, totally ordered
by inclusion.
-/

@[expose] public section

open Finset NumericalSemigroup

namespace HJO.Coercivity

variable {a b : ℕ}

/-! ### The structure of the layers -/

/-- **The layers are nested**: the layer at a higher level is contained in the layer at a lower
one. -/
@[hjo "lem_layer_nested"]
theorem layer_subset_layer {ι α : Type*} [Fintype ι] [Preorder α] [DecidableLE α] (n : ι → α)
    {s t : α} (hst : s ≤ t) : Defs.layer n t ⊆ Defs.layer n s := fun _ hi =>
  Defs.mem_layer.mpr (hst.trans (Defs.mem_layer.mp hi))

/-- **The Frobenius gap lies in every relevant layer**: at any level at most `n_f` the layer
contains the Frobenius gap, so every layer occurring in the multiplicity count is nonempty. -/
@[hjo "lem_layer_nonempty"]
theorem frobeniusGap_mem_layer (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    (n : (finspan {a, b}).gaps → ℤ) {t : ℤ}
    (ht : t ≤ HJO.extend n (Gaps.frobeniusGap a b)) :
    (⟨Gaps.frobeniusGap a b, (GapPoset.frobeniusGap_max a b hco ha hab).1⟩ :
        (finspan {a, b}).gaps) ∈ Defs.layer n t := by
  rw [Defs.mem_layer]
  rwa [HJO.extend_of_mem (GapPoset.frobeniusGap_max a b hco ha hab).1] at ht

/-- On the monotonicity cone the zero-extension of a cone vector is nonnegative at every natural
number, a gap or not. -/
theorem extend_nonneg {n : (finspan {a, b}).gaps → ℤ} (hn : n ∈ HJO.cone a b) (i : ℕ) :
    0 ≤ HJO.extend n i := by
  by_cases h : i ∈ (finspan {a, b}).gaps
  · rw [HJO.extend_of_mem h]
    exact hn.1 _
  · rw [HJO.extend_of_not_mem h]

/-- **The layers are order filters**: for `𝐧` in the monotonicity cone every layer of `𝐧` is an
order filter of the gap set. The layer is a subset of the gap *type*, so the statement is about its
image in `ℕ`, which is the shape `HJO.Gaps.IsOrderFilter` is stated at. -/
@[hjo "lem_layer_is_filter"]
theorem isOrderFilter_layer (hco : a.Coprime b) {n : (finspan {a, b}).gaps → ℤ}
    (hn : n ∈ HJO.cone a b) (t : ℤ) :
    Gaps.IsOrderFilter a b ((Defs.layer n t).image
      (fun g : (finspan {a, b}).gaps => (g : ℕ))) := by
  rw [Gaps.cone_eq a b hco] at hn
  refine ⟨fun g hg => ?_, fun g hg h hh hgh => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hg
    exact i.2
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    refine Finset.mem_image.mpr ⟨⟨h, hh⟩, Defs.mem_layer.mpr ?_, rfl⟩
    exact (Defs.mem_layer.mp hi).trans (hn.2 i ⟨h, hh⟩ hgh)

/-- A subset of the gap type with a positive multiplicity really is a layer, at some level between
`1` and `n_f`. -/
theorem exists_layer_eq {n : (finspan {a, b}).gaps → ℤ} {E : Finset (finspan {a, b}).gaps}
    (hE : 1 ≤ Defs.layerMult a b n E) :
    ∃ t ∈ Finset.Icc 1 (HJO.extend n (Gaps.frobeniusGap a b)), Defs.layer n t = E := by
  rw [Defs.layerMult] at hE
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hE
  exact ⟨t, (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2⟩

/-! ### Counting the levels -/

/-- **The multiplicities count levels**: for any predicate `P` on subsets of the gap type, the
multiplicities of the subsets satisfying `P` add up to the number of levels `1 ≤ t ≤ n_f` whose
layer satisfies `P`. Both counting identities below are instances of this, since the level sets of
`t ↦ D_t(𝐧)` partition the range of levels. -/
theorem sum_layerMult_mul_ite (n : (finspan {a, b}).gaps → ℤ)
    (P : Finset (finspan {a, b}).gaps → Prop) [DecidablePred P] :
    (∑ E : Finset (finspan {a, b}).gaps, Defs.layerMult a b n E * (if P E then 1 else 0))
      = #{t ∈ Finset.Icc 1 (HJO.extend n (Gaps.frobeniusGap a b)) | P (Defs.layer n t)} := by
  have hmaps : ∀ t ∈ {t ∈ Finset.Icc 1 (HJO.extend n (Gaps.frobeniusGap a b)) |
      P (Defs.layer n t)}, Defs.layer n t ∈ Finset.univ.filter P := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp ht).2
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_filter]
  refine Finset.sum_congr rfl fun E _ => ?_
  by_cases hP : P E
  · simp only [hP, ite_true, mul_one, Finset.filter_filter, Defs.layerMult]
    refine congrArg Finset.card (Finset.filter_congr fun t _ => ?_)
    exact ⟨fun h => ⟨by rw [h]; exact hP, h⟩, fun h => h.2⟩
  · simp only [hP, ite_false, mul_zero]

/-- **The multiplicities sum to the Frobenius coordinate**: `∑_E m_E(𝐧) = n_f`. -/
@[hjo "lem_layer_multiplicity_total"]
theorem sum_layerMult {n : (finspan {a, b}).gaps → ℤ} (hn : n ∈ HJO.cone a b) :
    (∑ E : Finset (finspan {a, b}).gaps, (Defs.layerMult a b n E : ℤ))
      = HJO.extend n (Gaps.frobeniusGap a b) := by
  have hnf := extend_nonneg hn (Gaps.frobeniusGap a b)
  have h := sum_layerMult_mul_ite n fun _ => True
  simp only [ite_true, mul_one, Finset.filter_true] at h
  have hcast : ((∑ E : Finset (finspan {a, b}).gaps, Defs.layerMult a b n E : ℕ) : ℤ)
      = HJO.extend n (Gaps.frobeniusGap a b) := by
    rw [h, Int.card_Icc]
    omega
  push_cast at hcast
  exact hcast

/-- **The layer decomposition**: `∑_E m_E(𝐧) (𝟙_E)_g = n_g` at every gap `g`. This is what exhibits
a cone vector as an integer combination of the indicators of its layers. -/
@[hjo "lem_layer_multiplicity_decomposition"]
theorem sum_layerMult_mul_indicator (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    {n : (finspan {a, b}).gaps → ℤ} (hn : n ∈ HJO.cone a b) (g : (finspan {a, b}).gaps) :
    (∑ E : Finset (finspan {a, b}).gaps,
        (Defs.layerMult a b n E : ℤ) * (if g ∈ E then 1 else 0)) = n g := by
  have hgnf : n g ≤ HJO.extend n (Gaps.frobeniusGap a b) := by
    have h1 := GoodTraverse.extend_le_frobenius hco ha hab hn g.2
    rwa [← HJO.extend_subtype n g] at h1
  have hg0 : 0 ≤ n g := hn.1 g
  have h := sum_layerMult_mul_ite n fun E => g ∈ E
  have hfil : {t ∈ Finset.Icc 1 (HJO.extend n (Gaps.frobeniusGap a b)) | g ∈ Defs.layer n t}
      = Finset.Icc 1 (n g) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc, Defs.mem_layer]
    omega
  rw [hfil, Int.card_Icc] at h
  have hcast : ((∑ E : Finset (finspan {a, b}).gaps,
      Defs.layerMult a b n E * (if g ∈ E then 1 else 0) : ℕ) : ℤ) = n g := by
    rw [h]
    omega
  push_cast at hcast
  exact hcast

/-! ### At most `|G|` layers occur -/

/-- **There are at most `|G|` distinct layers**: the subsets of the gap set with a positive
multiplicity number at most `|G|`, because they form a chain of nonempty subsets of `G`. This is the
only source of the constant in the coercivity bound. -/
@[hjo "lem_layer_multiplicity_support"]
theorem card_filter_one_le_layerMult_le (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    (n : (finspan {a, b}).gaps → ℤ) :
    #{E : Finset (finspan {a, b}).gaps | 1 ≤ Defs.layerMult a b n E}
      ≤ (finspan {a, b}).gaps.card := by
  have hcard : (Finset.univ : Finset (finspan {a, b}).gaps).card = (finspan {a, b}).gaps.card := by
    rw [Finset.card_univ, Fintype.card_coe]
  rw [← hcard]
  refine card_le_card_of_chain (X := Finset.univ) (fun E _ => Finset.subset_univ E)
    (fun E hE => ?_) (fun E hE E' hE' => ?_)
  · obtain ⟨t, ht, rfl⟩ := exists_layer_eq (Finset.mem_filter.mp hE).2
    exact ⟨_, frobeniusGap_mem_layer hco ha hab n (Finset.mem_Icc.mp ht).2⟩
  · obtain ⟨s, hs, rfl⟩ := exists_layer_eq (Finset.mem_filter.mp hE).2
    obtain ⟨t, ht, rfl⟩ := exists_layer_eq (Finset.mem_filter.mp hE').2
    rcases le_total s t with h | h
    · exact Or.inr (layer_subset_layer n h)
    · exact Or.inl (layer_subset_layer n h)

end HJO.Coercivity
