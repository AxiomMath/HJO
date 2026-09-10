/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The order filtration at `u = 1`

An endomorphism of differential order at most zero is multiplication by a symmetric function,
and at `u = 1` only the constant coefficient of the expansion of an element of the order
filtration survives: such an operator multiplies every symmetric function by its value on `1`.
-/

@[expose] public section

open Finset

namespace HJO.ReesSpecial

open HJO.Sym

/-- The operators of differential order at most zero are exactly the multiplication operators:
the spanning set of order zero already consists of these, and they form a submodule. -/
lemma exists_mulLeft_of_hasDiffOrderAtMost_zero {K : Type*} [CommRing K]
    {P : Module.End K (Lambda K)} (hP : HasDiffOrderAtMost 0 P) :
    ∃ g : Lambda K, P = LinearMap.mulLeft K g := by
  have hmem : P ∈ LinearMap.range (LinearMap.mul K (Lambda K)) := by
    refine Submodule.span_le.mpr ?_ hP
    rintro Q ⟨f, l, hl, rfl⟩
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    simp only [SetLike.mem_coe, LinearMap.mem_range]
    exact ⟨f, by ext x; simp⟩
  obtain ⟨g, hg⟩ := hmem
  refine ⟨g, ?_⟩
  ext x
  rw [← hg]
  simp

/-- At `u = 1` an element of the order filtration is multiplication by its value on `1`: the
terms of its expansion in `1 - u` with positive index vanish, and the constant coefficient has
differential order zero, hence is a multiplication operator. -/
@[hjo "lem_rees_special"]
theorem eq_mulLeft_of_mem_Rees {L : Type*} [Field L] {u : L} (hu : u = 1)
    {P : Module.End L (Lambda L)} (hP : P ∈ Rees u) :
    P = LinearMap.mulLeft L (P 1) := by
  subst hu
  obtain ⟨Q, hQord, hQsum⟩ := hP
  obtain ⟨g, hg⟩ := exists_mulLeft_of_hasDiffOrderAtMost_zero (hQord 0)
  have key : ∀ f : Lambda L, P f = g * f := by
    intro f
    obtain ⟨N, hN, hPf⟩ := hQsum f
    have h0 : P f = Q 0 f := by
      rcases N with _ | M
      · rw [hPf]
        simp [hN 0 le_rfl]
      · rw [hPf, Finset.sum_range_succ']
        simp
    rw [h0, hg]
    simp
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.mulLeft_apply, key f, key 1, mul_one]

/-- The pointwise form of the specialisation: at `u = 1` an element of the order filtration
sends every symmetric function `f` to `P 1 * f`. -/
lemma apply_eq_mul_of_mem_Rees {L : Type*} [Field L] {u : L} (hu : u = 1)
    {P : Module.End L (Lambda L)} (hP : P ∈ Rees u) (f : Lambda L) :
    P f = P 1 * f := by
  conv_lhs => rw [eq_mulLeft_of_mem_Rees hu hP]
  simp

end HJO.ReesSpecial
