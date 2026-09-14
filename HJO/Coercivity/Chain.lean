/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Order.Interval.Finset.Nat
public meta import HJO.Attr

/-! # Two counting inputs to the coercivity bound

The coercivity bound on the monotonicity cone is produced by counting, not by a spectral
estimate, and this file isolates the two elementary counting facts it uses.

The first is that a family of nonempty subsets of a finite set `X` that is totally ordered by
inclusion has at most `|X|` members. The proof here is not by a descending enumeration of the
family: cardinality is *injective* on it, because two members with the same
cardinality are comparable and hence equal, and the cardinalities lie in `{1, …, |X|}`.

The second is the Cauchy-Schwarz inequality `|T| ∑_t m_t^2 ≥ (∑_t m_t)^2` for an integer family,
which is Mathlib's `sq_sum_le_card_mul_sum_sq`; only the wrapper is new.
-/

@[expose] public section

open Finset

namespace HJO.Coercivity

/-! ### A chain of nonempty subsets is short -/

/-- **A chain of nonempty subsets is short**: a family `R` of nonempty subsets of a finite set `X`
that is totally ordered by inclusion has at most `|X|` members. -/
@[hjo "lem_chain_length"]
theorem card_le_card_of_chain {α : Type*} {X : Finset α} {R : Finset (Finset α)}
    (hsub : ∀ E ∈ R, E ⊆ X) (hne : ∀ E ∈ R, E.Nonempty)
    (hchain : ∀ E ∈ R, ∀ E' ∈ R, E ⊆ E' ∨ E' ⊆ E) : R.card ≤ X.card := by
  have hle : R.card ≤ (Finset.Icc 1 X.card).card := by
    refine Finset.card_le_card_of_injOn Finset.card (fun E hE => ?_) (fun E hE E' hE' hcard => ?_)
    · exact Finset.mem_Icc.mpr
        ⟨Finset.card_pos.mpr (hne E hE), Finset.card_le_card (hsub E hE)⟩
    · rcases hchain E hE E' hE' with hs | hs
      · exact Finset.eq_of_subset_of_card_le hs hcard.ge
      · exact (Finset.eq_of_subset_of_card_le hs hcard.le).symm
  simpa using hle

/-! ### Cauchy-Schwarz for a finite family of integers -/

/-- **Cauchy-Schwarz for a finite family of integers**: `|T| ∑_t m_t^2 ≥ (∑_t m_t)^2`. -/
@[hjo "lem_square_sum_lower"]
theorem sq_sum_le_card_mul_sum_sq_int {ι : Type*} (T : Finset ι) (m : ι → ℤ) :
    (∑ t ∈ T, m t) ^ 2 ≤ (T.card : ℤ) * ∑ t ∈ T, m t ^ 2 :=
  sq_sum_le_card_mul_sum_sq

end HJO.Coercivity
