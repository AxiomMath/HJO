/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.CriterionSufficient
public meta import HJO.Attr

/-! # Necessity at every level follows from necessity at the top level

The necessity half of the BGLX vanishing criterion concludes that *every* homogeneous part of a
vanishing combination has vanishing symmetrised symbol. Its proof reaches only the top part
directly; the rest is the descent that closes BGLX's argument, which is Step 7 of the
proof of `HJO.Bglx.criterionNecessary`:

once `Ξ_{c^{(m)}} = 0` is known, **sufficiency** turns it into `V_{c^{(m)}} = 0`, that operator may
be subtracted from the hypothesis, and the induction hypothesis at `m - 1` finishes.

So the whole of necessity is equivalent to its top-level case, and this file proves that
equivalence. What remains to be proved for necessity is then a statement about a *single*
coefficient family rather than a whole graded family, which is the shape BGLX's coefficient
extraction works in.

## Main definitions

* `HJO.Bglx.IsTopSymbolSymVanishing`: the top-level case of necessity — an operator acting by zero
  forces the symmetrised symbol of its *longest* homogeneous part to vanish.

## Main statements

* `HJO.Bglx.criterionNecessary_of_topSymbolSymVanishing`: Step 7 of the proof — the
  descent from the top level to every level.
* `HJO.Bglx.isTopSymbolSymVanishing_iff`: the two predicates are equivalent, so nothing is lost by
  working with the top-level one.

## Implementation notes

The induction is on `m` with the coefficient family `c` quantified inside, because the family the
induction hypothesis is applied to is the *same* family `c`, only with one fewer level summed. That
is why `IsVanishingCriterionNecessary` is unfolded to its `∀ m` form at the start rather than used
as a black box.

Nothing here touches `q` or `u`: the descent uses only sufficiency
(`HJO.Bglx.dopWordOperator_eq_zero_of_symbolSym`), which is a formal identity.

## References

F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic
operators in the theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016)
671--714, Theorem 2.1.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The top-level case of necessity**: if a combination of words of lengths at most `m` acts by
zero on the symmetric functions, then the symmetrised symbol of its part of length exactly `m`
vanishes. This is what BGLX's coefficient extraction proves directly, and by
`HJO.Bglx.criterionNecessary_of_topSymbolSymVanishing` it is all of necessity. -/
def IsTopSymbolSymVanishing (q u : L) : Prop :=
  ∀ (m : ℕ) (c : ∀ k : ℕ, (Fin k → ℕ) →₀ L),
    (∑ k ∈ Finset.range (m + 1), dopWordOperator q u k (c k)) = 0
      → symbolSym q u m (c m) = 0

/-- **Necessity at every level follows from necessity at the top level.** This is Step 7 of the
proof: the top level gives `Ξ_{c^{(m)}} = 0`, sufficiency turns that into
`V_{c^{(m)}} = 0`, subtracting it leaves a vanishing combination of the lower levels, and the
induction hypothesis applies to it. -/
theorem criterionNecessary_of_topSymbolSymVanishing (q u : L) (h : IsTopSymbolSymVanishing q u) :
    IsVanishingCriterionNecessary q u := by
  intro m
  induction m with
  | zero =>
    intro c hsum k hk
    rw [Nat.le_zero.1 hk]
    exact h 0 c hsum
  | succ n ih =>
    intro c hsum k hk
    have htop : symbolSym q u (n + 1) (c (n + 1)) = 0 := h (n + 1) c hsum
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hzero : dopWordOperator q u (n + 1) (c (n + 1)) = 0 :=
        dopWordOperator_eq_zero_of_symbolSym q u (n + 1) (c (n + 1)) htop
      have hlow : ∑ j ∈ Finset.range (n + 1), dopWordOperator q u j (c j) = 0 := by
        rw [Finset.sum_range_succ, hzero, add_zero] at hsum
        exact hsum
      exact ih c hlow k (Nat.lt_succ_iff.1 hlt)
    · rw [Nat.le_antisymm hk hge]
      exact htop

/-- **Necessity is exactly its top-level case.** The forward implication is Step 7; the converse is
immediate, the top level being one of the levels. -/
theorem isTopSymbolSymVanishing_iff (q u : L) :
    IsTopSymbolSymVanishing q u ↔ IsVanishingCriterionNecessary q u :=
  ⟨criterionNecessary_of_topSymbolSymVanishing q u, fun h m c hsum => h m c hsum m le_rfl⟩

end HJO.Bglx
