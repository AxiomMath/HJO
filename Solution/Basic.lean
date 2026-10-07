/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO

/-! # Satisfying the formal challenge

Each statement of `Challenge/Basic.lean`, restated verbatim under the same name and proved from
this library, with nothing assumed.
-/

@[expose] public section

open Finset HJO PowerSeries
open scoped QTheory PowerSeries.DiscreteTopology

local notation "gaps(" a ", " b ")" => NumericalSemigroup.gaps (NumericalSemigroup.finspan {a, b})

namespace HJO.Challenge

open HJO.Cylindric HJO.Finite

/-- The cylindric partitions with outgoing profile `c` and every entry at most `N` are
summable by volume. A `tsum` is zero by definition when the family is not summable, so
without this `boundedGF` says nothing. -/
theorem summable_boundedGF (a b N : ℕ) (ha : 0 < a) :
    Summable fun l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l ∧ BoundedBy N l} =>
      (X : ℤ⟦X⟧) ^ cylVolume a l.val :=
  HJO.Summable.summable_boundedGF a b N ha

/-- The cylindric partitions with outgoing profile `c` and no bound on their entries are
summable by volume. -/
theorem summable_unboundedGF (a b : ℕ) (ha : 0 < a) :
    Summable fun l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l} =>
      (X : ℤ⟦X⟧) ^ cylVolume a l.val :=
  HJO.Summable.summable_unboundedGF a b ha

/-- The index set of `poly` is finite, so its `finsum` is an honest `Finset` sum. A
`finsum` is zero by definition on infinite support, so without this `poly` says nothing. -/
theorem finite_index (a b N : ℕ) (hco : Nat.Coprime a b) (ha : 1 < a) (hab : a < b) :
    {n : gaps(a, b) → ℕ |
      (fun i => (n i : ℤ)) ∈ cone a b ∧ extendNat n (a * b - a - b) ≤ N}.Finite :=
  HJO.FiniteCanonical.finite_index a b N hco ha hab

/-- **The finite identity.** For coprime `1 < a < b` and every rank `N`, the HJO polynomial is
`(q)_N` times the generating function of the balanced cylindric partitions with largest entry at
most `N`. -/
theorem thm_finite (a b : ℕ) (hco : Nat.Coprime a b) (ha : 1 < a) (hab : a < b) (N : ℕ) :
    HJO.Finite.poly a b N = (X; X)_N * HJO.Cylindric.boundedGF a b N := by
  rw [HJO.FiniteCanonical.poly_eq]
  exact HJO.finiteSeries_eq_qPochhammer_mul_boundedGF hco ha hab N

/-- **The Huang–Jiang–Oblomkov conjecture.** The HJO series equals the HJO product, for every
coprime pair `a, b`. -/
theorem thm_main (a b : ℕ) (hco : Nat.Coprime a b) :
    Conjecture a b :=
  HJO.conjecture hco

end HJO.Challenge

end
