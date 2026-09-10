/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO

/-! # The solution half of the comparator pair

The challenge file grants the eight results quoted from the literature and asks for the finite
identity and the conjecture, with the paper's own contribution assumed nowhere. Each statement it
leaves open is restated here verbatim, under the same fully-qualified name, and proved from the
development. The eight hypotheses are exactly those the challenge grants; nothing further is
assumed.

This file cannot import the challenge file. Both name the same constants, so the two sets of
declarations collide -- which is the evidence that the pair speaks one vocabulary.
-/

@[expose] public section

open Finset HJO PowerSeries
open scoped QTheory PowerSeries.DiscreteTopology

local notation "gaps(" a ", " b ")" => NumericalSemigroup.gaps (NumericalSemigroup.finspan {a, b})

namespace HJO.Cylindric

open PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

/-- `C_{c,≤N}(q)` is a genuine sum. A `tsum` is zero by definition when the family is not
summable, so without this the statements above say nothing. -/
theorem summable_boundedGF (a b N : ℕ) (ha : 0 < a) :
    Summable fun l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l ∧ BoundedBy N l} =>
      (X : ℤ⟦X⟧) ^ cylVolume a l.val :=
  HJO.Summable.summable_boundedGF a b N ha

/-- `C_c(q)` is a genuine sum, for the same reason. -/
theorem summable_unboundedGF (a b : ℕ) (ha : 0 < a) :
    Summable fun l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l} =>
      (X : ℤ⟦X⟧) ^ cylVolume a l.val :=
  HJO.Summable.summable_unboundedGF a b ha

end HJO.Cylindric

namespace HJO.Finite

open PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

/-- The index set of `poly` is finite, so its `finsum` is an honest `Finset` sum. A
`finsum` is zero by definition on infinite support, so without this `poly` says nothing. -/
theorem finite_index (a b N : ℕ) (hco : Nat.Coprime a b) (ha : 1 < a) (hab : a < b) :
    {n : gaps(a, b) → ℕ |
      (fun i => (n i : ℤ)) ∈ cone a b ∧ extendNat n (a * b - a - b) ≤ N}.Finite :=
  HJO.FiniteCanonical.finite_index a b N hco ha hab

end HJO.Finite

namespace HJO.Challenge

open HJO.External HJO.Literature HJO.PhiMul

/-- **The finite identity.** For coprime `1 < a < b` and every rank `N`, the HJO polynomial is
`(q)_N` times the generating function of the balanced cylindric partitions with largest entry at
most `N`. -/
theorem thm_finite
    (rankOne : RankOneDinv)
    (goodTraverse : GoodTraverse)
    (coercivity : HuangCoercivity)
    (collinear : CollinearCommutation Witness.Base)
    (shuffle : Shuffle Witness.Base)
    (epsilonGessel : EpsilonGessel Witness.Base)
    (creationExpansion : CreationExpansion Witness.Base)
    (a b : ℕ) (hco : Nat.Coprime a b) (ha : 1 < a) (hab : a < b) (N : ℕ) :
    HJO.Finite.poly a b N = (X; X)_N * HJO.Cylindric.boundedGF a b N :=
  by
    rw [HJO.FiniteCanonical.poly_eq]
    exact HJO.Final.finiteSeries_eq_qPochhammer_mul_boundedGF rankOne goodTraverse coercivity
      collinear shuffle epsilonGessel creationExpansion hco ha hab N

/-- **The Huang–Jiang–Oblomkov conjecture.** The HJO series equals the HJO product, for every
coprime `1 < a < b`. -/
theorem thm_main
    (rankOne : RankOneDinv)
    (goodTraverse : GoodTraverse)
    (coercivity : HuangCoercivity)
    (collinear : CollinearCommutation Witness.Base)
    (shuffle : Shuffle Witness.Base)
    (epsilonGessel : EpsilonGessel Witness.Base)
    (creationExpansion : CreationExpansion Witness.Base)
    (cylindricProduct : CylindricProduct)
    (a b : ℕ) (hco : Nat.Coprime a b) (ha : 1 < a) (hab : a < b) :
    Conjecture a b :=
  HJO.Final.conjecture rankOne goodTraverse coercivity collinear shuffle epsilonGessel
    creationExpansion cylindricProduct hco ha hab

end HJO.Challenge

end
