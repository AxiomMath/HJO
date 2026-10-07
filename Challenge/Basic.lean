module

-- Load-bearing for the comparator, NOT for compilation. This import fixes which
-- `PartialOrder ℤ` instance path the statements elaborate against, and `HJO/Definitions.lean` must
-- resolve the same one. This file compiles without it, so `minimize_imports` reports it
-- UNUSED -- removing it changes the exported terms and the comparator then rejects
-- `HJO.Challenge.thm_finite`. Do not remove.
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import QSeriesLib.NumberTheory.HJO.Defs

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statements that this repository proves: the
Huang--Jiang--Oblomkov conjecture for every coprime pair, and the finite identity behind it, with
nothing assumed.
-/

@[expose] public section

open Finset HJO NumericalSemigroup PowerSeries
open scoped QTheory PowerSeries.DiscreteTopology

local notation "gaps(" a ", " b ")" => NumericalSemigroup.gaps (NumericalSemigroup.finspan {a, b})

namespace HJO.Cylindric

open PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

/-- The balanced profile `cᵢ = ⌊(i+1)b/a⌋ - ⌊ib/a⌋`. For `a > 0` it is periodic with
period `a`, and its first `a` entries sum to `b`. -/
def profile (a b : ℕ) (i : ℕ) : ℕ := (i + 1) * b / a - i * b / a

/-- A cylindric partition with outgoing profile `c`: an `a`-tuple of partitions, written
here as one row-indexed family with the row index taken modulo `a`, in which row `i + 1`
at position `j + c i` never exceeds row `i` at position `j`. -/
structure IsCylindric (a : ℕ) (c : ℕ → ℕ) (l : ℕ → ℕ → ℕ) : Prop where
  /-- Each row is a partition: weakly decreasing. -/
  antitone : ∀ i, Antitone (l i)
  /-- Each row has finitely many nonzero parts. -/
  eventually_zero : ∀ i, ∃ J, ∀ j, J ≤ j → l i j = 0
  /-- Rows depend only on `i` modulo `a`, closing the cylinder. -/
  periodic : ∀ i j, l (i + a) j = l i j
  /-- The outgoing inequality of the cylinder. -/
  outgoing : ∀ i j, l (i + 1) (j + c i) ≤ l i j

/-- The volume of a cylindric partition: the sum of the entries of its `a` rows. The
inner sum is finite because each row has finitely many nonzero parts. -/
noncomputable def cylVolume (a : ℕ) (l : ℕ → ℕ → ℕ) : ℕ := ∑ i ∈ range a, ∑ᶠ j, l i j

/-- Every entry of the cylinder is at most `N`. -/
def BoundedBy (N : ℕ) (l : ℕ → ℕ → ℕ) : Prop := ∀ i j, l i j ≤ N

/-- `C_{c,≤N}(q)`, the volume generating function of the cylindric partitions with
outgoing profile `c` whose every entry is at most `N`. A positive entry bound need not bound
the number of parts, so the definition uses a formal-series sum. At `N = 0` only the zero
cylinder contributes, giving the constant series `1`. -/
noncomputable def boundedGF (a b N : ℕ) : ℤ⟦X⟧ :=
  ∑' l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l ∧ BoundedBy N l},
    X ^ cylVolume a l.val

end HJO.Cylindric

namespace HJO.Finite

open PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

/-- The generalized Gaussian multinomial `[N; 𝐧]_{q;G}`: `(q)_N` divided by `(q)_{N - n_f}`,
the difference taken by truncated natural subtraction, times the product of the gap
multiplicands. The index set of `poly` requires `n_f ≤ N`. -/
noncomputable def gaussianMultinomial (a b N : ℕ) (n : gaps(a, b) → ℕ) : ℤ⟦X⟧ :=
  (X; X)_N * invOfUnit (X; X)_(N - extendNat n (a * b - a - b)) 1 *
    ∏ i : gaps(a, b), multiplicand gaps(a, b) a b (fun j => (n j : ℤ)) i

/-- `F_N(q) = N_{a,b;N}(q,1)`, the HJO polynomial at module rank `N`: the sum over
gap vectors in the monotonicity cone with `n_f ≤ N` of `[N; 𝐧]_{q;G} q^{Q(𝐧)}`. -/
noncomputable def poly (a b N : ℕ) : ℤ⟦X⟧ :=
  ∑ᶠ n ∈ {n : gaps(a, b) → ℕ |
      (fun i => (n i : ℤ)) ∈ cone a b ∧ extendNat n (a * b - a - b) ≤ N},
    gaussianMultinomial a b N n * X ^ (Q a b (fun i => (n i : ℤ))).toNat

end HJO.Finite

namespace HJO.Challenge

open HJO.Cylindric HJO.Finite

/-- The cylindric partitions with outgoing profile `c` and every entry at most `N` are
summable by volume. A `tsum` is zero by definition when the family is not summable, so
without this `boundedGF` says nothing. -/
theorem summable_boundedGF (a b N : ℕ) (ha : 0 < a) :
    Summable fun l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l ∧ BoundedBy N l} =>
      (X : ℤ⟦X⟧) ^ cylVolume a l.val :=
  sorry

/-- The cylindric partitions with outgoing profile `c` and no bound on their entries are
summable by volume. -/
theorem summable_unboundedGF (a b : ℕ) (ha : 0 < a) :
    Summable fun l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l} =>
      (X : ℤ⟦X⟧) ^ cylVolume a l.val :=
  sorry

/-- The index set of `poly` is finite, so its `finsum` is an honest `Finset` sum. A
`finsum` is zero by definition on infinite support, so without this `poly` says nothing. -/
theorem finite_index (a b N : ℕ) (hco : Nat.Coprime a b) (ha : 1 < a) (hab : a < b) :
    {n : gaps(a, b) → ℕ |
      (fun i => (n i : ℤ)) ∈ cone a b ∧ extendNat n (a * b - a - b) ≤ N}.Finite :=
  sorry

/-- **The finite identity.** For coprime `1 < a < b` and every rank `N`, the HJO polynomial is
`(q)_N` times the generating function of the balanced cylindric partitions with largest entry at
most `N`. -/
theorem thm_finite (a b : ℕ) (hco : Nat.Coprime a b) (ha : 1 < a) (hab : a < b) (N : ℕ) :
    HJO.Finite.poly a b N = (X; X)_N * HJO.Cylindric.boundedGF a b N :=
  sorry

/-- **The Huang–Jiang–Oblomkov conjecture.** The HJO series equals the HJO product, for every
coprime pair `a, b`. -/
theorem thm_main (a b : ℕ) (hco : Nat.Coprime a b) :
    Conjecture a b :=
  sorry

end HJO.Challenge
