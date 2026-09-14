/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Paths.ReturnPathSolves
public meta import HJO.Attr

/-! # The upper boundary of the gap set and the length of its chain

For coprime `1 < a < b` this file records the two objects that organise the good-traverse
factorisation of the generalised Gaussian multinomial: the upper boundary `𝓑` of the gap set `G`
of `⟨a, b⟩`, consisting of the gaps whose upper shift by `b` leaves `G`, and the length
`L = ⌊f/a⌋` of the chain that boundary forms below the Frobenius gap `f`.

The boundary is where the flag extension of a cone point switches from a cone value to the level
`N`, so its factors are the ones that survive the cancellation in pairs. What makes them
telescope is `mem_upperBoundary_iff_dvd`: a gap lies on the boundary exactly when its upper shift
is a multiple of `a`, so the boundary is a single `⟨a⟩`-chain, topped by the Frobenius gap.
-/

@[expose] public section

open Finset NumericalSemigroup

namespace HJO.Defs

/-! ### The upper boundary -/

/-- The upper boundary of the gap set, `𝓑 = {g ∈ G : g + b ∉ G}`: the gaps whose upper shift
by `b` leaves the gap set. -/
@[hjo "def_traverse_boundary"]
def upperBoundary (a b : ℕ) : Finset ℕ :=
  {g ∈ (finspan {a, b}).gaps | g + b ∉ (finspan {a, b}).gaps}

/-- Membership in the upper boundary is the defining pair of conditions. -/
@[simp]
theorem mem_upperBoundary {a b g : ℕ} :
    g ∈ upperBoundary a b ↔
      g ∈ (finspan {a, b}).gaps ∧ g + b ∉ (finspan {a, b}).gaps :=
  mem_filter

/-- The upper boundary consists of gaps. -/
theorem upperBoundary_subset_gaps (a b : ℕ) : upperBoundary a b ⊆ (finspan {a, b}).gaps :=
  filter_subset _ _

/-- The arithmetic description of the upper boundary: a gap lies on it exactly when its upper
shift is a multiple of `a`. This is what makes the boundary a single `⟨a⟩`-chain. -/
theorem mem_upperBoundary_iff_dvd {a b g : ℕ} (hco : a.Coprime b) :
    g ∈ upperBoundary a b ↔ g ∈ (finspan {a, b}).gaps ∧ a ∣ (g + b) := by
  simp only [mem_upperBoundary]
  exact ⟨fun h => ⟨h.1, (ReturnPathSolves.add_right_notMem_gaps_iff hco h.1).mp h.2⟩,
    fun h => ⟨h.1, (ReturnPathSolves.add_right_notMem_gaps_iff hco h.1).mpr h.2⟩⟩

/-- The Frobenius gap lies on the upper boundary: it is the top of the boundary chain, its upper
shift being `f + b = a * (b - 1)`. -/
theorem frobeniusGap_mem_upperBoundary (a b : ℕ) (hco : a.Coprime b) (ha : 1 < a) (hb : 1 < b) :
    Gaps.frobeniusGap a b ∈ upperBoundary a b := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have key : Gaps.frobeniusGap a (c + 1) + (c + 1) + a = a * c + a :=
    calc Gaps.frobeniusGap a (c + 1) + (c + 1) + a
        = Gaps.frobeniusGap a (c + 1) + a + (c + 1) := by ring
      _ = a * (c + 1) := GapPoset.frobeniusGap_add_add a (c + 1) ha hb
      _ = a * c + a := by ring
  exact (mem_upperBoundary_iff_dvd hco).mpr
    ⟨GapPoset.frobeniusGap_mem a (c + 1) hco ha hb, c, Nat.add_right_cancel key⟩

/-! ### The length of the boundary chain -/

/-- The length of the boundary chain, `L = ⌊f/a⌋` for the Frobenius gap `f`: the upper boundary
is `{f - j * a : 0 ≤ j ≤ L}`. The bound `L * a ≤ f` that keeps the chain inside `ℕ` is
`Nat.div_mul_le_self`, and the bound `f < (L + 1) * a` that stops it is `Nat.div_add_mod` with
`Nat.mod_lt`. -/
@[hjo "def_traverse_length"]
abbrev boundaryLength (a b : ℕ) : ℕ := Gaps.frobeniusGap a b / a

end HJO.Defs
