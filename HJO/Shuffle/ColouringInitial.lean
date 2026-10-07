/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ColouringStep

/-! # The initial value of the sweep: `D_{η,∅} = 1`

Above every rank of the rectangle the sweep has done nothing: no north step is crossed, no east
step is crossed, no swept point is above the level, so every above-diagonal path has the empty
colouring and the empty trace, and `HJO.Mellit.dsc` is a one-term sum whose term is the vacuum.
That is the starting value `D_{s,∅} = 1` of the recursion of Mellit's Theorem 4.2, and the initial
condition on which the proof of his Theorem 5.8 rests.

## Main results

* `HJO.Mellit.maxAbovePath` — the highest `(aN, bN)`-path, `ŷ_0 = 0` and `ŷ_r = bN` afterwards;
  the witness that an above-diagonal path exists at all.
* `HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one` — the base case of the
  induction.

## Implementation notes

`0 < a` is needed, for a reason more basic than the isolation
arguments elsewhere: at `a = 0 < b` and `N ≥ 1` the rectangle has no columns but the path must
still climb to `bN`, so **no above-diagonal path exists**, `∅` is an admissible colouring at no
level, and `HJO.Mellit.dsc` is the empty sum `0`. Both halves of the statement are then false. The
standing hypothesis is `1 < a < b`, so nothing is lost.

The level is not required to be admissible. It is usually assumed, but the hypothesis
`rk̂(x,y) + ω < η` already puts `η` above every rank, which is all the proof uses.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, arXiv:1604.07456, Theorem 4.2 and
the proof of Theorem 5.8.
-/

@[expose] public section

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The highest above-diagonal path -/

/-- **The highest `(aN, bN)`-path**: `ŷ_0 = 0` and `ŷ_r = bN` for every `r ≥ 1`. Every other
above-diagonal path lies weakly below it, and — what it is used for here — it shows that the set
of above-diagonal paths is not empty whenever `0 < a`. -/
def maxAbovePath (a b N : ℕ) : Heights a b N := fun r => if (r : ℕ) = 0 then 0 else Fin.last _

/-- The height function of `HJO.Mellit.maxAbovePath`, at every index including those past the
right edge, where `HJO.Paths.ht` holds its value at `bN`. -/
theorem ht_maxAbovePath (a b N r : ℕ) :
    ht (maxAbovePath a b N) r = if r = 0 then 0 else b * N := by
  rcases Nat.lt_or_ge r (a * N + 1) with h | h
  · by_cases hr : r = 0 <;> simp [ht, maxAbovePath, h, hr]
  · simp [ht, Nat.not_lt.2 h, show r ≠ 0 by omega]

/-- **The highest path is above the diagonal.** The only place `0 < a` enters is the right
endpoint: at `a = 0 < bN` the height at `aN = 0` is `0` and not `bN`, and indeed no above-diagonal
path exists there. -/
theorem isAboveDiagonal_maxAbovePath (ha : 0 < a) : IsAboveDiagonal (maxAbovePath a b N) := by
  have hz : ht (maxAbovePath a b N) 0 = 0 := by rw [ht_maxAbovePath]; simp
  have hne : ∀ r : ℕ, r ≠ 0 → ht (maxAbovePath a b N) r = b * N := fun r hr => by
    rw [ht_maxAbovePath]; simp [hr]
  refine ⟨hz, ?_, fun r hr => ?_, fun r hr => ?_⟩
  · rcases Nat.eq_zero_or_pos (a * N) with h | h
    · have hN : N = 0 := by
        rcases Nat.eq_zero_or_pos N with h0 | h0
        · exact h0
        · exact absurd h (Nat.mul_pos ha h0).ne'
      rw [h, hz, hN, Nat.mul_zero]
    · rw [hne _ (by omega)]
  · rw [hne (r + 1) (by omega)]
    exact ht_le_mul _ _
  · rcases Nat.eq_zero_or_pos r with h0 | h0
    · simp [h0]
    · rw [hne r (by omega)]
      calc b * r ≤ b * (a * N) := Nat.mul_le_mul_left b hr
        _ = a * (b * N) := by ring

/-! ### Above every rank nothing has been swept -/

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The initial value.** `HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`: at a level above
`rk̂ + ω` on the whole rectangle, `∅` is an admissible colouring and `D_{η,∅} = 1`.

Every north step `u` of every path has `rk̂(u) + ω < η`, so the crossing condition
`rk̂(u) < η < rk̂(u) + ω` fails; every east step `v` has `rk̂(v) < η`, so `η < rk̂(v)` fails; and
every swept point `P` has `rk̂(P) < η`, so the trace is empty and the partial word is the identity.
The index set of `HJO.Mellit.dsc` is therefore the single trace `∅` — single, and not empty,
because `HJO.Mellit.maxAbovePath` is an above-diagonal path realising it. -/
@[hjo "lem_colouring_initial"]
theorem isAdmissibleColouring_empty_and_dsc_eq_one (q u : L) (ha : 0 < a) {η : ℚ}
    (hη : ∀ P : ℕ × ℕ, P.1 ≤ a * N → P.2 ≤ b * N →
      ((pointRank a b N P : ℤ) : ℚ) + ((attackWindow a N : ℕ) : ℚ) < η) :
    IsAdmissibleColouring a b N η (∅ : Finset (ℕ × ℕ)) ∧
      dsc q u a b N η (∅ : Finset (ℕ × ℕ)) = (1 : Total L) := by
  have hω : (0 : ℚ) ≤ ((attackWindow a N : ℕ) : ℚ) := Nat.cast_nonneg _
  have hcol : ∀ y : Heights a b N, colouring y η = ∅ := by
    intro y
    rw [colouring, Finset.union_eq_empty]
    constructor
    · refine Finset.filter_eq_empty_iff.2 fun {P} hP => ?_
      obtain ⟨h1, -, h3⟩ := mem_northSteps_iff.1 hP
      have h2 : P.2 ≤ b * N := (Nat.le_of_lt h3).trans (ht_le_mul y _)
      exact fun hcross => absurd hcross.2 (not_lt.2 (hη P (by omega) h2).le)
    · refine Finset.filter_eq_empty_iff.2 fun {P} hP => ?_
      obtain ⟨h1, h2⟩ := mem_eastSteps_iff.1 hP
      have h3 : P.2 ≤ b * N := h2 ▸ ht_le_mul y _
      exact fun hcross => absurd hcross.2
        (not_lt.2 (by linarith [hη P (by omega : P.1 ≤ a * N) h3]))
  have hswept : ∀ y : Heights a b N, sweptAbove y η = ∅ := by
    intro y
    refine Finset.filter_eq_empty_iff.2 fun {P} hP => ?_
    obtain ⟨h1, -, h3⟩ := mem_sweptRegion.1 hP
    exact not_lt.2 (by linarith [hη P h1 (h3.trans (ht_le_mul y _))])
  have htrace : ∀ y : Heights a b N, levelTrace y η = ∅ := by
    intro y
    rw [levelTrace, hswept, Finset.image_empty]
  have hword : ∀ y : Heights a b N, partialSweepWord q u y η = (1 : Module.End L (Total L)) := by
    intro y
    rw [partialSweepWord, hswept, sortByRank_empty, List.map_nil, List.prod_nil]
  refine ⟨⟨maxAbovePath a b N, isAboveDiagonal_maxAbovePath ha, hcol _⟩, ?_⟩
  have hindex : traceIndex a b N η (∅ : Finset (ℕ × ℕ)) = {∅} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_image.2
      ⟨maxAbovePath a b N, Finset.mem_filter.2 ⟨Finset.mem_univ _,
        isAboveDiagonal_maxAbovePath ha, hcol _⟩, htrace _⟩, fun τ hτ => ?_⟩
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hτ
    exact htrace y
  rw [dsc, hindex, Finset.sum_singleton, hword]
  rfl

end HJO.Mellit
