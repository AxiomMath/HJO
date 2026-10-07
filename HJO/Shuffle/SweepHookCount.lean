/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepHookLine
public meta import HJO.Attr

/-! # The hook count is the number of crossed (east, north) pairs

`ĥ(P̂)` counts the cells of the diagram above the path that pass Macdonald's hook condition.
`HJO.Paths.aboveHookCount_eq_card_crossingPairs` says that this is the number of pairs `(e, u)` — an
east step and a north step strictly to its right — that some level line crosses.

The two sides match cell by pair. The pair "east step at `s`, north step at height `i`" spans the
cell `(s+1, i+1)`, whose arm and leg are the two offsets `α` and `λ` of that pair
(`HJO.Paths.aboveArm_succ_succ`, `HJO.Paths.aboveLeg_succ_succ`); and by
`HJO.Paths.exists_levelCrosses_iff_hook` the cell passes the hook condition exactly when some level
line crosses both steps. So the correspondence is the reindexing `(s, i) ↦ (s+1, i+1)` and nothing
else happens.

## Main results

* `HJO.Paths.crossingPairs`: the pairs, indexed by the abscissa of the east step and the height of
  the north step's foot.
* `HJO.Paths.aboveHookCount_eq_card_crossingPairs`.

## Implementation notes

### How a pair is named

A pair is a point `(s, i)` of `range (aN) ×ˢ range (bN)` with `s + 1 ≤ Â_{i+1}`: `s` is the abscissa
of the east step, `i` the height of the north step's foot — which names the step uniquely on an
above-diagonal path, as `HJO.Paths.northSteps_eq_image` records — and the inequality is "`e`
strictly to the left of `u`", since the north step at height `i` sits in column
`Â_{i+1}` (`HJO.Paths.lastBelow_succ_of_mem_northSteps`). Naming the north step by its height rather
than as a lattice point is what makes the reindexing to cells the map `(s, i) ↦ (s+1, i+1)`.

### `Classical` in the definition

The crossing condition is `∃ η : ℤ, …`, an existential over `ℤ`, which carries no `Decidable`
instance even though `HJO.Paths.LevelCrosses` itself is decidable. `HJO.Paths.crossingPairs` is
therefore a `noncomputable def` whose filter uses classical decidability, in the house style of
`HJO.Mellit.sortByRank` and `HJO.Paths.sweepChar`. Nothing below evaluates it.

An equivalent decidable formulation is available and is *not* used: by
`HJO.Paths.exists_mem_inter_Ico` the existential is the pair of rank inequalities
`rk(R) < rk(H)` and `rk(F) < rk(L)`, both decidable. Stating the definition that way would have made
it computable at the cost of no longer saying "some level line crosses both steps", which is the
wording of the hook condition and the thing
`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv` reads. The
phrasing is kept and the decidable form left to `exists_levelCrosses_iff_hook`.

### A false variant of this statement

Reading `ĥ(P̂)` as a count of pairs indexed by sweep events, whose second summand counts north steps
where it must count east steps, gives a false statement: it disagrees with
`HJO.Paths.aboveHookCount` on above-diagonal paths, the smallest witness being `a = 2`, `b = 3`,
`N = 1`, `ŷ = (0,2,3)` with hook count `1` against the formula's `2`. The statement formalized here
is the count of crossing pairs. The regrouping by sweep events that
`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv` actually
consumes is `HJO.Paths.revealPoint_rank_ne_and_eventType`, which is separate.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section "The sweep process", for Lemma
`HJO.Paths.aboveHookCount_eq_card_crossingPairs`, using `HJO.Paths.IsAboveDiagonal`,
`HJO.Paths.aboveCells`, `HJO.Paths.aboveHookCount`, `HJO.Paths.sweptRegion`, `HJO.Paths.liveSteps`
and `HJO.Paths.eventType`.
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### The crossed pairs -/

open Classical in
/-- **The crossed (east, north) pairs of an above-diagonal path**, each named by the abscissa `s` of
its east step and the height `i` of its north step's foot: the pairs with the east step strictly to
the left of the north step, `s + 1 ≤ Â_{i+1}`, and with some level line crossing both.

`noncomputable` because the crossing condition is an existential over `ℤ`; see the module
docstring, and `HJO.Paths.exists_levelCrosses_iff_hook` for the decidable equivalent. -/
noncomputable def crossingPairs (y : Heights a b N) : Finset (ℕ × ℕ) :=
  (range (a * N) ×ˢ range (b * N)).filter
    (fun p => p.1 + 1 ≤ ParkingFunctions.aboveColumn y p.2 ∧
      ∃ η : ℤ, LevelCrosses a b N η (eastLeft y p.1) (eastRight y p.1) ∧
        LevelCrosses a b N η (ParkingFunctions.aboveColumn y p.2, p.2)
          (ParkingFunctions.aboveColumn y p.2, p.2 + 1))

open Classical in
theorem mem_crossingPairs {y : Heights a b N} {s i : ℕ} :
    (s, i) ∈ crossingPairs y ↔ (s < a * N ∧ i < b * N) ∧
      s + 1 ≤ ParkingFunctions.aboveColumn y i ∧
      ∃ η : ℤ, LevelCrosses a b N η (eastLeft y s) (eastRight y s) ∧
        LevelCrosses a b N η (ParkingFunctions.aboveColumn y i, i)
          (ParkingFunctions.aboveColumn y i, i + 1) := by
  rw [crossingPairs, mem_filter, mem_product, mem_range, mem_range]

/-! ### The hook count -/

/-- **`ĥ(P̂)` is the number of crossed pairs.** `HJO.Paths.aboveHookCount_eq_card_crossingPairs`.

The hook-passing cells are the image of `HJO.Paths.crossingPairs` under `(s, i) ↦ (s+1, i+1)`: the
pair spans that cell (`HJO.Paths.mem_aboveCells_of_mem_northSteps`), the cell's arm and leg are the
pair's two offsets (`HJO.Paths.aboveArm_succ_succ`, `HJO.Paths.aboveLeg_succ_succ`), and the hook
condition on those offsets is the crossing condition
(`HJO.Paths.exists_levelCrosses_iff_hook`). The reindexing is injective, so the counts agree. -/
@[hjo "lem_sweep_hook_crossings"]
theorem aboveHookCount_eq_card_crossingPairs {y : Heights a b N} (hy : IsAboveDiagonal y)
    (ha : 0 < a) (hb : 0 < b) : aboveHookCount y = #(crossingPairs y) := by
  have hstep : ∀ i : ℕ, i < b * N →
      (ParkingFunctions.aboveColumn y i, i) ∈ northSteps y := fun i hi =>
    (ParkingFunctions.mem_northSteps_iff_eq_aboveColumn hy).2 ⟨hi, rfl⟩
  -- the arm and the leg of the cell a pair spans, at the pair's own offsets
  have harm : ∀ s i : ℕ, i < b * N →
      aboveArm y (s + 1) (i + 1) = ParkingFunctions.aboveColumn y i - (s + 1) := fun s i hi =>
    aboveArm_succ_succ hy s (u := (ParkingFunctions.aboveColumn y i, i)) (hstep i hi)
  have hleg : ∀ s i : ℕ, aboveLeg y (s + 1) (i + 1) = i - ht y (s + 1) :=
    fun s i => aboveLeg_succ_succ y s i
  have himg : {q ∈ aboveCells y | b * aboveArm y q.1 q.2 ≤ a * (aboveLeg y q.1 q.2 + 1) ∧
      a * aboveLeg y q.1 q.2 < b * (aboveArm y q.1 q.2 + 1)}
      = (crossingPairs y).image (fun p => (p.1 + 1, p.2 + 1)) := by
    ext q
    obtain ⟨r, j⟩ := q
    simp only [mem_filter, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨hq, h1, h2⟩
      obtain ⟨hr1, hr2, hj1, hj2⟩ := mem_aboveCells.1 hq
      simp only at hr1 hr2 hj1 hj2
      obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hi : i < b * N := by omega
      have hu := hstep i hi
      have hcol : s + 1 ≤ ParkingFunctions.aboveColumn y i := by
        have hcl : ParkingFunctions.aboveColumn y i = lastBelow y (i + 1) := rfl
        rw [hcl]
        exact le_lastBelow (by omega) hj1
      rw [harm s i hi, hleg s i] at h1 h2
      refine ⟨(s, i), mem_crossingPairs.2 ⟨⟨by omega, hi⟩, hcol, ?_⟩, rfl, rfl⟩
      exact (exists_levelCrosses_iff_hook (y := y) ha hb (s := s) (by omega) hu
        (α := ParkingFunctions.aboveColumn y i - (s + 1)) (l := i - ht y (s + 1))
        (by simp only; omega) (by simp only; omega)).2 ⟨h1, h2⟩
    · rintro ⟨p, hp, rfl, rfl⟩
      obtain ⟨s, i⟩ := p
      obtain ⟨⟨hs, hi⟩, hcol, hcross⟩ := mem_crossingPairs.1 hp
      have hu := hstep i hi
      have hfoot : ht y (ParkingFunctions.aboveColumn y i) ≤ i := by
        have := (mem_northSteps_iff.1 hu).2.1
        simp only at this
        exact this
      have hmono : ht y (s + 1) ≤ ht y (ParkingFunctions.aboveColumn y i) :=
        ht_mono hy.2.2.1 hcol
      have hhook := (exists_levelCrosses_iff_hook (y := y) ha hb (s := s) hs hu
        (α := ParkingFunctions.aboveColumn y i - (s + 1)) (l := i - ht y (s + 1))
        (by simp only; omega) (by simp only; omega)).1 hcross
      refine ⟨mem_aboveCells_of_mem_northSteps hy
        (u := (ParkingFunctions.aboveColumn y i, i)) hu hcol, ?_, ?_⟩
      · change b * aboveArm y (s + 1) (i + 1) ≤ a * (aboveLeg y (s + 1) (i + 1) + 1)
        rw [harm s i hi, hleg s i]
        exact hhook.1
      · change a * aboveLeg y (s + 1) (i + 1) < b * (aboveArm y (s + 1) (i + 1) + 1)
        rw [harm s i hi, hleg s i]
        exact hhook.2
  rw [aboveHookCount, himg,
    card_image_of_injective _ fun p q h => by
      rw [Prod.ext_iff]
      exact ⟨by simpa using congrArg Prod.fst h, by simpa using congrArg Prod.snd h⟩]

end HJO.Paths
