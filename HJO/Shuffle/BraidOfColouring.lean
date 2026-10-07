/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ColouringStepCounts

/-! # The special-braid data of a colouring

A colouring determines a special braid as follows: project each component of the
colouring to the torus, let `v_i` be its first intersection with the antidiagonal followed from the
east end back to the north end, and let `α_i` be the total number of its intersections with the
antidiagonal. A point `(x, w)` of the plane lies over the antidiagonal of `ℝ²/ℤ²` exactly when
`x + w ∈ ℤ`, and on the level line `w = s x + η/(aM)` that reads `(1 + s)x + η/(aM) ∈ ℤ`.

## Main results

* `HJO.Mellit.componentCrossings` — the `X_i(c)`, verbatim.
* `HJO.Mellit.crossingAbscissa` and `HJO.Mellit.componentCrossingIndices` — the same set
  parametrised by the integer it crosses, which is what makes it finite, countable and ordered.
* `HJO.Mellit.componentCrossings_eq_image` — the two descriptions agree.
* `HJO.Mellit.braidDataOfColouring`.
* `HJO.Mellit.mem_componentCrossings_componentTopIndex` and
  `HJO.Mellit.le_crossingAbscissa_componentTopIndex` — the position `v_i` is read off the crossing
  of *largest* abscissa, as the construction asks: that crossing is one of them, and no crossing
  exceeds it.

## Implementation notes

`ℚ` is not conditionally complete, so `max X_i(c)` is not available as a `sSup`; and the set
`X_i(c)` is cut out of a closed interval by a divisibility condition, which is a `Set ℚ` and not a
`Finset`. Both are handled by parametrising the crossings by the integer they cross:
`HJO.Mellit.componentCrossingIndices` is the `Finset.Icc` of integers `n` with
`⌈(1+s)L + η/(aM)⌉ ≤ n ≤ ⌊(1+s)R + η/(aM)⌋`, the crossing of index `n` is at abscissa
`(n - η/(aM))/(1+s)`, and the two are matched by
`HJO.Mellit.componentCrossings_eq_image`. The maximum is then the crossing of the largest index,
`HJO.Mellit.componentTopIndex`, since the abscissa is increasing in the index.

`v_i := max X_i(c) - ⌊max X_i(c)⌋` is `Int.fract` of that abscissa.

Everything here needs `0 < 1 + s_{a,b,N}`, which `HJO.Mellit.sweepSlope_pos` supplies for
`0 < a`, `0 < b`, `0 < N`; on a degenerate rectangle the level line is not a line the crossings can
be read along, and the definitions return junk rather than being undefined.

## References

This file builds `HJO.Mellit.braidDataOfColouring` from `HJO.Mellit.colouringComponent`,
`HJO.Mellit.sweepSlope` and `HJO.Braid.nextCrossing`, towards `HJO.Braid.IsSpecialBraidData` and
`HJO.Mellit.isSpecialBraidData_braidDataOfColouring`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The slope is positive -/

/-- **The sweep slope is positive** on a rectangle with a row and a column: the numerator
`b(aN+1)N - 1` is at least `1`, since `aN + 1 ≥ 2`. -/
theorem sweepSlope_pos (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) : 0 < sweepSlope a b N := by
  have haN : 1 ≤ a * N := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h2 : 2 ≤ b * (a * N + 1) * N := by
    calc (2 : ℕ) = 1 * 2 * 1 := by norm_num
      _ ≤ b * (a * N + 1) * N := by gcongr <;> omega
  have h2' : (2 : ℚ) ≤ (b : ℚ) * ((a : ℚ) * N + 1) * N := by exact_mod_cast h2
  have hden : (0 : ℚ) < (a : ℚ) * ((a : ℚ) * N + 1) * N := by
    have ha' : (0 : ℚ) < a := by exact_mod_cast ha
    have hN' : (0 : ℚ) < N := by exact_mod_cast hN
    positivity
  rw [sweepSlope]
  exact div_pos (by linarith) (by linarith)

/-- `1 + s_{a,b,N}` is positive, which is what every division below needs. -/
theorem one_add_sweepSlope_pos (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    0 < 1 + sweepSlope a b N := by
  have := sweepSlope_pos ha hb hN (a := a) (b := b) (N := N)
  linarith

/-! ### The crossings of a component with the antidiagonal -/

/-- **The crossings of the `i`-th component with the antidiagonal.** The `X_i(c)`: the
abscissae `x` in `J_i(c)` at which `(1 + s_{a,b,N})x + η/(a(aN+1)N)` is an integer, that is at which
the point of the level line over `x` lies over the antidiagonal of the torus. -/
def componentCrossings (a b N : ℕ) (y : Heights a b N) (η : ℚ) (i : ℕ) : Set ℚ :=
  {x ∈ colouringComponent a b N y η i |
    ∃ n : ℤ, (1 + sweepSlope a b N) * x + levelIntercept a N η = (n : ℚ)}

/-- The abscissa at which the level line meets the antidiagonal `x + w = n`. Consecutive values
differ by `1/(1 + s_{a,b,N}) = θ`, which is why the iterates of `HJO.Braid.nextCrossing` list the
crossings after the first. -/
def crossingAbscissa (a b N : ℕ) (η : ℚ) (n : ℤ) : ℚ :=
  ((n : ℚ) - levelIntercept a N η) / (1 + sweepSlope a b N)

/-- Consecutive crossings are `θ = 1/(1+s)` apart in abscissa. -/
theorem crossingAbscissa_succ (hs : 1 + sweepSlope a b N ≠ 0) (η : ℚ) (n : ℤ) :
    crossingAbscissa a b N η (n + 1) =
      crossingAbscissa a b N η n + 1 / (1 + sweepSlope a b N) := by
  rw [crossingAbscissa, crossingAbscissa]
  field_simp
  push_cast
  ring

/-- The crossing abscissa is increasing in the index. -/
theorem crossingAbscissa_le (hs : 0 < 1 + sweepSlope a b N) (η : ℚ) {m n : ℤ} (h : m ≤ n) :
    crossingAbscissa a b N η m ≤ crossingAbscissa a b N η n := by
  have hne : (1 + sweepSlope a b N) ≠ 0 := hs.ne'
  have hmn : ((m : ℚ)) ≤ (n : ℚ) := by exact_mod_cast h
  have key : crossingAbscissa a b N η n - crossingAbscissa a b N η m
      = ((n : ℚ) - m) / (1 + sweepSlope a b N) := by
    rw [crossingAbscissa, crossingAbscissa]
    field_simp
    ring
  have hnn : 0 ≤ ((n : ℚ) - m) / (1 + sweepSlope a b N) :=
    div_nonneg (by linarith) hs.le
  linarith

/-- The integer indices of the crossings of the `i`-th component: the integers `n` with
`⌈(1+s)L + η/(aM)⌉ ≤ n ≤ ⌊(1+s)R + η/(aM)⌋`, where `[L, R]` is the component. -/
noncomputable def componentCrossingIndices (a b N : ℕ) (y : Heights a b N) (η : ℚ) (i : ℕ) :
    Finset ℤ :=
  Finset.Icc ⌈(1 + sweepSlope a b N) * componentLeft y η i + levelIntercept a N η⌉
    ⌊(1 + sweepSlope a b N) * componentRight a b N y η i + levelIntercept a N η⌋

/-- The largest index of a crossing of the `i`-th component. -/
noncomputable def componentTopIndex (a b N : ℕ) (y : Heights a b N) (η : ℚ) (i : ℕ) : ℤ :=
  ⌊(1 + sweepSlope a b N) * componentRight a b N y η i + levelIntercept a N η⌋

/-- **The `X_i(c)` is the image of its index set.** Every crossing is the crossing of
exactly one integer, and the integers that occur are those between the two endpoints. -/
theorem componentCrossings_eq_image (hs : 0 < 1 + sweepSlope a b N) (y : Heights a b N) (η : ℚ)
    (i : ℕ) :
    componentCrossings a b N y η i =
      (crossingAbscissa a b N η) '' (componentCrossingIndices a b N y η i : Set ℤ) := by
  have hne : (1 + sweepSlope a b N) ≠ 0 := hs.ne'
  ext x
  constructor
  · rintro ⟨hx, n, hn⟩
    have hL : componentLeft y η i ≤ x := hx.1
    have hR : x ≤ componentRight a b N y η i := hx.2
    refine ⟨n, ?_, ?_⟩
    · refine Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨Int.ceil_le.2 ?_, Int.le_floor.2 ?_⟩)
      · have := mul_le_mul_of_nonneg_left hL hs.le
        linarith
      · have := mul_le_mul_of_nonneg_left hR hs.le
        linarith
    · rw [crossingAbscissa, ← hn]
      field_simp
      ring
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 (Finset.mem_coe.1 hn)
    have hval : (1 + sweepSlope a b N) * crossingAbscissa a b N η n + levelIntercept a N η
        = (n : ℚ) := by
      rw [crossingAbscissa, mul_div_cancel₀ _ hne]
      ring
    refine ⟨⟨?_, ?_⟩, n, hval⟩
    · have hc := Int.ceil_le.1 h1
      refine le_of_mul_le_mul_left ?_ hs
      linarith
    · have hf := Int.le_floor.1 h2
      refine le_of_mul_le_mul_left ?_ hs
      linarith

/-! ### The data -/

/-- **The special-braid data of a colouring.** `HJO.Mellit.braidDataOfColouring`: with
`X_i(c)` the crossings of the `i`-th component with the antidiagonal, `α_i := #X_i(c)` and
`v_i := max X_i(c) - ⌊max X_i(c)⌋`.

Written against the index parametrisation: `α_i` is the number of integer indices, which is
`#X_i(c)` by `HJO.Mellit.card_componentCrossingIndices`, and `v_i` is the fractional part of the
crossing of largest index, which is `max X_i(c)` by
`HJO.Mellit.mem_componentCrossings_componentTopIndex` together with
`HJO.Mellit.le_crossingAbscissa_componentTopIndex`. -/
@[hjo "def_braid_of_colouring"]
noncomputable def braidDataOfColouring (a b N : ℕ) (y : Heights a b N) (η : ℚ) (k : ℕ) :
    (Fin k → ℚ) × (Fin k → ℕ) :=
  (fun i => Int.fract (crossingAbscissa a b N η (componentTopIndex a b N y η i)),
    fun i => #(componentCrossingIndices a b N y η i))

/-- The multiplicity `α_i` is the number of crossings, `#X_i(c)`. -/
theorem card_componentCrossingIndices (hs : 0 < 1 + sweepSlope a b N) (y : Heights a b N) (η : ℚ)
    (i : ℕ) :
    (componentCrossings a b N y η i).ncard = #(componentCrossingIndices a b N y η i) := by
  have hne : (1 + sweepSlope a b N) ≠ 0 := hs.ne'
  have hinj : Function.Injective (crossingAbscissa a b N η) := by
    intro m n h
    rw [crossingAbscissa, crossingAbscissa] at h
    field_simp at h
    have hq : (m : ℚ) = (n : ℚ) := by linarith
    exact_mod_cast hq
  rw [componentCrossings_eq_image hs, Set.ncard_image_of_injective _ hinj]
  simp

/-- The crossing of largest index is the largest crossing, which is the one `v_i` is read
off: the crossing of largest abscissa is the first one met following the component from its
east-step end back to its north-step end. -/
theorem le_crossingAbscissa_componentTopIndex (hs : 0 < 1 + sweepSlope a b N)
    (y : Heights a b N) (η : ℚ) (i : ℕ) {x : ℚ} (hx : x ∈ componentCrossings a b N y η i) :
    x ≤ crossingAbscissa a b N η (componentTopIndex a b N y η i) := by
  rw [componentCrossings_eq_image hs] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  exact crossingAbscissa_le hs η (Finset.mem_Icc.1 (by exact_mod_cast hn)).2

/-- **The crossing of largest index is itself a crossing**, whenever the component has any. With
`HJO.Mellit.le_crossingAbscissa_componentTopIndex` this says it is `max X_i(c)`, which is what
`HJO.Mellit.braidDataOfColouring` takes the fractional part of. -/
theorem mem_componentCrossings_componentTopIndex (hs : 0 < 1 + sweepSlope a b N)
    (y : Heights a b N) (η : ℚ) {i : ℕ}
    (hne : (componentCrossingIndices a b N y η i).Nonempty) :
    crossingAbscissa a b N η (componentTopIndex a b N y η i) ∈
      componentCrossings a b N y η i := by
  obtain ⟨n, hn⟩ := hne
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
  rw [componentCrossings_eq_image hs]
  exact ⟨componentTopIndex a b N y η i,
    Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨h1.trans h2, le_rfl⟩), rfl⟩

end HJO.Mellit
