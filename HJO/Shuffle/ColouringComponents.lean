/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidData
public import HJO.Shuffle.ColouringStep

/-! # The components of a colouring

A colouring is the set of steps of a path that the level line crosses; the *components* are the
intervals of the line between them. Pairing the `i`-th crossed north step with the `i`-th crossed
east step, in order of abscissa, gives the abscissa range `J_i(c)` of the `i`-th interval
`[a_i, b_i]` of an admissible colouring in the sense of Definition 4.1 of A. Mellit, *Toric braids
and `(m, n)`-parking functions*, arXiv:1604.07456 — and it is `J_i(c)` that
`HJO.Mellit.braidDataOfColouring` intersects with the antidiagonal to produce the special-braid
data.

## Main results

* `HJO.Mellit.levelIntercept` and `HJO.Mellit.abovePointRank_sub_level` — the level set
  `rk̂ = η` **is** the line `y = s_{a,b,N} x + η/(a(aN+1)N)`, as the identity
  `a(aN+1)N · (y - (s x + η/(a(aN+1)N))) = rk̂(x, y) - η` over `ℚ`. This is the dictionary the
  whole subsection is written in, and it is proved rather than asserted.
* `HJO.Mellit.colouringNorth`, `HJO.Mellit.colouringEast` — the two halves of
  `HJO.Mellit.colouring`, named.
* `HJO.Mellit.colouringComponent`.
* `HJO.Mellit.sweepSlope_mul_componentRight_add` — the right endpoint is where the level line
  reaches the ordinate of the `i`-th crossed east step, which is what the definition is for.

## Implementation notes

The colouring `c` is usually taken together with a witnessing above-diagonal path `P̂`, reading
the north/east split of `c` off `P̂`. Here the definition takes the path and the level directly, and
the colouring is `HJO.Mellit.colouring y η` — the same data, with the witness not left implicit.
Every lemma that uses the components has the witness in hand.

The components are usually indexed `1 ≤ i ≤ k`; here `i : ℕ` runs from `0`, and outside the range
the two lists are read with the junk default `(0, 0)`, so the component is the degenerate interval
`[0, -η/(s a(aN+1)N)]`. Nothing reads it there.

## References

The objects involved are `HJO.Mellit.colouringComponent`, `HJO.Mellit.sweepSlope`,
`HJO.Mellit.colouring`, `HJO.Mellit.eastSteps`, `HJO.Paths.northSteps`,
`HJO.ParkingFunctions.abovePointRank`, `HJO.Mellit.card_colouringNorth_eq_card_colouringEast`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The level line in rank coordinates -/

/-- The intercept `η / (a(aN+1)N)` of the level line `rk̂ = η`. -/
def levelIntercept (a N : ℕ) (η : ℚ) : ℚ := η / ((a : ℚ) * (a * N + 1) * N)

/-- **The level set of the above-diagonal rank is the line of slope `s_{a,b,N}` through the
intercept `η/(a(aN+1)N)`.** Scaled by `a(aN+1)N`, the vertical distance from `(x, w)` to the level
line is exactly `rk̂(x, w) - η`.

This is the sentence "the level set `rk̂ = η` is the line
`y = s_{a,b,N} x + η/(aM)`, since `M(ay - bx) + x = η` solves to `y = (b/a)x - x/(aM) + η/(aM)`",
as an identity of rational functions. It needs a rectangle with a column, the scaling factor being
the denominator of both `HJO.Mellit.sweepSlope` and `HJO.Mellit.levelIntercept`. -/
theorem abovePointRank_sub_level (ha : a ≠ 0) (hN : N ≠ 0) (η x w : ℚ) :
    ((a : ℚ) * (a * N + 1) * N) * (w - (sweepSlope a b N * x + levelIntercept a N η)) =
      (((a : ℚ) * N + 1) * N) * ((a : ℚ) * w - (b : ℚ) * x) + x - η := by
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.2 ha
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hM : ((a : ℚ) * N + 1) ≠ 0 := by positivity
  rw [sweepSlope, levelIntercept]
  field_simp
  ring

/-! ### The two halves of a colouring -/

/-- The crossed north steps of `y` at `η`: the first half of `HJO.Mellit.colouring`. -/
def colouringNorth (y : Heights a b N) (η : ℚ) : Finset (ℕ × ℕ) :=
  {u ∈ northSteps y | (pointRank a b N u : ℚ) < η ∧
    η < (pointRank a b N u : ℚ) + (attackWindow a N : ℚ)}

/-- The crossed east steps of `y` at `η`: the second half of `HJO.Mellit.colouring`. -/
def colouringEast (y : Heights a b N) (η : ℚ) : Finset (ℕ × ℕ) :=
  {v ∈ eastSteps y | (pointRank a b N (v.1 + 1, v.2) : ℚ) < η ∧ η < (pointRank a b N v : ℚ)}

/-- The colouring is the union of its two halves, which is `HJO.Mellit.colouring` verbatim. -/
theorem colouring_eq_union (y : Heights a b N) (η : ℚ) :
    colouring y η = colouringNorth y η ∪ colouringEast y η := rfl

/-- The two halves are disjoint: a north step `(s, i)` has `i < ŷ_{s+1}` and an east step at `s`
has ordinate exactly `ŷ_{s+1}`. -/
theorem disjoint_colouringNorth_colouringEast (y : Heights a b N) (η : ℚ) :
    Disjoint (colouringNorth y η) (colouringEast y η) := by
  refine Finset.disjoint_left.2 fun P hP hP' => ?_
  have h1 := (mem_northSteps_iff.1 (Finset.mem_filter.1 hP).1).2.2
  have h2 := (mem_eastSteps_iff.1 (Finset.mem_filter.1 hP').1).2
  omega

/-! ### Listing by column -/

/-- A finite set of lattice points listed in weakly increasing order of abscissa. The crossed north
steps are listed by column and the crossed east steps by abscissa, which is the order along the
level line: this is what makes the pairing by index in `HJO.Mellit.colouringComponent` the
pairing by position along the line.

Noncomputable only because `Finset.toList` is. -/
noncomputable def sortByColumn (s : Finset (ℕ × ℕ)) : List (ℕ × ℕ) :=
  s.toList.mergeSort fun P Q => decide (P.1 ≤ Q.1)

/-- The column listing of a finite set of lattice points is a permutation of it. -/
theorem sortByColumn_perm (s : Finset (ℕ × ℕ)) : (sortByColumn s).Perm s.toList :=
  List.mergeSort_perm _ _

/-- The column listing enumerates exactly the set. -/
theorem mem_sortByColumn {s : Finset (ℕ × ℕ)} {P : ℕ × ℕ} : P ∈ sortByColumn s ↔ P ∈ s := by
  rw [(sortByColumn_perm s).mem_iff, Finset.mem_toList]

/-- The column listing has no repetitions. -/
theorem sortByColumn_nodup (s : Finset (ℕ × ℕ)) : (sortByColumn s).Nodup :=
  ((sortByColumn_perm s).nodup_iff).2 s.nodup_toList

/-- The column listing has the length of the set. -/
theorem length_sortByColumn (s : Finset (ℕ × ℕ)) : (sortByColumn s).length = #s := by
  rw [(sortByColumn_perm s).length_eq, Finset.length_toList]

/-- **The column listing is sorted by abscissa**, which is what makes it the listing
`u_1, …, u_k` "in increasing order of column". -/
theorem sortByColumn_pairwise (s : Finset (ℕ × ℕ)) :
    (sortByColumn s).Pairwise fun P Q => P.1 ≤ Q.1 := by
  refine (List.pairwise_mergeSort (fun P Q R hPQ hQR => ?_) (fun P Q => ?_) s.toList).imp ?_
  · exact decide_eq_true ((of_decide_eq_true hPQ).trans (of_decide_eq_true hQR))
  · rcases le_total P.1 Q.1 with h | h
    · simp [h]
    · simp [h]
  · exact fun h => of_decide_eq_true h

/-! ### The components -/

/-- The left endpoint of the `i`-th component: the column of the `i`-th crossed north step, which
is the abscissa at which the level line crosses it. -/
noncomputable def componentLeft (y : Heights a b N) (η : ℚ) (i : ℕ) : ℚ :=
  (((sortByColumn (colouringNorth y η)).getD i (0, 0)).1 : ℚ)

/-- The right endpoint of the `i`-th component: the abscissa at which the level line reaches the
ordinate of the `i`-th crossed east step. -/
noncomputable def componentRight (a b N : ℕ) (y : Heights a b N) (η : ℚ) (i : ℕ) : ℚ :=
  ((((sortByColumn (colouringEast y η)).getD i (0, 0)).2 : ℚ) - levelIntercept a N η) /
    sweepSlope a b N

/-- **The `i`-th component of a colouring.** `HJO.Mellit.colouringComponent`: with
`u_1, …, u_k` the crossed north steps in increasing order of column and `w_1, …, w_k` the crossed
east steps in increasing order of abscissa,
`J_i(c) = [x(u_i), (y(w_i) - η/(a(aN+1)N)) / s_{a,b,N}]`.

The two lists have the same length by `HJO.Mellit.card_colouringNorth_eq_card_colouringEast`. The
left end is the abscissa of the crossing of `u_i`, which is its column, and the right end is the
abscissa at which the level line reaches the ordinate of `w_i` —
`HJO.Mellit.sweepSlope_mul_componentRight_add`. Pairing by index is pairing by position along the
line.

Indexed from `0`, where the components are usually indexed from `1`; off the range the lists are
read with the junk default `(0, 0)`. -/
@[hjo "def_braid_colouring_interval"]
noncomputable def colouringComponent (a b N : ℕ) (y : Heights a b N) (η : ℚ) (i : ℕ) : Set ℚ :=
  Set.Icc (componentLeft y η i) (componentRight a b N y η i)

/-- **The right endpoint is on the level line at the ordinate of the `i`-th crossed east step.**
This is what `HJO.Mellit.componentRight` is solving for, and it is the only content of the division
by the slope. Stated where the slope is nonzero, which for `0 < a`, `0 < b` and `0 < N` it is. -/
theorem sweepSlope_mul_componentRight_add (hs : sweepSlope a b N ≠ 0)
    (y : Heights a b N) (η : ℚ) (i : ℕ) :
    sweepSlope a b N * componentRight a b N y η i + levelIntercept a N η =
      ((((sortByColumn (colouringEast y η)).getD i (0, 0)).2 : ℚ)) := by
  rw [componentRight, mul_div_cancel₀ _ hs]
  ring

/-- The left endpoint is the column of the `i`-th crossed north step, as a natural number. -/
theorem componentLeft_eq (y : Heights a b N) (η : ℚ) (i : ℕ) :
    componentLeft y η i = (((sortByColumn (colouringNorth y η)).getD i (0, 0)).1 : ℚ) := rfl

/-- The `i`-th component is a nonempty interval exactly when its right endpoint is not to the left
of its column; `Set.Icc` is empty otherwise, so no lemma can read a reversed interval as a
component. -/
theorem colouringComponent_nonempty_iff (y : Heights a b N) (η : ℚ) (i : ℕ) :
    (colouringComponent a b N y η i).Nonempty ↔
      componentLeft y η i ≤ componentRight a b N y η i :=
  Set.nonempty_Icc

end HJO.Mellit
