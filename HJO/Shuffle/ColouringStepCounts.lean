/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ColouringComponents

/-! # A colouring has as many east steps as north steps

The usual proof is geometric: the part of the level line lying between the diagonal and
the path is a finite union of closed intervals, each beginning at a north-step crossing and ending
at an east-step crossing, so the two counts are the number of intervals.

**That is not the argument here, and the replacement is cheaper and needs less.** Walk along the
path. The rank rises by the attack window `ω` at each north step and falls by `(aN+1)Nb - 1` at
each east step; a crossed north step is a step that carries the rank *up* past `η` and a crossed
east step is one that carries it *down* past `η`. A sequence that starts below `η` and ends below
`η` crosses upwards exactly as often as it crosses downwards — and the path starts at
`rk̂(0,0) = 0` and ends at `rk̂(aN, bN) = aN`, both below `η` because `η > aN`. So the identity is a
telescoping sum of indicator functions, with no intervals, no real line and no continuity.

## Main results

* `HJO.Mellit.card_colouringNorth_eq_card_colouringEast` — the main
  result.
* `HJO.Mellit.card_crossing_Ico` — the crossing count of a monotone integer sequence over a range
  is the difference of the two endpoint indicators. This is the whole content, and it is stated for
  an arbitrary monotone sequence missing `η`.

## Implementation notes

`0 < b` and `0 < N` are carried explicitly; the standing hypothesis of the setting is `1 < a < b`.
They are used only to know that an east step lowers the rank, `(aN+1)Nb ≥ 1`. `0 < a` is *not*
needed.

Admissibility of the level is used exactly where the geometric proof uses "neither kind of endpoint
is a lattice point": a rank equal to `η` would be a crossing counted by neither indicator.

## References

Declarations involved: `HJO.Mellit.card_colouringNorth_eq_card_colouringEast`,
`HJO.Mellit.colouring`, `HJO.Mellit.eastSteps`, `HJO.Paths.northSteps`,
`HJO.ParkingFunctions.abovePointRank`, `HJO.Paths.attackWindow`, `HJO.Mellit.IsAdmissibleLevel`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### Arithmetic of the rank along a path -/

/-- No lattice point at all has rank an admissible level. This is
`HJO.Mellit.pointRank_ne_of_isAdmissibleLevel` with the inert bounds dropped, so that it
applies to the ordinates swept through inside a column without a side condition. -/
theorem cast_pointRank_ne_of_isAdmissibleLevel {η : ℚ} (hη : IsAdmissibleLevel η) (a b N : ℕ)
    (P : ℕ × ℕ) : ((pointRank a b N P : ℤ) : ℚ) ≠ η := by
  obtain ⟨n, rfl⟩ := hη
  intro h
  have h2 : ((2 * pointRank a b N P : ℤ) : ℚ) = ((2 * n + 1 : ℤ) : ℚ) := by
    push_cast
    linarith
  have h3 : 2 * pointRank a b N P = 2 * n + 1 := by exact_mod_cast h2
  omega

/-- The rank rises with the ordinate: `rk̂(x, j) - rk̂(x, i) = (aN+1)Na(j - i)`. -/
theorem pointRank_sub_pointRank_snd (a b N x i j : ℕ) :
    pointRank a b N (x, j) - pointRank a b N (x, i) =
      (((a * N + 1) * N : ℕ) : ℤ) * a * ((j : ℤ) - i) := by
  simp only [pointRank, abovePointRank]
  push_cast
  ring

/-- The rank is monotone in the ordinate. -/
theorem pointRank_mono_snd (a b N x : ℕ) {i j : ℕ} (h : i ≤ j) :
    pointRank a b N (x, i) ≤ pointRank a b N (x, j) := by
  have hij : (0 : ℤ) ≤ (j : ℤ) - i := by
    have : (i : ℤ) ≤ j := by exact_mod_cast h
    linarith
  have := pointRank_sub_pointRank_snd a b N x i j
  nlinarith [Int.natCast_nonneg ((a * N + 1) * N), Int.natCast_nonneg a,
    mul_nonneg (mul_nonneg (Int.natCast_nonneg ((a * N + 1) * N)) (Int.natCast_nonneg a)) hij]

/-- An east step lowers the rank by `(aN+1)Nb - 1`. -/
theorem pointRank_sub_pointRank_fst (a b N x h : ℕ) :
    pointRank a b N (x, h) - pointRank a b N (x + 1, h) =
      (((a * N + 1) * N * b : ℕ) : ℤ) - 1 := by
  simp only [pointRank, abovePointRank]
  push_cast
  ring

/-- On a rectangle with a row and a column an east step does not raise the rank. -/
theorem pointRank_succ_fst_le (hb : 0 < b) (hN : 0 < N) (a x h : ℕ) :
    pointRank a b N (x + 1, h) ≤ pointRank a b N (x, h) := by
  have hpos : 1 ≤ (((a * N + 1) * N * b : ℕ) : ℤ) := by
    have : 1 ≤ (a * N + 1) * N * b := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have := pointRank_sub_pointRank_fst a b N x h
  omega

/-- The rank at the origin is `0`. -/
theorem pointRank_zero_zero (a b N : ℕ) : pointRank a b N (0, 0) = 0 := by
  simp [pointRank, abovePointRank]

/-- The rank at the far corner is `aN`. -/
theorem pointRank_corner (a b N : ℕ) : pointRank a b N (a * N, b * N) = (a * N : ℕ) := by
  simp only [pointRank, abovePointRank]
  push_cast
  ring

/-! ### Counting crossings of a monotone integer sequence -/

/-- **The indicator of a crossing is the difference of the two endpoint indicators.** For
`A ≤ B` with `A ≠ η`, the interval `(A, B)` contains `η` exactly when `B` is above `η` and `A` is
not. The hypothesis `A ≠ η` is where admissibility of the level is spent: at `A = η` the step
carries the rank past the level without either endpoint recording it. -/
theorem indicator_between {A B : ℤ} {η : ℚ} (hAB : A ≤ B) (hA : ((A : ℤ) : ℚ) ≠ η) :
    (if ((A : ℤ) : ℚ) < η ∧ η < ((B : ℤ) : ℚ) then (1 : ℤ) else 0) =
      (if η < ((B : ℤ) : ℚ) then 1 else 0) - (if η < ((A : ℤ) : ℚ) then 1 else 0) := by
  have hABQ : ((A : ℤ) : ℚ) ≤ ((B : ℤ) : ℚ) := by exact_mod_cast hAB
  rcases lt_or_ge ((A : ℤ) : ℚ) η with h1 | h1
  · rcases lt_or_ge η ((B : ℤ) : ℚ) with h2 | h2
    · simp [h1, h2, not_lt.2 h1.le]
    · simp [h1, not_lt.2 h2, not_lt.2 h1.le]
  · have h1' : η < ((A : ℤ) : ℚ) := lt_of_le_of_ne h1 (Ne.symm hA)
    have h2 : η < ((B : ℤ) : ℚ) := h1'.trans_le hABQ
    simp [h1', h2, not_lt.2 h1]

/-- **The number of upward crossings of a monotone integer sequence over a range is the difference
of its endpoint indicators.** This is the arithmetic heart of the identity, and it knows nothing
about paths: the intervals `(t_i, t_{i+1})` for `lo ≤ i < hi` cover `(t_lo, t_hi)` apart from the
integers `t_i`, which `η` misses. -/
theorem card_crossing_Ico {t : ℕ → ℤ} {η : ℚ} (hmono : ∀ i, t i ≤ t (i + 1))
    (hne : ∀ i, ((t i : ℤ) : ℚ) ≠ η) (lo : ℕ) :
    ∀ hi : ℕ, lo ≤ hi →
      (#{i ∈ Finset.Ico lo hi | ((t i : ℤ) : ℚ) < η ∧ η < ((t (i + 1) : ℤ) : ℚ)} : ℤ) =
        (if η < ((t hi : ℤ) : ℚ) then 1 else 0) - (if η < ((t lo : ℤ) : ℚ) then 1 else 0) := by
  intro hi hle
  induction hi, hle using Nat.le_induction with
  | base => simp
  | succ hi hle ih =>
    have hins : Finset.Ico lo (hi + 1) = insert hi (Finset.Ico lo hi) :=
      Nat.Ico_succ_right_eq_insert_Ico hle
    have hnot : hi ∉ Finset.Ico lo hi := by simp
    have hstep := indicator_between (hmono hi) (hne hi)
    have hcard :
        (#{i ∈ insert hi (Finset.Ico lo hi) |
            ((t i : ℤ) : ℚ) < η ∧ η < ((t (i + 1) : ℤ) : ℚ)} : ℤ) =
          (#{i ∈ Finset.Ico lo hi | ((t i : ℤ) : ℚ) < η ∧ η < ((t (i + 1) : ℤ) : ℚ)} : ℤ) +
            (if ((t hi : ℤ) : ℚ) < η ∧ η < ((t (hi + 1) : ℤ) : ℚ) then (1 : ℤ) else 0) := by
      by_cases hc : ((t hi : ℤ) : ℚ) < η ∧ η < ((t (hi + 1) : ℤ) : ℚ)
      · simp [Finset.filter_insert, hc,
          Finset.card_insert_of_notMem (fun hm => hnot (Finset.mem_filter.1 hm).1)]
      · simp [Finset.filter_insert, hc]
    rw [hins, hcard, ih, hstep]
    ring

/-! ### The two counts -/

/-- The crossed north steps, sorted into their columns: in column `x` they are the ordinates `i`
with `ŷ_x ≤ i < ŷ_{x+1}` at which the rank crosses `η`, written with `rk̂(x, i+1)` in place of
`rk̂(x, i) + ω`. -/
theorem colouringNorth_eq_biUnion (y : Heights a b N) (η : ℚ) :
    colouringNorth y η = (Finset.range (a * N)).biUnion fun x =>
      {x} ×ˢ {i ∈ Finset.Ico (ht y x) (ht y (x + 1)) |
        ((pointRank a b N (x, i) : ℤ) : ℚ) < η ∧
          η < ((pointRank a b N (x, i + 1) : ℤ) : ℚ)} := by
  have hsucc : ∀ x i : ℕ, pointRank a b N (x, i + 1) =
      pointRank a b N (x, i) + (attackWindow a N : ℤ) := fun x i =>
    abovePointRank_succ a b N x i
  ext P
  obtain ⟨x, i⟩ := P
  simp only [colouringNorth, Finset.mem_filter, mem_northSteps_iff, Finset.mem_biUnion,
    Finset.mem_range, Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico, hsucc]
  push_cast
  tauto

/-- The count of crossed north steps, column by column. -/
theorem card_colouringNorth (y : Heights a b N) (η : ℚ) :
    #(colouringNorth y η) = ∑ x ∈ Finset.range (a * N),
      #{i ∈ Finset.Ico (ht y x) (ht y (x + 1)) |
        ((pointRank a b N (x, i) : ℤ) : ℚ) < η ∧
          η < ((pointRank a b N (x, i + 1) : ℤ) : ℚ)} := by
  rw [colouringNorth_eq_biUnion, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun x _ => by
      rw [Finset.card_product, Finset.card_singleton, one_mul]
  · intro x _ x' _ hne
    refine Finset.disjoint_left.2 fun P hP hP' => hne ?_
    rw [Finset.mem_product, Finset.mem_singleton] at hP hP'
    rw [← hP.1, ← hP'.1]

/-- The crossed east steps are indexed by their columns. -/
theorem colouringEast_eq_image (y : Heights a b N) (η : ℚ) :
    colouringEast y η =
      ({x ∈ Finset.range (a * N) |
        ((pointRank a b N (x + 1, ht y (x + 1)) : ℤ) : ℚ) < η ∧
          η < ((pointRank a b N (x, ht y (x + 1)) : ℤ) : ℚ)}).image
        fun x => (x, ht y (x + 1)) := by
  ext P
  obtain ⟨x, i⟩ := P
  simp only [colouringEast, Finset.mem_filter, mem_eastSteps_iff, Finset.mem_image,
    Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    subst h2
    exact ⟨x, ⟨h1, h3, h4⟩, rfl, rfl⟩
  · rintro ⟨x', ⟨hx', h3, h4⟩, rfl, rfl⟩
    exact ⟨⟨hx', rfl⟩, h3, h4⟩

/-- The count of crossed east steps, column by column. -/
theorem card_colouringEast (y : Heights a b N) (η : ℚ) :
    #(colouringEast y η) = ∑ x ∈ Finset.range (a * N),
      if ((pointRank a b N (x + 1, ht y (x + 1)) : ℤ) : ℚ) < η ∧
          η < ((pointRank a b N (x, ht y (x + 1)) : ℤ) : ℚ) then 1 else 0 := by
  rw [colouringEast_eq_image, Finset.card_image_of_injOn, Finset.card_filter]
  intro x _ x' _ h
  exact (Prod.mk.injEq .. ▸ h : x = x' ∧ _).1

/-! ### The two halves are the two counts -/

/-- A north step is never an east step: a north step `(s, i)` has `i < ŷ_{s+1}` and an east step at
`s` has ordinate exactly `ŷ_{s+1}`. -/
theorem disjoint_northSteps_eastSteps (y : Heights a b N) :
    Disjoint (northSteps y) (eastSteps y) := by
  refine Finset.disjoint_left.2 fun P hP hP' => ?_
  have h1 := (mem_northSteps_iff.1 hP).2.2
  have h2 := (mem_eastSteps_iff.1 hP').2
  omega

/-- **The members of the colouring that are north steps of the path are exactly
`HJO.Mellit.colouringNorth`**, which is what makes the identity below a count. -/
theorem colouring_inter_northSteps (y : Heights a b N) (η : ℚ) :
    colouring y η ∩ northSteps y = colouringNorth y η := by
  ext P
  simp only [colouring_eq_union, Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hN⟩
    · exact h
    · exact absurd hN (Finset.disjoint_right.1 (disjoint_northSteps_eastSteps y)
        (Finset.mem_filter.1 h).1)
  · intro h
    exact ⟨Or.inl h, (Finset.mem_filter.1 h).1⟩

/-- **The members of the colouring that are east steps of the path are exactly
`HJO.Mellit.colouringEast`.** -/
theorem colouring_inter_eastSteps (y : Heights a b N) (η : ℚ) :
    colouring y η ∩ eastSteps y = colouringEast y η := by
  ext P
  simp only [colouring_eq_union, Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hE⟩
    · exact absurd hE (Finset.disjoint_left.1 (disjoint_northSteps_eastSteps y)
        (Finset.mem_filter.1 h).1)
    · exact h
  · intro h
    exact ⟨Or.inr h, (Finset.mem_filter.1 h).1⟩

/-! ### The identity -/

/-- **A colouring has as many east steps as north steps.** This is
`HJO.Mellit.card_colouringNorth_eq_card_colouringEast`, proved by the crossing count rather than by
the interval decomposition: the rank along the path starts at `0` and ends at `aN`, both below `η`,
so the upward crossings — the crossed north steps — and the downward crossings — the crossed east
steps — are equally many.

The hypotheses are `0 < b`, `0 < N`, `η` admissible, `η > aN` and `P̂` above-diagonal; `0 < a` is
not needed. -/
@[hjo "lem_colouring_step_counts"]
theorem card_colouringNorth_eq_card_colouringEast (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) : #(colouringNorth y η) = #(colouringEast y η) := by
  classical
  set u : ℕ → ℤ := fun r =>
    if η < ((pointRank a b N (r, ht y r) : ℤ) : ℚ) then 1 else 0 with hudef
  set w : ℕ → ℤ := fun x =>
    if η < ((pointRank a b N (x, ht y (x + 1)) : ℤ) : ℚ) then 1 else 0 with hwdef
  -- the north count, column by column
  have hnorth : (#(colouringNorth y η) : ℤ) = ∑ x ∈ Finset.range (a * N), (w x - u x) := by
    rw [card_colouringNorth]
    push_cast
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxlt : x < a * N := Finset.mem_range.1 hx
    have hmono : ht y x ≤ ht y (x + 1) := hy.2.2.1 x hxlt
    rw [card_crossing_Ico (t := fun i => pointRank a b N (x, i))
      (fun i => pointRank_mono_snd a b N x (Nat.le_succ i))
      (fun i => cast_pointRank_ne_of_isAdmissibleLevel hη a b N (x, i)) (ht y x) (ht y (x + 1))
      hmono]
  -- the east count, column by column
  have heast : (#(colouringEast y η) : ℤ) = ∑ x ∈ Finset.range (a * N), (w x - u (x + 1)) := by
    rw [card_colouringEast]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    exact indicator_between (pointRank_succ_fst_le hb hN a x (ht y (x + 1)))
      (cast_pointRank_ne_of_isAdmissibleLevel hη a b N (x + 1, ht y (x + 1)))
  -- the two ends of the path are below the level
  have hu0 : u 0 = 0 := by
    have h : pointRank a b N (0, ht y 0) = 0 := by rw [hy.1]; exact pointRank_zero_zero a b N
    have : ¬ η < ((pointRank a b N (0, ht y 0) : ℤ) : ℚ) := by
      rw [h]
      push_cast
      have : (0 : ℚ) ≤ ((a * N : ℕ) : ℚ) := Nat.cast_nonneg _
      linarith
    simp [hudef, this]
  have huN : u (a * N) = 0 := by
    have h : pointRank a b N (a * N, ht y (a * N)) = ((a * N : ℕ) : ℤ) := by
      rw [hy.2.1]; exact pointRank_corner a b N
    have : ¬ η < ((pointRank a b N (a * N, ht y (a * N)) : ℤ) : ℚ) := by
      rw [h]
      push_cast
      push_cast at hηa
      linarith
    simp [hudef, this]
  have htel : ∑ x ∈ Finset.range (a * N), (u (x + 1) - u x) = u (a * N) - u 0 :=
    Finset.sum_range_sub u (a * N)
  have hdiff : (#(colouringNorth y η) : ℤ) - #(colouringEast y η) = 0 := by
    rw [hnorth, heast, ← Finset.sum_sub_distrib]
    simp only [sub_sub_sub_cancel_left]
    rw [htel, hu0, huN, sub_zero]
  omega

/-! ### The identity, checked on the example

The `(2,3)`-path of heights `(0,2,3)` at `η = 21/2` is the path
`HJO.Mellit.colouring_east_steps_not_determined` computes the colouring of. Its colouring is
`{(0,1), (0,2)}`, one crossed north step and one crossed east step, so the identity reads
`1 = 1` there. -/

/-- The two halves of the example colouring, computed. -/
theorem colouringNorth_and_colouringEast_example :
    colouringNorth (![0, 2, 3] : Heights 2 3 1) (21 / 2) = {(0, 1)} ∧
      colouringEast (![0, 2, 3] : Heights 2 3 1) (21 / 2) = {(0, 2)} := by
  constructor
  · have hn : northSteps (![0, 2, 3] : Heights 2 3 1) = {(0, 0), (0, 1), (1, 2)} := by decide
    rw [colouringNorth, hn]
    norm_num [pointRank, abovePointRank, attackWindow, Finset.filter_insert,
      Finset.filter_singleton]
  · have he : eastSteps (![0, 2, 3] : Heights 2 3 1) = {(0, 2), (1, 3)} := by decide
    rw [colouringEast, he]
    norm_num [pointRank, abovePointRank, attackWindow, Finset.filter_insert,
      Finset.filter_singleton]

end HJO.Mellit
