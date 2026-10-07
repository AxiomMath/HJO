/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendWidth
public import HJO.Shuffle.SweepAppendBandInterleave
public meta import HJO.Attr

/-!
# The band word IS grouped into rounds, and each round is a tail layer then a base layer

`HJO.Mellit.sweepAppend_of_forall_band_uniform` reduces `HJO.Mellit.SweepAppend` to a single band
identity. A natural plan for it is the *round-grouping*: cut the band word at every level of
diagonal excess and argue one level at a time. `HJO.Mellit.partialSweepWord_eq_bandSweepWord_mul`
cuts at **one** threshold only, and `HJO/Shuffle/SweepAppendBandInterleave.lean` counts the two
coupling windows without ever factorising the word. This file supplies the grouping itself.

## The grouping

* `HJO.Mellit.roundSweepWord` is one round: the events of a fixed diagonal excess `e`, in the order
  the sweep applies them.
* `HJO.Mellit.bandSweepWord_succ` is the recursion `Band_{d+1} = Band_d · Round_{d+1}`, the round of
  highest excess standing rightmost and so applied first.
* `HJO.Mellit.bandSweepWord_eq_prod_roundSweepWord` is the closed form: the band word to threshold
  `D` is `Round_0 · Round_1 ⋯ Round_D`, with **no** hypothesis beyond `0 < a` and `0 < M` — in
  particular none on `q`, on `u`, on coprimality, or on the path.
* `HJO.Mellit.roundSweepWord_split_fst` splits one round at an abscissa. Inside a level the rank
  order *is* the order of abscissae (`HJO.Mellit.abovePointRank_le_iff`: the rank is lexicographic
  in `(ay - bx, x)` and the first coordinate is now constant), so the cut is clean and needs nothing
  about the two paths.

## What the grouping buys at an extension, and it is sharper than the pointwise statement

At `c = aN` the split of `HJO.Mellit.roundSweepWord_split_fst` is the band interleaving: the tail's
points of a round are swept first, the base's after them. Two facts then make the round, and not the
point, the right unit.

* **The width shift is constant on a round.** `HJO.Paths.sweepWidth_appendHeights_eq` shifts the
  width at a base point `P` by `#(tailLiveSteps w (diagExcess a b P))`, and on a round that argument
  is the constant `e`. So the base layer of round `e` is read at widths raised by **one integer**,
  `#(tailLiveSteps w e)`, uniformly over the layer:
  `HJO.Mellit.sweepWidth_appendHeights_of_diagExcess_eq` and
  `HJO.Mellit.sweepRight_appendHeights_of_diagExcess_eq`.
* **The base layer is read on the base's own list, in the base's own order.**
  `HJO.Mellit.baseRoundList_appendHeights` identifies the index set with the base's own round set
  and `HJO.Mellit.baseRoundWord_appendHeights` transports the listing into the base's rectangle. So
  the only thing about the base layer that is not the base's own data is the operator, and that
  differs from the base's by the one integer above.

## What it does not buy

The residual obligation is untouched, and is not combinatorial. Moving the base layer of round `e`
back to the base's own widths needs `d_+`, `d_-` and `Δ` at index `k + δ_e` related to the same
operators at index `k`, and the comparisons
(`HJO.Sweep.dminus_eq_of_mem_piece`, `HJO.Sweep.dplus_succ_eq_dplus_add`,
`HJO.Sweep.corner_transport_split_prefix`) all read a **graded piece of the incoming vector**, which
no count of lattice points can supply. Concretely `HJO.Sweep.dminus_eq_of_mem_piece` is useful only
on `V_{k-1}`, whereas the vector arriving at a base event of the extension carries the `δ_e`
variables the tail's live north steps opened; and `HJO.Sweep.dplus_succ_eq_dplus_add` pays one
Demazure term per unit of shift. Rounds make the shift one integer instead of one integer per point;
they do not make it free.

Nor does the grouping shorten the induction. The number of rounds is `a·bA + 1`, fixed by the
appended part alone, but the *contents* of a round vary with the tail: `δ_e` is a function of the
tail (`HJO.Paths.card_liveSteps_high_appendHeights_ne`), so the sum over the fibre cannot be taken
round by round.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep HJO.Paths Finset ParkingFunctions

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b M : ℕ}

/-! ### A swept point has nonnegative diagonal excess -/

/-- **The diagonal excess of a swept point is nonnegative.** This is the middle clause
`b·x ≤ a·y` of `HJO.Paths.mem_sweptRegion`, which is what `HJO.Paths.sweptRegion` means by "weakly
above the diagonal", read in the coordinates of `HJO.Paths.diagExcess`. No above-diagonality of the
path enters: the condition is on the point. -/
theorem diagExcess_nonneg_of_mem_sweptRegion {y : Heights a b M} {P : ℕ × ℕ}
    (hP : P ∈ sweptRegion y) : 0 ≤ diagExcess a b P := by
  have h := (mem_sweptRegion.1 hP).2.1
  have h' : (b : ℤ) * P.1 ≤ (a : ℤ) * P.2 := by exact_mod_cast h
  rw [diagExcess]
  omega

/-! ### One round of the band -/

/-- **One round of the band word**: the events of a fixed diagonal excess `e`, in the order the
sweep applies them. Inside a round the rank order is the order of abscissae, the excess being
constant.

`HJO.Mellit.bandSweepWord` is the product of the rounds of excess at most its threshold
(`HJO.Mellit.bandSweepWord_eq_prod_roundSweepWord`). -/
@[hjo "lem_sweep_band_rounds"]
noncomputable def roundSweepWord (q u : L) {a b M : ℕ} (y : Heights a b M) (η : ℚ) (e : ℤ) :
    Module.End L (Total L) :=
  ((sortByRank a b M {P ∈ sweptAbove y η | diagExcess a b P = e}).map (sweepOperator q u y)).prod

/-- **Below the diagonal there are no rounds.** With `HJO.Mellit.bandSweepWord_of_neg` this is the
base of the induction that groups the band into rounds. -/
theorem roundSweepWord_of_neg (q u : L) (y : Heights a b M) (η : ℚ) {e : ℤ} (he : e < 0) :
    roundSweepWord q u y η e = 1 := by
  have hempty : {P ∈ sweptAbove y η | diagExcess a b P = e} = (∅ : Finset (ℕ × ℕ)) :=
    Finset.filter_eq_empty_iff.2 fun {P} hP hcon => by
      have := diagExcess_nonneg_of_mem_sweptRegion (Finset.mem_filter.1 hP).1
      omega
  rw [roundSweepWord, hempty, sortByRank_empty, List.map_nil, List.prod_nil]

/-- **A band whose threshold is under the diagonal is empty.** -/
theorem bandSweepWord_of_neg (q u : L) (y : Heights a b M) (η : ℚ) {d : ℤ} (hd : d < 0) :
    bandSweepWord q u y η d = 1 := by
  have hempty : {P ∈ sweptAbove y η | diagExcess a b P ≤ d} = (∅ : Finset (ℕ × ℕ)) :=
    Finset.filter_eq_empty_iff.2 fun {P} hP hcon => by
      have := diagExcess_nonneg_of_mem_sweptRegion (Finset.mem_filter.1 hP).1
      omega
  rw [bandSweepWord, hempty, sortByRank_empty, List.map_nil, List.prod_nil]

/-! ### The recursion that groups the band into rounds -/

/-- Splitting a band index set into the band one level lower and the top round. -/
theorem filter_le_union_filter_eq (y : Heights a b M) (η : ℚ) (d : ℤ) :
    {P ∈ sweptAbove y η | diagExcess a b P ≤ d} ∪ {P ∈ sweptAbove y η | diagExcess a b P = d + 1}
      = {P ∈ sweptAbove y η | diagExcess a b P ≤ d + 1} := by
  ext P
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨h, hd⟩ | ⟨h, hd⟩) <;> exact ⟨h, by omega⟩
  · rintro ⟨h, hd⟩
    rcases le_or_gt (diagExcess a b P) d with hle | hgt
    · exact Or.inl ⟨h, hle⟩
    · exact Or.inr ⟨h, by omega⟩

/-- **The band word grows by one round.** `Band_{d+1} = Band_d · Round_{d+1}`: the new round stands
**rightmost**, hence is applied first, the sweep running inwards from high excess to the diagonal.

The rank order on the strip is lexicographic in `(ay - bx, x)` with the excess deciding first
(`HJO.Mellit.abovePointRank_le_iff`), so every point of the lower band is outranked by every point
of the top round and `HJO.Mellit.sortByRank_union` cuts the listing exactly there. -/
theorem bandSweepWord_succ (ha : 0 < a) (hM : 0 < M) (q u : L) (y : Heights a b M) (η : ℚ)
    (d : ℤ) :
    bandSweepWord q u y η (d + 1) = bandSweepWord q u y η d * roundSweepWord q u y η (d + 1) := by
  have hlist : sortByRank a b M {P ∈ sweptAbove y η | diagExcess a b P ≤ d + 1}
      = sortByRank a b M {P ∈ sweptAbove y η | diagExcess a b P ≤ d}
        ++ sortByRank a b M {P ∈ sweptAbove y η | diagExcess a b P = d + 1} := by
    conv_lhs => rw [← filter_le_union_filter_eq y η d]
    refine sortByRank_union (y := y) ha ?_ ?_ ?_
    · rw [filter_le_union_filter_eq y η d]
      exact fun P hP => (Finset.mem_filter.1 (Finset.mem_filter.1 hP).1).1
    · rw [Finset.disjoint_left]
      intro P hP hP'
      have h1 := (Finset.mem_filter.1 hP).2
      have h2 := (Finset.mem_filter.1 hP').2
      omega
    · intro P hP Q hQ
      have hPs : P ∈ sweptAbove y η := (Finset.mem_filter.1 hP).1
      have hQs : Q ∈ sweptAbove y η := (Finset.mem_filter.1 hQ).1
      have hP1 : P.1 ≤ a * M := (mem_sweptRegion.1 (Finset.mem_filter.1 hPs).1).1
      have hQ1 : Q.1 ≤ a * M := (mem_sweptRegion.1 (Finset.mem_filter.1 hQs).1).1
      have hlow := (Finset.mem_filter.1 hP).2
      have hhigh := (Finset.mem_filter.1 hQ).2
      have hkey : ¬ (pointRank a b M Q ≤ pointRank a b M P) := by
        rw [pointRank, pointRank, abovePointRank_le_iff hM hQ1 hP1]
        simp only [diagExcess] at hlow hhigh
        push Not
        refine ⟨by omega, fun h => absurd h (by omega)⟩
      omega
  rw [bandSweepWord, hlist, List.map_append, List.prod_append, bandSweepWord, roundSweepWord]

/-- **At the diagonal the band is a single round.** Every swept point has nonnegative excess
(`HJO.Mellit.diagExcess_nonneg_of_mem_sweptRegion`), so `≤ 0` and `= 0` select the same points. -/
theorem bandSweepWord_zero (q u : L) (y : Heights a b M) (η : ℚ) :
    bandSweepWord q u y η 0 = roundSweepWord q u y η 0 := by
  have hset : {P ∈ sweptAbove y η | diagExcess a b P ≤ 0}
      = {P ∈ sweptAbove y η | diagExcess a b P = 0} := by
    refine Finset.filter_congr fun P hP => ?_
    have := diagExcess_nonneg_of_mem_sweptRegion (Finset.mem_filter.1 hP).1
    omega
  rw [bandSweepWord, hset, roundSweepWord]

/-- **THE ROUND GROUPING.** The band word to threshold `D` is the product of its rounds,
`Round_0 · Round_1 ⋯ Round_D`, the round of highest excess rightmost and so applied first.

No hypothesis beyond `0 < a` and `0 < M`: nothing on `q`, nothing on `u`, no coprimality, and
nothing about the path beyond its being a height vector of the rectangle. So the grouping named as
the plan for `HJO.Mellit.sweepAppend_of_forall_band_uniform` exists unconditionally; what it does
not do is say what a round is worth. -/
@[hjo "lem_sweep_band_rounds"]
theorem bandSweepWord_eq_prod_roundSweepWord (ha : 0 < a) (hM : 0 < M) (q u : L)
    (y : Heights a b M) (η : ℚ) (D : ℕ) :
    bandSweepWord q u y η (D : ℤ)
      = (((List.range (D + 1)).map (fun e : ℕ => roundSweepWord q u y η (e : ℤ))).prod) := by
  induction D with
  | zero =>
    rw [List.range_succ, List.range_zero]
    simpa using bandSweepWord_zero q u y η
  | succ n ih =>
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [hcast, bandSweepWord_succ ha hM q u y η (n : ℤ), ih,
      show n + 1 + 1 = (n + 1) + 1 from rfl, List.range_succ (n := n + 1), List.map_append,
      List.prod_append]
    simp

/-! ### Splitting one round at an abscissa: the band interleaving as a factorisation -/

/-- Splitting a round's index set at an abscissa. -/
theorem filter_lt_union_filter_le_fst (y : Heights a b M) (η : ℚ) (e : ℤ) (c : ℕ) :
    {P ∈ sweptAbove y η | diagExcess a b P = e ∧ P.1 < c}
        ∪ {P ∈ sweptAbove y η | diagExcess a b P = e ∧ c ≤ P.1}
      = {P ∈ sweptAbove y η | diagExcess a b P = e} := by
  ext P
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨h, he, -⟩ | ⟨h, he, -⟩) <;> exact ⟨h, he⟩
  · rintro ⟨h, he⟩
    rcases Nat.lt_or_ge P.1 c with hlt | hge
    · exact Or.inl ⟨h, he, hlt⟩
    · exact Or.inr ⟨h, he, hge⟩

/-- **One round splits at an abscissa**, the low-abscissa layer standing **leftmost** and so applied
**last**.

Inside a round the diagonal excess is constant, so the lexicographic order of
`HJO.Mellit.abovePointRank_le_iff` reduces to the order of abscissae and the cut is exact. At
`c = aN` this is the band interleaving of `HJO/Shuffle/SweepAppendBandInterleave.lean` as a
factorisation of the word rather than a count: the tail's points of the round are swept first, the
base's after them. -/
@[hjo "lem_sweep_band_rounds"]
theorem roundSweepWord_split_fst (ha : 0 < a) (hM : 0 < M) (q u : L) (y : Heights a b M) (η : ℚ)
    (e : ℤ) (c : ℕ) :
    roundSweepWord q u y η e
      = ((sortByRank a b M {P ∈ sweptAbove y η | diagExcess a b P = e ∧ P.1 < c}).map
            (sweepOperator q u y)).prod
        * ((sortByRank a b M {P ∈ sweptAbove y η | diagExcess a b P = e ∧ c ≤ P.1}).map
            (sweepOperator q u y)).prod := by
  have hlist : sortByRank a b M {P ∈ sweptAbove y η | diagExcess a b P = e}
      = sortByRank a b M {P ∈ sweptAbove y η | diagExcess a b P = e ∧ P.1 < c}
        ++ sortByRank a b M {P ∈ sweptAbove y η | diagExcess a b P = e ∧ c ≤ P.1} := by
    conv_lhs => rw [← filter_lt_union_filter_le_fst y η e c]
    refine sortByRank_union (y := y) ha ?_ ?_ ?_
    · rw [filter_lt_union_filter_le_fst y η e c]
      exact fun P hP => (Finset.mem_filter.1 (Finset.mem_filter.1 hP).1).1
    · rw [Finset.disjoint_left]
      intro P hP hP'
      have h1 := (Finset.mem_filter.1 hP).2.2
      have h2 := (Finset.mem_filter.1 hP').2.2
      omega
    · intro P hP Q hQ
      have hPs : P ∈ sweptAbove y η := (Finset.mem_filter.1 hP).1
      have hQs : Q ∈ sweptAbove y η := (Finset.mem_filter.1 hQ).1
      have hP1 : P.1 ≤ a * M := (mem_sweptRegion.1 (Finset.mem_filter.1 hPs).1).1
      have hQ1 : Q.1 ≤ a * M := (mem_sweptRegion.1 (Finset.mem_filter.1 hQs).1).1
      have hlow := (Finset.mem_filter.1 hP).2
      have hhigh := (Finset.mem_filter.1 hQ).2
      simp only [diagExcess] at hlow hhigh
      rcases lt_or_ge (pointRank a b M P) (pointRank a b M Q) with h | h
      · exact h
      · exfalso
        rw [pointRank, pointRank, abovePointRank_le_iff hM hQ1 hP1] at h
        omega
  rw [roundSweepWord, hlist, List.map_append, List.prod_append]

/-! ### The base layer of a round at an extension -/

section Append

variable {N A : ℕ}

/-- **The width shift is constant on a round.** `HJO.Paths.sweepWidth_appendHeights_eq` shifts the
width at a base point by the number of the tail's live north steps there, and that number reads the
point only through its diagonal excess — which is the constant `e` on the round. So the whole base
layer of round `e` is read at widths raised by the single integer `#(tailLiveSteps w e)`.

This is what makes the round, rather than the point, the unit of the grouping: pointwise the shift
is a function on the layer, on a round it is a number. -/
@[hjo "lem_sweep_band_rounds"]
theorem sweepWidth_appendHeights_of_diagExcess_eq {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) {e : ℤ} {P : ℕ × ℕ}
    (hP : P.1 < a * N) (he : diagExcess a b P = e) :
    sweepWidth (appendHeights z w) P = sweepWidth z P + #(tailLiveSteps w e) := by
  rw [sweepWidth_appendHeights_eq hz hw hN hP, he]

/-- **The right count is shifted by the same constant on a round**, by the same reading of
`HJO.Paths.sweepRight_appendHeights_eq`. -/
@[hjo "lem_sweep_band_rounds"]
theorem sweepRight_appendHeights_of_diagExcess_eq {z : Heights a b N} {w : Heights a b A}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N) {e : ℤ} {P : ℕ × ℕ}
    (hP : P.1 < a * N) (he : diagExcess a b P = e) :
    sweepRight (appendHeights z w) P = sweepRight z P + #(tailLiveSteps w e) := by
  rw [sweepRight_appendHeights_eq hz hw hN hP, he]

/-- **The base layer of a round is indexed by the base's own round.** The low-abscissa part of the
extension's round-`e` index set is the base's own round-`e` index set, by
`HJO.Mellit.sweptAbove_filter_lt_appendHeights` — the corner column contributing nothing on the base
side at a separating level. -/
@[hjo "lem_sweep_band_rounds"]
theorem baseRoundList_appendHeights {z : Heights a b N} {w : Heights a b A} {η η' : ℚ}
    (hη : SeparatesDiagonal a b (N + A) η) (hη' : SeparatesDiagonal a b N η') (e : ℤ) :
    {P ∈ sweptAbove (appendHeights z w) η | diagExcess a b P = e ∧ P.1 < a * N}
      = {P ∈ sweptAbove z η' | diagExcess a b P = e} := by
  have h := sweptAbove_filter_lt_appendHeights (z := z) (w := w) hη hη'
  rw [Finset.ext_iff] at h
  simp only [Finset.mem_filter] at h
  ext P
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hP, he', hlt⟩
    exact ⟨(h P).1 ⟨hP, hlt⟩, he'⟩
  · rintro ⟨hP, he'⟩
    obtain ⟨hP', hlt⟩ := (h P).2 hP
    exact ⟨hP', he', hlt⟩

/-- **The base layer of a round is the base's own point list, in the base's own order — and nothing
else about it is the base's.** The index set is the base's round set
(`HJO.Mellit.baseRoundList_appendHeights`) and the listing is rectangle-free on the strip
(`HJO.Mellit.sortByRank_congr`), so the only discrepancy left between the base layer of the
extension and the base's own round word is the *operator*, which by
`HJO.Mellit.sweepWidth_appendHeights_of_diagExcess_eq` and
`HJO.Mellit.sweepRight_appendHeights_of_diagExcess_eq` is the base's own read at width and right
count raised by the one integer `#(tailLiveSteps w e)`.

That is the exact residual of the round-grouping at a round, and it is an operator statement, not a
combinatorial one: the index comparisons `HJO.Sweep.dminus_eq_of_mem_piece`,
`HJO.Sweep.dplus_succ_eq_dplus_add` and `HJO.Sweep.corner_transport_split_prefix` all read a graded
piece of the incoming vector, which no count of lattice points supplies. -/
@[hjo "lem_sweep_band_rounds"]
theorem baseRoundWord_appendHeights (ha : 0 < a) (hN : 0 < N) {z : Heights a b N}
    {w : Heights a b A} {η η' : ℚ} (hη : SeparatesDiagonal a b (N + A) η)
    (hη' : SeparatesDiagonal a b N η') (e : ℤ) :
    ((sortByRank a b (N + A) {P ∈ sweptAbove (appendHeights z w) η |
          diagExcess a b P = e ∧ P.1 < a * N}).map
        (sweepOperator q u (appendHeights z w))).prod
      = ((sortByRank a b N {P ∈ sweptAbove z η' | diagExcess a b P = e}).map
          (sweepOperator q u (appendHeights z w))).prod := by
  have hsub : {P ∈ sweptAbove z η' | diagExcess a b P = e} ⊆ sweptRegion z :=
    fun P hP => (Finset.mem_filter.1 (Finset.mem_filter.1 hP).1).1
  have hbound : ∀ P ∈ {P ∈ sweptAbove z η' | diagExcess a b P = e}, P.1 ≤ a * (N + A) := by
    intro P hP
    have := (mem_sweptRegion.1 (hsub hP)).1
    have hle : a * N ≤ a * (N + A) := Nat.mul_le_mul_left a (by omega)
    omega
  rw [baseRoundList_appendHeights hη hη' e,
    sortByRank_congr (y := z) ha hN (show 0 < N + A by omega) hsub hbound]

end Append

end HJO.Mellit

end
