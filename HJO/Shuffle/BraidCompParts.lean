/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidColStepInsert

/-! # The parts of the special-braid data of a composition colouring

The proof of `HJO.Mellit.mellitInduction_sweepWitness` cites
`HJO.Mellit.braidRep_specialBraid_dplusIter` "with `A = α_ℓ`", and that lemma's hypothesis on its
appended part is `β_0 = A(a+b) - 1` — the repair made at
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`, where the naive `β_{k+1} = A` is refuted by
the letter count of `HJO/Shuffle/BraidLetterCount.lean`. The resulting obligation falls on
the proof of `HJO.Mellit.mellitInduction_sweepWitness`: that under
`HJO.Mellit.braidDataOfColouring` the last component of `c_α` carries the part `α_ℓ(a+b) - 1`, "the
number of anti-diagonal positions its `α_ℓ` turns produce". This file discharges it, and discharges
more than was asked: the identity holds at
**every** component, not only the last.

## Main results

* `HJO.Mellit.card_componentCrossingIndices_hasAboveReturns` — the `i`-th component of the colouring
  of an above-diagonal path of return composition `α`, at a separating admissible level, has exactly
  `(a+b)α_{i+1} - 1` crossings of the anti-diagonal.
* `HJO.Mellit.braidDataOfColouring_snd_hasAboveReturns` — the same read off
  `HJO.Mellit.braidDataOfColouring`: the `i`-th part of the special-braid data is
  `(a+b)α_{i+1} - 1`.
* `HJO.Mellit.braidDataOfColouring_snd_last` — **the obligation for the last component**: the
  last component contributes the part `α_ℓ(a+b) - 1`.
* `HJO.Mellit.colStep_eq_of_strictMono` — the column listing of `HJO.Mellit.colStep` is the *unique*
  enumeration of a column-injective set that increases strictly in the column. This is what turns
  the explicit description of the two halves of `c_α` into a description of the components.
* `HJO.Mellit.colouringNorth_eq_image_returns`, `HJO.Mellit.colouringEast_eq_image_returns` — the
  two halves of the colouring of a path of return composition `α`, as explicit images of
  `Finset.range α.length`.

## Implementation notes

No hypothesis on `q` or `u` appears, and none is needed: every step is a count of integers in an
interval of the level line. The standing `1 < a < b` of the section is not used either — `0 < a`,
`0 < b`, `0 < N` and `Nat.Coprime a b` are what the two halves of the colouring need, and the level
is only required to be admissible, separating and positive.

The count itself: by `HJO.Mellit.componentBotIndex_eq` and `HJO.Mellit.componentTopIndex_eq` the
crossing indices of the `i`-th component run from `x(u_i) + I_{x(u_i)} + 1` to `x(w_i) + y(w_i)`.
For a path of return composition `α` the `i`-th crossed north step is the diagonal touch point
`(aA_i, bA_i)` — whose column's level index is its own ordinate `bA_i`, since it lies in the
colouring — and the `i`-th crossed east step is `(aA_{i+1} - 1, bA_{i+1})`. So the indices run from
`(a+b)A_i + 1` to `(a+b)A_{i+1} - 1`, and there are `(a+b)(A_{i+1} - A_i) - 1 = (a+b)α_{i+1} - 1`
of them. The `-1` is exactly the touch point's own crossing, which belongs to no component: it is
the point at which the level line has already passed the path.

## References

The obligation discharged here arises in the proof of `HJO.Mellit.mellitInduction_sweepWitness`,
through `HJO.Mellit.braidRep_specialBraid_dplusIter` and
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`; the objects counted are
`HJO.Mellit.braidDataOfColouring`, `HJO.Mellit.colouringComponent`, `HJO.Mellit.compColouring`,
`HJO.Paths.HasAboveReturns` and `HJO.Mellit.colouring`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The column listing is the unique strictly increasing enumeration -/

/-- Two members of a finite set of lattice points with the same number of members strictly to their
left share a column: otherwise the one further left is counted by the other and not by itself. -/
theorem fst_eq_of_card_filter_fst_lt_eq {S : Finset (ℕ × ℕ)} {P Q : ℕ × ℕ} (hP : P ∈ S)
    (hQ : Q ∈ S) (h : #({R ∈ S | R.1 < P.1}) = #({R ∈ S | R.1 < Q.1})) : P.1 = Q.1 := by
  classical
  have key : ∀ P' Q' : ℕ × ℕ, P' ∈ S → P'.1 < Q'.1 →
      #({R ∈ S | R.1 < P'.1}) < #({R ∈ S | R.1 < Q'.1}) := by
    intro P' Q' hP' hlt
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset (fun R hR => ?_)).2 ⟨P', ?_, ?_⟩)
    · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hR).1,
        lt_trans (Finset.mem_filter.1 hR).2 hlt⟩
    · exact Finset.mem_filter.2 ⟨hP', hlt⟩
    · exact fun hc => absurd (Finset.mem_filter.1 hc).2 (lt_irrefl _)
  rcases lt_trichotomy P.1 Q.1 with hlt | heq | hgt
  · exact absurd h (by have := key P Q hP hlt; omega)
  · exact heq
  · exact absurd h (by have := key Q P hQ hgt; omega)

/-- **The column listing is the unique enumeration that increases strictly in the column.** If `g`
sends `{0, …, #S - 1}` into `S` with strictly increasing column, then `g` *is*
`HJO.Mellit.colStep S` there. Both enumerations are counted by
`HJO.Mellit.card_filter_fst_lt_colStep` and its analogue for `g`, and a column-injective set has at
most one point per column. -/
theorem colStep_eq_of_strictMono {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S)
    {g : ℕ → ℕ × ℕ} (hmem : ∀ j < #S, g j ∈ S)
    (hmono : ∀ j j', j < j' → j' < #S → (g j).1 < (g j').1) {i : ℕ} (hi : i < #S) :
    colStep S i = g i := by
  classical
  have hinj : ∀ j < #S, ∀ j' < #S, g j = g j' → j = j' := by
    intro j hj j' hj' hjj'
    rcases lt_trichotomy j j' with h | h | h
    · exact absurd (congrArg Prod.fst hjj') (by have := hmono j j' h hj'; omega)
    · exact h
    · exact absurd (congrArg Prod.fst hjj') (by have := hmono j' j h hj; omega)
  have hinjOn : ∀ n ≤ #S, Set.InjOn g (Finset.range n : Finset ℕ) := by
    intro n hn j hj j' hj' hjj'
    rw [Finset.coe_range, Set.mem_Iio] at hj hj'
    exact hinj j (by omega) j' (by omega) hjj'
  have himg : (Finset.range #S).image g = S := by
    refine Finset.eq_of_subset_of_card_le (fun P hP => ?_) ?_
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hP
      exact hmem j (Finset.mem_range.1 hj)
    · rw [Finset.card_image_of_injOn (hinjOn _ le_rfl), Finset.card_range]
  have hcount : #({P ∈ S | P.1 < (g i).1}) = i := by
    have hset : {P ∈ S | P.1 < (g i).1} = (Finset.range i).image g := by
      ext P
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hPS, hP⟩
        rw [← himg] at hPS
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hPS
        rw [Finset.mem_range] at hj
        refine ⟨j, ?_, rfl⟩
        rcases lt_trichotomy j i with h | h | h
        · exact h
        · exact absurd hP (by rw [h]; exact lt_irrefl _)
        · exact absurd hP (by have := hmono i j h hj; omega)
      · rintro ⟨j, hj, rfl⟩
        exact ⟨hmem j (by omega), hmono j i hj hi⟩
    rw [hset, Finset.card_image_of_injOn (hinjOn i hi.le), Finset.card_range]
  exact hcol _ (colStep_mem hi) _ (hmem i hi)
    (fst_eq_of_card_filter_fst_lt_eq (colStep_mem hi) (hmem i hi)
      (by rw [card_filter_fst_lt_colStep hcol hi, hcount]))

/-! ### The two halves of the colouring of a path of return composition `α` -/

/-- **The crossed north steps of a path of return composition `α`** are the diagonal touch points
`(aA_i, bA_i)` for `0 ≤ i < ℓ`, `A_i` being the `i`-th partial sum of `α`. By
`HJO.Mellit.mem_colouring_north_iff` they are the returns below the top, and by
`HJO.Paths.HasAboveReturns` the returns are exactly the partial sums. -/
theorem colouringNorth_eq_image_returns {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) {α : List ℕ} {y : Heights a b N} (hret : HasAboveReturns α y) :
    colouringNorth y η =
      (Finset.range α.length).image fun j => (a * (α.take j).sum, b * (α.take j).sum) := by
  obtain ⟨hy, hpos, hsum, hk⟩ := hret
  have hfull : (α.take α.length).sum = N := by rw [List.take_length, hsum]
  have hlt : ∀ j < α.length, (α.take j).sum < N := by
    intro j hj
    rw [← hfull]
    exact sum_take_lt hpos hj le_rfl
  ext P
  rw [colouringNorth, Finset.mem_filter, mem_colouring_north_iff hηa hηs hab ha hb hN hy]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hkN, hretk, rfl⟩
    obtain ⟨m, hm, hmk⟩ := (mem_scanl_add_iff α 0 k).1 ((hk k hkN.le).1 hretk)
    rw [Nat.zero_add] at hmk
    refine ⟨m, ?_, by rw [hmk]⟩
    rcases Nat.lt_or_ge m α.length with h | h
    · exact h
    · rw [show m = α.length from by omega, hfull] at hmk
      omega
  · rintro ⟨j, hj, rfl⟩
    refine ⟨(α.take j).sum, hlt j hj, ?_, rfl⟩
    exact (hk _ (hlt j hj).le).2 ((mem_scanl_add_iff α 0 _).2 ⟨j, hj.le, by simp⟩)

/-- **The crossed east steps of a path of return composition `α`** are the western neighbours
`(aA_{i+1} - 1, bA_{i+1})` of the diagonal touch points other than the origin, for `0 ≤ i < ℓ`. -/
theorem colouringEast_eq_image_returns {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {α : List ℕ} {y : Heights a b N} (hret : HasAboveReturns α y) :
    colouringEast y η =
      (Finset.range α.length).image
        fun j => (a * (α.take (j + 1)).sum - 1, b * (α.take (j + 1)).sum) := by
  obtain ⟨hy, hpos, hsum, hk⟩ := hret
  have hfull : (α.take α.length).sum = N := by rw [List.take_length, hsum]
  have hpos' : ∀ j, 0 < j → j ≤ α.length → 0 < (α.take j).sum := by
    intro j hj0 hj
    have := sum_take_lt hpos hj0 hj
    simpa using this
  have hle : ∀ j ≤ α.length, (α.take j).sum ≤ N := by
    intro j hj
    rw [← hfull]
    exact List.monotone_sum_take α hj
  ext P
  rw [colouringEast, Finset.mem_filter, mem_colouring_east_iff hηa hηs hab ha hb hy]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk1, hkN, hretk, rfl⟩
    obtain ⟨m, hm, hmk⟩ := (mem_scanl_add_iff α 0 k).1 ((hk k hkN).1 hretk)
    rw [Nat.zero_add] at hmk
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := by
      match m with
      | 0 => simp at hmk; omega
      | (j + 1) => exact ⟨j, rfl⟩
    exact ⟨j, by omega, by rw [hmk]⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨(α.take (j + 1)).sum, hpos' _ (by omega) (by omega), hle _ (by omega), ?_, rfl⟩
    exact (hk _ (hle _ (by omega))).2 ((mem_scanl_add_iff α 0 _).2 ⟨j + 1, by omega, by simp⟩)

/-- The number of crossed north steps of a path of return composition `α` is the number of parts. -/
theorem card_colouringNorth_hasAboveReturns {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) {α : List ℕ} {y : Heights a b N} (hret : HasAboveReturns α y) :
    #(colouringNorth y η) = α.length := by
  classical
  rw [colouringNorth_eq_image_returns hηa hηs hab ha hb hN hret, Finset.card_image_of_injOn,
    Finset.card_range]
  intro j hj j' hj' hjj'
  rw [Finset.coe_range, Set.mem_Iio] at hj hj'
  have h2 := congrArg Prod.snd hjj'
  simp only at h2
  have := Nat.eq_of_mul_eq_mul_left hb h2
  rcases lt_trichotomy j j' with h | h | h
  · exact absurd this (by have := sum_take_lt hret.2.1 h hj'.le; omega)
  · exact h
  · exact absurd this (by have := sum_take_lt hret.2.1 h hj.le; omega)

/-- The number of crossed east steps of a path of return composition `α` is the number of parts. -/
theorem card_colouringEast_hasAboveReturns {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ} {y : Heights a b N}
    (hret : HasAboveReturns α y) : #(colouringEast y η) = α.length := by
  rw [← card_colouringNorth_eq_card_colouringEast hb hN hηa hηN hret.1,
    card_colouringNorth_hasAboveReturns hηa hηs hab ha hb hN hret]

/-! ### The two ends of a component of `c_α` -/

/-- The `i`-th crossed north step of a path of return composition `α` is the diagonal touch point
`(aA_i, bA_i)`: the explicit family of `HJO.Mellit.colouringNorth_eq_image_returns` increases
strictly in the column, so it is the column listing. -/
theorem colStep_colouringNorth_hasAboveReturns {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) {α : List ℕ} {y : Heights a b N} (hret : HasAboveReturns α y) {i : ℕ}
    (hi : i < α.length) :
    colStep (colouringNorth y η) i = (a * (α.take i).sum, b * (α.take i).sum) := by
  have hcard := card_colouringNorth_hasAboveReturns hηa hηs hab ha hb hN hret
  have himg := colouringNorth_eq_image_returns hηa hηs hab ha hb hN hret
  have hiS : i < #(colouringNorth y η) := by omega
  refine colStep_eq_of_strictMono (columnInjective_colouringNorth ha hN hηa y)
    (g := fun j => (a * (α.take j).sum, b * (α.take j).sum))
    (fun j hj => ?_) (fun j j' hjj' hj' => ?_) hiS
  · rw [himg]
    exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩
  · exact mul_lt_mul_of_pos_left (sum_take_lt hret.2.1 hjj' (by omega)) ha

/-- The `i`-th crossed east step of a path of return composition `α` is the western neighbour
`(aA_{i+1} - 1, bA_{i+1})` of the `(i+1)`-st touch point. -/
theorem colStep_colouringEast_hasAboveReturns {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ} {y : Heights a b N}
    (hret : HasAboveReturns α y) {i : ℕ} (hi : i < α.length) :
    colStep (colouringEast y η) i =
      (a * (α.take (i + 1)).sum - 1, b * (α.take (i + 1)).sum) := by
  have hcard := card_colouringEast_hasAboveReturns hηa hηs hab ha hb hN hηN hret
  have himg := colouringEast_eq_image_returns (a := a) (b := b) (N := N) hηa hηs hab ha hb hret
  have hiS : i < #(colouringEast y η) := by omega
  refine colStep_eq_of_strictMono (columnInjective_colouringEast ha hN hηa y)
    (g := fun j => (a * (α.take (j + 1)).sum - 1, b * (α.take (j + 1)).sum))
    (fun j hj => ?_) (fun j j' hjj' hj' => ?_) hiS
  · rw [himg]
    exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩
  · have hlt : a * (α.take (j + 1)).sum < a * (α.take (j' + 1)).sum :=
      mul_lt_mul_of_pos_left (sum_take_lt hret.2.1 (by omega) (by omega)) ha
    have h1 : 0 < (α.take (j + 1)).sum := by
      have := sum_take_lt hret.2.1 (show 0 < j + 1 by omega) (show j + 1 ≤ α.length by omega)
      simpa using this
    have h2 : 0 < a * (α.take (j + 1)).sum := Nat.mul_pos ha h1
    simp only
    omega

/-- The level index of the column of a touch point of a path of return composition `α` is the
ordinate of that touch point: the crossed north step of a column has ordinate the level index of the
column, by `HJO.Mellit.mem_colouringNorth_iff`. -/
theorem levelIndex_diag_hasAboveReturns {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) {α : List ℕ} {y : Heights a b N} (hret : HasAboveReturns α y) {i : ℕ}
    (hi : i < α.length) :
    levelIndex a b N η (a * (α.take i).sum) = ((b * (α.take i).sum : ℕ) : ℤ) := by
  have hmem : ((a * (α.take i).sum, b * (α.take i).sum) : ℕ × ℕ) ∈ colouringNorth y η := by
    rw [colouringNorth_eq_image_returns hηa hηs hab ha hb hN hret]
    exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
  exact ((mem_colouringNorth_iff ha hN hηa y _ _).1 hmem).2.2.2.symm

/-! ### The part of a component of `c_α` -/

/-- **THE OBLIGATION OF `HJO.Mellit.mellitInduction_sweepWitness`, at every component.** For an
above-diagonal path of return composition `α` and a positive separating admissible level, the `i`-th
component of the colouring meets the anti-diagonal exactly `(a+b)α_{i+1} - 1` times.

The proof of `HJO.Mellit.mellitInduction_sweepWitness` uses only the last component — "the last
component contributes the part `α_ℓ(a+b) - 1`, the number of anti-diagonal positions its `α_ℓ`
turns produce" — and needs it as an obligation because `HJO.Mellit.braidDataOfColouring` does not
make the statement. It is true at every component and is proved uniformly here;
`HJO.Mellit.braidDataOfColouring_snd_last` is the last-component instance that proof cites.

The crossing indices of the component run from `(a+b)A_i + 1` to `(a+b)A_{i+1} - 1`, by
`HJO.Mellit.componentBotIndex_eq` at the touch point `(aA_i, bA_i)` and
`HJO.Mellit.componentTopIndex_eq` at the east step `(aA_{i+1} - 1, bA_{i+1})`. The single index
`(a+b)A_i` that both components adjacent to the touch point omit is the crossing at the touch point
itself, which the level line has already passed. -/
theorem card_componentCrossingIndices_hasAboveReturns (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) {i : ℕ} (hi : i < α.length) :
    #(componentCrossingIndices a b N y η i) = (a + b) * α[i] - 1 := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηN
  have hcardE := card_colouringEast_hasAboveReturns hηa hηs hab ha hb hN hηN hret
  have hstepN := colStep_colouringNorth_hasAboveReturns hηa hηs hab ha hb hN hret hi
  have hstepE := colStep_colouringEast_hasAboveReturns hηa hηs hab ha hb hN hηN hret hi
  rw [componentCrossingIndices_eq_Icc, Int.card_Icc,
    componentBotIndex_eq ha hb hN hηa hηpos y i,
    componentTopIndex_eq ha hb hN hηa hηpos (show i < #(colouringEast y η) by omega),
    hstepN, hstepE]
  simp only
  rw [levelIndex_diag_hasAboveReturns hηa hηs hab ha hb hN hret hi]
  -- the arithmetic: `A_{i+1} = A_i + α_{i+1}`, and both ends are strictly inside
  have hA : (α.take (i + 1)).sum = (α.take i).sum + α[i] := List.sum_take_succ α i hi
  have hc : 0 < α[i] := hret.2.1 α[i] (List.getElem_mem hi)
  have hexp : a * (α.take (i + 1)).sum = a * (α.take i).sum + a * α[i] := by rw [hA]; ring
  have hexp' : b * (α.take (i + 1)).sum = b * (α.take i).sum + b * α[i] := by rw [hA]; ring
  have hsum : (a + b) * α[i] = a * α[i] + b * α[i] := by ring
  have hac : 0 < a * α[i] := Nat.mul_pos ha hc
  have hbc : 0 < b * α[i] := Nat.mul_pos hb hc
  rw [hexp, hexp', hsum]
  omega

/-- **The obligation read off `HJO.Mellit.braidDataOfColouring`**: the `i`-th part of the
special-braid data of the colouring of a path of return composition `α` is `(a+b)α_{i+1} - 1`. -/
theorem braidDataOfColouring_snd_hasAboveReturns (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) (i : Fin α.length) :
    (braidDataOfColouring a b N y η α.length).2 i = (a + b) * α[(i : ℕ)] - 1 := by
  rw [braidDataOfColouring_snd]
  exact card_componentCrossingIndices_hasAboveReturns ha hb hN hab hηa hηs hηN hret i.isLt

/-- **The obligation as `HJO.Mellit.mellitInduction_sweepWitness` states it.** The last component of
`c_α` contributes, under `HJO.Mellit.braidDataOfColouring`, the part `α_ℓ(a+b) - 1` — which is
exactly the form `HJO.Mellit.braidRep_specialBraid_dplusIter` requires of its appended part,
`β_0 = A(a+b) - 1`, at `A = α_ℓ`.

The proof of `HJO.Mellit.mellitInduction_sweepWitness` said "the last part is `α_ℓ`" and cited
`HJO.Mellit.braidRep_specialBraid_dplusIter` "with `A = α_ℓ`"; read literally that needs
`α_ℓ = α_ℓ(a+b) - 1`, i.e. `a + b = 2`, which the standing `1 < a < b` excludes. This is the repair,
and it is a theorem rather than a rewording. -/
theorem braidDataOfColouring_snd_last (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) (hα : α ≠ []) :
    (braidDataOfColouring a b N y η α.length).2 ⟨α.length - 1, by
        have := List.length_pos_of_ne_nil hα; omega⟩ = α.getLast hα * (a + b) - 1 := by
  rw [braidDataOfColouring_snd_hasAboveReturns ha hb hN hab hηa hηs hηN hret,
    List.getLast_eq_getElem]
  ring_nf

/-! ### The hypotheses are satisfiable, and the one-part case is the letter count's value -/

/-- **The hypotheses of the results above are satisfiable**: the `(4,6)`-path of heights
`(0,3,3,6,6)` is above-diagonal with return composition `(1,1)`, and `η = aN + 1/2 = 9/2` is an
admissible separating level exceeding `aN = 4`. Without this the statements could be vacuous. -/
theorem hasAboveReturns_example :
    HasAboveReturns [1, 1] (![0, 3, 3, 6, 6] : Heights 2 3 2) := by
  refine ⟨by decide, by decide, by decide, fun k hk => ?_⟩
  have hscanl : ([1, 1] : List ℕ).scanl (· + ·) 0 = [0, 1, 2] := by norm_num
  rw [hscanl]
  interval_cases k <;> simp [ht]

/-- **The count in the kernel**, on the witness of `HJO.Mellit.hasAboveReturns_example`: each of the
two components of the colouring carries `(a+b)·1 - 1 = 4` crossings of the anti-diagonal. -/
theorem card_componentCrossingIndices_example (i : ℕ) (hi : i < 2) :
    #(componentCrossingIndices 2 3 2 (![0, 3, 3, 6, 6] : Heights 2 3 2) (sepLevel 2 2) i) = 4 := by
  have h := card_componentCrossingIndices_hasAboveReturns (a := 2) (b := 3) (N := 2)
    (by norm_num) (by norm_num) (by norm_num) (by decide)
    (isAdmissibleLevel_sepLevel 2 2) (separatesDiagonal_sepLevel (by norm_num))
    (by rw [sepLevel]; norm_num) hasAboveReturns_example (i := i) (by simpa using hi)
  rw [h]
  interval_cases i <;> norm_num

/-- **The one-part case is exactly the value the letter count forces.** For `α = (A)` the single
component carries `A(a+b) - 1`, which is the part
`HJO.Braid.letterCount_specialBraid_eq_letterCount_appendRhs_iff` admits and the one
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` was repaired to. The obligation of
`HJO.Mellit.mellitInduction_sweepWitness` is therefore not an independent guess: at `ℓ = 1` it
agrees with the letter count that forced the repair. -/
theorem card_componentCrossingIndices_single (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {A : ℕ}
    {y : Heights a b N} (hret : HasAboveReturns [A] y) :
    #(componentCrossingIndices a b N y η 0) = A * (a + b) - 1 := by
  rw [card_componentCrossingIndices_hasAboveReturns ha hb hN hab hηa hηs hηN hret
    (show 0 < [A].length by norm_num)]
  simp [Nat.mul_comm]

/-! ### A second, distinct defect in the same step: the appended entry is not `1-θ`

The obligation above is about the *part*. Its neighbouring clause — "the
special-braid data of `c_α` is obtained from that of `c_{α'}` by adjoining a last entry lying
between the previous ones and `1-θ`" — cannot feed `HJO.Mellit.braidRep_specialBraid_dplusIter`
either, because that lemma (and
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` behind it) requires the appended **entry** to be
`1-θ` on the nose: `hw₀ : w₀ 0 = 1 - θ`. The colouring never supplies that. -/

/-- The top crossing index of the last component of the colouring of a path of return composition
`α` is `(aN - 1) + bN`, the last east step of the path arriving at the top touch point. -/
theorem componentTopIndex_last (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : Nat.Coprime a b)
    {η : ℚ} (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η)
    (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ} {y : Heights a b N}
    (hret : HasAboveReturns α y) (hα : α ≠ []) :
    componentTopIndex a b N y η (α.length - 1) = ((a * N - 1 : ℕ) : ℤ) + ((b * N : ℕ) : ℤ) := by
  have hlen : 0 < α.length := List.length_pos_of_ne_nil hα
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηN
  have hAl : (α.take (α.length - 1 + 1)).sum = N := by
    rw [show α.length - 1 + 1 = α.length from by omega, List.take_length, hret.2.2.1]
  have hstepE := colStep_colouringEast_hasAboveReturns hηa hηs hab ha hb hN hηN hret
    (show α.length - 1 < α.length from by omega)
  rw [hAl] at hstepE
  have hcardE := card_colouringEast_hasAboveReturns hηa hηs hab ha hb hN hηN hret
  rw [componentTopIndex_eq ha hb hN hηa hηpos
    (show α.length - 1 < #(colouringEast y η) from by omega), hstepE]

/-- **THE APPENDED ENTRY IS NOT `1-θ`, and here is the witness.** On the `(4,6)`-path of heights
`(0,3,3,6,6)` at `η = 9/2`, whose return composition is `(1,1)`, the position
`HJO.Mellit.braidDataOfColouring` reads off the last component is `57/98`, while
`1-θ = 29/49 = 58/98`.

So `HJO.Mellit.braidRep_specialBraid_dplusIter` — whose hypothesis is `w₀ 0 = 1-θ`, inherited
unchanged from `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` — cannot be applied to the
special-braid data of `c_α` as it stands,
*even after* the part is repaired by `HJO.Mellit.braidDataOfColouring_snd_last`. This is a second
defect in the same step of `HJO.Mellit.mellitInduction_sweepWitness`, independent of the first.

The gap is exactly `(η - aN)/((a+b)(aN+1)N - 1)`: in general the last component's position is
`1 - θ - (η - aN)/(a(aN+1)N + b(aN+1)N - 1)`, which equals `1-θ` only at `η = aN`, and every
separating level has `η > aN`. Here `(9/2 - 4)/49 = 1/98`. -/
theorem fract_crossingAbscissa_componentTopIndex_last_example :
    Int.fract (crossingAbscissa 2 3 2 (sepLevel 2 2)
        (componentTopIndex 2 3 2 (![0, 3, 3, 6, 6] : Heights 2 3 2) (sepLevel 2 2) 1))
      = 57 / 98 ∧ (1 : ℚ) - sweepTheta 2 3 2 = 29 / 49 := by
  have htop : componentTopIndex 2 3 2 (![0, 3, 3, 6, 6] : Heights 2 3 2) (sepLevel 2 2) 1 = 9 := by
    have h := componentTopIndex_last (a := 2) (b := 3) (N := 2) (by norm_num) (by norm_num)
      (by norm_num) (by decide) (isAdmissibleLevel_sepLevel 2 2)
      (separatesDiagonal_sepLevel (by norm_num)) (by rw [sepLevel]; norm_num)
      hasAboveReturns_example (by simp)
    norm_num at h
    exact h
  refine ⟨?_, ?_⟩
  · rw [htop, crossingAbscissa, levelIntercept, sweepSlope, sepLevel, Int.fract]
    norm_num
  · rw [sweepTheta, sweepSlope]
    norm_num

/-- The same defect read off `HJO.Mellit.braidDataOfColouring` itself: the position of the last
component is not `1-θ`, so the appended-entry hypothesis of
`HJO.Mellit.braidRep_specialBraid_dplusIter` fails. -/
theorem braidDataOfColouring_fst_last_ne_example :
    (braidDataOfColouring 2 3 2 (![0, 3, 3, 6, 6] : Heights 2 3 2) (sepLevel 2 2) 2).1 1
      ≠ 1 - sweepTheta 2 3 2 := by
  rw [braidDataOfColouring_fst]
  rw [show ((1 : Fin 2) : ℕ) = 1 from rfl,
    fract_crossingAbscissa_componentTopIndex_last_example.1,
    fract_crossingAbscissa_componentTopIndex_last_example.2]
  norm_num

/-- From `(x - c)·d = y` with `d > 0` and `y < 0`: `x < c`. Stated abstractly so that the
comparisons below need no arithmetic on the big rational expressions they instantiate it at. -/
private theorem lt_of_sub_mul_eq_of_neg {c d x y : ℚ} (hd : 0 < d) (h : (x - c) * d = y)
    (hy : y < 0) : x < c := by
  by_contra hcon
  have hge : c ≤ x := not_lt.1 hcon
  nlinarith [mul_nonneg (sub_nonneg.2 hge) hd.le]

/-- From `(x - c)·d = y` with `d > 0` and `y > 0`: `c < x`. -/
private theorem lt_of_sub_mul_eq_of_pos {c d x y : ℚ} (hd : 0 < d) (h : (x - c) * d = y)
    (hy : 0 < y) : c < x := by
  by_contra hcon
  have hle : x ≤ c := not_lt.1 hcon
  nlinarith [mul_nonneg (sub_nonneg.2 hle) hd.le]

/-- **THE APPENDED ENTRY IS NEVER `1-θ`** — not at this example, and not at any separating level.
The position `HJO.Mellit.braidDataOfColouring` reads off the last component of `c_α` is
`1 - θ - (η - aN)/(a(aN+1)N + b(aN+1)N - 1)`, and every separating admissible level has `η > aN`, so
the gap is strictly positive.

`HJO.Mellit.braidRep_specialBraid_dplusIter` and `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`
both require the appended entry to be `1-θ` exactly (`hw₀ : w₀ 0 = 1 - θ`). So the step of
`HJO.Mellit.mellitInduction_sweepWitness` cannot apply them however the part is repaired: what it
needs in addition is a statement that the braid of special-braid data depends only on the *cell* its
entries lie in — the reading suggested by the wording of the proof, "a last entry lying between the
previous ones and `1-θ`" — which neither lemma provides.

`a ≤ b` is the only place the section's standing `1 < a < b` is used in this file, and it is used
only to place `η` below `aN + b(aN+1)N - 1`; the conclusion is a strict inequality either way. -/
theorem fract_crossingAbscissa_componentTopIndex_last_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) (hle : a ≤ b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) (hα : α ≠ []) :
    Int.fract (crossingAbscissa a b N η (componentTopIndex a b N y η (α.length - 1)))
      < 1 - sweepTheta a b N := by
  have ha' : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hb' : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
  have hNq : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  have hleq : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hle
  have haNq : (1 : ℚ) ≤ (a : ℚ) * N := by nlinarith
  have hηNq : (a : ℚ) * N < η := by push_cast at hηN; exact hηN
  have hMpos : (0 : ℚ) < (a : ℚ) * ((a : ℚ) * N + 1) * N := by nlinarith
  have hMB : (a : ℚ) * ((a : ℚ) * N + 1) * N ≤ (b : ℚ) * ((a : ℚ) * N + 1) * N := by nlinarith
  have hDpos : (0 : ℚ) <
      (a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 := by nlinarith
  -- the level lies below the rank of the lattice point `(0, 1)`, which is `a(aN+1)N`
  have hupper : η < (a : ℚ) * ((a : ℚ) * N + 1) * N := by
    have hbN : (1 : ℕ) ≤ b * N := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h := (hηs 0 1 (Nat.zero_le _) hbN (by simp)).2
      (by simpa using (show (0 : ℤ) < a by exact_mod_cast ha))
    rw [abovePointRank] at h
    push_cast at h
    nlinarith [h]
  have hSne : (1 : ℚ) + sweepSlope a b N ≠ 0 := (one_add_sweepSlope_pos ha hb hN).ne'
  have haN : (1 : ℕ) ≤ a * N := Nat.one_le_iff_ne_zero.2 (by positivity)
  set x : ℚ := crossingAbscissa a b N η (componentTopIndex a b N y η (α.length - 1)) with hxdef
  -- the crossing index, as a rational
  have hn : ((componentTopIndex a b N y η (α.length - 1) : ℤ) : ℚ)
      = (a : ℚ) * N + (b : ℚ) * N - 1 := by
    rw [componentTopIndex_last ha hb hN hab hηa hηs hηN hret hα]
    push_cast [Nat.cast_sub haN]
    ring
  -- clearing the two denominators once
  have hSM : (1 + sweepSlope a b N) * ((a : ℚ) * ((a : ℚ) * N + 1) * N)
      = (a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 := by
    rw [sweepSlope]
    field_simp
    ring
  have hLM : levelIntercept a N η * ((a : ℚ) * ((a : ℚ) * N + 1) * N) = η := by
    rw [levelIntercept]
    field_simp
  have h0 : x * (1 + sweepSlope a b N)
      = ((a : ℚ) * N + (b : ℚ) * N - 1) - levelIntercept a N η := by
    rw [hxdef, crossingAbscissa, hn]
    field_simp
  have hxD : x * ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
      = ((a : ℚ) * N + (b : ℚ) * N - 1) * ((a : ℚ) * ((a : ℚ) * N + 1) * N) - η := by
    rw [← hSM, show x * ((1 + sweepSlope a b N) * ((a : ℚ) * ((a : ℚ) * N + 1) * N))
      = (x * (1 + sweepSlope a b N)) * ((a : ℚ) * ((a : ℚ) * N + 1) * N) from by ring, h0]
    rw [show (((a : ℚ) * N + (b : ℚ) * N - 1) - levelIntercept a N η) *
        ((a : ℚ) * ((a : ℚ) * N + 1) * N)
      = ((a : ℚ) * N + (b : ℚ) * N - 1) * ((a : ℚ) * ((a : ℚ) * N + 1) * N)
        - levelIntercept a N η * ((a : ℚ) * ((a : ℚ) * N + 1) * N) from by ring, hLM]
  have hθD : sweepTheta a b N *
      ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
      = (a : ℚ) * ((a : ℚ) * N + 1) * N := by
    rw [sweepTheta, ← hSM]
    field_simp
  -- the three comparisons, each a single ring identity away from `hxD`
  have e1 : (x - ((a : ℚ) * N - 1)) *
      ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
      = (a : ℚ) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 - η := by
    rw [show (x - ((a : ℚ) * N - 1)) *
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
      = x * ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
        - ((a : ℚ) * N - 1) *
          ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1) from by ring,
      hxD]
    ring
  have e2 : (x - (a : ℚ) * N) *
      ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
      = (a : ℚ) * N - (a : ℚ) * ((a : ℚ) * N + 1) * N - η := by
    rw [show (x - (a : ℚ) * N) *
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
      = x * ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
        - (a : ℚ) * N *
          ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1) from by ring,
      hxD]
    ring
  have e3 : (x - ((a : ℚ) * N - sweepTheta a b N)) *
      ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
      = (a : ℚ) * N - η := by
    rw [show (x - ((a : ℚ) * N - sweepTheta a b N)) *
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
      = x * ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
        - (a : ℚ) * N *
          ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
        + sweepTheta a b N *
          ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1) from by ring,
      hxD, hθD]
    ring
  have hlow : (a : ℚ) * N - 1 < x := lt_of_sub_mul_eq_of_pos hDpos e1 (by linarith)
  have hhigh : x < (a : ℚ) * N := lt_of_sub_mul_eq_of_neg hDpos e2 (by linarith)
  have hgap : x < (a : ℚ) * N - sweepTheta a b N :=
    lt_of_sub_mul_eq_of_neg hDpos e3 (by linarith)
  have hfl : ⌊x⌋ = ((a * N : ℕ) : ℤ) - 1 := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · push_cast
      linarith
    · push_cast
      linarith
  rw [Int.fract, hfl]
  push_cast
  linarith

/-- The general failure read off `HJO.Mellit.braidDataOfColouring`: the position of the last
component of `c_α` is strictly below `1-θ`, so `HJO.Mellit.braidRep_specialBraid_dplusIter`'s
`hw₀ : w₀ 0 = 1 - θ` is never available. -/
theorem braidDataOfColouring_fst_last_ne (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) (hle : a ≤ b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) (hα : α ≠ []) :
    (braidDataOfColouring a b N y η α.length).1 ⟨α.length - 1, by
        have := List.length_pos_of_ne_nil hα; omega⟩ ≠ 1 - sweepTheta a b N := by
  rw [braidDataOfColouring_fst]
  exact ne_of_lt (fract_crossingAbscissa_componentTopIndex_last_lt ha hb hN hab hle hηa hηs hηN
    hret hα)

end HJO.Mellit

end
