/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ColouringCrossings
public import HJO.Shuffle.ColouringLevelIndex
public meta import HJO.Attr

/-! # The data of a colouring is special-braid data

`HJO.Mellit.isSpecialBraidData_braidDataOfColouring`. Four of its six clauses are statements about a
single crossing abscissa and are `HJO/Shuffle/ColouringCrossings.lean`; the two that remain — that
every component carries a crossing, and that distinct components share none — need the pairing of
crossed north with crossed east steps, and are here.

## Main results

* `HJO.Mellit.isSpecialBraidData_braidDataOfColouring` — the data of a colouring is special-braid
  data.
* `HJO.Mellit.card_colouringNorth_filter_lt` — the alternation of the two kinds of crossing along
  the level line, as a count: left of any column the crossed north steps outnumber the crossed east
  steps by the indicator of the line's lying below the path there. The usual proof of
  `HJO.Mellit.card_colouringNorth_eq_card_colouringEast` reads this off its interval decomposition,
  and neither that lemma's statement nor its proof here provides it.
* `HJO.Mellit.northCol_le_eastCol` and `HJO.Mellit.eastCol_lt_northCol_succ` — the interleaving of
  the two listings that follows, which is the statement that the components are pairwise disjoint.
* `HJO.Mellit.componentBotIndex_eq`, `HJO.Mellit.componentTopIndex_eq` — the two ends of a
  component as crossing indices: `x(u_i) + I_{x(u_i)} + 1` and `x(w_i) + y(w_i)`.
* `HJO.Mellit.iterate_nextCrossing_fract_crossingAbscissa` — listing a component downwards from its
  top crossing is iterating `nx_θ` on the torus.

## Implementation notes

The intervals `J_i(c)` are pairwise disjoint in `i` because the two kinds of crossing alternate
along the level line, which the usual argument establishes *inside the proof* of
`HJO.Mellit.card_colouringNorth_eq_card_colouringEast` — a fact that lemma's statement does not
carry, and that its proof here does not produce either, having replaced the interval decomposition
by a telescoping count. So the alternation is proved here, in the same telescoping style: the count
identity `HJO.Mellit.card_colouringNorth_filter_lt`, whose column-by-column content is a five-case
check on whether the level line is below the path at `x`, over `(x, x+1)`, and at `x + 1`.
Everything else in the proof of `HJO.Mellit.isSpecialBraidData_braidDataOfColouring` reduces to it.

## References

This file proves `HJO.Mellit.isSpecialBraidData_braidDataOfColouring`, using
`HJO.Mellit.braidDataOfColouring`, `HJO.Mellit.colouringComponent`, `HJO.Braid.IsSpecialBraidData`,
`HJO.Braid.nextCrossing`, `HJO.Mellit.sweepSlope`,
`HJO.Mellit.card_colouringNorth_eq_card_colouringEast` and `HJO.Mellit.IsAdmissibleLevel`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The level index is the floor of the ordinate of the level line -/

/-- **The level index is the floor of the ordinate of the level line.** `I_x(η)` was defined by
solving the rank inequality; this identifies it with `⌊s_{a,b,N}x + η/(aM)⌋`, which is the shape
every geometric statement below is written in. -/
theorem levelIndex_eq_floor (ha : 0 < a) (hN : 0 < N) (η : ℚ) (x : ℕ) :
    levelIndex a b N η x = ⌊sweepSlope a b N * (x : ℚ) + levelIntercept a N η⌋ := by
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hM : ((a : ℚ) * N + 1) ≠ 0 := by positivity
  rw [levelIndex]
  congr 1
  rw [sweepSlope, levelIntercept]
  push_cast
  field_simp
  ring

/-- The ordinate of the level line over a natural abscissa is positive. -/
theorem levelOrd_pos (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ} (hηpos : 0 < η) (x : ℕ) :
    0 < sweepSlope a b N * (x : ℚ) + levelIntercept a N η := by
  have hs := sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  have hh := levelIntercept_pos (a := a) (N := N) ha hN hηpos
  have hx : (0 : ℚ) ≤ (x : ℚ) := Nat.cast_nonneg x
  nlinarith

/-- **The level line passes through no lattice point over a natural abscissa.** This is
`HJO.Mellit.pointRank_ne_of_on_level` with the ordinate allowed to be any integer: over a natural
abscissa the ordinate of the level line is positive, so an integer value would be a natural one. -/
theorem levelOrd_ne_intCast (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) (x : ℕ) (w : ℤ) :
    sweepSlope a b N * (x : ℚ) + levelIntercept a N η ≠ (w : ℚ) := by
  intro h
  have hw : 0 < (w : ℚ) := h ▸ levelOrd_pos (b := b) ha hb hN hηpos x
  have hw' : 0 < w := by exact_mod_cast hw
  obtain ⟨v, hv⟩ : ∃ v : ℕ, w = (v : ℤ) := ⟨w.toNat, by omega⟩
  exact pointRank_ne_of_on_level (b := b) ha hN hη x v (by rw [h, hv]; norm_num)

/-- The ordinate of the level line over a natural abscissa is *strictly* above its floor: the two
would otherwise be the ordinate of a lattice point on the level line. -/
theorem levelIndex_lt_levelOrd (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) (x : ℕ) :
    ((levelIndex a b N η x : ℤ) : ℚ) < sweepSlope a b N * (x : ℚ) + levelIntercept a N η := by
  rw [levelIndex_eq_floor ha hN]
  exact lt_of_le_of_ne (Int.floor_le _)
    (Ne.symm (levelOrd_ne_intCast ha hb hN hη hηpos x _))

/-- The ceiling of the ordinate of the level line over a natural abscissa is one more than the level
index, that ordinate being no integer. -/
theorem ceil_levelOrd (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) (x : ℕ) :
    ⌈sweepSlope a b N * (x : ℚ) + levelIntercept a N η⌉ = levelIndex a b N η x + 1 := by
  have hlt := levelIndex_lt_levelOrd ha hb hN hη hηpos (b := b) x
  rw [levelIndex_eq_floor ha hN] at hlt ⊢
  set r := sweepSlope a b N * (x : ℚ) + levelIntercept a N η with hr
  refine le_antisymm (Int.ceil_le.2 ?_) ?_
  · push_cast
    exact (Int.lt_floor_add_one r).le
  · have h1 : ((⌊r⌋ : ℤ) : ℚ) < ((⌈r⌉ : ℤ) : ℚ) := lt_of_lt_of_le hlt (Int.le_ceil r)
    have h2 : ⌊r⌋ < ⌈r⌉ := by exact_mod_cast h1
    omega

/-- The level index of a column is nonnegative: the level line is above the axis. -/
theorem levelIndex_nonneg (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ} (hηpos : 0 < η)
    (x : ℕ) : 0 ≤ levelIndex a b N η x := by
  rw [levelIndex_eq_floor ha hN]
  exact Int.le_floor.2 (by exact_mod_cast (levelOrd_pos (b := b) ha hb hN hηpos x).le)

/-- The level index is nondecreasing in the column, the level line having positive slope. -/
theorem levelIndex_le_levelIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) {x x' : ℕ}
    (h : x ≤ x') : levelIndex a b N η x ≤ levelIndex a b N η x' := by
  have hs := sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  have hx : (x : ℚ) ≤ (x' : ℚ) := by exact_mod_cast h
  rw [levelIndex_eq_floor ha hN, levelIndex_eq_floor ha hN]
  exact Int.floor_le_floor (by nlinarith)

/-! ### Listing a set of lattice points that meets each column once -/

/-- A finite set of lattice points is *column-injective* when it meets each column at most once.
Both halves of a colouring are: a crossed north step has ordinate the level index of its column and
a crossed east step has ordinate the height of the path just right of its column, so in either case
the column determines the point. -/
def ColumnInjective (S : Finset (ℕ × ℕ)) : Prop := ∀ P ∈ S, ∀ Q ∈ S, P.1 = Q.1 → P = Q

/-- The `i`-th member of a finite set of lattice points in the column listing, with the junk
default `(0, 0)` off the range. -/
noncomputable def colStep (S : Finset (ℕ × ℕ)) (i : ℕ) : ℕ × ℕ :=
  (sortByColumn S).getD i (0, 0)

/-- Inside the range the column listing lists members of the set. -/
theorem colStep_mem {S : Finset (ℕ × ℕ)} {i : ℕ} (hi : i < #S) : colStep S i ∈ S := by
  have hlen : i < (sortByColumn S).length := by rw [length_sortByColumn]; exact hi
  rw [colStep, List.getD_eq_getElem _ _ hlen]
  exact mem_sortByColumn.1 (List.getElem_mem hlen)

/-- **The column listing of a column-injective set is strictly increasing in the column**, the
listing being sorted and repetition-free. -/
theorem colStep_fst_lt {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) {i j : ℕ} (hj : j < #S)
    (hij : i < j) : (colStep S i).1 < (colStep S j).1 := by
  have hleni : i < (sortByColumn S).length := by rw [length_sortByColumn]; omega
  have hlenj : j < (sortByColumn S).length := by rw [length_sortByColumn]; exact hj
  rw [colStep, colStep, List.getD_eq_getElem _ _ hleni, List.getD_eq_getElem _ _ hlenj]
  refine lt_of_le_of_ne
    (List.pairwise_iff_getElem.1 (sortByColumn_pairwise S) i j hleni hlenj hij) fun heq => ?_
  have hpt := hcol _ (mem_sortByColumn.1 (List.getElem_mem hleni)) _
    (mem_sortByColumn.1 (List.getElem_mem hlenj)) heq
  exact absurd ((List.Nodup.getElem_inj_iff (sortByColumn_nodup S)).1 hpt) (by omega)

/-- The column listing of a column-injective set is nondecreasing in the column. -/
theorem colStep_fst_le {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) {i j : ℕ} (hj : j < #S)
    (hij : i ≤ j) : (colStep S i).1 ≤ (colStep S j).1 := by
  rcases eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact (colStep_fst_lt hcol hj h).le

/-- Every member of the set occurs in the column listing. -/
theorem exists_colStep {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP : P ∈ S) :
    ∃ i < #S, colStep S i = P := by
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 (mem_sortByColumn.2 hP)
  refine ⟨i, ?_, ?_⟩
  · rw [← length_sortByColumn S]; exact hi
  · rw [colStep, List.getD_eq_getElem _ _ hi]; exact hie

/-- **Strictly left of the `i`-th column there are at most `i` members**: every member whose column
is strictly smaller than the `i`-th one occurs earlier in the listing. -/
theorem card_filter_fst_lt_le {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) {i t : ℕ}
    (_hi : i < #S) (ht : t ≤ (colStep S i).1) : #({P ∈ S | P.1 < t}) ≤ i := by
  classical
  have hsub : {P ∈ S | P.1 < t} ⊆ (Finset.range i).image (colStep S) := by
    intro P hP
    obtain ⟨hPS, hPt⟩ := Finset.mem_filter.1 hP
    obtain ⟨j, hj, hje⟩ := exists_colStep hPS
    refine Finset.mem_image.2 ⟨j, Finset.mem_range.2 ?_, hje⟩
    by_contra hcon
    have := colStep_fst_le hcol hj (by omega : i ≤ j)
    rw [hje] at this
    omega
  calc #({P ∈ S | P.1 < t}) ≤ #((Finset.range i).image (colStep S)) := Finset.card_le_card hsub
    _ ≤ #(Finset.range i) := Finset.card_image_le
    _ = i := Finset.card_range i

/-- **Weakly left of the `i`-th column there are at least `i + 1` members**: the first `i + 1`
members of the listing all lie there, and they are distinct. -/
theorem le_card_filter_fst_lt {S : Finset (ℕ × ℕ)} (hcol : ColumnInjective S) {i t : ℕ}
    (hi : i < #S) (ht : (colStep S i).1 < t) : i + 1 ≤ #({P ∈ S | P.1 < t}) := by
  classical
  have hsub : (Finset.range (i + 1)).image (colStep S) ⊆ {P ∈ S | P.1 < t} := by
    intro P hP
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hP
    have hj' : j ≤ i := by have := Finset.mem_range.1 hj; omega
    exact Finset.mem_filter.2 ⟨colStep_mem (by omega), lt_of_le_of_lt
      (colStep_fst_le hcol hi hj') ht⟩
  have hinj : Set.InjOn (colStep S) (Finset.range (i + 1)) := by
    intro j hj j' hj' hjj'
    have hj2 : j ≤ i := by have := Finset.mem_range.1 hj; omega
    have hj2' : j' ≤ i := by have := Finset.mem_range.1 hj'; omega
    by_contra hcon
    rcases Nat.lt_or_ge j j' with h | h
    · exact absurd (congrArg Prod.fst hjj') (by
        have := colStep_fst_lt hcol (show j' < #S by omega) h; omega)
    · have h' : j' < j := by omega
      exact absurd (congrArg Prod.fst hjj') (by
        have := colStep_fst_lt hcol (show j < #S by omega) h'; omega)
  calc i + 1 = #((Finset.range (i + 1)).image (colStep S)) := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    _ ≤ #({P ∈ S | P.1 < t}) := Finset.card_le_card hsub

/-! ### The two halves of a colouring meet each column once -/

/-- The crossed north steps meet each column at most once, their ordinate being the level index of
their column. -/
theorem columnInjective_colouringNorth (ha : 0 < a) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (y : Heights a b N) :
    ColumnInjective (colouringNorth y η) := by
  rintro ⟨x, i⟩ hP ⟨x', i'⟩ hQ h
  obtain ⟨-, -, -, hi⟩ := (mem_colouringNorth_iff ha hN hη y x i).1 hP
  obtain ⟨-, -, -, hi'⟩ := (mem_colouringNorth_iff ha hN hη y x' i').1 hQ
  simp only at h
  subst h
  have : (i : ℤ) = (i' : ℤ) := by rw [hi, hi']
  exact Prod.ext rfl (by exact_mod_cast this)

/-- The crossed east steps meet each column at most once, their ordinate being the height of the
path just right of their column. -/
theorem columnInjective_colouringEast (ha : 0 < a) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (y : Heights a b N) :
    ColumnInjective (colouringEast y η) := by
  rintro ⟨x, i⟩ hP ⟨x', i'⟩ hQ h
  obtain ⟨-, hi, -, -⟩ := (mem_colouringEast_iff ha hN hη y x i).1 hP
  obtain ⟨-, hi', -, -⟩ := (mem_colouringEast_iff ha hN hη y x' i').1 hQ
  simp only at h
  subst h
  exact Prod.ext rfl (by rw [hi, hi'])

/-! ### The balance of the two halves, column by column -/

/-- Splitting a count by column: the members left of `t + 1` are those left of `t` together with
those in column `t`. -/
theorem card_filter_fst_lt_succ (S : Finset (ℕ × ℕ)) (t : ℕ) :
    #({P ∈ S | P.1 < t + 1}) = #({P ∈ S | P.1 < t}) + #({P ∈ S | P.1 = t}) := by
  classical
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.2 fun P hP hP' => by
    have h1 := (Finset.mem_filter.1 hP).2
    have h2 := (Finset.mem_filter.1 hP').2
    omega)]
  congr 1
  ext P
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · intro h
    rcases Nat.lt_or_ge P.1 t with h' | h'
    · exact Or.inl ⟨h.1, h'⟩
    · exact Or.inr ⟨h.1, by omega⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩

/-- **A column carries a crossed north step or it does not**, and the condition is the one
`HJO.Mellit.colouringNorth_column_iff` reads off the level index. -/
theorem card_filter_colouringNorth_col (ha : 0 < a) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (y : Heights a b N) {x : ℕ} (hx : x < a * N) :
    #({P ∈ colouringNorth y η | P.1 = x}) =
      if (ht y x : ℤ) ≤ levelIndex a b N η x ∧ levelIndex a b N η x < (ht y (x + 1) : ℤ)
        then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨i, hi⟩ := (colouringNorth_column_iff ha hN hη y hx).2 h
    refine Finset.card_eq_one.2 ⟨(x, i), Finset.eq_singleton_iff_unique_mem.2
      ⟨Finset.mem_filter.2 ⟨hi, rfl⟩, fun Q hQ => ?_⟩⟩
    obtain ⟨hQS, hQx⟩ := Finset.mem_filter.1 hQ
    exact columnInjective_colouringNorth ha hN hη y _ hQS _ hi hQx
  · refine Finset.card_eq_zero.2 (Finset.eq_empty_iff_forall_notMem.2 fun Q hQ => ?_)
    obtain ⟨hQS, hQx⟩ := Finset.mem_filter.1 hQ
    exact h ((colouringNorth_column_iff ha hN hη y hx).1 ⟨Q.2, by rw [← hQx]; exact hQS⟩)

/-- **A column carries a crossed east step or it does not**, and the condition is the one
`HJO.Mellit.colouringEast_column_iff` reads off the level index. -/
theorem card_filter_colouringEast_col (ha : 0 < a) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (y : Heights a b N) {x : ℕ} (hx : x < a * N) :
    #({P ∈ colouringEast y η | P.1 = x}) =
      if levelIndex a b N η x < (ht y (x + 1) : ℤ) ∧
          (ht y (x + 1) : ℤ) ≤ levelIndex a b N η (x + 1)
        then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨i, hi⟩ := (colouringEast_column_iff ha hN hη y hx).2 h
    refine Finset.card_eq_one.2 ⟨(x, i), Finset.eq_singleton_iff_unique_mem.2
      ⟨Finset.mem_filter.2 ⟨hi, rfl⟩, fun Q hQ => ?_⟩⟩
    obtain ⟨hQS, hQx⟩ := Finset.mem_filter.1 hQ
    exact columnInjective_colouringEast ha hN hη y _ hQS _ hi hQx
  · refine Finset.card_eq_zero.2 (Finset.eq_empty_iff_forall_notMem.2 fun Q hQ => ?_)
    obtain ⟨hQS, hQx⟩ := Finset.mem_filter.1 hQ
    exact h ((colouringEast_column_iff ha hN hη y hx).1 ⟨Q.2, by rw [← hQx]; exact hQS⟩)

/-- **The balance of the two halves of a colouring, read left of a column.** Left of `t` the
crossed north steps outnumber the crossed east steps by `1` if the level line is below the path at
the vertical lattice line `t` and by `0` if it is above it.

This is the alternation — that the two kinds of crossing follow one another along the
level line — proved as `HJO.Mellit.card_colouringNorth_eq_card_colouringEast` is proved here, by a
telescoping count rather than by decomposing the line into intervals. The whole
column-by-column content is the case analysis at the end: with `A` the statement that the line is
below the path at `t`, `B` that it is below the path over `(t, t+1)` and `C` that it is below the
path at `t+1`, a crossed north step in column `t` is `¬A ∧ B`, a crossed east step there is
`B ∧ ¬C`, and `[A] + [¬A ∧ B] = [B ∧ ¬C] + [C]` in all five possible states. -/
theorem card_colouringNorth_filter_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) {y : Heights a b N} (hy : IsAboveDiagonal y)
    {t : ℕ} (htN : t ≤ a * N) :
    #({P ∈ colouringNorth y η | P.1 < t}) =
      #({P ∈ colouringEast y η | P.1 < t}) +
        (if levelIndex a b N η t < (ht y t : ℤ) then 1 else 0) := by
  classical
  induction t with
  | zero =>
    have h0 : ht y 0 = 0 := hy.1
    have hI : 0 ≤ levelIndex a b N η 0 := levelIndex_nonneg (b := b) ha hb hN hηpos 0
    have hfalse : ¬ levelIndex a b N η 0 < (ht y 0 : ℤ) := by rw [h0]; omega
    simp [hfalse]
  | succ t ih =>
    have htN' : t < a * N := by omega
    have ihm := ih (by omega)
    have hmono : ht y t ≤ ht y (t + 1) := hy.2.2.1 t htN'
    have hmono' : (ht y t : ℤ) ≤ (ht y (t + 1) : ℤ) := by exact_mod_cast hmono
    have hImono : levelIndex a b N η t ≤ levelIndex a b N η (t + 1) :=
      levelIndex_le_levelIndex ha hb hN η (Nat.le_succ t)
    rw [card_filter_fst_lt_succ, card_filter_fst_lt_succ, ihm,
      card_filter_colouringNorth_col ha hN hη y htN',
      card_filter_colouringEast_col ha hN hη y htN']
    split_ifs <;> omega

/-! ### What a crossed step of a colouring says about its column -/

/-- The level-index reading of a crossed north step, as a statement about the point. -/
theorem mem_colouringNorth_spec (ha : 0 < a) (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η)
    (y : Heights a b N) {P : ℕ × ℕ} (hP : P ∈ colouringNorth y η) :
    P.1 < a * N ∧ (ht y P.1 : ℤ) ≤ levelIndex a b N η P.1 ∧
      levelIndex a b N η P.1 < (ht y (P.1 + 1) : ℤ) ∧ (P.2 : ℤ) = levelIndex a b N η P.1 := by
  obtain ⟨x, i⟩ := P
  obtain ⟨h1, h2, h3, h4⟩ := (mem_colouringNorth_iff ha hN hη y x i).1 hP
  have h2' : (ht y x : ℤ) ≤ (i : ℤ) := by exact_mod_cast h2
  have h3' : (i : ℤ) < (ht y (x + 1) : ℤ) := by exact_mod_cast h3
  exact ⟨h1, h4 ▸ h2', h4 ▸ h3', h4⟩

/-- The level-index reading of a crossed east step, as a statement about the point. -/
theorem mem_colouringEast_spec (ha : 0 < a) (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η)
    (y : Heights a b N) {P : ℕ × ℕ} (hP : P ∈ colouringEast y η) :
    P.1 < a * N ∧ P.2 = ht y (P.1 + 1) ∧ levelIndex a b N η P.1 < (P.2 : ℤ) ∧
      (P.2 : ℤ) ≤ levelIndex a b N η (P.1 + 1) := by
  obtain ⟨x, i⟩ := P
  exact (mem_colouringEast_iff ha hN hη y x i).1 hP

/-! ### The components are ordered and nondegenerate -/

/-- **The `i`-th crossed north step is weakly left of the `i`-th crossed east step.** Otherwise the
count of crossed east steps left of the `i`-th east column would exceed the count of crossed north
steps there, which `HJO.Mellit.card_colouringNorth_filter_lt` forbids. -/
theorem northCol_le_eastCol (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {i : ℕ} (hi : i < #(colouringNorth y η)) :
    (colStep (colouringNorth y η) i).1 ≤ (colStep (colouringEast y η) i).1 := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηa
  have hk : #(colouringNorth y η) = #(colouringEast y η) :=
    card_colouringNorth_eq_card_colouringEast hb hN hη hηa hy
  have hiE : i < #(colouringEast y η) := hk ▸ hi
  have hecN := (mem_colouringEast_spec ha hN hη y (colStep_mem hiE)).1
  by_contra hcon
  have hlt : (colStep (colouringEast y η) i).1 < (colStep (colouringNorth y η) i).1 := by omega
  have hbal := card_colouringNorth_filter_lt ha hb hN hη hηpos hy
    (t := (colStep (colouringEast y η) i).1 + 1) (by omega)
  have h1 : #({P ∈ colouringNorth y η | P.1 < (colStep (colouringEast y η) i).1 + 1}) ≤ i :=
    card_filter_fst_lt_le (columnInjective_colouringNorth ha hN hη y) hi (by omega)
  have h2 : i + 1 ≤ #({P ∈ colouringEast y η | P.1 < (colStep (colouringEast y η) i).1 + 1}) :=
    le_card_filter_fst_lt (columnInjective_colouringEast ha hN hη y) hiE (by omega)
  split_ifs at hbal <;> omega

/-- **The `i`-th crossed east step is strictly left of the `(i+1)`-st crossed north step.** If it
were not, the count left of that north column would put the level line below the path there, which
is exactly what having a crossed north step in that column denies. This is the
disjointness of the components. -/
theorem eastCol_lt_northCol_succ (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {i : ℕ} (hi : i + 1 < #(colouringNorth y η)) :
    (colStep (colouringEast y η) i).1 < (colStep (colouringNorth y η) (i + 1)).1 := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηa
  have hk : #(colouringNorth y η) = #(colouringEast y η) :=
    card_colouringNorth_eq_card_colouringEast hb hN hη hηa hy
  have hiE : i < #(colouringEast y η) := by omega
  obtain ⟨hncN, hncI, -, -⟩ :=
    mem_colouringNorth_spec ha hN hη y (colStep_mem (show i + 1 < #(colouringNorth y η) from hi))
  by_contra hcon
  have hle : (colStep (colouringNorth y η) (i + 1)).1 ≤ (colStep (colouringEast y η) i).1 := by
    omega
  have hbal := card_colouringNorth_filter_lt ha hb hN hη hηpos hy
    (t := (colStep (colouringNorth y η) (i + 1)).1) (by omega)
  have h1 : i + 1 ≤ #({P ∈ colouringNorth y η | P.1 < (colStep (colouringNorth y η) (i + 1)).1}) :=
    le_card_filter_fst_lt (columnInjective_colouringNorth ha hN hη y) (by omega)
      (colStep_fst_lt (columnInjective_colouringNorth ha hN hη y) hi (by omega))
  have h2 : #({P ∈ colouringEast y η | P.1 < (colStep (colouringNorth y η) (i + 1)).1}) ≤ i :=
    card_filter_fst_lt_le (columnInjective_colouringEast ha hN hη y) hiE hle
  split_ifs at hbal with h
  · omega
  · omega

/-! ### The two ends of a component, as crossing indices -/

/-- The smallest index of a crossing of the `i`-th component, the companion of
`HJO.Mellit.componentTopIndex`. -/
noncomputable def componentBotIndex (a b N : ℕ) (y : Heights a b N) (η : ℚ) (i : ℕ) : ℤ :=
  ⌈(1 + sweepSlope a b N) * componentLeft y η i + levelIntercept a N η⌉

/-- The index set of the crossings of a component runs from its bottom index to its top index. -/
theorem componentCrossingIndices_eq_Icc (a b N : ℕ) (y : Heights a b N) (η : ℚ) (i : ℕ) :
    componentCrossingIndices a b N y η i =
      Finset.Icc (componentBotIndex a b N y η i) (componentTopIndex a b N y η i) := rfl

/-- **The bottom index of a component is `x(u_i) + I_{x(u_i)} + 1`.** The left end of the component
is on the vertical lattice line through the crossed north step `u_i`, so the first crossing of the
antidiagonal at or after it is the one just above the level index of that column. -/
theorem componentBotIndex_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) (y : Heights a b N) (i : ℕ) :
    componentBotIndex a b N y η i = ((colStep (colouringNorth y η) i).1 : ℤ) +
      levelIndex a b N η (colStep (colouringNorth y η) i).1 + 1 := by
  set x := (colStep (colouringNorth y η) i).1 with hx
  have hL : componentLeft y η i = ((x : ℤ) : ℚ) := by push_cast; rfl
  rw [componentBotIndex, hL,
    show (1 + sweepSlope a b N) * ((x : ℤ) : ℚ) + levelIntercept a N η =
      ((x : ℤ) : ℚ) + (sweepSlope a b N * (x : ℚ) + levelIntercept a N η) by push_cast; ring,
    Int.ceil_intCast_add, ceil_levelOrd ha hb hN hη hηpos x]
  ring

/-- The left end of the `i`-th component is weakly below the crossing of its bottom index, hence so
is the crossing of any index at or above it. -/
theorem componentLeft_le_crossingAbscissa (hs : 0 < 1 + sweepSlope a b N) (y : Heights a b N)
    (η : ℚ) (i : ℕ) {n : ℤ} (hn : componentBotIndex a b N y η i ≤ n) :
    componentLeft y η i ≤ crossingAbscissa a b N η n := by
  have hceil := Int.le_ceil ((1 + sweepSlope a b N) * componentLeft y η i + levelIntercept a N η)
  have hcast : ((componentBotIndex a b N y η i : ℤ) : ℚ) ≤ ((n : ℤ) : ℚ) := by exact_mod_cast hn
  rw [componentBotIndex] at hcast
  rw [crossingAbscissa, le_div_iff₀ hs]
  linarith

/-- The crossing of any index at or below the top index is weakly below the right end of the
component. -/
theorem crossingAbscissa_le_componentRight (hs : 0 < 1 + sweepSlope a b N) (y : Heights a b N)
    (η : ℚ) (i : ℕ) {n : ℤ} (hn : n ≤ componentTopIndex a b N y η i) :
    crossingAbscissa a b N η n ≤ componentRight a b N y η i := by
  have hfl := Int.floor_le ((1 + sweepSlope a b N) * componentRight a b N y η i +
    levelIntercept a N η)
  have hcast : ((n : ℤ) : ℚ) ≤ ((componentTopIndex a b N y η i : ℤ) : ℚ) := by exact_mod_cast hn
  rw [componentTopIndex] at hcast
  rw [crossingAbscissa, div_le_iff₀ hs]
  nlinarith

/-- **The right end of a component lies strictly inside the column of its crossed east step.** The
level line reaches the ordinate of `w_i` after the vertical lattice line through its column, by the
first clause of `HJO.Mellit.colouring` for an east step, and before the next one, by the second —
which is an inequality of integers and cannot be an equality, that being a lattice point on the
level line. -/
theorem eastCol_lt_componentRight (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) {y : Heights a b N} {i : ℕ}
    (hi : i < #(colouringEast y η)) :
    (((colStep (colouringEast y η) i).1 : ℕ) : ℚ) < componentRight a b N y η i ∧
      componentRight a b N y η i < (((colStep (colouringEast y η) i).1 : ℕ) : ℚ) + 1 := by
  have hs := sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  obtain ⟨-, -, h3, h4⟩ := mem_colouringEast_spec ha hN hη y (colStep_mem hi)
  set x := (colStep (colouringEast y η) i).1 with hxdef
  set w := (colStep (colouringEast y η) i).2 with hwdef
  have hR : sweepSlope a b N * componentRight a b N y η i + levelIntercept a N η = (w : ℚ) :=
    sweepSlope_mul_componentRight_add hs.ne' y η i
  -- the level line is below the ordinate `w` at the column `x`
  have hlow : sweepSlope a b N * (x : ℚ) + levelIntercept a N η < (w : ℚ) := by
    rw [levelIndex_eq_floor ha hN] at h3
    have := Int.floor_lt.1 h3
    exact_mod_cast this
  -- and above it at the next column, strictly, no lattice point being on the level line
  have hhigh : (w : ℚ) < sweepSlope a b N * ((x : ℚ) + 1) + levelIntercept a N η := by
    rw [levelIndex_eq_floor ha hN] at h4
    have hle := Int.le_floor.1 h4
    have hne := levelOrd_ne_intCast (b := b) ha hb hN hη hηpos (x + 1) (w : ℤ)
    push_cast at hle hne ⊢
    exact lt_of_le_of_ne hle (Ne.symm hne)
  refine ⟨lt_of_mul_lt_mul_left (a := sweepSlope a b N) (by linarith) hs.le,
    lt_of_mul_lt_mul_left (a := sweepSlope a b N) (by linarith) hs.le⟩

/-- **The top index of a component is `x(w_i) + y(w_i)`**, the sum of the coordinates of the
crossing of its east step, which is the integer that crossing crosses. -/
theorem componentTopIndex_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) {y : Heights a b N} {i : ℕ}
    (hi : i < #(colouringEast y η)) :
    componentTopIndex a b N y η i =
      ((colStep (colouringEast y η) i).1 : ℤ) + ((colStep (colouringEast y η) i).2 : ℤ) := by
  have hs := sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  obtain ⟨h1, h2⟩ := eastCol_lt_componentRight ha hb hN hη hηpos hi
  have hR : sweepSlope a b N * componentRight a b N y η i + levelIntercept a N η =
      (((colStep (colouringEast y η) i).2 : ℕ) : ℚ) :=
    sweepSlope_mul_componentRight_add hs.ne' y η i
  rw [componentTopIndex,
    show (1 + sweepSlope a b N) * componentRight a b N y η i + levelIntercept a N η =
      componentRight a b N y η i + (((colStep (colouringEast y η) i).2 : ℤ) : ℚ) by
        push_cast; linarith,
    Int.floor_add_intCast, Int.floor_eq_iff.2 ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩]

/-! ### Each component has a crossing, and distinct components share none -/

/-- **Each component carries at least one crossing**, which is the `α_i ≥ 1` clause of
`HJO.Braid.IsSpecialBraidData`. The bottom index is `x(u_i) + I_{x(u_i)} + 1` and the top index is
`x(w_i) + y(w_i)`; the crossed north step is weakly left of the crossed east step and its column's
level index is below the ordinate of that east step, so the first sum is at most the second. -/
theorem componentBotIndex_le_componentTopIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {i : ℕ} (hi : i < #(colouringNorth y η)) :
    componentBotIndex a b N y η i ≤ componentTopIndex a b N y η i := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηa
  have hk : #(colouringNorth y η) = #(colouringEast y η) :=
    card_colouringNorth_eq_card_colouringEast hb hN hη hηa hy
  have hiE : i < #(colouringEast y η) := hk ▸ hi
  obtain ⟨-, -, h3, -⟩ := mem_colouringEast_spec ha hN hη y (colStep_mem hiE)
  have hnc := northCol_le_eastCol ha hb hN hη hηa hy hi
  have hmono := levelIndex_le_levelIndex (a := a) (b := b) (N := N) ha hb hN η hnc
  rw [componentBotIndex_eq ha hb hN hη hηpos, componentTopIndex_eq ha hb hN hη hηpos hiE]
  omega

/-- **Distinct components share no crossing index**: the top index of the `i`-th is below the bottom
index of any later one. The crossed east step of the `i`-th component is strictly left of the
crossed north step of the `(i+1)`-st — `HJO.Mellit.eastCol_lt_northCol_succ` — and the ordinate of
that east step is at most the level index of the next column, hence of the later north column. -/
theorem componentTopIndex_lt_componentBotIndex (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {i i' : ℕ} (hi' : i' < #(colouringNorth y η)) (hii' : i < i') :
    componentTopIndex a b N y η i < componentBotIndex a b N y η i' := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηa
  have hk : #(colouringNorth y η) = #(colouringEast y η) :=
    card_colouringNorth_eq_card_colouringEast hb hN hη hηa hy
  have hiE : i < #(colouringEast y η) := by omega
  obtain ⟨-, -, -, h4⟩ := mem_colouringEast_spec ha hN hη y (colStep_mem hiE)
  have hstep := eastCol_lt_northCol_succ ha hb hN hη hηa hy (i := i) (by omega)
  have hnc : (colStep (colouringNorth y η) (i + 1)).1 ≤ (colStep (colouringNorth y η) i').1 :=
    colStep_fst_le (columnInjective_colouringNorth ha hN hη y) hi' (by omega)
  have hmono := levelIndex_le_levelIndex (a := a) (b := b) (N := N) ha hb hN η
    (show (colStep (colouringEast y η) i).1 + 1 ≤ (colStep (colouringNorth y η) i').1 by omega)
  rw [componentBotIndex_eq ha hb hN hη hηpos, componentTopIndex_eq ha hb hN hη hηpos hiE]
  omega

/-! ### Listing a component downwards from its top crossing -/

/-- **Following the level line downwards by `θ` is `nx_θ` on the torus.** The step "consecutive
elements of `X_i(c)` differ by `θ`, so their fractional parts are the iterates `nx_θ^j(v_i)`" of the
usual argument: lowering the abscissa by `θ` is, read on the antidiagonal, the next-crossing map of
`HJO.Braid.nextCrossing` — provided the coordinate is not the puncture, where that map is
meaningless. -/
theorem nextCrossing_fract {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {z : ℚ} (h : Int.fract z ≠ θ) :
    Braid.nextCrossing θ (Int.fract z) = Int.fract (z - θ) := by
  have hz0 := Int.fract_nonneg z
  have hz1 := Int.fract_lt_one z
  have hkey : Int.fract (z - θ) = Int.fract (Int.fract z - θ) := by
    rw [show z - θ = Int.fract z - θ + ((⌊z⌋ : ℤ) : ℚ) by
      have := Int.fract_add_floor z; linarith, Int.fract_add_intCast]
  rw [Braid.nextCrossing, hkey]
  split_ifs with hlt
  · exact (Int.fract_eq_self.2 ⟨by linarith, by linarith⟩).symm
  · have hlt' : Int.fract z < θ := lt_of_le_of_ne (not_lt.1 hlt) h
    rw [show Int.fract z - θ = Int.fract z + 1 - θ + ((-1 : ℤ) : ℚ) by push_cast; ring,
      Int.fract_add_intCast]
    exact (Int.fract_eq_self.2 ⟨by linarith, by linarith⟩).symm

/-- Consecutive crossings are `θ` apart in abscissa, read downwards. -/
theorem crossingAbscissa_sub_sweepTheta (hs : 1 + sweepSlope a b N ≠ 0) (η : ℚ) (n : ℤ) :
    crossingAbscissa a b N η n - sweepTheta a b N = crossingAbscissa a b N η (n - 1) := by
  have h := crossingAbscissa_succ (a := a) (b := b) (N := N) hs η (n - 1)
  rw [show n - 1 + 1 = n by ring] at h
  rw [sweepTheta]
  linarith

/-- The left end of a component is nonnegative, being the column of a lattice point. -/
theorem componentLeft_nonneg (y : Heights a b N) (η : ℚ) (i : ℕ) : 0 ≤ componentLeft y η i :=
  Nat.cast_nonneg _

/-- Every crossing at or above the bottom index of a component has nonnegative abscissa. -/
theorem crossingAbscissa_nonneg (hs : 0 < 1 + sweepSlope a b N) (y : Heights a b N) (η : ℚ)
    (i : ℕ) {n : ℤ} (hn : componentBotIndex a b N y η i ≤ n) :
    0 ≤ crossingAbscissa a b N η n :=
  le_trans (componentLeft_nonneg y η i) (componentLeft_le_crossingAbscissa hs y η i hn)

/-- **A component ends inside the rectangle**, which is `HJO.Mellit.componentRight_le` with the
bound on the ordinate of the crossed east step supplied: that ordinate is a height of the path. -/
theorem componentRight_le_of_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N} {i : ℕ}
    (hi : i < #(colouringEast y η)) : componentRight a b N y η i ≤ ((a * N : ℕ) : ℚ) := by
  obtain ⟨-, h2, -, -⟩ := mem_colouringEast_spec ha hN hη y (colStep_mem hi)
  refine componentRight_le ha hb hN hηa y i ?_
  have h3 : (colStep (colouringEast y η) i).2 ≤ b * N := h2 ▸ ht_le_mul y _
  rw [colStep] at h3
  exact_mod_cast h3

/-- Every crossing at or below the top index of a component has abscissa at most `aN`. -/
theorem crossingAbscissa_le_mul (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N} {i : ℕ}
    (hi : i < #(colouringEast y η)) {n : ℤ} (hn : n ≤ componentTopIndex a b N y η i) :
    crossingAbscissa a b N η n ≤ ((a * N : ℕ) : ℚ) :=
  le_trans (crossingAbscissa_le_componentRight
    (one_add_sweepSlope_pos ha hb hN) y η i hn) (componentRight_le_of_lt ha hb hN hη hηa hi)

/-- The first component of the special-braid data of a colouring, unfolded. -/
theorem braidDataOfColouring_fst (a b N : ℕ) (y : Heights a b N) (η : ℚ) (k : ℕ) (i : Fin k) :
    (braidDataOfColouring a b N y η k).1 i =
      Int.fract (crossingAbscissa a b N η (componentTopIndex a b N y η i)) := rfl

/-- The second component of the special-braid data of a colouring, unfolded. -/
theorem braidDataOfColouring_snd (a b N : ℕ) (y : Heights a b N) (η : ℚ) (k : ℕ) (i : Fin k) :
    (braidDataOfColouring a b N y η k).2 i = #(componentCrossingIndices a b N y η i) := rfl

/-- **The `j`-th iterate of `nx_θ` at `v_i` is the torus coordinate of the crossing `j` integers
below the top one.** This is the listing of `X_i(c)` downwards from `max X_i(c)`: the
abscissae are `max X_i(c) - jθ`, and their fractional parts are the iterates of
`HJO.Braid.nextCrossing`. The hypothesis is that the `j`-th crossing down is still a crossing of the
component, without which the iterate would pass the puncture and mean nothing. -/
theorem iterate_nextCrossing_fract_crossingAbscissa (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) (y : Heights a b N) (i : ℕ) {j : ℕ}
    (hj : componentBotIndex a b N y η i ≤ componentTopIndex a b N y η i - (j : ℤ)) :
    (Braid.nextCrossing (sweepTheta a b N))^[j]
        (Int.fract (crossingAbscissa a b N η (componentTopIndex a b N y η i))) =
      Int.fract (crossingAbscissa a b N η (componentTopIndex a b N y η i - (j : ℤ))) := by
  obtain ⟨hθ0, hθ1⟩ := sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN
  have hs := one_add_sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : componentBotIndex a b N y η i ≤ componentTopIndex a b N y η i - (j : ℤ) := by
      push_cast at hj; omega
    have hidx : componentTopIndex a b N y η i - ((j + 1 : ℕ) : ℤ) =
        componentTopIndex a b N y η i - (j : ℤ) - 1 := by push_cast; ring
    rw [hidx, Function.iterate_succ_apply', ih hj',
      nextCrossing_fract hθ0 hθ1 (fract_crossingAbscissa_ne_sweepTheta ha hb hN hη hηpos
        (crossingAbscissa_nonneg hs y η i hj')),
      crossingAbscissa_sub_sweepTheta hs.ne' η _]

/-! ### The data of a colouring is special-braid data -/

/-- **The data of a colouring is special-braid data**, the lemma
`HJO.Mellit.isSpecialBraidData_braidDataOfColouring`: in the situation of
`HJO.Mellit.braidDataOfColouring`, `(v, α)` is special-braid data of rank `k` at slope `s_{a,b,N}`,
with `θ = 1/(1 + s_{a,b,N})`.

The rank `k` is the number of members of the colouring that are north steps of the realising path,
which by `HJO.Mellit.card_colouringNorth_eq_card_colouringEast` is also the number that are east
steps, so there are exactly `k` pairs `(v_i, α_i)`. Each clause of `HJO.Braid.IsSpecialBraidData` is
one step of the proof: `θ(s+1) = 1` is `HJO.Mellit.sweepTheta_mul`; the positions lie in `(0,1)`
because no crossing sits on a vertical lattice line; each `α_i ≥ 1` by the endpoint argument
`HJO.Mellit.componentBotIndex_le_componentTopIndex`; no iterate is the puncture `θ`; and the
iterates are pairwise distinct because two crossings with the same coordinate have the same index —
`HJO.Mellit.crossingAbscissa_injOn_fract`, the coprimality argument — and distinct components share
no index, `HJO.Mellit.componentTopIndex_lt_componentBotIndex`.

The hypotheses are `η` an admissible level with `η > aN` and `c` an admissible colouring
at `η`; as everywhere in this layer the realising path is taken directly rather than through the
colouring, and `0 < a`, `0 < b`, `0 < N` are carried — the standing hypothesis is
`1 < a < b`, and on a degenerate rectangle the slope is not positive and the level line is not a
line the crossings can be read along. -/
@[hjo "lem_braid_colouring_is_data"]
theorem isSpecialBraidData_braidDataOfColouring (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    Braid.IsSpecialBraidData (sweepSlope a b N) (sweepTheta a b N) #(colouringNorth y η)
      (braidDataOfColouring a b N y η #(colouringNorth y η)).1
      (braidDataOfColouring a b N y η #(colouringNorth y η)).2 := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηa
  have hspos := sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  have hs := one_add_sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  have hk : #(colouringNorth y η) = #(colouringEast y η) :=
    card_colouringNorth_eq_card_colouringEast hb hN hη hηa hy
  -- the two ends of each component
  have hbot : ∀ i : Fin #(colouringNorth y η),
      componentBotIndex a b N y η i ≤ componentTopIndex a b N y η i := fun i =>
    componentBotIndex_le_componentTopIndex ha hb hN hη hηa hy i.isLt
  -- a multiplicity counts the indices between them
  have hcard : ∀ i : Fin #(colouringNorth y η), ∀ j : ℕ,
      j < (braidDataOfColouring a b N y η #(colouringNorth y η)).2 i →
        componentBotIndex a b N y η i ≤ componentTopIndex a b N y η i - (j : ℤ) := by
    intro i j hj
    rw [braidDataOfColouring_snd, componentCrossingIndices_eq_Icc, Int.card_Icc] at hj
    have hj' : ((j : ℕ) : ℤ) <
        ((componentTopIndex a b N y η i + 1 - componentBotIndex a b N y η i).toNat : ℤ) := by
      exact_mod_cast hj
    rw [Int.toNat_of_nonneg (by have := hbot i; omega)] at hj'
    omega
  refine ⟨hspos, sweepTheta_mul hs.ne', fun i => ?_, fun i => ?_, fun i j hj => ?_,
    fun i i' j j' hj hj' heq => ?_⟩
  · -- the positions lie in `(0, 1)`
    rw [braidDataOfColouring_fst]
    refine Set.mem_Ioo.2 ⟨lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm
      (fract_crossingAbscissa_ne_zero ha hb hN hη hηpos ?_)), Int.fract_lt_one _⟩
    exact crossingAbscissa_nonneg hs y η i (hbot i)
  · -- every multiplicity is at least one
    rw [braidDataOfColouring_snd, componentCrossingIndices_eq_Icc]
    exact Finset.card_pos.2 ⟨componentBotIndex a b N y η i,
      Finset.mem_Icc.2 ⟨le_rfl, hbot i⟩⟩
  · -- no iterate meets the puncture
    rw [braidDataOfColouring_fst,
      iterate_nextCrossing_fract_crossingAbscissa ha hb hN hη hηpos y i (hcard i j hj)]
    exact fract_crossingAbscissa_ne_sweepTheta ha hb hN hη hηpos
      (crossingAbscissa_nonneg hs y η i (hcard i j hj))
  · -- the iterates are pairwise distinct
    rw [braidDataOfColouring_fst,
      iterate_nextCrossing_fract_crossingAbscissa ha hb hN hη hηpos y i (hcard i j hj),
      braidDataOfColouring_fst,
      iterate_nextCrossing_fract_crossingAbscissa ha hb hN hη hηpos y i' (hcard i' j' hj')] at heq
    have hiE : (i : ℕ) < #(colouringEast y η) := hk ▸ i.isLt
    have hiE' : (i' : ℕ) < #(colouringEast y η) := hk ▸ i'.isLt
    have hidx : componentTopIndex a b N y η i - (j : ℤ) =
        componentTopIndex a b N y η i' - (j' : ℤ) :=
      crossingAbscissa_injOn_fract ha hb hN
        (crossingAbscissa_nonneg hs y η i (hcard i j hj))
        (crossingAbscissa_le_mul ha hb hN hη hηa hiE (by have := hcard i j hj; omega))
        (crossingAbscissa_nonneg hs y η i' (hcard i' j' hj'))
        (crossingAbscissa_le_mul ha hb hN hη hηa hiE' (by have := hcard i' j' hj'; omega))
        heq
    have hii' : (i : ℕ) = (i' : ℕ) := by
      rcases lt_trichotomy (i : ℕ) (i' : ℕ) with hlt | heqi | hgt
      · have h1 := componentTopIndex_lt_componentBotIndex ha hb hN hη hηa hy i'.isLt hlt
        have h2 := hcard i' j' hj'
        omega
      · exact heqi
      · have h1 := componentTopIndex_lt_componentBotIndex ha hb hN hη hηa hy i.isLt hgt
        have h2 := hcard i j hj
        omega
    refine ⟨Fin.ext hii', ?_⟩
    rw [hii'] at hidx
    omega

/-- **`HJO.Mellit.isSpecialBraidData_braidDataOfColouring` on the running example.** The
`(2,3)`-path of heights `(0,2,3)` at `η = 21/2` has exactly one crossed north step, so its data is
special-braid data of rank `1`: the hypotheses of that theorem are satisfiable and at that rank no
clause of `HJO.Braid.IsSpecialBraidData` is vacuous. -/
theorem isSpecialBraidData_braidDataOfColouring_example :
    Braid.IsSpecialBraidData (sweepSlope 2 3 1) (sweepTheta 2 3 1) 1
      (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (21 / 2) 1).1
      (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (21 / 2) 1).2 := by
  have hk : #(colouringNorth (![0, 2, 3] : Heights 2 3 1) (21 / 2)) = 1 := by
    rw [colouringNorth_and_colouringEast_example.1, Finset.card_singleton]
  have h := isSpecialBraidData_braidDataOfColouring (a := 2) (b := 3) (N := 1)
    (η := 21 / 2) (y := (![0, 2, 3] : Heights 2 3 1)) (by norm_num) (by norm_num) (by norm_num)
    ⟨10, by norm_num⟩ (by norm_num) (by decide)
  rwa [hk] at h

end HJO.Mellit
