/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.DyckAttackSets
public import HJO.Shuffle.BraidData
public import HJO.Shuffle.SweepGeometry
public import HJO.Shuffle.SweepStandardisation
public meta import HJO.Attr

/-! # The rank-order listing of the north steps, and the attack set in positions

The sweep process lists the north steps of an above-diagonal `(aN, bN)`-path as
`u_1, …, u_{bN}` **in strictly increasing order of above-diagonal rank**, and indexes the attack
set `𝒜(P̂)`, the marked pairs, the letters of a word and the square partner `P̂'` by positions in
that listing. This library indexes a north step by the **height of its foot**: the step named by
`i : Fin (bN)` has foot `(Â_{i+1}, i)` and rank `HJO.Paths.stepRank y i`. Nothing sorts.

Nine statements about the sweep are made over the listing, and every one of them needs the same
bridge.
This file is that bridge, built once:

* the two indexings are the same set of north steps (`HJO.Paths.northSteps_eq_image`), so an
  above-diagonal path has exactly `bN` north steps;
* the rank is injective on them (`HJO.Paths.stepRank_injective`, proved earlier), so the rank
  order is a total order and the listing is well defined;
* `HJO.Paths.stepIndex` is the position of a north step in that listing, `0`-based, and it is a
  bijection of `Fin (bN)` whose inverse `HJO.Paths.stepAt` is the `u_{j}`;
* `HJO.Paths.attackPositions` is `𝒜(P̂)` read through it, on which the lemma
  `HJO.Paths.isTransitiveAttackSet_attackPositions` becomes `HJO.Dyck.IsTransitiveAttackSet`, and so
  `𝒜(P̂)` acquires the square partner `P̂'` of `HJO.Dyck.attackPartner` and everything proved about
  it.

## Main definitions

* `HJO.Paths.stepFoot`: the foot of the north step named by a height, as a lattice point.
* `HJO.Paths.stepIndex`: the `0`-based position of a north step in the increasing-rank listing.
* `HJO.Paths.stepAt`: its inverse — the north step at a given position, the `u_{j+1}`.
* `HJO.Paths.attackPositions`: the attack set `𝒜(P̂)` relabelled to `0`-based rank-order positions.

## Main results

* `HJO.Paths.card_northSteps`: an above-diagonal path has exactly `bN` north steps.
* `HJO.Paths.stepRank_injective_of_isAboveDiagonal`: distinct north steps of an above-diagonal
  path have distinct ranks, from the `0 < a` form already in
  `HJO/Shuffle/SweepStandardisation.lean`.
* `HJO.Paths.stepIndex_lt_stepIndex_iff`: the position order **is** the rank order. This is the one
  statement the nine consumers rely on, and the one an off-by-one or a reversal would break.
* `HJO.Paths.stepAt_stepIndex`, `HJO.Paths.stepIndex_stepAt`: the two round trips.
* `HJO.Paths.mem_attackPositions_iff`: membership in the relabelled attack set.
* `HJO.Paths.isTransitiveAttackSet_attackPositions`.
* `HJO.Paths.isSquareDyck_partner`: `𝒜(P̂)` is the attack set of a square Dyck path of length `bN`,
  namely its square partner. This is
  `HJO.Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet` instantiated at a path.

## Implementation notes

`stepIndex` is `HJO.Braid.entryRank (stepRank y)` shifted down by one. `entryRank` is `1`-based —
the index counts itself — and the positions are `1`-based too, so the `u_j`
is `stepAt y ⟨j - 1, _⟩` and its `x'_j` is `attackPartner (attackPositions y) (j - 1) + 1`. That
shift is done here, once, rather than in nine consumers.

`entryRank` is used rather than a sorting function because the *order-reflection*
`HJO.Braid.entryRank_lt_entryRank_iff` is the whole content of the relabelling and needs no sort: a
position order agrees with a rank order exactly when the position is the rank's own counting
function. Going through `Finset.sort` would additionally have to prove that the sorted list's index
is that counting function.

The positivity `0 < a * N` is never a hypothesis. It follows from the existence of a north step:
above-diagonality forces `ŷ_{aN} = bN` and `ŷ_0 = 0`, so `a * N = 0` makes `b * N = 0` and
`Fin (b * N)` empty (`HJO.Paths.mul_pos_of_isAboveDiagonal`). Every statement below that needs the
attack window to be positive derives it that way, so no lemma carries a hypothesis a consumer would
have to discharge.

`attackPositions` is an image rather than a `Finset` comprehension over positions, so that it is
manifestly the relabelling of `sweepAttack` and not a second definition of the same set;
`mem_attackPositions_iff` is the comprehension, proved from the bijection.

## References

This file serves the definition `HJO.Paths.sweepAttack` (the listing and the attack set), the lemmas
`HJO.Paths.isTransitiveAttackSet_attackPositions` and `HJO.Paths.abovePointRank_injOn`, and
`HJO.Dyck.attackPartner` with `HJO.Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet`. The
indexing discrepancy this file resolves is the one recorded in the module docstring of
`HJO/Shuffle/Sweep.lean`.
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### The two indexings of the north steps -/

/-- The foot of the north step of an above-diagonal path named by the height `i` of that foot: the
lattice point `(Â_{i+1}, i)`. This is the north step `u` of the listing, named as
`HJO.Paths.northSteps` names it. -/
def stepFoot (y : Heights a b N) (i : Fin (b * N)) : ℕ × ℕ :=
  (ParkingFunctions.aboveColumn y (i : ℕ), (i : ℕ))

@[simp]
theorem stepFoot_fst (y : Heights a b N) (i : Fin (b * N)) :
    (stepFoot y i).1 = ParkingFunctions.aboveColumn y (i : ℕ) := rfl

@[simp]
theorem stepFoot_snd (y : Heights a b N) (i : Fin (b * N)) : (stepFoot y i).2 = (i : ℕ) := rfl

theorem stepRank_eq_abovePointRank_stepFoot (y : Heights a b N) (i : Fin (b * N)) :
    stepRank y i = ParkingFunctions.abovePointRank a b N (stepFoot y i).1 (stepFoot y i).2 := rfl

/-- **The rectangle has a column as soon as the path has a north step.** Above-diagonality forces
`ŷ_0 = 0` and `ŷ_{aN} = bN`, so `a * N = 0` collapses `b * N` to `0` and `Fin (b * N)` is empty.
This is what lets every statement below derive the positivity of the attack window instead of
carrying it. -/
theorem mul_pos_of_isAboveDiagonal {y : Heights a b N} (hy : IsAboveDiagonal y)
    (i : Fin (b * N)) : 0 < a * N := by
  rcases Nat.eq_zero_or_pos (a * N) with h | h
  · have hb : b * N = 0 := by rw [← hy.2.1, h, hy.1]
    have := i.isLt
    omega
  · exact h

/-- **The north steps of an above-diagonal path are exactly the feet named by heights.** The image
of `HJO.Paths.stepFoot` over all of `Fin (bN)` is `HJO.Paths.northSteps`, which is the sentence
"on an above-diagonal path the index type `Fin (bN)` is the set of north steps on the nose". -/
theorem northSteps_eq_image {y : Heights a b N} (hy : IsAboveDiagonal y) :
    northSteps y = (univ : Finset (Fin (b * N))).image (stepFoot y) := by
  ext P
  simp only [mem_image, mem_univ, true_and]
  constructor
  · intro hP
    obtain ⟨h1, h2⟩ := (ParkingFunctions.mem_northSteps_iff_eq_aboveColumn hy).1
      (show (P.1, P.2) ∈ northSteps y from hP)
    exact ⟨⟨P.2, h1⟩, by rw [stepFoot]; exact Prod.ext h2.symm rfl⟩
  · rintro ⟨i, rfl⟩
    exact (ParkingFunctions.mem_northSteps_iff_eq_aboveColumn hy).2 ⟨i.isLt, rfl⟩

/-- Naming a north step by the height of its foot is injective: the height is the second
coordinate. -/
theorem stepFoot_injective (y : Heights a b N) : Function.Injective (stepFoot y) :=
  fun _ _ h => Fin.val_injective (congrArg Prod.snd h)

/-- **An above-diagonal `(aN, bN)`-path has exactly `bN` north steps.** The heights rise from `0` to
`bN`, so each height below `bN` is the foot of exactly one north step. -/
@[simp]
theorem card_northSteps {y : Heights a b N} (hy : IsAboveDiagonal y) :
    #(northSteps y) = b * N := by
  rw [northSteps_eq_image hy, card_image_of_injective _ (stepFoot_injective y), card_univ,
    Fintype.card_fin]

/-! ### The rank order on the north steps -/

/-- The rank is injective on the north steps, in the form this file uses it: above-diagonality
supplies `0 < a` through `HJO.Paths.mul_pos_of_isAboveDiagonal`, and the injectivity itself is
`HJO.Paths.stepRank_injective` of `HJO/Shuffle/SweepStandardisation.lean`, which needs only
`0 < a` and is not restated here. The *point*-level statement is
`HJO.Paths.abovePointRank_injOn`, of which this one is the case at the feet of north steps. -/
theorem stepRank_injective_of_isAboveDiagonal {y : Heights a b N} (hy : IsAboveDiagonal y) :
    Function.Injective (stepRank y) := fun i j h => by
  have h0 : 0 < a * N := mul_pos_of_isAboveDiagonal hy i
  exact stepRank_injective (Nat.pos_of_ne_zero fun hc => by simp [hc] at h0) y h

/-- **The `0`-based position of a north step in the increasing-rank listing.** The `u_j`
is the step with `stepIndex = j - 1`, the listing being `1`-based.

It is `HJO.Braid.entryRank (stepRank y)` shifted down by one: the rank of an entry counts the
entries weakly below it, so it is the `1`-based position in the increasing listing, and the shift is
done here rather than in each consumer. -/
def stepIndex (y : Heights a b N) (i : Fin (b * N)) : Fin (b * N) :=
  ⟨Braid.entryRank (stepRank y) i - 1, by
    have h1 := Braid.entryRank_pos (stepRank y) i
    have h2 := Braid.entryRank_le (stepRank y) i
    have h3 := i.isLt
    omega⟩

theorem stepIndex_val (y : Heights a b N) (i : Fin (b * N)) :
    ((stepIndex y i : Fin (b * N)) : ℕ) + 1 = Braid.entryRank (stepRank y) i := by
  have h1 := Braid.entryRank_pos (stepRank y) i
  simp only [stepIndex]
  omega

/-- **The position order is the rank order.** This is the one property the nine consumers rely on:
a statement indexed by position in the increasing-rank listing and the same statement indexed by
foot height say the same thing, because `stepIndex` reflects the order.

A reversal or an off-by-one in `stepIndex` would typecheck and silently renumber every consumer, so
this iff is also what the value checks at the end of the file are checking. -/
theorem stepIndex_lt_stepIndex_iff (y : Heights a b N) (i j : Fin (b * N)) :
    stepIndex y i < stepIndex y j ↔ stepRank y i < stepRank y j := by
  rw [← Braid.entryRank_lt_entryRank_iff (stepRank y) i j, Fin.lt_def,
    ← Nat.add_lt_add_iff_right (k := 1), stepIndex_val, stepIndex_val]

/-- The position determines the step: `stepIndex` is injective, hence a bijection of `Fin (bN)`. -/
theorem stepIndex_injective {y : Heights a b N} (hy : IsAboveDiagonal y) :
    Function.Injective (stepIndex y) := fun i j h =>
  Braid.entryRank_injective (stepRank_injective_of_isAboveDiagonal hy) (by
    rw [← stepIndex_val y i, ← stepIndex_val y j, h])

/-- The increasing-rank listing as an equivalence: position `p` names the north step
`stepAt y p`. -/
noncomputable def stepIndexEquiv {y : Heights a b N} (hy : IsAboveDiagonal y) :
    Fin (b * N) ≃ Fin (b * N) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (stepIndex_injective hy))

/-- **The north step at a given position of the increasing-rank listing**: the step
`u_{p+1}` of the listing, named by the height of its foot. -/
noncomputable def stepAt {y : Heights a b N} (hy : IsAboveDiagonal y) (p : Fin (b * N)) :
    Fin (b * N) :=
  (stepIndexEquiv hy).symm p

@[simp]
theorem stepIndex_stepAt {y : Heights a b N} (hy : IsAboveDiagonal y) (p : Fin (b * N)) :
    stepIndex y (stepAt hy p) = p :=
  (stepIndexEquiv hy).apply_symm_apply p

@[simp]
theorem stepAt_stepIndex {y : Heights a b N} (hy : IsAboveDiagonal y) (i : Fin (b * N)) :
    stepAt hy (stepIndex y i) = i :=
  (stepIndexEquiv hy).symm_apply_apply i

/-- The listing is increasing in the rank, which is what "in strictly increasing order of
above-diagonal rank" says. -/
theorem stepRank_stepAt_lt_iff {y : Heights a b N} (hy : IsAboveDiagonal y) (p q : Fin (b * N)) :
    stepRank y (stepAt hy p) < stepRank y (stepAt hy q) ↔ p < q := by
  rw [← stepIndex_lt_stepIndex_iff, stepIndex_stepAt, stepIndex_stepAt]

/-! ### The attack set in rank-order positions -/

/-- **The attack set `𝒜(P̂)` read in `0`-based rank-order positions.** The sweep process indexes
`𝒜(P̂)` by positions in the increasing-rank listing; `HJO.Paths.sweepAttack` indexes it by foot
heights. This is the image of the second under the relabelling, so it is the set and not a second
definition of it. -/
def attackPositions (y : Heights a b N) : Finset (ℕ × ℕ) :=
  (sweepAttack y).image fun p => ((stepIndex y p.1 : ℕ), (stepIndex y p.2 : ℕ))

/-- **Membership in the relabelled attack set, at a pair of north steps.** The positions of two
north steps attack in `attackPositions` exactly when the steps attack in `sweepAttack`: the
relabelling is faithful, neither losing nor inventing a pair. Injectivity of `stepIndex` is what
rules out inventing one. -/
theorem mem_attackPositions {y : Heights a b N} (hy : IsAboveDiagonal y) (s t : Fin (b * N)) :
    (((stepIndex y s : ℕ), (stepIndex y t : ℕ)) ∈ attackPositions y) ↔ (s, t) ∈ sweepAttack y := by
  simp only [attackPositions, mem_image, Prod.ext_iff]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    have e1 : p.1 = s := stepIndex_injective hy (Fin.val_injective h1)
    have e2 : p.2 = t := stepIndex_injective hy (Fin.val_injective h2)
    rw [← e1, ← e2]
    exact hp
  · exact fun h => ⟨(s, t), h, rfl, rfl⟩

/-- Membership in the relabelled attack set, at a pair of positions: `(m, n)` attacks exactly when
the north steps standing at those positions do. -/
theorem mem_attackPositions_iff {y : Heights a b N} (hy : IsAboveDiagonal y) {m n : ℕ} :
    (m, n) ∈ attackPositions y ↔
      ∃ hm : m < b * N, ∃ hn : n < b * N,
        (stepAt hy ⟨m, hm⟩, stepAt hy ⟨n, hn⟩) ∈ sweepAttack y := by
  constructor
  · intro h
    simp only [attackPositions, mem_image, Prod.ext_iff] at h
    obtain ⟨p, hp, h1, h2⟩ := h
    have hm : m < b * N := by rw [← h1]; exact (stepIndex y p.1).isLt
    have hn : n < b * N := by rw [← h2]; exact (stepIndex y p.2).isLt
    refine ⟨hm, hn, ?_⟩
    have e1 : (⟨m, hm⟩ : Fin (b * N)) = stepIndex y p.1 := Fin.val_injective h1.symm
    have e2 : (⟨n, hn⟩ : Fin (b * N)) = stepIndex y p.2 := Fin.val_injective h2.symm
    rw [e1, e2, stepAt_stepIndex, stepAt_stepIndex]
    exact hp
  · rintro ⟨hm, hn, h⟩
    have := (mem_attackPositions hy (stepAt hy ⟨m, hm⟩) (stepAt hy ⟨n, hn⟩)).2 h
    rwa [stepIndex_stepAt, stepIndex_stepAt] at this

/-- **The attack set is a staircase.** In rank-order positions `𝒜(P̂)` is a transitive attack set on
`{1, …, bN}`: an attacking pair splits at every intermediate position, and the set lies in the
window `1 ≤ i < j ≤ bN`. This is `HJO.Paths.isTransitiveAttackSet_attackPositions`, stated through
`HJO.Dyck.IsTransitiveAttackSet` because that predicate *is* the condition — the staircase
condition's two clauses are its two splitting fields verbatim — and because stating it that way lets
`HJO.Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet` apply with no bridging. -/
@[hjo "lem_sweep_attack_staircase"]
theorem isTransitiveAttackSet_attackPositions {y : Heights a b N} (hy : IsAboveDiagonal y) :
    Dyck.IsTransitiveAttackSet (b * N) (attackPositions y) := by
  have key : ∀ m n : ℕ, (m, n) ∈ attackPositions y →
      ∃ hm : m < b * N, ∃ hn : n < b * N,
        stepRank y (stepAt hy ⟨m, hm⟩) < stepRank y (stepAt hy ⟨n, hn⟩) ∧
          stepRank y (stepAt hy ⟨n, hn⟩) <
            stepRank y (stepAt hy ⟨m, hm⟩) + attackWindow a N := fun m n h => by
    obtain ⟨hm, hn, h⟩ := (mem_attackPositions_iff hy).1 h
    simp only [sweepAttack, mem_filter, mem_univ, true_and] at h
    exact ⟨hm, hn, h.1, h.2⟩
  refine ⟨fun p hp => ?_, fun p hp => ?_, ?_, ?_⟩
  · obtain ⟨hm, hn, h1, -⟩ := key p.1 p.2 hp
    have := (stepRank_stepAt_lt_iff hy ⟨p.1, hm⟩ ⟨p.2, hn⟩).1 h1
    exact this
  · obtain ⟨-, hn, -⟩ := key p.1 p.2 hp
    exact hn
  · intro j j' j'' hjj' hj'j'' hR
    obtain ⟨hm, hn, h1, h2⟩ := key j j'' hR
    have hj' : j' < b * N := hj'j''.trans hn
    have hlt1 : stepRank y (stepAt hy ⟨j, hm⟩) < stepRank y (stepAt hy ⟨j', hj'⟩) :=
      (stepRank_stepAt_lt_iff hy _ _).2 hjj'
    have hlt2 : stepRank y (stepAt hy ⟨j', hj'⟩) < stepRank y (stepAt hy ⟨j'', hn⟩) :=
      (stepRank_stepAt_lt_iff hy _ _).2 hj'j''
    exact (mem_attackPositions_iff hy).2 ⟨hm, hj',
      by simp only [sweepAttack, mem_filter, mem_univ, true_and]; exact ⟨hlt1, by omega⟩⟩
  · intro j j' j'' hjj' hj'j'' hR
    obtain ⟨hm, hn, h1, h2⟩ := key j j'' hR
    have hj' : j' < b * N := hj'j''.trans hn
    have hlt1 : stepRank y (stepAt hy ⟨j, hm⟩) < stepRank y (stepAt hy ⟨j', hj'⟩) :=
      (stepRank_stepAt_lt_iff hy _ _).2 hjj'
    have hlt2 : stepRank y (stepAt hy ⟨j', hj'⟩) < stepRank y (stepAt hy ⟨j'', hn⟩) :=
      (stepRank_stepAt_lt_iff hy _ _).2 hj'j''
    exact (mem_attackPositions_iff hy).2 ⟨hj', hn,
      by simp only [sweepAttack, mem_filter, mem_univ, true_and]; exact ⟨hlt2, by omega⟩⟩

/-- **The square partner of an above-diagonal path is a square Dyck path of length `bN` whose attack
set is `𝒜(P̂)`.** This is `HJO.Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet` at a
path: `HJO.Dyck.attackPartner` applied to `attackPositions y` is the `P̂'`, `0`-based, and
`HJO.Dyck.isSquareDyck_and_attackSet_eq_of_isTransitiveAttackSet` supplies both halves from
`isTransitiveAttackSet_attackPositions`. -/
theorem isSquareDyck_partner {y : Heights a b N} (hy : IsAboveDiagonal y) :
    Dyck.IsSquareDyck (b * N)
        (fun p : Fin (b * N) => Dyck.attackPartner (attackPositions y) (p : ℕ)) ∧
      Dyck.attackSet (fun p : Fin (b * N) =>
        Dyck.attackPartner (attackPositions y) (p : ℕ)) = attackPositions y :=
  Dyck.isSquareDyck_attackPartner (isTransitiveAttackSet_attackPositions hy)

/-! ### Value checks on the worked example

The counterexample path — `a = 1`, `b = 2`, `N = 2`, heights `(0, 2, 4)`, quoted in the
docstring of `HJO.Paths.sweepMarked` — is the right test for this file, because on it the
relabelling is a **genuine non-identity permutation**. The above-diagonal rank is `6y - 11x`, so the
four north steps, named by the height of their feet, are

  `i = 0 : (0,0)` rank `0`, `i = 1 : (0,1)` rank `6`, `i = 2 : (1,2)` rank `1`,
  `i = 3 : (1,3)` rank `7`,

and the increasing-rank listing is `(0,0), (1,2), (0,1), (1,3)` — exactly the listing that docstring
quotes. So `stepIndex` is the transposition `[0, 2, 1, 3]`, and an off-by-one or a reversed order
would be visible here where on a path with heights in rank order it would not. -/

/-- The worked example: the above-diagonal `(2, 4)`-path with heights `(0, 2, 4)`. -/
def example_1_2_2 : Heights 1 2 2 := ![0, 2, 4]

theorem isAboveDiagonal_example : IsAboveDiagonal example_1_2_2 := by decide

/-- The ranks of the four north steps, by the height of the foot: `0, 6, 1, 7`. Not increasing in
the height, which is the whole reason this file exists. -/
theorem stepRank_example : ∀ i : Fin 4, stepRank example_1_2_2 i = ![0, 6, 1, 7] i := by decide

/-- **The relabelling on the example is the transposition `[0, 2, 1, 3]`.** The step at height `1`
stands third in the increasing-rank listing and the step at height `2` stands second, so the
permutation is not the identity and the value check has content. -/
theorem stepIndex_example :
    ∀ i : Fin 4, ((stepIndex example_1_2_2 i : Fin 4) : ℕ) = ![0, 2, 1, 3] i := by decide

/-- The attack set in foot heights. -/
theorem sweepAttack_example : sweepAttack example_1_2_2 = {(0, 2), (2, 1), (1, 3)} := by decide

/-- **The attack set in rank-order positions.** Note that `(2, 1)` is an attacking pair of *heights*
with the larger height first; after relabelling it becomes `(1, 2)`, increasing. That the relabelled
set consists of increasing pairs is the first field of
`isTransitiveAttackSet_attackPositions`, and here it is the content rather than a formality. -/
theorem attackPositions_example :
    attackPositions example_1_2_2 = {(0, 1), (1, 2), (2, 3)} := by decide

/-- **End to end: the square partner of the example path is `(0, 0, 1, 2)`.** Read `1`-based, the
partner `x'` is `(1, 1, 2, 3)`. The attack set of that square Dyck path is the relabelled attack
set of the path, which is `isSquareDyck_partner` at a concrete input. -/
theorem attackPartner_example : ∀ p : Fin 4,
    Dyck.attackPartner (attackPositions example_1_2_2) (p : ℕ) = ![0, 0, 1, 2] p := by
  intro p
  have h : attackPositions example_1_2_2 = Dyck.attackSet (![0, 0, 1, 2] : Fin 4 → ℕ) := by decide
  rw [h, Dyck.attackPartner_attackSet (by decide) p]

end HJO.Paths
