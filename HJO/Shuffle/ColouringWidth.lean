/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ColouringComponents
public import HJO.Shuffle.ColouringLevel
public import HJO.Shuffle.SweepWordV0
public meta import HJO.Attr

/-! # The invariant of a colouring lies in the module of its width

`HJO.Mellit.dsc_mem_piece`: for an admissible level `η` and an admissible colouring
`c` at `η`, the invariant `D_{η,c}` lies in `V_k`, where `k` is the number of members of `c` that
are north steps of an above-diagonal path realising `c`.

## Main definitions

* `HJO.Mellit.levelWidth` — how many north steps of a path the level line crosses, that is
  `#HJO.Mellit.colouringNorth`, the *north half* of `HJO.Mellit.colouring`.
* `HJO.Mellit.colouringWidth` — the `k`, read off `c` and `η` alone.

## Main results

* `HJO.Mellit.filter_colouring_lt` — the members of `c_η(P̂)` below the level are exactly the
  crossed north steps, which with `HJO.Mellit.colouring_inter_northSteps` makes
  `HJO.Mellit.colouringWidth` the `k`.
* `HJO.Mellit.nextWidth_eq_levelWidth` — at the lowest swept point above the level, the codomain
  index of the event operator is the level width. This is the "taking `ϱ = η` is
  legitimate".
* `HJO.Mellit.partialSweepWord_mem_piece` — `W_η(P̂)` carries `V_0` into `V_k`.
* `HJO.Mellit.dsc_mem_piece`.

## Implementation notes

### `k` is read off `c`, not off a path

One may define `k` through a path `P̂` realising `c` and then argue that the value does not
depend on the choice. Here `HJO.Mellit.colouringWidth a b N η c := #{p ∈ c : rk̂(p) < η}` is a
function of `c` and `η` only, and `HJO.Mellit.colouringWidth_colouring` identifies it with the
level width of *every* realising path, which is exactly that independence. The
separation is exact and needs no hypothesis: a crossed north step has `rk̂(u) < η` and a crossed
east step has `η < rk̂(v)`, by the two halves of `HJO.Mellit.colouring` themselves.

### Where the `ϱ = η` goes

The width at the last factor of the partial word is
`#{u : rk̂(u) ≤ ϱ < rk̂(u) + ω}` "for any `ϱ` with `η ≤ ϱ < rk̂(P_r)`", and one takes `ϱ = η`. The
argument here is the same balance the proof of `HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent`
runs, with the *level* `η` in place of the upper point of a rank-adjacent pair: the live steps at
the lowest swept point `p` above `η` and the north steps the line at `η` crosses differ by the step
with foot `p` on one side and the step with head `p` on the other
(`HJO.Mellit.sdiff_liveSteps_colouringNorth` and `HJO.Mellit.sdiff_colouringNorth_liveSteps`), and
those two indicators are exactly the ones `HJO.Paths.mem_northSteps_iff_eventType` and
`HJO.Paths.isSweepHead_iff_eventType` read off the event type at `p`. So
`nextWidth y p = levelWidth y η` case by case, which is the identification needed.

That `η` is the rank of no lattice point — `HJO.Mellit.pointRank_ne_of_isAdmissibleLevel` — is used
twice and is not decoration: without it a north step could have `rk̂(u) = η`, and it would be
counted by `liveSteps` and not by `levelSteps`, breaking both set differences.

### The nondegeneracy hypotheses

`0 < a` and `0 < N` make the rank injective on the strip, which is what turns "two swept points of
equal rank" into "the same point", and make the attack window positive, without which a north step
would never be live anywhere. `0 < b` is **not** needed, although
`HJO.Mellit.sweepWord_mem_piece_zero` carries it: that lemma reads the origin as the last factor of
the full word, where `0 < b` is what makes the event type there `B`, and the partial word's last
factor is the lowest point *above the level*, whose codomain index is computed here from the balance
rather than from the event type at a named point.

`HJO.Mellit.dsc_mem_piece` asks nothing of `c`: at an inadmissible `c` the invariant is `0`, which
lies in every piece, so the conclusion holds with no admissibility hypothesis.

## References

The north half of a colouring is `HJO.Mellit.colouringNorth`, defined with
`HJO.Mellit.card_colouringNorth_eq_card_colouringEast`; no second copy of it is made here.
Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 4.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The width of a level and the width of a colouring -/

/-- **The width of a level on a path**: how many north steps of `P̂` the level line at `η` crosses,
`HJO.Mellit.colouringNorth` being the north half of `HJO.Mellit.colouring`. This is the
`k` of the invariant, read on a path. -/
def levelWidth (y : Heights a b N) (η : ℚ) : ℕ := #(colouringNorth y η)

/-- **The width of a colouring**: the number of its members lying below the level. By
`HJO.Mellit.filter_colouring_lt` and `HJO.Mellit.colouring_inter_northSteps` these are exactly the
members that are north steps of any realising path, so this is the `k` read off `c` and
`η` alone — in particular the independence of the choice of path is built into the definition
rather than argued for. -/
def colouringWidth (a b N : ℕ) (η : ℚ) (c : Finset (ℕ × ℕ)) : ℕ :=
  #{p ∈ c | (pointRank a b N p : ℚ) < η}

/-- **The colouring, restricted to the level's lower side, is the set of crossed north steps.** A
crossed north step has `rk̂(u) < η` and a crossed east step has `η < rk̂(v)`, so the two halves of
`HJO.Mellit.colouring` are separated by the level with nothing to prove about either. -/
theorem filter_colouring_lt (y : Heights a b N) (η : ℚ) :
    {p ∈ colouring y η | (pointRank a b N p : ℚ) < η} = colouringNorth y η := by
  rw [colouring_eq_union, Finset.filter_union,
    Finset.filter_true_of_mem (fun x hx => (Finset.mem_filter.1 hx).2.1),
    Finset.filter_false_of_mem (fun x hx => not_lt.2 (le_of_lt (Finset.mem_filter.1 hx).2.2)),
    Finset.union_empty]

/-- **`colouringWidth` is the level width of every realising path**, which is the statement
"`k` does not depend on which such `P̂` is fixed". -/
theorem colouringWidth_colouring (y : Heights a b N) (η : ℚ) :
    colouringWidth a b N η (colouring y η) = levelWidth y η := by
  rw [colouringWidth, filter_colouring_lt, levelWidth]

/-! ### The width at the lowest swept point above the level -/

/-- An admissible level is the rank of no swept point: the swept region lies in the rectangle, and
`HJO.Mellit.pointRank_ne_of_isAdmissibleLevel` applies there. -/
private theorem pointRank_ne_of_mem_sweptRegion {y : Heights a b N} {η : ℚ}
    (hη : IsAdmissibleLevel η) {P : ℕ × ℕ} (hP : P ∈ sweptRegion y) :
    ((pointRank a b N P : ℤ) : ℚ) ≠ η := by
  obtain ⟨h1, -, h3⟩ := mem_sweptRegion.1 hP
  exact pointRank_ne_of_isAdmissibleLevel hη a b N h1 (h3.trans (ht_le_mul y _))

section Balance

variable {y : Heights a b N} {η : ℚ} {p : ℕ × ℕ}

/-- **The live north steps at the lowest swept point above the level that the line at the level
does not cross are exactly those whose foot is that point.** A step live at `p` and not crossed at
`η` has `η < rk̂(u) ≤ rk̂(p)`, so its foot is itself a swept point above the level, whence
`rk̂(p) ≤ rk̂(u)` by minimality and the two points coincide. -/
theorem sdiff_liveSteps_colouringNorth (hy : IsAboveDiagonal y) (ha : 0 < a) (hN : 0 < N)
    (hη : IsAdmissibleLevel η) (hp : p ∈ sweptAbove y η)
    (hmin : ∀ R ∈ sweptAbove y η, pointRank a b N p ≤ pointRank a b N R) :
    liveSteps y p \ colouringNorth y η = {u ∈ northSteps y | u = p} := by
  obtain ⟨hpS, hpη⟩ := Finset.mem_filter.1 hp
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
  have hωq : (0 : ℚ) < (attackWindow a N : ℚ) := by exact_mod_cast hω
  ext u
  rw [Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hlive, hnlev⟩
    rw [liveSteps, Finset.mem_filter] at hlive
    obtain ⟨hun, h1, h2⟩ := hlive
    refine ⟨hun, ?_⟩
    have hsw := mem_sweptRegion_of_mem_northSteps hy hun
    -- the line at `η` is strictly below the head of `u`
    have h2q : ((pointRank a b N p : ℤ) : ℚ) <
        ((pointRank a b N u : ℤ) : ℚ) + (attackWindow a N : ℚ) := by
      have : ((pointRank a b N p : ℤ) : ℚ) <
          (((pointRank a b N u + attackWindow a N : ℤ)) : ℚ) := by exact_mod_cast h2
      push_cast at this ⊢
      linarith
    have hhigh : η < ((pointRank a b N u : ℤ) : ℚ) + (attackWindow a N : ℚ) := lt_trans hpη h2q
    -- so `u` is not crossed only because its foot is at or above the level
    have hlow : ¬ ((pointRank a b N u : ℤ) : ℚ) < η := by
      intro hlt
      exact hnlev (Finset.mem_filter.2 ⟨hun, hlt, hhigh⟩)
    have hne : ((pointRank a b N u : ℤ) : ℚ) ≠ η :=
      pointRank_ne_of_mem_sweptRegion hη hsw.1
    have habove : η < ((pointRank a b N u : ℤ) : ℚ) := lt_of_le_of_ne (not_lt.1 hlow) (Ne.symm hne)
    have hge : pointRank a b N p ≤ pointRank a b N u :=
      hmin u (Finset.mem_filter.2 ⟨hsw.1, habove⟩)
    have heq : abovePointRank a b N u.1 u.2 = abovePointRank a b N p.1 p.2 := by
      simp only [pointRank] at h1 hge
      omega
    obtain ⟨e1, e2⟩ := abovePointRank_injOn (b := b) ha hN
      (le_of_lt (mem_northSteps_iff.1 hun).1) (mem_sweptRegion.1 hpS).1 heq
    exact Prod.ext e1 e2
  · rintro ⟨hun, rfl⟩
    refine ⟨Finset.mem_filter.2 ⟨hun, le_rfl, by omega⟩, ?_⟩
    intro hlev
    exact absurd (Finset.mem_filter.1 hlev).2.1 (not_lt.2 (le_of_lt hpη))

/-- **The north steps the line at the level crosses that are not live at the lowest swept point
above it are exactly those whose head is that point.** Such a step has its head above the level,
hence swept and above the level, so its head is ranked at or above `p`; and its foot is ranked
below `p`, so the head is `p` itself. -/
theorem sdiff_colouringNorth_liveSteps (hy : IsAboveDiagonal y) (ha : 0 < a) (hN : 0 < N)
    (hη : IsAdmissibleLevel η) (hp : p ∈ sweptAbove y η)
    (hmin : ∀ R ∈ sweptAbove y η, pointRank a b N p ≤ pointRank a b N R) :
    colouringNorth y η \ liveSteps y p = {u ∈ northSteps y | (u.1, u.2 + 1) = p} := by
  obtain ⟨hpS, hpη⟩ := Finset.mem_filter.1 hp
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
  have hωq : (0 : ℚ) < (attackWindow a N : ℚ) := by exact_mod_cast hω
  ext u
  rw [Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hlev, hnlive⟩
    rw [colouringNorth, Finset.mem_filter] at hlev
    obtain ⟨hun, hlow, hhigh⟩ := hlev
    refine ⟨hun, ?_⟩
    have hsw := mem_sweptRegion_of_mem_northSteps hy hun
    have hhead : abovePointRank a b N u.1 (u.2 + 1) =
        abovePointRank a b N u.1 u.2 + attackWindow a N := abovePointRank_succ a b N u.1 u.2
    -- the foot is below `p`
    have hfoot : pointRank a b N u ≤ pointRank a b N p := by
      have : ((pointRank a b N u : ℤ) : ℚ) < ((pointRank a b N p : ℤ) : ℚ) :=
        lt_trans hlow hpη
      exact le_of_lt (by exact_mod_cast this)
    -- so the failure of liveness is a failure of the upper bound
    have hup : pointRank a b N u + (attackWindow a N : ℤ) ≤ pointRank a b N p := by
      by_contra hcon
      exact hnlive (Finset.mem_filter.2 ⟨hun, hfoot, by simp only [pointRank] at hcon ⊢; omega⟩)
    -- and the head is a swept point above the level, hence ranked at or above `p`
    have hheadmem : (u.1, u.2 + 1) ∈ sweptAbove y η := by
      refine Finset.mem_filter.2 ⟨hsw.2, ?_⟩
      have : ((pointRank a b N (u.1, u.2 + 1) : ℤ) : ℚ) =
          ((pointRank a b N u : ℤ) : ℚ) + (attackWindow a N : ℚ) := by
        simp only [pointRank] at hhead ⊢
        rw [hhead]
        push_cast
        ring
      rw [this]
      exact hhigh
    have hge := hmin _ hheadmem
    have heq : abovePointRank a b N u.1 (u.2 + 1) = abovePointRank a b N p.1 p.2 := by
      simp only [pointRank] at hge hup hhead ⊢
      omega
    obtain ⟨h1, h2⟩ := mem_northSteps_iff.1 hun
    obtain ⟨e1, e2⟩ := abovePointRank_injOn (b := b) ha hN (le_of_lt h1)
      (mem_sweptRegion.1 hpS).1 heq
    exact Prod.ext e1 e2
  · rintro ⟨hun, hhd⟩
    have hsw := mem_sweptRegion_of_mem_northSteps hy hun
    have hhead : abovePointRank a b N u.1 (u.2 + 1) =
        abovePointRank a b N u.1 u.2 + attackWindow a N := abovePointRank_succ a b N u.1 u.2
    have hpeq : pointRank a b N p = pointRank a b N u + (attackWindow a N : ℤ) := by
      simp only [pointRank] at hhead ⊢
      rw [← hhd]
      exact hhead
    have hpeqq : ((pointRank a b N p : ℤ) : ℚ) =
        ((pointRank a b N u : ℤ) : ℚ) + (attackWindow a N : ℚ) := by
      rw [hpeq]; push_cast; ring
    have hhigh : η < ((pointRank a b N u : ℤ) : ℚ) + (attackWindow a N : ℚ) := by
      rw [← hpeqq]; exact hpη
    have hlow : ((pointRank a b N u : ℤ) : ℚ) < η := by
      rcases lt_trichotomy ((pointRank a b N u : ℤ) : ℚ) η with h | h | h
      · exact h
      · exact absurd h (pointRank_ne_of_mem_sweptRegion hη hsw.1)
      · have hge := hmin u (Finset.mem_filter.2 ⟨hsw.1, h⟩)
        exfalso
        have : (0 : ℤ) < (attackWindow a N : ℤ) := by exact_mod_cast hω
        omega
    refine ⟨Finset.mem_filter.2 ⟨hun, hlow, hhigh⟩, ?_⟩
    intro hlive
    obtain ⟨-, -, h2⟩ := Finset.mem_filter.1 hlive
    simp only [pointRank] at hpeq h2
    omega

/-- **The balance between the live steps at the lowest swept point above the level and the steps
the level line crosses.** The two sets differ by the step with foot `p` on one side and the step
with head `p` on the other, and both corrections are `0` or `1`. This is the identity that lets
one take `ϱ = η` in the computation of the adjusted width. -/
theorem card_levelWidth_balance (hy : IsAboveDiagonal y) (ha : 0 < a) (hN : 0 < N)
    (hη : IsAdmissibleLevel η) (hp : p ∈ sweptAbove y η)
    (hmin : ∀ R ∈ sweptAbove y η, pointRank a b N p ≤ pointRank a b N R) :
    #{u ∈ northSteps y | (u.1, u.2 + 1) = p} + sweepWidth y p
      = #{u ∈ northSteps y | u = p} + levelWidth y η := by
  rw [sweepWidth, levelWidth, ← sdiff_liveSteps_colouringNorth hy ha hN hη hp hmin,
    ← sdiff_colouringNorth_liveSteps hy ha hN hη hp hmin, Finset.card_sdiff_add_card,
    Finset.card_sdiff_add_card, Finset.union_comm]

/-- **The codomain index at the lowest swept point above the level is the level width.** This is
the statement "taking `ϱ = η` is legitimate, and the value is
`#{u : rk̂(u) < η < rk̂(u) + ω} = k`": the two corrections of
`HJO.Mellit.card_levelWidth_balance` are the indicators `HJO.Paths.mem_northSteps_iff_eventType` and
`HJO.Paths.isSweepHead_iff_eventType` read off the event type at `p`, which is exactly how
`HJO.Mellit.nextWidth` adjusts the width. -/
theorem nextWidth_eq_levelWidth (hy : IsAboveDiagonal y) (ha : 0 < a) (hN : 0 < N)
    (hη : IsAdmissibleLevel η) (hp : p ∈ sweptAbove y η)
    (hmin : ∀ R ∈ sweptAbove y η, pointRank a b N p ≤ pointRank a b N R) :
    nextWidth y p = levelWidth y η := by
  have hpS : p ∈ sweptRegion y := (Finset.mem_filter.1 hp).1
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
  have hbal := card_levelWidth_balance hy ha hN hη hp hmin
  have hfoot1 : p ∈ northSteps y → #{u ∈ northSteps y | u = p} = 1 := fun h => by
    simp [Finset.filter_eq', h]
  have hfoot0 : p ∉ northSteps y → #{u ∈ northSteps y | u = p} = 0 := fun h => by
    simp [Finset.filter_eq', h]
  have hhead1 : IsSweepHead y p → #{u ∈ northSteps y | (u.1, u.2 + 1) = p} = 1 := by
    rintro ⟨w, hw, hwP⟩
    have hsingle : {u ∈ northSteps y | (u.1, u.2 + 1) = p} = {w} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_singleton]
      refine ⟨fun hv => ?_, fun hv => ?_⟩
      · have hvw := hv.2.trans hwP.symm
        have h1 : v.1 = w.1 := by simpa using congrArg Prod.fst hvw
        have h2 : v.2 = w.2 := by
          have := congrArg Prod.snd hvw
          simp only at this
          omega
        exact Prod.ext h1 h2
      · rw [hv]; exact ⟨hw, hwP⟩
    rw [hsingle, Finset.card_singleton]
  have hhead0 : ¬IsSweepHead y p → #{u ∈ northSteps y | (u.1, u.2 + 1) = p} = 0 := fun h => by
    rw [Finset.card_eq_zero]
    exact Finset.filter_eq_empty_iff.2 fun {v} hv hvP => h ⟨v, hv, hvP⟩
  have hfoot' := mem_northSteps_iff_eventType (y := y) (P := p) hpS
  have hhead' := isSweepHead_iff_eventType hy hpS
  cases hev : eventType y p with
  | A =>
    rw [hfoot0 fun h => by simpa [hev] using hfoot'.1 h,
      hhead1 (hhead'.2 (Or.inl hev))] at hbal
    have hn : nextWidth y p = sweepWidth y p + 1 := by rw [nextWidth, hev]
    omega
  | B =>
    rw [hfoot1 (hfoot'.2 (Or.inl hev)), hhead0 fun h => by simpa [hev] using hhead'.1 h] at hbal
    have hn : nextWidth y p = sweepWidth y p - 1 := by rw [nextWidth, hev]
    have hpos : 1 ≤ sweepWidth y p := by
      rw [sweepWidth, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
      exact ⟨p, (Finset.mem_filter.2 ⟨mem_northSteps_iff_eventType hpS |>.2 (Or.inl hev),
        le_rfl, by omega⟩ : p ∈ liveSteps y p)⟩
    omega
  | C =>
    rw [hfoot1 (hfoot'.2 (Or.inr hev)), hhead1 (hhead'.2 (Or.inr hev))] at hbal
    have hn : nextWidth y p = sweepWidth y p := by rw [nextWidth, hev]
    omega
  | D =>
    rw [hfoot0 fun h => by simpa [hev] using hfoot'.1 h,
      hhead0 fun h => by simpa [hev] using hhead'.1 h] at hbal
    have hn : nextWidth y p = sweepWidth y p := by rw [nextWidth, hev]
    omega
  | E =>
    rw [hfoot0 fun h => by simpa [hev] using hfoot'.1 h,
      hhead0 fun h => by simpa [hev] using hhead'.1 h] at hbal
    have hn : nextWidth y p = sweepWidth y p := by rw [nextWidth, hev]
    omega

end Balance

/-! ### The rank listing of the part above the level -/

/-- **Consecutive points of the rank listing of the part of the swept region above a level are
rank-adjacent in the whole swept region.** The part above a level is an up-set for the rank, so a
swept point ranked between two of its members is itself above the level and so appears in the
listing. -/
theorem isChain_rankAdjacent_sortByRank_sweptAbove {y : Heights a b N} (ha : 0 < a) (hN : 0 < N)
    (η : ℚ) : (sortByRank a b N (sweptAbove y η)).IsChain (RankAdjacent a b N y) := by
  have hpw := sortByRank_pairwise a b N (sweptAbove y η)
  have hnd := sortByRank_nodup a b N (sweptAbove y η)
  simp only [pointRank, List.pairwise_iff_getElem] at hpw
  rw [List.isChain_iff_getElem]
  intro i hi
  have hmI' : (sortByRank a b N (sweptAbove y η))[i] ∈ sweptAbove y η :=
    mem_sortByRank.1 (List.getElem_mem (by omega))
  have hmI1' : (sortByRank a b N (sweptAbove y η))[i + 1] ∈ sweptAbove y η :=
    mem_sortByRank.1 (List.getElem_mem hi)
  have hmI : (sortByRank a b N (sweptAbove y η))[i] ∈ sweptRegion y :=
    (Finset.mem_filter.1 hmI').1
  have hmI1 : (sortByRank a b N (sweptAbove y η))[i + 1] ∈ sweptRegion y :=
    (Finset.mem_filter.1 hmI1').1
  have hstrict : abovePointRank a b N (sortByRank a b N (sweptAbove y η))[i].1
        (sortByRank a b N (sweptAbove y η))[i].2 <
      abovePointRank a b N (sortByRank a b N (sweptAbove y η))[i + 1].1
        (sortByRank a b N (sweptAbove y η))[i + 1].2 := by
    rcases eq_or_lt_of_le (hpw i (i + 1) (by omega) hi (by omega)) with heq | hlt
    · obtain ⟨e1, e2⟩ := abovePointRank_injOn (b := b) ha hN
        (mem_sweptRegion.1 hmI).1 (mem_sweptRegion.1 hmI1).1 heq
      have hij : (sortByRank a b N (sweptAbove y η))[i]
          = (sortByRank a b N (sweptAbove y η))[i + 1] := Prod.ext e1 e2
      exact absurd (hnd.getElem_inj_iff.1 hij) (by omega)
    · exact hlt
  refine ⟨hmI, hmI1, hstrict, fun R hR hbetween => ?_⟩
  obtain ⟨hb1, hb2⟩ := hbetween
  have hRabove : R ∈ sweptAbove y η := by
    refine Finset.mem_filter.2 ⟨hR, lt_of_lt_of_le (Finset.mem_filter.1 hmI').2 ?_⟩
    have : ((abovePointRank a b N (sortByRank a b N (sweptAbove y η))[i].1
        (sortByRank a b N (sweptAbove y η))[i].2 : ℤ) : ℚ) ≤
        ((abovePointRank a b N R.1 R.2 : ℤ) : ℚ) := by exact_mod_cast le_of_lt hb1
    simpa only [pointRank] using this
  obtain ⟨j, hj, hjR⟩ := List.getElem_of_mem (mem_sortByRank.2 hRabove)
  have hRj : abovePointRank a b N R.1 R.2
      = abovePointRank a b N (sortByRank a b N (sweptAbove y η))[j].1
          (sortByRank a b N (sweptAbove y η))[j].2 := by rw [hjR]
  rcases Nat.lt_or_ge j i with hjlt | hjge
  · have := hpw j i hj (by omega) hjlt
    omega
  rcases eq_or_lt_of_le hjge with hje | hilt
  · subst hje
    omega
  rcases eq_or_lt_of_le (show i + 1 ≤ j by omega) with hje | hjgt
  · subst hje
    omega
  · have := hpw (i + 1) j hi hj hjgt
    omega

/-- A sorted list's last entry is maximal for the sort key. The private copy in
`HJO.Shuffle.SweepWordV0` is unreachable from here. -/
private theorem le_getLast_of_pairwise {α : Type*} {f : α → ℤ} : ∀ (l : List α) (h : l ≠ []),
    l.Pairwise (fun x z => f x ≤ f z) → ∀ z ∈ l, f z ≤ f (l.getLast h) := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons p t ih =>
    intro h hpw z hz
    rcases t with _ | ⟨r, t'⟩
    · rw [List.mem_singleton] at hz
      rw [hz]
      exact le_rfl
    · obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hpw
      rcases List.mem_cons.1 hz with rfl | hzt
      · exact h1 _ (List.getLast_mem (List.cons_ne_nil r t'))
      · exact ih (List.cons_ne_nil r t') h2 z hzt

/-! ### The partial sweep word on the graded pieces -/

/-- **The level width vanishes above every rank.** If no swept point outranks the level then no
north step is crossed: the head of a north step is swept and outranks its foot by `ω`. -/
theorem levelWidth_eq_zero_of_sweptAbove_eq_empty {y : Heights a b N} (hy : IsAboveDiagonal y)
    {η : ℚ} (h : sweptAbove y η = ∅) : levelWidth y η = 0 := by
  rw [levelWidth, Finset.card_eq_zero]
  refine Finset.filter_eq_empty_iff.2 fun {u} hu hcon => ?_
  have hsw := mem_sweptRegion_of_mem_northSteps hy hu
  have hhead : abovePointRank a b N u.1 (u.2 + 1) =
      abovePointRank a b N u.1 u.2 + attackWindow a N := abovePointRank_succ a b N u.1 u.2
  have hmem : (u.1, u.2 + 1) ∈ sweptAbove y η := by
    refine Finset.mem_filter.2 ⟨hsw.2, ?_⟩
    have heq : ((pointRank a b N (u.1, u.2 + 1) : ℤ) : ℚ) =
        ((pointRank a b N u : ℤ) : ℚ) + (attackWindow a N : ℚ) := by
      simp only [pointRank] at hhead ⊢
      rw [hhead]; push_cast; ring
    rw [heq]
    exact hcon.2
  rw [h] at hmem
  simp at hmem

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The partial sweep word carries `V_0` into `V_k`, with `k` the level width.** The grading
chains along the rank listing of the part of the swept region above the level exactly as it does
along the whole listing in `HJO.Mellit.sweepWord_mem_piece_zero`: the highest-ranked swept point has
width `0`, and the codomain index of the last factor — the operator of the *lowest* point above the
level, applied last — is the level width by `HJO.Mellit.nextWidth_eq_levelWidth`. -/
theorem partialSweepWord_mem_piece (q u : L) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (ha : 0 < a) (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η)
    {F : Total L} (hF : F ∈ piece L 0) :
    partialSweepWord q u y η F ∈ piece L (levelWidth y η) := by
  rcases Finset.eq_empty_or_nonempty (sweptAbove y η) with hempty | hne
  · have hall : ∀ P ∈ sweptRegion y, (pointRank a b N P : ℚ) ≤ η := by
      intro P hP
      by_contra hcon
      have : P ∈ sweptAbove y η := Finset.mem_filter.2 ⟨hP, not_le.1 hcon⟩
      rw [hempty] at this
      simp at this
    rw [partialSweepWord_of_forall_le q u y η hall,
      levelWidth_eq_zero_of_sweptAbove_eq_empty hy hempty]
    simpa using hF
  obtain ⟨P0, hP0⟩ := hne
  have hlne : sortByRank a b N (sweptAbove y η) ≠ [] :=
    List.ne_nil_of_mem (mem_sortByRank.2 hP0)
  obtain ⟨p, t, hlt⟩ := List.exists_cons_of_ne_nil hlne
  have hpw : (p :: t).Pairwise fun P Q =>
      abovePointRank a b N P.1 P.2 ≤ abovePointRank a b N Q.1 Q.2 :=
    hlt ▸ sortByRank_pairwise a b N (sweptAbove y η)
  have hmemcons : ∀ R, R ∈ sweptAbove y η → R ∈ p :: t := fun R hR =>
    hlt ▸ mem_sortByRank.2 hR
  have hpmem : p ∈ sweptAbove y η :=
    mem_sortByRank.1 (by rw [hlt]; exact List.mem_cons_self ..)
  have hmin : ∀ R ∈ sweptAbove y η, pointRank a b N p ≤ pointRank a b N R := by
    intro R hR
    rcases List.mem_cons.1 (hmemcons R hR) with rfl | hRt
    · exact le_rfl
    · exact (List.pairwise_cons.1 hpw).1 R hRt
  set Q := (p :: t).getLast (List.cons_ne_nil p t) with hQ
  have hQmem : Q ∈ sweptAbove y η :=
    mem_sortByRank.1 (by rw [hlt]; exact List.getLast_mem (List.cons_ne_nil p t))
  have hQmax : ∀ R ∈ sweptRegion y,
      abovePointRank a b N R.1 R.2 ≤ abovePointRank a b N Q.1 Q.2 := by
    intro R hR
    by_cases hRa : η < (pointRank a b N R : ℚ)
    · exact le_getLast_of_pairwise (f := fun P => abovePointRank a b N P.1 P.2) (p :: t)
        (List.cons_ne_nil p t) hpw R (hmemcons R (Finset.mem_filter.2 ⟨hR, hRa⟩))
    · have h1 : pointRank a b N R ≤ pointRank a b N p := by
        have hRq : (pointRank a b N R : ℚ) < (pointRank a b N p : ℚ) :=
          lt_of_le_of_lt (not_lt.1 hRa) (Finset.mem_filter.1 hpmem).2
        exact le_of_lt (by exact_mod_cast hRq)
      have h2 : pointRank a b N p ≤ pointRank a b N Q := hmin Q hQmem
      simp only [pointRank] at h1 h2
      omega
  have hmain := prod_mem_piece_of_isChain q u hy ha hN t p
    (hlt ▸ isChain_rankAdjacent_sortByRank_sweptAbove (y := y) ha hN η) (F := F)
    (by rw [← hQ, sweepWidth_eq_zero_of_maximal hy hQmax]; exact hF)
  rw [partialSweepWord, hlt, ← nextWidth_eq_levelWidth hy ha hN hη hpmem hmin]
  exact hmain

/-- **The invariant of a colouring lies in the module of its width.**
For an admissible level `η`, `D_{η,c} ∈ V_k` with `k` the number of members of `c` that are north
steps of a realising path — which by `HJO.Mellit.colouring_inter_northSteps` and
`HJO.Mellit.filter_colouring_lt` is `HJO.Mellit.colouringWidth a b N η c`, a function of `c`
and `η` alone.

Nothing is asked of `c`: at an inadmissible colouring the sum is empty and the value `0`, which
lies in every piece. Each summand is `W_η(P̂_τ)(1)` for a path `P̂_τ` realising `c`
(`HJO.Mellit.traceRep_spec`), so `HJO.Mellit.partialSweepWord_mem_piece` places it in the piece of
that path's level width, and every realising path has the same one. -/
@[hjo "lem_colouring_dsc_width"]
theorem dsc_mem_piece (q u : L) (ha : 0 < a) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (c : Finset (ℕ × ℕ)) :
    dsc q u a b N η c ∈ piece L (colouringWidth a b N η c) := by
  rw [dsc]
  refine sum_mem fun τ hτ => ?_
  obtain ⟨hy, hc, -⟩ := traceRep_spec hτ
  have hwidth : colouringWidth a b N η c = levelWidth (traceRep a b N η c τ) η := by
    rw [← colouringWidth_colouring (traceRep a b N η c τ) η, hc]
  rw [hwidth]
  exact partialSweepWord_mem_piece q u hy ha hN hη (one_mem _)

end HJO.Mellit
