/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitOriginTransfer

/-! # The level drop at a point the path does not sweep: the fourth clause of the recursion

Iterating `HJO.Mellit.eq_dsc_of_recursion_step_everywhere` down the levels forces a case Mellit's
Theorem 4.2 never mentions. A level drop is bracketed by `HJO.Mellit.Isolates a b N X Y ηlo ηhi`,
which isolates the rank of *one* lattice point `(X, Y)` of the rectangle, and the chain of drops
from the top of the rectangle to a given level must cross the rank of **every** lattice point in
between. But the three clauses now available — `HJO.Mellit.SweepRecursionACD`,
`HJO.Mellit.SweepRecursionBE` and `HJO.Mellit.SweepRecursionBOrigin` — all have
`(X, Y) ∈ sweptRegion y` among their hypotheses, and a lattice point strictly above the path `y` is
swept by no clause at all. This file settles that case.

## Which levels move the colouring, and why the answer is simpler than it looks

`HJO/Shuffle/MellitThm58Transfer.lean` records the obligation as "the colouring moves both when the
level passes a rank and when it passes a rank *plus* the attack window". The second half turns out
to be the first half again: by `HJO.Paths.abovePointRank_succ` the head of a north step outranks its
foot by exactly `ω`, so `rk̂(u) + ω = rk̂(u + (0,1))` is itself the rank of a lattice point — and,
for a north step `u = (x, i)` of `y`, of a point `(x, i+1)` with `i + 1 ≤ ŷ_{x+1}`, hence a point of
`sweptRegion y`. The same holds of the other three thresholds `HJO.Mellit.colouring` compares
against the level: the foot `u`, the east step `v` and its right end `v + (1,0)` are all swept by
`y`. So **every transition level of `η ↦ colouring y η` is the rank of a point of `sweptRegion y`**,
and `HJO.Mellit.colouring_eq_of_notMem_sweptRegion` is that statement in the form the iteration
uses: across a bracketed drop whose isolated point `y` does not sweep, the colouring of `y` does not
move at all.

That is the good news. The bad news is that the colouring not moving is *not* enough, because
`HJO.Mellit.dsc` is a sum over the traces of the whole fibre of the colouring, and the fibre is
indexed by paths, not by `y`. A path `z` sharing `y` 's colouring may sweep `(X, Y)` even though
`y` does not, and then `z` 's own trace does move. Two facts close that gap.

*Below the level the fibre cannot see the point at all.*
`HJO.Mellit.notMem_sweptRegion_of_colouring_lo_eq`: an above-diagonal path with `y` 's colouring at
`ηlo` does not sweep `(X, Y)` either. The colouring at `ηlo` records the crossed north step of the
column of `X` at the ordinate `Y - 1` and the crossed east step at the ordinate `Y`, and a path
reaching `Y` in that column is caught by one or the other.

*Above the level it can, and the extra paths contribute nothing new.*
`HJO.Mellit.exists_notMem_sweptRegion_colouring_hi_eq`: a path `z` with `y` 's colouring at `ηhi`
that does sweep `(X, Y)` must do so with `ŷ_{X+1} = Y` exactly, and is then the splice
`HJO.Mellit.raiseFrom w X Y` of a path `w` that does not sweep it — `HJO.Mellit.lowerAt`, the
one-column lowering, produces `w`. Since `HJO.Mellit.colouring_hi_raiseFrom` and
`HJO.Mellit.levelTrace_raiseFrom` say the splice changes neither the colouring nor the trace above
the level, `z` contributes the trace of `w`, which the fibre below the level already has.

Together they give `HJO.Mellit.traceIndex_eq_of_notMem_sweptRegion` and hence
`HJO.Mellit.dsc_lo_eq_dsc_hi_of_notMem_sweptRegion`: **at a bracketed drop whose isolated point the
path does not sweep, the invariant does not change.**

## What this settles

`HJO.Mellit.SweepRecursionUnswept` is that identity asked of a candidate `R`, and
`HJO.Mellit.dsc_sweepRecursionUnswept` inhabits it. It is a *fourth* clause, and none of the other
three constrains `R` at an unswept point: the `A`/`C`/`D` clause and the `BE` clause both require
`(X, Y) ∈ sweptRegion y`, which is exactly what fails, and the origin clause is about the bracketing
of `(0, 0)` alone — which is not this bracketing, the rank being injective on the rectangle, and in
any case the origin is swept by every above-diagonal path. So what the braid side must satisfy on
Mellit's route is two clauses more than his Theorem 4.2 states, not one. (That the fourth clause
does not *follow* from the other three is argued this way, by inspection of their hypotheses, and
not by exhibiting a candidate `R` that satisfies the three and fails the fourth.)

Unlike the three, this clause carries no operator: it says the value is *unchanged*. That is why it
costs no genericity. `0 < a`, `0 < b` and `0 < N` are all that is spent — the same three the drop
lemmas carry, `0 < b` for the strict drop of the rank along an east step and `0 < a`, `0 < N` for
the injectivity of the rank on the rectangle — and no inverse is introduced, so there is no excluded
value of `q` or `u` and the identity holds at every `q` and `u` in a field. In particular the
`(q - 1)⁻¹` of `HJO.Sweep.corner` and the `(q u)⁻¹` of `HJO.Sweep.zop` do not enter.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-! ### Reading a height vector off its height function -/

/-- Two height vectors with the same height function are equal. `HJO.Paths.ht` reads the entry at
every index of the rectangle, so it determines the vector. -/
theorem heights_eq_of_ht_eq {y z : Heights a b N} (h : ∀ r, ht y r = ht z r) : y = z := by
  funext r
  exact Fin.val_injective ((ht_coe y r).symm.trans ((h (r : ℕ)).trans (ht_coe z r)))

/-- `HJO.Paths.mem_sweptRegion` at a pair written out, so that the two coordinates are literals
rather than projections and `omega` can see them. -/
theorem mem_sweptRegion_pair {y : Heights a b N} {X Y : ℕ} :
    ((X, Y) : ℕ × ℕ) ∈ sweptRegion y ↔
      X ≤ a * N ∧ b * X ≤ a * Y ∧ Y ≤ ht y (X + 1) :=
  Paths.mem_sweptRegion

/-! ### The one-column lowering -/

/-- The path `z` with its height at the single abscissa `X + 1` replaced by `v`: the inverse of the
splice `HJO.Mellit.raiseFrom` in the one situation this file needs it, where `z` touches the level
line at `(X, Y)` from below and is to be pushed off it. Total in `v`: the lemmas ask for whatever
monotonicity they need. -/
def lowerAt (z : Heights a b N) (X : ℕ) (v : Fin (b * N + 1)) : Heights a b N :=
  fun r => if (r : ℕ) = X + 1 then v else z r

/-- Away from the lowered abscissa the heights are untouched. -/
theorem ht_lowerAt_of_ne (z : Heights a b N) {X : ℕ} (v : Fin (b * N + 1)) {r : ℕ}
    (hr : r ≠ X + 1) : ht (lowerAt z X v) r = ht z r := by
  by_cases h : r < a * N + 1
  · rw [show r = ((⟨r, h⟩ : Fin (a * N + 1)) : ℕ) from rfl, ht_coe, ht_coe]
    simp [lowerAt, hr]
  · rw [ht_of_gt _ (by omega), ht_of_gt _ (by omega)]

/-- At the lowered abscissa the height is the new value. -/
theorem ht_lowerAt_self (z : Heights a b N) {X : ℕ} (v : Fin (b * N + 1))
    (hX : X + 1 < a * N + 1) : ht (lowerAt z X v) (X + 1) = (v : ℕ) := by
  rw [show X + 1 = ((⟨X + 1, hX⟩ : Fin (a * N + 1)) : ℕ) from rfl, ht_coe]
  simp [lowerAt]

/-- **Raising the lowering gives the path back.** If `z` reaches the ordinate `Y` exactly at the
abscissa `X + 1` and stays at or above it afterwards, then lowering it there below `Y` and splicing
with `HJO.Mellit.raiseFrom` at `Y` recovers `z`. This is what lets the lemmas of the splice be read
backwards. -/
theorem raiseFrom_lowerAt_eq (z : Heights a b N) {X : ℕ} {v Y' : Fin (b * N + 1)}
    (hX : X + 1 < a * N + 1) (hvY : (v : ℕ) ≤ (Y' : ℕ)) (hzY : ht z (X + 1) = (Y' : ℕ))
    (hmono : ∀ r, X + 1 ≤ r → (Y' : ℕ) ≤ ht z r) :
    raiseFrom (lowerAt z X v) X Y' = z := by
  refine heights_eq_of_ht_eq fun r => ?_
  rcases Nat.lt_or_ge X r with hr | hr
  swap
  · rw [ht_raiseFrom_of_le _ _ hr (by omega), ht_lowerAt_of_ne _ _ (by omega)]
  · rw [ht_raiseFrom_of_gt _ _ hr]
    rcases Nat.lt_or_ge (X + 1) r with h2 | h2
    · rw [ht_lowerAt_of_ne _ _ (by omega)]
      exact max_eq_left (hmono r (by omega))
    · have hr1 : r = X + 1 := by omega
      subst hr1
      rw [ht_lowerAt_self _ _ hX, hzY]
      exact max_eq_right hvY

section Unswept

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The colouring does not move at a point the path does not sweep -/

/-- **Above the level the point under `(X, Y)` is never coloured**, with nothing asked of the path.
This is `HJO.Mellit.not_mem_colouring_hi_at_below` with its hypothesis `Y ≤ ŷ_{X+1}` dropped: the
upper level's index in the column of `X` is `Y`, which already refutes both disjuncts of
`HJO.Mellit.mem_colouring_iff_levelIndex`, so the path's height there is not consulted. The
hypothesis has to go, because the paths of interest here are exactly those with `ŷ_{X+1} < Y`. -/
theorem notMem_colouring_hi_at_below (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (y : Heights a b N) (hY : 1 ≤ Y) :
    (X, Y - 1) ∉ colouring y ηhi := by
  rw [mem_colouring_iff_levelIndex ha hN hI.hi]
  have h2 := hI.le_levelIndex_hi_iff ha hN (j := Y) hI.yle
  rintro (⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩) <;> omega

/-- **The local shape of a path at a lattice point of the rectangle it does not sweep.** Either the
point is below the diagonal, and then no above-diagonal path can be at or above it in that column;
or the path's top in the column of `X` is strictly under `Y`. Either way the four height conditions
that the two colourings read at the three points of the event all fail. -/
theorem shape_of_notMem_sweptRegion (hX : X ≤ a * N) (hYb : Y ≤ b * N)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hsw : (X, Y) ∉ sweptRegion y) :
    ¬ (X < a * N ∧ ht y (X + 1) = Y) ∧ ¬ (ht y X ≤ Y ∧ Y < ht y (X + 1)) ∧
      (1 ≤ Y → ¬ (ht y X ≤ Y - 1 ∧ Y - 1 < ht y (X + 1))) ∧ ht y X ≠ Y := by
  have hcase : Y ≤ ht y (X + 1) → ¬ (b * X ≤ a * Y) := fun h1 h2 =>
    hsw (mem_sweptRegion_pair.2 ⟨hX, h2, h1⟩)
  rcases Nat.lt_or_ge (ht y (X + 1)) Y with h | h
  · have hXlt : X < a * N := by
      by_contra hcon
      have he : ht y (X + 1) = b * N := ht_of_gt y (by omega)
      omega
    have hmono : ht y X ≤ ht y (X + 1) := hy.2.2.1 X hXlt
    exact ⟨by omega, by omega, fun _ => by omega, by omega⟩
  · have hnd : ¬ (b * X ≤ a * Y) := hcase h
    have hd : b * X ≤ a * ht y X := hy.2.2.2 X hX
    have hgt : Y < ht y X := by
      by_contra hcon
      exact hnd (hd.trans (Nat.mul_le_mul_left a (by omega)))
    refine ⟨?_, by omega, fun _ => by omega, by omega⟩
    rintro ⟨h1, h2⟩
    exact hnd ((Nat.mul_le_mul_left b (Nat.le_succ X)).trans
      (h2 ▸ hy.2.2.2 (X + 1) (by omega)))

/-- **A bracketed drop whose isolated point the path does not sweep leaves the path's colouring
alone.** By `HJO.Mellit.mem_colouring_iff_of_ne` the two colourings can differ only at `(X, Y)`,
the point under it and the point left of it, and at each of the three the membership test asks for
height data that `HJO.Mellit.shape_of_notMem_sweptRegion` refutes.

This is the precise form of "the colouring moves only at ranks of swept points" that the iteration
needs, and it is where the attack window is accounted for: the upper end `rk̂(u) + ω` of the window
of a north step `u` is the rank of the *head* of `u` by `HJO.Paths.abovePointRank_succ`, a point
the path sweeps, so it is not a transition the isolation fails to see. -/
theorem colouring_eq_of_notMem_sweptRegion (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hsw : (X, Y) ∉ sweptRegion y) : colouring y ηlo = colouring y ηhi := by
  obtain ⟨s1, s2, s3, s4⟩ := shape_of_notMem_sweptRegion hI.xle hI.yle hy hsw
  ext p
  by_cases hp1 : p = (X, Y)
  · subst hp1
    rw [mem_colouring_lo_at_point ha hb hN hI y, mem_colouring_hi_at_point ha hN hI y]
    exact iff_of_false s1 fun h => s2 ⟨h.2.1, h.2.2⟩
  · by_cases hp2 : p = (X, Y - 1)
    · subst hp2
      have hY : 1 ≤ Y := by
        rcases Nat.eq_zero_or_pos Y with rfl | h
        · simp at hp1
        · exact h
      rw [mem_colouring_lo_at_below ha hN hI y hY]
      exact iff_of_false (fun h => s3 hY ⟨h.2.1, h.2.2⟩)
        (notMem_colouring_hi_at_below ha hN hI y hY)
    · by_cases hp3 : p = (X - 1, Y)
      · subst hp3
        have hX : 1 ≤ X := by
          rcases Nat.eq_zero_or_pos X with rfl | h
          · simp at hp1
          · exact h
        rw [mem_colouring_hi_at_left ha hb hN hI y hX]
        exact iff_of_false (not_mem_colouring_lo_at_left ha hb hN hI y hX) s4
      · exact mem_colouring_iff_of_ne ha hN hI y hp1 hp2 hp3

/-! ### The trace does not move either -/

/-- **A bracketed drop whose isolated point the path does not sweep leaves the swept part above the
level alone.** The only rank the two levels separate is `rk̂(X, Y)`, and by
`HJO.Paths.abovePointRank_injOn` the only lattice point of the rectangle carrying it is `(X, Y)`
itself, which is not swept. -/
theorem sweptAbove_eq_of_notMem_sweptRegion (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hsw : (X, Y) ∉ sweptRegion y) :
    sweptAbove y ηlo = sweptAbove y ηhi := by
  have hlt : ηlo < ηhi := hI.ltP.trans hI.Plt
  ext P
  simp only [sweptAbove, Finset.mem_filter]
  refine and_congr_right fun hP => ⟨fun h => ?_, fun h => hlt.trans h⟩
  by_contra hcon
  have hPlt : ((pointRank a b N P : ℤ) : ℚ) < ηhi :=
    lt_of_le_of_ne (not_lt.1 hcon) (cast_pointRank_ne_of_isAdmissibleLevel hI.hi a b N P)
  obtain ⟨h1, -, h3⟩ := Paths.mem_sweptRegion.1 hP
  obtain ⟨e1, e2⟩ := abovePointRank_injOn (b := b) ha hN h1 hI.xle
    (hI.iso P h1 (h3.trans (ht_le_mul y _)) h hPlt)
  exact hsw (Prod.ext_iff.2 ⟨e1, e2⟩ ▸ hP)

/-- The trace above the level is the image of the swept part above it, so it does not move either.
-/
theorem levelTrace_eq_of_notMem_sweptRegion (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hsw : (X, Y) ∉ sweptRegion y) :
    levelTrace y ηlo = levelTrace y ηhi := by
  rw [levelTrace, levelTrace, sweptAbove_eq_of_notMem_sweptRegion ha hN hI hsw]

/-- The partial sweep word is the product over the swept part above the level, so it does not move
either. -/
theorem partialSweepWord_eq_of_notMem_sweptRegion (q u : L) (ha : 0 < a) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hsw : (X, Y) ∉ sweptRegion y) :
    partialSweepWord q u y ηlo = partialSweepWord q u y ηhi := by
  rw [partialSweepWord, partialSweepWord, sweptAbove_eq_of_notMem_sweptRegion ha hN hI hsw]

/-! ### The fibre below the level does not see the point either -/

/-- **Below the level, sharing the colouring of a path that does not sweep `(X, Y)` forbids sweeping
it.** The colouring at `ηlo` records, in the column of `X`, the crossed north step at the ordinate
`Y - 1` and the crossed east step at the ordinate `Y`; a path whose top in that column reaches `Y`
is caught by one of the two, while the reference path, whose top is strictly below `Y`, is caught
by neither. `HJO.Mellit.ht_le_levelIndex_iff` supplies the one remaining configuration, a path
already over the level at the abscissa `X`. -/
theorem notMem_sweptRegion_of_colouring_lo_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y z : Heights a b N} (hy : IsAboveDiagonal y)
    (hz : IsAboveDiagonal z) (hsw : (X, Y) ∉ sweptRegion y)
    (hc : colouring z ηlo = colouring y ηlo) : (X, Y) ∉ sweptRegion z := by
  intro hzsw
  obtain ⟨-, hdiag, hzht⟩ := mem_sweptRegion_pair.1 hzsw
  have hyht : ht y (X + 1) < Y := by
    by_contra hcon
    exact hsw (mem_sweptRegion_pair.2 ⟨hI.xle, hdiag, by omega⟩)
  have hXlt : X < a * N := by
    by_contra hcon
    have he : ht y (X + 1) = b * N := ht_of_gt y (by omega)
    have := hI.yle
    omega
  have hymono : ht y X ≤ ht y (X + 1) := hy.2.2.1 X hXlt
  have hY : 1 ≤ Y := by omega
  have hzX : ht z X < Y := by
    have hside := ht_le_levelIndex_iff ha hb hN hI.lo hy hz hc.symm X hI.xle
    have e1 := hI.le_levelIndex_lo_iff ha hN (j := ht y X) (ht_le_mul y X)
    have e2 := hI.le_levelIndex_lo_iff ha hN (j := ht z X) (ht_le_mul z X)
    omega
  rcases eq_or_lt_of_le hzht with heq | hlt
  · have h1 : (X, Y) ∈ colouring z ηlo :=
      (mem_colouring_lo_at_point ha hb hN hI z).2 ⟨hXlt, heq.symm⟩
    rw [hc, mem_colouring_lo_at_point ha hb hN hI y] at h1
    omega
  · have h1 : (X, Y - 1) ∈ colouring z ηlo :=
      (mem_colouring_lo_at_below ha hN hI z hY).2 ⟨hXlt, by omega, by omega⟩
    rw [hc, mem_colouring_lo_at_below ha hN hI y hY] at h1
    omega

/-! ### The fibre above the level contributes no new trace -/

/-- **A path sharing the colouring above the level contributes the trace of one that does not sweep
the point.** If `y` does not sweep `(X, Y)` and `z` has `y` 's colouring at `ηhi`, then either `z`
does not sweep `(X, Y)` either — and `w = z` will do — or it touches the point exactly, with
`ẑ_X < Y = ẑ_{X+1}`, and is then `HJO.Mellit.raiseFrom w X Y` for the one-column lowering
`w = HJO.Mellit.lowerAt z X (max ẑ_X ŷ_{X+1})`, which does not sweep the point. In the second case
`HJO.Mellit.colouring_hi_raiseFrom` and `HJO.Mellit.levelTrace_raiseFrom` say `w` carries the same
colouring and the same trace above the level as `z`.

This is the asymmetry of the splice used in the direction the `A`/`C`/`D` argument does not need
it: there the fibre below the level is the smaller one and `raiseFrom` maps into it, here the fibre
above the level is the larger one and every extra member is in the image of the splice. -/
theorem exists_notMem_sweptRegion_colouring_hi_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y z : Heights a b N} (hy : IsAboveDiagonal y)
    (hz : IsAboveDiagonal z) (hsw : (X, Y) ∉ sweptRegion y)
    (hc : colouring z ηhi = colouring y ηhi) :
    ∃ w : Heights a b N, IsAboveDiagonal w ∧ (X, Y) ∉ sweptRegion w ∧
      colouring w ηhi = colouring z ηhi ∧ levelTrace w ηhi = levelTrace z ηhi := by
  by_cases hzsw : (X, Y) ∈ sweptRegion z
  swap
  · exact ⟨z, hz, hzsw, rfl, rfl⟩
  obtain ⟨-, hdiag, hzht⟩ := mem_sweptRegion_pair.1 hzsw
  have hyht : ht y (X + 1) < Y := by
    by_contra hcon
    exact hsw (mem_sweptRegion_pair.2 ⟨hI.xle, hdiag, by omega⟩)
  have hYb := hI.yle
  have hX1 : X + 1 < a * N := by
    rcases Nat.lt_or_ge X (a * N) with hXlt | hXge
    · by_contra hcon
      have he : ht y (X + 1) = b * N := by
        have : X + 1 = a * N := by omega
        rw [this]; exact hy.2.1
      omega
    · exfalso
      have he : ht y (X + 1) = b * N := ht_of_gt y (by omega)
      omega
  have hymono : ht y X ≤ ht y (X + 1) := hy.2.2.1 X (by omega)
  have hzmono : Monotone (ht z) := ht_mono hz.2.2.1
  -- the path `z` is at or below `Y` at the abscissa `X`
  have hzXle : ht z X ≤ Y := by
    have hside := ht_le_levelIndex_iff ha hb hN hI.hi hy hz hc.symm X hI.xle
    have e1 := hI.le_levelIndex_hi_iff ha hN (j := ht y X) (ht_le_mul y X)
    have e2 := hI.le_levelIndex_hi_iff ha hN (j := ht z X) (ht_le_mul z X)
    omega
  -- and touches `Y` exactly at the abscissa `X + 1`
  have hzeq : ht z (X + 1) = Y := by
    by_contra hcon
    have hgt : Y < ht z (X + 1) := by omega
    have h1 : (X, Y) ∈ colouring z ηhi :=
      (mem_colouring_hi_at_point ha hN hI z).2 ⟨by omega, hzXle, hgt⟩
    rw [hc, mem_colouring_hi_at_point ha hN hI y] at h1
    omega
  have hzXlt : ht z X < Y := by
    rcases Nat.eq_zero_or_pos X with rfl | hX
    · rw [hz.1]; omega
    · by_contra hcon
      have h1 : (X - 1, Y) ∈ colouring z ηhi :=
        (mem_colouring_hi_at_left ha hb hN hI z hX).2 (by omega)
      rw [hc, mem_colouring_hi_at_left ha hb hN hI y hX] at h1
      omega
  -- the lowering: a height at the abscissa `X + 1` over the diagonal and under `Y`
  obtain ⟨v, hv1, hv2, hv3⟩ : ∃ v : ℕ, ht z X ≤ v ∧ ht y (X + 1) ≤ v ∧ v < Y :=
    ⟨max (ht z X) (ht y (X + 1)), le_max_left _ _, le_max_right _ _, max_lt hzXlt hyht⟩
  have hvb : v < b * N + 1 := by omega
  have hYbb : Y < b * N + 1 := by omega
  have hwself : ht (lowerAt z X (⟨v, hvb⟩ : Fin (b * N + 1))) (X + 1) = v :=
    ht_lowerAt_self z _ (by omega)
  have hre : raiseFrom (lowerAt z X (⟨v, hvb⟩ : Fin (b * N + 1))) X
      (⟨Y, hYbb⟩ : Fin (b * N + 1)) = z :=
    raiseFrom_lowerAt_eq z (by omega) (show v ≤ Y by omega) hzeq fun r hr =>
      hzeq ▸ hzmono hr
  have hne : ∀ r : ℕ, r ≠ X + 1 →
      ht (lowerAt z X (⟨v, hvb⟩ : Fin (b * N + 1))) r = ht z r := fun r hr =>
    ht_lowerAt_of_ne z _ hr
  refine ⟨lowerAt z X ⟨v, hvb⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hne 0 (by omega)]; exact hz.1
  · rw [hne (a * N) (by omega)]; exact hz.2.1
  · intro r hr
    rcases eq_or_ne r (X + 1) with rfl | hr1
    · have h1 : ht z (X + 1) ≤ ht z (X + 1 + 1) := hzmono (by omega)
      rw [hwself, hne (X + 1 + 1) (by omega)]
      omega
    · rcases eq_or_ne (r + 1) (X + 1) with hr2 | hr2
      · have hrX : r = X := by omega
        rw [hne r hr1, hrX, hwself]
        exact hv1
      · rw [hne r hr1, hne (r + 1) hr2]
        exact hz.2.2.1 r hr
  · intro r hr
    rcases eq_or_ne r (X + 1) with rfl | hr1
    · rw [hwself]
      exact (hy.2.2.2 (X + 1) (by omega)).trans (Nat.mul_le_mul_left a hv2)
    · rw [hne r hr1]; exact hz.2.2.2 r hr
  · intro hcon
    have h1 := (mem_sweptRegion_pair.1 hcon).2.2
    rw [hwself] at h1
    omega
  · have hcol := colouring_hi_raiseFrom ha hb hN hI (lowerAt z X (⟨v, hvb⟩ : Fin (b * N + 1)))
      (Y' := (⟨Y, hYbb⟩ : Fin (b * N + 1))) rfl
    rw [hre] at hcol
    exact hcol.symm
  · have htr := levelTrace_raiseFrom ha hb hN hI (lowerAt z X (⟨v, hvb⟩ : Fin (b * N + 1)))
      (Y' := (⟨Y, hYbb⟩ : Fin (b * N + 1))) rfl
    rw [hre] at htr
    exact htr.symm

/-! ### The invariant does not move -/

/-- **The two levels of a drop whose isolated point the path does not sweep index the same traces.**
Below the level the fibre of the colouring consists of paths that do not sweep `(X, Y)` (
`HJO.Mellit.notMem_sweptRegion_of_colouring_lo_eq`), and each of them has the same trace at both
levels; above the level the fibre may be larger, and every extra member contributes the trace of a
path that does not sweep the point (`HJO.Mellit.exists_notMem_sweptRegion_colouring_hi_eq`). -/
theorem traceIndex_eq_of_notMem_sweptRegion (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hsw : (X, Y) ∉ sweptRegion y) :
    traceIndex a b N ηlo (colouring y ηlo) = traceIndex a b N ηhi (colouring y ηhi) := by
  have hcy : colouring y ηlo = colouring y ηhi :=
    colouring_eq_of_notMem_sweptRegion ha hb hN hI hy hsw
  refine Finset.Subset.antisymm (fun τ hτ => ?_) fun τ hτ => ?_
  · obtain ⟨z, hz, hcz, htz⟩ := exists_path_of_mem_traceIndex hτ
    have hzsw : (X, Y) ∉ sweptRegion z :=
      notMem_sweptRegion_of_colouring_lo_eq ha hb hN hI hy hz hsw hcz
    have hczhi : colouring z ηhi = colouring y ηhi := by
      rw [← colouring_eq_of_notMem_sweptRegion ha hb hN hI hz hzsw, hcz, hcy]
    have := mem_traceIndex_of_colouring_eq z hz ηhi hczhi
    rwa [← levelTrace_eq_of_notMem_sweptRegion ha hN hI hzsw, htz] at this
  · obtain ⟨z, hz, hcz, htz⟩ := exists_path_of_mem_traceIndex hτ
    obtain ⟨w, hw, hwsw, hcw, htw⟩ :=
      exists_notMem_sweptRegion_colouring_hi_eq ha hb hN hI hy hz hsw hcz
    have hcwlo : colouring w ηlo = colouring y ηlo := by
      rw [colouring_eq_of_notMem_sweptRegion ha hb hN hI hw hwsw, hcw, hcz, hcy]
    have := mem_traceIndex_of_colouring_eq w hw ηlo hcwlo
    rwa [levelTrace_eq_of_notMem_sweptRegion ha hN hI hwsw, htw, htz] at this

/-- **Lowering the level past a point the path does not sweep does not change the invariant.** The
fourth clause of the level recursion, for `HJO.Mellit.dsc`: the index sets of the two sums agree (
`HJO.Mellit.traceIndex_eq_of_notMem_sweptRegion`), and at a common trace `τ` the two
representatives — one chosen below the level, one above — have the same trace at `ηhi`, so
`HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq` makes their words agree, and the lower
representative's word does not depend on which of the two levels it is read at.

No genericity is spent and no inverse is introduced: the identity is that two sums of the same terms
are equal, so it holds at every `q` and `u` in a field. -/
theorem dsc_lo_eq_dsc_hi_of_notMem_sweptRegion (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hsw : (X, Y) ∉ sweptRegion y) :
    dsc q u a b N ηlo (colouring y ηlo) = dsc q u a b N ηhi (colouring y ηhi) := by
  have hidx : traceIndex a b N ηlo (colouring y ηlo) = traceIndex a b N ηhi (colouring y ηhi) :=
    traceIndex_eq_of_notMem_sweptRegion ha hb hN hI hy hsw
  rw [dsc, dsc, hidx]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  obtain ⟨hpLo, hcLo, htLo⟩ := traceRep_spec (hidx ▸ hτ)
  obtain ⟨hpHi, -, htHi⟩ := traceRep_spec hτ
  have hnsLo : (X, Y) ∉ sweptRegion (traceRep a b N ηlo (colouring y ηlo) τ) :=
    notMem_sweptRegion_of_colouring_lo_eq ha hb hN hI hy hpLo hsw hcLo
  have hword : partialSweepWord q u (traceRep a b N ηlo (colouring y ηlo) τ) ηlo =
      partialSweepWord q u (traceRep a b N ηlo (colouring y ηlo) τ) ηhi :=
    partialSweepWord_eq_of_notMem_sweptRegion q u ha hN hI hnsLo
  rw [hword, partialSweepWord_eq_of_levelTrace_eq q u ha hN hpLo hpHi
    (by rw [← levelTrace_eq_of_notMem_sweptRegion ha hN hI hnsLo, htLo, htHi])]

/-! ### The fourth clause, as a property of a candidate -/

/-- **The unswept clause of the level recursion, asked of a candidate `R`.** Verbatim the shape of
`HJO.Mellit.dsc_lo_eq_dsc_hi_of_notMem_sweptRegion`, which is this statement for `R = dsc`:
at a bracketed lattice point `(X, Y)` that the above-diagonal path `y` does *not* sweep, lowering
the level past it leaves the value unchanged.

This is a fourth clause beside `HJO.Mellit.SweepRecursionACD`, `HJO.Mellit.SweepRecursionBE` and
`HJO.Mellit.SweepRecursionBOrigin`, and none of those says anything at a point strictly above the
path or below the diagonal: the first two require `(X, Y) ∈ sweptRegion y`, which is what fails, and
the third speaks only of the bracketing of `(0, 0)`, a point every above-diagonal path sweeps. The
iteration of the drops cannot skip such a point either — the bracketing `HJO.Mellit.Isolates`
isolates a rank of the whole rectangle, not of the swept region of one path.

It mentions neither `q` nor `u` beyond the ambient field, and carries no operator: the clause is an
equality of two values of `R`. -/
def SweepRecursionUnswept (a b N : ℕ) (R : ℚ → Finset (ℕ × ℕ) → Total L) : Prop :=
  ∀ (X Y : ℕ) (ηlo ηhi : ℚ), Isolates a b N X Y ηlo ηhi →
    ∀ y : Heights a b N, IsAboveDiagonal y → (X, Y) ∉ sweptRegion y →
      R ηlo (colouring y ηlo) = R ηhi (colouring y ηhi)

/-- **`HJO.Mellit.dsc` satisfies the unswept clause**, which is
`HJO.Mellit.dsc_lo_eq_dsc_hi_of_notMem_sweptRegion` packaged as `HJO.Mellit.SweepRecursionUnswept`.
Recorded so that the abstraction is known to be inhabited: a recursion property with no example is a
hypothesis nothing satisfies, and the iteration below would then be vacuous. -/
theorem dsc_sweepRecursionUnswept (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    SweepRecursionUnswept a b N (dsc q u a b N) :=
  fun _ _ _ _ hI _ hy hsw => dsc_lo_eq_dsc_hi_of_notMem_sweptRegion q u ha hb hN hI hy hsw

/-- **One drop of the level transfers agreement at every bracketed point, swept or not.** The
composite of `HJO.Mellit.eq_dsc_of_recursion_step_everywhere`, which needs the point to be swept,
and the unswept clause. This is the step the iteration repeats. -/
theorem eq_dsc_of_recursion_step_any (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hACD : SweepRecursionACD q u a b N R)
    (hBE : SweepRecursionBE q u a b N R) (hB0 : SweepRecursionBOrigin q a b N R)
    (hUn : SweepRecursionUnswept a b N R) (hI : Isolates a b N X Y ηlo ηhi)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hhi : ∀ z : Heights a b N, IsAboveDiagonal z →
      R ηhi (colouring z ηhi) = dsc q u a b N ηhi (colouring z ηhi)) :
    R ηlo (colouring y ηlo) = dsc q u a b N ηlo (colouring y ηlo) := by
  by_cases hsw : (X, Y) ∈ sweptRegion y
  · exact eq_dsc_of_recursion_step_everywhere q u ha hb hN hACD hBE hB0 hI hy hsw hhi
  · rw [hUn X Y ηlo ηhi hI y hy hsw, hhi y hy,
      dsc_lo_eq_dsc_hi_of_notMem_sweptRegion q u ha hb hN hI hy hsw]

end Unswept

end HJO.Mellit

end
