/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWidth
public meta import HJO.Attr

/-! # Two readings of a definition: marked pairs never attack, and the origin is a type-`B` event

Both statements here are clauses of definitions read directly, not counting arguments.

A marked pair `(s, t) ∈ S(P̂)` has `u_t = u_s + (0,1)`, so `HJO.Paths.abovePointRank_succ` makes
`rk̂(u_t) = rk̂(u_s) + ω` **on the nose**; the attack condition of `HJO.Paths.sweepAttack` asks for
`rk̂(u_t) < rk̂(u_s) + ω`, which that equality contradicts. So `S(P̂) ∩ 𝒜(P̂) = ∅` needs no
hypothesis whatever — not above-diagonality, not `0 < a`.

The event type at the origin is the third branch of `HJO.Paths.eventType`: `ŷ_0 = 0` puts the point
*on* the path with incoming letter `E`, and the branch then asks only whether the outgoing letter is
`N`, that is whether `1 ≤ aN` and `0 < ŷ_1`. Those are exactly the two facts
`HJO.Paths.mem_northSteps_zero` establishes.

## Main results

* `HJO.Paths.sweepMarked_inter_sweepAttack`: `S(P̂) ∩ 𝒜(P̂) = ∅`
  (`HJO.Paths.sweepMarked_inter_sweepAttack`), with
  `HJO.Paths.notMem_sweepAttack_of_mem_sweepMarked` and `HJO.Paths.disjoint_sweepMarked_sweepAttack`
  the pointwise and `Finset.Disjoint` forms.
* `HJO.Paths.eventType_zero`: `ev_{P̂}(0,0) = B` (`HJO.Paths.eventType_zero`).

## Implementation notes

**The statement `ev_{P̂}(0,0) = B` of `HJO.Paths.eventType_zero` is usually made with the single
hypothesis `N ≥ 1`, and is false as so stated at `b = 0`.** For `b = 0` an above-diagonal path has
`ŷ_{aN} = 0`, hence `ŷ_1 = 0` by monotonicity, so the outgoing letter at the origin is `E` and the
event type is `D` (or `D` again at `aN = 0`, where the guard `1 ≤ aN` fails) — never `B`. The usual
proof uses `b ≥ 1` silently, through `HJO.Paths.abovePointRank_lt_of_mem_northSteps`, whose proof
reads `a ŷ_1 ≥ b ≥ 1`; the repairing hypothesis is `0 < b`, carried here as `hb`. The earlier lemma
`HJO.Paths.mem_northSteps_zero` carries it too, for the same reason.

No hypothesis `0 < a` is needed: `IsAboveDiagonal` together with `0 < b` and `0 < N` forces
`0 < aN`, since `ht y (a * N) = b * N > 0 = ht y 0`.

## References

A. Mellit, *Toric braids and
`(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Paths

variable {a b N : ℕ}

/-! ### A marked pair is not an attacking pair -/

/-- **The two feet of a marked pair differ in rank by exactly the window.** The pair shares a column
and the upper foot is one unit higher, so `HJO.Paths.abovePointRank_succ` applies verbatim. This is
the whole content of `HJO.Paths.sweepMarked_inter_sweepAttack`: the attack condition asks for
a *strict* inequality against `rk̂(u_s) + ω`, and here there is equality. -/
theorem stepRank_eq_add_attackWindow_of_mem_sweepMarked {y : Heights a b N} {s t : Fin (b * N)}
    (h : (s, t) ∈ sweepMarked y) : stepRank y t = stepRank y s + attackWindow a N := by
  simp only [sweepMarked, mem_filter, mem_univ, true_and] at h
  rw [stepRank, stepRank, h.1, h.2, abovePointRank_succ]

/-- **A marked pair is not an attacking pair.** `HJO.Paths.sweepMarked_inter_sweepAttack`, in
pointwise form. -/
theorem notMem_sweepAttack_of_mem_sweepMarked {y : Heights a b N} {s t : Fin (b * N)}
    (h : (s, t) ∈ sweepMarked y) : (s, t) ∉ sweepAttack y := fun hA => by
  have := stepRank_lt_of_mem_sweepAttack (y := y) (s := s) (t := t) hA
  simp only [sweepAttack, mem_filter, mem_univ, true_and] at hA
  rw [stepRank_eq_add_attackWindow_of_mem_sweepMarked h] at hA
  exact absurd hA.2 (lt_irrefl _)

/-- **`S(P̂) ∩ 𝒜(P̂) = ∅`**: `HJO.Paths.sweepMarked_inter_sweepAttack`, as the intersection it
states. No hypothesis is needed: the rank identity along a unit north step holds at every lattice
point. -/
@[hjo "lem_sweep_marked_not_attack"]
theorem sweepMarked_inter_sweepAttack (y : Heights a b N) :
    sweepMarked y ∩ sweepAttack y = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun p hp => ?_
  obtain ⟨hS, hA⟩ := mem_inter.1 hp
  exact notMem_sweepAttack_of_mem_sweepMarked (s := p.1) (t := p.2) hS hA

/-- `HJO.Paths.sweepMarked_inter_sweepAttack` as `Finset.Disjoint`, the form the
characteristic-function comparison of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` reads it in: the marked
constraint set and the attack set of a path share no pair, so each plays its own role in
`HJO.Paths.sweepChar`. -/
theorem disjoint_sweepMarked_sweepAttack (y : Heights a b N) :
    Disjoint (sweepMarked y) (sweepAttack y) :=
  disjoint_iff_inter_eq_empty.2 (sweepMarked_inter_sweepAttack y)

/-! ### The origin is an event of type `B` -/

/-- **The origin is an event of type `B`.** `HJO.Paths.eventType_zero`, with the
repairing hypothesis `0 < b` — the printed statement, which asks only `N ≥ 1`, is false at `b = 0`,
where the origin has type `D`.

At the origin `ŷ_0 = 0`, so neither of the first two branches of `HJO.Paths.eventType` is taken and
the event type is `B` or `D` according as the outgoing letter is `N` or `E`. It is `N`: the origin
is a north step of the path (`HJO.Paths.mem_northSteps_zero`), which is exactly `1 ≤ aN` together
with `0 < ŷ_1`. -/
@[hjo "lem_sweep_origin_type"]
theorem eventType_zero {y : Heights a b N} (hy : IsAboveDiagonal y) (hb : 0 < b) (hN : 0 < N) :
    eventType y (0, 0) = EventType.B := by
  obtain ⟨haN, -, hup⟩ := mem_northSteps_iff.1 (mem_northSteps_zero hy hb hN)
  have h0 : ht y 0 = 0 := hy.1
  change (0 : ℕ) < ht y (0 + 1) at hup
  rw [eventType]
  split_ifs with h1 h2 h3 h4 <;> simp_all
  omega

end HJO.Paths
