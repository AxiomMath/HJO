/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.AboveParking
public meta import HJO.Attr

/-! # The sweep process: the data an above-diagonal path presents to it

Mellit computes the summand of the right-hand side of the compositional rational shuffle identity
attached to one above-diagonal `(aN, bN)`-path by moving a line of slope just below `b/a` downwards
across the `aN × bN` rectangle and registering an event at every lattice point it meets weakly
below the path. This file carries the combinatorial data that process reads off the path: the
window in which a north step is live, the region swept, the live north steps at a point and their
number, the number of them lying to the right, the event type at a point, the attack set and the
marked pairs of the path, the characteristic function summed over the words compatible with them,
and the standardisation of a word.

Nothing here is the sweep process itself; the operators it applies and the word it forms are
elsewhere. What is here is the input every one of those declarations reads.

## Main definitions

* `HJO.Paths.attackWindow`: the attack window `ω = (aN + 1)aN` of the rectangle.
* `HJO.Paths.sweptRegion`: the swept region `Sw(P̂)`, as a `Finset` of lattice points.
* `HJO.Paths.liveSteps`, `HJO.Paths.sweepWidth`, `HJO.Paths.sweepRight`: the live north steps
  `Live_{P̂}(P)` at a point, their number `k_{P̂}(P)`, and the number `a_{P̂}(P)` of them lying
  strictly to the right of the point.
* `HJO.Paths.EventType`, `HJO.Paths.eventType`: the five event types and the event type
  `ev_{P̂}(P)` at a point of the swept region.
* `HJO.Paths.sweepAttack`, `HJO.Paths.sweepMarked`: the attack set `𝒜(P̂)` and the marked pairs
  `S(P̂)` of the path, as `Finset`s of pairs of north steps.
* `HJO.Paths.sweepChar`: the characteristic function `χ(P̂)` of the path.
* `HJO.Paths.standardisation`: the standardisation `std(w)` of a word.

## Main results

* `HJO.Paths.attackWindow_pos_iff`, `HJO.Paths.cast_attackWindow`: the window is positive exactly
  when the rectangle has a column, and its value in a semiring.
* `HJO.Paths.mem_sweptRegion`, `HJO.Paths.corner_mem_sweptRegion`,
  `HJO.Paths.IsAboveDiagonal.mem_sweptRegion`: membership in the swept region is the
  three defining conditions; the corner `(aN, bN)` is swept; the column of the path at an abscissa
  is swept.
* `HJO.Paths.abovePointRank_succ`: the head of a north step outranks its foot by exactly the
  window. This is the identity the half-open window criterion of `liveSteps` is a reading of.
* `HJO.Paths.liveSteps_subset`: the live steps at a point are north steps of the path.
* `HJO.Paths.eventType_eq_E_iff`: the event type is `E` exactly at the points strictly below the
  path, which is the one reading of the definition that the usual presentation singles out.
* `HJO.Paths.stepRank_lt_of_mem_sweepAttack`, `HJO.Paths.stepRank_lt_of_mem_sweepMarked`: both
  `𝒜(P̂)` and `S(P̂)` consist of rank-increasing pairs. These are what make the transport of the
  index set described below checkable rather than asserted.

## Implementation notes

### The indexing of the north steps

The usual presentation lists the north steps of `P̂` as `u_1, …, u_{bN}` **in strictly increasing
order of above-diagonal rank**, and indexes `𝒜(P̂)`, `S(P̂)` and the letters of a word by positions
in that listing. The encoding used here indexes a north step by the **height of its foot**: the step
indexed by `i : Fin (bN)` has foot `(aboveColumn y i, i)`, and `HJO.Paths.stepRank` is the
above-diagonal rank of that foot. Nothing here sorts.

The transport is legitimate because every condition that presentation imposes is a condition on
ranks and on the geometry of the feet, never on the integer positions themselves. Since the listing
is by strictly increasing rank, and the rank is injective on the north steps of an above-diagonal
path with `0 < a`, the position order and the rank order are the same order, so:

* the `1 ≤ i < j ≤ bN` is exactly `rk̂(u_i) < rk̂(u_j)`;
* `𝒜(P̂) = {(i,j) : i < j, rk̂(u_j) < rk̂(u_i) + ω}` becomes
  `{(s,t) : rk̂ s < rk̂ t ∧ rk̂ t < rk̂ s + ω}`;
* `S(P̂) = {(i,j) : i < j, u_j = u_i + (0,1)}` becomes `{(s,t) : foot t = foot s + (0,1)}`, that
  is, same column and `t = s + 1` as heights; the `i < j` is then automatic, because
  the rank increases strictly upwards along a column — which is `abovePointRank_succ` together
  with `attackWindow_pos_iff`, and is recorded as `stepRank_lt_of_mem_sweepMarked`.

The transported sets are literally the same sets of pairs of north steps, read through the
rank-order bijection `Fin (bN) ≃ {1, …, bN}`; only the names of the indices differ. Nor does the
relabelling change `sweepChar`: the words are indexed by the same index set as the pairs, so a
relabelling of that set by a bijection permutes the summation variable `w` of a sum over *all*
words and leaves both the exponent `#{p ∈ 𝒜 : w p.2 < w p.1}` and the monomial `∏ x_{w i}`
unchanged term by term.

### Totality

As with every statistic of `HJO.Paths`, each definition here is total on the height vectors
`HJO.Paths.Heights a b N` and takes neither `HJO.Paths.IsAboveDiagonal` nor `P ∈ sweptRegion y` as
a hypothesis; the hypotheses enter in the lemmas, as they do for `HJO.Paths.aboveArm`. In
particular `liveSteps`, `sweepWidth`, `sweepRight` and `eventType` are defined at every lattice
point `P`, and `sweepAttack` and `sweepMarked` on every height vector. On an above-diagonal path
the index type `Fin (bN)` is the set of north steps on the nose — the heights rise from `0` to
`bN`, so each height `i < bN` is the foot of exactly one north step — so no filter is needed
there.

### The truncated subtraction in the outgoing letter

The outgoing letter at `P = (x,y)` is `N` if `x ≤ aN - 1` and `y < ŷ_{x+1}`. That
subtraction is over `ℤ`, and `x ≤ aN - 1` is `x + 1 ≤ aN`, which is what `eventType` writes. It
is **not** written as `x ≤ a * N - 1`: in `ℕ` that reads `x ≤ 0` at `aN = 0`, which is true at
`x = 0`, where the condition is false. The guard is live: `HJO.Paths.ht` holds the
height at `bN` beyond the rectangle, so dropping it would read `y < bN` at `x = aN` and return
`N` where the definition returns `E`.

### The alphabet of `sweepChar`

The words are `w : {1, …, bN} → ℤ_{>0}` into an alphabet `x_1, x_2, …`. Here a word is
`w : Fin (bN) → ℕ`, with no positivity condition on the letter, because the alphabet of
`HJO.Sym.AlphabetSeries` is indexed by `ℕ` and `HJO.ParkingFunctions.gessel` likewise puts no
positivity on its letters. The two conventions must agree,
`HJO.Mellit.eq_sum_sweepChar_of_eq_sum_gessel` equating a sum of Gessel functions with a sum of
these characteristic functions; both are the alphabet `x_1, x_2, …` above with its index shifted
down by one, which is a relabelling of the variables of `MvPowerSeries ℕ K`.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section "The sweep
process" (arXiv:1604.07456), with his coprime pair
`(m₁, n₁)` read as `(a, b)` and his multiplier `g` as `N`. His `ε` is replaced throughout by the
integer rank `HJO.ParkingFunctions.abovePointRank`, and his `a` of the rules C) and D) — "the
number of vertical steps the line crosses to the right of the event" — is `sweepRight`.
-/

@[expose] public section

open Finset

namespace HJO.Paths

/-! ### The attack window -/

/-- The attack window `ω = (aN + 1)aN` of the `aN × bN` rectangle: the amount by which the
above-diagonal rank `(aN + 1)N(ay - bx) + x` increases along a north step, hence the width, in
rank units, of the window `rk u ≤ rk P < rk u + ω` in which a north step `u` is crossed by the
level line through `P`. -/
@[hjo "def_sweep_window"]
def attackWindow (a N : ℕ) : ℕ := (a * N + 1) * (a * N)

/-- The attack window is positive exactly when the rectangle has a column: it vanishes for
`a = 0` and for `N = 0`, and only there. -/
@[simp]
theorem attackWindow_pos_iff {a N : ℕ} : 0 < attackWindow a N ↔ 0 < a * N :=
  ⟨fun h => Nat.pos_of_ne_zero fun h0 => by simp [attackWindow, h0] at h,
    fun h => Nat.mul_pos (Nat.succ_pos _) h⟩

/-- The attack window in a semiring, the ranks it is compared against being integers. -/
@[norm_cast]
theorem cast_attackWindow {R : Type*} [NonAssocSemiring R] (a N : ℕ) :
    ((attackWindow a N : ℕ) : R) = (a * N + 1) * (a * N) := by
  simp [attackWindow]

/-! ### The swept region -/

/-- The swept region `Sw(P̂) = {(x, y) : 0 ≤ x ≤ aN, a y ≥ b x, y ≤ ŷ⁺_x}` of a height vector: the
lattice points weakly above the diagonal and weakly below the path, `ŷ⁺_x = ht y (x + 1)` being the
top of the path's column at `x`, equal to `bN` at `x = aN`. These are the points at which the sweep
process registers an event. -/
@[hjo "def_sweep_region"]
def sweptRegion {a b N : ℕ} (y : Heights a b N) : Finset (ℕ × ℕ) :=
  {p ∈ Iic (a * N) ×ˢ Iic (b * N) | b * p.1 ≤ a * p.2 ∧ p.2 ≤ ht y (p.1 + 1)}

@[simp]
theorem mem_sweptRegion {a b N : ℕ} {y : Heights a b N} {p : ℕ × ℕ} :
    p ∈ sweptRegion y ↔ p.1 ≤ a * N ∧ b * p.1 ≤ a * p.2 ∧ p.2 ≤ ht y (p.1 + 1) := by
  simp only [sweptRegion, mem_filter, mem_product, mem_Iic]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.2.trans (ht_le_mul y _)⟩, h.2⟩⟩

/-- The corner `(aN, bN)` of the rectangle is swept, whatever the height vector: it is the top of
the column at `x = aN`, where `ŷ⁺_{aN} = bN`, and `a bN ≥ b aN` holds with equality. -/
theorem corner_mem_sweptRegion {a b N : ℕ} (y : Heights a b N) :
    (a * N, b * N) ∈ sweptRegion y := by
  refine Paths.mem_sweptRegion.2 ⟨le_rfl, le_of_eq (by ring), ?_⟩
  unfold ht
  split
  · next h => exact absurd h (by omega)
  · exact le_rfl

/-- The column of an above-diagonal path at abscissa `x` lies in its swept region: a point whose
ordinate is between `ŷ_x` and `ŷ⁺_x = ht y (x + 1)` is weakly below the path, and weakly above the
diagonal because `a ŷ_x ≥ b x`. -/
theorem IsAboveDiagonal.mem_sweptRegion {a b N : ℕ} {y : Heights a b N} (hy : IsAboveDiagonal y)
    {x k : ℕ} (hx : x ≤ a * N) (hk : ht y x ≤ k) (hk' : k ≤ ht y (x + 1)) :
    (x, k) ∈ sweptRegion y :=
  Paths.mem_sweptRegion.2 ⟨hx, (hy.2.2.2 x hx).trans (Nat.mul_le_mul_left a hk), hk'⟩

variable {a b N : ℕ}

/-! ### The rank of a north step -/

/-- The head of a north step outranks its foot by exactly the attack window: the above-diagonal rank
of `(x, y + 1)` is that of `(x, y)` plus `ω`. This is the identity that makes the half-open window
`rk u ≤ rk P < rk u + ω` of `liveSteps` say "the foot has rank at most, and the head rank greater
than, that of `P`". The statement holds at every lattice point, with no bound on `x` or `k`, because
the rank is affine in the ordinate with slope `(aN+1)Na` and `ω = (aN+1)aN`. -/
@[hjo "lem_sweep_rank_step_omega"]
theorem abovePointRank_succ (a b N x k : ℕ) :
    ParkingFunctions.abovePointRank a b N x (k + 1) =
      ParkingFunctions.abovePointRank a b N x k + attackWindow a N := by
  simp only [ParkingFunctions.abovePointRank, cast_attackWindow]
  push_cast
  ring

/-- The above-diagonal rank of the north step of the path `y` indexed by the height `i` of its
foot: the rank of the lattice point `(aboveColumn y i, i)`. On an above-diagonal path this is the
foot of the unique north step at height `i`, so this agrees with
`HJO.ParkingFunctions.aboveStepRank π i` whenever `y = HJO.ParkingFunctions.abovePath π`: the two
are the same expression, `aboveStepRank` reading the path off the parking function. -/
def stepRank (y : Heights a b N) (i : Fin (b * N)) : ℤ :=
  ParkingFunctions.abovePointRank a b N (ParkingFunctions.aboveColumn y (i : ℕ)) (i : ℕ)

/-! ### The live north steps at a point -/

/-- The live north steps `Live_{P̂}(P) = {u a north step of P̂ : rk̂(u) ≤ rk̂(P) < rk̂(u) + ω}` at a
lattice point `P`: the north steps of the path, each named by its foot, that the level line of the
above-diagonal rank through `P` crosses. By `abovePointRank_succ` the second inequality says that
the head of `u` outranks `P`, so the pair says that the line is at or above the foot of `u` and
strictly below its head — "the line of slope `b/a - ε` through `P` crosses `u`", with
the tie-breaking constant `ε` replaced by the integer rank.

Two departures from the definition as usually written, neither of them a change of the set. That
definition takes `P ∈ Sw(P̂)`; this is total in `P`, in the house style of `HJO.Paths.aboveArm`, and
every use supplies a point of `sweptRegion y` anyway. And the `{u a north step of P̂}`
is here a `Finset` filtered out of `HJO.Paths.northSteps`, which is that set of feet; see
`liveSteps_subset`. -/
@[hjo "def_sweep_live"]
def liveSteps (y : Heights a b N) (P : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  {u ∈ northSteps y | ParkingFunctions.abovePointRank a b N u.1 u.2 ≤
      ParkingFunctions.abovePointRank a b N P.1 P.2 ∧
    ParkingFunctions.abovePointRank a b N P.1 P.2 <
      ParkingFunctions.abovePointRank a b N u.1 u.2 + attackWindow a N}

/-- The live north steps at a point are north steps of the path. -/
theorem liveSteps_subset (y : Heights a b N) (P : ℕ × ℕ) : liveSteps y P ⊆ northSteps y :=
  filter_subset _ _

/-- The width `k_{P̂}(P) = #Live_{P̂}(P)` at a lattice point: the number of north steps of the path
that the level line through `P` crosses, which in Mellit's argument is the number of connected
components of the intersection of that line with the figure bounded by the path and the diagonal.
Total in `P`, where the definition is usually stated for `P ∈ Sw(P̂)`, `liveSteps` being total. -/
@[hjo "def_sweep_width"]
def sweepWidth (y : Heights a b N) (P : ℕ × ℕ) : ℕ := #(liveSteps y P)

/-- The live count to the right `a_{P̂}(P) = #{(x', y') ∈ Live_{P̂}(P) : x' > x}` at a lattice point
`P = (x, y)`: the number of live north steps whose column is strictly to the right of `P`. This is
Mellit's `a`, "the number of vertical steps the line crosses to the right of the event", which
his rules C) and D) raise `q` to. The inequality on columns is strict, so a live north step in the
column of `P` itself — at a type-`C` event, the step with foot `P` — is not counted. Total in `P`,
where the definition is usually stated for `P ∈ Sw(P̂)`. -/
@[hjo "def_sweep_right"]
def sweepRight (y : Heights a b N) (P : ℕ × ℕ) : ℕ := #{u ∈ liveSteps y P | P.1 < u.1}

/-! ### The event type at a point -/

/-- The five event types of the sweep process, in Mellit's order: `A` is a north step followed
by an east step, `B` an east step followed by a north step, `C` two consecutive north steps, `D`
two consecutive east steps, and `E` a point strictly below the path. They are the codomain of
`HJO.Paths.eventType`, which assigns one of them to each point; being the constructors of an
inductive type they are exhaustive and disjoint by construction. -/
inductive EventType : Type
  /-- A north step followed by an east step; the sweep applies `d₊`. -/
  | A
  /-- An east step followed by a north step; the sweep applies `d₋`. -/
  | B
  /-- Two consecutive north steps; the sweep applies `q^{-a}(d₋d₊ - d₊d₋)/(q-1)`. -/
  | C
  /-- Two consecutive east steps; the sweep multiplies by `q^a`. -/
  | D
  /-- A point strictly below the path; the sweep multiplies by `u`. -/
  | E
  deriving DecidableEq

/-- The event type `ev_{P̂}(P)` at a lattice point `P = (x, y)`: it is `E` if `y < ŷ_x`, and
otherwise is `A`, `B`, `C`, `D` according as the pair (incoming letter, outgoing letter) is
`(N, E)`, `(E, N)`, `(N, N)`, `(E, E)`, where the incoming letter is `N` if `y > ŷ_x` and `E`
otherwise, and the outgoing letter is `N` if `x ≤ aN - 1` and `y < ŷ_{x+1}`, and `E` otherwise. On
a point of `sweptRegion y` the ordinate satisfies `y ≤ ŷ⁺_x`, so `y ≥ ŷ_x` says that the point is
on the path and `y < ŷ_x` that it is strictly below it; `eventType_eq_E_iff` is that reading.

Two departures from the definition as usually written. The guard `x ≤ aN - 1` on the outgoing
letter, a subtraction over `ℤ`, is written `x + 1 ≤ aN`; spelling it `x ≤ a * N - 1` in `ℕ` would
read `x ≤ 0` at `aN = 0` and so return the wrong letter at `(0,0)` on the empty rectangle. And the
definition is total in `P`, where it is usually stated for `P ∈ Sw(P̂)`; off the swept region the
value is still one of the five types, but the prose reading of it above is not available. -/
@[hjo "def_sweep_event"]
def eventType (y : Heights a b N) (P : ℕ × ℕ) : EventType :=
  if P.2 < ht y P.1 then EventType.E
  else if ht y P.1 < P.2 then
    if P.1 + 1 ≤ a * N ∧ P.2 < ht y (P.1 + 1) then EventType.C else EventType.A
  else
    if P.1 + 1 ≤ a * N ∧ P.2 < ht y (P.1 + 1) then EventType.B else EventType.D

/-- The event type at `P` is `E` exactly when `P` lies strictly below the path. On a point of the
swept region, whose ordinate is at most `ŷ⁺_x`, this says that the four types `A`, `B`, `C`, `D`
are the points *on* the path and `E` the points strictly below it. -/
@[simp]
theorem eventType_eq_E_iff {y : Heights a b N} {P : ℕ × ℕ} :
    eventType y P = EventType.E ↔ P.2 < ht y P.1 := by
  unfold eventType
  split_ifs <;> simp_all

/-! ### The attack set and the marked pairs -/

/-- The attack set `𝒜(P̂)` of the path `y`: the pairs `(s, t)` of north steps, each indexed by the
height of its foot, with `rk̂ s < rk̂ t < rk̂ s + ω`. The usual presentation lists the north steps
`u_1, …, u_{bN}` in strictly increasing order of above-diagonal rank and asks for
`1 ≤ i < j ≤ bN` together with `rk̂(u_j) < rk̂(u_i) + ω`; the listing being by strictly increasing
rank, its `i < j` *is* `rk̂(u_i) < rk̂(u_j)`, so the set of pairs of north steps it names is the one
below, read through the rank-order bijection. `stepRank_lt_of_mem_sweepAttack` records the first
half of that, so the transport is checkable and not merely asserted; the module docstring gives the
argument in full, including why the relabelling leaves `sweepChar` unchanged.

The window is the same integer `HJO.ParkingFunctions.aboveTdinv` counts against, written there
out in full rather than cited. Total on the height vectors, as everything in `HJO.Paths` is: on an
above-diagonal path `Fin (bN)` indexes the north steps exactly. -/
@[hjo "def_sweep_attack"]
def sweepAttack (y : Heights a b N) : Finset (Fin (b * N) × Fin (b * N)) :=
  {p ∈ (univ : Finset (Fin (b * N) × Fin (b * N))) | stepRank y p.1 < stepRank y p.2 ∧
    stepRank y p.2 < stepRank y p.1 + attackWindow a N}

/-- The marked pairs `S(P̂)` of the path `y`: the pairs `(s, t)` of north steps, each indexed by the
height of its foot, whose feet share a column and are vertically adjacent, `u_t = u_s + (0,1)` —
that is, `aboveColumn y t = aboveColumn y s` and `t = s + 1`.

**The condition is same column and vertically adjacent, and is NOT the condition that `t` follow
`s` immediately in the rank-order listing.** A counterexample: for
`a = 1`, `b = 2`, `N = 2` and heights `(0, 2, 4)` the above-diagonal rank is `6y - 11x`, so the
north steps in increasing rank are `(0,0), (1,2), (0,1), (1,3)` and the two same-column pairs are
the rank-order positions `(1,3)` and `(2,4)`, neither of them consecutive. Reading the condition
as consecutiveness makes `S(P̂)` too small and so makes `sweepChar` impose fewer conditions than
the word-parking-function condition does; that condition is same-column, Mellit
asking the labels to decrease along each two consecutive north steps of a column.

The `1 ≤ i < j ≤ bN` is dropped rather than transported, because on the height
indexing it is automatic: the rank increases strictly upwards along a column, which is
`stepRank_lt_of_mem_sweepMarked`. Total on the height vectors, as everything in `HJO.Paths` is. -/
@[hjo "def_sweep_marked"]
def sweepMarked (y : Heights a b N) : Finset (Fin (b * N) × Fin (b * N)) :=
  {p ∈ (univ : Finset (Fin (b * N) × Fin (b * N))) |
    ParkingFunctions.aboveColumn y (p.2 : ℕ) = ParkingFunctions.aboveColumn y (p.1 : ℕ) ∧
      (p.2 : ℕ) = (p.1 : ℕ) + 1}

/-- An attacking pair is rank-increasing. This is the first half of the `i < j`, which
on the rank-order listing is exactly this inequality. -/
theorem stepRank_lt_of_mem_sweepAttack {y : Heights a b N} {s t : Fin (b * N)}
    (h : (s, t) ∈ sweepAttack y) : stepRank y s < stepRank y t := by
  simp only [sweepAttack, mem_filter, mem_univ, true_and] at h
  exact h.1

/-- A marked pair is rank-increasing: the two feet share a column and the upper one is one step
higher, so `abovePointRank_succ` raises the rank by the window, which is positive as soon as the
rectangle has a column. The hypothesis `0 < a` is not a restriction on the paths of
interest: an above-diagonal path with a north step has `bN > 0`, hence `ht y (aN) ≠ ht y 0`,
hence `aN > 0`, so `Fin (bN)` is empty and the statement vacuous whenever it fails. -/
theorem stepRank_lt_of_mem_sweepMarked {y : Heights a b N} (ha : 0 < a) {s t : Fin (b * N)}
    (h : (s, t) ∈ sweepMarked y) : stepRank y s < stepRank y t := by
  have hbN : 0 < b * N := s.pos
  have hN : 0 < N := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hbN
  simp only [sweepMarked, mem_filter, mem_univ, true_and] at h
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
  rw [stepRank, stepRank, h.1, h.2, abovePointRank_succ]
  exact lt_add_of_pos_right _ (by exact_mod_cast hω)

/-! ### The characteristic function of a path -/

/-- The characteristic function
`χ(P̂) = ∑_w q^{#{(i,j) ∈ 𝒜(P̂) : w_i > w_j}} x_{w_1} ⋯ x_{w_{bN}}` of the path `y`, the sum over
the words `w` on the north steps whose letters strictly decrease along every marked pair, that is
with `w_i > w_j` for every `(i,j) ∈ S(P̂)`.

An element of `HJO.Sym.AlphabetSeries K` is a function of the exponent vector `d : ℕ →₀ ℕ`, and
this is written in that register, as `HJO.ParkingFunctions.gessel` is. The coefficient at `d` is a
*finite* sum, because a word whose monomial `∏_i x_{w i}` is `d` takes all of its letters in
`d.support`: so the admissible words contributing to `d` are cut out of
`Fintype.piFinset fun _ => d.support`, and the infinite sum over all words is
recovered coefficientwise.

Two departures from the definition as usually written. The words are `w : Fin (bN) → ℕ` where that
definition has `w : {1, …, bN} → ℤ_{>0}`: the alphabet of `HJO.Sym.AlphabetSeries` is indexed by `ℕ`
and `HJO.ParkingFunctions.gessel` puts no positivity on its letters either, and the two conventions
must agree because `HJO.Mellit.eq_sum_sweepChar_of_eq_sum_gessel` equates a sum of Gessel functions
with a sum of these functions. And the index set of the words and of the pairs is the height
indexing of the north steps rather than the rank-order positions, on which see `sweepAttack`,
`sweepMarked` and the module docstring: relabelling that set by a bijection permutes the summation
variable `w` of a sum over all words and changes neither the exponent of `q` nor the monomial.

**The marked condition is same-column adjacency, not consecutiveness in the rank order**; reading
it as consecutiveness imposes strictly fewer conditions here than the
word-parking-function condition does. See `sweepMarked` for the counterexample. -/
@[hjo "def_sweep_char"]
noncomputable def sweepChar {K : Type*} [CommRing K] (q : K) (y : Heights a b N) :
    Sym.AlphabetSeries K :=
  fun d => ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin (b * N) => d.support |
      (∀ p ∈ sweepMarked y, w p.2 < w p.1) ∧ ∑ i, Finsupp.single (w i) 1 = d},
    q ^ #{p ∈ sweepAttack y | w p.2 < w p.1}

/-! ### Standardisation of a word -/

/-- The standardisation `std(w)` of a word `w` of length `n`:
`std(w)_i = #{j : w_j < w_i} + #{j ≤ i : w_j = w_i}`, the position of the letter `w_i` when the
letters are sorted increasingly and equal letters are broken by their position in `w`. The
codomain is usually given as `{1, …, n}`, which is the range of the map and not a condition
enforced by the type `Fin n → ℕ` used here; the `n ≥ 1` is likewise not a hypothesis,
the definition being vacuous at `n = 0`. The letters are `ℕ` rather than the `ℤ_{>0}`,
matching the alphabet convention of `sweepChar`; only the order on the letters is used, and the
two orders agree. -/
@[hjo "def_sweep_standardisation"]
def standardisation {n : ℕ} (w : Fin n → ℕ) (i : Fin n) : ℕ :=
  #{j ∈ (univ : Finset (Fin n)) | w j < w i} + #{j ∈ Iic i | w j = w i}

end HJO.Paths
