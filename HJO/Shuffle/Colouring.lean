/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.Sweep
public import HJO.Shuffle.SweepModule
public import HJO.Shuffle.Mellit
public meta import HJO.Attr

/-! # The sweep word, and the admissible colourings of a level

The sweep process of Mellit's Section 4 reads off, at every point of the swept region of an
above-diagonal `(aN, bN)`-path, one of five operators on the Carlsson–Mellit module, and multiplies
them along the region in decreasing order of above-diagonal rank. His Sections 4 and 6 then cut
that word at a level: the *colouring* of a path at a level records which steps of the path the
level line crosses, the *trace* records the part of the sweep already performed, and the
*invariant of a colouring* sums the intermediate results of the sweep over the traces the
colouring admits.

This file carries that layer: the event operator, the sweep word, the east steps, the colouring,
the admissible colourings, the partial sweep word, the trace, and the invariant `D_{η,c}`.

## Main definitions

* `HJO.Mellit.sweepOperator`: the event operator `Φ_{P̂}(P)`, an endomorphism of the total space.
* `HJO.Mellit.sweepWord`: the sweep word `W(P̂)`.
* `HJO.Mellit.eastSteps`: the east steps of an above-diagonal path, each named by its left end.
* `HJO.Mellit.colouring`: the colouring `c_η(P̂)` of a path at a level.
* `HJO.Mellit.IsAdmissibleColouring`: the admissible colourings at a level.
* `HJO.Mellit.partialSweepWord`: the partial sweep word `W_η(P̂)`.
* `HJO.Mellit.levelTrace`: the trace `τ_η(P̂)`.
* `HJO.Mellit.dsc`: the invariant `D_{η,c}` of a colouring.

## Main results

* `HJO.Mellit.sweepOperator_of_eventType_D_of_sweepRight_eq_zero`,
  `HJO.Mellit.sweepOperator_of_eventType_E`: the two branches of `sweepOperator` that are
  read off directly — rule D with exponent `0`, as at the corner `(aN, bN)`, is the
  identity, and rule E is multiplication by `u`.
* `HJO.Mellit.sortByRank_pairwise`, `HJO.Mellit.mem_sortByRank`,
  `HJO.Mellit.sortByRank_reverse_pairwise`: the listing of a set of lattice points used by the
  sweep word really is a rank-sorted enumeration of it, and its reverse is the
  decreasing listing.
* `HJO.Mellit.sweepWord_eq_mul_of_reverse_eq_cons`: the composition order. If `P_1 :: Ps` is the
  decreasing listing of `Sw(P̂)`, then `W(P̂)` has `Φ_{P̂}(P_1)` as its rightmost
  factor, hence applies it first — which is the reading of `Φ_{P̂}(P_M) ∘ ⋯ ∘ Φ_{P̂}(P_1)`.
* `HJO.Mellit.partialSweepWord_of_forall_le`: the `r = 0` clause, `W_η(P̂) = id` when
  no swept point outranks `η`.
* `HJO.Mellit.partialSweepWord_eq_sweepWord`: below every rank of the swept region the partial
  word is the full word, so the two listing conventions agree.
* `HJO.Mellit.colouring_subset`, `HJO.Mellit.fst_lt_of_mem_colouring`: a colouring consists of
  north and east steps of the path, and so meets only the `aN` columns of the rectangle — whence
  `HJO.Mellit.not_isAdmissibleColouring_of_le`, that a colouring reaching further east is
  admissible at no level.
* `HJO.Mellit.traceRep_spec`: the path chosen for a trace in the index set of `dsc` does realize
  that trace, so the sum of `dsc` is not indexed by fiat.
* `HJO.Mellit.traceIndex_eq_empty_iff`, `HJO.Mellit.dsc_eq_zero_of_not_isAdmissibleColouring`: the
  index set of `D_{η,c}` is empty exactly off the admissible locus, where the invariant is
  therefore `0`. This is the "Total in `c`" clause of `HJO.Mellit.dsc` read as a lemma, and it
  is what lets an identity in `D_{η,·}` survive a degenerate `c` with both sides `0`.

## Implementation notes

### The event operators live in one total space

`HJO.Mellit.sweepOperator` reads `Φ_{P̂}(P)` as a map `V_k → V_{k'}` with
`k = k_{P̂}(P)` and `k'` one of `k-1`, `k`, `k+1`, and `HJO.Mellit.sweepWord` and
`HJO.Mellit.partialSweepWord` compose those maps along the swept region with `k` changing at every
type-`A` and type-`B` event. Modelling `V_k` as a family of types would make both words
dependently typed composites whose intermediate types are computed from the path. So `V_k` is
`HJO.Sweep.piece L k` inside the single space `HJO.Sweep.Total L`, every `Φ_{P̂}(P)` is an element
of `Module.End L (HJO.Sweep.Total L)`, and both words are ordinary products in that monoid; the
domains and codomains of the graded maps are membership statements about `HJO.Sweep.piece`,
proved elsewhere. The graded index is not lost: each branch of `sweepOperator` passes
`HJO.Paths.sweepWidth y P` to the operator that reads it, which is exactly `k = k_{P̂}(P)`.

### The sort key

Both words list the swept points in strictly decreasing above-diagonal rank. The rank is injective
on the lattice points with `0 ≤ x ≤ aN` — two points of equal rank have `ay - bx` and `x` equal,
hence are equal — so the listing is unambiguous. The sort here is by that rank as an
**injective key into a linear order**, never by the order on `ℕ × ℕ`: `List.mergeSort (· ≤ ·)` on
pairs sorts by the product order, which is not total, and so silently returns a
permutation-dependent list. `HJO.Mellit.sortByRank_pairwise` records that the list produced is
genuinely sorted by the key and `HJO.Mellit.mem_sortByRank` that it enumerates the set.

`HJO.Mellit.sortByRank` sorts **increasingly**, where Mellit's sweep visits the points in decreasing
rank, and the words are the `List.prod` of the operators along the increasing list. This is Mellit's
composite and not its opposite: in `Module.End L M` the product `f * g` applies `g` first, so the
product along the increasing list applies the operator of the *highest*-ranked point first, which is
the `Φ_{P̂}(P_1)` of `Φ_{P̂}(P_M) ∘ ⋯ ∘ Φ_{P̂}(P_1)`. The decreasing listing `P_1, …, P_M` is
`(sortByRank …).reverse`, and `HJO.Mellit.sweepWord_eq_mul_of_reverse_eq_cons` states the order
against it.

### Levels are rationals, ranks are integers

A level is a `ℚ`, by `HJO.Mellit.IsAdmissibleLevel` (defined
in `HJO/Shuffle/Mellit.lean`): it must be allowed to be a half-integer, because integers do
not separate adjacent ranks — `(x, y)` and `(x+1, y + b/a)` have ranks differing by exactly `1`,
and the second is a lattice point whenever `a ∣ b`. Every rank is an integer, so every comparison
of a rank with a level below is a comparison in `ℚ` of the cast of an integer with a rational, and
nothing is definable at a level that would not be definable at an integer level.

Every definition here is total in the level and does not take `IsAdmissibleLevel` as a hypothesis,
in the house style of `HJO.Paths`; likewise none of them takes `HJO.Paths.IsAboveDiagonal` or
`P ∈ HJO.Paths.sweptRegion y`. The hypotheses enter in the lemmas.

### The representative of a trace

`HJO.Mellit.dsc` sums `W_η(P̂_τ)(1)` over the traces `τ` realized by some above-diagonal path
with colouring `c`, `P̂_τ` denoting such a path. **The sum is over traces and not over paths**, and
that is the substance of the object: summing over paths would count each intermediate result once
per completion of the swept part, and `HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`'s
value `D_{η,∅} = 1` would become the number of above-diagonal paths. So the index set
`HJO.Mellit.traceIndex` is the *image* of the paths with colouring `c` under `τ_η(·)` — a `Finset`
of traces, each counted once — and `HJO.Mellit.traceRep` picks a path out of the fibre by
`Exists.choose`, the existential being decidable because `HJO.Paths.Heights a b N` is a `Fintype`
with decidable equality. `HJO.Mellit.traceRep_spec` records that the chosen path realizes the trace.
The value does not depend on the choice, by `HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq`, which
is not formalized here; off the index set `traceRep` returns a junk path, which no statement reads.

The vacuum `1` is the unit of `HJO.Sweep.Total L`, which lies in `HJO.Sweep.piece L 0`, the
space `V_0`. That is the right end: the highest-ranked point of `Sw(P̂)` has width `0`
(`HJO.Mellit.sweepWord_mem_piece_zero`), so both the full and the partial sweep start on `V_0`, and
at a level above every rank the trace is empty, `W_η(P̂) = 1` and `D_{η,∅} = 1`, which is
`HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`.

### Checks of the arithmetic

Three numerical checks are recorded because they are the ones a transcription can get backwards.

The exponents of `q` are `q^{-a_{P̂}(P)}Δ` at type `C` and `q^{+a_{P̂}(P)}id` at type `D`, as Mellit
prints them in the sweep process of §4. They agree with the event-type docstrings of
`HJO.Paths.EventType`, and with
`HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv`: the total
power of `q` the sweep word produces is `Σ_D - Σ_C`, which that lemma evaluates as
`ĥ(P̂) - max t̂dinv(P̂)`, so `D` contributes positively and `C` negatively.

The east-step condition of `HJO.Mellit.colouring` is `rk̂(v + (1,0)) < η < rk̂(v)`, as printed, and
the direction is right because the rank *decreases* along an east step: it changes by
`1 - bN(aN + 1)`, negative as soon as `a`, `b`, `N ≥ 1`. On the example
`a = 2, b = 3, N = 1`, where `rk̂(x,y) = 6y - 8x` and `η = 21/2`, the east step at `(0,2)` has rank
`12` and `(1,2)` has rank `4`, and `4 < 21/2 < 12`. The `example` at the end of this file is that
computation, `decide`-checked.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, arXiv:1604.07456, §§4 and 6.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-! ### The above-diagonal rank of a lattice point -/

/-- The above-diagonal rank `rk̂(P)` of a lattice point `P = (x, y)`, as a function of the point:
`HJO.ParkingFunctions.abovePointRank` with its two coordinates packed into a pair. This is only
repackaging — `HJO.ParkingFunctions.abovePointRank` is that declaration — but it is the sort key of
`HJO.Mellit.sortByRank` and the quantity every condition below compares against a level, so it is
named once. -/
def pointRank (a b N : ℕ) (P : ℕ × ℕ) : ℤ := abovePointRank a b N P.1 P.2

/-! ### The operator of an event -/

/-- **The operator of an event.** `HJO.Mellit.sweepOperator`: for an above-diagonal
`(aN, bN)`-path `P̂` and `P ∈ Sw(P̂)`, `Φ_{P̂}(P)` is the `𝕜`-linear map from `V_k` to `V_{k'}`,
where `k = k_{P̂}(P)`, given by `d_+` with `k' = k+1` at event type `A`; by `d_-` with `k' = k-1`
at type `B`; by `q^{-a_{P̂}(P)}Δ` with `k' = k` at type `C`; by `q^{a_{P̂}(P)}id` with `k' = k` at
type `D`; and by `u · id` with `k' = k` at type `E`.

The graded index `k` is `HJO.Paths.sweepWidth y P` and the exponent `a_{P̂}(P)` is
`HJO.Paths.sweepRight y P`. **The exponent at type `C` is negative and at type `D` positive**, as
Mellit prints them and as the docstrings of `HJO.Paths.EventType` say; the negative one is
therefore a `zpow`, meaningful as the inverse of a power only for `q ≠ 0`, which holds over the
intended coefficient field `𝕜 = ℚ(q, u)`, where `q` and `u` are indeterminates and so
invertible. Nothing here assumes it: at `q = 0` the value is
the zero map, and every lemma that needs the exponent to be an inverse supplies `q ≠ 0`.

Three departures from the letter, none a change of the operator.

The domain and codomain are not types: `Φ_{P̂}(P)` is an endomorphism of the single space
`HJO.Sweep.Total L`, and the `V_k → V_{k'}` is a pair of membership statements about
`HJO.Sweep.piece`. See the module docstring: modelling `V_k` as a family of types would make the
sweep word a dependently typed composite whose intermediate types are computed from the path.

The definition is total in `P` and in `y`, where Mellit takes an above-diagonal path and
`P ∈ Sw(P̂)`; off the swept region `HJO.Paths.eventType` still returns one of the five types, so
the value is still one of the five operators, but the prose reading of it is not available.

The operators `d_-`, `d_+` and `Δ` are read at the index Mellit gives them, which is the
width at `P` — `HJO.Sweep.dminus q k`, `HJO.Sweep.dplus q k`, `HJO.Sweep.corner q k`. On the total
space those three constants are single endomorphisms whose index records only which graded piece
they are read on, so passing `k = k_{P̂}(P)` is what makes this the intended
operator rather than one of its siblings. -/
@[hjo "def_sweep_operator"]
noncomputable def sweepOperator (q u : L) (y : Heights a b N) (P : ℕ × ℕ) :
    Module.End L (Total L) :=
  match eventType y P with
  | EventType.A => dplus q (sweepWidth y P)
  | EventType.B => dminus q (sweepWidth y P)
  | EventType.C => q ^ (-(sweepRight y P : ℤ)) • corner q (sweepWidth y P)
  | EventType.D => q ^ sweepRight y P • (1 : Module.End L (Total L))
  | EventType.E => u • (1 : Module.End L (Total L))

/-- **Rule `D` with exponent `0` is the identity.** At a type-`D` event with no live north step to
the right — as at the corner `(aN, bN)`, where nothing is live at all — the event operator is the
identity map, the `q^{a_{P̂}(P)}id` at `a_{P̂}(P) = 0`. -/
theorem sweepOperator_of_eventType_D_of_sweepRight_eq_zero (q u : L) (y : Heights a b N)
    (P : ℕ × ℕ) (hP : eventType y P = EventType.D) (h0 : sweepRight y P = 0) :
    sweepOperator q u y P = 1 := by
  rw [sweepOperator, hP, h0, pow_zero, one_smul]

/-- **Rule `E` is multiplication by `u`.** At a point strictly below the path — which by
`HJO.Paths.eventType_eq_E_iff` is exactly a type-`E` event — the event operator is `u · id`. -/
theorem sweepOperator_of_eventType_E (q u : L) (y : Heights a b N) (P : ℕ × ℕ)
    (hP : eventType y P = EventType.E) : sweepOperator q u y P = u • 1 := by
  rw [sweepOperator, hP]

/-! ### Listing a set of lattice points by rank -/

/-- A finite set of lattice points listed in weakly **increasing** order of above-diagonal rank.
The sort is by the rank as a key into the linear order `ℤ`, never by the order on `ℕ × ℕ`: the
product order is not total, so `List.mergeSort (· ≤ ·)` on pairs neither sorts nor fails but
returns a permutation-dependent list. `HJO.Mellit.sortByRank_pairwise` and
`HJO.Mellit.mem_sortByRank` record that this is a sorted enumeration of the set.

Mellit's sweep visits the points of a swept region in strictly *decreasing* rank; listed as
`P_1, …, P_M`, that listing is `(sortByRank a b N s).reverse`, and the sweep words below are the
`List.prod` along the increasing list precisely so that `Φ_{P̂}(P_1)` is applied first. The
listing is unambiguous because the rank is injective on the lattice points with
`0 ≤ x ≤ aN`; no injectivity is needed here, the key being sorted weakly.

Noncomputable only because `Finset.toList` is: nothing below evaluates the list. -/
noncomputable def sortByRank (a b N : ℕ) (s : Finset (ℕ × ℕ)) : List (ℕ × ℕ) :=
  s.toList.mergeSort fun P Q => decide (pointRank a b N P ≤ pointRank a b N Q)

/-- The rank listing of a finite set of lattice points is a permutation of it. -/
theorem sortByRank_perm (a b N : ℕ) (s : Finset (ℕ × ℕ)) :
    (sortByRank a b N s).Perm s.toList :=
  List.mergeSort_perm _ _

/-- The rank listing of a finite set of lattice points enumerates exactly that set. -/
theorem mem_sortByRank {s : Finset (ℕ × ℕ)} {P : ℕ × ℕ} :
    P ∈ sortByRank a b N s ↔ P ∈ s := by
  rw [(sortByRank_perm a b N s).mem_iff, Finset.mem_toList]

/-- The rank listing has no repetitions, being a permutation of the `Finset`'s own list. -/
theorem sortByRank_nodup (a b N : ℕ) (s : Finset (ℕ × ℕ)) : (sortByRank a b N s).Nodup :=
  (sortByRank_perm a b N s).nodup_iff.2 s.nodup_toList

/-- **The rank listing is sorted by rank.** This is what makes `sortByRank` a reading of the
rank-ordered listing rather than an arbitrary enumeration. -/
theorem sortByRank_pairwise (a b N : ℕ) (s : Finset (ℕ × ℕ)) :
    (sortByRank a b N s).Pairwise fun P Q => pointRank a b N P ≤ pointRank a b N Q := by
  refine (List.pairwise_mergeSort (fun P Q R hPQ hQR => ?_) (fun P Q => ?_) s.toList).imp ?_
  · exact decide_eq_true ((of_decide_eq_true hPQ).trans (of_decide_eq_true hQR))
  · rcases le_total (pointRank a b N P) (pointRank a b N Q) with h | h
    · simp [h]
    · simp [h]
  · exact fun h => of_decide_eq_true h

/-- **The listing is the reverse of the rank listing**, and it is sorted by decreasing
rank, as `P_1, …, P_M` is asked to be. -/
theorem sortByRank_reverse_pairwise (a b N : ℕ) (s : Finset (ℕ × ℕ)) :
    (sortByRank a b N s).reverse.Pairwise fun P Q => pointRank a b N Q ≤ pointRank a b N P :=
  List.pairwise_reverse.2 (sortByRank_pairwise a b N s)

/-- The rank listing of the empty set is empty. -/
@[simp]
theorem sortByRank_empty (a b N : ℕ) : sortByRank a b N ∅ = [] := by
  simp [sortByRank]

/-! ### The sweep word -/

/-- **The sweep word.** `HJO.Mellit.sweepWord`: for an above-diagonal `(aN, bN)`-path
`P̂`, listing `Sw(P̂)` as `P_1, …, P_M` in strictly decreasing order of above-diagonal rank,
`W(P̂) := Φ_{P̂}(P_M) ∘ ⋯ ∘ Φ_{P̂}(P_1)`.

Written here as the `List.prod` of the event operators along
`HJO.Mellit.sortByRank a b N (HJO.Paths.sweptRegion y)`, the *increasing* rank listing — that is,
along `P_M, …, P_1`. **That is the composite and not its opposite**: in
`Module.End L (HJO.Sweep.Total L)` the product `f * g` applies `g` first, so the rightmost factor
of this product, the operator of the highest-ranked point `P_1`, acts first, exactly as
`Φ_{P̂}(P_M) ∘ ⋯ ∘ Φ_{P̂}(P_1)` asks. `HJO.Mellit.sweepWord_eq_mul_of_reverse_eq_cons` states this
against the decreasing listing.

The composite is an endomorphism of the total space `HJO.Sweep.Total L`, where Mellit's
factors go between the graded pieces; `HJO.Mellit.sweepWord_mem_piece_zero` — that `W(P̂)` is
defined and maps `V_0` to `V_0` — is not part of the definition here, since a product in
`Module.End` is defined whatever the widths do. Total in `y`, where Mellit takes an
above-diagonal path. -/
@[hjo "def_sweep_word"]
noncomputable def sweepWord (q u : L) (y : Heights a b N) : Module.End L (Total L) :=
  ((sortByRank a b N (sweptRegion y)).map (sweepOperator q u y)).prod

/-- **The composition order of the sweep word.** Let `P :: Ps` be the listing of
`Sw(P̂)` in decreasing rank, so that `P = P_1` is the highest-ranked swept point. Then
`W(P̂) = (Φ_{P̂}(P_r) ⋯ Φ_{P̂}(P_2)) · Φ_{P̂}(P)`: the factor of `P_1` stands rightmost, hence acts
first, which is the reading of `Φ_{P̂}(P_M) ∘ ⋯ ∘ Φ_{P̂}(P_1)`. -/
theorem sweepWord_eq_mul_of_reverse_eq_cons (q u : L) (y : Heights a b N) {P : ℕ × ℕ}
    {Ps : List (ℕ × ℕ)} (h : (sortByRank a b N (sweptRegion y)).reverse = P :: Ps) :
    sweepWord q u y = (Ps.reverse.map (sweepOperator q u y)).prod * sweepOperator q u y P := by
  have hasc : sortByRank a b N (sweptRegion y) = Ps.reverse ++ [P] := by
    rw [← List.reverse_reverse (sortByRank a b N (sweptRegion y)), h]
    simp
  rw [sweepWord, hasc, List.map_append, List.prod_append]
  simp

/-! ### The partial sweep word -/

/-- The points of the swept region of `y` that outrank a level `η`: the index set of the partial
sweep word and of the trace. The rank is an integer and the level a rational, so the comparison is
in `ℚ`; see the module docstring on why a level must be allowed to be a half-integer. -/
def sweptAbove (y : Heights a b N) (η : ℚ) : Finset (ℕ × ℕ) :=
  {P ∈ sweptRegion y | η < (pointRank a b N P : ℚ)}

/-- **The partial sweep word.** `HJO.Mellit.partialSweepWord`: for an
above-diagonal `(aN, bN)`-path `P̂` and an admissible level `η`, listing as `P_1, …, P_r` in
strictly decreasing order of above-diagonal rank the points `P ∈ Sw(P̂)` with `rk̂(P) > η`,
`W_η(P̂) := Φ_{P̂}(P_r) ∘ ⋯ ∘ Φ_{P̂}(P_1)`, and `W_η(P̂) := id` when `r = 0`.

The `r = 0` clause needs no case split here: the product along an empty list is `1`, the identity
endomorphism, which is `HJO.Mellit.partialSweepWord_of_forall_le`. As with
`HJO.Mellit.sweepWord`, the composite is written as the `List.prod` along the *increasing* rank
listing, which applies `Φ_{P̂}(P_1)` first; the two definitions use the same convention, and
`HJO.Mellit.partialSweepWord_eq_sweepWord` records that below every rank of the swept region the
partial word is the full word.

The level is a `ℚ` and is not required to satisfy `HJO.Mellit.IsAdmissibleLevel`, and `y` is not
required to be above-diagonal; both hypotheses enter in the lemmas, in the house style of
`HJO.Paths`. -/
@[hjo "def_colouring_partial_word"]
noncomputable def partialSweepWord (q u : L) (y : Heights a b N) (η : ℚ) :
    Module.End L (Total L) :=
  ((sortByRank a b N (sweptAbove y η)).map (sweepOperator q u y)).prod

/-- **The `r = 0` clause.** When no point of the swept region outranks `η`, the partial sweep word
is the identity. -/
theorem partialSweepWord_of_forall_le (q u : L) (y : Heights a b N) (η : ℚ)
    (h : ∀ P ∈ sweptRegion y, (pointRank a b N P : ℚ) ≤ η) : partialSweepWord q u y η = 1 := by
  have hempty : sweptAbove y η = ∅ :=
    Finset.filter_eq_empty_iff.2 fun {_} hP => not_lt.2 (h _ hP)
  rw [partialSweepWord, hempty, sortByRank_empty, List.map_nil, List.prod_nil]

/-- **Below every rank of the swept region the partial word is the full word.** The two
listings — `HJO.Mellit.sweepWord` over all of `Sw(P̂)` and `HJO.Mellit.partialSweepWord` over the
part above `η` — use the same convention, so at a level under every rank they agree. -/
theorem partialSweepWord_eq_sweepWord (q u : L) (y : Heights a b N) (η : ℚ)
    (h : ∀ P ∈ sweptRegion y, η < (pointRank a b N P : ℚ)) :
    partialSweepWord q u y η = sweepWord q u y := by
  rw [partialSweepWord, sweepWord, sweptAbove, Finset.filter_true_of_mem h]

/-! ### The east steps of an above-diagonal path -/

/-- **The east steps of an above-diagonal path.** `HJO.Mellit.eastSteps`: the
lattice points `(x, ŷ_{x+1})` with `0 ≤ x ≤ aN - 1`, the point `(x, ŷ_{x+1})` standing for the
unit segment from `(x, ŷ_{x+1})` to `(x+1, ŷ_{x+1})`. Each east step is named by its **left** end,
as each north step of `HJO.Paths.northSteps` is named by its foot.

The `0 ≤ x ≤ aN - 1` is written as `x ∈ range (aN)`, avoiding the truncated
subtraction of `ℕ`, which at `aN = 0` would read `x ≤ 0` and admit `x = 0` where the range is
empty. Total on the height vectors, as `HJO.Paths.northSteps` is: on an above-diagonal
path the ordinate `ŷ_{x+1}` is the height of the path just right of `x`, so the pairs listed are
the east steps on the nose, and column `x` contributes one whatever the heights do. -/
@[hjo "def_colouring_east_steps"]
def eastSteps (y : Heights a b N) : Finset (ℕ × ℕ) :=
  (Finset.range (a * N)).image fun x => (x, ht y (x + 1))

/-! ### The colouring of a path at a level -/

/-- **The colouring of a path at a level.** `HJO.Mellit.colouring`: for an
above-diagonal `(aN, bN)`-path `P̂` and an admissible level `η`, `c_η(P̂)` is the union of
`{u a north step of P̂ : rk̂(u) < η < rk̂(u) + ω}` and
`{v an east step of P̂ : rk̂(v + (1,0)) < η < rk̂(v)}`, where `ω` is the attack window.

Mellit's colouring is the family of connected components of the intersection of the level line
with the figure bounded by the path and the diagonal; each component starts where the line crosses
a north step and ends where it crosses an east step, and the two conditions above are exactly those
crossings — the rank rises by `ω` from the foot to the head of a north step, and falls along an
east step.

**Both halves are needed, and a colouring recording only the north steps is a different and
unusable object.** The exit points are not determined by the entering ones: two above-diagonal
paths can have the same crossed north steps at one level and different crossed east steps. Take
`a = 2`, `b = 3`, `N = 1`, so `aN = 2`, `bN = 3`, `ω = 6` and `rk̂(x,y) = 6y - 8x`, and take
`η = 21/2`. The two `(2,3)`-paths with height vectors `(0,2,3)` and `(0,3,3)` each have `(0,1)`, of
rank `6`, as their only crossed north step; their crossed east steps differ — the step at `(0,2)`,
of rank `12`, for the first path and the step at `(0,3)`, of rank `18`, for the second. So a
colouring recording `{(0,1)}` alone does not say where the component ends, and rule D of
Mellit's Theorem 4.2, which fires exactly when the swept point is an endpoint of that kind, cannot
be stated against it. The `example` at the end of this file is that computation, `decide`-checked,
so the warning is machine-checked and not merely recorded.

Two departures from the letter. The ranks are integers and the level a rational, so
every comparison is a comparison in `ℚ` of the cast of an integer with a rational; the level must
be allowed to be a half-integer, because integers do not separate adjacent ranks — `(x,y)` and
`(x+1, y + b/a)` have ranks differing by exactly `1`, and the second is a lattice point whenever
`a ∣ b`, so with integer levels those points could not be separated and the recursion of
Mellit's Theorem 4.2 could not be stepped past them. And the definition is total: it takes neither
`HJO.Mellit.IsAdmissibleLevel η` nor `HJO.Paths.IsAboveDiagonal y`, both of which enter in the
lemmas. -/
@[hjo "def_colouring_of_path"]
def colouring (y : Heights a b N) (η : ℚ) : Finset (ℕ × ℕ) :=
  {u ∈ northSteps y | (pointRank a b N u : ℚ) < η ∧
      η < (pointRank a b N u : ℚ) + (attackWindow a N : ℚ)} ∪
    {v ∈ eastSteps y | (pointRank a b N (v.1 + 1, v.2) : ℚ) < η ∧
      η < (pointRank a b N v : ℚ)}

/-- A colouring consists of north steps and east steps of the path. -/
theorem colouring_subset (y : Heights a b N) (η : ℚ) :
    colouring y η ⊆ northSteps y ∪ eastSteps y :=
  Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- **A coloured point lies in a column of the rectangle.** Both halves of a colouring are indexed
by `Finset.range (aN)` — the north steps by their column, the east steps by their left end — so no
colouring of an `(aN, bN)`-path reaches the column `aN`. Nothing is asked of the level, nor of `y`
being above-diagonal. -/
theorem fst_lt_of_mem_colouring {y : Heights a b N} {η : ℚ} {p : ℕ × ℕ}
    (hp : p ∈ colouring y η) : p.1 < a * N := by
  rcases Finset.mem_union.1 (colouring_subset y η hp) with h | h
  · exact (Paths.mem_northSteps_iff.1 h).1
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
    exact Finset.mem_range.1 hx

/-- **Admissible colouring.** `HJO.Mellit.IsAdmissibleColouring`: an admissible colouring
at an admissible level `η` is a set of the form `c_η(P̂)` for some above-diagonal
`(aN, bN)`-path `P̂`.

This is Mellit's own characterisation (§4, after Definition 4.1) — "admissible colorings of `l_h`
are precisely the sets that can appear as the intersection of `l_h` with the figure bounded by some
`(m,n)`-Dyck path and the diagonal" — taken as the definition, rather than the intrinsic description
by non-overlapping intervals. The two agree, but the intrinsic form needs the interleaving condition
on the crossed steps written out, and nothing below uses it.

The level is not required to satisfy `HJO.Mellit.IsAdmissibleLevel`; the predicate is total in it,
and the admissibility of the level enters in the lemmas. The path *is* required to be
above-diagonal, since the quantifier is over above-diagonal paths and dropping it
would make far more sets admissible. -/
@[hjo "def_colouring_admissible"]
def IsAdmissibleColouring (a b N : ℕ) (η : ℚ) (c : Finset (ℕ × ℕ)) : Prop :=
  ∃ y : Heights a b N, IsAboveDiagonal y ∧ colouring y η = c

/-- **A colouring carrying a point east of the rectangle is inadmissible at every level.** By
`HJO.Mellit.fst_lt_of_mem_colouring` no colouring of an `(aN, bN)`-path reaches the column `aN`, and
that bound is uniform in the level, so such a `c` is admissible at no `η` at all. -/
theorem not_isAdmissibleColouring_of_le {c : Finset (ℕ × ℕ)} {p : ℕ × ℕ} (hpc : p ∈ c)
    (hp : a * N ≤ p.1) (η : ℚ) : ¬ IsAdmissibleColouring a b N η c := by
  rintro ⟨y, -, hy⟩
  exact absurd (fst_lt_of_mem_colouring (y := y) (η := η) (hy ▸ hpc)) (by omega)

/-! ### The trace of a path at a level -/

/-- **The trace of a path at a level.** `HJO.Mellit.levelTrace`: for an
above-diagonal `(aN, bN)`-path `P̂` and an admissible level `η`,
`τ_η(P̂) := {(P, ev_{P̂}(P), a_{P̂}(P)) : P ∈ Sw(P̂) and rk̂(P) > η}`.

A `Finset` of triples (point, event type, live count to the right), obtained as the image of
`HJO.Mellit.sweptAbove y η` under the evident map; the first component determines the other two,
so the image has one element per swept point above the level. The trace is what
`HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq` shows the partial sweep word to depend on, and
therefore what `HJO.Mellit.dsc` sums over. Total in `η` and in `y`, as everything here is. -/
@[hjo "def_colouring_trace"]
def levelTrace (y : Heights a b N) (η : ℚ) : Finset ((ℕ × ℕ) × EventType × ℕ) :=
  (sweptAbove y η).image fun P => (P, eventType y P, sweepRight y P)

/-! ### The invariant of a colouring -/

/-- The traces realized at level `η` by the above-diagonal paths whose colouring at `η` is `c`:
the index set of `HJO.Mellit.dsc`. It is the *image* of those paths under `τ_η(·)`, so each trace
is counted once however many paths realize it — which is the substance of `HJO.Mellit.dsc`. -/
def traceIndex (a b N : ℕ) (η : ℚ) (c : Finset (ℕ × ℕ)) :
    Finset (Finset ((ℕ × ℕ) × EventType × ℕ)) :=
  {y ∈ (univ : Finset (Heights a b N)) | IsAboveDiagonal y ∧ colouring y η = c}.image
    fun y => levelTrace y η

/-- **The index set of `HJO.Mellit.dsc` is empty exactly off the admissible locus.** A trace is
indexed by a path, so the image is empty precisely when no above-diagonal path is coloured `c` —
which is the negation of `HJO.Mellit.IsAdmissibleColouring`, that predicate being the bare
existential. -/
theorem traceIndex_eq_empty_iff {η : ℚ} {c : Finset (ℕ × ℕ)} :
    traceIndex a b N η c = ∅ ↔ ¬ IsAdmissibleColouring a b N η c := by
  rw [traceIndex, Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  exact ⟨fun h ⟨y, hy, hc⟩ => h (Finset.mem_univ y) ⟨hy, hc⟩,
    fun h {y} _ hy => h ⟨y, hy.1, hy.2⟩⟩

/-- The path `P̂_τ` picked for a trace `τ`: an above-diagonal path with colouring `c`
at `η` and trace `τ`, chosen by `Exists.choose` out of the fibre. The existential is decidable,
`HJO.Paths.Heights a b N` being a `Fintype` with decidable equality and each condition decidable,
so the `dite` is not a use of choice on a proposition without content;
`HJO.Mellit.traceRep_spec` records that the chosen path does realize the trace. Off
`HJO.Mellit.traceIndex a b N η c` the value is a junk path, which no statement reads. -/
noncomputable def traceRep (a b N : ℕ) (η : ℚ) (c : Finset (ℕ × ℕ))
    (τ : Finset ((ℕ × ℕ) × EventType × ℕ)) : Heights a b N :=
  if h : ∃ y : Heights a b N, IsAboveDiagonal y ∧ colouring y η = c ∧ levelTrace y η = τ then
    h.choose
  else default

/-- **The representative of a trace realizes it.** For a trace in the index set of
`HJO.Mellit.dsc`, the chosen path is above-diagonal, has colouring `c` at `η`, and has that very
trace. This is what makes the sum of `HJO.Mellit.dsc` a sum over realized traces rather than over
an index set produced by fiat. -/
theorem traceRep_spec {η : ℚ} {c : Finset (ℕ × ℕ)} {τ : Finset ((ℕ × ℕ) × EventType × ℕ)}
    (hτ : τ ∈ traceIndex a b N η c) :
    IsAboveDiagonal (traceRep a b N η c τ) ∧ colouring (traceRep a b N η c τ) η = c ∧
      levelTrace (traceRep a b N η c τ) η = τ := by
  have h : ∃ y : Heights a b N, IsAboveDiagonal y ∧ colouring y η = c ∧ levelTrace y η = τ := by
    simp only [traceIndex, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hτ
    obtain ⟨y, ⟨hy, hc⟩, hyt⟩ := hτ
    exact ⟨y, hy, hc, hyt⟩
  rw [traceRep]
  split_ifs
  exact h.choose_spec

/-- **The invariant of a colouring.** `HJO.Mellit.dsc`: for an admissible level
`η` and an admissible colouring `c` at `η`, `D_{η,c} := ∑_τ W_η(P̂_τ)(1)`, the sum over those sets
`τ` that are `τ_η(P̂)` for at least one above-diagonal `(aN, bN)`-path `P̂` with `c_η(P̂) = c`,
where `P̂_τ` denotes such a path.

The summand does not depend on which such path is taken, by
`HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq`, which is not formalized here;
`HJO.Mellit.traceRep` makes the choice and `HJO.Mellit.traceRep_spec` says it is a path of the
fibre.

**The sum is over traces and not over paths**, and that is the substance of the object: Mellit
describes `D_{s,c}` as a sum of the intermediate results of the sweep over the families of
colourings that begin empty and end at `c`, and such a family records only what the sweep has
already seen. Summing over complete paths instead would count each intermediate result once per
completion of the swept part, and the initial value `D_{η,∅} = 1` of
`HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one` would become the number of above-diagonal
paths. So the index set is `HJO.Mellit.traceIndex a b N η c`, the image of the paths with colouring
`c` under `τ_η(·)`.

The vacuum `1` is the unit of `HJO.Sweep.Total L`, which lies in `HJO.Sweep.piece L 0` — the
space `V_0`, and not `V_k` for the width at the start of the partial sweep. That is the right
reading: the highest-ranked point of `Sw(P̂)` has width `0` by
`HJO.Mellit.sweepWord_mem_piece_zero`, so the partial sweep, like the full one, starts on `V_0`; and
at a level above every rank the trace is empty, `W_η(P̂) = 1` by
`HJO.Mellit.partialSweepWord_of_forall_le`, the index set is the single trace `∅`, and the sum is
`1`, which is `HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`.

Total in `c`: Mellit takes `c` admissible, and at an inadmissible `c` the index set is
empty and the value `0`, which is
`HJO.Mellit.dsc_eq_zero_of_not_isAdmissibleColouring`. -/
@[hjo "def_colouring_dsc"]
noncomputable def dsc (q u : L) (a b N : ℕ) (η : ℚ) (c : Finset (ℕ × ℕ)) : Total L :=
  ∑ τ ∈ traceIndex a b N η c, partialSweepWord q u (traceRep a b N η c τ) η (1 : Total L)

/-- **`dsc` vanishes at an inadmissible colouring**, its index set `HJO.Mellit.traceIndex` being
empty there. This is the "Total in `c`" clause of `HJO.Mellit.dsc`'s own docstring, and it asks
nothing of `η`, `a`, `b` or `N`. -/
theorem dsc_eq_zero_of_not_isAdmissibleColouring (q u : L) {η : ℚ} {c : Finset (ℕ × ℕ)}
    (h : ¬ IsAdmissibleColouring a b N η c) : dsc q u a b N η c = 0 := by
  rw [dsc, traceIndex_eq_empty_iff.2 h, Finset.sum_empty]

/-! ### The counterexample, checked

Two above-diagonal `(2,3)`-paths with the same crossed north step at `η = 21/2` and different
crossed east steps. This is why `HJO.Mellit.colouring` records both halves: dropping the east
steps would identify these two colourings and lose where the component ends. -/

/-- **The crossed east steps are not determined by the crossed north steps.** The counterexample of
`HJO.Mellit.colouring`'s docstring, computed. Both `(0,2,3)` and `(0,3,3)` are above-diagonal
`(2,3)`-paths; at the level `η = 21/2` both colourings contain the north step `(0,1)`, of rank `6`,
as their only north step, and their east steps differ — `(0,2)`, of rank `12`, for the first and
`(0,3)`, of rank `18`, for the second. So a colouring recording only `{(0,1)}` would identify these
two paths and lose where the component of the level line ends.

The equalities are checked by computation on the explicit `Finset`s: the north and east steps by
`decide`, the level comparisons by `norm_num`, the rational level being outside the reach of the
kernel's arithmetic. -/
theorem colouring_east_steps_not_determined :
    IsAboveDiagonal (![0, 2, 3] : Heights 2 3 1) ∧
      IsAboveDiagonal (![0, 3, 3] : Heights 2 3 1) ∧
      colouring (![0, 2, 3] : Heights 2 3 1) (21 / 2) = {(0, 1), (0, 2)} ∧
      colouring (![0, 3, 3] : Heights 2 3 1) (21 / 2) = {(0, 1), (0, 3)} := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · have hn : northSteps (![0, 2, 3] : Heights 2 3 1) = {(0, 0), (0, 1), (1, 2)} := by decide
    have he : eastSteps (![0, 2, 3] : Heights 2 3 1) = {(0, 2), (1, 3)} := by decide
    rw [colouring, hn, he]
    norm_num [pointRank, abovePointRank, attackWindow, Finset.filter_insert,
      Finset.filter_singleton]
  · have hn : northSteps (![0, 3, 3] : Heights 2 3 1) = {(0, 0), (0, 1), (0, 2)} := by decide
    have he : eastSteps (![0, 3, 3] : Heights 2 3 1) = {(0, 3), (1, 3)} := by decide
    rw [colouring, hn, he]
    norm_num [pointRank, abovePointRank, attackWindow, Finset.filter_insert,
      Finset.filter_singleton]

end HJO.Mellit
