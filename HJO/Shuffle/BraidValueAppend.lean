/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendBandPerPath

/-! # The `append` field of `IsBraidValue` at `braidValue`, as one identity between path sums

`HJO.Mellit.mellitInduction_iff_braidClosedForm` makes the clause `HJO.Mellit.MellitInduction`
equivalent to `HJO.Mellit.BraidClosedForm`, and at `HJO.Mellit.sweepWitness` three of that
conjunction's pieces are proved: `HJO.Mellit.replExists_sweepWitness`,
`HJO.Mellit.isColouringValue_sweepWitness` and `HJO.Mellit.braidValue_nil`. The piece left is the
`append` field of `HJO.Mellit.IsBraidValue` at `B := HJO.Mellit.braidValue`.

This file writes that field out as an identity between two sums over the *same* index set of paths,
and hands the result to the `hind` binder of `HJO.Mellit.shuffle_of_lhs_and_induction` in the shape
that binder asks for it. Nothing of the braid monoid occurs anywhere, and no route through
`HJO.Mellit.braidValueColouring_eq_dsc_floor` or
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` is used: both sides of the field are expanded
into partial sweep words by `HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord`, and the two
index sets are matched by `HJO.Mellit.sum_aboveReturnPaths_append_singleton`.

## What is here

Three compositions of proved equivalences and one binder:

* `HJO.Mellit.braidValue_append_iff_sum_split` — the `append` field at `HJO.Mellit.braidValue` is
  the summed identity, base path by base path on the right and base path with tail on the left;
* `HJO.Mellit.braidClosedForm_sweepWitness_iff_sum_split` and
  `HJO.Mellit.mellitInduction_sweepWitness_iff_sum_split` — the same for the whole conjunction and
  for the clause;
* `HJO.Mellit.hind_of_forall_sum_split` — the summed identity, asked for only under
  `AlgebraicIndependent ℤ ![q, u]` and `1 < a < b`, gives the second binder of
  `HJO.Mellit.shuffle_of_lhs_and_induction` verbatim.

## THE SUM DOES NOT SPLIT, AND CANNOT BE MADE TO

The identity cannot be proved summand by summand. Write `D(z)` for the per-base-path discrepancy —
the left summand at `z` minus the right summand at `z`. The identity above says `∑_z D(z) = 0`, and
the temptation is to prove `D(z) = 0` at each `z` and be done.

`D(z) = 0` at every `z` is `HJO.Mellit.sweepAppend_of_forall_path`, and it is **false**:
`HJO/Shuffle/SweepAppendBandPerPath.lean` records the computation at `(a,b) = (2,3)`,
`α = [1]`, `A = 1`, where the two discrepancies are nonzero and exactly opposite.
`HJO.Mellit.sweepAppend_of_forall_band` and `HJO.Mellit.sweepAppend_of_forall_band_uniform` are that
same hypothesis in the band factorisation, by `HJO.Mellit.band_iff_perPath`, so all three are
vacuous.

Further computation gives a stronger negative answer than "the per-path reading is too strong". At
`(a,b) = (2,3)`, `α = [1,1]`, `A = 1` there are four base paths; all four discrepancies are nonzero,
pairwise distinct up to sign, and **no proper nonempty subset of them sums to zero**. The same at
`(a,b) = (2,5)`, `α = [1]` (three base paths), at `(a,b) = (3,4)`, `α = [1]` (five), at
`(a,b) = (3,5)`, `α = [1]` (seven) and at `(a,b) = (2,7)`, `α = [1]` (four). At `(a,b) = (2,3)`,
`α = [2]`, `A = 1` there are nineteen base paths, nineteen discrepancies pairwise distinct up to
sign, no `±` pair among them, and no partition of them by any of the obvious path statistics — each
height, the north-step vector, the diagonal-excess vector — whose blocks sum to zero. The exact `±`
pairing at `α = [1]` is an accident of that index set having two elements.

Two weakenings of the per-path reading were tested in the same computation at `(a,b) = (2,3)`,
`α = [1,1]`, `A = 1`, and both fail. The per-path identity does **not** hold up to a path-dependent
scalar: at no base path is the left summand a multiple of the right summand by an element of
`ℚ(q,u)`. And the two per-path families are not related by any linear reindexing at all: the four
right summands are linearly independent over `ℚ(q,u)`, and **no** left summand lies in their span.
So there is no triangular or permuted change of basis carrying one family to the other; only the two
totals agree.

So the cancellation is **global over the whole base-path index set**, and every strategy that
refines it is closed rather than merely unproved: one identity per base path, one identity per block
of any partition of the base paths, a sign-reversing involution on the base paths, a per-path
identity corrected by a scalar, and a linear reindexing between the two per-path families are all
refuted. No lemma reducing the identity to any of them is stated here, for the reason
`HJO/Shuffle/SweepAppendBandPerPath.lean` gives: it would be one more correct theorem with a
false hypothesis. `HJO/Shuffle/SweepAppendPairing.lean` reaches the same verdict from a second,
independently written transcription — it names the per-path discrepancy
`HJO.Mellit.appendDisc`, reports that the `ℚ(q,u)`-span of the discrepancies has rank `#z - 1` with
the all-ones vector spanning the relations, and proves that the half turn cannot be the pairing.
Two transcriptions, written without reference to each other, agree instance by instance.

What the same computation says positively is that the summed identity itself holds at every one of
the ten instances tested: `(a,b) = (2,3)` at `α = []` with `A ∈ {1,2}`, at `α = [1]` with
`A ∈ {1,2}`, at `α = [2]` and at `α = [1,1]` with `A = 1`; and `α = [1]`, `A = 1` at each of
`(a,b) = (2,5)`, `(3,4)`, `(3,5)` and `(2,7)`. The per-path reading failed at each of the eight of
those with more than one base path. All of that is **model-only** — a transcription of
`HJO.Paths.sweptRegion`, `HJO.Paths.eventType`, `HJO.Paths.sweepWidth`, `HJO.Paths.sweepRight`,
`HJO.ParkingFunctions.abovePointRank`, `HJO.Mellit.sweepOperator`, `HJO.Mellit.partialSweepWord` and
`HJO.Mellit.stageTotal`, validated by reproducing `HJO.Mellit.sweepAppend_nil_two_three_one`,
`HJO.Mellit.sweepAppend_nil_one_two_two` and the `decide`-checked ranks, event types, widths and
`HJO.Paths.sweepRight`s of `HJO/Shuffle/SweepAppendNilTwo.lean` exactly. It is not a Lean proof
and nothing below depends on it. The instances that *are* Lean-proved are
`HJO.Mellit.sweepAppend_nil_two_three_one`, `HJO.Mellit.sweepAppend_nil_one_two_two` and
`HJO.Mellit.sweepAppend_nil_one_one_b`, all at `α = []`, where the base index set is a singleton and
the defect above cannot be seen.

## Genericity

The three equivalences carry coprimality and `0 < a`, `0 < b`, and nothing on `q` or `u` — exactly
what `HJO.Mellit.braidClosedForm_sweepWitness_iff_sweepAppend` and
`HJO.Mellit.sweepAppend_iff_sum_split` carry, and for the same reason: the bare statement is refuted
at `q = 1, a = 1` by `HJO.Mellit.not_sweepAppend_one_left`, and at `q = 0` and at `u = 0` by the
`(2,3)` instances of `HJO/Shuffle/SweepAppendTwoThree.lean`, so a per-`q` equivalence cannot
carry the hypothesis that excludes them. `HJO.Mellit.hind_of_forall_sum_split` is where the
genericity sits, and it takes it from the quantifier of `HJO.Mellit.shuffle_of_lhs_and_induction`.

The `(q*u)^(1 - (A:ℤ))` of the scalar is a `zpow` with a negative exponent at `1 < A`, and no
hypothesis on `q * u` is needed for it here for the reason `HJO/Shuffle/MellitAppend.lean`
records: the factor is only ever factored out, never divided by. Below it is carried through
untouched as the scalar of a `•`, and is never inverted.

## What this file does NOT do

It does not prove the field. Every statement is an equivalence or a one-way reduction whose
hypothesis is the path-sum identity; none assumes `HJO.Mellit.SweepAppend`,
`HJO.Mellit.BraidClosedForm` or `HJO.Mellit.braidValueColouring_eq_dsc_floor`. Of the
two binders of `HJO.Mellit.shuffle_of_lhs_and_induction`, `hlhs` is
untouched by anything here and `hind` is reduced, not discharged.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking
functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Mellit

open Finset Paths HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-- **The `append` field of `HJO.Mellit.IsBraidValue` at `HJO.Mellit.braidValue`, written out as an
identity between two sums over the base paths.** On the left, for each above-diagonal
`(a·α.sum, b·α.sum)`-path `z` of return composition `α`, the partial sweep words of `z` extended by
each above-diagonal `(aA, bA)`-path `w` of return composition `(A)`; on the right the stage
`G_{ℓ+1,A}` of `HJO.Mellit.stage` applied to the partial sweep word of `z`, with the scalar
`(-1)^{(a-1)A}(qu)^{1-A}` of `HJO.Mellit.braidRep_specialBraid_dplusIter`.

The `nil` field is `HJO.Mellit.braidValue_nil`, already proved, so the whole structure *is* the
`append` field; `HJO.Mellit.isBraidValue_sweepWitness_iff` turns that into `HJO.Mellit.SweepAppend`
and `HJO.Mellit.sweepAppend_iff_sum_split` turns that into the path sums. The replication family is
arbitrary: `HJO.Mellit.euclid` pins both inputs of the stage, so no choice of `Ω` is privileged.

The summands do **not** agree base path by base path — see the module docstring. -/
theorem braidValue_append_iff_sum_split (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω) :
    IsBraidValue (sweepWitness q u a b) Ω a b (braidValue q u a b)
      ↔ ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
        ∑ z ∈ aboveReturnPaths a b α.sum α,
            ∑ w ∈ aboveReturnPaths a b A [A],
              partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
          = ∑ z ∈ aboveReturnPaths a b α.sum α,
              ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
                stageTotal q u a b α.length A
                  (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L)) :=
  (isBraidValue_sweepWitness_iff hab ha hb hΩ).trans (sweepAppend_iff_sum_split hab ha hb)

/-- **`HJO.Mellit.BraidClosedForm` at the witness is that same identity between path sums.** The
three proved pieces — `HJO.Mellit.replExists_sweepWitness`,
`HJO.Mellit.isColouringValue_sweepWitness` and `HJO.Mellit.braidValue_nil` — are spent inside
`HJO.Mellit.braidClosedForm_sweepWitness_iff_sweepAppend`, which also supplies the backward
direction: the braid value is *forced* at this witness, so the conjunction cannot be met by any
other `B`. -/
theorem braidClosedForm_sweepWitness_iff_sum_split (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) :
    BraidClosedForm (sweepWitness q u a b) a b
      ↔ ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
        ∑ z ∈ aboveReturnPaths a b α.sum α,
            ∑ w ∈ aboveReturnPaths a b A [A],
              partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
          = ∑ z ∈ aboveReturnPaths a b α.sum α,
              ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
                stageTotal q u a b α.length A
                  (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L)) :=
  (braidClosedForm_sweepWitness_iff_sweepAppend hab ha hb).trans
    (sweepAppend_iff_sum_split hab ha hb)

/-- **`HJO.Mellit.mellitInduction_sweepWitness` at the witness is that same identity between path
sums.** The composition through `HJO.Mellit.mellitInduction_iff_braidClosedForm`, so the clause the
shuffle side still owes at this witness is one statement about `HJO.Mellit.partialSweepWord` and
`HJO.Mellit.stageTotal`, with no braid representation, no `HJO.Braid.specialBraid` and no level in
either index set. So the braid half of the argument is a **sufficient route, not a necessary
one**: anything that proves the identity between path sums closes this clause.

**What this does not do is make it easier.** An equivalence carrying no hypothesis on `q` or `u` is
a change of vocabulary, not a reduction of content: a "reduction" of this kind can be equivalent to
its own conclusion. What keeps the braid route the right one is
that the cancellation is global over the base set — at `(a,b) = (2,3)`, `α = [1,1]`, `A = 1` no
proper nonempty subfamily of the per-path discrepancies has vanishing sum, so no partition,
involution, per-path scalar or reindexing localises it — and the braid representation is the device
that localises it anyway. -/
@[hjo "lem_sweep_append_totals"]
theorem mellitInduction_sweepWitness_iff_sum_split (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) :
    MellitInduction (sweepWitness q u a b) a b
      ↔ ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
        ∑ z ∈ aboveReturnPaths a b α.sum α,
            ∑ w ∈ aboveReturnPaths a b A [A],
              partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
          = ∑ z ∈ aboveReturnPaths a b α.sum α,
              ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
                stageTotal q u a b α.length A
                  (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L)) :=
  (mellitInduction_sweepWitness_iff_sweepAppend hab ha hb).trans
    (sweepAppend_iff_sum_split hab ha hb)

/-- **The `hind` binder of `HJO.Mellit.shuffle_of_lhs_and_induction`, from the path-sum identity.**
The identity is asked for only under the hypotheses the assembly itself carries — algebraic
independence of `q, u` over `ℤ` and `1 < a < b` — which is where the `q ≠ 0`, `q ≠ 1` and `u ≠ 0`
that the bare statement needs come from; the coprimality is passed through and `0 < a`, `0 < b` come
out of `1 < a < b`.

This is the exact second binder of `HJO.Mellit.shuffle_of_lhs_and_induction`, so a proof of the
path-sum identity at those parameters closes `hind` and leaves `hlhs` untouched. -/
theorem hind_of_forall_sum_split
    (h : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
      ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
        ∑ z ∈ aboveReturnPaths a b α.sum α,
            ∑ w ∈ aboveReturnPaths a b A [A],
              partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
          = ∑ z ∈ aboveReturnPaths a b α.sum α,
              ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
                stageTotal q u a b α.length A
                  (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L))) :
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
      MellitInduction (sweepWitness q u a b) a b :=
  fun q u hqu a b hab ha hb =>
    (mellitInduction_sweepWitness_iff_sum_split hab (by omega) (by omega)).2
      (h q u hqu a b hab ha hb)

end HJO.Mellit

end
