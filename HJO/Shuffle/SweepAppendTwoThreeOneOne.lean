/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepStageTwoThreeOne
public import HJO.Shuffle.SweepInductionInstanceTwoDecided
public import HJO.Shuffle.SweepAppendBandPerPath

/-! # The `append` clause of `SweepAppend` at `(2,3)`, `α = [1]`, `A = 1`

This is the **second in-range instance** of `HJO.Mellit.SweepAppend`'s `append` clause, and the
**first whose base index set is not a singleton**. The only other one inside the range of coprime
`1 < a < b` used downstream is `HJO.Mellit.sweepAppend_nil_two_three_one`, at `α = []`, where
`HJO.Mellit.aboveReturnPaths_zero_nil_eq_singleton` makes the base set a single path — so the
phenomenon that makes the general statement hard cannot be seen there.

Here the base set is the two-element `HJO.Mellit.aboveReturnPaths_two_three_one` and the left-hand
side is a sum over the **four** paths of `HJO.Mellit.aboveReturnPaths_two_three_two_one_one`. Both
sides are

`q y_1^2y_2^2((e_1 - uy_1)(e_1 - uy_2) + (q-1)e_2)`,

for every `q ∉ {0,1}` and every `u ≠ 0`: the left by
`HJO.Mellit.dsc_two_three_two_one_one`, the right by
`HJO.Mellit.stageTotal_two_three_one_one_base` on `HJO.Mellit.dsc_two_three_one`.

## Why this instance and not another

The per-path reading of the append identity — one identity for each base path, which
`HJO.Mellit.sweepAppend_of_forall_band`, `HJO.Mellit.sweepAppend_of_forall_band_uniform` and
`HJO.Mellit.sweepAppend_of_forall_path` all ask for — is refuted at exactly this instance: the two
per-path discrepancies are nonzero and exact negatives, so they cancel in the sum and in no proper
part of it. (That refutation is a computation, not a theorem of this library; see the module
docstring of `HJO/Shuffle/SweepAppendBandPerPath.lean`.) What is proved below is the **summed**
identity, which is what `HJO.Mellit.SweepAppend` asks for and what
`HJO.Mellit.sweepAppend_of_forall_sum_band` asks for, and it holds.

So this is the smallest place where the two readings say different things, and the summed one is
proved here.

## The clause-level reduction

`HJO.Mellit.sum_band_clause_iff_dsc` extracts, as an `iff` at one composition, what the proof of
`HJO.Mellit.sweepAppend_of_forall_sum_band` establishes inside itself: **the summed band identity at
`(α, A)` is the `HJO.Mellit.dsc` identity at `(α, A)`** — no quantifier over compositions on
either side. That turns the remaining hypothesis into something checkable one instance at a
time, by exactly the computation the two proved instances are, and it is why
`HJO.Mellit.sum_band_two_three_one_one` and `HJO.Mellit.sum_band_two_three_nil_one` are two lines
each.

Those two are the only instances of that hypothesis proved here inside coprime `1 < a < b`. They
do not prove it: it is quantified over every composition with positive parts and every `0 < A`, and
the cancellation it needs is global over the base set at every one of them.

## The band statement is a restatement of the target, not a reduction of it

`HJO.Mellit.sweepAppend_iff_forall_sum_band`: the hypothesis of
`HJO.Mellit.sweepAppend_of_forall_sum_band` is **equivalent** to its conclusion, with no hypothesis
on `q` or `u` spent on the equivalence. So that theorem is the forward half of a trivial `iff`, and
the summed band statement — the only surviving *form* of the band statement — buys nothing over the
raw `HJO.Mellit.dsc` recursion.

The reason is visible in the factorisation itself. The outer word is the same for every tail
(`HJO.Mellit.outerSweepWord_appendHeights`), which is exactly why it comes off both sides and leaves
the clause unchanged. Splitting at the threshold `ab A` does not decompose the index set, does not
change the operators, and does not move the cancellation.

Stated without the band vocabulary, then, the obligation is: prove
`D(α ++ [A]) = (-1)^{(a-1)A}(qu)^{1-A}G_{k+1,A}(D(α))` at every composition — and the only two
compositions where it is proved here are the two where `D` has been evaluated in closed form.

## Genericity

`q ≠ 0`, `u ≠ 0`, `q ≠ 1` on the two instances, inherited unchanged from
`HJO.Mellit.dsc_two_three_two_one_one`, `HJO.Mellit.dsc_two_three_one` and
`HJO.Mellit.stageTotal_two_three_one_one_base`, and each is the field's `0⁻¹ = 0` turning a letter
into the zero map rather than bookkeeping: `q ≠ 1` for `HJO.Sweep.corner`'s `(q-1)^{-1}` and
`HJO.Sweep.zop`'s `q^k/(1-q)`, `q ≠ 0` for the `q^{-a_P̂}` of `HJO.Mellit.sweepOperator` and for the
inverted braid letters, `u ≠ 0` for the `(qu)^{-1}` of `HJO.Sweep.slopeOperator`. All three lie
inside the binder of `HJO.Mellit.shuffle_of_lhs_and_induction`, which carries
`AlgebraicIndependent ℤ ![q, u]`.

`HJO.Mellit.sum_band_clause_iff_dsc` carries **none** of them: it is coprimality and positivity
only, the same as `HJO.Mellit.sweepAppend_iff_sum_split`.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking
functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep HJO.Sym HJO.Paths Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

variable {a b : ℕ}

/-- **The summed band identity at one composition is the `HJO.Mellit.dsc` identity at that
composition.** No quantifier over compositions on either side: this is the clause-level content of
`HJO.Mellit.sweepAppend_of_forall_sum_band`, whose proof establishes both halves internally and
exports neither.

Left to right and right to left are the same three rewritings. The band factorisation comes off each
base path — `HJO.Mellit.partialSweepWord_eq_bandSweepWord_mul` together with
`HJO.Mellit.outerSweepWord_appendHeights` when `0 < α.sum`, and
`HJO.Mellit.outerSweepWord_eq_one_of_le` with
`HJO.Mellit.bandSweepWord_eq_partialSweepWord_of_le` when `α.sum = 0`; the double sum is reindexed
by `HJO.Mellit.sum_aboveReturnPaths_append_singleton`; and
`HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` closes both sides, the right one through the
linearity of `HJO.Mellit.stage`.

**This is what makes the hypothesis checkable instance by instance.** The hypothesis of
`HJO.Mellit.sweepAppend_of_forall_sum_band` is quantified over every composition with positive parts
and every `0 < A`; this says each of its clauses is a single `HJO.Mellit.dsc` identity, of
exactly the shape the proved instances evaluate. It does not weaken the hypothesis and it proves
no instance of it.

Coprimality and positivity only — no hypothesis on `q` or `u`, in keeping with
`HJO.Mellit.sweepAppend_iff_sum_split`. -/
theorem sum_band_clause_iff_dsc (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {α : List ℕ} {A : ℕ} (hpos : ∀ x ∈ α, 0 < x) (hA : 0 < A) :
    (∑ z ∈ aboveReturnPaths a b α.sum α,
          ∑ w ∈ aboveReturnPaths a b A [A],
            bandSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) ((a : ℤ) * (b * A))
              (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L))
        = ∑ z ∈ aboveReturnPaths a b α.sum α,
            ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (bandSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A))
                  (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L))))
      ↔ dsc q u a b (α.sum + A) (sepLevel a (α.sum + A)) (compColouring a b (α ++ [A]))
          = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (dsc q u a b α.sum (sepLevel a α.sum) (compColouring a b α)) := by
  have hsum : (α ++ [A]).sum = α.sum + A := by
    simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
  have key : ∀ z ∈ aboveReturnPaths a b α.sum α,
      ∑ w ∈ aboveReturnPaths a b A [A],
          partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
        = ∑ w ∈ aboveReturnPaths a b A [A],
            bandSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) ((a : ℤ) * (b * A))
              (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L)) := by
    intro z hz
    rcases Nat.eq_zero_or_pos α.sum with h0 | h0
    · have hbase : (a : ℤ) * (b * α.sum) ≤ (a : ℤ) * (b * A) := by
        rw [h0]
        push_cast
        positivity
      have hext : (a : ℤ) * (b * (α.sum + A)) ≤ (a : ℤ) * (b * A) :=
        le_of_eq (by rw [h0]; push_cast; ring)
      rw [outerSweepWord_eq_one_of_le q u z _ hbase]
      simp only [Module.End.one_apply]
      exact Finset.sum_congr rfl fun w _ => by
        rw [bandSweepWord_eq_partialSweepWord_of_le q u (appendHeights z w)
          (sepLevel a (α.sum + A)) hext]
    · have hzd : IsAboveDiagonal z := (mem_aboveReturnPaths_iff.1 hz).1
      have hη : SeparatesDiagonal a b (α.sum + A) (sepLevel a (α.sum + A)) :=
        separatesDiagonal_sepLevel' a b (α.sum + A)
      have hη' : SeparatesDiagonal a b α.sum (sepLevel a α.sum) :=
        separatesDiagonal_sepLevel' a b α.sum
      refine Finset.sum_congr rfl fun w hw => ?_
      have hwd : IsAboveDiagonal w := (mem_aboveReturnPaths_iff.1 hw).1
      rw [partialSweepWord_eq_bandSweepWord_mul ha (show 0 < α.sum + A by omega) _ _
          ((a : ℤ) * (b * A)), Module.End.mul_apply,
        outerSweepWord_appendHeights ha hzd hwd h0 hη hη']
  have keyb : ∀ z ∈ aboveReturnPaths a b α.sum α,
      ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
            stageTotal q u a b α.length A
              (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L))
        = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
            stageTotal q u a b α.length A
              (bandSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A))
                (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L))) := by
    intro z _
    rcases Nat.eq_zero_or_pos α.sum with h0 | h0
    · have hbase : (a : ℤ) * (b * α.sum) ≤ (a : ℤ) * (b * A) := by
        rw [h0]
        push_cast
        positivity
      rw [outerSweepWord_eq_one_of_le q u z _ hbase]
      simp only [Module.End.one_apply]
      rw [bandSweepWord_eq_partialSweepWord_of_le q u z _ hbase]
    · rw [partialSweepWord_eq_bandSweepWord_mul ha h0 z (sepLevel a α.sum) ((a : ℤ) * (b * A)),
        Module.End.mul_apply]
  rw [← Finset.sum_congr rfl key, ← Finset.sum_congr rfl keyb,
    ← sum_aboveReturnPaths_append_singleton (a := a) (b := b) (N := α.sum) (A := A) (α := α)
      (f := fun y => partialSweepWord q u y (sepLevel a (α.sum + A)) (1 : Total L)),
    ← dsc_compColouring_eq_sum_partialSweepWord q u (isAdmissibleLevel_sepLevel a (α.sum + A))
      (separatesDiagonal_sepLevel' a b (α.sum + A)) hab ha hb
      (forall_pos_append_singleton hpos hA) hsum,
    ← Finset.smul_sum, ← map_sum,
    ← dsc_compColouring_eq_sum_partialSweepWord q u (isAdmissibleLevel_sepLevel a α.sum)
      (separatesDiagonal_sepLevel' a b α.sum) hab ha hb hpos rfl]

/-- **`HJO.Mellit.SweepAppend` is EQUIVALENT to the hypothesis of
`HJO.Mellit.sweepAppend_of_forall_sum_band`, not merely implied by it.**

`HJO.Mellit.sum_band_clause_iff_dsc` at every composition, and `HJO.Mellit.SweepAppend` is by
definition the conjunction of the `HJO.Mellit.dsc` clauses. So that theorem's hypothesis is a
**restatement of its conclusion**: `HJO.Mellit.sweepAppend_of_forall_sum_band` is the forward half
of this `iff`, and it reduces nothing.

**This is worth being blunt about, because the summed band statement has been the recorded live
route.** It is the only surviving *form* of the band statement — the per-path forms
`HJO.Mellit.sweepAppend_of_forall_band`, `HJO.Mellit.sweepAppend_of_forall_band_uniform` and
`HJO.Mellit.sweepAppend_of_forall_path` ask for a strictly stronger hypothesis, and that one is
refuted — but being the only surviving form is not the same as being progress. The band
factorisation splits each partial sweep word at the threshold `ab A` into an inner band word and an
outer word (`HJO.Mellit.partialSweepWord_eq_bandSweepWord_mul`); the outer word is the *same* on the
whole inner sum (`HJO.Mellit.outerSweepWord_appendHeights`), which is exactly why it cancels out of
the clause and leaves the clause unchanged. It does not decompose the index set, it does not change
the operators, and it does not move the cancellation anywhere.

What that leaves, stated without the band vocabulary: the obligation is the `HJO.Mellit.dsc`
recursion `D(α ++ [A]) = (-1)^{(a-1)A}(qu)^{1-A}G_{k+1,A}(D(α))` at every composition, and the two
compositions at which it is proved here (`HJO.Mellit.sum_band_two_three_nil_one`,
`HJO.Mellit.sum_band_two_three_one_one`) are the two at which `D` has been evaluated in closed form.
Neither avoids evaluating `D`.

Coprimality and positivity only; no hypothesis on `q` or `u`, so this `iff` transports the known
refutations at `q = 1`, `q = 0` and `u = 0` in both directions exactly as
`HJO.Mellit.sweepAppend_iff_sum_split` does. -/
theorem sweepAppend_iff_forall_sum_band (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    SweepAppend q u a b ↔ ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
      ∑ z ∈ aboveReturnPaths a b α.sum α,
          ∑ w ∈ aboveReturnPaths a b A [A],
            bandSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) ((a : ℤ) * (b * A))
              (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L))
        = ∑ z ∈ aboveReturnPaths a b α.sum α,
            ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (bandSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A))
                  (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A))
                    (1 : Total L))) :=
  ⟨fun h α A hpos hA => (sum_band_clause_iff_dsc hab ha hb hpos hA).2 (h α A hpos hA),
    fun h α A hpos hA => (sum_band_clause_iff_dsc hab ha hb hpos hA).1 (h α A hpos hA)⟩

/-- **The `append` clause of `HJO.Mellit.SweepAppend` at `(a,b) = (2,3)`, `α = [1]`, `A = 1`, and it
is TRUE for every `q ∉ {0,1}` and every `u ≠ 0`.**

Both sides are `q y_1^2y_2^2((e_1 - uy_1)(e_1 - uy_2) + (q-1)e_2)`: the left by
`HJO.Mellit.dsc_two_three_two_one_one`, a sum over the **four** paths of the `4 × 6` rectangle
coloured `c_{(1,1)}` at the level `9/2`, and the right by
`HJO.Mellit.stageTotal_two_three_one_one_base` applied to `HJO.Mellit.dsc_two_three_one`.

**This is the second instance of the clause inside coprime `1 < a < b`, and the first with a base
index set that is not a singleton.** `HJO.Mellit.sweepAppend_nil_two_three_one` is the other one, at
`α = []`; there the base set is one path, the per-path and summed readings coincide, and the
identity says nothing about the cancellation. Here the base set is
`HJO.Mellit.aboveReturnPaths_two_three_one`, with two elements, and the four terms of the left-hand
side do not split into two independently correct halves — two of them cancel against each other on
`e_1y_1^3y_2^2` (see `HJO.Mellit.dsc_two_three_two_one_one`), so no single base path carries its own
share of the answer.

`q ≠ 0`, `u ≠ 0` and `q ≠ 1` are all three necessary and all three inherited; see the module
docstring. -/
theorem sweepAppend_two_three_one_one (q u : L) (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    dsc q u 2 3 (([1] : List ℕ).sum + 1) (sepLevel 2 (([1] : List ℕ).sum + 1))
        (compColouring 2 3 ([1] ++ [1]))
      = ((-1 : L) ^ ((2 - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) •
          stageTotal q u 2 3 ([1] : List ℕ).length 1
            (dsc q u 2 3 ([1] : List ℕ).sum (sepLevel 2 ([1] : List ℕ).sum)
              (compColouring 2 3 ([1] : List ℕ))) := by
  have hsum : ([1] : List ℕ).sum = 1 := by simp
  have hlen : ([1] : List ℕ).length = 1 := by simp
  have happ : ([1] : List ℕ) ++ [1] = [1, 1] := by simp
  have hsc : ((-1 : L) ^ ((2 - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) = -1 := by norm_num
  rw [hsum, hlen, happ, hsc, show (1 : ℕ) + 1 = 2 from rfl,
    dsc_two_three_one q u hq0 hq1, show (MvPolynomial.X 0 : Total L) = auxVar 1 from rfl,
    stageTotal_two_three_one_one_base hq0 hu0 hq1, dsc_two_three_two_one_one hq0 hq1]
  simp only [← scal_mul_eq_smul_total]
  simp only [scal, map_mul, map_sub, map_neg, map_one, map_pow]
  ring


/-- **The hypothesis of `HJO.Mellit.sweepAppend_of_forall_sum_band` holds at `α = [1]`, `A = 1`,
`(a,b) = (2,3)`** — its first in-range instance with a non-singleton base index set, and therefore
the first that says anything the per-path readings do not.

`HJO.Mellit.sum_band_clause_iff_dsc` on `HJO.Mellit.sweepAppend_two_three_one_one`. One instance of
a hypothesis quantified over every composition; it is evidence, not a proof. -/
theorem sum_band_two_three_one_one (q u : L) (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    ∑ z ∈ aboveReturnPaths 2 3 (([1] : List ℕ).sum) ([1] : List ℕ),
          ∑ w ∈ aboveReturnPaths 2 3 1 [1],
            bandSweepWord q u (appendHeights z w) (sepLevel 2 (([1] : List ℕ).sum + 1))
                (((2 : ℕ) : ℤ) * (((3 : ℕ) : ℤ) * ((1 : ℕ) : ℤ)))
              (outerSweepWord q u z (sepLevel 2 ([1] : List ℕ).sum)
                (((2 : ℕ) : ℤ) * (((3 : ℕ) : ℤ) * ((1 : ℕ) : ℤ))) (1 : Total L))
        = ∑ z ∈ aboveReturnPaths 2 3 (([1] : List ℕ).sum) ([1] : List ℕ),
            ((-1 : L) ^ ((2 - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) •
              stageTotal q u 2 3 ([1] : List ℕ).length 1
                (bandSweepWord q u z (sepLevel 2 ([1] : List ℕ).sum)
                    (((2 : ℕ) : ℤ) * (((3 : ℕ) : ℤ) * ((1 : ℕ) : ℤ)))
                  (outerSweepWord q u z (sepLevel 2 ([1] : List ℕ).sum)
                    (((2 : ℕ) : ℤ) * (((3 : ℕ) : ℤ) * ((1 : ℕ) : ℤ))) (1 : Total L))) :=
  (sum_band_clause_iff_dsc (q := q) (u := u) (a := 2) (b := 3) (α := [1]) (A := 1)
      (by decide) (by omega) (by omega) (by simp) one_pos).2
    (sweepAppend_two_three_one_one q u hq0 hu0 hq1)

/-- **The hypothesis of `HJO.Mellit.sweepAppend_of_forall_sum_band` holds at `α = []`, `A = 1`,
`(a,b) = (2,3)`.** `HJO.Mellit.sum_band_clause_iff_dsc` on
`HJO.Mellit.sweepAppend_nil_two_three_one`.

Together with `HJO.Mellit.sum_band_two_three_one_one` these are the only instances of
that hypothesis proved inside coprime `1 < a < b`: two compositions at one `(a,b)`. -/
theorem sum_band_two_three_nil_one (q u : L) (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    ∑ z ∈ aboveReturnPaths 2 3 (([] : List ℕ).sum) ([] : List ℕ),
          ∑ w ∈ aboveReturnPaths 2 3 1 [1],
            bandSweepWord q u (appendHeights z w) (sepLevel 2 (([] : List ℕ).sum + 1))
                (((2 : ℕ) : ℤ) * (((3 : ℕ) : ℤ) * ((1 : ℕ) : ℤ)))
              (outerSweepWord q u z (sepLevel 2 ([] : List ℕ).sum)
                (((2 : ℕ) : ℤ) * (((3 : ℕ) : ℤ) * ((1 : ℕ) : ℤ))) (1 : Total L))
        = ∑ z ∈ aboveReturnPaths 2 3 (([] : List ℕ).sum) ([] : List ℕ),
            ((-1 : L) ^ ((2 - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) •
              stageTotal q u 2 3 ([] : List ℕ).length 1
                (bandSweepWord q u z (sepLevel 2 ([] : List ℕ).sum)
                    (((2 : ℕ) : ℤ) * (((3 : ℕ) : ℤ) * ((1 : ℕ) : ℤ)))
                  (outerSweepWord q u z (sepLevel 2 ([] : List ℕ).sum)
                    (((2 : ℕ) : ℤ) * (((3 : ℕ) : ℤ) * ((1 : ℕ) : ℤ))) (1 : Total L))) :=
  (sum_band_clause_iff_dsc (q := q) (u := u) (a := 2) (b := 3) (α := []) (A := 1)
      (by decide) (by omega) (by omega) (by simp) one_pos).2
    (sweepAppend_nil_two_three_one q u hq0 hu0 hq1)

end HJO.Mellit

end
