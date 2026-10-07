/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendNilBand

/-! # The band clause is the PER-PATH append identity, and that is the reading that is false

`HJO.Mellit.sweepAppend_of_forall_band` and `HJO.Mellit.sweepAppend_of_forall_band_uniform` ask for
one identity **per base path** `z`. `HJO.Mellit.SweepAppend` itself asks only for the identity
**summed over the base paths** — that is not an approximation of it, it is
`HJO.Mellit.sweepAppend_iff_sum_split`, an `iff`. The per-path reading is therefore strictly
stronger, and the gap between the two is not slack: it is where the hypothesis fails.

## What this file proves

`HJO.Mellit.band_iff_perPath` — at `0 < α.sum`, the band clause at one base path is **equivalent**
to the raw per-path identity

`∑_w W_{η}(z·w)(1) = (-1)^{(a-1)A}(qu)^{1-A} G_{ℓ+1,A}(W_{η'}(z)(1))`,

in `HJO.Mellit.partialSweepWord` alone. Both directions, from
`HJO.Mellit.outerSweepWord_appendHeights` and
`HJO.Mellit.partialSweepWord_eq_bandSweepWord_mul`. So the band factorisation adds nothing to the
per-path statement and subtracts nothing from it: the two hypotheses of
`HJO.Mellit.sweepAppend_of_forall_band` are, at every `α` with `0 < α.sum`, its `hzero` clause read
at a longer composition. To refute the band route it suffices to refute the *simpler* sentence.

## Why that matters: the per-path reading is FALSE, by computation

At `(a,b) = (2,3)`, `α = [1]`, `A = 1` — the smallest instance beyond
`HJO.Mellit.sweepAppend_nil_two_three_one`, and the first with **more than one base path** — the
per-path identity fails at *each* of the two base paths of
`HJO.Mellit.aboveReturnPaths 2 3 1 [1]`, namely `HJO.Paths.baseTwoThreeA = (0,2,3)` and
`HJO.Paths.baseTwoThreeB = (0,3,3)`. The discrepancy at `(0,2,3)` is

`-(q-1)uy_1^2y_2^2/2 ·`
`  (p_2 - p_1^2 - 2(q-1)p_1uy_1 + 2p_1uy_2 + 2(q-1)u^2y_1(y_1+y_2) - 2u^2y_2^2)`

and at `(0,3,3)` it is exactly the negative of that. The two cancel, so the **sum** over the base
paths holds: `HJO.Mellit.SweepAppend` is TRUE at this instance. It is the *split* that is wrong.

The `(q-1)` and the `u` are explicit, so the failure is not a degeneracy: the coefficient of `p_2`
alone is `∓(q-1)uy_1^2y_2^2/2`, nonzero for every `q ≠ 1` and `u ≠ 0`, hence nonzero under the
algebraic independence of `HJO.Mellit.shuffle_of_lhs_and_induction`'s binder. The exclusions
`q ∉ {0,1}` and `u ≠ 0` do not rescue it.

This computation is **model-only** — a transcription of `HJO.Paths.sweptRegion`,
`HJO.Paths.eventType`, `HJO.Paths.sweepWidth`, `HJO.Paths.sweepRight`,
`HJO.ParkingFunctions.abovePointRank`, `HJO.Mellit.sweepOperator`,
`HJO.Mellit.partialSweepWord` and the whole of `HJO.Mellit.stageTotal` into a computer model,
validated by reproducing `HJO.Mellit.sweepAppend_nil_two_three_one`,
`HJO.Mellit.sweepAppend_nil_one_two_two`, `HJO.Mellit.dsc_one_two_two`,
`HJO.Mellit.partialSweepWord_tailEx1_apply_one`,
`HJO.Mellit.partialSweepWord_tailEx2_apply_one`, `HJO.Sweep.replOneTotal_two_three` and the
`decide`-checked ranks, event types, widths and `sweepRight`s of
`HJO/Shuffle/SweepAppendNilTwo.lean`, all exactly. It is not a Lean proof and nothing here
depends on it.

## Where that leaves the route

`HJO.Mellit.hzero_of_band_nil` and `HJO.Mellit.sweepAppend_of_forall_band_uniform` are correct
theorems with a false hypothesis, so they are vacuous. They are not *wrong* about `α = []`: there
the base index set is a singleton (`HJO.Mellit.aboveReturnPaths_zero_nil_eq_singleton`), so the
per-path and summed readings coincide, which is exactly why the two proved instances — both at
`α = []` — do not see the defect.

What survives is `HJO.Mellit.sweepAppend_iff_sum_split`: the target is the summed identity, and the
correct band statement carries `∑_z` outside. That is what
`HJO.Mellit.sweepAppend_of_forall_sum_band` below asks for, and it is the hypothesis a proof should
aim at.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep HJO.Sym HJO.Paths Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-! ### The band clause at a base path is the raw per-path identity -/

/-- **At a base path in a nonempty rectangle, the band clause of
`HJO.Mellit.sweepAppend_of_forall_band` and the raw per-path identity are the same sentence.**

The outer word comes off both sides: on the left because it does not depend on the tail
(`HJO.Mellit.outerSweepWord_appendHeights`), on the right because the base's own partial word
factors at the same threshold (`HJO.Mellit.partialSweepWord_eq_bandSweepWord_mul`). Neither
direction spends anything on `q` or `u`, and neither needs coprimality.

So the band factorisation is a *rewriting* of the per-path hypothesis, not a weakening of it: the
sentence to refute, or to prove, may be taken in `HJO.Mellit.partialSweepWord` alone. -/
theorem band_iff_perPath (ha : 0 < a) {α : List ℕ} {A : ℕ} (hs : 0 < α.sum)
    {z : Heights a b α.sum} (hz : z ∈ aboveReturnPaths a b α.sum α) :
    (∑ w ∈ aboveReturnPaths a b A [A],
          bandSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) ((a : ℤ) * (b * A))
            (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L))
        = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
            stageTotal q u a b α.length A
              (bandSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A))
                (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L))))
      ↔ (∑ w ∈ aboveReturnPaths a b A [A],
            partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
          = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L))) := by
  have hzd : IsAboveDiagonal z := (mem_aboveReturnPaths_iff.1 hz).1
  have hη : SeparatesDiagonal a b (α.sum + A) (sepLevel a (α.sum + A)) :=
    separatesDiagonal_sepLevel' a b (α.sum + A)
  have hη' : SeparatesDiagonal a b α.sum (sepLevel a α.sum) :=
    separatesDiagonal_sepLevel' a b α.sum
  have hlhs : ∀ w ∈ aboveReturnPaths a b A [A],
      partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
        = bandSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) ((a : ℤ) * (b * A))
            (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L)) := by
    intro w hw
    have hwd : IsAboveDiagonal w := (mem_aboveReturnPaths_iff.1 hw).1
    rw [partialSweepWord_eq_bandSweepWord_mul ha (show 0 < α.sum + A by omega) _ _
        ((a : ℤ) * (b * A)), Module.End.mul_apply,
      outerSweepWord_appendHeights ha hzd hwd hs hη hη']
  rw [Finset.sum_congr rfl hlhs,
    partialSweepWord_eq_bandSweepWord_mul ha hs z (sepLevel a α.sum) ((a : ℤ) * (b * A)),
    Module.End.mul_apply]

/-! ### The band clause at `α.sum = 0` is the raw per-path identity too

`HJO.Mellit.hzero_of_band_nil` says this one way round; the equivalence is what lets the summed
band hypothesis below be stated uniformly in `α`, with no `0 < α.sum` and no separate clause. -/

/-- **At `α.sum = 0` the band clause at a base path is again the raw per-path identity.** Both
directions of `HJO.Mellit.hzero_of_band_nil`'s computation, one base path at a time: the outer word
of the base is the identity and both band words are whole partial words, by
`HJO.Mellit.outerSweepWord_eq_one_of_le` and
`HJO.Mellit.bandSweepWord_eq_partialSweepWord_of_le` at `M = 0` and at `M = 0 + A`. -/
theorem band_iff_perPath_of_sum_eq_zero {α : List ℕ} {A : ℕ} (hs : α.sum = 0)
    (z : Heights a b α.sum) :
    (∑ w ∈ aboveReturnPaths a b A [A],
          bandSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) ((a : ℤ) * (b * A))
            (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L))
        = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
            stageTotal q u a b α.length A
              (bandSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A))
                (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L))))
      ↔ (∑ w ∈ aboveReturnPaths a b A [A],
            partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
          = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L))) := by
  have hbase : (a : ℤ) * (b * α.sum) ≤ (a : ℤ) * (b * A) := by
    rw [hs]
    push_cast
    positivity
  have hext : (a : ℤ) * (b * (α.sum + A)) ≤ (a : ℤ) * (b * A) :=
    le_of_eq (by rw [hs]; push_cast; ring)
  have houter : outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) = 1 :=
    outerSweepWord_eq_one_of_le q u z _ hbase
  have hbz : bandSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A))
      = partialSweepWord q u z (sepLevel a α.sum) :=
    bandSweepWord_eq_partialSweepWord_of_le q u z _ hbase
  have hsum : ∀ w ∈ aboveReturnPaths a b A [A],
      bandSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) ((a : ℤ) * (b * A))
          (1 : Total L)
        = partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L) :=
    fun w _ => by
      rw [bandSweepWord_eq_partialSweepWord_of_le q u (appendHeights z w)
        (sepLevel a (α.sum + A)) hext]
  rw [houter]
  simp only [Module.End.one_apply]
  rw [hbz, Finset.sum_congr rfl hsum]

/-! ### The repair: the summed band hypothesis -/

/-- **`HJO.Mellit.SweepAppend` from the band identity summed over the base paths.** The statement
`HJO.Mellit.sweepAppend_of_forall_band_uniform` should have made: one band identity per composition,
with `∑_z` **outside**, quantified over every composition with positive parts, `α = []` included.

This is `HJO.Mellit.sweepAppend_iff_sum_split` read through
`HJO.Mellit.band_iff_perPath` and `HJO.Mellit.band_iff_perPath_of_sum_eq_zero`, so it carries
exactly the coprimality and positivity that `iff` does and nothing on `q` or `u`.

The per-path hypothesis it replaces is not merely stronger than needed: at `(a,b) = (2,3)`,
`α = [1]`, `A = 1` it is false at both base paths while their sum is fine — see the module
docstring. So this is the form of the band statement that is still open, and the per-path form is
closed. -/
theorem sweepAppend_of_forall_sum_band (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hband : ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
      ∑ z ∈ aboveReturnPaths a b α.sum α,
          ∑ w ∈ aboveReturnPaths a b A [A],
            bandSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) ((a : ℤ) * (b * A))
              (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L))
        = ∑ z ∈ aboveReturnPaths a b α.sum α,
            ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (bandSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A))
                  (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L)))) :
    SweepAppend q u a b := by
  refine (sweepAppend_iff_sum_split hab ha hb).2 fun α A hpos hA => ?_
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
  rw [Finset.sum_congr rfl key, Finset.sum_congr rfl keyb]
  exact hband α A hpos hA

end HJO.Mellit

end
