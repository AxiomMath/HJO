/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendBandPerPath

/-! # The append identity is a fact about the vacuum, not an identity of operators

`HJO.Mellit.sweepAppend_iff_sum` and `HJO.Mellit.sweepAppend_iff_sum_split` state
`HJO.Mellit.SweepAppend` as an equality between two elements of `HJO.Sweep.Total L`, each obtained
by applying an operator to the vacuum `1`. Both sides are built from *linear* maps, so each is the
value at `1` of an endomorphism of `HJO.Sweep.Total L`, and the identity has an evident
strengthening: that those two **endomorphisms** are equal, i.e. that the identity holds with `1`
replaced by an arbitrary `F`. That strengthening is what a proof by operator algebra would deliver —
a chain of identities in `Module.End L (HJO.Sweep.Total L)` rewriting one side into the other proves
the identity at every input at once, never at `1` alone.

**This file shows that strengthening is FALSE.**

## What is proved here

`HJO.Mellit.not_forall_sum_partialSweepWord_eq_sum_stageTotal_one_two` — at `(a,b) = (1,2)`,
`α = []`, `A = 1`, for every `q ≠ 1` and every `u ≠ 1`, the clause of
`HJO.Mellit.sweepAppend_iff_sum` does **not** hold for all `F`. The witness is `F = Ce_1`, and the
discrepancy is `(q-1)(1-u)y_1^3`.

`HJO.Mellit.sum_partialSweepWord_eq_sum_stageTotal_one_two_apply_one` — the same clause, at the
same parameters, at `F = 1`: it holds, for every `q ≠ 1`. This is
`HJO.Mellit.sweepAppend_nil_one_one_two` in path-sum form, and it is here so that the refutation
above cannot be mistaken for a mis-stated instance, a sign error or a level error. The difference of
the two operators is nonzero and annihilates the vacuum.

## The mechanism, and it is parameter-free

The two sides read their input through two operators that differ by one substitution:

* `HJO.Mellit.partialSweepWord_baseEx_of_mem_piece_zero` — on `V_0` the whole sweep side is
  `F ↦ y_1^2τ_{1,1}(F)`. The word is `Δ^{(1)}d_+^{(0)}` (`HJO.Mellit.partialSweepWord_baseEx`),
  `d_+^{(0)}` is `-y_1τ_{1,1}` with an empty train, and `HJO.Sweep.corner_one_auxVar_mul` turns the
  corner at width `1` into a second factor of `-y_1`.
* `HJO.Mellit.stageTotal_one_two_apply` — the whole stage side is
  `F ↦ y_1^2cy_1(τ_{1,1}(F))`, unconditionally. Every factor of `HJO.Mellit.stageTotal` reads `F`
  only through `HJO.Sweep.dplusStar`, and `HJO.Sweep.dplusStar_apply` *is*
  `cy_1 ∘ τ_{1,1}`.

**That second bullet is general**, and `HJO.Mellit.stageTotal_zero_apply_congr` proves it at every
`a`, `b` and `A`: at the base grading the stage cannot distinguish two arguments with the same
`d^*_+{}^{(0)}`, because `HJO.Mellit.replOneTotal` applies `d^*_+` first and every other factor —
both trains, the power of `Z^{(1)}_{a,b}`, the slope operator — stands to its left. So the
right-hand side of the `α = []` clause depends on `F` only through `cy_1(τ_{1,1}(F))` in every
rectangle, while the sweep side applies `τ_{1,1}` with no `cy_1`, its top event being a type-`A`
event of width `0`. Only the sweep half of the bullet list is instance-bound here.

So the clause says exactly that `cy_1` of `HJO.Sweep.cycleShift` — the substitution `y_1 ↦ uy_1` —
acts trivially on `τ_{1,1}(F)`, which is
`HJO.Mellit.sum_partialSweepWord_eq_sum_stageTotal_one_two_iff`. And `τ_{1,1}(F)` is free of `y_1`
exactly when `F` is: `τ_{1,1}` of `HJO.Sweep.qshift` adds `(q-1)y_1^r` to each `p_r`. **The vacuum
is the unique place where a `q`-shift is invisible, and that is the whole reason the identity holds
there.** The discrepancy is divisible by `(q-1)` because `τ_{1,1}` is trivial at `q = 1`, and by
`(u-1)` because `cy_1` is trivial at `u = 1`; neither is excluded by
`HJO.Mellit.shuffle_of_lhs_and_induction`'s `AlgebraicIndependent ℤ ![q, u]`, so this is not a
degeneracy of the excluded parameters and not the `0⁻¹ = 0` hazard.

## What this closes

A proof of the `hind` binder cannot be an operator computation. In particular the analysis recorded
at `HJO.Mellit.sweepAppend_of_forall_path` — that by `HJO.Paths.northSteps_appendHeights` the two
sweeps do not share their event operators, so the `HJO.Braid.trainDown`, `HJO.Braid.trainUp` and
`HJO.Mellit.replicatedLetter` factors of `HJO.Mellit.stageTotal` are what has to absorb the
difference — describes a difference that **no** operator identity absorbs: there is nothing to
absorb it *into*, the two endomorphisms simply differ. Whatever closes `hind` must at some point use
a property of the vector `1` itself, in the manner of `HJO.Sweep.corner_stairWord_consume`, whose
hypothesis is on the vector and not on the word.

## What is proved in Lean, and what is not

The Lean refutation above is at `a = 1`, which `HJO.Mellit.shuffle_of_lhs_and_induction`'s `hind`
excludes (it demands `1 < a`). What is Lean-proved is therefore that the operator reading of
`HJO.Mellit.SweepAppend` is false at `(a,b) = (1,2)`, not that it is false in the target range. The
target-range failures are **model-only**, in a computer-algebra transcription validated
against `HJO.Mellit.sweepAppend_nil_two_three_one` and `HJO.Mellit.sweepAppend_nil_one_two_two` and
the `decide`-checked ranks, event types, widths and `sweepRight`s of
`HJO/Shuffle/SweepAppendNilTwo.lean`. Nine instances over seven parameter pairs — `(2,3)` with
`α = []`, `A ∈ {1,2}` and with `α = [1]`, `A = 1`; `(3,4)`, `(2,5)`, `(3,5)` with `α = []`, `A = 1`;
`(1,2)` with `α = []`, `A ∈ {1,2}` and with `α = [1]`, `A = 1` — and **every one holds at `F = 1`
and fails at `F = Cp_1`, with `(q-1)(u-1)` dividing the discrepancy**, the mechanism above and
not an accident of the instance. That includes `A = 2`, where the power of `Z^{(1)}_{a,b}` of
`HJO.Mellit.replicatedLetter` is not empty and the tail index set has `19` paths: the replicated
letter does not absorb it either. At `(a,b) = (2,3)`, `α = []`, `A = 1` — the instance
`HJO.Mellit.sweepAppend_nil_two_three_one` proves — the discrepancy at `F = Cp_1` is
`(q-1)(u-1)y_1^2(e_2 - (u+1)p_1y_1 + u(u+1)y_1^2)`. Nothing in this file depends on any of that.

## References

This file concerns `HJO.Mellit.braidRep_specialBraid_dplusIter`,
`HJO.Mellit.mellitInduction_sweepWitness`, `HJO.Mellit.sweepOperator`, `HJO.Sweep.corner`,
`HJO.Sweep.qshift`, `HJO.Sweep.cycleShift`, `HJO.Mellit.stage`. Transcribing A. Mellit, *Toric
braids and `(m, n)`-parking functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The sweep side of the `1 × 2` rectangle, on `V_0` -/

/-- **`Δ^{(1)}d_+^{(0)}(F) = y_1^2τ_{1,1}(F)` for `F ∈ V_0`**, at every `q ≠ 1`. The word of the
`1 × 2` rectangle written as a substitution: `d_+^{(0)}` of `HJO.Sweep.cmDPlus` is `-y_1τ_{1,1}`
with an empty ascending train (`HJO.Mellit.trainUpEnd_one_one`), its value lies in `y_1V_1` because
`HJO.Sweep.qshift_mem_piece` puts `τ_{1,1}(F)` in `V_1`, and there
`HJO.Sweep.corner_one_auxVar_mul` makes the corner of `HJO.Sweep.corner` a second factor of `-y_1`.

This is the identity the stage is to be compared with, and the comparison is then between
`τ_{1,1}` and `HJO.Sweep.dplusStar`. -/
theorem corner_one_dplus_zero_of_mem_piece_zero (hq1 : q ≠ 1) {F : Total L}
    (hF : F ∈ piece L 0) :
    corner q 1 (dplus q 0 F) = (MvPolynomial.X 0 : Total L) ^ 2 * qshift q 1 F := by
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hmem : qshift q 1 F ∈ piece L 1 :=
    qshift_mem_piece q (i := 1) (k := 0) (m := 1) (by omega) (by omega) hF
  rw [dplus_apply, Nat.zero_add, Mellit.trainUpEnd_one_one, Module.End.one_apply,
    map_neg, corner_one_auxVar_mul hq1 hmem, hav]
  ring

omit [Algebra ℚ L] in
/-- **`d^*_+{}^{(0)} = cy_1 ∘ τ_{1,1}`**, `HJO.Sweep.dplusStar_apply` at `k = 0` with the index
arithmetic done. The starred raising operator of `HJO.Sweep.dplusStar` is the same `q`-shift the
sweep side applies, followed by the substitution `y_1 ↦ uy_1` of `HJO.Sweep.cycleShift`. -/
theorem dplusStar_zero_eq (q u : L) (F : Total L) :
    dplusStar q u 0 F = cycleShift u 0 (qshift q 1 F) := by
  rw [dplusStar_apply, Nat.zero_add]

/-! ### The two substitutions at `e_1`, where they part -/

/-- **`τ_{1,1}(Ce_1) = Ce_1 + (q-1)y_1`**, `HJO.Sweep.qshift_one_C_powerSum_one` at `e_1 = p_1`. -/
theorem qshift_one_C_elemSymm_one (q : L) :
    qshift q 1 (MvPolynomial.C (elemSymm L 1) : Total L)
      = MvPolynomial.C (elemSymm L 1) + scal (q - 1) * (MvPolynomial.X 0 : Total L) := by
  rw [Sym.elemSymm_one_eq_powerSum]
  exact qshift_one_C_powerSum_one q

/-- **`cy_1(Ce_1 + (q-1)y_1) = Ce_1 + (q-1)uy_1`.** The substitution of `HJO.Sweep.cycleShift` fixes
the coefficients from `Λ` and multiplies the one `y_1` by `u`, so it moves `τ_{1,1}(Ce_1)` and would
not have moved `Ce_1`. -/
theorem cycleShift_zero_C_elemSymm_one_add (q u : L) :
    cycleShift u 0 (MvPolynomial.C (elemSymm L 1) + scal (q - 1) * (MvPolynomial.X 0 : Total L))
      = MvPolynomial.C (elemSymm L 1) + scal ((q - 1) * u) * (MvPolynomial.X 0 : Total L) := by
  rw [map_add, map_mul, cycleShift_C, cycleShift_scal, cycleShift_zero_X_zero, ← mul_assoc,
    ← scal_mul]

/-- `e_1 ∈ V_0`: a scalar of the base `Λ`. -/
theorem C_elemSymm_one_mem_piece_zero :
    (MvPolynomial.C (elemSymm L 1) : Total L) ∈ piece L 0 := by
  have h : (MvPolynomial.C (elemSymm L 1) : Total L)
      = algebraMap (Sym.Lambda L) (Total L) (elemSymm L 1) := rfl
  rw [h]
  exact (piece L 0).algebraMap_mem _

end HJO.Sweep

namespace HJO.Mellit

open HJO.Sweep HJO.Sym HJO.Paths Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The two sides of the `α = []`, `A = 1`, `(a,b) = (1,2)` clause, as operators -/

/-- The word of `HJO.Paths.baseEx` applied to an argument, `HJO.Mellit.partialSweepWord_baseEx`
read pointwise. -/
theorem partialSweepWord_baseEx_apply (q u : L) (F : Total L) :
    partialSweepWord q u baseEx (sepLevel 1 1) F = corner q 1 (dplus q 0 F) := by
  rw [partialSweepWord_baseEx, Module.End.mul_apply]

/-- **The sweep side of the clause is `F ↦ y_1^2τ_{1,1}(F)` on `V_0`.** -/
theorem partialSweepWord_baseEx_of_mem_piece_zero (hq1 : q ≠ 1) {F : Total L}
    (hF : F ∈ piece L 0) :
    partialSweepWord q u baseEx (sepLevel 1 1) F
      = (MvPolynomial.X 0 : Total L) ^ 2 * qshift q 1 F := by
  rw [partialSweepWord_baseEx_apply, corner_one_dplus_zero_of_mem_piece_zero hq1 hF]

/-- **`Ω(1;1,2)(F) = y_1^2d^*_+{}^{(0)}(F)`, for every `F`.** At `a = 1` the slope word of
`HJO.Braid.slopeBraid` has no letter `𝗓` (`HJO.Mellit.slopeOperator_one_two_apply`), so
`Ω(1;1,2)` is multiplication by `-y_1` composed with `-y_1d^*_+`, and no inverse of `q` or of `u`
occurs. Total in `F`: no hypothesis, and in particular no grading condition. -/
theorem replOneTotal_one_two_apply (q u : L) (F : Total L) :
    replOneTotal q u 1 2 0 F
      = (MvPolynomial.X 0 : Total L) ^ 2 * cycleShift u 0 (qshift q 1 F) := by
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  rw [replOneTotal]
  simp only [Nat.sub_self, pow_zero, one_smul, Module.End.mul_apply, LinearMap.neg_apply,
    LinearMap.mulLeft_apply, map_neg, Nat.zero_add]
  rw [slopeOperator_one_two_apply, dplusStar_zero_eq, hav]
  ring

/-- **The stage side of the clause is `F ↦ y_1^2cy_1(τ_{1,1}(F))`, for every `F`.** Both trains of
`HJO.Mellit.stage` are empty at the grading `0` (`HJO.Mellit.trainDownEnd_one_one`) and the power of
the replicated letter is empty at `A = 1`, so the stage is `Ω(1;1,2)` itself.

Compare `HJO.Mellit.partialSweepWord_baseEx_of_mem_piece_zero`: the two sides differ by exactly the
substitution `cy_1`. -/
theorem stageTotal_one_two_apply (q u : L) (F : Total L) :
    stageTotal q u 1 2 0 1 F
      = (MvPolynomial.X 0 : Total L) ^ 2 * cycleShift u 0 (qshift q 1 F) := by
  rw [stageTotal_one, Module.End.mul_apply, Nat.zero_add, trainDownEnd_one_one,
    Module.End.one_apply, replOneTotal_one_two_apply]

/-! ### The general half of the mechanism: at the base grading the stage sees only `d^*_+`

Nothing below fixes `a`, `b` or `A`. -/

/-- **At the base grading the stage reads its argument only through `d^*_+{}^{(0)}`, for every `a`,
`b` and `A`.** `HJO.Mellit.replOneTotal` applies `HJO.Sweep.dplusStar` first and every other factor
of `HJO.Mellit.stageTotal` — the two trains of `HJO.Braid.trainDown` and `HJO.Braid.trainUp`, the
power of the replicated letter `Z^{(1)}_{a,b}` of `HJO.Mellit.replicatedLetter`, and the slope
operator of `HJO.Sweep.slopeOperator` — stands to its left. So two arguments with the same `d^*_+`
are indistinguishable to the whole right-hand side of the `α = []` clause.

By `HJO.Sweep.dplusStar_zero_eq` that operator is `cy_1 ∘ τ_{1,1}`, so **the right-hand side of the
`α = []` clause depends on `F` only through `cy_1(τ_{1,1}(F))`, at every `(a,b,A)`** — while the
sweep side applies `τ_{1,1}` with no `cy_1` (at `(a,b) = (1,2)`,
`HJO.Mellit.partialSweepWord_baseEx_of_mem_piece_zero`; the top event of a sweep is a type-`A` event
of width `0`, which is `d_+^{(0)} = -y_1τ_{1,1}`, in every rectangle). That is the discrepancy the
refutation below computes, and this lemma is the half of it that is parameter-free. -/
theorem stageTotal_zero_apply_congr (q u : L) (a b A : ℕ) {F G : Total L}
    (h : dplusStar q u 0 F = dplusStar q u 0 G) :
    stageTotal q u a b 0 A F = stageTotal q u a b 0 A G := by
  have hrep : replOneTotal q u a b 0 F = replOneTotal q u a b 0 G := by
    rw [replOneTotal]
    simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.neg_apply,
      LinearMap.mulLeft_apply, h]
  rw [stageTotal, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply,
    Module.End.mul_apply, hrep]

/-- **The stage at the base grading cannot tell `F` from the vacuum when `cy_1(τ_{1,1}(F)) = 1`.**
`d^*_+{}^{(0)}` fixes `1`, being a composite of two algebra maps, so any such `F` is sent where `1`
is sent. The refutation below is the other side of this: at `F = Ce_1` the two arguments
`τ_{1,1}(F)` and `cy_1(τ_{1,1}(F))` differ, and only the stage side applies the `cy_1`. -/
theorem stageTotal_zero_apply_eq_apply_one (q u : L) (a b A : ℕ) {F : Total L}
    (h : cycleShift u 0 (qshift q 1 F) = 1) :
    stageTotal q u a b 0 A F = stageTotal q u a b 0 A (1 : Total L) := by
  refine stageTotal_zero_apply_congr q u a b A ?_
  have hone : dplusStar q u 0 (1 : Total L) = 1 := by
    rw [dplusStar_apply, map_one, map_one]
  rw [dplusStar_zero_eq, h, hone]

/-! ### The index sets of the clause at `α = []`, `A = 1` -/

/-- The `0 × 0` rectangle has an above-diagonal path of return composition `[]`, so the base index
set of the `α = []` clause is not empty and
`HJO.Mellit.aboveReturnPaths_zero_nil_eq_singleton` is not vacuous at `(a,b) = (1,2)`. -/
theorem mem_aboveReturnPaths_zero_nil_one_two :
    (fun _ => 0 : Heights 1 2 0) ∈ aboveReturnPaths 1 2 0 ([] : List ℕ) := by
  refine mem_aboveReturnPaths_iff.2 ?_
  simp [HasAboveReturns, IsAboveDiagonal, ht]

/-- **The base side of the `α = []` clause is the identity operator.** The index set is a singleton
(`HJO.Mellit.aboveReturnPaths_zero_nil_eq_singleton`) and its word is the identity
(`HJO.Mellit.partialSweepWord_zero_eq_one`), so reading that side as the bare argument loses
nothing. -/
theorem sum_partialSweepWord_zero_nil_apply (q u : L) (F : Total L) :
    ∑ y ∈ aboveReturnPaths 1 2 0 ([] : List ℕ), partialSweepWord q u y (sepLevel 1 0) F = F := by
  rw [aboveReturnPaths_zero_nil_eq_singleton mem_aboveReturnPaths_zero_nil_one_two,
    Finset.sum_singleton, partialSweepWord_zero_eq_one, Module.End.one_apply]

/-- **The sweep side of the clause, summed: one path, one substitution.** -/
theorem sum_partialSweepWord_one_two_of_mem_piece_zero (hq1 : q ≠ 1) {F : Total L}
    (hF : F ∈ piece L 0) :
    ∑ y ∈ aboveReturnPaths 1 2 1 [1], partialSweepWord q u y (sepLevel 1 1) F
      = (MvPolynomial.X 0 : Total L) ^ 2 * qshift q 1 F := by
  rw [aboveReturnPaths_one_two, Finset.sum_singleton,
    partialSweepWord_baseEx_of_mem_piece_zero hq1 hF]

/-! ### The clause at one input is exactly "the substitution `cy_1` acts trivially" -/

/-- **What the `α = []`, `A = 1`, `(a,b) = (1,2)` clause says at an input `F ∈ V_0`.** The scalar
`(-1)^{(a-1)A}(qu)^{1-A}` of `HJO.Mellit.braidRep_specialBraid_dplusIter` is `1` here, and both
sides are `y_1^2` times a substitution applied to `F`: `τ_{1,1}` on the left and `cy_1 ∘ τ_{1,1}` on
the right. So the clause is the assertion that `cy_1` fixes `τ_{1,1}(F)` — nothing else about the
geometry, the level or the stage survives.

At `F = 1` that is true, `τ_{1,1}` and `cy_1` both fixing the scalars; that is
`HJO.Mellit.sum_partialSweepWord_eq_sum_stageTotal_one_two_apply_one`, and it is
`HJO.Mellit.sweepAppend_nil_one_one_two`. At `F = Ce_1` it is false for every `q ≠ 1` and `u ≠ 1`;
that is `HJO.Mellit.not_forall_sum_partialSweepWord_eq_sum_stageTotal_one_two`. -/
theorem sum_partialSweepWord_eq_sum_stageTotal_one_two_iff (hq1 : q ≠ 1) {F : Total L}
    (hF : F ∈ piece L 0) :
    (∑ y ∈ aboveReturnPaths 1 2 1 [1], partialSweepWord q u y (sepLevel 1 1) F
        = ((-1 : L) ^ ((1 - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) • stageTotal q u 1 2 0 1 F)
      ↔ (MvPolynomial.X 0 : Total L) ^ 2 * qshift q 1 F
          = (MvPolynomial.X 0 : Total L) ^ 2 * cycleShift u 0 (qshift q 1 F) := by
  rw [sum_partialSweepWord_one_two_of_mem_piece_zero hq1 hF, stageTotal_one_two_apply]
  norm_num

/-! ### The clause holds at the vacuum -/

/-- **The `α = []`, `A = 1`, `(a,b) = (1,2)` clause of `HJO.Mellit.sweepAppend_iff_sum`, verbatim,
at the vacuum**, for every `q ≠ 1`: both sides are `y_1^2`. This is
`HJO.Mellit.sweepAppend_nil_one_one_two` in path-sum form, and it is what makes
`HJO.Mellit.not_forall_sum_partialSweepWord_eq_sum_stageTotal_one_two` a statement about the
*input* rather than about the instance: the difference of the two operators annihilates `1`. -/
theorem sum_partialSweepWord_eq_sum_stageTotal_one_two_apply_one (q u : L) (hq1 : q ≠ 1) :
    ∑ y ∈ aboveReturnPaths 1 2 (([] : List ℕ).sum + 1) (([] : List ℕ) ++ [1]),
        partialSweepWord q u y (sepLevel 1 (([] : List ℕ).sum + 1)) (1 : Total L)
      = ∑ y ∈ aboveReturnPaths 1 2 ([] : List ℕ).sum ([] : List ℕ),
          ((-1 : L) ^ ((1 - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) •
            stageTotal q u 1 2 ([] : List ℕ).length 1
              (partialSweepWord q u y (sepLevel 1 ([] : List ℕ).sum) (1 : Total L)) := by
  simp only [List.sum_nil, List.length_nil, List.nil_append, Nat.zero_add, Nat.sub_self,
    pow_zero, Nat.cast_one, sub_self, zpow_zero, mul_one, one_smul]
  rw [sum_partialSweepWord_one_two_of_mem_piece_zero hq1 (one_mem (piece L 0)),
    aboveReturnPaths_zero_nil_eq_singleton mem_aboveReturnPaths_zero_nil_one_two,
    Finset.sum_singleton, partialSweepWord_zero_eq_one, Module.End.one_apply,
    stageTotal_one_two_apply, map_one, map_one]

/-! ### And it fails at every other input: the operator reading is refuted -/

/-- **The append identity is NOT an identity of operators.** At `(a,b) = (1,2)`, `α = []`, `A = 1`,
for every `q ≠ 1` and every `u ≠ 1`, the clause of `HJO.Mellit.sweepAppend_iff_sum` fails with the
vacuum `1` replaced by a general argument. The witness is `F = Ce_1`, where the sweep side is
`y_1^2(e_1 + (q-1)y_1)` and the stage side is `y_1^2(e_1 + (q-1)uy_1)`: the discrepancy is
`(q-1)(1-u)y_1^3`, nonzero in `HJO.Sweep.Total L` because `y_1` is one of the polynomial ring's own
variables.

Together with `HJO.Mellit.sum_partialSweepWord_eq_sum_stageTotal_one_two_apply_one`, which is the
same clause at `F = 1` and is TRUE: the difference of the two endomorphisms is nonzero and
annihilates the vacuum. So there is no operator identity here to prove, and a proof of the append
identity cannot be a chain of identities in `Module.End L (HJO.Sweep.Total L)` — such a chain would
prove the statement at every input. Whatever closes it must use a property of the vector `1`.

Neither `q ≠ 1` nor `u ≠ 1` is a hypothesis the target excludes: both follow from the
`AlgebraicIndependent ℤ ![q, u]` of `HJO.Mellit.shuffle_of_lhs_and_induction`, so the failure is at
generic parameters, not at a degeneracy. `a = 1` *is* outside that binder's `1 < a`; see the module
docstring on what is model-only. -/
theorem not_forall_sum_partialSweepWord_eq_sum_stageTotal_one_two (q u : L) (hq1 : q ≠ 1)
    (hu1 : u ≠ 1) :
    ¬ ∀ F : Total L,
        ∑ y ∈ aboveReturnPaths 1 2 (([] : List ℕ).sum + 1) (([] : List ℕ) ++ [1]),
            partialSweepWord q u y (sepLevel 1 (([] : List ℕ).sum + 1)) F
          = ∑ y ∈ aboveReturnPaths 1 2 ([] : List ℕ).sum ([] : List ℕ),
              ((-1 : L) ^ ((1 - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) •
                stageTotal q u 1 2 ([] : List ℕ).length 1
                  (partialSweepWord q u y (sepLevel 1 ([] : List ℕ).sum) F) := by
  intro h
  have h1 := h (MvPolynomial.C (elemSymm L 1))
  simp only [List.sum_nil, List.length_nil, List.nil_append, Nat.zero_add, Nat.sub_self,
    pow_zero, Nat.cast_one, sub_self, zpow_zero, mul_one, one_smul] at h1
  rw [sum_partialSweepWord_one_two_of_mem_piece_zero hq1 C_elemSymm_one_mem_piece_zero,
    aboveReturnPaths_zero_nil_eq_singleton mem_aboveReturnPaths_zero_nil_one_two,
    Finset.sum_singleton, partialSweepWord_zero_eq_one, Module.End.one_apply,
    stageTotal_one_two_apply, qshift_one_C_elemSymm_one,
    cycleShift_zero_C_elemSymm_one_add] at h1
  have hsc : (scal ((q - 1) * (1 - u)) : Total L) = scal (q - 1) - scal ((q - 1) * u) := by
    rw [← scal_sub]
    congr 1
    ring
  have hz : (scal ((q - 1) * (1 - u)) : Total L) * MvPolynomial.X 0 ^ 3 = 0 := by
    rw [hsc]
    linear_combination h1
  rcases mul_eq_zero.1 hz with hs | hx
  · rw [scal, MvPolynomial.C_eq_zero, MvPolynomial.C_eq_zero, mul_eq_zero] at hs
    rcases hs with h' | h'
    · exact hq1 (sub_eq_zero.1 h')
    · exact hu1 (sub_eq_zero.1 h').symm
  · exact absurd (pow_eq_zero_iff (n := 3) (by omega) |>.1 hx) (MvPolynomial.X_ne_zero 0)

end HJO.Mellit

end
