/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepTruncate

/-! # `HJO.Mellit.SweepAppend` is false at `q = 1`, and so is
`HJO.Mellit.mellitInduction_sweepWitness` at the witness

`HJO.Mellit.SweepAppend` (`HJO/Shuffle/SweepWitnessAppend.lean`) carries no hypothesis on `q`
or on `u`, and neither does `HJO.Mellit.mellitInduction_sweepWitness_iff_sweepAppend`, whose
docstring records that as a feature: "Genericity is therefore spent inside
`HJO.Mellit.SweepAppend` alone." This file shows that at `q = 1` there is no genericity left to
spend — the identity is refuted, and with it `HJO.Mellit.BraidClosedForm` and
`HJO.Mellit.MellitInduction` at the sweep witness.

## The mechanism

`HJO.Sweep.corner` is `(q-1)^{-1}` times a difference of composites, so at `q = 1` it is the
**zero map** (`HJO.Sweep.corner_one_eq_zero`); `0^{-1} = 0` in a field. The event operator of
`HJO.Mellit.sweepOperator` at a type-`C` event is `q^{-a_{P̂}(P)}Δ^{(k)}`, so at `q = 1` a *single*
type-`C` event above the level annihilates the whole product
(`HJO.Mellit.partialSweepWord_one_eq_zero_of_eventType_C`). Nothing about the path is used: the
sweep word is a `List.prod` and one zero factor is enough.

The one-part composition `(1)` puts such an event on **every** path, whenever `a < b`. An
above-diagonal `(a, b)`-path has `ŷ_0 = 0` and `b ≤ aŷ_1`, so `a < b` forces `ŷ_1 ≥ 2`; then
`(0,1)` lies strictly above the foot of its own column, its outgoing letter is north, and its
above-diagonal rank `(a+1)a` exceeds `HJO.Mellit.sepLevel a 1 = a + 1/2`. So it is a type-`C` event
of `HJO.Mellit.sweptAbove`, and `HJO.Mellit.dsc_one_eq_zero`:

  `D_{a+1/2, c_{(1)}} = 0` at `q = 1`, for every coprime `a < b` with `0 < a`.

That is a statement about `HJO.Mellit.dsc` alone and does not mention `SweepAppend`.

## The refutation

`HJO.Mellit.dsc_singleton_of_sweepAppend` reads the `α = []` instance of `SweepAppend` in closed
form, and at `A = 1` its right-hand side is `Ω(1;a,b)(1)`. At `a = 1` that is computed by
`HJO.Mellit.replOneTotal_one_left` to be `(-y_1)^b`, which is nonzero because `y_1` is one of the
polynomial ring's own variables — this is exactly the non-vacuity check
`HJO.Mellit.stageTotal_one_left_ne_zero` already performs. So at `q = 1`, `(a,b) = (1,b)` with
`1 < b`, the identity asserts `0 = (-y_1)^b`: `HJO.Mellit.not_sweepAppend_one_left`.

Transported along the two equivalences this gives
`HJO.Mellit.not_braidClosedForm_sweepWitness_one_left` and
`HJO.Mellit.not_mellitInduction_sweepWitness_one_left`.

## What it costs and what it does not

It does **not** touch `HJO.Mellit.shuffle_of_lhs_and_induction`, which asks for
`MellitInduction (sweepWitness q u a b) a b` only at `q, u` algebraically independent over `ℤ` and
at `1 < a < b`; `q = 1` is excluded there and `a = 1` is excluded twice over. The shuffle side is
not weakened by this.

What it does cost is the statement. Any proof of `HJO.Mellit.SweepAppend` must spend `q ≠ 1`, so
either that predicate acquires a hypothesis — which breaks the `iff` against the hypothesis-free
`HJO.Mellit.MellitInduction`, and therefore has to be paid for on the `MellitInduction` side
instead — or the `iff` is restated at a generic `q`. The corner is not an artefact of a degenerate
rectangle: `HJO.Mellit.dsc_one_eq_zero` holds at every coprime `a < b`, so the vanishing half is as
general as the standing range `1 < a < b`. Only the *nonvanishing* of the right-hand side is
proved here at `a = 1`, that being where `HJO.Mellit.euclid`'s slope word has no `𝗓` letter and the
stage is computable in closed form (`HJO.Mellit.replOneTotal_one_left`).
-/

@[expose] public section

open Finset

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The corner operator of `HJO.Sweep.corner` is the zero map at `q = 1`.** It is
`(q-1)^{-1}` times a difference of composites of `d_-` and `d_+`, and `0^{-1} = 0` in a field, so
the scalar kills it whatever the composites are. This is why the sweep has no corner rule at
`q = 1`, and it is the whole mechanism of this file. -/
theorem corner_one_eq_zero (k : ℕ) : corner (1 : L) k = 0 := by
  rw [corner, sub_self, inv_zero, zero_smul]

end HJO.Sweep

namespace HJO.Mellit

open HJO.Sweep Paths

/-- A list product with a zero factor is zero, in any `MonoidWithZero`. Mathlib's
`List.prod_eq_zero` asks for `NoZeroDivisors`, which `Module.End L (Total L)` does not have. -/
theorem list_prod_eq_zero_of_mem {M : Type*} [MonoidWithZero M] {l : List M}
    (h : (0 : M) ∈ l) : l.prod = 0 := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    rcases List.mem_cons.1 h with rfl | h
    · rw [List.prod_cons, zero_mul]
    · rw [List.prod_cons, ih h, mul_zero]

section Refutation

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-- **At `q = 1` a single type-`C` event above the level annihilates the whole sweep word.**
`HJO.Mellit.partialSweepWord` is a `List.prod` of the event operators along
`HJO.Mellit.sortByRank`, and at a type-`C` event the operator is a scalar multiple of
`HJO.Sweep.corner`, which is `0` at `q = 1`. No hypothesis on the path, the level or the rectangle:
one zero factor is enough. -/
theorem partialSweepWord_one_eq_zero_of_eventType_C (u : L) {y : Heights a b N} {η : ℚ}
    {P : ℕ × ℕ} (hP : P ∈ sweptAbove y η) (hC : eventType y P = EventType.C) :
    partialSweepWord (1 : L) u y η = 0 := by
  refine list_prod_eq_zero_of_mem (List.mem_map.2 ⟨P, mem_sortByRank.2 hP, ?_⟩)
  rw [sweepOperator, hC, corner_one_eq_zero, smul_zero]

/-! ### The forced type-`C` event of the one-part rectangle

On the `a × b` rectangle — `N = 1`, the return composition `(1)` — every above-diagonal path climbs
to `ŷ_1 = b` in `a` columns, so when `a < b` its first column climbs past height `1`. The point
`(0,1)` is then interior to a run of north steps, which is a type-`C` event, and its rank is above
`HJO.Mellit.sepLevel a 1`. -/

/-- **`a < b` forces the first column of an above-diagonal `(a, b)`-path past height one.** The
diagonal clause of `HJO.Paths.IsAboveDiagonal` at `r = 1` reads `b ≤ aŷ_1`; if `ŷ_1 ≤ 1` that gives
`b ≤ a`. -/
theorem two_le_ht_one (ha : 0 < a) (hlt : a < b) {y : Heights a b 1} (hy : IsAboveDiagonal y) :
    2 ≤ ht y 1 := by
  have h := hy.2.2.2 1 (by omega)
  rcases Nat.lt_or_ge (ht y 1) 2 with h2 | h2
  · interval_cases h' : ht y 1 <;> omega
  · exact h2

/-- **`(0,1)` is swept above `HJO.Mellit.sepLevel a 1`.** Its above-diagonal rank is `(a+1)a`, and
`a + 1/2 < a^2 + a` as soon as `0 < a`. -/
theorem mem_sweptAbove_zero_one (ha : 0 < a) (hlt : a < b) {y : Heights a b 1}
    (hy : IsAboveDiagonal y) : ((0, 1) : ℕ × ℕ) ∈ sweptAbove y (sepLevel a 1) := by
  have h2 := two_le_ht_one ha hlt hy
  refine Finset.mem_filter.2
    ⟨Paths.mem_sweptRegion.2 ⟨by norm_num, by norm_num, by simpa using by omega⟩, ?_⟩
  have hq : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  rw [sepLevel, pointRank, ParkingFunctions.abovePointRank]
  push_cast
  nlinarith

/-- **The event at `(0,1)` is of type `C`.** The incoming letter is north because `ŷ_0 = 0 < 1`, and
the outgoing letter is north because `1 ≤ a` and `1 < ŷ_1`. -/
theorem eventType_zero_one_eq_C (ha : 0 < a) (hlt : a < b) {y : Heights a b 1}
    (hy : IsAboveDiagonal y) : eventType y ((0, 1) : ℕ × ℕ) = EventType.C := by
  have h0 : ht y 0 = 0 := hy.1
  have h2 := two_le_ht_one ha hlt hy
  rw [eventType]
  norm_num [h0, h2, ha, Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 ha)]
  omega

/-- **At `q = 1` the invariant of the `a × b` rectangle at the one-part colouring vanishes**, for
every coprime `a < b` with `0 < a`.
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`'s path form
(`HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord`) writes `D_{a+1/2, c_{(1)}}` as a sum over
`HJO.Mellit.aboveReturnPaths a b 1 (1)`, and every summand is killed by the type-`C` event at
`(0,1)`. The sum is not empty — `HJO.Mellit.aboveReturnPaths_nonempty` — so this really is a
collapse and not a vacuous index set.

This is a statement about `HJO.Mellit.dsc` alone; nothing about `HJO.Mellit.SweepAppend` enters
its proof. -/
theorem dsc_one_eq_zero (u : L) (hab : Nat.Coprime a b) (ha : 0 < a) (hlt : a < b) :
    dsc (1 : L) u a b 1 (sepLevel a 1) (compColouring a b [1]) = 0 := by
  have hb : 0 < b := by omega
  rw [dsc_compColouring_eq_sum_partialSweepWord (1 : L) u (isAdmissibleLevel_sepLevel a 1)
    (separatesDiagonal_sepLevel' a b 1) hab ha hb (by simp) (by simp)]
  refine Finset.sum_eq_zero fun y hy => ?_
  have hyd : IsAboveDiagonal y := (mem_aboveReturnPaths_iff.1 hy).1
  rw [partialSweepWord_one_eq_zero_of_eventType_C u (mem_sweptAbove_zero_one ha hlt hyd)
    (eventType_zero_one_eq_C ha hlt hyd), LinearMap.zero_apply]

/-- **`HJO.Mellit.SweepAppend` is FALSE at `q = 1`.** Witness: `a = 1`, any `1 < b`, any `u`, in any
field of characteristic zero. The instance that fails is the smallest one off the `nil` field of
`HJO.Mellit.IsBraidValue` — `α = []`, `A = 1` — read in closed form by
`HJO.Mellit.dsc_singleton_of_sweepAppend`. Its two sides are `0`, by
`HJO.Mellit.dsc_one_eq_zero`, and `(-y_1)^b ≠ 0`, by `HJO.Mellit.replOneTotal_one_left`
and `HJO.Mellit.stageTotal_one_left_ne_zero`.

`SweepAppend` quantifies over `α` and `A` with hypotheses only `∀ x ∈ α, 0 < x` and `0 < A`, and
takes `q u : L` as free parameters with no condition, so this is a refutation of the predicate as
stated and not of some instance outside its range. -/
theorem not_sweepAppend_one_left (u : L) {b : ℕ} (hb : 1 < b) : ¬ SweepAppend (1 : L) u 1 b := by
  intro h
  have key := dsc_singleton_of_sweepAppend h (Nat.coprime_one_left b) one_pos (by omega) one_pos
  rw [dsc_one_eq_zero u (Nat.coprime_one_left b) one_pos hb] at key
  refine stageTotal_one_left_ne_zero (1 : L) u (show 0 < b by omega) ?_
  rw [stageTotal_one_left (1 : L) u (show 0 < b by omega),
    ← replOneTotal_one_left (1 : L) u (show 0 < b by omega)]
  simpa using key.symm

/-- **`HJO.Mellit.BraidClosedForm` at the sweep witness is FALSE at `q = 1`**, by
`HJO.Mellit.braidClosedForm_sweepWitness_iff_sweepAppend`. -/
theorem not_braidClosedForm_sweepWitness_one_left (u : L) {b : ℕ} (hb : 1 < b) :
    ¬ BraidClosedForm (sweepWitness (1 : L) u 1 b) 1 b := fun h =>
  not_sweepAppend_one_left u hb
    ((braidClosedForm_sweepWitness_iff_sweepAppend (Nat.coprime_one_left b) one_pos
      (by omega)).1 h)

/-- **`HJO.Mellit.mellitInduction_sweepWitness` at the sweep witness is FALSE at `q = 1`**, by
`HJO.Mellit.mellitInduction_sweepWitness_iff_sweepAppend`. So the clause of `HJO.Mellit.MellitInput`
that the shuffle side requires is not a theorem of the witness as it stands: it holds, if it holds
at all, only at a `q` with `q ≠ 1`.

`HJO.Mellit.shuffle_of_lhs_and_induction` is untouched — it asks for this clause only at `q, u`
algebraically independent over `ℤ` and at `1 < a < b`, and `AlgebraicIndependent ℤ ![q, u]` gives
`q ≠ 1` (`HJO.Mellit.sub_one_ne_zero_of_algebraicIndependent_fst`). What is refuted is the
hypothesis-free reading of the equivalence, not the shuffle assembly. -/
theorem not_mellitInduction_sweepWitness_one_left (u : L) {b : ℕ} (hb : 1 < b) :
    ¬ MellitInduction (sweepWitness (1 : L) u 1 b) 1 b := fun h =>
  not_sweepAppend_one_left u hb
    ((mellitInduction_sweepWitness_iff_sweepAppend (Nat.coprime_one_left b) one_pos
      (by omega)).1 h)

end Refutation

end HJO.Mellit

end
