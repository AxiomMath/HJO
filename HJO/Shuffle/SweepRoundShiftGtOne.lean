/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepConsumeClosure
public meta import HJO.Attr

/-!
# The shift of a round exceeds one exactly when two tail north steps share a window

`HJO.Paths.tailLiveSteps w d` is the set of north steps of the tail `w` that the level line of
diagonal excess `d` crosses, and its cardinality `δ_d` is the shift of round `d`. This file records
the two halves of the statement that the shift is a window count and exceeds one when two tail
north steps are close:

* the count is a count over a **half-open window of width `a`** in the tail's own excess
  (`HJO.Paths.card_tailLiveSteps_eq_card_filter_mem_Ioc`, the cardinality reading of
  `HJO.Paths.mem_tailLiveSteps_iff_Ioc`);
* hence `δ_d > 1` for a suitable `d` **as soon as two distinct north steps of the tail have excesses
  differing by less than `a`** (`HJO.Paths.one_lt_card_tailLiveSteps_of_abs_sub_lt`), and *only*
  then (`HJO.Paths.exists_one_lt_card_tailLiveSteps_iff`).

## How the statement had to be sharpened

The second half, as usually stated, reads "for `a ≥ 2` it exceeds one as soon as the tail has two
north steps within `a` levels of each other". Three things are made precise here.

* **"Within `a` levels" is `|e - e'| < a`, not `≤ a`.** The window `(e, e + a]` of
  `HJO.Paths.mem_tailLiveSteps_iff_Ioc` has `a` integers in it, so two excesses share a window
  exactly when they differ by at most `a - 1`. At a difference of exactly `a` the two windows are
  adjacent and disjoint, so such a pair is no longer a witness.
* **The two north steps must be distinct as lattice points**, which is what makes the shared window
  contain two elements. Distinct excesses are *not* required — two north steps of equal excess are a
  legitimate witness, and the only one available at `a = 1`.
* **`a ≥ 2` is not needed for the implication**, only `0 < a`: what `a ≥ 2` buys is that two
  steps at *different* levels can share a window, which at `a = 1` never happens
  (`HJO.Paths.tailLiveSteps_one_left`). So the hypothesis is weakened here, and the sharpening of
  "within `a` levels" is what replaces it.

The witness is explicit and is the larger of the two excesses plus one — the first level at which
both steps are already live — so the statement names the round, not merely its existence.

## Checked against a computed instance

`HJO.Mellit.card_tailLiveSteps_tailTwoThreeA_two` computes `δ_2 = 2` by kernel evaluation on the
`2 × 3` tail `ŷ = (0,2,3)`. `HJO.Mellit.one_lt_card_tailLiveSteps_tailTwoThreeA_two` derives
`δ_2 > 1` there from the general statement, at the same round `d = 2`, from the north steps `(0,0)`
and `(1,2)` of excesses `0` and `1`. The general lemma's witness `max 0 1 + 1` *is* that instance's
round, so the two agree on which round fails, not merely on the inequality.

## What this costs

Nothing. There is no field element anywhere in this file: `q` and `u` do not appear, and the only
hypothesis is `0 < a`.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

namespace HJO.Paths

open Finset

variable {a b A : ℕ}

/-- **The shift of a round is a count over a half-open window of width `a`.** The cardinality
reading of `HJO.Paths.mem_tailLiveSteps_iff_Ioc`: the north steps of the tail live at diagonal
excess `d` are exactly those whose own excess `e` has `d ∈ (e, e + a]`, an interval of `a`
integers. This is the first half of the statement described in the module docstring. -/
@[hjo "lem_sweep_round_shift_gt_one"]
theorem card_tailLiveSteps_eq_card_filter_mem_Ioc (w : Heights a b A) (d : ℤ) :
    #(tailLiveSteps w d)
      = #{p ∈ northSteps w | d ∈ Finset.Ioc (diagExcess a b p) (diagExcess a b p + a)} := by
  congr 1
  ext p
  constructor
  · intro hp
    have hn : p ∈ northSteps w := (Finset.mem_filter.1 hp).1
    exact Finset.mem_filter.2 ⟨hn, (mem_tailLiveSteps_iff_Ioc hn d).1 hp⟩
  · intro hp
    have hn : p ∈ northSteps w := (Finset.mem_filter.1 hp).1
    exact (mem_tailLiveSteps_iff_Ioc hn d).2 (Finset.mem_filter.1 hp).2

/-- **TWO TAIL NORTH STEPS WITHIN `a - 1` LEVELS OF EACH OTHER MAKE A ROUND OF SHIFT AT LEAST TWO.**
The second half of the statement described in the module docstring, in the sharpened form
the window of `HJO.Paths.mem_tailLiveSteps_iff_Ioc` actually gives: two *distinct* north steps whose
excesses differ by *strictly less than* `a` are both live at the round

`d = max(e, e') + 1`,

the first level past the higher of the two, and so `δ_d ≥ 2`. Only `0 < a` is assumed — at `a = 1`
the hypothesis forces `e = e'` and the statement is the observation that two steps at one level are
both live there; the content of `a ≥ 2` is that *distinct* levels can then share a window. -/
@[hjo "lem_sweep_round_shift_gt_one"]
theorem one_lt_card_tailLiveSteps_of_abs_sub_lt (ha : 0 < a) {w : Heights a b A} {p p' : ℕ × ℕ}
    (hp : p ∈ northSteps w) (hp' : p' ∈ northSteps w) (hne : p ≠ p')
    (hlt : |diagExcess a b p - diagExcess a b p'| < a) :
    1 < #(tailLiveSteps w (max (diagExcess a b p) (diagExcess a b p') + 1)) := by
  have haz : (1 : ℤ) ≤ a := by exact_mod_cast ha
  rw [abs_sub_lt_iff] at hlt
  refine Finset.one_lt_card.2 ⟨p, ?_, p', ?_, hne⟩
  · rw [mem_tailLiveSteps_iff_Ioc hp, Finset.mem_Ioc]
    rcases max_cases (diagExcess a b p) (diagExcess a b p') with ⟨h, -⟩ | ⟨h, -⟩ <;>
      rw [h] <;> omega
  · rw [mem_tailLiveSteps_iff_Ioc hp', Finset.mem_Ioc]
    rcases max_cases (diagExcess a b p) (diagExcess a b p') with ⟨h, -⟩ | ⟨h, -⟩ <;>
      rw [h] <;> omega

/-- **And that is the only way a round can have shift more than one.** Two distinct north steps live
at a common level have their excesses inside a common window of width `a`
(`HJO.Paths.mem_tailLiveSteps_iff_Ioc`), so they differ by less than `a`. Together with
`HJO.Paths.one_lt_card_tailLiveSteps_of_abs_sub_lt` this makes the "as soon as" an
equivalence: the rectangle has a round of shift at least two exactly when the tail has two distinct
north steps within `a - 1` levels of each other. -/
theorem exists_one_lt_card_tailLiveSteps_iff (ha : 0 < a) (w : Heights a b A) :
    (∃ d : ℤ, 1 < #(tailLiveSteps w d)) ↔
      ∃ p ∈ northSteps w, ∃ p' ∈ northSteps w,
        p ≠ p' ∧ |diagExcess a b p - diagExcess a b p'| < a := by
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨p, hp, p', hp', hne⟩ := Finset.one_lt_card.1 hd
    have hpn : p ∈ northSteps w := (Finset.mem_filter.1 hp).1
    have hpn' : p' ∈ northSteps w := (Finset.mem_filter.1 hp').1
    refine ⟨p, hpn, p', hpn', hne, ?_⟩
    rw [mem_tailLiveSteps_iff_Ioc hpn, Finset.mem_Ioc] at hp
    rw [mem_tailLiveSteps_iff_Ioc hpn', Finset.mem_Ioc] at hp'
    rw [abs_sub_lt_iff]
    omega
  · rintro ⟨p, hp, p', hp', hne, hlt⟩
    exact ⟨_, one_lt_card_tailLiveSteps_of_abs_sub_lt ha hp hp' hne hlt⟩

end HJO.Paths

/-! ### Checked against the computed `(2,3)` instance -/

namespace HJO.Mellit

open HJO.Paths Finset

/-- **The general statement, read at the worked instance.** The `2 × 3` tail
`HJO.Mellit.tailTwoThreeA` has the distinct north steps `(0,0)` and `(1,2)`, of diagonal excesses
`0` and `1`, which differ by `1 < 2 = a`; so
`HJO.Paths.one_lt_card_tailLiveSteps_of_abs_sub_lt` gives a round of shift at least two, and names
it as `max 0 1 + 1 = 2`. That is the same round at which
`HJO.Mellit.card_tailLiveSteps_tailTwoThreeA_two` computes the shift to be exactly `2` by kernel
evaluation, so the general lemma and the instance agree on the round and not merely on the
inequality. -/
theorem one_lt_card_tailLiveSteps_tailTwoThreeA_two :
    1 < #(tailLiveSteps tailTwoThreeA 2) := by
  have hmax : max (diagExcess 2 3 ((0, 0) : ℕ × ℕ)) (diagExcess 2 3 ((1, 2) : ℕ × ℕ)) + 1
      = (2 : ℤ) := by
    norm_num [diagExcess]
  have h := one_lt_card_tailLiveSteps_of_abs_sub_lt (a := 2) (b := 3) (A := 1) (by norm_num)
    (w := tailTwoThreeA) (p := (0, 0)) (p' := (1, 2)) (by decide) (by decide) (by decide)
    (by norm_num [diagExcess])
  rwa [hmax] at h

end HJO.Mellit
