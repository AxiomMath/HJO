/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidAppendRanks
public import HJO.Shuffle.SlopeBraid
public meta import HJO.Attr

/-! # The trajectory of the moving point is the slope word

The arithmetic half of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`: the letters the appended
point contributes are those of `HJO.Mellit.slopeWord`.

The argument is the following:

> With `M := m+n` one has `θ = m/M` and `1-θ = n/M`, so in units of `1/M` the map `nx_θ` of
> Definition `HJO.Braid.nextCrossing` subtracts `m` when the coordinate exceeds `m` and adds `n`
> when it is less than `m`; both are subtraction of `m` modulo `M`. Starting just below `n` and
> taking `i` steps therefore reaches the coordinate `-im` modulo `M`, and the wall crossed at the
> following step is the horizontal one exactly when that residue exceeds `m`.

Mellit's own justification is an "it is easy to see". This file proves it, and in the form the
lemma needs, which is not the form described above: the argument above takes
`θ = m/M` *exactly*, and at the exact slope the orbit is periodic of period `M`, so the appended
point would revisit each of its own earlier positions and `HJO.Braid.IsSpecialBraidData`'s
injectivity clause would fail at `A ≥ 2`. The slope used downstream is `s = b/a - ε`, i.e.

`θ = a/(a+b) + e` with `e > 0`,

and the orbit then drifts downwards by `(a+b)e` per turn. What makes the letters the same as at the
exact slope is that the drift accumulated over the whole run stays inside one cell of width
`1/(a+b)`; that is the hypothesis `hsmall` below, and it is the precise content of Mellit's
"for a small `ε' > 0`".

## Main results

* `HJO.Mellit.trajPos` — the closed form: after `j` steps from `1 - θ - δ` the coordinate is
  `(a + b - ϱ_{a,b}(j+1))/(a+b) - ((j+1)e + δ)`, a point of the `(a+b)`-grid displaced downwards by
  the accumulated drift.
* `HJO.Mellit.iterate_nextCrossing_eq_trajPos` — that closed form is what `HJO.Braid.nextCrossing`
  iterates to. This is the preamble's "taking `i` steps reaches the coordinate `-im` modulo `M`",
  with the drift carried.
* `HJO.Mellit.trajPos_lt_theta_iff` — the wall crossed at step `j` is the vertical one exactly when
  `ϱ_{a,b}(j+1) ≥ b`, which is exactly `HJO.Mellit.slopeLetter a b (j+1) = .z`:
  `HJO.Mellit.slopeLetter_eq_z_iff_trajPos_lt_theta`.
* `HJO.Mellit.trajPos_ne_theta` — no position of the run meets the puncture, which
  `HJO.Braid.IsSpecialBraidData` requires and which the same smallness hypothesis gives for free.

The offset `δ` is allowed to be `0`, which is the case needed downstream: the appended entry of
`HJO.Braid.specialBraid_eq_conj_phiPlusStar` is exactly `1 - θ`. What the comparisons need is not
`δ > 0` but only that `δ` and `e` are not both zero, `0 < 2e + δ`; with `δ = 0` the perturbation
`e > 0` of the slope does that work by itself, and `δ < 0` is admitted too.

## The three letters of a turn, and why the exception is forced

`HJO.Mellit.slopeWord` lists `λ(i)` for `1 ≤ i ≤ a+b-2` only, and the run is longer than that: a
turn is `a+b` steps. The two extra letters per turn are the ones Mellit writes out separately,

> each extra round begins with `ỹ_{k+1} z_{k+1} = ỹ_{k+1} T_{k+1↘1} z_1 T_{1↗k+1}`,

and they are *forced* by the arithmetic rather than assumed:

* at `j + 1 = a+b-1` the residue is `ϱ = b` (`HJO.Mellit.slopeResidue_top`), so the letter is a
  `z` — and this is the step at which the point is next to the finish, Mellit's exception, where
  `HJO.Braid.entryRank_update_eq_succ_of_forall_lt` puts it at rank `k+1` rather than `1`;
* at `j + 1 = a+b` the residue is `0 < b`, so the letter is a `y`.

So the letter sequence of one turn is `λ(1), …, λ(a+b-2), 𝗓, 𝗒` in time order, and
`HJO.Mellit.slopeLetter_periodic` makes the next turn repeat it. That is the right-hand side of the
lemma read backwards, `HJO.Braid.braidWord` putting the earliest move rightmost.

## References

The lemma
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`. Transcribing A. Mellit, *Toric braids and
`(m, n)`-parking functions*, section 6.
-/

@[expose] public section

namespace HJO.Mellit

open Braid

/-! ### The residue recursion -/

/-- **One step of the residue**: `ϱ_{a,b}(j+2) = ϱ_{a,b}(j+1) + a` reduced modulo `a+b`. This is the
preamble's "both are subtraction of `m` modulo `M`", read forwards. -/
theorem slopeResidue_succ (a b j : ℕ) (ha : a < a + b) :
    slopeResidue a b (j + 2) = (slopeResidue a b (j + 1) + a) % (a + b) := by
  have h : (j + 2) * a = (j + 1) * a + a := by ring
  rw [slopeResidue, slopeResidue, h]
  conv_lhs => rw [Nat.add_mod, Nat.mod_eq_of_lt ha]

/-- The residue is periodic of period `a + b`, so the letters of the second turn repeat those of the
first. -/
theorem slopeResidue_periodic (a b j : ℕ) :
    slopeResidue a b (j + (a + b)) = slopeResidue a b j := by
  rw [slopeResidue, slopeResidue, Nat.add_mul, Nat.add_mul_mod_self_left]

/-- The letters of the run are periodic of period `a + b`: a turn repeats. -/
theorem slopeLetter_periodic (a b j : ℕ) :
    slopeLetter a b (j + (a + b)) = slopeLetter a b j := by
  rw [slopeLetter, slopeLetter, slopeResidue_periodic]

/-- The residue is smaller than `a + b`, so the grid point of `HJO.Mellit.trajPos` below lies in
`(0, 1]`. -/
theorem slopeResidue_lt_add (a b : ℕ) (hb : 1 ≤ b) (i : ℕ) : slopeResidue a b i < a + b :=
  Nat.mod_lt _ (by omega)

/-- `HJO.Mellit.slopeWord`'s letter is `𝗓` exactly when the residue is not below `n`. The `=`
boundary falls in the `𝗓` branch, as `HJO.Mellit.slopeLetter` has it. -/
theorem slopeLetter_eq_z_iff (m n i : ℕ) :
    slopeLetter m n i = SlopeLetter.z ↔ n ≤ slopeResidue m n i := by
  unfold slopeLetter
  by_cases hc : slopeResidue m n i < n
  · have hn : ¬ (n ≤ slopeResidue m n i) := by omega
    simp [hc, hn]
  · have hn : n ≤ slopeResidue m n i := by omega
    simp [hc, hn]

/-- `HJO.Mellit.slopeWord`'s letter is `𝗒` exactly when the residue is below `n`. -/
theorem slopeLetter_eq_y_iff (m n i : ℕ) :
    slopeLetter m n i = SlopeLetter.y ↔ slopeResidue m n i < n := by
  unfold slopeLetter
  by_cases hc : slopeResidue m n i < n
  · simp [hc]
  · simp [hc]

/-- The residue is unchanged by adding any multiple of `a + b`: a turn repeats, `q` turns later
too. -/
theorem slopeResidue_add_mul (a b j q : ℕ) :
    slopeResidue a b (j + q * (a + b)) = slopeResidue a b j := by
  rw [slopeResidue, slopeResidue, Nat.add_mul,
    show q * (a + b) * a = q * a * (a + b) from by ring, Nat.add_mul_mod_self_right]

/-- The letters repeat with the residue. -/
theorem slopeLetter_add_mul (a b j q : ℕ) :
    slopeLetter a b (j + q * (a + b)) = slopeLetter a b j := by
  rw [slopeLetter, slopeLetter, slopeResidue_add_mul]

/-- The residue at a multiple of `a + b` is `0`: the step that begins each extra round. -/
theorem slopeResidue_mul (a b q : ℕ) : slopeResidue a b (q * (a + b)) = 0 := by
  rw [slopeResidue, show q * (a + b) * a = q * a * (a + b) from by ring, Nat.mul_mod_left]

/-! ### The closed form of the trajectory -/

/-- **The position of the moving point after `j` steps.** The point starts at `1 - θ - δ`, just
below Mellit's starting point, and `θ = a/(a+b) + e` is the perturbed slope's antidiagonal
coordinate. The position is then a point of the `(a+b)`-grid — namely `(a+b-ϱ_{a,b}(j+1))/(a+b)`,
which is the preamble's `-(j+1)a` modulo `a+b` — displaced downwards by the drift `(j+1)e`
accumulated so far together with the initial offset `δ`. -/
def trajPos (a b : ℕ) (e δ : ℚ) (j : ℕ) : ℚ :=
  ((a : ℚ) + b - (slopeResidue a b (j + 1) : ℚ)) / ((a : ℚ) + b) - ((j + 1) * e + δ)

/-! ### Which wall is crossed -/

section Comparison

variable {a b : ℕ} {e δ θ : ℚ} {m j : ℕ}

/-- The gap between the trajectory and the puncture, cleared of denominators: the whole comparison
of `HJO.Mellit.trajPos a b e δ j` with `θ` is the comparison of the integer `b - ϱ_{a,b}(j+1)` with
the accumulated drift `(a+b)((j+2)e + δ)`. -/
theorem trajPos_sub_theta_mul (hb : 1 ≤ b) (hθ : θ = (a : ℚ) / ((a : ℚ) + b) + e) :
    (trajPos a b e δ j - θ) * ((a : ℚ) + b)
      = ((b : ℚ) - (slopeResidue a b (j + 1) : ℚ))
        - ((a : ℚ) + b) * (((j : ℚ) + 2) * e + δ) := by
  have hD : (0 : ℚ) < (a : ℚ) + b := by positivity
  rw [trajPos, hθ]
  field_simp
  ring

/-- The drift accumulated by step `j` is positive and stays below `1`: the two halves of the
smallness hypothesis, in the cleared form. -/
theorem drift_bounds (hb : 1 ≤ b) (he : 0 ≤ e) (hpos : 0 < 2 * e + δ) (hj : j ≤ m)
    (hsmall : ((m : ℚ) + 2) * e + δ < 1 / ((a : ℚ) + b)) :
    0 < ((a : ℚ) + b) * (((j : ℚ) + 2) * e + δ) ∧
      ((a : ℚ) + b) * (((j : ℚ) + 2) * e + δ) < 1 := by
  have hD : (0 : ℚ) < (a : ℚ) + b := by positivity
  have hjm : (j : ℚ) ≤ (m : ℚ) := Nat.cast_le.2 hj
  have hjpos : (0 : ℚ) ≤ (j : ℚ) := Nat.cast_nonneg j
  have hje : (0 : ℚ) ≤ ((j : ℚ) + 2) * e := mul_nonneg (by linarith) he
  have hje2 : (2 : ℚ) * e ≤ ((j : ℚ) + 2) * e := mul_le_mul_of_nonneg_right (by linarith) he
  refine ⟨mul_pos hD (by linarith), ?_⟩
  have hmul : (((m : ℚ) + 2) * e + δ) * ((a : ℚ) + b) < 1 := by
    have h := mul_lt_mul_of_pos_right hsmall hD
    rwa [one_div, inv_mul_cancel₀ (ne_of_gt hD)] at h
  have hstep : ((j : ℚ) + 2) * e ≤ ((m : ℚ) + 2) * e :=
    mul_le_mul_of_nonneg_right (by linarith) he
  calc ((a : ℚ) + b) * (((j : ℚ) + 2) * e + δ)
      ≤ ((a : ℚ) + b) * (((m : ℚ) + 2) * e + δ) :=
        mul_le_mul_of_nonneg_left (by linarith) hD.le
    _ = (((m : ℚ) + 2) * e + δ) * ((a : ℚ) + b) := by ring
    _ < 1 := hmul

/-- **The vertical wall is the one crossed at step `j` exactly when `ϱ_{a,b}(j+1) ≥ b`.** One
direction needs only `δ > 0`; the other is where the smallness of the perturbation is used, the
drift having to stay below the `1/(a+b)` gap between two grid points. -/
theorem trajPos_lt_theta_iff (hb : 1 ≤ b) (hθ : θ = (a : ℚ) / ((a : ℚ) + b) + e) (he : 0 ≤ e)
    (hpos : 0 < 2 * e + δ) (hj : j ≤ m) (hsmall : ((m : ℚ) + 2) * e + δ < 1 / ((a : ℚ) + b)) :
    trajPos a b e δ j < θ ↔ b ≤ slopeResidue a b (j + 1) := by
  have hD : (0 : ℚ) < (a : ℚ) + b := by positivity
  have hmul := trajPos_sub_theta_mul (a := a) (b := b) (e := e) (δ := δ) (j := j) hb hθ
  obtain ⟨hd0, hd1⟩ := drift_bounds (a := a) hb he hpos hj hsmall
  constructor
  · intro h
    by_contra hc
    have hlt : slopeResidue a b (j + 1) < b := by omega
    have hge : (1 : ℚ) ≤ (b : ℚ) - (slopeResidue a b (j + 1) : ℚ) := by
      have : (slopeResidue a b (j + 1) : ℚ) + 1 ≤ (b : ℚ) := by exact_mod_cast hlt
      linarith
    have hneg : (trajPos a b e δ j - θ) * ((a : ℚ) + b) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hD
    linarith
  · intro h
    have hle : (b : ℚ) - (slopeResidue a b (j + 1) : ℚ) ≤ 0 := by
      have : (b : ℚ) ≤ (slopeResidue a b (j + 1) : ℚ) := Nat.cast_le.2 h
      linarith
    have hneg : (trajPos a b e δ j - θ) * ((a : ℚ) + b) < 0 := by linarith
    nlinarith

/-- **The horizontal wall is crossed exactly when `ϱ_{a,b}(j+1) < b`**: the complementary form of
`HJO.Mellit.trajPos_lt_theta_iff`, with the strict inequality on the other side. Having both is what
makes `HJO.Mellit.trajPos_ne_theta` available. -/
theorem theta_lt_trajPos_iff (hb : 1 ≤ b) (hθ : θ = (a : ℚ) / ((a : ℚ) + b) + e) (he : 0 ≤ e)
    (hpos : 0 < 2 * e + δ) (hj : j ≤ m) (hsmall : ((m : ℚ) + 2) * e + δ < 1 / ((a : ℚ) + b)) :
    θ < trajPos a b e δ j ↔ slopeResidue a b (j + 1) < b := by
  have hD : (0 : ℚ) < (a : ℚ) + b := by positivity
  have hmul := trajPos_sub_theta_mul (a := a) (b := b) (e := e) (δ := δ) (j := j) hb hθ
  obtain ⟨hd0, hd1⟩ := drift_bounds (a := a) hb he hpos hj hsmall
  constructor
  · intro h
    by_contra hc
    have hle : (b : ℚ) - (slopeResidue a b (j + 1) : ℚ) ≤ 0 := by
      have : (b : ℚ) ≤ (slopeResidue a b (j + 1) : ℚ) := Nat.cast_le.2 (by omega)
      linarith
    have hmulpos : 0 < (trajPos a b e δ j - θ) * ((a : ℚ) + b) :=
      mul_pos (by linarith) hD
    linarith
  · intro h
    have hge : (1 : ℚ) ≤ (b : ℚ) - (slopeResidue a b (j + 1) : ℚ) := by
      have : (slopeResidue a b (j + 1) : ℚ) + 1 ≤ (b : ℚ) := by exact_mod_cast h
      linarith
    have hmulpos : 0 < (trajPos a b e δ j - θ) * ((a : ℚ) + b) := by linarith
    nlinarith

/-- **No position of the run meets the puncture**, which `HJO.Braid.IsSpecialBraidData`'s `ne_theta`
clause requires: the two comparisons above are exhaustive and both strict. -/
theorem trajPos_ne_theta (hb : 1 ≤ b) (hθ : θ = (a : ℚ) / ((a : ℚ) + b) + e) (he : 0 ≤ e)
    (hpos : 0 < 2 * e + δ) (hj : j ≤ m) (hsmall : ((m : ℚ) + 2) * e + δ < 1 / ((a : ℚ) + b)) :
    trajPos a b e δ j ≠ θ := by
  rcases le_or_gt b (slopeResidue a b (j + 1)) with h | h
  · exact ne_of_lt ((trajPos_lt_theta_iff hb hθ he hpos hj hsmall).2 h)
  · exact ne_of_gt ((theta_lt_trajPos_iff hb hθ he hpos hj hsmall).2 h)

end Comparison

/-! ### The trajectory -/

/-- `HJO.Braid.nextCrossing` below the puncture. -/
theorem nextCrossing_eq_add_of_lt {θ x : ℚ} (h : x < θ) : nextCrossing θ x = x + 1 - θ := by
  simp [nextCrossing, not_lt.2 h.le]

/-- `HJO.Braid.nextCrossing` above the puncture. -/
theorem nextCrossing_eq_sub_of_gt {θ x : ℚ} (h : θ < x) : nextCrossing θ x = x - θ := by
  simp [nextCrossing, h]

/-- **The trajectory of the moving point is the closed form.** The preamble's "starting just below
`n` and taking `i` steps reaches the coordinate `-im` modulo `M`", with the drift of the perturbed
slope carried along.

The induction is the preamble's own dichotomy: below the puncture `HJO.Braid.nextCrossing` adds
`1 - θ` and the residue wraps past `a+b`; above it subtracts `θ` and the residue simply increases by
`a`. Which of the two happens is decided by `HJO.Mellit.trajPos_lt_theta_iff`, and that is where the
drift bound enters. -/
theorem iterate_nextCrossing_eq_trajPos {a b : ℕ} {e δ θ : ℚ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hθ : θ = (a : ℚ) / ((a : ℚ) + b) + e) (he : 0 ≤ e) (hpos : 0 < 2 * e + δ) {m : ℕ}
    (hsmall : ((m : ℚ) + 2) * e + δ < 1 / ((a : ℚ) + b)) :
    ∀ j ≤ m, (nextCrossing θ)^[j] (1 - θ - δ) = trajPos a b e δ j := by
  have hD : (0 : ℚ) < (a : ℚ) + b := by positivity
  have halt : a < a + b := by omega
  intro j hj
  induction j with
  | zero =>
    have h1 : slopeResidue a b 1 = a := by rw [slopeResidue, one_mul, Nat.mod_eq_of_lt halt]
    rw [Function.iterate_zero_apply, trajPos, h1, hθ]
    push_cast
    field_simp
    ring
  | succ j ih =>
    have hjm : j ≤ m := by omega
    rw [Function.iterate_succ_apply', ih hjm]
    have hrlt : slopeResidue a b (j + 1) < a + b := slopeResidue_lt_add a b hb _
    have hsucc : slopeResidue a b (j + 2) = (slopeResidue a b (j + 1) + a) % (a + b) :=
      slopeResidue_succ a b j halt
    rcases le_or_gt b (slopeResidue a b (j + 1)) with h | h
    · have hlt : trajPos a b e δ j < θ := (trajPos_lt_theta_iff hb hθ he hpos hjm hsmall).2 h
      have hr' : slopeResidue a b (j + 2) = slopeResidue a b (j + 1) + a - (a + b) := by
        rw [hsucc, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      have hcast : ((slopeResidue a b (j + 1) + a - (a + b) : ℕ) : ℚ)
          = (slopeResidue a b (j + 1) : ℚ) + a - ((a : ℚ) + b) := by
        have h2 : ((slopeResidue a b (j + 1) + a - (a + b) : ℕ) : ℚ)
            = ((slopeResidue a b (j + 1) + a : ℕ) : ℚ) - ((a + b : ℕ) : ℚ) :=
          Nat.cast_sub (by omega)
        push_cast at h2 ⊢
        linarith
      rw [nextCrossing_eq_add_of_lt hlt, trajPos, trajPos, show j + 1 + 1 = j + 2 from rfl, hr',
        hcast, hθ]
      push_cast
      field_simp
      ring
    · have hgt : θ < trajPos a b e δ j := (theta_lt_trajPos_iff hb hθ he hpos hjm hsmall).2 h
      have hr' : slopeResidue a b (j + 2) = slopeResidue a b (j + 1) + a := by
        rw [hsucc, Nat.mod_eq_of_lt (by omega)]
      rw [nextCrossing_eq_sub_of_gt hgt, trajPos, trajPos, show j + 1 + 1 = j + 2 from rfl, hr',
        hθ]
      push_cast
      field_simp
      ring

/-! ### The letters -/

/-- **The letter of step `j` is `λ_{a,b}(j+1)`.** `HJO.Braid.braidStep` takes the `z` branch exactly
when the coordinate is below `θ`, and `HJO.Mellit.slopeWord`'s letter is `𝗓` exactly when the
residue is not below `b`; `HJO.Mellit.trajPos_lt_theta_iff` says those are the same condition.

The two agree at `ϱ = b` as well, where `HJO.Mellit.slopeLetter`'s `<` puts the letter in the `𝗓`
branch: that residue occurs at `j + 1 = a+b-1` by `HJO.Mellit.slopeResidue_top`, which is the step
at which the point is next to the finish, and it is indeed a `z` — Mellit's exception is about
the *rank* of that letter, not about the letter. -/
theorem slopeLetter_eq_z_iff_trajPos_lt_theta {a b : ℕ} {e δ θ : ℚ} {m j : ℕ} (hb : 1 ≤ b)
    (hθ : θ = (a : ℚ) / ((a : ℚ) + b) + e) (he : 0 ≤ e) (hpos : 0 < 2 * e + δ)
    (hj : j ≤ m)
    (hsmall : ((m : ℚ) + 2) * e + δ < 1 / ((a : ℚ) + b)) :
    slopeLetter a b (j + 1) = SlopeLetter.z ↔ trajPos a b e δ j < θ := by
  rw [trajPos_lt_theta_iff hb hθ he hpos hj hsmall, slopeLetter_eq_z_iff]

/-- **The letter of step `j` is a `y` exactly when the point crosses the horizontal wall.** -/
theorem slopeLetter_eq_y_iff_theta_lt_trajPos {a b : ℕ} {e δ θ : ℚ} {m j : ℕ} (hb : 1 ≤ b)
    (hθ : θ = (a : ℚ) / ((a : ℚ) + b) + e) (he : 0 ≤ e) (hpos : 0 < 2 * e + δ)
    (hj : j ≤ m)
    (hsmall : ((m : ℚ) + 2) * e + δ < 1 / ((a : ℚ) + b)) :
    slopeLetter a b (j + 1) = SlopeLetter.y ↔ θ < trajPos a b e δ j := by
  rw [theta_lt_trajPos_iff hb hθ he hpos hj hsmall, slopeLetter_eq_y_iff]

/-- **The first of the two extra letters of a turn.** At `j+1 = a+b-1` the residue is `b`, so the
step is a `z`; this is the passage next to the finish, Mellit's exception, where
`HJO.Braid.entryRank_update_eq_succ_of_forall_lt` puts the letter at rank `k+1` rather than `1`. -/
theorem slopeLetter_pred_eq_z {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    slopeLetter a b (a + b - 1) = SlopeLetter.z := by
  rw [slopeLetter_eq_z_iff, slopeResidue_top ha hb]

/-- **The second extra letter of a turn.** At `j+1 = a+b` the residue is `0`, so the step is a `y`:
the `ỹ_{k+1}` that begins each extra round. -/
theorem slopeLetter_add_eq_y {a b : ℕ} (hb : 1 ≤ b) :
    slopeLetter a b (a + b) = SlopeLetter.y := by
  have h0 : slopeResidue a b (a + b) = 0 := by rw [slopeResidue, Nat.mul_mod_right]
  rw [slopeLetter_eq_y_iff, h0]
  omega

end HJO.Mellit

end
