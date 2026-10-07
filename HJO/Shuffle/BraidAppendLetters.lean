/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidLetterCount
public import HJO.Shuffle.SlopeTrajectory
public meta import HJO.Attr

/-! # The letters of the appended point's run, one by one

`HJO/Shuffle/BraidAppendRanks.lean` reduces the appended point's run of moves to
`HJO.Braid.conjRun`, a product of letters each conjugated to rank `1`, and shows under the weak
clustering hypothesis that every rank is `1` or `k+1`. `HJO/Shuffle/SlopeTrajectory.lean`
computes which wall is crossed at each step. This file puts the two together and evaluates each
conjugated letter outright, which needs the clustering hypothesis in its *quantitative* form.

## Why the weak hypothesis is not enough here

`HJO.Braid.IsFinishCluster` says the moving point's trajectory misses the cluster of the other
points' final positions, and that gives the rank dichotomy. It does not say *which* of the vertical
crossings sit at rank `1`. The statement proved here needs exactly that: the crossings next to the
finish at rank `k+1` (Mellit's exception) and every other one at rank `1`. Locating the cluster in
units of `1/(a+b)` is what settles it, and that is `HJO.Braid.IsAppendSetup` below:

* `cluster_lo`, `θ - 1/d < f_i`: the cluster sits above every point of the `1/d`-grid except the one
  hugging the finish, so a vertical crossing away from the finish — where the grid point is at most
  `(a-1)/d` — falls below the whole cluster and has rank `1`;
* `cluster_hi`, `f_i < θ - ((Ad)e + δ)`: the cluster sits below all `A` of the near-finish positions
  `θ - ((j+2)e + δ)`, so a vertical crossing next to the finish rises above the whole cluster and
  has rank `k+1`.

Together they are Mellit's "in the final position all points are clustered close to `finish` at
`(t, 1-t)`" (Section 6) made quantitative, and they imply `IsFinishCluster`.

## Main results

* `HJO.Braid.IsAppendSetup` — the hypotheses of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`
  as this file needs them, with the appended entry at `1 - θ - δ` for any offset `δ ≥ 0` small
  enough to keep the run inside its grid cell and above the cluster.
* `HJO.Braid.gap_of_grid` — the one hypothesis a lowered appended entry costs, discharged from a
  grid: if every position of the data is a multiple of `1/n` and `δ ≤ 1/n`, no other position can
  separate the appended entry from `1 - θ`.
* `HJO.Braid.conjRun_succ_eq_y` — a step with `ϱ_{a,b}(j+1) < b` contributes `y_1`.
* `HJO.Braid.conjRun_succ_eq_z` — a step with `ϱ_{a,b}(j+1) > b` contributes `z_1`.
* `HJO.Braid.conjRun_succ_eq_z_finish` — a step with `ϱ_{a,b}(j+1) = b`, which is the passage next
  to the finish, contributes `z_1·T_{1↗k+1}T_{k+1↘1}`.
* `HJO.Braid.conjRun_succ_eq_slopeLetter` — the first two combined: away from the finish the step
  contributes exactly the letter `HJO.Braid.slopeBraid` reads off `λ_{a,b}(j+1)`.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 6. -/

@[expose] public section

namespace HJO.Braid

open Mellit

/-! ### The setup -/

/-- **The situation of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`.** The appended point of
index `0` stands at `1 - θ - δ`, weakly below Mellit's start `1 - θ`; the slope is `b/a`
perturbed by `ε > 0`, which makes `θ = a/d + e` with `e > 0` and `d = a+b`; the run is `A` turns, so
`Ad - 2` moves; the drift accumulated over the run, *together with the offset `δ`*, stays inside one
cell of the `1/d`-grid; and the other `k` points stand at final positions clustered at the finish,
below the whole run.

**Why `δ` is here, and what it is for.** The plain form of the statement has the appended entry
equal to `1 - θ` exactly, and no consumer supplies that: under `HJO.Mellit.braidDataOfColouring` the
last component's position is `(1-θ) - (η - aN)/D`, strictly below `1-θ` at every separating level
(`HJO.Mellit.fract_crossingAbscissa_componentTopIndex_last_lt`). What the proof actually reads off
the appended entry is which cell of the `1/d`-grid each of its iterates falls in, and lowering the
entry by `δ` lowers every iterate by the same `δ` (`HJO.Mellit.trajPos`, whose `δ` argument enters
as a uniform shift). So the whole argument survives as long as `δ` does not carry an iterate out of
its cell — the `drift` clause — and does not carry the run below the cluster — the `cluster_hi`
clause. At `δ = 0` both are the hypotheses of the plain form. -/
structure IsAppendSetup (a b A k : ℕ) (e δ θ : ℚ) (w : Fin (k + 1) → ℚ) : Prop where
  /-- `1 ≤ a`. -/
  one_le_a : 1 ≤ a
  /-- `1 ≤ b`. -/
  one_le_b : 1 ≤ b
  /-- `a` and `b` are coprime, which `HJO.Mellit.slopeWord` needs. -/
  coprime : Nat.Coprime a b
  /-- `a < b`: it is what puts the start `1 - θ` above the finish `θ`, and so what selects the
  second case, `finish < start`, of Mellit's case distinction for the braid with the new point
  held fixed. -/
  a_lt_b : a < b
  /-- The run has at least one turn. -/
  one_le_A : 1 ≤ A
  /-- The slope is perturbed, not exact: at `e = 0` the orbit is periodic of period `d`. -/
  e_pos : 0 < e
  /-- The appended point is not above the start. -/
  delta_nonneg : 0 ≤ δ
  /-- `θ = a/d + e`, which is `θ(s+1) = 1` at `s = b/a - ε`. -/
  theta_eq : θ = (a : ℚ) / ((a : ℚ) + b) + e
  /-- The drift over the whole run, together with the offset of the appended entry, stays inside one
  cell of the grid. -/
  drift : ((A * (a + b) : ℕ) : ℚ) * e + δ < 1 / ((a : ℚ) + b)
  /-- The appended point stands at the start, lowered by `δ`. -/
  start : w 0 = 1 - θ - δ
  /-- The cluster is above every grid point but the one hugging the finish. -/
  cluster_lo : ∀ t : Fin k, θ - 1 / ((a : ℚ) + b) < w t.succ
  /-- The cluster is below all `A` near-finish positions of the moving point. -/
  cluster_hi : ∀ t : Fin k, w t.succ < θ - (((A * (a + b) : ℕ) : ℚ) * e + δ)

/-! ### The isotopy clause, discharged from a grid -/

/-- **The isotopy clause of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`, from a grid.** The
hypothesis a lowered appended entry costs — no iterate of another point lying in `[w_0, 1-θ)`,
stated forwards as `nx_θ^i(w_t) < w_0 + θ` — is free as soon as every position of the data is a
multiple of `1/n` and the offset `δ = (1-θ) - w_0` is at most `1/n`. That is the exact sense in
which "the braid depends on the entries only through the cell of the grid": one cell of the
`1/n`-grid has no room for another position.

The bound `δ ≤ 1/n` is not strict, and the boundary case is where `HJO.Braid.IsSpecialBraidData`
does the work: an iterate at exactly `1 - δ = w_0 + θ` would be carried by `HJO.Braid.nextCrossing`
onto `w_0` itself, and the distinctness clause of `HJO.Braid.IsSpecialBraidData` forbids two points
of the data sharing a position. This is also why the clause is only needed at the iterates a point
actually *moves* from, `i + 1 < β_t`: it is the *next* position that has to miss `w_0`.

For `HJO.Mellit.braidDataOfColouring` the grid is `1/(2D)` with `D = a(aN+1)N + b(aN+1)N - 1`, every
position being `Int.fract` of a point of the level line and every admissible level a half-integer,
while `δ = (η - aN)/D`; so `δ ≤ 1/(2D)` holds exactly at `η = aN + 1/2`, i.e. at
`HJO.Mellit.sepLevel`. -/
@[hjo "lem_mellit_append_cell"]
theorem gap_of_grid {θ δ : ℚ} {s : ℚ} {k n : ℕ} {w : Fin (k + 1) → ℚ} {β : Fin (k + 1) → ℕ}
    (hdata : IsSpecialBraidData s θ (k + 1) w β) (hn : 0 < n)
    (hgrid : ∀ (t : Fin (k + 1)) (i : ℕ), i < β t → ∃ m : ℤ,
      (nextCrossing θ)^[i] (w t) * (n : ℚ) = (m : ℚ))
    (hδ : 0 ≤ δ) (hδn : δ * (n : ℚ) ≤ 1) (hw0 : w 0 = 1 - θ - δ) :
    ∀ (t : Fin k) (i : ℕ), i + 1 < β t.succ →
      (nextCrossing θ)^[i] (w t.succ) < w 0 + θ := by
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  intro t i hi
  set x : ℚ := (nextCrossing θ)^[i] (w t.succ) with hxdef
  have hx1 : x < 1 := (hdata.iterate_mem_Ioo t.succ i (by omega)).2
  obtain ⟨m, hm⟩ := hgrid t.succ i (by omega)
  -- a multiple of `1/n` below `1` is at most `1 - 1/n`
  have hmn : (m : ℚ) < (n : ℚ) := by rw [← hm]; nlinarith
  have hmn' : (m : ℚ) ≤ (n : ℚ) - 1 := by
    have h1 : m < (n : ℤ) := by exact_mod_cast hmn
    have h2 : m + 1 ≤ (n : ℤ) := h1
    have h3 : ((m + 1 : ℤ) : ℚ) ≤ (((n : ℤ) : ℚ)) := by exact_mod_cast h2
    push_cast at h3
    linarith
  have hxle : x * (n : ℚ) ≤ (n : ℚ) - 1 := by rw [hm]; exact hmn'
  rw [hw0, show (1 : ℚ) - θ - δ + θ = 1 - δ from by ring]
  rcases lt_or_ge x (1 - δ) with h | h
  · exact h
  -- the boundary: `x = 1 - δ` would put the next position on `w 0`
  exfalso
  have hxeq : x = 1 - δ := by nlinarith
  have hw0pos : 0 < w 0 := (hdata.mem_Ioo 0).1
  have hδθ : (0 : ℚ) < 1 - θ - δ := by rw [← hw0]; exact hw0pos
  have hxθ : θ < x := by rw [hxeq]; linarith
  have hnext : (nextCrossing θ)^[i + 1] (w t.succ) = (nextCrossing θ)^[0] (w 0) := by
    rw [Function.iterate_succ_apply', ← hxdef, nextCrossing_of_gt hxθ, hxeq, hw0,
      Function.iterate_zero_apply]
    ring
  exact absurd (hdata.injective t.succ 0 (i + 1) 0 hi (hdata.one_le_mult 0) hnext).1
    (Fin.succ_ne_zero t)

/-! ### One turn's worth of letters -/

/-- **The letters of one turn, read as a prefix of `HJO.Braid.slopeBraid`.** The `t`-th prefix is
`λ(t)λ(t-1)⋯λ(1)` with `𝗒 ↦ y_1` and `𝗓 ↦ z_1`; at `t = a+b-2` it is the slope braid itself
(`HJO.Braid.slopeBraidPrefix_top`). -/
def slopeBraidPrefix (K a b : ℕ) : ℕ → BraidMonoid K
  | 0 => 1
  | t + 1 =>
    (match Mellit.slopeLetter a b (t + 1) with
      | Mellit.SlopeLetter.y => braidGenY K 1
      | Mellit.SlopeLetter.z => braidGenZ K 1) * slopeBraidPrefix K a b t

theorem slopeBraidPrefix_eq_prod (K a b : ℕ) : ∀ t : ℕ,
    slopeBraidPrefix K a b t
      = (((List.range t).map fun i => Mellit.slopeLetter a b (t - i)).map fun l =>
          match l with
          | Mellit.SlopeLetter.y => braidGenY K 1
          | Mellit.SlopeLetter.z => braidGenZ K 1).prod := by
  intro t
  induction t with
  | zero => simp [slopeBraidPrefix]
  | succ t ih =>
    rw [slopeBraidPrefix, ih, List.range_succ_eq_map]
    simp [List.map_map, Function.comp_def]

/-- The full prefix is `HJO.Braid.slopeBraid`: both are the product over `List.range (a+b-2)` of
`λ(a+b-2-i)`. -/
theorem slopeBraidPrefix_top (K a b : ℕ) :
    slopeBraidPrefix K a b (a + b - 2) = slopeBraid K a b := by
  rw [slopeBraidPrefix_eq_prod, slopeBraid, Mellit.slopeWord]
  rfl

/-- The factor separating two consecutive turns: the exception's `z` at rank `k+1` and the round's
`ỹ_{k+1}`, conjugated. This is Mellit's `ỹ_{k+1}z_{k+1}`, and it is the `y_1z_1T_{1↗k+1}` of a round
of `HJO.Braid.appendRhs` with the extra `T_{k+1↘1}` that the next turn's train absorbs. -/
def roundFactor (K : ℕ) : BraidMonoid K :=
  braidGenY K 1 * (braidGenZ K 1 * (braidTrainUp K 1 K * braidTrainDown K K 1))

namespace IsAppendSetup

variable {a b A k : ℕ} {e δ θ : ℚ} {w : Fin (k + 1) → ℚ} (H : IsAppendSetup a b A k e δ θ w)

include H

/-- The number of moves of the appended point, `β_{k+1} - 1 = Ad - 2`. -/
def runLength (_H : IsAppendSetup a b A k e δ θ w) : ℕ := A * (a + b) - 2

theorem two_le_mul : 2 ≤ A * (a + b) :=
  calc 2 ≤ 1 * (a + b) := by have := H.one_le_a; have := H.one_le_b; omega
    _ ≤ A * (a + b) := Nat.mul_le_mul_right _ H.one_le_A

theorem runLength_add_two : (H.runLength : ℚ) + 2 = ((A * (a + b) : ℕ) : ℚ) := by
  have h : H.runLength + 2 = A * (a + b) := by
    have := H.two_le_mul
    rw [runLength]
    omega
  calc (H.runLength : ℚ) + 2 = ((H.runLength + 2 : ℕ) : ℚ) := by push_cast; ring
    _ = ((A * (a + b) : ℕ) : ℚ) := by rw [h]

theorem denom_pos : (0 : ℚ) < (a : ℚ) + b := by
  have := H.one_le_b
  positivity

theorem denom_ne : ((a : ℚ) + b) ≠ 0 := ne_of_gt H.denom_pos

/-- The smallness hypothesis of `HJO/Shuffle/SlopeTrajectory.lean`, at the offset `δ`. -/
theorem small : ((H.runLength : ℚ) + 2) * e + δ < 1 / ((a : ℚ) + b) := by
  rw [H.runLength_add_two]
  exact H.drift

theorem two_e_pos : (0 : ℚ) < 2 * e + δ := by
  have := H.e_pos
  have := H.delta_nonneg
  linarith

/-- The appended point's position after `j` moves, in closed form. -/
theorem moveTuple_eq {j : ℕ} (hj : j ≤ H.runLength) :
    moveTuple θ w (List.replicate j (0 : Fin (k + 1)))
      = Function.update w 0 (trajPos a b e δ j) := by
  have h := iterate_nextCrossing_eq_trajPos H.one_le_a H.one_le_b H.theta_eq H.e_pos.le
    H.two_e_pos H.small j hj
  rw [moveTuple_replicate, H.start, h]

/-! ### The three cases -/

/-- A step whose residue is below `b` crosses the horizontal wall, so it lies above `θ` and hence
above the whole cluster: rank `k+1`. -/
theorem entryRank_eq_succ_of_lt {j : ℕ} (hj : j ≤ H.runLength)
    (hres : slopeResidue a b (j + 1) < b) :
    entryRank (Function.update w 0 (trajPos a b e δ j)) 0 = k + 1 := by
  have hgt : θ < trajPos a b e δ j :=
    (theta_lt_trajPos_iff H.one_le_b H.theta_eq H.e_pos.le H.two_e_pos hj H.small).2 hres
  refine entryRank_update_eq_succ_of_forall_lt fun t => ?_
  have h1 := H.cluster_hi t
  have h2 : (0 : ℚ) ≤ ((A * (a + b) : ℕ) : ℚ) * e :=
    mul_nonneg (Nat.cast_nonneg _) H.e_pos.le
  have h3 := H.delta_nonneg
  linarith

/-- The position at a step whose residue is exactly `b`: the grid point is `a/d`, so the position is
`θ - (j+2)e`. That step is the passage next to the finish. -/
theorem trajPos_eq_of_res_eq {j : ℕ} (hres : slopeResidue a b (j + 1) = b) :
    trajPos a b e δ j = θ - (((j : ℚ) + 2) * e + δ) := by
  have hD := H.denom_ne
  rw [trajPos, hres, H.theta_eq]
  field_simp
  ring

/-- A step whose residue is exactly `b` is the passage next to the finish, and `cluster_hi` puts its
position above the whole cluster: rank `k+1`, Mellit's exception. -/
theorem entryRank_eq_succ_of_eq {j : ℕ} (hj : j ≤ H.runLength)
    (hres : slopeResidue a b (j + 1) = b) :
    entryRank (Function.update w 0 (trajPos a b e δ j)) 0 = k + 1 := by
  refine entryRank_update_eq_succ_of_forall_lt fun t => ?_
  have h1 := H.cluster_hi t
  have hle : ((j : ℚ) + 2) * e ≤ ((A * (a + b) : ℕ) : ℚ) * e := by
    refine mul_le_mul_of_nonneg_right ?_ H.e_pos.le
    rw [← H.runLength_add_two]
    have : (j : ℚ) ≤ (H.runLength : ℚ) := Nat.cast_le.2 hj
    linarith
  rw [H.trajPos_eq_of_res_eq hres]
  linarith

/-- A step whose residue exceeds `b` crosses the vertical wall away from the finish: its grid point
is at most `(a-1)/d`, which `cluster_lo` puts below the whole cluster. Rank `1`. -/
theorem entryRank_eq_one_of_gt {j : ℕ} (hres : b < slopeResidue a b (j + 1)) :
    entryRank (Function.update w 0 (trajPos a b e δ j)) 0 = 1 := by
  have hD := H.denom_pos
  have hDne := H.denom_ne
  refine entryRank_update_eq_one_of_forall_lt fun t => ?_
  have hw := H.cluster_lo t
  have hcast : ((b : ℚ) + 1) ≤ (slopeResidue a b (j + 1) : ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt hres
  -- both sides cleared of the denominator `a + b`
  have hL : trajPos a b e δ j * ((a : ℚ) + b)
      = (a : ℚ) + b - (slopeResidue a b (j + 1) : ℚ)
        - (((j : ℚ) + 1) * e + δ) * ((a : ℚ) + b) := by
    rw [trajPos]
    field_simp
  have hR : (θ - 1 / ((a : ℚ) + b)) * ((a : ℚ) + b) = (a : ℚ) - 1 + e * ((a : ℚ) + b) := by
    rw [H.theta_eq]
    field_simp
    ring
  have hdrift : (0 : ℚ) ≤ (((j : ℚ) + 1) * e + δ) * ((a : ℚ) + b) := by
    have h1 : (0 : ℚ) ≤ ((j : ℚ) + 1) * e := mul_nonneg (by positivity) H.e_pos.le
    have h2 := H.delta_nonneg
    exact mul_nonneg (by linarith) hD.le
  have hepos : (0 : ℚ) < e * ((a : ℚ) + b) := mul_pos H.e_pos hD
  have hstep : trajPos a b e δ j * ((a : ℚ) + b) < (θ - 1 / ((a : ℚ) + b)) * ((a : ℚ) + b) := by
    rw [hL, hR]
    linarith
  have := lt_of_mul_lt_mul_right hstep hD.le
  linarith

/-! ### The conjugated letter of each step -/

theorem trajPos_lt_theta_of_le {j : ℕ} (hj : j ≤ H.runLength)
    (hres : b ≤ slopeResidue a b (j + 1)) : trajPos a b e δ j < θ :=
  (trajPos_lt_theta_iff H.one_le_b H.theta_eq H.e_pos.le H.two_e_pos hj H.small).2 hres

/-- **A step across the horizontal wall contributes `y_1`.** The residue is below `b`, so the point
is above `θ` and at rank `k+1`, the letter is `ỹ_{k+1}`, and
`HJO.Braid.trainDown_mul_braidYtilde_top_mul_trainDown` turns the conjugate of that into `y_1` —
exactly the letter `HJO.Braid.slopeBraid` reads for `𝗒`. -/
theorem conjRun_succ_eq_y {j : ℕ} (hj : j ≤ H.runLength) (hres : slopeResidue a b (j + 1) < b) :
    conjRun θ w 0 (j + 1) = braidGenY (k + 1) 1 * conjRun θ w 0 j := by
  have hgt : θ < trajPos a b e δ j :=
    (theta_lt_trajPos_iff H.one_le_b H.theta_eq H.e_pos.le H.two_e_pos hj H.small).2 hres
  rw [conjRun, H.moveTuple_eq hj, Function.update_self, H.entryRank_eq_succ_of_lt hj hres]
  rw [show (if trajPos a b e δ j < θ then braidGenZ (k + 1) (k + 1)
      else braidYtilde (k + 1) (k + 1)) = braidYtilde (k + 1) (k + 1) from by
    simp [not_lt.2 hgt.le]]
  rw [trainDown_mul_braidYtilde_top_mul_trainDown (Nat.le_add_left 1 k)]

/-- **A step across the vertical wall away from the finish contributes `z_1`.** The residue exceeds
`b`, so the point is below `θ` and at rank `1`, where the two conjugating trains are empty and the
letter is a bare `z_1` — exactly the letter `HJO.Braid.slopeBraid` reads for `𝗓`. -/
theorem conjRun_succ_eq_z {j : ℕ} (hj : j ≤ H.runLength) (hres : b < slopeResidue a b (j + 1)) :
    conjRun θ w 0 (j + 1) = braidGenZ (k + 1) 1 * conjRun θ w 0 j := by
  have hlt : trajPos a b e δ j < θ := H.trajPos_lt_theta_of_le hj (le_of_lt hres)
  rw [conjRun, H.moveTuple_eq hj, Function.update_self, H.entryRank_eq_one_of_gt hres]
  rw [show (if trajPos a b e δ j < θ then braidGenZ (k + 1) 1
      else braidYtilde (k + 1) 1) = braidGenZ (k + 1) 1 from by simp [hlt]]
  rw [braidTrainDown_self, one_mul, mul_one]

/-- **The passage next to the finish contributes `z_1·T_{1↗k+1}T_{k+1↘1}`.** The residue is exactly
`b`, which by `HJO.Mellit.slopeResidue_top` happens once per turn, and there the point is below `θ`
but *above* the whole cluster, so its rank is `k+1` and not `1`: Mellit's exception. The two
trains do not cancel, and they are the `T_{1↗k+1}` standing at the right-hand end of each round of
`HJO.Braid.appendRhs`. -/
theorem conjRun_succ_eq_z_finish {j : ℕ} (hj : j ≤ H.runLength)
    (hres : slopeResidue a b (j + 1) = b) :
    conjRun θ w 0 (j + 1)
      = braidGenZ (k + 1) 1 * (braidTrainUp (k + 1) 1 (k + 1) * braidTrainDown (k + 1) (k + 1) 1) *
        conjRun θ w 0 j := by
  have hlt : trajPos a b e δ j < θ := H.trajPos_lt_theta_of_le hj (le_of_eq hres.symm)
  rw [conjRun, H.moveTuple_eq hj, Function.update_self, H.entryRank_eq_succ_of_eq hj hres]
  rw [show (if trajPos a b e δ j < θ then braidGenZ (k + 1) (k + 1)
      else braidYtilde (k + 1) (k + 1)) = braidGenZ (k + 1) (k + 1) from by simp [hlt]]
  rw [trainDown_mul_braidGenZ_top_mul_trainDown (Nat.le_add_left 1 k)]

/-- **Away from the finish the step contributes exactly the slope word's letter.** The two cases of
`HJO.Mellit.slopeLetter` combined: `𝗒 ↦ y_1` and `𝗓 ↦ z_1`, which is the map
`HJO.Braid.slopeBraid` applies. The hypothesis `ϱ ≠ b` is what
`HJO.Mellit.slopeResidue_ne` supplies on the range `1 ≤ i ≤ a+b-2` that the slope word uses. -/
theorem conjRun_succ_eq_slopeLetter {j : ℕ} (hj : j ≤ H.runLength)
    (hres : slopeResidue a b (j + 1) ≠ b) :
    conjRun θ w 0 (j + 1)
      = (match slopeLetter a b (j + 1) with
          | SlopeLetter.y => braidGenY (k + 1) 1
          | SlopeLetter.z => braidGenZ (k + 1) 1) * conjRun θ w 0 j := by
  rcases lt_or_gt_of_ne hres with h | h
  · rw [H.conjRun_succ_eq_y hj h, (slopeLetter_eq_y_iff a b (j + 1)).2 h]
  · rw [H.conjRun_succ_eq_z hj h, (slopeLetter_eq_z_iff a b (j + 1)).2 (le_of_lt h)]

/-- **A block of `a+b-2` consecutive steps beginning at a multiple of `a+b` contributes the letters
of the slope word.** The residue is periodic, so step `N + r` carries the letter `λ(r+1)`, and
`HJO.Mellit.slopeResidue_ne` keeps every one of those away from the exceptional residue `b`. -/
theorem conjRun_add_eq_prefix_mul {N : ℕ} (hN : (a + b) ∣ N) : ∀ t : ℕ, t ≤ a + b - 2 →
    N + t ≤ H.runLength →
    conjRun θ w 0 (N + t) = slopeBraidPrefix (k + 1) a b t * conjRun θ w 0 N := by
  obtain ⟨q, hq⟩ := hN
  intro t
  induction t with
  | zero => simp [slopeBraidPrefix]
  | succ t ih =>
    intro ht hle
    have hres : Mellit.slopeResidue a b (N + t + 1) = Mellit.slopeResidue a b (t + 1) := by
      rw [hq, show (a + b) * q + t + 1 = t + 1 + q * (a + b) from by ring,
        Mellit.slopeResidue_add_mul]
    have hne : Mellit.slopeResidue a b (N + t + 1) ≠ b := by
      rw [hres]
      exact Mellit.slopeResidue_ne H.coprime H.one_le_a H.one_le_b (by omega) (by omega)
    have hletter : Mellit.slopeLetter a b (N + t + 1) = Mellit.slopeLetter a b (t + 1) := by
      rw [Mellit.slopeLetter, Mellit.slopeLetter, hres]
    rw [show N + (t + 1) = N + t + 1 from by ring,
      H.conjRun_succ_eq_slopeLetter (by omega) hne, hletter, slopeBraidPrefix,
      ih (by omega) (by omega), mul_assoc]
/-! ### The turns -/

/-- **The whole run of the appended point, after `q` turns.**
`conjRun = b_{a,b}·(roundFactor·b_{a,b})^{q-1}`: each turn contributes the `a+b-2` letters of the
slope word, and every turn but the last is followed by the exception's `z` and the round's `ỹ`. -/
theorem conjRun_turns : ∀ q : ℕ, 1 ≤ q → q ≤ A →
    conjRun θ w 0 (q * (a + b) - 2)
      = slopeBraid (k + 1) a b * (roundFactor (k + 1) * slopeBraid (k + 1) a b) ^ (q - 1) := by
  have hab : 2 ≤ a + b := by have := H.one_le_a; have := H.one_le_b; omega
  have hrun : H.runLength = A * (a + b) - 2 := rfl
  intro q hq
  induction q, hq using Nat.le_induction with
  | base =>
    intro hA
    have hAle : a + b ≤ A * (a + b) := Nat.le_mul_of_pos_left _ (by omega)
    have h : 1 * (a + b) - 2 = 0 + (a + b - 2) := by omega
    rw [h, H.conjRun_add_eq_prefix_mul (dvd_zero _) _ le_rfl (by rw [hrun]; omega),
      slopeBraidPrefix_top, conjRun_zero, mul_one, Nat.sub_self, pow_zero, mul_one]
  | succ q hq ih =>
    intro hA
    have hqA : q ≤ A := by omega
    have hqd : 2 ≤ q * (a + b) := by
      calc 2 ≤ 1 * (a + b) := by omega
        _ ≤ q * (a + b) := Nat.mul_le_mul_right _ hq
    -- the exception's `z`, at `q(a+b) - 1`
    have hresz : Mellit.slopeResidue a b (q * (a + b) - 2 + 1) = b := by
      have hidx : q * (a + b) - 2 + 1 = (a + b - 1) + (q - 1) * (a + b) := by
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        have h1 : (q' + 1) * (a + b) = q' * (a + b) + (a + b) := by ring
        simp only [Nat.add_sub_cancel]
        omega
      rw [hidx, Mellit.slopeResidue_add_mul,
        Mellit.slopeResidue_top H.one_le_a H.one_le_b]
    -- the round's `ỹ`, at `q(a+b)`
    have hresy : Mellit.slopeResidue a b (q * (a + b) - 2 + 1 + 1) < b := by
      have hidx : q * (a + b) - 2 + 1 + 1 = q * (a + b) := by omega
      rw [hidx, Mellit.slopeResidue_mul]
      exact H.one_le_b
    have hb1 : q * (a + b) - 2 ≤ H.runLength := by
      rw [hrun]
      have : q * (a + b) ≤ A * (a + b) := Nat.mul_le_mul_right _ hqA
      omega
    have hb2 : q * (a + b) - 2 + 1 ≤ H.runLength := by
      rw [hrun]
      have : (q + 1) * (a + b) ≤ A * (a + b) := Nat.mul_le_mul_right _ hA
      have h2 : (q + 1) * (a + b) = q * (a + b) + (a + b) := by ring
      omega
    have hstep1 := H.conjRun_succ_eq_z_finish hb1 hresz
    have hstep2 := H.conjRun_succ_eq_y hb2 hresy
    -- the next turn's own letters
    have hdvd : (a + b) ∣ q * (a + b) := dvd_mul_left (a + b) q
    have hidx : q * (a + b) - 2 + 1 + 1 = q * (a + b) := by omega
    have hblock := H.conjRun_add_eq_prefix_mul hdvd (a + b - 2) le_rfl
      (by rw [hrun]
          have : (q + 1) * (a + b) ≤ A * (a + b) := Nat.mul_le_mul_right _ hA
          have h2 : (q + 1) * (a + b) = q * (a + b) + (a + b) := by ring
          omega)
    have hfinal : (q + 1) * (a + b) - 2 = q * (a + b) + (a + b - 2) := by
      have : (q + 1) * (a + b) = q * (a + b) + (a + b) := by ring
      omega
    rw [hfinal, hblock, slopeBraidPrefix_top, ← hidx, hstep2, hstep1, ih hqA,
      Nat.add_sub_cancel]
    conv_rhs => rw [show q = q - 1 + 1 from by omega]
    rw [pow_succ']
    simp only [roundFactor, mul_assoc]

end IsAppendSetup

/-! ### The braid of the appended composition -/

/-- `x(yx)^n = (xy)^n x`, the regrouping that turns the run's single outer train into one train per
round. -/
theorem mul_mul_pow_comm {M : Type*} [Monoid M] (x y : M) :
    ∀ n : ℕ, x * (y * x) ^ n = (x * y) ^ n * x
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, pow_succ, ← mul_assoc, mul_mul_pow_comm x y n]
    simp only [mul_assoc]

namespace IsAppendSetup

variable {a b A k : ℕ} {e δ θ : ℚ} {w : Fin (k + 1) → ℚ} (H : IsAppendSetup a b A k e δ θ w)

include H

/-- **The start lies above the finish**, `θ < 1 - θ`: the standing `a < b` with the drift bound.
This is what selects the second case, `finish < start`, of Mellit's case distinction, the one
`HJO.Braid.appendRhs` is built on. -/
theorem theta_lt_one_sub : θ < 1 - θ := by
  have hD := H.denom_pos
  have hDne := H.denom_ne
  have hab : 2 ≤ a + b := by have := H.one_le_a; have := H.one_le_b; omega
  have h2e : 2 * e ≤ ((A * (a + b) : ℕ) : ℚ) * e := by
    refine mul_le_mul_of_nonneg_right ?_ H.e_pos.le
    have : 2 ≤ A * (a + b) := H.two_le_mul
    exact_mod_cast this
  have hgap : (1 : ℚ) / ((a : ℚ) + b) ≤ ((b : ℚ) - a) / ((a : ℚ) + b) := by
    have h1 : (1 : ℚ) ≤ (b : ℚ) - a := by
      have : ((a : ℚ) + 1) ≤ (b : ℚ) := by exact_mod_cast H.a_lt_b
      linarith
    have := mul_le_mul_of_nonneg_right h1 (le_of_lt (inv_pos.2 hD))
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linarith
  have hkey : 2 * e < ((b : ℚ) - a) / ((a : ℚ) + b) := by
    have := H.drift
    have := H.delta_nonneg
    linarith
  rw [H.theta_eq]
  have hsplit : ((b : ℚ) - a) / ((a : ℚ) + b)
      = 1 - (a : ℚ) / ((a : ℚ) + b) - (a : ℚ) / ((a : ℚ) + b) := by
    field_simp
    ring
  rw [hsplit] at hkey
  linarith

/-- The whole run of the appended point, at `q = A`. -/
theorem conjRun_runLength :
    conjRun θ w 0 H.runLength
      = slopeBraid (k + 1) a b * (roundFactor (k + 1) * slopeBraid (k + 1) a b) ^ (A - 1) := by
  have h : H.runLength = A * (a + b) - 2 := rfl
  rw [h, H.conjRun_turns A H.one_le_A le_rfl]

/-- **The rank of the appended point at the start of its run is `k+1`**: it stands at `1 - θ`, which
is above `θ` and so above the whole cluster. -/
theorem entryRank_start : entryRank w 0 = k + 1 := by
  refine entryRank_zero_of_forall_lt fun t => ?_
  have h1 := H.cluster_hi t
  have h2 : (0 : ℚ) ≤ ((A * (a + b) : ℕ) : ℚ) * e :=
    mul_nonneg (Nat.cast_nonneg _) H.e_pos.le
  have h3 := H.theta_lt_one_sub
  rw [H.start]
  linarith

/-- **The rank of the appended point at the end of its run is `k+1`**: its last position is next to
the finish, where `cluster_hi` puts it above the whole cluster. -/
theorem entryRank_finish :
    entryRank (moveTuple θ w (List.replicate H.runLength (0 : Fin (k + 1)))) 0 = k + 1 := by
  have hab : 2 ≤ a + b := by have := H.one_le_a; have := H.one_le_b; omega
  have hres : Mellit.slopeResidue a b (H.runLength + 1) = b := by
    have hidx : H.runLength + 1 = (a + b - 1) + (A - 1) * (a + b) := by
      have h2 := H.two_le_mul
      have hA := H.one_le_A
      obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
      have h1 : (A' + 1) * (a + b) = A' * (a + b) + (a + b) := by ring
      simp only [Nat.add_sub_cancel]
      rw [runLength]
      omega
    rw [hidx, Mellit.slopeResidue_add_mul, Mellit.slopeResidue_top H.one_le_a H.one_le_b]
  rw [H.moveTuple_eq le_rfl]
  exact H.entryRank_eq_succ_of_eq le_rfl hres

/-- **`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`.** For special-braid data `(w₀, β)` of
rank `k+1` whose appended point — of index `0`, not `k+1`; see the docstring of
`HJO/Shuffle/BraidAppendPart.lean` — stands at Mellit's start `1 - θ`, lies above every
other entry, and carries the part `β_0 = A(a+b) - 1`,

`B_{s,w₀,β} = (T_{k+1↘1} b_{a,b} y_1 z_1 T_{1↗k+1})^{A-1} T_{k+1↘1} b_{a,b} φ*₊(B_{s,v,α})
T_{1↘k+1}`

with `(v, α) = (w₀ ∘ Fin.succ, β ∘ Fin.succ)` the deleted rank-`k` data.

**Where the clustering hypothesis sits.** `H` is `HJO.Braid.IsAppendSetup` at the tuple `w`, and
`hmove` says `w` is `w₀` after the *other* points have made all of their moves. So `w t.succ` is the
final position `f_t = nx_θ^{α_t-1}(v_t)` of `HJO.Braid.positionPair` — the proof below derives that
identification — and `H.cluster_lo`, `H.cluster_hi` are therefore `θ - 1/d < f_t < θ - (Ad)e`,
Mellit's clustering at the finish. `H.drift` is `(Ad)e < 1/d`. The `IsSpecialBraidData` hypothesis
ties `θ` to `s` by `θ(s+1) = 1`, and `H.theta_eq` writes `θ = a/d + e`; together they are the
consumer's `s = b/a - ε`.

The right-hand side is `HJO.Braid.appendRhs`, the very element that, by
`HJO.Braid.eq_one_and_add_eq_two_of_specialBraid_eq_appendRhs`, the left-hand side cannot equal at
the naive part `β_0 = A`; at the corrected part `β_0 = A(a+b) - 1` it is a theorem, and by
`HJO.Braid.letterCount_specialBraid_eq_letterCount_appendRhs_iff` that is the only part at which it
could have been one.

The case `k = 0`, which this statement does not cover and the consumer needs, is
`HJO.Braid.IsAppendSetup.specialBraid_eq_slopeBraid_pow'`. -/
@[hjo "lem_mellit_braid_composition"]
theorem specialBraid_eq_appendRhs {s : ℚ} {w₀ : Fin (k + 1) → ℚ} {β : Fin (k + 1) → ℕ}
    (hk : 1 ≤ k)
    (hdata : IsSpecialBraidData s θ (k + 1) w₀ β) (hβ : β 0 = A * (a + b) - 1)
    (hw₀ : w₀ 0 = 1 - θ - δ)
    (hgap : ∀ (t : Fin k) (i : ℕ), i + 1 < β t.succ →
      (nextCrossing θ)^[i] (w₀ t.succ) < w₀ 0 + θ)
    (hstart : ∀ t : Fin k, w₀ t.succ < w₀ 0)
    (hmove : moveTuple θ w₀ ((specialMoveList (β ∘ Fin.succ)).map Fin.succ) = w) :
    specialBraid θ w₀ β
      = appendRhs θ hk A a b (w₀ ∘ Fin.succ) (β ∘ Fin.succ) := by
  have hab : 2 ≤ a + b := by have := H.one_le_a; have := H.one_le_b; omega
  have hmul := H.two_le_mul
  -- the finish domination, from the cluster and `θ < 1 - θ`
  have hfin : ∀ t : Fin k, (positionPair θ (w₀ ∘ Fin.succ) (β ∘ Fin.succ)).2 t < w₀ 0 := by
    intro t
    have hEq : moveTuple θ w₀ ((specialMoveList (β ∘ Fin.succ)).map Fin.succ) t.succ
        = (positionPair θ (w₀ ∘ Fin.succ) (β ∘ Fin.succ)).2 t := by
      have h := congrFun (moveTuple_comp_succAbove (θ := θ) w₀ 0 (specialMoveList (β ∘ Fin.succ))) t
      simp only [Fin.succAbove_zero, Function.comp_apply] at h
      rw [h, moveTuple_specialMoveList]
    rw [← hEq, hmove, hw₀]
    have h1 := H.cluster_hi t
    have h2 : (0 : ℚ) ≤ ((A * (a + b) : ℕ) : ℚ) * e :=
      mul_nonneg (Nat.cast_nonneg _) H.e_pos.le
    have h3 := H.theta_lt_one_sub
    linarith
  -- the factorisation of `HJO/Shuffle/BraidAppendPart.lean`
  have hle : w₀ 0 ≤ 1 - θ := by rw [hw₀]; have := H.delta_nonneg; linarith
  have hsplit := specialBraid_eq_conj_phiPlusStar hk w₀ β hdata hle hgap hstart hfin
  -- the run's trains come out to the ends
  have hlen : β 0 - 1 = H.runLength := by rw [hβ, runLength]; omega
  have hrun := braidWord_replicate_mul_trainDown_one (Nat.le_add_left 1 k) θ w 0 H.runLength
  rw [H.entryRank_start, H.entryRank_finish, H.conjRun_runLength] at hrun
  -- assemble
  rw [hsplit, hmove, hlen, hrun, appendRhs, roundFactor]
  -- the single outer train becomes one train per round, `x(yx)^n = (xy)^n x`
  set S := slopeBraid (k + 1) a b
  set TD := braidTrainDown (k + 1) (k + 1) 1
  set TU := braidTrainUp (k + 1) 1 (k + 1)
  set Y := braidGenY (k + 1) 1
  set Z := braidGenZ (k + 1) 1
  have hkey : TD * (S * (Y * (Z * (TU * TD)) * S) ^ (A - 1))
      = (TD * S * Y * Z * TU) ^ (A - 1) * (TD * S) := by
    have h1 : Y * (Z * (TU * TD)) * S = Y * Z * TU * (TD * S) := by simp only [mul_assoc]
    have h2 : TD * S * Y * Z * TU = TD * S * (Y * Z * TU) := by simp only [mul_assoc]
    rw [h1, h2, ← mul_assoc]
    exact mul_mul_pow_comm (TD * S) (Y * Z * TU) (A - 1)
  rw [hkey]
  simp only [mul_assoc]

/-! ### The hypotheses are not vacuous

A bundle of inequalities can be inconsistent, and then the theorem above says nothing. Here is a
witness: `(a,b) = (2,3)`, one turn, one other point, `e = 1/1000`, so `θ = 401/1000`, the appended
point **strictly below** the start at `598/1000 = (1-θ) - 1/1000` and the other point's final
position at `3/10`, inside the window `(θ - 1/5, θ - (5e + δ)) = (201/1000, 395/1000)`. The window
is nonempty exactly because of the drift bound, `(Ad)e + δ < 1/d`, so it is nonempty in general and
not only here; taking `δ = 1/1000 > 0` also witnesses that the widened hypotheses are consistent
with the appended entry being where a consumer actually finds it, rather than only at `1-θ`. -/
omit H in
theorem isAppendSetup_example :
    IsAppendSetup 2 3 1 1 (1 / 1000) (1 / 1000) (401 / 1000)
      (fun i => if i = 0 then 598 / 1000 else 3 / 10) where
  one_le_a := by norm_num
  one_le_b := by norm_num
  coprime := by decide
  a_lt_b := by norm_num
  one_le_A := by norm_num
  e_pos := by norm_num
  delta_nonneg := by norm_num
  theta_eq := by norm_num
  drift := by norm_num
  start := by norm_num
  cluster_lo t := by
    have : (t.succ : Fin 2) ≠ 0 := Fin.succ_ne_zero t
    norm_num [this]
  cluster_hi t := by
    have : (t.succ : Fin 2) ≠ 0 := Fin.succ_ne_zero t
    norm_num [this]

/-! ### The base case `k = 0` -/

omit H in
/-- **`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` at `k = 0`**, where there are no other
points and the factor `φ*₊(B_{s,v,α})` of `HJO.Braid.appendRhs` and all four trains are the
identity: `B_{s,w,β} = b^{(A)}_{a,b}`, Mellit's one-strand braid `(b_{a,b}y_1z_1)^{A-1}b_{a,b}`.

The consumer needs this case — `HJO.Mellit.braidRep_specialBraid_dplusIter` runs at `k = ℓ - 1` and
`ℓ = 1` occurs — and `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` does not cover it,
`HJO.Braid.phiPlusStar` being defined only for `k ≥ 1`. Nothing of the geometry is needed here: with
one point every rank is `1`, so `HJO.Braid.braidWord_replicate_mul_trainDown_one` has no trains to
move and the letters are the bare ones `HJO.Braid.slopeBraid` reads. -/
theorem specialBraid_eq_slopeBraid_pow {a b A : ℕ} {e δ θ : ℚ} {w : Fin 1 → ℚ}
    (H : IsAppendSetup a b A 0 e δ θ w) {β : Fin 1 → ℕ} (hβ : β 0 = A * (a + b) - 1) :
    specialBraid θ w β
      = slopeBraid 1 a b * (braidGenY 1 1 * braidGenZ 1 1 * slopeBraid 1 a b) ^ (A - 1) := by
  have hlen : β 0 - 1 = H.runLength := by
    have := H.two_le_mul
    rw [hβ, runLength]
    omega
  have hmoves : specialMoveList β = List.replicate (β 0 - 1) (0 : Fin 1) := by
    rw [specialMoveList, show List.finRange 1 = [(0 : Fin 1)] from rfl]
    simp
  have hrun := braidWord_replicate_mul_trainDown_one (le_refl 1) θ w 0 H.runLength
  rw [H.entryRank_start, H.entryRank_finish, H.conjRun_runLength] at hrun
  simp only [Nat.zero_add, roundFactor, braidTrainDown_self, braidTrainUp_self, mul_one,
    one_mul] at hrun
  rw [specialBraid, hmoves, hlen, hrun]

omit H in
/-- Mellit's own form of the base case, `b^{(A)}_{a,b} = (b_{a,b}y_1z_1)^{A-1}b_{a,b}`
(Section 6), which is `HJO.Braid.IsAppendSetup.specialBraid_eq_slopeBraid_pow` regrouped
by `HJO.Braid.mul_mul_pow_comm`. -/
@[hjo "lem_mellit_braid_composition"]
theorem specialBraid_eq_slopeBraid_pow' {a b A : ℕ} {e δ θ : ℚ} {w : Fin 1 → ℚ}
    (H : IsAppendSetup a b A 0 e δ θ w) {β : Fin 1 → ℕ} (hβ : β 0 = A * (a + b) - 1) :
    specialBraid θ w β
      = (slopeBraid 1 a b * braidGenY 1 1 * braidGenZ 1 1) ^ (A - 1) * slopeBraid 1 a b := by
  rw [H.specialBraid_eq_slopeBraid_pow hβ,
    show slopeBraid 1 a b * braidGenY 1 1 * braidGenZ 1 1
      = slopeBraid 1 a b * (braidGenY 1 1 * braidGenZ 1 1) from by simp only [mul_assoc]]
  exact mul_mul_pow_comm (slopeBraid 1 a b) (braidGenY 1 1 * braidGenZ 1 1) (A - 1)

end IsAppendSetup

end HJO.Braid

end
