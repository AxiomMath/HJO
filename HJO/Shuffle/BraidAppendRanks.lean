/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidAppendPart
public meta import HJO.Attr

/-! # The rank of the moving point: the clustering hypothesis of Mellit's Section 6

The second half of the geometry of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`.
`HJO/Shuffle/BraidAppendPart.lean` reduces that statement to the appended point's own run of moves;
what remains is to read off the *letters* of that run, and each letter is `HJO.Braid.braidStep` at
the appended point's rank. That statement asserts

> each crossing of the vertical wall occurring at position `1` and each crossing of the horizontal
> wall at position `k+1` except at the passage next to the finish

and its naive hypothesis — the entries and final positions of the rank-`k` data all below
`1 - θ` — does not give that claim: those are statements about where the other points *are*, while
the claim is about the rank of the moving point at each of its `β_{k+1} - 1` intermediate positions
`nx_θ^j(w_{k+1})`, which range over the whole of `(0,1)`. The other points sit at their final
positions while the new one moves, and a trajectory merely below `1 - θ` passes straight through
them.

## The hypothesis Mellit actually makes

A. Mellit, *Toric braids and `(m,n)`-parking functions*, section 6:

> In the initial position all points are clustered close to the "start" at point `(1-t, t)`, and
> their labels are in the opposite order. In the final position all points are clustered close to
> "finish" at `(t, 1-t)`, and their labels are again in the opposite order.

and, of the one-strand braid `b_{m,n}`:

> which starts at `(1-t-ε, t+ε)`, travels at slope `s` downwards until it reaches a position at
> `(t-ε', 1-t+ε')` for a small `ε' > 0`

Both sentences are about the *antidiagonal coordinate*, which is `x` (`HJO.Braid.nextCrossing`
records a point of the torus on the antidiagonal by its first coordinate). Mellit's `t` is `θ`,
so the start is the coordinate `1 - θ` and the finish is the coordinate `θ`, and `b_{m,n}` both
starts and finishes *just below* those two values. So the clustering says: the other points' final
positions all lie just below `θ`, in a window short enough that the moving point's trajectory never
lands inside it.

That is what is stated below as `HJO.Braid.IsFinishCluster`, in the two clauses it is actually used
through:

* `finish_lt_theta` — every final position of the rank-`k` data is `< θ`;
* `avoids` — each of the moving point's positions is either below every final position or above
  every final position.

The second is "the cluster is short enough"; it needs no `min`/`max` and no metric, and at `k = 0`
it is vacuous.

## Why those two clauses give exactly Mellit's sentence, exception included

* A crossing of the *horizontal* wall is a position `> θ` (`HJO.Braid.braidStep`), and
  `finish_lt_theta` puts every other point below `θ`, hence below it: rank `k+1`. So
  `finish_lt_theta` alone disposes of every horizontal crossing —
  `HJO.Braid.entryRank_update_eq_succ_of_theta_lt`.
* A crossing of the *vertical* wall is a position `< θ`, and there `avoids` splits into the two
  cases of Mellit's own sentence: below the cluster gives rank `1`
  (`HJO.Braid.entryRank_update_eq_one_of_forall_lt`), and above the cluster — which by
  `finish_lt_theta` is the window `(max f, θ)` hugging the finish — gives rank `k+1`
  (`HJO.Braid.entryRank_update_eq_succ_of_forall_lt`). The second case is Mellit's

  > This holds with one exception: each time we are passing next to the finish, the position is
  > `k+1` instead of `1`.

So the exception is not an extra hypothesis; it is the upper branch of `avoids`, and it is forced
rather than assumed.

## Main results

* `HJO.Braid.IsFinishCluster` — the clustering hypothesis.
* `HJO.Braid.entryRank_update_eq_one_of_forall_lt`,
  `HJO.Braid.entryRank_update_eq_succ_of_forall_lt` — the two ranks, from the two branches.
* `HJO.Braid.entryRank_update_eq_succ_of_theta_lt` — every horizontal crossing is at rank `k+1`,
  from `finish_lt_theta` alone.
* `HJO.Braid.entryRank_moveTuple_replicate_eq_or` — under the hypothesis every intermediate rank
  of the moving point is `1` or `k+1`, so no rank between them ever occurs.
* `HJO.Braid.braidStep_moveTuple_replicate_eq` — the letter of the `j`-th move, with its train:
  `T_{r'↘r} z_r` or `T_{r'↘r} ỹ_r` with `r, r'` each `1` or `k+1`, and `ỹ` only at `k+1`. This
  is Mellit's "the rules produce combinations of `z_1`, `T_{k+1↘1}`, `ỹ_{k+1}`, `T_{1↗k+1}`".
* `HJO.Braid.conjRun`, `HJO.Braid.braidWord_replicate_mul_trainDown_one` — the whole run is one
  train at each end and a product of letters conjugated to rank `1`, which is the shape the
  right-hand side `HJO.Braid.appendRhs` has. Pure train algebra, `HJO.Braid.trainDown_mul_trainDown`
  at the base point; no clustering.
* `HJO.Braid.conjRun_succ_eq_of_finishCluster` — and under the clustering hypothesis each of those
  conjugated letters is one of exactly three elements, a bare `z_1` or a conjugate of `z_{k+1}` or
  of `ỹ_{k+1}`.
* `HJO.Braid.braidYtilde_top_eq`, `HJO.Braid.trainDown_mul_braidYtilde_top_mul_trainDown` — the
  conjugate of `ỹ_{k+1}` *is* `y_1`, the letter `HJO.Braid.slopeBraid` reads. This is what makes
  the right-hand side `HJO.Braid.appendRhs` a word in `y_1` and `z_1` at all.
* `HJO.Braid.trainDown_mul_braidGenZ_top_mul_trainDown` — the conjugate of `z_{k+1}` is `z_1`
  followed by the mixed pair `T_{1↗k+1}T_{k+1↘1}`, which does *not* cancel and is not meant to: it
  is the `T_{1↗k+1}` standing at the right-hand end of each round of `HJO.Braid.appendRhs`.

## What separates this from `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`

Two things one might expect to be obstacles are not. The conjugate of `ỹ_{k+1}` is `y_1` on the nose
(`HJO.Braid.trainDown_mul_braidYtilde_top_mul_trainDown`), and no *mixed* train cancellation
`T_{1↗k+1}T_{k+1↘1} = 1` is needed anywhere — that product is a factor of the answer. With
`HJO/Shuffle/SlopeTrajectory.lean` supplying the order of the letters, that statement reduces to
one list identity and one monoid identity:

* `HJO.Braid.conjRun θ w 0 (Ad-2)` is `b_{a,b}·(y_1 z_1 T_{1↗k+1}T_{k+1↘1} b_{a,b})^{A-1}`, a turn
  contributing the `a+b-2` letters of `HJO.Mellit.slopeWord` and then, at every turn but the last,
  the exception's `z` and the round's `ỹ`;
* and `X(YX)^{A-1} = (XY)^{A-1}X` at `X = T_{k+1↘1}b_{a,b}`, `Y = y_1z_1T_{1↗k+1}`, which turns that
  into the right-hand side `HJO.Braid.appendRhs`.

**But the hypothesis of this file is too weak for the first of those, and deliberately so.**
`IsFinishCluster` gives the rank *dichotomy* — every intermediate rank is `1` or `k+1` — and it
gives every horizontal crossing at `k+1`. It does not say *which* vertical crossings are at `1`,
and that is what the first bullet needs: the ones next to the finish must be at `k+1` and all the
others at `1`. Pinning that needs the cluster located, not merely avoided, in units of `1/(a+b)`:
with `θ = a/(a+b) + e` and the run of `A` turns,

`θ - 1/(a+b) < f_i < θ - (A(a+b))·e` for every `i`.

The lower bound puts the cluster above every grid point other than the one hugging the finish, so
every `z` away from the finish falls below it; the upper bound puts it below every one of the `A`
near-finish positions `θ - (j+2)e`, so every `z` next to the finish rises above it. That pair is
Mellit's "clustered close to the finish" made quantitative, and it implies `avoids`. It is not
assumed here, this file being about what the weak hypothesis
already yields.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 6.
-/

@[expose] public section

open Finset

namespace HJO.Braid

variable {θ : ℚ} {k : ℕ}

/-! ### The two ranks an entry of index zero can have -/

/-- **An entry of index `0` below every other entry has rank `1`.** The companion of
`HJO.Braid.entryRank_zero_of_forall_lt`, which is the same statement with the inequality reversed
and the rank `k + 1`. -/
theorem entryRank_zero_eq_one_of_forall_lt {w : Fin (k + 1) → ℚ}
    (h : ∀ t : Fin k, w 0 < w t.succ) : entryRank w 0 = 1 := by
  have hset : ({j | w j ≤ w 0} : Finset (Fin (k + 1))) = {0} := by
    refine eq_singleton_iff_unique_mem.2 ⟨mem_filter.2 ⟨mem_univ _, le_rfl⟩, fun j hj => ?_⟩
    have hj' := (mem_filter.1 hj).2
    revert hj'
    exact Fin.cases (fun _ => rfl) (fun t hj' => absurd hj' (not_le.2 (h t))) j
  rw [entryRank, hset, card_singleton]

/-- Updating the entry of index `0` leaves the others alone, so a rank hypothesis on the *other*
entries transfers to the updated tuple. -/
theorem update_zero_succ {w : Fin (k + 1) → ℚ} (x : ℚ) (t : Fin k) :
    Function.update w 0 x t.succ = w t.succ :=
  Function.update_of_ne (Fin.succ_ne_zero t) _ _

/-- **The moving point below the whole cluster has rank `1`.** In Mellit's words, a crossing
of the vertical wall away from the finish happens at position `1`. -/
theorem entryRank_update_eq_one_of_forall_lt {w : Fin (k + 1) → ℚ} {x : ℚ}
    (h : ∀ t : Fin k, x < w t.succ) : entryRank (Function.update w 0 x) 0 = 1 := by
  refine entryRank_zero_eq_one_of_forall_lt fun t => ?_
  rw [update_zero_succ, Function.update_self]
  exact h t

/-- **The moving point above the whole cluster has rank `k + 1`.** This is both the rank at every
crossing of the horizontal wall and — that being Mellit's exception — the rank at the passages
next to the finish. -/
theorem entryRank_update_eq_succ_of_forall_lt {w : Fin (k + 1) → ℚ} {x : ℚ}
    (h : ∀ t : Fin k, w t.succ < x) : entryRank (Function.update w 0 x) 0 = k + 1 := by
  refine entryRank_zero_of_forall_lt fun t => ?_
  rw [update_zero_succ, Function.update_self]
  exact h t

/-- **Every crossing of the horizontal wall is at rank `k + 1`**, and this needs only that the
other points lie below `θ`: a crossing of the horizontal wall is by `HJO.Braid.braidStep` a position
above `θ`, hence above all of them. No avoidance clause is used. -/
theorem entryRank_update_eq_succ_of_theta_lt {w : Fin (k + 1) → ℚ} {x : ℚ}
    (hf : ∀ t : Fin k, w t.succ < θ) (hx : θ < x) :
    entryRank (Function.update w 0 x) 0 = k + 1 :=
  entryRank_update_eq_succ_of_forall_lt fun t => (hf t).trans hx

/-! ### The clustering hypothesis -/

/-- **The clustering hypothesis of Section 6 of Mellit's paper**, for a run of `m` moves of a point
starting at `x` against `k` points standing at the positions `f`.

* `finish_lt_theta`: every one of the `k` standing positions is below `θ`. This is "in the final
  position all points are clustered close to `finish` at `(t, 1-t)`" together with Mellit's own
  `(t - ε', 1 - t + ε')`, which says the arrival is on the near side of the finish.
* `avoids`: each of the moving point's `m + 1` positions lies either below all of the standing
  positions or above all of them — the cluster is short enough that the trajectory misses it.

At `k = 0` both clauses are vacuous, as they must be: with no other points every rank is `1` and
also `k + 1`. -/
structure IsFinishCluster (θ : ℚ) {k : ℕ} (f : Fin k → ℚ) (x : ℚ) (m : ℕ) : Prop where
  /-- Every standing position lies below the puncture. -/
  finish_lt_theta : ∀ t, f t < θ
  /-- No position of the moving point lies inside the cluster of standing positions. -/
  avoids : ∀ j ≤ m, (∀ t, (nextCrossing θ)^[j] x < f t) ∨ (∀ t, f t < (nextCrossing θ)^[j] x)

/-- **Under the clustering hypothesis the moving point's rank is `1` or `k + 1` at every
intermediate position** — never anything between. This is what the naive hypothesis of
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` fails to give, and what the letter-reading of
that statement needs. -/
theorem entryRank_moveTuple_replicate_eq_or {w : Fin (k + 1) → ℚ} {m j : ℕ}
    (hcl : IsFinishCluster θ (fun t => w t.succ) (w 0) m) (hj : j ≤ m) :
    entryRank (moveTuple θ w (List.replicate j (0 : Fin (k + 1)))) 0 = 1 ∨
      entryRank (moveTuple θ w (List.replicate j (0 : Fin (k + 1)))) 0 = k + 1 := by
  rw [moveTuple_replicate]
  exact (hcl.avoids j hj).imp entryRank_update_eq_one_of_forall_lt
    entryRank_update_eq_succ_of_forall_lt

/-! ### The letter of one move of the moving point -/

/-- The tuple after one further move of the point of index `0`. -/
theorem moveOne_update_zero (θ : ℚ) {w : Fin (k + 1) → ℚ} (x : ℚ) :
    moveOne θ (Function.update w 0 x) 0 = Function.update w 0 (nextCrossing θ x) := by
  rw [moveOne, Function.update_self, Function.update_idem]

/-- **The letter of one move of the moving point**, `HJO.Braid.braidStep` with both ranks read off
the clustering hypothesis: a descending train between two ranks each of which is `1` or `k + 1`,
then `z` at the rank before the move if the point crosses the vertical wall and `ỹ` at that rank if
it crosses the horizontal one.

Together with `HJO.Braid.entryRank_update_eq_succ_of_theta_lt`, which forces the `ỹ` branch to sit
at rank `k + 1`, this is Mellit's

> the rules produce combinations of `z_1`, `T_{k+1↘1}`, `ỹ_{k+1}`, `T_{1↗k+1}`.

The three letters that occur are therefore `z_1`, `z_{k+1}` and `ỹ_{k+1}`: `z_1` at a vertical
crossing away from the finish, `z_{k+1}` at one next to the finish, and `ỹ_{k+1}` at every
horizontal crossing. -/
theorem braidStep_moveTuple_replicate_eq {w : Fin (k + 1) → ℚ} {m j : ℕ}
    (hcl : IsFinishCluster θ (fun t => w t.succ) (w 0) m) (hj : j + 1 ≤ m) :
    ∃ r r' : ℕ, (r = 1 ∨ r = k + 1) ∧ (r' = 1 ∨ r' = k + 1) ∧
      (θ < (nextCrossing θ)^[j] (w 0) → r = k + 1) ∧
      braidStep θ (moveTuple θ w (List.replicate j (0 : Fin (k + 1)))) 0
        = braidTrainDown (k + 1) r' r *
          (if (nextCrossing θ)^[j] (w 0) < θ then braidGenZ (k + 1) r
            else braidYtilde (k + 1) r) := by
  set x := (nextCrossing θ)^[j] (w 0) with hx
  have hxsucc : (nextCrossing θ)^[j + 1] (w 0) = nextCrossing θ x := by
    rw [hx, Function.iterate_succ_apply']
  -- the rank before the move
  refine ⟨entryRank (Function.update w 0 x) 0,
    entryRank (Function.update w 0 (nextCrossing θ x)) 0, ?_, ?_, ?_, ?_⟩
  · exact (hcl.avoids j (by omega)).imp entryRank_update_eq_one_of_forall_lt
      entryRank_update_eq_succ_of_forall_lt
  · refine ((hcl.avoids (j + 1) hj).imp ?_ ?_) <;> rw [hxsucc] <;>
      exact fun h => by
        first
          | exact entryRank_update_eq_one_of_forall_lt h
          | exact entryRank_update_eq_succ_of_forall_lt h
  · exact fun h => entryRank_update_eq_succ_of_theta_lt hcl.finish_lt_theta h
  · rw [moveTuple_replicate, braidStep, moveOne_update_zero, Function.update_self]

/-! ### Pushing the trains out to the ends of the run -/

/-- **The moving point's run with its trains pushed out**: the product of the run's letters, each
conjugated to rank `1` by the train of the rank it sits at.

`HJO.Braid.braidStep` decorates the `j`-th letter with the train `T_{r_{j+1}↘r_j}` of the *change*
of rank, so the letters of the run sit at all the ranks the point passes through. Splitting each
such train through the base point, `T_{r'↘r} = T_{r'↘1}T_{1↘r}`, telescopes the whole run into one
train at each end and a product of letters each of which is conjugated to rank `1`; this is that
product. The head of the recursion is the *last* move, which `HJO.Braid.braidWord` puts leftmost. -/
def conjRun (θ : ℚ) {K : ℕ} (w : Fin K → ℚ) (i : Fin K) : ℕ → BraidMonoid K
  | 0 => 1
  | m + 1 =>
    braidTrainDown K 1 (entryRank (moveTuple θ w (List.replicate m i)) i) *
        (if moveTuple θ w (List.replicate m i) i < θ then
            braidGenZ K (entryRank (moveTuple θ w (List.replicate m i)) i)
          else braidYtilde K (entryRank (moveTuple θ w (List.replicate m i)) i)) *
        braidTrainDown K (entryRank (moveTuple θ w (List.replicate m i)) i) 1 *
      conjRun θ w i m

@[simp]
theorem conjRun_zero (θ : ℚ) {K : ℕ} (w : Fin K → ℚ) (i : Fin K) : conjRun θ w i 0 = 1 := rfl

/-- **The run of one point is a conjugate**:
`b_{i^m}(w)·T_{rk_w(i)↘1} = T_{rk_{w'}(i)↘1}·(the conjugated letters)`, where `w'` is the tuple
after the `m` moves.

This is Mellit's "the rules produce combinations of `z_1`, `T_{k+1↘1}`, `ỹ_{k+1}`, `T_{1↗k+1}`" made
into an identity, and it is the shape the right-hand side `HJO.Braid.appendRhs` has: one `T_{k+1↘1}`
outside everything on the left, and a word in letters at rank `1` inside. Nothing about the
clustering is used — this is pure train algebra, `HJO.Braid.trainDown_mul_trainDown` at the base
point. What the clustering supplies is the *value* of each conjugated letter, by way of the rank: at
rank `1` the two trains vanish and the letter is bare. -/
theorem braidWord_replicate_mul_trainDown_one {K : ℕ} (hK : 1 ≤ K) (θ : ℚ) (w : Fin K → ℚ)
    (i : Fin K) (m : ℕ) :
    braidWord θ w (List.replicate m i) * braidTrainDown K (entryRank w i) 1
      = braidTrainDown K (entryRank (moveTuple θ w (List.replicate m i)) i) 1 *
        conjRun θ w i m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsys := isBraidSystem_braidGenT K
    set v := moveTuple θ w (List.replicate m i) with hv
    have hmove : moveTuple θ w (List.replicate (m + 1) i) = moveOne θ v i := by
      rw [List.replicate_succ, moveTuple_cons]
    have hsplit : braidTrainDown K (entryRank (moveOne θ v i) i) 1 *
        braidTrainDown K 1 (entryRank v i)
          = braidTrainDown K (entryRank (moveOne θ v i) i) (entryRank v i) :=
      trainDown_mul_trainDown hsys (entryRank_pos _ _) (entryRank_le _ _) le_rfl hK
        (entryRank_pos _ _) (entryRank_le _ _)
    rw [hmove, braidWord_replicate_succ, mul_assoc, ih, braidStep, conjRun]
    rw [show ∀ x y z t : BraidMonoid K, x * y * (z * t) = x * (y * z) * t from
      fun x y z t => by rw [mul_assoc, ← mul_assoc y, ← mul_assoc]]
    rw [← hsplit]
    simp only [mul_assoc]
    rw [hv]

/-- **Under the clustering hypothesis each conjugated letter of the run is one of three elements.**
At rank `1` the two trains vanish, so the letter is the bare `z_1`; at rank `k+1` it is the
conjugate of `z_{k+1}` or of `ỹ_{k+1}`, and the `ỹ` case is the only one that can occur above `θ`
(`HJO.Braid.entryRank_update_eq_succ_of_theta_lt`).

Together with `HJO.Braid.braidWord_replicate_mul_trainDown_one` this reduces
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` to a statement about the *sequence* of these
three, which is what `HJO/Shuffle/SlopeTrajectory.lean` computes. -/
theorem conjRun_succ_eq_of_finishCluster {w : Fin (k + 1) → ℚ} {m j : ℕ}
    (hcl : IsFinishCluster θ (fun t => w t.succ) (w 0) m) (hj : j ≤ m) :
    (conjRun θ w 0 (j + 1) = (if (nextCrossing θ)^[j] (w 0) < θ then braidGenZ (k + 1) 1
        else braidYtilde (k + 1) 1) * conjRun θ w 0 j) ∨
      (conjRun θ w 0 (j + 1) = braidTrainDown (k + 1) 1 (k + 1) *
          (if (nextCrossing θ)^[j] (w 0) < θ then braidGenZ (k + 1) (k + 1)
            else braidYtilde (k + 1) (k + 1)) *
          braidTrainDown (k + 1) (k + 1) 1 * conjRun θ w 0 j) := by
  have hval : moveTuple θ w (List.replicate j (0 : Fin (k + 1))) 0
      = (nextCrossing θ)^[j] (w 0) := by
    rw [moveTuple_replicate, Function.update_self]
  rcases entryRank_moveTuple_replicate_eq_or hcl hj with h | h
  · refine Or.inl ?_
    rw [conjRun, h, hval]
    simp
  · exact Or.inr (by rw [conjRun, h, hval])

/-! ### The conjugated letters, evaluated -/

/-- **`ỹ` at the top rank is `y_1` conjugated by the full train**:
`ỹ_K = T_{K↘1}·y_1·T_{1↘K}`.

`HJO.Braid.braidYtilde` writes `ỹ_K = T_{K↘1}T_{1↗K}y_K`, and
`HJO.Braid.braidGenY_eq_trainUp_mul_mul_trainDown` writes `y_K = T_{K↗1}y_1T_{1↘K}`; the two
ascending trains `T_{1↗K}T_{K↗1}` cancel by `HJO.Braid.trainUp_mul_trainUp_self`. -/
theorem braidYtilde_top_eq {K : ℕ} (hK : 1 ≤ K) :
    braidYtilde K K = braidTrainDown K K 1 * braidGenY K 1 * braidTrainDown K 1 K := by
  rw [braidYtilde_self, braidGenY_eq_trainUp_mul_mul_trainDown K K hK le_rfl]
  rw [show ∀ x y z t v : BraidMonoid K, x * y * (z * t * v) = x * (y * z) * t * v from
    fun x y z t v => by simp only [mul_assoc]]
  rw [trainUp_mul_trainUp_self (isBraidSystem_braidGenT K) le_rfl hK hK le_rfl, mul_one]

/-- **The conjugated `ỹ` of the run is exactly `y_1`**, the letter `HJO.Braid.slopeBraid` reads.

This is the identity that makes the right-hand side `HJO.Braid.appendRhs` a word in `y_1` and `z_1`
at all: a horizontal crossing of the moving point contributes `ỹ_{k+1}`, at rank `k+1` by
`HJO.Braid.entryRank_update_eq_succ_of_theta_lt`, and
`HJO.Braid.braidWord_replicate_mul_trainDown_one` conjugates it by `T_{1↘k+1}` and `T_{k+1↘1}`,
which are inverse to the two trains of `HJO.Braid.braidYtilde_top_eq`. -/
theorem trainDown_mul_braidYtilde_top_mul_trainDown {K : ℕ} (hK : 1 ≤ K) :
    braidTrainDown K 1 K * braidYtilde K K * braidTrainDown K K 1 = braidGenY K 1 := by
  have hcancel : braidTrainDown K 1 K * braidTrainDown K K 1 = 1 :=
    trainDown_mul_trainDown_self (isBraidSystem_braidGenT K) le_rfl hK hK le_rfl
  rw [braidYtilde_top_eq hK]
  rw [show ∀ x y z t v : BraidMonoid K, x * (y * z * t) * v = x * y * z * (t * v) from
    fun x y z t v => by simp only [mul_assoc]]
  rw [hcancel, one_mul, mul_one]

/-- **The conjugated `z` of the run is `z_1` followed by a mixed pair of trains.** Unlike the `ỹ`
case the two trains do not cancel, and they are not meant to: they are the `T_{1↗k+1}` standing at
the right-hand end of each round of the right-hand side `HJO.Braid.appendRhs`,
`HJO.Braid.braidTrainDown_mul_braidGenZ` turning `T_{1↘k+1}z_{k+1}` into `z_1T_{1↗k+1}`.

The `z` letters of the run that sit at rank `1` need no identity at all: there the two conjugating
trains are empty, `HJO.Braid.conjRun_succ_eq_of_finishCluster` reading them off as bare `z_1`. -/
theorem trainDown_mul_braidGenZ_top_mul_trainDown {K : ℕ} (hK : 1 ≤ K) :
    braidTrainDown K 1 K * braidGenZ K K * braidTrainDown K K 1
      = braidGenZ K 1 * (braidTrainUp K 1 K * braidTrainDown K K 1) := by
  rw [braidTrainDown_mul_braidGenZ le_rfl hK hK le_rfl]
  simp only [mul_assoc]

end HJO.Braid

end
