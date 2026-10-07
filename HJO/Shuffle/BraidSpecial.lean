/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidMonoid
public import Mathlib.Algebra.BigOperators.Fin
public meta import HJO.Attr

/-! # Moves, words of moves, and the special braid

A point of the punctured torus travelling down a line of slope `s` returns to the antidiagonal at
`nx_θ` of where it started, and each such return contributes one letter to a braid. This file
writes down the letter of one move, the braid of a sequence of moves, and the braid of
special-braid data.

## Main definitions

* `HJO.Braid.braidStep`, the element `b_i(w)` of `𝔹_k^+(𝕋_0)`.
* `HJO.Braid.braidWord`, `b_{i_1, …, i_l}(w)`.
* `HJO.Braid.specialMoveList`, `HJO.Braid.specialBraid`, `B_{s,v,α}`.

## Main results

* `HJO.Braid.braidWord_cons_moveStage` — the indexing by stages: the factor of `i_1` is
  `b_{i_1}(w^{(l-1)})`, read against `HJO.Braid.moveStage`.
* `HJO.Braid.braidWord_pair` — a two-move word written out, the check that the earliest move
  stands rightmost.
* `HJO.Braid.braidWord_append` — the moves of a suffix are performed first, so a word splits as
  the prefix's braid at the advanced tuple times the suffix's braid.
* `HJO.Braid.count_specialMoveList` — the sequence of `HJO.Braid.specialBraid` contains `i` exactly
  `α_i - 1` times.

## Implementation notes

### `HJO.Braid.braidStep` is total, and the excluded argument falls into the `ỹ` branch

One usually takes `w_i ≠ θ`, distinct entries of `w`, and distinct entries of the advanced tuple
`w'`. None of the three is carried in the type: `HJO.Braid.entryRank` is total, `HJO.Braid.moveOne`
is total, and the trains of `HJO.Braid.trainDown` are words. The case split is on `w_i < θ`, so the
excluded value `w_i = θ` — the trajectory through the puncture — falls into the `ỹ` branch and is
junk, exactly as `HJO.Braid.nextCrossing` is junk there. The three conditions are the clauses of
`HJO.Braid.IsAdmissibleMoveSeq` and of `HJO.Braid.IsSpecialBraidData`, and they are hypotheses
of the statements that use the letter.

The ranks are `HJO.Braid.entryRank`, which is `1`-based and lands in `{1, …, k}` for a tuple with
distinct entries, so the trains `T_{a'↘a}` read only letters `T_j` with `j < max(a, a') ≤ k`, all
in rank. No subtraction occurs in the index: the `T_{a'↘a}` is a word in the letters
between the two ranks and `HJO.Braid.trainDown` takes the two endpoints, not their difference.

### The order of the factors, and why the recursion is the definition

`HJO.Braid.braidWord` displays the product `b_{i_1}(w^{(l-1)}) ⋯ b_{i_l}(w^{(0)})`: the **last**
index of the sequence is the move performed **first**, and its factor stands rightmost. Mellit
writes this recursively, and the recursion is what is taken as the definition here —
`b_{i :: rest}(w) = b_i(w^{(|rest|)}) · b_{rest}(w)` — because the displayed product needs the
stage numbering of `HJO.Braid.moveStage` at every factor and the recursion needs it at none.
`HJO.Braid.braidWord_cons_moveStage` is the bridge: the tuple the head's factor is evaluated at is
`HJO.Braid.moveStage θ w l (l.length - 1)`, the `w^{(l-1)}`. The stage of a suffix
agrees with the stage of the whole list at the same index, which is why the recursion is
well-formed against `moveStage` at all.

### `α_i - 1` is `ℕ`-subtraction

`HJO.Braid.specialMoveList` lists `α_i - 1` copies of `i`, and the subtraction truncates. It is
honest exactly under `HJO.Braid.IsSpecialBraidData.one_le_mult`, the `α ∈ ℤ_{≥1}^k`:
at `α_i = 0` the count is `-1`, which is not a number of copies, and the truncation
lists none. That is the same trap `HJO.Braid.positionPair` carries in
`nx_θ^{α_i - 1}(v_i)`, and it is repaired by the same hypothesis; `HJO.Braid.length_specialMoveList`
states the length in the truncated form, which is the correct one under `one_le_mult`.

The sequence is in increasing order of `i`, as `HJO.Braid.specialBraid` asks, `List.finRange k`
being that order.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

namespace HJO.Braid

/-! ### One move -/

/-- **One move**, `HJO.Braid.braidStep`. With `a = rk_w(i)` the rank of the moving
entry before the move and `a' = rk_{w'}(i)` its rank after,
`b_i(w) = T_{a'↘a} z_a` when `w_i < θ` and `T_{a'↘a} ỹ_a` when `w_i > θ`: a point crossing the
vertical wall of the torus contributes a `z`, one crossing the horizontal wall a `ỹ`, after the
same descending train.

Total in every argument; at the excluded `w_i = θ` the value is the `ỹ` branch and is junk. See the
module docstring. -/
@[hjo "def_braid_step"]
def braidStep (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (i : Fin k) : BraidMonoid k :=
  braidTrainDown k (entryRank (moveOne θ w i) i) (entryRank w i) *
    (if w i < θ then braidGenZ k (entryRank w i) else braidYtilde k (entryRank w i))

/-- The first branch: a point below the puncture crosses the vertical wall and contributes `z_a`. -/
theorem braidStep_of_lt {θ : ℚ} {k : ℕ} {w : Fin k → ℚ} {i : Fin k} (h : w i < θ) :
    braidStep θ w i =
      braidTrainDown k (entryRank (moveOne θ w i) i) (entryRank w i) *
        braidGenZ k (entryRank w i) := by
  simp only [braidStep, h, ite_true]

/-- The second branch: a point above the puncture crosses the horizontal wall and contributes
`ỹ_a`. -/
theorem braidStep_of_gt {θ : ℚ} {k : ℕ} {w : Fin k → ℚ} {i : Fin k} (h : θ < w i) :
    braidStep θ w i =
      braidTrainDown k (entryRank (moveOne θ w i) i) (entryRank w i) *
        braidYtilde k (entryRank w i) := by
  simp only [braidStep, not_lt.2 h.le, ite_false]

/-- **A move that does not change the rank contributes no train.** The `T_{a'↘a}` is
empty exactly when the moving entry keeps its place in the order, and then the letter of the move
is `z_a` or `ỹ_a` alone. -/
theorem braidStep_of_entryRank_eq {θ : ℚ} {k : ℕ} {w : Fin k → ℚ} {i : Fin k}
    (h : entryRank (moveOne θ w i) i = entryRank w i) :
    braidStep θ w i =
      if w i < θ then braidGenZ k (entryRank w i) else braidYtilde k (entryRank w i) := by
  rw [braidStep, h, braidTrainDown_self, one_mul]

/-! ### The braid of a sequence of moves -/

/-- **The braid of a sequence of moves**, `HJO.Braid.braidWord`:
`b_{i_1, …, i_l}(w) = b_{i_1}(w^{(l-1)}) b_{i_2}(w^{(l-2)}) ⋯ b_{i_l}(w^{(0)})`, the empty product
being the identity.

This is Mellit's own recursion — the head of the list is the move performed *last* and its
factor stands leftmost — and `HJO.Braid.braidWord_cons_moveStage` reads the tuple it is evaluated
at as the `w^{(l-1)}`. -/
@[hjo "def_braid_word"]
def braidWord (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) : List (Fin k) → BraidMonoid k
  | [] => 1
  | i :: rest => braidStep θ (moveTuple θ w rest) i * braidWord θ w rest

/-- The empty sequence gives the identity of `𝔹_k^+(𝕋_0)`. -/
@[simp]
theorem braidWord_nil (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) : braidWord θ w ([] : List (Fin k)) = 1 :=
  rfl

/-- Mellit's recursion
`b_{i_1, i_2, …, i_l}(v) = b_{i_1}(next_{i_2, …, i_l}(v)) b_{i_2, …, i_l}(v)`. -/
theorem braidWord_cons (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (i : Fin k) (rest : List (Fin k)) :
    braidWord θ w (i :: rest) = braidStep θ (moveTuple θ w rest) i * braidWord θ w rest := rfl

/-- **The head's factor is evaluated at the `w^{(l-1)}`.** The stage numbering of
`HJO.Braid.moveStage` counts moves already performed, so the tuple the *last* move sees is the one
after all `l - 1` earlier ones. -/
theorem braidWord_cons_moveStage (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (i : Fin k)
    (rest : List (Fin k)) :
    braidWord θ w (i :: rest) =
      braidStep θ (moveStage θ w (i :: rest) rest.length) i * braidWord θ w rest := by
  rw [braidWord_cons]
  congr 2
  rw [moveStage, List.length_cons, show rest.length + 1 - rest.length = 1 by omega,
    List.drop_one, List.tail_cons]

/-- A one-move word is the move itself, at the tuple it starts from. -/
theorem braidWord_singleton (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (i : Fin k) :
    braidWord θ w [i] = braidStep θ w i := by
  rw [braidWord_cons, braidWord_nil, mul_one, moveTuple_nil]

/-- **A two-move word written out, and the order is the usual one**: the sequence `(i, j)`
performs `j` first, so its factor stands rightmost and `i`'s factor sees the tuple `j` has already
advanced. -/
theorem braidWord_pair (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (i j : Fin k) :
    braidWord θ w [i, j] = braidStep θ (moveOne θ w j) i * braidStep θ w j := by
  rw [braidWord_cons, braidWord_singleton, moveTuple_cons, moveTuple_nil]

/-- **A word splits along a concatenation**: the moves of the suffix are performed first, so the
suffix's braid stands on the right and the prefix's braid is read at the tuple the suffix has
advanced. -/
theorem braidWord_append (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (l₁ l₂ : List (Fin k)) :
    braidWord θ w (l₁ ++ l₂) = braidWord θ (moveTuple θ w l₂) l₁ * braidWord θ w l₂ := by
  induction l₁ with
  | nil => rw [List.nil_append, braidWord_nil, one_mul]
  | cons i l₁' ih =>
    rw [List.cons_append, braidWord_cons, braidWord_cons, ih, mul_assoc]
    congr 2
    rw [moveTuple, moveTuple, moveTuple, List.foldr_append]

/-! ### The special braid -/

/-- **The sequence of moves of `HJO.Braid.specialBraid`**: `α_i - 1` copies of `i`, for each `i` in
increasing order of `i`. The subtraction is `ℕ`-subtraction and is honest under
`HJO.Braid.IsSpecialBraidData.one_le_mult`; see the module docstring. -/
def specialMoveList {k : ℕ} (α : Fin k → ℕ) : List (Fin k) :=
  (List.finRange k).flatMap fun i => List.replicate (α i - 1) i

/-- **The sequence contains `i` exactly `α_i - 1` times**, which is what `HJO.Braid.specialBraid`
asks. -/
theorem count_specialMoveList {k : ℕ} (α : Fin k → ℕ) (i : Fin k) :
    (specialMoveList α).count i = α i - 1 := by
  rw [specialMoveList, List.count_flatMap, ← Fin.sum_univ_def,
    Finset.sum_eq_single i
      (fun j _ hj => by
        simp only [Function.comp_apply, List.count_replicate, beq_iff_eq, hj, ite_false])
      (fun h => absurd (Finset.mem_univ i) h)]
  simp

/-- The length of the sequence is `∑_i (α_i - 1)`, the total number of moves. -/
theorem length_specialMoveList {k : ℕ} (α : Fin k → ℕ) :
    (specialMoveList α).length = ∑ i : Fin k, (α i - 1) := by
  rw [specialMoveList, List.length_flatMap, Fin.sum_univ_def]
  simp

/-- At rank `0` there is nothing to move. -/
@[simp]
theorem specialMoveList_zero (α : Fin 0 → ℕ) : specialMoveList α = [] := by
  simp [specialMoveList]

/-- **The special braid**, `HJO.Braid.specialBraid`:
`B_{s,v,α} = b_{1^{α_1-1}, …, k^{α_k-1}}(v)`.

Total in `(v, α)`: the usual setting takes special-braid data, and every clause of
`HJO.Braid.IsSpecialBraidData` — the slope, the interval `(0,1)`, the multiplicities and the
distinctness — is a hypothesis of the statements about it. The slope `s` does not appear, `θ` being
what every clause of `HJO.Braid.braidStep` and `HJO.Braid.nextCrossing` reads; the two are tied by
`θ(s+1) = 1`, which is a field of `HJO.Braid.IsSpecialBraidData`. -/
@[hjo "def_braid_special"]
def specialBraid (θ : ℚ) {k : ℕ} (v : Fin k → ℚ) (α : Fin k → ℕ) : BraidMonoid k :=
  braidWord θ v (specialMoveList α)

/-- **The rank-`0` special braid is the identity**, which is why `HJO.Braid.BraidMonoid` has to
exist at `k = 0`: the "the braid of an empty sequence of moves is the identity of
`𝔹_k^+(𝕋_0)`, so that monoid has to exist at `k = 0` for the rank-`0` special braid to name
something". -/
@[simp]
theorem specialBraid_zero (θ : ℚ) (v : Fin 0 → ℚ) (α : Fin 0 → ℕ) : specialBraid θ v α = 1 := by
  rw [specialBraid, specialMoveList_zero, braidWord_nil]

/-- **Every multiplicity `1` gives the identity braid**: no point moves, so no letter is
contributed. -/
theorem specialBraid_of_forall_eq_one {θ : ℚ} {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (h : ∀ i, α i = 1) : specialBraid θ v α = 1 := by
  have hnil : specialMoveList α = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro i hi
    have := count_specialMoveList α i
    rw [h i] at this
    have hpos : 0 < (specialMoveList α).count i := List.count_pos_iff.2 hi
    omega
  rw [specialBraid, hnil, braidWord_nil]

end HJO.Braid
