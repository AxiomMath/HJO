/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidTrainRelations
public import HJO.Shuffle.MellitProp57
public meta import HJO.Attr

/-! # Appending a part: splitting the moves of one point off a special braid

The first half of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`. That statement adjoins to
special-braid data `(v, α)` of rank `k` one further point, of multiplicity `A`, lying above every
entry of `v`, and asserts a factorisation of `B_{s,w,β}` into the new point's own contribution and
`φ*₊(B_{s,v,α})` conjugated by a pair of trains. This file proves everything in that factorisation
*except* the identification of the new point's contribution with the slope braid `b_{a,b}` — see
"What is not here" below, which also records two defects of the naive form of the statement that
block that last step.

## Main results

* `HJO.Braid.specialMoveList_split_zero` — the move sequence of `HJO.Braid.specialBraid` splits at
  the first index: `A - 1` copies of `0`, then the moves of the deleted data read in the larger
  tuple. This is `HJO.Braid.specialMoveList_eq_map_succAbove` with its hypothesis `β_j = 1` removed,
  which is exactly what an *appended part* needs.
* `HJO.Braid.specialBraid_eq_braidWord_replicate_mul` — the resulting factorisation of
  `HJO.Braid.specialBraid` into the two phases.
* `HJO.Braid.braidWord_specialMoveList_succ_mul_trainDown_one_of_le`
  — **`HJO.Braid.specialBraid_mul_trainDown_one` with the multiplicity-one hypothesis on the
  inserted point dropped**: the moves of the *other* points, performed while the inserted point
  stands still, conjugate to `φ*₊(B_{s,v,α})`. The inserted point may stand anywhere weakly below
  `1-θ` that no iterate of the data separates from `1-θ`;
  `HJO.Braid.braidWord_specialMoveList_succ_mul_trainDown_one` is the case of the value `1-θ`
  itself, where that is free.
* `HJO.Braid.specialBraid_eq_conj_phiPlusStar` — the two combined: `B_{s,w,β}` is the new point's
  own word times `T_{k+1↘1}·φ*₊(B_{s,v,α})·T_{1↘k+1}`.
* `HJO.Braid.specialMoveList_split_last`,
  `HJO.Braid.specialBraid_eq_braidWord_mul_replicate_last` — the same splitting at the *last* index,
  where the temporal order comes out reversed. This is the evidence that the reindexing
  `HJO.Mellit.mellitInduction_sweepWitness` asks for is not a relabelling; see the second docstring.
* `HJO.Braid.moveTuple_replicate`, `HJO.Braid.braidWord_replicate_succ` — the new point's own phase:
  a run of moves of a single point advances only that point, and contributes one factor of
  `HJO.Braid.braidStep` per move.
* `HJO.Braid.braidWord_replicate_succ_rank_one` — at rank one that factor is a bare letter, `z_1`
  or `ỹ_1` according to the side of `θ` the point is on. This is the shape the slope braid would
  have to be read off from.

## Which index the appended point has, and why it is `0`

The appended entry is written `w_{k+1}`, the *last*. That cannot be the index, only the value.
`HJO.Braid.specialMoveList` lists the moves in increasing order of index and `HJO.Braid.moveTuple`
performs the *last* entry of the list first, so the highest index moves earliest and stands
rightmost in `HJO.Braid.braidWord`. The right-hand side of the identity has `φ*₊(B_{s,v,α})`
rightmost, i.e. the other points moving first and the new point's turns outermost; that forces the
new point to be the *lowest* index. Its being above the others in value is a separate matter,
`HJO.Braid.entryRank` reading only values, and is what gives it rank `k+1`
(`HJO.Braid.entryRank_zero_of_forall_lt`).

So the appended point is index `0` here, the deletion is `w ∘ Fin.succ`, and
`(0 : Fin (k+1)).succAbove` is `Fin.succ` by `Fin.succAbove_zero` — which is what lets the machinery
of `HJO/Shuffle/BraidInsertPoint.lean`, written for a general insertion index, be used
unchanged.

## The hypothesis the naive statement is missing

The naive statement asks for `1 - θ > w_{k+1} > max(v)` and for the entries and the final positions
of `(v, α)` to be below `1 - θ`. Those do not suffice for the step the proof attributes to
`HJO.Braid.specialBraid_mul_trainDown_one`: that step needs the new point to be above the others
both at the start *and* at the finish, and a strict inequality `w_{k+1} < 1 - θ` leaves the final
positions of `(v, α)` free to lie between `w_{k+1}` and `1 - θ`, in which case the new point's rank
at the finish is not `k + 1` and the two conjugating trains are not the ones it names.

What is needed is that the new point dominate the others at both ends. That is stated below as the
two hypotheses `∀ t, w t.succ < w 0` and `∀ t, (final position of t) < w 0`, which is what the ranks
are actually read from, rather than as `max(v) < w_{k+1}` alone.

**The `θ = 1/2` corner is not excluded, and two of the statements below are vacuous at `w 0 = 1-θ`
there.** `HJO.Braid.braidWord_specialMoveList_succ_mul_trainDown_one` and
`HJO.Braid.specialBraid_eq_conj_phiPlusStar` read `w 0 ≤ 1 - θ` together with the separation clause,
inheriting them from `HJO/Shuffle/BraidInsertPoint.lean`, where what makes each move's crossing
of the inserted point decidable from the side of `θ` the moving point starts on is that no position
of another point lies between `w 0` and `1 - θ`. At the naive value `w 0 = 1 - θ` that is free, and
together with `HJO.Braid.IsSpecialBraidData`'s `ne_theta` clause it forces `1 - θ ≠ θ`, i.e.
`θ ≠ 1/2`, i.e. `s ≠ 1` — exactly
the degenerate corner `HJO.Braid.specialBraid_mul_trainDown_one` carries, and for exactly the same
reason. The move-list split (`HJO.Braid.specialMoveList_split_zero`,
`HJO.Braid.specialBraid_eq_braidWord_replicate_mul`), the rank computation
(`HJO.Braid.entryRank_zero_of_forall_lt`) and the single-point lemmas read neither `w 0 = 1 - θ` nor
`IsSpecialBraidData`, and so hold at every slope.

## What is not here, and the second defect

The remaining step of the statement is the identification
`b_{i^{A-1}}(w) = (T_{k+1↘1} b_{a,b} y_1z_1 T_{1↗k+1})^{A-1} T_{k+1↘1} b_{a,b}`, the new point's own
`A - 1` moves against the slope braid. It is not provable in its naive form, for two reasons.

* **`a` and `b` are not bound by the statement.** The naive statement's hypotheses name only `s`,
  `θ` and `A`; `b_{a,b}` is `HJO.Braid.slopeBraid (k+1) a b`, and no hypothesis ties `(a, b)` to the
  slope. The consumer `HJO.Mellit.braidRep_specialBraid_dplusIter` supplies `s = b/a - ε`, so the
  missing hypothesis belongs here.
* **The letter counts do not match.** One move of `HJO.Braid.braidStep` contributes exactly one
  letter (`HJO.Braid.braidWord_replicate_succ_rank_one`), so the new point's word has `A - 1`
  letters besides trains, while the naive right-hand side has `(A-1)(a+b-2) + (a+b-2) + 2(A-1)` of
  them. The two agree only if `A - 1` counts *turns* rather than crossings, whereas
  `HJO.Braid.specialMoveList` gives `β_i - 1` crossings. At `A = 1` the mismatch is visible with no
  arithmetic: the new point makes no move and contributes nothing, while the naive right-hand side
  still carries one factor `b_{a,b}`.

## References

The append-a-part recursion of Mellit's Section 6: Lemma
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`, using `HJO.Braid.trainUp`,
`HJO.Braid.trainDown`, `HJO.Braid.BraidMonoid`, `HJO.Braid.braidGenT`,
`HJO.Braid.IsSpecialBraidData`, `HJO.Braid.specialBraid`, `HJO.Braid.phiPlusStar`,
`HJO.Braid.slopeBraid`, and `HJO.Braid.specialBraid_mul_trainDown_one` in its proof. Transcribing A.
Mellit, *Toric braids and `(m, n)`-parking functions*, section 6.
-/

@[expose] public section

open Finset

namespace HJO.Braid

variable {θ : ℚ} {k : ℕ}

/-! ### A run of moves of a single point -/

/-- **A run of moves of one point advances only that point**, to the corresponding iterate of
`HJO.Braid.nextCrossing`. -/
theorem moveTuple_replicate {K : ℕ} (w : Fin K → ℚ) (i : Fin K) (m : ℕ) :
    moveTuple θ w (List.replicate m i)
      = Function.update w i ((nextCrossing θ)^[m] (w i)) := by
  funext t
  rw [moveTuple_apply_eq_iterate]
  by_cases h : t = i
  · subst h
    simp
  · simp [List.count_replicate, Ne.symm h, Function.update_of_ne h]

/-- **Peeling one move off a run**: the head of the run is performed last and stands leftmost, so
the factor it contributes is `HJO.Braid.braidStep` at the tuple the earlier moves have already
reached. -/
theorem braidWord_replicate_succ {K : ℕ} (w : Fin K → ℚ) (i : Fin K) (m : ℕ) :
    braidWord θ w (List.replicate (m + 1) i)
      = braidStep θ (moveTuple θ w (List.replicate m i)) i *
        braidWord θ w (List.replicate m i) := by
  rw [List.replicate_succ, braidWord_cons]

/-- At rank one there is a single point, so every rank is `1`. -/
theorem entryRank_fin_one (w : Fin 1 → ℚ) (i : Fin 1) : entryRank w i = 1 := by
  have h : ({j | w j ≤ w i} : Finset (Fin 1)) = univ :=
    filter_true_of_mem fun j _ => by rw [Subsingleton.elim j i]
  rw [entryRank, h, card_univ, Fintype.card_fin]

/-- **One move of a single point at rank one contributes one bare letter**: no train, since the rank
cannot change, and `z_1` or `ỹ_1` according to the side of the puncture the point is on.

This is the shape the slope braid `HJO.Braid.slopeBraid` would have to be read off from, and it
is what makes the letter count of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` visible:
`m + 1` moves give `m + 1` letters. -/
theorem braidWord_replicate_succ_rank_one (θ : ℚ) (w : Fin 1 → ℚ) (m : ℕ) :
    braidWord θ w (List.replicate (m + 1) (0 : Fin 1))
      = (if (nextCrossing θ)^[m] (w 0) < θ then braidGenZ 1 1 else braidYtilde 1 1) *
        braidWord θ w (List.replicate m (0 : Fin 1)) := by
  rw [braidWord_replicate_succ,
    braidStep_of_entryRank_eq
      (by rw [entryRank_fin_one, entryRank_fin_one]), entryRank_fin_one]
  congr 2
  rw [moveTuple_replicate, Function.update_self]

/-! ### Splitting the moves of the first index off the move sequence -/

/-- **The move sequence of `HJO.Braid.specialBraid` splits at the first index**: the `β_0 - 1` moves
of the point of index `0`, and then the moves of the deleted data read in the larger tuple.

This is `HJO.Braid.specialMoveList_eq_map_succAbove` with its hypothesis `β_j = 1` dropped; that
lemma is the case `β_0 = 1`, in which the first block is empty. `List.finRange_succ` puts index `0`
at the head, and the head of the sequence is the move performed last. -/
theorem specialMoveList_split_zero (β : Fin (k + 1) → ℕ) :
    specialMoveList β
      = List.replicate (β 0 - 1) 0 ++ (specialMoveList (β ∘ Fin.succ)).map Fin.succ := by
  rw [specialMoveList, specialMoveList, List.finRange_succ, List.flatMap_cons, List.flatMap_map,
    List.map_flatMap]
  simp

/-- **`HJO.Braid.specialBraid` splits into the two phases**: the other points move first, so their
braid stands rightmost, and the appended point's own `β_0 - 1` moves are read at the tuple they have
left. -/
theorem specialBraid_eq_braidWord_replicate_mul (θ : ℚ) (w : Fin (k + 1) → ℚ)
    (β : Fin (k + 1) → ℕ) :
    specialBraid θ w β
      = braidWord θ (moveTuple θ w ((specialMoveList (β ∘ Fin.succ)).map Fin.succ))
            (List.replicate (β 0 - 1) 0) *
          braidWord θ w ((specialMoveList (β ∘ Fin.succ)).map Fin.succ) := by
  rw [specialBraid, specialMoveList_split_zero, braidWord_append]

/-- **`HJO.Braid.specialBraid` splits at the LAST index as well**, `List.finRange_succ_last` putting
that index at the *end* of the sequence. -/
theorem specialMoveList_split_last (β : Fin (k + 1) → ℕ) :
    specialMoveList β
      = (specialMoveList (β ∘ Fin.castSucc)).map Fin.castSucc
        ++ List.replicate (β (Fin.last k) - 1) (Fin.last k) := by
  rw [specialMoveList, specialMoveList, List.finRange_succ_last, List.flatMap_append,
    List.flatMap_map, List.map_flatMap]
  simp

/-- **The temporal order of `HJO.Braid.specialBraid` is fixed by the index, and at the last index it
is the reverse of the one `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` needs.**

`HJO.Braid.specialBraid_eq_braidWord_replicate_mul` puts the moves of index `0` *last* in time, so
their braid stands leftmost. Here the moves of index `Fin.last k` come out *first* in time and
their braid stands rightmost, with the other points' braid to its left.

**This is why the reindexing the proof of `HJO.Mellit.mellitInduction_sweepWitness` calls for is not
a relabelling.** `HJO.Mellit.braidDataOfColouring` puts the appended component at index
`ℓ-1 = Fin.last (ℓ-1)`, and `HJO.Mellit.braidRep_specialBraid_dplusIter` needs it at index `0`. The
usual argument justifies the move by the permutation invariance of
`HJO.Braid.IsSpecialBraidData`, but that is a statement about the *predicate*, and every clause of
it does indeed quantify over all indices; `HJO.Braid.specialBraid` is not a predicate, and it fixes
the order in which the points move by their index. Comparing the two splittings, passing the
appended point from the last index to the first commutes its whole run of moves past the runs of all
the other points, which is not formal: `HJO.Braid.braidWord` reads `HJO.Braid.braidStep` at the
intermediate tuples, and those differ between the two orders.

**The commutation lemma this calls for.** That the braid of a sequence of moves is
unchanged when two moves of *distinct* points are exchanged is `HJO.Braid.braidWord_pair_comm`, in
all three cases of where the two points sit relative to the puncture; its iterated form, for an
arbitrary permutation of the move list, is `HJO.Braid.braidWord_perm_of_isSpecialBraidData`, and the
form this paragraph asks for — one component's whole run of moves commuting past the runs of all the
others — is `HJO.Braid.braidWord_append_comm_of_isSpecialBraidData`. None of them assumes
admissibility of the permuted sequence: every clause they read at an intermediate tuple is an
instance of `HJO.Braid.IsSpecialBraidData.injective`, `.ne_theta` or `.iterate_mem_Ioo` about the
iterates `nx_θ^j(v_i)` with `j < α_i`, by `HJO.Braid.moveTuple_apply_eq_iterate`.

So the *temporal* half of the reindexing is a theorem, and what it needs
of the data is the single hypothesis `HJO.Braid.IsSpecialBraidData`, which
`HJO.Mellit.isSpecialBraidData_braidDataOfColouring` proves of what
`HJO.Mellit.braidDataOfColouring` produces — at the rank the append chain reads it by
`HJO.Mellit.isSpecialBraidData_braidDataOfColouring_succ`.

What remains of the reindexing is the *index* half: the exchange lemmas move the entries of the move
list at a fixed tuple, whereas `HJO.Mellit.braidRep_specialBraid_dplusIter` wants the appended
component sitting at index `0` of the tuple, i.e. `specialBraid θ w β` compared with
`specialBraid θ (w ∘ σ) (β ∘ σ)` for the cycle `σ` carrying `0` to `Fin.last k`. That comparison is
not made here: relabelling `HJO.Braid.specialBraid` along a permutation of the index set is
`HJO.Braid.specialBraid_comp_perm`, proved later in `HJO/Shuffle/BraidIndexRelabel.lean`. -/
theorem specialBraid_eq_braidWord_mul_replicate_last (θ : ℚ) (w : Fin (k + 1) → ℚ)
    (β : Fin (k + 1) → ℕ) :
    specialBraid θ w β
      = braidWord θ (moveTuple θ w (List.replicate (β (Fin.last k) - 1) (Fin.last k)))
            ((specialMoveList (β ∘ Fin.castSucc)).map Fin.castSucc) *
          braidWord θ w (List.replicate (β (Fin.last k) - 1) (Fin.last k)) := by
  rw [specialBraid, specialMoveList_split_last, braidWord_append]

/-! ### The rank of an appended point that lies above the others -/

/-- **A point of index `0` above every other entry has rank `k + 1`**, so its train is the full
`T_{k+1↘1}`. -/
theorem entryRank_zero_of_forall_lt {w : Fin (k + 1) → ℚ} (h : ∀ t : Fin k, w t.succ < w 0) :
    entryRank w 0 = k + 1 := by
  have huniv : ({t : Fin k | (w ∘ Fin.succAbove 0) t ≤ w 0} : Finset (Fin k)) = univ :=
    filter_true_of_mem fun t _ => (h t).le
  rw [entryRank_self_succAbove w 0, huniv, card_univ, Fintype.card_fin]

/-! ### The other points' phase -/

/-- **`HJO.Braid.specialBraid_mul_trainDown_one` with the multiplicity-one hypothesis on the
inserted point dropped.**

Let `(w, β)` be special-braid data of rank `k + 1` whose entry of index `0` is Mellit's start
`1 - θ`. The moves of the *other* points — all of them, the point of index `0` standing still
throughout — conjugate to `φ*₊(B_{s,v,α})` for the deleted data `v = w ∘ Fin.succ`,
`α = β ∘ Fin.succ`:
`b_{others}(w)·T_{rk_w(0)↘1} = T_{rk_{w'}(0)↘1}·φ*₊(B_{s,v,α})`.

`HJO.Braid.specialBraid_mul_trainDown_one` is the case `β_0 = 1`, where the other points' moves
are *all* the moves and the left-hand side is `B_{s,w,β}` itself. The proof is the same: what
`HJO.Braid.braidWord_map_succAbove_mul_trainDown_one` needs of the sequence is that each of its
suffixes leaves the tuple admissible, and that is read off the iterate count, which here is bounded
by `β_t - 1` because the sequence is a *suffix* of `HJO.Braid.specialMoveList β` rather than equal
to it (`HJO.Braid.specialMoveList_split_zero`).

**The standing point does not have to sit at `1 - θ`**, and this is the isotopy clause of
`HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le` read on the data: what the ranks see is
the *order*, so the entry of index `0` may lie anywhere weakly below `1 - θ` provided no iterate of
another point separates it from `1 - θ`. The separation clause is `hgap`, `nx_θ^i(w_t) < w_0 + θ`;
since `w_0 + θ = 1` at the value `w_0 = 1 - θ` it is then free, and in general it says exactly that
no iterate of the data lies in `[w_0, 1-θ)` other than `w_0` itself. -/
theorem braidWord_specialMoveList_succ_mul_trainDown_one_of_le {s : ℚ} (hk : 1 ≤ k)
    (w : Fin (k + 1) → ℚ) (β : Fin (k + 1) → ℕ) (hdata : IsSpecialBraidData s θ (k + 1) w β)
    (hw0 : w 0 ≤ 1 - θ)
    (hgap : ∀ (t : Fin k) (i : ℕ), i + 1 < β t.succ → (nextCrossing θ)^[i] (w t.succ) < w 0 + θ) :
    braidWord θ w ((specialMoveList (β ∘ Fin.succ)).map Fin.succ) *
        braidTrainDown (k + 1) (entryRank w 0) 1
      = braidTrainDown (k + 1)
          (entryRank (moveTuple θ w ((specialMoveList (β ∘ Fin.succ)).map Fin.succ)) 0) 1 *
        phiPlusStar k hk (specialBraid θ (w ∘ Fin.succ) (β ∘ Fin.succ)) := by
  -- every move of every suffix is one of the iterates `HJO.Braid.IsSpecialBraidData` controls
  have hcount : ∀ l' : List (Fin k), l' <:+ specialMoveList (β ∘ Fin.succ) →
      ∀ t : Fin (k + 1), (l'.map Fin.succ).count t < β t := by
    intro l' hl' t
    obtain ⟨pre, hpre⟩ := hl'
    have hsuf : (l'.map Fin.succ) <:+ specialMoveList β :=
      ⟨List.replicate (β 0 - 1) 0 ++ pre.map Fin.succ, by
        rw [List.append_assoc, ← List.map_append, hpre, specialMoveList_split_zero]⟩
    have hle := hsuf.sublist.count_le t
    rw [count_specialMoveList] at hle
    have := hdata.one_le_mult t
    omega
  have hiter : ∀ l' : List (Fin k), ∀ t : Fin (k + 1),
      moveTuple θ w (l'.map Fin.succ) t
        = (nextCrossing θ)^[(l'.map Fin.succ).count t] (w t) :=
    fun l' t => moveTuple_apply_eq_iterate w _ t
  refine braidWord_map_succAbove_mul_trainDown_one_of_le hk 0 w hw0
    (specialMoveList (β ∘ Fin.succ)) ?_ ?_ ?_ ?_
  · intro l' hl' t t' htt
    simp only [Fin.succAbove_zero] at htt
    rw [hiter l' t, hiter l' t'] at htt
    exact (hdata.injective t t' _ _ (hcount l' hl' t) (hcount l' hl' t') htt).1
  · intro l' hl' t
    simp only [Fin.succAbove_zero]
    rw [hiter l' t]
    exact hdata.iterate_mem_Ioo t _ (hcount l' hl' t)
  · intro t₀ l' hl'
    simp only [Fin.succAbove_zero]
    rw [hiter l' t₀.succ]
    exact hdata.ne_theta _ _ (hcount l' ((List.suffix_cons t₀ l').trans hl') t₀.succ)
  · intro t₀ l' hl'
    simp only [Fin.succAbove_zero]
    rw [hiter l' t₀.succ]
    refine hgap t₀ _ ?_
    have h := hcount (t₀ :: l') hl' t₀.succ
    simpa using h

/-- **`HJO.Braid.specialBraid_mul_trainDown_one` with the multiplicity-one hypothesis dropped and
the standing point at the start `1 - θ`**: the isotopy clause of
`HJO.Braid.braidWord_specialMoveList_succ_mul_trainDown_one_of_le` is then `nx_θ^i(w_t) < 1`, which
`HJO.Braid.IsSpecialBraidData` supplies. -/
theorem braidWord_specialMoveList_succ_mul_trainDown_one {s : ℚ} (hk : 1 ≤ k)
    (w : Fin (k + 1) → ℚ) (β : Fin (k + 1) → ℕ) (hdata : IsSpecialBraidData s θ (k + 1) w β)
    (hw0 : w 0 = 1 - θ) :
    braidWord θ w ((specialMoveList (β ∘ Fin.succ)).map Fin.succ) *
        braidTrainDown (k + 1) (entryRank w 0) 1
      = braidTrainDown (k + 1)
          (entryRank (moveTuple θ w ((specialMoveList (β ∘ Fin.succ)).map Fin.succ)) 0) 1 *
        phiPlusStar k hk (specialBraid θ (w ∘ Fin.succ) (β ∘ Fin.succ)) := by
  refine braidWord_specialMoveList_succ_mul_trainDown_one_of_le hk w β hdata hw0.le
    fun t i hi => ?_
  have h := (hdata.iterate_mem_Ioo t.succ i (by omega)).2
  rw [hw0]
  linarith

/-! ### The two phases together -/

/-- **`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` up to the slope braid.** For special-braid
data `(w, β)` of rank `k + 1` whose entry of index `0` is the start `1 - θ` and lies above every
other entry and above every other final position of `HJO.Braid.positionPair`,

`B_{s,w,β} = b_{0^{β_0-1}}(w')·T_{k+1↘1}·φ*₊(B_{s,v,α})·T_{1↘k+1}`,

`w'` being the tuple after the other points have moved and `(v, α) = (w ∘ Fin.succ, β ∘ Fin.succ)`
the deleted data. The two trains are those of `HJO.Braid.appendRhs`, `T_{1↘k+1}` being the inverse
of `T_{k+1↘1}` by `HJO.Braid.trainUp_mul_trainUp_self`'s descending form.

What separates this from `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` is the evaluation of
the first factor, the appended point's own run of moves; see the module docstring for the two
reasons the naive form of that factor cannot be proved. -/
theorem specialBraid_eq_conj_phiPlusStar {s : ℚ} (hk : 1 ≤ k) (w : Fin (k + 1) → ℚ)
    (β : Fin (k + 1) → ℕ) (hdata : IsSpecialBraidData s θ (k + 1) w β) (hw0 : w 0 ≤ 1 - θ)
    (hgap : ∀ (t : Fin k) (i : ℕ), i + 1 < β t.succ → (nextCrossing θ)^[i] (w t.succ) < w 0 + θ)
    (hstart : ∀ t : Fin k, w t.succ < w 0)
    (hfinish : ∀ t : Fin k, (positionPair θ (w ∘ Fin.succ) (β ∘ Fin.succ)).2 t < w 0) :
    specialBraid θ w β
      = braidWord θ (moveTuple θ w ((specialMoveList (β ∘ Fin.succ)).map Fin.succ))
            (List.replicate (β 0 - 1) 0) *
          braidTrainDown (k + 1) (k + 1) 1 *
          phiPlusStar k hk (specialBraid θ (w ∘ Fin.succ) (β ∘ Fin.succ)) *
          braidTrainDown (k + 1) 1 (k + 1) := by
  set L : List (Fin (k + 1)) := (specialMoveList (β ∘ Fin.succ)).map Fin.succ with hL
  -- the appended point is above the others at the start, and still above them at the finish
  have hrank : entryRank w 0 = k + 1 := entryRank_zero_of_forall_lt hstart
  have hmove : ∀ t : Fin k, moveTuple θ w L t.succ
      = (positionPair θ (w ∘ Fin.succ) (β ∘ Fin.succ)).2 t := by
    intro t
    have h := congrFun (moveTuple_comp_succAbove (θ := θ) w 0 (specialMoveList (β ∘ Fin.succ))) t
    simp only [Fin.succAbove_zero, Function.comp_apply] at h
    rw [hL, h, moveTuple_specialMoveList]
  have h0 : moveTuple θ w L 0 = w 0 := by
    rw [hL]
    exact moveTuple_map_succAbove_self w 0 (specialMoveList (β ∘ Fin.succ))
  have hrank' : entryRank (moveTuple θ w L) 0 = k + 1 := by
    refine entryRank_zero_of_forall_lt fun t => ?_
    rw [hmove t, h0]
    exact hfinish t
  -- the other points' phase, and the train that undoes the conjugation
  have hothers := braidWord_specialMoveList_succ_mul_trainDown_one_of_le hk w β hdata hw0 hgap
  rw [hrank, hrank'] at hothers
  have hinv : braidTrainDown (k + 1) (k + 1) 1 * braidTrainDown (k + 1) 1 (k + 1) = 1 :=
    trainDown_mul_trainDown_self (isBraidSystem_braidGenT (k + 1)) (by omega) le_rfl
      (by omega) (by omega)
  calc specialBraid θ w β
      = braidWord θ (moveTuple θ w L) (List.replicate (β 0 - 1) 0) * braidWord θ w L :=
        specialBraid_eq_braidWord_replicate_mul θ w β
    _ = braidWord θ (moveTuple θ w L) (List.replicate (β 0 - 1) 0) *
          (braidWord θ w L * (braidTrainDown (k + 1) (k + 1) 1 *
            braidTrainDown (k + 1) 1 (k + 1))) := by rw [hinv, mul_one]
    _ = braidWord θ (moveTuple θ w L) (List.replicate (β 0 - 1) 0) *
          ((braidWord θ w L * braidTrainDown (k + 1) (k + 1) 1) *
            braidTrainDown (k + 1) 1 (k + 1)) := by rw [mul_assoc]
    _ = braidWord θ (moveTuple θ w L) (List.replicate (β 0 - 1) 0) *
          braidTrainDown (k + 1) (k + 1) 1 *
          phiPlusStar k hk (specialBraid θ (w ∘ Fin.succ) (β ∘ Fin.succ)) *
          braidTrainDown (k + 1) 1 (k + 1) := by
        rw [hothers]
        simp only [mul_assoc]

end HJO.Braid

end
