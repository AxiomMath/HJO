/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidMoveCommMixed
public import HJO.Shuffle.MellitProp57
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public meta import HJO.Attr

/-! # Order independence: the braid of a sequence of moves depends only on the multiset

`HJO.Braid.braidWord_pair_comm` exchanges **one** adjacent pair of moves. Its main application moves
a whole component from one index to another, which is a composite of many transpositions, each read
at its own intermediate tuple. This file is the iterated form — Mellit's own order-independence
statement — and the discharge of its admissibility hypothesis for special-braid data.

## Main results

* `HJO.Braid.moveTuple_perm` — the position tuple depends only on how many times each index moves.
* `HJO.Braid.braidWord_perm_of_pair_comm` — **the iterated form, abstractly**: if the two-move
  identity holds at every tuple a submultiset of the moves reaches, then `b_{i_1, …, i_l}(w)` is
  invariant under every permutation of `(i_1, …, i_l)`.
* `HJO.Braid.moveTuple_injective_of_isSpecialBraidData`,
  `HJO.Braid.moveTuple_mem_Ioo_of_isSpecialBraidData`,
  `HJO.Braid.moveTuple_ne_theta_of_isSpecialBraidData` —
  **`HJO.Braid.IsAdmissibleMoveSeq` for every ordering at once**: for `(v, α)` special-braid data,
  every intermediate tuple of every sequence of moves bounded by `α` has pairwise distinct entries,
  lies in `(0,1)^k`, and has no entry on the puncture.
* `HJO.Braid.braidWord_perm_of_isSpecialBraidData` — **the iterated form for the data that occurs**:
  for `(v, α)` special-braid data, every permutation of any move sequence bounded by `α` gives the
  same braid. No extra hypothesis: `HJO.Braid.IsSpecialBraidData`'s admissibility is a condition on
  the
  *multiset* of moves, so it is automatically inherited by every permutation and by every
  intermediate tuple of every permutation.
* `HJO.Braid.specialBraid_eq_braidWord_of_perm` — `B_{s,v,α}` is the braid of *any* ordering of its
  moves.
* `HJO.Braid.braidWord_append_comm_of_isSpecialBraidData` — the form the append step of
  `HJO.Mellit.mellitInduction_sweepWitness` asks for: one component's whole run of moves commutes
  past the runs of all the others, in one step and at every intermediate tuple.

## Implementation notes

### Why admissibility comes for free, which is the whole point

Mellit's Lemma 5.9 assumes that the sequence *and all its permutations* are admissible; the
hypothesis is left standing, and for a general sequence it has to be, since a permutation can make
two points collide that did not collide before. For the sequences that actually occur it is not an
extra assumption at all. `HJO.Braid.moveTuple_apply_eq_iterate` says the entry a sequence of moves
leaves at `t` is `nx_θ^{(count of t)}(w_t)`, so an intermediate tuple of a sequence of moves is
determined by the *counts* of its suffix — and counts are permutation-invariant. Every clause
`HJO.Braid.braidWord_pair_comm` reads is then one of the finitely many separations that
`HJO.Braid.IsSpecialBraidData.injective` and `HJO.Braid.IsSpecialBraidData.ne_theta` already
assert about the iterates `nx_θ^j(v_i)` with `j < α_i`, and those clauses know nothing about order.

The one place care is needed is the two clauses `nx_θ(u_i) ≠ u_j` and `nx_θ(u_j) ≠ u_i`: they read
an iterate one step *beyond* the current tuple, so they need `count_i + 1 < α_i` rather than
`count_i < α_i`. That is exactly why the abstract lemma's hypothesis is indexed by the counts of
`i :: j :: l` and not of `l`: the two moves about to be performed are counted, and the bound
`≤ α_t - 1` then supplies the strict inequality through `one_le_mult`.

### The exchange lemma is stronger than its natural form, but not where the induction needs it

The exchange lemma in its natural form asks that each of the three tuples obtained from `w`
by advancing the `i`-th entry, the `j`-th entry, and both, have pairwise distinct entries.
`HJO.Braid.braidWord_pair_comm` asks instead for the three comparisons its proof actually reads —
`w_i ≠ w_j`, `nx_θ(w_i) ≠ w_j`, `nx_θ(w_j) ≠ w_i` — and for nothing about the other `k - 2` entries.
It is tempting to read that extra strength as what makes the induction below go through. It is not:
`HJO.Braid.moveTuple_injective_of_isSpecialBraidData` gives pairwise distinctness of *all* the
entries of every intermediate tuple, from the same single clause
`HJO.Braid.IsSpecialBraidData.injective`, so the weaker natural form of the exchange lemma would
be dischargeable here too and at the same price. What the extra strength buys is that the discharge
never has to *propagate* a property of the tuple from one intermediate stage to the next: the only
thing the induction carries is a bound on occurrence counts, and `List.Sublist.count_le` and
`List.Perm.count_eq` between them make that bound survive both the `cons` and the `trans` step.

### The reduction of a permutation to adjacent transpositions

`List.Perm` is generated by `nil`, `cons`, `swap` and `trans`, and the induction below is one case
per constructor: `swap` is `HJO.Braid.braidWord_swap_of_pair_comm` at an empty prefix, `cons` needs
in addition that the two tails leave the same tuple (`HJO.Braid.moveTuple_perm`) because the head's
factor is read there, and `trans` needs the count bound transported across the middle list, which
is `List.Perm.count_eq`. So Mellit's "it is enough to permute only two indices" is discharged, not
assumed.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, Lemma 5.9.
-/

@[expose] public section

namespace HJO.Braid

/-! ### The position tuple depends only on the counts -/

/-- **A permutation of the moves leaves the same position tuple.** Each entry is advanced once per
occurrence of its index (`HJO.Braid.moveTuple_apply_eq_iterate`), and a permutation preserves
occurrence counts. -/
theorem moveTuple_perm (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) {l₁ l₂ : List (Fin k)}
    (h : l₁.Perm l₂) : moveTuple θ w l₁ = moveTuple θ w l₂ := by
  funext t
  rw [moveTuple_apply_eq_iterate, moveTuple_apply_eq_iterate, h.count_eq t]

/-! ### The iterated form, abstractly -/

/-- **Order independence from the two-move identity.** If, for every list `l` of moves and every
pair `i ≠ j` such that `i :: j :: l` uses each index `t` at most `c t` times, the two-move words at
the tuple `l` has advanced agree, then the braid of a sequence of moves bounded by `c` is unchanged
by every permutation of that sequence.

This is the induction Mellit replaces by "it is enough to permute only two indices". The bound
`c` is what carries admissibility through the induction: it is permutation-invariant and decreases
along sublists, so the two-move hypothesis is available at every list the recursion visits. -/
theorem braidWord_perm_of_pair_comm (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (c : Fin k → ℕ)
    (H : ∀ (l : List (Fin k)) (i j : Fin k), i ≠ j → (∀ t, (i :: j :: l).count t ≤ c t) →
      braidWord θ (moveTuple θ w l) [i, j] = braidWord θ (moveTuple θ w l) [j, i])
    {l₁ l₂ : List (Fin k)} (hperm : l₁.Perm l₂) (hc : ∀ t, l₁.count t ≤ c t) :
    braidWord θ w l₁ = braidWord θ w l₂ := by
  induction hperm with
  | nil => rfl
  | @cons x l l' hp ih =>
    rw [braidWord_cons, braidWord_cons, moveTuple_perm θ w hp,
      ih fun t => le_trans ((List.sublist_cons_self x l).count_le t) (hc t)]
  | swap x y l =>
    by_cases hxy : y = x
    · rw [hxy]
    · simpa using braidWord_swap_of_pair_comm θ w hxy [] l (H l y x hxy hc)
  | @trans la lb lc hp₁ _ ih₁ ih₂ =>
    exact (ih₁ hc).trans (ih₂ fun t => by rw [← hp₁.count_eq t]; exact hc t)

/-! ### Admissibility of every intermediate tuple, for every ordering -/

/-- **Every index still has a move of the data left to spend.** A sequence bounded by `α_t - 1` at
each index leaves the `t`-th entry at the iterate `nx_θ^{count}(v_t)` with `count < α_t`, so every
entry of every intermediate tuple is one of the iterates `HJO.Braid.IsSpecialBraidData` controls. -/
theorem count_lt_of_isSpecialBraidData {s θ : ℚ} {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (hdata : IsSpecialBraidData s θ k v α) {l : List (Fin k)} (hc : ∀ t, l.count t ≤ α t - 1)
    (t : Fin k) : l.count t < α t := by
  have := hc t
  have := hdata.one_le_mult t
  omega

/-- **The first clause of `HJO.Braid.IsAdmissibleMoveSeq`, at every ordering**: the entries of every
intermediate tuple are pairwise distinct. The tuple is determined by the occurrence counts of the
moves already performed, so this is a single instance of
`HJO.Braid.IsSpecialBraidData.injective` and is blind to the order. -/
@[hjo "lem_braid_admissible_perm"]
theorem moveTuple_injective_of_isSpecialBraidData {s θ : ℚ} {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (hdata : IsSpecialBraidData s θ k v α) {l : List (Fin k)} (hc : ∀ t, l.count t ≤ α t - 1) :
    Function.Injective (moveTuple θ v l) := by
  intro t t' h
  rw [moveTuple_apply_eq_iterate, moveTuple_apply_eq_iterate] at h
  exact (hdata.injective t t' _ _ (count_lt_of_isSpecialBraidData hdata hc t)
    (count_lt_of_isSpecialBraidData hdata hc t') h).1

/-- **`w \in (0,1)^k` at every intermediate tuple, at every ordering.** This is the hypothesis
`HJO.Braid.braidWord_pair_comm` spends in the mixed case, and the only thing it spends it on. -/
@[hjo "lem_braid_admissible_perm"]
theorem moveTuple_mem_Ioo_of_isSpecialBraidData {s θ : ℚ} {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (hdata : IsSpecialBraidData s θ k v α) {l : List (Fin k)} (hc : ∀ t, l.count t ≤ α t - 1)
    (t : Fin k) : moveTuple θ v l t ∈ Set.Ioo (0 : ℚ) 1 := by
  rw [moveTuple_apply_eq_iterate]
  exact hdata.iterate_mem_Ioo t _ (count_lt_of_isSpecialBraidData hdata hc t)

/-- **The second clause of `HJO.Braid.IsAdmissibleMoveSeq`, at every ordering and for every entry**:
no entry of an intermediate tuple sits on the puncture, so in particular the entry about to move
does not. -/
@[hjo "lem_braid_admissible_perm"]
theorem moveTuple_ne_theta_of_isSpecialBraidData {s θ : ℚ} {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (hdata : IsSpecialBraidData s θ k v α) {l : List (Fin k)} (hc : ∀ t, l.count t ≤ α t - 1)
    (t : Fin k) : moveTuple θ v l t ≠ θ := by
  rw [moveTuple_apply_eq_iterate]
  exact hdata.ne_theta t _ (count_lt_of_isSpecialBraidData hdata hc t)

/-! ### The iterated form for special-braid data -/

/-- **Order independence for the data that occurs, with no admissibility hypothesis left over.**
For `(v, α)` special-braid data, any two sequences of moves that use each index `i` at most
`α_i - 1` times and are permutations of one another give the same braid.

Mellit's Lemma 5.9 carries the hypothesis that the sequence *and all its permutations* be
admissible. Here that hypothesis is discharged rather than assumed: every clause
`HJO.Braid.braidWord_pair_comm` reads at an intermediate tuple is an instance of
`HJO.Braid.IsSpecialBraidData.injective`, `HJO.Braid.IsSpecialBraidData.ne_theta` or
`HJO.Braid.IsSpecialBraidData.iterate_mem_Ioo` about the iterates `nx_θ^j(v_i)` with `j < α_i`, and
the intermediate tuple is determined by the *counts* of the suffix, which no reordering changes. -/
@[hjo "lem_braid_move_comm_perm"]
theorem braidWord_perm_of_isSpecialBraidData {s θ : ℚ} {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (hdata : IsSpecialBraidData s θ k v α) {l₁ l₂ : List (Fin k)}
    (hc : ∀ t, l₁.count t ≤ α t - 1) (hperm : l₁.Perm l₂) :
    braidWord θ v l₁ = braidWord θ v l₂ := by
  refine braidWord_perm_of_pair_comm θ v (fun t => α t - 1) ?_ hperm hc
  intro l i j hij hcij
  have hu : ∀ t, moveTuple θ v l t = (nextCrossing θ)^[l.count t] (v t) :=
    fun t => moveTuple_apply_eq_iterate v l t
  have hcl : ∀ t, l.count t ≤ α t - 1 := fun t =>
    le_trans (((List.sublist_cons_self j l).trans
      (List.sublist_cons_self i (j :: l))).count_le t) (hcij t)
  have hlt : ∀ t, l.count t < α t := count_lt_of_isSpecialBraidData hdata hcl
  -- the two indices about to move have one move *more* than that left, which is what the two
  -- `nextCrossing` clauses read
  have hci : (i :: j :: l).count i = l.count i + 1 := by
    rw [List.count_cons_self, List.count_cons_of_ne (Ne.symm hij)]
  have hcj : (i :: j :: l).count j = l.count j + 1 := by
    rw [List.count_cons_of_ne hij, List.count_cons_self]
  have hi1 : l.count i + 1 < α i := by
    have := hcij i; have := hdata.one_le_mult i; omega
  have hj1 : l.count j + 1 < α j := by
    have := hcij j; have := hdata.one_le_mult j; omega
  refine braidWord_pair_comm hij hdata.theta_mem_Ioo.1 hdata.theta_mem_Ioo.2
    (moveTuple_mem_Ioo_of_isSpecialBraidData hdata hcl)
    (moveTuple_ne_theta_of_isSpecialBraidData hdata hcl i)
    (moveTuple_ne_theta_of_isSpecialBraidData hdata hcl j)
    (fun h => hij (moveTuple_injective_of_isSpecialBraidData hdata hcl h)) ?_ ?_
  · rw [hu i, hu j, ← Function.iterate_succ_apply' (nextCrossing θ) (l.count i) (v i)]
    exact fun h => hij (hdata.injective i j _ _ hi1 (hlt j) h).1
  · rw [hu i, hu j, ← Function.iterate_succ_apply' (nextCrossing θ) (l.count j) (v j)]
    exact fun h => hij (hdata.injective j i _ _ hj1 (hlt i) h).1.symm

/-- **The special braid is the braid of any ordering of its moves.** `HJO.Braid.specialBraid` fixes
the temporal order by index; this says the choice costs nothing. -/
@[hjo "lem_braid_move_comm_perm"]
theorem specialBraid_eq_braidWord_of_perm {s θ : ℚ} {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (hdata : IsSpecialBraidData s θ k v α) {l : List (Fin k)}
    (hperm : (specialMoveList α).Perm l) : specialBraid θ v α = braidWord θ v l :=
  braidWord_perm_of_isSpecialBraidData hdata
    (fun t => (count_specialMoveList α t).le) hperm

/-- **One component's whole run of moves commutes past the runs of all the others.** This is the
form the append step of `HJO.Mellit.mellitInduction_sweepWitness` asks for: with `l₂` the `α_j - 1`
moves of the appended component and `l₁` the moves of everything else, the two orderings — appended
component first in time, or last — give the same braid, every intermediate tuple included. -/
@[hjo "lem_braid_move_comm_perm"]
theorem braidWord_append_comm_of_isSpecialBraidData {s θ : ℚ} {k : ℕ} {v : Fin k → ℚ}
    {α : Fin k → ℕ} (hdata : IsSpecialBraidData s θ k v α) (l₁ l₂ : List (Fin k))
    (hc : ∀ t, (l₁ ++ l₂).count t ≤ α t - 1) :
    braidWord θ v (l₁ ++ l₂) = braidWord θ v (l₂ ++ l₁) :=
  braidWord_perm_of_isSpecialBraidData hdata hc List.perm_append_comm

/-! ### The hypotheses are satisfiable, at a permutation no single swap reaches -/

/-- Special-braid data of rank `3` with every multiplicity `2`: at `θ = 1/3` the three points
`1/10`, `1/2`, `9/10` and their images `23/30`, `1/6`, `17/30` are six distinct numbers in `(0,1)`,
none equal to `θ`. -/
theorem isSpecialBraidData_three :
    IsSpecialBraidData 2 (1 / 3) 3 (![1 / 10, 1 / 2, 9 / 10] : Fin 3 → ℚ) (fun _ => 2) where
  slope_pos := by norm_num
  theta_spec := by norm_num
  mem_Ioo i := by fin_cases i <;> norm_num [Set.mem_Ioo]
  one_le_mult _ := one_le_two
  ne_theta i j hj := by
    interval_cases j <;> fin_cases i <;> norm_num [nextCrossing]
  injective i i' j j' hj hj' := by
    interval_cases j <;> interval_cases j' <;> fin_cases i <;> fin_cases i' <;>
      norm_num [nextCrossing, Function.iterate_one]

/-- **The iterated form does something the single swap does not.** Reversing the three moves of
`HJO.Braid.isSpecialBraidData_three` is an odd permutation of length `3` needing three adjacent
transpositions, each read at a different intermediate tuple; the braid is unchanged. -/
theorem specialBraid_three_eq_braidWord_reverse :
    specialBraid (1 / 3 : ℚ) (![1 / 10, 1 / 2, 9 / 10] : Fin 3 → ℚ) (fun _ => 2)
      = braidWord (1 / 3 : ℚ) (![1 / 10, 1 / 2, 9 / 10] : Fin 3 → ℚ) [2, 1, 0] :=
  specialBraid_eq_braidWord_of_perm isSpecialBraidData_three (by decide)

end HJO.Braid
