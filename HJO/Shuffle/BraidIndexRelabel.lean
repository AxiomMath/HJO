/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidMoveCommPerm
public import HJO.Shuffle.BraidCompAppendData
public meta import HJO.Attr

/-! # Relabelling the index set of a special braid

`HJO.Braid.specialBraid` fixes two things about a sequence of moves: *when* each point moves,
and *which index* each point carries. `HJO.Braid.specialBraid_comp_perm` settles the first — the
braid of a sequence of moves depends only on the multiset of moves, so the temporal order costs
nothing. This file settles the second: the braid depends on the *tuple* and not on the labelling of
the tuple's index set.

## Main results

* `HJO.Braid.braidWord_comp_perm` — **the core, with no hypothesis at all**: for every permutation
  `σ` of the index set, `b_{l}(w ∘ σ) = b_{σ(l)}(w)`. Nothing about admissibility, about `θ`, or
  about the positions is needed: `HJO.Braid.entryRank` counts entries and not indices
  (`HJO.Braid.entryRank_comp_perm`), and a relabelled move acts on the relabelled tuple
  (`HJO.Braid.moveOne_comp_perm`), so every letter `HJO.Braid.braidStep` emits is literally the same
  letter.
* `HJO.Braid.specialBraid_comp_perm` — **the index half of the reindexing**:
  `B_{s,v∘σ,α∘σ} = B_{s,v,α}` for special-braid data `(v, α)` and any permutation `σ` of
  `Fin k`. The one hypothesis is `HJO.Braid.IsSpecialBraidData`, and it is spent *only* on the
  temporal half: relabelling turns the `i`-blocks of `HJO.Braid.specialBraid` into the `σ(i)`-blocks
  in a different order, and `HJO.Braid.specialBraid_comp_perm` reorders them back.
* `HJO.Braid.IsSpecialBraidData.comp_perm` — `HJO.Braid.IsSpecialBraidData` is itself invariant
  under relabelling, so the relabelled data is again data and the statement above composes with
  itself.
* `HJO.Braid.rotateLast`, `HJO.Braid.rotateLast_zero`, `HJO.Braid.rotateLast_succ` — the
  permutation the append step wants: the cycle carrying `0` to `Fin.last k` and `t.succ` to
  `t.castSucc`, i.e. the inverse of `finRotate`. It is the *order-preserving* choice on the
  remaining indices, which is what makes the deleted data come out as `w ∘ Fin.castSucc` rather
  than some reshuffling of it.
* `HJO.Braid.specialBraid_comp_rotateLast` — the two combined, in the shape the append step reads:
  `B_{s,w,β} = B_{s,w∘ρ,β∘ρ}` with `(w∘ρ) 0 = w (Fin.last k)` and
  `(w∘ρ) ∘ Fin.succ = w ∘ Fin.castSucc`.
* `HJO.Mellit.braidDataOfColouring_snd_last_succ`,
  `HJO.Mellit.braidDataOfColouring_fst_last_succ_ne` — the last-index facts about
  `HJO.Mellit.braidDataOfColouring`, transported to `Fin.last k` at rank `k + 1`, which is where
  `HJO.Braid.rotateLast` reads them.
* `HJO.Mellit.braidDataOfColouring_fst_comp_castSucc`,
  `HJO.Mellit.braidDataOfColouring_snd_comp_castSucc` — deleting the last index of the colouring
  data is *lowering its rank*: `HJO.Mellit.braidDataOfColouring` reads its index only through
  `(i : ℕ)`.
* `HJO.Mellit.sweepIn_braidRep_specialBraid_rotateLast` —
  `HJO.Mellit.braidRep_specialBraid_dplusIter` at the *relabelled* colouring data, with `hdata` and
  `hβ` both discharged and the remaining five hypotheses — `HJO.Braid.IsAppendSetup`, `hw₀`, `hgap`,
  `hstart`, `hmove` — still binders. Its left-hand side is `π_{k+1}` of the colouring's *own* braid,
  the relabelling being invisible there by `HJO.Braid.specialBraid_comp_rotateLast`, and the `π_k`
  on its right-hand side is `π_k` of the *same colouring one rank down*. So the clause now composes
  with itself, which is what the induction on the return composition of
  `HJO.Mellit.mellitInduction_sweepWitness` needs.

## Implementation notes

### Why the index half is bookkeeping and the temporal half is not

`HJO.Braid.braidStep` reads a tuple `w` at a moving index `i` through four quantities: `rk_w(i)`,
`rk_{next_i(w)}(i)`, whether `w_i < θ`, and `w_i` itself. Every one of them is invariant under
relabelling, `HJO.Braid.entryRank` being a count of entries `≤ w_i` and a permutation of the index
set being a bijection of what is counted. So `b_i(w ∘ σ) = b_{σ(i)}(w)` *as letters of the braid
monoid*, with no side condition, and the same holds along a whole sequence of moves. That is
`HJO.Braid.braidWord_comp_perm`, and it is an identity of the free-monoid words before any braid
relation is used.

What relabelling does change is the *order* in which `HJO.Braid.specialBraid` schedules the blocks:
the moves of `HJO.Braid.specialBraid` for `α ∘ σ` run through the blocks of `σ(0), σ(1), …` in that
order, which is the blocks of `α` in the order `σ` lists them. Turning that back into increasing
order is exactly `HJO.Braid.specialBraid_comp_perm`, and it is the only place
`HJO.Braid.IsSpecialBraidData` is spent. So the reindexing obligation is one obligation, not two,
and its hard half is the temporal one.

### What this is for

`HJO.Mellit.braidRep_specialBraid_dplusIter` peels the component of index `0` off a rank-`k+1`
tuple, and its hypotheses `hβ : β_0 = A(a+b) - 1` and `hw₀ : w_0 = 1 - θ - δ` are about that index.
`HJO.Mellit.braidDataOfColouring` puts the appended component at the *last* index, and the
facts about it — `HJO.Mellit.braidDataOfColouring_snd_last` and
`HJO.Mellit.braidDataOfColouring_fst_last_ne` — are stated there. `HJO.Braid.rotateLast` is the
translation, and it is faithful in both directions at once: it moves the last component to index `0`
*and* leaves the other components in their original order at `Fin.succ`, so
`HJO.Mellit.braidRep_specialBraid_dplusIter`'s `π_k(B_{s,v,α})` becomes the colouring data with its
last component dropped, which is what an induction on the return composition needs.

**No hypothesis on `q`, `u` or any field.** Everything in the `HJO.Braid` section lives in
`HJO.Braid.BraidMonoid` and is pure combinatorics of `Fin k`; `HJO.Braid.braidMonoid_nontrivial`
rules out the identities being vacuous.

## References

This file concerns `HJO.Braid.specialBraid`, `HJO.Braid.braidWord`, `HJO.Braid.braidStep`,
`HJO.Braid.entryRank`, `HJO.Braid.IsSpecialBraidData`, `HJO.Braid.specialBraid_comp_perm`,
`HJO.Mellit.braidRep_specialBraid_dplusIter`, `HJO.Mellit.mellitInduction_sweepWitness` and
`HJO.Mellit.braidDataOfColouring`.
-/

@[expose] public section

open Finset

namespace HJO.Braid

variable {k : ℕ}

/-! ### The rank is blind to the index labelling -/

/-- **`HJO.Braid.entryRank` counts entries, not indices.** Relabelling the index set by `σ` carries
the rank of `i` in `w ∘ σ` to the rank of `σ i` in `w`, because `σ` is a bijection of the set being
counted. -/
theorem entryRank_comp_perm {β : Type*} [LinearOrder β] (σ : Equiv.Perm (Fin k)) (w : Fin k → β)
    (i : Fin k) : entryRank (w ∘ σ) i = entryRank w (σ i) := by
  rw [entryRank, entryRank]
  refine Finset.card_equiv σ fun j => ?_
  simp

/-! ### A relabelled move acts on the relabelled tuple -/

/-- Moving the entry of index `i` of `w ∘ σ` is moving the entry of index `σ i` of `w`, read through
`σ` again. -/
theorem moveOne_comp_perm (θ : ℚ) (σ : Equiv.Perm (Fin k)) (w : Fin k → ℚ) (i : Fin k) :
    moveOne θ (w ∘ σ) i = moveOne θ w (σ i) ∘ σ := by
  funext j
  by_cases h : j = i
  · subst h
    simp only [Function.comp_apply, moveOne_self]
  · rw [moveOne_of_ne _ _ h, Function.comp_apply, Function.comp_apply,
      moveOne_of_ne _ _ (fun hc => h (σ.injective hc))]

/-- **A sequence of moves commutes with relabelling.** The tuple left by the moves `l` on `w ∘ σ` is
the tuple left by the relabelled moves `σ(l)` on `w`, read through `σ`. -/
theorem moveTuple_comp_perm (θ : ℚ) (σ : Equiv.Perm (Fin k)) (w : Fin k → ℚ) (l : List (Fin k)) :
    moveTuple θ (w ∘ σ) l = moveTuple θ w (l.map σ) ∘ σ := by
  induction l with
  | nil => rw [List.map_nil, moveTuple_nil, moveTuple_nil]
  | cons i l ih =>
    rw [moveTuple_cons, ih, moveOne_comp_perm, List.map_cons, moveTuple_cons]

/-! ### The letter of a move is unchanged -/

/-- **`HJO.Braid.braidStep` emits the same letter after relabelling.** All four quantities it reads
— the two ranks, the side of the puncture, and the position itself — are carried by
`HJO.Braid.entryRank_comp_perm` and `HJO.Braid.moveOne_comp_perm`. No hypothesis. -/
theorem braidStep_comp_perm (θ : ℚ) (σ : Equiv.Perm (Fin k)) (w : Fin k → ℚ) (i : Fin k) :
    braidStep θ (w ∘ σ) i = braidStep θ w (σ i) := by
  rw [braidStep, braidStep, moveOne_comp_perm, entryRank_comp_perm, entryRank_comp_perm,
    Function.comp_apply]

/-! ### The core: the braid of a sequence of moves is blind to the labelling -/

/-- **The index half of the reindexing, at the level of `HJO.Braid.braidWord` and with no
hypothesis**: `b_{i_1, …, i_l}(w ∘ σ) = b_{σ(i_1), …, σ(i_l)}(w)`.

This is an identity of the words `HJO.Braid.braidWord` builds, before any braid relation or any
admissibility clause is used: relabelling the index set permutes which *entry* each move touches
and leaves every letter alone. -/
theorem braidWord_comp_perm (θ : ℚ) (σ : Equiv.Perm (Fin k)) (w : Fin k → ℚ) (l : List (Fin k)) :
    braidWord θ (w ∘ σ) l = braidWord θ w (l.map σ) := by
  induction l with
  | nil => rw [List.map_nil, braidWord_nil, braidWord_nil]
  | cons i l ih =>
    rw [braidWord_cons, ih, moveTuple_comp_perm, braidStep_comp_perm, List.map_cons,
      braidWord_cons]

/-! ### The move list of a relabelled multiplicity vector -/

/-- **Relabelling `HJO.Braid.specialBraid`'s move sequence permutes it.** The sequence of `α ∘ σ`
carries the index `i` exactly `α_{σ i} - 1` times, so pushing it forward along `σ` gives a list
carrying each index `t` exactly `α_t - 1` times: a permutation of the sequence of `α`. -/
theorem specialMoveList_comp_perm_perm (σ : Equiv.Perm (Fin k)) (α : Fin k → ℕ) :
    ((specialMoveList (α ∘ σ)).map σ).Perm (specialMoveList α) := by
  rw [List.perm_iff_count]
  intro t
  have h : t = σ (σ.symm t) := (σ.apply_symm_apply t).symm
  rw [h, List.count_map_of_injective _ _ σ.injective, count_specialMoveList,
    count_specialMoveList, Function.comp_apply]

/-! ### `HJO.Braid.IsSpecialBraidData` is invariant under relabelling -/

/-- **Relabelled special-braid data is special-braid data.** Every clause of
`HJO.Braid.IsSpecialBraidData` is a statement about the *family* of iterates `nx_θ^j(v_i)` with
`j < α_i`, and relabelling the index set does not change that family; the distinctness clause
transports because `σ` is injective. -/
theorem IsSpecialBraidData.comp_perm {s θ : ℚ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (hdata : IsSpecialBraidData s θ k v α) (σ : Equiv.Perm (Fin k)) :
    IsSpecialBraidData s θ k (v ∘ σ) (α ∘ σ) where
  slope_pos := hdata.slope_pos
  theta_spec := hdata.theta_spec
  mem_Ioo i := hdata.mem_Ioo (σ i)
  one_le_mult i := hdata.one_le_mult (σ i)
  ne_theta i j hj := hdata.ne_theta (σ i) j hj
  injective i i' j j' hj hj' h :=
    ⟨σ.injective (hdata.injective (σ i) (σ i') j j' hj hj' h).1,
      (hdata.injective (σ i) (σ i') j j' hj hj' h).2⟩

/-! ### The index half of the reindexing -/

/-- **`HJO.Braid.specialBraid` depends on the tuple and not on the labelling of its index set**:
`B_{s,v∘σ,α∘σ} = B_{s,v,α}` for every permutation `σ` of `Fin k`.

The proof is the two halves of the reindexing composed. `HJO.Braid.braidWord_comp_perm` — no
hypothesis — turns the left-hand side into the braid of the relabelled move sequence
`σ(specialMoveList (α ∘ σ))`, which by `HJO.Braid.specialMoveList_comp_perm_perm` is a permutation
of `specialMoveList α`; `HJO.Braid.specialBraid_comp_perm`, in the form
`HJO.Braid.specialBraid_eq_braidWord_of_perm`, reorders it. So `HJO.Braid.IsSpecialBraidData` is
spent on the
*temporal* half alone, which is the whole content of the obligation. -/
@[hjo "lem_braid_move_comm_perm"]
theorem specialBraid_comp_perm {s θ : ℚ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (hdata : IsSpecialBraidData s θ k v α) (σ : Equiv.Perm (Fin k)) :
    specialBraid θ (v ∘ σ) (α ∘ σ) = specialBraid θ v α := by
  rw [specialBraid, braidWord_comp_perm]
  exact (specialBraid_eq_braidWord_of_perm hdata
    (specialMoveList_comp_perm_perm σ α).symm).symm

/-! ### The permutation the append step wants -/

/-- **The cycle carrying `0` to the last index.** The inverse of `finRotate`: it sends `0` to
`Fin.last k` and `t.succ` to `t.castSucc`, so relabelling a tuple along it presents the last
component at index `0` and leaves the other components in their original order. -/
def rotateLast (k : ℕ) : Equiv.Perm (Fin (k + 1)) := (finRotate (k + 1)).symm

/-- `ρ(0) = Fin.last k`: the appended component, which `HJO.Mellit.braidDataOfColouring` puts last,
is what index `0` of the relabelled tuple reads. -/
@[simp]
theorem rotateLast_zero (k : ℕ) : rotateLast k 0 = Fin.last k := by
  apply (finRotate (k + 1)).injective
  simp [rotateLast]

/-- `ρ(t.succ) = t.castSucc`: the other components keep their order, which is what makes the
deleted data of `HJO.Mellit.braidRep_specialBraid_dplusIter` come out as `w ∘ Fin.castSucc`. -/
@[simp]
theorem rotateLast_succ {k : ℕ} (t : Fin k) : rotateLast k t.succ = t.castSucc := by
  apply (finRotate (k + 1)).injective
  simp [rotateLast, Fin.coeSucc_eq_succ]

/-- The relabelled tuple reads the last entry at index `0`. -/
theorem comp_rotateLast_zero {β : Type*} (w : Fin (k + 1) → β) :
    (w ∘ rotateLast k) 0 = w (Fin.last k) := by
  rw [Function.comp_apply, rotateLast_zero]

/-- The relabelled tuple with index `0` deleted is the original tuple with its *last* entry
deleted — in the original order. -/
theorem comp_rotateLast_comp_succ {β : Type*} (w : Fin (k + 1) → β) :
    (w ∘ rotateLast k) ∘ Fin.succ = w ∘ Fin.castSucc := by
  funext t
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, rotateLast_succ]

/-- **The index half of the reindexing in the shape the append step reads it.** The special braid is
unchanged when the last component is relabelled to index `0`; by
`HJO.Braid.comp_rotateLast_zero` and `HJO.Braid.comp_rotateLast_comp_succ` the relabelled data has
`w (Fin.last k)` at index `0` and the other components, in order, at `Fin.succ`. -/
@[hjo "lem_braid_move_comm_perm"]
theorem specialBraid_comp_rotateLast {s θ : ℚ} {w : Fin (k + 1) → ℚ} {β : Fin (k + 1) → ℕ}
    (hdata : IsSpecialBraidData s θ (k + 1) w β) :
    specialBraid θ (w ∘ rotateLast k) (β ∘ rotateLast k) = specialBraid θ w β :=
  specialBraid_comp_perm hdata (rotateLast k)

/-- **`HJO.Braid.IsSpecialBraidData` at the relabelled data**, which is what the `hdata` slot of
`HJO.Mellit.braidRep_specialBraid_dplusIter` asks for once the appended component has been moved to
index `0`. -/
theorem IsSpecialBraidData.comp_rotateLast {s θ : ℚ} {w : Fin (k + 1) → ℚ} {β : Fin (k + 1) → ℕ}
    (hdata : IsSpecialBraidData s θ (k + 1) w β) :
    IsSpecialBraidData s θ (k + 1) (w ∘ rotateLast k) (β ∘ rotateLast k) :=
  hdata.comp_perm (rotateLast k)

/-- **The relabelling is not vacuous**: at the rank-`3` data of
`HJO.Braid.isSpecialBraidData_three` the two sides of
`HJO.Braid.specialBraid_comp_perm` are a genuine identity in a monoid with more than one element
(`HJO.Braid.braidMonoid_nontrivial`), the relabelled multiplicity vector and position tuple being
literally different functions from the originals. -/
theorem specialBraid_comp_perm_example :
    specialBraid (1 / 3 : ℚ) ((![1 / 10, 1 / 2, 9 / 10] : Fin 3 → ℚ) ∘ rotateLast 2)
        ((fun _ => 2) ∘ rotateLast 2)
      = specialBraid (1 / 3 : ℚ) (![1 / 10, 1 / 2, 9 / 10] : Fin 3 → ℚ) (fun _ => 2) :=
  specialBraid_comp_rotateLast isSpecialBraidData_three

/-- **The relabelling really relabels**: the position tuple of the witness above is not fixed by
`HJO.Braid.rotateLast`, so the identity is not an equation between two copies of the same term. The
physical points move in a *different temporal order* on the two sides — `9/10` first on the right,
`1/2` first on the left — which is exactly the content `HJO.Braid.specialBraid_comp_perm`
supplies. -/
theorem comp_rotateLast_example_ne :
    (![1 / 10, 1 / 2, 9 / 10] : Fin 3 → ℚ) ∘ rotateLast 2
      ≠ (![1 / 10, 1 / 2, 9 / 10] : Fin 3 → ℚ) := by
  intro h
  have := congrFun h 0
  rw [comp_rotateLast_zero] at this
  simp only [show (Fin.last 2) = (2 : Fin 3) from rfl, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at this
  norm_num at this

/-- **Neither side of the witness is the identity braid.** Both have letter length
`∑_i (α_i - 1) = 3` by `HJO.Braid.letterCount_specialBraid`, so the identity is an equation between
non-identity elements of a monoid `HJO.Braid.braidMonoid_nontrivial` shows is not trivial. -/
theorem specialBraid_comp_perm_example_ne_one :
    specialBraid (1 / 3 : ℚ) (![1 / 10, 1 / 2, 9 / 10] : Fin 3 → ℚ) (fun _ => 2) ≠ 1 := by
  intro h
  have hc := letterCount_specialBraid (θ := (1 / 3 : ℚ)) (k := 3) (by omega)
    (![1 / 10, 1 / 2, 9 / 10] : Fin 3 → ℚ) (fun _ => 2)
  rw [h, letterCount_one] at hc
  rw [Fin.sum_univ_three] at hc
  omega

end HJO.Braid

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {a b N : ℕ}

/-! ### Deleting the last index of the colouring data lowers its rank -/

/-- **The rank-`k+1` colouring data restricted to `Fin.castSucc` is the rank-`k` colouring data.**
`HJO.Mellit.braidDataOfColouring` reads its index only through `(i : ℕ)`
(`HJO.Mellit.braidDataOfColouring_fst`), so dropping the last index is literally lowering the rank —
no transport, and no reshuffling of the remaining components. Together with
`HJO.Braid.comp_rotateLast_comp_succ` this is what turns the `π_k` of
`HJO.Mellit.braidRep_specialBraid_dplusIter` into the
*same* colouring one rank down, which is what an induction on the return composition consumes. -/
theorem braidDataOfColouring_fst_comp_castSucc (a b N : ℕ) (y : Heights a b N) (η : ℚ) (k : ℕ) :
    (braidDataOfColouring a b N y η (k + 1)).1 ∘ Fin.castSucc
      = (braidDataOfColouring a b N y η k).1 := by
  funext t
  rw [Function.comp_apply, braidDataOfColouring_fst, braidDataOfColouring_fst, Fin.val_castSucc]

/-- The multiplicity half of `HJO.Mellit.braidDataOfColouring_fst_comp_castSucc`. -/
theorem braidDataOfColouring_snd_comp_castSucc (a b N : ℕ) (y : Heights a b N) (η : ℚ) (k : ℕ) :
    (braidDataOfColouring a b N y η (k + 1)).2 ∘ Fin.castSucc
      = (braidDataOfColouring a b N y η k).2 := by
  funext t
  rw [Function.comp_apply, braidDataOfColouring_snd, braidDataOfColouring_snd, Fin.val_castSucc]

/-! ### The last-index facts, at `Fin.last k` and rank `k + 1` -/

/-- **`HJO.Mellit.braidDataOfColouring_snd_last` at the index `HJO.Braid.rotateLast` reads.** The
part carried by the last component is `α_ℓ(a+b) - 1`, which is exactly the `β_0 = A(a+b) - 1` of
`HJO.Mellit.braidRep_specialBraid_dplusIter` at `A = α_ℓ` once the last component sits at index `0`.
The transport is the same dependent-type cast as in
`HJO.Mellit.isSpecialBraidData_braidDataOfColouring_succ`. -/
theorem braidDataOfColouring_snd_last_succ (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) (hα : α ≠ []) {k : ℕ}
    (hlen : α.length = k + 1) :
    (braidDataOfColouring a b N y η (k + 1)).2 (Fin.last k)
      = α.getLast hα * (a + b) - 1 := by
  have hpos : 0 < α.length := List.length_pos_of_ne_nil hα
  obtain rfl : k = α.length - 1 := by omega
  rw [braidDataOfColouring_snd, Fin.val_last,
    card_componentCrossingIndices_hasAboveReturns ha hb hN hab hηa hηs hηN hret
      (show α.length - 1 < α.length by omega),
    List.getLast_eq_getElem hα, Nat.mul_comm]

/-- **`HJO.Mellit.braidDataOfColouring_fst_last_ne` at the index `HJO.Braid.rotateLast` reads.**
Once the last component sits at index `0`, this is the statement that
`HJO.Mellit.braidRep_specialBraid_dplusIter`'s `hw₀ : w_0 = 1 - θ` is refuted *at that index* — so
the offset `δ` of `HJO.Braid.IsAppendSetup` is not optional, and `hw₀` can only be met in its offset
form. -/
theorem braidDataOfColouring_fst_last_succ_ne (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) (hle : a ≤ b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) (hα : α ≠ []) {k : ℕ}
    (hlen : α.length = k + 1) :
    (braidDataOfColouring a b N y η (k + 1)).1 (Fin.last k) ≠ 1 - sweepTheta a b N := by
  have hpos : 0 < α.length := List.length_pos_of_ne_nil hα
  obtain rfl : k = α.length - 1 := by omega
  rw [braidDataOfColouring_fst, Fin.val_last]
  exact ne_of_lt (fract_crossingAbscissa_componentTopIndex_last_lt ha hb hN hab hle hηa hηs hηN
    hret hα)

/-! ### `HJO.Mellit.braidRep_specialBraid_dplusIter` at the relabelled colouring data

The check below is the append clause of `HJO.Mellit.BraidClosedForm` — the eighth of the eight
lemmas that carry `hdata` (see `HJO/Shuffle/BraidCompAppendData.lean`), stated in
`HJO/Shuffle/MellitAppend.lean` — instantiated at the *relabelled* data of a composition colouring.
Two of its seven hypotheses are discharged rather than assumed: `hdata`, by
`HJO.Mellit.isSpecialBraidData_braidDataOfColouring_succ` composed with
`HJO.Braid.IsSpecialBraidData.comp_rotateLast`, and `hβ`, by
`HJO.Mellit.braidDataOfColouring_snd_last_succ` at `A = α_ℓ` — which is the `A = α_ℓ` of the proof
of `HJO.Mellit.mellitInduction_sweepWitness`, now reading the *last* part as the append step's part
rather than the first.

The remaining five — `HJO.Braid.IsAppendSetup`, `hw₀`, `hgap`, `hstart`, `hmove` — are still
binders, and they are now stated at the *colouring's own* indices: `hw₀` at `Fin.last k`,
`hgap` and `hstart` at `Fin.castSucc`. That is the whole gain, and it is a gain in statement and not
in content:

* `hw₀` is the one the colouring refutes at `δ = 0`
  (`HJO.Mellit.braidDataOfColouring_fst_last_succ_ne`). What it needs is the *value* of the offset,
  `δ = (η - aN)/D` with `D = a(aN+1)N + b(aN+1)N - 1`; the arithmetic is already inside the proof of
  `HJO.Mellit.fract_crossingAbscissa_componentTopIndex_last_lt`, which derives its strict inequality
  from exactly that identity together with
  `HJO.Mellit.componentTopIndex_last`. Nothing here supplies the identity as a statement.
* `hstart` asks that the appended component stand *above* all the others,
  `v_{castSucc t} < v_{last}`. That is a comparison between the positions of different components of
  the colouring — and nothing in this file's imports compares them.
-/

section AppendAtLast

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`HJO.Mellit.braidRep_specialBraid_dplusIter` at the relabelled colouring data.** The left-hand
side is the colouring's own `π_{k+1}(B_{s,v,α})` — the relabelling is invisible there, by
`HJO.Braid.specialBraid_comp_rotateLast` — and the `π_k` on the right-hand side is the braid of the
colouring data with its *last* component deleted, by
`HJO.Braid.comp_rotateLast_comp_succ`. That is the shape an induction on the return composition
needs, and it is what the index half of the reindexing buys. -/
theorem sweepIn_braidRep_specialBraid_rotateLast {q u r : L} {k : ℕ} {e δ : ℚ}
    {w : Fin (k + 1) → ℚ} {η : ℚ} {y : Heights a b N} {α : List ℕ}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : Nat.Coprime a b)
    (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η)
    (hηN : ((a * N : ℕ) : ℚ) < η) (hret : HasAboveReturns α y) (hlen : α.length = k + 1)
    (hα : α ≠ [])
    (H : IsAppendSetup a b (α.getLast hα) k e δ (sweepTheta a b N) w)
    (hw₀ : (braidDataOfColouring a b N y η (k + 1)).1 (Fin.last k)
      = 1 - sweepTheta a b N - δ)
    (hgap : ∀ (t : Fin k) (i : ℕ),
      i + 1 < (braidDataOfColouring a b N y η (k + 1)).2 t.castSucc →
      (nextCrossing (sweepTheta a b N))^[i]
          ((braidDataOfColouring a b N y η (k + 1)).1 t.castSucc) <
        (braidDataOfColouring a b N y η (k + 1)).1 (Fin.last k) + sweepTheta a b N)
    (hstart : ∀ t : Fin k, (braidDataOfColouring a b N y η (k + 1)).1 t.castSucc <
      (braidDataOfColouring a b N y η (k + 1)).1 (Fin.last k))
    (hmove : moveTuple (sweepTheta a b N)
      ((braidDataOfColouring a b N y η (k + 1)).1 ∘ rotateLast k)
      ((specialMoveList ((braidDataOfColouring a b N y η (k + 1)).2 ∘ Fin.castSucc)).map
        Fin.succ) = w) :
    sweepIn q u a b (k + 1)
        ((braidRepMellit q u hq hq1 hqp hr (k + 1)
            (specialBraid (sweepTheta a b N) (braidDataOfColouring a b N y η (k + 1)).1
              (braidDataOfColouring a b N y η (k + 1)).2)
          (dplusIterPiece q (k + 1)) : pieceSub L (k + 1)) : Total L)
      = ((-1 : L) ^ ((a - 1) * α.getLast hα) * (q * u) ^ (1 - (α.getLast hα : ℤ))) •
          stage (sweepWitness q u a b) Ω a b k (α.getLast hα) (sweepIn q u a b k
            ((braidRepMellit q u hq hq1 hqp hr k
                (specialBraid (sweepTheta a b N) (braidDataOfColouring a b N y η k).1
                  (braidDataOfColouring a b N y η k).2)
              (dplusIterPiece q k) : pieceSub L k) : Total L)) := by
  have hdata := (isSpecialBraidData_braidDataOfColouring_succ ha hb hN hab hηa hηs hηN
    hret hlen).comp_rotateLast
  have key := sweepIn_braidRep_specialBraid (u := u) hq hq1 hqp hr hΩ H hdata
    (by
      simp only [Function.comp_apply, rotateLast_zero]
      exact braidDataOfColouring_snd_last_succ ha hb hN hab hηa hηs hηN hret hα hlen)
    (by simpa only [Function.comp_apply, rotateLast_zero] using hw₀)
    (by
      intro t i hi
      simp only [Function.comp_apply, rotateLast_zero, rotateLast_succ] at hi ⊢
      exact hgap t i hi)
    (by
      intro t
      simp only [Function.comp_apply, rotateLast_zero, rotateLast_succ]
      exact hstart t)
    (by
      rw [show ((braidDataOfColouring a b N y η (k + 1)).2 ∘ rotateLast k) ∘ Fin.succ
            = (braidDataOfColouring a b N y η (k + 1)).2 ∘ Fin.castSucc from
          comp_rotateLast_comp_succ _]
      exact hmove)
  rwa [specialBraid_comp_rotateLast
      (isSpecialBraidData_braidDataOfColouring_succ ha hb hN hab hηa hηs hηN hret hlen),
    show ((braidDataOfColouring a b N y η (k + 1)).1 ∘ rotateLast k) ∘ Fin.succ
        = (braidDataOfColouring a b N y η k).1 from
      (comp_rotateLast_comp_succ _).trans (braidDataOfColouring_fst_comp_castSucc a b N y η k),
    show ((braidDataOfColouring a b N y η (k + 1)).2 ∘ rotateLast k) ∘ Fin.succ
        = (braidDataOfColouring a b N y η k).2 from
      (comp_rotateLast_comp_succ _).trans (braidDataOfColouring_snd_comp_castSucc a b N y η k)]
    at key

end AppendAtLast

end HJO.Mellit

end
