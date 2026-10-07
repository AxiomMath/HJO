/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public meta import HJO.Attr

/-! # Deleting two positions from a sequence

The two-letter analysis of the Carlsson--Mellit `χ` combinatorics compares a word of length `m`
with the word of length `m - 2` obtained by deleting the entries at two distinguished positions
`a ≠ b` — the positions carrying the maximal attacking pair. This file fixes that deletion.

## Main definitions

* `HJO.Dyck.pairComplEmb`: the increasing enumeration `s_1 < ⋯ < s_{m-2}` of the positions other
  than `a` and `b`, as an order embedding `Fin (m - 2) ↪o Fin m`.
* `HJO.Dyck.removePair`: the sequence `v^{(a,b)}`, of length `m - 2`, with `j`-th entry `v_{s_j}`.

## Main results

* `HJO.Dyck.removePair_comm`: the two deleted positions enter unordered.
* `HJO.Dyck.prod_removePair`, `HJO.Dyck.sum_removePair`: a product or sum over the entries of `v`
  splits as the one over `v^{(a,b)}` and the two deleted contributions.
* `HJO.Dyck.eq_of_removePair_eq`: a sequence is determined by `v^{(a,b)}` together with `v a` and
  `v b`. This is the injectivity half of the bijection the two-letter difference runs over.

## Implementation notes

The deletion is a *reindexing*, `v ∘ pairComplEmb hab`, and not a `List` operation: the words of
this layer are functions `Fin m → α`, so the enumeration of the surviving positions is where the
content sits, and `Finset.orderEmbOfFin` on `({a, b}ᶜ : Finset (Fin m))` is it.

`m - 2` is truncated subtraction, and no bound `2 ≤ m` is carried: the hypothesis `a ≠ b` already
forces `2 ≤ m`, since two distinct elements of `Fin m` exist only then, and
`Finset.card_compl_pair` computes the cardinality of the complement as `m - 2` from that
hypothesis alone. So the type is right without a side condition, and at `m < 2` the statement is
vacuous rather than false.

`hab : a ≠ b` is an argument of `pairComplEmb` and of `removePair` rather than a hypothesis of the
lemmas, because the enumeration cannot be written without it — `Finset.orderEmbOfFin` needs the
cardinality — so the subject of every statement below mentions it. `removePair_comm` is then the
statement that the subject does not depend on which of the two proofs is supplied.

## References

`HJO.Dyck.removePair` transcribes E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, §4 (the proof of "`χ` is symmetric"), where `w_S` denotes the sequence `w`
with the entries `w_a` and `w_b` removed, for `S = {1, …, k} ∖ {a, b}`. Consumed by
`HJO.Dyck.IsMaximalPair.card_invSet_erase` and
`HJO.Dyck.IsMaximalPair.twoLetterChar_sub_twoLetterChar_erase`.
-/

@[expose] public section

open Finset

namespace Finset

/-- The complement of a pair of distinct elements has two elements fewer than the whole type. -/
theorem card_compl_pair {α : Type*} [Fintype α] [DecidableEq α] {a b : α} (hab : a ≠ b) :
    #({a, b}ᶜ : Finset α) = Fintype.card α - 2 := by
  rw [card_compl, card_pair hab]

end Finset

namespace HJO.Dyck

variable {α : Type*} {m : ℕ} {a b : Fin m}

/-- The increasing enumeration `s_1 < s_2 < ⋯ < s_{m-2}` of the positions other than the two
distinct positions `a` and `b`, as an order embedding `Fin (m - 2) ↪o Fin m`. -/
def pairComplEmb (hab : a ≠ b) : Fin (m - 2) ↪o Fin m :=
  ({a, b}ᶜ : Finset (Fin m)).orderEmbOfFin (by
    rw [Finset.card_compl_pair hab, Fintype.card_fin])

/-- `pairComplEmb` is the increasing enumeration of `{a, b}ᶜ` in the sense of
`Finset.orderEmbOfFin`, hence the unique strictly monotone map `Fin (m - 2) → Fin m` with image
`{a, b}ᶜ` by `Finset.orderEmbOfFin_unique`. -/
theorem pairComplEmb_eq_orderEmbOfFin (hab : a ≠ b)
    (h : #({a, b}ᶜ : Finset (Fin m)) = m - 2) :
    pairComplEmb hab = ({a, b}ᶜ : Finset (Fin m)).orderEmbOfFin h :=
  rfl

theorem pairComplEmb_mem (hab : a ≠ b) (j : Fin (m - 2)) :
    pairComplEmb hab j ∈ ({a, b}ᶜ : Finset (Fin m)) :=
  Finset.orderEmbOfFin_mem _ _ j

theorem pairComplEmb_ne_left (hab : a ≠ b) (j : Fin (m - 2)) : pairComplEmb hab j ≠ a := by
  have h := pairComplEmb_mem hab j
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton] at h
  tauto

theorem pairComplEmb_ne_right (hab : a ≠ b) (j : Fin (m - 2)) : pairComplEmb hab j ≠ b := by
  have h := pairComplEmb_mem hab j
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton] at h
  tauto

/-- Every position other than `a` and `b` occurs in the enumeration `pairComplEmb`. -/
theorem exists_pairComplEmb_eq (hab : a ≠ b) {i : Fin m} (hia : i ≠ a) (hib : i ≠ b) :
    ∃ j, pairComplEmb hab j = i := by
  have h : i ∈ Set.range (pairComplEmb hab) := by
    rw [pairComplEmb, Finset.range_orderEmbOfFin]
    simp [hia, hib]
  exact h

/-- The enumeration of the positions other than `a` and `b` does not depend on the order of the
two: it is an enumeration of the set `{a, b}ᶜ`. -/
theorem pairComplEmb_comm (hab : a ≠ b) :
    (pairComplEmb (Ne.symm hab) : Fin (m - 2) → Fin m) = pairComplEmb hab :=
  Finset.orderEmbOfFin_unique _
    (fun j => by simpa [Finset.pair_comm] using pairComplEmb_mem (Ne.symm hab) j)
    (pairComplEmb (Ne.symm hab)).strictMono

/-- The sequence `v^{(a,b)}` of length `m - 2` obtained from a sequence `v` of length `m` by
deleting the entries at the two distinct positions `a` and `b`: writing
`s_1 < s_2 < ⋯ < s_{m-2}` for the increasing enumeration of the other positions, its `j`-th entry
is `v_{s_j}`. -/
@[hjo "def_dyck_delete"]
def removePair (hab : a ≠ b) (v : Fin m → α) : Fin (m - 2) → α :=
  fun j => v (pairComplEmb hab j)

theorem removePair_apply (hab : a ≠ b) (v : Fin m → α) (j : Fin (m - 2)) :
    removePair hab v j = v (pairComplEmb hab j) :=
  rfl

/-- The two deleted positions enter unordered: `v^{(a,b)} = v^{(b,a)}`. -/
theorem removePair_comm (hab : a ≠ b) (v : Fin m → α) :
    removePair (Ne.symm hab) v = removePair hab v := by
  funext j
  rw [removePair_apply, removePair_apply,
    show pairComplEmb (Ne.symm hab) j = pairComplEmb hab j from congrFun (pairComplEmb_comm hab) j]

@[simp]
theorem removePair_const (hab : a ≠ b) (c : α) : removePair hab (fun _ => c) = fun _ => c :=
  rfl

/-- A product over the entries of `v` splits as the product over the entries of `v^{(a,b)}` times
the contributions of the two deleted entries. -/
@[to_additive]
theorem prod_removePair {M : Type*} [CommMonoid M] (hab : a ≠ b) (f : α → M) (v : Fin m → α) :
    (∏ j, f (removePair hab v j)) * (f (v a) * f (v b)) = ∏ i, f (v i) := by
  have h : (∏ j, f (removePair hab v j)) = ∏ i ∈ ({a, b}ᶜ : Finset (Fin m)), f (v i) := by
    rw [← Finset.map_orderEmbOfFin_univ ({a, b}ᶜ : Finset (Fin m))
      ((Finset.card_compl_pair hab).trans (by rw [Fintype.card_fin])), Finset.prod_map]
    rfl
  rw [h, ← Finset.prod_pair (f := fun i => f (v i)) hab, Finset.prod_compl_mul_prod]

/-- A sequence is determined by the sequence with two entries deleted together with those two
entries: the injectivity half of the bijection between the two-letter words with prescribed
letters at `a` and `b` and the two-letter words of length `m - 2`. -/
theorem eq_of_removePair_eq (hab : a ≠ b) {v w : Fin m → α} (ha : v a = w a) (hb : v b = w b)
    (h : removePair hab v = removePair hab w) : v = w := by
  funext i
  by_cases hia : i = a
  · rw [hia]; exact ha
  by_cases hib : i = b
  · rw [hib]; exact hb
  obtain ⟨j, hj⟩ := exists_pairComplEmb_eq hab hia hib
  have hj' := congrFun h j
  rw [removePair_apply, removePair_apply, hj] at hj'
  exact hj'

/-! ### Value checks

At `m = 5`, `a = 1`, `b = 3` the surviving positions are `0 < 2 < 4`, so `v^{(1,3)}` is
`(v_0, v_2, v_4)`. The enumeration is the content: `Finset.sort` does not reduce in the kernel, so
the order is pinned by `Finset.orderEmbOfFin_unique` against an explicit strictly monotone map,
and only the *set* of surviving positions is settled by computation. -/

theorem compl_pair_value_check : ({(1 : Fin 5), 3}ᶜ : Finset (Fin 5)) = {0, 2, 4} := by decide

theorem pairComplEmb_value_check :
    (pairComplEmb (a := (1 : Fin 5)) (b := (3 : Fin 5)) (by decide) : Fin (5 - 2) → Fin 5) =
      fun j => ⟨2 * (j : ℕ), by omega⟩ :=
  (Finset.orderEmbOfFin_unique
    (f := fun j : Fin (5 - 2) => (⟨2 * (j : ℕ), by omega⟩ : Fin 5)) _ (by decide) (by decide)).symm

end HJO.Dyck
