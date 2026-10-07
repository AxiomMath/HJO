/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.HalfTurnIdes
public meta import HJO.Attr

/-! # The half turn reverses and complements the reading word

The reading word of a parking function `π` in the `aN × bN` rectangle lists its `bN` labels in
decreasing order of the rank of the north step each one marks; the above-diagonal reading word of an
above-diagonal parking function does the same with the above-diagonal rank. For `0 < a`, and for
`0 < N` above the diagonal, neither order has a tie, so each word is the unique listing of the
labels sorted by the relevant rank.

The half turn carries the north steps of `P_π` onto those of `P̂_π` reversing the rank order, and
complements every label, so it reverses the reading word and replaces each letter `ℓ` by
`bN + 1 - ℓ`:

  `ŵ = reverse (ℓ ↦ bN + 1 - ℓ)(w)`,  equivalently  `ŵ_k = bN + 1 - w_{bN+1-k}`.

## Main results

* `HJO.ParkingFunctions.aboveReadingWord_halfTurnPf`: the above-diagonal reading word of `π̂` is
  the reading word of `π` reversed and complemented.
* `HJO.ParkingFunctions.getElem_aboveReadingWord_halfTurnPf`: the same statement letter by letter,
  `ŵ_k = bN + 1 - w_{bN+1-k}`.
* `HJO.ParkingFunctions.length_readingWord`, `HJO.ParkingFunctions.length_aboveReadingWord`: both
  words have length `bN`, so the letterwise form is equivalent to the form as words.

## Implementation notes

The two words are `mergeSort` of `List.finRange (bN)` by the comparators derived from `ReadBefore`
and from `AboveReadBefore`, so the whole content is that sorting by a strict total order has a
unique answer: `List.pairwise_mergeSort_of_strictTotal` and `List.mergeSort_eq_of_strictTotal`
isolate that, and the half turn then only has to be exhibited as an order-reversing bijection of the
index set, which is `Fin.rev` and `HJO.ParkingFunctions.aboveReadBefore_halfTurnPf_iff`.

Both statements carry `0 < a` and `0 < N`, which the standing conventions supply: they
are what makes the tie-breaking clauses of the two reading orders vacuous.

## References

This file proves `HJO.ParkingFunctions.aboveReadingWord_halfTurnPf`.
-/

@[expose] public section

/-! ### Sorting by a strict total order

`mergeSort` is only specified up to the ties of its comparator, and the comparator "`x` is not
strictly after `y`" of a strict total order `R` has none. So the `R`-sorted list is *the* list that
is `Pairwise` "not strictly after", and any two permutations of one another that are both sorted
agree.
-/

namespace List

variable {α : Type*} {R : α → α → Prop} [DecidableRel R]
  (hirr : ∀ x, ¬ R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
  (htotal : ∀ x y, x ≠ y → R x y ∨ R y x)

include hirr htrans htotal in
/-- **Sorting by a strict total order.** Sorting a list by the comparator "`x` is not strictly after
`y`" of a strict total order `R` yields a list along which "not strictly after" holds pairwise. -/
theorem pairwise_mergeSort_of_strictTotal (l : List α) :
    (l.mergeSort fun x y => !decide (R y x)).Pairwise fun x y => ¬ R y x := by
  have hasym : ∀ ⦃x y : α⦄, R x y → ¬ R y x := fun x y h h' => hirr x (htrans x y x h h')
  have htr : ∀ x y z : α, (!decide (R y x)) = true → (!decide (R z y)) = true →
      (!decide (R z x)) = true := by
    intro x y z h1 h2
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h1 h2 ⊢
    intro hzx
    by_cases hyx : y = x
    · exact h2 (hyx ▸ hzx)
    by_cases hyz : y = z
    · exact h1 (hyz ▸ hzx)
    exact hasym (htrans x y z ((htotal y x hyx).resolve_left h1)
      ((htotal y z hyz).resolve_right h2)) hzx
  have hto : ∀ x y : α, ((!decide (R y x)) || (!decide (R x y))) = true := by
    intro x y
    simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    by_cases h : R y x
    · exact Or.inr (hasym h)
    · exact Or.inl h
  refine (List.pairwise_mergeSort htr hto l).imp fun {x y} h => ?_
  simpa using h

include hirr htrans htotal in
/-- **Sorting by a strict total order is determined.** A list that is `Pairwise` "not strictly
after" is the `R`-sorted form of every permutation of it. -/
theorem mergeSort_eq_of_strictTotal {l l' : List α} (hperm : l'.Perm l)
    (hpw : l'.Pairwise fun x y => ¬ R y x) :
    (l.mergeSort fun x y => !decide (R y x)) = l' := by
  refine List.Perm.eq_of_pairwise (fun x y _ _ h1 h2 => ?_)
    (pairwise_mergeSort_of_strictTotal hirr htrans htotal l) hpw
    ((List.mergeSort_perm l _).trans hperm.symm)
  by_contra hxy
  exact (htotal x y hxy).elim h2 h1

end List

namespace HJO.ParkingFunctions

variable {a b N : ℕ}

/-! ### The two reading words have length `bN` -/

@[simp]
theorem length_readingWord (π : ParkingFunction a b N) : (readingWord π).length = b * N := by
  rw [readingWord, List.length_map, List.length_mergeSort, List.length_finRange]

@[simp]
theorem length_aboveReadingWord (π : AboveParkingFunction a b N) :
    (aboveReadingWord π).length = b * N := by
  rw [aboveReadingWord, List.length_map, List.length_mergeSort, List.length_finRange]

/-! ### The half turn reverses the sorted listing of the north steps -/

/-- The half turn reverses the order in which the north steps are read: the listing of the north
steps of `P̂_π` in above-diagonal reading order is the listing of those of `P_π` in reading
order, read backwards through `Fin.rev`. -/
theorem mergeSort_aboveReadBefore_halfTurnPf (ha : 0 < a) (hN : 0 < N)
    (π : ParkingFunction a b N) :
    ((List.finRange (b * N)).mergeSort
        fun s t => !decide (AboveReadBefore (halfTurnPf π) t s))
      = (((List.finRange (b * N)).mergeSort
          fun s t => !decide (ReadBefore π t s)).map Fin.rev).reverse := by
  set m := (List.finRange (b * N)).mergeSort fun s t => !decide (ReadBefore π t s)
  have hmpw : m.Pairwise fun s t => ¬ ReadBefore π t s :=
    List.pairwise_mergeSort_of_strictTotal (readBefore_irrefl ha π) (readBefore_trans ha π)
      (readBefore_total ha π) _
  have hmperm : m.Perm (List.finRange (b * N)) := List.mergeSort_perm _ _
  refine List.mergeSort_eq_of_strictTotal (aboveReadBefore_irrefl ha hN π)
    (aboveReadBefore_trans ha hN π) (aboveReadBefore_total ha hN π) ?_ ?_
  · refine (List.reverse_perm _).trans ?_
    refine (hmperm.map Fin.rev).trans ?_
    refine (List.perm_ext_iff_of_nodup
      ((List.nodup_finRange (b * N)).map Fin.rev_injective) (List.nodup_finRange _)).2 ?_
    intro s
    simp only [List.mem_map, List.mem_finRange, iff_true, true_and]
    exact ⟨s.rev, Fin.rev_rev s⟩
  · rw [List.pairwise_reverse, List.pairwise_map]
    refine hmpw.imp fun {s t} hst => ?_
    rw [aboveReadBefore_halfTurnPf_iff ha hN, Fin.rev_rev, Fin.rev_rev]
    exact hst

/-! ### The half turn reverses and complements the reading word -/

/-- **The half turn reverses and complements the reading word.** The above-diagonal reading word
of `π̂` is the reading word of `π` with every letter `ℓ` replaced by `bN + 1 - ℓ`, read
backwards. -/
@[hjo "lem_half_turn_word"]
theorem aboveReadingWord_halfTurnPf (ha : 0 < a) (hN : 0 < N) (π : ParkingFunction a b N) :
    aboveReadingWord (halfTurnPf π)
      = ((readingWord π).map fun ℓ => b * N + 1 - ℓ).reverse := by
  rw [aboveReadingWord, readingWord, mergeSort_aboveReadBefore_halfTurnPf ha hN, List.map_map,
    ← List.map_reverse, ← List.map_reverse, List.map_map]
  refine List.map_congr_left fun s _ => ?_
  have h : (label π s : ℕ) < b * N := (label π s).isLt
  simp only [Function.comp_apply, aboveLabel_halfTurnPf, Fin.rev_rev, Fin.val_rev]
  omega

/-- **The half turn reverses and complements the reading word**, letter by letter: for
`1 ≤ k ≤ bN`, `ŵ_k = bN + 1 - w_{bN+1-k}`. Positions are `0`-based here, so the `k`
is `k + 1` and its position `bN + 1 - k` is the index `b * N - 1 - k`. -/
@[hjo "lem_half_turn_word"]
theorem getElem_aboveReadingWord_halfTurnPf (ha : 0 < a) (hN : 0 < N)
    (π : ParkingFunction a b N) {k : ℕ} (hk : k < b * N) :
    (aboveReadingWord (halfTurnPf π))[k]'(by rw [length_aboveReadingWord]; exact hk)
      = b * N + 1 - (readingWord π)[b * N - 1 - k]'(by
          rw [length_readingWord]; omega) := by
  rw [List.getElem_of_eq (aboveReadingWord_halfTurnPf ha hN π)]
  simp only [List.getElem_reverse, List.getElem_map, List.length_map, length_readingWord]

end HJO.ParkingFunctions
