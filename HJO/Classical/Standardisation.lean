/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Order.Interval.Finset.Fin
public import HJO.CarlssonMellit.WordStatistics
public import HJO.DyckInversions
public meta import HJO.Attr

/-! # Standardisation of a word

The standardisation `Std(w)` of a word: the rank of each letter, counting the strictly smaller
letters and the ties at or before its own position. This file defines it and proves the four
facts that read it off the definition — the order it induces, that it is a permutation,
that it preserves the inversions of an increasing set of pairs, and that its descent set is a
blockwise-increase condition on the word — together with the rigidity fact that a bijection of
positions is determined by the comparisons of its values.

## Main definitions

* `HJO.Sym.finWord`: a tuple on `Fin n` read as a word on `ℕ`.
* `HJO.Sym.std`: `Std(w)`.
* `HJO.Sym.stdPerm`: `Std(w)` packaged as a permutation of the positions.

## Main statements

* `HJO.Sym.std_lt_std_iff`.
* `HJO.Sym.std_bijective`.
* `HJO.Sym.eq_of_lt_iff_lt`.
* `HJO.Dyck.invSet_std`.
* `HJO.Sym.descentSet_std_subset_iff`.

## Implementation notes

`std` returns the usual `1`-based rank lowered by one, so that it is a `0`-based position like every
other index here, exactly as `HJO.Sym.coStd` does: the count `#\{j ≤ i : w_j = w_i\}`
always contains `j = i`, so the subtraction is genuine, and `std_lt` bounds the value by `n`. The
usual condition `n ≥ 1` is nowhere a hypothesis, every statement being vacuous at `n = 0`.

`HJO.Paths.standardisation` is the same statistic in the `1`-based convention:
`Paths.standardisation w i = std w i + 1`. The
`0`-based form is the one used here because its companion `HJO.Sym.coStd` is `0`-based and the two
are compared position by position in `HJO.Sym.coStd_eq_std_wordReverse`.

Descent sets are read through `finWord`, the tuple extended off the window by `0`: `descentSet`
takes a word on `ℕ`, so that it can be restricted and shifted, and `descentSet_congr` says only the
letters inside the window matter.

`HJO.Sym.descentSet_std_subset_iff` is stated with the condition in the shape
`HJO.Sym.IsAscendingWord.lt_of_mem` uses — a demand across a pair of adjacent positions of `Fin n`
— rather than at a natural-number index with a side condition, because that is the shape the
lemma using it, `HJO.ParkingFunctions.realisation_completeHomogComp`, produces.

## References

The file formalises `HJO.Sym.std`, `HJO.Sym.std_lt_std_iff`, `HJO.Sym.std_bijective`,
`HJO.Dyck.invSet_std`, `HJO.Sym.eq_of_lt_iff_lt` and `HJO.Sym.descentSet_std_subset_iff`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### A tuple read as a word -/

/-- A tuple on `Fin n` read as a word on `ℕ`, the letters outside the window being `0`. This is the
extension `HJO.Sym.descentSet_congr` licenses: only the letters inside the window are read, so which
letters are chosen outside it does not matter. -/
def finWord {α : Type*} [Zero α] {n : ℕ} (w : Fin n → α) : ℕ → α :=
  fun j => if h : j < n then w ⟨j, h⟩ else 0

@[simp]
theorem finWord_of_lt {α : Type*} [Zero α] {n : ℕ} (w : Fin n → α) {j : ℕ} (h : j < n) :
    finWord w j = w ⟨j, h⟩ := dite_eq_left h

/-! ### The standardisation -/

section Std

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- **The standardisation `Std(w)` of a word**: the entry at the position `i` is the number of
positions carrying a strictly smaller letter, plus the number of positions at or before `i` carrying
the same letter, lowered by one. The usual
`Std(w)_i = \#\{j : w_j < w_i\} + \#\{j ≤ i : w_j = w_i\}` is a rank in `\{1, …, n\}`; the value
here is that rank minus one, a `0`-based position, as everywhere in this part of the library and as
for `HJO.Sym.coStd`. The second count always contains `j = i`, so the subtraction is genuine, and
`HJO.Sym.std_lt` bounds the value by `n`. Positivity of the letters is not used, so it is not
assumed. -/
@[hjo "def_cm_std"]
def std (w : Fin n → α) (i : Fin n) : ℕ :=
  #{j | w j < w i} + #{j | j ≤ i ∧ w j = w i} - 1

/-- The `1`-based rank, before it is lowered: the number of positions carrying a smaller letter plus
the number of positions at or before `i` carrying the same letter. Adding the one back is legitimate
because the second count contains `j = i`. -/
theorem std_add_one (w : Fin n → α) (i : Fin n) :
    std w i + 1 = #{j | w j < w i} + #{j | j ≤ i ∧ w j = w i} := by
  have hi : i ∈ ({j | j ≤ i ∧ w j = w i} : Finset (Fin n)) := by simp
  have : 1 ≤ #{j | j ≤ i ∧ w j = w i} := card_pos.2 ⟨i, hi⟩
  rw [std]
  omega

/-- The two counts of the standardisation are disjoint, a letter being either smaller than `w i` or
equal to it but not both, so their sum is at most the length of the word. -/
theorem std_bound (w : Fin n → α) (i : Fin n) :
    #{j | w j < w i} + #{j | j ≤ i ∧ w j = w i} ≤ n := by
  have hdisj : Disjoint ({j | w j < w i} : Finset (Fin n))
      ({j | j ≤ i ∧ w j = w i} : Finset (Fin n)) :=
    disjoint_filter.2 fun j _ hj hj' => absurd (hj'.2 ▸ hj) (lt_irrefl _)
  calc #{j | w j < w i} + #{j | j ≤ i ∧ w j = w i}
      = #(({j | w j < w i} : Finset (Fin n)) ∪ ({j | j ≤ i ∧ w j = w i} : Finset (Fin n))) :=
        (card_union_of_disjoint hdisj).symm
    _ ≤ #(univ : Finset (Fin n)) := card_le_card (subset_univ _)
    _ = n := by simp

/-- The standardisation takes values among the positions: the `1`-based rank lies in `\{1, …, n\}`,
so its `0`-based form lies below `n`. This is what lets it be read as a permutation of the
positions. -/
theorem std_lt (w : Fin n → α) (i : Fin n) : std w i < n := by
  have h := std_bound w i
  have h' := std_add_one w i
  omega

/-- A strictly smaller letter gets a strictly smaller rank: every position counted at `i` is counted
at `j`, and the positions carrying `w i` are counted at `j` too. -/
private theorem std_lt_std_of_lt {w : Fin n → α} {i j : Fin n} (hij : w i < w j) :
    std w i < std w j := by
  have hdisj : Disjoint ({l | w l < w i} : Finset (Fin n))
      ({l | w l = w i} : Finset (Fin n)) :=
    disjoint_filter.2 fun l _ hl hl' => absurd (hl' ▸ hl) (lt_irrefl _)
  have hsub : (({l | w l < w i} : Finset (Fin n)) ∪ ({l | w l = w i} : Finset (Fin n)))
      ⊆ ({l | w l < w j} : Finset (Fin n)) := by
    intro l hl
    simp only [mem_union, mem_filter, mem_univ, true_and] at hl ⊢
    rcases hl with hl | hl
    · exact hl.trans hij
    · exact hl ▸ hij
  have hA : #{l | w l < w i} + #{l | w l = w i} ≤ #{l | w l < w j} := by
    rw [← card_union_of_disjoint hdisj]
    exact card_le_card hsub
  have hB : #{l | l ≤ i ∧ w l = w i} ≤ #{l | w l = w i} := by
    refine card_le_card fun l hl => ?_
    simp only [mem_filter, mem_univ, true_and] at hl ⊢
    exact hl.2
  have hBj : 1 ≤ #{l | l ≤ j ∧ w l = w j} := card_pos.2 ⟨j, by simp⟩
  have h1 := std_add_one w i
  have h2 := std_add_one w j
  omega

/-- Equal letters compare by position: the counts of smaller letters agree, and the counts of ties
compare as the positions do. -/
private theorem std_lt_std_iff_of_eq {w : Fin n → α} {i j : Fin n} (hij : w i = w j) :
    std w i < std w j ↔ i < j := by
  have hA : ({l | w l < w i} : Finset (Fin n)) = ({l | w l < w j} : Finset (Fin n)) := by
    refine filter_congr fun l _ => ?_
    rw [hij]
  have hmono : ∀ a b : Fin n, w a = w b → a ≤ b →
      ({l | l ≤ a ∧ w l = w a} : Finset (Fin n)) ⊆ ({l | l ≤ b ∧ w l = w b} : Finset (Fin n)) := by
    intro a b hab hle l hl
    simp only [mem_filter, mem_univ, true_and] at hl ⊢
    exact ⟨hl.1.trans hle, hl.2.trans hab⟩
  have hstrict : ∀ a b : Fin n, w a = w b → a < b →
      #{l | l ≤ a ∧ w l = w a} < #{l | l ≤ b ∧ w l = w b} := by
    intro a b hab hlt
    refine card_lt_card ⟨hmono a b hab hlt.le, fun hsub => ?_⟩
    have hb : b ∈ ({l | l ≤ b ∧ w l = w b} : Finset (Fin n)) := by simp
    have hbb := hsub hb
    simp only [mem_filter, mem_univ, true_and] at hbb
    exact absurd (hbb.1.trans_lt hlt) (lt_irrefl _)
  have h1 := std_add_one w i
  have h2 := std_add_one w j
  rw [hA] at h1
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases lt_trichotomy i j with h' | rfl | h'
    · exact h'
    · omega
    · have := hstrict j i hij.symm h'
      omega
  · have := hstrict i j hij h
    omega

/-- **Standardisation orders the entries.** `Std(w)_i < Std(w)_j` holds exactly
when either `w_i < w_j`, or `w_i = w_j` and `i < j`: the standardisation is the rank for the order
on positions that compares letters and breaks ties by position. -/
@[hjo "lem_cm_std_order"]
theorem std_lt_std_iff (w : Fin n → α) (i j : Fin n) :
    std w i < std w j ↔ (w i < w j ∨ (w i = w j ∧ i < j)) := by
  rcases lt_trichotomy (w i) (w j) with h | h | h
  · exact iff_of_true (std_lt_std_of_lt h) (Or.inl h)
  · rw [std_lt_std_iff_of_eq h]
    simp [h]
  · refine iff_of_false (asymm (std_lt_std_of_lt h)) ?_
    rintro (hc | ⟨hc, -⟩)
    · exact absurd hc (asymm h)
    · exact absurd hc (ne_of_gt h)

/-- The standardisation is injective: two positions are separated by the order of
`HJO.Sym.std_lt_std_iff`, which is a strict total order on them. -/
theorem std_injective (w : Fin n → α) : Function.Injective (std w) := by
  intro i j hij
  by_contra hne
  rcases lt_trichotomy (w i) (w j) with h | h | h
  · exact absurd ((std_lt_std_iff w i j).2 (Or.inl h)) (by omega)
  · rcases lt_or_gt_of_ne hne with h' | h'
    · exact absurd ((std_lt_std_iff w i j).2 (Or.inr ⟨h, h'⟩)) (by omega)
    · exact absurd ((std_lt_std_iff w j i).2 (Or.inr ⟨h.symm, h'⟩)) (by omega)
  · exact absurd ((std_lt_std_iff w j i).2 (Or.inl h)) (by omega)

/-- **Standardisation is a permutation.** `Std(w)` is a bijection from the `n`
positions to themselves: it is injective by `HJO.Sym.std_lt_std_iff`, its values lie below `n` by
`HJO.Sym.std_lt`, and an injective self-map of a finite type is a bijection. -/
@[hjo "lem_cm_std_perm"]
theorem std_bijective (w : Fin n → α) :
    Function.Bijective fun i => (⟨std w i, std_lt w i⟩ : Fin n) :=
  Finite.injective_iff_bijective.1 fun _ _ hij => std_injective w (congrArg Fin.val hij)

/-- `Std(w)` packaged as a permutation of the positions. -/
noncomputable def stdPerm (w : Fin n → α) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective _ (std_bijective w)

@[simp]
theorem stdPerm_apply (w : Fin n → α) (i : Fin n) : ((stdPerm w i : Fin n) : ℕ) = std w i := rfl

/-- The entries of a standardisation at two positions are distinct, which is what makes its descent
set the complement of its ascent set. -/
theorem std_ne_std {w : Fin n → α} {i j : Fin n} (hij : i ≠ j) : std w i ≠ std w j :=
  fun h => hij (std_injective w h)

end Std

/-! ### Comparisons determine a permutation -/

/-- The number of positions whose value under a bijection of the positions is smaller than the value
at `i` is that value: the values run over all the positions exactly once. -/
theorem card_filter_lt_apply {n : ℕ} {τ : Fin n → Fin n} (hτ : Function.Bijective τ) (i : Fin n) :
    #{j | τ j < τ i} = (τ i : ℕ) := by
  have himg : ({j | τ j < τ i} : Finset (Fin n)).image τ = Finset.Iio (τ i) := by
    ext v
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_Iio]
    refine ⟨fun ⟨j, hj, hjv⟩ => hjv ▸ hj, fun hv => ?_⟩
    obtain ⟨j, rfl⟩ := hτ.2 v
    exact ⟨j, hv, rfl⟩
  rw [← card_image_of_injective _ hτ.1, himg, Fin.card_Iio]

/-- **Comparisons determine a permutation.** Two bijections of the positions
inducing the same comparisons are equal: the number of positions whose value is below the value at
`i` is that value itself, so the two values at `i` agree. -/
@[hjo "lem_cm_perm_by_order"]
theorem eq_of_lt_iff_lt {n : ℕ} {π σ : Fin n → Fin n} (hπ : Function.Bijective π)
    (hσ : Function.Bijective σ) (h : ∀ i j : Fin n, π i < π j ↔ σ i < σ j) : π = σ := by
  funext i
  have hset : ({j | π j < π i} : Finset (Fin n)) = ({j | σ j < σ i} : Finset (Fin n)) :=
    filter_congr fun j _ => h j i
  have h1 := card_filter_lt_apply hπ i
  have h2 := card_filter_lt_apply hσ i
  rw [hset, h2] at h1
  exact Fin.ext h1.symm

/-! ### Blockwise increase is a descent condition on the standardisation -/

section Block

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- **Blockwise increase is a descent condition on the standardisation.**
`Des(Std(u)) ⊆ T` holds exactly when `u` does not decrease across any step outside `T`.

The entries of a standardisation at two adjacent positions are distinct, so a step is a non-descent
exactly when it is an ascent, and by `HJO.Sym.std_lt_std_iff` that is `u_j ≤ u_{j+1}`. -/
@[hjo "lem_om_block_std"]
theorem descentSet_std_subset_iff (T : Finset ℕ) (u : Fin n → α) :
    descentSet n (finWord (std u)) ⊆ T ↔
      ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → (l : ℕ) ∉ T → u k ≤ u l := by
  constructor
  · intro hsub k l hkl hl
    by_contra hlt
    refine hl (hsub (mem_descentSet.2 ⟨by omega, l.isLt, ?_⟩))
    rw [finWord_of_lt _ l.isLt, finWord_of_lt _ (by omega : (l : ℕ) - 1 < n),
      show (⟨(l : ℕ), l.isLt⟩ : Fin n) = l from rfl,
      show (⟨(l : ℕ) - 1, by omega⟩ : Fin n) = k from
        Fin.ext (show (l : ℕ) - 1 = (k : ℕ) by omega)]
    exact (std_lt_std_iff u l k).2 (Or.inl (lt_of_not_ge hlt))
  · intro hmono j hj
    obtain ⟨h1, h2, h3⟩ := mem_descentSet.1 hj
    by_contra hjT
    have hk : j - 1 < n := by omega
    rw [finWord_of_lt _ h2, finWord_of_lt _ hk] at h3
    have hstep := hmono ⟨j - 1, hk⟩ ⟨j, h2⟩ (show j - 1 + 1 = j by omega) hjT
    rcases (std_lt_std_iff u ⟨j, h2⟩ ⟨j - 1, hk⟩).1 h3 with hc | ⟨-, hc⟩
    · exact absurd hstep (not_le.2 hc)
    · exact absurd (show j < j - 1 from Fin.lt_def.1 hc) (by omega)

end Block

end HJO.Sym

namespace HJO.Dyck

/-- **Standardisation preserves inversions.** For a set `R` of increasing pairs of
positions, `Inv(R, w) = Inv(R, Std(w))`.

A pair `(i, j) ∈ R` has `i < j`, so `HJO.Sym.std_lt_std_iff` makes `Std(w)_j < Std(w)_i` equivalent
to `w_j < w_i`: the tie-breaking clause, which would need `j < i`, never fires. -/
@[hjo "lem_cm_inv_std"]
theorem invSet_std {α : Type*} [LinearOrder α] {n : ℕ} (R : Finset (Fin n × Fin n))
    (hR : ∀ p ∈ R, p.1 < p.2) (w : Fin n → α) : invSet R w = invSet R (Sym.std w) := by
  rw [invSet, invSet]
  refine Finset.filter_congr fun p hp => ?_
  rw [Sym.std_lt_std_iff w p.2 p.1]
  exact ⟨Or.inl, fun h => h.elim id fun h' => absurd h'.2 (asymm (hR p hp))⟩

end HJO.Dyck
