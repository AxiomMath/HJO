/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.RealisationReverse
public import HJO.Shuffle.HalfTurnParking
public meta import HJO.Attr

/-! # The half turn complements the inverse descent set

The reading word of a parking function lists its labels in decreasing order of the rank of the
north step each one marks. For `0 < a` the ranks of distinct north steps differ
(`HJO.ParkingFunctions.stepRank_injective`), so that order is a strict total order and the reading
word is the unique listing sorted by it. The half turn reverses the rank order and complements
every label, so it reverses and complements the reading word, and therefore reflects the inverse
descent set: `ideŝ(π̂) = ides(π)^{∨bN}`.

That reflection is the *reason* the derivation of the below-diagonal shuffle identity needs
`HJO.gessel_reverse_sum`. It is not an artefact of the encoding and it cannot be dropped.

## Main results

* `HJO.ParkingFunctions.mem_ides_iff`, `HJO.ParkingFunctions.mem_aboveIdes_iff`: membership in an
  inverse descent set is a single `ReadBefore` comparison between the two north steps carrying the
  labels `i + 1` and `i`.
* `HJO.ParkingFunctions.aboveIdes_halfTurnPf`: `ideŝ(π̂) = ides(π)^{∨bN}`.

## Implementation notes

`List.idxOf_lt_idxOf_map_mergeSort_iff` is the one piece of list combinatorics hidden
inside the phrase "the word listing its labels in decreasing order": for a strict total order `R`
on `Fin n` and an injection `g`, the position of `g s` in the `R`-sorted listing of `Fin n` precedes
that of `g t` exactly when `R s t`. Both reading words are of that shape, with `R` the respective
`ReadBefore`, so the same lemma serves both sides.

## References

This file concerns `HJO.ParkingFunctions.aboveReadingWord_halfTurnPf` and
`HJO.ParkingFunctions.aboveIdes_halfTurnPf`.
-/

@[expose] public section

open Finset

/-! ### Positions in a sorted listing -/

/-- The position of `f x` in the image of `l` under an injection is the position of `x` in `l`. -/
theorem List.idxOf_map_of_injective {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    {f : α → β} (hf : Function.Injective f) (l : List α) (x : α) :
    (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => simp
  | cons y l ih =>
    by_cases h : y = x
    · simp [h]
    · rw [List.map_cons, List.idxOf_cons_ne _ (fun hh => h (hf hh)), List.idxOf_cons_ne _ h, ih]

/-- **Positions in a sorted listing.** For a strict total order `R` on `Fin n` and an injection `g`,
the letter `g s` precedes the letter `g t` in the listing of `Fin n` sorted so that `R`-earlier
elements come first, exactly when `R s t`. This is what "the word listing the labels in decreasing
order of rank" means once the order is known to have no ties. -/
theorem List.idxOf_lt_idxOf_map_mergeSort_iff {n : ℕ} {β : Type*} [BEq β] [LawfulBEq β]
    (R : Fin n → Fin n → Prop) [DecidableRel R] {g : Fin n → β} (hg : Function.Injective g)
    (hirr : ∀ s, ¬ R s s) (htrans : ∀ s t u, R s t → R t u → R s u)
    (htotal : ∀ s t, s ≠ t → R s t ∨ R t s) {s t : Fin n} (hst : s ≠ t) :
    (((List.finRange n).mergeSort fun x y => !decide (R y x)).map g).idxOf (g s) <
      (((List.finRange n).mergeSort fun x y => !decide (R y x)).map g).idxOf (g t) ↔ R s t := by
  have hasym : ∀ x y, R x y → ¬ R y x := fun x y h h' => hirr x (htrans x y x h h')
  set le : Fin n → Fin n → Bool := fun x y => !decide (R y x) with hle
  have hleiff : ∀ x y, le x y = true ↔ ¬ R y x := by intro x y; simp [hle]
  have htr : ∀ x y z, le x y → le y z → le x z := by
    intro x y z h1 h2
    rw [hleiff] at h1 h2 ⊢
    intro hzx
    by_cases hyx : y = x
    · rw [hyx] at h2; exact h2 hzx
    by_cases hyz : y = z
    · rw [← hyz] at hzx; exact h1 hzx
    exact hasym x z (htrans x y z ((htotal y x hyx).resolve_left h1)
      ((htotal y z hyz).resolve_right h2)) hzx
  have hto : ∀ x y, le x y || le y x := by
    intro x y
    simp only [hle, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    by_cases h : R y x
    · exact Or.inr (hasym y x h)
    · exact Or.inl h
  set m := (List.finRange n).mergeSort le with hm
  have hperm : m.Perm (List.finRange n) := List.mergeSort_perm (List.finRange n) le
  have hnd : m.Nodup := hperm.symm.nodup (List.nodup_finRange n)
  have hmem : ∀ x : Fin n, x ∈ m := fun x => hperm.mem_iff.2 (List.mem_finRange x)
  have hpw : m.Pairwise R := by
    have h1 : m.Pairwise (fun x y => le x y = true) := List.pairwise_mergeSort htr hto _
    rw [List.pairwise_iff_getElem] at h1 ⊢
    intro i j hi hj hij
    refine (htotal _ _ fun hcon => ?_).resolve_right ((hleiff _ _).1 (h1 i j hi hj hij))
    exact absurd (hnd.getElem_inj_iff.1 hcon) (by omega)
  rw [List.idxOf_map_of_injective hg, List.idxOf_map_of_injective hg]
  have hi : m.idxOf s < m.length := List.idxOf_lt_length_iff.2 (hmem s)
  have hj : m.idxOf t < m.length := List.idxOf_lt_length_iff.2 (hmem t)
  have hgs : m[m.idxOf s] = s := List.getElem_idxOf hi
  have hgt : m[m.idxOf t] = t := List.getElem_idxOf hj
  rw [List.pairwise_iff_getElem] at hpw
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hthis := hpw _ _ hi hj h
    rwa [hgs, hgt] at hthis
  rcases Nat.lt_or_ge (m.idxOf s) (m.idxOf t) with hlt | hge
  · exact hlt
  · have hne : m.idxOf s ≠ m.idxOf t := fun h' => hst ((List.idxOf_inj (hmem s)).1 h')
    have hthis := hpw _ _ hj hi (by omega : m.idxOf t < m.idxOf s)
    rw [hgs, hgt] at hthis
    exact absurd hthis (hasym s t h)

namespace HJO.ParkingFunctions

variable {a b N : ℕ}

/-! ### The reading order has no ties -/

/-- For `0 < a` the tie-breaking clause of `ReadBefore` never fires: the step with the larger rank
is read first, full stop. -/
theorem readBefore_iff (ha : 0 < a) (π : ParkingFunction a b N) (s t : Fin (b * N)) :
    ReadBefore π s t ↔ stepRank π t < stepRank π s := by
  refine ⟨fun h => h.elim id fun ⟨h1, h2⟩ => ?_, Or.inl⟩
  exact absurd (stepRank_injective ha π h1) (ne_of_gt h2)

theorem readBefore_irrefl (ha : 0 < a) (π : ParkingFunction a b N) (s : Fin (b * N)) :
    ¬ ReadBefore π s s := by rw [readBefore_iff ha]; exact lt_irrefl _

theorem readBefore_trans (ha : 0 < a) (π : ParkingFunction a b N) (s t u : Fin (b * N)) :
    ReadBefore π s t → ReadBefore π t u → ReadBefore π s u := by
  rw [readBefore_iff ha, readBefore_iff ha, readBefore_iff ha]
  exact fun h1 h2 => h2.trans h1

theorem readBefore_total (ha : 0 < a) (π : ParkingFunction a b N) (s t : Fin (b * N))
    (hst : s ≠ t) : ReadBefore π s t ∨ ReadBefore π t s := by
  rw [readBefore_iff ha, readBefore_iff ha]
  rcases lt_trichotomy (stepRank π s) (stepRank π t) with h | h | h
  · exact Or.inr h
  · exact absurd (stepRank_injective ha π h) hst
  · exact Or.inl h

/-! ### Inverse descent sets as a single comparison -/

theorem injective_readingLetter (π : ParkingFunction a b N) :
    Function.Injective fun s : Fin (b * N) => (label π s : ℕ) + 1 := by
  intro s t h
  have h' : (label π s : ℕ) = (label π t : ℕ) := by simpa using h
  exact (bijective_label π).1 (Fin.val_injective h')

/-- **Membership in `ides`.** For `1 ≤ i < bN`, the index `i` is an inverse descent of `π` exactly
when the north step carrying the label `i + 1` is read before the one carrying the label `i`. -/
theorem mem_ides_iff (ha : 0 < a) (π : ParkingFunction a b N) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i < b * N) :
    i ∈ ides π ↔
      ReadBefore π (labelStep π ⟨i, hi2⟩) (labelStep π ⟨i - 1, by omega⟩) := by
  have hne : labelStep π ⟨i, hi2⟩ ≠ labelStep π ⟨i - 1, by omega⟩ := by
    intro h
    have h2 : (⟨i, hi2⟩ : Fin (b * N)) = ⟨i - 1, by omega⟩ := by
      rw [← label_labelStep π ⟨i, hi2⟩, ← label_labelStep π ⟨i - 1, by omega⟩, h]
    have h3 : i = i - 1 := by simpa using congrArg Fin.val h2
    omega
  have e1 : (label π (labelStep π ⟨i, hi2⟩) : ℕ) + 1 = i + 1 := by rw [label_labelStep]
  have e2 : (label π (labelStep π ⟨i - 1, by omega⟩) : ℕ) + 1 = i := by
    rw [label_labelStep]; simp only; omega
  rw [ides, mem_filter, mem_Ico, readingWord,
    ← List.idxOf_lt_idxOf_map_mergeSort_iff (ReadBefore π) (injective_readingLetter π)
      (readBefore_irrefl ha π) (readBefore_trans ha π) (readBefore_total ha π) hne,
    e1, e2]
  exact and_iff_right ⟨hi1, hi2⟩

theorem aboveReadBefore_irrefl (ha : 0 < a) (hN : 0 < N) (π : ParkingFunction a b N)
    (s : Fin (b * N)) : ¬ AboveReadBefore (halfTurnPf π) s s := by
  rw [aboveReadBefore_halfTurnPf_iff ha hN]; exact readBefore_irrefl ha π _

theorem aboveReadBefore_trans (ha : 0 < a) (hN : 0 < N) (π : ParkingFunction a b N)
    (s t u : Fin (b * N)) : AboveReadBefore (halfTurnPf π) s t →
      AboveReadBefore (halfTurnPf π) t u → AboveReadBefore (halfTurnPf π) s u := by
  rw [aboveReadBefore_halfTurnPf_iff ha hN, aboveReadBefore_halfTurnPf_iff ha hN,
    aboveReadBefore_halfTurnPf_iff ha hN]
  exact fun h1 h2 => readBefore_trans ha π _ _ _ h2 h1

theorem aboveReadBefore_total (ha : 0 < a) (hN : 0 < N) (π : ParkingFunction a b N)
    (s t : Fin (b * N)) (hst : s ≠ t) :
    AboveReadBefore (halfTurnPf π) s t ∨ AboveReadBefore (halfTurnPf π) t s := by
  rw [aboveReadBefore_halfTurnPf_iff ha hN, aboveReadBefore_halfTurnPf_iff ha hN]
  exact readBefore_total ha π t.rev s.rev fun h => hst (Fin.rev_inj.1 h).symm

theorem injective_aboveReadingLetter (π : AboveParkingFunction a b N) :
    Function.Injective fun i : Fin (b * N) => (aboveLabel π i : ℕ) + 1 := by
  intro s t h
  have h' : (aboveLabel π s : ℕ) = (aboveLabel π t : ℕ) := by simpa using h
  exact (bijective_aboveLabel π).1 (Fin.val_injective h')

/-- **Membership in `ideŝ`**, for a half turn: the same single comparison as `mem_ides_iff`. -/
theorem mem_aboveIdes_iff (ha : 0 < a) (hN : 0 < N) (π : ParkingFunction a b N) {i : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i < b * N) :
    i ∈ aboveIdes (halfTurnPf π) ↔
      AboveReadBefore (halfTurnPf π) (aboveLabelStep (halfTurnPf π) ⟨i, hi2⟩)
        (aboveLabelStep (halfTurnPf π) ⟨i - 1, by omega⟩) := by
  have hne : aboveLabelStep (halfTurnPf π) ⟨i, hi2⟩
      ≠ aboveLabelStep (halfTurnPf π) ⟨i - 1, by omega⟩ := by
    intro h
    have h2 : (⟨i, hi2⟩ : Fin (b * N)) = ⟨i - 1, by omega⟩ := by
      rw [← aboveLabel_aboveLabelStep (halfTurnPf π) ⟨i, hi2⟩,
        ← aboveLabel_aboveLabelStep (halfTurnPf π) ⟨i - 1, by omega⟩, h]
    have h3 : i = i - 1 := by simpa using congrArg Fin.val h2
    omega
  have e1 : (aboveLabel (halfTurnPf π) (aboveLabelStep (halfTurnPf π) ⟨i, hi2⟩) : ℕ) + 1
      = i + 1 := by rw [aboveLabel_aboveLabelStep]
  have e2 : (aboveLabel (halfTurnPf π)
      (aboveLabelStep (halfTurnPf π) ⟨i - 1, by omega⟩) : ℕ) + 1 = i := by
    rw [aboveLabel_aboveLabelStep]; simp only; omega
  rw [aboveIdes, mem_filter, mem_Ico, aboveReadingWord,
    ← List.idxOf_lt_idxOf_map_mergeSort_iff (AboveReadBefore (halfTurnPf π))
      (injective_aboveReadingLetter (halfTurnPf π)) (aboveReadBefore_irrefl ha hN π)
      (aboveReadBefore_trans ha hN π) (aboveReadBefore_total ha hN π) hne,
    e1, e2]
  exact and_iff_right ⟨hi1, hi2⟩

/-! ### The half turn complements the inverse descent set -/

/-- **The half turn complements the inverse descent set**: `ideŝ(π̂) = ides(π)^{∨bN}`. -/
@[hjo "lem_half_turn_ides"]
theorem aboveIdes_halfTurnPf (ha : 0 < a) (hN : 0 < N) (π : ParkingFunction a b N) :
    aboveIdes (halfTurnPf π) = descentReverse (b * N) (ides π) := by
  have key : ∀ i, 1 ≤ i → i < b * N →
      (i ∈ aboveIdes (halfTurnPf π) ↔ b * N - i ∈ ides π) := by
    intro i hi1 hi2
    rw [mem_aboveIdes_iff ha hN π hi1 hi2, aboveReadBefore_halfTurnPf_iff ha hN,
      mem_ides_iff ha π (by omega : 1 ≤ b * N - i) (by omega : b * N - i < b * N),
      aboveLabelStep_halfTurnPf, aboveLabelStep_halfTurnPf, Fin.rev_rev, Fin.rev_rev]
    have h1 : (⟨i - 1, by omega⟩ : Fin (b * N)).rev = ⟨b * N - i, by omega⟩ := by
      ext; rw [Fin.val_rev]; simp only; omega
    have h2 : (⟨i, hi2⟩ : Fin (b * N)).rev = ⟨b * N - i - 1, by omega⟩ := by
      ext; rw [Fin.val_rev]; simp only; omega
    rw [h1, h2]
  have hsub := ides_subset π
  ext i
  simp only [mem_descentReverse]
  by_cases hi : 1 ≤ i ∧ i < b * N
  · rw [key i hi.1 hi.2]
    refine ⟨fun h => ⟨b * N - i, h, by omega⟩, ?_⟩
    rintro ⟨j, hj, hji⟩
    have hjm := mem_Ico.1 (hsub hj)
    have : b * N - i = j := by omega
    rwa [this]
  · have h1 : i ∉ aboveIdes (halfTurnPf π) := fun h => by
      have := mem_Ico.1 (aboveIdes_subset _ h); omega
    have h2 : ¬ ∃ j ∈ ides π, b * N - j = i := by
      rintro ⟨j, hj, hji⟩
      have := mem_Ico.1 (hsub hj); omega
    simp only [h1, false_iff]
    exact h2

end HJO.ParkingFunctions
