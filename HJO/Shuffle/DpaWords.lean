/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidTrain
public meta import HJO.Attr

/-! # The four words in a family of invertible elements

Mellit's presentation of the double positive algebra uses four notations for words in a family
`S_1, …, S_m` of invertible elements of a unital algebra: the ascending word `S_{i↑j}`, the
descending word `S_{j↓i}`, and the two starred words `S^*_{i↑j}` and `S^*_{j↓i}` in which every
letter is replaced by its inverse. All four are indexed by `1 ≤ i ≤ j ≤ m + 1` and are the empty
product `1` when `j = i`.

## Main definitions

* `HJO.Braid.wordUp`, `HJO.Braid.wordDown`: `S_{i↑j} = S_i S_{i+1} ⋯ S_{j-1}` and
  `S_{j↓i} = S_{j-1} S_{j-2} ⋯ S_i`.
* `HJO.Braid.wordUpStar`, `HJO.Braid.wordDownStar`: the same words in the inverses,
  `S^*_{i↑j} = S_i^{-1} ⋯ S_{j-1}^{-1}` and `S^*_{j↓i} = S_{j-1}^{-1} ⋯ S_i^{-1}`.

## Main results

* `HJO.Braid.wordUp_self`, `HJO.Braid.wordDown_self`, and the two starred analogues: the empty
  product convention at `j = i`.
* `HJO.Braid.wordUp_succ`, `HJO.Braid.wordDown_succ`: the single-letter case `j = i + 1`, which is
  where the empty-product convention stops and the word begins.
* `HJO.Braid.wordUp_one_four` and its three companions: the four words at `i = 1`, `j = 4`, checked
  letter by letter against the display.

## Implementation notes

The family is `S : ℕ → Aˣ`, a total function into the **units** of a monoid `A`, and the words take
values in `A`. Invertibility is then not a hypothesis but part of the type, and `S_i^{-1}` is the
canonical inverse rather than a second named function: the letters are only required to be
invertible elements of `A`, and in a monoid the inverse of a unit is determined, so nothing is added
by naming it and something is lost by carrying it separately — two of the four definitions below
would depend on a choice. This differs deliberately from `HJO.Braid.IsBraidSystem`, whose letters
are operators that are invertible one by one but whose inverses are supplied by the construction and
not by a `Units` structure; the two layers meet through `HJO.Braid.ascendingWord`, which both use.

`A` is a monoid, not a `𝕜`-algebra: no statement about these words reads the addition or the
scalars. The `1 ≤ i ≤ j ≤ m + 1` is not carried in the type either. The formulas are
total, the letters outside the range being unconstrained, and a word with `1 ≤ i ≤ j ≤ m + 1` reads
only indices in `[i, j - 1] ⊆ [1, m]`, so the totality costs no faithfulness; Mellit's
extension of the unstarred notations to `i > j` is not introduced, no statement below using it.

The argument order follows the notation rather than the alphabet: `wordDown S j i` is `S_{j↓i}`,
with the *upper* index first, exactly as it is written. Reading `wordDown S 4 1` as `S_{4↓1}` is
then a matter of reading the line, and `wordDown_four_one` checks that it is `S_3 S_2 S_1`.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §2, where `HJO.Braid.wordUp`,
`HJO.Braid.wordDown`, `HJO.Braid.wordUpStar` and `HJO.Braid.wordDownStar` are `T_{i↑j}`,
`T_{j↓i}`, `T^*_{i↑j}` and `T^*_{j↓i}`, for a family satisfying `HJO.Braid.IsBraidSystem`.
Consumed by
`HJO.Braid.wordUp_mul_wordDownStar`, `HJO.Braid.wordDownStar_mul_wordUp`,
`HJO.Braid.wordDown_mul_wordUpStar` and the replication construction.
-/

@[expose] public section

namespace HJO.Braid

variable {A : Type*} [Monoid A] (S : ℕ → Aˣ)

/-- The ascending word `S_{i↑j} = S_i S_{i+1} ⋯ S_{j-1}` in the family `S` of invertible elements,
the empty product `1` when `j ≤ i`. -/
@[hjo "def_dpa_word_up"]
def wordUp (i j : ℕ) : A := ascendingWord (fun r => ((S r : A))) i j

/-- The descending word `S_{j↓i} = S_{j-1} S_{j-2} ⋯ S_i` in the family `S` of invertible elements,
the empty product `1` when `j ≤ i`. The upper index comes first, as in the notation. -/
@[hjo "def_dpa_word_down"]
def wordDown (j i : ℕ) : A := descendingWord (fun r => ((S r : A))) j i

/-- The starred ascending word `S^*_{i↑j} = S_i^{-1} S_{i+1}^{-1} ⋯ S_{j-1}^{-1}`: the ascending
word in the inverses of the letters, in the same order, and the empty product `1` when `j ≤ i`. -/
@[hjo "def_dpa_word_up_star"]
def wordUpStar (i j : ℕ) : A := ascendingWord (fun r => (((S r)⁻¹ : Aˣ) : A)) i j

/-- The starred descending word `S^*_{j↓i} = S_{j-1}^{-1} S_{j-2}^{-1} ⋯ S_i^{-1}`: the descending
word in the inverses of the letters, in the same order, and the empty product `1` when `j ≤ i`. -/
@[hjo "def_dpa_word_down_star"]
def wordDownStar (j i : ℕ) : A := descendingWord (fun r => (((S r)⁻¹ : Aˣ) : A)) j i

/-! ### The empty product at `j = i` -/

@[simp]
theorem wordUp_self (i : ℕ) : wordUp S i i = 1 := by simp [wordUp, ascendingWord]

@[simp]
theorem wordDown_self (i : ℕ) : wordDown S i i = 1 := by simp [wordDown, descendingWord]

@[simp]
theorem wordUpStar_self (i : ℕ) : wordUpStar S i i = 1 := by simp [wordUpStar, ascendingWord]

@[simp]
theorem wordDownStar_self (i : ℕ) : wordDownStar S i i = 1 := by
  simp [wordDownStar, descendingWord]

/-! ### The single letter at `j = i + 1`

This is where the empty-product convention stops. Without these four the definitions would be
consistent with every word being `1`. -/

theorem wordUp_succ (i : ℕ) : wordUp S i (i + 1) = (S i : A) := by
  simp [wordUp, ascendingWord]

theorem wordDown_succ (i : ℕ) : wordDown S (i + 1) i = (S i : A) := by
  simp [wordDown, descendingWord]

theorem wordUpStar_succ (i : ℕ) : wordUpStar S i (i + 1) = (((S i)⁻¹ : Aˣ) : A) := by
  simp [wordUpStar, ascendingWord]

theorem wordDownStar_succ (i : ℕ) : wordDownStar S (i + 1) i = (((S i)⁻¹ : Aˣ) : A) := by
  simp [wordDownStar, descendingWord]

/-! ### Value checks at `i = 1`, `j = 4`

The four displays read `S_1S_2S_3`, `S_3S_2S_1`, `S_1^{-1}S_2^{-1}S_3^{-1}` and
`S_3^{-1}S_2^{-1}S_1^{-1}`. The order of the factors is part of each definition and the starred
words are *not* the reverses of the unstarred ones, so all four are checked separately. -/

theorem wordUp_one_four : wordUp S 1 4 = (S 1 : A) * S 2 * S 3 := by
  simp [wordUp, ascendingWord, List.range', mul_assoc]

theorem wordDown_four_one : wordDown S 4 1 = (S 3 : A) * S 2 * S 1 := by
  simp [wordDown, descendingWord, List.range', mul_assoc]

theorem wordUpStar_one_four :
    wordUpStar S 1 4 = (((S 1)⁻¹ : Aˣ) : A) * ((S 2)⁻¹ : Aˣ) * ((S 3)⁻¹ : Aˣ) := by
  simp [wordUpStar, ascendingWord, List.range', mul_assoc]

theorem wordDownStar_four_one :
    wordDownStar S 4 1 = (((S 3)⁻¹ : Aˣ) : A) * ((S 2)⁻¹ : Aˣ) * ((S 1)⁻¹ : Aˣ) := by
  simp [wordDownStar, descendingWord, List.range', mul_assoc]

/-! ### The three cancellations

The unstarred and starred words cancel in three of the four possible pairings. All three come from
one fact about lists, `HJO.Braid.prod_map_mul_prod_reverse_map_inv`, applied to the index range
`List.range' i (j - i)` that all four words are built on: read one way round it is
`HJO.Braid.wordUp_mul_wordDownStar`, with the range reversed it is
`HJO.Braid.wordDown_mul_wordUpStar`, and with the family replaced by its inverses it is
`HJO.Braid.wordDownStar_mul_wordUp`. -/

/-- **A word in a family of units cancels the reversed word in their inverses.** For any list `L` of
indices, `(∏_{r ∈ L} f_r) · (∏_{r ∈ L^{rev}} f_r^{-1}) = 1`: the outermost pair cancels, and the
rest is the same statement for the tail.

This is where all three cancellation lemmas below come from. It is stated for a list rather than for
`List.range'` because the induction is on the list; the words of this file are the case
`L = List.range' i (j - i)`, and the induction step `j ↦ j - 1` of the proofs is the
`cons` step here. -/
theorem prod_map_mul_prod_reverse_map_inv (f : ℕ → Aˣ) (L : List ℕ) :
    ((L.map fun r => ((f r : A))).prod) *
      ((L.reverse.map fun r => (((f r)⁻¹ : Aˣ) : A)).prod) = 1 := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have h : ((a :: t).reverse.map fun r => (((f r)⁻¹ : Aˣ) : A)).prod
        = ((t.reverse.map fun r => (((f r)⁻¹ : Aˣ) : A)).prod) * (((f a)⁻¹ : Aˣ) : A) := by
      simp [List.reverse_cons]
    rw [List.map_cons, List.prod_cons, h]
    calc ((f a : A) * (t.map fun r => ((f r : A))).prod)
          * ((t.reverse.map fun r => (((f r)⁻¹ : Aˣ) : A)).prod * (((f a)⁻¹ : Aˣ) : A))
        = (f a : A) * ((t.map fun r => ((f r : A))).prod
            * (t.reverse.map fun r => (((f r)⁻¹ : Aˣ) : A)).prod) * (((f a)⁻¹ : Aˣ) : A) := by
          simp only [mul_assoc]
      _ = 1 := by rw [ih, mul_one]; exact Units.mul_inv (f a)

/-- **An ascending word cancels a starred descending word**: `S_{i↑j} S^*_{j↓i} = 1`.

No bound `1 ≤ i ≤ j ≤ m + 1` is needed: both words read the same index range
`List.range' i (j - i)`, empty when `j ≤ i`, so the identity holds for all `i` and `j`. -/
@[hjo "lem_dpa_word_cancel_up"]
theorem wordUp_mul_wordDownStar (i j : ℕ) : wordUp S i j * wordDownStar S j i = 1 :=
  prod_map_mul_prod_reverse_map_inv S (List.range' i (j - i))

/-- **A starred descending word cancels an ascending word**: `S^*_{j↓i} S_{i↑j} = 1`.

One can argue that `S_{i↑j}` is invertible, being a product of invertible elements, so its
right inverse from `HJO.Braid.wordUp_mul_wordDownStar` is a two-sided inverse. Here the same fact is
read off directly: the product is `prod_map_mul_prod_reverse_map_inv` at the family of inverses
`r ↦ S_r^{-1}` and the reversed index range, `(S_r^{-1})^{-1}` being `S_r`. Nothing is inverted. -/
@[hjo "lem_dpa_word_cancel_down"]
theorem wordDownStar_mul_wordUp (i j : ℕ) : wordDownStar S j i * wordUp S i j = 1 := by
  have h := prod_map_mul_prod_reverse_map_inv (fun r => (S r)⁻¹) (List.range' i (j - i)).reverse
  simp only [inv_inv, List.reverse_reverse] at h
  exact h

/-- **A descending word cancels a starred ascending word**: `S_{j↓i} S^*_{i↑j} = 1`.

Note that this is a genuinely different identity from `wordUp_mul_wordDownStar` and not its reverse:
the descending word reads the letters in the opposite order from the ascending one, so the
cancellation here starts at the *inner* index `i` where the other starts at `j - 1`. In the proof
that is the index range being reversed before the induction. -/
@[hjo "lem_dpa_word_cancel_mixed"]
theorem wordDown_mul_wordUpStar (i j : ℕ) : wordDown S j i * wordUpStar S i j = 1 := by
  have h := prod_map_mul_prod_reverse_map_inv S (List.range' i (j - i)).reverse
  rw [List.reverse_reverse] at h
  exact h

/-- The fourth pairing, `S^*_{i↑j} S_{j↓i} = 1`. The other three are what the later results use;
this one is the same fact about lists read at the family of inverses, and it is what makes the two
unstarred words two-sidedly invertible below. -/
theorem wordUpStar_mul_wordDown (i j : ℕ) : wordUpStar S i j * wordDown S j i = 1 := by
  have h := prod_map_mul_prod_reverse_map_inv (fun r => (S r)⁻¹) (List.range' i (j - i))
  simp only [inv_inv] at h
  exact h

/-- The ascending word is a unit, the starred descending word being its two-sided inverse. `A` is
not assumed commutative, so both cancellations are needed. -/
theorem isUnit_wordUp (i j : ℕ) : IsUnit (wordUp S i j) :=
  ⟨⟨wordUp S i j, wordDownStar S j i, wordUp_mul_wordDownStar S i j,
    wordDownStar_mul_wordUp S i j⟩, rfl⟩

/-- The descending word is a unit, the starred ascending word being its two-sided inverse. -/
theorem isUnit_wordDown (i j : ℕ) : IsUnit (wordDown S j i) :=
  ⟨⟨wordDown S j i, wordUpStar S i j, wordDown_mul_wordUpStar S i j,
    wordUpStar_mul_wordDown S i j⟩, rfl⟩

end HJO.Braid
