/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SquareDyck
public import HJO.DyckAttackSets
public meta import HJO.Attr

/-! # The no-attack labellings with prescribed special values

The characteristic function `ν_σ(π)` of a partial Dyck path is a sum over the labellings of the path
that give distinct letters to the two positions of every attacking pair and carry prescribed letters
at the first `k` positions. This file defines that index set, Carlsson and Mellit's `U(π, σ)`, and
nothing else.

## Main definitions

* `HJO.Dyck.noAttackLabellings`: `U(π, σ)`.

## Implementation notes

`U(π, σ)` is a `Set` and not a `Finset`: it is infinite, the letters being unbounded. The consumers
sum over it coefficientwise, cutting out the labellings with letters in a given finite range, which
is what `decidablePredMemNoAttackLabellings` is for.

Positions and letters are indexed from `0`, as everywhere in this layer, and the condition `N ≥ k`
is spent only where a position of `Fin k` is read as one of `Fin N`
(`mem_noAttackLabellings_iff_castLE`). No hypothesis is imposed on `x` or on `σ`: Carlsson and
Mellit's requirement that `σ` have pairwise distinct entries is not assumed but *derived* where it
is actually needed — `injective_of_mem_noAttackLabellings_zero` shows that at the lowest path a
labelling exists only for an injective `σ`, and `noAttackLabellings_eq_empty_example` exhibits the
emptiness a repeated special letter causes.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 3, characteristic functions of partial Dyck paths: Definition
`HJO.Dyck.noAttackLabellings`.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

/-- The no-attack labellings of `x` with prescribed special values `σ`, Carlsson and Mellit's
`U(π, σ) = {w ∈ ℤ_{>0}^N : w_i = σ_i for i ≤ k, w_i ≠ w_j for (i,j) ∈ At(π)}`: the tuples `w` of `N`
letters whose entry at each position below `k` is the entry of `σ` there, and which give distinct
letters to the two positions of every attacking pair of `x`. Positions and letters are indexed from
`0`; no hypothesis is imposed on `x` or on `σ`. -/
@[hjo "def_cm_noattack"]
def noAttackLabellings {N k : ℕ} (x : Fin N → ℕ) (σ : Fin k → ℕ) : Set (Fin N → ℕ) :=
  {w | (∀ (i : Fin N) (j : Fin k), (i : ℕ) = (j : ℕ) → w i = σ j) ∧
    ∀ i j : Fin N, ((i : ℕ), (j : ℕ)) ∈ attackSet x → w i ≠ w j}

variable {N k : ℕ} {x y : Fin N → ℕ} {σ : Fin k → ℕ} {w : Fin N → ℕ}

/-- A labelling lies in `U(π, σ)` exactly when it satisfies Carlsson and Mellit's two conditions: it
agrees with `σ` at the positions below `k`, and it gives distinct letters to the two positions of
every attacking pair. -/
theorem mem_noAttackLabellings :
    w ∈ noAttackLabellings x σ ↔
      (∀ (i : Fin N) (j : Fin k), (i : ℕ) = (j : ℕ) → w i = σ j) ∧
        ∀ i j : Fin N, ((i : ℕ), (j : ℕ)) ∈ attackSet x → w i ≠ w j :=
  Iff.rfl

/-- Membership in `U(π, σ)` is decidable: both conditions are bounded quantifications over the
positions. This is what cuts the labellings with letters in a given finite set out of the tuples
with letters there, the form in which the sums over `U(π, σ)` are formed coefficientwise. -/
instance decidablePredMemNoAttackLabellings (x : Fin N → ℕ) (σ : Fin k → ℕ) :
    DecidablePred (· ∈ noAttackLabellings x σ) := fun _ =>
  decidable_of_iff _ mem_noAttackLabellings.symm

/-- The prescription: a labelling of `U(π, σ)` carries the letter `σ_j` at the position of the same
index. -/
theorem eq_of_mem_noAttackLabellings (hw : w ∈ noAttackLabellings x σ) {i : Fin N} {j : Fin k}
    (hij : (i : ℕ) = (j : ℕ)) : w i = σ j := hw.1 i j hij

/-- The no-attack condition: a labelling of `U(π, σ)` gives distinct letters to the two positions
of an attacking pair. -/
theorem ne_of_mem_noAttackLabellings (hw : w ∈ noAttackLabellings x σ) {i j : Fin N}
    (hij : ((i : ℕ), (j : ℕ)) ∈ attackSet x) : w i ≠ w j := hw.2 i j hij

/-- The prescription with the position given as an element of `Fin k`, which is where the condition
`N ≥ k` is spent: the first `k` letters of a labelling of `U(π, σ)` are those of `σ`. -/
theorem apply_castLE_of_mem_noAttackLabellings (hk : k ≤ N)
    (hw : w ∈ noAttackLabellings x σ) (j : Fin k) : w (Fin.castLE hk j) = σ j := hw.1 _ j rfl

/-- Membership in `U(π, σ)` for a level at most the length, with the prescription read at the
positions `Fin.castLE`: the form in which a labelling is checked or constructed. -/
theorem mem_noAttackLabellings_iff_castLE (hk : k ≤ N) :
    w ∈ noAttackLabellings x σ ↔ (∀ j : Fin k, w (Fin.castLE hk j) = σ j) ∧
      ∀ i j : Fin N, ((i : ℕ), (j : ℕ)) ∈ attackSet x → w i ≠ w j := by
  rw [mem_noAttackLabellings]
  refine and_congr_left' ⟨fun h j => h _ j rfl, fun h i j hij => ?_⟩
  have hi : i = Fin.castLE hk j := Fin.ext (by simpa using hij)
  rw [hi]
  exact h j

/-- The path is read only through its attack set: two paths with the same attacking pairs have the
same no-attack labellings. This is how a description of `At(π)` after a step of a recursion is
transported to the labellings. -/
theorem noAttackLabellings_congr (h : attackSet x = attackSet y) (σ : Fin k → ℕ) :
    noAttackLabellings x σ = noAttackLabellings y σ := by
  simp only [noAttackLabellings, h]

/-- More attacking pairs are more conditions: enlarging the attack set shrinks the no-attack
labellings. -/
theorem noAttackLabellings_subset_of_subset (h : attackSet x ⊆ attackSet y) (σ : Fin k → ℕ) :
    noAttackLabellings y σ ⊆ noAttackLabellings x σ :=
  fun _ hw => ⟨hw.1, fun i j hij => hw.2 i j (h hij)⟩

/-- Raising a path enlarges its no-attack labellings, the attack set being antitone: there is less
room between the path and the diagonal, hence fewer attacking pairs to separate. -/
theorem noAttackLabellings_monotone (σ : Fin k → ℕ) :
    Monotone fun x : Fin N → ℕ => noAttackLabellings x σ :=
  fun _ _ h => noAttackLabellings_subset_of_subset (attackSet_antitone h) σ

/-- At the staircase path hugging the diagonal the no-attack condition is vacuous, its attack set
being empty, and only the prescription remains. -/
theorem noAttackLabellings_val (σ : Fin k → ℕ) :
    noAttackLabellings (Fin.val : Fin N → ℕ) σ =
      {w | ∀ (i : Fin N) (j : Fin k), (i : ℕ) = (j : ℕ) → w i = σ j} := by
  ext w
  simp [noAttackLabellings, attackSet_val]

/-- At the lowest path, whose `N` north steps all precede its east steps and whose attack set is the
whole window, the no-attack condition is injectivity of the labelling. This is the path lying in
every `𝔻_{k,N}`, so it is where Carlsson and Mellit's distinctness of `σ` is forced. -/
theorem noAttackLabellings_zero (σ : Fin k → ℕ) :
    noAttackLabellings (0 : Fin N → ℕ) σ =
      {w | (∀ (i : Fin N) (j : Fin k), (i : ℕ) = (j : ℕ) → w i = σ j) ∧ Function.Injective w} := by
  have key : ∀ a b : Fin N, (a : ℕ) < (b : ℕ) →
      ((a : ℕ), (b : ℕ)) ∈ attackSet (0 : Fin N → ℕ) :=
    fun a b hab => mem_attackSet.2 ⟨b.isLt, by simp, hab⟩
  ext w
  simp only [Set.mem_ofPred_eq, mem_noAttackLabellings]
  refine and_congr_right' ⟨fun h a b hab => ?_, fun h i j hij hw => ?_⟩
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h a b (key a b (by simpa using hlt)) hab
    · exact h b a (key b a (by simpa using hlt)) hab.symm
  · exact absurd (h hw) (Fin.val_ne_iff.1 (fst_lt_snd_of_mem_attackSet hij).ne)

/-- The labelling carrying the letter `i` at the position `i` lies in `U(π, Id_k)` for every path
and every level: its letters at the two positions of an attacking pair differ because those
positions do. So no set `U(π, Id_k)` is empty, at any level and for any path. -/
theorem val_mem_noAttackLabellings (x : Fin N → ℕ) (k : ℕ) :
    (Fin.val : Fin N → ℕ) ∈ noAttackLabellings x (Fin.val : Fin k → ℕ) :=
  ⟨fun _ _ hij => hij, fun _ _ hij => Nat.ne_of_lt (fst_lt_snd_of_mem_attackSet hij)⟩

/-- At the lowest path a labelling exists only for an injective `σ`: it restricts to `σ` on the
first `k` positions and is injective there. This is Carlsson and Mellit's distinctness of `σ`,
obtained as a consequence of nonemptiness instead of assumed. -/
theorem injective_of_mem_noAttackLabellings_zero (hk : k ≤ N)
    (hw : w ∈ noAttackLabellings (0 : Fin N → ℕ) σ) : Function.Injective σ := by
  rw [noAttackLabellings_zero] at hw
  intro j j' hjj'
  have e : w (Fin.castLE hk j) = w (Fin.castLE hk j') := by
    rw [hw.1 _ j rfl, hw.1 _ j' rfl, hjj']
  exact Fin.ext (by simpa using congrArg Fin.val (hw.2 e))

/-- On the worked path `x(π) = (1,2,2,2,3,3,7,7)` of Carlsson and Mellit's Example 2.1, which is
`![0,1,1,1,2,2,6,6]` here, the labelling `![0,0,1,2,3,4,0,1]` has no attack: it repeats a letter at
the positions `0` and `1`, which do not attack, so `U(π, σ)` is strictly larger than the set of
injective labellings. -/
theorem noAttackLabellings_source_example :
    ![0, 0, 1, 2, 3, 4, 0, 1] ∈
      noAttackLabellings ![0, 1, 1, 1, 2, 2, 6, 6] (![] : Fin 0 → ℕ) := by decide

/-- Changing the last letter of that labelling to repeat the letter at position `6` breaks the
no-attack condition, the pair `(6, 7)` attacking. -/
theorem notMem_noAttackLabellings_source_counterexample :
    ![0, 0, 1, 2, 3, 4, 0, 0] ∉
      noAttackLabellings ![0, 1, 1, 1, 2, 2, 6, 6] (![] : Fin 0 → ℕ) := by decide

/-- That worked path lies in `𝔻_{1,8}`, and at that level the prescription `σ = (8)`, here
`![7]`, forces the letter at the position `0`. -/
theorem noAttackLabellings_source_example_level_one :
    ![7, 0, 1, 2, 3, 4, 0, 1] ∈ noAttackLabellings ![0, 1, 1, 1, 2, 2, 6, 6] ![7] := by decide

/-- The prescription is not dead: the labelling of `noAttackLabellings_source_example` has no
attack on the same path and is rejected at level `1` for its letter at the position `0` alone,
that position lying in no attacking pair there. -/
theorem notMem_noAttackLabellings_source_counterexample_level_one :
    ![0, 0, 1, 2, 3, 4, 0, 1] ∉ noAttackLabellings ![0, 1, 1, 1, 2, 2, 6, 6] ![7] := by decide

/-- A repeated special letter leaves no labelling at the lowest path: at length `2` the two
positions attack, so they cannot both carry the letter `5`. -/
theorem noAttackLabellings_eq_empty_example :
    noAttackLabellings (0 : Fin 2 → ℕ) ![5, 5] = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ hw =>
    (by decide : ¬Function.Injective ![(5 : ℕ), 5])
      (injective_of_mem_noAttackLabellings_zero le_rfl hw)

/-- The same repeated special letter is admissible on the staircase path, whose attack set is
empty: the emptiness above is caused by the path and not by the prescription alone. -/
theorem mem_noAttackLabellings_val_example :
    ![5, 5] ∈ noAttackLabellings (Fin.val : Fin 2 → ℕ) ![5, 5] := by decide

/-- At the lowest path of length `3` the no-attack labellings by `3` letters are the `3! = 6`
injective ones, out of the `27` labellings. -/
theorem card_filter_mem_noAttackLabellings_zero_three :
    #{w ∈ Fintype.piFinset fun _ : Fin 3 => range 3 |
        w ∈ noAttackLabellings (0 : Fin 3 → ℕ) (![] : Fin 0 → ℕ)} = 6 := by decide

/-- Two letters do not suffice for `3` pairwise attacking positions: none of those `8` labellings
lies in `U(0, ![])`. -/
theorem card_filter_mem_noAttackLabellings_zero_two :
    #{w ∈ Fintype.piFinset fun _ : Fin 3 => range 2 |
        w ∈ noAttackLabellings (0 : Fin 3 → ℕ) (![] : Fin 0 → ℕ)} = 0 := by decide

end HJO.Dyck
