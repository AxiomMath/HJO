/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public meta import HJO.Attr

/-! # The label tuples of the Carlsson--Mellit recursions

The characteristic function `ν_σ(π)` of a partial Dyck path is indexed by a tuple `σ` of distinct
labels prescribing the letters carried by the path's first steps, and each of the two recursions of
Carlsson and Mellit moves that tuple in a fixed way. This file defines the three tuples they
prescribe, the two relabellings of letters they use, and the east inverse `D_k`, which moves the
path rather than the tuple: all of them are plain functions between the tuple types `Fin m → ℕ`,
and the recursions themselves live above.

## Main definitions

* `HJO.Dyck.identityTuple`: `Id_k`, the tuple whose `i`-th entry is `i`.
* `HJO.Dyck.lowerTuple`: `σ^{[r]} = (1, …, k-1, k+r)`, the tuple of the lowering recursion.
* `HJO.Dyck.cycleTuple`: `σ^{(i)}`, the tuple interpolating from `Id_{k+1}` to the cyclic shift.
* `HJO.Dyck.transposeTuple`: `τ_m σ`, the tuple with the labels `m` and `m+1` interchanged.
* `HJO.Dyck.prependLabel`: `E^*_k w`, prepending the new special label to a labelling.
* `HJO.Dyck.eastInverse`: `D_k(x)`, deleting the `k`-th east step from a path.

## Main results

* `HJO.Dyck.cycleTuple_zero_eq_identityTuple` and
  `HJO.Dyck.cycleTuple_last_eq_prependLabel_identityTuple`: the two distinguished members of the
  family `σ^{(i)}`, namely `σ^{(1)} = Id_{k+1}` at one end and `σ^{(k+1)} = E^*_k Id_k` at the
  other. The second is the prescription carried by the target of the raising recursion, and reading
  it as a prepended identity tuple is what lets that recursion be compared with `E^*_k`.

## Implementation notes

Positions and labels are both indexed from `0`, as for the paths of `HJO.Dyck.IsSquareDyck`, so the
`1`-based label `i` is `i - 1` here and the `1`-based position `j` is `j - 1`. The side conditions
`k ≥ 1` and `N ≥ k` are carried in the shapes of the types where they are needed — `Fin (m + 1)` for
`lowerTuple`, `Fin (N + 1) → Fin N` for `eastInverse` — and nowhere else: every formula below is
total, and no lemma applies one outside the range `k ≥ 1`, `N ≥ k`.

`eastInverse` is a function between the tuple types `Fin (N + 1) → ℕ` and `Fin N → ℕ` rather than
one on lists. Lists would give the length `N - 1` for free, but the lemmas that use it test
membership of the value in `𝔻_{k-1,N-1}`, which is `HJO.Dyck.IsPartialDyck` on a tuple; going
through lists would put a length coercion on each of those, and writing the domain as `Fin (N + 1)`
removes the truncated subtraction from the length instead.

## References

This file defines `HJO.Dyck.identityTuple`, `HJO.Dyck.lowerTuple`, `HJO.Dyck.cycleTuple`,
`HJO.Dyck.transposeTuple`, `HJO.Dyck.prependLabel` and `HJO.Dyck.eastInverse`, used by the raising
recursion, the lowering recursion, the swapping operators and the assembly of the word.
-/

@[expose] public section

namespace HJO.Dyck

/-! ### The three distinguished tuples -/

/-- The identity tuple `Id_k`: the `k`-tuple whose `i`-th entry is `i`, the special labels being
the first `k` letters, each at its own position. Positions and letters are both indexed from `0`,
so this is the `1`-based `(1, 2, …, k)` and the entry at the `0`-based position `i` is the letter
`i`, namely the coercion `Fin k → ℕ`. -/
@[hjo "def_cm_identity_tuple"]
abbrev identityTuple (k : ℕ) : Fin k → ℕ := Fin.val

/-- Every entry of `Id_k` is a label of the level `k`. -/
theorem identityTuple_lt (k : ℕ) (i : Fin k) : identityTuple k i < k := i.isLt

/-- The entries of `Id_k` are pairwise distinct, which is what makes it a tuple of labels. -/
theorem identityTuple_injective (k : ℕ) : Function.Injective (identityTuple k) :=
  Fin.val_injective

/-- The lower tuple `σ^{[r]}` of the lowering recursion: the `k`-tuple `(1, …, k-1, k+r)`, for
`k = m + 1 ≥ 1` and `r ≥ 0`, whose entries prescribe the first `k` letters of the labellings
counted by `μ_r(π)`. Positions and letters are both indexed from `0`, so the entry at the position
`i < m` is the letter `i` and the entry at the last position is the letter `m + r`, the `1`-based
`k + r`; at `r = 0` this is `HJO.Dyck.identityTuple (m + 1)`. -/
@[hjo "def_cm_lower_tuple"]
def lowerTuple (m r : ℕ) : Fin (m + 1) → ℕ := Fin.snoc Fin.val (m + r)

/-- The entries of `σ^{[r]}` before the last one are the `1`-based `σ_i = i` for `1 ≤ i ≤ k-1`,
read here at the `0`-based position `i < m` as the letter `i`. -/
@[simp]
theorem lowerTuple_castSucc (m r : ℕ) (i : Fin m) : lowerTuple m r i.castSucc = (i : ℕ) :=
  Fin.snoc_castSucc _ _ _

/-- The last entry of `σ^{[r]}` is the freed label, the `1`-based `σ_k = k + r`, read here as the
letter `m + r`. -/
@[simp]
theorem lowerTuple_last (m r : ℕ) : lowerTuple m r (Fin.last m) = m + r :=
  Fin.snoc_last _ _

/-- At `r = 0` the lower tuple is the identity tuple, `σ^{[0]} = Id_k`. This is the
second conclusion of `HJO.Dyck.lowerTuple_zero`; the first, that the entries are pairwise
distinct, is `HJO.Dyck.lowerTuple_injective`. -/
@[hjo "lem_cm_lower_tuple_distinct", simp]
theorem lowerTuple_zero (m : ℕ) : lowerTuple m 0 = identityTuple (m + 1) := by
  refine funext fun i => ?_
  induction i using Fin.lastCases with
  | last => rw [lowerTuple_last, Nat.add_zero]; rfl
  | cast i => rw [lowerTuple_castSucc]; rfl

/-- The tuple `σ^{(i)}` interpolating from the identity tuple to the cyclic shift: the
`(k+1)`-tuple whose first entry is the label `i` and whose remaining entries list the other labels
in increasing order. Positions and labels are both indexed from `0`, so this is the `1`-based
`σ^{(i+1)} = (i+1, 1, …, i, i+2, …, k+1)`: the entry at position `0` is `i`, the entry at a
position `0 < j ≤ i` is `j - 1`, and the entry at a position `j > i` is `j`. Equivalently it is
the inverse of the cycle `Fin.cycleRange i` on the first `i` positions, read as a labelling. -/
@[hjo "def_cm_sigmaseq"]
def cycleTuple {k : ℕ} (i : Fin (k + 1)) : Fin (k + 1) → ℕ := fun j => (i.cycleRange.symm j : ℕ)

/-- The first entry of `σ^{(i)}` is the label `i`. -/
@[simp]
theorem cycleTuple_zero {k : ℕ} (i : Fin (k + 1)) : cycleTuple i 0 = (i : ℕ) :=
  congrArg Fin.val (Fin.cycleRange_symm_zero i)

/-- The entries of `σ^{(i)}` after the first list the labels other than `i` in increasing order:
the entry at position `j + 1` is `Fin.succAbove i j`, namely `j` for `j < i` and `j + 1` for
`j ≥ i`. -/
@[simp]
theorem cycleTuple_succ {k : ℕ} (i : Fin (k + 1)) (j : Fin k) :
    cycleTuple i j.succ = (i.succAbove j : ℕ) :=
  congrArg Fin.val (Fin.cycleRange_symm_succ i j)

/-- The second clause of the definition: at a position `j` with `0 < j ≤ i` the entry of `σ^{(i)}`
is `j - 1`. -/
theorem cycleTuple_of_pos_of_le {k : ℕ} {i j : Fin (k + 1)} (h0 : 0 < j) (h : j ≤ i) :
    cycleTuple i j = (j : ℕ) - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j' : Fin k, j = j'.succ := ⟨j.pred h0.ne', by simp⟩
  rw [cycleTuple_succ, Fin.succAbove_of_castSucc_lt]
  · simp
  · exact lt_of_lt_of_le (by simp [Fin.lt_def]) h

/-- The third clause of the definition: at a position `j` with `j > i` the entry of `σ^{(i)}` is
`j`. -/
theorem cycleTuple_of_lt {k : ℕ} {i j : Fin (k + 1)} (h : i < j) : cycleTuple i j = (j : ℕ) :=
  congrArg Fin.val (Equiv.symm_apply_eq _ |>.mpr (Fin.cycleRange_of_gt h).symm)

/-- Every entry of `σ^{(i)}` is a label of the level `k + 1`. -/
theorem cycleTuple_lt {k : ℕ} (i j : Fin (k + 1)) : cycleTuple i j < k + 1 :=
  (i.cycleRange.symm j).isLt

/-- The entries of `σ^{(i)}` are pairwise distinct: it is a permutation of the labels read as a
tuple. -/
theorem cycleTuple_injective {k : ℕ} (i : Fin (k + 1)) : Function.Injective (cycleTuple i) :=
  Fin.val_injective.comp (i.cycleRange.symm.injective)

/-- The first member of the family is the identity tuple, the `1`-based `σ^{(1)} = Id_{k+1}`. -/
@[simp]
theorem cycleTuple_zero_eq_identityTuple {k : ℕ} :
    cycleTuple (0 : Fin (k + 1)) = identityTuple (k + 1) :=
  funext fun j => congrArg Fin.val (Equiv.symm_apply_eq _ |>.mpr (by simp [Fin.cycleRange_zero]))

/-- A worked example of the last member of the family, the cyclic shift
`σ^{(3)} = (3, 0, 1, 2)` at `k = 3` on labels indexed from `0`; its general form is
`HJO.Dyck.cycleTuple_last_eq_prependLabel_identityTuple`, and the `decide` below is independent
of that lemma, so the two check each other. -/
theorem cycleTuple_last_three : cycleTuple (Fin.last 3) = ![3, 0, 1, 2] := by decide

/-! ### The two relabellings -/

/-- The tuple `τ_m σ`, obtained from a tuple `σ` of letters by applying to each of its entries the
transposition of letters interchanging `m` and `m+1`: the `i`-th entry of `τ_m σ` is `m+1` if
`σ_i = m`, is `m` if `σ_i = m+1`, and is `σ_i` otherwise. Letters are indexed from `0`, so `m` is
the `1`-based `m - 1`, and the index type is untouched — the letters are permuted, the positions
are not. -/
@[hjo "def_cm_transposetuple"]
abbrev transposeTuple {ι : Type*} (m : ℕ) (σ : ι → ℕ) : ι → ℕ := Equiv.swap m (m + 1) ∘ σ

/-- The swap is an involution on tuples: `τ_m (τ_m σ) = σ`. -/
@[simp]
theorem transposeTuple_transposeTuple {ι : Type*} (m : ℕ) (σ : ι → ℕ) :
    transposeTuple m (transposeTuple m σ) = σ := by
  simp [transposeTuple, Function.comp_def]

/-- The map `E^*_k` of the raising recursion: prepending the new special label to a labelling,
sending a labelling `w` of `N` letters to the labelling of `N + 1` letters whose first entry is the
letter `k` and whose entry at the position `i + 1` is `w i`. Positions and letters are both indexed
from `0`, so the prepended letter `k` is the `1`-based `k + 1`, the label the level `k + 1` adds. -/
@[hjo "def_cm_east_relabel"]
abbrev prependLabel (k : ℕ) {N : ℕ} (w : Fin N → ℕ) : Fin (N + 1) → ℕ := Fin.cons k w

/-- The last member of the family `σ^{(i)}` is the identity tuple with the new label prepended,
in `1`-based notation `σ^{(k+1)} = E^*_k Id_k = (k+1, 1, …, k)`: both sides read `(k, 0, 1, …, k-1)`
entrywise. This is the form in which the prescription of the target of the raising recursion is
read, and it is where that prescription's injectivity comes from, through
`HJO.Dyck.cycleTuple_injective`. Not a `simp` lemma: `cycleTuple (Fin.last k)` is the spelling the
raising recursion states its target in, and rewriting it away is a step a proof takes
deliberately. -/
theorem cycleTuple_last_eq_prependLabel_identityTuple (k : ℕ) :
    cycleTuple (Fin.last k) = prependLabel k (identityTuple k) := by
  refine funext fun j => ?_
  induction j using Fin.cases with
  | zero => simp
  | succ i => simp [Fin.succAbove_last]

/-! ### Deleting an east step -/

/-- The east inverse `D_k(x)` of the assembly: the sequence of length `N` obtained from a sequence
`x` of length `N + 1` by deleting the `k`-th east step, whose entry at the position `j` is the
minimal value `1` — here `0` — for `j + 1 < k` and `x_{j+1} - 1` for `j + 1 ≥ k`.

Positions and entries are both indexed from `0`, so the `1`-based condition `1 ≤ j ≤ k - 1` on the
untouched initial entries reads `j + 1 < k` and its `x_{j+1} - 1` reads `x (j + 1) - 1`, one
subtraction rather than two. Written this way the formula is total in `k`, and the hypotheses
`k ≥ 1` and `N ≥ k` are not needed to state it: at `k = 0` the first branch is empty and the map is
the plain shift-and-lower, which is `D_1` in `1`-based notation. -/
@[hjo "def_cm_east_inverse"]
def eastInverse (k : ℕ) {N : ℕ} (x : Fin (N + 1) → ℕ) : Fin N → ℕ :=
  fun j => if (j : ℕ) + 1 < k then 0 else x j.succ - 1

/-- The initial entries of `D_k(x)` are minimal, the `1`-based `1`: this is the first branch of the
definition, at the positions `j` with `j + 1 < k`. -/
@[simp]
theorem eastInverse_of_lt {k N : ℕ} (x : Fin (N + 1) → ℕ) {j : Fin N} (h : (j : ℕ) + 1 < k) :
    eastInverse k x j = 0 := by
  simp [eastInverse, h]

/-- The remaining entries of `D_k(x)` are `x_{j+1} - 1`: this is the second branch,
at the positions `j` with `j + 1 ≥ k`. -/
@[simp]
theorem eastInverse_of_le {k N : ℕ} (x : Fin (N + 1) → ℕ) {j : Fin N} (h : k ≤ (j : ℕ) + 1) :
    eastInverse k x j = x j.succ - 1 := by
  simp [eastInverse, Nat.not_lt.2 h]

/-- `D_k(x)` does not see the entries of `x` below the east step it deletes: the initial entries of
the value are held at the minimum and mention no sequence at all, and the remaining ones read `x`
only at the positions `p ≥ k`. For `k ≥ 1`, which is the range of the definition, those positions
are exactly the ones the value depends on, the position `0` being read at no level. -/
theorem eastInverse_congr {k N : ℕ} {x y : Fin (N + 1) → ℕ}
    (h : ∀ p : Fin (N + 1), k ≤ (p : ℕ) → x p = y p) :
    eastInverse k x = eastInverse k y := by
  refine funext fun j => ?_
  rcases lt_or_ge ((j : ℕ) + 1) k with hj | hj
  · rw [eastInverse_of_lt _ hj, eastInverse_of_lt _ hj]
  · rw [eastInverse_of_le _ hj, eastInverse_of_le _ hj, h j.succ (by simpa using hj)]

/-- The east inverse of a worked example path, whose coarea sequence is
`x(π) = (1, 2, 2, 2, 3, 3, 7, 7)` and which reads `(0, 1, 1, 1, 2, 2, 6, 6)` here, at `k = 3`: the
first two entries are held at the minimum and the remaining five are the last five entries of `x`
lowered by one and shifted into place, giving `(0, 0, 0, 1, 1, 5, 5)`. -/
theorem eastInverse_source_example :
    eastInverse 3 ![0, 1, 1, 1, 2, 2, 6, 6] = ![0, 0, 0, 1, 1, 5, 5] := by decide

end HJO.Dyck
