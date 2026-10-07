/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import HJO.CarlssonMellit.SquareDyck
public meta import HJO.Attr

/-! # Partial Dyck paths: prepending an east step, the level word, and the corner flip

Three operations on the coarea sequences of `HJO.Dyck.IsSquareDyck` are read by the recursions of
the Carlsson--Mellit layer, and this file defines them.

`E_k` prepends an east step to a partial Dyck path of level `k`, which is the move of the raising
recursion: the value is a sequence of length `n + 1` whose first `k + 1` entries are the virtual
north steps of the new level and whose remaining entries are the old ones raised by one.

`w_k(π)` is the step word of a sequence read at the level `k`, the word of length `2N - k` in
`{+, -}` recording the steps of the partial path in reading order; on a path whose first `k` entries
are minimal it is the step word of the underlying square path with its first `k` letters deleted,
which is `partialStepWord_eq_drop_stepWord`, and that is what makes it the word `w_k` of the
recursion rather than an independent reading of the same combinatorics.

`π_S` lowers the entry of a path at each position whose corner cell lies in `S`, which is the move
of the corner inclusion--exclusion: the cells adjoined are exactly those of `S`.

## Main definitions

* `HJO.Dyck.prependEast`: `E_kπ`.
* `HJO.Dyck.partialStepWord`: `w_k(π)`.
* `HJO.Dyck.flipCorners`: `π_S`.

## Implementation notes

Positions and entries are both indexed from `0`, as for `HJO.Dyck.IsSquareDyck`, so the paper's
`x_j` for `1 ≤ j ≤ n` is `x (j - 1) + 1`, and levels are unshifted. The step word emits `Mathlib`'s
`DyckStep`, with `U` for the paper's `-` (a north step) and `D` for its `+` (an east step), as a
plain `List DyckStep` rather than a `DyckWord`: the consumers index positions and pair `r - 1` with
`r`, which `DyckWord`'s bundled balance conditions obstruct.

`flipCorners` is total on every `S`, the Dyck condition on the value being a separate lemma: the
consumers need the entrywise formula, and a subtype-valued definition would carry a proof
obligation into every rewrite. Its cells are named in the coordinates of `HJO.Dyck.corner`, so the
flipped position is the one whose corner cell `(x k - 1, k)` lies in `S`.

## References

The definitions `HJO.Dyck.prependEast`, `HJO.Dyck.partialStepWord` and `HJO.Dyck.flipCorners`; and
E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 2.2.
-/

@[expose] public section

namespace HJO.Dyck

open Finset List DyckStep

/-! ### Prepending an east step -/

/-- The map `E_k` of the raising recursion: prepending an east step to the beginning of a partial
Dyck path of level `k`, sending a sequence `x` of length `n` to the sequence of length `n + 1` whose
entry at a position `p ≤ k` is the minimal one — the one-based `x'_j = 1` for `1 ≤ j ≤ k + 1` — and
whose entry at the position `l + 1` with `l ≥ k` is `x l + 1`, the one-based `x'_j = x_{j-1} + 1`
for `k + 2 ≤ j ≤ n + 1`. Positions and entries are both indexed from `0`, so the paper's `x_j` is
`x (j - 1) + 1`. -/
@[hjo "def_cm_prepend_east"]
def prependEast (k : ℕ) {n : ℕ} (x : Fin n → ℕ) : Fin (n + 1) → ℕ :=
  Fin.cons 0 fun l => if (l : ℕ) < k then 0 else x l + 1

/-- The first entry of `E_kπ` is minimal, the one-based `x'_1 = 1`: the new path begins with an east
step, so its first north step is the first of the `k + 1` virtual ones. -/
@[simp]
theorem prependEast_zero {k n : ℕ} (x : Fin n → ℕ) : prependEast k x 0 = 0 :=
  rfl

/-- The entries of `E_kπ` after the first, by the two branches of the definition. -/
theorem prependEast_succ {k n : ℕ} (x : Fin n → ℕ) (l : Fin n) :
    prependEast k x l.succ = if (l : ℕ) < k then 0 else x l + 1 :=
  rfl

/-- The first clause of the one-based prescription: the entries of `E_kπ` at the positions `p ≤ k`
are minimal, the one-based `x'_j = 1` for `1 ≤ j ≤ k + 1`. These are the `k + 1` virtual north steps
of the new level, so the value does not depend on `π`. -/
theorem prependEast_of_le {k n : ℕ} (x : Fin n → ℕ) {p : Fin (n + 1)} (h : (p : ℕ) ≤ k) :
    prependEast k x p = 0 := by
  induction p using Fin.cases with
  | zero => rfl
  | succ l =>
    rw [Fin.val_succ] at h
    have hl : (l : ℕ) < k := by omega
    simp [prependEast_succ, hl]

/-- The second clause of the one-based prescription: the entry of `E_kπ` at the position `l + 1`
with `l ≥ k` is `x l + 1`, the one-based `x'_j = x_{j-1} + 1` for `k + 2 ≤ j ≤ n + 1`. Both sides
are lowered by one, so the surviving `+ 1` is the increase of the abscissa under the translation. -/
theorem prependEast_succ_of_le {k n : ℕ} (x : Fin n → ℕ) {l : Fin n} (h : k ≤ (l : ℕ)) :
    prependEast k x l.succ = x l + 1 := by
  have hl : ¬ (l : ℕ) < k := Nat.not_lt.2 h
  simp [prependEast_succ, hl]

/-- The second clause with a `ℕ`-valued position: for `k < p < n + 1` the entry of `E_kπ` at the
position `p` is `x (p - 1) + 1`. This is the form to cite when the position is an expression rather
than a `Fin.succ`. -/
theorem prependEast_mk_of_lt {k n p : ℕ} (x : Fin n → ℕ) (hp : p < n + 1) (h : k < p) :
    prependEast k x ⟨p, hp⟩ = x ⟨p - 1, by omega⟩ + 1 := by
  obtain ⟨p, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have hp' : p < n := by omega
  have hcast : (⟨p + 1, hp⟩ : Fin (n + 1)) = (⟨p, hp'⟩ : Fin n).succ := rfl
  rw [hcast, prependEast_succ_of_le x (l := ⟨p, hp'⟩) (Nat.le_of_lt_succ h)]
  rfl

/-- `E_kπ` does not see the entries of `π` below the level: the first `k` entries of a partial path
of level `k` are the encoding's virtual north steps, which `E_k` discards and replaces by the
`k + 1` virtual steps of the new level. -/
theorem prependEast_congr {k n : ℕ} {x y : Fin n → ℕ} (h : ∀ l : Fin n, k ≤ (l : ℕ) → x l = y l) :
    prependEast k x = prependEast k y := by
  refine funext fun p => ?_
  induction p using Fin.cases with
  | zero => rfl
  | succ l =>
    rcases le_or_gt k (l : ℕ) with hl | hl
    · rw [prependEast_succ_of_le x hl, prependEast_succ_of_le y hl, h l hl]
    · rw [prependEast_of_le x (by simp; omega), prependEast_of_le y (by simp; omega)]

/-- `E_k` sends the one element of `𝔻_{k,k}`, the empty partial path, to the minimal path of length
`k + 1`, all of whose entries are the paper's `x_j = 1`: every position of a sequence of length `k`
lies below the level, so every entry of the value is virtual. This is the base of the raising
recursion, and it holds for every sequence of length `k` because the entries below the level are
discarded. -/
@[simp]
theorem prependEast_self {k : ℕ} (x : Fin k → ℕ) : prependEast k x = 0 :=
  funext fun p => prependEast_of_le x (by omega)

/-- The paper's own worked path, whose coarea sequence is `x(π) = (1, 2, 2, 2, 3, 3, 7, 7)` and
which reads `![0, 1, 1, 1, 2, 2, 6, 6]` here, lies in `𝔻_{1,8}`: its first entry is minimal and its
second is not, so it is a partial Dyck path of level exactly `1`. -/
theorem isPartialDyck_source_example : IsPartialDyck 1 8 ![0, 1, 1, 1, 2, 2, 6, 6] := by decide

/-- Prepending an east step to the paper's worked path at its level `k = 1` gives the one-based
`(1, 1, 3, 3, 3, 4, 4, 8, 8)`, which reads `![0, 0, 2, 2, 2, 3, 3, 7, 7]` here: the first two
entries are the virtual steps of the level `2`, and the remaining seven are the last seven entries
of `x(π)` raised by one and shifted into place. -/
theorem prependEast_source_example :
    prependEast 1 ![0, 1, 1, 1, 2, 2, 6, 6] =
      (fun p => ![0, 0, 2, 2, 2, 3, 3, 7, 7] p : Fin 9 → ℕ) := by
  decide

/-- The value at the paper's worked path lies in `𝔻_{2,9}`: the witness that `E_k` lands in
`𝔻_{k+1,n+1}` at a path with a nonzero entry, the general statement being
`HJO.Dyck.isPartialDyck_prependEast`. -/
theorem isPartialDyck_prependEast_source_example :
    IsPartialDyck 2 9 (prependEast 1 ![0, 1, 1, 1, 2, 2, 6, 6]) := by decide

/-! ### The step word at a level -/


/-- The step word `w_k(π) = ε₁ ⋯ ε_{2N-k}` of the sequence `x : Fin N → ℕ` read at level `k`: the
word of length `2N - k` whose letter at position `s` is `U` — the paper's `-`, a north step —
when `x j + j = s + k` for some `j` with `k ≤ j`, and `D` — the paper's `+`, an east step —
otherwise. With levels unshifted and entries and positions indexed from `0`, `x j + j = s + k` is
the one-based `s = x_j + j - 1 - k` and `k ≤ j` its `k + 1 ≤ j`, so the letters marking north steps
sit at the abscissas of the north steps of the partial path shifted by their row indices and down
by the level, and the word is in the paper's reading order, from the bottom left end of the path
to its top right end. -/
@[hjo "def_cm_partial_word"]
def partialStepWord (k : ℕ) {N : ℕ} (x : Fin N → ℕ) : List DyckStep :=
  List.ofFn fun s : Fin (2 * N - k) =>
    if ∃ j : Fin N, k ≤ (j : ℕ) ∧ x j + (j : ℕ) = (s : ℕ) + k then U else D

@[simp]
theorem length_partialStepWord (k : ℕ) {N : ℕ} (x : Fin N → ℕ) :
    (partialStepWord k x).length = 2 * N - k :=
  List.length_ofFn

/-- The letters of the step word at level `k`, one by one: the prescription for
`ε_s`. -/
theorem getElem_partialStepWord (k : ℕ) {N : ℕ} (x : Fin N → ℕ) (s : ℕ)
    (hs : s < (partialStepWord k x).length) :
    (partialStepWord k x)[s] = if ∃ j : Fin N, k ≤ (j : ℕ) ∧ x j + (j : ℕ) = s + k then U else D :=
  List.getElem_ofFn hs

/-- The positions of the step word at level `k` carrying `U`, a north step, are exactly the
one-based `x_j + j - 1 - k` for `k + 1 ≤ j ≤ N`: this is the characterising property of the word,
and what a consumer cites in place of unfolding `partialStepWord`. -/
theorem getElem_partialStepWord_eq_U_iff (k : ℕ) {N : ℕ} (x : Fin N → ℕ) (s : ℕ)
    (hs : s < (partialStepWord k x).length) :
    (partialStepWord k x)[s] = U ↔ ∃ j : Fin N, k ≤ (j : ℕ) ∧ x j + (j : ℕ) = s + k := by
  rw [getElem_partialStepWord]
  split <;> simp_all

/-- Every other position of the step word at level `k` carries `D`, an east step, i.e.
`ε_s = +` otherwise. -/
theorem getElem_partialStepWord_eq_D_iff (k : ℕ) {N : ℕ} (x : Fin N → ℕ) (s : ℕ)
    (hs : s < (partialStepWord k x).length) :
    (partialStepWord k x)[s] = D ↔ ∀ j : Fin N, k ≤ (j : ℕ) → x j + (j : ℕ) ≠ s + k := by
  rw [getElem_partialStepWord]
  split <;> simp_all

/-- The characterisation in one-based indices: for `1 ≤ s ≤ 2N - k` the letter `ε_s`, the
letter at position `s - 1`, is `-` exactly when `s = x_j + j - 1 - k` for some `k + 1 ≤ j ≤ N`,
where `x_j = x (j - 1) + 1` are the one-based entries and `j` runs over `Fin N` as `j - 1`. This is
the formula transcribed with nothing shifted, so the zero-based prescription of
`partialStepWord` is equivalent to it by proof rather than by inspection. All three bounds are
used: `1 ≤ s` because `s - 1` truncates at `s = 0`, `s ≤ 2N - k` because a sequence that is not a
path can mark a position beyond the word, and `k + 1 ≤ j` because the subtraction `- k`
truncates below it. -/
theorem getElem?_partialStepWord_eq_U_iff_source (k : ℕ) {N : ℕ} (x : Fin N → ℕ) (s : ℕ)
    (hs : 1 ≤ s) (hs2 : s ≤ 2 * N - k) :
    (partialStepWord k x)[s - 1]? = some U ↔
      ∃ j : Fin N, k + 1 ≤ (j : ℕ) + 1 ∧ s = x j + 1 + ((j : ℕ) + 1) - 1 - k := by
  have hlen : s - 1 < (partialStepWord k x).length := by
    rw [length_partialStepWord]; omega
  rw [List.getElem?_eq_getElem hlen, Option.some_inj,
    getElem_partialStepWord_eq_U_iff k x _ hlen]
  exact ⟨fun ⟨j, hj, hj'⟩ => ⟨j, by omega, by omega⟩, fun ⟨j, hj, hj'⟩ => ⟨j, by omega, by omega⟩⟩

/-- Once the first `k` entries are `1` the range restriction `k + 1 ≤ j` is automatic: an
entry `x_j` with `j ≤ k` is `1`, so its marking position `x_j + j - 1` is `j`, one of the `k`
letters deleted and hence none of the positions of `w_k(π)`. This is the only clause of
`IsPartialDyck` the equivalence uses — monotonicity and the diagonal bound play no part in it, so
they are not assumed. -/
theorem getElem_partialStepWord_eq_U_iff_of_forall_eq_zero {k N : ℕ} {x : Fin N → ℕ}
    (hx : ∀ l : Fin N, (l : ℕ) < k → x l = 0) (s : ℕ)
    (hs : s < (partialStepWord k x).length) :
    (partialStepWord k x)[s] = U ↔ ∃ j : Fin N, x j + (j : ℕ) = s + k := by
  rw [getElem_partialStepWord_eq_U_iff]
  refine ⟨fun ⟨j, _, hj⟩ => ⟨j, hj⟩, fun ⟨j, hj⟩ => ⟨j, ?_, hj⟩⟩
  by_contra hjk
  rw [hx j (by omega)] at hj
  omega

/-- The characterisation on a partial Dyck path, in the form the recursion on the level uses, where
the level moves and the range would have to move with it. It is the dot-notation reading of
`getElem_partialStepWord_eq_U_iff_of_forall_eq_zero`, whose hypothesis is not a structure and so
cannot supply one: `HJO.Dyck.partialStepWord_eq_U_cons_partialStepWord_succ`,
`HJO.Dyck.partialStepWord_succ_eq_D_cons_partialStepWord_eastInverse` and
`HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp'` each hold an `IsPartialDyck` and each reads
the letters of the word through it. -/
theorem IsPartialDyck.getElem_partialStepWord_eq_U_iff {k N : ℕ} {x : Fin N → ℕ}
    (h : IsPartialDyck k N x) (s : ℕ) (hs : s < (partialStepWord k x).length) :
    (partialStepWord k x)[s] = U ↔ ∃ j : Fin N, x j + (j : ℕ) = s + k :=
  Dyck.getElem_partialStepWord_eq_U_iff_of_forall_eq_zero h.eq_zero_of_lt_level s hs

/-- The step word at level `k` of a sequence whose first `k` entries are minimal is the step word of
the underlying path with its first `k` letters deleted. This lemma derives the prescription stated
for `partialStepWord`: the north steps of the partial path are the `j`-th north steps of the
underlying path for `j > k`, the first `k` letters of `w(π)` are the prepended ones, at the
positions `x_j + j - 1 = j` for `j ≤ k`, and deleting them shifts every later position down by `k`.
So it is what makes `partialStepWord` the word `w_k` of the recursion rather than an independent
reading of the same combinatorics, and it is the form in which a consumer carries a fact about
`stepWord` over to `partialStepWord`. The hypothesis is the only one used and it is sharp: at
`k = N = 2` on the one-based entries `(3, 1)` the left side is `+ +` and the right side `- +`, which
is what `partialStepWord_level_restriction_example` exhibits. -/
theorem partialStepWord_eq_drop_stepWord {k N : ℕ} {x : Fin N → ℕ}
    (hx : ∀ l : Fin N, (l : ℕ) < k → x l = 0) :
    partialStepWord k x = (stepWord x).drop k := by
  refine List.ext_getElem (by simp) fun s h1 h2 => ?_
  rw [List.getElem_drop, getElem_partialStepWord, getElem_stepWord]
  refine if_congr ⟨fun ⟨j, _, hj⟩ => ⟨j, by omega⟩, fun ⟨j, hj⟩ => ⟨j, ?_, by omega⟩⟩ rfl rfl
  by_contra hjk
  rw [hx j (by omega)] at hj
  omega

/-- The word of a partial Dyck path is the word of the underlying Dyck path with its first `k`
letters, the `k` prepended north steps, deleted: the dot-notation reading of
`partialStepWord_eq_drop_stepWord`, whose hypothesis is not a structure and so cannot supply one.
This is the form `HJO.Dyck.partialStepWord_zero_left`,
`HJO.Dyck.partialStepWord_eq_U_cons_partialStepWord_succ` and
`HJO.Dyck.partialStepWord_succ_eq_D_cons_partialStepWord_eastInverse` read the word through, each
holding an `IsPartialDyck` and each comparing the word at one level with a word at another. -/
theorem IsPartialDyck.partialStepWord_eq_drop_stepWord {k N : ℕ} {x : Fin N → ℕ}
    (h : IsPartialDyck k N x) : partialStepWord k x = (stepWord x).drop k :=
  Dyck.partialStepWord_eq_drop_stepWord h.eq_zero_of_lt_level

/-- A Dyck path of length `N` read at level `k` has exactly `N - k` north steps, the paper's
`|π| = N - k`, so its step word at level `k` has exactly `N - k` letters `U`: the marking positions
`x_j + j - 1 - k` are distinct by `IsSquareDyck.strictMono_add_index` and lie among the `2N - k`
positions of the word by `IsSquareDyck.add_index_add_one_lt_two_mul`. The level enters only through
the range `k ≤ j` it selects, so the path need not be partial at that level and the vanishing of
its first `k` entries is not assumed; on an `IsPartialDyck` the statement is reached by dot
notation through `extends`. -/
theorem IsSquareDyck.count_U_partialStepWord {k N : ℕ} {x : Fin N → ℕ}
    (h : IsSquareDyck N x) : (partialStepWord k x).count U = N - k := by
  classical
  have key : ∀ (m : ℕ) (f : Fin m → DyckStep),
      (List.ofFn f).count U = #{s : Fin m | f s = U} := by
    intro m f
    have h1 : ((List.ofFn f : List DyckStep) : Multiset DyckStep)
        = (univ : Finset (Fin m)).val.map f := by
      rw [List.ofFn_eq_map]; rfl
    rw [← Multiset.coe_count, h1, Multiset.count_map]
    simp [Finset.card, Finset.filter, eq_comm]
  have hcard : #{j : Fin N | k ≤ (j : ℕ)} = N - k := by
    rw [← Nat.card_Ico k N]
    refine Finset.card_nbij (fun j => (j : ℕ)) ?_ (fun a _ b _ hab => Fin.val_injective hab) ?_
    · intro a ha
      simp only [coe_filter_univ, Set.mem_ofPred_eq] at ha
      simp [ha, a.isLt]
    · intro m hm
      simp only [coe_Ico, Set.mem_Ico] at hm
      exact ⟨⟨m, hm.2⟩, by simp [hm.1], rfl⟩
  have hlt : ∀ j : Fin N, k ≤ (j : ℕ) → x j + (j : ℕ) - k < 2 * N - k := by
    intro j hj
    have := h.add_index_add_one_lt_two_mul j
    omega
  rw [partialStepWord, key, ← hcard]
  refine (Finset.card_bij
    (fun j hj => (⟨x j + (j : ℕ) - k, hlt j (by simpa using hj)⟩ : Fin (2 * N - k))) ?_ ?_ ?_).symm
  · intro j hj
    simp only [mem_filter_univ] at hj ⊢
    have hex : ∃ i : Fin N, k ≤ (i : ℕ) ∧ x i + (i : ℕ) = x j + (j : ℕ) - k + k :=
      ⟨j, hj, by omega⟩
    simp [hex]
  · intro a ha b hb hab
    simp only [mem_filter_univ] at ha hb
    have hv : x a + (a : ℕ) - k = x b + (b : ℕ) - k := congrArg Fin.val hab
    exact h.strictMono_add_index.injective
      (show x a + (a : ℕ) = x b + (b : ℕ) by omega)
  · intro s hs
    simp only [mem_filter_univ] at hs
    by_cases hcon : ∃ j : Fin N, k ≤ (j : ℕ) ∧ x j + (j : ℕ) = (s : ℕ) + k
    · obtain ⟨j, hj, hj'⟩ := hcon
      exact ⟨j, by simpa using hj, by simp only [Fin.ext_iff]; omega⟩
    · simp [hcon] at hs

/-- A Dyck path of length `N` read at a level `k ≤ N` has exactly `N` east steps, so its step word
at level `k` has exactly `N` letters `D`: the word has `2N - k` letters and `N - k` of them are
`U`. The bound `k ≤ N` is the bound `N ≥ k` and is used, not decoration: at `k > N` the word is
shorter than `N` and the count drops. -/
theorem IsSquareDyck.count_D_partialStepWord {k N : ℕ} {x : Fin N → ℕ}
    (h : IsSquareDyck N x) (hk : k ≤ N) : (partialStepWord k x).count D = N := by
  have hsum : (partialStepWord k x).count U + (partialStepWord k x).count D = 2 * N - k := by
    rw [← length_partialStepWord k x]
    induction partialStepWord k x with
    | nil => simp
    | cons a t ih => cases a <;> simp <;> omega
  have := h.count_U_partialStepWord (k := k)
  omega

/-- The first letter of the step word at level `k` marks a north step exactly when the entry at the
position `k` is minimal, the one-based `x_{k+1} = 1`. This is the distinguished letter of `w_k(π)`:
the right-hand side is the first alternative of
`HJO.Dyck.IsSquareDyck.xor_exists_apply_eq_zero_level_pos` verbatim, and a sequence satisfying it is
a partial path at the level `k + 1` as well, whose word is `w_k(π)` with this letter deleted — which
is what `HJO.Dyck.partialStepWord_eq_U_cons_partialStepWord_succ` reads.

Neither direction asks for a path, and neither asks for `k ≤ N`: the marking condition
`x j + j = k` with `k ≤ j` forces `j = k`, so `k < N` and the nonemptiness of the word are
concluded rather than assumed, where the mirror fact about the last letter spends the diagonal
bound. -/
theorem head?_partialStepWord_eq_U_iff {k N : ℕ} {x : Fin N → ℕ} :
    (partialStepWord k x).head? = some U ↔ ∃ hk : k < N, x ⟨k, hk⟩ = 0 := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_some_iff]
  constructor
  · rintro ⟨hlen, hU⟩
    obtain ⟨j, hj, hj'⟩ := (getElem_partialStepWord_eq_U_iff k x 0 hlen).1 hU
    have hjlt := j.isLt
    have hjk : (j : ℕ) = k := by omega
    have hkN : k < N := by omega
    refine ⟨hkN, ?_⟩
    rw [show (⟨k, hkN⟩ : Fin N) = j by simp [Fin.ext_iff, hjk]]
    omega
  · rintro ⟨hk, h0⟩
    have hlen : 0 < (partialStepWord k x).length := by rw [length_partialStepWord]; omega
    exact ⟨hlen, (getElem_partialStepWord_eq_U_iff k x 0 hlen).2 ⟨⟨k, hk⟩, le_rfl, by simp [h0]⟩⟩

/-- The first letter of the step word at level `k` marks an east step exactly when the word has a
first letter at all and the entry at the position `k` is not minimal, the one-based `x_{k+1} ≥ 2`.
The first conjunct is the side condition `2N - k ≥ 1` and the second is the second
alternative of `HJO.Dyck.IsSquareDyck.xor_exists_apply_eq_zero_level_pos` less its `0 < k`, which is
a fact about the path and not about the letter: at `k = 0` the sequence `![1]` has an east step
first. So with `head?_partialStepWord_eq_U_iff` the two alternatives of the dichotomy are the two
readings of one letter, and `HJO.Dyck.partialStepWord_succ_eq_D_cons_partialStepWord_eastInverse`
reads this one. -/
theorem head?_partialStepWord_eq_D_iff {k N : ℕ} {x : Fin N → ℕ} :
    (partialStepWord k x).head? = some D ↔ k < 2 * N ∧ ∀ hk : k < N, x ⟨k, hk⟩ ≠ 0 := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_some_iff]
  constructor
  · rintro ⟨hlen, hD⟩
    have hlen' : 0 < 2 * N - k := by rw [← length_partialStepWord k x]; exact hlen
    exact ⟨by omega, fun hk h0 =>
      (getElem_partialStepWord_eq_D_iff k x 0 hlen).1 hD ⟨k, hk⟩ le_rfl (by simp [h0])⟩
  · rintro ⟨hlt, h0⟩
    have hlen : 0 < (partialStepWord k x).length := by rw [length_partialStepWord]; omega
    refine ⟨hlen, (getElem_partialStepWord_eq_D_iff k x 0 hlen).2 fun j hj hj' => ?_⟩
    have hjlt := j.isLt
    have hjk : (j : ℕ) = k := by omega
    have hkN : k < N := by omega
    refine h0 hkN ?_
    rw [show (⟨k, hkN⟩ : Fin N) = j by simp [Fin.ext_iff, hjk]]
    omega

/-- The last letter of the step word of a partial Dyck path marks an east step: the path arrives at
`(N, N)` from the west, the one-based `x_j + j - 1 ≤ 2N - 1`. This is what makes the composite
`d_{ε₁} ⋯ d_{ε_{2N-k}}` of the character recursion begin with a raising operator. -/
theorem IsSquareDyck.getElem?_partialStepWord_last {k N : ℕ} {x : Fin N → ℕ}
    (h : IsSquareDyck N x) (hk : k ≤ N) (hN : 0 < N) :
    (partialStepWord k x)[2 * N - k - 1]? = some D := by
  have hlen : 2 * N - k - 1 < (partialStepWord k x).length := by
    rw [length_partialStepWord]; omega
  rw [List.getElem?_eq_getElem hlen]
  refine congrArg some ((getElem_partialStepWord_eq_D_iff k x _ hlen).2 fun j hj hj' => ?_)
  have := h.add_index_add_one_lt_two_mul j
  omega

/-- The range restriction `k + 1 ≤ j` is not decoration: away from `𝔻_{k,N}` the
restricted and the unrestricted readings of the marking condition give different words. At
`k = N = 2` and the one-based entries `x = (3, 1)` — here `![2, 0]`, not a Dyck path, its entries
decreasing — the equation `s = x_j + j - 1 - k` is solved at `s = 1` by `j = 1`, so the
unrestricted reading would make the first letter `-`; the restriction `3 ≤ j` discards that
solution and the word is `+ +`. So a statement about `partialStepWord` off the index set `𝔻_{k,N}`
is a statement about the restricted reading, and
`getElem_partialStepWord_eq_U_iff_of_forall_eq_zero` names the exact hypothesis under which the two
readings agree.

The last clause is the same witness read against `stepWord`, and it is what makes the hypothesis of
`partialStepWord_eq_drop_stepWord` sharp rather than merely sufficient: here `w(π) = + - - +`, so
dropping its first `k = 2` letters leaves `- +`, while `w_2` of the same entries is `+ +`. The two
sides of that lemma are therefore unequal at these entries, whose first `k` are not minimal, so no
weakening of its hypothesis to a condition these entries satisfy can hold. -/
theorem partialStepWord_level_restriction_example :
    ¬IsSquareDyck 2 ![2, 0] ∧ partialStepWord 2 ![2, 0] = [D, D] ∧
      (∃ j : Fin 2, ![2, 0] j + (j : ℕ) = 0 + 2) ∧
      (stepWord ![2, 0]).drop 2 = [U, D] := by
  decide

/-- The sequence `![0, 0, 1]`, in one-based form `(1, 1, 2)`, lies in `𝔻_{2,3}`: the level-`2`
worked word below is therefore the word of an element of the index set and not of an arbitrary
sequence. -/
theorem isPartialDyck_example_two_three : IsPartialDyck 2 3 ![0, 0, 1] := by decide

/-- The step word at level `2` of the sequence `![0, 0, 1]`, in one-based form `(1, 1, 2)`, a
partial Dyck path in `𝔻_{2,3}` by `isPartialDyck_example_two_three`: east, north, east, east from
`(0, 2)` to `(3, 3)`. -/
theorem partialStepWord_example_two_three : partialStepWord 2 ![0, 0, 1] = [D, U, D, D] := by
  decide

/-- The sequence `![0, 1, 1]`, in one-based form `(1, 2, 2)`, lies in `𝔻_{1,3}`: a witness at a
second level, the level entering both the length of the word and the range of the marking
positions. -/
theorem isPartialDyck_example_one_three : IsPartialDyck 1 3 ![0, 1, 1] := by decide

/-- The step word at level `1` of the sequence `![0, 1, 1]`, in one-based form `(1, 2, 2)`, a
partial Dyck path in `𝔻_{1,3}` by `isPartialDyck_example_one_three`: east, north, north, east, east
from `(0, 1)` to `(3, 3)`. -/
theorem partialStepWord_example_one_three : partialStepWord 1 ![0, 1, 1] = [D, U, U, D, D] := by
  decide

/-- The same sequence `![0, 0, 1]` read at level `0`, where it is an ordinary Dyck path of length
`3`: `isPartialDyck_zero_left_iff` applied to the square path underlying
`isPartialDyck_example_two_three`, so the two worked words at levels `2` and `0` are words of one
and the same path. -/
theorem isPartialDyck_example_zero_three : IsPartialDyck 0 3 ![0, 0, 1] :=
  isPartialDyck_zero_left_iff.2 isPartialDyck_example_two_three.toIsSquareDyck

/-- That path's word at level `0` is longer by two letters and begins differently, so the level is
not idle: `w_k` depends on `k` and not only on the path. -/
theorem partialStepWord_example_zero_three :
    partialStepWord 0 ![0, 0, 1] = [U, U, D, U, D, D] := by
  decide

/-- The sequence `![0, 0, 0]` read at level `2`, the partial path taking its north step first, lies
in `𝔻_{2,3}` as well, by `isPartialDyck_zero`: a second element of one and the same
`𝔻_{k,N}`. -/
theorem isPartialDyck_example_two_three_zero : IsPartialDyck 2 3 (0 : Fin 3 → ℕ) :=
  isPartialDyck_zero (by omega)

/-- Its word differs from that of `partialStepWord_example_two_three`, so `w_k` separates two
partial paths of one level and one length. -/
theorem partialStepWord_example_two_three_zero :
    partialStepWord 2 (0 : Fin 3 → ℕ) = [U, D, D, D] := by
  decide

/-- The paper reads a *second* word of length `2N - k` off a Dyck path of length `N`: Proposition
4.14 takes a path **ending** in `k` east steps and writes its full word as
`(ε₁, …, ε_{2N-k}, +ᵏ)`, so that word is `w(π)` with its **last** `k` letters removed. The word
defined here removes the **first** `k`, the north steps prepended to reach `(0, k)`, because the
recursion adds steps to the beginning of the path. The two truncations have the same length and the
same alphabet and are not the same word: at `N = 3`, `k = 1` and the paper's path `(1, 1, 3)` —
here `![0, 0, 2]`, a member of `𝔻_{1,3}` — the full word is `- - + + - +`, and removing its first
letter leaves `- + + - +` while removing its last leaves `- - + + -`. So the matching length
`2N - k` is not an identification of the two readings, and a consumer of `partialStepWord` is
reading a partial path from `(0, k)`, never a path that ends in east steps. -/
theorem partialStepWord_ne_take_example :
    IsPartialDyck 1 3 ![0, 0, 2] ∧
      partialStepWord 1 ![0, 0, 2] = (stepWord ![0, 0, 2]).drop 1 ∧
      (stepWord ![0, 0, 2]).drop 1 ≠ (stepWord ![0, 0, 2]).take (2 * 3 - 1) := by
  decide

/-! ### Flipping a set of corners -/

/-- The flip `π_S` of the sequence `x` at the set `S` of cells: the sequence whose entry at a
position `k` is lowered by one when the corner cell `(x k - 1, k)` of that position lies in `S`,
and is `x k` otherwise. This is the paper's `π_S`, whose `j`-th entry is `x_j - 1` if
`(x_j - 1, j) ∈ S` and `x_j` otherwise, in the coordinates of `HJO.Dyck.corner`: both coordinates
of the paper's cell are lowered by one, so the paper's `(x_j - 1, j)` is `(x k - 1, k)` at
`k = j - 1`.

Total on every `S`, and not only on the subsets of `c(π)` the paper takes: the consumers need the
entrywise formula, and that the value is again a Dyck path for `S ⊆ c(π)` is a separate lemma. -/
@[hjo "def_cm_flip"]
def flipCorners {n : ℕ} (x : Fin n → ℕ) (S : Finset (ℕ × ℕ)) : Fin n → ℕ :=
  fun k => if (x k - 1, (k : ℕ)) ∈ S then x k - 1 else x k

/-- The entry of the flip at a position whose corner cell lies in `S`: the paper's `x_j - 1`. -/
theorem flipCorners_of_mem {n : ℕ} {x : Fin n → ℕ} {S : Finset (ℕ × ℕ)} {k : Fin n}
    (h : (x k - 1, (k : ℕ)) ∈ S) : flipCorners x S k = x k - 1 := by
  simp only [flipCorners, h, ↓reduceIte]

/-- The entry of the flip at every other position: the paper's `x_j`. -/
theorem flipCorners_of_notMem {n : ℕ} {x : Fin n → ℕ} {S : Finset (ℕ × ℕ)} {k : Fin n}
    (h : (x k - 1, (k : ℕ)) ∉ S) : flipCorners x S k = x k := by
  simp only [flipCorners, h, ↓reduceIte]

/-- Flipping nothing changes nothing: `π_∅ = π`, the base of the corner
inclusion--exclusion. -/
@[simp]
theorem flipCorners_empty {n : ℕ} (x : Fin n → ℕ) : flipCorners x ∅ = x :=
  funext fun _ => flipCorners_of_notMem (notMem_empty _)

/-- A flip never raises an entry, so it never moves a path away from the diagonal: this is what
makes `π_S` again satisfy the bound `x_j ≤ j` of `HJO.Dyck.IsSquareDyck`. -/
theorem flipCorners_le {n : ℕ} (x : Fin n → ℕ) (S : Finset (ℕ × ℕ)) (k : Fin n) :
    flipCorners x S k ≤ x k := by
  by_cases h : (x k - 1, (k : ℕ)) ∈ S
  · rw [flipCorners_of_mem h]; omega
  · rw [flipCorners_of_notMem h]

/-- A flip lowers each entry by at most one: the cell adjoined at a flipped position is the single
corner cell of that position. -/
theorem le_flipCorners_succ {n : ℕ} (x : Fin n → ℕ) (S : Finset (ℕ × ℕ)) (k : Fin n) :
    x k ≤ flipCorners x S k + 1 := by
  by_cases h : (x k - 1, (k : ℕ)) ∈ S
  · rw [flipCorners_of_mem h]; omega
  · rw [flipCorners_of_notMem h]; omega

/-- A value check at the paper's own worked path, whose coarea sequence is
`x(π) = (1, 2, 2, 2, 3, 3, 7, 7)`, reading `![0, 1, 1, 1, 2, 2, 6, 6]` here, and whose corner set is
`{(0, 1), (1, 4), (5, 6)}` by `HJO.Dyck.corner_source_example`. Flipping its first corner lowers the
second entry alone, giving in one-based form `(1, 1, 2, 2, 3, 3, 7, 7)`: the cell `(0, 1)` is
adjoined and no other entry moves, because no other position has its corner cell in the
singleton. -/
theorem flipCorners_source_example :
    flipCorners ![0, 1, 1, 1, 2, 2, 6, 6] {(0, 1)} = ![0, 0, 1, 1, 2, 2, 6, 6] := by
  decide

/-- Flipping the whole corner set of the paper's worked path lowers the entries at its three corner
positions and no others, giving in one-based form `(1, 1, 2, 2, 3, 3, 7, 7)` with the further two
turning points lowered as well. This separates `flipCorners` from a map that would lower every
entry. -/
theorem flipCorners_corner_source_example :
    flipCorners ![0, 1, 1, 1, 2, 2, 6, 6] (corner ![0, 1, 1, 1, 2, 2, 6, 6]) =
      ![0, 0, 1, 1, 1, 2, 5, 6] := by
  decide

end HJO.Dyck
