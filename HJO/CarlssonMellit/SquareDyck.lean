/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.VecNotation
public meta import HJO.Attr

/-! # Square Dyck paths, partial Dyck paths, their step words and their corners

Carlsson and Mellit index a Dyck path in the `n × n` square by its *coarea sequence*
`x_1 ≤ ⋯ ≤ x_n` with `1 ≤ x_j ≤ j`, the abscissa of its `j`-th north step. This file fixes that
encoding for the whole Carlsson--Mellit layer, together with the three things read off it that the
layer's recursions need: the partial paths `𝔻_{k,n}`, whose first `k` steps are north; the step
word `w(π)`, the word in `{+, -}` whose letters are the path's steps in reading order and which
turns a path into a composite of the raising and lowering operators; and the corner set `c(π)`,
the cells above the path whose southern and eastern neighbours lie below it, over whose subsets the
inclusion--exclusion of the marked characteristic functions runs.

## Main definitions

* `HJO.Dyck.IsSquareDyck`: `x` is the coarea sequence of a Dyck path of length `n`.
* `HJO.Dyck.IsPartialDyck`: `x ∈ 𝔻_{k,n}`, a Dyck path whose first `k` entries are minimal.
* `HJO.Dyck.stepWord`: the step word `w(π) = ε₁ ⋯ ε_{2n}` of a path.
* `HJO.Dyck.corner`: the corner set `c(π)` of a path.

## Implementation notes

Both positions and entries are indexed from `0`, so Carlsson and Mellit's `x_j` for `1 ≤ j ≤ n` is
`x (j - 1) + 1` and the paper's lower bound `x_j ≥ 1` is vacuous. In these coordinates the attack
set of the path is `{(i, k) : x k ≤ i < k}` — the paper's cells shifted down by one in both
coordinates — and the corner set is `{(x k - 1, k) : x (k-1) < x k}`, so a corner is never an
attacking cell and flipping one adjoins exactly it, as the paper requires.

A corner is the cell *above* the path at a turning point, not the cell south-east of it. Naming the
cell `(x_j, j)` instead gives a coherent notion that is not the paper's and that passes every check
the layer below can state, being detectable only in the exponent of `q` that the corner
inclusion--exclusion produces. The value check `corner_source_example` pins the convention against
the paper's own worked path.

The step word emits `Mathlib`'s `DyckStep`, with `U` for the paper's `-` (a north step) and `D`
for its `+` (an east step), as a plain `List DyckStep` rather than a `DyckWord`: the consumers index
positions `r` and pair `r - 1` with `r`, which `DyckWord`'s bundled balance conditions obstruct.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 2.2. -/

@[expose] public section

namespace HJO.Dyck

open Finset List DyckStep

/-! ### Square Dyck paths -/

/-- `x` is a square Dyck path of length `n`: the coarea sequence `x_1 ≤ ⋯ ≤ x_n`, `1 ≤ x_j ≤ j`,
of a lattice path from `(0, 0)` to `(n, n)` staying weakly above the diagonal, with both its
positions and its entries indexed from `0`, so that the paper's `x_j` is `x (j - 1) + 1` and the
paper's lower bound is vacuous. Thus `x k` is the number of east steps preceding the `(k + 1)`-st
north step. -/
@[hjo "def_dyck_square"]
structure IsSquareDyck (n : ℕ) (x : Fin n → ℕ) : Prop where
  /-- The abscissas of the north steps are weakly increasing: `x_1 ≤ x_2 ≤ ⋯ ≤ x_n`. -/
  mono : Monotone x
  /-- The path stays weakly above the diagonal: the paper's `x_j ≤ j`, which on entries and
  positions indexed from `0` reads `x k ≤ k`. -/
  le_index : ∀ k : Fin n, x k ≤ (k : ℕ)

/-- `x` is a square Dyck path of length `n` exactly when it is weakly increasing and stays weakly
above the diagonal: the structure `IsSquareDyck` read as a conjunction. This is what a consumer
checking the two clauses one at a time uses, and the witness of `instDecidableIsSquareDyck`. -/
theorem isSquareDyck_iff {n : ℕ} {x : Fin n → ℕ} :
    IsSquareDyck n x ↔ Monotone x ∧ ∀ k : Fin n, x k ≤ (k : ℕ) :=
  ⟨fun h => ⟨h.mono, h.le_index⟩, fun h => ⟨h.1, h.2⟩⟩

/-- The entries of a square Dyck path of length `n` are smaller than `n`, so the paths of a fixed
length lie in `Fintype.piFinset fun _ => Finset.range n` and are finite in number. -/
theorem IsSquareDyck.apply_lt {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) (k : Fin n) :
    x k < n :=
  lt_of_le_of_lt (h.le_index k) k.isLt

/-- `x k + k`, the position in the step word of the letter marking the `(k + 1)`-st north step
and the one-based `x_j + j - 1`, is strictly increasing in `k`: the abscissas are weakly increasing
while the row index grows by one at each step. So those positions are distinct — take
`IsSquareDyck.strictMono_add_index.injective` — which, with
`IsSquareDyck.add_index_add_one_lt_two_mul` placing them among the word's `2n` positions, is what
leaves the step word of a path of length `n` with exactly `n` letters marking north steps. -/
theorem IsSquareDyck.strictMono_add_index {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) :
    StrictMono fun k : Fin n => x k + (k : ℕ) :=
  h.mono.add_strictMono Fin.val_strictMono

/-- The position `x k + k` of the letter marking the `(k + 1)`-st north step lies among the `2n`
positions of the step word and is never the last of them: this is the one-based bound
`x_j + j - 1 ≤ 2n - 1`, which on positions indexed from `0` reads `x k + k + 1 < 2n`. Sharpness is
not decoration: it says the last letter of the word marks an east step, which is what starts the
composite `d_{ε₁} ∘ ⋯ ∘ d_{ε_{2n}}` in `V₀`. -/
theorem IsSquareDyck.add_index_add_one_lt_two_mul {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x)
    (k : Fin n) : x k + (k : ℕ) + 1 < 2 * n := by
  have := h.le_index k
  have := k.isLt
  omega

/-- Being a square Dyck path is decidable: by `isSquareDyck_iff` both clauses are bounded
quantifications over the finitely many positions. -/
instance instDecidableIsSquareDyck (n : ℕ) (x : Fin n → ℕ) : Decidable (IsSquareDyck n x) :=
  decidable_of_iff _ isSquareDyck_iff.symm

/-- The square Dyck paths of a fixed length are finite in number, and computably so: by
`IsSquareDyck.apply_lt` they are a filter of `Fintype.piFinset fun _ => Finset.range n`. This does
not follow from `instDecidableIsSquareDyck`, the ambient `Fin n → ℕ` being infinite, so a consumer
summing a statistic over the paths of length `n` takes its index set from here. -/
instance instFintypeIsSquareDyck (n : ℕ) : Fintype {x : Fin n → ℕ // IsSquareDyck n x} :=
  Fintype.ofFinset ((Fintype.piFinset fun _ => Finset.range n).filter (IsSquareDyck n))
    fun x => by
      refine ⟨fun hx => (Finset.mem_filter.1 hx).2, fun hx => Finset.mem_filter.2 ⟨?_, hx⟩⟩
      exact Fintype.mem_piFinset.2 fun k => Finset.mem_range.2 (hx.apply_lt k)

/-- The path of `n` north steps followed by `n` east steps, all of whose abscissas are the
paper's `x_j = 1`: the witness that there is a path of every length, and the one path lying in
every set of partial paths `𝔻_{k,n}`. -/
theorem isSquareDyck_zero (n : ℕ) : IsSquareDyck n 0 :=
  ⟨monotone_const, fun _ => Nat.zero_le _⟩

/-- The staircase path hugging the diagonal, whose `j`-th north step has the one-based abscissa
`x_j = j`: the path with empty attack set. -/
theorem isSquareDyck_val (n : ℕ) : IsSquareDyck n Fin.val :=
  ⟨fun _ _ h => h, fun _ => le_rfl⟩

/-- The paper's own worked path, whose coarea sequence is `x(π) = (1, 2, 2, 2, 3, 3, 7, 7)`, is a
square Dyck path of length `8` in these coordinates. -/
theorem isSquareDyck_source_example : IsSquareDyck 8 ![0, 1, 1, 1, 2, 2, 6, 6] := by decide

/-- The constant sequence `(2, 2)`, in one-based form, is not a Dyck path of length `2`: the
predicate is not vacuously true. -/
theorem not_isSquareDyck_source_counterexample : ¬IsSquareDyck 2 ![1, 1] := by decide

/-- The square Dyck paths of length `n` are counted by the Catalan number `C_n`, checked here at
`n = 0, 3, 4` against `1, 5, 14`. A miscount would mean the predicate is not the paper's. -/
theorem card_isSquareDyck_zero : Fintype.card {x : Fin 0 → ℕ // IsSquareDyck 0 x} = 1 := by decide

/-- The square Dyck paths of length `3` number `C_3 = 5`. -/
theorem card_isSquareDyck_three : Fintype.card {x : Fin 3 → ℕ // IsSquareDyck 3 x} = 5 := by decide

/-- The square Dyck paths of length `4` number `C_4 = 14`. -/
theorem card_isSquareDyck_four : Fintype.card {x : Fin 4 → ℕ // IsSquareDyck 4 x} = 14 := by decide

/-! ### Partial Dyck paths -/

/-- `x` is a partial Dyck path of level `k` and length `n`, an element of the paper's `𝔻_{k,n}`:
a square Dyck path of length `n` whose first `k` entries are the paper's `x_j = 1`, which is the
image of a path from `(0, k)` to `(n, n)` under prepending `k` north steps. With entries indexed
from `0` the condition on the first `k` entries reads `x l = 0` for `l < k`. -/
@[hjo "def_cm_partial"]
structure IsPartialDyck (k n : ℕ) (x : Fin n → ℕ) : Prop extends IsSquareDyck n x where
  /-- The level is at most the length: the paper's `n ≥ k`, without which there is no path from
  `(0, k)` to `(n, n)` staying weakly above the diagonal. -/
  le_length : k ≤ n
  /-- The first `k` north steps precede every east step: the paper's `x_1 = ⋯ = x_k = 1`, which
  on entries indexed from `0` reads `x l = 0` for `l < k`. -/
  eq_zero_of_lt_level : ∀ l : Fin n, (l : ℕ) < k → x l = 0

/-- `x` is a partial Dyck path of level `k` and length `n` exactly when it is a square Dyck path,
the level is at most the length, and the entries vanish in the positions below `k`: the structure
`IsPartialDyck` read as a conjunction. This is what a consumer comparing two levels clause by
clause uses, and it is the witness of `instDecidableIsPartialDyck`. -/
theorem isPartialDyck_iff {k n : ℕ} {x : Fin n → ℕ} :
    IsPartialDyck k n x ↔ IsSquareDyck n x ∧ k ≤ n ∧ ∀ l : Fin n, (l : ℕ) < k → x l = 0 :=
  ⟨fun h => ⟨h.toIsSquareDyck, h.le_length, h.eq_zero_of_lt_level⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- A sequence is a partial Dyck path of level `k` and length `n` as soon as it is a square Dyck
path whose entries vanish in the positions below `k`, the level bound `k ≤ n` being granted as a
side condition. This is the form a consumer comparing two levels reads them in, the bound holding
at both, where `isPartialDyck_iff` would leave it behind as a conjunct at each level. -/
theorem isPartialDyck_iff_of_le {k n : ℕ} {x : Fin n → ℕ} (hk : k ≤ n) :
    IsPartialDyck k n x ↔ IsSquareDyck n x ∧ ∀ l : Fin n, (l : ℕ) < k → x l = 0 :=
  ⟨fun h => ⟨h.toIsSquareDyck, h.eq_zero_of_lt_level⟩, fun h => ⟨h.1, hk, h.2⟩⟩

/-- `𝔻_{0,n}` is the set of Dyck paths of length `n`: at level `0` the condition on the first
entries is vacuous and the bound `0 ≤ n` automatic. This is the step taken whenever a statement
about a Dyck path is fed to the recursion on partial paths. -/
theorem isPartialDyck_zero_left_iff {n : ℕ} {x : Fin n → ℕ} :
    IsPartialDyck 0 n x ↔ IsSquareDyck n x :=
  ⟨fun h => h.toIsSquareDyck,
    fun h => ⟨h, Nat.zero_le _, fun _ hl => absurd hl (Nat.not_lt_zero _)⟩⟩

/-- The path of `n` north steps followed by `n` east steps lies in `𝔻_{k,n}` for every level
`k ≤ n`: it is the image of the partial path that takes its `n - k` north steps first, and it
witnesses that no `𝔻_{k,n}` in the paper's range is empty. -/
theorem isPartialDyck_zero {k n : ℕ} (h : k ≤ n) : IsPartialDyck k n 0 :=
  ⟨isSquareDyck_zero n, h, fun _ _ => rfl⟩

/-- Being a partial Dyck path is decidable: by `isPartialDyck_iff` the two Dyck clauses are, and
the remaining two are a comparison of numerals and a bounded quantification over the positions. -/
instance instDecidableIsPartialDyck (k n : ℕ) (x : Fin n → ℕ) : Decidable (IsPartialDyck k n x) :=
  decidable_of_iff _ isPartialDyck_iff.symm

/-- The partial Dyck paths of a fixed level and length are finite in number, and computably so: by
`IsSquareDyck.apply_lt` they are a filter of `Fintype.piFinset fun _ => Finset.range n`. This does
not follow from `instDecidableIsPartialDyck`, the ambient `Fin n → ℕ` being infinite, so a
consumer summing a statistic over `𝔻_{k,n}` takes its index set from here. -/
instance instFintypeIsPartialDyck (k n : ℕ) : Fintype {x : Fin n → ℕ // IsPartialDyck k n x} :=
  Fintype.ofFinset ((Fintype.piFinset fun _ => Finset.range n).filter (IsPartialDyck k n))
    fun x => by
      refine ⟨fun hx => (Finset.mem_filter.1 hx).2, fun hx => Finset.mem_filter.2 ⟨?_, hx⟩⟩
      exact Fintype.mem_piFinset.2 fun l => Finset.mem_range.2 (hx.toIsSquareDyck.apply_lt l)

/-- `𝔻_{n,n}` has exactly one element, the path of `n` north steps followed by `n` east steps:
a path all of whose entries are minimal is the minimal path. This is the base of the raising
recursion, where the level has caught up with the length. -/
theorem isPartialDyck_self_iff {n : ℕ} {x : Fin n → ℕ} : IsPartialDyck n n x ↔ x = 0 := by
  refine ⟨fun h => funext fun l => h.eq_zero_of_lt_level l l.isLt, fun h => ?_⟩
  subst h
  exact isPartialDyck_zero le_rfl

/-! ### The step word -/

/-- The step word `w(π) = ε₁ ⋯ ε_{2n}` of the sequence `x : Fin n → ℕ`: the word of length `2n`
whose letter at position `s` is `U` — the paper's `-`, a north step — when `s = x k + k` for some
`k`, and `D` — the paper's `+`, an east step — otherwise. With entries and positions indexed
from `0`, `s = x k + k` is the one-based `r = x_j + j - 1`, so the letters marking north steps sit
at the abscissas of the north steps shifted by their row indices, and the word is in the paper's
reading order, from the bottom left end of the path to its top right end. -/
@[hjo "def_cm_word"]
def stepWord {n : ℕ} (x : Fin n → ℕ) : List DyckStep :=
  List.ofFn fun s : Fin (2 * n) => if ∃ k : Fin n, x k + (k : ℕ) = (s : ℕ) then U else D

@[simp]
theorem length_stepWord {n : ℕ} (x : Fin n → ℕ) : (stepWord x).length = 2 * n :=
  List.length_ofFn

/-- The letters of the step word, one by one: the one-based prescription for `ε_r`. -/
theorem getElem_stepWord {n : ℕ} (x : Fin n → ℕ) (s : ℕ) (hs : s < (stepWord x).length) :
    (stepWord x)[s] = if ∃ k : Fin n, x k + (k : ℕ) = s then U else D :=
  List.getElem_ofFn hs

/-- The positions of the step word carrying `U`, a north step, are exactly the one-based
`x_j + j - 1`: this is the characterising property of the word, and what a consumer cites in place
of unfolding `stepWord`. -/
theorem getElem_stepWord_eq_U_iff {n : ℕ} (x : Fin n → ℕ) (s : ℕ)
    (hs : s < (stepWord x).length) : (stepWord x)[s] = U ↔ ∃ k : Fin n, x k + (k : ℕ) = s := by
  rw [getElem_stepWord]
  split <;> simp_all

/-- Every other position of the step word carries `D`, an east step, `ε_r = +`, and
only those. -/
theorem getElem_stepWord_eq_D_iff {n : ℕ} (x : Fin n → ℕ) (s : ℕ)
    (hs : s < (stepWord x).length) : (stepWord x)[s] = D ↔ ∀ k : Fin n, x k + (k : ℕ) ≠ s := by
  rw [getElem_stepWord]
  split <;> simp_all

/-- The characterisation in one-based indices: for `1 ≤ r ≤ 2n` the letter `ε_r`, the
letter at position `r - 1`, is `-` exactly when `r = x_j + j - 1` for some `1 ≤ j ≤ n`, where
`x_j = x (j - 1) + 1` are the one-based entries and `j` runs over `Fin n` as `j - 1`. This is the
one-based formula transcribed with nothing shifted, so the zero-based prescription of `stepWord`
is equivalent to it by proof rather than by inspection. Both bounds on `r` are used: the lower one
because `r - 1` truncates at `r = 0`, the upper one because an `x` that is not a path can mark a
position beyond the word. -/
theorem getElem?_stepWord_eq_U_iff_source {n : ℕ} (x : Fin n → ℕ) (r : ℕ)
    (hr : 1 ≤ r) (hr2 : r ≤ 2 * n) :
    (stepWord x)[r - 1]? = some U ↔ ∃ j : Fin n, r = x j + 1 + ((j : ℕ) + 1) - 1 := by
  have hlen : r - 1 < (stepWord x).length := by rw [length_stepWord]; omega
  rw [List.getElem?_eq_getElem hlen, Option.some_inj, getElem_stepWord_eq_U_iff x _ hlen]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, by omega⟩, fun ⟨k, hk⟩ => ⟨k, by omega⟩⟩

/-- The number of letters of `List.ofFn f` equal to `a` is the number of positions where `f` takes
the value `a`: the bridge from the step word, which is defined by `List.ofFn`, to a count of
positions. -/
private theorem count_ofFn {α : Type*} [DecidableEq α] {m : ℕ} (f : Fin m → α) (a : α) :
    (List.ofFn f).count a = #{s : Fin m | f s = a} := by
  have hmap : ((List.ofFn f : List α) : Multiset α) = (univ : Finset (Fin m)).val.map f := by
    rw [List.ofFn_eq_map]; rfl
  rw [← Multiset.coe_count, hmap, Multiset.count_map, ← Finset.filter_val, ← Finset.card_def,
    Finset.filter_congr fun _ _ => eq_comm]

/-- A square Dyck path of length `n` has exactly `n` north steps, so its step word has exactly `n`
letters `U`: the positions `x k + k` are distinct by `IsSquareDyck.strictMono_add_index` and lie
among the `2n` positions of the word by `IsSquareDyck.add_index_add_one_lt_two_mul`. -/
theorem IsSquareDyck.count_U_stepWord {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) :
    (stepWord x).count U = n := by
  have hlt (k : Fin n) : x k + (k : ℕ) < 2 * n := by
    have := h.add_index_add_one_lt_two_mul k
    omega
  have hinj : Function.Injective fun k : Fin n => (⟨x k + (k : ℕ), hlt k⟩ : Fin (2 * n)) :=
    fun a b hab => h.strictMono_add_index.injective (by simpa [Fin.ext_iff] using hab)
  have himg : ({s : Fin (2 * n) | (if ∃ k : Fin n, x k + (k : ℕ) = (s : ℕ) then U else D) = U} :
        Finset (Fin (2 * n)))
      = univ.image fun k : Fin n => (⟨x k + (k : ℕ), hlt k⟩ : Fin (2 * n)) := by
    ext s
    simp only [mem_filter_univ, mem_image, mem_univ, true_and, Fin.ext_iff]
    split <;> simp_all
  rw [stepWord, count_ofFn, himg, Finset.card_image_of_injective _ hinj, card_univ,
    Fintype.card_fin]

/-- A word in `{U, D}` is as long as its north steps and its east steps together. -/
private theorem count_U_add_count_D (l : List DyckStep) : l.count U + l.count D = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => cases a <;> simp <;> omega

/-- A square Dyck path of length `n` has exactly `n` east steps, so its step word has exactly `n`
letters `D`: the word has `2n` letters and `n` of them are `U`. -/
theorem IsSquareDyck.count_D_stepWord {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) :
    (stepWord x).count D = n := by
  have hsum := count_U_add_count_D (stepWord x)
  rw [length_stepWord] at hsum
  have := h.count_U_stepWord
  omega

/-- The first letter of the step word of a nonempty square Dyck path marks a north step: the path
leaves `(0, 0)` upwards, the paper's `x_1 = 1`. -/
theorem IsSquareDyck.getElem?_stepWord_zero {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x)
    (hn : 0 < n) : (stepWord x)[0]? = some U := by
  have h0 : x ⟨0, hn⟩ = 0 := Nat.le_zero.1 (h.le_index ⟨0, hn⟩)
  have hlen : 0 < (stepWord x).length := by rw [length_stepWord]; omega
  rw [List.getElem?_eq_getElem hlen]
  exact congrArg some ((getElem_stepWord_eq_U_iff x 0 hlen).2 ⟨⟨0, hn⟩, by simp [h0]⟩)

/-- The last letter of the step word of a nonempty square Dyck path marks an east step: the path
arrives at `(n, n)` from the west, the one-based `x_j + j - 1 ≤ 2n - 1`. This is what starts the
composite `d_{ε₁} ⋯ d_{ε_{2n}}` of Theorem 4.4 with `d₊` on `1 ∈ V₀`. -/
theorem IsSquareDyck.getElem?_stepWord_two_mul_sub_one {n : ℕ} {x : Fin n → ℕ}
    (h : IsSquareDyck n x) (hn : 0 < n) : (stepWord x)[2 * n - 1]? = some D := by
  have hlen : 2 * n - 1 < (stepWord x).length := by rw [length_stepWord]; omega
  rw [List.getElem?_eq_getElem hlen]
  refine congrArg some ((getElem_stepWord_eq_D_iff x (2 * n - 1) hlen).2 fun k hk => ?_)
  have := h.add_index_add_one_lt_two_mul k
  omega

/-- The step word of the paper's worked path of Example 3.8, north, north, east, east, north,
east from `(0, 0)` to `(3, 3)`, whose coarea sequence is the paper's `(1, 1, 3)`: it is the
paper's own word `d₋ d₋ d₊ d₊ d₋ d₊` for that path, the one Example 4.5 evaluates. -/
theorem stepWord_source_example : stepWord ![0, 0, 2] = [U, U, D, D, U, D] := by decide

/-- The step word of the path of `n` north steps followed by `n` east steps, at `n = 2`. -/
theorem stepWord_zero_two : stepWord (0 : Fin 2 → ℕ) = [U, U, D, D] := by decide

/-- The step word of the staircase path hugging the diagonal, at `n = 2`: a different path of the
same length has a different word. -/
theorem stepWord_val_two : stepWord (Fin.val : Fin 2 → ℕ) = [U, D, U, D] := by decide

/-! ### The corners -/

/-- `k` is a corner position of the sequence `x`: the position of a north step whose abscissa is
larger than that of the north step below it, the one-based `2 ≤ j ≤ n` with `x_{j-1} < x_j` read at
`k = j - 1`. Stating the predecessor as an existential rather than as `x (k - 1) < x k` keeps the
position inside `Fin n` with no truncated subtraction and makes `0 < k` a consequence. -/
def IsCornerIndex {n : ℕ} (x : Fin n → ℕ) (k : Fin n) : Prop :=
  ∃ l : Fin n, (l : ℕ) + 1 = (k : ℕ) ∧ x l < x k

/-- Being a corner position is decidable: the existential runs over the finitely many positions. -/
instance instDecidableIsCornerIndex {n : ℕ} (x : Fin n → ℕ) (k : Fin n) :
    Decidable (IsCornerIndex x k) := by
  unfold IsCornerIndex; infer_instance

/-- A corner position is not the first one: the one-based `j ≥ 2`. -/
theorem IsCornerIndex.pos {n : ℕ} {x : Fin n → ℕ} {k : Fin n} (h : IsCornerIndex x k) :
    0 < (k : ℕ) := by
  obtain ⟨l, hl, -⟩ := h
  omega

/-- The abscissa at a corner position is positive: the one-based `x_j ≥ 2`, which is what makes
`(x_j - 1, j)` a cell and the flipped sequence still a path. -/
theorem IsCornerIndex.pos_apply {n : ℕ} {x : Fin n → ℕ} {k : Fin n} (h : IsCornerIndex x k) :
    0 < x k :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) h.choose_spec.2

/-- The corner set `c(π)` of the sequence `x`: the cells `(x_j - 1, j)` for the positions
`2 ≤ j ≤ n` with `x_{j-1} < x_j`, in coordinates indexed from `0`, so the cell at the corner
position `k` is `(x k - 1, k)` and the one-based cell is this one shifted up by one in both
coordinates.

These are the cells *above* the path whose southern and eastern neighbours lie below it: in these
coordinates the attack set of the path is `{(i, k) : x k ≤ i < k}`, so a corner cell, having
`i = x k - 1 < x k`, is never an attacking cell, and lowering the entry at its position adjoins
exactly it. Each position contributes at most one cell, so the elements of `c(π)` have distinct
second coordinates. -/
@[hjo "def_cm_corner"]
def corner {n : ℕ} (x : Fin n → ℕ) : Finset (ℕ × ℕ) :=
  (Finset.univ.filter (IsCornerIndex x)).image fun k => (x k - 1, (k : ℕ))

/-- Membership in the corner set: a cell is a corner exactly when it is `(x k - 1, k)` at a
corner position `k`. -/
@[simp]
theorem mem_corner {n : ℕ} {x : Fin n → ℕ} {c : ℕ × ℕ} :
    c ∈ corner x ↔ ∃ k : Fin n, IsCornerIndex x k ∧ c = (x k - 1, (k : ℕ)) := by
  simp only [corner, Finset.mem_image, mem_filter_univ]
  exact exists_congr fun _ => and_congr_right' eq_comm

/-- No corner of a square Dyck path is an attacking cell of it: the attack set in these
coordinates is `{(i, k) : x k ≤ i < k}`, and a corner has `i = x k - 1 < x k`.
Naming the cell `(x_j, j)` instead — which *is* an attacking cell — is the error this
statement rules out. -/
theorem fst_lt_of_mem_corner {n : ℕ} {x : Fin n → ℕ} {c : ℕ × ℕ} (hc : c ∈ corner x)
    (hlt : c.2 < n) : c.1 < x ⟨c.2, hlt⟩ := by
  obtain ⟨k, hk, rfl⟩ := mem_corner.1 hc
  rw [Fin.eta]
  exact Nat.sub_lt hk.pos_apply Nat.one_pos

/-- The corners of a sequence have distinct second coordinates, so `c(π)` has at most one cell in
each row of the square. This is what makes the flip of a subset of `c(π)` adjoin one cell per
position. -/
theorem snd_injOn_corner {n : ℕ} (x : Fin n → ℕ) :
    Set.InjOn Prod.snd (corner x : Set (ℕ × ℕ)) := by
  intro a ha b hb hab
  obtain ⟨k, -, rfl⟩ := mem_corner.1 ha
  obtain ⟨l, -, rfl⟩ := mem_corner.1 hb
  obtain rfl : k = l := Fin.ext hab
  rfl

/-- The corner set of the paper's own worked path, whose coarea sequence is
`x(π) = (1, 2, 2, 2, 3, 3, 7, 7)`. In one-based coordinates its corners are the three cells
`(1, 2)`, `(2, 5)` and `(6, 7)` — the turning points of the path at `j = 2, 5, 7` — which in the
coordinates used here, both shifted down by one, are `(0, 1)`, `(1, 4)` and `(5, 6)`. This is the
value check that pins the convention: naming the cell south-east of the turning point instead would
give `{(1, 1), (2, 4), (6, 6)}`. -/
theorem corner_source_example :
    corner ![0, 1, 1, 1, 2, 2, 6, 6] = {(0, 1), (1, 4), (5, 6)} := by decide

/-- The staircase path hugging the diagonal turns at every step, so every position after the first
is a corner of it. At `n = 3` its corner set is `{(0, 1), (1, 2)}`. -/
theorem corner_val_three : corner (Fin.val : Fin 3 → ℕ) = {(0, 1), (1, 2)} := by decide

/-- The path of `n` north steps followed by `n` east steps never turns, so it has no corners. -/
@[simp]
theorem corner_zero {n : ℕ} : corner (0 : Fin n → ℕ) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
  obtain ⟨k, hk, rfl⟩ := mem_corner.1 hc
  exact absurd hk.pos_apply (by simp)

end HJO.Dyck
