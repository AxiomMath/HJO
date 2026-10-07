/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidTrain
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring
public meta import HJO.Attr

/-! # The data of a special braid: slopes, ranks, positions and the `y`-words

Mellit attaches a *special braid* to an admissible colouring by projecting each of its intervals to
the torus and recording where it crosses the antidiagonal. This file fixes the combinatorial data
of that construction: the unimodularity of a pair of slopes, the sweep slope of a rectangle, the
rank of an entry in a tuple, special-braid data itself, the position tuple after a sequence of
elementary moves, and the words `𝗒_1, …, 𝗒_k` of the braid monoid.

Nothing here is the braid; what is here is the data it is built from, and the `nx_θ` of
`HJO.Braid.nextCrossing` is the one dynamic all of it runs on.

## Main definitions

* `HJO.Mellit.IsUnimodular`: a unimodular pair of slopes in `ℕ²`.
* `HJO.Mellit.sweepSlope`: the sweep slope `s_{a,b,N}` of the `aN × bN` rectangle.
* `HJO.Braid.entryRank`: the rank `rk_w(i)` of an entry of a tuple.
* `HJO.Braid.IsSpecialBraidData`: special-braid data of rank `k` at slope `s`.
* `HJO.Braid.moveOne`, `HJO.Braid.moveStage`: one elementary move, and the position tuple
  `w^{(r)}` after the last `r` moves of a sequence.
* `HJO.Braid.Letter`, `HJO.Braid.yWord`: the alphabet of the braid monoid and the words `𝗒_i`.

## Main results

* `HJO.Mellit.sweepSlope_eq_sub`: the sweep slope is `b/a - 1/(a(aN+1)N)`, Mellit's
  `b/a - ε`; and `HJO.Mellit.sweepSlope_one_one_one` evaluates it at `a = b = N = 1`.
* `HJO.Braid.moveStage_zero`, `HJO.Braid.moveStage_length`, `HJO.Braid.moveStage_succ`: the
  recursion `w^{(0)} = w` and `w^{(r+1)} = ` one move on `w^{(r)}`, at the prescribed index,
  together with the identification of the last stage.
* `HJO.Braid.yWord_one`, `HJO.Braid.yWord_two`, `HJO.Braid.yWord_three`: the first three `y`-words
  written out.

## Implementation notes

### Slopes and ranks

`IsUnimodular` is written `m' * n = m * n' + 1` rather than `m' * n - m * n' = 1`: the pairs are in
`ℕ²`, where subtraction truncates and the difference `-1` would read as `1`. The two say the same
thing over `ℤ` and the additive form needs no cast.

`sweepSlope` is over `ℚ`, which is where the levels used throughout live, and its denominator
`a(aN+1)N` is `a * HJO.Paths.attackWindow a N / (aN)` — that is, `attackWindow` scaled; the
identity `sweepSlope_eq_sub` is what identifies it with Mellit's `b/a - ε`. At `a = 0` or
`N = 0` the denominator vanishes and the value is `0` by the division convention of `ℚ`; no
statement reads it there, the rectangle having no column.

`entryRank` is stated for a tuple in an arbitrary linear order, not for real numbers: the rank is
`#{j : w_j ≤ w_i}` and nothing else about `ℝ` enters. The hypothesis that the entries
are pairwise distinct is not carried — it is what makes the rank a bijection onto `{1, …, k}`, which
is a lemma about `entryRank` and not part of its definition. Note `entryRank w i ≥ 1` always, since
`j = i` is counted: this is the `1`-based rank.

### Special-braid data

The parameter `θ` is carried alongside `s` with its defining equation `θ * (s + 1) = 1` as a field,
rather than being substituted as `1/(s+1)`: `HJO.Braid.nextCrossing` takes `θ`, so `θ` is what every
clause reads, and the equation `θ(s + 1) = 1` is all any clause needs of it.

The "the `α_1 + ⋯ + α_k` numbers `nx_θ^j(v_i)` are pairwise distinct" is an injectivity
statement about the index set `{(i, j) : j < α_i}`, and it is written that way: a count of a set of
values would additionally have to say that the set is the image, which is what injectivity gives.

### The move sequence

The sequence of indices is read **backwards**: `w^{(r)}` applies the moves
`i_l, i_{l-1}, …, i_{l+1-r}` in that order. So `moveStage` is a right fold over the last `r` entries
of the list, and `moveStage_succ` is the recursion at the index `i_{l-r}` it names. The
reversal is not a convention that could be dropped: `moveStage_succ` would otherwise read a
different entry of the list.

### The `y`-words

The alphabet `Letter` carries `T i` and `Tbar i` for every natural `i`, together with `y1` and `z1`,
rather than being cut down to the `F_k` on `2k` symbols. The words `𝗒_1, …, 𝗒_k` use
`Tbar 1, …, Tbar (k-1)` and `y1`, so each lies in the image of `F_k` in the larger free monoid, and
that image is a submonoid on a subset of the generators, hence `F_k` itself: truncating the
alphabet would put a bound proof on every letter of every word and change no statement. At
`k = 0` the `F_0` is trivial and there is no `𝗒_0`; `yWord 0` is the empty word, a junk
value no statement reads.

## References

Special braids from colourings: the definitions `HJO.Mellit.IsUnimodular`,
`HJO.Mellit.sweepSlope`, `HJO.Braid.entryRank`, `HJO.Braid.IsSpecialBraidData`,
`HJO.Braid.moveStage` and `HJO.Braid.yWord`, using `HJO.Braid.nextCrossing`. Transcribing A.
Mellit, *Toric braids and `(m, n)`-parking functions*, §§3.6, 4.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

/-- A pair `((m, n), (m', n'))` of slopes in `ℕ²` is *unimodular* when `m'n - mn' = 1`.

Written additively as `m' * n = m * n' + 1`, since `ℕ` subtraction truncates and the difference
`-1` would read as `1`; over `ℤ` the two are the same condition. -/
@[hjo "def_dpa_unimodular"]
def IsUnimodular (p p' : ℕ × ℕ) : Prop := p'.1 * p.2 = p.1 * p'.2 + 1

/-- Unimodularity is decidable, being an equation between naturals. -/
instance (p p' : ℕ × ℕ) : Decidable (IsUnimodular p p') := by
  unfold IsUnimodular; infer_instance

/-- `((1, 0), (0, 1))` is not unimodular but `((0, 1), (1, 0))` is: the condition is not symmetric,
the determinant changing sign. -/
theorem isUnimodular_zero_one_one_zero : IsUnimodular (0, 1) (1, 0) := by decide

theorem not_isUnimodular_one_zero_zero_one : ¬IsUnimodular (1, 0) (0, 1) := by decide

/-- `((1, 2), (2, 3))` is unimodular: `2 * 2 = 1 * 3 + 1`, the determinant of a pair of
neighbouring slopes in the Stern--Brocot tree. -/
theorem isUnimodular_one_two_two_three : IsUnimodular (1, 2) (2, 3) := by decide

/-- The sweep slope `s_{a,b,N} = (b(aN+1)N - 1) / (a(aN+1)N)` of the `aN × bN` rectangle: the slope
of the level lines of the above-diagonal rank `HJO.ParkingFunctions.abovePointRank`, and
Mellit's `b/a - ε` with `ε = 1/(a(aN+1)N)`. -/
@[hjo "def_braid_sweep_slope"]
def sweepSlope (a b N : ℕ) : ℚ :=
  ((b * (a * N + 1) * N : ℚ) - 1) / (a * (a * N + 1) * N)

/-- **The sweep slope is `b/a` lowered by `1/(a(aN+1)N)`**, which is Mellit's `s_- = b/a - ε`.
Stated for a rectangle with a column, where the denominator is nonzero. -/
theorem sweepSlope_eq_sub {a b N : ℕ} (ha : a ≠ 0) (hN : N ≠ 0) :
    sweepSlope a b N = (b : ℚ) / a - 1 / (a * (a * N + 1) * N) := by
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.2 ha
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hM : ((a : ℚ) * N + 1) ≠ 0 := by positivity
  rw [sweepSlope, eq_sub_iff_add_eq, ← add_div, sub_add_cancel,
    div_eq_div_iff (by positivity) ha']
  ring

/-- The sweep slope of the `1 × 1` rectangle is `1/2`: at `a = b = N = 1` the formula reads
`(1 · 2 · 1 - 1)/(1 · 2 · 1)`, and `b/a - ε` reads `1 - 1/2`. -/
theorem sweepSlope_one_one_one : sweepSlope 1 1 1 = 1 / 2 := by
  rw [sweepSlope]; norm_num

/-- The sweep slope of the `2 × 3` rectangle at `N = 1` is `14/6 = 7/3`, one sixth below `3/2`. -/
theorem sweepSlope_two_three_one : sweepSlope 2 3 1 = 3 / 2 - 1 / 6 := by
  rw [sweepSlope]; norm_num

end HJO.Mellit

namespace HJO.Braid

/-! ### The rank of an entry -/

/-- The rank `rk_w(i)` of the `i`-th entry of a tuple `w`: the number of indices `j` with
`w_j ≤ w_i`. It is at least `1`, the index `i` being counted, so this is the `1`-based
rank; for a tuple with pairwise distinct entries it is a bijection `Fin k → {1, …, k}`. -/
@[hjo "def_braid_rank"]
def entryRank {α : Type*} [LinearOrder α] {k : ℕ} (w : Fin k → α) (i : Fin k) : ℕ :=
  #{j | w j ≤ w i}

/-- The rank of an entry is positive: the entry is counted against itself. -/
theorem entryRank_pos {α : Type*} [LinearOrder α] {k : ℕ} (w : Fin k → α) (i : Fin k) :
    0 < entryRank w i :=
  card_pos.2 ⟨i, by simp⟩

/-- The rank of an entry is at most the length of the tuple. -/
theorem entryRank_le {α : Type*} [LinearOrder α] {k : ℕ} (w : Fin k → α) (i : Fin k) :
    entryRank w i ≤ k := by
  have h : entryRank w i ≤ #(univ : Finset (Fin k)) := card_filter_le _ _
  simpa using h

/-- **The rank reflects the order.** `rk_w(i) < rk_w(j)` exactly when `w_i < w_j`: one direction is
that `{t : w_t ≤ w_i}` is a *strict* subset of `{t : w_t ≤ w_j}` when `w_i < w_j`, the index `j`
lying in the second and not the first; the other is the same containment the other way round.

No injectivity is needed. It is what makes the rank a relabelling of a tuple by its order type, and
so it is the bridge between a statement indexed by position in an increasing listing and the same
statement indexed by anything else. -/
theorem entryRank_lt_entryRank_iff {α : Type*} [LinearOrder α] {k : ℕ} (w : Fin k → α)
    (i j : Fin k) : entryRank w i < entryRank w j ↔ w i < w j := by
  constructor
  · intro h
    by_contra hc
    have hji : w j ≤ w i := le_of_not_gt hc
    have : entryRank w j ≤ entryRank w i :=
      card_le_card (fun t ht => mem_filter.2 ⟨mem_univ t, (mem_filter.1 ht).2.trans hji⟩)
    omega
  · intro h
    refine card_lt_card ⟨fun t ht => mem_filter.2 ⟨mem_univ t, (mem_filter.1 ht).2.trans h.le⟩, ?_⟩
    intro hsub
    have hj : j ∈ ({t | w t ≤ w j} : Finset (Fin k)) := mem_filter.2 ⟨mem_univ j, le_rfl⟩
    exact absurd (mem_filter.1 (hsub hj)).2 (not_le.2 h)

/-- For a tuple with pairwise distinct entries the rank is injective, hence — the source and target
being the same finite type up to the shift by one — a bijection onto `{1, …, k}`. This is where
the hypothesis that `w` is a tuple of `k` pairwise distinct numbers does its work. -/
theorem entryRank_injective {α : Type*} [LinearOrder α] {k : ℕ} {w : Fin k → α}
    (hw : Function.Injective w) : Function.Injective (entryRank w) := by
  intro i j h
  refine hw (le_antisymm ?_ ?_)
  · exact not_lt.1 fun hc => by
      have := (entryRank_lt_entryRank_iff w j i).2 hc; omega
  · exact not_lt.1 fun hc => by
      have := (entryRank_lt_entryRank_iff w i j).2 hc; omega

/-- The ranks of the increasing tuple `(0, 1, 2)` are `1, 2, 3`: the rank is `1`-based and reads
the order and not the index. -/
theorem entryRank_value_check :
    ∀ i : Fin 3, entryRank (fun j : Fin 3 => (j : ℕ)) i = (i : ℕ) + 1 := by decide

/-- The ranks of the decreasing tuple `(2, 1, 0)` are `3, 2, 1`. -/
theorem entryRank_value_check_rev :
    ∀ i : Fin 3, entryRank (fun j : Fin 3 => 2 - (j : ℕ)) i = 3 - (i : ℕ) := by decide

/-! ### Special-braid data -/

/-- **Special-braid data of rank `k` at slope `s`**, with antidiagonal coordinate `θ`: a pair
`(v, α)` with `v ∈ (0,1)^k` and `α ∈ ℤ_{≥1}^k` such that the `α_1 + ⋯ + α_k` numbers
`nx_θ^j(v_i)`, for `1 ≤ i ≤ k` and `0 ≤ j ≤ α_i - 1`, are pairwise distinct and all different from
`θ`.

The pairwise distinctness is stated as injectivity of `(i, j) ↦ nx_θ^j(v_i)` on the index set
`{(i, j) : j < α_i}`, which is what it says. The condition `nx_θ^j(v_i) ≠ θ` makes every iterate of
`nextCrossing` appearing in the data well defined — `HJO.Braid.nextCrossing` needs its argument to
differ from `θ` — and is the admissibility of the data: the points never collide with one another
and never meet the puncture. -/
@[hjo "def_braid_data"]
structure IsSpecialBraidData (s θ : ℚ) (k : ℕ) (v : Fin k → ℚ) (α : Fin k → ℕ) : Prop where
  /-- The slope is positive. -/
  slope_pos : 0 < s
  /-- The antidiagonal coordinate satisfies `θ(s + 1) = 1`. -/
  theta_spec : θ * (s + 1) = 1
  /-- Every initial position lies in the open interval `(0, 1)`. -/
  mem_Ioo : ∀ i, v i ∈ Set.Ioo (0 : ℚ) 1
  /-- Every multiplicity is at least `1`: the `α ∈ ℤ_{≥1}^k`. -/
  one_le_mult : ∀ i, 1 ≤ α i
  /-- No iterate appearing in the data meets the puncture. -/
  ne_theta : ∀ (i : Fin k) (j : ℕ), j < α i → (nextCrossing θ)^[j] (v i) ≠ θ
  /-- The `α_1 + ⋯ + α_k` iterates appearing in the data are pairwise distinct. -/
  injective : ∀ (i i' : Fin k) (j j' : ℕ), j < α i → j' < α i' →
    (nextCrossing θ)^[j] (v i) = (nextCrossing θ)^[j'] (v i') → i = i' ∧ j = j'

/-- Special-braid data of rank `0` at any positive slope: there are no positions, so every clause is
vacuous. This is the `k ≥ 0` being no restriction. -/
theorem isSpecialBraidData_zero {s θ : ℚ} (hs : 0 < s) (hθ : θ * (s + 1) = 1) :
    IsSpecialBraidData s θ 0 (fun i => (i : Fin 0).elim0) (fun i => (i : Fin 0).elim0) where
  slope_pos := hs
  theta_spec := hθ
  mem_Ioo i := i.elim0
  one_le_mult i := i.elim0
  ne_theta i := i.elim0
  injective i := i.elim0

/-! ### The position tuple after a sequence of moves -/

/-- One elementary move on a position tuple: replace the `i`-th entry by `nx_θ` of it. -/
def moveOne (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (i : Fin k) : Fin k → ℚ :=
  Function.update w i (nextCrossing θ (w i))

@[simp]
theorem moveOne_self (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (i : Fin k) :
    moveOne θ w i i = nextCrossing θ (w i) := by
  simp [moveOne]

theorem moveOne_of_ne (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) {i j : Fin k} (h : j ≠ i) :
    moveOne θ w i j = w j := by
  simp [moveOne, Function.update_of_ne h]

/-- The position tuple after applying the moves of a list, the **last entry first**. This is the
fold the backwards reading of `(i_1, …, i_l)` amounts to. -/
def moveTuple (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (l : List (Fin k)) : Fin k → ℚ :=
  l.foldr (fun i v => moveOne θ v i) w

@[simp]
theorem moveTuple_nil (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) : moveTuple θ w [] = w := rfl

theorem moveTuple_cons (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (i : Fin k) (l : List (Fin k)) :
    moveTuple θ w (i :: l) = moveOne θ (moveTuple θ w l) i := rfl

/-- **The position tuple `w^{(r)}` after `r` moves of the sequence `(i_1, …, i_l)`**: the tuple
obtained from `w` by applying, in order, the moves at the indices `i_l, i_{l-1}, …, i_{l+1-r}`.

The sequence is read backwards: `w^{(0)} = w`, and `w^{(r)}` is obtained
from `w^{(r-1)}` by replacing its `i_{l+1-r}`-th entry with `nx_θ` of that entry. So the stage `r`
is the fold over the last `r` entries of the list, and `moveStage_succ` is exactly that
recursion. -/
@[hjo "def_braid_move_seq"]
def moveStage (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (l : List (Fin k)) (r : ℕ) : Fin k → ℚ :=
  moveTuple θ w (l.drop (l.length - r))

/-- `w^{(0)} = w`: no moves. -/
@[simp]
theorem moveStage_zero (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (l : List (Fin k)) :
    moveStage θ w l 0 = w := by
  simp [moveStage, moveTuple]

/-- `w^{(l)}` is the whole sequence applied. -/
theorem moveStage_length (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (l : List (Fin k)) :
    moveStage θ w l l.length = moveTuple θ w l := by
  simp [moveStage]

/-- **The recursion.** `w^{(r+1)}` is obtained from `w^{(r)}` by replacing its
`i_{l-r}`-th entry — the `(l - r - 1)`-st entry of the `0`-based list — with `nx_θ` of it. -/
theorem moveStage_succ (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (l : List (Fin k)) {r : ℕ}
    (hr : r < l.length) :
    moveStage θ w l (r + 1) =
      moveOne θ (moveStage θ w l r) (l[l.length - r - 1]'(by omega)) := by
  have hlt : l.length - r - 1 < l.length := by omega
  have hdrop : l.drop (l.length - (r + 1)) =
      l[l.length - r - 1]'hlt :: l.drop (l.length - r) := by
    have h1 : l.length - (r + 1) = l.length - r - 1 := by omega
    have h2 : l.length - r - 1 + 1 = l.length - r := by omega
    rw [h1, List.drop_eq_getElem_cons hlt, h2]
  rw [moveStage, moveStage, hdrop, moveTuple_cons]

/-! ### The `y`-words -/

/-- The alphabet of Mellit's braid monoid: the braid letters `T_i` and their inverses `T̄_i`,
together with the two loops `y_1` and `z_1`. The `F_k` is the free monoid on the
`2k` letters with `1 ≤ i ≤ k - 1`; here the index runs over all of `ℕ` and the bound is a fact about
which letters a given word uses. -/
inductive Letter where
  /-- The braid generator `T_i`. -/
  | T (i : ℕ) : Letter
  /-- The inverse braid generator `T̄_i`. -/
  | Tbar (i : ℕ) : Letter
  /-- The loop `y_1`. -/
  | y1 : Letter
  /-- The loop `z_1`. -/
  | z1 : Letter
  deriving DecidableEq

/-- **The `y`-words `𝗒_1, …, 𝗒_k` of the braid monoid**: `𝗒_1 = y_1` and
`𝗒_{i+1} = T̄_i 𝗒_i T̄_i`, as elements of the free monoid on `HJO.Braid.Letter`.

`yWord 0` is the empty word, a junk value: the family starts at `𝗒_1`, and `F_0` is the
trivial monoid, so there is no `𝗒_0` to be faithful to. -/
@[hjo "def_braid_yword"]
def yWord : ℕ → FreeMonoid Letter
  | 0 => 1
  | 1 => FreeMonoid.of Letter.y1
  | (i + 2) =>
    FreeMonoid.of (Letter.Tbar (i + 1)) * yWord (i + 1) * FreeMonoid.of (Letter.Tbar (i + 1))

/-- `𝗒_1 = y_1`. -/
theorem yWord_one : yWord 1 = FreeMonoid.of Letter.y1 := rfl

/-- The recursion `𝗒_{i+1} = T̄_i 𝗒_i T̄_i`, for `i ≥ 1`. -/
theorem yWord_succ (i : ℕ) :
    yWord (i + 2) =
      FreeMonoid.of (Letter.Tbar (i + 1)) * yWord (i + 1) *
        FreeMonoid.of (Letter.Tbar (i + 1)) := rfl

/-- `𝗒_2 = T̄_1 y_1 T̄_1`, written out. -/
theorem yWord_two : yWord 2 = FreeMonoid.ofList [Letter.Tbar 1, Letter.y1, Letter.Tbar 1] := rfl

/-- `𝗒_3 = T̄_2 T̄_1 y_1 T̄_1 T̄_2`, written out: the recursion wraps a new letter around both ends,
so the word is a palindrome of odd length `2i - 1`. -/
theorem yWord_three :
    yWord 3 = FreeMonoid.ofList
      [Letter.Tbar 2, Letter.Tbar 1, Letter.y1, Letter.Tbar 1, Letter.Tbar 2] := rfl

/-- `𝗒_i` has length `2i - 1`, so no letter of the alphabet is lost or repeated by accident. -/
theorem length_yWord (i : ℕ) : (yWord (i + 1)).length = 2 * i + 1 := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [yWord_succ]
    simp only [FreeMonoid.length_mul, FreeMonoid.length_of] at ih ⊢
    omega

end HJO.Braid
