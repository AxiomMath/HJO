/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Defs
public import HJO.Paths.Primitive
public import HJO.Series.GapPoset

/-! # Blocks of a return path

A path returning to the diagonal after every one of its `N` blocks is the concatenation of `N`
single-block below-diagonal paths, and a single block is the same thing as an order filter of the
gap set. This file builds both correspondences, translates the arm-leg hook condition on a cell
into an interval test on the ranks `bx - ay` of its two boundary steps, splits the hook count of a
concatenation into the blocks' own hook counts plus one cross-block count per ordered pair of
blocks, and evaluates the cross-block count of two empty-filter blocks as `d - 1`, so that a
concatenation of empty-filter blocks has exactly `κ_N` hooks.

It then computes the cross-block count of two arbitrary primitive blocks. The boundary ranks of the
block of a filter are the empty-filter ranks corrected by one telescoping term per cell, which
splits the count into the baseline `d - 1`, a constant detecting the Frobenius gap in the earlier
filter, and a bilinear kernel term. Polarising the quadratic form of the gap set identifies the
symmetric half of that kernel with the cross terms of the form at the summed indicator vector, so
that, taking Huang's rank-one evaluation as an input, the hook count of a concatenation is `κ_N`
plus a weight attached to the word of filters. Finally the generating function over return paths is
reindexed as a generating function over words of filters.
-/

@[expose] public section

open Finset NumericalSemigroup

namespace HJO.ReturnPath

/-! ### Heights -/

/-- A height of a candidate `(aN, bN)`-path never exceeds `bN`. -/
theorem ht_le {a b N : ℕ} (y : Paths.Heights a b N) (r : ℕ) : Paths.ht y r ≤ b * N := by
  rw [Paths.ht]
  split
  · exact Nat.lt_succ_iff.mp (y _).2
  · exact le_rfl

/-- Below the right endpoint the height function reads off the entry of the height vector. -/
theorem ht_coe {a b N : ℕ} (y : Paths.Heights a b N) (r : Fin (a * N + 1)) :
    Paths.ht y (r : ℕ) = (y r : ℕ) := by
  rw [Paths.ht]
  split
  · rfl
  · next h => exact absurd r.2 h

/-- Along a below-diagonal path the height is monotone up to the right endpoint. -/
theorem ht_mono {a b N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    {r r' : ℕ} (hle : r ≤ r') (hr' : r' ≤ a * N) : Paths.ht y r ≤ Paths.ht y r' := by
  induction r' with
  | zero => rw [Nat.le_zero.mp hle]
  | succ n ih =>
    rcases Nat.lt_or_ge r (n + 1) with h | h
    · exact (ih (by omega) (by omega)).trans (hy.2.2.1 n (by omega))
    · rw [show r = n + 1 by omega]

/-! ### Heights of a concatenation -/

/-- The height at `r` of the concatenation of `N` single-block paths: the `r / a`-th block
contributes its own height at `r % a` on top of the `b * (r / a)` already climbed. -/
def concatHeight {a b N : ℕ} (ys : Fin N → Paths.Heights a b 1) (r : ℕ) : ℕ :=
  if h : r / a < N then b * (r / a) + Paths.ht (ys ⟨r / a, h⟩) (r % a) else b * N

/-- A concatenated height never exceeds `bN`. -/
theorem concatHeight_le {a b N : ℕ} (ys : Fin N → Paths.Heights a b 1) (r : ℕ) :
    concatHeight ys r ≤ b * N := by
  rw [concatHeight]
  split
  · next h =>
    have h1 := ht_le (ys ⟨r / a, h⟩) (r % a)
    have h2 : b * (r / a + 1) ≤ b * N := Nat.mul_le_mul le_rfl h
    have h3 : b * (r / a + 1) = b * (r / a) + b * 1 := by ring
    linarith
  · exact le_rfl

/-- The concatenation of `N` single-block paths, as a candidate `(aN, bN)`-path. -/
def concat {a b N : ℕ} (ys : Fin N → Paths.Heights a b 1) : Paths.Heights a b N :=
  fun r => ⟨concatHeight ys r, Nat.lt_succ_of_le (concatHeight_le ys r)⟩

/-- The heights of a concatenation are given by `concatHeight`, at every index. -/
theorem ht_concat {a b N : ℕ} (ha : 0 < a) (ys : Fin N → Paths.Heights a b 1) (r : ℕ) :
    Paths.ht (concat ys) r = concatHeight ys r := by
  rw [Paths.ht]
  split
  · rfl
  · next h =>
    rw [concatHeight]
    split
    · next hlt =>
      refine absurd (show r < a * N + 1 from ?_) h
      have := (Nat.div_lt_iff_lt_mul ha).mp hlt
      rw [Nat.mul_comm] at this
      omega
    · rfl

/-- The height of a concatenation at a point of the `k`-th block, given the block index and the
offset inside the block. -/
theorem ht_concat_eq {a b N : ℕ} (ha : 0 < a) (ys : Fin N → Paths.Heights a b 1) {r k s : ℕ}
    (hk : k < N) (hdiv : r / a = k) (hmod : r % a = s) :
    Paths.ht (concat ys) r = b * k + Paths.ht (ys ⟨k, hk⟩) s := by
  rw [ht_concat ha, concatHeight]
  simp only [hdiv, hmod]
  split
  · rfl
  · next h => exact absurd hk h

/-- Inside the `k`-th block the concatenation climbs `b * k` and then follows the block. -/
theorem ht_concat_add {a b N : ℕ} (ha : 0 < a) (ys : Fin N → Paths.Heights a b 1)
    {k : ℕ} (hk : k < N) {s : ℕ} (hs : s < a) :
    Paths.ht (concat ys) (a * k + s) = b * k + Paths.ht (ys ⟨k, hk⟩) s :=
  ht_concat_eq ha ys hk (by rw [Nat.mul_add_div ha, Nat.div_eq_of_lt hs, Nat.add_zero])
    (by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs])

/-- A concatenation of blocks that start at height `0` returns to the diagonal at every block
boundary. -/
theorem ht_concat_mul {a b N : ℕ} (ha : 0 < a) (ys : Fin N → Paths.Heights a b 1)
    (h0 : ∀ k : Fin N, Paths.ht (ys k) 0 = 0) {k : ℕ} (hk : k ≤ N) :
    Paths.ht (concat ys) (a * k) = b * k := by
  rcases Nat.lt_or_ge k N with h | h
  · rw [show a * k = a * k + 0 from rfl, ht_concat_add ha ys h ha, h0 ⟨k, h⟩, Nat.add_zero]
  · have hkN : k = N := by omega
    subst hkN
    rw [ht_concat ha, concatHeight]
    split
    · next hlt => exact absurd (Nat.mul_div_cancel_left k ha ▸ hlt) (by omega)
    · rfl

/-! ### The block decomposition -/

/-- The concatenation of below-diagonal single-block paths is a return path. -/
theorem isReturnPath_concat {a b N : ℕ} (ha : 0 < a) (ys : Fin N → Paths.Heights a b 1)
    (hys : ∀ k : Fin N, Paths.IsBelowDiagonal (ys k)) : Paths.IsReturnPath (concat ys) := by
  have h0 : ∀ k : Fin N, Paths.ht (ys k) 0 = 0 := fun k => (hys k).1
  have hend : ∀ k : Fin N, Paths.ht (ys k) a = b := fun k => by
    have := (hys k).2.1
    rwa [Nat.mul_one, Nat.mul_one] at this
  have hstep : ∀ (k : Fin N) (s : ℕ), s < a → Paths.ht (ys k) s ≤ Paths.ht (ys k) (s + 1) :=
    fun k s hs => (hys k).2.2.1 s (by rw [Nat.mul_one]; exact hs)
  have hdiag : ∀ (k : Fin N) (s : ℕ), s ≤ a → a * Paths.ht (ys k) s ≤ b * s :=
    fun k s hs => (hys k).2.2.2 s (by rw [Nat.mul_one]; exact hs)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun k hk => ht_concat_mul ha ys h0 hk⟩
  · simpa using ht_concat_mul ha ys h0 (Nat.zero_le N)
  · exact ht_concat_mul ha ys h0 le_rfl
  · intro r hr
    have hk : r / a < N := (Nat.div_lt_iff_lt_mul ha).mpr (by rw [Nat.mul_comm]; omega)
    have hs : r % a < a := Nat.mod_lt _ ha
    have hr' : a * (r / a) + r % a = r := Nat.div_add_mod r a
    have h1 : Paths.ht (concat ys) r = b * (r / a) + Paths.ht (ys ⟨r / a, hk⟩) (r % a) :=
      ht_concat_eq ha ys hk rfl rfl
    rcases Nat.lt_or_ge (r % a + 1) a with h | h
    · have h2 : Paths.ht (concat ys) (r + 1)
          = b * (r / a) + Paths.ht (ys ⟨r / a, hk⟩) (r % a + 1) :=
        ht_concat_eq ha ys hk
          (by rw [show r + 1 = a * (r / a) + (r % a + 1) by omega, Nat.mul_add_div ha,
            Nat.div_eq_of_lt h, Nat.add_zero])
          (by rw [show r + 1 = a * (r / a) + (r % a + 1) by omega, Nat.mul_add_mod,
            Nat.mod_eq_of_lt h])
      have := hstep ⟨r / a, hk⟩ (r % a) hs
      omega
    · have hsa : r % a + 1 = a := by omega
      have h2 : Paths.ht (concat ys) (r + 1) = b * (r / a + 1) := by
        rw [show r + 1 = a * (r / a + 1) by rw [Nat.mul_add, Nat.mul_one]; omega]
        exact ht_concat_mul ha ys h0 (by omega)
      have h3 := hstep ⟨r / a, hk⟩ (r % a) hs
      have h4 : Paths.ht (ys ⟨r / a, hk⟩) (r % a + 1) = b := by rw [hsa]; exact hend _
      have h5 : b * (r / a + 1) = b * (r / a) + b := by ring
      omega
  · intro r hr
    rcases Nat.lt_or_ge (r / a) N with hk | hk
    · have hs : r % a < a := Nat.mod_lt _ ha
      have hr' : a * (r / a) + r % a = r := Nat.div_add_mod r a
      have h1 : Paths.ht (concat ys) r = b * (r / a) + Paths.ht (ys ⟨r / a, hk⟩) (r % a) :=
        ht_concat_eq ha ys hk rfl rfl
      have h2 := hdiag ⟨r / a, hk⟩ (r % a) hs.le
      rw [h1]
      have h4 : b * (a * (r / a) + r % a) = b * a * (r / a) + b * (r % a) := by ring
      rw [hr'] at h4
      have h5 : a * (b * (r / a) + Paths.ht (ys ⟨r / a, hk⟩) (r % a))
          = b * a * (r / a) + a * Paths.ht (ys ⟨r / a, hk⟩) (r % a) := by ring
      omega
    · have hle : a * N ≤ a * (r / a) := Nat.mul_le_mul le_rfl hk
      have hr' : a * (r / a) + r % a = r := Nat.div_add_mod r a
      have hrN : r = a * N := by omega
      subst hrN
      rw [ht_concat_mul ha ys h0 le_rfl]
      exact le_of_eq (by ring)

/-- The height at offset `s` of the `k`-th block of a candidate `(aN, bN)`-path: the height of
the path shifted down by `b * k`, capped at `b`, the cap being inactive on a return path. -/
def blockHeight {a b N : ℕ} (y : Paths.Heights a b N) (k s : ℕ) : ℕ :=
  min (Paths.ht y (a * k + s) - b * k) (b * 1)

/-- The `k`-th block of a candidate `(aN, bN)`-path, as a candidate `(a, b)`-path. -/
def block {a b N : ℕ} (y : Paths.Heights a b N) (k : Fin N) : Paths.Heights a b 1 :=
  fun s => ⟨blockHeight y k s, by rw [blockHeight]; omega⟩

/-- The heights of a block are given by `blockHeight`, up to its right endpoint. -/
theorem ht_block_eq {a b N : ℕ} (y : Paths.Heights a b N) (k : Fin N) {s : ℕ} (hs : s ≤ a) :
    Paths.ht (block y k) s = blockHeight y k s := by
  rw [Paths.ht]
  split
  · rfl
  · next h => exact absurd (show s < a * 1 + 1 by rw [Nat.mul_one]; omega) h

/-- On a return path the `k`-th block is the stretch of heights over `[ak, ak + a]`, shifted down
by `bk`. -/
theorem ht_block {a b N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsReturnPath y) (k : Fin N)
    {s : ℕ} (hs : s ≤ a) : Paths.ht (block y k) s = Paths.ht y (a * k + s) - b * k := by
  have hka : a * (k : ℕ) + a ≤ a * N := by
    have h : a * ((k : ℕ) + 1) ≤ a * N := Nat.mul_le_mul (le_refl a) (by omega)
    rw [Nat.mul_add, Nat.mul_one] at h
    exact h
  have hup : Paths.ht y (a * k + s) ≤ b * ((k : ℕ) + 1) := by
    have h1 : Paths.ht y (a * ((k : ℕ) + 1)) = b * ((k : ℕ) + 1) := hy.2 _ k.2
    have h2 : a * (k : ℕ) + s ≤ a * ((k : ℕ) + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    have := ht_mono hy.1 h2 (by rw [Nat.mul_add, Nat.mul_one]; omega)
    omega
  have hexp : b * ((k : ℕ) + 1) = b * (k : ℕ) + b * 1 := by ring
  rw [ht_block_eq y k hs, blockHeight]
  omega

/-- Every block of a return path is a below-diagonal single-block path. -/
theorem isBelowDiagonal_block {a b N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsReturnPath y)
    (k : Fin N) : Paths.IsBelowDiagonal (block y k) := by
  have hka : a * (k : ℕ) + a ≤ a * N := by
    have h : a * ((k : ℕ) + 1) ≤ a * N := Nat.mul_le_mul (le_refl a) (by omega)
    rw [Nat.mul_add, Nat.mul_one] at h
    exact h
  have hbase : Paths.ht y (a * k) = b * k := hy.2 _ (by omega)
  have hnext : Paths.ht y (a * (k : ℕ) + a) = b * (k : ℕ) + b := by
    have := hy.2 ((k : ℕ) + 1) k.2
    rw [Nat.mul_add, Nat.mul_one] at this
    rw [this, Nat.mul_add, Nat.mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht_block hy k (Nat.zero_le a), Nat.add_zero, hbase, Nat.sub_self]
  · rw [Nat.mul_one, ht_block hy k le_rfl, hnext, Nat.mul_one]
    omega
  · intro s hs
    rw [Nat.mul_one] at hs
    rw [ht_block hy k hs.le, ht_block hy k (by omega)]
    have := ht_mono hy.1 (show a * (k : ℕ) + s ≤ a * (k : ℕ) + (s + 1) by omega) (by omega)
    omega
  · intro s hs
    rw [Nat.mul_one] at hs
    rw [ht_block hy k hs]
    have hlow : b * (k : ℕ) ≤ Paths.ht y (a * k + s) := by
      have := ht_mono hy.1 (show a * (k : ℕ) ≤ a * (k : ℕ) + s by omega) (by omega)
      omega
    have hd := hy.1.2.2.2 (a * (k : ℕ) + s) (by omega)
    have h1 : a * (Paths.ht y (a * k + s) - b * (k : ℕ))
        = a * Paths.ht y (a * k + s) - a * (b * (k : ℕ)) := by rw [Nat.mul_sub]
    have h2 : b * (a * (k : ℕ) + s) = a * (b * (k : ℕ)) + b * s := by ring
    omega

/-- A return path is the concatenation of its blocks. -/
theorem concat_block {a b N : ℕ} (ha : 0 < a) {y : Paths.Heights a b N}
    (hy : Paths.IsReturnPath y) : concat (block y) = y := by
  have key : ∀ r : ℕ, r ≤ a * N → Paths.ht (concat (block y)) r = Paths.ht y r := by
    intro r hr
    have hr' : a * (r / a) + r % a = r := Nat.div_add_mod r a
    rcases Nat.lt_or_ge (r / a) N with hk | hk
    · have hs : r % a < a := Nat.mod_lt _ ha
      have h1 : Paths.ht (concat (block y)) r
          = b * (r / a) + Paths.ht (block y ⟨r / a, hk⟩) (r % a) :=
        ht_concat_eq ha _ hk rfl rfl
      have h2 : Paths.ht (block y ⟨r / a, hk⟩) (r % a) = Paths.ht y r - b * (r / a) := by
        rw [ht_block hy ⟨r / a, hk⟩ hs.le]
        exact congrArg (fun t => Paths.ht y t - b * (r / a)) hr'
      have h3 : b * (r / a) ≤ Paths.ht y r := by
        have := ht_mono hy.1 (show a * (r / a) ≤ r by omega) hr
        rw [hy.2 (r / a) (by omega)] at this
        exact this
      omega
    · have hle : a * N ≤ a * (r / a) := Nat.mul_le_mul le_rfl hk
      have hrN : r = a * N := by omega
      subst hrN
      rw [hy.1.2.1]
      exact ht_concat_mul ha _ (fun k => (isBelowDiagonal_block hy k).1) le_rfl
  funext r
  exact Fin.ext ((ht_coe _ r).symm.trans ((key r (by omega)).trans (ht_coe y r)))

/-- The blocks of a concatenation of below-diagonal single-block paths are the original
blocks. -/
theorem block_concat {a b N : ℕ} (ha : 0 < a) {ys : Fin N → Paths.Heights a b 1}
    (hys : ∀ k : Fin N, Paths.IsBelowDiagonal (ys k)) : block (concat ys) = ys := by
  have hret := isReturnPath_concat ha ys hys
  funext k s
  have hs : (s : ℕ) ≤ a := by have := s.2; omega
  have hsucc : a * ((k : ℕ) + 1) = a * (k : ℕ) + a := by ring
  refine Fin.ext ?_
  rw [← ht_coe (block (concat ys) k) s, ← ht_coe (ys k) s, ht_block hret k hs]
  rcases Nat.lt_or_ge (s : ℕ) a with h | h
  · rw [ht_concat_add ha ys k.2 h]
    have heta : Paths.ht (ys ⟨(k : ℕ), k.2⟩) (s : ℕ) = Paths.ht (ys k) (s : ℕ) := rfl
    omega
  · have hsa : (s : ℕ) = a := by omega
    have hend : Paths.ht (ys k) (s : ℕ) = b := by
      have := (hys k).2.1
      rw [Nat.mul_one, Nat.mul_one] at this
      rw [hsa, this]
    have h2 : Paths.ht (concat ys) (a * (k : ℕ) + (s : ℕ)) = b * ((k : ℕ) + 1) := by
      rw [show a * (k : ℕ) + (s : ℕ) = a * ((k : ℕ) + 1) from by rw [hsucc, hsa]]
      exact ht_concat_mul ha ys (fun j => (hys j).1) k.2
    have h3 : b * ((k : ℕ) + 1) = b * (k : ℕ) + b := by ring
    rw [h2, hend]
    omega

/-- Unique factorisation of return paths: a path returning to the diagonal after each of its `N`
blocks is the same thing as an `N`-tuple of below-diagonal single-block paths. -/
def returnPathEquiv {a b N : ℕ} (ha : 0 < a) :
    {y : Paths.Heights a b N // Paths.IsReturnPath y} ≃
      (Fin N → {z : Paths.Heights a b 1 // Paths.IsBelowDiagonal z}) where
  toFun y k := ⟨block y.1 k, isBelowDiagonal_block y.2 k⟩
  invFun ys := ⟨concat fun k => (ys k).1, isReturnPath_concat ha _ fun k => (ys k).2⟩
  left_inv y := Subtype.ext (concat_block ha y.2)
  right_inv ys := funext fun k => Subtype.ext (congrFun (block_concat ha fun j => (ys j).2) k)

/-! ### Ranks of the boundary steps of a cell -/

/-- The rank `bx - ay` of the lattice point starting the east step in column `r`. -/
def eastRank {a b N : ℕ} (y : Paths.Heights a b N) (r : ℕ) : ℤ := b * r - a * Paths.ht y r

/-- The rank `bx - ay` of the lattice point ending the north step in row `i`. -/
def northRank {a b N : ℕ} (y : Paths.Heights a b N) (i : ℕ) : ℤ :=
  b * Paths.firstReach y i - a * i

/-- If a predicate holds at some member of `List.range n`, the search finds a member no later. -/
theorem find?_range_le {n : ℕ} {p : ℕ → Bool} {r : ℕ} (hr : r < n) (hp : p r) :
    ∃ r' ≤ r, (List.range n).find? p = some r' := by
  rcases h : (List.range n).find? p with _ | r'
  · rw [List.find?_eq_none] at h
    exact absurd hp (h r (List.mem_range.mpr hr))
  · refine ⟨r', ?_, rfl⟩
    rw [List.find?_eq_some_iff_getElem] at h
    obtain ⟨-, j, hj, hjeq, hmin⟩ := h
    rw [List.getElem_range] at hjeq
    subst hjeq
    by_contra hcon
    have hlt := hmin r (by omega)
    rw [List.getElem_range] at hlt
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hlt
    exact absurd hp (by simp [hlt])

/-- The search on `List.range n` finds the least member satisfying the predicate. -/
theorem find?_range_eq_some {n : ℕ} {p : ℕ → Bool} {j : ℕ} (hj : j < n) (hp : p j)
    (hmin : ∀ j' < j, ¬ p j') : (List.range n).find? p = some j := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨hp, j, by simpa using hj, by simp, fun j' hj' => ?_⟩
  simpa using hmin j' hj'

/-- A row reached by column `r` is first reached no later than `r`. -/
theorem firstReach_le {a b N : ℕ} (y : Paths.Heights a b N) {i r : ℕ} (hr : r ≤ a * N)
    (hi : i ≤ Paths.ht y r) : Paths.firstReach y i ≤ r := by
  obtain ⟨r', hr'r, hr'⟩ := find?_range_le (n := a * N + 1) (r := r)
    (p := fun r' => i ≤ Paths.ht y r') (by omega) (by simpa using hi)
  rw [Paths.firstReach, hr', Option.getD_some]
  exact hr'r

/-- The first column reaching row `i` is `j`, given that `j` reaches it and no earlier column
does. -/
theorem firstReach_eq {a b N : ℕ} (y : Paths.Heights a b N) {i j : ℕ} (hj : j ≤ a * N)
    (hij : i ≤ Paths.ht y j) (hmin : ∀ j' < j, ¬ i ≤ Paths.ht y j') :
    Paths.firstReach y i = j := by
  have hfind : (List.range (a * N + 1)).find? (fun j' => i ≤ Paths.ht y j') = some j :=
    find?_range_eq_some (n := a * N + 1) (j := j) (by omega) (by simpa using hij)
      (by simpa using hmin)
  rw [Paths.firstReach, hfind, Option.getD_some]

/-- The hook condition on an arm and a leg is an interval test on `b⋅arm - a⋅leg`. -/
theorem hook_iff_interval (a b arm leg : ℕ) :
    (b * arm ≤ a * (leg + 1) ∧ a * leg < b * (arm + 1)) ↔
      (-(b : ℤ) < (b : ℤ) * arm - (a : ℤ) * leg ∧ (b : ℤ) * arm - (a : ℤ) * leg ≤ (a : ℤ)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (b : ℤ) * arm ≤ (a : ℤ) * ((leg : ℤ) + 1) := by exact_mod_cast h1
    have h2' : (a : ℤ) * leg < (b : ℤ) * ((arm : ℤ) + 1) := by exact_mod_cast h2
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have : (b : ℤ) * arm ≤ (a : ℤ) * ((leg : ℤ) + 1) := by linarith
      exact_mod_cast this
    · have : (a : ℤ) * leg < (b : ℤ) * ((arm : ℤ) + 1) := by linarith
      exact_mod_cast this

/-- The difference of the two boundary ranks of a cell is `b⋅arm - a⋅leg`. -/
theorem eastRank_sub_northRank {a b N : ℕ} (y : Paths.Heights a b N) {r i : ℕ}
    (hA : Paths.firstReach y i ≤ r) (hi : i ≤ Paths.ht y r) :
    eastRank y r - northRank y i = (b : ℤ) * Paths.arm y r i - (a : ℤ) * Paths.leg y r i := by
  rw [eastRank, northRank, Paths.arm, Paths.leg, Nat.cast_sub hA, Nat.cast_sub hi]
  ring

/-- The hook condition on a cell is the interval test `-b < σ - ρ ≤ a` on the rank `ρ` ending its
north step and the rank `σ` starting its east step. -/
theorem hook_iff_rank {a b N : ℕ} (y : Paths.Heights a b N) {r i : ℕ}
    (hA : Paths.firstReach y i ≤ r) (hi : i ≤ Paths.ht y r) :
    (b * Paths.arm y r i ≤ a * (Paths.leg y r i + 1) ∧
        a * Paths.leg y r i < b * (Paths.arm y r i + 1)) ↔
      (-(b : ℤ) < eastRank y r - northRank y i ∧ eastRank y r - northRank y i ≤ (a : ℤ)) := by
  rw [hook_iff_interval, eastRank_sub_northRank y hA hi]

/-- The hook count as a count of cells passing the rank interval test. -/
theorem hookCount_eq_card_rank {a b N : ℕ} (y : Paths.Heights a b N) :
    Paths.hookCount y = #{p ∈ Ico 1 (a * N) ×ˢ Icc 1 (b * N) | p.2 ≤ Paths.ht y p.1 ∧
      -(b : ℤ) < eastRank y p.1 - northRank y p.2 ∧
        eastRank y p.1 - northRank y p.2 ≤ (a : ℤ)} := by
  refine congrArg card (filter_congr fun p hp => ?_)
  simp only [mem_product, mem_Ico, mem_Icc] at hp
  exact and_congr_right fun hi => hook_iff_rank y (firstReach_le y (by omega) hi) hi

/-- The cross-block hook count of an earlier block `z` and a later block `w`: the pairs made of a
north step of `z` and an east step of `w` that pass the rank interval test. -/
def crossCount {a b : ℕ} (z w : Paths.Heights a b 1) : ℕ :=
  #{p ∈ Icc 1 b ×ˢ range a | -(b : ℤ) < eastRank w p.2 - northRank z p.1 ∧
    eastRank w p.2 - northRank z p.1 ≤ (a : ℤ)}

/-! ### The lattice count behind the baseline -/

/-- With `a` and `b` coprime, exactly `a + b - 1` of the `ab` pairs `(i, r)` with `1 ≤ i ≤ b` and
`r < a` pass the interval test on `a i - b (a - r)`: the map to that value is injective with image
the interval `(-b, a]` minus its top point. -/
theorem card_rank_pairs (a b : ℕ) (hco : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    #{p ∈ Icc 1 b ×ˢ range a | -(b : ℤ) < (a : ℤ) * p.1 - (b : ℤ) * ((a : ℤ) - p.2) ∧
      (a : ℤ) * p.1 - (b : ℤ) * ((a : ℤ) - p.2) ≤ (a : ℤ)} = a + b - 1 := by
  have ha0 : (0 : ℤ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℤ) < b := by exact_mod_cast hb
  have hcop : IsCoprime (b : ℤ) (a : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using hco.symm
  have hdvd : ∀ x : ℤ, (b : ℤ) ∣ (a : ℤ) * x → (b : ℤ) ∣ x := fun _ h => hcop.dvd_of_dvd_mul_left h
  have key : #((Finset.Ioc (-(b : ℤ)) (a : ℤ)).erase (a : ℤ)) = a + b - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_Ioc.mpr ⟨by omega, le_rfl⟩), Int.card_Ioc,
      show (a : ℤ) - -(b : ℤ) = ((a + b : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
  rw [← key]
  refine Finset.card_bij (fun p _ => (a : ℤ) * p.1 - (b : ℤ) * ((a : ℤ) - p.2)) ?_ ?_ ?_
  · rintro ⟨i, r⟩ hp
    simp only [mem_filter, mem_product, mem_Icc, mem_range] at hp
    obtain ⟨⟨⟨hi1, hib⟩, hr⟩, hlow, hhigh⟩ := hp
    have hi1' : (1 : ℤ) ≤ i := by exact_mod_cast hi1
    have hib' : (i : ℤ) ≤ b := by exact_mod_cast hib
    have hr' : (r : ℤ) < a := by exact_mod_cast hr
    refine Finset.mem_erase.mpr ⟨fun heq => ?_, Finset.mem_Ioc.mpr ⟨hlow, hhigh⟩⟩
    have h1 : (b : ℤ) ∣ (a : ℤ) * ((i : ℤ) - 1) := ⟨(a : ℤ) - r, by linarith⟩
    have h2 : (i : ℤ) - 1 = 0 :=
      Int.eq_zero_of_abs_lt_dvd (hdvd _ h1) (by rw [abs_lt]; constructor <;> linarith)
    have h3 : (b : ℤ) * ((a : ℤ) - r) = 0 := by
      have : (i : ℤ) = 1 := by linarith
      rw [this] at heq
      linarith
    have h4 : (a : ℤ) - r = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · omega
      · exact h
    linarith
  · rintro ⟨i₁, r₁⟩ hp₁ ⟨i₂, r₂⟩ hp₂ heq
    simp only [mem_filter, mem_product, mem_Icc, mem_range] at hp₁ hp₂
    have hi₁ : (1 : ℤ) ≤ i₁ ∧ (i₁ : ℤ) ≤ b := ⟨by exact_mod_cast hp₁.1.1.1, by
      exact_mod_cast hp₁.1.1.2⟩
    have hi₂ : (1 : ℤ) ≤ i₂ ∧ (i₂ : ℤ) ≤ b := ⟨by exact_mod_cast hp₂.1.1.1, by
      exact_mod_cast hp₂.1.1.2⟩
    have h1 : (b : ℤ) ∣ (a : ℤ) * ((i₁ : ℤ) - i₂) := ⟨(r₂ : ℤ) - r₁, by simp only at heq; linarith⟩
    have h2 : (i₁ : ℤ) - i₂ = 0 :=
      Int.eq_zero_of_abs_lt_dvd (hdvd _ h1)
        (by rw [abs_lt]; constructor <;> [linarith [hi₁.1, hi₂.2]; linarith [hi₁.2, hi₂.1]])
    have h2' : (a : ℤ) * ((i₁ : ℤ) - i₂) = 0 := by rw [h2]; ring
    have h3 : (b : ℤ) * ((r₂ : ℤ) - r₁) = 0 := by simp only at heq; linarith
    have h4 : (r₁ : ℤ) = r₂ := by
      rcases mul_eq_zero.mp h3 with h | h
      · omega
      · linarith
    have : i₁ = i₂ := by omega
    subst this
    have : r₁ = r₂ := by exact_mod_cast h4
    subst this
    rfl
  · intro t ht
    rw [Finset.mem_erase, Finset.mem_Ioc] at ht
    obtain ⟨htne, htlow, hthigh⟩ := ht
    obtain ⟨u, v, huv⟩ := hcop
    have hbne : (b : ℤ) ≠ 0 := by omega
    have hmod1 := Int.emod_nonneg (t * v - 1) hbne
    have hmod2 := Int.emod_lt_of_pos (t * v - 1) hb0
    have hmodeq : (t * v - 1) % (b : ℤ) = t * v - 1 - b * ((t * v - 1) / b) := Int.emod_def _ _
    obtain ⟨i, hieq, hi1, hib⟩ :
        ∃ i : ℤ, i = t * v - b * ((t * v - 1) / b) ∧ 1 ≤ i ∧ i ≤ b :=
      ⟨(t * v - 1) % b + 1, by linarith, by linarith, by linarith⟩
    obtain ⟨m, hbm⟩ : ∃ m : ℤ, (b : ℤ) * m = (a : ℤ) * i - t := by
      refine ⟨-(t * u) - a * ((t * v - 1) / b), ?_⟩
      have hva : (v : ℤ) * a = 1 - u * b := by linarith
      have h1 : (a : ℤ) * (t * v) = t * (1 - u * b) := by
        rw [show (a : ℤ) * (t * v) = t * (v * a) by ring, hva]
      rw [hieq]
      linarith [h1]
    have hai : (a : ℤ) ≤ a * i := le_mul_of_one_le_right (by linarith) hi1
    have haib : (a : ℤ) * i ≤ a * b := by
      exact mul_le_mul_of_nonneg_left hib (by linarith)
    have hm0 : 0 ≤ m := by nlinarith
    have hm1 : 1 ≤ m := by
      rcases eq_or_lt_of_le hm0 with h | h
      · exfalso
        have h1 : (a : ℤ) * i = t := by rw [← h] at hbm; linarith
        have h2 : (i : ℤ) = 1 := by nlinarith
        rw [h2, mul_one] at h1
        exact htne h1.symm
      · omega
    have hma : m ≤ a := by nlinarith
    refine ⟨(i.toNat, ((a : ℤ) - m).toNat), ?_, ?_⟩
    · simp only [mem_filter, mem_product, mem_Icc, mem_range]
      refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, ?_, ?_⟩
      · rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
        linarith
      · rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
        linarith
    · simp only
      rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ i by omega),
        Int.toNat_of_nonneg (show (0 : ℤ) ≤ (a : ℤ) - m by omega)]
      linarith

/-! ### Reaching a row -/

/-- The value found by a search over `List.range n` lies below `n` when the fallback does. -/
theorem find?_range_getD_lt {n : ℕ} (p : ℕ → Bool) {d : ℕ} (hd : d < n) :
    ((List.range n).find? p).getD d < n := by
  rcases h : (List.range n).find? p with _ | r'
  · simpa [h] using hd
  · have := List.mem_of_find?_eq_some h
    rw [List.mem_range] at this
    simpa [h] using this

/-- The value found by a search over `List.range n` satisfies the predicate when the fallback
does. -/
theorem find?_range_getD_spec {n : ℕ} {p : ℕ → Bool} {d : ℕ} (hd : d < n) (hpd : p d) :
    p (((List.range n).find? p).getD d) := by
  rcases h : (List.range n).find? p with _ | r'
  · rw [List.find?_eq_none] at h
    exact absurd hpd (h d (List.mem_range.mpr hd))
  · simpa [h] using List.find?_some h

/-- The first column reaching a row lies in the range of columns. -/
theorem firstReach_lt {a b N : ℕ} (y : Paths.Heights a b N) (i : ℕ) :
    Paths.firstReach y i < a * N + 1 :=
  find?_range_getD_lt _ (by omega)

/-- A row that the right endpoint reaches is reached at the column `firstReach` reports. -/
theorem le_ht_firstReach {a b N : ℕ} (y : Paths.Heights a b N) {i : ℕ}
    (hi : i ≤ Paths.ht y (a * N)) : i ≤ Paths.ht y (Paths.firstReach y i) := by
  have h := find?_range_getD_spec (n := a * N + 1) (p := fun r => i ≤ Paths.ht y r) (d := a * N)
    (by omega) (by simpa using hi)
  simpa [Paths.firstReach] using h

/-- No column before the one `firstReach` reports reaches the row. -/
theorem ht_lt_of_lt_firstReach {a b N : ℕ} (y : Paths.Heights a b N) {i j : ℕ}
    (hj : j < Paths.firstReach y i) : Paths.ht y j < i := by
  by_contra hcon
  have hjle : j ≤ a * N := by have := firstReach_lt y i; omega
  have := firstReach_le y (i := i) hjle (by omega)
  omega

/-! ### The baseline cross-block count -/

/-- The primitive path of the empty filter stays at height `0` before its endpoint. -/
theorem ht_primitivePath_empty {a b r : ℕ} (hr : r < a) :
    Paths.ht (Primitive.primitivePath a b ∅) r = 0 := by
  rw [Primitive.ht_primitivePath_of_lt ∅ hr, Primitive.primitiveHeight]
  simp

/-- The primitive path of the empty filter reaches every row only at its endpoint. -/
theorem firstReach_primitivePath_empty {a b : ℕ} {i : ℕ} (hi1 : 1 ≤ i) (hib : i ≤ b) :
    Paths.firstReach (Primitive.primitivePath a b ∅) i = a := by
  refine firstReach_eq _ (by omega) ?_ fun j' hj' => ?_
  · rw [Primitive.ht_primitivePath_self]
    exact hib
  · rw [ht_primitivePath_empty hj']
    omega

/-- For two blocks of the empty filter the rank difference of a north step and a later east step
is `a i - b (a - r)`. -/
theorem rank_diff_primitivePath_empty (a b : ℕ) {i r : ℕ} (hi1 : 1 ≤ i) (hib : i ≤ b)
    (hr : r < a) :
    eastRank (Primitive.primitivePath a b ∅) r - northRank (Primitive.primitivePath a b ∅) i
      = (a : ℤ) * i - (b : ℤ) * ((a : ℤ) - r) := by
  rw [eastRank, northRank, ht_primitivePath_empty hr,
    firstReach_primitivePath_empty hi1 hib]
  push_cast
  ring

/-- Two consecutive blocks of the empty filter contribute `d - 1 = a + b - 1` cross-block
hooks. -/
theorem crossCount_primitivePath_empty (a b : ℕ) (hco : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    crossCount (Primitive.primitivePath a b ∅) (Primitive.primitivePath a b ∅) = a + b - 1 := by
  rw [crossCount, ← card_rank_pairs a b hco ha hb]
  refine congrArg card (filter_congr fun p hp => ?_)
  simp only [mem_product, mem_Icc, mem_range] at hp
  rw [rank_diff_primitivePath_empty a b hp.1.1 hp.1.2 hp.2]

/-! ### Ranks of a concatenation -/

/-- East-step ranks are invariant under the translation carrying a block into place. -/
theorem eastRank_concat {a b N : ℕ} (ha : 0 < a) (ys : Fin N → Paths.Heights a b 1) {q : ℕ}
    (hq : q < N) {r : ℕ} (hr : r < a) :
    eastRank (concat ys) (a * q + r) = eastRank (ys ⟨q, hq⟩) r := by
  rw [eastRank, eastRank, ht_concat_add ha ys hq hr]
  push_cast
  ring

/-- The first column of a concatenation reaching a row of the `p`-th block is the corresponding
column of that block, translated. -/
theorem firstReach_concat {a b N : ℕ} (ha : 0 < a) {ys : Fin N → Paths.Heights a b 1}
    (hys : ∀ k : Fin N, Paths.IsBelowDiagonal (ys k)) {p : ℕ} (hp : p < N) {i : ℕ}
    (hi1 : 1 ≤ i) (hib : i ≤ b) :
    Paths.firstReach (concat ys) (b * p + i) = a * p + Paths.firstReach (ys ⟨p, hp⟩) i := by
  have hpN : a * (p + 1) ≤ a * N := Nat.mul_le_mul le_rfl (by omega)
  rw [Nat.mul_add, Nat.mul_one] at hpN
  have hend : Paths.ht (ys ⟨p, hp⟩) (a * 1) = b * 1 := (hys ⟨p, hp⟩).2.1
  have hA : Paths.firstReach (ys ⟨p, hp⟩) i ≤ a := by
    have := firstReach_lt (ys ⟨p, hp⟩) i
    omega
  have hreach : i ≤ Paths.ht (ys ⟨p, hp⟩) (Paths.firstReach (ys ⟨p, hp⟩) i) :=
    le_ht_firstReach _ (by rw [hend]; omega)
  refine firstReach_eq _ (by omega) ?_ fun j' hj' => ?_
  · rcases Nat.lt_or_ge (Paths.firstReach (ys ⟨p, hp⟩) i) a with h | h
    · rw [ht_concat_add ha ys hp h]
      omega
    · have hAa : Paths.firstReach (ys ⟨p, hp⟩) i = a := by omega
      have hbp : b * (p + 1) = b * p + b := by ring
      rw [hAa, show a * p + a = a * (p + 1) by ring,
        ht_concat_mul ha ys (fun k => (hys k).1) (by omega)]
      omega
  · have hdm : a * (j' / a) + j' % a = j' := Nat.div_add_mod j' a
    have hmod : j' % a < a := Nat.mod_lt _ ha
    have hp' : j' / a ≤ p := by
      by_contra hcon
      have h1 : a * (p + 1) ≤ a * (j' / a) := Nat.mul_le_mul le_rfl (by omega)
      rw [Nat.mul_add, Nat.mul_one] at h1
      omega
    rcases Nat.lt_or_ge (j' / a) p with h | h
    · have hp'N : j' / a < N := by omega
      rw [ht_concat_eq ha ys hp'N rfl rfl]
      have h1 : b * (j' / a + 1) ≤ b * p := Nat.mul_le_mul le_rfl (by omega)
      have h2 : b * (j' / a + 1) = b * (j' / a) + b := by ring
      have h3 := ht_le (ys ⟨j' / a, hp'N⟩) (j' % a)
      rw [Nat.mul_one] at h3
      omega
    · have hpp : j' / a = p := by omega
      rw [ht_concat_eq ha ys hp hpp rfl]
      have hdm' : a * p + j' % a = j' := by rw [← hpp]; exact hdm
      intro hcon
      have hlt : j' % a < Paths.firstReach (ys ⟨p, hp⟩) i := by omega
      have := ht_lt_of_lt_firstReach (ys ⟨p, hp⟩) hlt
      omega

/-- North-step ranks are invariant under the translation carrying a block into place. -/
theorem northRank_concat {a b N : ℕ} (ha : 0 < a) {ys : Fin N → Paths.Heights a b 1}
    (hys : ∀ k : Fin N, Paths.IsBelowDiagonal (ys k)) {p : ℕ} (hp : p < N) {i : ℕ}
    (hi1 : 1 ≤ i) (hib : i ≤ b) :
    northRank (concat ys) (b * p + i) = northRank (ys ⟨p, hp⟩) i := by
  rw [northRank, northRank, firstReach_concat ha hys hp hi1 hib]
  push_cast
  ring

/-- Every north step of an earlier block precedes every east step of a later one: the cell it cuts
out really is a cell of the concatenation. -/
theorem le_ht_concat_of_lt {a b N : ℕ} (ha : 0 < a) {ys : Fin N → Paths.Heights a b 1}
    (hys : ∀ k : Fin N, Paths.IsBelowDiagonal (ys k)) {p q : ℕ} (hpq : p < q) (hq : q < N)
    {i r : ℕ} (hib : i ≤ b) (hr : r < a) : b * p + i ≤ Paths.ht (concat ys) (a * q + r) := by
  have hqN : a * (q + 1) ≤ a * N := Nat.mul_le_mul le_rfl (by omega)
  rw [Nat.mul_add, Nat.mul_one] at hqN
  have hmono := ht_mono (isReturnPath_concat ha ys hys).1
    (show a * q ≤ a * q + r by omega) (show a * q + r ≤ a * N by omega)
  rw [ht_concat_mul ha ys (fun k => (hys k).1) (le_of_lt hq)] at hmono
  have h1 : b * (p + 1) ≤ b * q := Nat.mul_le_mul le_rfl (by omega)
  have h2 : b * (p + 1) = b * p + b := by ring
  omega

/-! ### Primitive blocks of order filters -/

/-- Every positive `rb - ai` with `1 ≤ i` and `r < a` is a gap: it lies in the residue class of
`rb` modulo `a`, strictly below `rb`. -/
theorem mem_gaps_of_sub {a b : ℕ} (hco : a.Coprime b) {r i : ℕ} (hr : r < a) (hi : 1 ≤ i)
    (hlt : a * i < r * b) : r * b - a * i ∈ (finspan {a, b}).gaps := by
  have hai : 0 < a * i := Nat.mul_pos (by omega) hi
  have hsum : r * b - a * i + a * i = r * b := by omega
  have hmod : (r * b - a * i) % a = r * b % a := by
    conv_rhs => rw [← hsum]
    rw [Nat.add_mul_mod_self_left]
  rw [Gaps.mem_gaps_iff_not_exists a b hco,
    Nat.exists_mul_add_mul_eq_iff_mul_le_of_coprime hco hr hmod]
  omega

/-- A finset of positive naturals closed downwards above `1` is an initial interval. -/
theorem eq_Icc_one_card {S : Finset ℕ} (h0 : 0 ∉ S)
    (hdown : ∀ i ∈ S, ∀ j, 1 ≤ j → j ≤ i → j ∈ S) : S = Icc 1 #S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hm := S.max'_mem hne
    have heq : S = Icc 1 (S.max' hne) := by
      refine Finset.Subset.antisymm (fun i hi => mem_Icc.mpr ⟨?_, S.le_max' i hi⟩) fun i hi => ?_
      · rcases Nat.eq_zero_or_pos i with rfl | h
        · exact absurd hi h0
        · exact h
      · rw [mem_Icc] at hi
        exact hdown _ hm i hi.1 hi.2
    rw [heq]
    congr 1
    rw [Nat.card_Icc]
    omega

/-- In an order filter the indices counted in a column form the initial interval of length the
column's height. -/
theorem primitiveHeight_column {a b : ℕ} (hco : a.Coprime b) {F : Finset ℕ}
    (hF : Gaps.IsOrderFilter a b F) {r : ℕ} (hr : r < a) :
    {i ∈ Icc 1 b | a * i < r * b ∧ r * b - a * i ∈ F}
      = Icc 1 (Primitive.primitiveHeight a b F r) := by
  rw [Primitive.primitiveHeight]
  refine eq_Icc_one_card (by simp) fun i hi j hj1 hji => ?_
  simp only [mem_filter, mem_Icc] at hi ⊢
  obtain ⟨⟨hi1, hib⟩, hlt, hmem⟩ := hi
  have hai : a * j ≤ a * i := Nat.mul_le_mul le_rfl hji
  exact ⟨⟨hj1, by omega⟩, by omega,
    Primitive.sub_mem_of_le hF hji (by omega) hmem (mem_gaps_of_sub hco hr hj1 (by omega))⟩

/-- A column of the primitive path of an order filter reaches an index exactly when that index
contributes a gap of the filter. -/
theorem le_primitiveHeight_iff {a b : ℕ} (hco : a.Coprime b) {F : Finset ℕ}
    (hF : Gaps.IsOrderFilter a b F) {r i : ℕ} (hr : r < a) (hi1 : 1 ≤ i) :
    i ≤ Primitive.primitiveHeight a b F r ↔ i ≤ b ∧ a * i < r * b ∧ r * b - a * i ∈ F := by
  have h := primitiveHeight_column hco hF hr
  constructor
  · intro hle
    have hmem : i ∈ Icc 1 (Primitive.primitiveHeight a b F r) := mem_Icc.mpr ⟨hi1, hle⟩
    rw [← h, mem_filter, mem_Icc] at hmem
    exact ⟨hmem.1.2, hmem.2.1, hmem.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    have hmem : i ∈ {i ∈ Icc 1 b | a * i < r * b ∧ r * b - a * i ∈ F} :=
      mem_filter.mpr ⟨mem_Icc.mpr ⟨hi1, h1⟩, h2, h3⟩
    rw [h, mem_Icc] at hmem
    exact hmem.2

/-- The heights of the primitive path of an order filter are weakly increasing. -/
theorem primitiveHeight_le_succ {a b : ℕ} (hco : a.Coprime b) {F : Finset ℕ}
    (hF : Gaps.IsOrderFilter a b F) {r : ℕ} (hr : r + 1 < a) :
    Primitive.primitiveHeight a b F r ≤ Primitive.primitiveHeight a b F (r + 1) := by
  rw [Primitive.primitiveHeight, Primitive.primitiveHeight]
  refine card_le_card fun i hi => ?_
  simp only [mem_filter, mem_Icc] at hi ⊢
  obtain ⟨⟨hi1, hib⟩, hlt, hmem⟩ := hi
  have hrb : (r + 1) * b = r * b + b := by ring
  have hgap : (r + 1) * b - a * i ∈ (finspan {a, b}).gaps :=
    mem_gaps_of_sub hco hr hi1 (by omega)
  exact ⟨⟨hi1, hib⟩, by omega, hF.2 _ hmem _ hgap ⟨0, 1, by omega⟩⟩

/-- The primitive path of an order filter is a below-diagonal single-block path. -/
theorem isBelowDiagonal_primitivePath {a b : ℕ} (hco : a.Coprime b) (ha : 0 < a) {F : Finset ℕ}
    (hF : Gaps.IsOrderFilter a b F) : Paths.IsBelowDiagonal (Primitive.primitivePath a b F) := by
  refine ⟨Primitive.ht_primitivePath_zero F ha, ?_, ?_, ?_⟩
  · rw [Nat.mul_one, Nat.mul_one]
    exact Primitive.ht_primitivePath_self a b F
  · intro r hr
    rw [Nat.mul_one] at hr
    rcases Nat.lt_or_ge (r + 1) a with h | h
    · rw [Primitive.ht_primitivePath_of_lt F (by omega), Primitive.ht_primitivePath_of_lt F h]
      exact primitiveHeight_le_succ hco hF h
    · rw [Primitive.ht_primitivePath_of_lt F hr, show r + 1 = a by omega,
        Primitive.ht_primitivePath_self]
      exact Primitive.primitiveHeight_le a b F r
  · intro r hr
    rw [Nat.mul_one] at hr
    rcases Nat.lt_or_ge r a with h | h
    · rw [Primitive.ht_primitivePath_of_lt F h]
      have h3 : b * r = r * b := Nat.mul_comm b r
      rcases Nat.eq_zero_or_pos (Primitive.primitiveHeight a b F r) with hc | hc
      · rw [hc]
        omega
      · have htop := (le_primitiveHeight_iff hco hF h hc).mp le_rfl
        omega
    · rw [show r = a by omega, Primitive.ht_primitivePath_self]
      exact le_of_eq (Nat.mul_comm a b)

/-- Every gap is `rb - ai` for some column `r < a` and some index `1 ≤ i ≤ b`. -/
theorem exists_rep_of_mem_gaps {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) {g : ℕ}
    (hg : g ∈ (finspan {a, b}).gaps) :
    ∃ r i, r < a ∧ 1 ≤ i ∧ i ≤ b ∧ a * i < r * b ∧ g = r * b - a * i := by
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | h
    · exact absurd hg (NumericalSemigroup.zero_notMem_gaps _)
    · exact h
  obtain ⟨r, hra, hmod⟩ := GapPoset.exists_lt_mod_eq_mul a b hco (by omega) g
  rw [Gaps.mem_gaps_iff_not_exists a b hco g,
    Nat.exists_mul_add_mul_eq_iff_mul_le_of_coprime hco hra hmod, not_le] at hg
  have hdvd : a ∣ r * b - g := (Nat.modEq_iff_dvd' hg.le).mp hmod
  have hai : a * ((r * b - g) / a) = r * b - g := Nat.mul_div_cancel' hdvd
  have hrb : r * b ≤ (a - 1) * b := Nat.mul_le_mul (by omega) le_rfl
  have hab : (a - 1) * b + b = a * b := by
    rw [Nat.sub_mul, Nat.one_mul]
    have : b ≤ a * b := Nat.le_mul_of_pos_left b (by omega)
    omega
  refine ⟨r, (r * b - g) / a, hra, ?_, ?_, by omega, by omega⟩
  · rcases Nat.eq_zero_or_pos ((r * b - g) / a) with h | h
    · rw [h, Nat.mul_zero] at hai
      omega
    · exact h
  · have : a * ((r * b - g) / a) < a * b := by omega
    exact le_of_lt (Nat.lt_of_mul_lt_mul_left this)

/-- The primitive path determines the order filter it came from. -/
theorem primitivePath_injective {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) {F F' : Finset ℕ}
    (hF : Gaps.IsOrderFilter a b F) (hF' : Gaps.IsOrderFilter a b F')
    (h : Primitive.primitivePath a b F = Primitive.primitivePath a b F') : F = F' := by
  have hcol : ∀ r < a, Primitive.primitiveHeight a b F r = Primitive.primitiveHeight a b F' r := by
    intro r hr
    rw [← Primitive.ht_primitivePath_of_lt F hr, ← Primitive.ht_primitivePath_of_lt F' hr, h]
  ext g
  constructor <;> intro hgF
  · obtain ⟨r, i, hr, hi1, hib, hlt, rfl⟩ := exists_rep_of_mem_gaps hco ha (hF.1 hgF)
    have h1 := (le_primitiveHeight_iff hco hF hr hi1).mpr ⟨hib, hlt, hgF⟩
    rw [hcol r hr] at h1
    exact ((le_primitiveHeight_iff hco hF' hr hi1).mp h1).2.2
  · obtain ⟨r, i, hr, hi1, hib, hlt, rfl⟩ := exists_rep_of_mem_gaps hco ha (hF'.1 hgF)
    have h1 := (le_primitiveHeight_iff hco hF' hr hi1).mpr ⟨hib, hlt, hgF⟩
    rw [← hcol r hr] at h1
    exact ((le_primitiveHeight_iff hco hF hr hi1).mp h1).2.2

/-! ### Order filters of single-block paths -/

/-- With `a` and `b` coprime, `ai` never equals `rb` for a column `1 ≤ r < a`. -/
theorem mul_ne_mul_of_lt {a b : ℕ} (hco : a.Coprime b) {r i : ℕ} (hr1 : 1 ≤ r) (hr : r < a) :
    a * i ≠ r * b := by
  intro heq
  have hdvd : a ∣ r := hco.dvd_of_dvd_mul_right ⟨i, heq.symm⟩
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- The column and index of a gap are determined by the gap. -/
theorem rep_unique {a b : ℕ} (hco : a.Coprime b) {r i r' i' g : ℕ} (hr : r < a) (hr' : r' < a)
    (h : a * i + g = r * b) (h' : a * i' + g = r' * b) : r = r' ∧ i = i' := by
  have ha0 : (0 : ℤ) < a := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · omega
    · exact_mod_cast hpos
  have hacop : IsCoprime (a : ℤ) (b : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using hco
  have e1 : (a : ℤ) * i + g = r * b := by exact_mod_cast h
  have e2 : (a : ℤ) * i' + g = r' * b := by exact_mod_cast h'
  have hdvd : (a : ℤ) ∣ ((r : ℤ) - r') :=
    hacop.dvd_of_dvd_mul_right ⟨(i : ℤ) - i', by linarith⟩
  have hrr : (r : ℤ) - r' = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
    rw [abs_lt]
    have h1 : (r : ℤ) < a := by exact_mod_cast hr
    have h2 : (r' : ℤ) < a := by exact_mod_cast hr'
    have h3 : (0 : ℤ) ≤ r := by positivity
    have h4 : (0 : ℤ) ≤ r' := by positivity
    exact ⟨by linarith, by linarith⟩
  have hii : (i : ℤ) = i' := by
    have hrb : (r : ℤ) * b = (r' : ℤ) * b := by rw [show (r : ℤ) = r' by linarith]
    have : (a : ℤ) * i = a * i' := by linarith
    exact mul_left_cancel₀ (by linarith) this
  exact ⟨by omega, by omega⟩

/-- The set of gaps cut out by a single-block path: the gap `rb - ai` for each of its cells. -/
def pathFilter {a b : ℕ} (z : Paths.Heights a b 1) : Finset ℕ :=
  ((Ico 1 a ×ˢ Icc 1 b).filter fun p => p.2 ≤ Paths.ht z p.1).image fun p => p.1 * b - a * p.2

/-- Membership in the gap set of a below-diagonal single-block path, in terms of its cells. -/
theorem mem_pathFilter_iff {a b : ℕ} {z : Paths.Heights a b 1} (hz : Paths.IsBelowDiagonal z)
    {g : ℕ} :
    g ∈ pathFilter z ↔ ∃ r i, 1 ≤ r ∧ r < a ∧ 1 ≤ i ∧ i ≤ Paths.ht z r ∧ a * i + g = r * b := by
  rw [pathFilter]
  simp only [mem_image, mem_filter, mem_product, mem_Ico, mem_Icc, Prod.exists]
  constructor
  · rintro ⟨r, i, ⟨⟨⟨hr1, hra⟩, hi1, hib⟩, hile⟩, rfl⟩
    have hdiag := hz.2.2.2 r (by rw [Nat.mul_one]; omega)
    have hai : a * i ≤ a * Paths.ht z r := Nat.mul_le_mul le_rfl hile
    have hcomm : b * r = r * b := Nat.mul_comm b r
    exact ⟨r, i, hr1, hra, hi1, hile, by omega⟩
  · rintro ⟨r, i, hr1, hra, hi1, hile, heq⟩
    have hbz : Paths.ht z r ≤ b := by have := ht_le z r; omega
    exact ⟨r, i, ⟨⟨⟨hr1, hra⟩, hi1, by omega⟩, hile⟩, by omega⟩

/-- The gap set of a below-diagonal single-block path is an order filter. -/
theorem isOrderFilter_pathFilter {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a)
    {z : Paths.Heights a b 1} (hz : Paths.IsBelowDiagonal z) :
    Gaps.IsOrderFilter a b (pathFilter z) := by
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | h
    · rw [Nat.Coprime, Nat.gcd_zero_right] at hco
      omega
    · exact h
  have ha0 : (0 : ℤ) < a := by exact_mod_cast (by omega : 0 < a)
  have hb0 : (0 : ℤ) < b := by exact_mod_cast hb1
  have hacop : IsCoprime (a : ℤ) (b : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using hco
  refine ⟨fun g hg => ?_, fun g hg h hh hgh => ?_⟩
  · obtain ⟨r, i, hr1, hr, hi1, hile, heq⟩ := (mem_pathFilter_iff hz).mp hg
    have hne : a * i ≠ r * b := mul_ne_mul_of_lt hco hr1 hr
    rw [show g = r * b - a * i by omega]
    exact mem_gaps_of_sub hco hr hi1 (by omega)
  · obtain ⟨r, i, hr1, hr, hi1, hile, heq⟩ := (mem_pathFilter_iff hz).mp hg
    obtain ⟨r', i', hr'a, hi'1, hi'b, hlt', hheq⟩ := exists_rep_of_mem_gaps hco ha hh
    obtain ⟨u, v, huv⟩ := hgh
    have hh' : a * i' + h = r' * b := by omega
    have hr'1 : 1 ≤ r' := by
      rcases Nat.eq_zero_or_pos r' with rfl | hpos
      · omega
      · exact hpos
    have e1 : (a : ℤ) * i + g = r * b := by exact_mod_cast heq
    have e2 : (a : ℤ) * i' + h = r' * b := by exact_mod_cast hh'
    have e3 : (g : ℤ) + ((u : ℤ) * a + (v : ℤ) * b) = h := by exact_mod_cast huv
    have hkey : ((r : ℤ) + v - r') * b = a * ((i : ℤ) - i' - u) := by linarith
    obtain ⟨w, hw⟩ : (a : ℤ) ∣ ((r : ℤ) + v - r') :=
      hacop.dvd_of_dvd_mul_right ⟨(i : ℤ) - i' - u, hkey⟩
    have hib : (i : ℤ) ≤ b := by
      have h1 := ht_le z r
      have h2 : i ≤ b := by omega
      exact_mod_cast h2
    have hwb : (w : ℤ) * b = (i : ℤ) - i' - u := by
      refine mul_left_cancel₀ (show (a : ℤ) ≠ 0 by linarith) ?_
      rw [← hkey, hw]
      ring
    have hw0 : 0 ≤ w := by
      by_contra hcon
      have hw1 : w ≤ -1 := by omega
      have h1 : (a : ℤ) * w ≤ a * (-1) := mul_le_mul_of_nonneg_left hw1 (le_of_lt ha0)
      have h2 : (r' : ℤ) < a := by exact_mod_cast hr'a
      have h3 : (0 : ℤ) ≤ r := by positivity
      have h4 : (0 : ℤ) ≤ v := by positivity
      linarith
    have hwle : w ≤ 0 := by
      by_contra hcon
      have hw1 : 1 ≤ w := by omega
      have h1 : (1 : ℤ) * b ≤ w * b := mul_le_mul_of_nonneg_right hw1 (le_of_lt hb0)
      have h2 : (0 : ℤ) ≤ u := by positivity
      have h3 : (1 : ℤ) ≤ i' := by exact_mod_cast hi'1
      linarith
    have hw_eq : w = 0 := le_antisymm hwle hw0
    rw [hw_eq, mul_zero] at hw
    rw [hw_eq, zero_mul] at hwb
    have hrr' : r ≤ r' := by
      have h4 : (0 : ℤ) ≤ v := by positivity
      have : (r : ℤ) ≤ r' := by linarith
      exact_mod_cast this
    have hii' : i' ≤ i := by
      have h2 : (0 : ℤ) ≤ u := by positivity
      have : (i' : ℤ) ≤ i := by linarith
      exact_mod_cast this
    refine (mem_pathFilter_iff hz).mpr ⟨r', i', hr'1, hr'a, hi'1, ?_, hh'⟩
    exact le_trans hii' (le_trans hile (ht_mono hz hrr' (by rw [Nat.mul_one]; omega)))

/-- The primitive path of the gap set of a below-diagonal single-block path is that path. -/
theorem primitivePath_pathFilter {a b : ℕ} (hco : a.Coprime b)
    {z : Paths.Heights a b 1} (hz : Paths.IsBelowDiagonal z) :
    Primitive.primitivePath a b (pathFilter z) = z := by
  funext s
  have hs : (s : ℕ) ≤ a := by have := s.2; omega
  refine Fin.ext ?_
  rw [← ht_coe (Primitive.primitivePath a b (pathFilter z)) s, ← ht_coe z s]
  rcases Nat.lt_or_ge (s : ℕ) a with h | h
  · rw [Primitive.ht_primitivePath_of_lt _ h, Primitive.primitiveHeight]
    rcases Nat.eq_zero_or_pos (s : ℕ) with h0 | h0
    · rw [h0, hz.1]
      simp
    · have hbz : Paths.ht z (s : ℕ) ≤ b := by have := ht_le z (s : ℕ); omega
      have hdiag := hz.2.2.2 (s : ℕ) (by omega)
      have hcomm : b * (s : ℕ) = (s : ℕ) * b := Nat.mul_comm _ _
      have hne : ∀ i, a * i ≠ (s : ℕ) * b := fun i => mul_ne_mul_of_lt hco h0 h
      have hset : {i ∈ Icc 1 b | a * i < (s : ℕ) * b ∧ (s : ℕ) * b - a * i ∈ pathFilter z}
          = Icc 1 (Paths.ht z (s : ℕ)) := by
        ext i
        simp only [mem_filter, mem_Icc]
        constructor
        · rintro ⟨⟨hi1, hib⟩, hlt, hmem⟩
          obtain ⟨r', i', hr'1, hr'a, hi'1, hi'le, heq'⟩ := (mem_pathFilter_iff hz).mp hmem
          obtain ⟨hrr, hii⟩ := rep_unique hco h hr'a
            (show a * i + ((s : ℕ) * b - a * i) = (s : ℕ) * b by omega) heq'
          rw [hrr, hii]
          exact ⟨hi'1, hi'le⟩
        · rintro ⟨hi1, hile⟩
          have hai : a * i ≤ a * Paths.ht z (s : ℕ) := Nat.mul_le_mul le_rfl hile
          have hne' := hne i
          refine ⟨⟨hi1, by omega⟩, by omega, ?_⟩
          exact (mem_pathFilter_iff hz).mpr ⟨s, i, h0, h, hi1, hile, by omega⟩
      rw [hset, Nat.card_Icc]
      omega
  · have hend := hz.2.1
    rw [Nat.mul_one, Nat.mul_one] at hend
    rw [show (s : ℕ) = a by omega, Primitive.ht_primitivePath_self, hend]

/-- Single-block below-diagonal paths are the same thing as order filters of the gap set. -/
def blockFilterEquiv {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) :
    {z : Paths.Heights a b 1 // Paths.IsBelowDiagonal z} ≃
      {F : Finset ℕ // Gaps.IsOrderFilter a b F} where
  toFun z := ⟨pathFilter z.1, isOrderFilter_pathFilter hco ha z.2⟩
  invFun F := ⟨Primitive.primitivePath a b F.1,
    isBelowDiagonal_primitivePath hco (by omega) F.2⟩
  left_inv z := Subtype.ext (primitivePath_pathFilter hco z.2)
  right_inv F := Subtype.ext <| by
    have hbd := isBelowDiagonal_primitivePath hco (show 0 < a by omega) F.2
    exact primitivePath_injective hco ha (isOrderFilter_pathFilter hco ha hbd) F.2
      (primitivePath_pathFilter hco hbd)

/-- Unique factorisation, in the form the return-path identity uses it: a path returning to the
diagonal after each of its `N` blocks is the same thing as a word of `N` order filters. -/
def returnPathFilterEquiv {a b N : ℕ} (hco : a.Coprime b) (ha : 1 < a) :
    {y : Paths.Heights a b N // Paths.IsReturnPath y} ≃
      (Fin N → {F : Finset ℕ // Gaps.IsOrderFilter a b F}) :=
  (returnPathEquiv (show 0 < a by omega)).trans
    (Equiv.piCongrRight fun _ => blockFilterEquiv hco ha)

/-! ### The block splitting of the hook count -/

/-- The cells of a concatenation reindexed by block: the row `bp + i` lies in block `p` with
`1 ≤ i ≤ b`, and the column `aq + r` in block `q` with `r < a`. -/
theorem hookCount_concat_eq_sum {a b N : ℕ} (ha : 0 < a) (hb : 0 < b)
    (ys : Fin N → Paths.Heights a b 1) (hys : ∀ k : Fin N, Paths.IsBelowDiagonal (ys k)) :
    Paths.hookCount (concat ys) =
      ∑ x : Fin N × Fin N, #{y ∈ Icc 1 b ×ˢ range a |
        b * (x.1 : ℕ) + y.1 ≤ Paths.ht (concat ys) (a * (x.2 : ℕ) + y.2) ∧
        -(b : ℤ) < eastRank (concat ys) (a * (x.2 : ℕ) + y.2)
            - northRank (concat ys) (b * (x.1 : ℕ) + y.1) ∧
          eastRank (concat ys) (a * (x.2 : ℕ) + y.2)
            - northRank (concat ys) (b * (x.1 : ℕ) + y.1) ≤ (a : ℤ)} := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Paths.hookCount]
  have hzero : Paths.ht (concat ys) 0 = 0 := (isReturnPath_concat ha ys hys).1.1
  rw [hookCount_eq_card_rank,
    show #{c ∈ Ico 1 (a * N) ×ˢ Icc 1 (b * N) | c.2 ≤ Paths.ht (concat ys) c.1 ∧
        -(b : ℤ) < eastRank (concat ys) c.1 - northRank (concat ys) c.2 ∧
          eastRank (concat ys) c.1 - northRank (concat ys) c.2 ≤ (a : ℤ)}
      = #{z ∈ (univ : Finset (Fin N × Fin N)) ×ˢ (Icc 1 b ×ˢ range a) |
          b * (z.1.1 : ℕ) + z.2.1 ≤ Paths.ht (concat ys) (a * (z.1.2 : ℕ) + z.2.2) ∧
          -(b : ℤ) < eastRank (concat ys) (a * (z.1.2 : ℕ) + z.2.2)
              - northRank (concat ys) (b * (z.1.1 : ℕ) + z.2.1) ∧
            eastRank (concat ys) (a * (z.1.2 : ℕ) + z.2.2)
              - northRank (concat ys) (b * (z.1.1 : ℕ) + z.2.1) ≤ (a : ℤ)} from ?_,
    Finset.card_filter, Finset.sum_product]
  · exact sum_congr rfl fun x _ => (Finset.card_filter _ _).symm
  refine Finset.card_bij'
    (fun c _ => ((⟨(c.2 - 1) / b % N, Nat.mod_lt _ hN⟩, ⟨c.1 / a % N, Nat.mod_lt _ hN⟩),
      (c.2 - b * ((c.2 - 1) / b), c.1 % a)))
    (fun z _ => (a * (z.1.2 : ℕ) + z.2.2, b * (z.1.1 : ℕ) + z.2.1)) ?_ ?_ ?_ ?_
  · intro c hc
    simp only [mem_filter, mem_product, mem_Ico, mem_Icc, mem_range, mem_univ, true_and] at hc ⊢
    obtain ⟨⟨⟨hc1, hc2⟩, hc3, hc4⟩, hcell, hr1, hr2⟩ := hc
    have hdm1 : a * (c.1 / a) + c.1 % a = c.1 := Nat.div_add_mod c.1 a
    have hmod1 : c.1 % a < a := Nat.mod_lt _ ha
    have hq : c.1 / a < N := (Nat.div_lt_iff_lt_mul ha).mpr (by rw [Nat.mul_comm]; omega)
    have hdm2 : b * ((c.2 - 1) / b) + (c.2 - 1) % b = c.2 - 1 := Nat.div_add_mod (c.2 - 1) b
    have hmod2 : (c.2 - 1) % b < b := Nat.mod_lt _ hb
    have hp : (c.2 - 1) / b < N := (Nat.div_lt_iff_lt_mul hb).mpr (by rw [Nat.mul_comm]; omega)
    rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq,
      show b * ((c.2 - 1) / b) + (c.2 - b * ((c.2 - 1) / b)) = c.2 from by omega, hdm1]
    exact ⟨⟨by omega, by omega⟩, hcell, hr1, hr2⟩
  · intro z hz
    simp only [mem_filter, mem_product, mem_Ico, mem_Icc, mem_range, mem_univ, true_and] at hz ⊢
    obtain ⟨⟨⟨hi1, hib⟩, hra⟩, hcell, hr1, hr2⟩ := hz
    have hqN : a * ((z.1.2 : ℕ) + 1) ≤ a * N := Nat.mul_le_mul le_rfl (by omega)
    have hpN : b * ((z.1.1 : ℕ) + 1) ≤ b * N := Nat.mul_le_mul le_rfl (by omega)
    rw [Nat.mul_add, Nat.mul_one] at hqN
    rw [Nat.mul_add, Nat.mul_one] at hpN
    refine ⟨⟨⟨?_, by omega⟩, by omega, by omega⟩, hcell, hr1, hr2⟩
    rcases Nat.eq_zero_or_pos (a * (z.1.2 : ℕ) + z.2.2) with h | h
    · rw [h] at hcell
      omega
    · exact h
  · intro c hc
    simp only [mem_filter, mem_product, mem_Ico, mem_Icc] at hc
    obtain ⟨⟨⟨hc1, hc2⟩, hc3, hc4⟩, -⟩ := hc
    have hdm1 : a * (c.1 / a) + c.1 % a = c.1 := Nat.div_add_mod c.1 a
    have hdm2 : b * ((c.2 - 1) / b) + (c.2 - 1) % b = c.2 - 1 := Nat.div_add_mod (c.2 - 1) b
    have hmod2 : (c.2 - 1) % b < b := Nat.mod_lt _ hb
    have hq : c.1 / a < N := (Nat.div_lt_iff_lt_mul ha).mpr (by rw [Nat.mul_comm]; omega)
    have hp : (c.2 - 1) / b < N := (Nat.div_lt_iff_lt_mul hb).mpr (by rw [Nat.mul_comm]; omega)
    refine Prod.ext ?_ ?_
    · simpa [Nat.mod_eq_of_lt hq] using hdm1
    · simp only [Nat.mod_eq_of_lt hp]
      omega
  · intro z hz
    simp only [mem_filter, mem_product, mem_Icc, mem_range, mem_univ, true_and] at hz
    obtain ⟨⟨⟨hi1, hib⟩, hra⟩, -⟩ := hz
    have hdiv1 : (a * (z.1.2 : ℕ) + z.2.2) / a = (z.1.2 : ℕ) := by
      rw [Nat.mul_add_div ha, Nat.div_eq_of_lt hra, Nat.add_zero]
    have hmod1 : (a * (z.1.2 : ℕ) + z.2.2) % a = z.2.2 := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hra]
    have hdiv2 : (b * (z.1.1 : ℕ) + z.2.1 - 1) / b = (z.1.1 : ℕ) := by
      rw [show b * (z.1.1 : ℕ) + z.2.1 - 1 = b * (z.1.1 : ℕ) + (z.2.1 - 1) from by omega,
        Nat.mul_add_div hb, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    refine Prod.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) (Prod.ext ?_ ?_)
    · simpa [hdiv2] using Nat.mod_eq_of_lt (z.1.1).2
    · simpa [hdiv1] using Nat.mod_eq_of_lt (z.1.2).2
    · simp only [hdiv2]
      omega
    · simpa using hmod1

/-- A row of a later block never cuts out a cell with a column of an earlier block. -/
theorem card_blockPair_gt {a b N : ℕ} (ha : 0 < a) {ys : Fin N → Paths.Heights a b 1}
    {p q : Fin N} (hqp : (q : ℕ) < (p : ℕ)) :
    #{y ∈ Icc 1 b ×ˢ range a |
        b * (p : ℕ) + y.1 ≤ Paths.ht (concat ys) (a * (q : ℕ) + y.2) ∧
        -(b : ℤ) < eastRank (concat ys) (a * (q : ℕ) + y.2)
            - northRank (concat ys) (b * (p : ℕ) + y.1) ∧
          eastRank (concat ys) (a * (q : ℕ) + y.2)
            - northRank (concat ys) (b * (p : ℕ) + y.1) ≤ (a : ℤ)} = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro y hy
  simp only [mem_product, mem_Icc, mem_range] at hy
  rw [ht_concat_add ha ys q.2 hy.2]
  have h1 := ht_le (ys ⟨(q : ℕ), q.2⟩) y.2
  have h2 : b * ((q : ℕ) + 1) ≤ b * (p : ℕ) := Nat.mul_le_mul le_rfl (by omega)
  have h3 : b * ((q : ℕ) + 1) = b * (q : ℕ) + b := by ring
  rw [Nat.mul_one] at h1
  rintro ⟨hcell, -, -⟩
  omega

/-- The cells cut out by a row of an earlier block and a column of a later one are exactly the
cross-block pairs of the two blocks. -/
theorem card_blockPair_lt {a b N : ℕ} (ha : 0 < a) {ys : Fin N → Paths.Heights a b 1}
    (hys : ∀ k : Fin N, Paths.IsBelowDiagonal (ys k)) {p q : Fin N} (hpq : (p : ℕ) < (q : ℕ)) :
    #{y ∈ Icc 1 b ×ˢ range a |
        b * (p : ℕ) + y.1 ≤ Paths.ht (concat ys) (a * (q : ℕ) + y.2) ∧
        -(b : ℤ) < eastRank (concat ys) (a * (q : ℕ) + y.2)
            - northRank (concat ys) (b * (p : ℕ) + y.1) ∧
          eastRank (concat ys) (a * (q : ℕ) + y.2)
            - northRank (concat ys) (b * (p : ℕ) + y.1) ≤ (a : ℤ)}
      = crossCount (ys p) (ys q) := by
  rw [crossCount]
  refine congrArg card (filter_congr fun y hy => ?_)
  simp only [mem_product, mem_Icc, mem_range] at hy
  rw [eastRank_concat ha ys q.2 hy.2, northRank_concat ha hys p.2 hy.1.1 hy.1.2]
  exact and_iff_right (le_ht_concat_of_lt ha hys hpq q.2 hy.1.2 hy.2)

/-- The cells cut out by a row and a column of the same block are exactly that block's own
cells. -/
theorem card_blockPair_self {a b N : ℕ} (ha : 0 < a) {ys : Fin N → Paths.Heights a b 1}
    (hys : ∀ k : Fin N, Paths.IsBelowDiagonal (ys k)) (q : Fin N) :
    #{y ∈ Icc 1 b ×ˢ range a |
        b * (q : ℕ) + y.1 ≤ Paths.ht (concat ys) (a * (q : ℕ) + y.2) ∧
        -(b : ℤ) < eastRank (concat ys) (a * (q : ℕ) + y.2)
            - northRank (concat ys) (b * (q : ℕ) + y.1) ∧
          eastRank (concat ys) (a * (q : ℕ) + y.2)
            - northRank (concat ys) (b * (q : ℕ) + y.1) ≤ (a : ℤ)}
      = Paths.hookCount (ys q) := by
  have h0 : Paths.ht (ys q) 0 = 0 := (hys q).1
  have hq : (⟨(q : ℕ), q.2⟩ : Fin N) = q := rfl
  rw [hookCount_eq_card_rank]
  refine Finset.card_bij' (fun y _ => (y.2, y.1)) (fun c _ => (c.2, c.1)) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [mem_filter, mem_product, mem_Icc, mem_range, mem_Ico, Nat.mul_one] at hy ⊢
    obtain ⟨⟨⟨hi1, hib⟩, hra⟩, hcell, hr1, hr2⟩ := hy
    rw [ht_concat_add ha ys q.2 hra, hq] at hcell
    rw [eastRank_concat ha ys q.2 hra, northRank_concat ha hys q.2 hi1 hib, hq] at hr1 hr2
    refine ⟨⟨⟨?_, hra⟩, hi1, hib⟩, by omega, hr1, hr2⟩
    rcases Nat.eq_zero_or_pos y.2 with h | h
    · rw [h] at hcell
      omega
    · exact h
  · intro c hc
    simp only [mem_filter, mem_product, mem_Icc, mem_range, mem_Ico, Nat.mul_one] at hc ⊢
    obtain ⟨⟨⟨hr1', hra⟩, hi1, hib⟩, hcell, hrk1, hrk2⟩ := hc
    rw [ht_concat_add ha ys q.2 hra, hq, eastRank_concat ha ys q.2 hra,
      northRank_concat ha hys q.2 hi1 hib, hq]
    exact ⟨⟨⟨hi1, hib⟩, hra⟩, by omega, hrk1, hrk2⟩
  · exact fun y _ => rfl
  · exact fun c _ => rfl

/-- The hook count of a concatenation splits into the blocks' own hook counts and one cross-block
contribution for each ordered pair of blocks. -/
theorem hookCount_concat {a b N : ℕ} (ha : 0 < a) (hb : 0 < b)
    (ys : Fin N → Paths.Heights a b 1) (hys : ∀ k : Fin N, Paths.IsBelowDiagonal (ys k)) :
    Paths.hookCount (concat ys) =
      ∑ x : Fin N × Fin N, if x.1 = x.2 then Paths.hookCount (ys x.1)
        else if (x.1 : ℕ) < (x.2 : ℕ) then crossCount (ys x.1) (ys x.2) else 0 := by
  rw [hookCount_concat_eq_sum ha hb ys hys]
  refine sum_congr rfl fun x _ => ?_
  rcases lt_trichotomy (x.1 : ℕ) (x.2 : ℕ) with h | h | h
  · rw [ite_eq_right fun he => absurd (congrArg Fin.val he) (by omega), ite_eq_left h]
    exact card_blockPair_lt ha hys h
  · have hx : x.1 = x.2 := Fin.ext h
    rw [ite_eq_left hx, ← hx]
    exact card_blockPair_self ha hys x.1
  · rw [ite_eq_right fun he => absurd (congrArg Fin.val he) (by omega),
      ite_eq_right (by omega : ¬ (x.1 : ℕ) < (x.2 : ℕ))]
    exact card_blockPair_gt ha h

/-! ### The block hook shift -/

/-- The primitive block of the empty filter has no cells, hence no hooks. -/
theorem hookCount_primitivePath_empty (a b : ℕ) :
    Paths.hookCount (Primitive.primitivePath a b ∅) = 0 := by
  rw [Paths.hookCount, card_eq_zero, filter_eq_empty_iff]
  intro c hc
  simp only [mem_product, mem_Ico, mem_Icc, Nat.mul_one] at hc
  rw [ht_primitivePath_empty hc.1.2]
  rintro ⟨h1, -, -⟩
  omega

/-- There are `C(N,2)` ordered pairs of distinct blocks. -/
theorem card_pairs_lt (N : ℕ) :
    #{x ∈ (univ : Finset (Fin N × Fin N)) | (x.1 : ℕ) < (x.2 : ℕ)} = N.choose 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  have hinner : ∀ q : Fin N, (∑ p : Fin N, if (p : ℕ) < (q : ℕ) then 1 else 0) = (q : ℕ) := by
    intro q
    rw [Finset.sum_congr rfl fun (p : Fin N) _ =>
      if_congr (show ((p : ℕ) < (q : ℕ)) ↔ p ∈ Finset.Iio q by simp) rfl rfl,
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Fin.card_Iio, smul_eq_mul,
      Nat.mul_one]
  rw [Finset.sum_congr rfl fun q _ => hinner q, Fin.sum_univ_eq_sum_range (fun i => i) N,
    Finset.sum_range_id, Nat.choose_two_right]

/-- The concatenation of `N` empty-filter blocks has exactly `κ_N` hooks: every one of the
`C(N,2)` ordered pairs of blocks contributes the baseline `d - 1`. -/
theorem hookCount_concat_primitivePath_empty (a b N : ℕ) (hco : a.Coprime b) (ha : 0 < a)
    (hb : 0 < b) :
    Paths.hookCount (concat fun _ : Fin N => Primitive.primitivePath a b ∅)
      = Paths.kappaShift a b N := by
  have hbd : ∀ _ : Fin N, Paths.IsBelowDiagonal (Primitive.primitivePath a b ∅) := fun _ =>
    isBelowDiagonal_primitivePath hco ha ⟨by simp, by simp⟩
  rw [hookCount_concat ha hb _ hbd]
  have hstep : ∀ x : Fin N × Fin N,
      (if x.1 = x.2 then Paths.hookCount (Primitive.primitivePath a b ∅)
        else if (x.1 : ℕ) < (x.2 : ℕ) then
          crossCount (Primitive.primitivePath a b ∅) (Primitive.primitivePath a b ∅) else 0)
      = if (x.1 : ℕ) < (x.2 : ℕ) then a + b - 1 else 0 := by
    intro x
    rw [hookCount_primitivePath_empty, crossCount_primitivePath_empty a b hco ha hb]
    by_cases h1 : x.1 = x.2
    · rw [ite_eq_left h1, ite_eq_right (by rw [h1]; omega)]
    · rw [ite_eq_right h1]
  rw [Finset.sum_congr rfl fun x _ => hstep x, ← Finset.sum_filter, Finset.sum_const,
    card_pairs_lt, Paths.kappaShift, smul_eq_mul, Nat.mul_comm]

/-! ### The internal counts as values of the quadratic form -/

/-- The indicator vector of a set of gaps, as a point of `ℤ^G`. -/
def filterVector (a b : ℕ) (F : Finset ℕ) : (finspan {a, b}).gaps → ℤ :=
  fun g => if (g : ℕ) ∈ F then 1 else 0

/-- Taking the rank-one evaluation of the hook count of a primitive block as an input, the hook
count of the concatenation of a word of order filters is the sum of the quadratic form at the
indicator vectors of the letters plus one cross-block contribution per ordered pair. -/
theorem hookCount_concat_primitivePath {a b N : ℕ} (hco : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (rankOne : ∀ F : Finset ℕ, Gaps.IsOrderFilter a b F →
      (Paths.hookCount (Primitive.primitivePath a b F) : ℤ) = HJO.Q a b (filterVector a b F))
    (F : Fin N → Finset ℕ) (hF : ∀ k, Gaps.IsOrderFilter a b (F k)) :
    (Paths.hookCount (concat fun k => Primitive.primitivePath a b (F k)) : ℤ)
      = ∑ x : Fin N × Fin N, if x.1 = x.2 then HJO.Q a b (filterVector a b (F x.1))
          else if (x.1 : ℕ) < (x.2 : ℕ) then
            (crossCount (Primitive.primitivePath a b (F x.1))
              (Primitive.primitivePath a b (F x.2)) : ℤ) else 0 := by
  rw [hookCount_concat ha hb _ fun k => isBelowDiagonal_primitivePath hco ha (hF k),
    Nat.cast_sum]
  refine sum_congr rfl fun x _ => ?_
  by_cases h1 : x.1 = x.2
  · rw [ite_eq_left h1, ite_eq_left h1, rankOne _ (hF x.1)]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : (x.1 : ℕ) < (x.2 : ℕ)
    · rw [ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2, Nat.cast_zero]

/-! ### The cells of a set of gaps -/

/-- Every gap is positive. -/
theorem one_le_of_mem_gaps {a b : ℕ} {g : ℕ} (hg : g ∈ (finspan {a, b}).gaps) : 1 ≤ g := by
  rcases Nat.eq_zero_or_pos g with rfl | h
  · exact absurd hg (NumericalSemigroup.zero_notMem_gaps _)
  · exact h

/-- Every gap is at most the Frobenius gap `ab - a - b`. -/
theorem add_le_of_mem_gaps {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) {g : ℕ}
    (hg : g ∈ (finspan {a, b}).gaps) : g + a + b ≤ a * b := by
  obtain ⟨r, i, hr, hi1, hib, hlt, rfl⟩ := exists_rep_of_mem_gaps hco ha hg
  have h1 : (r + 1) * b ≤ a * b := Nat.mul_le_mul_right b (by omega)
  have h2 : a * 1 ≤ a * i := Nat.mul_le_mul_left a hi1
  have h3 : (r + 1) * b = r * b + b := by ring
  omega

/-- The cells of the diagram of a set of gaps: the pairs `(r, i)` with `1 ≤ r < a`, `1 ≤ i ≤ b`
and `rb - ai` in the set. -/
def cellSet (a b : ℕ) (F : Finset ℕ) : Finset (ℕ × ℕ) :=
  {p ∈ Ico 1 a ×ˢ Icc 1 b | a * p.2 < p.1 * b ∧ p.1 * b - a * p.2 ∈ F}

/-- A sum over a set of gaps is a sum over its cells. -/
theorem sum_cellSet {M : Type*} [AddCommMonoid M] {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a)
    {F : Finset ℕ} (hF : F ⊆ (finspan {a, b}).gaps) (w : ℕ → M) :
    ∑ p ∈ cellSet a b F, w (p.1 * b - a * p.2) = ∑ g ∈ F, w g := by
  refine Finset.sum_bij (fun p _ => p.1 * b - a * p.2) ?_ ?_ ?_ fun p _ => rfl
  · intro p hp
    simp only [cellSet, mem_filter, mem_product, mem_Ico, mem_Icc] at hp
    exact hp.2.2
  · intro p hp p' hp' heq
    simp only [cellSet, mem_filter, mem_product, mem_Ico, mem_Icc] at hp hp'
    obtain ⟨hrr, hii⟩ := rep_unique hco hp.1.1.2 hp'.1.1.2
      (show a * p.2 + (p.1 * b - a * p.2) = p.1 * b by omega)
      (show a * p'.2 + (p.1 * b - a * p.2) = p'.1 * b by rw [heq]; omega)
    exact Prod.ext hrr hii
  · intro g hg
    obtain ⟨r, i, hr, hi1, hib, hlt, rfl⟩ := exists_rep_of_mem_gaps hco ha (hF hg)
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | h
      · omega
      · exact h
    have hmem : (r, i) ∈ cellSet a b F := by
      simp only [cellSet, mem_filter, mem_product, mem_Ico, mem_Icc]
      exact ⟨⟨⟨hr1, hr⟩, hi1, hib⟩, hlt, hg⟩
    exact ⟨(r, i), hmem, rfl⟩

/-- Splitting the cells of a set of gaps by column. -/
theorem sum_cellSet_col {M : Type*} [AddCommMonoid M] (a b : ℕ) (F : Finset ℕ) (v : ℕ → ℕ → M) :
    ∑ p ∈ cellSet a b F, v p.1 p.2
      = ∑ r ∈ Ico 1 a, ∑ i ∈ {i ∈ Icc 1 b | a * i < r * b ∧ r * b - a * i ∈ F}, v r i := by
  rw [cellSet, Finset.sum_filter, Finset.sum_product]
  exact sum_congr rfl fun r _ => (Finset.sum_filter _ _).symm

/-- Splitting the cells of a set of gaps by row. -/
theorem sum_cellSet_row {M : Type*} [AddCommMonoid M] (a b : ℕ) (F : Finset ℕ) (v : ℕ → ℕ → M) :
    ∑ p ∈ cellSet a b F, v p.1 p.2
      = ∑ i ∈ Icc 1 b, ∑ r ∈ {r ∈ Ico 1 a | a * i < r * b ∧ r * b - a * i ∈ F}, v r i := by
  rw [cellSet, Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
  exact sum_congr rfl fun i _ => (Finset.sum_filter _ _).symm

/-- Telescoping a column: the cells of a filter in column `r` move the east-step start of that
column from `br` down to the rank of the topmost cell. -/
theorem sum_col_telescope {M : Type*} [AddCommGroup M] {a b : ℕ} (hco : a.Coprime b)
    {F : Finset ℕ} (hF : Gaps.IsOrderFilter a b F) {r : ℕ} (hra : r < a) (w : ℤ → M) :
    ∑ i ∈ Icc 1 (Primitive.primitiveHeight a b F r),
        (w ((r * b - a * i : ℕ) : ℤ) - w (((r * b - a * i : ℕ) : ℤ) + a))
      = w (eastRank (Primitive.primitivePath a b F) r) - w ((b : ℤ) * r) := by
  rw [show Icc 1 (Primitive.primitiveHeight a b F r)
        = Ico 1 (Primitive.primitiveHeight a b F r + 1) from by ext i; simp,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  have key : ∀ j ∈ range (Primitive.primitiveHeight a b F r),
      w ((r * b - a * (1 + j) : ℕ) : ℤ) - w (((r * b - a * (1 + j) : ℕ) : ℤ) + a)
        = (fun k : ℕ => w ((r : ℤ) * b - a * k)) (j + 1)
          - (fun k : ℕ => w ((r : ℤ) * b - a * k)) j := by
    intro j hj
    rw [mem_range] at hj
    have hle : a * (1 + j) ≤ r * b :=
      le_of_lt ((le_primitiveHeight_iff hco hF hra (by omega)).mp (by omega)).2.1
    rw [show ((r * b - a * (1 + j) : ℕ) : ℤ) = (r : ℤ) * b - a * ((j : ℤ) + 1) from by
        rw [Nat.cast_sub hle]; push_cast; ring,
      show (r : ℤ) * b - a * ((j : ℤ) + 1) + a = (r : ℤ) * b - a * (j : ℤ) from by ring]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl key,
    Finset.sum_range_sub (fun k : ℕ => w ((r : ℤ) * b - (a : ℤ) * k)), eastRank,
    Primitive.ht_primitivePath_of_lt F hra]
  push_cast
  ring_nf

/-- In an order filter the columns whose cells meet a given row form the interval from the first
column reaching that row to the right end of the block. -/
theorem row_eq_Ico {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) {F : Finset ℕ}
    (hF : Gaps.IsOrderFilter a b F) {i : ℕ} (hi1 : 1 ≤ i) (hib : i ≤ b) :
    {r ∈ Ico 1 a | a * i < r * b ∧ r * b - a * i ∈ F}
      = Ico (Paths.firstReach (Primitive.primitivePath a b F) i) a := by
  have ha0 : 0 < a := by omega
  have hbd := isBelowDiagonal_primitivePath hco ha0 hF
  have hend : Paths.ht (Primitive.primitivePath a b F) (a * 1) = b * 1 := hbd.2.1
  have hreach : i ≤ Paths.ht (Primitive.primitivePath a b F)
      (Paths.firstReach (Primitive.primitivePath a b F) i) :=
    le_ht_firstReach _ (by rw [hend]; omega)
  have hAa : Paths.firstReach (Primitive.primitivePath a b F) i ≤ a := by
    have := firstReach_lt (Primitive.primitivePath a b F) i
    omega
  ext r
  simp only [mem_filter, mem_Ico]
  constructor
  · rintro ⟨⟨hr1, hra⟩, hlt, hmem⟩
    have hht : i ≤ Paths.ht (Primitive.primitivePath a b F) r := by
      rw [Primitive.ht_primitivePath_of_lt F hra]
      exact (le_primitiveHeight_iff hco hF hra hi1).mpr ⟨hib, hlt, hmem⟩
    exact ⟨firstReach_le _ (by omega) hht, hra⟩
  · rintro ⟨hAr, hra⟩
    have hht : i ≤ Paths.ht (Primitive.primitivePath a b F) r :=
      hreach.trans (ht_mono hbd hAr (by omega))
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | h
      · rw [Primitive.ht_primitivePath_zero F ha0] at hht
        omega
      · exact h
    rw [Primitive.ht_primitivePath_of_lt F hra] at hht
    obtain ⟨-, hlt, hmem⟩ := (le_primitiveHeight_iff hco hF hra hi1).mp hht
    exact ⟨⟨hr1, hra⟩, hlt, hmem⟩

/-- Telescoping a row: the cells of a filter in row `i` move the north-step end of that row from
`a(b - i)` down to the rank of the leftmost cell. -/
theorem sum_row_telescope {M : Type*} [AddCommGroup M] {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a)
    {F : Finset ℕ} (hF : Gaps.IsOrderFilter a b F) {i : ℕ} (hi1 : 1 ≤ i) (hib : i ≤ b)
    (w : ℤ → M) :
    ∑ r ∈ {r ∈ Ico 1 a | a * i < r * b ∧ r * b - a * i ∈ F},
        (w ((r * b - a * i : ℕ) : ℤ) - w (((r * b - a * i : ℕ) : ℤ) + b))
      = w (northRank (Primitive.primitivePath a b F) i) - w ((a : ℤ) * ((b : ℤ) - i)) := by
  have hrow := row_eq_Ico hco ha hF hi1 hib
  have hAa : Paths.firstReach (Primitive.primitivePath a b F) i ≤ a := by
    have := firstReach_lt (Primitive.primitivePath a b F) i
    omega
  rw [hrow, Finset.sum_Ico_eq_sum_range]
  have key : ∀ j ∈ range (a - Paths.firstReach (Primitive.primitivePath a b F) i),
      (fun r : ℕ => w ((r * b - a * i : ℕ) : ℤ) - w (((r * b - a * i : ℕ) : ℤ) + b))
          (Paths.firstReach (Primitive.primitivePath a b F) i + j)
        = (fun k : ℕ =>
              w (((Paths.firstReach (Primitive.primitivePath a b F) i + k : ℕ) : ℤ) * b
                - (a : ℤ) * i)) j
          - (fun k : ℕ =>
              w (((Paths.firstReach (Primitive.primitivePath a b F) i + k : ℕ) : ℤ) * b
                - (a : ℤ) * i)) (j + 1) := by
    intro j hj
    rw [mem_range] at hj
    have hmemr : Paths.firstReach (Primitive.primitivePath a b F) i + j
        ∈ {r ∈ Ico 1 a | a * i < r * b ∧ r * b - a * i ∈ F} := by
      rw [hrow, mem_Ico]
      omega
    rw [mem_filter] at hmemr
    have hle : a * i ≤ (Paths.firstReach (Primitive.primitivePath a b F) i + j) * b :=
      le_of_lt hmemr.2.1
    simp only
    rw [Nat.cast_sub hle]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub' (fun k : ℕ =>
      w (((Paths.firstReach (Primitive.primitivePath a b F) i + k : ℕ) : ℤ) * b - (a : ℤ) * i)),
    northRank]
  simp only [Nat.add_zero, Nat.add_sub_cancel' hAa]
  ring_nf

/-- The east-step ranks of a primitive block: the baseline `b k`, corrected by one telescoping
term per cell of the filter, which moves an east start from `g + a` down to `g`. -/
theorem sum_eastRank_primitivePath {M : Type*} [AddCommGroup M] {a b : ℕ} (hco : a.Coprime b)
    (ha : 1 < a) {F : Finset ℕ} (hF : Gaps.IsOrderFilter a b F) (w : ℤ → M) :
    ∑ r ∈ range a, w (eastRank (Primitive.primitivePath a b F) r)
      = ∑ k ∈ range a, w ((b : ℤ) * k) + ∑ g ∈ F, (w (g : ℤ) - w ((g : ℤ) + a)) := by
  have h1 : ∑ p ∈ cellSet a b F,
      (w ((p.1 * b - a * p.2 : ℕ) : ℤ) - w (((p.1 * b - a * p.2 : ℕ) : ℤ) + (a : ℤ)))
        = ∑ g ∈ F, (w (g : ℤ) - w ((g : ℤ) + a)) :=
    sum_cellSet hco ha hF.1 fun g : ℕ => w (g : ℤ) - w ((g : ℤ) + (a : ℤ))
  have h2 : ∑ p ∈ cellSet a b F,
      (w ((p.1 * b - a * p.2 : ℕ) : ℤ) - w (((p.1 * b - a * p.2 : ℕ) : ℤ) + (a : ℤ)))
        = ∑ r ∈ Ico 1 a, ∑ i ∈ {i ∈ Icc 1 b | a * i < r * b ∧ r * b - a * i ∈ F},
            (w ((r * b - a * i : ℕ) : ℤ) - w (((r * b - a * i : ℕ) : ℤ) + (a : ℤ))) :=
    sum_cellSet_col a b F fun r i : ℕ =>
      w ((r * b - a * i : ℕ) : ℤ) - w (((r * b - a * i : ℕ) : ℤ) + (a : ℤ))
  have h3 : ∑ r ∈ Ico 1 a, (w (eastRank (Primitive.primitivePath a b F) r) - w ((b : ℤ) * r))
      = ∑ g ∈ F, (w (g : ℤ) - w ((g : ℤ) + a)) := by
    rw [← h1, h2]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [mem_Ico] at hr
    rw [primitiveHeight_column hco hF hr.2]
    exact (sum_col_telescope hco hF hr.2 w).symm
  have hzero : w (eastRank (Primitive.primitivePath a b F) 0) - w ((b : ℤ) * 0) = 0 := by
    rw [eastRank, Primitive.ht_primitivePath_zero F (by omega : 0 < a)]
    norm_num
  have h4 : ∑ r ∈ range a, (w (eastRank (Primitive.primitivePath a b F) r) - w ((b : ℤ) * r))
      = ∑ g ∈ F, (w (g : ℤ) - w ((g : ℤ) + a)) := by
    rw [← h3]
    refine (Finset.sum_subset (fun r hr => ?_) fun r _ hr => ?_).symm
    · rw [mem_Ico] at hr
      exact mem_range.mpr hr.2
    · rw [mem_Ico] at hr
      have : r = 0 := by
        rcases Nat.eq_zero_or_pos r with h | h
        · exact h
        · exact absurd ⟨h, mem_range.mp ‹r ∈ range a›⟩ hr
      rw [this]
      exact hzero
  rw [← h4, Finset.sum_sub_distrib]
  abel

/-- The north-step ranks of a primitive block: the baseline `a(b - i)`, corrected by one
telescoping term per cell of the filter, which moves a north end from `g + b` down to `g`. -/
theorem sum_northRank_primitivePath {M : Type*} [AddCommGroup M] {a b : ℕ} (hco : a.Coprime b)
    (ha : 1 < a) {F : Finset ℕ} (hF : Gaps.IsOrderFilter a b F) (w : ℤ → M) :
    ∑ i ∈ Icc 1 b, w (northRank (Primitive.primitivePath a b F) i)
      = ∑ i ∈ Icc 1 b, w ((a : ℤ) * ((b : ℤ) - i)) + ∑ g ∈ F, (w (g : ℤ) - w ((g : ℤ) + b)) := by
  have h1 : ∑ p ∈ cellSet a b F,
      (w ((p.1 * b - a * p.2 : ℕ) : ℤ) - w (((p.1 * b - a * p.2 : ℕ) : ℤ) + (b : ℤ)))
        = ∑ g ∈ F, (w (g : ℤ) - w ((g : ℤ) + b)) :=
    sum_cellSet hco ha hF.1 fun g : ℕ => w (g : ℤ) - w ((g : ℤ) + (b : ℤ))
  have h2 : ∑ p ∈ cellSet a b F,
      (w ((p.1 * b - a * p.2 : ℕ) : ℤ) - w (((p.1 * b - a * p.2 : ℕ) : ℤ) + (b : ℤ)))
        = ∑ i ∈ Icc 1 b, ∑ r ∈ {r ∈ Ico 1 a | a * i < r * b ∧ r * b - a * i ∈ F},
            (w ((r * b - a * i : ℕ) : ℤ) - w (((r * b - a * i : ℕ) : ℤ) + (b : ℤ))) :=
    sum_cellSet_row a b F fun r i : ℕ =>
      w ((r * b - a * i : ℕ) : ℤ) - w (((r * b - a * i : ℕ) : ℤ) + (b : ℤ))
  have h3 : ∑ i ∈ Icc 1 b, (w (northRank (Primitive.primitivePath a b F) i)
        - w ((a : ℤ) * ((b : ℤ) - i))) = ∑ g ∈ F, (w (g : ℤ) - w ((g : ℤ) + b)) := by
    rw [← h1, h2]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_Icc] at hi
    exact (sum_row_telescope hco ha hF hi.1 hi.2 w).symm
  rw [← h3, Finset.sum_sub_distrib]
  abel

/-! ### The interval test on rank differences -/

/-- The interval test `-b < t ≤ a` on a rank difference, as a `0`/`1` integer. -/
def rankWeight (a b : ℕ) (t : ℤ) : ℤ := if -(b : ℤ) < t ∧ t ≤ (a : ℤ) then 1 else 0

/-- The four-corner kernel of the cross-block count: the second difference of the interval test
in the two step directions. -/
def crossKernel (a b : ℕ) (t : ℤ) : ℤ :=
  rankWeight a b t - rankWeight a b (t + a) - rankWeight a b (t - b) + rankWeight a b (t + a - b)

/-- Telescoping an arithmetic progression of arguments, upward. -/
theorem sum_range_shift_sub {M : Type*} [AddCommGroup M] (w : ℤ → M) (c s : ℤ) (n : ℕ) :
    ∑ j ∈ range n, (w (c + s * ((j : ℤ) + 1)) - w (c + s * (j : ℤ))) = w (c + s * n) - w c := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    abel

/-- Telescoping an arithmetic progression of arguments, downward. -/
theorem sum_range_shift_sub' {M : Type*} [AddCommGroup M] (w : ℤ → M) (c s : ℤ) (n : ℕ) :
    ∑ j ∈ range n, (w (c + s * (j : ℤ)) - w (c + s * ((j : ℤ) + 1))) = w c - w (c + s * n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    abel

/-- The cross-block count as a double sum of interval tests over the north-step ranks of the
earlier block and the east-step ranks of the later one. -/
theorem crossCount_eq_sum {a b : ℕ} (z w : Paths.Heights a b 1) :
    (crossCount z w : ℤ)
      = ∑ i ∈ Icc 1 b, ∑ r ∈ range a, rankWeight a b (eastRank w r - northRank z i) := by
  rw [crossCount, Finset.card_filter, Nat.cast_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
  rw [rankWeight]
  split <;> simp

/-- The baseline of the cross-block count: two empty-filter blocks share `d - 1` hooks. -/
theorem sum_rankWeight_baseline {a b : ℕ} (hco : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    ∑ i ∈ Icc 1 b, ∑ k ∈ range a, rankWeight a b ((b : ℤ) * k - (a : ℤ) * ((b : ℤ) - i))
      = (a : ℤ) + b - 1 := by
  have h : (#{p ∈ Icc 1 b ×ˢ range a | -(b : ℤ) < (a : ℤ) * p.1 - (b : ℤ) * ((a : ℤ) - p.2) ∧
      (a : ℤ) * p.1 - (b : ℤ) * ((a : ℤ) - p.2) ≤ (a : ℤ)} : ℤ) = (a : ℤ) + b - 1 := by
    rw [card_rank_pairs a b hco ha hb, Nat.cast_sub (by omega : 1 ≤ a + b)]
    push_cast
    ring
  rw [← h, Finset.card_filter, Nat.cast_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [rankWeight, show (b : ℤ) * k - (a : ℤ) * ((b : ℤ) - i)
    = (a : ℤ) * i - (b : ℤ) * ((a : ℤ) - k) from by ring]
  split <;> simp

/-- The interval test telescopes to zero along the north-step baseline: a gap of the later block
makes no linear contribution to the cross-block count. -/
theorem sum_rankWeight_north {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) {h : ℕ}
    (hh : h ∈ (finspan {a, b}).gaps) :
    ∑ i ∈ Icc 1 b, (rankWeight a b ((h : ℤ) - (a : ℤ) * ((b : ℤ) - i))
      - rankWeight a b ((h : ℤ) + a - (a : ℤ) * ((b : ℤ) - i))) = 0 := by
  have hh1 : 1 ≤ h := one_le_of_mem_gaps hh
  have hhf : h + a + b ≤ a * b := add_le_of_mem_gaps hco ha hh
  have hcast : ((h : ℤ) + a + b ≤ (a : ℤ) * b) := by exact_mod_cast hhf
  have hh1' : (1 : ℤ) ≤ h := by exact_mod_cast hh1
  rw [show Icc 1 b = Ico 1 (b + 1) from by ext i; simp, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  have key : ∀ j ∈ range b,
      rankWeight a b ((h : ℤ) - (a : ℤ) * ((b : ℤ) - ((1 + j : ℕ) : ℤ)))
          - rankWeight a b ((h : ℤ) + a - (a : ℤ) * ((b : ℤ) - ((1 + j : ℕ) : ℤ)))
        = (fun t : ℤ => rankWeight a b t) ((h : ℤ) + a - (a : ℤ) * b + (a : ℤ) * (j : ℤ))
          - (fun t : ℤ => rankWeight a b t)
              ((h : ℤ) + a - (a : ℤ) * b + (a : ℤ) * ((j : ℤ) + 1)) := by
    intro j _
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl key,
    sum_range_shift_sub' (fun t : ℤ => rankWeight a b t)
      ((h : ℤ) + a - (a : ℤ) * b) (a : ℤ) b]
  have e1 : rankWeight a b ((h : ℤ) + a - (a : ℤ) * b) = 0 := by
    rw [rankWeight, ite_eq_right (by intro hcon; omega)]
  have e2 : rankWeight a b ((h : ℤ) + a - (a : ℤ) * b + (a : ℤ) * b) = 0 := by
    rw [rankWeight, ite_eq_right (by intro hcon; omega)]
  rw [e1, e2, sub_zero]

/-- The interval test telescopes along the east-step baseline to the indicator of the Frobenius
gap: that is the only gap of the earlier block making a linear contribution. -/
theorem sum_rankWeight_east {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) {g : ℕ}
    (hg : g ∈ (finspan {a, b}).gaps) :
    ∑ k ∈ range a, rankWeight a b ((b : ℤ) * k - g)
        - ∑ k ∈ range a, rankWeight a b ((b : ℤ) * k - ((g : ℤ) + b))
      = if g + a + b = a * b then 1 else 0 := by
  have hg1 : 1 ≤ g := one_le_of_mem_gaps hg
  have hgf : g + a + b ≤ a * b := add_le_of_mem_gaps hco ha hg
  have hcast : ((g : ℤ) + a + b ≤ (a : ℤ) * b) := by exact_mod_cast hgf
  have hg1' : (1 : ℤ) ≤ g := by exact_mod_cast hg1
  have hcomm : (b : ℤ) * (a : ℤ) = (a : ℤ) * (b : ℤ) := by ring
  rw [← Finset.sum_sub_distrib]
  have key : ∀ k ∈ range a,
      rankWeight a b ((b : ℤ) * k - g) - rankWeight a b ((b : ℤ) * k - ((g : ℤ) + b))
        = (fun t : ℤ => rankWeight a b t)
              (-(g : ℤ) - b + (b : ℤ) * ((k : ℤ) + 1))
          - (fun t : ℤ => rankWeight a b t) (-(g : ℤ) - b + (b : ℤ) * (k : ℤ)) := by
    intro k _
    ring_nf
  rw [Finset.sum_congr rfl key,
    sum_range_shift_sub (fun t : ℤ => rankWeight a b t) (-(g : ℤ) - b) (b : ℤ) a]
  have e1 : rankWeight a b (-(g : ℤ) - b) = 0 := by
    rw [rankWeight, ite_eq_right (by intro hcon; omega)]
  rw [e1, sub_zero, rankWeight]
  by_cases hfrob : g + a + b = a * b
  · have hfrob' : (g : ℤ) + a + b = (a : ℤ) * b := by exact_mod_cast hfrob
    rw [ite_eq_left (by constructor <;> omega), ite_eq_left hfrob]
  · have hfrob' : (g : ℤ) + a + b ≠ (a : ℤ) * b := by
      intro hcon
      exact hfrob (by exact_mod_cast hcon)
    rw [ite_eq_right (by intro hcon; omega), ite_eq_right hfrob]

/-- The bilinear part of the cross-block count, collected gap by gap of the later block. -/
theorem sum_crossKernel {a b : ℕ} (H : Finset ℕ) (g : ℕ) :
    ∑ h ∈ H, (rankWeight a b ((h : ℤ) - g) - rankWeight a b ((h : ℤ) + a - g))
        - ∑ h ∈ H, (rankWeight a b ((h : ℤ) - ((g : ℤ) + b))
          - rankWeight a b ((h : ℤ) + a - ((g : ℤ) + b)))
      = ∑ h ∈ H, crossKernel a b ((h : ℤ) - g) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [crossKernel, show (h : ℤ) - g + a = (h : ℤ) + a - g from by ring,
    show (h : ℤ) - g - b = (h : ℤ) - ((g : ℤ) + b) from by ring,
    show (h : ℤ) + a - g - b = (h : ℤ) + a - ((g : ℤ) + b) from by ring]
  ring

/-- The cross-block count of the primitive blocks of two order filters: the universal baseline
`d - 1`, an ordered constant detecting the Frobenius gap in the earlier filter, and a bilinear
kernel term over the pairs of gaps. -/
theorem crossCount_primitivePath_eq {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a)
    {F H : Finset ℕ} (hF : Gaps.IsOrderFilter a b F) (hH : Gaps.IsOrderFilter a b H) :
    (crossCount (Primitive.primitivePath a b F) (Primitive.primitivePath a b H) : ℤ)
      = ((a : ℤ) + b - 1) + ((if Gaps.frobeniusGap a b ∈ F then 1 else 0)
        + ∑ g ∈ F, ∑ h ∈ H, crossKernel a b ((h : ℤ) - g)) := by
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [Nat.Coprime, Nat.gcd_zero_right] at hco
      omega
    · exact hb
  have step2 : ∀ ρ : ℤ, ∑ r ∈ range a,
        rankWeight a b (eastRank (Primitive.primitivePath a b H) r - ρ)
      = ∑ k ∈ range a, rankWeight a b ((b : ℤ) * k - ρ)
        + ∑ h ∈ H, (rankWeight a b ((h : ℤ) - ρ) - rankWeight a b ((h : ℤ) + a - ρ)) :=
    fun ρ => sum_eastRank_primitivePath hco ha hH fun t => rankWeight a b (t - ρ)
  have step1 : ∑ i ∈ Icc 1 b, ∑ r ∈ range a,
        rankWeight a b (eastRank (Primitive.primitivePath a b H) r
          - northRank (Primitive.primitivePath a b F) i)
      = ∑ i ∈ Icc 1 b, ∑ r ∈ range a,
          rankWeight a b (eastRank (Primitive.primitivePath a b H) r - (a : ℤ) * ((b : ℤ) - i))
        + ∑ g ∈ F, ((∑ r ∈ range a,
              rankWeight a b (eastRank (Primitive.primitivePath a b H) r - (g : ℤ)))
            - ∑ r ∈ range a,
              rankWeight a b (eastRank (Primitive.primitivePath a b H) r - ((g : ℤ) + b))) :=
    sum_northRank_primitivePath hco ha hF fun ρ =>
      ∑ r ∈ range a, rankWeight a b (eastRank (Primitive.primitivePath a b H) r - ρ)
  have hfirst : ∑ i ∈ Icc 1 b, ∑ r ∈ range a,
        rankWeight a b (eastRank (Primitive.primitivePath a b H) r - (a : ℤ) * ((b : ℤ) - i))
      = (a : ℤ) + b - 1 := by
    refine Eq.trans (Finset.sum_congr rfl fun i _ => step2 ((a : ℤ) * ((b : ℤ) - (i : ℤ)))) ?_
    have hzero : ∑ h ∈ H, ∑ i ∈ Icc 1 b,
        (rankWeight a b ((h : ℤ) - (a : ℤ) * ((b : ℤ) - i))
          - rankWeight a b ((h : ℤ) + a - (a : ℤ) * ((b : ℤ) - i))) = 0 :=
      Finset.sum_eq_zero fun h hh => sum_rankWeight_north hco ha (hH.1 hh)
    rw [Finset.sum_add_distrib, sum_rankWeight_baseline hco (by omega) hb, Finset.sum_comm, hzero,
      add_zero]
  have hsecond : ∑ g ∈ F, ((∑ r ∈ range a,
          rankWeight a b (eastRank (Primitive.primitivePath a b H) r - (g : ℤ)))
        - ∑ r ∈ range a,
          rankWeight a b (eastRank (Primitive.primitivePath a b H) r - ((g : ℤ) + b)))
      = (if Gaps.frobeniusGap a b ∈ F then 1 else 0)
        + ∑ g ∈ F, ∑ h ∈ H, crossKernel a b ((h : ℤ) - g) := by
    have hstep : ∀ g ∈ F, ((∑ r ∈ range a,
            rankWeight a b (eastRank (Primitive.primitivePath a b H) r - (g : ℤ)))
          - ∑ r ∈ range a,
            rankWeight a b (eastRank (Primitive.primitivePath a b H) r - ((g : ℤ) + b)))
        = (if g = Gaps.frobeniusGap a b then 1 else 0)
          + ∑ h ∈ H, crossKernel a b ((h : ℤ) - g) := by
      intro g hg
      have hgb := add_le_of_mem_gaps hco ha (hF.1 hg)
      rw [step2 (g : ℤ), step2 ((g : ℤ) + b), ← sum_crossKernel H g,
        show (if g = Gaps.frobeniusGap a b then (1 : ℤ) else 0)
          = if g + a + b = a * b then 1 else 0 from
          if_congr (by rw [Gaps.frobeniusGap]; omega) rfl rfl,
        ← sum_rankWeight_east hco ha (hF.1 hg)]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
      Finset.sum_ite_eq' F (Gaps.frobeniusGap a b) fun _ => (1 : ℤ)]
  rw [crossCount_eq_sum, step1, hfirst, hsecond]

/-! ### Polarising the quadratic form -/

/-- A sum over the gap type is a sum over the gap set. -/
theorem sum_gaps_type (a b : ℕ) (f : ℕ → ℤ) :
    ∑ g : (finspan {a, b}).gaps, f (g : ℕ) = ∑ g ∈ (finspan {a, b}).gaps, f g :=
  (Finset.sum_subtype _ (fun _ => Iff.rfl) f).symm

/-- An indicator of a set of gaps restricts a sum over the gap type to that set. -/
theorem sum_gaps_indicator {a b : ℕ} {S : Finset ℕ} (hS : S ⊆ (finspan {a, b}).gaps)
    (f : ℕ → ℤ) :
    ∑ g : (finspan {a, b}).gaps, (if (g : ℕ) ∈ S then (1 : ℤ) else 0) * f (g : ℕ)
      = ∑ g ∈ S, f g := by
  rw [sum_gaps_type a b fun g => (if g ∈ S then (1 : ℤ) else 0) * f g]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hS]

/-- The polarisation of the quadratic form: its cross term on two gap vectors. -/
def polarQ (a b : ℕ) (m n : (finspan {a, b}).gaps → ℤ) : ℤ :=
  ∑ g : (finspan {a, b}).gaps, ∑ h : (finspan {a, b}).gaps,
    HJO.U a b ((h : ℕ) - (g : ℕ)) * (m g * n h + n g * m h)

/-- The quadratic form is the quadratic form of its polarisation: adding two gap vectors adds the
values and the cross term. -/
theorem polar_q_eq {a b : ℕ} (m n : (finspan {a, b}).gaps → ℤ) :
    QuadraticMap.polar' (HJO.Q a b) m n = polarQ a b m n := by
  rw [QuadraticMap.polar', Gaps.q_eq_sum_sum, Gaps.q_eq_sum_sum, Gaps.q_eq_sum_sum, polarQ,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Pi.add_apply]
  ring

/-- The cross term of the quadratic form on two filter indicators, as a sum over pairs of gaps of
the two filters. -/
theorem polarQ_filterVector {a b : ℕ} {F H : Finset ℕ} (hF : F ⊆ (finspan {a, b}).gaps)
    (hH : H ⊆ (finspan {a, b}).gaps) :
    polarQ a b (filterVector a b F) (filterVector a b H)
      = ∑ g ∈ F, ∑ h ∈ H, (HJO.U a b ((h : ℤ) - g) + HJO.U a b ((g : ℤ) - h)) := by
  rw [polarQ]
  have hsplit : ∀ g : (finspan {a, b}).gaps,
      ∑ h : (finspan {a, b}).gaps, HJO.U a b ((h : ℕ) - (g : ℕ))
          * (filterVector a b F g * filterVector a b H h
            + filterVector a b H g * filterVector a b F h)
        = filterVector a b F g * ∑ h ∈ H, HJO.U a b ((h : ℤ) - (g : ℕ))
          + filterVector a b H g * ∑ h ∈ F, HJO.U a b ((h : ℤ) - (g : ℕ)) := by
    intro g
    rw [Finset.mul_sum, Finset.mul_sum, ← sum_gaps_indicator hH
        (fun h => filterVector a b F g * HJO.U a b ((h : ℤ) - (g : ℕ))),
      ← sum_gaps_indicator hF (fun h => filterVector a b H g * HJO.U a b ((h : ℤ) - (g : ℕ))),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [filterVector]
    ring
  have hswap : ∑ g ∈ H, ∑ h ∈ F, HJO.U a b ((h : ℤ) - g)
      = ∑ g ∈ F, ∑ h ∈ H, HJO.U a b ((g : ℤ) - h) := Finset.sum_comm
  rw [Finset.sum_congr rfl fun g _ => hsplit g, Finset.sum_add_distrib]
  simp only [filterVector]
  rw [sum_gaps_indicator hF (fun g => ∑ h ∈ H, HJO.U a b ((h : ℤ) - g)),
    sum_gaps_indicator hH (fun g => ∑ h ∈ F, HJO.U a b ((h : ℤ) - g)), hswap,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_add_distrib.symm

/-! ### The hook count of a word of filters -/

/-- The ordered part of the interaction of two order filters: what the cross-block count of their
primitive blocks contributes beyond the baseline and the symmetric polarisation. -/
def orderedPart (a b : ℕ) (F H : Finset ℕ) : ℤ :=
  (if Gaps.frobeniusGap a b ∈ F then 1 else 0)
    + ∑ g ∈ F, ∑ h ∈ H, (crossKernel a b ((h : ℤ) - g)
        - HJO.U a b ((h : ℤ) - g) - HJO.U a b ((g : ℤ) - h))

/-- The cross-block count of two primitive blocks separates into the baseline `d - 1`, the
symmetric cross term of the quadratic form, and the ordered part. -/
theorem crossCount_eq_polar {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a)
    {F H : Finset ℕ} (hF : Gaps.IsOrderFilter a b F) (hH : Gaps.IsOrderFilter a b H) :
    (crossCount (Primitive.primitivePath a b F) (Primitive.primitivePath a b H) : ℤ)
      = ((a : ℤ) + b - 1) + polarQ a b (filterVector a b F) (filterVector a b H)
        + orderedPart a b F H := by
  have hcomb : ∑ g ∈ F, ∑ h ∈ H, (HJO.U a b ((h : ℤ) - g) + HJO.U a b ((g : ℤ) - h))
      + ∑ g ∈ F, ∑ h ∈ H, (crossKernel a b ((h : ℤ) - g)
          - HJO.U a b ((h : ℤ) - g) - HJO.U a b ((g : ℤ) - h))
      = ∑ g ∈ F, ∑ h ∈ H, crossKernel a b ((h : ℤ) - g) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  rw [crossCount_primitivePath_eq hco ha hF hH, polarQ_filterVector hF.1 hH.1, orderedPart,
    ← hcomb]
  ring

/-- Splitting a sum over ordered pairs of block positions into the diagonal terms and the strictly
increasing pairs. -/
theorem sum_prod_split {M : Type*} [AddCommMonoid M] {N : ℕ} (A : Fin N → M)
    (B : Fin N → Fin N → M) :
    ∑ x : Fin N × Fin N,
        (if x.1 = x.2 then A x.1 else if (x.1 : ℕ) < (x.2 : ℕ) then B x.1 x.2 else 0)
      = ∑ p : Fin N, A p
        + ∑ p : Fin N, ∑ r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val}, B p r := by
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  dsimp only
  have hsplit : ∀ r : Fin N,
      (if p = r then A p else if (p : ℕ) < (r : ℕ) then B p r else 0)
        = (if p = r then A p else 0) + (if (p : ℕ) < (r : ℕ) then B p r else 0) := by
    intro r
    by_cases h : p = r
    · subst h
      simp
    · simp [h]
  rw [Finset.sum_congr rfl fun r _ => hsplit r, Finset.sum_add_distrib, Finset.sum_filter,
    Finset.sum_ite_eq univ p fun _ => A p]
  simp

/-- Counting the ordered pairs of distinct block positions one position at a time. -/
theorem sum_card_pairs_lt (N : ℕ) :
    ∑ p : Fin N, #{r ∈ (univ : Finset (Fin N)) | p.val < r.val} = N.choose 2 := by
  rw [← card_pairs_lt N, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.card_filter]

/-- The weight of a word of order filters: the quadratic form at the summed indicator vector plus
one ordered interaction per ordered pair of positions. -/
def wordWeight (a b : ℕ) {N : ℕ} (F : Fin N → Finset ℕ) : ℤ :=
  HJO.Q a b (∑ p : Fin N, filterVector a b (F p))
    + ∑ p : Fin N, ∑ r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val},
        orderedPart a b (F p) (F r)

/-- The hook count of a concatenation of primitive blocks, taking Huang's rank-one evaluation as
an input: the block hook shift `κ_N` plus the weight of the word of filters. -/
theorem hookCount_concat_primitivePath_quadratic {a b N : ℕ} (hco : a.Coprime b) (ha : 1 < a)
    (hab : a < b) (rankOne : External.RankOneDinv) (F : Fin N → Finset ℕ)
    (hF : ∀ k, Gaps.IsOrderFilter a b (F k)) :
    (Paths.hookCount (concat fun k => Primitive.primitivePath a b (F k)) : ℤ)
      = Paths.kappaShift a b N + wordWeight a b F := by
  have hb : 0 < b := by omega
  rw [wordWeight, ← add_assoc]
  have hrank : ∀ G : Finset ℕ, Gaps.IsOrderFilter a b G →
      (Paths.hookCount (Primitive.primitivePath a b G) : ℤ) = HJO.Q a b (filterVector a b G) :=
    fun G hG => rankOne a b hco ha hab G hG
  have hQ : HJO.Q a b (∑ p : Fin N, filterVector a b (F p))
      = ∑ p : Fin N, HJO.Q a b (filterVector a b (F p))
        + ∑ p : Fin N, ∑ r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val},
            polarQ a b (filterVector a b (F p)) (filterVector a b (F r)) := by
    rw [QuadraticMap.map_sum_of_linearOrder (HJO.Q a b) (fun p => filterVector a b (F p)) univ]
    refine congrArg (∑ p : Fin N, HJO.Q a b (filterVector a b (F p)) + ·) ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show {r ∈ (univ : Finset (Fin N)) | p < r}
        = {r ∈ (univ : Finset (Fin N)) | p.val < r.val} from by
      exact Finset.filter_congr fun r _ => Fin.lt_def]
    exact Finset.sum_congr rfl fun r _ => polar_q_eq _ _
  have hkappa : (Paths.kappaShift a b N : ℤ)
      = ∑ _p : Fin N, ∑ _r ∈ {r ∈ (univ : Finset (Fin N)) | _p.val < r.val},
          ((a : ℤ) + b - 1) := by
    have h1 : ∀ p : Fin N,
        (∑ _r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val}, ((a : ℤ) + b - 1))
          = (#{r ∈ (univ : Finset (Fin N)) | p.val < r.val} : ℤ) * ((a : ℤ) + b - 1) :=
      fun p => by rw [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun p _ => h1 p, ← Finset.sum_mul, ← Nat.cast_sum, sum_card_pairs_lt,
      Paths.kappaShift, Nat.cast_mul, Nat.cast_sub (show 1 ≤ a + b by omega)]
    push_cast
    ring
  have hpair : ∀ p : Fin N, ∀ r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val},
      (crossCount (Primitive.primitivePath a b (F p))
          (Primitive.primitivePath a b (F r)) : ℤ)
        = ((a : ℤ) + b - 1) + polarQ a b (filterVector a b (F p)) (filterVector a b (F r))
          + orderedPart a b (F p) (F r) :=
    fun p r _ => crossCount_eq_polar hco ha (hF p) (hF r)
  have hsplit3 : ∀ p : Fin N,
      (∑ r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val},
          (((a : ℤ) + b - 1) + polarQ a b (filterVector a b (F p)) (filterVector a b (F r))
            + orderedPart a b (F p) (F r)))
        = (∑ _r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val}, ((a : ℤ) + b - 1))
          + (∑ r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val},
              polarQ a b (filterVector a b (F p)) (filterVector a b (F r)))
          + ∑ r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val},
              orderedPart a b (F p) (F r) :=
    fun p => by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hookCount_concat_primitivePath hco (by omega) hb hrank F hF,
    sum_prod_split (fun p => HJO.Q a b (filterVector a b (F p)))
      (fun p r => (crossCount (Primitive.primitivePath a b (F p))
        (Primitive.primitivePath a b (F r)) : ℤ)),
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl (hpair p),
    Finset.sum_congr rfl fun p _ => hsplit3 p, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hQ, hkappa]
  ring

/-- The generating function over return paths as a generating function over words of order
filters: the block factorisation reindexes the sum. -/
theorem sum_pow_hookCount_returnPath {a b N : ℕ} (hco : a.Coprime b) (ha : 1 < a)
    [Fintype {G : Finset ℕ // Gaps.IsOrderFilter a b G}] {R : Type*} [CommSemiring R] (x : R) :
    ∑ y ∈ {y ∈ (univ : Finset (Paths.Heights a b N)) | Paths.IsReturnPath y},
        x ^ Paths.hookCount y
      = ∑ F : Fin N → {G : Finset ℕ // Gaps.IsOrderFilter a b G},
          x ^ Paths.hookCount (concat fun k => Primitive.primitivePath a b (F k).1) := by
  rw [Finset.sum_subtype (p := Paths.IsReturnPath) _ (fun y => by simp)
    fun y => x ^ Paths.hookCount y]
  refine Fintype.sum_equiv (returnPathFilterEquiv hco ha) _ _ fun y => ?_
  refine congrArg (x ^ ·) (congrArg Paths.hookCount ?_)
  have hblock : (fun k => Primitive.primitivePath a b
      ((returnPathFilterEquiv hco ha y) k).1) = block y.1 :=
    funext fun k => primitivePath_pathFilter hco (isBelowDiagonal_block y.2 k)
  rw [hblock, concat_block (by omega) y.2]

/-! ### The kernel of the ordered interaction -/

/-- The `0`/`1` indicator of a half-line: the building block of both the interval test and the
kernel of the quadratic form. -/
def stepInd (c t : ℤ) : ℤ := if c ≤ t then 1 else 0

/-- Shifting the argument of a half-line indicator upward shifts its threshold downward. -/
theorem stepInd_add (c t s : ℤ) : stepInd c (t + s) = stepInd (c - s) t := by
  rw [stepInd, stepInd]
  split_ifs <;> omega

/-- Shifting the argument of a half-line indicator downward shifts its threshold upward. -/
theorem stepInd_sub (c t s : ℤ) : stepInd c (t - s) = stepInd (c + s) t := by
  rw [stepInd, stepInd]
  split_ifs <;> omega

/-- Negating the argument of a half-line indicator reflects the half-line. -/
theorem stepInd_neg (c t : ℤ) : stepInd c (-t) = 1 - stepInd (1 - c) t := by
  rw [stepInd, stepInd]
  split_ifs <;> omega

/-- The indicator of a point as a difference of two half-line indicators. -/
theorem stepInd_eq_point (c t : ℤ) :
    (if t = c then (1 : ℤ) else 0) = stepInd c t - stepInd (c + 1) t := by
  rw [stepInd, stepInd]
  split_ifs <;> omega

/-- The interval test as a difference of two half-line indicators. -/
theorem rankWeight_eq_stepInd (a b : ℕ) (t : ℤ) :
    rankWeight a b t = stepInd (1 - b) t - stepInd ((a : ℤ) + 1) t := by
  rw [rankWeight, stepInd, stepInd]
  split_ifs <;> omega

/-- The kernel of the quadratic form as a signed sum of half-line indicators. -/
theorem u_eq_stepInd (a b : ℕ) (s : ℤ) :
    HJO.U a b s = stepInd 0 s - stepInd a s - stepInd b s + stepInd ((a : ℤ) + b) s := by
  simp [Gaps.u_eq_kernel, stepInd]

/-- The four-corner kernel of the cross-block count in terms of the kernel of the quadratic
form. -/
theorem crossKernel_eq_u (a b : ℕ) (t : ℤ) :
    crossKernel a b t = HJO.U a b (t - 1) + HJO.U a b (-t) := by
  rw [crossKernel, u_eq_stepInd, u_eq_stepInd, rankWeight_eq_stepInd, rankWeight_eq_stepInd,
    rankWeight_eq_stepInd, rankWeight_eq_stepInd]
  simp only [stepInd_add, stepInd_sub, stepInd_neg]
  ring_nf

/-- What the four-corner kernel adds to the symmetric polarisation: a signed indicator of the four
unit shifts `0`, `a`, `b`, `d`. -/
theorem crossKernel_sub_u (a b : ℕ) (t : ℤ) :
    crossKernel a b t - HJO.U a b t - HJO.U a b (-t)
      = (if t = (a : ℤ) then 1 else 0) + (if t = (b : ℤ) then 1 else 0)
        - (if t = 0 then 1 else 0) - (if t = (a : ℤ) + b then 1 else 0) := by
  rw [crossKernel_eq_u, u_eq_stepInd a b (t - 1), u_eq_stepInd a b t, u_eq_stepInd a b (-t),
    stepInd_eq_point (a : ℤ) t, stepInd_eq_point (b : ℤ) t, stepInd_eq_point 0 t,
    stepInd_eq_point ((a : ℤ) + b) t]
  simp only [stepInd_sub]
  ring_nf

/-- The ordered part of the interaction of two order filters as a signed count of shifted gaps:
for each gap of the earlier filter, whether its `a`-, `b`- and `d`-shifts and itself lie in the
later one. -/
theorem orderedPart_eq (a b : ℕ) (F H : Finset ℕ) :
    orderedPart a b F H = (if Gaps.frobeniusGap a b ∈ F then 1 else 0)
      + ∑ g ∈ F, ((if g + a ∈ H then (1 : ℤ) else 0) + (if g + b ∈ H then 1 else 0)
        - (if g ∈ H then 1 else 0) - (if g + a + b ∈ H then 1 else 0)) := by
  rw [orderedPart]
  refine congrArg ((if Gaps.frobeniusGap a b ∈ F then (1 : ℤ) else 0) + ·) ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  have hpt : ∀ c : ℕ, ∑ h ∈ H, (if (h : ℤ) - g = (c : ℤ) then (1 : ℤ) else 0)
      = if g + c ∈ H then 1 else 0 := by
    intro c
    rw [← Finset.sum_ite_eq' H (g + c) fun _ => (1 : ℤ)]
    exact Finset.sum_congr rfl fun h _ => if_congr (by omega) rfl rfl
  have hstep : ∀ h ∈ H,
      crossKernel a b ((h : ℤ) - g) - HJO.U a b ((h : ℤ) - g) - HJO.U a b ((g : ℤ) - h)
        = (if (h : ℤ) - g = ((a : ℕ) : ℤ) then 1 else 0)
          + (if (h : ℤ) - g = ((b : ℕ) : ℤ) then 1 else 0)
          - (if (h : ℤ) - g = ((0 : ℕ) : ℤ) then 1 else 0)
          - (if (h : ℤ) - g = ((a + b : ℕ) : ℤ) then 1 else 0) := by
    intro h _
    rw [show (g : ℤ) - h = -((h : ℤ) - g) from by ring, crossKernel_sub_u]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hpt a, hpt b, hpt 0, hpt (a + b), Nat.add_zero, ← Nat.add_assoc]

end HJO.ReturnPath
