/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerCalculus
public meta import HJO.Attr

/-! # The loops against the words of arrows

Carlsson and Mellit move a loop past a word of arrows: a descending word of loops cycles the index
down by one, a raising arrow cycles it up, and a loop is *idle* on a long enough word of arrows in
either direction. This file proves those four moves.

## Main definitions

* `HJO.Dyck.Aq.dPlusPow`: the word `d₊^n e_0` of raising arrows from the vertex `0` to `n`.
* `HJO.Dyck.Aq.dMinusPow`: the word `d₋^m` of lowering arrows from the vertex `k + m` to `k`.

## Main results

* `HJO.Dyck.Aq.tSeg_mul_Tg_cycle`: `(T_r ⋯ T_1)T_j = T_{j-1}(T_r ⋯ T_1)` for `2 ≤ j ≤ r`.
* `HJO.Dyck.Aq.dPlus_mul_tSeg`: `d₊(T_r ⋯ T_1) = (T_{r+1} ⋯ T_2)d₊`.
* `HJO.Dyck.Aq.Tg_mul_dPlusPow`: `T_id₊^ne_0 = d₊^ne_0`.
* `HJO.Dyck.Aq.dMinusPow_mul_Tg`: `d₋^mT_j = d₋^m`.

## Implementation notes

The two words of arrows take the *empty product to be the idempotent* at the vertex where the word
ends, as the words of loops do: `dPlusPow 0 = e_0` and `dMinusPow k 0 = e_k`. `dPlusPow n` is
therefore Carlsson and Mellit's `d₊^ne_0` complete with its trailing idempotent, and no separate
`* e_0` is needed anywhere below.

The loop index is the shifted one, `Tg k i` being Carlsson and Mellit's `T_{i+1}` at the vertex `k`.
So their admissible range `k+1 ≤ j ≤ k+m-1` for `HJO.Dyck.Aq.dMinusPow_mul_Tg` reads `k ≤ i` and
`i + 2 ≤ k + m`, and its `1 ≤ i ≤ n-1` for `HJO.Dyck.Aq.Tg_mul_dPlusPow` reads `j + 2 ≤ n`. The
arithmetic of the vertex indices is discharged by `omega` through explicit rewrites rather than
left to defeq: `k + (p + 2)` and `k + p + 2` are equal but not syntactically so, and a `rw` that
silently fails to fire there is exactly how a formal proof goes wrong.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 3, the Dyck path algebra and the involution: Lemmas
`HJO.Dyck.Aq.tSeg_mul_Tg_cycle`, `HJO.Dyck.Aq.dPlus_mul_tSeg`, `HJO.Dyck.Aq.Tg_mul_dPlusPow` and
`HJO.Dyck.Aq.dMinusPow_mul_Tg`.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K}

/-! ### A loop past a descending word of loops -/

/-- A loop of index above the whole word commutes past it: every letter of `T_n ⋯ T_1` has index at
least two below `i`, so each commutes with `T_i` by the relation `T_iT_j = T_jT_i`. -/
theorem tSeg_comm_Tg {k i : ℕ} (hi : i + 2 ≤ k) :
    ∀ n : ℕ, n + 1 ≤ i → tSeg K q k 0 n * Tg K q k i = Tg K q k i * tSeg K q k 0 n := by
  intro n
  induction n with
  | zero => intro _; rw [tSeg_zero, e_mul_Tg, Tg_mul_e]
  | succ n ih =>
    intro hn
    rw [tSeg_succ, Nat.zero_add, mul_assoc, ih (by omega), ← mul_assoc, ← mul_assoc,
      Tg_comm (by omega) hi (by omega)]

/-- **The descending word cycles a loop's index down by one**: `(T_r ⋯ T_1)T_j = T_{j-1}(T_r ⋯ T_1)`
for `2 ≤ j ≤ r ≤ k-1`. In the shifted indexing Carlsson and Mellit's `T_j` is `Tg k (m+1)` and its
`T_{j-1}` is `Tg k m`, and `2 ≤ j ≤ r` reads `m + 2 ≤ r`. -/
@[hjo "lem_cm_braid_cycle"]
theorem tSeg_mul_Tg_cycle {k m : ℕ} :
    ∀ r : ℕ, r + 1 ≤ k → m + 2 ≤ r →
      tSeg K q k 0 r * Tg K q k (m + 1) = Tg K q k m * tSeg K q k 0 r := by
  intro r
  induction r with
  | zero => intro _ h; omega
  | succ n ih =>
    intro hr hm
    rw [tSeg_succ, Nat.zero_add]
    rcases Nat.lt_or_ge (m + 1) n with hcase | hcase
    · have hcomm : Tg K q k m * Tg K q k n = Tg K q k n * Tg K q k m :=
        Tg_comm (by omega) (by omega) (by omega)
      rw [mul_assoc, ih (by omega) (by omega), ← mul_assoc, ← mul_assoc, ← hcomm]
    · obtain rfl : n = m + 1 := by omega
      rw [tSeg_succ, Nat.zero_add, mul_assoc, mul_assoc, tSeg_comm_Tg (by omega) m (by omega),
        ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc,
        Tg_braid (by omega) (by omega) (Or.inl rfl), mul_assoc, mul_assoc]

/-! ### The raising arrow against a descending word of loops -/

/-- **The raising arrow cycles a descending word's indices up by one**:
`d₊(T_r ⋯ T_1) = (T_{r+1} ⋯ T_2)d₊`, the words being the idempotents when `r = 0`. In the shifted
indexing Carlsson and Mellit's `T_r ⋯ T_1` at the vertex `k` is `tSeg k 0 r` and its `T_{r+1} ⋯ T_2`
at the vertex `k + 1` is `tSeg (k+1) 1 r`. -/
@[hjo "lem_cm_dpa_dplus_cycle"]
theorem dPlus_mul_tSeg {k : ℕ} :
    ∀ r : ℕ, r + 1 ≤ k →
      dPlus K q k * tSeg K q k 0 r = tSeg K q (k + 1) 1 r * dPlus K q k := by
  intro r
  induction r with
  | zero => intro _; rw [tSeg_zero, tSeg_zero, dPlus_mul_e, e_mul_dPlus]
  | succ n ih =>
    intro hr
    rw [tSeg_succ, Nat.zero_add, tSeg_succ, ← mul_assoc, dPlus_mul_Tg (by omega), mul_assoc,
      ih (by omega), ← mul_assoc, show 1 + n = n + 1 from Nat.add_comm 1 n]

/-! ### A loop is idle on a long word of arrows -/

/-- The word `d₊^ne_0` of raising arrows from the vertex `0` to the vertex `n`, the empty word being
the idempotent `e_0`. -/
noncomputable def dPlusPow (K : Type*) [CommRing K] (q : K) : ℕ → Aq K q
  | 0 => e K q 0
  | n + 1 => dPlus K q n * dPlusPow K q n

theorem dPlusPow_succ (n : ℕ) :
    dPlusPow K q (n + 1) = dPlus K q n * dPlusPow K q n := rfl

/-- **Every loop is idle on a long enough word of raising arrows**: `T_id₊^ne_0 = d₊^ne_0` for
`1 ≤ i ≤ n-1`, which in the shifted indexing is `j + 2 ≤ n`. The loop walks down the word by
`d₊T_j = T_{j+1}d₊` until it is the first loop at a vertex two above the bottom, where
`T_1d₊² = d₊²` absorbs it. -/
@[hjo "lem_cm_dpa_tdplus_power"]
theorem Tg_mul_dPlusPow (j : ℕ) :
    ∀ n : ℕ, j + 2 ≤ n → Tg K q n j * dPlusPow K q n = dPlusPow K q n := by
  induction j with
  | zero =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [dPlusPow_succ, dPlusPow_succ,
      ← mul_assoc (dPlus K q (m + 1)) (dPlus K q m) (dPlusPow K q m),
      ← mul_assoc (Tg K q (m + 2) 0), Tg_mul_dPlus_dPlus]
  | succ j ih =>
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    rw [dPlusPow_succ, ← mul_assoc, ← dPlus_mul_Tg (by omega : j + 2 ≤ p), mul_assoc,
      ih p (by omega)]

/-- The word `d₋^m` of lowering arrows from the vertex `k + m` down to the vertex `k`, the empty
word being the idempotent `e_k`. -/
noncomputable def dMinusPow (K : Type*) [CommRing K] (q : K) (k : ℕ) : ℕ → Aq K q
  | 0 => e K q k
  | m + 1 => dMinusPow K q k m * dMinus K q (k + m)

theorem dMinusPow_succ (k m : ℕ) :
    dMinusPow K q k (m + 1) = dMinusPow K q k m * dMinus K q (k + m) := rfl

/-- **Every loop is idle on a long enough word of lowering arrows**: `d₋^mT_j = d₋^m` for
`k+1 ≤ j ≤ k+m-1`, the loop being taken at the vertex `k + m`. In the shifted indexing Carlsson and
Mellit's `T_j` is `Tg (k+m) i` with `i = j - 1`, and the range reads `k ≤ i` and `i + 2 ≤ k + m`.
The loop walks left past the lowering arrows by `T_id₋ = d₋T_i` until it meets the two arrows at its
own level, where `d₋²T_{k-1} = d₋²` absorbs it. -/
@[hjo "lem_cm_dminus_power_tj"]
theorem dMinusPow_mul_Tg {k i : ℕ} (hki : k ≤ i) :
    ∀ m : ℕ, i + 2 ≤ k + m →
      dMinusPow K q k m * Tg K q (k + m) i = dMinusPow K q k m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ n ih =>
    intro hm
    rcases Nat.lt_or_ge (i + 2) (k + n + 1) with hcase | hcase
    · have hidx : k + (n + 1) = k + n + 1 := by omega
      rw [dMinusPow_succ, hidx, mul_assoc, ← Tg_mul_dMinus (by omega), ← mul_assoc,
        ih (by omega)]
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
      obtain rfl : i = k + p := by omega
      have h1 : k + (p + 1 + 1) = k + p + 2 := by omega
      have h2 : k + (p + 1) = k + p + 1 := by omega
      rw [dMinusPow_succ, dMinusPow_succ, h1, h2, mul_assoc, mul_assoc,
        ← mul_assoc (dMinus K q (k + p)), dMinus_dMinus_mul_Tg, ← mul_assoc]

end HJO.Dyck.Aq
