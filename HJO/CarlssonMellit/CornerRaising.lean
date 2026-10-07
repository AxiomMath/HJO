/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerTopCommute
public meta import HJO.Attr

/-! # Every corner element transports along the raising arrow

Across `d₋` the corner elements keep their subscript. Across `d₊` they cannot — the raising arrow
shifts every loop index up by one — but they do transport up to conjugation by an ascending word of
loops: `d₊y_i^{(k)} = W_iy_i^{(k+1)}W_i^{-1}d₊` with `W_i = T_1T_2 ⋯ T_i` at the vertex `k+1`. The
case `i = 1` is already proved; this file runs the induction that gives every `i`.

## Main results

* `HJO.Dyck.Aq.dPlus_mul_yElt`: `d₊y_i^{(k)} = W_iy_i^{(k+1)}W_i^{-1}d₊` for every `1 ≤ i ≤ k`.

Along the way, the braid calculus for the polynomial inverses:

* `HJO.Dyck.Aq.braid_conj_shift`: `T̂_{i+1}T_iT_{i+1} = T_iT_{i+1}T̂_i`.
* `HJO.Dyck.Aq.Tinv_braid`: the braid relation for the inverses,
  `T̂_{i+1}T̂_iT̂_{i+1} = T̂_iT̂_{i+1}T̂_i`.
* `HJO.Dyck.Aq.tSegUp_comm_Tinv`, `HJO.Dyck.Aq.tinvWord_comm_Tinv`: a loop or its inverse of index
  above a whole word commutes past it.

## Implementation notes

The word `W_i = T_1 ⋯ T_i` at the vertex `k+1` is `tSegUp (k+1) 0 i` and its inverse
`T_i^{-1} ⋯ T_1^{-1}` is `tinvWord (k+1) i`; `HJO.Dyck.Aq.tSegUp_mul_tinvWord` is the statement that
they are inverse in the corner, and neither is `1` — both are the idempotent when `i = 0`.

The induction step is the paper's, and its content is one identity between six letters at two
adjacent indices. The bookkeeping that surrounds it — the ascending word `U = T_1 ⋯ T_{i-1}` and its
inverse, which the two new letters must be commuted past — is handled by
`tSegUp_comm_Tinv`/`tinvWord_comm_Tinv`, and the identity itself is `braid_y_step`, an abstract ring
lemma. Splitting it that way is what keeps the step readable: in place, the two halves are eleven
factors long and no `rw` can be aimed.

Indices run through `m + 1 + 1` rather than `m + 2`, which is the form `Nat.le_induction` produces
and the form the word recursions match.

## References

The lemma `HJO.Dyck.Aq.dPlus_mul_yElt`; E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q]

/-! ### Two cancellation devices -/

/-- Right cancellation inside a corner whose unit is an idempotent `ε`: if `S` has the right inverse
`B` and both `X` and `Y` absorb `ε` on the right, then `S` may be cancelled. -/
theorem eq_of_mul_right_corner {A₀ : Type*} [Ring A₀] {X Y S B ε : A₀} (hSB : S * B = ε)
    (hX : X * ε = X) (hY : Y * ε = Y) (h : X * S = Y * S) : X = Y := by
  rw [← hX, ← hSB, ← mul_assoc, h, mul_assoc, hSB, hY]

/-- The identity the induction step of `HJO.Dyck.Aq.dPlus_mul_yElt` reduces to, stated for six
elements of an arbitrary ring. -/
theorem braid_y_step {A₀ : Type*} [Ring A₀] {A B S R y ε : A₀} (h1 : A * S * R = S * R * B)
    (h2 : A * B * A = B * A * B) (h3 : y * R = R * y) (h4 : R * A = ε) (h5 : ε * B = B) :
    S * R * B * y * (B * A * B) = A * S * y * B * A := by
  calc S * R * B * y * (B * A * B)
      = A * S * R * y * (A * B * A) := by rw [h1, h2]
    _ = A * S * (R * y) * (A * B * A) := by simp only [mul_assoc]
    _ = A * S * (y * R) * (A * B * A) := by rw [h3]
    _ = A * S * y * (R * A) * (B * A) := by simp only [mul_assoc]
    _ = A * S * y * ε * (B * A) := by rw [h4]
    _ = A * S * y * (ε * B) * A := by simp only [mul_assoc]
    _ = A * S * y * B * A := by rw [h5]

/-! ### The braid calculus for the inverses -/

omit [Invertible q] in
/-- The one-letter ascending word is the loop itself. -/
@[simp] theorem tSegUp_one (k a : ℕ) : tSegUp K q k a 1 = Tg K q k a := by
  rw [tSegUp_succ, tSegUp_zero, Nat.add_zero, e_mul_Tg]

/-- **The raising arrow shifts the index of a polynomial inverse up by one**, exactly as it does for
a loop: the inverse is a combination of the loop and the idempotent, and both cross the arrow. -/
theorem dPlus_mul_Tinv {k j : ℕ} (h : j + 2 ≤ k) :
    dPlus K q k * Tinv K q k j = Tinv K q (k + 1) (j + 1) * dPlus K q k := by
  simp only [Tinv_eq, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, dPlus_mul_Tg h,
    dPlus_mul_e, e_mul_dPlus]

/-- A loop commutes with the polynomial inverse of a loop two or more indices away. -/
theorem Tg_comm_Tinv {k a b : ℕ} (ha : a + 2 ≤ k) (hb : b + 2 ≤ k)
    (hab : a + 1 < b ∨ b + 1 < a) :
    Tg K q k a * Tinv K q k b = Tinv K q k b * Tg K q k a := by
  refine comm_Tinv_of_comm_Tg (e_mul_Tg k a) (Tg_mul_e k a) ?_
  rcases hab with hab | hab
  · exact Tg_comm ha hb hab
  · exact (Tg_comm hb ha hab).symm

/-- **`T̂_{i+1}T_iT_{i+1} = T_iT_{i+1}T̂_i`**: the braid relation read with one inverse on each
side. Both sides become `T_iT_{i+1}` after multiplying on the right by `T_i`, and that is
cancellable in the corner. -/
theorem braid_conj_shift {k m : ℕ} (h : m + 3 ≤ k) :
    Tinv K q k (m + 1) * Tg K q k m * Tg K q k (m + 1)
      = Tg K q k m * Tg K q k (m + 1) * Tinv K q k m := by
  have hSB : Tg K q k m * Tinv K q k m = e K q k := Tg_mul_Tinv (by omega)
  have hBS : Tinv K q k m * Tg K q k m = e K q k := Tinv_mul_Tg (by omega)
  have hAR : Tinv K q k (m + 1) * Tg K q k (m + 1) = e K q k := Tinv_mul_Tg (by omega)
  have hbr : Tg K q k m * Tg K q k (m + 1) * Tg K q k m
      = Tg K q k (m + 1) * Tg K q k m * Tg K q k (m + 1) :=
    Tg_braid (by omega) (by omega) (Or.inr rfl)
  have hXS : Tinv K q k (m + 1) * Tg K q k m * Tg K q k (m + 1) * Tg K q k m
      = Tg K q k m * Tg K q k (m + 1) := by
    calc Tinv K q k (m + 1) * Tg K q k m * Tg K q k (m + 1) * Tg K q k m
        = Tinv K q k (m + 1) * (Tg K q k m * Tg K q k (m + 1) * Tg K q k m) := by
          simp only [mul_assoc]
      _ = Tinv K q k (m + 1) * (Tg K q k (m + 1) * Tg K q k m * Tg K q k (m + 1)) := by rw [hbr]
      _ = Tinv K q k (m + 1) * Tg K q k (m + 1) * (Tg K q k m * Tg K q k (m + 1)) := by
          simp only [mul_assoc]
      _ = e K q k * (Tg K q k m * Tg K q k (m + 1)) := by rw [hAR]
      _ = Tg K q k m * Tg K q k (m + 1) := by rw [← mul_assoc, e_mul_Tg]
  have hYS : Tg K q k m * Tg K q k (m + 1) * Tinv K q k m * Tg K q k m
      = Tg K q k m * Tg K q k (m + 1) := by
    rw [mul_assoc (Tg K q k m * Tg K q k (m + 1)), hBS, mul_assoc, Tg_mul_e]
  exact eq_of_mul_right_corner hSB (by rw [mul_assoc, Tg_mul_e])
    (by rw [mul_assoc, Tinv_mul_e]) (hXS.trans hYS.symm)

/-- **The braid relation for the polynomial inverses**:
`T̂_{i+1}T̂_iT̂_{i+1} = T̂_iT̂_{i+1}T̂_i`. -/
theorem Tinv_braid {k m : ℕ} (h : m + 3 ≤ k) :
    Tinv K q k (m + 1) * Tinv K q k m * Tinv K q k (m + 1)
      = Tinv K q k m * Tinv K q k (m + 1) * Tinv K q k m := by
  have hbr := Tinv_mul_Tinv_mul_Tg (K := K) (q := q) (k := k) (a := m) (b := m + 1)
    (by omega) (by omega) (Or.inr rfl)
  have hSB : Tg K q k m * Tinv K q k m = e K q k := Tg_mul_Tinv (by omega)
  have hAR : Tinv K q k (m + 1) * Tg K q k (m + 1) = e K q k := Tinv_mul_Tg (by omega)
  have key : Tinv K q k m * Tinv K q k (m + 1)
      = Tg K q k (m + 1) * (Tinv K q k m * Tinv K q k (m + 1) * Tinv K q k m) := by
    calc Tinv K q k m * Tinv K q k (m + 1)
        = Tinv K q k m * (Tinv K q k (m + 1) * e K q k) := by rw [Tinv_mul_e]
      _ = Tinv K q k m * (Tinv K q k (m + 1) * (Tg K q k m * Tinv K q k m)) := by rw [hSB]
      _ = Tinv K q k m * (Tinv K q k (m + 1) * Tg K q k m) * Tinv K q k m := by
          simp only [mul_assoc]
      _ = Tg K q k (m + 1) * (Tinv K q k m * Tinv K q k (m + 1)) * Tinv K q k m := by rw [hbr]
      _ = Tg K q k (m + 1) * (Tinv K q k m * Tinv K q k (m + 1) * Tinv K q k m) := by
          simp only [mul_assoc]
  calc Tinv K q k (m + 1) * Tinv K q k m * Tinv K q k (m + 1)
      = Tinv K q k (m + 1) * (Tinv K q k m * Tinv K q k (m + 1)) := by simp only [mul_assoc]
    _ = Tinv K q k (m + 1) *
          (Tg K q k (m + 1) * (Tinv K q k m * Tinv K q k (m + 1) * Tinv K q k m)) := by
        conv_lhs => rw [key]
    _ = Tinv K q k (m + 1) * Tg K q k (m + 1) *
          (Tinv K q k m * Tinv K q k (m + 1) * Tinv K q k m) := by simp only [mul_assoc]
    _ = e K q k * (Tinv K q k m * Tinv K q k (m + 1) * Tinv K q k m) := by rw [hAR]
    _ = Tinv K q k m * Tinv K q k (m + 1) * Tinv K q k m := by
        rw [← mul_assoc, ← mul_assoc, e_mul_Tinv]

/-! ### A high loop past a whole word -/

omit [Invertible q] in
/-- A loop of index above every letter of the ascending word commutes past it. -/
theorem tSegUp_comm_Tg {k j : ℕ} (hj : j + 2 ≤ k) :
    ∀ n : ℕ, n + 1 ≤ j → tSegUp K q k 0 n * Tg K q k j = Tg K q k j * tSegUp K q k 0 n := by
  intro n
  induction n with
  | zero => intro _; rw [tSegUp_zero, e_mul_Tg, Tg_mul_e]
  | succ n ih =>
    intro hn
    rw [tSegUp_succ, Nat.zero_add, mul_assoc, Tg_comm (by omega) hj (by omega), ← mul_assoc,
      ih (by omega), mul_assoc]

/-- A loop of index above every letter of the descending word of inverses commutes past it. -/
theorem tinvWord_comm_Tg {k j : ℕ} (hj : j + 2 ≤ k) :
    ∀ n : ℕ, n + 1 ≤ j → tinvWord K q k n * Tg K q k j = Tg K q k j * tinvWord K q k n := by
  intro n
  induction n with
  | zero => intro _; rw [tinvWord_zero, e_mul_Tg, Tg_mul_e]
  | succ n ih =>
    intro hn
    rw [tinvWord_succ, mul_assoc, ih (by omega), ← mul_assoc,
      ← Tg_comm_Tinv hj (by omega) (Or.inr (by omega)), mul_assoc]

/-- The inverse of a loop of index above every letter of the ascending word commutes past it. -/
theorem tSegUp_comm_Tinv {k j n : ℕ} (hj : j + 2 ≤ k) (hn : n + 1 ≤ j) :
    tSegUp K q k 0 n * Tinv K q k j = Tinv K q k j * tSegUp K q k 0 n :=
  comm_Tinv_of_comm_Tg (e_mul_tSegUp k 0 n) (tSegUp_mul_e k 0 n) (tSegUp_comm_Tg hj n hn)

/-- The inverse of a loop of index above every letter of the descending word of inverses commutes
past it. -/
theorem tinvWord_comm_Tinv {k j n : ℕ} (hj : j + 2 ≤ k) (hn : n + 1 ≤ j) :
    tinvWord K q k n * Tinv K q k j = Tinv K q k j * tinvWord K q k n :=
  comm_Tinv_of_comm_Tg (e_mul_tinvWord k n) (tinvWord_mul_e k n) (tinvWord_comm_Tg hj n hn)

/-! ### The transport -/

variable [Invertible (q - 1)]

/-- **Every corner element transports along the raising arrow, up to conjugation by an ascending
word**: `d₊y_i^{(k)} = W_iy_i^{(k+1)}W_i^{-1}d₊` for `1 ≤ i ≤ k`, where `W_i = T_1 ⋯ T_i` at the
vertex `k+1` is `tSegUp (k+1) 0 i` and `W_i^{-1} = T_i^{-1} ⋯ T_1^{-1}` is `tinvWord (k+1) i`. -/
@[hjo "lem_cm_yelement_dplus"]
theorem dPlus_mul_yElt {k : ℕ} :
    ∀ i : ℕ, 1 ≤ i → i ≤ k →
      dPlus K q k * yElt K q k i
        = tSegUp K q (k + 1) 0 i * yElt K q (k + 1) i * tinvWord K q (k + 1) i *
          dPlus K q k := by
  intro i h1
  induction i, h1 using Nat.le_induction with
  | base =>
    intro hik
    rw [tSegUp_one, tinvWord_one]
    exact dPlus_mul_yElt_one (by omega)
  | succ n hn ih =>
    intro hik
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have em : m + 1 - 1 = m := by omega
    -- the two recursions, at the vertex `k` and at the vertex `k + 1`
    have hrecK : yElt K q k (m + 1 + 1)
        = q • (Tinv K q k m * yElt K q k (m + 1) * Tinv K q k m) := by
      have h := yElt_succ_eq (K := K) (q := q) (k := k) (i := m + 1) (by omega) (by omega)
      rw [em] at h
      exact h
    have hrecK1 : yElt K q (k + 1) (m + 1 + 1)
        = q • (Tinv K q (k + 1) m * yElt K q (k + 1) (m + 1) * Tinv K q (k + 1) m) := by
      have h := yElt_succ_eq (K := K) (q := q) (k := k + 1) (i := m + 1) (by omega) (by omega)
      rw [em] at h
      exact h
    -- the words, peeled
    have hWup : tSegUp K q (k + 1) 0 (m + 1 + 1)
        = tSegUp K q (k + 1) 0 m * Tg K q (k + 1) m * Tg K q (k + 1) (m + 1) := by
      rw [tSegUp_succ, tSegUp_succ, Nat.zero_add, Nat.zero_add]
    have hWinv : tinvWord K q (k + 1) (m + 1 + 1)
        = Tinv K q (k + 1) (m + 1) * (Tinv K q (k + 1) m * tinvWord K q (k + 1) m) := by
      rw [tinvWord_succ, tinvWord_succ]
    have hIH : dPlus K q k * yElt K q k (m + 1)
        = tSegUp K q (k + 1) 0 m * Tg K q (k + 1) m * yElt K q (k + 1) (m + 1) *
          (Tinv K q (k + 1) m * tinvWord K q (k + 1) m) * dPlus K q k := by
      rw [ih (by omega), tSegUp_succ, Nat.zero_add, tinvWord_succ]
    -- the arrow shifts an inverse's index
    have hDB : dPlus K q k * Tinv K q k m = Tinv K q (k + 1) (m + 1) * dPlus K q k :=
      dPlus_mul_Tinv (by omega)
    -- the new letter commutes past the old word and its inverse
    have hAU : tSegUp K q (k + 1) 0 m * Tinv K q (k + 1) (m + 1)
        = Tinv K q (k + 1) (m + 1) * tSegUp K q (k + 1) 0 m :=
      tSegUp_comm_Tinv (by omega) (by omega)
    have hAUinv : tinvWord K q (k + 1) m * Tinv K q (k + 1) (m + 1)
        = Tinv K q (k + 1) (m + 1) * tinvWord K q (k + 1) m :=
      tinvWord_comm_Tinv (by omega) (by omega)
    -- the six-letter identity
    have h1 : Tinv K q (k + 1) (m + 1) * Tg K q (k + 1) m * Tg K q (k + 1) (m + 1)
        = Tg K q (k + 1) m * Tg K q (k + 1) (m + 1) * Tinv K q (k + 1) m :=
      braid_conj_shift (by omega)
    have h2 : Tinv K q (k + 1) (m + 1) * Tinv K q (k + 1) m * Tinv K q (k + 1) (m + 1)
        = Tinv K q (k + 1) m * Tinv K q (k + 1) (m + 1) * Tinv K q (k + 1) m :=
      Tinv_braid (by omega)
    have h3 : yElt K q (k + 1) (m + 1) * Tg K q (k + 1) (m + 1)
        = Tg K q (k + 1) (m + 1) * yElt K q (k + 1) (m + 1) :=
      yElt_mul_Tg_comm (by omega) (by omega) (by omega) (by omega)
    have h4 : Tg K q (k + 1) (m + 1) * Tinv K q (k + 1) (m + 1) = e K q (k + 1) :=
      Tg_mul_Tinv (by omega)
    have h5 : e K q (k + 1) * Tinv K q (k + 1) m = Tinv K q (k + 1) m := e_mul_Tinv (k + 1) m
    -- both sides, brought to a common form
    have hL : dPlus K q k * yElt K q k (m + 1 + 1)
        = q • (tSegUp K q (k + 1) 0 m *
            (Tinv K q (k + 1) (m + 1) * Tg K q (k + 1) m * yElt K q (k + 1) (m + 1) *
              Tinv K q (k + 1) m * Tinv K q (k + 1) (m + 1)) *
            tinvWord K q (k + 1) m * dPlus K q k) := by
      rw [hrecK, mul_smul_comm]
      congr 1
      calc dPlus K q k * (Tinv K q k m * yElt K q k (m + 1) * Tinv K q k m)
          = dPlus K q k * Tinv K q k m * (yElt K q k (m + 1) * Tinv K q k m) := by
            simp only [mul_assoc]
        _ = Tinv K q (k + 1) (m + 1) * dPlus K q k * (yElt K q k (m + 1) * Tinv K q k m) := by
            rw [hDB]
        _ = Tinv K q (k + 1) (m + 1) * (dPlus K q k * yElt K q k (m + 1)) *
              Tinv K q k m := by simp only [mul_assoc]
        _ = Tinv K q (k + 1) (m + 1) *
              (tSegUp K q (k + 1) 0 m * Tg K q (k + 1) m * yElt K q (k + 1) (m + 1) *
                (Tinv K q (k + 1) m * tinvWord K q (k + 1) m) * dPlus K q k) *
              Tinv K q k m := by rw [hIH]
        _ = Tinv K q (k + 1) (m + 1) *
              (tSegUp K q (k + 1) 0 m * Tg K q (k + 1) m * yElt K q (k + 1) (m + 1) *
                (Tinv K q (k + 1) m * tinvWord K q (k + 1) m)) *
              (dPlus K q k * Tinv K q k m) := by simp only [mul_assoc]
        _ = Tinv K q (k + 1) (m + 1) *
              (tSegUp K q (k + 1) 0 m * Tg K q (k + 1) m * yElt K q (k + 1) (m + 1) *
                (Tinv K q (k + 1) m * tinvWord K q (k + 1) m)) *
              (Tinv K q (k + 1) (m + 1) * dPlus K q k) := by rw [hDB]
        _ = Tinv K q (k + 1) (m + 1) * tSegUp K q (k + 1) 0 m *
              (Tg K q (k + 1) m * yElt K q (k + 1) (m + 1) * Tinv K q (k + 1) m *
                (tinvWord K q (k + 1) m * Tinv K q (k + 1) (m + 1))) *
              dPlus K q k := by simp only [mul_assoc]
        _ = tSegUp K q (k + 1) 0 m * Tinv K q (k + 1) (m + 1) *
              (Tg K q (k + 1) m * yElt K q (k + 1) (m + 1) * Tinv K q (k + 1) m *
                (tinvWord K q (k + 1) m * Tinv K q (k + 1) (m + 1))) *
              dPlus K q k := by rw [← hAU]
        _ = tSegUp K q (k + 1) 0 m * Tinv K q (k + 1) (m + 1) *
              (Tg K q (k + 1) m * yElt K q (k + 1) (m + 1) * Tinv K q (k + 1) m *
                (Tinv K q (k + 1) (m + 1) * tinvWord K q (k + 1) m)) *
              dPlus K q k := by rw [hAUinv]
        _ = tSegUp K q (k + 1) 0 m *
              (Tinv K q (k + 1) (m + 1) * Tg K q (k + 1) m * yElt K q (k + 1) (m + 1) *
                Tinv K q (k + 1) m * Tinv K q (k + 1) (m + 1)) *
              tinvWord K q (k + 1) m * dPlus K q k := by simp only [mul_assoc]
    have hR : tSegUp K q (k + 1) 0 (m + 1 + 1) * yElt K q (k + 1) (m + 1 + 1) *
          tinvWord K q (k + 1) (m + 1 + 1) * dPlus K q k
        = q • (tSegUp K q (k + 1) 0 m *
            (Tg K q (k + 1) m * Tg K q (k + 1) (m + 1) * Tinv K q (k + 1) m *
              yElt K q (k + 1) (m + 1) *
              (Tinv K q (k + 1) m * Tinv K q (k + 1) (m + 1) * Tinv K q (k + 1) m)) *
            tinvWord K q (k + 1) m * dPlus K q k) := by
      rw [hWup, hWinv, hrecK1]
      simp only [smul_mul_assoc, mul_smul_comm]
      congr 1
      simp only [mul_assoc]
    rw [hL, hR, braid_y_step h1 h2 h3 h4 h5]

end HJO.Dyck.Aq
