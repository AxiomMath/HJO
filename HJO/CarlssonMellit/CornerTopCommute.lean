/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerCommutator
public import HJO.CarlssonMellit.CornerTCommute
public meta import HJO.Attr

/-! # The first and the last corner element commute

`y_1` and `y_k` are the two ends of the family, and the loops in between separate them: `y_1`
commutes with every loop `T_2, …, T_{k-1}`, and the only one it does not commute with, `T_1`, is
exactly the one the commutator conjugates it by. Those two facts cancel, and `y_1y_k = y_ky_1`.

## Main results

* `HJO.Dyck.Aq.yElt_one_mul_yElt_top`: `y_1y_k = y_ky_1`.

## Implementation notes

The proof reads `y_k` through its defining formula as a descending word of inverses times the
commutator, peels the *rightmost* letter `T̂_1` off that word, and lets the commutator conjugate
`y_1` past it: the `T_1` the conjugation produces is cancelled by exactly that peeled `T̂_1`. What
is left of the word has letters `T̂_2, …, T̂_{k-1}`, and `y_1` commutes with all of them.

`HJO.Dyck.Aq.tinvSeg` is the descending word of inverses with an offset, which
`HJO.Dyck.Aq.tinvWord` is the case `a = 0` of; the offset is what lets the peeled word be named.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q]

/-! ### The descending word of inverses with an offset -/

/-- The descending word `T̂_{a+n} ⋯ T̂_{a+1}` of polynomial inverses at the vertex `k`, in the
shifted indexing `Tinv k (a+n-1) ⋯ Tinv k a`; the empty word is the idempotent `e_k`. -/
noncomputable def tinvSeg (K : Type*) [CommRing K] (q : K) [Invertible q] (k a : ℕ) :
    ℕ → Aq K q
  | 0 => e K q k
  | n + 1 => Tinv K q k (a + n) * tinvSeg K q k a n

@[simp] theorem tinvSeg_zero (k a : ℕ) : tinvSeg K q k a 0 = e K q k := rfl

theorem tinvSeg_succ (k a n : ℕ) :
    tinvSeg K q k a (n + 1) = Tinv K q k (a + n) * tinvSeg K q k a n := rfl

/-- The word of `HJO.Dyck.Aq.CornerElements` is the offset word at offset `0`. -/
theorem tinvSeg_eq_tinvWord (k n : ℕ) : tinvSeg K q k 0 n = tinvWord K q k n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tinvSeg_succ, tinvWord_succ, Nat.zero_add, ih]

/-- The offset word peels off its rightmost — that is, its lowest-index — letter. -/
theorem tinvSeg_succ_right (k a n : ℕ) :
    tinvSeg K q k a (n + 1) = tinvSeg K q k (a + 1) n * Tinv K q k a := by
  induction n with
  | zero => rw [tinvSeg_succ, tinvSeg_zero, tinvSeg_zero, Nat.add_zero, e_mul_Tinv, Tinv_mul_e]
  | succ n ih =>
    rw [tinvSeg_succ, ih, ← mul_assoc, tinvSeg_succ k (a + 1) n,
      show a + (n + 1) = a + 1 + n by omega]

/-- An element of the corner commutes with a polynomial inverse as soon as it commutes with the
loop: the inverse is a combination of the loop and the idempotent, and the idempotent is a
two-sided identity on the corner. -/
theorem comm_Tinv_of_comm_Tg {k j : ℕ} {X : Aq K q} (hl : e K q k * X = X) (hr : X * e K q k = X)
    (h : X * Tg K q k j = Tg K q k j * X) : X * Tinv K q k j = Tinv K q k j * X := by
  simp only [Tinv_eq, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, h, hl, hr, mul_smul_comm,
    smul_mul_assoc]

/-! ### `y_1` past the word of inverses above the first letter -/

variable [Invertible (q - 1)]

/-- `y_1` commutes with the descending word `T̂_{m+1} ⋯ T̂_2`: every letter has index at least `2`
in the paper's indexing, and `HJO.Dyck.Aq.yElt_mul_Tg_comm` applies to each. -/
theorem yElt_one_mul_tinvSeg {k : ℕ} :
    ∀ m : ℕ, m + 2 ≤ k →
      yElt K q k 1 * tinvSeg K q k 1 m = tinvSeg K q k 1 m * yElt K q k 1 := by
  intro m
  induction m with
  | zero => intro _; rw [tinvSeg_zero, yElt_mul_e, e_mul_yElt]
  | succ m ih =>
    intro hm
    have hTg : yElt K q k 1 * Tg K q k (1 + m) = Tg K q k (1 + m) * yElt K q k 1 :=
      yElt_mul_Tg_comm (by omega) (by omega) (by omega) (by omega)
    have hTinv : yElt K q k 1 * Tinv K q k (1 + m) = Tinv K q k (1 + m) * yElt K q k 1 :=
      comm_Tinv_of_comm_Tg (e_mul_yElt k 1) (yElt_mul_e k 1) hTg
    rw [tinvSeg_succ, ← mul_assoc, hTinv, mul_assoc, ih (by omega), ← mul_assoc]

/-! ### The two ends of the family -/

/-- The algebra behind `HJO.Dyck.Aq.yElt_one_mul_yElt_top`: the conjugation `DY = RYBD` produced by
the commutator is undone by the peeled letter `B`, since `BR` is the corner's identity. -/
theorem comm_top_aux {A₀ : Type*} [Ring A₀] {S B R D Y ε : A₀} (hBR : B * R = ε)
    (hεY : ε * Y = Y) (hconj : D * Y = R * Y * B * D) (hSY : Y * S = S * Y) :
    S * B * D * Y = Y * (S * B * D) := by
  calc S * B * D * Y = S * (B * (D * Y)) := by simp only [mul_assoc]
    _ = S * (B * (R * Y * B * D)) := by rw [hconj]
    _ = S * (B * R * (Y * (B * D))) := by simp only [mul_assoc]
    _ = S * (ε * (Y * (B * D))) := by rw [hBR]
    _ = S * (ε * Y * (B * D)) := by simp only [mul_assoc]
    _ = S * (Y * (B * D)) := by rw [hεY]
    _ = S * Y * (B * D) := by simp only [mul_assoc]
    _ = Y * S * (B * D) := by rw [← hSY]
    _ = Y * (S * B * D) := by simp only [mul_assoc]

/-- **The first and the last corner element commute**: `y_1y_k = y_ky_1` in `e_k𝔸_qe_k`. -/
@[hjo "lem_cm_yelement_one_k_commute"]
theorem yElt_one_mul_yElt_top {k : ℕ} (hk : 1 ≤ k) :
    yElt K q k 1 * yElt K q k k = yElt K q k k * yElt K q k 1 := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    rfl
  obtain ⟨p, rfl⟩ : ∃ p, k = p + 2 := ⟨k - 2, by omega⟩
  have e1 : p + 2 - 1 = p + 1 := by omega
  have hpeel : tinvWord K q (p + 2) (p + 1)
      = tinvSeg K q (p + 2) 1 p * Tinv K q (p + 2) 0 := by
    rw [← tinvSeg_eq_tinvWord, tinvSeg_succ_right, Nat.zero_add]
  have htop : yElt K q (p + 2) (p + 2)
      = ⅟(q - 1) • (tinvSeg K q (p + 2) 1 p * Tinv K q (p + 2) 0 * Delta K q (p + 1)) := by
    rw [yElt_self, e1, hpeel]
    congr 1
    rw [mul_assoc, Delta_mul_e]
  have hconj : Delta K q (p + 1) * yElt K q (p + 2) 1
      = Tg K q (p + 2) 0 * yElt K q (p + 2) 1 * Tinv K q (p + 2) 0 * Delta K q (p + 1) :=
    Delta_mul_yElt_one (by omega)
  have hBR : Tinv K q (p + 2) 0 * Tg K q (p + 2) 0 = e K q (p + 2) := Tinv_mul_Tg (by omega)
  have hSY : yElt K q (p + 2) 1 * tinvSeg K q (p + 2) 1 p
      = tinvSeg K q (p + 2) 1 p * yElt K q (p + 2) 1 := yElt_one_mul_tinvSeg p le_rfl
  rw [htop, mul_smul_comm, smul_mul_assoc]
  congr 1
  exact (comm_top_aux hBR (e_mul_yElt (p + 2) 1) hconj hSY).symm

end HJO.Dyck.Aq
