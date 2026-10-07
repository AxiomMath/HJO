/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerElements
public meta import HJO.Attr

/-! # The calculus of the corner elements

The paper moves the corner elements `y_i` of `e_k𝔸_qe_k` past the loops, and reads the top
element `y_k` back as the commutator `D_k`. This file proves those moves: the Hecke commutation
`T_iy_i = y_{i+1}T_i + (1-q)y_i` and its companion, the upward recursion `y_{i+1} = qT̂_iy_iT̂_i`,
the closed form of `y_1` as a conjugate of `y_k`, and the inversion of `y_k` back to `D_k`.

## Main definitions

* `HJO.Dyck.Aq.tSeg`: the descending word `T_{a+n} ⋯ T_{a+1}` of loops at a vertex.
* `HJO.Dyck.Aq.tSegUp`: the ascending word `T_{a+1} ⋯ T_{a+n}`.

## Main results

* `HJO.Dyck.Aq.Tinv_mul_Tinv_mul_Tg`: `T̂_aT̂_bT_a = T_bT̂_aT̂_b` for `|a - b| = 1`.
* `HJO.Dyck.Aq.yElt_succ_eq`: `y_{i+1} = qT̂_iy_iT̂_i`.
* `HJO.Dyck.Aq.Tg_mul_yElt`, `HJO.Dyck.Aq.Tg_mul_yElt_succ`: the two Hecke commutations.
* `HJO.Dyck.Aq.yElt_one_eq`: `y_1 = q^{1-k}(T_1 ⋯ T_{k-1})y_k(T_{k-1} ⋯ T_1)`.
* `HJO.Dyck.Aq.Delta_eq_smul_tSegUp_mul_yElt`: `D_k = (q-1)(T_1 ⋯ T_{k-1})y_k`.

## Implementation notes

Both words take the *empty product to be the idempotent* `e_k`, as `HJO.Dyck.Aq.tinvWord` does and
for the same reason: the unit of `𝔸_q` is not in the span of the idempotents, so `1` would take the
word out of the corner. With that convention `tSegUp k 0 n` is the inverse of
`HJO.Dyck.Aq.tinvWord k n` *in the corner* — `HJO.Dyck.Aq.tSegUp_mul_tinvWord` — which is what
inverts the defining formula for `y_k`.

The loop index is the shifted one throughout, as in `HJO.Dyck.Aq.Tg`: `Tg k i` is the paper's
`T_{i+1}` at the vertex `k`, so the paper's `T_i` is `Tg k (i-1)` and its admissible range
`1 ≤ i ≤ k-1` reads `i + 1 ≤ k`. The words are indexed by an offset `a` and a length `n` rather
than by the paper's two endpoints, which keeps the recursions structural and keeps the truncated
subtraction of `ℕ` out of the definitions; the paper's `T_1 ⋯ T_{k-1}` is `tSegUp k 0 (k-1)` and
its `T_{k-1} ⋯ T_1` is `tSeg k 0 (k-1)`.

`𝔸_q` is not commutative, so `ring` is unavailable and every reassociation below is either an
explicit `mul_assoc` or the normalisation `simp only [mul_assoc]`. The braid identity for the
inverses is proved from an abstract lemma about a pair of invertible elements of any ring, where
the atoms are opaque variables and the rewrites can be aimed exactly.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K}

/-! ### The braid relation, and the words of loops -/

/-- The paper's braid relation `T_aT_bT_a = T_bT_aT_b` for `|a - b| = 1`, in the form that does
not name which of the two indices is the smaller. -/
theorem Tg_braid {k a b : ℕ} (ha : a + 2 ≤ k) (hb : b + 2 ≤ k) (hab : a = b + 1 ∨ b = a + 1) :
    Tg K q k a * Tg K q k b * Tg K q k a = Tg K q k b * Tg K q k a * Tg K q k b := by
  rcases hab with rfl | rfl
  · exact (braid_braid (q := q) (by omega)).symm
  · exact braid_braid (q := q) (by omega)

/-- The descending word `T_{a+n} ⋯ T_{a+1}` of loops at the vertex `k`, in the shifted indexing
`Tg k (a+n-1) ⋯ Tg k a`; the empty word is the idempotent `e_k`. -/
noncomputable def tSeg (K : Type*) [CommRing K] (q : K) (k a : ℕ) : ℕ → Aq K q
  | 0 => e K q k
  | n + 1 => Tg K q k (a + n) * tSeg K q k a n

/-- The ascending word `T_{a+1} ⋯ T_{a+n}` of loops at the vertex `k`, in the shifted indexing
`Tg k a ⋯ Tg k (a+n-1)`; the empty word is the idempotent `e_k`. -/
noncomputable def tSegUp (K : Type*) [CommRing K] (q : K) (k a : ℕ) : ℕ → Aq K q
  | 0 => e K q k
  | n + 1 => tSegUp K q k a n * Tg K q k (a + n)

@[simp] theorem tSeg_zero (k a : ℕ) : tSeg K q k a 0 = e K q k := rfl

theorem tSeg_succ (k a n : ℕ) : tSeg K q k a (n + 1) = Tg K q k (a + n) * tSeg K q k a n := rfl

@[simp] theorem tSegUp_zero (k a : ℕ) : tSegUp K q k a 0 = e K q k := rfl

theorem tSegUp_succ (k a n : ℕ) :
    tSegUp K q k a (n + 1) = tSegUp K q k a n * Tg K q k (a + n) := rfl

@[simp]
theorem e_mul_tSeg (k a n : ℕ) : e K q k * tSeg K q k a n = tSeg K q k a n := by
  cases n with
  | zero => rw [tSeg_zero, e_mul_self]
  | succ n => rw [tSeg_succ, ← mul_assoc, e_mul_Tg]

@[simp]
theorem tSeg_mul_e (k a n : ℕ) : tSeg K q k a n * e K q k = tSeg K q k a n := by
  induction n with
  | zero => rw [tSeg_zero, e_mul_self]
  | succ n ih => rw [tSeg_succ, mul_assoc, ih]

@[simp]
theorem e_mul_tSegUp (k a n : ℕ) : e K q k * tSegUp K q k a n = tSegUp K q k a n := by
  induction n with
  | zero => rw [tSegUp_zero, e_mul_self]
  | succ n ih => rw [tSegUp_succ, ← mul_assoc, ih]

@[simp]
theorem tSegUp_mul_e (k a n : ℕ) : tSegUp K q k a n * e K q k = tSegUp K q k a n := by
  cases n with
  | zero => rw [tSegUp_zero, e_mul_self]
  | succ n => rw [tSegUp_succ, mul_assoc, Tg_mul_e]

/-! ### The braid relation for the polynomial inverses -/

/-- The braid identity for a pair of invertible elements of a ring, with the unit of the corner
carried as an idempotent `ε` rather than as `1`: if `S` and `R` braid and `Sa`, `Rb` invert them,
then `SaRbS = RSaRb`. Both sides become `S` after multiplying on the left by `RS`, which is
invertible with inverse `SaRb`. -/
private theorem braid_conj_aux {A : Type*} [Ring A] {S R Sa Rb ε : A}
    (hεS : ε * S = S) (hSε : S * ε = S) (hεR : ε * R = R) (hRε : R * ε = R)
    (hεSa : ε * Sa = Sa) (hεRb : ε * Rb = Rb)
    (h1 : S * Sa = ε) (h2 : Sa * S = ε) (h3 : R * Rb = ε) (h4 : Rb * R = ε)
    (hb : S * R * S = R * S * R) :
    Sa * (Rb * S) = R * (Sa * Rb) := by
  have hX : R * (S * (Sa * (Rb * S))) = S := by
    rw [← mul_assoc S Sa, h1, ← mul_assoc R ε, hRε, ← mul_assoc R Rb, h3, hεS]
  have hY : R * (S * (R * (Sa * Rb))) = S := by
    rw [← mul_assoc R S, ← mul_assoc (R * S) R, ← hb, mul_assoc (S * R) S, ← mul_assoc S Sa, h1,
      hεRb, mul_assoc S R, h3, hSε]
  have cancel : ∀ Z : A, ε * Z = Z → Sa * (Rb * (R * (S * Z))) = Z := by
    intro Z hZ
    rw [← mul_assoc Rb R, h4, ← mul_assoc ε S, hεS, ← mul_assoc Sa S, h2, hZ]
  have hεX : ε * (Sa * (Rb * S)) = Sa * (Rb * S) := by rw [← mul_assoc, hεSa]
  have hεY : ε * (R * (Sa * Rb)) = R * (Sa * Rb) := by rw [← mul_assoc, hεR]
  rw [← cancel _ hεX, ← cancel _ hεY, hX, hY]

variable [Invertible q]

/-- **The braid relation for the inverses**: `T̂_aT̂_bT_a = T_bT̂_aT̂_b` for `|a - b| = 1`. Both
sides become the single loop `T_b` after multiplying on the left by `T_bT_a`, which is invertible
in the corner. -/
@[hjo "lem_cm_braid_conj"]
theorem Tinv_mul_Tinv_mul_Tg {k a b : ℕ} (ha : a + 2 ≤ k) (hb : b + 2 ≤ k)
    (hab : a = b + 1 ∨ b = a + 1) :
    Tinv K q k a * (Tinv K q k b * Tg K q k a)
      = Tg K q k b * (Tinv K q k a * Tinv K q k b) :=
  braid_conj_aux (e_mul_Tg k a) (Tg_mul_e k a) (e_mul_Tg k b) (Tg_mul_e k b) (e_mul_Tinv k a)
    (e_mul_Tinv k b) (Tg_mul_Tinv ha) (Tinv_mul_Tg ha) (Tg_mul_Tinv hb) (Tinv_mul_Tg hb)
    (Tg_braid ha hb hab)

/-- **The ascending word inverts the descending word of inverses**, in the corner: the paper's
`(T_1 ⋯ T_n)(T̂_n ⋯ T̂_1) = e_k`. This is what inverts the defining formula for `y_k`. -/
theorem tSegUp_mul_tinvWord {k : ℕ} (n : ℕ) (h : n + 1 ≤ k) :
    tSegUp K q k 0 n * tinvWord K q k n = e K q k := by
  induction n with
  | zero => rw [tSegUp_zero, tinvWord_zero, e_mul_self]
  | succ n ih =>
    rw [tSegUp_succ, tinvWord_succ, Nat.zero_add, mul_assoc, ← mul_assoc (Tg K q k n),
      Tg_mul_Tinv (by omega), e_mul_tinvWord, ih (by omega)]

/-! ### The corner elements against the loops -/

variable [Invertible (q - 1)]

@[simp]
theorem e_mul_yElt (k i : ℕ) : e K q k * yElt K q k i = yElt K q k i := e_mul_yAux k (k - i)

@[simp]
theorem yElt_mul_e (k i : ℕ) : yElt K q k i * e K q k = yElt K q k i := yAux_mul_e k (k - i)

/-- **The upward recursion**: `y_{i+1} = qT̂_iy_iT̂_i`, the paper's downward recursion read the
other way. The inverses cancel the two loops of `HJO.Dyck.Aq.yElt_recursion`, and the idempotents
they leave behind are absorbed by the corner element. -/
@[hjo "lem_cm_yelement_up"]
theorem yElt_succ_eq {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    yElt K q k (i + 1) = q • (Tinv K q k (i - 1) * yElt K q k i * Tinv K q k (i - 1)) := by
  have hadm : i - 1 + 2 ≤ k := by omega
  rw [yElt_recursion h1 hik, mul_smul_comm, smul_mul_assoc, smul_smul, mul_invOf_self, one_smul,
    show Tinv K q k (i - 1) * (Tg K q k (i - 1) * yElt K q k (i + 1) * Tg K q k (i - 1)) *
        Tinv K q k (i - 1)
      = Tinv K q k (i - 1) * Tg K q k (i - 1) * yElt K q k (i + 1) *
        (Tg K q k (i - 1) * Tinv K q k (i - 1)) from by simp only [mul_assoc],
    Tinv_mul_Tg hadm, Tg_mul_Tinv hadm, e_mul_yElt, yElt_mul_e]

/-- **The first Hecke commutation**: `T_iy_i = y_{i+1}T_i + (1-q)y_i`. -/
@[hjo "lem_cm_yelement_hecke_left"]
theorem Tg_mul_yElt {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    Tg K q k (i - 1) * yElt K q k i
      = yElt K q k (i + 1) * Tg K q k (i - 1) + (1 - q) • yElt K q k i := by
  have hadm : i - 1 + 2 ≤ k := by omega
  have hstep : q • yElt K q k i
      = Tg K q k (i - 1) * yElt K q k (i + 1) * Tg K q k (i - 1) := by
    rw [yElt_recursion h1 hik, smul_smul, mul_invOf_self, one_smul]
  have key : yElt K q k (i + 1) * Tg K q k (i - 1)
      = Tg K q k (i - 1) * yElt K q k i + (q - 1) • yElt K q k i := by
    have hcancel : Tinv K q k (i - 1) * (q • yElt K q k i)
        = yElt K q k (i + 1) * Tg K q k (i - 1) := by
      rw [hstep, ← mul_assoc, ← mul_assoc, Tinv_mul_Tg hadm, e_mul_yElt]
    rw [← hcancel, Tinv_eq, smul_mul_assoc, mul_smul_comm, smul_smul, invOf_mul_self, one_smul,
      add_mul, smul_mul_assoc, e_mul_yElt]
  rw [key, sub_smul, sub_smul, one_smul]
  abel

/-- **The second Hecke commutation**: `T_iy_{i+1} = y_iT_i + (q-1)y_i`. -/
@[hjo "lem_cm_yelement_hecke_right"]
theorem Tg_mul_yElt_succ {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    Tg K q k (i - 1) * yElt K q k (i + 1)
      = yElt K q k i * Tg K q k (i - 1) + (q - 1) • yElt K q k i := by
  have hadm : i - 1 + 2 ≤ k := by omega
  have hstep : q • yElt K q k i
      = Tg K q k (i - 1) * yElt K q k (i + 1) * Tg K q k (i - 1) := by
    rw [yElt_recursion h1 hik, smul_smul, mul_invOf_self, one_smul]
  have hcancel : (q • yElt K q k i) * Tinv K q k (i - 1)
      = Tg K q k (i - 1) * yElt K q k (i + 1) := by
    rw [hstep, mul_assoc, mul_assoc, Tg_mul_Tinv hadm, yElt_mul_e]
  rw [← hcancel, Tinv_eq, smul_mul_assoc, mul_smul_comm, smul_smul, mul_invOf_self, one_smul,
    mul_add, mul_smul_comm, yElt_mul_e]

/-! ### The closed forms -/

/-- The induction behind `HJO.Dyck.Aq.yElt_one_eq`:
`y_1 = q^{-j}(T_1 ⋯ T_j)y_{j+1}(T_j ⋯ T_1)` for `j ≤ k - 1`. -/
theorem yElt_one_eq_aux {k : ℕ} (j : ℕ) (hj : j + 1 ≤ k) :
    yElt K q k 1 = (⅟q) ^ j • (tSegUp K q k 0 j * yElt K q k (j + 1) * tSeg K q k 0 j) := by
  induction j with
  | zero => rw [pow_zero, one_smul, tSegUp_zero, tSeg_zero, e_mul_yElt, yElt_mul_e]
  | succ j ih =>
    have hrec := yElt_recursion (K := K) (q := q) (k := k) (i := j + 1)
      (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hrec
    rw [ih (by omega), hrec, tSegUp_succ, tSeg_succ, Nat.zero_add, pow_succ, mul_smul_comm,
      smul_mul_assoc, smul_smul]
    simp only [mul_assoc]

/-- **The closed form of `y_1`**: `y_1 = q^{1-k}(T_1 ⋯ T_{k-1})y_k(T_{k-1} ⋯ T_1)`, the words
being the idempotent when `k = 1`. -/
@[hjo "lem_cm_yelement_iterate"]
theorem yElt_one_eq {k : ℕ} (hk : 1 ≤ k) :
    yElt K q k 1
      = (⅟q) ^ (k - 1) • (tSegUp K q k 0 (k - 1) * yElt K q k k * tSeg K q k 0 (k - 1)) := by
  have h := yElt_one_eq_aux (K := K) (q := q) (k := k) (k - 1) (by omega)
  rwa [show k - 1 + 1 = k by omega] at h

/-- **The commutator read back from the top corner element**: `D_k = (q-1)(T_1 ⋯ T_{k-1})y_k`, the
word being the idempotent when `k = 1`. Multiplying the defining formula for `y_k` on the left by
the ascending word inverts the descending word of inverses that it carries. -/
@[hjo "lem_cm_dpa_dplusdminus"]
theorem Delta_eq_smul_tSegUp_mul_yElt {k : ℕ} (hk : 1 ≤ k) :
    Delta K q (k - 1) = (q - 1) • (tSegUp K q k 0 (k - 1) * yElt K q k k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [yElt_self]
  simp only [Nat.add_sub_cancel]
  rw [mul_smul_comm, smul_smul, mul_invOf_self, one_smul, ← mul_assoc, ← mul_assoc,
    tSegUp_mul_tinvWord m le_rfl, e_mul_Delta, Delta_mul_e]

end HJO.Dyck.Aq
