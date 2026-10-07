/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerTopCommute
public meta import HJO.Attr

/-! # The corner elements commute with one another

`y_1, …, y_k` is a *commuting* family — that is the whole point of the construction, and it is what
lets Carlsson and Mellit treat `e_k𝔸_qe_k` as containing a polynomial ring in the `y_i`. This file
proves it.

## Main results

* `HJO.Dyck.Aq.yElt_comm`: `y_iy_j = y_jy_i` for all `1 ≤ i, j ≤ k`.

## Implementation notes

The proof is two nested inductions, both reducing to the case already in hand. First
`y_iy_k = y_ky_i` for every `i`, by induction *upward* on `i` from
`HJO.Dyck.Aq.yElt_one_mul_yElt_top`: the step writes `y_{i+1}` as `T̂_iy_iT̂_i` and needs `y_k` to
commute with `T̂_i`, which
`HJO.Dyck.Aq.yElt_mul_Tg_comm` gives — and note where the range comes from, since `y_k` does *not*
commute with `T_{k-1}`, so the step only reaches `i + 1 ≤ k - 1` and the case `i = k` is separate.
Then the general case by induction *downward* on `j`, writing `y_j` as `q^{-1}T_jy_{j+1}T_j` and
moving `y_i` rightwards through the three factors.

Both steps are the same two-line abstract moves as before — `HJO.Dyck.Aq.comm_conj_aux` for the
first, `HJO.Dyck.Aq.comm_triple_aux` for the second — with the corner's unit playing no role, so
they are stated for an arbitrary ring.

The downward induction is run against an explicit bound on `k - j` rather than through a
well-founded recursion combinator, which keeps each recursive call's side condition ordinary
arithmetic for `omega`.

**The range is `k ≥ 1`.** The lemma is sometimes stated only for `k ≥ 3`, on the grounds that the
vertex-`2` case is not available from the definition of `HJO.Dyck.Aq`. It is available, and the
range of `HJO.Dyck.Aq.yElt_comm` is the Carlsson–Mellit one: `k ≥ 1`. The difference is the route
taken to `y_1y_k = y_ky_1`. A route carrying `T_1` *down* from the vertex `k` to `k-1` needs
`1 ≤ k-2`; the route here goes through `HJO.Dyck.Aq.Delta_mul_yElt_one`, stated for `k ≥ 2`, which
reads `T_id_- = d_-T_i` at the vertex `k+1` and so needs only `1 ≤ k-1`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 3, and A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3, for the lemma
`HJO.Dyck.Aq.yElt_comm` on the Dyck path algebra, its loops and its braid generators.
-/

@[expose] public section

namespace HJO.Dyck.Aq

/-- An element commuting with `S` and with `Y` commutes with `SYS`. -/
theorem comm_triple_aux {A₀ : Type*} [Ring A₀] {X S Y : A₀} (hS : X * S = S * X)
    (hY : X * Y = Y * X) : X * (S * Y * S) = S * Y * S * X := by
  calc X * (S * Y * S) = X * S * (Y * S) := by simp only [mul_assoc]
    _ = S * X * (Y * S) := by rw [hS]
    _ = S * (X * Y) * S := by simp only [mul_assoc]
    _ = S * (Y * X) * S := by rw [hY]
    _ = S * Y * (X * S) := by simp only [mul_assoc]
    _ = S * Y * (S * X) := by rw [hS]
    _ = S * Y * S * X := by simp only [mul_assoc]

variable {K : Type*} [CommRing K] {q : K} [Invertible q] [Invertible (q - 1)]

/-! ### Commuting with the top element -/

/-- The upward induction: `y_i` commutes with `y_k` for `i ≤ k - 1`. The bound is not slack —
`y_k` does not commute with `T_{k-1}`, so the step cannot be taken at `i + 1 = k`. -/
theorem yElt_comm_top_aux {k : ℕ} :
    ∀ i : ℕ, 1 ≤ i → i + 1 ≤ k →
      yElt K q k i * yElt K q k k = yElt K q k k * yElt K q k i := by
  intro i h1
  induction i, h1 using Nat.le_induction with
  | base => intro hk; exact yElt_one_mul_yElt_top (by omega)
  | succ n hn ih =>
    intro hk
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have em : m + 1 - 1 = m := by omega
    have hrec : yElt K q k (m + 1 + 1)
        = q • (Tinv K q k m * yElt K q k (m + 1) * Tinv K q k m) := by
      have h := yElt_succ_eq (K := K) (q := q) (k := k) (i := m + 1) (by omega) (by omega)
      rw [em] at h
      exact h
    have hTg : yElt K q k k * Tg K q k m = Tg K q k m * yElt K q k k :=
      yElt_mul_Tg_comm (by omega) le_rfl (by omega) (by omega)
    have hT : Tinv K q k m * yElt K q k k = yElt K q k k * Tinv K q k m :=
      (comm_Tinv_of_comm_Tg (e_mul_yElt k k) (yElt_mul_e k k) hTg).symm
    have hY : yElt K q k (m + 1) * yElt K q k k = yElt K q k k * yElt K q k (m + 1) :=
      ih (by omega)
    rw [hrec, smul_mul_assoc, mul_smul_comm]
    congr 1
    exact comm_conj_aux hT hY

/-- Every corner element commutes with the top one. -/
theorem yElt_comm_top {k : ℕ} (i : ℕ) (h1 : 1 ≤ i) (hik : i ≤ k) :
    yElt K q k i * yElt K q k k = yElt K q k k * yElt K q k i := by
  rcases Nat.lt_or_ge i k with h | h
  · exact yElt_comm_top_aux i h1 (by omega)
  · obtain rfl : i = k := by omega
    rfl

/-! ### The general case -/

/-- The downward induction on `j`, run against an explicit bound on `k - j`. -/
theorem yElt_comm_aux {k : ℕ} :
    ∀ d i j : ℕ, k - j ≤ d → 1 ≤ i → i < j → j ≤ k →
      yElt K q k i * yElt K q k j = yElt K q k j * yElt K q k i := by
  intro d
  induction d with
  | zero =>
    intro i j hd h1 hij hjk
    obtain rfl : j = k := by omega
    exact yElt_comm_top i h1 (by omega)
  | succ d ih =>
    intro i j hd h1 hij hjk
    by_cases hjk' : j = k
    · subst hjk'
      exact yElt_comm_top i h1 (by omega)
    have hlt : j < k := by omega
    have hrec : yElt K q k j
        = ⅟q • (Tg K q k (j - 1) * yElt K q k (j + 1) * Tg K q k (j - 1)) :=
      yElt_recursion (by omega) hlt
    have hS : yElt K q k i * Tg K q k (j - 1) = Tg K q k (j - 1) * yElt K q k i :=
      yElt_mul_Tg_comm h1 (by omega) (by omega) (by omega)
    have hY : yElt K q k i * yElt K q k (j + 1) = yElt K q k (j + 1) * yElt K q k i :=
      ih i (j + 1) (by omega) h1 (by omega) (by omega)
    rw [hrec, mul_smul_comm, smul_mul_assoc]
    congr 1
    exact comm_triple_aux hS hY

/-- **The corner elements commute**: `y_iy_j = y_jy_i` in `e_k𝔸_qe_k` for all `1 ≤ i, j ≤ k`.

The range is every vertex `k ≥ 1`, the vertex `2` included, which is also the range of the relation
`y_iy_j = y_jy_i` (`1 ≤ i, j ≤ k`) in Mellit's §3.1; it is wider than the range `k ≥ 3` that a
route through the vertex `k-1` reaches. See this file's implementation notes for where the two
ranges part. -/
@[hjo "lem_dpa_y_commute"]
theorem yElt_comm {k i j : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    yElt K q k i * yElt K q k j = yElt K q k j * yElt K q k i := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact yElt_comm_aux k i j (by omega) hi1 h hjk
  · rfl
  · exact (yElt_comm_aux k j i (by omega) hj1 h hik).symm

attribute [hjo "lem_cm_yelement_commute"] yElt_comm

end HJO.Dyck.Aq
