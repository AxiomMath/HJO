/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerRing
public import HJO.CarlssonMellit.CornerTransport
public meta import HJO.Attr

/-! # The corner-element calculus in Mellit's notation

The module `HJO.CarlssonMellit.CornerRing` makes Mellit's `𝟏_k𝔸_q𝟏_k` and his words in
*invertible* letters available; this file reads three more of the paper's identities in that
notation. Each is an identity already proved in `𝔸_q`, but stated through the loops as units of
the corner and through `HJO.Braid.wordUp` / `HJO.Braid.wordDown`, which is the notation used for
the double algebra.

## Main results

* `HJO.Dyck.Aq.cval_wordUp`: Mellit's ascending word `T_{1↑k}` is `HJO.Dyck.Aq.tSegUp`.
* `HJO.Dyck.Aq.yElt_succ_eq_units`: `y_{i+1}𝟏_k = qT_i^{-1}y_iT_i^{-1}𝟏_k`, the inverse being
  that of the unit.
* `HJO.Dyck.Aq.Delta_eq_wordUp`: `(d₊d₋-d₋d₊)𝟏_k = (q-1)T_{1↑k}y_k𝟏_k`.
* `HJO.Dyck.Aq.yElt_one_mul_Tg_wordDown`: `y_1T_j𝟏_k = T_jy_1𝟏_k`.

## Implementation notes

`HJO.Dyck.Aq.cval_wordUp` is the mirror of `HJO.Dyck.Aq.cval_wordDown`, and peels the same way:
`HJO.Braid.ascendingWord_mul` splits off the last letter and `HJO.Braid.ascendingWord_succ_self`
reads it, so no `List.range'` arithmetic is redone. The ascending word peels on the *right*, which
is exactly how `HJO.Dyck.Aq.tSegUp` recurses.

`HJO.Dyck.Aq.yElt_one_mul_Tg_wordDown` has the same statement as
`HJO.Dyck.Aq.yElt_one_mul_Tg` — the claim is stated twice, once in each
notation — but it is proved here by a different route: through the closed form
`HJO.Dyck.Aq.yElt_one_eq_wordDown`, then `HJO.Dyck.Aq.wordDown_mul_Tg_cycle` to move the loop past
the word, then `HJO.Dyck.Aq.Delta_mul_Tg_source` to move it past the commutator. That is a genuine
check on the bridge rather than a restatement of its twin `HJO.Dyck.Aq.yElt_one_mul_Tg`, which is
proved from the ascending-word closed form instead.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q]

/-! ### The inverses of the unit letters -/

/-- The inverse of the `r`-th unit letter is the polynomial inverse of the loop it names. -/
theorem cval_braidUnits_inv {k r : ℕ} (h1 : 1 ≤ r) (h2 : r + 1 ≤ k) :
    cval (((braidUnits K q k r)⁻¹ : (Corner K q k)ˣ) : Corner K q k) = Tinv K q k (r - 1) := by
  have hc : 1 ≤ r ∧ r + 1 ≤ k := ⟨h1, h2⟩
  simp only [braidUnits, hc]
  rfl

/-! ### Mellit's ascending word -/

/-- The ascending word of units peels off its rightmost letter, which is how
`HJO.Dyck.Aq.tSegUp` recurses. -/
theorem wordUp_peel {A : Type*} [Monoid A] (S : ℕ → Aˣ) (n : ℕ) :
    HJO.Braid.wordUp S 1 (n + 1 + 1) = HJO.Braid.wordUp S 1 (n + 1) * (S (n + 1) : A) := by
  simp only [HJO.Braid.wordUp]
  rw [← HJO.Braid.ascendingWord_mul (fun r => ((S r : A))) (by omega : 1 ≤ n + 1)
    (by omega : n + 1 ≤ n + 1 + 1), HJO.Braid.ascendingWord_succ_self]

/-- **Mellit's `T_{1↑k}` is the ascending word of loops** `T_1 ⋯ T_{k-1}`, which in the shifted
indexing of `HJO.Dyck.Aq.Tg` is `tSegUp k 0 (k-1)`; the empty word is the idempotent on both
sides. -/
theorem cval_wordUp {k : ℕ} :
    ∀ n : ℕ, n + 1 ≤ k →
      cval (HJO.Braid.wordUp (braidUnits K q k) 1 (n + 1)) = tSegUp K q k 0 n := by
  intro n
  induction n with
  | zero => intro _; rw [HJO.Braid.wordUp_self, cval_one, tSegUp_zero]
  | succ n ih =>
    intro hn
    rw [wordUp_peel, cval_mul, ih (by omega), cval_braidUnits (by omega) (by omega),
      tSegUp_succ, Nat.zero_add, Nat.add_sub_cancel]

/-! ### The three identities -/

variable [Invertible (q - 1)]

/-- **The upward recursion in Mellit's notation**: `y_{i+1}𝟏_k = qT_i^{-1}y_iT_i^{-1}𝟏_k`, where
`T_i^{-1}` is the inverse of the unit `T_i` of `𝟏_k𝔸_q𝟏_k` supplied by
`HJO.Dyck.Aq.isUnit_braid_corner`. -/
@[hjo "lem_dpa_y_recursion_up"]
theorem yElt_succ_eq_units {k i : ℕ} (h1 : 1 ≤ i) (h2 : i + 1 ≤ k) :
    yElt K q k (i + 1)
      = q • (cval (((braidUnits K q k i)⁻¹ : (Corner K q k)ˣ) : Corner K q k) * yElt K q k i *
          cval (((braidUnits K q k i)⁻¹ : (Corner K q k)ˣ) : Corner K q k)) := by
  rw [cval_braidUnits_inv h1 h2]
  exact yElt_succ_eq h1 (by omega)

/-- **The commutator as the ascending word times the top corner element**:
`(d₊d₋-d₋d₊)𝟏_k = (q-1)T_{1↑k}y_k𝟏_k`, the word being the idempotent when `k = 1`. -/
@[hjo "lem_dpa_commutator_top"]
theorem Delta_eq_wordUp {k : ℕ} (hk : 1 ≤ k) :
    Delta K q (k - 1)
      = (q - 1) • (cval (HJO.Braid.wordUp (braidUnits K q k) 1 k) * yElt K q k k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [cval_wordUp m (by omega), Delta_eq_smul_tSegUp_mul_yElt (by omega)]
  simp only [Nat.add_sub_cancel]

/-- **`y_1` commutes with the loops above the first**, by the descending-word route: the closed form
puts the commutator in front of `T_{k↓1}`, the word cycles the loop's index down, and the commutator
cycles it back up. The twin `HJO.Dyck.Aq.yElt_one_mul_Tg` is the same claim proved from the
ascending-word closed form instead. -/
@[hjo "lem_dpa_y1_braid"]
theorem yElt_one_mul_Tg_wordDown {k m : ℕ} (h : m + 3 ≤ k) :
    yElt K q k 1 * Tg K q k (m + 1) = Tg K q k (m + 1) * yElt K q k 1 := by
  have hy := yElt_one_eq_wordDown (K := K) (q := q) (k := k) (by omega)
  have hW := wordDown_mul_Tg_cycle (K := K) (q := q) (k := k) (m := m) h
  have hD : Delta K q (k - 1) * Tg K q k m = Tg K q k (m + 1) * Delta K q (k - 1) := by
    have h0 := Delta_mul_Tg_source (K := K) (q := q) (k := k) (i := m + 1) (by omega) (by omega)
    simpa using h0
  rw [hy, smul_mul_assoc, mul_smul_comm, mul_assoc, hW, ← mul_assoc, hD, mul_assoc]

end HJO.Dyck.Aq
