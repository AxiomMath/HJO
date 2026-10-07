/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerMellit
public import HJO.CarlssonMellit.CornerRaising
public import HJO.CarlssonMellit.TildeZ1
public meta import HJO.Attr

/-! # Two identities of the double algebra in Mellit's own notation

Two facts already proved in Carlsson and Mellit's notation are restated here, in the notation of
Mellit's §3:

* `HJO.Dyck.Tilde.Atilde.zElt_succ_eq`: `z_{i+1}𝟏_k = q^{-1}T_iz_iT_i𝟏_k`, the conjugate loops
  descending by conjugation. This is the inverse of the recursion `HJO.Dyck.cornerOf`'s definition
  builds in, read at the *starred* family of `Ã` — and that is the proof: the upward
  recursion `HJO.Dyck.Aq.yElt_succ_eq_units` is a consequence of the two formulas of
  `HJO.Dyck.Aq.yElt` alone, so the substitution `q ↦ q^{-1}`, `T_i ↦ T_i^{-1}` carries it over.
  Here `z_i` *is*
  `HJO.Dyck.cornerOf` at that substituted family (`HJO.Dyck.Tilde.Atilde.zElt`), so the transport is
  an instantiation and not a second proof.

* `HJO.Dyck.Aq.dPlus_mul_yElt_words`: `d_+y_i𝟏_k = T_{1↑i+1}\,y_i\,T^*_{i+1↓1}\,d_+𝟏_k`. This is
  verbatim the earlier lemma `HJO.Dyck.Aq.dPlus_mul_yElt`, whose conjugating words are written there
  as `HJO.Dyck.Aq.tSegUp` and `HJO.Dyck.Aq.tinvWord`; all that is supplied here is the
  identification of those two words with the `HJO.Braid.wordUp` and `HJO.Braid.wordDownStar` of
  `HJO/Shuffle/DpaWords.lean`, read on the loops as units of the corner
  `𝟏_{k+1}𝔸_q𝟏_{k+1}`. So one lemma appears twice, once in each notation; the corresponding
  statement for the lowering arrow reads the same in both notations and is the single lemma
  `HJO.Dyck.Aq.yElt_mul_dMinus`.

## Main results

* `HJO.Dyck.Tilde.Atilde.zElt_succ_eq`.
* `HJO.Dyck.Aq.cval_wordDownStar` — Mellit's `T^*_{j↓1}` is `HJO.Dyck.Aq.tinvWord`.
* `HJO.Dyck.Aq.dPlus_mul_yElt_words`.

## Implementation notes

In the shifted indexing of `HJO.Dyck.Aq.Tg` and `HJO.Dyck.Tilde.Atilde.Tg` the paper's `T_i` is
`Tg k (i - 1)`, so `HJO.Dyck.Tilde.Atilde.zElt_succ_eq`'s `T_i` is `Tg K q u k (i - 1)` and its
`1 ≤ i ≤ k-1` is `1 ≤ i` together with `i < k`; the truncated subtraction is exact there. The `𝟏_k`
of the displayed formula is not written: every element named is already absorbed by the idempotent
on both sides (`HJO.Dyck.Tilde.Atilde.e_mul_zElt`, `zElt_mul_e`), which is what makes the two-sided
multiplication by `T_i` a conjugation in the corner.

`HJO.Dyck.Aq.cval_wordDownStar` is the mirror of `HJO.Dyck.Aq.cval_wordUp` and peels the same way,
through the generic `HJO.Dyck.Tilde.Atilde.wordDownStar_peel` — a statement about an arbitrary
family of units in an arbitrary monoid, so it serves both `Ã` and `𝔸_q` and no list arithmetic is
redone.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3. -/

@[expose] public section

namespace HJO.Dyck.Tilde.Atilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-! ### The conjugate loops descend by conjugation -/

/-- The conjugate loops are loops at their vertex, from the starred corner family. -/
@[simp]
theorem e_mul_zElt (k i : ℕ) : e K q u k * zElt K q u k i = zElt K q u k i :=
  CornerFamily.e_mul_cornerOf (di := -(q * ⅟(q - 1))) starFamily k i

@[simp]
theorem zElt_mul_e (k i : ℕ) : zElt K q u k i * e K q u k = zElt K q u k i :=
  CornerFamily.cornerOf_mul_e (di := -(q * ⅟(q - 1))) starFamily k i

/-- **The conjugate loops descend by conjugation**, `HJO.Dyck.Tilde.Atilde.zElt_succ_eq`:
`z_{i+1}𝟏_k = q^{-1}T_iz_iT_i𝟏_k` for `1 ≤ i ≤ k-1`, the paper's `T_i` being `Tg K q u k (i-1)`.

`HJO.Dyck.cornerOf`'s own recursion, read at the starred family, is `z_i = qT̂_iz_{i+1}T̂_i`;
conjugating by `T_i` on both sides cancels the two `T̂_i` against it
(`HJO.Dyck.Tilde.Atilde.Tg_mul_Tinv`, `Tinv_mul_Tg`), the idempotents they leave behind are absorbed
by `z_{i+1}`, and the two scalars `q` and `q^{-1}` cancel. -/
@[hjo "lem_dpa_z_recursion"]
theorem zElt_succ_eq {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    zElt K q u k (i + 1) = ⅟q • (Tg K q u k (i - 1) * zElt K q u k i * Tg K q u k (i - 1)) := by
  have hadm : i - 1 + 2 ≤ k := by omega
  have hrec : zElt K q u k i
      = q • (Tinv K q u k (i - 1) * zElt K q u k (i + 1) * Tinv K q u k (i - 1)) :=
    cornerOf_recursion h1 hik
  rw [hrec, mul_smul_comm, smul_mul_assoc, smul_smul, invOf_mul_self, one_smul,
    show Tg K q u k (i - 1) *
          (Tinv K q u k (i - 1) * zElt K q u k (i + 1) * Tinv K q u k (i - 1)) *
          Tg K q u k (i - 1)
        = Tg K q u k (i - 1) * Tinv K q u k (i - 1) * zElt K q u k (i + 1) *
          (Tinv K q u k (i - 1) * Tg K q u k (i - 1)) from by simp only [mul_assoc],
    Tg_mul_Tinv hadm, Tinv_mul_Tg hadm, e_mul_zElt, zElt_mul_e]

end HJO.Dyck.Tilde.Atilde

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q]

/-! ### Mellit's starred descending word in `𝟏_k𝔸_q𝟏_k` -/

/-- **Mellit's `T^*_{n+1↓1}` is the descending word of the polynomial inverses** `T̂_n ⋯ T̂_1`,
which in the shifted indexing of `HJO.Dyck.Aq.Tinv` is `HJO.Dyck.Aq.tinvWord k n`; the empty word
is the idempotent on both sides. The mirror of `HJO.Dyck.Aq.cval_wordUp`. -/
theorem cval_wordDownStar {k : ℕ} :
    ∀ n : ℕ, n + 1 ≤ k →
      cval (HJO.Braid.wordDownStar (braidUnits K q k) (n + 1) 1) = tinvWord K q k n := by
  intro n
  induction n with
  | zero => intro _; rw [HJO.Braid.wordDownStar_self, cval_one, tinvWord_zero]
  | succ n ih =>
    intro hn
    rw [HJO.Dyck.Tilde.Atilde.wordDownStar_peel, cval_mul,
      cval_braidUnits_inv (by omega) (by omega), ih (by omega), tinvWord_succ, Nat.add_sub_cancel]

/-! ### The raising arrow and the loops, in Mellit's notation -/

variable [Invertible (q - 1)]

/-- **The raising arrow and the loops**, `HJO.Dyck.Aq.dPlus_mul_yElt_words`:
`d_+y_i𝟏_k = T_{1↑i+1}\,y_i\,T^*_{i+1↓1}\,d_+𝟏_k` for `1 ≤ i ≤ k`, the words being those of
`HJO.Braid.wordUp` and `HJO.Braid.wordDownStar` for the loops `T_1, …, T_k` of
`𝟏_{k+1}𝔸_q𝟏_{k+1}` read as units.

It is the earlier lemma `HJO.Dyck.Aq.dPlus_mul_yElt` with its two conjugating
words renamed: `T_{1↑i+1}` is `HJO.Dyck.Aq.tSegUp (k+1) 0 i` by `HJO.Dyck.Aq.cval_wordUp` and
`T^*_{i+1↓1}` is `HJO.Dyck.Aq.tinvWord (k+1) i` by `HJO.Dyck.Aq.cval_wordDownStar`. The lemma
thus appears twice, once in each notation. -/
@[hjo "lem_dpa_y_dplus"]
theorem dPlus_mul_yElt_words {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    dPlus K q k * yElt K q k i
      = cval (HJO.Braid.wordUp (braidUnits K q (k + 1)) 1 (i + 1)) * yElt K q (k + 1) i *
        cval (HJO.Braid.wordDownStar (braidUnits K q (k + 1)) (i + 1) 1) * dPlus K q k := by
  rw [cval_wordUp i (by omega), cval_wordDownStar i (by omega)]
  exact dPlus_mul_yElt i h1 hik

end HJO.Dyck.Aq
