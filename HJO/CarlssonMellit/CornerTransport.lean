/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ArrowWords
public import HJO.CarlssonMellit.CornerLowering
public import HJO.CarlssonMellit.CornerPowers
public meta import HJO.Attr

/-! # Transporting the corner elements along the arrows

The corner elements at successive vertices are matched by the two arrows: `d₋` carries `y_i` to
`y_i` with its subscript unchanged, and `d₊` carries `y_1` to a braid conjugate of `y_1`. This file
proves both, together with the commutation of `y_1` with the loops it does not involve.

## Main results

* `HJO.Dyck.Aq.yElt_mul_dMinus`: `y_i^{(k)}d₋ = d₋y_i^{(k+1)}` for every `1 ≤ i ≤ k`.
* `HJO.Dyck.Aq.dPlus_mul_yElt_one`: `d₊y_1^{(k)} = T_1y_1^{(k+1)}T_1^{-1}d₊`.
* `HJO.Dyck.Aq.yElt_one_mul_Tg`: `y_1T_j = T_jy_1` for `2 ≤ j ≤ k-1`.
* `HJO.Dyck.Aq.Delta_mul_Tg_source`: `D_kT_i = T_{i+1}D_k`, the commutator shift in the paper's
  own indexing.

## Implementation notes

`HJO.Dyck.Aq.yElt_mul_dMinus` is a *descending* induction on the subscript, so it is carried out on
the number of steps taken down from the top, which is the same reparametrisation
`HJO.Dyck.Aq.yAux` makes of the definition itself.

The lowering statement needs no hypothesis relating the two vertices beyond `1 ≤ i ≤ k`, but the
raising one is asymmetric: only the *first* corner element transports along `d₊`, and it does so up
to conjugation by `T_1`. That is not an artefact — `d₊` raises every loop index by one, so the
subscript cannot stay put, and `y_1` is the one element whose closed form
`HJO.Dyck.Aq.yElt_one_eq_Delta` puts the commutator on the left where the paper's
`T_1(d₊d₋-d₋d₊)d₊ = qd₊(d₊d₋-d₋d₊)` can act on it.

Indices are written `m + 1 + 1` rather than `m + 2` in the raising proof, matching the form the
surrounding lemmas produce; the relations that arrive as `m + 2` are restated by a `have`, which
typechecks on definitional equality.

## References

The lemmas `HJO.Dyck.Aq.yElt_mul_dMinus`, `HJO.Dyck.Aq.dPlus_mul_yElt_one`,
`HJO.Dyck.Aq.yElt_one_mul_Tg` and `HJO.Dyck.Aq.Delta_mul_Tg_source`, on the Dyck path algebra, its
involution, the loops and the braid generators; and E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q]

omit [Invertible q] in
/-- The descending word peels off its rightmost — that is, its lowest-index — letter. -/
theorem tSeg_succ_right (k a n : ℕ) :
    tSeg K q k a (n + 1) = tSeg K q k (a + 1) n * Tg K q k a := by
  induction n with
  | zero => rw [tSeg_succ, tSeg_zero, tSeg_zero, Nat.add_zero, e_mul_Tg, Tg_mul_e]
  | succ n ih =>
    rw [tSeg_succ, ih, ← mul_assoc, tSeg_succ k (a + 1) n,
      show a + (n + 1) = a + 1 + n by omega]

omit [Invertible q] in
/-- **The commutator shifts the loop index**, in the paper's own indexing: `D_kT_i = T_{i+1}D_k`
for `1 ≤ i ≤ k-2`, the loops being taken at the vertex `k` and `D_k` being
`HJO.Dyck.Aq.Delta K q (k-1)`. -/
@[hjo "lem_dpa_commutator_shift"]
theorem Delta_mul_Tg_source {k i : ℕ} (h1 : 1 ≤ i) (hi : i + 2 ≤ k) :
    Delta K q (k - 1) * Tg K q k (i - 1) = Tg K q k i * Delta K q (k - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simpa using Delta_mul_Tg (K := K) (q := q) (n := n) (m := j) (by omega)

variable [Invertible (q - 1)]

/-! ### Along the lowering arrow -/

/-- The descending induction behind `HJO.Dyck.Aq.yElt_mul_dMinus`, on the number `d` of steps taken
down from the top of the family. -/
theorem yElt_mul_dMinus_aux {k : ℕ} :
    ∀ d : ℕ, d + 1 ≤ k →
      yElt K q k (k - d) * dMinus K q k = dMinus K q k * yElt K q (k + 1) (k - d) := by
  intro d
  induction d with
  | zero => intro hd; rw [Nat.sub_zero]; exact yElt_top_mul_dMinus (by omega)
  | succ d ih =>
    intro hd
    have hi1 : 1 ≤ k - (d + 1) := by omega
    have hnext : k - (d + 1) + 1 = k - d := by omega
    have hcross : Tg K q k (k - (d + 1) - 1) * dMinus K q k
        = dMinus K q k * Tg K q (k + 1) (k - (d + 1) - 1) := Tg_mul_dMinus (by omega)
    rw [yElt_recursion hi1 (by omega), yElt_recursion hi1 (by omega), hnext,
      smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [mul_assoc (Tg K q k (k - (d + 1) - 1) * yElt K q k (k - d)), hcross,
      ← mul_assoc, ← mul_assoc, mul_assoc (Tg K q k (k - (d + 1) - 1)), ih (by omega),
      ← mul_assoc, hcross]
    simp only [mul_assoc]

/-- **The corner elements match across the lowering arrow**, with the subscript unchanged:
`y_i^{(k)}d₋ = d₋y_i^{(k+1)}` for every `1 ≤ i ≤ k`.

This is also `HJO.Dyck.Aq.yElt_mul_dMinus`, "a loop commutes with the lowering generator",
which states the same identity in Mellit's notation: `d_-y_i𝟏_k = y_id_-𝟏_k` for `k ≥ 2` and
`1 ≤ i ≤ k-1`. There `y_i𝟏_k` is the loop at the vertex `k` and the `y_i` on the right is the loop
at `k-1`, so the display is this equation read at `k - 1`, where the range `i ≤ k-1` is exactly the
hypothesis `i ≤ k` here. The same lemma thus appears twice, once in
each notation. -/
@[hjo "lem_dpa_y_dminus"]
theorem yElt_mul_dMinus {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    yElt K q k i * dMinus K q k = dMinus K q k * yElt K q (k + 1) i := by
  have h := yElt_mul_dMinus_aux (K := K) (q := q) (k := k) (k - i) (by omega)
  rwa [show k - (k - i) = i by omega] at h

attribute [hjo "lem_cm_yelement_dminus"] yElt_mul_dMinus

/-! ### `y_1` against the loops it does not involve -/

/-- **`y_1` commutes with the loops above the first**: `y_1T_j = T_jy_1` for `2 ≤ j ≤ k-1`. In the
shifted indexing the paper's `T_j` is `Tg k (m+1)` and the range reads `m + 3 ≤ k`. The descending
word inside `y_1` cycles the index down and the commutator cycles it back up. -/
@[hjo "lem_cm_yelement_one_tcommute"]
theorem yElt_one_mul_Tg {k m : ℕ} (h : m + 3 ≤ k) :
    yElt K q k 1 * Tg K q k (m + 1) = Tg K q k (m + 1) * yElt K q k 1 := by
  have hcyc : tSeg K q k 0 (k - 1) * Tg K q k (m + 1) = Tg K q k m * tSeg K q k 0 (k - 1) :=
    tSeg_mul_Tg_cycle (k - 1) (by omega) (by omega)
  have hshift : Delta K q (k - 1) * Tg K q k m = Tg K q k (m + 1) * Delta K q (k - 1) := by
    have h0 := Delta_mul_Tg_source (K := K) (q := q) (k := k) (i := m + 1) (by omega) (by omega)
    simpa using h0
  rw [yElt_one_eq_Delta (by omega), smul_mul_assoc, mul_smul_comm,
    mul_assoc (Delta K q (k - 1)) (tSeg K q k 0 (k - 1)) (Tg K q k (m + 1)), hcyc,
    ← mul_assoc (Delta K q (k - 1)) (Tg K q k m) (tSeg K q k 0 (k - 1)), hshift,
    mul_assoc (Tg K q k (m + 1)) (Delta K q (k - 1)) (tSeg K q k 0 (k - 1))]

/-! ### Along the raising arrow -/

/-- **The first corner element transports along the raising arrow, up to conjugation**:
`d₊y_1^{(k)} = T_1y_1^{(k+1)}T_1^{-1}d₊`. The raising arrow shifts every loop index up by one, so
the subscript cannot stay put as it does across `d₋`; what makes `y_1` transport at all is that its
closed form carries the commutator on the left, where the paper's
`T_1(d₊d₋-d₋d₊)d₊ = qd₊(d₊d₋-d₋d₊)` acts on it. -/
@[hjo "lem_cm_yelement_dplus_one"]
theorem dPlus_mul_yElt_one {k : ℕ} (hk : 1 ≤ k) :
    dPlus K q k * yElt K q k 1
      = Tg K q (k + 1) 0 * yElt K q (k + 1) 1 * Tinv K q (k + 1) 0 * dPlus K q k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hdp : dPlus K q (m + 1) * tSeg K q (m + 1) 0 m
      = tSeg K q (m + 1 + 1) 1 m * dPlus K q (m + 1) := dPlus_mul_tSeg m le_rfl
  have hTD : dPlus K q (m + 1) * Delta K q m
      = ⅟q • (Tg K q (m + 1 + 1) 0 * Delta K q (m + 1) * dPlus K q (m + 1)) := by
    have h : Tg K q (m + 1 + 1) 0 * Delta K q (m + 1) * dPlus K q (m + 1)
        = q • (dPlus K q (m + 1) * Delta K q m) := Tg_mul_Delta m
    rw [h, smul_smul, invOf_mul_self, one_smul]
  have hL : dPlus K q (m + 1) * yElt K q (m + 1) 1
      = ((⅟q) ^ (m + 1) * ⅟(q - 1)) •
        (Tg K q (m + 1 + 1) 0 * Delta K q (m + 1) * tSeg K q (m + 1 + 1) 1 m *
          dPlus K q (m + 1)) := by
    rw [yElt_one_eq_Delta (K := K) (q := q) (k := m + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [mul_smul_comm, ← mul_assoc (dPlus K q (m + 1)) (Delta K q m) (tSeg K q (m + 1) 0 m),
      hTD, smul_mul_assoc, smul_smul,
      mul_assoc (Tg K q (m + 1 + 1) 0 * Delta K q (m + 1)) (dPlus K q (m + 1))
        (tSeg K q (m + 1) 0 m), hdp,
      ← mul_assoc (Tg K q (m + 1 + 1) 0 * Delta K q (m + 1)) (tSeg K q (m + 1 + 1) 1 m)
        (dPlus K q (m + 1))]
    congr 1
    ring
  have hR : Tg K q (m + 1 + 1) 0 * yElt K q (m + 1 + 1) 1 * Tinv K q (m + 1 + 1) 0 *
        dPlus K q (m + 1)
      = ((⅟q) ^ (m + 1) * ⅟(q - 1)) •
        (Tg K q (m + 1 + 1) 0 * Delta K q (m + 1) * tSeg K q (m + 1 + 1) 1 m *
          dPlus K q (m + 1)) := by
    rw [yElt_one_eq_Delta (K := K) (q := q) (k := m + 1 + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
    congr 1
    rw [tSeg_succ_right]
    simp only [Nat.zero_add]
    rw [show Tg K q (m + 1 + 1) 0 *
            (Delta K q (m + 1) * (tSeg K q (m + 1 + 1) 1 m * Tg K q (m + 1 + 1) 0)) *
            Tinv K q (m + 1 + 1) 0 * dPlus K q (m + 1)
          = Tg K q (m + 1 + 1) 0 * Delta K q (m + 1) * tSeg K q (m + 1 + 1) 1 m *
            (Tg K q (m + 1 + 1) 0 * Tinv K q (m + 1 + 1) 0) * dPlus K q (m + 1)
        from by simp only [mul_assoc], Tg_mul_Tinv (by omega),
      show Tg K q (m + 1 + 1) 0 * Delta K q (m + 1) * tSeg K q (m + 1 + 1) 1 m *
            e K q (m + 1 + 1) * dPlus K q (m + 1)
          = Tg K q (m + 1 + 1) 0 * Delta K q (m + 1) * tSeg K q (m + 1 + 1) 1 m *
            (e K q (m + 1 + 1) * dPlus K q (m + 1)) from by simp only [mul_assoc],
      e_mul_dPlus]
  rw [hL, hR]

end HJO.Dyck.Aq
