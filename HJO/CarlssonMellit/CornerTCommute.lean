/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerTransport
public meta import HJO.Attr

/-! # The corner elements commute with the loops that do not touch them

The loop `T_j` acts on the two adjacent corner elements `y_j` and `y_{j+1}` and on nothing else: it
commutes with every `y_i` for `i ∉ {j, j+1}`. This file proves that.

## Main results

* `HJO.Dyck.Aq.yElt_mul_Tg_comm`: `y_iT_j = T_jy_i` whenever `i ∉ {j, j+1}`.

## Implementation notes

The condition "`1 ≤ j ≤ k-1` with `j ≠ i` and `j ≠ i-1`" of the paper is exactly `i ∉ {j, j+1}`.
In the shifted loop indexing of `HJO.Dyck.Aq.Tg` — where the paper's `T_j` is `Tg k s` with
`s = j-1` — that is `i ∉ {s+1, s+2}`, and it is stated here as the disjunction
`s + 3 ≤ i ∨ i ≤ s`. Writing it that way keeps `omega` in charge of the case analysis and keeps
truncated subtraction out of the statement entirely.

The induction is on `i` and descends by *one or two* steps — one when the loop is far from the
recursion's own loop, two when it is adjacent — so it is a strong induction. It is run against an
explicit bound `N` rather than through a well-founded recursion combinator, which keeps the
recursive calls' side conditions ordinary arithmetic.

Two abstract ring lemmas carry the algebra, `HJO.Dyck.Aq.comm_conj_aux` and
`HJO.Dyck.Aq.braid_conj_move`: the first says that conjugation by a commuting element preserves
commutation, the second is the two-step case, where the loop has to be braided past the two
conjugating inverses. With opaque atoms the rewrites can be aimed, which in a noncommutative ring
with no `ring` tactic is the difference between a calc block and a fight.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck.Aq

/-! ### The two abstract moves -/

/-- Conjugation by a commuting element preserves commutation. -/
theorem comm_conj_aux {A₀ : Type*} [Ring A₀] {T Y S : A₀} (hT : T * S = S * T)
    (hY : Y * S = S * Y) : T * Y * T * S = S * (T * Y * T) := by
  calc T * Y * T * S = T * (Y * (T * S)) := by simp only [mul_assoc]
    _ = T * (Y * (S * T)) := by rw [hT]
    _ = T * (Y * S * T) := by simp only [mul_assoc]
    _ = T * (S * Y * T) := by rw [hY]
    _ = T * S * (Y * T) := by simp only [mul_assoc]
    _ = S * T * (Y * T) := by rw [hT]
    _ = S * (T * Y * T) := by simp only [mul_assoc]

/-- The two-step move: when the loop `S` is adjacent to the inner conjugating element `B`, it is
braided outwards past both inverses, turning into the far loop `R` in the middle — which the
element `Y` does commute with — and back into `S` on the outside. -/
theorem braid_conj_move {A₀ : Type*} [Ring A₀] {A B S R Y : A₀}
    (h1 : B * (A * S) = R * (B * A)) (h2 : A * (B * R) = S * (A * B)) (hY : Y * R = R * Y) :
    A * (B * Y * B) * A * S = S * (A * (B * Y * B) * A) := by
  calc A * (B * Y * B) * A * S = A * (B * (Y * (B * (A * S)))) := by simp only [mul_assoc]
    _ = A * (B * (Y * (R * (B * A)))) := by rw [h1]
    _ = A * (B * (Y * R * (B * A))) := by simp only [mul_assoc]
    _ = A * (B * (R * Y * (B * A))) := by rw [hY]
    _ = A * (B * R) * (Y * (B * A)) := by simp only [mul_assoc]
    _ = S * (A * B) * (Y * (B * A)) := by rw [h2]
    _ = S * (A * (B * Y * B) * A) := by simp only [mul_assoc]

/-! ### The commutation -/

variable {K : Type*} [CommRing K] {q : K} [Invertible q] [Invertible (q - 1)]

omit [Invertible (q - 1)] in
/-- A loop commutes with the polynomial inverse of a loop two or more indices away. -/
theorem Tinv_comm_Tg {k b s : ℕ} (hTgComm : Tg K q k b * Tg K q k s = Tg K q k s * Tg K q k b) :
    Tinv K q k b * Tg K q k s = Tg K q k s * Tinv K q k b := by
  simp only [Tinv_eq, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, e_mul_Tg, Tg_mul_e,
    hTgComm]

/-- The strong induction behind `HJO.Dyck.Aq.yElt_mul_Tg_comm`, run against an explicit bound. -/
theorem yElt_mul_Tg_comm_aux :
    ∀ N i k s : ℕ, i ≤ N → 1 ≤ i → i ≤ k → s + 2 ≤ k → (s + 3 ≤ i ∨ i ≤ s) →
      yElt K q k i * Tg K q k s = Tg K q k s * yElt K q k i := by
  intro N
  induction N with
  | zero => intro i k s hN h1 _ _ _; omega
  | succ N ih =>
    intro i k s hN h1 hik hs hadm
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · obtain rfl : i = 1 := by omega
      obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
      exact yElt_one_mul_Tg (by omega)
    obtain ⟨b, rfl⟩ : ∃ b, i = b + 2 := ⟨i - 2, by omega⟩
    have hrec : yElt K q k (b + 2)
        = q • (Tinv K q k b * yElt K q k (b + 1) * Tinv K q k b) := by
      have h := yElt_succ_eq (K := K) (q := q) (k := k) (i := b + 1) (by omega) (by omega)
      have e : b + 1 - 1 = b := by omega
      rw [e] at h
      exact h
    rcases (by omega : (s + 2 ≤ b ∨ b + 2 ≤ s) ∨ s + 1 = b) with hc | hc
    · have hTgComm : Tg K q k b * Tg K q k s = Tg K q k s * Tg K q k b := by
        rcases hc with hc | hc
        · exact (Tg_comm (by omega) (by omega) (by omega)).symm
        · exact Tg_comm (by omega) (by omega) (by omega)
      have hyc : yElt K q k (b + 1) * Tg K q k s = Tg K q k s * yElt K q k (b + 1) :=
        ih (b + 1) k s (by omega) (by omega) (by omega) hs (by omega)
      rw [hrec, smul_mul_assoc, mul_smul_comm]
      congr 1
      exact comm_conj_aux (Tinv_comm_Tg hTgComm) hyc
    · obtain rfl : b = s + 1 := hc.symm
      have hrec2 : yElt K q k (s + 1 + 1)
          = q • (Tinv K q k s * yElt K q k (s + 1) * Tinv K q k s) := by
        have h := yElt_succ_eq (K := K) (q := q) (k := k) (i := s + 1) (by omega) (by omega)
        have e : s + 1 - 1 = s := by omega
        rw [e] at h
        exact h
      have hbraid1 : Tinv K q k s * (Tinv K q k (s + 1) * Tg K q k s)
          = Tg K q k (s + 1) * (Tinv K q k s * Tinv K q k (s + 1)) :=
        Tinv_mul_Tinv_mul_Tg (by omega) (by omega) (Or.inr rfl)
      have hbraid2 : Tinv K q k (s + 1) * (Tinv K q k s * Tg K q k (s + 1))
          = Tg K q k s * (Tinv K q k (s + 1) * Tinv K q k s) :=
        Tinv_mul_Tinv_mul_Tg (by omega) (by omega) (Or.inl rfl)
      have hY : yElt K q k (s + 1) * Tg K q k (s + 1)
          = Tg K q k (s + 1) * yElt K q k (s + 1) :=
        ih (s + 1) k (s + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hrec, hrec2]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      congr 1
      exact braid_conj_move hbraid1 hbraid2 hY

/-- **A corner element commutes with every loop that does not touch it**: `y_iT_j = T_jy_i` for
`1 ≤ i ≤ k` and `1 ≤ j ≤ k-1` with `j ≠ i` and `j ≠ i-1`. In the shifted loop indexing the paper's
`T_j` is `Tg k s` with `s = j - 1`, and the condition on `j` is the disjunction
`s + 3 ≤ i ∨ i ≤ s`. -/
@[hjo "lem_cm_yelement_tcommute"]
theorem yElt_mul_Tg_comm {k i s : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) (hs : s + 2 ≤ k)
    (hadm : s + 3 ≤ i ∨ i ≤ s) :
    yElt K q k i * Tg K q k s = Tg K q k s * yElt K q k i :=
  yElt_mul_Tg_comm_aux i i k s le_rfl h1 hik hs hadm

end HJO.Dyck.Aq
