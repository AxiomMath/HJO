/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerTransport
public meta import HJO.Attr

/-! # The commutator conjugates the first corner element

The commutator `D_k` is a loop at the vertex `k` built from one step down and one step back up, so
what it does to `y_1` is the composite of what the two arrows do: `d₋` leaves the subscript alone
and `d₊` conjugates by `T_1`. The net effect is that `D_k` conjugates `y_1` by `T_1`.

## Main results

* `HJO.Dyck.Aq.Delta_mul_yElt_one`: `D_ky_1 = T_1y_1T_1^{-1}D_k`.

## Implementation notes

The two summands of `D_k` are treated separately and give the *same* conjugation, which is why the
difference survives. They get there by different routes: in `d₊d₋` the lowering arrow acts first
and drops the vertex, so the raising lemma is read one vertex lower; in `d₋d₊` the raising arrow
acts first and the conjugating loop then has to be carried back down past `d₋`, which it can
because `T_1` and `T̂_1` both commute with the lowering arrow.

Vertices are written `n + 1 + 1` rather than `n + 2`, matching the form
`HJO.Dyck.Aq.dPlus_mul_yElt_one` produces, so that `rw` matches syntactically.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31**
(2018) 661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q] [Invertible (q - 1)]

/-- **The commutator conjugates the first corner element**: `D_ky_1 = T_1y_1T_1^{-1}D_k` in
`e_k𝔸_qe_k` for `k ≥ 2`, read here at `k = n + 1` with `D_k = Delta K q n`. -/
@[hjo "lem_cm_commutator_conj_y1"]
theorem Delta_mul_yElt_one {n : ℕ} (hn : 1 ≤ n) :
    Delta K q n * yElt K q (n + 1) 1
      = Tg K q (n + 1) 0 * yElt K q (n + 1) 1 * Tinv K q (n + 1) 0 * Delta K q n := by
  have hTg : Tg K q (n + 1) 0 * dMinus K q (n + 1)
      = dMinus K q (n + 1) * Tg K q (n + 1 + 1) 0 := Tg_mul_dMinus (by omega)
  have hTi : Tinv K q (n + 1) 0 * dMinus K q (n + 1)
      = dMinus K q (n + 1) * Tinv K q (n + 1 + 1) 0 := Tinv_mul_dMinus (by omega)
  have hy : yElt K q (n + 1) 1 * dMinus K q (n + 1)
      = dMinus K q (n + 1) * yElt K q (n + 1 + 1) 1 := yElt_mul_dMinus le_rfl (by omega)
  have h1 : dPlus K q n * dMinus K q n * yElt K q (n + 1) 1
      = Tg K q (n + 1) 0 * yElt K q (n + 1) 1 * Tinv K q (n + 1) 0 *
        (dPlus K q n * dMinus K q n) := by
    rw [mul_assoc, ← yElt_mul_dMinus (k := n) (i := 1) le_rfl hn, ← mul_assoc,
      dPlus_mul_yElt_one hn]
    simp only [mul_assoc]
  have h2 : dMinus K q (n + 1) * dPlus K q (n + 1) * yElt K q (n + 1) 1
      = Tg K q (n + 1) 0 * yElt K q (n + 1) 1 * Tinv K q (n + 1) 0 *
        (dMinus K q (n + 1) * dPlus K q (n + 1)) := by
    rw [mul_assoc, dPlus_mul_yElt_one (by omega : 1 ≤ n + 1),
      show dMinus K q (n + 1) * (Tg K q (n + 1 + 1) 0 * yElt K q (n + 1 + 1) 1 *
            Tinv K q (n + 1 + 1) 0 * dPlus K q (n + 1))
          = dMinus K q (n + 1) * Tg K q (n + 1 + 1) 0 * yElt K q (n + 1 + 1) 1 *
            Tinv K q (n + 1 + 1) 0 * dPlus K q (n + 1) from by simp only [mul_assoc],
      ← hTg,
      show Tg K q (n + 1) 0 * dMinus K q (n + 1) * yElt K q (n + 1 + 1) 1 *
            Tinv K q (n + 1 + 1) 0 * dPlus K q (n + 1)
          = Tg K q (n + 1) 0 * (dMinus K q (n + 1) * yElt K q (n + 1 + 1) 1) *
            Tinv K q (n + 1 + 1) 0 * dPlus K q (n + 1) from by simp only [mul_assoc],
      ← hy,
      show Tg K q (n + 1) 0 * (yElt K q (n + 1) 1 * dMinus K q (n + 1)) *
            Tinv K q (n + 1 + 1) 0 * dPlus K q (n + 1)
          = Tg K q (n + 1) 0 * yElt K q (n + 1) 1 *
            (dMinus K q (n + 1) * Tinv K q (n + 1 + 1) 0) * dPlus K q (n + 1)
        from by simp only [mul_assoc],
      ← hTi]
    simp only [mul_assoc]
  rw [Delta_eq K q n, sub_mul, h1, h2, ← mul_sub, ← Delta_eq K q n]

end HJO.Dyck.Aq
