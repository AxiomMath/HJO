/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerCalculus
public meta import HJO.Attr

/-! # The top corner element against the lowering arrow

The corner elements at successive vertices are matched by the lowering arrow: the top element at
the vertex `k` followed by `d₋` is `d₋` followed by the element `y_k` of the vertex `k + 1`. This
file proves that, together with the commutation of `d₋` past the polynomial inverses that it needs.

## Main results

* `HJO.Dyck.Aq.Tinv_mul_dMinus`: `T̂_id₋ = d₋T̂_i`, the paper's `T_id₋ = d₋T_i` for the inverses.
* `HJO.Dyck.Aq.tinvWord_mul_dMinus`: the same for the whole descending word.
* `HJO.Dyck.Aq.yElt_top_mul_dMinus`: `y_k^{(k)}d₋ = d₋y_k^{(k+1)}`.

## Implementation notes

The arrow's index is what makes the statement non-trivial: `d₋` is the arrow from `k + 1` to `k`,
so the loops on its left are at the vertex `k` and those on its right at the vertex `k + 1`, and
the corner element on its left is the one of `e_k𝔸_qe_k` while the one on its right is the *same
subscript* `k` at the vertex `k + 1`, which there is not the top element but one step down.

`d₋` passes the *inverses* by the same relation that lets it pass the loops, because the inverse is
a combination of the loop and the idempotent and both cross: `HJO.Dyck.Aq.Tinv_mul_dMinus` is one
`simp only` from `HJO.Dyck.Aq.Tg_mul_dMinus`.

Vertex indices are written as `m + 1 + 1` rather than `m + 2` throughout the main proof, because
that is the form the surrounding lemmas produce and `rw` matches syntactically; the relations
imported in the shape `m + 2` are restated at `m + 1 + 1` by a `have`, which typechecks because the
two are definitionally equal. Doing it the other way round means a `rw` that silently does not
fire.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q]

/-- **The lowering arrow passes a polynomial inverse** with the loop index unchanged and the vertex
dropping by one: the paper's `T_id₋ = d₋T_i` read for `T̂_i`, which holds because `T̂_i` is a
combination of `T_i` and the idempotent and both cross the arrow. -/
theorem Tinv_mul_dMinus {k i : ℕ} (h : i + 2 ≤ k) :
    Tinv K q k i * dMinus K q k = dMinus K q k * Tinv K q (k + 1) i := by
  simp only [Tinv_eq, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, Tg_mul_dMinus h,
    e_mul_dMinus, dMinus_mul_e]

/-- **The lowering arrow passes the whole descending word of inverses.** -/
theorem tinvWord_mul_dMinus {k : ℕ} :
    ∀ n : ℕ, n + 1 ≤ k →
      tinvWord K q k n * dMinus K q k = dMinus K q k * tinvWord K q (k + 1) n := by
  intro n
  induction n with
  | zero => intro _; rw [tinvWord_zero, tinvWord_zero, e_mul_dMinus, dMinus_mul_e]
  | succ n ih =>
    intro hn
    rw [tinvWord_succ, tinvWord_succ, mul_assoc, ih (by omega), ← mul_assoc,
      Tinv_mul_dMinus (by omega), mul_assoc]

variable [Invertible (q - 1)]

/-- **The top corner element matches across the lowering arrow**: `y_k^{(k)}d₋ = d₋y_k^{(k+1)}`,
where `d₋` is the arrow from `k + 1` to `k`. The element on the right is the *same subscript* at
the vertex above, so it is one step down that vertex's family; unfolding it by the recursion
cancels the pair `T_kT̂_k`, and what is left is the paper's
`d₋(d₊d₋ - d₋d₊)T_{k-1} = q(d₊d₋ - d₋d₊)d₋` read at the vertex `k + 1`. -/
@[hjo "lem_cm_yelement_dminus_top"]
theorem yElt_top_mul_dMinus {k : ℕ} (hk : 1 ≤ k) :
    yElt K q k k * dMinus K q k = dMinus K q k * yElt K q (k + 1) k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := by omega
  have e2 : m + 1 - 1 = m := by omega
  have hTT : Tg K q (m + 1 + 1) m * Tinv K q (m + 1 + 1) m = e K q (m + 1 + 1) :=
    Tg_mul_Tinv (by omega)
  have hDelta : dMinus K q (m + 1) * Delta K q (m + 1) * Tg K q (m + 1 + 1) m
      = q • (Delta K q m * dMinus K q (m + 1)) := dMinus_mul_Delta m
  have hword : tinvWord K q (m + 1) m * dMinus K q (m + 1)
      = dMinus K q (m + 1) * tinvWord K q (m + 1 + 1) m :=
    tinvWord_mul_dMinus m le_rfl
  have htop : yElt K q (m + 1 + 1) (m + 1)
      = (⅟q * ⅟(q - 1)) •
        (tinvWord K q (m + 1 + 1) m * Delta K q (m + 1) * Tg K q (m + 1 + 1) m) := by
    have hrec := yElt_recursion (K := K) (q := q) (k := m + 1 + 1) (i := m + 1)
      (by omega) (by omega)
    rw [e2] at hrec
    rw [hrec, yElt_self, e1, tinvWord_succ, mul_smul_comm, smul_mul_assoc, smul_smul]
    congr 1
    rw [show Tg K q (m + 1 + 1) m *
            (Tinv K q (m + 1 + 1) m * tinvWord K q (m + 1 + 1) m * Delta K q (m + 1) *
              e K q (m + 1 + 1)) * Tg K q (m + 1 + 1) m
          = Tg K q (m + 1 + 1) m * Tinv K q (m + 1 + 1) m * tinvWord K q (m + 1 + 1) m *
            (Delta K q (m + 1) * e K q (m + 1 + 1)) * Tg K q (m + 1 + 1) m
        from by simp only [mul_assoc], hTT, e_mul_tinvWord, Delta_mul_e]
  have hL : yElt K q (m + 1) (m + 1) * dMinus K q (m + 1)
      = ⅟(q - 1) • (tinvWord K q (m + 1) m * (Delta K q m * dMinus K q (m + 1))) := by
    rw [yElt_self, e2, smul_mul_assoc]
    congr 1
    rw [show tinvWord K q (m + 1) m * Delta K q m * e K q (m + 1) * dMinus K q (m + 1)
          = tinvWord K q (m + 1) m * (Delta K q m * e K q (m + 1)) * dMinus K q (m + 1)
        from by simp only [mul_assoc], Delta_mul_e, mul_assoc]
  have hR : dMinus K q (m + 1) * yElt K q (m + 1 + 1) (m + 1)
      = ⅟(q - 1) • (tinvWord K q (m + 1) m * (Delta K q m * dMinus K q (m + 1))) := by
    rw [htop, mul_smul_comm,
      show dMinus K q (m + 1) *
          (tinvWord K q (m + 1 + 1) m * Delta K q (m + 1) * Tg K q (m + 1 + 1) m)
        = dMinus K q (m + 1) * tinvWord K q (m + 1 + 1) m *
          (Delta K q (m + 1) * Tg K q (m + 1 + 1) m) from by simp only [mul_assoc],
      ← hword,
      show tinvWord K q (m + 1) m * dMinus K q (m + 1) *
          (Delta K q (m + 1) * Tg K q (m + 1 + 1) m)
        = tinvWord K q (m + 1) m *
          (dMinus K q (m + 1) * Delta K q (m + 1) * Tg K q (m + 1 + 1) m)
        from by simp only [mul_assoc], hDelta, mul_smul_comm, smul_smul]
    congr 1
    rw [mul_assoc, mul_comm (⅟(q - 1)) q, ← mul_assoc, invOf_mul_self, one_mul]
  rw [hL, hR]

end HJO.Dyck.Aq
