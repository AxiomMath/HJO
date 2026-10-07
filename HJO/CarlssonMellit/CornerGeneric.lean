/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.DPATilde
public meta import HJO.Attr

/-! # The closed form of the first corner element, in an arbitrary generator family

`HJO.Dyck.cornerOf` is the paper's two formulas for `y_i` written in an arbitrary family of
generators; `HJO.Dyck.Tilde.Atilde.zElt` is that same definition read at the *starred* family. The
natural argument for `z_1`'s closed form is that the closed form of `y_1` is a consequence of
those two formulas alone, so the same substitution applied to its conclusion is valid. This file
makes that argument a theorem: the closed form is proved once, from the recursion plus the handful
of facts about the family that it actually reads, and is therefore available at every
instantiation.

## Main definitions

* `HJO.Dyck.segUpOf`, `HJO.Dyck.segOf`: the ascending and descending words in an arbitrary loop
  family, the empty word being the idempotent at the vertex.
* `HJO.Dyck.CornerFamily`: what the calculus reads off a family — the idempotent's absorptions, the
  loops' incidences, that the polynomial inverse inverts, and the commutator's incidences.

## Main results

* `HJO.Dyck.cornerOf_recursion`: the paper's downward recursion, re-indexed. Pure index arithmetic;
  no property of the family is used.
* `HJO.Dyck.cornerOf_one_eq_comm`: `y_1 = q^{1-k}(q-1)^{-1}(UD - DU)(T_{k-1} ⋯ T_1)`.

## Implementation notes

The hypotheses are bundled as a `Prop`-valued structure because the final theorem reads all six and
every intermediate step reads a different three of them. They are passed explicitly rather than as a
section variable: a section variable is only auto-included when it appears in the *statement*, and
here it never does.

What the derivation uses beyond the two defining formulas is exactly the content of
`HJO.Dyck.CornerFamily`: the ascending word of loops cancels the descending word of *inverses*,
which needs the inverse to invert, and the idempotent has to be absorbed at four places. The
phrase "those two formulas alone" is therefore slightly generous — but the extra facts hold in
every family to which it is applied here, which is why the substitution argument is sound.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31**
(2018) 661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]

/-! ### The two words -/

/-- The ascending word `T_{a+1} ⋯ T_{a+n}` at the vertex `k`, the empty word being `E k`. -/
def segUpOf (E : ℕ → A) (T : ℕ → ℕ → A) (k a : ℕ) : ℕ → A
  | 0 => E k
  | n + 1 => segUpOf E T k a n * T k (a + n)

/-- The descending word `T_{a+n} ⋯ T_{a+1}` at the vertex `k`, the empty word being `E k`. -/
def segOf (E : ℕ → A) (T : ℕ → ℕ → A) (k a : ℕ) : ℕ → A
  | 0 => E k
  | n + 1 => T k (a + n) * segOf E T k a n

@[simp] theorem segUpOf_zero (E : ℕ → A) (T : ℕ → ℕ → A) (k a : ℕ) :
    segUpOf E T k a 0 = E k := rfl

theorem segUpOf_succ (E : ℕ → A) (T : ℕ → ℕ → A) (k a n : ℕ) :
    segUpOf E T k a (n + 1) = segUpOf E T k a n * T k (a + n) := rfl

@[simp] theorem segOf_zero (E : ℕ → A) (T : ℕ → ℕ → A) (k a : ℕ) : segOf E T k a 0 = E k := rfl

theorem segOf_succ (E : ℕ → A) (T : ℕ → ℕ → A) (k a n : ℕ) :
    segOf E T k a (n + 1) = T k (a + n) * segOf E T k a n := rfl

/-! ### The facts the calculus reads -/

/-- **What the corner-element calculus reads off a family of generators.** Everything below is a
consequence of the two defining formulas of `HJO.Dyck.cornerOf` together with these. -/
structure CornerFamily (q' qi : K) (E U D : ℕ → A) (T : ℕ → ℕ → A) : Prop where
  /-- The idempotents are idempotent. -/
  e_mul_e : ∀ k, E k * E k = E k
  /-- A loop is a loop at its vertex. -/
  e_mul_T : ∀ k i, E k * T k i = T k i
  /-- A loop is a loop at its vertex, on the right. -/
  T_mul_e : ∀ k i, T k i * E k = T k i
  /-- The polynomial inverse inverts the loop, in the corner. -/
  T_mul_Tinv : ∀ k i, i + 2 ≤ k → T k i * tinvOf q' qi (T k i) (E k) = E k
  /-- The commutator is a loop at its vertex. -/
  e_mul_comm : ∀ n, E (n + 1) * commOf U D n = commOf U D n
  /-- The commutator is a loop at its vertex, on the right. -/
  comm_mul_e : ∀ n, commOf U D n * E (n + 1) = commOf U D n

namespace CornerFamily

variable {q' qi di : K} {E U D : ℕ → A} {T : ℕ → ℕ → A}

theorem e_mul_tinvOf (h : CornerFamily q' qi E U D T) (k i : ℕ) :
    E k * tinvOf q' qi (T k i) (E k) = tinvOf q' qi (T k i) (E k) := by
  rw [tinvOf, mul_smul_comm, mul_add, mul_smul_comm, h.e_mul_T, h.e_mul_e]

theorem e_mul_tinvWordOf (h : CornerFamily q' qi E U D T) (k n : ℕ) :
    E k * tinvWordOf q' qi E T k n = tinvWordOf q' qi E T k n := by
  cases n with
  | zero => exact h.e_mul_e k
  | succ n => rw [tinvWordOf, ← mul_assoc, h.e_mul_tinvOf]

/-- **The ascending word of loops cancels the descending word of inverses**, in the corner. -/
theorem segUpOf_mul_tinvWordOf (h : CornerFamily q' qi E U D T) {k : ℕ} :
    ∀ n : ℕ, n + 1 ≤ k → segUpOf E T k 0 n * tinvWordOf q' qi E T k n = E k := by
  intro n
  induction n with
  | zero => intro _; rw [segUpOf_zero, tinvWordOf, h.e_mul_e]
  | succ n ih =>
    intro hn
    rw [segUpOf_succ, tinvWordOf, Nat.zero_add, mul_assoc,
      ← mul_assoc (T k n) (tinvOf q' qi (T k n) (E k)) (tinvWordOf q' qi E T k n),
      h.T_mul_Tinv k n (by omega), h.e_mul_tinvWordOf k n, ih (by omega)]

theorem e_mul_cornerAux (h : CornerFamily q' qi E U D T) (k j : ℕ) :
    E k * cornerAux q' qi di E U D T k j = cornerAux q' qi di E U D T k j := by
  induction j with
  | zero =>
    rw [cornerAux, mul_smul_comm, ← mul_assoc, ← mul_assoc, h.e_mul_tinvWordOf k (k - 1)]
  | succ j _ => rw [cornerAux, mul_smul_comm, ← mul_assoc, ← mul_assoc, h.e_mul_T]

theorem cornerAux_mul_e (h : CornerFamily q' qi E U D T) (k j : ℕ) :
    cornerAux q' qi di E U D T k j * E k = cornerAux q' qi di E U D T k j := by
  induction j with
  | zero => rw [cornerAux, smul_mul_assoc, mul_assoc, h.e_mul_e]
  | succ j _ => rw [cornerAux, smul_mul_assoc, mul_assoc, h.T_mul_e]

theorem e_mul_cornerOf (h : CornerFamily q' qi E U D T) (k i : ℕ) :
    E k * cornerOf q' qi di E U D T k i = cornerOf q' qi di E U D T k i :=
  h.e_mul_cornerAux k (k - i)

theorem cornerOf_mul_e (h : CornerFamily q' qi E U D T) (k i : ℕ) :
    cornerOf q' qi di E U D T k i * E k = cornerOf q' qi di E U D T k i :=
  h.cornerAux_mul_e k (k - i)

end CornerFamily

/-! ### The recursion and the closed form -/

variable {q' qi di : K} {E U D : ℕ → A} {T : ℕ → ℕ → A}

/-- **The paper's downward recursion**, re-indexed: `y_i = q^{-1}T_iy_{i+1}T_i`. Pure index
arithmetic — no property of the family is read. -/
theorem cornerOf_recursion {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    cornerOf q' qi di E U D T k i
      = qi • (T k (i - 1) * cornerOf q' qi di E U D T k (i + 1) * T k (i - 1)) := by
  have hj : k - i = (k - i - 1) + 1 := by omega
  have hidx : k - (k - i - 1) - 2 = i - 1 := by omega
  have hnext : k - (i + 1) = k - i - 1 := by omega
  rw [cornerOf, hj, cornerAux, hidx, cornerOf, hnext]

/-- The induction behind `HJO.Dyck.cornerOf_one_eq_comm`. -/
theorem cornerOf_one_eq_aux (h : CornerFamily q' qi E U D T) {k : ℕ} :
    ∀ j : ℕ, j + 1 ≤ k →
      cornerOf q' qi di E U D T k 1
        = qi ^ j •
          (segUpOf E T k 0 j * cornerOf q' qi di E U D T k (j + 1) * segOf E T k 0 j) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [pow_zero, one_smul, segUpOf_zero, segOf_zero, h.e_mul_cornerOf, h.cornerOf_mul_e]
  | succ j ih =>
    intro hj
    have hrec := cornerOf_recursion (q' := q') (qi := qi) (di := di) (E := E) (U := U) (D := D)
      (T := T) (k := k) (i := j + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hrec
    rw [ih (by omega), hrec, segUpOf_succ, segOf_succ, Nat.zero_add, pow_succ, mul_smul_comm,
      smul_mul_assoc, smul_smul]
    simp only [mul_assoc]

/-- **The closed form of the first corner element**:
`y_1 = q^{1-k}(q-1)^{-1}(UD - DU)(T_{k-1} ⋯ T_1)`. This is the statement transported
along the starred substitution to get `z_1`'s closed form, and transporting it is nothing more
than instantiating this theorem at the starred family. -/
theorem cornerOf_one_eq_comm (h : CornerFamily q' qi E U D T) {k : ℕ} (hk : 1 ≤ k) :
    cornerOf q' qi di E U D T k 1
      = (qi ^ (k - 1) * di) • (commOf U D (k - 1) * segOf E T k 0 (k - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hiter := cornerOf_one_eq_aux (di := di) (k := m + 1) h m le_rfl
  have htop : cornerOf q' qi di E U D T (m + 1) (m + 1)
      = di • (tinvWordOf q' qi E T (m + 1) m * commOf U D m * E (m + 1)) := by
    rw [cornerOf, Nat.sub_self, cornerAux]
    simp only [Nat.add_sub_cancel]
  rw [hiter, htop, mul_smul_comm, smul_mul_assoc, smul_smul]
  congr 1
  calc segUpOf E T (m + 1) 0 m *
        (tinvWordOf q' qi E T (m + 1) m * commOf U D m * E (m + 1)) * segOf E T (m + 1) 0 m
      = segUpOf E T (m + 1) 0 m * tinvWordOf q' qi E T (m + 1) m *
        (commOf U D m * E (m + 1)) * segOf E T (m + 1) 0 m := by simp only [mul_assoc]
    _ = E (m + 1) * commOf U D m * segOf E T (m + 1) 0 m := by
        rw [h.segUpOf_mul_tinvWordOf m le_rfl, h.comm_mul_e]
    _ = commOf U D m * segOf E T (m + 1) 0 m := by rw [h.e_mul_comm]

end HJO.Dyck
