/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.BraidInverse
public meta import HJO.Attr

/-! # The corner elements of the Dyck path algebra

Inside the corner `e_k𝔸_qe_k` the paper names `k` commuting elements `y_1, …, y_k`, built from the
commutator `d_+d_- - d_-d_+` by conjugating with the polynomial inverses of the loops and then
walking down with the loops themselves. This file defines them.

## Main definitions

* `HJO.Dyck.Aq.tinvWord`: the descending word `T̂_n ⋯ T̂_1` of polynomial inverses at a vertex.
* `HJO.Dyck.Aq.yElt`: the corner element `y_i` of `e_k𝔸_qe_k`.

## Implementation notes

The paper's two clauses are
`y_k = (q-1)⁻¹ T̂_{k-1} ⋯ T̂_1 (d_+d_- - d_-d_+) e_k` and `y_i = q⁻¹ T_i y_{i+1} T_i` for
`1 ≤ i ≤ k-1`, so the family is defined by *downward* recursion from `i = k`. `yAux k j` is
`y_{k-j}`, which makes the recursion structural in `j`, and `yElt k i` is `yAux k (k - i)`.

Two inverses are taken and both are carried as instances: `[Invertible q]`, which
`HJO.Dyck.braidInvGen` already needs, and `[Invertible (q - 1)]` for the leading scalar of `y_k`.
Neither is a field assumption, so the definition is available over any commutative ring in which
those two elements are units — at the paper's `𝕂 = ℚ(q, u)` both are, `q` being an indeterminate.

**The loop index is the shifted one**, as everywhere in `HJO.Dyck.Aq`: `Tg k i` and `Tinv k i` are
the paper's `T_{i+1}` and `T̂_{i+1}` at the vertex `k`. So the paper's `T_i` in the downward
recursion is `Tg k (i-1)` and its `T̂_{k-1} ⋯ T̂_1` is `Tinv k (k-2) * ⋯ * Tinv k 0`, which is
`tinvWord k (k-1)`. Reading the index as the paper's own instead is not a harmless relabelling: it
makes the recursion at `k = 2` multiply by `Tg 2 1`, which is `0` — the vertex `2` carries only the
one loop `T_1` — and the whole family below `y_k` collapses to zero. That is
`yElt_wrong_index_collapses`, which is the value check this definition needs, and it is available
without any nontriviality theorem for the quotient.

The empty word is the idempotent, not `1`: at `k = 1` the paper's product `T̂_0 ⋯ T̂_1` has no
factors and the element is `(q-1)⁻¹ D_1 e_1`, so `tinvWord k 0 = e k` is what makes the base case
land in the corner rather than in the whole algebra, whose unit is not in the span of the
idempotents.

The `D_k`, the commutator at the vertex `k`, is `HJO.Dyck.Aq.Delta K q (k-1)`:
`Delta K q n` is read at the vertex `n + 1`.

This descending word is of the *inverses* `T̂`; the words in the loops `T` themselves are
defined elsewhere and are not duplicated here.

## References

Definition `HJO.Dyck.Aq.yElt`; and
E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K}

/-! ### The commutator sits in its corner -/

section Corner

variable (K) (q)

/-- The commutator `D_{n+1}`, expanded into its two paths: `d_+d_-` read from the vertex `n + 1`
down and back, and `d_-d_+` read from it up and back. -/
theorem Delta_eq (n : ℕ) :
    Delta K q n = dPlus K q n * dMinus K q n - dMinus K q (n + 1) * dPlus K q (n + 1) := rfl

/-- The commutator `D_{n+1}` is a loop at the vertex `n + 1`: both of its two summands are paths
from that vertex to itself, so the idempotent there absorbs it on the left. -/
@[simp]
theorem e_mul_Delta (n : ℕ) : e K q (n + 1) * Delta K q n = Delta K q n := by
  rw [Delta_eq, mul_sub, ← mul_assoc, ← mul_assoc, e_mul_dPlus, e_mul_dMinus]

/-- The commutator `D_{n+1}` is a loop at the vertex `n + 1`, absorbed on the right. -/
@[simp]
theorem Delta_mul_e (n : ℕ) : Delta K q n * e K q (n + 1) = Delta K q n := by
  rw [Delta_eq, sub_mul, mul_assoc, mul_assoc, dMinus_mul_e, dPlus_mul_e]

end Corner

/-! ### The descending word of polynomial inverses -/

variable [Invertible q]

/-- The descending word `T̂_n ⋯ T̂_1` of polynomial inverses at the vertex `k`, the empty word being
the idempotent `e_k` rather than `1`: the unit of `𝔸_q` is not in the span of the idempotents, so it
is `e_k` that makes the word a loop at the vertex. In the shifted loop indexing the factors are
`Tinv k (n-1), …, Tinv k 0`, leftmost first. -/
noncomputable def tinvWord (K : Type*) [CommRing K] (q : K) [Invertible q] (k : ℕ) :
    ℕ → Aq K q
  | 0 => e K q k
  | n + 1 => Tinv K q k n * tinvWord K q k n

/-- The empty descending word is the idempotent at the vertex. -/
@[simp]
theorem tinvWord_zero (k : ℕ) : tinvWord K q k 0 = e K q k := rfl

/-- The descending word peels off its leftmost — that is, its highest-index — factor. -/
theorem tinvWord_succ (k n : ℕ) :
    tinvWord K q k (n + 1) = Tinv K q k n * tinvWord K q k n := rfl

/-- The one-factor word is `T̂_1`, the idempotent being absorbed. -/
@[simp]
theorem tinvWord_one (k : ℕ) : tinvWord K q k 1 = Tinv K q k 0 := by
  rw [tinvWord_succ, tinvWord_zero, Tinv_mul_e]

/-- The two-factor word is `T̂_2 T̂_1`, in that order. This pins the direction of the word: the
reversed product `T̂_1 T̂_2` is a different element of `𝔸_q`, and the paper's
`T̂_{k-1} ⋯ T̂_1` applies `T̂_1` first. -/
theorem tinvWord_two (k : ℕ) : tinvWord K q k 2 = Tinv K q k 1 * Tinv K q k 0 := by
  rw [tinvWord_succ, tinvWord_one]

/-- The descending word is a loop at its vertex, absorbed by the idempotent on the left. -/
@[simp]
theorem e_mul_tinvWord (k n : ℕ) : e K q k * tinvWord K q k n = tinvWord K q k n := by
  induction n with
  | zero => rw [tinvWord_zero, e_mul_self]
  | succ n _ => rw [tinvWord_succ, ← mul_assoc, e_mul_Tinv]

/-- The descending word is a loop at its vertex, absorbed by the idempotent on the right. -/
@[simp]
theorem tinvWord_mul_e (k n : ℕ) : tinvWord K q k n * e K q k = tinvWord K q k n := by
  induction n with
  | zero => rw [tinvWord_zero, e_mul_self]
  | succ n ih => rw [tinvWord_succ, mul_assoc, ih]

/-! ### The corner elements -/

variable [Invertible (q - 1)]

/-- The corner elements read from the top down: `yAux k j` is the paper's `y_{k-j}`. Recursing on
the number of steps taken down from `y_k` is what makes the paper's downward recursion structural.
-/
noncomputable def yAux (K : Type*) [CommRing K] (q : K) [Invertible q] [Invertible (q - 1)]
    (k : ℕ) : ℕ → Aq K q
  | 0 => ⅟(q - 1) • (tinvWord K q k (k - 1) * Delta K q (k - 1) * e K q k)
  | j + 1 => ⅟q • (Tg K q k (k - j - 2) * yAux K q k j * Tg K q k (k - j - 2))

/-- The top of the family, read off the recursion. -/
theorem yAux_zero (k : ℕ) :
    yAux K q k 0 = ⅟(q - 1) • (tinvWord K q k (k - 1) * Delta K q (k - 1) * e K q k) := rfl

/-- One step down the family, read off the recursion. -/
theorem yAux_succ (k j : ℕ) :
    yAux K q k (j + 1) =
      ⅟q • (Tg K q k (k - j - 2) * yAux K q k j * Tg K q k (k - j - 2)) := rfl

/-- **The corner elements** `y_1, …, y_k` of `e_k𝔸_qe_k`: the paper's family, with
`y_k = (q-1)⁻¹ T̂_{k-1} ⋯ T̂_1 (d_+d_- - d_-d_+) e_k` and `y_i = q⁻¹ T_i y_{i+1} T_i` walking down.
Only the values at `1 ≤ i ≤ k` are the paper's; outside that range the definition is a
totalization no statement reads. -/
@[hjo "def_cm_yelement"]
noncomputable def yElt (K : Type*) [CommRing K] (q : K) [Invertible q] [Invertible (q - 1)]
    (k i : ℕ) : Aq K q :=
  yAux K q k (k - i)

/-- **The top corner element**: the paper's first clause,
`y_k = (q-1)⁻¹ T̂_{k-1} ⋯ T̂_1 (d_+d_- - d_-d_+) e_k`, with the commutator at the vertex `k` being
`Delta K q (k-1)` and the word of inverses being `tinvWord k (k-1)`. -/
@[hjo "def_cm_yelement"]
theorem yElt_self (k : ℕ) :
    yElt K q k k = ⅟(q - 1) • (tinvWord K q k (k - 1) * Delta K q (k - 1) * e K q k) := by
  rw [yElt, Nat.sub_self, yAux_zero]

/-- **The downward recursion**: the paper's second clause, `y_i = q⁻¹ T_i y_{i+1} T_i` for
`1 ≤ i ≤ k-1`. The loop is `Tg k (i-1)`, which is the paper's `T_i` in the shifted indexing of
`HJO.Dyck.Aq.Tg`; `yElt_wrong_index_collapses` is why that shift is not a relabelling. -/
@[hjo "def_cm_yelement"]
theorem yElt_recursion {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    yElt K q k i = ⅟q • (Tg K q k (i - 1) * yElt K q k (i + 1) * Tg K q k (i - 1)) := by
  have hj : k - i = (k - i - 1) + 1 := by omega
  have hidx : k - (k - i - 1) - 2 = i - 1 := by omega
  have hnext : k - (i + 1) = k - i - 1 := by omega
  rw [yElt, hj, yAux_succ, hidx, yElt, hnext]

/-- At `k = 1` there is a single corner element and the word of inverses is empty:
`y_1 = (q-1)⁻¹ D_1`, the commutator at the vertex `1`. The idempotents are absorbed by
`e_mul_Delta` and `Delta_mul_e`, which is what the empty word being `e_1` rather than `1` buys. -/
theorem yElt_one_one : yElt K q 1 1 = ⅟(q - 1) • Delta K q 0 := by
  rw [yElt_self]
  norm_num [e_mul_Delta, Delta_mul_e]

/-- At `k = 2` the top element is `(q-1)⁻¹ T̂_1 D_2 e_2`, the word having its single factor. -/
theorem yElt_two_two :
    yElt K q 2 2 = ⅟(q - 1) • (Tinv K q 2 0 * Delta K q 1 * e K q 2) := by
  rw [yElt_self]
  norm_num

/-- At `k = 2` the lower element is `q⁻¹ T_1 y_2 T_1`, the loop `T_1` at the vertex `2` being
`Tg 2 0`. -/
theorem yElt_two_one :
    yElt K q 2 1 = ⅟q • (Tg K q 2 0 * yElt K q 2 2 * Tg K q 2 0) := by
  have h := yElt_recursion (K := K) (q := q) (k := 2) (i := 1) le_rfl (by omega)
  rwa [Nat.sub_self] at h

omit [Invertible q] [Invertible (q - 1)] in
/-- **The value check on the loop index.** The vertex `2` carries exactly one loop, the paper's
`T_1`, which is `Tg 2 0`; `Tg 2 1` is `0`. So reading the recursion's `T_i` as `Tg k i` rather than
`Tg k (i-1)` — that is, reading `Tg k i` as the paper's `T_i` instead of its `T_{i+1}` — makes the
step from `y_2` to `y_1` at `k = 2` multiply by zero on both sides, and every corner element below
the top collapses to `0` for every `k`.

The correct reading, `yElt_two_one`, multiplies by `Tg 2 0` instead. This is the separation the
definition needs, and it costs no nontriviality theorem for the quotient: the wrong reading is zero
outright. -/
theorem yElt_wrong_index_collapses (F : Aq K q) :
    Tg K q 2 1 * F * Tg K q 2 1 = 0 := by
  rw [Tg_eq_zero (by omega : (2 : ℕ) ≤ 1 + 1), zero_mul, mul_zero]

/-! ### The corner elements lie in the corner -/

/-- Every corner element is a loop at the vertex `k`, absorbed by the idempotent on the left: this
is the assertion that `y_i` lies in `e_k𝔸_qe_k`, which is where the paper places the family. -/
theorem e_mul_yAux (k j : ℕ) : e K q k * yAux K q k j = yAux K q k j := by
  induction j with
  | zero => rw [yAux_zero, mul_smul_comm, ← mul_assoc, ← mul_assoc, e_mul_tinvWord]
  | succ j _ => rw [yAux_succ, mul_smul_comm, ← mul_assoc, ← mul_assoc, e_mul_Tg]

/-- Every corner element is a loop at the vertex `k`, absorbed on the right. -/
theorem yAux_mul_e (k j : ℕ) : yAux K q k j * e K q k = yAux K q k j := by
  induction j with
  | zero => rw [yAux_zero, smul_mul_assoc, mul_assoc, e_mul_self]
  | succ j _ => rw [yAux_succ, smul_mul_assoc, mul_assoc, Tg_mul_e]

/-- **The corner elements lie in `e_k𝔸_qe_k`**: the idempotent at the vertex `k` is a two-sided
identity on each `y_i`, which is the paper's placement of the family. -/
@[hjo "def_cm_yelement"]
theorem e_mul_yElt_mul_e (k i : ℕ) :
    e K q k * yElt K q k i * e K q k = yElt K q k i := by
  rw [yElt, e_mul_yAux, yAux_mul_e]

end HJO.Dyck.Aq
