/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.DyckPathAlgebra
public meta import HJO.Attr

/-! # The polynomial inverse of a braid generator, and the relations it unlocks

The loops `T_i` of the Dyck path algebra satisfy a quadratic relation, so each is invertible in its
corner with an inverse that is again a `𝕂`-combination of `T_i` and the idempotent. This file names
that inverse, proves it is one, and proves the three relations of the layer that need it or that
follow from the commutation relations alone.

## Main definitions

* `HJO.Dyck.braidInvGen`: `T̂_i = q⁻¹(T_i + (q-1)e)`, for an arbitrary pair of ring elements.
* `HJO.Dyck.Aq.Tinv`: the same inside `𝔸_q`.

## Main results

* `HJO.Dyck.mul_braidInvGen`, `HJO.Dyck.braidInvGen_mul`: the polynomial inverse is a two-sided
  inverse wherever the four relations it reads hold.
* `HJO.Dyck.Aq.Tg_mul_Tinv`, `HJO.Dyck.Aq.Tinv_mul_Tg`: `T_i` is invertible in `e_k𝔸_qe_k`.
* `HJO.Dyck.Aq.Delta_mul_Tg`: the commutator shifts the loop index, `D_kT_{j-1} = T_jD_k`.

## Implementation notes

The formula divides by `q`, so `q` must be a unit; that is carried as `[Invertible q]` rather than
by assuming a field, which is what lets the same definition be read over a field and over any
commutative ring in which `q` is a unit. `braidInvGen` takes the two ring elements as arguments and
assumes nothing about them, which is the generality the formula is meant in: it is a combination
of loops in the path algebra of the quiver of `HJO.Dyck.Aq`, of any enlargement of that quiver by
further arrows, and of any quotient of either, and a definition depending only on `T` and `e` is
exactly that. The *inverse* property is what needs the quadratic relation, and it is proved inside
`𝔸_q`.

Loop indices are `HJO.Dyck.Aq.Tg`'s: `Tg k i` is the loop usually written `T_{i+1}` at the vertex
`k`, so the admissible range `1 ≤ i ≤ k-1` is `i + 2 ≤ k`. The `D_k`, the commutator at the
vertex `k`, is `HJO.Dyck.Aq.Delta K q (k-1)`: `Delta K q n` is read at the vertex `n + 1`, both of
its summands being paths from there to itself.

## References

The definition `HJO.Dyck.braidInvGen` and the lemmas `HJO.Dyck.Aq.Tg_mul_Tinv` and
`HJO.Dyck.Aq.Delta_mul_Tg`, on the Dyck path algebra and its involution.
-/

@[expose] public section

namespace HJO.Dyck

/-- **The polynomial inverse of a braid generator** `T̂_i = q⁻¹(T_i + (q-1)e)`. Stated for an
arbitrary pair of elements `T`, `e` of an arbitrary `K`-algebra, assuming nothing of them: the
formula is meant in the path algebra of the quiver, in any enlargement of that quiver
and in any quotient of either, and a definition reading only `T` and `e` is that assertion. That the
element *is* an inverse of `T` is the separate `HJO.Dyck.Aq.Tg_mul_Tinv`, which needs the quadratic
relation.

`q` is required to be a unit, the formula dividing by it; `[Invertible q]` rather than `[Field K]`
keeps the definition available over any commutative ring in which `q` is invertible. -/
@[hjo "def_cm_braid_inverse"]
noncomputable def braidInvGen {A : Type*} [Ring A] (K : Type*) [CommRing K] [Algebra K A] (q : K)
    [Invertible q] (T e : A) : A :=
  ⅟q • (T + (q - 1) • e)

section Inverse

variable {A : Type*} [Ring A] {K : Type*} [CommRing K] [Algebra K A] {q : K} [Invertible q]
  {T e : A}

omit [Invertible q] in
/-- The quadratic relation in expanded form, for an arbitrary pair `T`, `e` satisfying the relations
of `HJO.Dyck.Aq` at one vertex: `T² = T - qT + qe`. This is the form in which `T_i` is inverted, and
it is the value check on the signs — writing `(T + e)(T - q e)` instead would give
`T² = qT - T + qe`, a different element. -/
theorem mul_self_eq_of_quadratic (he : e * e = e) (heT : e * T = T) (hTe : T * e = T)
    (hquad : (T - e) * (T + q • e) = 0) : T * T = T - q • T + q • e := by
  rw [sub_mul, mul_add, mul_add, mul_smul_comm, mul_smul_comm, hTe, heT, he, sub_eq_zero] at hquad
  exact (eq_sub_of_add_eq hquad).trans (by abel)

/-- **The polynomial inverse is an inverse**, the half
`T T̂ = e`.

It is stated in a quotient `A` of the path algebra of the quiver of `HJO.Dyck.Aq`, or of
that quiver enlarged by further arrows, in which the relations of `HJO.Dyck.Aq` hold, for `k ≥ 2`
and `1 ≤ i ≤ k-1`. Only four of those relations are read, all at the single vertex `k`: that
`e_k` is idempotent, that `T_i` absorbs it on each side, and the quadratic relation. So the claim
here is for an arbitrary `K`-algebra `A` and an arbitrary pair `T`, `e` of its elements satisfying
those four — which every such quotient does at every admissible `(k, i)`, and which is therefore a
generalisation of the claim rather than a weakening of it. `HJO.Dyck.Aq.Tg_mul_Tinv` is
the instance in `𝔸_q`, and the same statement is available in `𝔹` and in `Ã` from this lemma with
no further work.

The quadratic relation makes the two cross terms cancel, and the surviving `q e` is what the
division by `q` clears. -/
@[hjo "lem_cm_braid_inverse_poly"]
theorem mul_braidInvGen (he : e * e = e) (heT : e * T = T) (hTe : T * e = T)
    (hquad : (T - e) * (T + q • e) = 0) : T * braidInvGen K q T e = e := by
  have hinner : T * T + (q - 1) • T = q • e := by
    rw [mul_self_eq_of_quadratic he heT hTe hquad, sub_smul, one_smul]; abel
  rw [braidInvGen, mul_smul_comm, mul_add, mul_smul_comm, hTe, hinner, smul_smul, invOf_mul_self,
    one_smul]

/-- **The polynomial inverse is an inverse**, the other half
`T̂ T = e`: the same computation with the factors in the other order, both being polynomials in `T`
and `e`. Together with `HJO.Dyck.mul_braidInvGen` this is the "two-sided inverse". -/
@[hjo "lem_cm_braid_inverse_poly"]
theorem braidInvGen_mul (he : e * e = e) (heT : e * T = T) (hTe : T * e = T)
    (hquad : (T - e) * (T + q • e) = 0) : braidInvGen K q T e * T = e := by
  have hinner : T * T + (q - 1) • T = q • e := by
    rw [mul_self_eq_of_quadratic he heT hTe hquad, sub_smul, one_smul]; abel
  rw [braidInvGen, smul_mul_assoc, add_mul, smul_mul_assoc, heT, hinner, smul_smul,
    invOf_mul_self, one_smul]

end Inverse

namespace Aq

variable {K : Type*} [CommRing K] {q : K}

/-- **The polynomial inverse of the loop `T_{i+1}` at the vertex `k`** inside `𝔸_q`: the element
`T̂_i = q⁻¹(T_i + (q-1)e_k)`. -/
@[hjo "def_cm_braid_inverse"]
noncomputable def Tinv (K : Type*) [CommRing K] (q : K) [Invertible q] (k i : ℕ) : Aq K q :=
  braidInvGen K q (Tg K q k i) (e K q k)

variable [Invertible q]

/-- The polynomial inverse, expanded: this is the formula read inside `𝔸_q`. -/
theorem Tinv_eq (k i : ℕ) :
    Tinv K q k i = ⅟q • (Tg K q k i + (q - 1) • e K q k) := rfl

/-- The polynomial inverse is a loop at the same vertex, so it lies in the corner
`e_k𝔸_qe_k` with the loop it inverts. -/
@[simp]
theorem e_mul_Tinv (k i : ℕ) : e K q k * Tinv K q k i = Tinv K q k i := by
  rw [Tinv_eq, mul_smul_comm, mul_add, mul_smul_comm, e_mul_Tg, e_mul_self]

/-- The polynomial inverse is a loop at the same vertex, on the right. -/
@[simp]
theorem Tinv_mul_e (k i : ℕ) : Tinv K q k i * e K q k = Tinv K q k i := by
  rw [Tinv_eq, smul_mul_assoc, add_mul, smul_mul_assoc, Tg_mul_e, e_mul_self]

/-- **The loops of `𝔸_q` are invertible in their corner**, with the polynomial inverse: this
is `HJO.Dyck.Aq.Tg_mul_Tinv`, the half `T_iT̂_i = e_k`. The quadratic relation
`T_i² = (1-q)T_i + qe_k` is what makes the two cross terms cancel, and the surviving `qe_k` is what
the division by `q` clears. -/
@[hjo "lem_cm_dpa_hecke_inverse"]
theorem Tg_mul_Tinv {k i : ℕ} (h : i + 2 ≤ k) :
    Tg K q k i * Tinv K q k i = e K q k :=
  mul_braidInvGen (e_mul_self k) (e_mul_Tg k i) (Tg_mul_e k i) (quadratic h)

/-- **The loops of `𝔸_q` are invertible in their corner**, the half `T̂_iT_i = e_k`: the same
computation with the factors in the other order, both being polynomials in `T_i` and `e_k`. -/
@[hjo "lem_cm_dpa_hecke_inverse"]
theorem Tinv_mul_Tg {k i : ℕ} (h : i + 2 ≤ k) :
    Tinv K q k i * Tg K q k i = e K q k :=
  braidInvGen_mul (e_mul_self k) (e_mul_Tg k i) (Tg_mul_e k i) (quadratic h)

/-! ### The commutator shifts the loop index -/

omit [Invertible q] in
/-- **The commutator shifts the loop index**: `HJO.Dyck.Aq.Delta_mul_Tg`,
`D_kT_{j-1} = T_jD_k`. Here `D_k` is `Delta K q n` at `k = n + 1`, and the loops `T_{j-1}`, `T_j`
at the vertex `k` are `Tg (n+1) m` and `Tg (n+1) (m+1)` at `j = m + 2`; the range
`2 ≤ j ≤ k-1` is `m + 2 ≤ n`.

Both summands of the commutator shift the index by the same one step, for the same reason read in
the two orders: a loop passes a lowering arrow with its index unchanged and its vertex dropping, and
a raising arrow shifts its index up by one. So the difference shifts, and no relation beyond those
two commutations is used. -/
@[hjo "lem_cm_dpa_commutator_shift"]
theorem Delta_mul_Tg {n m : ℕ} (h : m + 2 ≤ n) :
    Delta K q n * Tg K q (n + 1) m = Tg K q (n + 1) (m + 1) * Delta K q n := by
  have h1 : dPlus K q n * dMinus K q n * Tg K q (n + 1) m
      = Tg K q (n + 1) (m + 1) * (dPlus K q n * dMinus K q n) := by
    rw [mul_assoc, ← Tg_mul_dMinus h, ← mul_assoc, dPlus_mul_Tg h, mul_assoc]
  have h2 : dMinus K q (n + 1) * dPlus K q (n + 1) * Tg K q (n + 1) m
      = Tg K q (n + 1) (m + 1) * (dMinus K q (n + 1) * dPlus K q (n + 1)) := by
    rw [mul_assoc, dPlus_mul_Tg (by omega : m + 2 ≤ n + 1), ← mul_assoc,
      ← Tg_mul_dMinus (by omega : m + 1 + 2 ≤ n + 1), mul_assoc]
  change (dPlus K q n * dMinus K q n - dMinus K q (n + 1) * dPlus K q (n + 1)) *
      Tg K q (n + 1) m = Tg K q (n + 1) (m + 1) *
      (dPlus K q n * dMinus K q n - dMinus K q (n + 1) * dPlus K q (n + 1))
  rw [sub_mul, h1, h2, ← mul_sub]

end Aq

end HJO.Dyck
