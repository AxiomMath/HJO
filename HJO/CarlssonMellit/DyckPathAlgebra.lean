/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public meta import HJO.Attr

/-! # The Dyck path algebra

Carlsson and Mellit's algebra `𝔸_q` is a quotient of the path algebra of a quiver with one vertex
for each `k ≥ 0`, a raising arrow `d₊ : k → k+1` and a lowering arrow `d₋ : k+1 → k` for each `k`,
and `k - 1` loops `T₁, …, T_{k-1}` at the vertex `k`. This file presents it as a `RingQuot` of a
free algebra.

## Main definitions

* `HJO.Dyck.Gen`: the generators — one idempotent per vertex, the two families of arrows, and the
  loops.
* `HJO.Dyck.Rel`: the relations, the path-algebra structure together with the paper's nine.
* `HJO.Dyck.Aq`: the algebra `𝔸_q`.
* `HJO.Dyck.e`, `HJO.Dyck.dPlus`, `HJO.Dyck.dMinus`, `HJO.Dyck.Tg`: the generators in `𝔸_q`.
* `HJO.Dyck.Delta`: the commutator `d₊d₋ - d₋d₊` at a vertex.

## Implementation notes

Products are read right to left, as compositions of paths: in `d₊T_i` the loop acts first. That is
forced rather than chosen — the paper's relation `d₋²T_{k-1} = d₋²` names the loop `T_{k-1}`, which
exists at the vertex `k` and not at the vertex `k - 2`, so `T_{k-1}` must be the *first* factor
applied. With that fixed, every one of the paper's relations is read at the vertex `k` at which
its paths begin, and `k` is eliminated in favour of the level of the
arrow that carries it, which is what makes each relation a statement with no side condition on `k`.

The loop index is shifted: `Tg k i` is the paper's `T_{i+1}` at the vertex `k`, so the paper's
range `1 ≤ i ≤ k - 1` reads `i + 2 ≤ k`. Rather than index the loops by a dependent type, the
generator is declared at every pair and `Rel.braid_eq_zero` kills the ones the quiver does not
have; the algebra is the same, and every relation below can be written with plain `ℕ` indices.

The path-algebra structure needs only the *absorbing* relations `e_k T = T = T e_k` and
`e_k e_l = δ_{k,l} e_k`: a product of two non-composable arrows is then `0` automatically, since
each arrow absorbs the idempotents at its ends and `e_k e_l` vanishes between them. No relation
asserting `1 = ∑_k e_k` is imposed, and none can be — the sum is infinite; the unit of `Aq` is
therefore not in the span of the idempotents, which is why the paper works inside the corners
`e_k 𝔸_q e_k`.

The base is a commutative ring and `q` one of its elements. The paper's `𝕂 = ℚ(q, u)` with `q` an
indeterminate is one instance; nothing in the presentation needs `q` invertible, a field, or the
two parameters algebraically independent, and the elements that do — the polynomial inverse `T̂_i`
and the corner elements `y_i`, which divide by `q` and `q - 1` — carry those hypotheses
themselves.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck

/-- The generators of the path algebra of the paper's quiver: the idempotent `e k` at the vertex
`k`, the raising arrow `d₊ : k → k+1`, the lowering arrow `d₋ : k+1 → k`, and the loop
`braid k i`, the paper's `T_{i+1}` at the vertex `k`. The loops the quiver does not have — those
with `i + 2 > k` — are declared here too and set to `0` by `Rel.braid_eq_zero`. -/
inductive Gen where
  /-- The idempotent at the vertex `k`. -/
  | vertex (k : ℕ)
  /-- The raising arrow `d₊` from the vertex `k` to the vertex `k + 1`. -/
  | up (k : ℕ)
  /-- The lowering arrow `d₋` from the vertex `k + 1` to the vertex `k`. -/
  | down (k : ℕ)
  /-- The loop `T_{i+1}` at the vertex `k`. -/
  | braid (k i : ℕ)
  deriving DecidableEq

section Rel

variable (K : Type*) [CommRing K] (q : K)

/-- `e k` in the free algebra on the generators. -/
abbrev freeE (k : ℕ) : FreeAlgebra K Gen := FreeAlgebra.ι K (Gen.vertex k)

/-- `d₊ : k → k+1` in the free algebra on the generators. -/
abbrev freeUp (k : ℕ) : FreeAlgebra K Gen := FreeAlgebra.ι K (Gen.up k)

/-- `d₋ : k+1 → k` in the free algebra on the generators. -/
abbrev freeDown (k : ℕ) : FreeAlgebra K Gen := FreeAlgebra.ι K (Gen.down k)

/-- The paper's `T_{i+1}` at the vertex `k`, in the free algebra on the generators. -/
abbrev freeT (k i : ℕ) : FreeAlgebra K Gen := FreeAlgebra.ι K (Gen.braid k i)

/-- The commutator `d₊d₋ - d₋d₊` at the vertex `k + 1`, in the free algebra: the paths
`(k+1) → k → (k+1)` and `(k+1) → (k+2) → (k+1)`. -/
abbrev freeDelta (k : ℕ) : FreeAlgebra K Gen :=
  freeUp K k * freeDown K k - freeDown K (k + 1) * freeUp K (k + 1)

/-- **The relations of the Dyck path algebra.** The first nine are the path-algebra structure of
the paper's quiver; the last nine are the paper's own relations, each read at the vertex at
which its paths begin, with that vertex eliminated in favour of the level of the arrow carrying
it. -/
inductive Rel : FreeAlgebra K Gen → FreeAlgebra K Gen → Prop where
  /-- The vertex elements are idempotent. -/
  | vertex_mul_self (k : ℕ) : Rel (freeE K k * freeE K k) (freeE K k)
  /-- Distinct vertices are orthogonal. -/
  | vertex_mul_vertex {k l : ℕ} (h : k ≠ l) : Rel (freeE K k * freeE K l) 0
  /-- `d₊` lands at the vertex `k + 1`. -/
  | vertex_mul_up (k : ℕ) : Rel (freeE K (k + 1) * freeUp K k) (freeUp K k)
  /-- `d₊` starts at the vertex `k`. -/
  | up_mul_vertex (k : ℕ) : Rel (freeUp K k * freeE K k) (freeUp K k)
  /-- `d₋` lands at the vertex `k`. -/
  | vertex_mul_down (k : ℕ) : Rel (freeE K k * freeDown K k) (freeDown K k)
  /-- `d₋` starts at the vertex `k + 1`. -/
  | down_mul_vertex (k : ℕ) : Rel (freeDown K k * freeE K (k + 1)) (freeDown K k)
  /-- A loop at the vertex `k` lands there. -/
  | vertex_mul_braid (k i : ℕ) : Rel (freeE K k * freeT K k i) (freeT K k i)
  /-- A loop at the vertex `k` starts there. -/
  | braid_mul_vertex (k i : ℕ) : Rel (freeT K k i * freeE K k) (freeT K k i)
  /-- The quiver has the loops `T₁, …, T_{k-1}` at the vertex `k` and no others. -/
  | braid_eq_zero {k i : ℕ} (h : k ≤ i + 1) : Rel (freeT K k i) 0
  /-- The paper's `(T_i - 1)(T_i + q) = 0` at the vertex `k`, the unit being `e_k`. -/
  | quadratic {k i : ℕ} (h : i + 2 ≤ k) :
      Rel ((freeT K k i - freeE K k) * (freeT K k i + q • freeE K k)) 0
  /-- The paper's braid relation `T_iT_{i+1}T_i = T_{i+1}T_iT_{i+1}` at the vertex `k`. -/
  | braid_braid {k i : ℕ} (h : i + 3 ≤ k) :
      Rel (freeT K k i * freeT K k (i + 1) * freeT K k i)
        (freeT K k (i + 1) * freeT K k i * freeT K k (i + 1))
  /-- The paper's `T_iT_j = T_jT_i` for `|i - j| > 1`, at the vertex `k`. -/
  | braid_comm {k i j : ℕ} (hi : i + 2 ≤ k) (hj : j + 2 ≤ k) (hij : i + 1 < j) :
      Rel (freeT K k i * freeT K k j) (freeT K k j * freeT K k i)
  /-- The paper's `T_id₋ = d₋T_i`: the loop commutes past the lowering arrow, its index unchanged
  and its vertex dropping by one with the arrow. -/
  | braid_down {m i : ℕ} (h : i + 2 ≤ m) :
      Rel (freeT K m i * freeDown K m) (freeDown K m * freeT K (m + 1) i)
  /-- The paper's `d₊T_i = T_{i+1}d₊`: the raising arrow shifts the loop's index up by one. -/
  | up_braid {k i : ℕ} (h : i + 2 ≤ k) :
      Rel (freeUp K k * freeT K k i) (freeT K (k + 1) (i + 1) * freeUp K k)
  /-- The paper's `T_1d₊² = d₊²`. -/
  | braid_up_up (k : ℕ) :
      Rel (freeT K (k + 2) 0 * (freeUp K (k + 1) * freeUp K k)) (freeUp K (k + 1) * freeUp K k)
  /-- The paper's `d₋²T_{k-1} = d₋²`, at the vertex `k = m + 2`. -/
  | down_down_braid (m : ℕ) :
      Rel (freeDown K m * freeDown K (m + 1) * freeT K (m + 2) m)
        (freeDown K m * freeDown K (m + 1))
  /-- The paper's `d₋(d₊d₋ - d₋d₊)T_{k-1} = q(d₊d₋ - d₋d₊)d₋` for `k ≥ 2`, at `k = j + 2`. -/
  | down_delta {j : ℕ} :
      Rel (freeDown K (j + 1) * freeDelta K (j + 1) * freeT K (j + 2) j)
        (q • (freeDelta K j * freeDown K (j + 1)))
  /-- The paper's `T_1(d₊d₋ - d₋d₊)d₊ = qd₊(d₊d₋ - d₋d₊)` for `k ≥ 1`, at `k = m + 1`. -/
  | braid_delta {m : ℕ} :
      Rel (freeT K (m + 2) 0 * freeDelta K (m + 1) * freeUp K (m + 1))
        (q • (freeUp K (m + 1) * freeDelta K m))

end Rel

/-- **The Dyck path algebra** `𝔸_q`: the path algebra over `K` of the paper's quiver, modulo the
two-sided ideal generated by the paper's relations. Both `K` and `q` are explicit, the consumers
substituting `q⁻¹` for `q`. -/
@[hjo "def_cm_dpa"]
abbrev Aq (K : Type*) [CommRing K] (q : K) : Type _ := RingQuot (Rel K q)

namespace Aq

variable {K : Type*} [CommRing K] {q : K}

/-- The quotient map from the free algebra on the generators onto `𝔸_q`. -/
noncomputable def mk (K : Type*) [CommRing K] (q : K) : FreeAlgebra K Gen →ₐ[K] Aq K q :=
  RingQuot.mkAlgHom K (Rel K q)

/-- **The idempotent at the vertex `k`** in `𝔸_q`. -/
@[hjo "def_cm_dpa"]
noncomputable def e (K : Type*) [CommRing K] (q : K) (k : ℕ) : Aq K q := mk K q (freeE K k)

/-- **The raising arrow** `d₊ : k → k+1` in `𝔸_q`. -/
@[hjo "def_cm_dpa"]
noncomputable def dPlus (K : Type*) [CommRing K] (q : K) (k : ℕ) : Aq K q := mk K q (freeUp K k)

/-- **The lowering arrow** `d₋ : k+1 → k` in `𝔸_q`. -/
@[hjo "def_cm_dpa"]
noncomputable def dMinus (K : Type*) [CommRing K] (q : K) (k : ℕ) : Aq K q :=
  mk K q (freeDown K k)

/-- **The loop `T_{i+1}` at the vertex `k`** in `𝔸_q`, the paper's `T_i` being `Tg K q k (i - 1)`.
It is `0` unless `i + 2 ≤ k`. -/
@[hjo "def_cm_dpa"]
noncomputable def Tg (K : Type*) [CommRing K] (q : K) (k i : ℕ) : Aq K q := mk K q (freeT K k i)

/-- The commutator `d₊d₋ - d₋d₊` at the vertex `k + 1`: the difference of the two paths of length
two from that vertex back to itself. The paper writes it `d₊d₋ - d₋d₊` with the vertex left
implicit; it is the element the corner elements `y_i` and the Haglund--Morse--Zabrocki relation are
built from. -/
noncomputable def Delta (K : Type*) [CommRing K] (q : K) (k : ℕ) : Aq K q :=
  dPlus K q k * dMinus K q k - dMinus K q (k + 1) * dPlus K q (k + 1)

theorem mk_freeDelta (k : ℕ) : mk K q (freeDelta K k) = Delta K q k := by
  rw [freeDelta, Delta, map_sub, map_mul, map_mul]
  rfl

/-- Any relation of `Rel` holds in `𝔸_q`. -/
theorem mk_rel {x y : FreeAlgebra K Gen} (h : Rel K q x y) : mk K q x = mk K q y :=
  RingQuot.mkAlgHom_rel K h

/-! ### The path-algebra structure -/

/-- The vertex elements of `𝔸_q` are idempotent. -/
@[simp]
theorem e_mul_self (k : ℕ) : e K q k * e K q k = e K q k := by
  have := mk_rel (Rel.vertex_mul_self (K := K) (q := q) k)
  simp only [map_mul] at this
  exact this

/-- Distinct vertices of `𝔸_q` are orthogonal, so `𝔸_q` is a direct sum of corners. -/
@[simp]
theorem e_mul_e_of_ne {k l : ℕ} (h : k ≠ l) : e K q k * e K q l = 0 := by
  have := mk_rel (Rel.vertex_mul_vertex (K := K) (q := q) h)
  simp only [map_mul, map_zero] at this
  exact this

/-- `d₊` lands at the vertex `k + 1`. -/
@[simp]
theorem e_mul_dPlus (k : ℕ) : e K q (k + 1) * dPlus K q k = dPlus K q k := by
  have := mk_rel (Rel.vertex_mul_up (K := K) (q := q) k)
  simp only [map_mul] at this
  exact this

/-- `d₊` starts at the vertex `k`. -/
@[simp]
theorem dPlus_mul_e (k : ℕ) : dPlus K q k * e K q k = dPlus K q k := by
  have := mk_rel (Rel.up_mul_vertex (K := K) (q := q) k)
  simp only [map_mul] at this
  exact this

/-- `d₋` lands at the vertex `k`. -/
@[simp]
theorem e_mul_dMinus (k : ℕ) : e K q k * dMinus K q k = dMinus K q k := by
  have := mk_rel (Rel.vertex_mul_down (K := K) (q := q) k)
  simp only [map_mul] at this
  exact this

/-- `d₋` starts at the vertex `k + 1`. -/
@[simp]
theorem dMinus_mul_e (k : ℕ) : dMinus K q k * e K q (k + 1) = dMinus K q k := by
  have := mk_rel (Rel.down_mul_vertex (K := K) (q := q) k)
  simp only [map_mul] at this
  exact this

/-- A loop at the vertex `k` lands there. -/
@[simp]
theorem e_mul_Tg (k i : ℕ) : e K q k * Tg K q k i = Tg K q k i := by
  have := mk_rel (Rel.vertex_mul_braid (K := K) (q := q) k i)
  simp only [map_mul] at this
  exact this

/-- A loop at the vertex `k` starts there. -/
@[simp]
theorem Tg_mul_e (k i : ℕ) : Tg K q k i * e K q k = Tg K q k i := by
  have := mk_rel (Rel.braid_mul_vertex (K := K) (q := q) k i)
  simp only [map_mul] at this
  exact this

/-- **The quiver has exactly `k - 1` loops at the vertex `k`**: the paper's `T₁, …, T_{k-1}`, so
the generator vanishes outside that range. -/
@[hjo "def_cm_dpa"]
theorem Tg_eq_zero {k i : ℕ} (h : k ≤ i + 1) : Tg K q k i = 0 := by
  have := mk_rel (Rel.braid_eq_zero (K := K) (q := q) h)
  simp only [map_zero] at this
  exact this

/-- There is no loop at the vertex `0`. -/
@[simp]
theorem Tg_zero_left (i : ℕ) : Tg K q 0 i = 0 := Tg_eq_zero (Nat.zero_le _)

/-- There is no loop at the vertex `1`. -/
@[simp]
theorem Tg_one_left (i : ℕ) : Tg K q 1 i = 0 := Tg_eq_zero (Nat.succ_le_succ (Nat.zero_le _))

/-- Two arrows that do not compose give `0`: the raising arrows out of different vertices.  This is
what the absorbing relations buy — the vanishing is derived, not imposed. -/
theorem dPlus_mul_dPlus_of_ne {k l : ℕ} (h : k + 1 ≠ l) :
    dPlus K q l * dPlus K q k = 0 := by
  rw [← dPlus_mul_e l, ← e_mul_dPlus k, ← mul_assoc, mul_assoc (dPlus K q l),
    e_mul_e_of_ne (Ne.symm h), mul_zero, zero_mul]

/-! ### The paper's relations -/

/-- **The paper's quadratic relation** `(T_i - 1)(T_i + q) = 0` at the vertex `k`, the unit of the
corner being `e_k`. -/
@[hjo "def_cm_dpa"]
theorem quadratic {k i : ℕ} (h : i + 2 ≤ k) :
    (Tg K q k i - e K q k) * (Tg K q k i + q • e K q k) = 0 := by
  have := mk_rel (Rel.quadratic (K := K) (q := q) h)
  simp only [map_mul, map_sub, map_add, map_smul, map_zero] at this
  exact this

/-- **The paper's braid relation** `T_iT_{i+1}T_i = T_{i+1}T_iT_{i+1}` at the vertex `k`. -/
@[hjo "def_cm_dpa"]
theorem braid_braid {k i : ℕ} (h : i + 3 ≤ k) :
    Tg K q k i * Tg K q k (i + 1) * Tg K q k i =
      Tg K q k (i + 1) * Tg K q k i * Tg K q k (i + 1) := by
  have := mk_rel (Rel.braid_braid (K := K) (q := q) h)
  simp only [map_mul] at this
  exact this

/-- **The paper's commutation** `T_iT_j = T_jT_i` for `|i - j| > 1`, at the vertex `k`. -/
@[hjo "def_cm_dpa"]
theorem Tg_comm {k i j : ℕ} (hi : i + 2 ≤ k) (hj : j + 2 ≤ k) (hij : i + 1 < j) :
    Tg K q k i * Tg K q k j = Tg K q k j * Tg K q k i := by
  have := mk_rel (Rel.braid_comm (K := K) (q := q) hi hj hij)
  simp only [map_mul] at this
  exact this

/-- **The paper's `T_id₋ = d₋T_i`**: a loop commutes past a lowering arrow with its index
unchanged. -/
@[hjo "def_cm_dpa"]
theorem Tg_mul_dMinus {m i : ℕ} (h : i + 2 ≤ m) :
    Tg K q m i * dMinus K q m = dMinus K q m * Tg K q (m + 1) i := by
  have := mk_rel (Rel.braid_down (K := K) (q := q) h)
  simp only [map_mul] at this
  exact this

/-- **The paper's `d₊T_i = T_{i+1}d₊`**: a raising arrow shifts a loop's index up by one. -/
@[hjo "def_cm_dpa"]
theorem dPlus_mul_Tg {k i : ℕ} (h : i + 2 ≤ k) :
    dPlus K q k * Tg K q k i = Tg K q (k + 1) (i + 1) * dPlus K q k := by
  have := mk_rel (Rel.up_braid (K := K) (q := q) h)
  simp only [map_mul] at this
  exact this

/-- **The paper's `T_1d₊² = d₊²`**: the first loop is idle on a doubled raising arrow. -/
@[hjo "def_cm_dpa"]
theorem Tg_mul_dPlus_dPlus (k : ℕ) :
    Tg K q (k + 2) 0 * (dPlus K q (k + 1) * dPlus K q k) = dPlus K q (k + 1) * dPlus K q k := by
  have := mk_rel (Rel.braid_up_up (K := K) (q := q) k)
  simp only [map_mul] at this
  exact this

/-- **The paper's `d₋²T_{k-1} = d₋²`**: the top loop at the vertex `k = m + 2` is idle on a
doubled lowering arrow. -/
@[hjo "def_cm_dpa"]
theorem dMinus_dMinus_mul_Tg (m : ℕ) :
    dMinus K q m * dMinus K q (m + 1) * Tg K q (m + 2) m =
      dMinus K q m * dMinus K q (m + 1) := by
  have := mk_rel (Rel.down_down_braid (K := K) (q := q) m)
  simp only [map_mul] at this
  exact this

/-- **The paper's `d₋(d₊d₋ - d₋d₊)T_{k-1} = q(d₊d₋ - d₋d₊)d₋`** for `k ≥ 2`, read at
`k = j + 2`. -/
@[hjo "def_cm_dpa"]
theorem dMinus_mul_Delta (j : ℕ) :
    dMinus K q (j + 1) * Delta K q (j + 1) * Tg K q (j + 2) j =
      q • (Delta K q j * dMinus K q (j + 1)) := by
  have := mk_rel (Rel.down_delta (K := K) (q := q) (j := j))
  simp only [map_mul, map_sub, map_smul] at this
  exact this

/-- **The paper's `T_1(d₊d₋ - d₋d₊)d₊ = qd₊(d₊d₋ - d₋d₊)`** for `k ≥ 1`, read at `k = m + 1`. -/
@[hjo "def_cm_dpa"]
theorem Tg_mul_Delta (m : ℕ) :
    Tg K q (m + 2) 0 * Delta K q (m + 1) * dPlus K q (m + 1) =
      q • (dPlus K q (m + 1) * Delta K q m) := by
  have := mk_rel (Rel.braid_delta (K := K) (q := q) (m := m))
  simp only [map_mul, map_sub, map_smul] at this
  exact this

/-! ### Consequences pinning the presentation -/

/-- The quadratic relation in expanded form: `T_i² = (1 - q)T_i + q e_k` at the vertex `k`. This is
the form in which the paper inverts `T_i`, and it is the value check on the signs of the quadratic
relation: writing `(T_i + 1)(T_i - q)` instead would give `T_i² = (q - 1)T_i + q e_k`, a different
element. -/
theorem Tg_sq {k i : ℕ} (h : i + 2 ≤ k) :
    Tg K q k i * Tg K q k i = Tg K q k i - q • Tg K q k i + q • e K q k := by
  have hq := quadratic (q := q) h
  rw [sub_mul, mul_add, mul_add, mul_smul_comm, mul_smul_comm, Tg_mul_e, e_mul_Tg, e_mul_self,
    sub_eq_zero] at hq
  exact (eq_sub_of_add_eq hq).trans (by abel)

/-- The first loop at the vertex `2` is the paper's `T_1`, and it is not killed by
`Tg_eq_zero`: the range `i + 2 ≤ k` is exactly the paper's `1 ≤ i ≤ k - 1` and no wider. This is
the check that the shift of the loop index is the intended one — reading `Tg k i` as the paper's
`T_i` instead would make the paper's `T_1` at the vertex `2` vanish. -/
theorem two_le_of_Tg_ne_zero {k i : ℕ} (h : Tg K q k i ≠ 0) : i + 2 ≤ k :=
  Nat.lt_of_not_le fun hle => h (Tg_eq_zero (by omega))

end Aq

end HJO.Dyck
