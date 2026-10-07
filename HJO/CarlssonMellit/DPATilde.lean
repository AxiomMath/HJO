/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerElements
public meta import HJO.Attr

/-! # The extended Dyck path algebra `Ã`

Carlsson and Mellit enlarge the quiver of `HJO.Dyck.Aq` by a second raising arrow `d₊^*` at every
vertex and impose three groups of relations: the relations of `HJO.Dyck.Aq`, *the same relations
read after the substitution* `q ↦ q⁻¹`, `d₊ ↦ d₊^*`, `T_i ↦ T_i⁻¹`, and three further relations
mixing the two raising arrows. The resulting algebra is `Ã`.

## Main definitions

* `HJO.Dyck.commOf`, `HJO.Dyck.tinvOf`, `HJO.Dyck.tinvWordOf`, `HJO.Dyck.cornerOf`: the commutator
  `d₊d₋ - d₋d₊`, the polynomial inverse `T̂_i`, the descending word `T̂_n ⋯ T̂_1` and the corner
  element `y_i`, each written as a formula in an *arbitrary* family of generators. Instantiating at
  `(q, d₊, T)` gives `HJO.Dyck.Aq.yElt` — that is `HJO.Dyck.Aq.cornerOf_eq_yElt` — and
  instantiating at `(q⁻¹, d₊^*, T̂)` gives the paper's `z_i`.
* `HJO.Dyck.SourceRel`: the paper's relations, likewise in an arbitrary family. The starred group
  is this same inductive at the substituted family, which is what makes "the relations obtained
  from those of `HJO.Dyck.Aq` by replacing `q` by `q⁻¹`, `d₊` by `d₊^*` and each `T_i` by `T_i⁻¹`" a
  statement rather than a second transcription.
* `HJO.Dyck.Tilde.Gen`, `HJO.Dyck.Tilde.Rel`, `HJO.Dyck.Tilde.Atilde`: the enlarged quiver, the
  full relation list, and `Ã`.
* `HJO.Dyck.Tilde.Atilde.yElt`, `HJO.Dyck.Tilde.Atilde.zElt`: the corner elements `y_i` and `z_i`
  inside `Ã`.

## Main results

* `HJO.Dyck.Tilde.Atilde.eq_of_sourceRel` and
  `HJO.Dyck.Tilde.Atilde.eq_of_sourceRelStar`: the unstarred and the starred group of relations
  hold in `Ã`.
* `HJO.Dyck.Tilde.Atilde.mixed_z`, `HJO.Dyck.Tilde.Atilde.mixed_y`,
  `HJO.Dyck.Tilde.Atilde.mixed_top`: the three mixed relations.

## Implementation notes

The substitution is carried out *by supplying the scalars*, not through `Invertible`: `cornerOf`
and the descending word take the inverse `qi` of `q` and the inverse `di` of `q - 1` as plain ring
elements, so that the starred instantiation — where those scalars become `q` and
`(q⁻¹-1)⁻¹ = -q(q-1)⁻¹`, the latter checked in
`HJO.Dyck.Tilde.neg_mul_invOf_sub_one_mul` — needs no instance search and no `letI`. The two
`Invertible` hypotheses are carried by `Ã` itself, which does use `⅟q` and `⅟(q-1)`.

`tinvOf q qi T e = qi • (T + (q-1) • e)` is `HJO.Dyck.braidInvGen` with the inverse supplied, and
`HJO.Dyck.Tilde.tinvOf_tinvOf` is the check that the substitution is an involution on the loops:
applying it again with the substituted scalars returns `T` exactly, which is the assertion that
`T_i⁻¹` is sent back to `T_i` and hence that the starred group really is the paper's own list read
in the starred generators.

`braid_eq_zero` — the assertion that the quiver has no loop `T_i` at the vertex `k` when
`i + 2 > k` — is *not* part of `SourceRel`, and deliberately so. It is a statement about the
quiver, imposed once; substituted into the starred group it would read `q⁻¹(0 + (q-1)e_k) = 0`,
i.e. `(q-1)e_k = 0`, which kills every idempotent. The same goes for the idempotent relations and
for the incidences of `d₋` and of the loops, which do not mention the raising arrow and are imposed
once. What `SourceRel` carries beyond the paper's nine relations is the incidence of the raising
arrow, `e_{k+1}d₊ = d₊ = d₊e_k`: that one *must* be substituted, `d₊^*` being an arrow of the
enlarged quiver with the same two ends.

The three mixed relations are read at the vertex at which their paths begin, as throughout:
`d₊ : k → k+1` is `dPlus k`, so in `z_{i+1}d₊ - d₊z_i` the left `z_{i+1}` is a corner
element at the vertex `k + 1` and the right `z_i` one at the vertex `k`, and the admissible range
is `1 ≤ i ≤ k`. In the third relation both corner elements sit at the vertex `k + 1` and the scalar
is `uq^{k+1}`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31**
(2018) 661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck

/-! ### The paper's data, written in an arbitrary family of generators -/

section Generic

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]

/-- The commutator `d₊d₋ - d₋d₊` at the vertex `k + 1`, for an arbitrary raising family `U` and
lowering family `D`. At `U = d₊` this is `HJO.Dyck.Aq.Delta`; at `U = d₊^*` it is the starred
commutator the elements `z_i` are built from. -/
def commOf (U D : ℕ → A) (k : ℕ) : A := U k * D k - D (k + 1) * U (k + 1)

/-- The polynomial inverse `T̂ = q⁻¹(T + (q-1)e)` of a loop, with the inverse `qi` of `q` supplied
as a ring element rather than through `Invertible`. -/
def tinvOf (q qi : K) (T e : A) : A := qi • (T + (q - 1) • e)

/-- The descending word `T̂_n ⋯ T̂_1` at the vertex `k`, the empty word being the idempotent `E k`.
-/
def tinvWordOf (q qi : K) (E : ℕ → A) (T : ℕ → ℕ → A) (k : ℕ) : ℕ → A
  | 0 => E k
  | n + 1 => tinvOf q qi (T k n) (E k) * tinvWordOf q qi E T k n

/-- The corner elements read from the top down: `cornerAux … k j` is `y_{k-j}`. -/
def cornerAux (q qi di : K) (E U D : ℕ → A) (T : ℕ → ℕ → A) (k : ℕ) : ℕ → A
  | 0 => di • (tinvWordOf q qi E T k (k - 1) * commOf U D (k - 1) * E k)
  | j + 1 => qi • (T k (k - j - 2) * cornerAux q qi di E U D T k j * T k (k - j - 2))

/-- **The corner element `y_i` at the vertex `k`**, written in an arbitrary family of generators:
`y_k = (q-1)⁻¹ T̂_{k-1} ⋯ T̂_1 (UD - DU) E_k` and `y_i = q⁻¹ T_i y_{i+1} T_i` walking down. The
inverses of `q` and of `q - 1` are supplied as the ring elements `qi` and `di`. -/
def cornerOf (q qi di : K) (E U D : ℕ → A) (T : ℕ → ℕ → A) (k i : ℕ) : A :=
  cornerAux q qi di E U D T k (k - i)

/-! #### Transport along an algebra map -/

variable (f : A →ₐ[K] B) {E U D : ℕ → A} {T : ℕ → ℕ → A} {E' U' D' : ℕ → B} {T' : ℕ → ℕ → B}

theorem map_commOf (hU : ∀ n, f (U n) = U' n) (hD : ∀ n, f (D n) = D' n) (k : ℕ) :
    f (commOf U D k) = commOf U' D' k := by
  simp [commOf, hU, hD]

theorem map_tinvOf (q qi : K) {T e : A} {T' e' : B} (hT : f T = T') (he : f e = e') :
    f (tinvOf q qi T e) = tinvOf q qi T' e' := by
  simp [tinvOf, hT, he]

theorem map_tinvWordOf (q qi : K) (hE : ∀ n, f (E n) = E' n) (hT : ∀ n i, f (T n i) = T' n i)
    (k n : ℕ) : f (tinvWordOf q qi E T k n) = tinvWordOf q qi E' T' k n := by
  induction n with
  | zero => exact hE k
  | succ n ih => rw [tinvWordOf, tinvWordOf, map_mul, map_tinvOf f q qi (hT k n) (hE k), ih]

theorem map_cornerAux (q qi di : K) (hE : ∀ n, f (E n) = E' n) (hU : ∀ n, f (U n) = U' n)
    (hD : ∀ n, f (D n) = D' n) (hT : ∀ n i, f (T n i) = T' n i) (k j : ℕ) :
    f (cornerAux q qi di E U D T k j) = cornerAux q qi di E' U' D' T' k j := by
  induction j with
  | zero =>
    rw [cornerAux, cornerAux, map_smul, map_mul, map_mul, map_tinvWordOf f q qi hE hT,
      map_commOf f hU hD, hE]
  | succ j ih => rw [cornerAux, cornerAux, map_smul, map_mul, map_mul, ih, hT]

theorem map_cornerOf (q qi di : K) (hE : ∀ n, f (E n) = E' n) (hU : ∀ n, f (U n) = U' n)
    (hD : ∀ n, f (D n) = D' n) (hT : ∀ n i, f (T n i) = T' n i) (k i : ℕ) :
    f (cornerOf q qi di E U D T k i) = cornerOf q qi di E' U' D' T' k i :=
  map_cornerAux f q qi di hE hU hD hT k (k - i)

/-! #### The paper's relations, in an arbitrary family of generators -/

/-- **The paper's relations**, written in an arbitrary family of generators: the incidence of the
raising arrow `U`, and the nine relations of `HJO.Dyck.Aq`. Everything that does not mention the
raising arrow — the idempotents, the incidences of `D` and of the loops, and the vanishing of the
loops the quiver does not have — is excluded, being a statement about the quiver rather than a
relation to be substituted. -/
inductive SourceRel (q : K) (E U D : ℕ → A) (T : ℕ → ℕ → A) : A → A → Prop where
  /-- The raising arrow lands at the vertex `k + 1`. -/
  | vertex_mul_up (k : ℕ) : SourceRel q E U D T (E (k + 1) * U k) (U k)
  /-- The raising arrow starts at the vertex `k`. -/
  | up_mul_vertex (k : ℕ) : SourceRel q E U D T (U k * E k) (U k)
  /-- `(T_i - 1)(T_i + q) = 0` at the vertex `k`. -/
  | quadratic {k i : ℕ} (h : i + 2 ≤ k) :
      SourceRel q E U D T ((T k i - E k) * (T k i + q • E k)) 0
  /-- `T_iT_{i+1}T_i = T_{i+1}T_iT_{i+1}`. -/
  | braid_braid {k i : ℕ} (h : i + 3 ≤ k) :
      SourceRel q E U D T (T k i * T k (i + 1) * T k i) (T k (i + 1) * T k i * T k (i + 1))
  /-- `T_iT_j = T_jT_i` for `|i - j| > 1`. -/
  | braid_comm {k i j : ℕ} (hi : i + 2 ≤ k) (hj : j + 2 ≤ k) (hij : i + 1 < j) :
      SourceRel q E U D T (T k i * T k j) (T k j * T k i)
  /-- `T_id₋ = d₋T_i`. -/
  | braid_down {m i : ℕ} (h : i + 2 ≤ m) :
      SourceRel q E U D T (T m i * D m) (D m * T (m + 1) i)
  /-- `d₊T_i = T_{i+1}d₊`. -/
  | up_braid {k i : ℕ} (h : i + 2 ≤ k) :
      SourceRel q E U D T (U k * T k i) (T (k + 1) (i + 1) * U k)
  /-- `T_1d₊² = d₊²`. -/
  | braid_up_up (k : ℕ) :
      SourceRel q E U D T (T (k + 2) 0 * (U (k + 1) * U k)) (U (k + 1) * U k)
  /-- `d₋²T_{k-1} = d₋²`. -/
  | down_down_braid (m : ℕ) :
      SourceRel q E U D T (D m * D (m + 1) * T (m + 2) m) (D m * D (m + 1))
  /-- `d₋(d₊d₋ - d₋d₊)T_{k-1} = q(d₊d₋ - d₋d₊)d₋`. -/
  | down_delta (j : ℕ) :
      SourceRel q E U D T (D (j + 1) * commOf U D (j + 1) * T (j + 2) j)
        (q • (commOf U D j * D (j + 1)))
  /-- `T_1(d₊d₋ - d₋d₊)d₊ = qd₊(d₊d₋ - d₋d₊)`. -/
  | braid_delta (m : ℕ) :
      SourceRel q E U D T (T (m + 2) 0 * commOf U D (m + 1) * U (m + 1))
        (q • (U (m + 1) * commOf U D m))

end Generic

/-! ### The generic data, read in `𝔸_q` -/

namespace Aq

variable {K : Type*} [CommRing K] {q : K}

theorem commOf_eq_Delta (k : ℕ) : commOf (dPlus K q) (dMinus K q) k = Delta K q k := rfl

variable [Invertible q]

theorem tinvOf_eq_Tinv (k i : ℕ) : tinvOf q ⅟q (Tg K q k i) (e K q k) = Tinv K q k i := rfl

theorem tinvWordOf_eq_tinvWord (k n : ℕ) :
    tinvWordOf q ⅟q (e K q) (Tg K q) k n = tinvWord K q k n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tinvWordOf, tinvWord, tinvOf_eq_Tinv, ih]

variable [Invertible (q - 1)]

/-- **The generic corner element is the corner element**: `HJO.Dyck.cornerOf`, instantiated at the
generators of `𝔸_q` and at the scalars `⅟q` and `⅟(q-1)`, is `HJO.Dyck.Aq.yElt`. This is the check
that the generic formula transcribes `HJO.Dyck.Aq.yElt` and nothing else. -/
theorem cornerOf_eq_yElt (k i : ℕ) :
    cornerOf q ⅟q ⅟(q - 1) (e K q) (dPlus K q) (dMinus K q) (Tg K q) k i = yElt K q k i := by
  rw [cornerOf, yElt]
  generalize k - i = j
  induction j with
  | zero => rw [cornerAux, yAux, tinvWordOf_eq_tinvWord, commOf_eq_Delta]
  | succ j ih => rw [cornerAux, yAux, ih]

end Aq

/-! ### The enlarged quiver -/

namespace Tilde

/-- The generators of the path algebra of the paper's enlarged quiver: the idempotent at each
vertex, the two raising arrows `d₊` and `d₊^*`, the lowering arrow, and the loops. -/
inductive Gen where
  /-- The idempotent at the vertex `k`. -/
  | vertex (k : ℕ)
  /-- The raising arrow `d₊` from the vertex `k` to the vertex `k + 1`. -/
  | up (k : ℕ)
  /-- The second raising arrow `d₊^*` from the vertex `k` to the vertex `k + 1`. -/
  | upStar (k : ℕ)
  /-- The lowering arrow `d₋` from the vertex `k + 1` to the vertex `k`. -/
  | down (k : ℕ)
  /-- The loop `T_{i+1}` at the vertex `k`. -/
  | braid (k i : ℕ)
  deriving DecidableEq

section Free

variable (K : Type*) [CommRing K] (q u : K)

/-- `e k` in the free algebra on the enlarged quiver's generators. -/
abbrev freeE (k : ℕ) : FreeAlgebra K Gen := FreeAlgebra.ι K (Gen.vertex k)

/-- `d₊` in the free algebra on the enlarged quiver's generators. -/
abbrev freeUp (k : ℕ) : FreeAlgebra K Gen := FreeAlgebra.ι K (Gen.up k)

/-- `d₊^*` in the free algebra on the enlarged quiver's generators. -/
abbrev freeUpStar (k : ℕ) : FreeAlgebra K Gen := FreeAlgebra.ι K (Gen.upStar k)

/-- `d₋` in the free algebra on the enlarged quiver's generators. -/
abbrev freeDown (k : ℕ) : FreeAlgebra K Gen := FreeAlgebra.ι K (Gen.down k)

/-- The paper's `T_{i+1}` at the vertex `k`, in the free algebra. -/
abbrev freeT (k i : ℕ) : FreeAlgebra K Gen := FreeAlgebra.ι K (Gen.braid k i)

variable [Invertible q]

/-- The polynomial inverse `T̂_{i+1}` at the vertex `k`, in the free algebra: the element the
substitution `T_i ↦ T_i⁻¹` puts in place of the loop. -/
noncomputable def freeTinv (k i : ℕ) : FreeAlgebra K Gen :=
  tinvOf q ⅟q (freeT K k i) (freeE K k)

variable {K q}

/-- **The substitution is an involution on the loops**: applying the polynomial inverse a second
time, with the substituted scalars `q ↦ q⁻¹` and `q⁻¹ ↦ q`, returns the loop itself. This is what
makes the starred group of relations the paper's own list: the starred copy of `T̂_i` is `T_i`. -/
theorem tinvOf_tinvOf {A : Type*} [Ring A] [Algebra K A] (T e : A) :
    tinvOf (⅟q) q (tinvOf q ⅟q T e) e = T := by
  have h : q - 1 + q * (⅟q - 1) = 0 := by
    rw [mul_sub, mul_one, mul_invOf_self]; ring
  rw [tinvOf, tinvOf, smul_add, smul_smul, mul_invOf_self, one_smul, add_assoc, smul_smul,
    ← add_smul, h, zero_smul, add_zero]

/-- The scalar `-q(q-1)⁻¹` is the inverse of `q⁻¹ - 1`, which is what
`HJO.Dyck.Tilde.freeZ` supplies in place of `(q-1)⁻¹` under the substitution. -/
theorem neg_mul_invOf_sub_one_mul [Invertible (q - 1)] : -(q * ⅟(q - 1)) * (⅟q - 1) = 1 := by
  have h : ⅟q - 1 = -(⅟q * (q - 1)) := by rw [mul_sub, mul_one, invOf_mul_self]; ring
  rw [h, neg_mul_neg,
    show q * ⅟(q - 1) * (⅟q * (q - 1)) = q * ⅟q * (⅟(q - 1) * (q - 1)) from by ring,
    mul_invOf_self, invOf_mul_self, one_mul]

variable (K q) [Invertible (q - 1)]

/-- **The corner element `y_i`** at the vertex `k`, in the free algebra on the enlarged quiver. -/
noncomputable def freeY (k i : ℕ) : FreeAlgebra K Gen :=
  cornerOf q ⅟q ⅟(q - 1) (freeE K) (freeUp K) (freeDown K) (freeT K) k i

/-- **The corner element `z_i`** at the vertex `k`, in the free algebra on the enlarged quiver: the
same two formulas after the substitution `q ↦ q⁻¹`, `d₊ ↦ d₊^*`, `T_i ↦ T_i⁻¹`. The substituted
scalars are `q⁻¹ ↦ q` and `(q⁻¹-1)⁻¹ = -q(q-1)⁻¹`. -/
noncomputable def freeZ (k i : ℕ) : FreeAlgebra K Gen :=
  cornerOf (⅟q) q (-(q * ⅟(q - 1))) (freeE K) (freeUpStar K) (freeDown K) (freeTinv K q) k i

/-- **The relations of `Ã`.** The quiver's own structure, then the paper's relations in the
unstarred generators, then the same inductive read in the starred ones, then the three mixed
relations. -/
inductive Rel : FreeAlgebra K Gen → FreeAlgebra K Gen → Prop where
  /-- The vertex elements are idempotent. -/
  | vertex_mul_self (k : ℕ) : Rel (freeE K k * freeE K k) (freeE K k)
  /-- Distinct vertices are orthogonal. -/
  | vertex_mul_vertex {k l : ℕ} (h : k ≠ l) : Rel (freeE K k * freeE K l) 0
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
  /-- **The unstarred group**: the paper's relations in `d₊` and the loops. -/
  | source {x y : FreeAlgebra K Gen}
      (h : SourceRel q (freeE K) (freeUp K) (freeDown K) (freeT K) x y) : Rel x y
  /-- **The starred group**: the very same relations after `q ↦ q⁻¹`, `d₊ ↦ d₊^*`,
  `T_i ↦ T_i⁻¹`. -/
  | sourceStar {x y : FreeAlgebra K Gen}
      (h : SourceRel (⅟q) (freeE K) (freeUpStar K) (freeDown K) (freeTinv K q) x y) : Rel x y
  /-- **The first mixed relation** `z_{i+1}d₊ = d₊z_i`, at the vertex `k` with `1 ≤ i ≤ k`. -/
  | mixed_z {k i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
      Rel (freeZ K q (k + 1) (i + 1) * freeUp K k) (freeUp K k * freeZ K q k i)
  /-- **The second mixed relation** `y_{i+1}d₊^* = d₊^*y_i`, at the vertex `k` with `1 ≤ i ≤ k`. -/
  | mixed_y {k i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
      Rel (freeY K q (k + 1) (i + 1) * freeUpStar K k) (freeUpStar K k * freeY K q k i)
  /-- **The third mixed relation** `z_1d₊ + uq^{k+1}y_1d₊^* = 0`, at the vertex `k`. -/
  | mixed_top (k : ℕ) :
      Rel (freeZ K q (k + 1) 1 * freeUp K k)
        (-(u * q ^ (k + 1)) • (freeY K q (k + 1) 1 * freeUpStar K k))

end Free

/-- **The extended Dyck path algebra `Ã`**: the path algebra over `K` of the paper's quiver
enlarged by a second raising arrow `d₊^*` at every vertex, modulo the two-sided ideal generated by
the relations of `𝔸_q`, their images under `q ↦ q⁻¹`, `d₊ ↦ d₊^*`, `T_i ↦ T_i⁻¹`, and the three
mixed relations. -/
@[hjo "def_cm_dpa_tilde"]
abbrev Atilde (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)] : Type _ :=
  RingQuot (Rel K q u)

namespace Atilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-- The quotient map from the free algebra on the enlarged quiver onto `Ã`. -/
noncomputable def mk (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)] :
    FreeAlgebra K Gen →ₐ[K] Atilde K q u :=
  RingQuot.mkAlgHom K (Rel K q u)

/-- **The idempotent at the vertex `k`** in `Ã`. -/
@[hjo "def_cm_dpa_tilde"]
noncomputable def e (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (k : ℕ) : Atilde K q u := mk K q u (freeE K k)

/-- **The raising arrow `d₊`** in `Ã`. -/
@[hjo "def_cm_dpa_tilde"]
noncomputable def dPlus (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (k : ℕ) : Atilde K q u := mk K q u (freeUp K k)

/-- **The second raising arrow `d₊^*`** in `Ã`, the arrow by which the quiver of `HJO.Dyck.Aq` is
enlarged. -/
@[hjo "def_cm_dpa_tilde"]
noncomputable def dPlusStar (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (k : ℕ) : Atilde K q u := mk K q u (freeUpStar K k)

/-- **The lowering arrow `d₋`** in `Ã`. -/
@[hjo "def_cm_dpa_tilde"]
noncomputable def dMinus (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (k : ℕ) : Atilde K q u := mk K q u (freeDown K k)

/-- **The loop `T_{i+1}` at the vertex `k`** in `Ã`. -/
@[hjo "def_cm_dpa_tilde"]
noncomputable def Tg (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (k i : ℕ) : Atilde K q u := mk K q u (freeT K k i)

/-- The polynomial inverse of the loop `T_{i+1}` at the vertex `k`, inside `Ã`. -/
noncomputable def Tinv (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (k i : ℕ) : Atilde K q u := tinvOf q ⅟q (Tg K q u k i) (e K q u k)

@[simp] theorem mk_freeE (k : ℕ) : mk K q u (freeE K k) = e K q u k := rfl
@[simp] theorem mk_freeUp (k : ℕ) : mk K q u (freeUp K k) = dPlus K q u k := rfl
@[simp] theorem mk_freeUpStar (k : ℕ) : mk K q u (freeUpStar K k) = dPlusStar K q u k := rfl
@[simp] theorem mk_freeDown (k : ℕ) : mk K q u (freeDown K k) = dMinus K q u k := rfl
@[simp] theorem mk_freeT (k i : ℕ) : mk K q u (freeT K k i) = Tg K q u k i := rfl

@[simp] theorem mk_freeTinv (k i : ℕ) : mk K q u (freeTinv K q k i) = Tinv K q u k i :=
  map_tinvOf _ q ⅟q (mk_freeT k i) (mk_freeE k)

/-- **The corner element `y_i`** at the vertex `k`, inside `Ã`. -/
@[hjo "def_cm_dpa_tilde"]
noncomputable def yElt (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (k i : ℕ) : Atilde K q u :=
  cornerOf q ⅟q ⅟(q - 1) (e K q u) (dPlus K q u) (dMinus K q u) (Tg K q u) k i

/-- **The corner element `z_i`** at the vertex `k`, inside `Ã`: the same two formulas read in the
starred generators. -/
@[hjo "def_cm_dpa_tilde"]
noncomputable def zElt (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (k i : ℕ) : Atilde K q u :=
  cornerOf (⅟q) q (-(q * ⅟(q - 1))) (e K q u) (dPlusStar K q u) (dMinus K q u) (Tinv K q u) k i

@[simp] theorem mk_freeY (k i : ℕ) : mk K q u (freeY K q k i) = yElt K q u k i :=
  map_cornerOf _ q ⅟q ⅟(q - 1) mk_freeE mk_freeUp mk_freeDown mk_freeT k i

@[simp] theorem mk_freeZ (k i : ℕ) : mk K q u (freeZ K q k i) = zElt K q u k i :=
  map_cornerOf _ (⅟q) q (-(q * ⅟(q - 1))) mk_freeE mk_freeUpStar mk_freeDown mk_freeTinv k i

/-- Any relation of `Rel` holds in `Ã`. -/
theorem mk_rel {x y : FreeAlgebra K Gen} (h : Rel K q u x y) : mk K q u x = mk K q u y :=
  RingQuot.mkAlgHom_rel K h

/-! ### The path-algebra structure -/

@[simp]
theorem e_mul_self (k : ℕ) : e K q u k * e K q u k = e K q u k := by
  simpa using mk_rel (Rel.vertex_mul_self (K := K) (q := q) (u := u) k)

@[simp]
theorem e_mul_e_of_ne {k l : ℕ} (h : k ≠ l) : e K q u k * e K q u l = 0 := by
  simpa using mk_rel (Rel.vertex_mul_vertex (K := K) (q := q) (u := u) h)

@[simp]
theorem e_mul_dMinus (k : ℕ) : e K q u k * dMinus K q u k = dMinus K q u k := by
  simpa using mk_rel (Rel.vertex_mul_down (K := K) (q := q) (u := u) k)

@[simp]
theorem dMinus_mul_e (k : ℕ) : dMinus K q u k * e K q u (k + 1) = dMinus K q u k := by
  simpa using mk_rel (Rel.down_mul_vertex (K := K) (q := q) (u := u) k)

@[simp]
theorem e_mul_Tg (k i : ℕ) : e K q u k * Tg K q u k i = Tg K q u k i := by
  simpa using mk_rel (Rel.vertex_mul_braid (K := K) (q := q) (u := u) k i)

@[simp]
theorem Tg_mul_e (k i : ℕ) : Tg K q u k i * e K q u k = Tg K q u k i := by
  simpa using mk_rel (Rel.braid_mul_vertex (K := K) (q := q) (u := u) k i)

/-- The polynomial inverse is a loop at its vertex, absorbed by the idempotent on the left. -/
@[simp]
theorem e_mul_Tinv (k i : ℕ) : e K q u k * Tinv K q u k i = Tinv K q u k i := by
  rw [Tinv, tinvOf, mul_smul_comm, mul_add, mul_smul_comm, e_mul_Tg, e_mul_self]

/-- The polynomial inverse is a loop at its vertex, absorbed by the idempotent on the right. -/
@[simp]
theorem Tinv_mul_e (k i : ℕ) : Tinv K q u k i * e K q u k = Tinv K q u k i := by
  rw [Tinv, tinvOf, smul_mul_assoc, add_mul, smul_mul_assoc, Tg_mul_e, e_mul_self]

/-- The quiver has exactly `k - 1` loops at the vertex `k`. -/
@[hjo "def_cm_dpa_tilde"]
theorem Tg_eq_zero {k i : ℕ} (h : k ≤ i + 1) : Tg K q u k i = 0 := by
  simpa using mk_rel (Rel.braid_eq_zero (K := K) (q := q) (u := u) h)

/-! ### The unstarred and the starred groups of relations -/

/-- **The unstarred group of relations holds in `Ã`**: every instance of `HJO.Dyck.SourceRel`, read
at the scalar `q` and the generators `e`, `d₊`, `d₋`, `T`, is an identity of `Ã`. -/
@[hjo "def_cm_dpa_tilde"]
theorem eq_of_sourceRel {x y : Atilde K q u}
    (h : SourceRel q (e K q u) (dPlus K q u) (dMinus K q u) (Tg K q u) x y) : x = y := by
  induction h with
  | vertex_mul_up k =>
    simpa using mk_rel (Rel.source (u := u) (SourceRel.vertex_mul_up k))
  | up_mul_vertex k =>
    simpa using mk_rel (Rel.source (u := u) (SourceRel.up_mul_vertex k))
  | quadratic h =>
    simpa using mk_rel (Rel.source (u := u) (SourceRel.quadratic h))
  | braid_braid h =>
    simpa using mk_rel (Rel.source (u := u) (SourceRel.braid_braid h))
  | braid_comm hi hj hij =>
    simpa using mk_rel (Rel.source (u := u) (SourceRel.braid_comm hi hj hij))
  | braid_down h =>
    simpa using mk_rel (Rel.source (u := u) (SourceRel.braid_down h))
  | up_braid h =>
    simpa using mk_rel (Rel.source (u := u) (SourceRel.up_braid h))
  | braid_up_up k =>
    simpa using mk_rel (Rel.source (u := u) (SourceRel.braid_up_up k))
  | down_down_braid m =>
    simpa using mk_rel (Rel.source (u := u) (SourceRel.down_down_braid m))
  | down_delta j =>
    simpa [commOf] using mk_rel (Rel.source (u := u) (SourceRel.down_delta (E := freeE K) j))
  | braid_delta m =>
    simpa [commOf] using mk_rel (Rel.source (u := u) (SourceRel.braid_delta (E := freeE K) m))

/-- **The starred group of relations holds in `Ã`**: every instance of `HJO.Dyck.SourceRel`, read
at the substituted scalar `q⁻¹` and the substituted generators `e`, `d₊^*`, `d₋`, `T̂`, is an
identity of `Ã`. This is the second group — the paper's own relations after
`q ↦ q⁻¹`, `d₊ ↦ d₊^*`, `T_i ↦ T_i⁻¹`. -/
@[hjo "def_cm_dpa_tilde"]
theorem eq_of_sourceRelStar {x y : Atilde K q u}
    (h : SourceRel (⅟q) (e K q u) (dPlusStar K q u) (dMinus K q u) (Tinv K q u) x y) : x = y := by
  induction h with
  | vertex_mul_up k =>
    simpa using mk_rel (Rel.sourceStar (u := u) (SourceRel.vertex_mul_up k))
  | up_mul_vertex k =>
    simpa using mk_rel (Rel.sourceStar (u := u) (SourceRel.up_mul_vertex k))
  | quadratic h =>
    simpa using mk_rel (Rel.sourceStar (u := u) (SourceRel.quadratic h))
  | braid_braid h =>
    simpa using mk_rel (Rel.sourceStar (u := u) (SourceRel.braid_braid h))
  | braid_comm hi hj hij =>
    simpa using mk_rel (Rel.sourceStar (u := u) (SourceRel.braid_comm hi hj hij))
  | braid_down h =>
    simpa using mk_rel (Rel.sourceStar (u := u) (SourceRel.braid_down h))
  | up_braid h =>
    simpa using mk_rel (Rel.sourceStar (u := u) (SourceRel.up_braid h))
  | braid_up_up k =>
    simpa using mk_rel (Rel.sourceStar (u := u) (SourceRel.braid_up_up k))
  | down_down_braid m =>
    simpa using mk_rel (Rel.sourceStar (u := u) (SourceRel.down_down_braid m))
  | down_delta j =>
    simpa [commOf] using mk_rel (Rel.sourceStar (u := u) (SourceRel.down_delta (E := freeE K) j))
  | braid_delta m =>
    simpa [commOf] using mk_rel (Rel.sourceStar (u := u) (SourceRel.braid_delta (E := freeE K) m))

/-! ### The three mixed relations -/

/-- **The first mixed relation** `z_{i+1}d₊ = d₊z_i`. -/
@[hjo "def_cm_dpa_tilde"]
theorem mixed_z {k i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    zElt K q u (k + 1) (i + 1) * dPlus K q u k = dPlus K q u k * zElt K q u k i := by
  simpa using mk_rel (Rel.mixed_z (K := K) (q := q) (u := u) h1 h2)

/-- **The second mixed relation** `y_{i+1}d₊^* = d₊^*y_i`. -/
@[hjo "def_cm_dpa_tilde"]
theorem mixed_y {k i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    yElt K q u (k + 1) (i + 1) * dPlusStar K q u k = dPlusStar K q u k * yElt K q u k i := by
  simpa using mk_rel (Rel.mixed_y (K := K) (q := q) (u := u) h1 h2)

/-- **The third mixed relation** `z_1d₊ + uq^{k+1}y_1d₊^* = 0`. -/
@[hjo "def_cm_dpa_tilde"]
theorem mixed_top (k : ℕ) :
    zElt K q u (k + 1) 1 * dPlus K q u k
      + (u * q ^ (k + 1)) • (yElt K q u (k + 1) 1 * dPlusStar K q u k) = 0 := by
  have h := mk_rel (Rel.mixed_top (K := K) (q := q) (u := u) k)
  simp only [map_mul, map_smul, mk_freeZ, mk_freeY, mk_freeUp, mk_freeUpStar] at h
  rw [h, neg_smul, neg_add_cancel]

end Atilde

end Tilde

end HJO.Dyck
