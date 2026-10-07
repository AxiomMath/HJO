/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.Idempotents
public import HJO.CarlssonMellit.CornerGeneric
public import HJO.CarlssonMellit.DPATildeIdeals
public import HJO.Shuffle.BraidTrainRelations
public import HJO.Shuffle.DpaWords
public meta import HJO.Attr

/-! # The closed form of `z_1`

`z_1` is the starred twin of `y_1`, and the argument for its closed form is that `y_1`'s
closed form follows from the two defining formulas alone, so the starred substitution carries it
over. In this library `z_1` *is* `HJO.Dyck.cornerOf` at the starred family, so that argument is
an instantiation: `HJO.Dyck.cornerOf_one_eq_comm` at `(q⁻¹, d₊^*, T̂)`.

## Main results

* `HJO.Dyck.Tilde.Atilde.starFamily`: the starred generators of `Ã` are a
  `HJO.Dyck.CornerFamily`.
* `HJO.Dyck.Tilde.Atilde.zElt_one_eq_wordDownStar`:
  `z_1𝟏_k = q^k(1-q)^{-1}(d₊^*d₋ - d₋d₊^*)T^*_{k↓1}𝟏_k`.

Along the way, the loops of `Ã` are inverted in their corner exactly as in `𝔸_q`
(`HJO.Dyck.Tilde.Atilde.Tg_mul_Tinv`, `Tinv_mul_Tg`), and `𝟏_kÃ𝟏_k` is named as a unital ring so
that Mellit's starred word `T^*_{k↓1}` can be read in it.

## Implementation notes

The starred family's `T` is `Ã`'s `Tinv`, and the `CornerFamily` field asking that the polynomial
inverse invert it is discharged by `HJO.Dyck.Tilde.tinvOf_tinvOf`: the inverse of `T̂_i`, computed
with the *substituted* scalars, is `T_i` on the nose, so the requirement is the ordinary
`Tinv_mul_Tg` of `Ã`. That is the same observation that made the starred group of relations an
instance of the list `HJO.Dyck.SourceRel` of relations of `𝔸_q`, used a second time.

The scalar is stated as `-(q^k(q-1)^{-1})`, which is `q^k/(1-q)`: `1 - q = -(q-1)`.
It is not written with an `Invertible (1-q)` instance, which would be a second inverse for an
element already invertible and an instance diamond for no gain.

As in `HJO.CarlssonMellit.CornerRing`, the corner of `Ã` is Mathlib's `IsIdempotentElem.Corner` and
no `Module K` structure is put on it: every statement is an equation in `Ã` between the underlying
elements, and the corner supplies only the units that `HJO.Braid.wordDownStar` consumes.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Dyck.Tilde.Atilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-! ### The loops of `Ã` are invertible in their corner -/

/-- The quadratic relation `HJO.Dyck.SourceRel.quadratic` of `𝔸_q`, read in `Ã`. -/
theorem quadratic {k i : ℕ} (h : i + 2 ≤ k) :
    (Tg K q u k i - e K q u k) * (Tg K q u k i + q • e K q u k) = 0 :=
  eq_of_sourceRel (SourceRel.quadratic h)

/-- The quadratic relation expanded, as in `𝔸_q`. -/
theorem Tg_sq {k i : ℕ} (h : i + 2 ≤ k) :
    Tg K q u k i * Tg K q u k i = Tg K q u k i - q • Tg K q u k i + q • e K q u k := by
  have hq := quadratic (K := K) (q := q) (u := u) h
  rw [sub_mul, mul_add, mul_add, mul_smul_comm, mul_smul_comm, Tg_mul_e, e_mul_Tg, e_mul_self,
    sub_eq_zero] at hq
  exact (eq_sub_of_add_eq hq).trans (by abel)

theorem Tinv_eq (k i : ℕ) :
    Tinv K q u k i = ⅟q • (Tg K q u k i + (q - 1) • e K q u k) := rfl

/-- **The loops of `Ã` are invertible in their corner**, with the polynomial inverse. -/
theorem Tg_mul_Tinv {k i : ℕ} (h : i + 2 ≤ k) :
    Tg K q u k i * Tinv K q u k i = e K q u k := by
  have hinner : Tg K q u k i * Tg K q u k i + (q - 1) • Tg K q u k i = q • e K q u k := by
    rw [Tg_sq h, sub_smul, one_smul]; abel
  rw [Tinv_eq, mul_smul_comm, mul_add, mul_smul_comm, Tg_mul_e, hinner, smul_smul,
    invOf_mul_self, one_smul]

/-- The other half: the polynomial inverse is a two-sided inverse in the corner. -/
theorem Tinv_mul_Tg {k i : ℕ} (h : i + 2 ≤ k) :
    Tinv K q u k i * Tg K q u k i = e K q u k := by
  have hinner : Tg K q u k i * Tg K q u k i + (q - 1) • Tg K q u k i = q • e K q u k := by
    rw [Tg_sq h, sub_smul, one_smul]; abel
  rw [Tinv_eq, smul_mul_assoc, add_mul, smul_mul_assoc, e_mul_Tg, hinner, smul_smul,
    invOf_mul_self, one_smul]

/-! ### The starred family -/

theorem e_mul_commOf_star (n : ℕ) :
    e K q u (n + 1) * commOf (dPlusStar K q u) (dMinus K q u) n
      = commOf (dPlusStar K q u) (dMinus K q u) n := by
  rw [commOf, mul_sub, ← mul_assoc, ← mul_assoc, e_mul_dPlusStar, e_mul_dMinus]

theorem commOf_star_mul_e (n : ℕ) :
    commOf (dPlusStar K q u) (dMinus K q u) n * e K q u (n + 1)
      = commOf (dPlusStar K q u) (dMinus K q u) n := by
  rw [commOf, sub_mul, mul_assoc, mul_assoc, dMinus_mul_e, dPlusStar_mul_e]

/-- **The starred generators of `Ã` are a corner family**, so the whole generic corner-element
calculus applies to them. The one clause with content is that the polynomial inverse of `T̂_i`,
computed with the substituted scalars, is `T_i` — which is `HJO.Dyck.Tilde.tinvOf_tinvOf`. -/
theorem starFamily :
    CornerFamily (⅟q) q (e K q u) (dPlusStar K q u) (dMinus K q u) (Tinv K q u) where
  e_mul_e := e_mul_self
  e_mul_T := e_mul_Tinv
  T_mul_e := Tinv_mul_e
  T_mul_Tinv k i h := by
    rw [show tinvOf (⅟q) q (Tinv K q u k i) (e K q u k) = Tg K q u k i from
      tinvOf_tinvOf (Tg K q u k i) (e K q u k), Tinv_mul_Tg h]
  e_mul_comm := e_mul_commOf_star
  comm_mul_e := commOf_star_mul_e

/-! ### The corner of `Ã`, and Mellit's starred word in it -/

/-- The vertex element of `Ã` is idempotent. -/
theorem eIdemT (k : ℕ) : IsIdempotentElem (e K q u k) := e_mul_self k

/-- **The corner `𝟏_kÃ𝟏_k`** as a unital ring, its `1` being the idempotent. -/
abbrev CornerT (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)] (k : ℕ) :
    Type _ := (eIdemT (K := K) (q := q) (u := u) k).Corner

/-- The underlying element of `Ã`. -/
noncomputable def tcval {k : ℕ} (a : CornerT K q u k) : Atilde K q u :=
  Subtype.val (show Subsemigroup.corner (e K q u k) from a)

/-- An element of `Ã` absorbed by the idempotent on both sides, read in the corner. -/
noncomputable def tcmk {k : ℕ} (x : Atilde K q u) (h1 : e K q u k * x = x)
    (h2 : x * e K q u k = x) : CornerT K q u k :=
  show Subsemigroup.corner (e K q u k) from
    ⟨x, (Subsemigroup.mem_corner_iff (eIdemT k)).2 ⟨h1, h2⟩⟩

@[simp] theorem tcval_tcmk {k : ℕ} (x : Atilde K q u) (h1 : e K q u k * x = x)
    (h2 : x * e K q u k = x) : tcval (tcmk x h1 h2) = x := rfl

@[simp] theorem tcval_mul {k : ℕ} (a b : CornerT K q u k) :
    tcval (a * b) = tcval a * tcval b := rfl

@[simp] theorem tcval_one {k : ℕ} : tcval (1 : CornerT K q u k) = e K q u k := rfl

theorem tcval_injective {k : ℕ} {a b : CornerT K q u k} (h : tcval a = tcval b) : a = b :=
  Subtype.ext h

/-- A loop of the corner of `Ã`, as a unit. -/
noncomputable def tbraidUnit {k i : ℕ} (h : i + 2 ≤ k) : (CornerT K q u k)ˣ where
  val := tcmk (Tg K q u k i) (e_mul_Tg k i) (Tg_mul_e k i)
  inv := tcmk (Tinv K q u k i) (e_mul_Tinv k i) (Tinv_mul_e k i)
  val_inv := tcval_injective (by rw [tcval_mul, tcval_one, tcval_tcmk, tcval_tcmk, Tg_mul_Tinv h])
  inv_val := tcval_injective (by rw [tcval_mul, tcval_one, tcval_tcmk, tcval_tcmk, Tinv_mul_Tg h])

/-- The loops of `Ã` at the vertex `k` as a total family of units of the corner, indexed from `1`
as in the word `T^*_{k↓1}`; `1` outside the range `1 ≤ r ≤ k-1`, where there is no loop. -/
noncomputable def tbraidUnits (K : Type*) [CommRing K] (q u : K) [Invertible q]
    [Invertible (q - 1)] (k : ℕ) : ℕ → (CornerT K q u k)ˣ :=
  fun r => if h : 1 ≤ r ∧ r + 1 ≤ k then tbraidUnit (show r - 1 + 2 ≤ k by omega) else 1

/-- Inside the range `1 ≤ r ≤ k-1`, the inverse of the `r`-th letter is `T̂_r`. -/
theorem tcval_tbraidUnits_inv {k r : ℕ} (h1 : 1 ≤ r) (h2 : r + 1 ≤ k) :
    tcval (((tbraidUnits K q u k r)⁻¹ : (CornerT K q u k)ˣ) : CornerT K q u k)
      = Tinv K q u k (r - 1) := by
  have hc : 1 ≤ r ∧ r + 1 ≤ k := ⟨h1, h2⟩
  simp only [tbraidUnits, hc]
  rfl

/-- The starred descending word peels off its leftmost letter. -/
theorem wordDownStar_peel {A : Type*} [Monoid A] (S : ℕ → Aˣ) (n : ℕ) :
    HJO.Braid.wordDownStar S (n + 1 + 1) 1
      = (((S (n + 1))⁻¹ : Aˣ) : A) * HJO.Braid.wordDownStar S (n + 1) 1 := by
  simp only [HJO.Braid.wordDownStar]
  rw [← HJO.Braid.descendingWord_mul (fun r => (((S r)⁻¹ : Aˣ) : A)) (by omega : 1 ≤ n + 1)
    (by omega : n + 1 ≤ n + 1 + 1), HJO.Braid.descendingWord_succ_self]

/-- **Mellit's `T^*_{k↓1}` is the descending word of the polynomial inverses** `T̂_{k-1} ⋯ T̂_1`;
the empty word is the idempotent on both sides. -/
theorem tcval_wordDownStar {k : ℕ} :
    ∀ n : ℕ, n + 1 ≤ k →
      tcval (HJO.Braid.wordDownStar (tbraidUnits K q u k) (n + 1) 1)
        = segOf (e K q u) (Tinv K q u) k 0 n := by
  intro n
  induction n with
  | zero => intro _; rw [HJO.Braid.wordDownStar_self, tcval_one, segOf_zero]
  | succ n ih =>
    intro hn
    rw [wordDownStar_peel, tcval_mul, tcval_tbraidUnits_inv (by omega) (by omega), ih (by omega),
      segOf_succ, Nat.zero_add, Nat.add_sub_cancel]

/-! ### The closed form -/

/-- **The closed form of `z_1`**: `z_1𝟏_k = q^k(1-q)^{-1}(d₊^*d₋ - d₋d₊^*)T^*_{k↓1}𝟏_k`, the scalar
being written `-(q^k(q-1)^{-1})` since `1 - q = -(q-1)`. The proof is the standard one:
the closed form of `y_1` is a statement about an arbitrary corner family, and `z_1` is that family
substituted. -/
@[hjo "lem_dpa_z1_formula"]
theorem zElt_one_eq_wordDownStar {k : ℕ} (hk : 1 ≤ k) :
    zElt K q u k 1
      = (-(q ^ k * ⅟(q - 1))) •
        (commOf (dPlusStar K q u) (dMinus K q u) (k - 1) *
          tcval (HJO.Braid.wordDownStar (tbraidUnits K q u k) k 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h := cornerOf_one_eq_comm (di := -(q * ⅟(q - 1)))
    (starFamily (K := K) (q := q) (u := u)) (k := m + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h
  rw [tcval_wordDownStar m le_rfl]
  simp only [Nat.add_sub_cancel]
  rw [show -(q ^ (m + 1) * ⅟(q - 1)) = q ^ m * -(q * ⅟(q - 1)) from by rw [pow_succ]; ring]
  exact h

end HJO.Dyck.Tilde.Atilde
