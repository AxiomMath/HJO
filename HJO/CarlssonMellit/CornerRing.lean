/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.Idempotents
public import HJO.CarlssonMellit.ArrowWords
public import HJO.CarlssonMellit.CornerPowers
public import HJO.Shuffle.BraidTrainRelations
public import HJO.Shuffle.DpaWords
public meta import HJO.Attr

/-! # The corner `𝟏_k𝔸_q𝟏_k` as a unital ring, and Mellit's words in it

Mellit writes the Dyck path algebra's identities inside the corner `𝟏_k𝔸_q𝟏_k`, whose unit is the
idempotent `𝟏_k`, and his words `T_{k↓1}` are words in *invertible* elements — `HJO.Braid.wordDown`
takes a family of units of a monoid. Neither is available in `𝔸_q` itself: the loops are invertible
only in their corner, and the unit of `𝔸_q` is not in the span of the idempotents at all, so the
empty word `1` of `HJO.Braid.wordDown` is not `e_k`. This file supplies the bridge.

## Main definitions

* `HJO.Dyck.Aq.Corner`: the corner `e_k𝔸_qe_k` as a unital ring, `Mathlib`'s
  `IsIdempotentElem.Corner` at the idempotent `e_k`.
* `HJO.Dyck.Aq.cval`, `HJO.Dyck.Aq.cmk`: the underlying element of `𝔸_q`, and the corner element of
  a given element of `𝔸_q`.
* `HJO.Dyck.Aq.braidUnits`: the loops as a total family of *units* of the corner, which is what
  `HJO.Braid.wordDown` consumes.

## Main results

* `HJO.Dyck.Aq.isUnit_braid_corner`: `T_i𝟏_k` is invertible in `𝟏_k𝔸_q𝟏_k`, with inverse
  `q^{-1}(T_i + (q-1))𝟏_k`.
* `HJO.Dyck.Aq.cval_wordDown`: `T_{k↓1}` is the descending word `HJO.Dyck.Aq.tSeg`.
* `HJO.Dyck.Aq.yElt_one_eq_wordDown`: `y_1𝟏_k = (q^{k-1}(q-1))^{-1}(d₊d₋-d₋d₊)T_{k↓1}𝟏_k`.
* `HJO.Dyck.Aq.wordDown_mul_Tg_cycle`: `T_{k↓1}T_j𝟏_k = T_{j-1}T_{k↓1}𝟏_k`.

## Implementation notes

Mathlib's `IsIdempotentElem.Corner` supplies the `Ring` structure outright, so nothing has to be
built by hand. It does **not** supply a `Module K` or `Algebra K` structure, and this file does not
add one: every statement below is an equation in `𝔸_q` between the *underlying* elements, so the
scalars stay where they already are and the corner is used only to manufacture the units that
`HJO.Braid.wordDown` demands. That is the whole of what was missing.

`HJO.Dyck.Aq.braidUnits` has to be total, since `HJO.Braid.wordDown` takes a family indexed by all
of `ℕ`, while the loop `T_r` at the vertex `k` exists only for `1 ≤ r ≤ k-1` — outside that range
`Tg` is `0`, which is not a unit. The family is therefore `1` outside the range, and
`HJO.Dyck.Aq.cval_braidUnits` is the statement that inside it the letters are the loops. Every word
read below has all of its letters inside the range.

`IsIdempotentElem.Corner` is a plain type synonym for the subsemigroup, with no coercion registered,
so `HJO.Dyck.Aq.cval` and `HJO.Dyck.Aq.cmk` are written out; each of their computation rules is
`rfl`.

## References

A. Mellit, *Toric braids and
`(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K}

/-! ### The corner as a unital ring -/

/-- The vertex element is idempotent, which is what makes `e_k𝔸_qe_k` a unital ring with `e_k` as
its `1`. -/
theorem eIdem (k : ℕ) : IsIdempotentElem (e K q k) := e_mul_self k

/-- **The corner `𝟏_k𝔸_q𝟏_k`** as a unital ring, its `1` being the idempotent `e_k`. -/
abbrev Corner (K : Type*) [CommRing K] (q : K) (k : ℕ) : Type _ :=
  (eIdem (K := K) (q := q) k).Corner

/-- The underlying element of `𝔸_q`. -/
noncomputable def cval {k : ℕ} (a : Corner K q k) : Aq K q :=
  Subtype.val (show Subsemigroup.corner (e K q k) from a)

/-- An element of `𝔸_q` absorbed by the idempotent on both sides, read in the corner. -/
noncomputable def cmk {k : ℕ} (x : Aq K q) (h1 : e K q k * x = x) (h2 : x * e K q k = x) :
    Corner K q k :=
  show Subsemigroup.corner (e K q k) from ⟨x, (Subsemigroup.mem_corner_iff (eIdem k)).2 ⟨h1, h2⟩⟩

@[simp] theorem cval_cmk {k : ℕ} (x : Aq K q) (h1 : e K q k * x = x) (h2 : x * e K q k = x) :
    cval (cmk x h1 h2) = x := rfl

@[simp] theorem cval_mul {k : ℕ} (a b : Corner K q k) : cval (a * b) = cval a * cval b := rfl

@[simp] theorem cval_one {k : ℕ} : cval (1 : Corner K q k) = e K q k := rfl

theorem cval_injective {k : ℕ} {a b : Corner K q k} (h : cval a = cval b) : a = b := Subtype.ext h

/-! ### The loops as units of the corner -/

variable [Invertible q]

/-- A loop of the corner, as a unit: the polynomial inverse is its inverse there. -/
noncomputable def braidUnit {k i : ℕ} (h : i + 2 ≤ k) : (Corner K q k)ˣ where
  val := cmk (Tg K q k i) (e_mul_Tg k i) (Tg_mul_e k i)
  inv := cmk (Tinv K q k i) (e_mul_Tinv k i) (Tinv_mul_e k i)
  val_inv := cval_injective (by rw [cval_mul, cval_one, cval_cmk, cval_cmk, Tg_mul_Tinv h])
  inv_val := cval_injective (by rw [cval_mul, cval_one, cval_cmk, cval_cmk, Tinv_mul_Tg h])

/-- **The loops of the vertex `k` as a total family of units of the corner**, indexed as the paper
indexes them: the `r`-th letter is the paper's `T_r`, which is `Tg k (r-1)`. Outside the paper's
range `1 ≤ r ≤ k-1` the letter is `1`, there being no loop there; `HJO.Braid.wordDown` needs a
family indexed by all of `ℕ` and every word read below stays inside the range. -/
noncomputable def braidUnits (K : Type*) [CommRing K] (q : K) [Invertible q] (k : ℕ) :
    ℕ → (Corner K q k)ˣ :=
  fun r => if h : 1 ≤ r ∧ r + 1 ≤ k then braidUnit (show r - 1 + 2 ≤ k by omega) else 1

/-- Inside the paper's range the letters are the loops. -/
theorem cval_braidUnits {k r : ℕ} (h1 : 1 ≤ r) (h2 : r + 1 ≤ k) :
    cval ((braidUnits K q k r : Corner K q k)) = Tg K q k (r - 1) := by
  have hc : 1 ≤ r ∧ r + 1 ≤ k := ⟨h1, h2⟩
  simp only [braidUnits, hc]
  rfl

/-- **The loops are invertible in the corner**: `T_i𝟏_k` is a unit of `𝟏_k𝔸_q𝟏_k` whose inverse is
`q^{-1}(T_i + (q-1))𝟏_k`, which is `HJO.Dyck.Aq.Tinv`. -/
@[hjo "lem_dpa_braid_invertible"]
theorem isUnit_braid_corner {k i : ℕ} (h1 : 1 ≤ i) (h2 : i + 1 ≤ k) :
    ∃ v : (Corner K q k)ˣ, cval (v : Corner K q k) = Tg K q k (i - 1) ∧
      cval ((v⁻¹ : (Corner K q k)ˣ) : Corner K q k) = Tinv K q k (i - 1) :=
  ⟨braidUnit (show i - 1 + 2 ≤ k by omega), rfl, rfl⟩

/-! ### Mellit's descending word is the descending word of loops -/

/-- The descending word of units peels off its leftmost letter. Pure `List.range'` arithmetic, via
`HJO.Braid.descendingWord_mul`. -/
theorem wordDown_peel {A : Type*} [Monoid A] (S : ℕ → Aˣ) (n : ℕ) :
    HJO.Braid.wordDown S (n + 1 + 1) 1 = (S (n + 1) : A) * HJO.Braid.wordDown S (n + 1) 1 := by
  simp only [HJO.Braid.wordDown]
  rw [← HJO.Braid.descendingWord_mul (fun r => ((S r : A))) (by omega : 1 ≤ n + 1)
    (by omega : n + 1 ≤ n + 1 + 1), HJO.Braid.descendingWord_succ_self]

/-- **Mellit's `T_{k↓1}` is the descending word of loops** `T_{k-1} ⋯ T_1`, which in the shifted
indexing of `HJO.Dyck.Aq.Tg` is `tSeg k 0 (k-1)`; the empty word is the idempotent on both sides. -/
theorem cval_wordDown {k : ℕ} :
    ∀ n : ℕ, n + 1 ≤ k →
      cval (HJO.Braid.wordDown (braidUnits K q k) (n + 1) 1) = tSeg K q k 0 n := by
  intro n
  induction n with
  | zero => intro _; rw [HJO.Braid.wordDown_self, cval_one, tSeg_zero]
  | succ n ih =>
    intro hn
    rw [wordDown_peel, cval_mul, cval_braidUnits (by omega) (by omega), ih (by omega),
      tSeg_succ, Nat.zero_add, Nat.add_sub_cancel]

/-! ### The two identities read in Mellit's notation -/

variable [Invertible (q - 1)]

/-- **The closed form of `y_1` in Mellit's notation**:
`y_1𝟏_k = (q^{k-1}(q-1))^{-1}(d₊d₋-d₋d₊)T_{k↓1}𝟏_k`. Both sides are written as elements of `𝔸_q`;
`T_{k↓1}` is `HJO.Braid.wordDown` of the loops read as units of the corner, and the trailing `𝟏_k`
is absorbed, every factor already lying in `e_k𝔸_qe_k`. -/
@[hjo "lem_dpa_y1_formula"]
theorem yElt_one_eq_wordDown {k : ℕ} (hk : 1 ≤ k) :
    yElt K q k 1
      = ((⅟q) ^ (k - 1) * ⅟(q - 1)) •
        (Delta K q (k - 1) * cval (HJO.Braid.wordDown (braidUnits K q k) k 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [cval_wordDown m (by omega), yElt_one_eq_Delta (by omega)]
  simp only [Nat.add_sub_cancel]

omit [Invertible (q - 1)] in
/-- **The descending word cycles a loop's index down by one**, in Mellit's notation:
`T_{k↓1}T_j𝟏_k = T_{j-1}T_{k↓1}𝟏_k` for `2 ≤ j ≤ k-1`. In the shifted indexing the paper's `T_j`
is `Tg k (m+1)` and its `T_{j-1}` is `Tg k m`, and the range reads `m + 3 ≤ k`. -/
@[hjo "lem_dpa_tdown_shift"]
theorem wordDown_mul_Tg_cycle {k m : ℕ} (h : m + 3 ≤ k) :
    cval (HJO.Braid.wordDown (braidUnits K q k) k 1) * Tg K q k (m + 1)
      = Tg K q k m * cval (HJO.Braid.wordDown (braidUnits K q k) k 1) := by
  obtain ⟨p, rfl⟩ : ∃ p, k = p + 1 := ⟨k - 1, by omega⟩
  rw [cval_wordDown p (by omega)]
  exact tSeg_mul_Tg_cycle p (by omega) (by omega)

end HJO.Dyck.Aq
