/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.AtildeKernel
public meta import HJO.Attr

/-! # Two preliminaries of the structure theorem for the double module

Facts used by `HJO/CarlssonMellit/DpaStructure.lean` that need none of its machinery.

## Main results

* `HJO.Dyck.cornerOf_congr`: a corner element `y_i`, `i ≥ 1`, reads only the loops `T_j` with
  `j + 2 ≤ k`.
* `HJO.Dyck.Tilde.Atilde.mellitKernel_le_atildeE0`: every element of `𝓘` ends in `𝟏_0`.
-/

@[expose] public section

namespace HJO.Dyck

/-! ### Corner elements only read the loops inside the quiver's range -/

section Congr

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]

/-- The words `tinvWordOf` at a level `k` and depth `n ≤ k - 1` agree for two loop families that
agree on every `T_j` with `j + 2 ≤ k`. -/
theorem tinvWordOf_congr (q qi : K) (E : ℕ → A) {T T' : ℕ → ℕ → A}
    (hT : ∀ n j, j + 2 ≤ n → T n j = T' n j) {k : ℕ} :
    ∀ n, n ≤ k - 1 → tinvWordOf q qi E T k n = tinvWordOf q qi E T' k n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [tinvWordOf, tinvWordOf, tinvWordOf_congr q qi E hT n (by omega), hT k n (by omega)]

/-- The auxiliary corner words `cornerAux` at a level `k` and an index `j = 0` or `j + 1 ≤ k` agree
for two loop families that agree on every `T_j` with `j + 2 ≤ k`. -/
theorem cornerAux_congr (q qi di : K) (E U D : ℕ → A) {T T' : ℕ → ℕ → A}
    (hT : ∀ n j, j + 2 ≤ n → T n j = T' n j) {k : ℕ} :
    ∀ j, (j = 0 ∨ j + 1 ≤ k) →
      cornerAux q qi di E U D T k j = cornerAux q qi di E U D T' k j
  | 0, _ => by rw [cornerAux, cornerAux, tinvWordOf_congr q qi E hT (k - 1) le_rfl]
  | j + 1, hj => by
    rw [cornerAux, cornerAux, cornerAux_congr q qi di E U D hT j (Or.inr (by omega)),
      hT k (k - j - 2) (by omega)]

/-- **A corner element `y_i` with `i ≥ 1` reads only the loops `T_j` with `j + 2 ≤ k`**, so two
loop families agreeing inside the quiver's range give the same corner elements. -/
theorem cornerOf_congr (q qi di : K) (E U D : ℕ → A) {T T' : ℕ → ℕ → A}
    (hT : ∀ n j, j + 2 ≤ n → T n j = T' n j) {k i : ℕ} (hi : 1 ≤ i) :
    cornerOf q qi di E U D T k i = cornerOf q qi di E U D T' k i :=
  cornerAux_congr q qi di E U D hT (k - i) (by omega)

end Congr

end HJO.Dyck

/-! ### `𝓘` lies in `Ã𝟏_0` -/

namespace HJO.Dyck.Tilde.Atilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-- An element lies in `Ã𝟏_0` exactly when right multiplication by `𝟏_0` fixes it. -/
theorem mem_atildeE0_iff {x : Atilde K q u} : x ∈ atildeE0 K q u ↔ x * e K q u 0 = x := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [rightE0_apply, mul_assoc, e_mul_self]
  · intro h
    exact ⟨x, h⟩

/-- **Every element of `𝓘` ends in `𝟏_0`**: each generator does, and `𝓘` is generated as a left
submodule. -/
theorem mellitKernel_le_atildeE0 :
    (mellitKernel K q u).restrictScalars K ≤ atildeE0 K q u := by
  intro x hx
  rw [mem_atildeE0_iff]
  change x ∈ mellitKernel K q u at hx
  refine Submodule.span_induction (p := fun x _ => x * e K q u 0 = x) ?_ ?_ ?_ ?_ hx
  · rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> rw [mul_assoc, dPlusStarPow_mul_e]
  · rw [zero_mul]
  · intro x y _ _ hx hy; rw [add_mul, hx, hy]
  · intro a x _ hx; rw [smul_eq_mul, mul_assoc, hx]

end HJO.Dyck.Tilde.Atilde
