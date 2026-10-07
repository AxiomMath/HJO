/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.KernelSpanRoute
public import HJO.CarlssonMellit.CornerTCommute
public import HJO.CarlssonMellit.CornerTransport
public import HJO.CarlssonMellit.StarFlipExists
public meta import HJO.Attr

/-! # Moving the starred corner element rightwards in `Ã`

The span route of `HJO.Dyck.Tilde.Atilde.dPlusStar_mul_mem_aqE0_sup_kernelIdealE0` —
`HJO.Dyck.Tilde.Atilde.aqE0_eq_raisingSpan` — leaves the lemma needing to push `d₊^*` rightwards
through a word in the letters `{e, T, y, d₋}`. Two of those steps are relations of `Ã` (`mixed_y`
for `y`, the starred `up_braid` for `T`), and the third, `d₊^*d₋`, is the starred commutator
`d₊^*d₋ = d₋d₊^* + (q^{-1}-1)T_1^{-1} ⋯ T_{k-1}^{-1}z_k`. That introduces a `z_k`, which then has to
be moved rightwards too. A direct argument asserts at the `y_iG` step that the braid operators
commute with the `z_j` up to index shift, and proves nothing about it.

This file supplies the two moves the span route needs, in the weakest form that suffices:

* **`z` past a loop** (`HJO.Dyck.Tilde.Atilde.zElt_mul_Tg_mem_span`): a *span* statement, not a
  commutation. `z_iT_j` is a `K`-combination of `T_jz_{i'}` and `z_{i'}`. A bare commutation is
  false: for `j` adjacent to `i` the Hecke relation produces the other corner element and a
  scalar, exactly as the unstarred `HJO.Dyck.Aq.Tg_mul_yElt` does.
* **`z` past a lowering arrow** (`HJO.Dyck.Tilde.Atilde.zElt_mul_dMinus`): here a genuine
  commutation `z_i^{(k)}d₋ = d₋z_i^{(k+1)}` *is* true, the starred image of
  `HJO.Dyck.Aq.yElt_mul_dMinus`. That argument asserts this one (as `z_kG = d_-z_kG'` for
  `G = d_-G'`), and it is the one assertion of that argument that holds as stated.

## Where these come from, and what they cost

Both are the *starred images* of `𝔸_q` facts, obtained in two steps: `HJO.Dyck.toTilde` reads the
`𝔸_q` fact inside `Ã`, and a star swap of `HJO.Dyck.IsStarSwap` — which `Ã` admits by
`HJO.Dyck.Tilde.Atilde.exists_isStarSwap` — exchanges the unstarred generators for the starred ones
and `y_i` for `z_i`. So they carry the hypotheses of `HJO.Sym.paramInvLambda`: a ring involution of
`K` inverting `q` and `u`, and `u` invertible. That is a real hypothesis and it is stated, not
hidden; the base field `𝕂 = ℚ(q,u)` satisfies it, and `HJO.Dyck.Tilde.Atilde.exists_isStarSwap`
already carries it.

They are *not* obtained by lifting the `𝔸_q` calculus to `HJO.Dyck.CornerFamily`: that calculus
reads `Tg_comm`, `Tinv_mul_Tinv_mul_Tg`, `Delta_mul_Tg` and `tSeg_mul_Tg_cycle`, none of which is a
field of `CornerFamily`, so the generic route is a rewrite of five files rather than a transport.
The one piece that *is* generic is proved generically here, because both families need it:
`HJO.Dyck.commOf_eq_smul_segUpOf_mul_cornerOf`.

## Main results

* `HJO.Dyck.commOf_eq_smul_segUpOf_mul_cornerOf`: `UD - DU = c(T_1 ⋯ T_{k-1})y_k` in an arbitrary
  `HJO.Dyck.CornerFamily`; at the starred family this is the `z_k` the starred commutator produces.
* `HJO.Dyck.Tilde.Atilde.zElt_mul_dMinus`: **the second move**, `z` past a lowering arrow.
* `HJO.Dyck.Tilde.Atilde.zElt_mul_Tg_mem_span`: **the first move**, `z` past a loop.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Sections 3 and 7.
-/

@[expose] public section

namespace HJO.Dyck

/-! ### The commutator read back from the top corner element, generically -/

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable {q' qi di : K} {E U D : ℕ → A} {T : ℕ → ℕ → A}

/-- The top corner element, unfolded: `y_k = (q-1)^{-1}T̂_{k-1} ⋯ T̂_1(UD-DU)E_k`. The first of the
two defining formulas of `HJO.Dyck.cornerOf`, read off the recursion. -/
theorem cornerOf_self_eq (q' qi di : K) (E U D : ℕ → A) (T : ℕ → ℕ → A) (k : ℕ) :
    cornerOf q' qi di E U D T k k
      = di • (tinvWordOf q' qi E T k (k - 1) * commOf U D (k - 1) * E k) := by
  rw [cornerOf, Nat.sub_self, cornerAux]

/-- **The commutator read back from the top corner element, in an arbitrary corner family**:
`UD - DU = c(T_1 ⋯ T_{k-1})y_k` at the vertex `k`, where `c` is any inverse of the family's `di`.
Multiplying the defining formula for `y_k` on the left by the ascending word of loops cancels the
descending word of inverses it carries, by
`HJO.Dyck.CornerFamily.segUpOf_mul_tinvWordOf`, and the idempotent is absorbed at both ends.

This is `HJO.Dyck.Aq.Delta_eq_smul_tSegUp_mul_yElt` with the family left open, which is what the
*starred* family needs: the starred commutator `d₊^*d₋ - d₋d₊^*` that
`HJO.Dyck.Tilde.Atilde.dPlusStar_mul_mem_aqE0_sup_kernelIdealE0` produces is a word of inverse loops
times `z_k`. -/
theorem commOf_eq_smul_segUpOf_mul_cornerOf (h : CornerFamily q' qi E U D T) {c : K}
    (hc : c * di = 1) {k : ℕ} (hk : 1 ≤ k) :
    commOf U D (k - 1) = c • (segUpOf E T k 0 (k - 1) * cornerOf q' qi di E U D T k k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have htop : cornerOf q' qi di E U D T (m + 1) (m + 1)
      = di • (tinvWordOf q' qi E T (m + 1) m * commOf U D m * E (m + 1)) := by
    have h0 := cornerOf_self_eq q' qi di E U D T (m + 1)
    simpa only [Nat.add_sub_cancel] using h0
  rw [htop, mul_smul_comm, smul_smul, hc, one_smul, ← mul_assoc, ← mul_assoc,
    h.segUpOf_mul_tinvWordOf m le_rfl, h.e_mul_comm, h.comm_mul_e]

/-! ### The bar on the two scalars the Hecke relations carry -/

theorem bar_one_sub_of {K : Type*} [CommRing K] {q : K} [Invertible q] {bar : K ≃+* K}
    (hbar : bar q = ⅟q) : bar (1 - q) = 1 - ⅟q := by rw [map_sub, map_one, hbar]

theorem bar_sub_one_of {K : Type*} [CommRing K] {q : K} [Invertible q] {bar : K ≃+* K}
    (hbar : bar q = ⅟q) : bar (q - 1) = ⅟q - 1 := by rw [map_sub, map_one, hbar]

/-! ### The unstarred corner calculus, read inside `Ã`

Each of the four is an `𝔸_q` lemma, proved in `HJO.Dyck.Aq`, read along `HJO.Dyck.toTilde`.
-/

namespace Tilde.Atilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-- The corner elements match across the lowering arrow, inside `Ã`: `y_i^{(k)}d₋ = d₋y_i^{(k+1)}`.
`HJO.Dyck.Aq.yElt_mul_dMinus` read along `HJO.Dyck.toTilde`. -/
theorem yElt_mul_dMinus {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    yElt K q u k i * dMinus K q u k = dMinus K q u k * yElt K q u (k + 1) i := by
  have h := congrArg (HJO.Dyck.toTilde K q u) (Aq.yElt_mul_dMinus (K := K) (q := q) h1 hik)
  simpa only [map_mul, HJO.Dyck.toTilde_yElt, HJO.Dyck.toTilde_dMinus] using h

/-- The first Hecke commutation, inside `Ã`: `T_iy_i = y_{i+1}T_i + (1-q)y_i`. -/
theorem Tg_mul_yElt {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    Tg K q u k (i - 1) * yElt K q u k i
      = yElt K q u k (i + 1) * Tg K q u k (i - 1) + (1 - q) • yElt K q u k i := by
  have h := congrArg (HJO.Dyck.toTilde K q u) (Aq.Tg_mul_yElt (K := K) (q := q) h1 hik)
  simpa only [map_mul, map_add, map_smul, HJO.Dyck.toTilde_yElt, HJO.Dyck.toTilde_Tg] using h

/-- The second Hecke commutation, inside `Ã`: `T_iy_{i+1} = y_iT_i + (q-1)y_i`. -/
theorem Tg_mul_yElt_succ {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    Tg K q u k (i - 1) * yElt K q u k (i + 1)
      = yElt K q u k i * Tg K q u k (i - 1) + (q - 1) • yElt K q u k i := by
  have h := congrArg (HJO.Dyck.toTilde K q u) (Aq.Tg_mul_yElt_succ (K := K) (q := q) h1 hik)
  simpa only [map_mul, map_add, map_smul, HJO.Dyck.toTilde_yElt, HJO.Dyck.toTilde_Tg] using h

/-- A corner element commutes with every loop that does not touch it, inside `Ã`. -/
theorem yElt_mul_Tg_comm {k i s : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) (hs : s + 2 ≤ k)
    (hadm : s + 3 ≤ i ∨ i ≤ s) :
    yElt K q u k i * Tg K q u k s = Tg K q u k s * yElt K q u k i := by
  have h := congrArg (HJO.Dyck.toTilde K q u)
    (Aq.yElt_mul_Tg_comm (K := K) (q := q) h1 hik hs hadm)
  simpa only [map_mul, HJO.Dyck.toTilde_yElt, HJO.Dyck.toTilde_Tg] using h

/-! ### The starred relations, named -/

/-- The starred raising arrow shifts an inverse loop's index up by one:
`d₊^*T̂_i = T̂_{i+1}d₊^*`. -/
theorem dPlusStar_mul_Tinv {k i : ℕ} (h : i + 2 ≤ k) :
    dPlusStar K q u k * Tinv K q u k i = Tinv K q u (k + 1) (i + 1) * dPlusStar K q u k :=
  eq_of_sourceRelStar (SourceRel.up_braid (q := ⅟q) (E := e K q u) (U := dPlusStar K q u)
    (D := dMinus K q u) (T := Tinv K q u) h)

/-- The unstarred loop, as a `K`-combination of the inverse loop and the idempotent: the
polynomial inverse is an involution, so `T_i = q(T̂_i + (q^{-1}-1)e_k)`. -/
theorem Tg_eq_tinvOf_Tinv (k i : ℕ) :
    Tg K q u k i = q • (Tinv K q u k i + (⅟q - 1) • e K q u k) := by
  have h : tinvOf (⅟q) q (Tinv K q u k i) (e K q u k) = Tg K q u k i :=
    tinvOf_tinvOf (Tg K q u k i) (e K q u k)
  rw [← h, tinvOf]

/-- The starred commutator, as an inverse-loop word times `z_k`:
`d₊^*d₋ - d₋d₊^* = -(q-1)q^{-1}\,T̂_1 ⋯ T̂_{k-1}z_k` at the vertex `k`. This is
`HJO.Dyck.commOf_eq_smul_segUpOf_mul_cornerOf` at `HJO.Dyck.Tilde.Atilde.starFamily`, and it is the
statement usually written as `(q^{-1}-1)T_1^{-1} ⋯ T_{k-1}^{-1}z_k`. -/
theorem commOf_star_eq_smul_segUpOf_mul_zElt {k : ℕ} (hk : 1 ≤ k) :
    commOf (dPlusStar K q u) (dMinus K q u) (k - 1)
      = (⅟q - 1) • (segUpOf (e K q u) (Tinv K q u) k 0 (k - 1) * zElt K q u k k) := by
  refine commOf_eq_smul_segUpOf_mul_cornerOf starFamily ?_ hk
  have h : -(q * ⅟(q - 1)) * (⅟q - 1) = 1 := neg_mul_invOf_sub_one_mul
  rw [mul_comm]
  exact h


/-! ### The starred images of the corner calculus

Everything below is an unstarred identity of `Ã` with a star swap applied to it. The star swap is
taken as a hypothesis rather than constructed, so that the one place `HJO.Sym.paramInvLambda` is
needed is visible in every signature; `HJO.Dyck.Tilde.Atilde.exists_isStarSwap` produces one.
-/

section StarSwap

variable {bar : K ≃+* K} {σ : Atilde K q u →+ Atilde K q u}
  (h : IsStarSwap q bar (e K q u) (dPlus K q u) (dPlusStar K q u) (dMinus K q u) (Tg K q u) σ)
  (hbar : bar q = ⅟q)

include h hbar

/-- A star swap carries `y_i` to `z_i`, at `Ã`'s own generators. -/
theorem map_yElt {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    σ (yElt K q u k i) = zElt K q u k i := h.map_cornerOf hbar h1 hik

/-- A star swap carries `z_i` back to `y_i`. -/
theorem map_zElt {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    σ (zElt K q u k i) = yElt K q u k i := h.map_cornerOf_symm hbar h1 hik

omit hbar in
theorem map_Tinv {k i : ℕ} (hi : i + 2 ≤ k) : σ (Tinv K q u k i) = Tg K q u k i := by
  change σ (tinvOf q ⅟q (Tg K q u k i) (e K q u k)) = Tg K q u k i
  rw [← h.map_T hi, h.involutive]

/-- **The second move: `z` past a lowering arrow.** `z_i^{(k)}d₋ = d₋z_i^{(k+1)}`, a genuine
commutation with the subscript unchanged — the starred image of `HJO.Dyck.Aq.yElt_mul_dMinus`.

This is the one move of the direct argument for
`HJO.Dyck.Tilde.Atilde.dPlusStar_mul_mem_aqE0_sup_kernelIdealE0` at this step (for `G = d_-G'` one
has `z_kG = d_-z_kG'`) that is true as asserted. -/
theorem zElt_mul_dMinus {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    zElt K q u k i * dMinus K q u k = dMinus K q u k * zElt K q u (k + 1) i := by
  have hy := congrArg σ (yElt_mul_dMinus (K := K) (q := q) (u := u) h1 hik)
  rw [h.map_mul, h.map_mul, h.map_dMinus, map_yElt h hbar h1 hik,
    map_yElt h hbar h1 (by omega : i ≤ k + 1)] at hy
  exact hy

/-- The starred first Hecke commutation: `T̂_iz_i = z_{i+1}T̂_i + (q^{-1}-1)z_i`. -/
theorem Tinv_mul_zElt {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    Tinv K q u k (i - 1) * zElt K q u k i
      = zElt K q u k (i + 1) * Tinv K q u k (i - 1) + (1 - ⅟q) • zElt K q u k i := by
  have hy := congrArg σ (Tg_mul_yElt (K := K) (q := q) (u := u) h1 hik)
  rw [h.map_mul, map_add σ, h.map_mul, h.map_smul, h.map_T (by omega : i - 1 + 2 ≤ k),
    map_yElt h hbar h1 (by omega : i ≤ k), map_yElt h hbar (by omega : 1 ≤ i + 1)
      (by omega : i + 1 ≤ k), HJO.Dyck.bar_one_sub_of hbar] at hy
  exact hy

/-- The starred second Hecke commutation: `T̂_iz_{i+1} = z_iT̂_i + (1-q^{-1})z_i`. -/
theorem Tinv_mul_zElt_succ {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    Tinv K q u k (i - 1) * zElt K q u k (i + 1)
      = zElt K q u k i * Tinv K q u k (i - 1) + (⅟q - 1) • zElt K q u k i := by
  have hy := congrArg σ (Tg_mul_yElt_succ (K := K) (q := q) (u := u) h1 hik)
  rw [h.map_mul, map_add σ, h.map_mul, h.map_smul, h.map_T (by omega : i - 1 + 2 ≤ k),
    map_yElt h hbar h1 (by omega : i ≤ k), map_yElt h hbar (by omega : 1 ≤ i + 1)
      (by omega : i + 1 ≤ k), HJO.Dyck.bar_sub_one_of hbar] at hy
  exact hy

/-- The starred corner element commutes with every inverse loop that does not touch it. -/
theorem zElt_mul_Tinv_comm {k i s : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) (hs : s + 2 ≤ k)
    (hadm : s + 3 ≤ i ∨ i ≤ s) :
    zElt K q u k i * Tinv K q u k s = Tinv K q u k s * zElt K q u k i := by
  have hy := congrArg σ (yElt_mul_Tg_comm (K := K) (q := q) (u := u) h1 hik hs hadm)
  rw [h.map_mul, h.map_mul, h.map_T hs, map_yElt h hbar h1 hik] at hy
  exact hy

/-! ### `z` past a loop, as a span -/

omit h hbar in
/-- Where `z_iT_j` lands: the `K`-span of the starred corner elements at the vertex `k` and of the
loop `T_j` times them. -/
def zPastLoopSet (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (k s : ℕ) : Set (Atilde K q u) :=
  {x | ∃ i, 1 ≤ i ∧ i ≤ k ∧ (x = zElt K q u k i ∨ x = Tg K q u k s * zElt K q u k i)}

omit h hbar in
theorem zElt_mem_span_zPastLoopSet {k s i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    zElt K q u k i ∈ Submodule.span K (zPastLoopSet K q u k s) :=
  Submodule.subset_span ⟨i, h1, hik, Or.inl rfl⟩

omit h hbar in
theorem Tg_mul_zElt_mem_span_zPastLoopSet {k s i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    Tg K q u k s * zElt K q u k i ∈ Submodule.span K (zPastLoopSet K q u k s) :=
  Submodule.subset_span ⟨i, h1, hik, Or.inr rfl⟩

omit h hbar in
/-- An inverse loop times a starred corner element lands in the span, the inverse loop being a
combination of the loop and the idempotent. -/
theorem Tinv_mul_zElt_mem_span {k s i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    Tinv K q u k s * zElt K q u k i ∈ Submodule.span K (zPastLoopSet K q u k s) := by
  rw [Tinv_eq, smul_mul_assoc, add_mul, smul_mul_assoc, e_mul_zElt]
  exact Submodule.smul_mem _ _ (add_mem (Tg_mul_zElt_mem_span_zPastLoopSet h1 hik)
    (Submodule.smul_mem _ _ (zElt_mem_span_zPastLoopSet h1 hik)))

/-- **The first move: `z` past a loop.** For `1 ≤ i ≤ k`, `z_i^{(k)}T_j` is a `K`-linear
combination of the elements `T_jz_{i'}^{(k)}` and `z_{i'}^{(k)}` with `1 ≤ i' ≤ k`.

This is the weakest form the span route of
`HJO.Dyck.Tilde.Atilde.dPlusStar_mul_mem_aqE0_sup_kernelIdealE0` needs, and it is the weakest form
that is *true*: the direct argument asserts that the braid operators commute with the `z_j` up to
index shift, and a bare commutation is refuted by the adjacent cases, where
`HJO.Dyck.Tilde.Atilde.Tinv_mul_zElt` produces the neighbouring corner element together with the
scalar `1-q^{-1}`. Only three cases occur — `j` far from `i`, `j = i`, `j = i-1` — and the span
absorbs all three uniformly.

Note what is *not* claimed: no index shift. The unstarred analogue that is a genuine index shift is
`HJO.Dyck.Aq.Delta_mul_Tg`, about the commutator and not about a corner element. -/
theorem zElt_mul_Tg_mem_span {k i s : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    zElt K q u k i * Tg K q u k s ∈ Submodule.span K (zPastLoopSet K q u k s) := by
  rcases le_or_gt (s + 2) k with hs | hs
  · -- the loop exists; expand it in the inverse loop and the idempotent
    have hstep : zElt K q u k i * Tinv K q u k s
        ∈ Submodule.span K (zPastLoopSet K q u k s) := by
      rcases (by omega : (s + 3 ≤ i ∨ i ≤ s) ∨ i = s + 1 ∨ i = s + 2) with hc | hc | hc
      · rw [zElt_mul_Tinv_comm h hbar h1 hik hs hc]
        exact Tinv_mul_zElt_mem_span h1 hik
      · subst hc
        have key := Tinv_mul_zElt_succ h hbar (k := k) (i := s + 1) (by omega) (by omega)
        rw [Nat.add_sub_cancel] at key
        have heq : zElt K q u k (s + 1) * Tinv K q u k s
            = Tinv K q u k s * zElt K q u k (s + 1 + 1) - (⅟q - 1) • zElt K q u k (s + 1) := by
          rw [key]; abel
        rw [heq]
        exact sub_mem (Tinv_mul_zElt_mem_span (by omega) (by omega))
          (Submodule.smul_mem _ _ (zElt_mem_span_zPastLoopSet (by omega) (by omega)))
      · subst hc
        have key := Tinv_mul_zElt h hbar (k := k) (i := s + 1) (by omega) (by omega)
        rw [Nat.add_sub_cancel] at key
        have heq : zElt K q u k (s + 1 + 1) * Tinv K q u k s
            = Tinv K q u k s * zElt K q u k (s + 1) - (1 - ⅟q) • zElt K q u k (s + 1) := by
          rw [key]; abel
        rw [heq]
        exact sub_mem (Tinv_mul_zElt_mem_span (by omega) (by omega))
          (Submodule.smul_mem _ _ (zElt_mem_span_zPastLoopSet (by omega) (by omega)))
    rw [Tg_eq_tinvOf_Tinv, mul_smul_comm, mul_add, mul_smul_comm, zElt_mul_e]
    exact Submodule.smul_mem _ _ (add_mem hstep
      (Submodule.smul_mem _ _ (zElt_mem_span_zPastLoopSet h1 hik)))
  · rw [Tg_eq_zero (by omega), mul_zero]
    exact zero_mem _

end StarSwap

end Tilde.Atilde

end HJO.Dyck
