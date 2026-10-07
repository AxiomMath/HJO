/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.StarSwapExists
public meta import HJO.Attr

/-! # A star swap of the extended Dyck path algebra exists

`HJO.Dyck.Tilde.Atilde.exists_isStarSwap`: `Ã` of `HJO.Dyck.Tilde.Atilde` admits a star swap of
`HJO.Dyck.IsStarSwap`.

## The proof route, and why it is not the two-step one

The natural proof has two steps: `HJO.Dyck.TwoSided.Bq.exists_algEquiv_quotient_mixedIdeal`
identifies `Ã` with `𝔹/J`, and `HJO.Dyck.TwoSided.Bq.IsStarSwap.mem_mixedIdeal` says the star swap
of `𝔹` produced by `HJO.Dyck.TwoSided.exists_isStarSwap` preserves `J`, so it descends.

Here the same map is descended in **one** step instead, to `Ã` directly. `Ã` and `𝔹` are quotients
of the *same* free algebra `FreeAlgebra K HJO.Dyck.Tilde.Gen` by relation lists differing only in
the three mixed relations, and `HJO.Dyck.starSwapFree` — the conjugate-linear multiplicative map of
that free algebra — respects those three as well:

* the first mixed relation `z_{i+1}d₊ = d₊z_i` goes to the second, `y_{i+1}d₊^* = d₊^*y_i`;
* the second goes to the first;
* the third, `z_1d₊ + uq^{k+1}y_1d₊^* = 0`, goes to `u^{-1}q^{-(k+1)}` times itself.

The only new input is that `σ_P` exchanges the two *free* corner elements
`HJO.Dyck.Tilde.freeY` and `HJO.Dyck.Tilde.freeZ`, and that is
`HJO.Dyck.map_cornerOf_bar` with the three scalars barred — the same transport that gives
`HJO.Dyck.IsStarSwap.map_cornerOf` in a quotient. So this file does not need the two-step
isomorphism, and the statement proved is the same.

`HJO.Dyck.TwoSided.Bq.IsStarSwap.mem_mixedIdeal` and `HJO.Dyck.TwoSided.Bq.mixedIdeal` are proved
separately, in `HJO.CarlssonMellit.MixedIdeal`: they are results in their own right and the route
through them remains available; they are just not what this proof spends.

## The hypotheses

`bar q = q⁻¹`, `bar u = u⁻¹` and `bar (bar c) = c` — the content of `HJO.Sym.paramInvLambda` —
together with `[Invertible u]`, which is where `u ≠ 0` enters: the third mixed relation is sent to a
scalar multiple of itself by `u^{-1}q^{-(k+1)}`, and that scalar has to exist.

## Main definitions

* `HJO.Dyck.Tilde.Atilde.starSwapAtilde`: the induced map on `Ã`.

## Main results

* `HJO.Dyck.Tilde.Atilde.isStarSwap_starSwapAtilde` and
  `HJO.Dyck.Tilde.Atilde.exists_isStarSwap`: the induced map is a star swap, so `Ã` admits one.

## References

Transcribing E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math.
Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck

/-! ### The bar of the starred prefactor -/

section Bar

variable {K : Type*} [CommRing K] (bar : K ≃+* K) {q : K} [Invertible q] [Invertible (q - 1)]

/-- **The bar of the prefactor of `z_k` is the prefactor of `y_k`**: `-(q(q-1)⁻¹)` goes back to
`(q-1)⁻¹`. With `HJO.Dyck.bar_invOf_sub_one` this is the statement that the bar is an involution on
the third scalar of `HJO.Dyck.cornerOf`, and it turns the free `z` back into the free `y`. -/
theorem bar_neg_mul_invOf_sub_one (hbar : bar q = ⅟q) : bar (-(q * ⅟(q - 1))) = ⅟(q - 1) := by
  rw [map_neg, map_mul, hbar, bar_invOf_sub_one bar hbar, mul_neg, neg_neg,
    show ⅟q * (q * ⅟(q - 1)) = ⅟q * q * ⅟(q - 1) from by ring, invOf_mul_self, one_mul]

end Bar

/-! ### The free corner elements are exchanged -/

namespace Tilde

variable {K : Type*} [CommRing K] {q : K} [Invertible q] [Invertible (q - 1)] {bar : K ≃+* K}
variable (hbar : bar q = ⅟q)

include hbar

/-- **`σ_P` carries the free corner element `y_i` to the free `z_i`.** This is
`HJO.Dyck.map_cornerOf_bar` at the free algebra: the three scalars `q`, `q⁻¹`, `(q-1)⁻¹` are barred
to `q⁻¹`, `q`, `-(q(q-1)⁻¹)`, the raising arrow is exchanged, and each loop goes to its polynomial
inverse. The range `1 ≤ i ≤ k` is what keeps every loop the formula reads a loop the quiver has. -/
theorem starSwapFree_freeY {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    starSwapFree K q bar (freeY K q k i) = freeZ K q k i := by
  have hmain := map_cornerOf_bar (bar := bar) (f := starSwapFreeAdd K q bar)
    (E' := freeE K) (U' := freeUpStar K) (D' := freeDown K) (T' := freeTinv K q)
    (fun x y => map_mul (starSwapFree K q bar) x y) starSwapFree_smul q ⅟q ⅟(q - 1)
    (fun _ => starSwapFree_freeE _) (fun _ => starSwapFree_freeUp _)
    (fun _ => starSwapFree_freeDown _) (fun j hj => starSwapFree_freeT_of_le hj) hi hik
  rw [starSwapFreeAdd_apply] at hmain
  rw [freeY, hmain, hbar, bar_invOf bar hbar, bar_invOf_sub_one bar hbar, freeZ]

/-- **`σ_P` carries the free corner element `z_i` back to the free `y_i`.** The same transport in
the other direction: the loops go back by `HJO.Dyck.starSwapFree_freeTinv_of_le`, and the third
scalar by `HJO.Dyck.bar_neg_mul_invOf_sub_one`. -/
theorem starSwapFree_freeZ {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    starSwapFree K q bar (freeZ K q k i) = freeY K q k i := by
  have hmain := map_cornerOf_bar (bar := bar) (f := starSwapFreeAdd K q bar)
    (E' := freeE K) (U' := freeUp K) (D' := freeDown K) (T' := freeT K)
    (fun x y => map_mul (starSwapFree K q bar) x y) starSwapFree_smul
    (⅟q) q (-(q * ⅟(q - 1))) (fun _ => starSwapFree_freeE _)
    (fun _ => starSwapFree_freeUpStar _) (fun _ => starSwapFree_freeDown _)
    (fun j hj => starSwapFree_freeTinv_of_le hbar hj) hi hik
  rw [starSwapFreeAdd_apply] at hmain
  rw [freeZ, hmain, bar_invOf bar hbar, hbar, bar_neg_mul_invOf_sub_one bar hbar, freeY]

end Tilde

/-! ### The induced map on `Ã` -/

namespace Tilde.Atilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

theorem mk_eq_mkRingHom (x : FreeAlgebra K Tilde.Gen) :
    mk K q u x = RingQuot.mkRingHom (Rel K q u) x := by
  rw [← RingQuot.mkAlgHom_coe K (Rel K q u)]
  rfl

/-- The map of `HJO.Dyck.starSwapFree` followed by the quotient map onto `Ã`, bundled as an
additive map: the shape `HJO.Dyck.SourceRel.mapBar` reads. -/
noncomputable def mkStarSwap (K : Type*) [CommRing K] (q u : K) [Invertible q]
    [Invertible (q - 1)] (bar : K ≃+* K) : FreeAlgebra K Tilde.Gen →+ Atilde K q u :=
  ((mk K q u).toRingHom.comp (starSwapFree K q bar)).toAddMonoidHom

variable {bar : K ≃+* K}

theorem mkStarSwap_apply (x : FreeAlgebra K Tilde.Gen) :
    mkStarSwap K q u bar x = mk K q u (starSwapFree K q bar x) := rfl

theorem mkStarSwap_mul (x y : FreeAlgebra K Tilde.Gen) :
    mkStarSwap K q u bar (x * y) = mkStarSwap K q u bar x * mkStarSwap K q u bar y := by
  rw [mkStarSwap_apply, mkStarSwap_apply, mkStarSwap_apply, map_mul, map_mul]

theorem mkStarSwap_smul (c : K) (x : FreeAlgebra K Tilde.Gen) :
    mkStarSwap K q u bar (c • x) = bar c • mkStarSwap K q u bar x := by
  rw [mkStarSwap_apply, mkStarSwap_apply, starSwapFree_smul, map_smul]

variable [Invertible u] (hbar : bar q = ⅟q) (hbaru : bar u = ⅟u)

include hbar hbaru

/-- **The map respects the relations of `Ã`.** The quiver's own relations and the two groups
`source` and `sourceStar` go exactly as they do for `𝔹`; the three mixed relations of
`HJO.Dyck.Tilde.Atilde` are the new cases, and they are permuted among themselves — the first to the
second, the second to the first, and the third to `u^{-1}q^{-(k+1)}` times itself. -/
theorem mk_starSwapFree_rel {x y : FreeAlgebra K Tilde.Gen} (h : Rel K q u x y) :
    mk K q u (starSwapFree K q bar x) = mk K q u (starSwapFree K q bar y) := by
  induction h with
  | vertex_mul_self k =>
    simp only [map_mul, starSwapFree_freeE, mk_freeE]
    exact e_mul_self k
  | vertex_mul_vertex h =>
    simp only [map_mul, starSwapFree_freeE, mk_freeE, map_zero]
    exact e_mul_e_of_ne h
  | vertex_mul_down k =>
    simp only [map_mul, starSwapFree_freeE, starSwapFree_freeDown, mk_freeE, mk_freeDown]
    exact e_mul_dMinus k
  | down_mul_vertex k =>
    simp only [map_mul, starSwapFree_freeE, starSwapFree_freeDown, mk_freeE, mk_freeDown]
    exact dMinus_mul_e k
  | vertex_mul_braid k i =>
    rcases le_or_gt (i + 2) k with hk | hk
    · simp only [map_mul, starSwapFree_freeE, starSwapFree_freeT_of_le hk, mk_freeE, mk_freeTinv]
      exact e_mul_Tinv k i
    · simp only [map_mul, starSwapFree_freeE, starSwapFree_freeT_of_lt (by omega : k ≤ i + 1),
        mul_zero, map_zero]
  | braid_mul_vertex k i =>
    rcases le_or_gt (i + 2) k with hk | hk
    · simp only [map_mul, starSwapFree_freeE, starSwapFree_freeT_of_le hk, mk_freeE, mk_freeTinv]
      exact Tinv_mul_e k i
    · simp only [map_mul, starSwapFree_freeE, starSwapFree_freeT_of_lt (by omega : k ≤ i + 1),
        zero_mul, map_zero]
  | braid_eq_zero h => simp only [starSwapFree_freeT_of_lt h, map_zero]
  | source h =>
    refine eq_of_sourceRelStar ?_
    have hmain := SourceRel.mapBar (bar := bar) (f := mkStarSwap K q u bar) (E' := e K q u)
      (U' := dPlusStar K q u) (D' := dMinus K q u) (T' := Tinv K q u) mkStarSwap_mul
      mkStarSwap_smul (fun n => by rw [mkStarSwap_apply, starSwapFree_freeE]; rfl)
      (fun n => by rw [mkStarSwap_apply, starSwapFree_freeUp]; rfl)
      (fun n => by rw [mkStarSwap_apply, starSwapFree_freeDown]; rfl)
      (fun n i hni => by
        rw [mkStarSwap_apply, starSwapFree_freeT_of_le hni]; exact mk_freeTinv n i) h
    rwa [hbar] at hmain
  | sourceStar h =>
    refine eq_of_sourceRel ?_
    have hmain := SourceRel.mapBar (bar := bar) (f := mkStarSwap K q u bar) (E' := e K q u)
      (U' := dPlus K q u) (D' := dMinus K q u) (T' := Tg K q u) mkStarSwap_mul
      mkStarSwap_smul (fun n => by rw [mkStarSwap_apply, starSwapFree_freeE]; rfl)
      (fun n => by rw [mkStarSwap_apply, starSwapFree_freeUpStar]; rfl)
      (fun n => by rw [mkStarSwap_apply, starSwapFree_freeDown]; rfl)
      (fun n i hni => by
        rw [mkStarSwap_apply, starSwapFree_freeTinv_of_le hbar hni]; rfl) h
    rwa [bar_invOf bar hbar] at hmain
  | @mixed_z k i h1 h2 =>
    simp only [map_mul, starSwapFree_freeUp,
      starSwapFree_freeZ hbar (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ k + 1),
      starSwapFree_freeZ hbar h1 h2, mk_freeY, mk_freeUpStar]
    exact mixed_y h1 h2
  | @mixed_y k i h1 h2 =>
    simp only [map_mul, starSwapFree_freeUpStar,
      starSwapFree_freeY hbar (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ k + 1),
      starSwapFree_freeY hbar h1 h2, mk_freeZ, mk_freeUp]
    exact mixed_z h1 h2
  | mixed_top k =>
    have hone : ⅟u * ⅟q ^ (k + 1) * (u * q ^ (k + 1)) = 1 := by
      rw [show ⅟u * ⅟q ^ (k + 1) * (u * q ^ (k + 1))
        = ⅟u * u * (⅟q ^ (k + 1) * q ^ (k + 1)) from by ring, invOf_mul_self,
        ← mul_pow, invOf_mul_self, one_pow, mul_one]
    have hZ : zElt K q u (k + 1) 1 * dPlus K q u k
        = -((u * q ^ (k + 1)) • (yElt K q u (k + 1) 1 * dPlusStar K q u k)) := by
      rw [eq_neg_iff_add_eq_zero]
      exact mixed_top k
    simp only [map_mul, map_smul, starSwapFree_smul, starSwapFree_freeUp,
      starSwapFree_freeUpStar, starSwapFree_freeY hbar le_rfl (by omega : 1 ≤ k + 1),
      starSwapFree_freeZ hbar le_rfl (by omega : 1 ≤ k + 1), mk_freeY, mk_freeZ, mk_freeUp,
      mk_freeUpStar, map_neg, map_mul, map_pow, hbar, hbaru]
    rw [hZ, neg_smul_neg, smul_smul, hone, one_smul]

/-- **The star swap of `Ã`**: the map of `HJO.Dyck.starSwapFree` descended to the quotient. -/
noncomputable def starSwapAtilde : Atilde K q u →+* Atilde K q u :=
  RingQuot.lift ⟨(RingQuot.mkRingHom (Rel K q u)).comp (starSwapFree K q bar), fun _ _ h => by
    simp only [RingHom.comp_apply, ← mk_eq_mkRingHom]
    exact mk_starSwapFree_rel hbar hbaru h⟩

theorem starSwapAtilde_mk (x : FreeAlgebra K Tilde.Gen) :
    starSwapAtilde hbar hbaru (mk K q u x) = mk K q u (starSwapFree K q bar x) := by
  rw [mk_eq_mkRingHom, starSwapAtilde, RingQuot.lift_mkRingHom_apply, RingHom.comp_apply,
    ← mk_eq_mkRingHom]

variable (hbb : ∀ c : K, bar (bar c) = c)

include hbb

omit [Invertible u] hbaru in
/-- **The descended map is an involution**, by the same argument as for `𝔹`: on the free algebra it
is not, a loop the quiver does not have going to `0` and back to `0`; in `Ã` that loop is itself `0`
by `HJO.Dyck.Tilde.Atilde.Tg_eq_zero`. -/
theorem mk_starSwapFree_starSwapFree (x : FreeAlgebra K Tilde.Gen) :
    mk K q u (starSwapFree K q bar (starSwapFree K q bar x)) = mk K q u x := by
  induction x with
  | grade0 c => rw [starSwapFree_algebraMap, starSwapFree_algebraMap, hbb]
  | grade1 g =>
    match g with
    | .vertex k => rw [starSwapFree_freeE, starSwapFree_freeE]
    | .up k => rw [starSwapFree_freeUp, starSwapFree_freeUpStar]
    | .upStar k => rw [starSwapFree_freeUpStar, starSwapFree_freeUp]
    | .down k => rw [starSwapFree_freeDown, starSwapFree_freeDown]
    | .braid k i =>
      rcases le_or_gt (i + 2) k with hk | hk
      · rw [starSwapFree_freeT_of_le hk, starSwapFree_freeTinv_of_le hbar hk]
      · simp only [starSwapFree_freeT_of_lt (by omega : k ≤ i + 1), map_zero]
        exact (Tg_eq_zero (by omega : k ≤ i + 1)).symm
  | mul a b iha ihb => rw [map_mul, map_mul, map_mul, iha, ihb, map_mul]
  | add a b iha ihb => rw [map_add, map_add, map_add, iha, ihb, map_add]

/-- **`HJO.Dyck.Tilde.Atilde.exists_isStarSwap`: the map is a star swap of `Ã`.** -/
theorem isStarSwap_starSwapAtilde :
    IsStarSwap q bar (e K q u) (dPlus K q u) (dPlusStar K q u) (dMinus K q u) (Tg K q u)
      (starSwapAtilde hbar hbaru).toAddMonoidHom where
  map_smul c x := by
    change starSwapAtilde hbar hbaru (c • x) = bar c • starSwapAtilde hbar hbaru x
    obtain ⟨w, rfl⟩ := RingQuot.mkRingHom_surjective (Rel K q u) x
    rw [← mk_eq_mkRingHom, ← map_smul (mk K q u), starSwapAtilde_mk, starSwapAtilde_mk,
      starSwapFree_smul, map_smul]
  map_mul x y := by
    change starSwapAtilde hbar hbaru (x * y)
      = starSwapAtilde hbar hbaru x * starSwapAtilde hbar hbaru y
    exact map_mul _ x y
  involutive x := by
    change starSwapAtilde hbar hbaru (starSwapAtilde hbar hbaru x) = x
    obtain ⟨w, rfl⟩ := RingQuot.mkRingHom_surjective (Rel K q u) x
    rw [← mk_eq_mkRingHom, starSwapAtilde_mk, starSwapAtilde_mk]
    exact mk_starSwapFree_starSwapFree hbar hbb w
  map_e k := by
    change starSwapAtilde hbar hbaru (e K q u k) = e K q u k
    rw [show e K q u k = mk K q u (Tilde.freeE K k) from rfl, starSwapAtilde_mk,
      starSwapFree_freeE]
  map_dMinus k := by
    change starSwapAtilde hbar hbaru (dMinus K q u k) = dMinus K q u k
    rw [show dMinus K q u k = mk K q u (Tilde.freeDown K k) from rfl, starSwapAtilde_mk,
      starSwapFree_freeDown]
  map_dPlus k := by
    change starSwapAtilde hbar hbaru (dPlus K q u k) = dPlusStar K q u k
    rw [show dPlus K q u k = mk K q u (Tilde.freeUp K k) from rfl, starSwapAtilde_mk,
      starSwapFree_freeUp, mk_freeUpStar]
  map_dPlusStar k := by
    change starSwapAtilde hbar hbaru (dPlusStar K q u k) = dPlus K q u k
    rw [show dPlusStar K q u k = mk K q u (Tilde.freeUpStar K k) from rfl, starSwapAtilde_mk,
      starSwapFree_freeUpStar, mk_freeUp]
  map_T {k i} h := by
    change starSwapAtilde hbar hbaru (Tg K q u k i) = tinvOf q ⅟q (Tg K q u k i) (e K q u k)
    rw [show Tg K q u k i = mk K q u (Tilde.freeT K k i) from rfl, starSwapAtilde_mk,
      starSwapFree_freeT_of_le h]
    exact mk_freeTinv k i

/-- **`HJO.Dyck.Tilde.Atilde.exists_isStarSwap`: `Ã` admits a star swap.** The three hypotheses on
the bar are the content of `HJO.Sym.paramInvLambda` — it inverts `q` and `u` and is an involution —
and `[Invertible u]` is `u ≠ 0`, which the third mixed relation needs. -/
@[hjo "lem_cm_star_flip_exists"]
theorem exists_isStarSwap :
    ∃ σ : Atilde K q u →+ Atilde K q u,
      IsStarSwap q bar (e K q u) (dPlus K q u) (dPlusStar K q u) (dMinus K q u) (Tg K q u) σ :=
  ⟨_, isStarSwap_starSwapAtilde hbar hbaru hbb⟩

end Tilde.Atilde

end HJO.Dyck
