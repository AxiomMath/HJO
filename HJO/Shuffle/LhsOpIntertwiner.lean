/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitNablaPrime
public import HJO.CMStructure.StandingStructure

/-! # Mellit's `∇'` on every graded piece

Mellit's proof that conjugation by `∇` realises the shear `N = (1 1; 0 1)` (§3.7 of *Toric braids
and (m,n)-parking functions*) runs through the operator `∇'` that the endomorphism `N` of `Ã`
induces on `V_* = ⨁_k V_k ≅ Ã𝟏_0/𝓘`, with `∇'L = N(L)∇'`. `N` fixes the idempotents, the loops
`T_i`, `d_-` and `d_+^*`, and sends `d_+ ↦ (qu)^{-1}z_1d_+`; hence `y_1 ↦ (qu)^{-1}z_1y_1` at every
vertex. Read on the summand `V_k`, `∇'` is an endomorphism `𝒩_k` of `V_k`, and the family
`(𝒩_k)_k` satisfies, between the pieces each arrow joins,

* `𝒩_k d_- = d_- 𝒩_{k+1}`, `𝒩_{k+1} d_+^* = d_+^* 𝒩_k`, `𝒩_k T_i = T_i 𝒩_k`;
* `𝒩_k (y_1 F) = (qu)^{-1} z_1 (y_1 𝒩_k F)` and `𝒩_{k+1} (d_+ F) = (qu)^{-1} z_1 (d_+ 𝒩_k F)`;
* on `V_0 = Λ` it is `∇`.

This is `HJO.Sweep.IsNablaPrime`. Its consequences used by the slope recursion are proved from
these clauses alone: `𝒩_k` commutes with the inverse loops, with every train, and with
`z_1 = q^k/(1-q)(d_+^*d_- - d_-d_+^*)T^*_{k↘1}`; it carries the letter `𝗒` of a slope word to `𝗒𝗓`
(read in the order the letters act) and fixes `𝗓`; and so it shears the slope operator,
`𝒩_k Ξ_{m,n}(-y_1F) = Ξ_{m+n,n}(-y_1 𝒩_k F)`.

Existence: from the structure theorem and Mellit's `N` (`HJO.Sweep.exists_intertwiner`,
`HJO.Dyck.Tilde.Atilde.conjTwist_mem_mellitKernel`), any intertwiner of `N` gives such a family
over its own restriction to `V_0`; that restriction fixes `1`, commutes with `D_0` and turns `e_1·`
into `-D_1`, so it is every Macdonald conjugator normalised by `∇1 = 1`
(`HJO.Sym.eq_of_slope_clauses`).

## Main definitions

* `HJO.Sweep.IsNablaPrime`: a family of endomorphisms of the total space realising Mellit's `N`
  piece by piece over a given `∇`.
* `HJO.Sweep.sweepLetterAt`, `HJO.Sweep.sweepWordAt`: the letters of a slope word acting on `V_k`,
  and a word read in the order its letters act.

## Main results

* `HJO.Sweep.map_zElt_one_ofPiece`: `z_1 ∈ Ã` acts on `V_k` as `HJO.Sweep.zopOneStar`.
* `HJO.Sweep.isNablaPrime_of_intertwiner`: an intertwiner of `N` read on the pieces.
* `HJO.Sweep.exists_isNablaPrime_of_bar`: the family exists over every `∇` meeting the two slope
  clauses with `∇1 = 1`, given the involution of `HJO.Sym.paramInvLambda`.
* `HJO.Sweep.exists_isNablaPrime_param`: the same at the standing field, over a Macdonald
  conjugator with `∇1 = 1`.
* `HJO.Sweep.IsNablaPrime.map_zopOneStar`, `HJO.Sweep.IsNablaPrime.map_trainUpEnd`,
  `HJO.Sweep.IsNablaPrime.map_trainDownEnd`: commutation with `z_1` and with the trains.
* `HJO.Sweep.IsNablaPrime.map_slopeOperator_neg_auxVar_mul`: the shear of the slope operator.

## Implementation notes

The scalar at `d_+` is `(qu)^{-1}` and not Mellit's `-(qt)^{-1}`, as in
`HJO.Sweep.exists_isNOperatorOnPieces_of_bar`: Mellit's `∇` carries the sign `(-1)^{|λ|}` that
`HJO.Sym.IsMacdonaldConjugator` does not.

The family is indexed by the piece and acts on the whole total space (through the retraction onto
`V_k`); only its values on `V_k` are read. The pieces are nested in the total space, so a single
operator cannot serve for all of them (`HJO.Sweep.not_exists_isNOperator`).

## References

* [A. Mellit, *Toric braids and (m,n)-parking functions*][mellit2016], §3.6–3.7.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial Dyck.Tilde

open Mellit (SlopeLetter)

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The hypothesis -/

/-- **Mellit's `∇'` read on every graded piece**, over a given `∇`: endomorphisms `N k` of the
total space, of which only the restriction to `V_k` is read, preserving `V_k`, equal to `∇` on
`V_0 = Λ`, commuting with `d_-`, `d^*_+` and the loops between the pieces they join, and carrying
`y_1·` and `d_+` to `(qu)^{-1}z_1y_1·` and `(qu)^{-1}z_1d_+`. -/
structure IsNablaPrime (q u : L) (nabla : Module.End L (Sym.Lambda L))
    (N : ℕ → Module.End L (Total L)) : Prop where
  /-- `N k` preserves `V_k`. -/
  mem_piece : ∀ (k : ℕ) {F : Total L}, F ∈ piece L k → N k F ∈ piece L k
  /-- On `V_0` it is `∇`. -/
  map_C : ∀ f : Sym.Lambda L, N 0 (C f) = C (nabla f)
  /-- `N_k d_- = d_- N_{k+1}` out of `V_{k+1}`. -/
  map_dminus : ∀ (k : ℕ) {F : Total L}, F ∈ piece L (k + 1) →
    N k (dminus q (k + 1) F) = dminus q (k + 1) (N (k + 1) F)
  /-- `N_{k+1} d^*_+ = d^*_+ N_k` out of `V_k`. -/
  map_dplusStar : ∀ (k : ℕ) {F : Total L}, F ∈ piece L k →
    N (k + 1) (dplusStar q u k F) = dplusStar q u k (N k F)
  /-- `N_k T_i = T_i N_k` on `V_k`, `1 ≤ i < k`. -/
  map_braid : ∀ {k i : ℕ}, 1 ≤ i → i < k → ∀ {F : Total L}, F ∈ piece L k →
    N k (braidEnd q i F) = braidEnd q i (N k F)
  /-- `N_k y_1 = (qu)^{-1}z_1y_1N_k` on `V_k`, `k ≥ 1`. -/
  map_auxVar_mul : ∀ {k : ℕ}, 1 ≤ k → ∀ {F : Total L}, F ∈ piece L k →
    N k ((auxVar 1 : Total L) * F)
      = (q * u)⁻¹ • zopOneStar q u k ((auxVar 1 : Total L) * N k F)
  /-- `N_{k+1} d_+ = (qu)^{-1}z_1d_+N_k` out of `V_k`. -/
  map_dplus : ∀ (k : ℕ) {F : Total L}, F ∈ piece L k →
    N (k + 1) (dplus q k F) = (q * u)⁻¹ • zopOneStar q u (k + 1) (dplus q k (N k F))

/-! ### The action of `z_1` on every piece -/

section ZOne

variable {q u : L} [Invertible q] [Invertible (q - 1)]

/-- The additive group of `V_*`, supplied explicitly: instance search does not find it through
the summands here. -/
noncomputable local instance : AddCommGroup (Vstar L) :=
  @DirectSum.instAddCommGroup ℕ (fun k => pieceSub L k) (fun _ => Submodule.addCommGroup _)

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- `T^*_{a↘1}` is the descending word of the inverse letters. -/
theorem trainUpEnd_one_right {a : ℕ} (ha : 1 ≤ a) :
    trainUpEnd q a 1 = Braid.descendingWord (braidInvEnd q) a 1 := by
  rw [trainUpEnd, Braid.trainUp]
  split_ifs with h
  · obtain rfl : a = 1 := by omega
    simp [Braid.ascendingWord, Braid.descendingWord]
  · rfl

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- `T^*_{n+2↘1} = T^{-1}_{n+1} T^*_{n+1↘1}`. -/
theorem trainUpEnd_succ_one (n : ℕ) :
    trainUpEnd q (n + 2) 1 = braidInvEnd q (n + 1) * trainUpEnd q (n + 1) 1 := by
  rw [trainUpEnd_one_right (by omega), trainUpEnd_one_right (by omega),
    ← Braid.descendingWord_succ_self (braidInvEnd q) (n + 1),
    Braid.descendingWord_mul _ (by omega) (by omega)]

variable {ρ : Atilde L q u →ₐ[L] Module.End L (Vstar L)}
  (hρe : ∀ k : ℕ, ρ (Atilde.e L q u k) = pieceProj L k)
  (hρT : ∀ k i : ℕ, ρ (Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
  (hρD : ∀ k : ℕ, ρ (Atilde.dMinus L q u k) = lowerVstar (dminusModPiece q) k)
  (hρS : ∀ k : ℕ, ρ (Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)

include hρe hρT in
omit [Algebra ℚ L] in
/-- The polynomial inverse of a loop acts on `V_k` as the inverse braid operator. -/
theorem map_Tinv_ofPiece_atilde {k i : ℕ} (h : i + 2 ≤ k) (G X : pieceSub L k)
    (hX : (X : Total L) = braidInv q (i + 1) G) :
    ρ (Atilde.Tinv L q u k i) (ofPiece L k G) = ofPiece L k X := by
  rw [Atilde.Tinv, Dyck.tinvOf, map_smul, map_add, map_smul, hρT, hρe, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, loopVstar_ofPiece, pieceProj_ofPiece, ← map_smul,
    ← map_add, ← map_smul]
  refine congrArg (ofPiece L k) (Subtype.ext ?_)
  rw [hX, braidInv_apply, SetLike.val_smul, Submodule.coe_add, SetLike.val_smul,
    coe_braidModPiece q h, scal_eq_algebraMap, scal_eq_algebraMap, ← Algebra.smul_def,
    ← Algebra.smul_def, invOf_eq_inv]

include hρe hρT in
omit [Algebra ℚ L] in
/-- The descending word of polynomial inverses acts on `V_k` as the train `T^*_{n+1↘1}`. -/
theorem map_segOf_Tinv_ofPiece {k : ℕ} :
    ∀ n : ℕ, n + 1 ≤ k → ∀ G X : pieceSub L k, (X : Total L) = trainUpEnd q (n + 1) 1 G →
      ρ (Dyck.segOf (Atilde.e L q u) (Atilde.Tinv L q u) k 0 n) (ofPiece L k G)
        = ofPiece L k X := by
  intro n
  induction n with
  | zero =>
    intro _ G X hX
    rw [Dyck.segOf_zero, hρe, pieceProj_ofPiece]
    refine congrArg (ofPiece L k) (Subtype.ext ?_)
    rw [hX, trainUpEnd, Braid.trainUp_self]
    rfl
  | succ n ih =>
    intro hn G X hX
    have hmem : trainUpEnd q (n + 1) 1 (G : Total L) ∈ pieceSub L k :=
      trainUpEnd_mem_piece q (by omega) (by omega) G.2
    rw [Dyck.segOf_succ, map_mul, Module.End.mul_apply, ih (by omega) G ⟨_, hmem⟩ rfl, zero_add]
    refine map_Tinv_ofPiece_atilde hρe hρT (by omega) _ X ?_
    rw [hX, trainUpEnd_succ_one, Module.End.mul_apply]
    rfl

include hρD hρS in
/-- The starred commutator `d^*_+d_- - d_-d^*_+` at the vertex `m + 1`. -/
theorem map_commOf_star_ofPiece (m : ℕ) (G : pieceSub L (m + 1)) :
    ρ (Dyck.commOf (Atilde.dPlusStar L q u) (Atilde.dMinus L q u) m) (ofPiece L (m + 1) G)
      = ofPiece L (m + 1) (dplusStarPiece q u m (dminusModPiece q m G)
          - dminusModPiece q (m + 1) (dplusStarPiece q u (m + 1) G)) := by
  rw [Dyck.commOf, map_sub, map_mul, map_mul, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, hρD, hρS, lowerVstar_ofPiece, raiseVstar_ofPiece, hρS, hρD,
    raiseVstar_ofPiece, lowerVstar_ofPiece, map_sub]

include hρe hρT hρD hρS in
/-- **`z_1` acts on `V_k` as `HJO.Sweep.zopOneStar`**, at every `k ≥ 1`: the closed form
`z_1𝟏_k = q^k(1-q)^{-1}(d_+^*d_- - d_-d_+^*)T^*_{k↘1}𝟏_k`
(`HJO.Dyck.Tilde.Atilde.zElt_one_eq_wordDownStar`) read through the action. -/
theorem map_zElt_one_ofPiece {k : ℕ} (hk : 1 ≤ k) (G X : pieceSub L k)
    (hX : (X : Total L) = zopOneStar q u k G) :
    ρ (Atilde.zElt L q u k 1) (ofPiece L k G) = ofPiece L k X := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hmem : trainUpEnd q (m + 1) 1 (G : Total L) ∈ pieceSub L (m + 1) :=
    trainUpEnd_mem_piece q (by omega) (by omega) G.2
  rw [Atilde.zElt_one_eq_wordDownStar hk, Atilde.tcval_wordDownStar m le_rfl, map_smul, map_mul,
    LinearMap.smul_apply, Module.End.mul_apply,
    map_segOf_Tinv_ofPiece hρe hρT m le_rfl G ⟨_, hmem⟩ rfl, Nat.add_sub_cancel,
    map_commOf_star_ofPiece hρD hρS,
    ← map_smul]
  refine congrArg (ofPiece L (m + 1)) (Subtype.ext ?_)
  have hq1 : (q - 1 : L) ≠ 0 := Invertible.ne_zero _
  have hc : (-(q ^ (m + 1) * ⅟(q - 1)) : L) = q ^ (m + 1) / (1 - q) := by
    rw [invOf_eq_inv, div_eq_mul_inv, ← neg_sub q 1, inv_neg]; ring
  rw [hX, zopOneStar, hc, Nat.add_sub_cancel]
  rfl

variable (hρU : ∀ k : ℕ, ρ (Atilde.dPlus L q u k) = raiseVstar (dplusModPiece q) k)
  {Φ : Atilde L q u →ₐ[L] Atilde L q u}
  (hΦe : ∀ k : ℕ, Φ (Atilde.e L q u k) = Atilde.e L q u k)
  (hΦT : ∀ k i : ℕ, Φ (Atilde.Tg L q u k i) = Atilde.Tg L q u k i)
  (hΦD : ∀ k : ℕ, Φ (Atilde.dMinus L q u k) = Atilde.dMinus L q u k)
  (hΦS : ∀ k : ℕ, Φ (Atilde.dPlusStar L q u k) = Atilde.dPlusStar L q u k)
  (hΦU : ∀ k : ℕ, Φ (Atilde.dPlus L q u k)
    = (q * u)⁻¹ • (Atilde.zElt L q u (k + 1) 1 * Atilde.dPlus L q u k))
  (hΦy : ∀ k : ℕ, 1 ≤ k → Φ (Atilde.yElt L q u k 1)
    = (q * u)⁻¹ • (Atilde.zElt L q u k 1 * Atilde.yElt L q u k 1))
  {Nv : Module.End L (Vstar L)}
  (hNv : ∀ (a : Atilde L q u) (v : Vstar L), Nv (ρ a v) = ρ (Φ a) (Nv v))

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
/-- A vector read on a piece stays in the piece. -/
theorem nvTotal_mem_piece (Nv : Module.End L (Vstar L)) (k : ℕ) (F : Total L) :
    nvTotal Nv k F ∈ piece L k := by
  rw [nvTotal, LinearMap.comp_apply, LinearMap.comp_apply]
  exact (nvPiece Nv k (pieceRetract k F)).2

include hρe hρD hΦe hΦD hNv in
/-- The intertwiner commutes with `d_-` out of `V_{k+1}`. -/
theorem nvTotal_dminus (k : ℕ) {F : Total L} (hF : F ∈ piece L (k + 1)) :
    nvTotal Nv k (dminus q (k + 1) F) = dminus q (k + 1) (nvTotal Nv (k + 1) F) := by
  have hmem : dminus q (k + 1) F ∈ piece L k := by simpa using dminus_mem_piece q (k + 1) hF
  rw [nvTotal_of_mem Nv hmem, nvTotal_of_mem Nv hF]
  have h := nvPiece_lower hρe hΦe hNv (hΦD k) (hρD k) ⟨F, hF⟩
  have he : (⟨dminus q (k + 1) F, hmem⟩ : pieceSub L k) = dminusModPiece q k ⟨F, hF⟩ :=
    Subtype.ext rfl
  rw [he, h, coe_dminusModPiece]

include hρe hρS hΦe hΦS hNv in
omit [Algebra ℚ L] in
/-- The intertwiner commutes with `d^*_+` out of `V_k`. -/
theorem nvTotal_dplusStar (k : ℕ) {F : Total L} (hF : F ∈ piece L k) :
    nvTotal Nv (k + 1) (dplusStar q u k F) = dplusStar q u k (nvTotal Nv k F) := by
  have hmem : dplusStar q u k F ∈ piece L (k + 1) := dplusStar_mem_piece q u hF
  rw [nvTotal_of_mem Nv hmem, nvTotal_of_mem Nv hF]
  have h := nvPiece_raise hρe hΦe hNv (hΦS k) (hρS k) ⟨F, hF⟩
  have he : (⟨dplusStar q u k F, hmem⟩ : pieceSub L (k + 1)) = dplusStarPiece q u k ⟨F, hF⟩ :=
    Subtype.ext rfl
  rw [he, h, coe_dplusStarPiece]

include hρe hρT hΦe hΦT hNv in
omit [Algebra ℚ L] in
/-- The intertwiner commutes with the loops on `V_k`. -/
theorem nvTotal_braid {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) {F : Total L} (hF : F ∈ piece L k) :
    nvTotal Nv k (braidEnd q i F) = braidEnd q i (nvTotal Nv k F) := by
  have hmem : braidEnd q i F ∈ piece L k := braid_mem_piece q h1 hik hF
  rw [nvTotal_of_mem Nv hmem, nvTotal_of_mem Nv hF]
  have hi : i - 1 + 2 ≤ k := by omega
  have hi' : i - 1 + 1 = i := by omega
  have h := hNv (Atilde.Tg L q u k (i - 1)) (ofPiece L k ⟨F, hF⟩)
  rw [hΦT, hρT, loopVstar_ofPiece, nv_ofPiece hρe hΦe hNv, nv_ofPiece hρe hΦe hNv,
    loopVstar_ofPiece] at h
  have he : (⟨braidEnd q i F, hmem⟩ : pieceSub L k) = braidModPiece q k (i - 1) ⟨F, hF⟩ :=
    Subtype.ext (by rw [coe_braidModPiece q hi, hi']; rfl)
  rw [he, ofPiece_injective k h, coe_braidModPiece q hi, hi']
  rfl

include hρe hρT hρD hρU hρS hΦe hΦy hNv in
/-- The intertwiner carries `y_1·` on `V_k` to `(qu)^{-1}z_1y_1·`. -/
theorem nvTotal_auxVar_mul {k : ℕ} (hk : 1 ≤ k) {F : Total L} (hF : F ∈ piece L k) :
    nvTotal Nv k ((auxVar 1 : Total L) * F)
      = (q * u)⁻¹ • zopOneStar q u k ((auxVar 1 : Total L) * nvTotal Nv k F) := by
  have hy1 : (auxVar 1 : Total L) ∈ piece L k := auxVar_mem_piece le_rfl hk
  have hmem : (auxVar 1 : Total L) * F ∈ piece L k := mul_mem hy1 hF
  rw [nvTotal_of_mem Nv hmem, nvTotal_of_mem Nv hF]
  have hρy := map_yElt_atilde_eq_auxMulPiece hρe hρT hρD hρU (k := k) (i := 1) le_rfl hk
  have hyF : ρ (Atilde.yElt L q u k 1) (ofPiece L k ⟨F, hF⟩)
      = ofPiece L k ⟨(auxVar 1 : Total L) * F, hmem⟩ := by
    rw [hρy, loopVstar_ofPiece]
    exact congrArg (ofPiece L k) (Subtype.ext (coe_auxMulPiece le_rfl hk _))
  have h := hNv (Atilde.yElt L q u k 1) (ofPiece L k ⟨F, hF⟩)
  set G := nvPiece Nv k ⟨F, hF⟩ with hG
  have hyGm : (auxVar 1 : Total L) * G ∈ piece L k :=
    mul_mem hy1 (show (G : Total L) ∈ piece L k from G.2)
  have hyG : ρ (Atilde.yElt L q u k 1) (ofPiece L k G)
      = ofPiece L k ⟨(auxVar 1 : Total L) * G, hyGm⟩ := by
    rw [hρy, loopVstar_ofPiece]
    exact congrArg (ofPiece L k) (Subtype.ext (coe_auxMulPiece le_rfl hk _))
  have hz := map_zElt_one_ofPiece hρe hρT hρD hρS hk ⟨_, hyGm⟩
    ⟨zopOneStar q u k ((auxVar 1 : Total L) * G), zopOneStar_mem_piece q u hk hyGm⟩ rfl
  rw [hyF, nv_ofPiece hρe hΦe hNv, nv_ofPiece hρe hΦe hNv, hΦy k hk, map_smul, map_mul,
    LinearMap.smul_apply, Module.End.mul_apply, ← hG, hyG, hz, ← map_smul] at h
  have h' := congrArg Subtype.val (ofPiece_injective k h)
  rw [h']
  rfl

include hρe hρT hρD hρU hρS hΦe hΦU hNv in
/-- The intertwiner carries `d_+` out of `V_k` to `(qu)^{-1}z_1d_+`. -/
theorem nvTotal_dplus (k : ℕ) {F : Total L} (hF : F ∈ piece L k) :
    nvTotal Nv (k + 1) (dplus q k F)
      = (q * u)⁻¹ • zopOneStar q u (k + 1) (dplus q k (nvTotal Nv k F)) := by
  have hmem : dplus q k F ∈ piece L (k + 1) := (dplusModPiece q k ⟨F, hF⟩).2
  rw [nvTotal_of_mem Nv hmem, nvTotal_of_mem Nv hF]
  set G := nvPiece Nv k ⟨F, hF⟩ with hG
  have h := hNv (Atilde.dPlus L q u k) (ofPiece L k ⟨F, hF⟩)
  have hdG : dplus q k (G : Total L) ∈ piece L (k + 1) := (dplusModPiece q k G).2
  have hz := map_zElt_one_ofPiece hρe hρT hρD hρS (k := k + 1) (by omega) ⟨_, hdG⟩
    ⟨zopOneStar q u (k + 1) (dplus q k G), zopOneStar_mem_piece q u (by omega) hdG⟩ rfl
  have hd : dplusModPiece q k G = ⟨_, hdG⟩ := rfl
  rw [hρU, raiseVstar_ofPiece, nv_ofPiece hρe hΦe hNv, nv_ofPiece hρe hΦe hNv, hΦU, map_smul,
    map_mul, LinearMap.smul_apply, Module.End.mul_apply, ← hG, hρU, raiseVstar_ofPiece, hd, hz,
    ← map_smul] at h
  have h' := congrArg Subtype.val (ofPiece_injective (k + 1) h)
  have he : (⟨dplus q k F, hmem⟩ : pieceSub L (k + 1)) = dplusModPiece q k ⟨F, hF⟩ :=
    Subtype.ext rfl
  rw [he, h']
  rfl

include hρe hρT hρD hρU hρS hΦe hΦT hΦD hΦS hΦU hΦy hNv in
/-- **An intertwiner of Mellit's `N`, read on every piece, realises `N` piece by piece.** If `Φ`
fixes the idempotents, the loops, `d₋` and `d₊^*`, and sends `d₊` and `y_1` to `(qu)^{-1}z_1d₊`
and `(qu)^{-1}z_1y_1`, then any `𝒩'` with `𝒩'ρ(a) = ρ(Φa)𝒩'`, read on the summands, satisfies
`HJO.Sweep.IsNablaPrime` over its own restriction to `V_0`. -/
theorem isNablaPrime_of_intertwiner : IsNablaPrime q u (nvZero Nv) (nvTotal Nv) where
  mem_piece k F _ := nvTotal_mem_piece Nv k F
  map_C f := by rw [nvTotal_of_mem Nv (C_mem_piece_zero f), C_nvZero]
  map_dminus k _ hF := nvTotal_dminus hρe hρD hΦe hΦD hNv k hF
  map_dplusStar k _ hF := nvTotal_dplusStar hρe hρS hΦe hΦS hNv k hF
  map_braid h1 hik _ hF := nvTotal_braid hρe hρT hΦe hΦT hNv h1 hik hF
  map_auxVar_mul hk _ hF := nvTotal_auxVar_mul hρe hρT hρD hρS hρU hΦe hΦy hNv hk hF
  map_dplus k _ hF := nvTotal_dplus hρe hρT hρD hρS hρU hΦe hΦU hNv k hF

end ZOne

/-! ### Existence -/

section Existence

variable {q u : L} [Invertible q] [Invertible (q - 1)]

/-- The additive group of `V_*`, supplied explicitly: instance search does not find it through
the summands here. -/
noncomputable local instance : AddCommGroup (Vstar L) :=
  @DirectSum.instAddCommGroup ℕ (fun k => pieceSub L k) (fun _ => Submodule.addCommGroup _)

namespace IsNablaPrime

variable {nabla : Module.End L (Sym.Lambda L)} {N : ℕ → Module.End L (Total L)}

omit [Invertible q] [Invertible (q - 1)] in
/-- **The shadow on `V_0`**: `∇` commutes with `D_0 = d_-d^*_+`. -/
theorem nabla_dop_zero (hN : IsNablaPrime q u nabla N) (f : Sym.Lambda L) :
    nabla (Sym.Dop q u 0 f) = Sym.Dop q u 0 (nabla f) := by
  apply MvPolynomial.C_injective ℕ (Sym.Lambda L)
  have h1 := hN.map_dminus 0 (dplusStar_zero_C_mem_piece_one q u f)
  have h2 := hN.map_dplusStar 0 (C_mem_piece_zero f)
  rw [zero_add] at h1 h2
  rw [← hN.map_C, dop_zero_eq_dminus_dplusStar, h1, h2, hN.map_C, ← dop_zero_eq_dminus_dplusStar]

omit [Invertible q] [Invertible (q - 1)] in
/-- **The second slope clause on `V_0`**: `∇(e_1f) = -D_1∇f`, since `e_1 = d_-d_+` on `V_0` and
`(qu)^{-1}z_1d_+ = -y_1d_+^*` out of `V_0`. -/
theorem nabla_elemSymm_one_mul (hN : IsNablaPrime q u nabla N) (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hu : u ≠ 0) (f : Sym.Lambda L) :
    nabla (Sym.elemSymm L 1 * f) = -Sym.Dop q u 1 (nabla f) := by
  apply MvPolynomial.C_injective ℕ (Sym.Lambda L)
  have hd := dop_succ_eq_dminus_auxVar_pow_dplusStar q u 0 (nabla f)
  rw [zero_add, pow_one] at hd
  have hz := zopOneStar_dplus q u hq hq1 (C_mem_piece_zero (nabla f))
  rw [zero_add, pow_one] at hz
  have hm : dplus q 0 (C f : Total L) ∈ piece L (0 + 1) :=
    (dplusModPiece q 0 ⟨C f, C_mem_piece_zero f⟩).2
  have h1 := hN.map_dminus 0 hm
  have h2 := hN.map_dplus 0 (C_mem_piece_zero f)
  rw [zero_add] at h1 h2
  rw [← hN.map_C, ← dminus_dplus_C, h1, h2, hN.map_C, hz, smul_smul, map_smul, ← hd, map_neg,
    show (q * u)⁻¹ * -(u * q) = -1 from by field_simp, neg_one_smul]

end IsNablaPrime

/-- **Mellit's `∇'` exists on every piece**, over every `∇` meeting the two slope clauses with
`∇1 = 1`, under the hypotheses of `HJO.Sym.paramInvLambda`. The endomorphism `N` of `Ã`
(`HJO.Dyck.Tilde.Atilde.conjTwist` at the scalar `(qu)^{-1}`) preserves `𝓘`, so it induces an
intertwiner `∇'` of `V_*` (`HJO.Sweep.exists_intertwiner`); read on the summands it satisfies
`HJO.Sweep.IsNablaPrime` over `∇'|_{V_0}` (`HJO.Sweep.isNablaPrime_of_intertwiner`), and
`∇'|_{V_0}` fixes `1` and meets the two slope clauses, so it is `∇`
(`HJO.Sym.eq_of_slope_clauses`). -/
theorem exists_isNablaPrime_of_bar (hM : (1 - q) * (1 - u) ≠ 0) (hq1 : q + 1 ≠ 0) [Invertible u]
    {bar : L ≃+* L} (hbar : bar q = ⅟q) (hbaru : bar u = ⅟u) (hbb : ∀ c : L, bar (bar c) = c)
    {nabla : Module.End L (Sym.Lambda L)}
    (h0 : ∀ f : Sym.Lambda L, nabla (Sym.Dop q u 0 f) = Sym.Dop q u 0 (nabla f))
    (h1 : ∀ f : Sym.Lambda L, nabla (Sym.elemSymm L 1 * f) = -Sym.Dop q u 1 (nabla f))
    (hone : nabla 1 = 1) :
    ∃ N : ℕ → Module.End L (Total L), IsNablaPrime q u nabla N := by
  obtain ⟨ρ, hρe, hρT, hρD, hρU, hρS, hker, eiso, heiso⟩ := dpaStructure q u hq1 hbar hbaru hbb
  obtain ⟨σ, hσ⟩ := Atilde.exists_isStarSwap (K := L) (q := q) (u := u) hbar hbaru hbb
  set c : L := (q * u)⁻¹ with hc
  set Φ := Atilde.conjTwist hσ hbar c with hΦ
  have hsurj : ∀ v : Vstar L, ∃ x ∈ Atilde.atildeE0 L q u, evalOne ρ x = v := by
    intro v
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (eiso.symm v)
    exact ⟨x, x.2, by rw [← heiso, hx, LinearEquiv.apply_symm_apply]⟩
  have hker' : ∀ x ∈ Atilde.atildeE0 L q u, ∀ y ∈ Atilde.atildeE0 L q u,
      evalOne ρ x = evalOne ρ y → x - y ∈ Atilde.mellitKernel L q u := by
    intro x hx y hy hxy
    have hmem : (⟨x - y, sub_mem hx hy⟩ : Atilde.atildeE0 L q u)
        ∈ LinearMap.ker ((evalOne ρ).domRestrict (Atilde.atildeE0 L q u)) := by
      rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, map_sub, hxy, sub_self]
    rw [hker] at hmem
    exact hmem
  have hann : ∀ x ∈ Atilde.mellitKernel L q u, evalOne ρ x = 0 := by
    intro x hx
    have hx0 : x ∈ Atilde.atildeE0 L q u := Atilde.mellitKernel_le_atildeE0 hx
    have hmem : (⟨x, hx0⟩ : Atilde.atildeE0 L q u)
        ∈ LinearMap.ker ((evalOne ρ).domRestrict (Atilde.atildeE0 L q u)) := by
      rw [hker]; exact hx
    exact hmem
  obtain ⟨Nv, hNv, hNv1⟩ := exists_intertwiner hρe hsurj hker' hann Φ
    (Atilde.conjTwist_e hσ hbar c 0) (fun x hx => Atilde.conjTwist_mem_mellitKernel hσ hbar c hx)
  have hΦe : ∀ k, Φ (Atilde.e L q u k) = Atilde.e L q u k := Atilde.conjTwist_e hσ hbar c
  have hΦy : ∀ k : ℕ, 1 ≤ k → Φ (Atilde.yElt L q u k 1)
      = (q * u)⁻¹ • (Atilde.zElt L q u k 1 * Atilde.yElt L q u k 1) := fun k hk => by
    rw [hΦ, Atilde.conjTwist_yElt, Atilde.yTwist_one hσ hbar c hk]
  have hP := isNablaPrime_of_intertwiner hρe hρT hρD hρS hρU hΦe (Atilde.conjTwist_Tg hσ hbar c)
    (Atilde.conjTwist_dMinus hσ hbar c) (Atilde.conjTwist_dPlusStar hσ hbar c)
    (Atilde.conjTwist_dPlus hσ hbar c) hΦy hNv
  have hq0 : q ≠ 0 := Invertible.ne_zero q
  have hu0 : u ≠ 0 := Invertible.ne_zero u
  have hq1' : q ≠ 1 := sub_ne_zero.1 (Invertible.ne_zero (q - 1))
  have hone' : nvZero Nv 1 = 1 := by
    apply MvPolynomial.C_injective ℕ (Sym.Lambda L)
    rw [C_nvZero]
    have h1 : (⟨C 1, C_mem_piece_zero 1⟩ : pieceSub L 0) = ⟨1, one_mem (piece L 0)⟩ :=
      Subtype.ext (map_one _)
    have h := nv_ofPiece hρe hΦe hNv 0 ⟨1, one_mem (piece L 0)⟩
    rw [show ofPiece L 0 ⟨1, one_mem (piece L 0)⟩ = oneVstar L from rfl, hNv1] at h
    rw [h1, ofPiece_injective 0 h.symm, map_one]
  have heq : nvZero Nv = nabla := Sym.eq_of_slope_clauses q u hP.nabla_dop_zero
    (hP.nabla_elemSymm_one_mul hq0 hq1' hu0) h0 h1 (hone'.trans hone.symm) hM
  exact ⟨nvTotal Nv, heq ▸ hP⟩

end Existence

section Standing

open HJO.Ascent HJO.Standing HJO.Sym

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- **Mellit's `∇'` exists on every piece at the standing field**, over every Macdonald conjugator
normalised by `∇1 = 1`; the involution of `HJO.Sym.paramInvLambda` is the parameter inversion
`HJO.Standing.paramQUInv`. -/
theorem exists_isNablaPrime_param {nabla : Module.End K (Sym.Lambda K)}
    (hnab : Sym.IsMacdonaldConjugator (paramQ K) (paramU K) nabla) (hone : nabla 1 = 1) :
    ∃ N : ℕ → Module.End K (Total K), IsNablaPrime (paramQ K) (paramU K) nabla N := by
  have hM : (1 - paramQ K) * (1 - paramU K) ≠ 0 := by
    have hq := paramQ_pow_succ_ne_one K 0
    have hu := paramU_pow_succ_ne_one K 0
    rw [zero_add, pow_one] at hq hu
    exact mul_ne_zero (sub_ne_zero.2 hq.symm) (sub_ne_zero.2 hu.symm)
  exact exists_isNablaPrime_of_bar hM (paramQ_add_one_ne_zero K)
    (bar := (paramQUInv K).toRingEquiv) (paramQUInv_paramQ_eq_invOf K)
    (paramQUInv_paramU_eq_invOf K) (paramQUInv_involutive K) hnab.map_dop_zero
    hnab.map_elemSymm_one_mul hone

end Standing

/-! ### Consequences: the inverse loops, the trains and `z_1` -/

section Commutation

variable {q u : L} {nabla : Module.End L (Sym.Lambda L)} {N : ℕ → Module.End L (Total L)}

omit [Algebra ℚ L] in
/-- A product of endomorphisms each preserving a set and commuting with `M` on it preserves the set
and commutes with `M` on it. -/
theorem list_prod_mem_and_comm (M : Module.End L (Total L)) (P : Set (Total L))
    (l : List (Module.End L (Total L)))
    (hl : ∀ T ∈ l, (∀ F ∈ P, T F ∈ P) ∧ ∀ F ∈ P, M (T F) = T (M F)) :
    ∀ F ∈ P, l.prod F ∈ P ∧ M (l.prod F) = l.prod (M F) := by
  induction l with
  | nil => intro F hF; exact ⟨hF, rfl⟩
  | cons T l ih =>
    intro F hF
    obtain ⟨h1, h2⟩ := ih (fun T' hT' => hl T' (List.mem_cons_of_mem _ hT')) F hF
    obtain ⟨hT1, hT2⟩ := hl T List.mem_cons_self
    rw [List.prod_cons, Module.End.mul_apply, Module.End.mul_apply]
    exact ⟨hT1 _ h1, by rw [hT2 _ h1, h2]⟩

namespace IsNablaPrime

variable (hN : IsNablaPrime q u nabla N)
include hN

/-- `N_k` commutes with the inverse loops on `V_k`. -/
theorem map_braidInv (hq : q ≠ 0) {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) {F : Total L}
    (hF : F ∈ piece L k) : N k (braidInvEnd q i F) = braidInvEnd q i (N k F) := by
  have hG : braidInvEnd q i F ∈ piece L k := braidInv_mem_piece q hik hF
  have h := hN.map_braid h1 hik hG
  have hb : braidEnd q i (braidInvEnd q i F) = F := braid_braidInv q hq i F
  rw [hb] at h
  rw [h]
  exact (braidInv_braid q hq i _).symm

/-- `N_k` commutes with every word in the loops and inverse loops of `V_k`. -/
theorem map_word (hq : q ≠ 0) {k : ℕ} (l : List ℕ) (hl : ∀ i ∈ l, 1 ≤ i ∧ i < k)
    (T : ℕ → Module.End L (Total L)) (hT : T = braidEnd q ∨ T = braidInvEnd q) {F : Total L}
    (hF : F ∈ piece L k) : N k ((l.map T).prod F) = (l.map T).prod (N k F) := by
  refine (list_prod_mem_and_comm (N k) {F | F ∈ piece L k} (l.map T) ?_ F hF).2
  intro S hS
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hS
  obtain ⟨h1, h2⟩ := hl i hi
  rcases hT with rfl | rfl
  · exact ⟨fun F hF => braid_mem_piece q h1 h2 hF, fun F hF => hN.map_braid h1 h2 hF⟩
  · exact ⟨fun F hF => braidInv_mem_piece q h2 hF, fun F hF => hN.map_braidInv hq h1 h2 hF⟩

/-- **`N_k` commutes with the ascending trains** `T_{a↗b}` of `V_k`, `1 ≤ a, b ≤ k`. -/
theorem map_trainUpEnd (hq : q ≠ 0) {k a b : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b)
    (hbk : b ≤ k) {F : Total L} (hF : F ∈ piece L k) :
    N k (trainUpEnd q a b F) = trainUpEnd q a b (N k F) := by
  rw [trainUpEnd, Braid.trainUp]
  split_ifs with h
  · exact hN.map_word hq _ (fun i hi => by rw [List.mem_range'_1] at hi; omega) _
      (Or.inl rfl) hF
  · rw [Braid.descendingWord]
    exact hN.map_word hq _ (fun i hi => by
      rw [List.mem_reverse, List.mem_range'_1] at hi; omega) _ (Or.inr rfl) hF

/-- **`N_k` commutes with the descending trains** `T_{a↘b}` of `V_k`, `1 ≤ a, b ≤ k`. -/
theorem map_trainDownEnd (hq : q ≠ 0) {k a b : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b)
    (hbk : b ≤ k) {F : Total L} (hF : F ∈ piece L k) :
    N k (trainDownEnd q a b F) = trainDownEnd q a b (N k F) := by
  rw [trainDownEnd, Braid.trainDown]
  split_ifs with h
  · rw [Braid.descendingWord]
    exact hN.map_word hq _ (fun i hi => by
      rw [List.mem_reverse, List.mem_range'_1] at hi; omega) _ (Or.inl rfl) hF
  · exact hN.map_word hq _ (fun i hi => by rw [List.mem_range'_1] at hi; omega) _
      (Or.inr rfl) hF

/-- **`N_k` commutes with `z_1` on `V_k`**: `z_1 = q^k/(1-q)(d^*_+d_- - d_-d^*_+)T^*_{k↘1}` is a
word in `d_-`, `d^*_+` and the inverse loops. -/
theorem map_zopOneStar (hq : q ≠ 0) {k : ℕ} (hk : 1 ≤ k) {F : Total L} (hF : F ∈ piece L k) :
    N k (zopOneStar q u k F) = zopOneStar q u k (N k F) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hG : trainUpEnd q (m + 1) 1 F ∈ piece L (m + 1) :=
    trainUpEnd_mem_piece q le_rfl (by omega) hF
  have hG0 : dminus q (m + 1) (trainUpEnd q (m + 1) 1 F) ∈ piece L m := by
    simpa using dminus_mem_piece q (m + 1) hG
  have hG2 : dplusStar q u (m + 1) (trainUpEnd q (m + 1) 1 F) ∈ piece L (m + 1 + 1) :=
    dplusStar_mem_piece q u hG
  simp only [zopOneStar, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.sub_apply,
    Nat.add_sub_cancel, map_smul, map_sub]
  rw [hN.map_dplusStar m hG0, hN.map_dminus m hG, hN.map_dminus (m + 1) hG2,
    hN.map_dplusStar (m + 1) hG,
    hN.map_trainUpEnd hq (k := m + 1) (by omega) le_rfl le_rfl (by omega) hF]

end IsNablaPrime

end Commutation

/-! ### Slope words acting on every piece -/

section SlopeWords

variable {q u : L}

/-- The operator `HJO.Sweep.slopeOperator` substitutes for a letter on `V_k`: `𝗒 ↦ -y_1·` and
`𝗓 ↦ (qu)^{-1}z_1`. At `k = 1` it is `HJO.Sweep.sweepLetter`. -/
noncomputable def sweepLetterAt (q u : L) (k : ℕ) : SlopeLetter → Module.End L (Total L)
  | .y => -LinearMap.mulLeft L (auxVar 1 : Total L)
  | .z => (q * u)⁻¹ • zop q u k 1

/-- A word in the two letters acting on `V_k`, read in the order in which its letters **act**: the
head acts first. At `k = 1` it is `HJO.Sweep.sweepWordOp`. -/
noncomputable def sweepWordAt (q u : L) (k : ℕ) (t : List SlopeLetter) : Module.End L (Total L) :=
  ((t.map (sweepLetterAt q u k)).reverse).prod

/-- The empty word acts on `V_k` as the identity. -/
@[simp]
theorem sweepWordAt_nil (q u : L) (k : ℕ) : sweepWordAt q u k [] = 1 := rfl

/-- The word `x :: t` acts on `V_k` by first the letter `x`, then the word `t`. -/
theorem sweepWordAt_cons (q u : L) (k : ℕ) (x : SlopeLetter) (t : List SlopeLetter) :
    sweepWordAt q u k (x :: t) = sweepWordAt q u k t * sweepLetterAt q u k x := by
  simp [sweepWordAt, List.prod_append]

/-- Reading a concatenation: the first word acts first. -/
theorem sweepWordAt_append (q u : L) (k : ℕ) (s t : List SlopeLetter) :
    sweepWordAt q u k (s ++ t) = sweepWordAt q u k t * sweepWordAt q u k s := by
  simp [sweepWordAt, List.prod_append]

/-- The slope operator on `V_k` is its slope word read backwards. -/
theorem slopeOperator_eq_sweepWordAt (q u : L) (k a b : ℕ) :
    slopeOperator q u k a b = sweepWordAt q u k (Mellit.slopeWord a b).reverse := by
  rw [sweepWordAt, List.map_reverse, List.reverse_reverse, slopeOperator]
  congr 2

/-- Each letter preserves `V_k`, `k ≥ 1`. -/
theorem sweepLetterAt_mem_piece (q u : L) {k : ℕ} (hk : 1 ≤ k) (x : SlopeLetter) {F : Total L}
    (hF : F ∈ piece L k) : sweepLetterAt q u k x F ∈ piece L k := by
  cases x with
  | y =>
    change (-LinearMap.mulLeft L (auxVar 1 : Total L)) F ∈ piece L k
    rw [LinearMap.neg_apply, LinearMap.mulLeft_apply]
    exact neg_mem (mul_mem (auxVar_mem_piece le_rfl hk) hF)
  | z =>
    change ((q * u)⁻¹ • zop q u k 1) F ∈ piece L k
    rw [LinearMap.smul_apply, zop_one]
    exact smul_mem_piece (zopOneStar_mem_piece q u hk hF)

/-- A word preserves `V_k`, `k ≥ 1`. -/
theorem sweepWordAt_mem_piece (q u : L) {k : ℕ} (hk : 1 ≤ k) (t : List SlopeLetter)
    {F : Total L} (hF : F ∈ piece L k) : sweepWordAt q u k t F ∈ piece L k := by
  induction t generalizing F with
  | nil => exact hF
  | cons x t ih =>
    rw [sweepWordAt_cons, Module.End.mul_apply]
    exact ih (sweepLetterAt_mem_piece q u hk x hF)

namespace IsNablaPrime

variable {nabla : Module.End L (Sym.Lambda L)} {N : ℕ → Module.End L (Total L)}
  (hN : IsNablaPrime q u nabla N)
include hN

/-- `N_k` on a letter: it fixes `𝗓` and shears `𝗒` into `𝗒𝗓` (read in the order of action). -/
theorem map_sweepLetterAt (hq : q ≠ 0) {k : ℕ} (hk : 1 ≤ k) (x : SlopeLetter) {F : Total L}
    (hF : F ∈ piece L k) :
    N k (sweepLetterAt q u k x F) = sweepWordAt q u k (Mellit.addLeftSubst x) (N k F) := by
  cases x with
  | y =>
    change N k ((-LinearMap.mulLeft L (auxVar 1 : Total L)) F) = _
    rw [LinearMap.neg_apply, LinearMap.mulLeft_apply, map_neg, hN.map_auxVar_mul hk hF]
    simp [Mellit.addLeftSubst, sweepWordAt, sweepLetterAt, zop_one]
  | z =>
    change N k (((q * u)⁻¹ • zop q u k 1) F) = _
    rw [LinearMap.smul_apply, map_smul, zop_one, hN.map_zopOneStar hq hk hF]
    simp [Mellit.addLeftSubst, sweepWordAt, sweepLetterAt, zop_one]

/-- `N_k` on a word: the word acting on `V_k` is carried to its shear `t[𝗒 ↦ 𝗒𝗓]`. -/
theorem map_sweepWordAt (hq : q ≠ 0) {k : ℕ} (hk : 1 ≤ k) (t : List SlopeLetter) {F : Total L}
    (hF : F ∈ piece L k) :
    N k (sweepWordAt q u k t F) = sweepWordAt q u k (t.flatMap Mellit.addLeftSubst) (N k F) := by
  induction t generalizing F with
  | nil => simp
  | cons x t ih =>
    rw [sweepWordAt_cons, Module.End.mul_apply, ih (sweepLetterAt_mem_piece q u hk x hF),
      hN.map_sweepLetterAt hq hk x hF, List.flatMap_cons, sweepWordAt_append, Module.End.mul_apply]

/-- **`N_k` shears the slope operator**: `N_kΞ_{m,n}(-y_1F) = Ξ_{m+n,n}(-y_1N_kF)` on `V_k`, for
coprime `m, n ≥ 1`. The letter `-y_1` becomes `(qu)^{-1}z_1(-y_1)`, and the extra `𝗓` is the head
of `β_{m+n,n} = 𝗓·β_{m,n}[𝗒 ↦ 𝗒𝗓]` (`HJO.Mellit.reverse_slopeWord_add_left`). -/
theorem map_slopeOperator_neg_auxVar_mul (hq : q ≠ 0) {k m n : ℕ} (hk : 1 ≤ k)
    (hmn : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) {F : Total L} (hF : F ∈ piece L k) :
    N k (slopeOperator q u k m n (-((auxVar 1 : Total L) * F)))
      = slopeOperator q u k (m + n) n (-((auxVar 1 : Total L) * N k F)) := by
  have hy : ∀ G : Total L, -((auxVar 1 : Total L) * G) = sweepLetterAt q u k .y G := fun G => rfl
  rw [hy, hy, slopeOperator_eq_sweepWordAt, slopeOperator_eq_sweepWordAt,
    hN.map_sweepWordAt hq hk _ (sweepLetterAt_mem_piece q u hk _ hF),
    hN.map_sweepLetterAt hq hk _ hF, Mellit.reverse_slopeWord_add_left hmn hm hn,
    sweepWordAt_cons, Module.End.mul_apply]
  simp [Mellit.addLeftSubst, sweepWordAt]

end IsNablaPrime

end SlopeWords

end HJO.Sweep
