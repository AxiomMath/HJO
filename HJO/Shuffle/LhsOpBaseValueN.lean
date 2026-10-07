/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.LhsOpBaseValueM
public import HJO.Shuffle.LhsOpBaseValueLambda

/-! # The conjugated base-slope stage word is the conjugation operator applied to a monomial

Carlsson--Mellit's conjugation operator `𝒩` (`HJO.Sweep.IsConjugationOperator`) is an antilinear
involution of `V_*` with `𝒩d_-^{CM} = d_-^{CM}𝒩`, `𝒩d_+^{CM} = d^*_+𝒩` and `𝒩T_i = T_i^{-1}𝒩`.
Carlsson--Mellit's original raising operator is `d_+^{CM}F = T_1⋯T_k(F[X+(q-1)y_{k+1}])`, and their
commutator relation reads `y_{k+1} = (1-q)^{-1}T^*_{k+1↘1}[d_-^{CM},d_+^{CM}]` on `V_{k+1}`.
Applying `𝒩` to these two words gives exactly the two letters of the conjugated stage
`HJO.Mellit.LhsDesign.oldStage`:

* `𝒩 ∘ τ_{k+1} = oldOne ∘ 𝒩` (`HJO.Mellit.LhsDesign.NRel.qshift`),
* `𝒩 ∘ y_{k+1} = oldRep ∘ 𝒩` (`HJO.Mellit.LhsDesign.NRel.auxVar_mul`).

So the conjugated stage word is `𝒩` of `y_1^{α_1-1}⋯y_ℓ^{α_ℓ-1}`, and its lowering is `𝒩` of
`d_-^{CM,ℓ}(y^{α-1})` — Carlsson--Mellit's `𝒩(y_α) = N_α` at the level we need.

The relation `𝒩(F) = G` between two vectors of `V_k` of the total space is
`HJO.Mellit.LhsDesign.NRel`.
-/

@[expose] public section

namespace HJO.Mellit.LhsDesign

open HJO.Sweep MvPolynomial

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {bar : L ≃+* L}
  {N : Vstar L →+ Vstar L}

/-- `𝒩` carries the vector `F` of `V_k` to the vector `G` of `V_k`. -/
def NRel (N : Vstar L →+ Vstar L) (k : ℕ) (F G : Total L) : Prop :=
  ∃ (hF : F ∈ piece L k) (hG : G ∈ piece L k),
    N (ofPiece L k ⟨F, hF⟩) = ofPiece L k ⟨G, hG⟩

namespace NRel

omit [Algebra ℚ L] in
/-- If `𝒩(F) = G` on `V_k`, then `F ∈ V_k`. -/
theorem mem_left {k : ℕ} {F G : Total L} (h : NRel N k F G) : F ∈ piece L k := h.1

omit [Algebra ℚ L] in
/-- If `𝒩(F) = G` on `V_k`, then `G ∈ V_k`. -/
theorem mem_right {k : ℕ} {F G : Total L} (h : NRel N k F G) : G ∈ piece L k := h.2.1

/-- Every `F ∈ V_k` has an image `G` with `𝒩(F) = G` on `V_k`. -/
theorem «exists» (hN : IsConjugationOperator q u bar N) {k : ℕ} {F : Total L}
    (hF : F ∈ piece L k) : ∃ G, NRel N k F G := by
  obtain ⟨G, hG⟩ := hN.map_piece k ⟨F, hF⟩
  exact ⟨G, hF, G.2, hG⟩

omit [Algebra ℚ L] in
/-- The image `𝒩(F)` on `V_k` is unique. -/
theorem unique {k : ℕ} {F G G' : Total L} (h : NRel N k F G) (h' : NRel N k F G') : G = G' := by
  obtain ⟨hF, hG, e⟩ := h
  obtain ⟨hF', hG', e'⟩ := h'
  exact congrArg Subtype.val (ofPiece_injective k (e.symm.trans e'))

omit [Algebra ℚ L] in
/-- `𝒩(F + F') = 𝒩(F) + 𝒩(F')` on `V_k`. -/
theorem add {k : ℕ} {F G F' G' : Total L} (h : NRel N k F G) (h' : NRel N k F' G') :
    NRel N k (F + F') (G + G') := by
  obtain ⟨hF, hG, e⟩ := h
  obtain ⟨hF', hG', e'⟩ := h'
  refine ⟨add_mem hF hF', add_mem hG hG', ?_⟩
  have h1 : (⟨F + F', add_mem hF hF'⟩ : pieceSub L k) = ⟨F, hF⟩ + ⟨F', hF'⟩ := rfl
  have h2 : (⟨G + G', add_mem hG hG'⟩ : pieceSub L k) = ⟨G, hG⟩ + ⟨G', hG'⟩ := rfl
  rw [h1, h2, map_add, map_add, map_add, e, e']

/-- `𝒩(c • F) = c̄ • 𝒩(F)` on `V_k`. -/
theorem smul (hN : IsConjugationOperator q u bar N) {k : ℕ} {F G : Total L} (h : NRel N k F G)
    (c : L) : NRel N k (c • F) (bar c • G) := by
  obtain ⟨hF, hG, e⟩ := h
  refine ⟨Submodule.smul_mem (pieceSub L k) c hF, Submodule.smul_mem (pieceSub L k) (bar c) hG, ?_⟩
  have h1 : (⟨c • F, Submodule.smul_mem (pieceSub L k) c hF⟩ : pieceSub L k) = c • ⟨F, hF⟩ := rfl
  have h2 : (⟨bar c • G, Submodule.smul_mem (pieceSub L k) (bar c) hG⟩ : pieceSub L k)
      = bar c • ⟨G, hG⟩ := rfl
  rw [h1, h2, map_smul, hN.map_smul, e, map_smul]

/-- `𝒩(-F) = -𝒩(F)` on `V_k`. -/
theorem neg (hN : IsConjugationOperator q u bar N) {k : ℕ} {F G : Total L} (h : NRel N k F G) :
    NRel N k (-F) (-G) := by
  have := h.smul hN (-1)
  rwa [map_neg, map_one, neg_one_smul, neg_one_smul] at this

/-- `𝒩(F - F') = 𝒩(F) - 𝒩(F')` on `V_k`. -/
theorem sub (hN : IsConjugationOperator q u bar N) {k : ℕ} {F G F' G' : Total L}
    (h : NRel N k F G) (h' : NRel N k F' G') : NRel N k (F - F') (G - G') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h.add (h'.neg hN)

/-- `𝒩(1) = 1` on `V_0`. -/
theorem one (hN : IsConjugationOperator q u bar N) : NRel N 0 (1 : Total L) 1 :=
  ⟨one_mem (piece L 0), one_mem (piece L 0), hN.map_one⟩

/-- `𝒩d_-^{CM} = d_-^{CM}𝒩`. -/
theorem dminusCM (hN : IsConjugationOperator q u bar N) {k : ℕ} {F G : Total L}
    (h : NRel N (k + 1) F G) :
    NRel N k (dminusCM q (k + 1) F) (dminusCM q (k + 1) G) := by
  obtain ⟨hF, hG, e⟩ := h
  refine ⟨dminusCM_mem_piece q k hF, dminusCM_mem_piece q k hG, ?_⟩
  have h1 := hN.map_dminus k ⟨F, hF⟩
  rwa [e, dminusVstar_ofPiece, dminusVstar_ofPiece] at h1

/-- `𝒩d_+^{CM} = d^*_+𝒩`. -/
theorem cmDPlus (hN : IsConjugationOperator q u bar N) {k : ℕ} {F G : Total L}
    (h : NRel N k F G) :
    NRel N (k + 1) (Sweep.cmDPlus q k F) (dplusStar q u k G) := by
  obtain ⟨hF, hG, e⟩ := h
  refine ⟨cmDPlus_mem_piece q k hF, dplusStar_mem_piece q u hG, ?_⟩
  have h1 := hN.map_dplus k ⟨F, hF⟩
  rwa [e, cmDPlusVstar_ofPiece, dplusStarVstar_ofPiece] at h1

/-- `𝒩T_i = T_i^{-1}𝒩` on `V_k`, for `1 ≤ i < k`. -/
theorem braid (hN : IsConjugationOperator q u bar N) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k)
    {F G : Total L} (h : NRel N k F G) : NRel N k (Sweep.braid q i F) (braidInv q i G) := by
  obtain ⟨hF, hG, e⟩ := h
  refine ⟨braid_mem_piece q hi (by omega) hF, braidInv_mem_piece q (by omega) hG, ?_⟩
  have h1 := hN.map_loop (k := k) (i := i - 1) (by omega) (ofPiece L k ⟨F, hF⟩)
  rw [loopVstar_ofPiece, e, loopVstar_ofPiece, pieceProj_ofPiece, ← map_smul, ← map_add,
    ← map_smul] at h1
  have hi' : i - 1 + 1 = i := by omega
  have hL : braidModPiece q k (i - 1) ⟨F, hF⟩
      = ⟨Sweep.braid q i F, braid_mem_piece q hi (by omega) hF⟩ := by
    apply Subtype.ext
    rw [coe_braidModPiece q (by omega), hi']
  have hR : q⁻¹ • (braidModPiece q k (i - 1) ⟨G, hG⟩ + (q - 1) • (⟨G, hG⟩ : pieceSub L k))
      = ⟨braidInv q i G, braidInv_mem_piece q (by omega) hG⟩ := by
    apply Subtype.ext
    change q⁻¹ • ((braidModPiece q k (i - 1) ⟨G, hG⟩ : Total L) + (q - 1) • G)
      = Sweep.braidInv q i G
    rw [coe_braidModPiece q (by omega), hi', braidInv_apply, Sweep.smul_eq_scal_mul,
      Sweep.smul_eq_scal_mul]
  rwa [hL, hR] at h1

/-- `𝒩T_i^{-1} = T_i𝒩` on `V_k`, for `1 ≤ i < k`. -/
theorem braidInv (hN : IsConjugationOperator q u bar N) (hq : q ≠ 0) {k i : ℕ} (hi : 1 ≤ i)
    (hik : i + 1 ≤ k) {F G : Total L} (h : NRel N k F G) :
    NRel N k (Sweep.braidInv q i F) (Sweep.braid q i G) := by
  obtain ⟨G', hG'⟩ := NRel.exists hN (braidInv_mem_piece q (by omega : i < k) h.mem_left)
  have h2 := hG'.braid hN hi hik
  rw [braid_braidInv q hq] at h2
  have h3 := h.unique h2
  rw [h3, braid_braidInv q hq]
  exact hG'

/-- A word in the inverse braid operators of indices in `[1, k)` is carried by `𝒩` to the same
word in the braid operators. -/
theorem listProd (hN : IsConjugationOperator q u bar N) (hq : q ≠ 0) {k : ℕ} (l : List ℕ)
    (hl : ∀ j ∈ l, 1 ≤ j ∧ j + 1 ≤ k) {F G : Total L} (h : NRel N k F G) :
    NRel N k ((l.map (braidInvEnd q)).prod F) ((l.map (braidEnd q)).prod G) := by
  induction l with
  | nil => simpa using h
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact (ih fun i hi => hl i (List.mem_cons_of_mem j hi)).braidInv hN hq
      (hl j List.mem_cons_self).1 (hl j List.mem_cons_self).2

/-- `𝒩T^*_{m↘1} = T_{m↘1}𝒩` on `V_k`, for `1 ≤ m ≤ k`. -/
theorem trains (hN : IsConjugationOperator q u bar N) (hq : q ≠ 0) {k m : ℕ} (hm : 1 ≤ m)
    (hmk : m ≤ k) {F G : Total L} (h : NRel N k F G) :
    NRel N k (trainUpEnd q m 1 F) (trainDownEnd q m 1 G) := by
  rw [trainUpEnd, trainDownEnd, Braid.trainUp, Braid.trainDown]
  simp only [hm, ↓reduceIte]
  split_ifs with h1
  · obtain rfl : m = 1 := by omega
    simpa [Braid.ascendingWord, Braid.descendingWord] using h
  · exact h.listProd hN hq _ fun j hj => by rw [List.mem_reverse, List.mem_range'_1] at hj; omega

/-- **`𝒩 ∘ τ_{k+1} = oldOne ∘ 𝒩`** on `V_k → V_{k+1}`. -/
theorem qshift (hN : IsConjugationOperator q u bar N) (hq : q ≠ 0) {k : ℕ} {F G : Total L}
    (h : NRel N k F G) : NRel N (k + 1) (Sweep.qshift q (k + 1) F) (oldOne q u k G) := by
  have ht := (h.cmDPlus hN).trains hN hq (m := k + 1) (by omega) le_rfl
  have hc : trainUpEnd q (k + 1) 1 (Sweep.cmDPlus q k F) = Sweep.qshift q (k + 1) F := by
    change trainUpEnd q (k + 1) 1 (trainUpEnd q 1 (k + 1) (Sweep.qshift q (k + 1) F)) = _
    exact trainUpEnd_down_up q hq k _
  rwa [hc] at ht

/-- **`𝒩 ∘ y_{k+1} = oldRep ∘ 𝒩`** on `V_{k+1}`. -/
theorem auxVar_mul (hN : IsConjugationOperator q u bar N) (hq : q ≠ 0) (hq1 : 1 - q ≠ 0)
    (hbar : bar q = q⁻¹) {k : ℕ} {F G : Total L} (h : NRel N (k + 1) F G) :
    NRel N (k + 1) (auxVar (k + 1) * F) (oldRep q u k G) := by
  have hcomm := dminusCM_cmDPlus_sub_cmDPlus_dminusCM q k h.mem_left
  have hy : (auxVar (k + 1) : Total L) * F = (1 - q)⁻¹ • trainUpEnd q (k + 1) 1
      (Sweep.dminusCM q (k + 2) (Sweep.cmDPlus q (k + 1) F)
        - Sweep.cmDPlus q k (Sweep.dminusCM q (k + 1) F)) := by
    rw [hcomm, ← Sweep.smul_eq_scal_mul, map_smul, cmAscWord, trainUpEnd_down_up q hq, smul_smul,
      inv_mul_cancel₀ hq1, one_smul]
  have ha := (h.cmDPlus hN).dminusCM hN
  have hb := (h.dminusCM hN).cmDPlus hN
  have hs := ((ha.sub hN hb).trains hN hq (m := k + 1) (by omega) le_rfl).smul hN (1 - q)⁻¹
  rw [← hy] at hs
  convert hs using 1
  have hc : bar (1 - q)⁻¹ = -(q / (1 - q)) := by
    have hq1' : q - 1 ≠ 0 := fun h0 => hq1 (by linear_combination -h0)
    rw [map_inv₀, map_sub, map_one, hbar, inv_eq_iff_eq_inv, inv_neg, inv_div]
    field_simp
    ring
  rw [hc, oldRep, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply, neg_smul, ← smul_neg, ← map_neg, neg_sub]

end NRel

/-! ### The unstarred word `y_1^{α_1-1}⋯y_ℓ^{α_ℓ-1}` -/

omit [Algebra ℚ L] in
/-- The word whose image under `𝒩` is the conjugated stage word: from the grading `k`, each part
`A` applies `τ_{k+1}` and then multiplies by `y_{k+1}^{A-1}`. Started at `1`, it is the monomial
`y_1^{α_1-1}⋯y_ℓ^{α_ℓ-1}` (`τ` fixes it). -/
noncomputable def unFrom (q : L) : ℕ → Total L → List ℕ → Total L
  | _, F, [] => F
  | k, F, A :: α => unFrom q (k + 1) (auxVar (k + 1) ^ (A - 1) * Sweep.qshift q (k + 1) F) α

namespace NRel

/-- **One stage**: `𝒩(y_{k+1}^{A-1}τ_{k+1}F) = oldStage(𝒩F)`. -/
theorem stage (hN : IsConjugationOperator q u bar N) (hq : q ≠ 0) (hq1 : 1 - q ≠ 0)
    (hbar : bar q = q⁻¹) {k : ℕ} (A : ℕ) {F G : Total L} (h : NRel N k F G) :
    NRel N (k + 1) (auxVar (k + 1) ^ (A - 1) * Sweep.qshift q (k + 1) F) (oldStage q u k A G) := by
  rw [oldStage, Module.End.mul_apply]
  have h0 := h.qshift hN hq (u := u)
  generalize Sweep.qshift q (k + 1) F = X at h0
  generalize oldOne q u k G = Y at h0
  induction A - 1 with
  | zero => simpa using h0
  | succ n ih =>
    rw [pow_succ', pow_succ', mul_assoc, Module.End.mul_apply]
    exact ih.auxVar_mul hN hq hq1 hbar

/-- **The word**: `𝒩` carries the unstarred word to the conjugated stage word. -/
theorem unFrom (hN : IsConjugationOperator q u bar N) (hq : q ≠ 0) (hq1 : 1 - q ≠ 0)
    (hbar : bar q = q⁻¹) (α : List ℕ) :
    ∀ {k : ℕ} {F G : Total L}, NRel N k F G →
      NRel N (k + α.length) (LhsDesign.unFrom q k F α) (oldStageFrom q u k G α) := by
  induction α with
  | nil => intro k F G h; simpa [LhsDesign.unFrom, oldStageFrom] using h
  | cons A α ih =>
    intro k F G h
    have := ih (h.stage hN hq hq1 hbar A)
    rw [List.length_cons, show k + (α.length + 1) = k + 1 + α.length by omega]
    exact this

/-- `𝒩` commutes with `d_-^{CM,n}`. -/
theorem lowerRunCM (hN : IsConjugationOperator q u bar N) :
    ∀ (n : ℕ) {F G : Total L}, NRel N n F G →
      NRel N 0 (LhsDesign.lowerRunCM q n F) (LhsDesign.lowerRunCM q n G) := by
  intro n
  induction n with
  | zero => intro F G h; exact h
  | succ n ih =>
    intro F G h
    exact ih (h.dminusCM hN)

end NRel

/-! ### The unstarred word is a monomial, and its lowering is a word in `B_r` -/

omit [Algebra ℚ L] in
/-- Applied to a monomial `y^d` in `y_1, …, y_k`, the unstarred word for `β` from grading `k` is a
monomial `y^e` in `y_1, …, y_{k+ℓ(β)}`. -/
theorem unFrom_monomial (q : L) (β : List ℕ) :
    ∀ (k : ℕ) (d : ℕ →₀ ℕ), (∀ n, d n ≠ 0 → n < k) →
      ∃ e : ℕ →₀ ℕ, (∀ n, e n ≠ 0 → n < k + β.length)
        ∧ unFrom q k (MvPolynomial.monomial d 1) β = MvPolynomial.monomial e 1 := by
  induction β with
  | nil => intro k d hd; exact ⟨d, by simpa using hd, rfl⟩
  | cons A β ih =>
    intro k d hd
    have hstep : (auxVar (k + 1) : Total L) ^ (A - 1)
          * Sweep.qshift q (k + 1) (MvPolynomial.monomial d 1)
        = MvPolynomial.monomial (Finsupp.single k (A - 1) + d) 1 := by
      rw [qshift_monomial, auxVar, Nat.add_sub_cancel, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.monomial_mul, one_mul]
    obtain ⟨e, he, heq⟩ := ih (k + 1) (Finsupp.single k (A - 1) + d) (fun n hn => by
      rw [Finsupp.add_apply, Finsupp.single_apply] at hn
      by_cases hnk : k = n
      · omega
      · simp only [hnk, ↓reduceIte, zero_add] at hn; exact Nat.lt_succ_of_lt (hd n hn))
    refine ⟨e, fun n hn => by have := he n hn; simp only [List.length_cons]; omega, ?_⟩
    rw [unFrom, hstep, heq]

omit [Algebra ℚ L] in
/-- Appending a part `A` to `β` applies `τ_{m}` and then multiplies by `y_{m}^{A-1}`, where
`m = k + ℓ(β) + 1`. -/
theorem unFrom_append (q : L) (A : ℕ) (β : List ℕ) :
    ∀ (k : ℕ) (F : Total L), unFrom q k F (β ++ [A])
      = auxVar (k + β.length + 1) ^ (A - 1) * Sweep.qshift q (k + β.length + 1)
          (unFrom q k F β) := by
  induction β with
  | nil => intro k F; rfl
  | cons B β ih =>
    intro k F
    rw [List.cons_append, unFrom, ih, unFrom, List.length_cons,
      show k + 1 + β.length = k + (β.length + 1) by omega]

/-- The word `B_{α_1}⋯B_{α_ℓ}` in the Hall--Littlewood operators. -/
noncomputable def bopComp (q : L) (α : List ℕ) : Module.End L (Sym.Lambda L) :=
  (α.map fun a : ℕ => Sym.Bop q (a : ℤ)).prod

/-- The empty word in the Hall--Littlewood operators is the identity. -/
@[simp]
theorem bopComp_nil (q : L) : bopComp q [] = 1 := rfl

/-- The word for `a :: α` is `B_a` composed with the word for `α`. -/
@[simp]
theorem bopComp_cons (q : L) (a : ℕ) (α : List ℕ) :
    bopComp q (a :: α) = Sym.Bop q (a : ℤ) * bopComp q α := by
  simp [bopComp]

/-- The word for `α ++ β` is the composite of the words for `α` and for `β`. -/
theorem bopComp_append (q : L) (α β : List ℕ) :
    bopComp q (α ++ β) = bopComp q α * bopComp q β := by
  simp [bopComp]

/-- **The lowering of the unstarred word**:
`d_-^{CM,ℓ}(y_1^{β_1-1}⋯y_ℓ^{β_ℓ-1}f) = (-1)^ℓB_{β_1}⋯B_{β_ℓ}(f)` for `β` with
positive parts. -/
theorem lowerRunCM_unFrom_mul_C (q : L) (β : List ℕ) (hpos : ∀ x ∈ β, 0 < x) (f : Sym.Lambda L) :
    lowerRunCM q β.length (unFrom q 0 1 β * C f)
      = C ((-1) ^ β.length * bopComp q β f) := by
  induction β using List.reverseRecOn generalizing f with
  | nil =>
    change unFrom q 0 1 [] * C f = C ((-1) ^ 0 * (1 : Module.End L (Sym.Lambda L)) f)
    rw [unFrom, one_mul, pow_zero, one_mul, Module.End.one_apply]
  | append_singleton γ A ih =>
    have hA : 0 < A := hpos A (List.mem_append_right _ (List.mem_singleton_self A))
    have hγ : ∀ x ∈ γ, 0 < x := fun x hx => hpos x (List.mem_append_left _ hx)
    obtain ⟨e, he, heq⟩ := unFrom_monomial q γ 0 0 (fun n hn => absurd rfl hn)
    rw [MvPolynomial.monomial_zero', MvPolynomial.C_1] at heq
    have hmem : (MvPolynomial.monomial e (1 : Sym.Lambda L) : Total L) * C f ∈ piece L γ.length :=
      mul_mem (monomial_mem_piece (fun n hn => by have := he n hn; omega) 1)
        (piece_mono (Nat.zero_le _) (C_mem_piece_zero f))
    have hAz : (((A - 1 : ℕ) : ℤ) + 1) = (A : ℤ) := by omega
    rw [unFrom_append, Nat.zero_add, heq, qshift_monomial, List.length_append,
      List.length_singleton]
    change lowerRunCM q γ.length (dminusCM q (γ.length + 1) _) = _
    rw [mul_assoc, dminusCM_auxVar_pow_mul q γ.length (A - 1) hmem, hAz, bopExt_monomial_mul,
      bopExt_C, map_neg, ← heq, ih hγ, bopComp_append, bopComp_cons, bopComp_nil, mul_one,
      Module.End.mul_apply, pow_succ, mul_neg_one,
      neg_mul, map_neg]

/-- **`ω̄B_α(f) = (-q)^{|α|-ℓ(α)}C_α(ω̄f)`** for `σ` with `σ(q) = q⁻¹`. -/
theorem omegaBar_bopComp {σ : L ≃+* L} (hq : q ≠ 0) (hσ : σ q = q⁻¹) (α : List ℕ)
    (f : Sym.Lambda L) :
    Sym.omegaBar σ (bopComp q α f)
      = (-q) ^ ((α.sum : ℤ) - (α.length : ℤ)) • Sym.CopComp q α (Sym.omegaBar σ f) := by
  have hq' : (-q : L) ≠ 0 := neg_ne_zero.2 hq
  have hstep : ∀ (r : ℕ) (g : Sym.Lambda L), Sym.omegaBar σ (Sym.Bop q (r : ℤ) g)
      = (-q) ^ ((r : ℤ) - 1) • Sym.Cop q r (Sym.omegaBar σ g) := by
    intro r g
    rw [Sym.cop_omegaBar hσ, smul_smul, ← zpow_add₀ hq', show (r : ℤ) - 1 + (1 - r) = 0 by ring,
      zpow_zero, one_smul]
  induction α generalizing f with
  | nil => simp [Sym.CopComp]
  | cons a α ih =>
    have e1 : bopComp q (a :: α) f = Sym.Bop q (a : ℤ) (bopComp q α f) := by
      rw [bopComp_cons, Module.End.mul_apply]
    have e2 : Sym.CopComp q (a :: α) = Sym.Cop q a * Sym.CopComp q α := by
      rw [Sym.CopComp, Sym.CopComp, List.map_cons, List.prod_cons]
    rw [e1, hstep, ih, map_smul, smul_smul, ← zpow_add₀ hq', e2, Module.End.mul_apply,
      List.sum_cons, List.length_cons]
    congr 2
    push_cast
    ring

end HJO.Mellit.LhsDesign
