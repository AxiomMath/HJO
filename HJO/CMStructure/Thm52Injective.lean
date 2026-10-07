/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SphericalModule
public meta import HJO.Attr

/-! # Carlsson and Mellit's Theorem 5.2: `𝔸_q𝟏_0 ≅ V_*`

The evaluation map `f𝟏_0 ↦ f(1)` from the spherical module `𝔸_q𝟏_0` of the Dyck path algebra to
the module `V_*` of `HJO.Sweep.exists_isDpaAction_cm` is an isomorphism of `𝔸_q`-modules carrying
`𝟏_0` to `1` and `𝟏_k𝔸_q𝟏_0` onto `V_k`. Surjectivity, equivariance and the grading are proved in
the file of the spherical module; this file proves injectivity, which is Carlsson and Mellit's
Lemma 5.6.

The sorted normal-form words

`d_-^m y_1^{b_1} ⋯ y_{k+m}^{b_{k+m}} d_+^{k+m}𝟏_0`,   `b_{k+1} ≥ ⋯ ≥ b_{k+m}`,

span `𝔸_q𝟏_0`. Each evaluates exactly to

`(-1)^m y_1^{b_1} ⋯ y_k^{b_k} B_{b_{k+1}+1}(⋯ B_{b_{k+m}+1}(1)⋯) ∈ V_k`:

`d_+^{k+m}𝟏_0` evaluates to `1 ∈ V_{k+m}`, the corner elements act by multiplication by the
variables, and one lowering arrow at the vertex `j` passes the variables `y_1, …, y_j`
(`HJO.Sweep.dminusCM_auxVar_mul`) and turns `y_{j+1}^r g`, `g ∈ Λ`, into `-B_{r+1}g`
(`HJO.Sweep.dminusCM_auxVar_pow_mul`). These values are, up to sign, the basis of
`HJO.Sweep.exists_basis_vstar_prod_bop`, so a combination of sorted words evaluating to zero has
zero coefficients.

## Main results

* `HJO.Sweep.evalOneAq_normalWord`: the evaluation of a normal-form word.
* `HJO.Sweep.evalOneAq_injOn_e0Ideal`: the evaluation map is injective on `𝔸_q𝟏_0`.
* `HJO.Sweep.exists_linearEquiv_e0Ideal`.

## Implementation notes

**The normal-form words are reindexed by the basis.** A normal-form word is indexed by a function
`b : ℕ → ℕ`, of which only the values on `1, …, k + m` matter, so the words indexed by functions
are not independent. The words are therefore read along the index of
`HJO.Sweep.exists_basis_vstar_prod_bop` — the head `a : Fin k →₀ ℕ` and the weakly decreasing tail
`l` — through the exponent function `HJO.Sweep.thm52Exponent`, and every sorted word is shown equal
to the word at its index.

## References

`HJO.Sweep.exists_linearEquiv_e0Ideal` is E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Theorem 5.2 and Lemma 5.6.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q] [Invertible (q - 1)]

/-- A corner monomial at the vertex `n` reads its exponents only on `1, …, n`. -/
theorem yMon_congr {n : ℕ} {b b' : ℕ → ℕ} (h : ∀ s, 1 ≤ s → s ≤ n → b s = b' s) :
    yMon K q n b = yMon K q n b' := by
  unfold yMon yProd
  congr 1
  refine List.map_congr_left fun s hs => ?_
  obtain ⟨h1, h2⟩ := mem_range'_one_bounds hs
  rw [h s h1 h2]

/-- A normal-form word reads its exponents only on `1, …, k + m`. -/
theorem normalWord_congr {k m : ℕ} {b b' : ℕ → ℕ} (h : ∀ s, 1 ≤ s → s ≤ k + m → b s = b' s) :
    normalWord K q k m b = normalWord K q k m b' := by
  rw [normalWord, normalWord, yMon_congr h]

end HJO.Dyck.Aq

namespace HJO.Sweep

/-! ### The exponents of the normal-form word at an index of the basis -/

/-- The exponent function of the normal-form word at the index `(k, a, l)` of
`HJO.Sweep.exists_basis_vstar_prod_bop`: the head `a` on `1, …, k` and the tail `l` on
`k + 1, …, k + |l|`. -/
def thm52Exponent (k : ℕ) (a : Fin k →₀ ℕ) (l : List ℕ) (j : ℕ) : ℕ :=
  if h : 1 ≤ j ∧ j ≤ k then a ⟨j - 1, by omega⟩ else l.getD (j - k - 1) 0

/-- On `j + 1` with `j : Fin k`, the exponent function takes the value `a j` of the head. -/
theorem thm52Exponent_head {k : ℕ} (a : Fin k →₀ ℕ) (l : List ℕ) (j : Fin k) :
    thm52Exponent k a l ((j : ℕ) + 1) = a j := by
  rw [thm52Exponent]
  split_ifs with h
  · exact congrArg a (Fin.ext (by simp))
  · exact absurd ⟨by omega, j.2⟩ h

/-- On `k + 1 + i`, the exponent function takes the `i`-th entry of the tail, or `0` past its
end. -/
theorem thm52Exponent_tail {k : ℕ} (a : Fin k →₀ ℕ) (l : List ℕ) (i : ℕ) :
    thm52Exponent k a l (k + 1 + i) = l.getD i 0 := by
  rw [thm52Exponent]
  split_ifs with h
  · omega
  · congr 1
    omega

/-- The product of `f` over the list `1, …, k` is the product of `f (j + 1)` over `j : Fin k`. -/
theorem list_prod_map_range'_one {M : Type*} [CommMonoid M] (f : ℕ → M) (k : ℕ) :
    ((List.range' 1 k).map f).prod = ∏ j : Fin k, f ((j : ℕ) + 1) := by
  rw [Fin.prod_univ_def, List.range'_eq_map_range, List.map_map,
    ← List.map_coe_finRange_eq_range, List.map_map]
  congr 2
  funext j
  simp [add_comm]

/-! ### Iterated corner operators on one summand -/

section Loop

variable {L : Type*} [Field L]

/-- The `n`-th power of a loop operator on `V_*` acts on the summand `V_k` as the `n`-th power of
its component. -/
theorem loopVstar_pow_ofPiece (T : ∀ k : ℕ, ℕ → Module.End L (pieceSub L k)) (k i n : ℕ)
    (F : pieceSub L k) :
    (loopVstar T k i ^ n) (ofPiece L k F) = ofPiece L k ((T k i ^ n) F) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih => rw [pow_succ, Module.End.mul_apply, loopVstar_ofPiece, ih, pow_succ,
      Module.End.mul_apply]

/-- For `1 ≤ i ≤ k`, the `n`-th power of multiplication by `y_i` on `V_k` is multiplication by
`y_i ^ n`. -/
theorem coe_auxMulPiece_pow {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) (n : ℕ) (F : pieceSub L k) :
    ((auxMulPiece L k i ^ n) F : Total L) = (auxVar i : Total L) ^ n * F := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_mul]; rfl
  | succ n ih => rw [pow_succ', Module.End.mul_apply, coe_auxMulPiece h1 hik, ih, pow_succ',
      mul_assoc]

end Loop

/-! ### The lowering operator passes the earlier variables -/

section Lower

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- For `1 ≤ j ≤ k`, the lowering operator at the vertex `k + 1` commutes with multiplication by
`y_j ^ n`. -/
theorem dminusCM_auxVar_pow_mul' (q : L) {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (n : ℕ)
    (F : Total L) :
    dminusCM q (k + 1) ((auxVar j : Total L) ^ n * F)
      = (auxVar j : Total L) ^ n * dminusCM q (k + 1) F := by
  induction n with
  | zero => rw [pow_zero, one_mul, one_mul]
  | succ n ih => rw [pow_succ', mul_assoc, dminusCM_auxVar_mul q hj hjk, ih, mul_assoc]

/-- The lowering operator at the vertex `k + 1` commutes with multiplication by a product of
powers `y_s ^ b s` over a list of indices `1 ≤ s ≤ k`. -/
theorem dminusCM_prod_auxVar_pow_mul (q : L) {k : ℕ} (b : ℕ → ℕ) :
    ∀ l : List ℕ, (∀ s ∈ l, 1 ≤ s ∧ s ≤ k) → ∀ F : Total L,
      dminusCM q (k + 1) ((l.map fun s => (auxVar s : Total L) ^ b s).prod * F)
        = (l.map fun s => (auxVar s : Total L) ^ b s).prod * dminusCM q (k + 1) F := by
  intro l
  induction l with
  | nil => intro _ F; simp
  | cons s t ih =>
    intro hl F
    obtain ⟨hs1, hsk⟩ := hl s List.mem_cons_self
    rw [List.map_cons, List.prod_cons, mul_assoc, dminusCM_auxVar_pow_mul' q hs1 hsk,
      ih (fun r hr => hl r (List.mem_cons_of_mem _ hr)), mul_assoc]

end Lower

/-! ### The evaluation of a normal-form word -/

section Onto

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L} [Invertible q] [Invertible (q - 1)]
  {ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)} (hact : IsDpaAction q ρ)
  (hT : ∀ k i : ℕ, ρ (Dyck.Aq.Tg L q k i) = loopVstar (braidModPiece q) k i)
  (hD : ∀ k : ℕ, ρ (Dyck.Aq.dMinus L q k) = lowerVstar (dminusPiece q) k)
  (hU : ∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = raiseVstar (cmDPlusPiece q) k)

include hact hT hD hU in
/-- **A product of corner elements acts by multiplication by the variables.** -/
theorem map_yProd_ofPiece {k : ℕ} (b : ℕ → ℕ) :
    ∀ l : List ℕ, (∀ s ∈ l, 1 ≤ s ∧ s ≤ k) → ∀ F : pieceSub L k,
      ∃ G : pieceSub L k, ρ (Dyck.Aq.yProd L q k b l) (ofPiece L k F) = ofPiece L k G ∧
        (G : Total L) = (l.map fun s => (auxVar s : Total L) ^ b s).prod * F := by
  intro l
  induction l with
  | nil => intro _ F; exact ⟨F, by rw [Dyck.Aq.yProd_nil, map_one]; rfl, by simp⟩
  | cons s t ih =>
    intro hl F
    obtain ⟨hs1, hsk⟩ := hl s List.mem_cons_self
    obtain ⟨G, hG, hGv⟩ := ih (fun r hr => hl r (List.mem_cons_of_mem _ hr)) F
    refine ⟨(auxMulPiece L k s ^ b s) G, ?_, ?_⟩
    · rw [Dyck.Aq.yProd_cons, map_mul, Module.End.mul_apply, hG, map_pow,
        map_yElt_eq_auxMulPiece_cm hact hT hD hU hs1 hsk, loopVstar_pow_ofPiece]
    · rw [coe_auxMulPiece_pow hs1 hsk, hGv, List.map_cons, List.prod_cons, mul_assoc]

include hact hT hD hU in
/-- **The evaluation of a normal-form word**: the word
`d_-^m y_1^{b_1} ⋯ y_{k+m}^{b_{k+m}} d_+^{k+m}𝟏_0` evaluates to
`(-1)^m y_1^{b_1} ⋯ y_k^{b_k} B_{b_{k+1}+1}(⋯ B_{b_{k+m}+1}(1)⋯)`. -/
theorem evalOneAq_normalWord (b : ℕ → ℕ) (m : ℕ) :
    ∀ k : ℕ, ∃ F : pieceSub L k,
      evalOneAq ρ (Dyck.Aq.normalWord L q k m b) = (-1 : L) ^ m • ofPiece L k F ∧
      (F : Total L) = ((List.range' 1 k).map fun s => (auxVar s : Total L) ^ b s).prod *
        algebraMap (Sym.Lambda L) (Total L)
          (((((List.range m).map fun i => b (k + 1 + i)).map (· + 1)).map
            fun r : ℕ => Sym.Bop q (r : ℤ)).prod 1) := by
  induction m with
  | zero =>
    intro k
    obtain ⟨G, hG, hGv⟩ := map_yProd_ofPiece hact hT hD hU (k := k) b (List.range' 1 k)
      (fun s hs => Dyck.Aq.mem_range'_one_bounds hs) (oneAtPiece L k)
    refine ⟨G, ?_, ?_⟩
    · rw [Dyck.Aq.normalWord, Dyck.Aq.dMinusPow_zero, Nat.add_zero, evalOneAq_mul,
        evalOneAq_dPlusPow hact hU, map_mul, Module.End.mul_apply, Dyck.Aq.yMon, hG,
        hact.map_e, pieceProj_ofPiece, pow_zero, one_smul]
    · rw [hGv]; simp
  | succ m ih =>
    intro k
    obtain ⟨G, hG, hGv⟩ := ih (k + 1)
    refine ⟨-dminusPiece q k G, ?_, ?_⟩
    · rw [← Dyck.Aq.dMinus_mul_normalWord, evalOneAq_mul, hG, map_smul, hD, lowerVstar_ofPiece,
        map_neg, pow_succ, mul_neg_one, neg_smul_neg]
    · have hr : List.range' 1 (k + 1) = List.range' 1 k ++ [k + 1] := by
        rw [List.range'_concat]; congr 2; omega
      have hl : (List.range (m + 1)).map (fun i => b (k + 1 + i))
          = b (k + 1) :: (List.range m).map (fun i => b (k + 1 + 1 + i)) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp_apply, Nat.succ_eq_add_one]
        congr 1
        omega
      rw [NegMemClass.coe_neg, coe_dminusPiece, hGv, hr, List.map_append, List.prod_append,
        List.map_singleton, List.prod_singleton, mul_assoc,
        dminusCM_prod_auxVar_pow_mul q b _ (fun s hs => Dyck.Aq.mem_range'_one_bounds hs),
        MvPolynomial.algebraMap_eq, dminusCM_auxVar_pow_mul_C, mul_neg, neg_neg, hl,
        List.map_cons, List.map_cons, List.prod_cons, Module.End.mul_apply]
      congr 3

/-- The tail exponents of a sorted normal-form word form a weakly decreasing list, the tail of an
index of `HJO.Sweep.exists_basis_vstar_prod_bop`. -/
theorem sortedGE_map_range {k m : ℕ} {b : ℕ → ℕ}
    (hb : ∀ j, k + 1 ≤ j → j + 1 ≤ k + m → b (j + 1) ≤ b j) :
    ((List.range m).map fun i => b (k + 1 + i)).SortedGE := by
  refine List.sortedGE_of_getElem_ge_getElem_of_le fun i j hi hj hji => ?_
  simp only [List.length_map, List.length_range] at hi hj
  simp only [List.getElem_map, List.getElem_range]
  have key : ∀ d, j + d < m → b (k + 1 + (j + d)) ≤ b (k + 1 + j) := by
    intro d
    induction d with
    | zero => exact fun _ => le_rfl
    | succ d ih =>
      intro hd
      have h₁ := hb (k + 1 + (j + d)) (by omega) (by omega)
      rw [show k + 1 + (j + d) + 1 = k + 1 + (j + (d + 1)) by omega] at h₁
      exact h₁.trans (ih (by omega))
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
  exact key d hi

include hact hT hD hU in
/-- **The evaluation map is injective on `𝔸_q𝟏_0`**, the injectivity clause of
`HJO.Sweep.exists_linearEquiv_e0Ideal`. The sorted normal-form words span `𝔸_q𝟏_0`, and read along
the index of `HJO.Sweep.exists_basis_vstar_prod_bop` they evaluate to `±` the basis vectors, so a
combination of them evaluating to zero is zero. -/
theorem evalOneAq_injOn_e0Ideal : ∀ x ∈ Dyck.Aq.e0Ideal L q, evalOneAq ρ x = 0 → x = 0 := by
  classical
  obtain ⟨B, hB⟩ := exists_basis_vstar_prod_bop (L := L) q
  let w : (Σ k : ℕ, (Fin k →₀ ℕ) × {l : List ℕ // l.SortedGE}) → Dyck.Aq L q := fun i =>
    Dyck.Aq.normalWord L q i.1 i.2.2.1.length (thm52Exponent i.1 i.2.1 i.2.2.1)
  let u : (Σ k : ℕ, (Fin k →₀ ℕ) × {l : List ℕ // l.SortedGE}) → Lˣ := fun i =>
    (-1 : Lˣ) ^ i.2.2.1.length
  have hw : ∀ i, evalOneAq ρ (w i) = (u • ⇑B) i := by
    rintro ⟨k, a, l⟩
    obtain ⟨F, hF, hFv⟩ :=
      evalOneAq_normalWord hact hT hD hU (thm52Exponent k a l.1) l.1.length k
    obtain ⟨F', hF', hF'v⟩ := hB k a l
    have hl : (List.range l.1.length).map (fun i => thm52Exponent k a l.1 (k + 1 + i)) = l.1 := by
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      simp only [List.getElem_map, List.getElem_range, thm52Exponent_tail]
      exact List.getD_eq_getElem _ _ h2
    have hFF : F = F' := by
      refine Subtype.ext ?_
      rw [hFv, hF'v, hl, list_prod_map_range'_one]
      simp only [thm52Exponent_head]
    change _ = ((-1 : Lˣ) ^ l.1.length) • B ⟨k, (a, l)⟩
    rw [hF, hFF, hF', Units.smul_def]
    simp
  have hspan : Dyck.Aq.e0Ideal L q ≤ Submodule.span L (Set.range w) := by
    refine le_trans Dyck.Aq.e0Ideal_le_iSup_sortedNormalSpan
      (iSup_le fun k => Submodule.span_le.2 ?_)
    rintro _ ⟨m, b, hb, rfl⟩
    refine Submodule.subset_span ⟨⟨k, Finsupp.equivFunOnFinite.symm (fun j : Fin k => b (j + 1)),
      ⟨(List.range m).map fun i => b (k + 1 + i), sortedGE_map_range hb⟩⟩, ?_⟩
    simp only [w, List.length_map, List.length_range]
    refine Dyck.Aq.normalWord_congr fun s hs1 hs2 => ?_
    rw [thm52Exponent]
    split_ifs with h
    · rw [Finsupp.coe_equivFunOnFinite_symm]
      congr 1
      simp only
      omega
    · rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range]
      congr 1
      omega
  intro x hx h0
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hspan hx)
  have hc : c = 0 := by
    refine linearIndependent_iff.1 (B.linearIndependent.units_smul u) c ?_
    rw [Finsupp.linearCombination_apply, ← h0, map_finsuppSum]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [map_smul, hw]
  rw [hc, Finsupp.sum_zero_index]

include hact hT hD hU in
/-- **Carlsson and Mellit's Theorem 5.2.** The evaluation map `f𝟏_0 ↦ f(1)` is an
isomorphism of `𝔸_q`-modules from `𝔸_q𝟏_0` to `V_*`, carrying `𝟏_0` to `1 ∈ V_0` and
`𝟏_k𝔸_q𝟏_0` onto `V_k` for every `k ≥ 0`, where `V_*` carries the action of
`HJO.Sweep.exists_isDpaAction_cm`. -/
@[hjo "lem_cm_thm52"]
theorem exists_linearEquiv_e0Ideal :
    ∃ f : Dyck.Aq.e0Ideal L q ≃ₗ[L] Vstar L,
      (∀ x : Dyck.Aq.e0Ideal L q, f x = evalOneAq ρ (x : Dyck.Aq L q)) ∧
      (∀ (a : Dyck.Aq L q) (x : Dyck.Aq.e0Ideal L q),
        f ⟨a * (x : Dyck.Aq L q), Dyck.Aq.mul_mem_e0Ideal a x.2⟩ = ρ a (f x)) ∧
      f ⟨Dyck.Aq.e L q 0, Dyck.Aq.e_zero_mem_e0Ideal⟩ = oneVstar L ∧
      ∀ k : ℕ, Submodule.map (f : Dyck.Aq.e0Ideal L q →ₗ[L] Vstar L)
          ((Dyck.Aq.cornerE0 L q k).comap (Dyck.Aq.e0Ideal L q).subtype)
        = LinearMap.range (ofPiece L k) :=
  exists_linearEquiv_e0Ideal_of_injOn hact hT hD hU (evalOneAq_injOn_e0Ideal hact hT hD hU)

end Onto

end HJO.Sweep

end
